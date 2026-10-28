package shortscan

import (
	"bufio"
	"embed"
	"fmt"
	"io"
	"os"
	"strings"
	"sync"
	"time"

	"github.com/thezakman/shortscan/pkg/shortutil"
)

type wordlistRecord struct {
	checksums   string
	filename    string
	extension   string
	filename83  string
	extension83 string
}

type wordlistSource struct {
	name string
	open func() (io.ReadCloser, error)
}

type wordlistConfig struct {
	wordlist  []wordlistRecord
	isRainbow bool
	sources   []wordlistSource
	loadOnce  sync.Once
	loadDone  chan struct{}
	loadErr   error
	loadStats wordlistLoadStats
	// byFilename83 and byFirstChar are built once, after load() finishes populating
	// wordlist, so filenameCandidates (recovery.go) can look up candidates for a
	// resolved 8.3 alias without a full O(N) scan of the wordlist for every single
	// alias the scan resolves — on the embedded 111k-line default wordlist this was
	// 2-3 full linear passes per resolved short name (the dominant recovery-phase
	// cost on a directory with many short names). Both maps are read-only after
	// load() returns (waitLoaded()/records() already happens-before every reader via
	// the loadDone channel), so no extra locking is needed here.
	byFilename83 map[string][]wordlistRecord // key: strings.ToUpper(record.filename83)
	byFirstChar  map[byte][]wordlistRecord   // key: first byte of strings.ToUpper(record.filename); rainbow wordlists only
}

type wordlistLoadStats struct {
	entries    int
	duplicates int
	replaced   int
	files      int
	duration   time.Duration
}

// Embed the default wordlist and DLL/source-disclosure list
//
//go:embed resources/wordlist.txt resources/dll.txt
var defaultWordlist embed.FS

// configureWordlists records inexpensive openers up front but deliberately
// does not parse any entries. Custom paths are stat'ed so a typo still fails
// fast even when every target later proves non-vulnerable.
func configureWordlists(paths []string) (*wordlistConfig, error) {
	wc := &wordlistConfig{loadDone: make(chan struct{})}
	if len(paths) == 0 {
		wc.sources = append(wc.sources, wordlistSource{
			name: "embedded:resources/wordlist.txt",
			open: func() (io.ReadCloser, error) {
				return defaultWordlist.Open("resources/wordlist.txt")
			},
		})
		return wc, nil
	}
	for _, filename := range paths {
		if _, err := os.Stat(filename); err != nil {
			return nil, fmt.Errorf("wordlist %q: %w", filename, err)
		}
		filename := filename
		wc.sources = append(wc.sources, wordlistSource{
			name: filename,
			open: func() (io.ReadCloser, error) {
				return os.Open(filename)
			},
		})
	}
	return wc, nil
}

// startLoading begins the one-time parse without blocking the caller. Scan()
// invokes it only after confirming a vulnerable target, while character-set
// discovery continues on the network.
func (wc *wordlistConfig) startLoading() {
	if wc == nil {
		return
	}
	wc.loadOnce.Do(func() {
		go func() {
			started := time.Now()
			wc.loadErr = wc.load()
			wc.loadStats.duration = time.Since(started)
			close(wc.loadDone)
		}()
	})
}

func (wc *wordlistConfig) waitLoaded() error {
	if wc == nil {
		return nil
	}
	wc.startLoading()
	<-wc.loadDone
	return wc.loadErr
}

func (wc *wordlistConfig) records() ([]wordlistRecord, bool) {
	if wc == nil {
		return nil, false
	}
	if err := wc.waitLoaded(); err != nil {
		return nil, false
	}
	return wc.wordlist, wc.isRainbow
}

func (wc *wordlistConfig) load() error {
	index := make(map[string]int)
	wc.loadStats.files = len(wc.sources)
	for _, source := range wc.sources {
		isRainbow, err := readWordlistSource(source, func(record wordlistRecord) {
			key := strings.ToLower(record.filename + record.extension)
			if existingIndex, exists := index[key]; exists {
				wc.loadStats.duplicates++
				existing := wc.wordlist[existingIndex]
				if existing.checksums == "" && record.checksums != "" {
					wc.wordlist[existingIndex] = record
					wc.loadStats.replaced++
				} else if existing.checksums != "" && record.checksums != "" {
					existing.checksums = mergeChecksums(existing.checksums, record.checksums)
					wc.wordlist[existingIndex] = existing
				}
				return
			}
			index[key] = len(wc.wordlist)
			wc.wordlist = append(wc.wordlist, record)
		})
		if err != nil {
			return err
		}
		wc.isRainbow = wc.isRainbow || isRainbow
	}
	wc.loadStats.entries = len(wc.wordlist)
	wc.buildIndexes()
	return nil
}

// buildIndexes populates byFilename83/byFirstChar from the now-final wc.wordlist.
// Called once, at the end of load(), before loadDone is closed — every reader goes
// through waitLoaded()/records() first, so this always happens-before any lookup.
func (wc *wordlistConfig) buildIndexes() {
	wc.byFilename83 = make(map[string][]wordlistRecord, len(wc.wordlist))
	for _, record := range wc.wordlist {
		if record.filename83 == "" {
			continue
		}
		key := strings.ToUpper(record.filename83)
		wc.byFilename83[key] = append(wc.byFilename83[key], record)
	}
	// byFirstChar only serves the rainbow/checksummed-alias prefix scan
	// (filenameCandidates in recovery.go), so skip building it for a plain
	// (non-rainbow) wordlist that will never use it.
	if !wc.isRainbow {
		return
	}
	wc.byFirstChar = make(map[byte][]wordlistRecord, len(wc.wordlist))
	for _, record := range wc.wordlist {
		if record.filename == "" {
			continue
		}
		c := record.filename[0]
		if c >= 'a' && c <= 'z' {
			c -= 'a' - 'A'
		}
		wc.byFirstChar[c] = append(wc.byFirstChar[c], record)
	}
}

// candidatesByFilename83 returns the wordlist records whose 8.3 base matches
// filename83 (case-insensitive), O(1) average instead of a full-wordlist scan.
func (wc *wordlistConfig) candidatesByFilename83(filename83 string) []wordlistRecord {
	if wc == nil || wc.byFilename83 == nil {
		return nil
	}
	return wc.byFilename83[strings.ToUpper(filename83)]
}

// candidatesByPrefixBucket returns every record sharing prefix's first character
// (case-insensitive) — the coarse bucket the checksummed-alias scan (filenameCandidates
// in recovery.go) then filters further with the real strings.HasPrefix check. Cuts the
// scan to ~1/36th of the wordlist on average instead of every record on every call;
// nil (not a full scan) for a non-rainbow wordlist or an empty prefix.
func (wc *wordlistConfig) candidatesByPrefixBucket(prefix string) []wordlistRecord {
	if wc == nil || wc.byFirstChar == nil || prefix == "" {
		return nil
	}
	c := prefix[0]
	if c >= 'a' && c <= 'z' {
		c -= 'a' - 'A'
	}
	return wc.byFirstChar[c]
}

func readWordlistSource(source wordlistSource, add func(wordlistRecord)) (bool, error) {
	fh, err := source.open()
	if err != nil {
		return false, fmt.Errorf("open %s: %w", source.name, err)
	}
	defer fh.Close()
	scanner := bufio.NewScanner(fh)
	scanner.Buffer(make([]byte, 64*1024), 1024*1024)
	isRainbow := false
	sawContent := false
	lineNumber := 0
	for scanner.Scan() {
		lineNumber++
		line := scanner.Text()
		if len(line) == 0 || (line[0] == '#' && line != rainbowMagic) {
			continue
		}
		if !sawContent && line == rainbowMagic {
			isRainbow = true
			sawContent = true
			continue
		}
		sawContent = true
		var record wordlistRecord
		if isRainbow {
			parts := strings.Split(line, "\t")
			if len(parts) != 5 {
				return false, fmt.Errorf("%s:%d: invalid rainbow entry: expected 5 tab-separated fields", source.name, lineNumber)
			}
			extension := parts[4]
			if extension != "" {
				extension = "." + extension
			}
			record = wordlistRecord{
				checksums: parts[0], filename83: parts[1], extension83: parts[2],
				filename: parts[3], extension: extension,
			}
		} else if dot := strings.LastIndex(line, "."); dot > 0 && line[0] != '.' {
			filename, extension := line[:dot], line[dot:]
			_, filename83, extension83 := shortutil.Gen8dot3(filename, extension)
			record = wordlistRecord{filename: filename, extension: extension, filename83: filename83, extension83: extension83}
		} else {
			_, filename83, _ := shortutil.Gen8dot3(line, "")
			record = wordlistRecord{filename: line, filename83: filename83}
		}
		// A "." or ".." line becomes a dot-segment once resolved recovery paths
		// turn record.filename into a URL path component (recovery.go, and
		// --recurse's foundDirectories) — same guard class as references.go and
		// aliasprobe.go apply to untrusted path segments elsewhere.
		if isDotSegment(record.filename) {
			continue
		}
		add(record)
	}
	if err := scanner.Err(); err != nil {
		return false, fmt.Errorf("read %s: %w", source.name, err)
	}
	return isRainbow, nil
}

func mergeChecksums(left, right string) string {
	seen := make(map[string]struct{})
	var merged strings.Builder
	for _, checksums := range []string{left, right} {
		for offset := 0; offset+4 <= len(checksums); offset += 4 {
			checksum := checksums[offset : offset+4]
			if _, exists := seen[checksum]; exists {
				continue
			}
			seen[checksum] = struct{}{}
			merged.WriteString(checksum)
		}
	}
	return merged.String()
}
