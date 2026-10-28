package shortscan

import (
	"bufio"
	"io"
	"strings"
)

// readURLList applies the same bounded parsing to files and stdin. A read error
// rejects the entire list so a partial scan cannot be mistaken for a complete one.
func readURLList(r io.Reader) ([]string, error) {
	scanner := bufio.NewScanner(r)
	scanner.Buffer(make([]byte, 4096), 1<<20)
	var urls []string
	for scanner.Scan() {
		line := strings.TrimSpace(scanner.Text())
		if line != "" && !strings.HasPrefix(line, "#") {
			urls = append(urls, line)
		}
	}
	if err := scanner.Err(); err != nil {
		return nil, err
	}
	return urls, nil
}
