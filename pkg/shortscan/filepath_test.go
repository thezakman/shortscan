package shortscan

import (
	"os"
	"path/filepath"
	"testing"
)

func TestSameFilePathThroughDirectorySymlink(t *testing.T) {
	dir := t.TempDir()
	realDir := filepath.Join(dir, "real")
	aliasDir := filepath.Join(dir, "alias")
	if err := os.Mkdir(realDir, 0700); err != nil {
		t.Fatal(err)
	}
	if err := os.Symlink(realDir, aliasDir); err != nil {
		t.Skipf("symlinks unavailable: %v", err)
	}
	// Neither file exists: comparing only os.Stat and absolute paths misses this.
	if !sameFilePath(filepath.Join(realDir, "results.csv"), filepath.Join(aliasDir, "results.csv")) {
		t.Fatal("same future output file through a symlink was not detected")
	}
	if sameFilePath(filepath.Join(realDir, "results.csv"), filepath.Join(aliasDir, "candidates.txt")) {
		t.Fatal("distinct output files were treated as equal")
	}
}
