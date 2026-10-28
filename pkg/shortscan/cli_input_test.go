package shortscan

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

func TestInputFailurePreservesOutput(t *testing.T) {
	if os.Getenv("SHORTSCAN_TEST_INPUT_CHILD") == "1" {
		for i, value := range os.Args {
			if value == "--" {
				os.Args = append([]string{"shortscan"}, os.Args[i+1:]...)
				break
			}
		}
		Run()
		return
	}
	dir := t.TempDir()
	empty := filepath.Join(dir, "empty.txt")
	oversized := filepath.Join(dir, "oversized.txt")
	if err := os.WriteFile(empty, nil, 0600); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(oversized, []byte(strings.Repeat("x", 1<<20)), 0600); err != nil {
		t.Fatal(err)
	}
	for _, tc := range []struct {
		name  string
		input []string
	}{
		{"no targets", nil},
		{"missing list", []string{"--list", filepath.Join(dir, "missing.txt")}},
		{"empty list", []string{"--list", empty}},
		{"unreadable line", []string{"--list", oversized}},
		{"missing inline file", []string{"@" + filepath.Join(dir, "missing.txt")}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			output := filepath.Join(dir, "results.txt")
			candidates := filepath.Join(dir, "candidates.txt")
			const sentinel = "previous scan results\n"
			for _, path := range []string{output, candidates} {
				if err := os.WriteFile(path, []byte(sentinel), 0600); err != nil {
					t.Fatal(err)
				}
			}
			argv := []string{"-test.run=^TestInputFailurePreservesOutput$", "--", "--output-file", output, "--candidate-output", candidates}
			cmd := exec.Command(os.Args[0], append(argv, tc.input...)...)
			cmd.Env = append(os.Environ(), "SHORTSCAN_TEST_INPUT_CHILD=1")
			if text, err := cmd.CombinedOutput(); err == nil {
				t.Fatalf("invalid input accepted: %s", text)
			}
			for _, path := range []string{output, candidates} {
				got, err := os.ReadFile(path)
				if err != nil || string(got) != sentinel {
					t.Fatalf("output overwritten: %s, %q, %v", path, got, err)
				}
			}
		})
	}
}
