package shortscan

import (
	"errors"
	"io"
	"reflect"
	"strings"
	"testing"
)

type failedURLReader struct{}

func (failedURLReader) Read([]byte) (int, error) { return 0, io.ErrUnexpectedEOF }

func TestReadURLList(t *testing.T) {
	urls, err := readURLList(strings.NewReader(" # comment\r\n\n https://example.test/a \r\nhttps://example.test/b#part\n"))
	if err != nil || !reflect.DeepEqual(urls, []string{"https://example.test/a", "https://example.test/b#part"}) {
		t.Fatalf("urls=%v err=%v", urls, err)
	}
}

func TestReadURLListRejectsPartialInput(t *testing.T) {
	urls, err := readURLList(io.MultiReader(strings.NewReader("https://example.test/\n"), failedURLReader{}))
	if !errors.Is(err, io.ErrUnexpectedEOF) || urls != nil {
		t.Fatalf("partial list accepted: urls=%v err=%v", urls, err)
	}
	urls, err = readURLList(strings.NewReader("https://example.test/\n" + strings.Repeat("x", 1<<20)))
	if err == nil || urls != nil {
		t.Fatal("oversized input must fail without returning partial targets")
	}
}
