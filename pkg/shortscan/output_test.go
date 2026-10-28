package shortscan

import (
	"bytes"
	"encoding/csv"
	"strings"
	"testing"
)

func TestCSVRoundTripSpecialCharacters(t *testing.T) {
	previousArgs, previousWriter, previousHeader := args, outputWriter, csvHeaderPrinted
	defer func() { args, outputWriter, csvHeaderPrinted = previousArgs, previousWriter, previousHeader }()
	args = arguments{Output: "csv"}
	var output bytes.Buffer
	outputWriter = &output
	csvHeaderPrinted = false
	values := []string{"plain", "a,b", `a"b`, `C:\data\file`, "two\nlines", " leading space", "ação — arquivo", ""}
	for _, value := range values {
		printJSON(resultOutput{Type: "result", Fullname: value, SensitiveReason: value})
	}
	rows, err := csv.NewReader(strings.NewReader(output.String())).ReadAll()
	if err != nil {
		t.Fatalf("invalid CSV: %v\n%s", err, output.String())
	}
	if len(rows) != len(values)+1 {
		t.Fatalf("got %d rows", len(rows))
	}
	for i, value := range values {
		if rows[i+1][10] != value || rows[i+1][26] != value {
			t.Errorf("row %d: fullname=%q reason=%q; want %q", i, rows[i+1][10], rows[i+1][26], value)
		}
	}
}
