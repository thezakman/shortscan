// shortloot deep-dumps a .NET assembly recovered by shortscan's source-disclosure
// chain (App_Web_*.dll, App_Code.*.dll, …) WITHOUT loading it: PDB/build path, every
// identifier name (#Strings) and every string literal (#US). For a compiled ASP.NET
// page the literals include the page's static HTML markup and any hard-coded secrets.
//
//	shortloot App_Web_xxxx.dll                 # summary
//	shortloot --literals App_Web_xxxx.dll      # dump string literals (HTML/secrets)
//	shortloot --names App_Web_xxxx.dll         # dump identifier names
//	shortloot --grep -i pass,conn,secret *.dll # filter across many files
package main

import (
	"encoding/json"
	"fmt"
	"os"
	"strings"

	"github.com/thezakman/shortscan/pkg/dotnetmeta"
)

func main() {
	args := os.Args[1:]
	var files []string
	var showNames, showLits, showAll, asJSON, ci bool
	var greps []string
	for i := 0; i < len(args); i++ {
		switch args[i] {
		case "--names", "-n":
			showNames = true
		case "--literals", "-l":
			showLits = true
		case "--all", "-a":
			showAll = true
		case "--json", "-j":
			asJSON = true
		case "-i":
			ci = true
		case "--grep", "-g":
			if i+1 < len(args) {
				i++
				greps = strings.Split(args[i], ",")
			}
		case "-h", "--help":
			fmt.Fprintln(os.Stderr, "usage: shortloot [--names] [--literals] [--all] [--grep p1,p2] [-i] [--json] FILE...")
			return
		default:
			files = append(files, args[i])
		}
	}
	if len(files) == 0 {
		fmt.Fprintln(os.Stderr, "shortloot: give one or more .NET DLL/EXE files (from shortscan source-disclosure loot)")
		os.Exit(2)
	}
	match := func(s string) bool {
		if len(greps) == 0 {
			return true
		}
		hs := s
		if ci {
			hs = strings.ToLower(s)
		}
		for _, g := range greps {
			if ci {
				g = strings.ToLower(g)
			}
			if g != "" && strings.Contains(hs, g) {
				return true
			}
		}
		return false
	}

	exit := 0
	for _, fn := range files {
		raw, err := os.ReadFile(fn)
		if err != nil {
			fmt.Fprintf(os.Stderr, "%s: %v\n", fn, err)
			exit = 1
			continue
		}
		asm, err := dotnetmeta.Inspect(raw)
		if err != nil {
			fmt.Printf("%s: not a PE (%v)\n", fn, err)
			exit = 1
			continue
		}
		if asJSON {
			b, _ := json.MarshalIndent(asm, "", "  ")
			fmt.Printf("=== %s ===\n%s\n", fn, b)
			continue
		}
		fmt.Printf("=== %s ===\n", fn)
		fmt.Printf("  managed: %v   metadata: %s\n", asm.IsManaged, asm.MetadataVersion)
		if asm.PDBPath != "" {
			fmt.Printf("  PDB/build path: %s\n", asm.PDBPath)
		}
		fmt.Printf("  names: %d   literals: %d\n", len(asm.Names), len(asm.Literals))
		if showNames || showAll {
			fmt.Println("  --- identifier names (#Strings) ---")
			for _, s := range asm.Names {
				if match(s) {
					fmt.Printf("    %s\n", s)
				}
			}
		}
		if showLits || showAll {
			fmt.Println("  --- string literals (#US: page HTML, hard-coded secrets) ---")
			for _, s := range asm.Literals {
				if match(s) {
					fmt.Printf("    %q\n", s)
				}
			}
		}
		if !showNames && !showLits && !showAll && len(greps) > 0 {
			// grep-only mode: surface any match across names+literals
			for _, s := range append(append([]string{}, asm.Names...), asm.Literals...) {
				if match(s) {
					fmt.Printf("    match: %q\n", s)
				}
			}
		}
	}
	os.Exit(exit)
}
