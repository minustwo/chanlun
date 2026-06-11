// check is the Go conformance harness for the chanlun-v1 frozen corpus.
//
// Mirrors conformance/chanlun-v1/example_phase3_check.py:
//
//  1. Load conformance/chanlun-v1/manifest.json.
//  2. For each entry, load the fixture JSON, invoke the Go backend on `input`,
//     canonicalize the output via our canonical-JSON emitter
//     (sort_keys=True, separators=(",",":"), ensure_ascii=True - matching
//     Python json.dumps byte-for-byte), and compare SHA-256 against the entry.
//  3. Exit non-zero on ANY divergence.
//
// SHA-equality is the law. A byte off = FAIL. No fuzzy comparison, no float
// tolerance (the chanlun-v1 corpus is integer-core).
package main

import (
	"fmt"
	"os"
	"path/filepath"

	chanlun "github.com/minustwo/chanlun/impl/go/internal/chanlun"
)

func main() {
	if err := run(); err != nil {
		fmt.Fprintln(os.Stderr, "FAIL:", err)
		os.Exit(1)
	}
}

func run() error {
	manifestPath, err := locateManifest()
	if err != nil {
		return err
	}
	manifestBytes, err := os.ReadFile(manifestPath)
	if err != nil {
		return fmt.Errorf("read manifest %s: %w", manifestPath, err)
	}
	manV, err := chanlun.DecodeJSON(manifestBytes)
	if err != nil {
		return fmt.Errorf("decode manifest: %w", err)
	}
	manObj := manV.MustObj()
	entriesV, _ := manObj.Get("entries")
	corpusV, _ := manObj.Get("corpus_sha256")
	countV, _ := manObj.Get("count")
	entries := entriesV.MustArr()

	fmt.Printf("chanlun-v1 Go conformance check: %d fixtures\n", countV.MustInt())
	fmt.Printf("  corpus_sha256 = %s\n", corpusV.MustStr())

	// Corpus-level sanity: SHA-256(canonical([fixture_sha256 for each entry])).
	fxs := make([]chanlun.Value, len(entries))
	for i, e := range entries {
		fxV, _ := e.MustObj().Get("fixture_sha256")
		fxs[i] = chanlun.VStr(fxV.MustStr())
	}
	got := chanlun.SHA256Hex(chanlun.Canonical(chanlun.VArr(fxs)))
	if got != corpusV.MustStr() {
		return fmt.Errorf("corpus_sha256 mismatch: manifest=%s recomputed=%s",
			corpusV.MustStr(), got)
	}

	manifestDir := filepath.Dir(manifestPath)
	pass, fail := 0, 0
	for _, e := range entries {
		eo := e.MustObj()
		idV, _ := eo.Get("id")
		stageV, _ := eo.Get("stage")
		fileV, _ := eo.Get("file")
		inSHAV, _ := eo.Get("input_sha256")
		expSHAV, _ := eo.Get("expected_sha256")
		fixSHAV, _ := eo.Get("fixture_sha256")

		id := idV.MustStr()
		stage := stageV.MustStr()
		fxPath := filepath.Join(manifestDir, fileV.MustStr())
		fxBytes, err := os.ReadFile(fxPath)
		if err != nil {
			fail++
			fmt.Printf("  [FAIL] %-60s  read fixture: %v\n", id, err)
			continue
		}
		fxV, err := chanlun.DecodeJSON(fxBytes)
		if err != nil {
			fail++
			fmt.Printf("  [FAIL] %-60s  decode fixture: %v\n", id, err)
			continue
		}
		fo := fxV.MustObj()
		inputV, _ := fo.Get("input")
		expectedV, _ := fo.Get("expected")

		inCanon := chanlun.Canonical(inputV)
		inSHA := chanlun.SHA256Hex(inCanon)
		if inSHA != inSHAV.MustStr() {
			fail++
			fmt.Printf("  [FAIL] %-60s  input_sha256: manifest=%s got=%s\n",
				id, inSHAV.MustStr(), inSHA)
			continue
		}

		actualV, err := chanlun.RunStage(stage, inputV)
		if err != nil {
			fail++
			fmt.Printf("  [FAIL] %-60s  backend: %v\n", id, err)
			continue
		}
		expCanon := chanlun.Canonical(expectedV)
		actCanon := chanlun.Canonical(actualV)
		expSHA := chanlun.SHA256Hex(expCanon)
		actSHA := chanlun.SHA256Hex(actCanon)
		if expSHA != expSHAV.MustStr() {
			fail++
			fmt.Printf("  [FAIL] %-60s  expected_sha256: manifest=%s recomputed=%s\n",
				id, expSHAV.MustStr(), expSHA)
			continue
		}
		if actSHA != expSHA {
			fail++
			fmt.Printf("  [FAIL] %-60s  actual sha=%s expected sha=%s\n",
				id, actSHA, expSHA)
			fmt.Printf("           expected canon=%s\n", string(expCanon))
			fmt.Printf("           actual   canon=%s\n", string(actCanon))
			continue
		}
		fxSHA := chanlun.SHA256Hex(append(append([]byte{}, inCanon...), append([]byte("|"), expCanon...)...))
		if fxSHA != fixSHAV.MustStr() {
			fail++
			fmt.Printf("  [FAIL] %-60s  fixture_sha256: manifest=%s recomputed=%s\n",
				id, fixSHAV.MustStr(), fxSHA)
			continue
		}
		pass++
	}
	fmt.Println()
	fmt.Printf("Result: %d PASS, %d FAIL\n", pass, fail)
	if fail > 0 {
		return fmt.Errorf("conformance FAILED: %d divergence(s) - any byte-level mismatch breaks the FROZEN spec", fail)
	}
	fmt.Println("Conformance OK. All fixtures match the chanlun-v1 frozen spec byte-for-byte.")
	return nil
}

// locateManifest walks up from the current working directory looking for
// conformance/chanlun-v1/manifest.json, so the harness works whether invoked
// from impl/go or from the repo root.
func locateManifest() (string, error) {
	wd, err := os.Getwd()
	if err != nil {
		return "", err
	}
	dir := wd
	for {
		cand := filepath.Join(dir, "conformance", "chanlun-v1", "manifest.json")
		if _, err := os.Stat(cand); err == nil {
			return cand, nil
		}
		parent := filepath.Dir(dir)
		if parent == dir {
			break
		}
		dir = parent
	}
	return "", fmt.Errorf("could not locate conformance/chanlun-v1/manifest.json starting from %s", wd)
}
