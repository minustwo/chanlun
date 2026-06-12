// Check.java — Java conformance harness for the chanlun-v1 frozen corpus.
//
// Mirrors conformance/chanlun-v1/example_phase3_check.py + impl/go/cmd/check/main.go:
//   1. Load conformance/chanlun-v1/manifest.json.
//   2. For each entry, load the fixture JSON, invoke the Java backend on `input`,
//      canonicalize the output via our canonical-JSON emitter
//      (sort_keys=True, separators=(",",":"), ensure_ascii=True — matching
//      Python json.dumps byte-for-byte), and compare SHA-256 against the entry.
//   3. Exit non-zero on ANY divergence.
//
// SHA-equality is the law. A byte off = FAIL. No fuzzy comparison, no float
// tolerance (the chanlun-v1 corpus is integer-core).
package com.minustwo.chanlun.check;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

import com.minustwo.chanlun.Canonical;
import com.minustwo.chanlun.Pipeline;
import com.minustwo.chanlun.Types.OrderedObject;
import com.minustwo.chanlun.Types.Value;

public final class Check {

    private Check() {}

    public static void main(String[] args) {
        try {
            int code = run();
            System.exit(code);
        } catch (Exception e) {
            System.err.println("FAIL: " + e.getClass().getSimpleName() + ": " + e.getMessage());
            e.printStackTrace(System.err);
            System.exit(1);
        }
    }

    private static int run() throws IOException {
        Path manifestPath = locateManifest();
        byte[] manifestBytes = Files.readAllBytes(manifestPath);
        Value manV = Canonical.decode(manifestBytes);
        OrderedObject manObj = manV.mustObj();
        List<Value> entries = manObj.get("entries").mustArr();
        String corpusSha = manObj.get("corpus_sha256").mustStr();
        long count = manObj.get("count").mustInt();

        System.out.println("chanlun-v1 Java conformance check: " + count + " fixtures");
        System.out.println("  corpus_sha256 = " + corpusSha);

        // Corpus-level sanity: SHA-256(canonical([fixture_sha256 for each entry])).
        List<Value> fxs = new ArrayList<>(entries.size());
        for (Value e : entries) {
            fxs.add(Value.ofString(e.mustObj().get("fixture_sha256").mustStr()));
        }
        String recomputedCorpus = Canonical.sha256Hex(Canonical.canonical(Value.ofArray(fxs)));
        if (!recomputedCorpus.equals(corpusSha)) {
            System.err.println("FAIL: corpus_sha256 mismatch: manifest=" + corpusSha
                + " recomputed=" + recomputedCorpus);
            return 1;
        }

        Path manifestDir = manifestPath.getParent();
        int pass = 0, fail = 0;
        for (Value e : entries) {
            OrderedObject eo = e.mustObj();
            String id = eo.get("id").mustStr();
            String stage = eo.get("stage").mustStr();
            String file = eo.get("file").mustStr();
            String inShaExp = eo.get("input_sha256").mustStr();
            String expShaExp = eo.get("expected_sha256").mustStr();
            String fixShaExp = eo.get("fixture_sha256").mustStr();

            Path fxPath = manifestDir.resolve(file);
            byte[] fxBytes;
            try {
                fxBytes = Files.readAllBytes(fxPath);
            } catch (IOException ex) {
                fail++;
                System.out.printf("  [FAIL] %-60s  read fixture: %s%n", id, ex.getMessage());
                continue;
            }

            Value fxV;
            try {
                fxV = Canonical.decode(fxBytes);
            } catch (RuntimeException ex) {
                fail++;
                System.out.printf("  [FAIL] %-60s  decode fixture: %s%n", id, ex.getMessage());
                continue;
            }
            OrderedObject fo = fxV.mustObj();
            Value inputV = fo.get("input");
            Value expectedV = fo.get("expected");

            byte[] inCanon = Canonical.canonical(inputV);
            String inSha = Canonical.sha256Hex(inCanon);
            if (!inSha.equals(inShaExp)) {
                fail++;
                System.out.printf("  [FAIL] %-60s  input_sha256: manifest=%s got=%s%n",
                    id, inShaExp, inSha);
                continue;
            }

            Value actualV;
            try {
                actualV = Pipeline.runStage(stage, inputV);
            } catch (RuntimeException ex) {
                fail++;
                System.out.printf("  [FAIL] %-60s  backend: %s%n", id, ex.getMessage());
                continue;
            }
            byte[] expCanon = Canonical.canonical(expectedV);
            byte[] actCanon = Canonical.canonical(actualV);
            String expSha = Canonical.sha256Hex(expCanon);
            String actSha = Canonical.sha256Hex(actCanon);
            if (!expSha.equals(expShaExp)) {
                fail++;
                System.out.printf("  [FAIL] %-60s  expected_sha256: manifest=%s recomputed=%s%n",
                    id, expShaExp, expSha);
                continue;
            }
            if (!actSha.equals(expSha)) {
                fail++;
                System.out.printf("  [FAIL] %-60s  actual sha=%s expected sha=%s%n",
                    id, actSha, expSha);
                System.out.println("           expected canon=" + new String(expCanon));
                System.out.println("           actual   canon=" + new String(actCanon));
                continue;
            }
            // fixture_sha = sha256(in_canon + "|" + exp_canon)
            byte[] joined = new byte[inCanon.length + 1 + expCanon.length];
            System.arraycopy(inCanon, 0, joined, 0, inCanon.length);
            joined[inCanon.length] = (byte) '|';
            System.arraycopy(expCanon, 0, joined, inCanon.length + 1, expCanon.length);
            String fxSha = Canonical.sha256Hex(joined);
            if (!fxSha.equals(fixShaExp)) {
                fail++;
                System.out.printf("  [FAIL] %-60s  fixture_sha256: manifest=%s recomputed=%s%n",
                    id, fixShaExp, fxSha);
                continue;
            }
            pass++;
        }

        System.out.println();
        System.out.printf("Result: %d PASS, %d FAIL%n", pass, fail);
        if (fail > 0) {
            System.err.println("conformance FAILED: " + fail
                + " divergence(s) — any byte-level mismatch breaks the FROZEN spec");
            return 1;
        }
        System.out.println("Conformance OK. All fixtures match the chanlun-v1 frozen spec byte-for-byte.");
        return 0;
    }

    /** Walk up from CWD looking for conformance/chanlun-v1/manifest.json so the
     *  harness works whether invoked from impl/java or from the repo root. */
    private static Path locateManifest() {
        Path dir = Paths.get("").toAbsolutePath();
        while (dir != null) {
            Path cand = dir.resolve("conformance").resolve("chanlun-v1").resolve("manifest.json");
            if (Files.exists(cand)) return cand;
            dir = dir.getParent();
        }
        throw new IllegalStateException(
            "could not locate conformance/chanlun-v1/manifest.json from " + Paths.get("").toAbsolutePath());
    }
}
