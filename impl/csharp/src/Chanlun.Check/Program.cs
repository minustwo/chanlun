// chanlun-v1 C# conformance harness. Mirrors impl/go/cmd/check/main.go:
//
//  1. Load conformance/chanlun-v1/manifest.json.
//  2. For each entry, load the fixture JSON, invoke the C# backend on `input`,
//     canonicalize via our canonical-JSON encoder (sort_keys=True,
//     separators=(",",":"), ensure_ascii=True — matching Python json.dumps
//     byte-for-byte), and compare SHA-256 against the manifest entry.
//  3. Exit non-zero on ANY divergence.
//
// SHA-equality is the law. A byte off = FAIL. No fuzzy comparison.

using System.Text;
using Chanlun;

static class Program
{
    static int Main(string[] args)
    {
        try
        {
            return Run();
        }
        catch (Exception ex)
        {
            Console.Error.WriteLine($"FAIL: {ex.Message}");
            return 1;
        }
    }

    static int Run()
    {
        var manifestPath = LocateManifest();
        if (manifestPath is null)
        {
            Console.Error.WriteLine("FAIL: could not locate conformance/chanlun-v1/manifest.json");
            return 1;
        }

        var manifestBytes = File.ReadAllBytes(manifestPath);
        var manV = Canonical.Decode(manifestBytes);
        var manObj = manV.AsObject();
        var entries = manObj.Get("entries").AsArray();
        var corpusSha = manObj.Get("corpus_sha256").AsString();
        var count = manObj.Get("count").AsInt();

        Console.WriteLine($"chanlun-v1 C# conformance check: {count} fixtures");
        Console.WriteLine($"  corpus_sha256 = {corpusSha}");

        // Corpus-level sanity: SHA-256(canonical([fixture_sha256 ...])).
        var fxs = new List<Value>(entries.Count);
        foreach (var e in entries)
            fxs.Add(Value.Of(e.AsObject().Get("fixture_sha256").AsString()));
        var got = Canonical.Sha256Hex(Canonical.Encode(Value.Of(fxs)));
        if (got != corpusSha)
        {
            Console.Error.WriteLine(
                $"FAIL: corpus_sha256 mismatch: manifest={corpusSha} recomputed={got}");
            return 1;
        }

        var manifestDir = Path.GetDirectoryName(manifestPath)!;
        int pass = 0, fail = 0;
        foreach (var e in entries)
        {
            var eo = e.AsObject();
            var id = eo.Get("id").AsString();
            var stage = eo.Get("stage").AsString();
            var file = eo.Get("file").AsString();
            var inShaExpected = eo.Get("input_sha256").AsString();
            var expShaExpected = eo.Get("expected_sha256").AsString();
            var fixShaExpected = eo.Get("fixture_sha256").AsString();

            var fxPath = Path.Combine(manifestDir, file);
            byte[] fxBytes;
            try
            {
                fxBytes = File.ReadAllBytes(fxPath);
            }
            catch (Exception ex)
            {
                fail++;
                Console.WriteLine($"  [FAIL] {id,-60}  read fixture: {ex.Message}");
                continue;
            }

            Value fxV;
            try
            {
                fxV = Canonical.Decode(fxBytes);
            }
            catch (Exception ex)
            {
                fail++;
                Console.WriteLine($"  [FAIL] {id,-60}  decode fixture: {ex.Message}");
                continue;
            }

            var fo = fxV.AsObject();
            var inputV = fo.Get("input");
            var expectedV = fo.Get("expected");

            var inCanon = Canonical.Encode(inputV);
            var inSha = Canonical.Sha256Hex(inCanon);
            if (inSha != inShaExpected)
            {
                fail++;
                Console.WriteLine(
                    $"  [FAIL] {id,-60}  input_sha256: manifest={inShaExpected} got={inSha}");
                continue;
            }

            Value actualV;
            try
            {
                actualV = Pipeline.RunStage(stage, inputV);
            }
            catch (Exception ex)
            {
                fail++;
                Console.WriteLine($"  [FAIL] {id,-60}  backend: {ex.Message}");
                continue;
            }

            var expCanon = Canonical.Encode(expectedV);
            var actCanon = Canonical.Encode(actualV);
            var expSha = Canonical.Sha256Hex(expCanon);
            var actSha = Canonical.Sha256Hex(actCanon);

            if (expSha != expShaExpected)
            {
                fail++;
                Console.WriteLine(
                    $"  [FAIL] {id,-60}  expected_sha256: manifest={expShaExpected} recomputed={expSha}");
                continue;
            }
            if (actSha != expSha)
            {
                fail++;
                Console.WriteLine(
                    $"  [FAIL] {id,-60}  actual sha={actSha} expected sha={expSha}");
                Console.WriteLine(
                    $"           expected canon={Encoding.UTF8.GetString(expCanon)}");
                Console.WriteLine(
                    $"           actual   canon={Encoding.UTF8.GetString(actCanon)}");
                continue;
            }

            // fixture_sha = SHA-256(in_canon + "|" + exp_canon)
            var concat = new byte[inCanon.Length + 1 + expCanon.Length];
            Buffer.BlockCopy(inCanon, 0, concat, 0, inCanon.Length);
            concat[inCanon.Length] = (byte)'|';
            Buffer.BlockCopy(expCanon, 0, concat, inCanon.Length + 1, expCanon.Length);
            var fxSha = Canonical.Sha256Hex(concat);
            if (fxSha != fixShaExpected)
            {
                fail++;
                Console.WriteLine(
                    $"  [FAIL] {id,-60}  fixture_sha256: manifest={fixShaExpected} recomputed={fxSha}");
                continue;
            }

            pass++;
        }

        Console.WriteLine();
        Console.WriteLine($"Result: {pass} PASS, {fail} FAIL");
        if (fail > 0)
        {
            Console.Error.WriteLine(
                $"Conformance FAILED: {fail} divergence(s) - any byte-level mismatch breaks the FROZEN spec.");
            return 1;
        }
        Console.WriteLine("Conformance OK. All fixtures match the chanlun-v1 frozen spec byte-for-byte.");
        return 0;
    }

    /// <summary>
    /// Walk up from cwd looking for conformance/chanlun-v1/manifest.json.
    /// </summary>
    static string? LocateManifest()
    {
        var dir = Directory.GetCurrentDirectory();
        while (true)
        {
            var cand = Path.Combine(dir, "conformance", "chanlun-v1", "manifest.json");
            if (File.Exists(cand))
                return cand;
            var parent = Directory.GetParent(dir);
            if (parent is null)
                return null;
            dir = parent.FullName;
        }
    }
}
