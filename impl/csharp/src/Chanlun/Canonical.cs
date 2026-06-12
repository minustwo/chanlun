// Canonical JSON encoder + SHA-256, matching Python's
//
//     json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
//
// byte-for-byte over the integer/string domain used by the chanlun-v1 corpus.
//
// System.Text.Json does NOT sort keys lexicographically (it preserves
// insertion order) and its escape policy differs from Python's. We therefore
// roll a custom emitter over an ordered typed Value tree (similar to the Go
// port at impl/go/internal/chanlun/canon.go), then SHA-256 the bytes.

using System.Globalization;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;

namespace Chanlun;

public enum ValueKind { Null, Bool, Int, String, Array, Object }

/// <summary>
/// Typed JSON value tree (deliberately distinguishes int from float — the
/// chanlun-v1 corpus is integer-core).
/// </summary>
public sealed class Value
{
    public ValueKind Kind { get; }
    public long IntVal { get; }
    public bool BoolVal { get; }
    public string StrVal { get; }
    public List<Value> ArrVal { get; }
    public OrderedObject ObjVal { get; }

    private Value(
        ValueKind kind,
        long i = 0,
        bool b = false,
        string? s = null,
        List<Value>? a = null,
        OrderedObject? o = null)
    {
        Kind = kind;
        IntVal = i;
        BoolVal = b;
        StrVal = s ?? string.Empty;
        ArrVal = a ?? new List<Value>();
        ObjVal = o ?? new OrderedObject();
    }

    public static Value Null() => new(ValueKind.Null);
    public static Value Of(bool b) => new(ValueKind.Bool, b: b);
    public static Value Of(long n) => new(ValueKind.Int, i: n);
    public static Value Of(string s) => new(ValueKind.String, s: s);
    public static Value Of(List<Value> a) => new(ValueKind.Array, a: a);
    public static Value Of(OrderedObject o) => new(ValueKind.Object, o: o);

    public List<Value> AsArray()
    {
        if (Kind != ValueKind.Array)
            throw new InvalidOperationException($"AsArray: not an array (kind={Kind})");
        return ArrVal;
    }

    public OrderedObject AsObject()
    {
        if (Kind != ValueKind.Object)
            throw new InvalidOperationException($"AsObject: not an object (kind={Kind})");
        return ObjVal;
    }

    public long AsInt()
    {
        if (Kind != ValueKind.Int)
            throw new InvalidOperationException($"AsInt: not an int (kind={Kind})");
        return IntVal;
    }

    public string AsString()
    {
        if (Kind != ValueKind.String)
            throw new InvalidOperationException($"AsString: not a string (kind={Kind})");
        return StrVal;
    }
}

/// <summary>
/// Insertion-ordered string->Value map. Canonical emit re-sorts keys.
/// </summary>
public sealed class OrderedObject
{
    private readonly List<string> _keys = new();
    private readonly Dictionary<string, Value> _values = new(StringComparer.Ordinal);

    public void Set(string k, Value v)
    {
        if (!_values.ContainsKey(k))
            _keys.Add(k);
        _values[k] = v;
    }

    public bool TryGet(string k, out Value v) => _values.TryGetValue(k, out v!);

    public Value Get(string k) => _values[k];

    public IReadOnlyList<string> Keys => _keys;

    public int Count => _keys.Count;
}

public static class Canonical
{
    /// <summary>
    /// Canonical JSON bytes used for ALL SHA-256 computation. Matches Python
    /// json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    /// byte-for-byte.
    /// </summary>
    public static byte[] Encode(Value v)
    {
        var sb = new StringBuilder();
        Write(sb, v);
        return Encoding.UTF8.GetBytes(sb.ToString());
    }

    /// <summary>SHA-256 hex digest (lowercase) over `b`.</summary>
    public static string Sha256Hex(byte[] b)
    {
        var sum = SHA256.HashData(b);
        var s = new StringBuilder(sum.Length * 2);
        foreach (var x in sum)
            s.Append(x.ToString("x2", CultureInfo.InvariantCulture));
        return s.ToString();
    }

    private static void Write(StringBuilder sb, Value v)
    {
        switch (v.Kind)
        {
            case ValueKind.Null:
                sb.Append("null");
                break;
            case ValueKind.Bool:
                sb.Append(v.BoolVal ? "true" : "false");
                break;
            case ValueKind.Int:
                sb.Append(v.IntVal.ToString(CultureInfo.InvariantCulture));
                break;
            case ValueKind.String:
                WriteString(sb, v.StrVal);
                break;
            case ValueKind.Array:
                sb.Append('[');
                for (int i = 0; i < v.ArrVal.Count; i++)
                {
                    if (i > 0) sb.Append(',');
                    Write(sb, v.ArrVal[i]);
                }
                sb.Append(']');
                break;
            case ValueKind.Object:
                sb.Append('{');
                // Python json.dumps(sort_keys=True) sorts by raw str key. For ASCII
                // (which the chanlun-v1 corpus uses for keys), Unicode code-point
                // order = lexicographic byte order. StringComparer.Ordinal gives
                // that exact ordering.
                var keys = v.ObjVal.Keys.ToList();
                keys.Sort(StringComparer.Ordinal);
                for (int i = 0; i < keys.Count; i++)
                {
                    if (i > 0) sb.Append(',');
                    WriteString(sb, keys[i]);
                    sb.Append(':');
                    Write(sb, v.ObjVal.Get(keys[i]));
                }
                sb.Append('}');
                break;
            default:
                throw new InvalidOperationException($"canon: unknown kind {v.Kind}");
        }
    }

    /// <summary>
    /// Emit `s` as a JSON string matching Python json.dumps(ensure_ascii=True)
    /// escape rules: backslash, quote, b/f/n/r/t shortcuts; control chars and
    /// non-ASCII via \uXXXX (with UTF-16 surrogate pairs for non-BMP).
    /// </summary>
    private static void WriteString(StringBuilder sb, string s)
    {
        sb.Append('"');
        int i = 0;
        while (i < s.Length)
        {
            char c = s[i];
            switch (c)
            {
                case '"': sb.Append("\\\""); i++; continue;
                case '\\': sb.Append("\\\\"); i++; continue;
                case '\b': sb.Append("\\b"); i++; continue;
                case '\f': sb.Append("\\f"); i++; continue;
                case '\n': sb.Append("\\n"); i++; continue;
                case '\r': sb.Append("\\r"); i++; continue;
                case '\t': sb.Append("\\t"); i++; continue;
            }
            if (c < 0x20)
            {
                sb.Append("\\u").Append(((int)c).ToString("x4", CultureInfo.InvariantCulture));
                i++;
                continue;
            }
            if (c < 0x7f)
            {
                sb.Append(c);
                i++;
                continue;
            }
            // ensure_ascii=True path: escape via \uXXXX. C# strings are UTF-16
            // already, so a surrogate pair is two char units — emit both as
            // \uXXXX, exactly like Python json.dumps does.
            if (char.IsHighSurrogate(c) && i + 1 < s.Length && char.IsLowSurrogate(s[i + 1]))
            {
                sb.Append("\\u").Append(((int)c).ToString("x4", CultureInfo.InvariantCulture));
                sb.Append("\\u").Append(((int)s[i + 1]).ToString("x4", CultureInfo.InvariantCulture));
                i += 2;
                continue;
            }
            sb.Append("\\u").Append(((int)c).ToString("x4", CultureInfo.InvariantCulture));
            i++;
        }
        sb.Append('"');
    }

    // -- JSON decode --------------------------------------------------------

    /// <summary>
    /// Parse JSON bytes into a typed Value tree. Uses System.Text.Json under
    /// the hood, but reads numbers strictly as long (the chanlun-v1 corpus is
    /// integer-core; a non-integer number anywhere is an error).
    /// </summary>
    public static Value Decode(byte[] bytes)
    {
        var reader = new Utf8JsonReader(
            bytes,
            new JsonReaderOptions
            {
                CommentHandling = JsonCommentHandling.Disallow,
                AllowTrailingCommas = false,
            });
        reader.Read();
        return ReadValue(ref reader);
    }

    private static Value ReadValue(ref Utf8JsonReader reader)
    {
        switch (reader.TokenType)
        {
            case JsonTokenType.Null:
                return Value.Null();
            case JsonTokenType.True:
                return Value.Of(true);
            case JsonTokenType.False:
                return Value.Of(false);
            case JsonTokenType.Number:
                if (!reader.TryGetInt64(out var n))
                    throw new InvalidOperationException(
                        $"Decode: chanlun-v1 is integer-core; non-integer number at byte {reader.TokenStartIndex}");
                return Value.Of(n);
            case JsonTokenType.String:
                return Value.Of(reader.GetString() ?? string.Empty);
            case JsonTokenType.StartArray:
                {
                    var list = new List<Value>();
                    while (reader.Read() && reader.TokenType != JsonTokenType.EndArray)
                        list.Add(ReadValue(ref reader));
                    return Value.Of(list);
                }
            case JsonTokenType.StartObject:
                {
                    var obj = new OrderedObject();
                    while (reader.Read() && reader.TokenType != JsonTokenType.EndObject)
                    {
                        if (reader.TokenType != JsonTokenType.PropertyName)
                            throw new InvalidOperationException("Decode: expected property name");
                        var key = reader.GetString() ?? string.Empty;
                        reader.Read();
                        obj.Set(key, ReadValue(ref reader));
                    }
                    return Value.Of(obj);
                }
            default:
                throw new InvalidOperationException($"Decode: unsupported token {reader.TokenType}");
        }
    }
}
