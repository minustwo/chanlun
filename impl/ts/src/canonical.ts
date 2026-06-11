// Python-compatible canonical JSON serializer.
//
// Mirrors json.dumps(obj, sort_keys=True, separators=(',', ':'), ensure_ascii=True)
// from the Python stdlib - the format the chanlun-v1 corpus is hashed against.
//
// Rules:
//   * objects are emitted with keys sorted in lexicographic (UTF-16 code unit) order
//     - matches Python's str comparison for ASCII keys, which is what the corpus uses.
//   * separators are exactly ',' and ':' (no whitespace).
//   * non-ASCII characters are escaped as \uXXXX (or surrogate pairs above U+FFFF).
//   * the standard JSON escapes apply to " \\ \b \f \n \r \t and other C0 controls.
//   * integers are emitted as integers (no trailing .0). All fixture numbers are integers.
//   * arrays preserve insertion order.
//   * undefined, functions, BigInt, etc. trigger an error - the corpus never uses them.

function escapeString(s: string): string {
  let out = '"';
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    if (c === 0x22) {
      out += '\\"';
    } else if (c === 0x5c) {
      out += "\\\\";
    } else if (c === 0x08) {
      out += "\\b";
    } else if (c === 0x09) {
      out += "\\t";
    } else if (c === 0x0a) {
      out += "\\n";
    } else if (c === 0x0c) {
      out += "\\f";
    } else if (c === 0x0d) {
      out += "\\r";
    } else if (c < 0x20) {
      // other C0 controls
      out += "\\u" + c.toString(16).padStart(4, "0");
    } else if (c < 0x7f) {
      // printable ASCII (excluding DEL)
      out += s[i];
    } else {
      // non-ASCII -> \uXXXX (surrogate pairs are emitted as two \uXXXX escapes,
      // exactly as Python's json with ensure_ascii=True does).
      out += "\\u" + c.toString(16).padStart(4, "0");
    }
  }
  out += '"';
  return out;
}

function canonNumber(n: number): string {
  if (!Number.isFinite(n)) {
    throw new Error(`canonical-json: non-finite number ${n} not allowed`);
  }
  if (Number.isInteger(n)) {
    // Python integer literal: no decimal point.
    // JS toString already does this for safe integers.
    return n.toString();
  }
  // Floats are not used by the chanlun-v1 corpus; emit a guarded error.
  throw new Error(
    `canonical-json: non-integer ${n} not supported (corpus is integer-core)`
  );
}

export function canonical(value: unknown): string {
  if (value === null) return "null";
  if (typeof value === "boolean") return value ? "true" : "false";
  if (typeof value === "number") return canonNumber(value);
  if (typeof value === "string") return escapeString(value);
  if (Array.isArray(value)) {
    const parts = value.map((v) => canonical(v));
    return "[" + parts.join(",") + "]";
  }
  if (typeof value === "object") {
    const obj = value as Record<string, unknown>;
    const keys = Object.keys(obj).sort();
    const parts: string[] = [];
    for (const k of keys) {
      parts.push(escapeString(k) + ":" + canonical(obj[k]));
    }
    return "{" + parts.join(",") + "}";
  }
  throw new Error(`canonical-json: unsupported value type ${typeof value}`);
}

export function canonicalBytes(value: unknown): Uint8Array {
  return new TextEncoder().encode(canonical(value));
}
