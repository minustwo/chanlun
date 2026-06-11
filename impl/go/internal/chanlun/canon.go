// Package chanlun implements a faithful Go port of the chanlun-v1 Python reference backend.
//
// This file: canonical JSON encoder + SHA-256, matching Python's
//
//	json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
//
// byte-for-byte over the integer/string domain used by the chanlun-v1 corpus.
//
// The Go stdlib encoding/json does NOT sort keys and uses different whitespace
// defaults; reproducing Python's canonical bytes requires a custom emitter.
// We deliberately use ordered intermediate values rather than map[string]any
// so the SHA-256 inputs are reproducible across Go versions and architectures.
package chanlun

import (
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"sort"
	"strconv"
	"strings"
	"unicode/utf16"
)

// Value is the typed JSON value tree we work with. We deliberately distinguish
// int from float (the fixtures use only ints, but we want Python semantics).
type Value struct {
	kind valKind
	i    int64
	s    string
	arr  []Value
	obj  *Object // ordered for emit determinism even before canonical sort
}

type valKind int

const (
	kNull valKind = iota
	kBool
	kInt
	kString
	kArray
	kObject
)

// Object is an insertion-ordered string -> Value map. The canonical emitter
// re-sorts keys lexicographically (UTF-8 byte order).
type Object struct {
	keys []string
	vals []Value
	idx  map[string]int
}

// NewObject returns an empty insertion-ordered object.
func NewObject() *Object {
	return &Object{idx: make(map[string]int)}
}

// Set adds (or replaces) the key.
func (o *Object) Set(k string, v Value) {
	if i, ok := o.idx[k]; ok {
		o.vals[i] = v
		return
	}
	o.idx[k] = len(o.keys)
	o.keys = append(o.keys, k)
	o.vals = append(o.vals, v)
}

// Get returns the value and a present-bool.
func (o *Object) Get(k string) (Value, bool) {
	i, ok := o.idx[k]
	if !ok {
		return Value{}, false
	}
	return o.vals[i], true
}

// Len returns the number of keys.
func (o *Object) Len() int { return len(o.keys) }

// Keys returns the keys in insertion order.
func (o *Object) Keys() []string {
	out := make([]string, len(o.keys))
	copy(out, o.keys)
	return out
}

// Helpers ---------------------------------------------------------------------

// VInt wraps an int64.
func VInt(n int64) Value { return Value{kind: kInt, i: n} }

// VStr wraps a string.
func VStr(s string) Value { return Value{kind: kString, s: s} }

// VArr wraps a slice of Values.
func VArr(vs []Value) Value { return Value{kind: kArray, arr: vs} }

// VObj wraps an *Object.
func VObj(o *Object) Value { return Value{kind: kObject, obj: o} }

// Canonical returns the canonical JSON bytes (sorted keys, no whitespace,
// ensure_ascii=True).
func Canonical(v Value) []byte {
	var sb strings.Builder
	writeCanonical(&sb, v)
	return []byte(sb.String())
}

// SHA256Hex computes hex(sha256(b)).
func SHA256Hex(b []byte) string {
	sum := sha256.Sum256(b)
	return hex.EncodeToString(sum[:])
}

func writeCanonical(sb *strings.Builder, v Value) {
	switch v.kind {
	case kNull:
		sb.WriteString("null")
	case kBool:
		if v.i != 0 {
			sb.WriteString("true")
		} else {
			sb.WriteString("false")
		}
	case kInt:
		sb.WriteString(strconv.FormatInt(v.i, 10))
	case kString:
		writeCanonicalString(sb, v.s)
	case kArray:
		sb.WriteByte('[')
		for i, e := range v.arr {
			if i > 0 {
				sb.WriteByte(',')
			}
			writeCanonical(sb, e)
		}
		sb.WriteByte(']')
	case kObject:
		sb.WriteByte('{')
		// Python json.dumps sorts on the raw str key (Unicode code-point order
		// for ASCII == lexicographic byte order). All keys in fixtures are ASCII,
		// but we sort by Unicode code-point order to match Python exactly.
		ks := v.obj.Keys()
		sort.Slice(ks, func(i, j int) bool { return ks[i] < ks[j] })
		for i, k := range ks {
			if i > 0 {
				sb.WriteByte(',')
			}
			writeCanonicalString(sb, k)
			sb.WriteByte(':')
			val, _ := v.obj.Get(k)
			writeCanonical(sb, val)
		}
		sb.WriteByte('}')
	default:
		// Unreachable for well-formed values.
		panic(fmt.Sprintf("canon: unknown kind %d", v.kind))
	}
}

// writeCanonicalString writes s as a JSON string matching Python's
// json.dumps(..., ensure_ascii=True) escaping rules.
func writeCanonicalString(sb *strings.Builder, s string) {
	sb.WriteByte('"')
	for _, r := range s {
		switch r {
		case '"':
			sb.WriteString(`\"`)
		case '\\':
			sb.WriteString(`\\`)
		case '\b':
			sb.WriteString(`\b`)
		case '\f':
			sb.WriteString(`\f`)
		case '\n':
			sb.WriteString(`\n`)
		case '\r':
			sb.WriteString(`\r`)
		case '\t':
			sb.WriteString(`\t`)
		default:
			if r < 0x20 {
				fmt.Fprintf(sb, `\u%04x`, r)
			} else if r < 0x7f {
				sb.WriteRune(r)
			} else {
				// ensure_ascii=True: escape everything >= 0x7f via \uXXXX, using
				// UTF-16 surrogate pairs for code points beyond the BMP.
				if r > 0xffff {
					r1, r2 := utf16.EncodeRune(r)
					fmt.Fprintf(sb, `\u%04x\u%04x`, r1, r2)
				} else {
					fmt.Fprintf(sb, `\u%04x`, r)
				}
			}
		}
	}
	sb.WriteByte('"')
}
