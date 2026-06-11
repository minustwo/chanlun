package chanlun

import (
	"bytes"
	"encoding/json"
	"fmt"
)

// DecodeJSON parses JSON bytes into our typed Value tree. Uses json.Decoder
// with UseNumber so integer-vs-float distinction is preserved. The chanlun-v1
// corpus is integer-core, so a float anywhere in input is an error and we
// surface it (rather than silently converting).
func DecodeJSON(b []byte) (Value, error) {
	dec := json.NewDecoder(bytes.NewReader(b))
	dec.UseNumber()
	var raw any
	if err := dec.Decode(&raw); err != nil {
		return Value{}, fmt.Errorf("DecodeJSON: %w", err)
	}
	return convertRaw(raw)
}

func convertRaw(x any) (Value, error) {
	switch v := x.(type) {
	case nil:
		return Value{kind: kNull}, nil
	case bool:
		if v {
			return Value{kind: kBool, i: 1}, nil
		}
		return Value{kind: kBool, i: 0}, nil
	case string:
		return VStr(v), nil
	case json.Number:
		// Try integer first; reject if it has a fractional part (chanlun-v1 is
		// integer-core; a float would be a NAMED residue and we don't silently
		// downconvert).
		s := string(v)
		for _, c := range s {
			if c == '.' || c == 'e' || c == 'E' {
				return Value{}, fmt.Errorf("DecodeJSON: chanlun-v1 corpus is integer-core; refusing to parse non-integer number %q", s)
			}
		}
		n, err := v.Int64()
		if err != nil {
			return Value{}, fmt.Errorf("DecodeJSON: integer parse %q: %w", s, err)
		}
		return VInt(n), nil
	case []any:
		out := make([]Value, len(v))
		for i, e := range v {
			ev, err := convertRaw(e)
			if err != nil {
				return Value{}, err
			}
			out[i] = ev
		}
		return VArr(out), nil
	case map[string]any:
		o := NewObject()
		for k, e := range v {
			ev, err := convertRaw(e)
			if err != nil {
				return Value{}, err
			}
			o.Set(k, ev)
		}
		return VObj(o), nil
	default:
		return Value{}, fmt.Errorf("DecodeJSON: unsupported type %T", x)
	}
}

// MustObj returns o.obj or panics; used for hand-written stage drivers where
// we already validated shape.
func (v Value) MustObj() *Object {
	if v.kind != kObject {
		panic(fmt.Sprintf("MustObj: not an object (kind=%d)", v.kind))
	}
	return v.obj
}

// MustArr returns the underlying slice (no copy).
func (v Value) MustArr() []Value {
	if v.kind != kArray {
		panic(fmt.Sprintf("MustArr: not an array (kind=%d)", v.kind))
	}
	return v.arr
}

// MustInt returns the int64 payload.
func (v Value) MustInt() int64 {
	if v.kind != kInt {
		panic(fmt.Sprintf("MustInt: not an int (kind=%d)", v.kind))
	}
	return v.i
}

// MustStr returns the string payload.
func (v Value) MustStr() string {
	if v.kind != kString {
		panic(fmt.Sprintf("MustStr: not a string (kind=%d)", v.kind))
	}
	return v.s
}

// Kind returns the value kind name (for debug only).
func (v Value) Kind() string {
	switch v.kind {
	case kNull:
		return "null"
	case kBool:
		return "bool"
	case kInt:
		return "int"
	case kString:
		return "string"
	case kArray:
		return "array"
	case kObject:
		return "object"
	}
	return "?"
}
