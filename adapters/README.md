# Chanlun adapters

Adapters convert outside data into canonical `chanlun-v1` wire shapes. They do
not compute or modify the proven geometry.

Current adapter:

- `canonical_bars.py`: converts raw high/low rows into integer `{l,h}` bars by
  exact decimal scaling.

Adapter rules:

- No float tolerance in canonical data.
- Inexact scale conversion is a refusal, not rounding.
- Adapter output is input to the canonical pipeline; it is not a profile verdict.
- Derived fields such as volume, MACD, exchange symbol, timestamp, or risk data
  may be kept by product code, but they are not part of canonical geometry.

