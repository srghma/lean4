-- now https://github.com/leanprover/lean4/blob/b4812ae53eea93439ad5dce5a5c26591c31cb697/src/Init/Prelude.lean#L2827-L2832

abbrev Nat.isValidChar (n : Nat) : Prop :=
  Or (LT.lt n 0xd800) (And (LT.lt 0xdfff n) (LT.lt n 0x110000))

--- or

abbrev Nat.isValidChar (n : Nat) : Prop :=
  n < 0xd800 ∨ (0xdfff < n ∧ n < 0x110000)

--- or

/-- The total number of available code points in the Unicode codespace. -/
def codespaceSize : Nat := 0x110000

/-- The highest value a code point can have (U+10FFFF). -/
def maxCodePoint : Nat := 0x10FFFF

/-- The start of the surrogate block (U+D800). -/
def minSurrogate : Nat := 0xD800

/-- The end of the surrogate block (U+DFFF). -/
def maxSurrogate : Nat := 0xDFFF

abbrev Nat.isValidChar (n : Nat) : Prop :=
  n < minSurrogate ∨ (maxSurrogate < n ∧ n < codespaceSize)

---- or

/-- 
  A Nat is a valid Char if it is either:
  1. Below the surrogate range.
  2. Above the surrogate range AND within the maximum Unicode bound.
-/
abbrev Nat.isValidChar (n : Nat) : Prop :=
  n < minSurrogate ∨ (n > maxSurrogate ∧ n ≤ maxCodePoint)

-------------

/- 
Min UInt32 : 0x00000000 -- valid char
.... -- valid chars
minSurrogate 0xd800 -- invalid char
.... -- invalid chars
maxSurrogate 0xdfff -- invalid char
.... -- valid chars
Max Unicode 0x0010FFFF (only about 1.1 million) -- max valid char
codespaceSize 0x00110000 -- First Invalid char (Out of Range)
.... -- invalid chars
Max UInt32 0xFFFFFFFF (over 4 billion) -- invalid char
-/

-- ###########################################
-- PROPOSAL

namespace Unicode

/-! ### Constants: The "Source of Truth" -/

/-- The highest possible value in the Unicode codespace. -/
public abbrev maxCodePoint : UInt32 := 0x10FFFF

/-- The size of a Unicode Plane (65,536 codepoints). -/
public abbrev planeSize : UInt32 := 0x10000

-- Surrogate Boundaries
public abbrev minHighSurrogate : UInt32 := 0xD800
public abbrev maxHighSurrogate : UInt32 := 0xDBFF
public abbrev minLowSurrogate  : UInt32 := 0xDC00
public abbrev maxLowSurrogate  : UInt32 := 0xDFFF

-- Noncharacter Boundaries (The FDD0..FDEF block)
public abbrev minReservedNoncharacter : UInt32 := 0xFDD0
public abbrev maxReservedNoncharacter : UInt32 := 0xFDEF

-- Noncharacter Suffixes (The last two positions of every plane)
public abbrev noncharacterSuffix1 : UInt32 := 0xFFFE
public abbrev noncharacterSuffix2 : UInt32 := 0xFFFF

/-! ### Predicates: Logic using Constants -/

/-- A high-surrogate code point (used in UTF-16). -/
def isHighSurrogate (v : UInt32) : Prop := 
  minHighSurrogate ≤ v ∧ v ≤ maxHighSurrogate

/-- A low-surrogate code point (used in UTF-16). -/
def isLowSurrogate (v : UInt32) : Prop := 
  minLowSurrogate ≤ v ∧ v ≤ maxLowSurrogate

/-- Any surrogate code point. These are not valid as standalone characters. -/
def isSurrogate (v : UInt32) : Prop :=
  isHighSurrogate v ∨ isLowSurrogate v

/-- 
  A "Scalar Value" is the official Unicode term for a value that can 
  be represented as a Lean `Char`. 
-/
def isScalarValue (v : UInt32) : Prop :=
  v ≤ maxCodePoint ∧ ¬isSurrogate v

/-- 
  Noncharacters are code points permanently reserved for internal use.
  They are "valid" code points but should not be used in interchange.
-/
def isNoncharacter (v : UInt32) : Prop :=
  let planeOffset := v % planeSize
  (minReservedNoncharacter ≤ v ∧ v ≤ maxReservedNoncharacter) ∨ 
  (planeOffset = noncharacterSuffix1) ∨ 
  (planeOffset = noncharacterSuffix2)

/-- 
  The most restrictive definition of a "valid" character:
  1. Must be a Scalar Value (no surrogates).
  2. Must not be a Noncharacter.
-/
def isValidChar (v : UInt32) : Prop :=
  isScalarValue v ∧ ¬isNoncharacter v

end Unicode

/-
import React, { useMemo } from 'react';

// --- Constants & Logic (Equivalent to the Lean Implementation) ---
const MAX_CODEPOINT = 0x10FFFF;
const PLANE_SIZE = 0x10000;
const MIN_HIGH_SURROGATE = 0xD800;
const MAX_HIGH_SURROGATE = 0xDBFF;
const MIN_LOW_SURROGATE = 0xDC00;
const MAX_LOW_SURROGATE = 0xDFFF;
const MIN_RESERVED_NONCHAR = 0xFDD0;
const MAX_RESERVED_NONCHAR = 0xFDEF;
const SUFFIX1 = 0xFFFE;
const SUFFIX2 = 0xFFFF;

const isSurrogate = (v) => v >= MIN_HIGH_SURROGATE && v <= MAX_LOW_SURROGATE;
const isScalarValue = (v) => v <= MAX_CODEPOINT && !isSurrogate(v);
const isNoncharacter = (v) => {
  const offset = v % PLANE_SIZE;
  return (v >= MIN_RESERVED_NONCHAR && v <= MAX_RESERVED_NONCHAR) || 
         offset === SUFFIX1 || offset === SUFFIX2;
};
const isValidStrict = (v) => isScalarValue(v) && !isNoncharacter(v);

const toHex = (v) => `0x${v.toString(16).toUpperCase().padStart(8, '0')}`;

const UnicodeMapApp = () => {
  const rows = useMemo(() => {
    const data = [];

    // 1. Start to Surrogates
    data.push({ range: [0, 0xD7FF], desc: "Basic Multilingual Plane (Start)", type: 'valid' });

    // 2. High Surrogates
    data.push({ range: [MIN_HIGH_SURROGATE, MAX_HIGH_SURROGATE], desc: "High Surrogates (UTF-16)", constant: "minHighSurrogate - maxHighSurrogate", type: 'invalid' });
    
    // 3. Low Surrogates
    data.push({ range: [MIN_LOW_SURROGATE, MAX_LOW_SURROGATE], desc: "Low Surrogates (UTF-16)", constant: "minLowSurrogate - maxLowSurrogate", type: 'invalid' });

    // 4. Post-surrogates to Nonchar block
    data.push({ range: [0xE000, 0xFDCF], desc: "Basic Multilingual Plane (Cont.)", type: 'valid' });

    // 5. THE 66 HOLES - Part 1: The Reserved Block (32 holes)
    for (let i = MIN_RESERVED_NONCHAR; i <= MAX_RESERVED_NONCHAR; i++) {
      data.push({ 
        val: i, 
        desc: `Noncharacter Hole #${i - MIN_RESERVED_NONCHAR + 1}`, 
        constant: i === MIN_RESERVED_NONCHAR ? "minReservedNoncharacter" : i === MAX_RESERVED_NONCHAR ? "maxReservedNoncharacter" : "",
        type: 'nonchar' 
      });
    }

    // 6. Between Block and Suffixes
    data.push({ range: [0xFDF0, 0xFFFD], desc: "BMP Gap", type: 'valid' });

    // 7. THE 66 HOLES - Part 2: Suffixes across all 17 planes (34 holes)
    let holeCount = 33;
    for (let p = 0; p <= 16; p++) {
      const base = p * PLANE_SIZE;
      const s1 = base + SUFFIX1;
      const s2 = base + SUFFIX2;

      data.push({ val: s1, desc: `Noncharacter Hole #${holeCount++} (Plane ${p} Suffix)`, constant: "noncharacterSuffix1", type: 'nonchar' });
      data.push({ val: s2, desc: `Noncharacter Hole #${holeCount++} (Plane ${p} Suffix)`, constant: "noncharacterSuffix2", type: 'nonchar' });

      // Range between this plane's suffix and next plane's suffix
      const nextPlaneStart = (p + 1) * PLANE_SIZE;
      if (nextPlaneStart <= MAX_CODEPOINT) {
        data.push({ range: [s2 + 1, nextPlaneStart + SUFFIX1 - 1], desc: `Plane ${p+1} Content`, type: 'valid' });
      }
    }

    // 8. The End of Unicode
    data.push({ val: MAX_CODEPOINT, desc: "Last Possible Unicode Codepoint", constant: "maxCodePoint", type: 'valid' });
    data.push({ range: [MAX_CODEPOINT + 1, 0xFFFFFFFF], desc: "Out of Range (Junk Space)", type: 'out' });

    return data;
  }, []);

  return (
    <div style={{ padding: '20px', fontFamily: 'monospace', backgroundColor: '#1a1a1a', color: '#e0e0e0', minHeight: '100vh' }}>
      <h1>Unicode UInt32 Map & The 66 Holes</h1>
      <p>Comparing Lean Core <code>isScalarValue</code> vs Strict <code>isValidChar</code></p>
      
      <table style={{ width: '100%', borderCollapse: 'collapse', fontSize: '12px' }}>
        <thead>
          <tr style={{ borderBottom: '2px solid #555', textAlign: 'left' }}>
            <th style={pStyle}>Hex Value / Range</th>
            <th style={pStyle}>Constant / Description</th>
            <th style={pStyle}>Scalar (Lean)</th>
            <th style={pStyle}>Strict (Unicode)</th>
          </tr>
        </thead>
        <tbody>
          {rows.map((row, idx) => {
            const sample = row.val !== undefined ? row.val : row.range[0];
            const scalar = isScalarValue(sample);
            const strict = isValidStrict(sample);
            
            let bgColor = '#222';
            if (row.type === 'invalid') bgColor = '#441111';
            if (row.type === 'nonchar') bgColor = '#444411';
            if (row.type === 'out') bgColor = '#331133';

            return (
              <tr key={idx} style={{ backgroundColor: bgColor, borderBottom: '1px solid #333' }}>
                <td style={pStyle}>
                  {row.val !== undefined ? toHex(row.val) : `${toHex(row.range[0])} - ${toHex(row.range[1])}`}
                </td>
                <td style={pStyle}>
                  <span style={{ color: '#aaa', fontWeight: 'bold' }}>{row.constant}</span> {row.desc}
                </td>
                <td style={{ ...pStyle, color: scalar ? '#00ff00' : '#ff4444' }}>
                  {scalar ? '✅ Valid' : '❌ Invalid'}
                </td>
                <td style={{ ...pStyle, color: strict ? '#00ff00' : '#ff4444' }}>
                  {strict ? '✅ Valid' : '❌ Invalid'}
                </td>
              </tr>
            );
          })}
        </tbody>
      </table>
    </div>
  );
};

const pStyle = { padding: '8px', borderRight: '1px solid #333' };

export default UnicodeMapApp;
-/

-- ######################################################
/-
no


Short answer: **Lean's `isValidChar` is correct and complete.** It's not missing anything — and the "Strict (Unicode)" column in your app is actually the one that's mislabeled, not Lean's.

Here's the distinction that matters:

**"Valid scalar value" and "noncharacter" are not opposites.** The Unicode Standard's own formal definition (D76, §3.9) says: "D76 Unicode scalar value: Any Unicode code point except high-surrogate and low-surrogate code points." That's it. Surrogates are the only thing excluded. Lean's `Or (n < 0xD800) (And (0xDFFF < n) (n < 0x110000))` is exactly that set — the ranges `[0, 0xD7FF]` and `[0xE000, 0x10FFFF]` — expressed as an arithmetic predicate.

Noncharacters (the 32 in FDD0–FDEF, plus the 2-per-plane FFFE/FFFF × 17) are a *separate code point type* from surrogates. The standard's own type taxonomy (D10a) lists seven code point types, and specifically singles out "Surrogate", "Control", and "Noncharacter" as types "assigned to entities that are not actually characters or whose value as Unicode characters in text fields is questionable" — but "questionable as text content" is not "invalid as a scalar value." Noncharacters have well-defined UTF-8/16/32 encodings, they round-trip fine, and they are legal to store, transmit, and hold in a `Char`. They're just guaranteed by Unicode to never be assigned to an actual printable character, so higher-level text-processing code is free to treat them as sentinels internally.

There's a very on-point IETF document that formalizes precisely this layering — RFC 9839, "Unicode Character Repertoire Subsets." It defines the base "Unicode Scalars" subset exactly as Lean does, and then explicitly notes: "This subset is the default for CBOR... and has the advantage of excluding surrogates. However, it includes legacy controls and noncharacters." Then, separately, it documents that *some specific protocols* layer a stricter subset on top — e.g. "The XML 1.0 Specification, in its grammar production labeled 'Char,' specifies a subset of Unicode code points that excludes surrogates, legacy C0 controls, and the noncharacters U+FFFE and U+FFFF."

So the "strict" set you built is real and has real use cases (XML 1.0's `Char` production, PRECIS profiles, some security-hardening contexts) — but it's a *protocol-specific* narrowing, not "the" definition of a valid Unicode code point. It's also worth noting XML 1.0 only excludes FFFE/FFFF, not the FDD0–FDEF block — so even among "strict" specs, which noncharacters get excluded (and why) varies by protocol. There's no single universal "strict" standard the way there's a single scalar-value standard.

**Why this matters for a Lean proposal specifically:** Lean's `Char` backs `String`, which is UTF-8 internally. If `isValidChar` excluded noncharacters, then decoding a perfectly well-formed UTF-8 byte sequence that happens to encode U+FFFE would have to fail — even though that byte sequence is valid UTF-8 by the Unicode Standard's own encoding rules. That would break the invariant "any well-formed UTF-8 byte sequence decodes to a sequence of `Char`s," and it's exactly the choice Rust's `char` and Swift's `Unicode.Scalar` deliberately avoided for the same reason.

If I were reviewing a proposal here, I'd steer it away from "fix `isValidChar`" (there's nothing to fix) and toward something additive if you have a real use case, e.g.:

- `Char.isNoncharacter : Char → Bool` — a separate, explicit predicate for callers who need to reject/filter noncharacters for a specific protocol (XML parsing, IDNA, security filtering of untrusted input, etc.)
- Possibly renaming `isValidChar` → something like `isScalarValue` for terminological clarity, since that's literally the Unicode term for what it checks — a documentation/naming nit, not a soundness bug.

That framing is much more likely to land, because it doesn't ask Lean core to change the meaning of `Char` (which would be a breaking, semantically-wrong change), it just gives people the extra tool for the narrower cases where noncharacters genuinely need to be rejected.

-/
