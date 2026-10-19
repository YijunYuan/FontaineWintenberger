#!/usr/bin/env python3
"""A5: one notation for the ring of integers and residue field of the base field.

`LocalField/Basic.lean` declares the scoped notations
  𝒪[K] := (NormedField.valuation (K := K)).valuationSubring
  𝓀[K] := IsLocalRing.ResidueField 𝒪[K]
(definitionally Mathlib's `Valued.integer K` / `Valued.ResidueField K`, but kept as a
`ValuationSubring` so that every existing instance applies unchanged). This script rewrites every
hand-written spelling to the notation and inlines the 54 file-local notations `OK`/`R`/`A`/`R₀`/`O`
that abbreviated it. Run from the repository root: python3 scripts/a5_integer_notation.py
"""
import pathlib
import re

ROOT = pathlib.Path('FontaineWintenberger')
X = r'([A-Za-z][\w.₀₁]*)'
RES = [
    # residue field, possibly broken over two lines
    (re.compile(r'IsLocalRing\.ResidueField\s*\n?\s*\(Valuation\.valuationSubring \(NormedField\.valuation \(K := ' + X + r'\)\)\)'), r'𝓀[\1]'),
    (re.compile(r'IsLocalRing\.ResidueField\s*\n?\s*\(NormedField\.valuation \(K := ' + X + r'\)\)\.valuationSubring'), r'𝓀[\1]'),
    (re.compile(r'IsLocalRing\.ResidueField\s*\n?\s*\(\(NormedField\.valuation \(K := ' + X + r'\)\)\.valuationSubring\)'), r'𝓀[\1]'),
    # integer ring
    (re.compile(r'\(NormedField\.valuation \(K := ' + X + r'\)\)\.valuationSubring'), r'𝒪[\1]'),
    (re.compile(r'Valuation\.valuationSubring\s*\n?\s*\(NormedField\.valuation \(K := ' + X + r'\)\)'), r'𝒪[\1]'),
    # tidy: `(𝒪[K])` → `𝒪[K]` when parenthesised alone as an argument
    (re.compile(r'\((𝒪\[[^\]]+\])\)'), r'\1'),
    (re.compile(r'\((𝓀\[[^\]]+\])\)'), r'\1'),
]
NOTATION = re.compile(r'^local notation "(\w+₀?)" => (𝒪\[K\]|𝓀\[K\])\s*$')
PROSE = re.compile(r'/-[-!]?.*?-/|--[^\n]*', re.S)


def inline_notation(lines, i, tok, body):
    """Replace `tok` by `body` from line i to the end of the enclosing scope; drop line i."""
    depth = 0
    end = len(lines)
    for k in range(i + 1, len(lines)):
        l = lines[k]
        if re.match(r'^(noncomputable )?section\b', l) or re.match(r'^namespace\b', l):
            depth += 1
        elif re.match(r'^end\b', l):
            if depth == 0:
                end = k
                break
            depth -= 1
    pat = re.compile(r"(?<![\w'.₀-₉])" + re.escape(tok) + r"(?![\w'₀-₉])")

    def rep(m):
        # keep named arguments `(R := …)`: an opening parenthesis before and `:=` after
        before = m.string[:m.start()].rstrip()
        after = m.string[m.end():].lstrip()
        if before.endswith('(') and after.startswith(':='):
            return m.group(0)
        return body

    for k in range(i + 1, end):
        l = lines[k]
        if l.lstrip().startswith('--'):
            continue
        lines[k] = pat.sub(rep, l)
    lines[i] = None


def process(text):
    for p, r in RES:
        text = p.sub(r, text)
    lines = text.split('\n')
    # mark prose lines
    prose = [False] * len(lines)
    pos = 0
    offsets = []
    for l in lines:
        offsets.append(pos)
        pos += len(l) + 1
    for m in PROSE.finditer(text):
        a = text[:m.start()].count('\n')
        b = text[:m.end()].count('\n')
        for k in range(a, b + 1):
            prose[k] = True
    # inline file-local notations
    changed = True
    while changed:
        changed = False
        for i, l in enumerate(lines):
            if l is None:
                continue
            m = NOTATION.match(l)
            if m:
                tok, body = m.group(1), m.group(2)
                saved = {k: lines[k] for k in range(len(lines)) if prose[k] and lines[k] is not None}
                inline_notation(lines, i, tok, body)
                for k, v in saved.items():
                    if lines[k] is not None:
                        lines[k] = v
                changed = True
                break
    out = [l for l in lines if l is not None]
    return '\n'.join(out)


if __name__ == '__main__':
    n = 0
    for f in sorted(ROOT.rglob('*.lean')):
        if f.parts[1] == 'Mathlib' or f.name == 'Basic.lean' and f.parts[1] == 'LocalField':
            continue  # the Mathlib layer does not import the notation; Basic.lean declares it
        s = f.read_text()
        t = process(s)
        if t != s:
            f.write_text(t)
            n += 1
    print('files changed:', n)
