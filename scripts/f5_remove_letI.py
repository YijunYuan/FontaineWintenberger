#!/usr/bin/env python3
"""F5: delete `letI`/`let` installs of structures that are now global instances on the `def`
carriers `NormLimit` and `SeparableNormUnion`.

Removed forms (the installed value is one of INST below):
* `letI := INST args`                      (also `let`, `haveI`, `have`; also split over two lines)
* `letI (N : …) : Field … :=\n    INST …`    (binder form)
* `letI : Mul U := (INST …).toMul`          (projection pins: Mul/Add/Nontrivial)
* `letI : Group (RingAut U) := RingAut.instGroup U`
In statements the `letI … ;` prefix lines are deleted too. Nothing else is touched.
Run from the repository root: python3 scripts/f5_remove_letI.py
"""
import pathlib
import re

ROOT = pathlib.Path('FontaineWintenberger')
INST = (r'(normLimitField|normLimitValued|normLimitCommSemiring|normLimitAddCommMonoid|'
        r'normLimitField_charP|separableNormUnionField|separableNormUnionAlgebra|'
        r'separableNormUnionStageField|separableNormUnionStageAlgebra|separableNormUnionValued)')
KW = r'(letI|let|haveI|have)'
A = re.compile(r'^\s*' + KW + r'\s*:=\s*' + INST + r'\b[^\n]*$')
B = re.compile(r'^\s*' + KW + r'\s*:=\s*$')
C = re.compile(r'^\s*' + KW + r'\s*:\s*[^:=]+:=\s*\(' + INST + r'\b[^)]*\)\.to\w+\s*$')
D = re.compile(r'^\s*' + KW + r'\s*\([^)]*\)\s*:\s*[^:=]+:=\s*$')
G = re.compile(r'^\s*' + KW + r'\s*:\s*Group \(RingAut [^)]*\)\s*:=\s*RingAut\.instGroup\b[^\n]*$')
# inline inside a binder: `(B : letI := normLimitField K L` → `(B :`
INLINE = re.compile(r'^(\s*\([\w\']+ :)\s*' + KW + r'\s*:=\s*' + INST + r'\b[^\n]*$')


def process(lines):
    out = []
    i = 0
    n = 0
    while i < len(lines):
        l = lines[i]
        nxt = lines[i + 1] if i + 1 < len(lines) else ''
        if A.match(l) or C.match(l) or G.match(l):
            i += 1; n += 1; continue
        if (B.match(l) or D.match(l)) and re.match(r'^\s*' + INST + r'\b', nxt):
            i += 2; n += 1; continue
        m = INLINE.match(l)
        if m:
            out.append(m.group(1)); i += 1; n += 1; continue
        out.append(l)
        i += 1
    return out, n


if __name__ == '__main__':
    total = 0
    files = 0
    for f in sorted(ROOT.rglob('*.lean')):
        lines = f.read_text().split('\n')
        new, n = process(lines)
        if n:
            f.write_text('\n'.join(new)); total += n; files += 1
    print(f'removed {total} installs in {files} files')
