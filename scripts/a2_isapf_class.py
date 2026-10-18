#!/usr/bin/env python3
"""A2 migration: `IsAPF`, `IsStrictlyAPF`, `IsAPFSubextension` become classes and the
"L/K infinite" hypothesis becomes `[Fact (¬ Module.Finite K L)]` (docs/REFACTOR_PLAN.md A2, A3).

Mechanical part only; the handful of places that use the hypotheses as terms are fixed by hand.
Run from the repository root after the core files (APF/Basic, APF/Abstract, APF/Strict) have
been converted:  python3 scripts/a2_isapf_class.py
"""
import pathlib
import re

ROOT = pathlib.Path('FontaineWintenberger')
HYP = r'h(?:L|M|N|P|Infinite[A-Za-z]*)'
BINDER = re.compile(r'\((' + HYP + r') : (IsAPF|IsStrictlyAPF|IsAPFSubextension) ([^()]*(?:\([^()]*\)[^()]*)*)\)')
INF_BINDER = re.compile(r'\((hInfinite[A-Za-z]*) : ¬ ?Module\.Finite ([^()]*(?:\([^()]*\)[^()]*)*)\)')
# a hypothesis name used as an explicit argument: preceded by whitespace, not followed by ` :`

KEYWORDS = {'exact', 'apply', 'refine', "refine'", 'have', 'show', 'from', 'using', 'by', 'fun',
            'intro', 'at', 'with', 'obtain', 'rcases', 'simpa', 'calc', 'rw', 'simp', 'exacts',
            'convert', 'use', 'constructor', 'let', 'haveI', 'letI', 'then', 'else', 'if', 'of',
            'trans', 'case', 'specialize', 'absurd', 'change', 'in', 'rintro', 'induction',
            'cases', 'generalize', 'suffices', 'exists', 'refine', 'subst', 'revert', 'clear'}
PROJ = re.compile(r'\.(mp|mpr|1|2|symm|trans|le|lt|ne|elim|not|resolve_left|resolve_right|out)$')


def strip_args(line, names):
    """Remove hypothesis names used as explicit arguments; keep them where they are the head of an
    application or a projection argument (those are fixed by hand / replaced by ‹_›)."""
    pat = re.compile(r'\b(' + '|'.join(sorted(map(re.escape, names), key=len, reverse=True)) + r')\b(?! : )(?!\.)(?![\'_])')
    out = []
    pos = 0
    for m in pat.finditer(line):
        before = line[:m.start()]
        stripped = before.rstrip()
        prev = re.search(r'([^\s(⟨\[,]+)$', stripped)
        prev_tok = prev.group(1) if prev else ''
        # inside a binder like (hL : …) -- already converted, but be safe
        if before.endswith('(') or before.endswith('⟨') or before.endswith('[') or before.endswith(','):
            continue
        if not prev or prev_tok in KEYWORDS or stripped.endswith((':=', '=>', '↦', '←', '·', '|')):
            continue
        if PROJ.search(prev_tok):
            out.append(line[pos:m.start()] + '‹_›')
            pos = m.end()
            continue
        out.append(line[pos:m.start()].rstrip(' '))
        pos = m.end()
    out.append(line[pos:])
    return ''.join(out)


FINITE_ARG = re.compile(r' \(isAPF_of_finite [^()]*\)(?=[\s)⟩,])')

changed = 0
for f in sorted(ROOT.rglob('*.lean')):
    s = f.read_text()
    o = s
    names = {m.group(1) for m in BINDER.finditer(s)} | {m.group(1) for m in INF_BINDER.finditer(s)}
    s = BINDER.sub(lambda m: '[' + m.group(2) + ' ' + m.group(3) + ']', s)
    s = INF_BINDER.sub(lambda m: '[Fact (¬ Module.Finite ' + m.group(2) + ')]', s)
    s = re.sub(r'include p hInfinite in', 'include p in', s)
    # drop explicit hypothesis arguments
    lines = []
    for ln in s.split('\n'):
        if re.match(r'^\s*(variable|omit|include)\b', ln):
            lines.append(ln)
            continue
        if names:
            ln = strip_args(ln, names)
        ln = re.sub(r'(?<=\S)  +(?=\S)', ' ', ln) if not ln.lstrip().startswith('--') else ln
        ln = ln.rstrip()
        lines.append(ln)
    s = '\n'.join(lines)
    s = FINITE_ARG.sub('', s)
    # `foo K L ` left with trailing space before newline / paren
    s = re.sub(r' +\)', ')', s)
    s = re.sub(r' +\n', '\n', s)
    if s != o:
        f.write_text(s)
        changed += 1
print('files changed:', changed)
