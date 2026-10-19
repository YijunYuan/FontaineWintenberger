#!/usr/bin/env python3
"""B / appendix B-1: reorganize the source tree (docs/REFACTOR_PLAN.md §B).

Every old module is mapped to a new module; several old modules may be concatenated into one new
file (their import lists are merged and rewritten, module docstrings are combined, duplicate
`universe` declarations and `@[expose] public section` lines are dropped). Five old files are split
into two parts by line ranges (see PARTS). One aggregate file per top-level directory is written and
the root `FontaineWintenberger.lean` imports those aggregates. Old files are `git mv`-ed where the
mapping is one-to-one and deleted otherwise (history stays in git).
Run from the repository root, on a clean tree: python3 scripts/b1_reorganize.py
"""
import pathlib
import re
import subprocess
import sys

sys.path.insert(0, 'scripts')
from b1_mapping import MAP, TITLES  # noqa: E402

ROOT = pathlib.Path('FontaineWintenberger')
PKG = 'FontaineWintenberger'

HEADER = """/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module
"""


def read(old):
    return (ROOT / (old + '.lean')).read_text().split('\n')


def imports_of(lines):
    return [m.group(1) for l in lines for m in [re.match(r'^public import (\S+)', l)] if m]


def docstring_of(lines):
    """(title, body-lines) of the module docstring."""
    i = next(k for k, l in enumerate(lines) if l.startswith('/-!'))
    j = next(k for k in range(i, len(lines)) if lines[k].rstrip().endswith('-/'))
    block = lines[i:j + 1]
    block[0] = block[0][3:]
    block[-1] = block[-1].rstrip()[:-2]
    text = '\n'.join(block).strip('\n')
    m = re.match(r'# ([^\n]*)\n?', text)
    title = m.group(1) if m else ''
    body = text[m.end():].strip('\n') if m else text
    return title, body, j


def body_of(lines):
    """Everything after the `@[expose] public section` line."""
    j = next(k for k, l in enumerate(lines) if l.startswith('@[expose] public section'))
    return lines[j + 1:]


# Parts of split files: ranges are 1-based inclusive line numbers of the CURRENT file.
PARTS = {
    'FieldOfNorms/Multiplicative@FIF': dict(
        file='FieldOfNorms/Multiplicative', imports=[
            'Mathlib.FieldTheory.IntermediateField.Adjoin.Basic', 'Mathlib.RingTheory.Norm.Transitivity'],
        pre=['namespace FontaineWintenberger', '', 'noncomputable section', ''],
        ranges=[(25, 97)], post=['', 'end', '', 'end FontaineWintenberger']),
    'FieldOfNorms/Multiplicative@FoN': dict(
        file='FieldOfNorms/Multiplicative', imports=[
            f'{PKG}.Mathlib.FieldTheory.FiniteIntermediateField', 'Mathlib.Algebra.GroupWithZero.WithZero'],
        pre=['namespace FontaineWintenberger', '', 'noncomputable section', ''],
        ranges=[(25, 25), (99, 248)], post=['', 'end FontaineWintenberger']),
    'FieldOfNorms/Isomorphism@FIF': dict(
        file='FieldOfNorms/Isomorphism', imports=['Mathlib.Order.Filter.AtTopBot.Map'],
        pre=['namespace FontaineWintenberger', '', 'noncomputable section', ''],
        ranges=[(28, 29), (31, 94), (205, 220)], post=['', 'end', '', 'end FontaineWintenberger']),
    'FieldOfNorms/Isomorphism@FoN': dict(
        file='FieldOfNorms/Isomorphism', imports=[
            f'{PKG}.LocalField.Basic', f'{PKG}.FieldOfNorms.Basic.Ring',
            f'{PKG}.Ramification.Upper.Transport', f'{PKG}.Mathlib.Analysis.UniformContinuity'],
        pre=['namespace FontaineWintenberger', '', 'noncomputable section', ''],
        ranges=[(26, 29), (96, 203), (222, 246), (248, 406)], post=['', 'end', '', 'end FontaineWintenberger']),
    'FieldOfNorms/Addition@FIF': dict(
        file='FieldOfNorms/Addition', imports=['Mathlib.Order.Filter.AtTopBot.Basic'],
        pre=['namespace FontaineWintenberger', '', 'open Filter', '', 'section Nets', ''],
        ranges=[(34, 49), (70, 88)], post=['', 'end Nets', '', 'end FontaineWintenberger']),
    'FieldOfNorms/Addition@Rest': dict(
        file='FieldOfNorms/Addition', imports=[
            f'{PKG}.LocalField.Basic', f'{PKG}.FieldOfNorms.Basic.Valuation',
            f'{PKG}.FieldOfNorms.Estimates.Herbrand', f'{PKG}.FieldOfNorms.Estimates.Topology',
            f'{PKG}.APF.Tower.Wild', f'{PKG}.APF.Tower.Stages', f'{PKG}.FieldOfNorms.Estimates.FiniteLayer'],
        pre=['namespace FontaineWintenberger', '', 'noncomputable section', '', 'open Filter', ''],
        ranges=[(32, 34), (51, 68), (90, 295)], post=['', 'end', '', 'end FontaineWintenberger']),
    'Ramification/PrimeDegree@Group': dict(
        file='Ramification/PrimeDegree', imports=[
            f'{PKG}.LocalField.Basic', f'{PKG}.Ramification.Upper.Basic',
            'Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup'],
        pre=[], ranges=[(23, 169)], post=['', 'end FontaineWintenberger']),
    'Ramification/PrimeDegree@Spectral': dict(
        file='Ramification/PrimeDegree', imports=[
            f'{PKG}.LocalField.Basic', f'{PKG}.Ramification.Different.TraceIdeal',
            f'{PKG}.Ramification.Upper.PrimeOrder', f'{PKG}.APF.Finite.Galois'],
        pre=['namespace FontaineWintenberger', ''], ranges=[(170, 286)], post=['', 'end FontaineWintenberger']),
    'GroupTheory/PrimeChain@Group': dict(
        file='GroupTheory/PrimeChain', imports=['Mathlib.GroupTheory.PGroup', 'Mathlib.GroupTheory.Nilpotent',
                                                'Mathlib.Order.Atoms.Finite'],
        pre=[], ranges=[(22, 75)], post=['', 'end FontaineWintenberger']),
    'GroupTheory/PrimeChain@Wild': dict(
        file='GroupTheory/PrimeChain', imports=[f'{PKG}.Mathlib.GroupTheory.PrimeChain'],
        pre=['namespace FontaineWintenberger', ''], ranges=[(24, 24), (77, 87)], post=['', 'end FontaineWintenberger']),
    'Ramification/NormCongruence@Core': dict(
        file='Ramification/NormCongruence', imports=[
            f'{PKG}.LocalField.Basic', f'{PKG}.Ramification.Different.TraceIdeal',
            'Mathlib.GroupTheory.GroupAction.Quotient', 'Mathlib.GroupTheory.GroupAction.SubMulAction',
            'Mathlib.Algebra.Group.Action.Pointwise.Finset', 'Mathlib.Algebra.BigOperators.Ring.Finset',
            'Mathlib.RingTheory.Norm.Transitivity'],
        pre=[], ranges=[(24, 279)], post=['', 'end Spectral', '', 'end', '', 'end FontaineWintenberger']),
    'Ramification/NormCongruence@APF': dict(
        file='Ramification/NormCongruence', imports=[
            f'{PKG}.LocalField.Basic', f'{PKG}.Ramification.Norm.Congruence', f'{PKG}.APF.Elementary.PrimeDegree'],
        pre=['namespace FontaineWintenberger', '', 'noncomputable section', ''],
        ranges=[(193, 201), (280, 297)], post=['', 'end Spectral', '', 'end', '', 'end FontaineWintenberger']),
    'Ramification/NormTower@Core': dict(
        file='Ramification/NormTower', imports=[
            f'{PKG}.LocalField.Basic', f'{PKG}.Ramification.Norm.Congruence', f'{PKG}.Ramification.Norm.Valuation'],
        pre=[], ranges=[(22, 99)], post=['', 'end FontaineWintenberger']),
    'Ramification/NormTower@Spectral': dict(
        file='Ramification/NormTower', imports=[
            f'{PKG}.LocalField.Basic', f'{PKG}.Ramification.Norm.Tower', f'{PKG}.APF.Elementary.PrimeDegree'],
        pre=['namespace FontaineWintenberger', '', 'attribute [local instance] FractionRing.liftAlgebra', ''],
        ranges=[(101, 127)], post=['', 'end FontaineWintenberger']),
}


def part_body(name):
    p = PARTS[name]
    lines = read(p['file'])
    out = list(p['pre'])
    for a, b in p['ranges']:
        out += lines[a - 1:b]
    out += p['post']
    return out


# Where an import of a split file resolves (the part the importers actually use).
SPLIT_DEFAULT = {
    'FieldOfNorms/Multiplicative': 'Mathlib/FieldTheory/FiniteIntermediateField',
    'FieldOfNorms/Isomorphism': 'FieldOfNorms/Functor/Map',
    'FieldOfNorms/Addition': 'FieldOfNorms/Basic/Addition',
    'Ramification/PrimeDegree': 'APF/Elementary/PrimeDegree',
    'GroupTheory/PrimeChain': 'Ramification/Lower/Wild',
    'Ramification/NormCongruence': 'Ramification/Norm/Congruence',
    'Ramification/NormTower': 'Ramification/Norm/Tower',
}


def old2new():
    d = dict(SPLIT_DEFAULT)
    for n, olds in MAP.items():
        for o in olds:
            d[o] = n
            if '@' not in o:
                d[o] = n
    return d


def rewrite_import(imp, o2n, self_new):
    if imp.startswith(PKG + '.'):
        old = imp[len(PKG) + 1:].replace('.', '/')
        new = old if old in MAP else o2n.get(old)
        if new is None:
            raise KeyError(imp)
        if new == self_new:
            return None
        return f'{PKG}.{new.replace("/", ".")}'
    return imp


def build(new, olds, o2n):
    imports = []
    doc_title = TITLES.get(new)
    doc_bodies = []
    bodies = []
    universes = set()
    for idx, o in enumerate(olds):
        src = read(o.split('@')[0])
        title, body, _ = docstring_of(src)
        if doc_title is None:
            doc_title = title
        if len(olds) > 1:
            doc_bodies.append(f'## {title}\n\n{body}' if body else f'## {title}')
        else:
            doc_bodies.append(body)
        if '@' in o:
            imps = PARTS[o]['imports']
            blines = part_body(o)
        else:
            imps = imports_of(src)
            blines = body_of(src)
        for imp in imps:
            r = rewrite_import(imp, o2n, new)
            if r and r not in imports:
                imports.append(r)
        # drop duplicate universe declarations and nested public-section lines
        cleaned = []
        for l in blines:
            m = re.match(r'^universe (.*)$', l)
            if m:
                names = [u for u in m.group(1).split() if u not in universes]
                universes.update(names)
                if not names:
                    continue
                l = 'universe ' + ' '.join(names)
            if l.startswith('@[expose] public section'):
                continue
            cleaned.append(l)
        # trim leading/trailing blank lines
        while cleaned and not cleaned[0].strip():
            cleaned.pop(0)
        while cleaned and not cleaned[-1].strip():
            cleaned.pop()
        bodies.append('\n'.join(cleaned))
    # order imports: project first (as given), Mathlib after
    proj = [i for i in imports if i.startswith(PKG)]
    math = [i for i in imports if not i.startswith(PKG)]
    doc = f'/-!\n# {doc_title}\n\n' + '\n\n'.join(b for b in doc_bodies if b).strip() + '\n-/\n'
    text = HEADER + '\n' + '\n'.join(f'public import {i}' for i in proj + math) + '\n\n' + doc + \
        '\n@[expose] public section\n\n' + '\n\n'.join(bodies) + '\n'
    return text


# Hand fixes needed by the merges (name clashes created by the union of imports).
FIXUPS = {
    # `Valuation` used to reach the field-of-norms carrier through `Integral` → `Multiplicative`;
    # `Integral` now imports only the finite-intermediate-field half.
    'FieldOfNorms/Basic/Valuation': lambda s: s.replace(
        'public import FontaineWintenberger.FieldOfNorms.Estimates.Integral\n',
        'public import FontaineWintenberger.FieldOfNorms.Basic.Defs\n'
        'public import FontaineWintenberger.FieldOfNorms.Estimates.Integral\n'),
    # `IsDiscreteValuationRing.maximalIdeal : HeightOneSpectrum` becomes visible through the
    # normalized-valuation imports and clashes with `IsLocalRing.maximalIdeal`.
    'Ramification/Lower/Basic': lambda s: s.replace(
        'open IsDiscreteValuationRing IsLocalRing\n',
        'open IsDiscreteValuationRing hiding maximalIdeal\nopen IsLocalRing\n'),
}


def main():
    o2n = old2new()
    olds_all = {o.split('@')[0] for olds in MAP.values() for o in olds}
    existing = {str(f.relative_to(ROOT))[:-5] for f in ROOT.rglob('*.lean')}
    missing = olds_all - existing
    if missing:
        sys.exit(f'missing old files: {sorted(missing)}')
    unmapped = existing - olds_all
    if unmapped:
        sys.exit(f'unmapped files: {sorted(unmapped)}')
    texts = {new: build(new, olds, o2n) for new, olds in MAP.items()}
    # git mv one-to-one files first (keeps history), then write contents
    for new, olds in MAP.items():
        if len(olds) == 1 and '@' not in olds[0] and olds[0] != new:
            dst = ROOT / (new + '.lean')
            dst.parent.mkdir(parents=True, exist_ok=True)
            subprocess.run(['git', 'mv', str(ROOT / (olds[0] + '.lean')), str(dst)], check=True)
    for old in sorted(olds_all):
        p = ROOT / (old + '.lean')
        if p.exists() and old not in MAP:
            subprocess.run(['git', 'rm', '-q', str(p)], check=True)
    for new, text in texts.items():
        dst = ROOT / (new + '.lean')
        dst.parent.mkdir(parents=True, exist_ok=True)
        dst.write_text(FIXUPS.get(new, lambda x: x)(text))
    # remove empty old directories
    for d in ['Algebra', 'GroupTheory', 'FieldTheory']:
        p = ROOT / d
        if p.exists() and not any(p.iterdir()):
            p.rmdir()
    # aggregates
    layers = ['Mathlib', 'LocalField', 'Ramification', 'APF', 'FieldOfNorms']
    for lay in layers:
        mods = sorted(n for n in MAP if n.startswith(lay + '/'))
        text = HEADER + '\n' + '\n'.join(f'public import {PKG}.{m.replace("/", ".")}' for m in mods) + '\n'
        (ROOT / (lay + '.lean')).write_text(text)
    root = HEADER + '\n' + '\n'.join(f'public import {PKG}.{lay}' for lay in layers) + '\n'
    pathlib.Path(PKG + '.lean').write_text(root)
    print('new modules:', len(MAP), '; old modules:', len(olds_all))


if __name__ == '__main__':
    main()
