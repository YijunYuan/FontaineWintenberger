#!/usr/bin/env python3
"""F1a migration: bundle the base-field hypotheses into
`IsCompleteDiscreteValuedField` / `IsPerfectResidueLocalField` (see docs/REFACTOR_PLAN.md A1).

Idempotent on a clean tree. Run from the repository root:  python3 scripts/f1a_headers.py
"""
import pathlib
import re

ROOT = pathlib.Path('FontaineWintenberger')
DVR = r'\[IsDiscreteValuationRing\s+\(NormedField\.valuation\s+\(K\s*:=\s*(\w+)\)\)\.valuationSubring\]'
PF = (r'\[PerfectField\s+\((?:IsLocalRing\.)?ResidueField\s*'
      r'(?:\(NormedField\.valuation\s+\(K\s*:=\s*(\w+)\)\)\.valuationSubring'
      r'|\(Valuation\.valuationSubring\s+\(NormedField\.valuation\s+\(K\s*:=\s*(\w+)\)\)\))\)\]')
UD = r'\[IsUltrametricDist\s+(\w+)\]'
CS = r'\[CompleteSpace\s+(\w+)\]'
DECL = re.compile(r'^((?:@\[.*\]\s*)?(?:private |protected |noncomputable |local )*'
                  r'(?:theorem|lemma|def|abbrev|instance)\s+[^\s]+)(.*)$')
CMD_START = re.compile(
    r'^(variable|omit|theorem|lemma|def|noncomputable|abbrev|instance|local|private|protected|'
    r'@\[|/--|/-!|section|end|namespace|open|include|scoped|notation|attribute|set_option|#|'
    r'example|structure|class|universe|-- )')


def pf_var(m):
    return m.group(1) or m.group(2)


def commands(lines):
    """Spans (start, end, kind) of top-level `variable` / `omit` commands."""
    spans = []
    i = 0
    while i < len(lines):
        if lines[i].startswith('variable') or lines[i].startswith('omit'):
            j = i + 1
            while j < len(lines) and lines[j].strip() != '' and not CMD_START.match(lines[j]):
                j += 1
            spans.append((i, j, lines[i].split()[0]))
            i = j
        else:
            i += 1
    return spans


def tidy(blk):
    blk = '\n'.join(l.rstrip() for l in blk.split('\n'))
    blk = re.sub(r'\n\s*\n', '\n', blk)
    blk = re.sub(r'^(variable|omit)\s*\n\s+', r'\1 ', blk)
    blk = '\n'.join(re.sub(r'(\S)  +', r'\1 ', l) for l in blk.split('\n'))
    blk = re.sub(r'omit\s+in\s*$', 'omit in', blk)
    return blk


DECL_LINE = re.compile(r'^(@\[|theorem|lemma|def|noncomputable|abbrev|instance|local instance|private|protected|example|structure|class)')
COMPONENTS = (('ud', UD, lambda m: m.group(1)), ('cs', CS, lambda m: m.group(1)),
              ('dvr', DVR, lambda m: m.group(1)), ('pf', PF, pf_var))


def rewrite_file(f):
    text = f.read_text()
    if 'IsDiscreteValuationRing (NormedField.valuation' not in text:
        return False
    lines = text.split('\n')
    spans = commands(lines)
    scope_starts = [k for k, l in enumerate(lines) if re.match(r'^(section|namespace|end)\b', l)]

    def scope_of(i):
        return max([k for k in scope_starts if k <= i], default=0)

    # scope path (tuple of opening line indices) for every line
    paths = []
    stack = []
    for k, l in enumerate(lines):
        if re.match(r'^(section|namespace)\b', l):
            stack.append(k)
        elif re.match(r'^end\b', l) and stack:
            stack.pop()
        paths.append(tuple(stack))

    def visible(a, i):
        return a <= i and paths[a] == paths[i][:len(paths[a])]

    def has_decl_between(a, b):
        return any(DECL_LINE.match(lines[k]) for k in range(a, b))

    # (scope, var) -> dict(at=DVR cmd index, triple=triple cmd index, pf_early=bool, pf_late=[cmd indices])
    info = {}
    for (i, j, kind) in spans:
        if kind != 'variable':
            continue
        blk = '\n'.join(lines[i:j])
        for m in re.finditer(DVR, blk):
            v = m.group(1)
            sc = scope_of(i)
            cmds = [(a, b) for (a, b, k2) in spans if k2 == 'variable' and visible(a, i)]
            allv = '\n'.join('\n'.join(lines[a:b]) for (a, b) in cmds)
            triple = None
            for (a, b) in cmds:
                vb = '\n'.join(lines[a:b])
                if re.search(r'\[IsUltrametricDist\s+' + v + r'\]', vb) and re.search(r'\[CompleteSpace\s+' + v + r'\]', vb):
                    triple = a
            if triple is None or not re.search(r'\[NontriviallyNormedField\s+' + v + r'\]', allv):
                continue
            cross = False  # bundle at the triple even across scopes; see docs/REFACTOR_PLAN.md F1 log
            info[(sc, v)] = dict(at=i, triple=triple, cross=cross, pf_early=False, pf_late=[])
    if not info:
        return False
    # classify PerfectField variable commands
    for (i, j, kind) in spans:
        if kind != 'variable':
            continue
        blk = '\n'.join(lines[i:j])
        for m in re.finditer(PF, blk):
            v = pf_var(m)
            sc = scope_of(i)
            d = info.get((sc, v))
            if d is None:
                continue
            if not has_decl_between(d['triple'], i):
                d['pf_early'] = True
            else:
                d['pf_late'].append(i)

    def cls(sc, v, pos):
        # A PerfectField binder introduced later in the section cannot be expressed with `omit`
        # (the exact local instance always beats the projection path), so the whole section
        # takes the stronger class; single declarations drop it with `omit … in` below.
        # A PerfectField binder introduced after declarations is left as a plain variable:
        # bundling it would strengthen the earlier declarations' signatures.
        # F1a bundles only the DVR triple. `PerfectField 𝓀[K]` stays a separate binder: the
        # stronger `IsPerfectResidueLocalField` also asserts prime residue characteristic, which
        # callers with a bare `PerfectField` hypothesis cannot supply. It enters in F1b with `p`.
        return 'IsCompleteDiscreteValuedField'

    def bundled_at(sc, v, pos):
        for (s2, v2), d in info.items():
            if v2 == v and visible(d['triple'], pos) and pos >= d['triple']:
                return True
        return False

    def cls_at(v, pos):
        for (s2, v2), d in info.items():
            if v2 == v and visible(d['triple'], pos) and pos >= d['triple']:
                return cls(s2, v2, pos)
        return 'IsCompleteDiscreteValuedField'

    new = list(lines)
    for (i, j, kind) in reversed(spans):
        sc = scope_of(i)
        blk = '\n'.join(lines[i:j])
        orig = blk
        if kind == 'variable':
            late_here = []
            for (s2, v), d in info.items():
                if d['at'] != i and d['triple'] != i:
                    continue
                if d['at'] == i:
                    blk = re.sub(DVR, lambda m: '' if m.group(1) == v else m.group(0), blk)
                    if d['cross']:
                        late_here.append(v)
                if d['triple'] == i:
                    blk = re.sub(r'\[IsUltrametricDist\s+' + v + r'\]', '[' + cls(sc, v, i) + ' ' + v + ']', blk, count=1)
                    blk = re.sub(r'\s*\[CompleteSpace\s+' + v + r'\]', '', blk, count=1)
            blk = tidy(blk)
            if re.fullmatch(r'\s*variable\s*', blk):
                blk = ''
            for v in late_here:
                blk = (blk + '\n' if blk else '') + 'variable [IsCompleteDiscreteValuedField ' + v + ']\n' + \
                    'omit [IsUltrametricDist ' + v + '] [CompleteSpace ' + v + ']'
        else:  # omit
            comp = {}
            for name, pat, getter in COMPONENTS:
                for m in re.finditer(pat, blk):
                    v = getter(m)
                    if bundled_at(sc, v, i) and name != 'pf':
                        comp.setdefault(v, set()).add(name)
            if comp:
                add_omit = []
                for v, names in comp.items():
                    c = cls_at(v, i)
                    full = {'ud', 'cs', 'dvr'} | ({'pf'} if c == 'IsPerfectResidueLocalField' else set())
                    for name, pat, getter in COMPONENTS:
                        if name in names:
                            blk = re.sub(pat, lambda m, v=v, g=getter: '' if g(m) == v else m.group(0), blk)
                    if names >= full:
                        add_omit.append('[' + c + ' ' + v + ']')
                    elif c == 'IsPerfectResidueLocalField' and names == {'pf'}:
                        # omitting only PerfectField: drop to the weaker class on this declaration
                        add_omit.append('[IsPerfectResidueLocalField ' + v + ']')
                        k = j
                        while k < len(new) and not DECL.match(new[k]):
                            k += 1
                        m = DECL.match(new[k])
                        new[k] = m.group(1) + ' [IsCompleteDiscreteValuedField ' + v + ']' + m.group(2)
                    # otherwise: keep the class (partial omits are dropped)
                if add_omit:
                    blk = re.sub(r'^omit\s*', 'omit ' + ' '.join(add_omit) + ' ', blk, count=1)
                blk = tidy(blk)
                blk = re.sub(r'^omit\s*\n\s+', 'omit ', blk)
                if re.fullmatch(r'\s*omit\s*(in)?\s*', blk):
                    blk = ''
        if blk != orig:
            new[i:j] = blk.split('\n') if blk else []
    out = '\n'.join(new)
    if 'FontaineWintenberger.LocalField.Basic' not in out:
        out = out.replace('module\n\n', 'module\n\npublic import FontaineWintenberger.LocalField.Basic\n', 1)
    f.write_text(out)
    return True


def patch(path, old, new, count=1):
    p = pathlib.Path(path)
    s = p.read_text()
    assert old in s, (path, old[:60])
    p.write_text(s.replace(old, new, count))


def manual_patches():
    # OrbitDifferent spells the DVR binder differently
    patch('FontaineWintenberger/APF/OrbitDifferent.lean',
          'variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]\n'
          'variable [IsDiscreteValuationRing (Valuation.valuationSubring (NormedField.valuation (K := K)))]\n'
          'variable [PerfectField (IsLocalRing.ResidueField\n'
          '    (Valuation.valuationSubring (NormedField.valuation (K := K))))]\n',
          'variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]\n'
          'variable [PerfectField (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring)]\n')
    # bundled transfer theorems for finite normed extensions
    patch('FontaineWintenberger/LocalField/NormedTower.lean', 'end FontaineWintenberger', '''\
/-- A finite separable normed extension of a complete discretely valued field is again one. -/
theorem normedAlgebra_isCompleteDiscreteValuedField (K L : Type*) [NontriviallyNormedField K]
    [IsCompleteDiscreteValuedField K] [NontriviallyNormedField L] [IsUltrametricDist L]
    [NormedAlgebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    IsCompleteDiscreteValuedField L :=
  have : CompleteSpace L := FiniteDimensional.complete K L
  have := normedAlgebra_unitBall_isDiscreteValuationRing K L
  {}

end FontaineWintenberger''')
    patch('FontaineWintenberger/LocalField/ResidueField.lean', 'end FontaineWintenberger', '''\
omit [IsCompleteDiscreteValuedField K] in
/-- A finite separable normed extension of a local field is again a local field, with the same
residue characteristic. -/
theorem normedAlgebra_isPerfectResidueLocalField [IsPerfectResidueLocalField K] (L : Type*)
    [NontriviallyNormedField L] [IsUltrametricDist L] [NormedAlgebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] : IsPerfectResidueLocalField L :=
  have := normedAlgebra_isCompleteDiscreteValuedField K L
  have := normedAlgebra_residueField_perfectField K L
  have := normedAlgebra_residueField_finiteDimensional K L
  { residueChar_prime := by
      rw [← Algebra.ringChar_eq
        (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring)]
      exact IsPerfectResidueLocalField.residueChar_prime }

omit [IsCompleteDiscreteValuedField K] in
theorem normedAlgebra_residueChar_eq [IsPerfectResidueLocalField K] (L : Type*)
    [NontriviallyNormedField L] [IsUltrametricDist L] [NormedAlgebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] :
    haveI := normedAlgebra_isPerfectResidueLocalField K L
    residueChar L = residueChar K :=
  have := normedAlgebra_residueField_finiteDimensional K L
  (Algebra.ringChar_eq
    (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring) _).symm

end FontaineWintenberger''')
    # entry point from the Valued presentation
    cn = pathlib.Path('FontaineWintenberger/LocalField/CompatibleNorm.lean')
    s = cn.read_text()
    i = s.index('theorem discreteValued_unitBall_isDiscreteValuationRing')
    j = s.index('\n\n', s.index(':= by', i))
    s = s[:j] + '''

/-- The bundled hypothesis for the norm attached to a complete discrete valuation. -/
theorem discreteValued_isCompleteDiscreteValuedField [h : CompleteSpace K]
    [IsDiscreteValuationRing val.v.valuationSubring] : IsCompleteDiscreteValuedField K :=
  have : @CompleteSpace K (discreteValuedNormedField K Γ).toUniformSpace := h
  have := discreteValued_unitBall_isDiscreteValuationRing K Γ
  {}''' + s[j:]
    s = s.replace('  have := discreteValued_unitBall_isDiscreteValuationRing K Γ\n  exact extensionValuationSubring',
                  '  have := discreteValued_isCompleteDiscreteValuedField K Γ\n  exact extensionValuationSubring')
    s = s.replace('  have := discreteValued_norm_hasExtension K Γ L w\n  have := discreteValued_unitBall_isDiscreteValuationRing K Γ\n  have : PerfectField',
                  '  have := discreteValued_norm_hasExtension K Γ L w\n  have := discreteValued_isCompleteDiscreteValuedField K Γ\n  have : PerfectField')
    cn.write_text(s)
    for f in ['FontaineWintenberger/LocalField/KrasnerValuation.lean',
              'FontaineWintenberger/LocalField/SeparableRootExtraction.lean']:
        p = pathlib.Path(f)
        s = p.read_text()
        s = re.sub(r'  let : IsDiscreteValuationRing \(NormedField\.valuation \(K := K\)\)\.valuationSubring :=\n'
                   r'    discreteValued_unitBall_isDiscreteValuationRing K ΓK\n',
                   '  let : IsCompleteDiscreteValuedField K := discreteValued_isCompleteDiscreteValuedField K ΓK\n', s)
        p.write_text(s)
    patch('FontaineWintenberger/Ramification/Degree.lean',
          '  have := discreteValued_unitBall_isDiscreteValuationRing K ΓK\n  let e := RingEquiv.subringCongr',
          '  have := discreteValued_isCompleteDiscreteValuedField K ΓK\n  let e := RingEquiv.subringCongr')


def rewrite_install_sites():
    n = 0
    for f in ROOT.rglob('*.lean'):
        if f.name in ('ResidueField.lean', 'NormedTower.lean', 'CompatibleNorm.lean'):
            continue
        t = f.read_text()
        o = t
        pair = re.compile(r'^(\s*)(let|letI|have) := normedAlgebra_unitBall_isDiscreteValuationRing K ([^\n]+)\n'
                          r'\s*(let|letI|have) := normedAlgebra_residueField_perfectField K \3\n', re.M)
        t = pair.sub(lambda m: f"{m.group(1)}{m.group(2)} := normedAlgebra_isCompleteDiscreteValuedField K {m.group(3)}\n"
                     f"{m.group(1)}{m.group(2)} := normedAlgebra_residueField_perfectField K {m.group(3)}\n", t)
        pair2 = re.compile(r'^(\s*)(let|letI|have) := normedAlgebra_residueField_perfectField K ([^\n]+)\n'
                           r'\s*(let|letI|have) := normedAlgebra_unitBall_isDiscreteValuationRing K \3\n', re.M)
        t = pair2.sub(lambda m: f"{m.group(1)}{m.group(2)} := normedAlgebra_isCompleteDiscreteValuedField K {m.group(3)}\n"
                      f"{m.group(1)}{m.group(2)} := normedAlgebra_residueField_perfectField K {m.group(3)}\n", t)
        def merely_normed(x):
            base = x.split('.')[0]
            return re.search(r'\[NormedField\s+' + re.escape(base) + r'\]', t) is not None
        t = re.sub(r'IsDiscreteValuationRing\s*\(NormedField\.valuation \(K := ([^)]+)\)\)\.valuationSubring\s*:=\s*'
                   r'normedAlgebra_unitBall_isDiscreteValuationRing K \1\b',
                   lambda m: m.group(0) if merely_normed(m.group(1)) else
                   'IsCompleteDiscreteValuedField ' + m.group(1) + ' :=\n  normedAlgebra_isCompleteDiscreteValuedField K ' + m.group(1), t)
        t = re.sub(r'\b(let|letI|have) := normedAlgebra_unitBall_isDiscreteValuationRing K ([^\s)]+)',
                   lambda m: m.group(0) if merely_normed(m.group(2)) else
                   m.group(1) + ' := normedAlgebra_isCompleteDiscreteValuedField K ' + m.group(2), t)
        if t != o:
            f.write_text(t)
            n += 1
    return n


def split_point(line, limit=100):
    inq = False
    best = None
    for i, ch in enumerate(line):
        if ch == '"':
            inq = not inq
        if ch == ' ' and not inq and 0 < i <= limit and line[:i].strip():
            best = i
    return best


def post_process():
    for f in ROOT.rglob('*.lean'):
        t = f.read_text()
        o = t
        t = re.sub(r'(\[CompleteSpace (\w+)\]) \[CompleteSpace \2\]', r'\1', t)
        t = re.sub(r'(\[IsUltrametricDist (\w+)\]) \[IsUltrametricDist \2\]', r'\1', t)
        out = []
        for ln in t.split('\n'):
            while len(ln) > 100 and not ln.lstrip().startswith('--'):
                ind = len(ln) - len(ln.lstrip())
                sp = split_point(ln)
                if sp is None or sp <= ind:
                    break
                out.append(ln[:sp].rstrip())
                ln = ' ' * (ind + 4) + ln[sp + 1:].lstrip()
            out.append(ln)
        t = '\n'.join(out)
        if t != o:
            f.write_text(t)


if __name__ == '__main__':
    manual_patches()
    changed = sum(rewrite_file(f) for f in sorted(ROOT.rglob('*.lean')))
    sites = rewrite_install_sites()
    post_process()
    print('header-rewritten files:', changed, '| install-site files:', sites)
