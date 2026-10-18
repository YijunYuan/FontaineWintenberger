#!/usr/bin/env python3
"""C1/C4: rename the core field-of-norms identifiers (docs/REFACTOR_PLAN.md §C1, §C4).

* `NormLimit` → `FieldOfNorms`; `normLimitGroup` → `FieldOfNorms.normCompatibleUnits`;
  `normLimitEval` → `FieldOfNorms.coord`; `normLimitXxx` → `FieldOfNorms.xxx`;
  `finiteNormLimitXxx` → `FieldOfNorms.finiteXxx`.
* `SeparableNormUnion` → `RelFieldOfNorms`; `separableNormUnionXxx`, `normUnionXxx` → `RelFieldOfNorms.xxx`.
* `FiniteLayer` → `FiniteIntermediateField`; `finiteLayerXxx` → `FiniteIntermediateField.xxx`;
  the APF Galois-layer rebase `finiteLayer` → `rebaseFiniteGaloisLayer`.
* Instances: `normLimitField` → `FieldOfNorms.instField`, etc.
* Snake-case infixes `_normLimit`, `_finiteNormLimit`, `_finiteLayer`, `_separableNormUnion`,
  `_normUnion` → `_fieldOfNorms`, `_finiteFieldOfNorms`, `_finiteIntermediateField`,
  `_relFieldOfNorms`, `_relFieldOfNorms`.
* Prose: "norm limit"/"norm-limit" → "field of norms", "finite layer" → "finite intermediate field",
  "norm-field union"/"canonical union" → "relative field of norms".
Run from the repository root: python3 scripts/c1_rename.py
"""
import pathlib
import re

ROOT = pathlib.Path('FontaineWintenberger')

INSTANCES = {
    'normLimitAddCommMonoid': 'FieldOfNorms.instAddCommMonoid',
    'normLimitCommSemiring': 'FieldOfNorms.instCommSemiring',
    'normLimitNeg': 'FieldOfNorms.instNeg',
    'normLimitField': 'FieldOfNorms.instField',
    'normLimitField_charP': 'FieldOfNorms.instCharP',
    'normLimitValued': 'FieldOfNorms.instValued',
    'normLimitValued_v': 'FieldOfNorms.valued_v',
    'normLimitValued_isRankOneDiscrete': 'FieldOfNorms.instIsRankOneDiscrete',
    'normLimitValued_isDiscreteValuationRing': 'FieldOfNorms.instIsDiscreteValuationRing',
    'normLimitFieldValuation_isRankOneDiscrete': 'FieldOfNorms.fieldValuation_isRankOneDiscrete',
    'normLimitFieldValuation_isDiscreteValuationRing':
        'FieldOfNorms.fieldValuation_isDiscreteValuationRing',
    'normLimit_completeSpace': 'FieldOfNorms.instCompleteSpace',
    'normLimitResidue_perfectField': 'FieldOfNorms.instPerfectFieldResidueField',
    'separableNormUnionAlgebra': 'RelFieldOfNorms.instAlgebra',
    'separableNormUnionStageAlgebra': 'RelFieldOfNorms.instAlgebraStage',
    'separableNormUnionDirectedSystem': 'RelFieldOfNorms.instDirectedSystem',
    'separableNormUnionStage_fact_infinite': 'RelFieldOfNorms.instFactNotFiniteStage',
    'separableNormUnionStage_isAPF': 'RelFieldOfNorms.instIsAPFStage',
    'separableNormUnionValued': 'RelFieldOfNorms.instValued',
    'normLimitGroup': 'FieldOfNorms.normCompatibleUnits',
    'normLimitEval': 'FieldOfNorms.coord',
    'finiteLayer': 'rebaseFiniteGaloisLayer',
}


def low(s):
    return s[0].lower() + s[1:] if s else s


def rename_ident(name):
    if name in INSTANCES:
        return INSTANCES[name]
    for pre, new in [('normLimitEval', 'FieldOfNorms.coord'), ('normLimitGroup',
                     'FieldOfNorms.normCompatibleUnits')]:
        if name.startswith(pre) and (len(name) == len(pre) or name[len(pre)] in "_'"):
            return new + name[len(pre):]
    if name.startswith('finiteNormLimit'):
        return 'FieldOfNorms.finite' + name[len('finiteNormLimit'):]
    if name.startswith('normLimit'):
        return 'FieldOfNorms.' + low(name[len('normLimit'):])
    if name.startswith('NormLimit'):
        return 'FieldOfNorms' + name[len('NormLimit'):]
    if name.startswith('separableNormUnion'):
        return 'RelFieldOfNorms.' + low(name[len('separableNormUnion'):])
    if name.startswith('SeparableNormUnion'):
        return 'RelFieldOfNorms' + name[len('SeparableNormUnion'):]
    if name.startswith('normUnion'):
        return 'RelFieldOfNorms.' + low(name[len('normUnion'):])
    if name.startswith('finiteLayer'):
        rest = name[len('finiteLayer'):]
        return 'FiniteIntermediateField.' + low(rest.lstrip('_'))
    if name.startswith('FiniteLayer'):
        return 'FiniteIntermediateField' + name[len('FiniteLayer'):]
    return name


IDENT = re.compile(r"(?<![\w'.])((?:normLimit|NormLimit|separableNormUnion|SeparableNormUnion|normUnion|"
                   r"finiteNormLimit|finiteLayer|FiniteLayer)[\w']*(?:\.[\w']+)*)")
INFIX = [(re.compile(r"(?<=[\w'])_normLimit"), '_fieldOfNorms'),
         (re.compile(r"(?<=[\w'])_finiteNormLimit"), '_finiteFieldOfNorms'),
         (re.compile(r"(?<=[\w'])_finiteLayer"), '_finiteIntermediateField'),
         (re.compile(r"(?<=[\w'])_separableNormUnion"), '_relFieldOfNorms'),
         (re.compile(r"(?<=[\w'])_normUnion"), '_relFieldOfNorms')]
PROSE = [(re.compile(r'\bnorm[- ]limit\b', re.I), 'field of norms'),
         (re.compile(r'\bnorm[- ]limits\b', re.I), 'fields of norms'),
         (re.compile(r'\bfinite layers\b', re.I), 'finite intermediate fields'),
         (re.compile(r'\bfinite layer\b', re.I), 'finite intermediate field'),
         (re.compile(r'\bnorm-field union\b', re.I), 'relative field of norms'),
         (re.compile(r'\bcanonical union\b', re.I), 'relative field of norms')]


def rename_text(t):
    t = IDENT.sub(lambda m: rename_ident(m.group(1)), t)
    for pat, rep in INFIX:
        t = pat.sub(rep, t)
    for pat, rep in PROSE:
        t = pat.sub(rep, t)
    # namespaces
    t = re.sub(r'^(namespace|end) ((?:FontaineWintenberger\.)?)FiniteLayer\b',
               r'\1 \2FiniteIntermediateField', t, flags=re.M)
    t = re.sub(r'^(namespace|end) ((?:FontaineWintenberger\.)?)NormLimit\b',
               r'\1 \2FieldOfNorms', t, flags=re.M)
    return t


def wrap_long_lines(t, width=100):
    """Break lines longer than `width` at the last space before the limit; the continuation is
    indented four more columns (inside a `--` comment it is commented too)."""
    out = []
    for line in t.split('\n'):
        while len(line) > width:
            cut = line.rfind(' ', 0, width)
            indent = len(line) - len(line.lstrip())
            if cut <= indent:
                break
            head, rest = line[:cut].rstrip(), line[cut + 1:]
            comment = head.lstrip().startswith('--') or ' -- ' in head
            prefix = ' ' * (indent + 4) + ('-- ' if comment and not head.lstrip().startswith('/-') else '')
            out.append(head)
            line = prefix + rest
        out.append(line)
    return '\n'.join(out)


if __name__ == '__main__':
    n = 0
    for f in sorted(ROOT.rglob('*.lean')):
        s = f.read_text()
        t = rename_text(s)
        if t != s:
            t = wrap_long_lines(t)
            f.write_text(t)
            n += 1
    print('files changed:', n)
