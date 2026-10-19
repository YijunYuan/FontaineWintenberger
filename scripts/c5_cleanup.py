#!/usr/bin/env python3
"""C5 (docs/REFACTOR_PLAN.md): mechanical naming and prose cleanup.

* Identifiers: drop the filler words `source`/`original` (`sourceResidueConstants` →
  `residueConstants`, …), repair the `FieldOfNorms._foo` names left by C1, move the discriminant
  lemmas into the `Polynomial` namespace, camel-case the two snake_case `def`s.
* Prose (docstrings and comments only): delete "actual", "original", "genuine", "literal",
  "actually", "genuinely", "literally", "the same original", and "source" when used as a filler
  adjective; recapitalise sentence starts.
Run from the repository root: python3 scripts/c5_cleanup.py
"""
import pathlib
import re

ROOT = pathlib.Path('FontaineWintenberger')

IDENT = [
    (re.compile(r'\b(FieldOfNorms|RelFieldOfNorms|FiniteIntermediateField)\._(?=[a-zA-Z])'), r'\1.'),
    (re.compile(r'\bsourceDeep'), 'deep'),
    (re.compile(r'\bsourceResidue'), 'residue'),
    (re.compile(r'(?<=[\w.])_sourceResidue'), '_residue'),
    (re.compile(r'\bgaloisGoodSourceUpper'), 'galoisGoodUpper'),
    (re.compile(r'\bgaloisSourceCoordinate'), 'galoisCoordinate'),
    (re.compile(r'_exists_originalHom\b'), '_exists_hom'),
    (re.compile(r'\.exists_originalHom\b'), '.exists_hom'),
    (re.compile(r'_finiteHom_source_inclusion\b'), '_finiteHom_inclusion'),
    (re.compile(r'\.finiteHom_source_inclusion\b'), '.finiteHom_inclusion'),
    (re.compile(r'apfPsi_originalBase_eq_fixing_herbrand'), 'apfPsi_base_eq_fixing_herbrand'),
    (re.compile(r'embeddingNumber_eq_restriction_of_lt_originalBound'), 'embeddingNumber_eq_restriction_of_lt_bound'),
    (re.compile(r'isGoodFiniteLayer_of_original_tensor'), 'isGoodFiniteLayer_of_tensor'),
    (re.compile(r'\boriginalClosure_isSepClosure\b'), 'closure_isSepClosure'),
    (re.compile(r'\boriginalSeparableClosureEquiv\b'), 'separableClosureEquiv'),
    (re.compile(r'\bmonic_discr_map\b'), 'Polynomial.Monic.discr_map'),
    (re.compile(r'\bsq_sub_dvd_discr\b'), 'Polynomial.sq_sub_dvd_discr'),
    (re.compile(r'\binertia_fixedField_residueEquiv\b'), 'inertiaFixedFieldResidueEquiv'),
    (re.compile(r'\bfiniteTower_autEquivImage\b'), 'finiteTowerAutEquivImage'),
]

FILLER = r'(?:actual|original|genuine|literal)'
PROSE = [
    (re.compile(r'\b[Tt]he same original '), lambda m: m.group(0)[0] + 'he '),
    (re.compile(r'\b(the|an|a|its|their|this|that|every|each|any|all|both|same|one|two|no|some|given|specified|fixed|chosen|new|old|ambient|finite|canonical|intrinsic|abstract) ' + FILLER + r' '), r'\1 '),
    (re.compile(r'\b(The|An|A|Its|Their|This|That|Every|Each|Any|All|Both|Same|One|Two|No|Some) ' + FILLER + r' '), r'\1 '),
    (re.compile(r'\b' + FILLER + r' (?=[a-zA-Z])'), ''),
    (re.compile(r'\b(actually|genuinely|literally) '), ''),
    (re.compile(r'\b(Actual|Original|Genuine|Literal) ([a-z])'), lambda m: m.group(2).upper()),
    (re.compile(r'\b(Actually|Genuinely|Literally) ([a-z])'), lambda m: m.group(2).upper()),
    (re.compile(r'\b(the|an|a|its|this|that|every|each|finite|embedded|integral|and) source '), r'\1 '),
    (re.compile(r'\b(The|An|A|Its|This|That|Every|Each) source '), r'\1 '),
    (re.compile(r'\bSource ([a-z])'), lambda m: m.group(1).upper()),
    (re.compile(r'\bsource (?=(constant|constants|field|valuation|norm|coordinate|half|domain|cardinality|product|uniformity|integral|supremum|ratio|strictness|inverse|Herbrand|positivity|completeness|discrete))'), ''),
]
# "an finite" → "a finite" after deletions
ARTICLE = re.compile(r'\b([Aa])n (?=[^aeiouAEIOU\W])')
ARTICLE_A = re.compile(r'\b([Aa]) (?=[aeiouAEIOU])')


def fix_articles(t):
    t = ARTICLE.sub(lambda m: m.group(1) + ' ', t)
    t = ARTICLE_A.sub(lambda m: m.group(1) + 'n ', t)
    return t


def clean_prose(t):
    """Apply PROSE to docstrings/comments, leaving code (and backtick spans) untouched."""
    out = []
    i = 0
    # split into prose regions: /-- ... -/, /-! ... -/, /- ... -/, and `--` to end of line
    pat = re.compile(r'/-[-!]?.*?-/|--[^\n]*', re.S)
    for m in pat.finditer(t):
        out.append(t[i:m.start()])
        seg = m.group(0)
        parts = re.split(r'(`[^`\n]*`)', seg)
        for k in range(0, len(parts), 2):
            s = parts[k]
            for p, r in PROSE:
                s = p.sub(r, s)
            parts[k] = fix_articles(s)
        out.append(''.join(parts))
        i = m.end()
    out.append(t[i:])
    return ''.join(out)


if __name__ == '__main__':
    n = 0
    for f in sorted(ROOT.rglob('*.lean')):
        s = f.read_text()
        t = s
        for p, r in IDENT:
            t = p.sub(r, t)
        t = clean_prose(t)
        if t != s:
            f.write_text(t)
            n += 1
    print('files changed:', n)
