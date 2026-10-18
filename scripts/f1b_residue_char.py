#!/usr/bin/env python3
"""F1b: the residue characteristic `p` of the base field `K` is `residueChar K`.

In every file that threads `(p : ℕ) [Fact p.Prime] [CharP 𝓀[K] p]`:
* `[IsCompleteDiscreteValuedField K] [PerfectField 𝓀[K]]` → `[IsPerfectResidueLocalField K]`;
* the `p` variable block is deleted and `local notation "p" => residueChar K` is declared after the
  `K` header, so term-level uses (`p ^ n`, `p.Prime`, `(p : E)`) stay textually unchanged;
* `p` is removed where it is passed as an explicit argument to project declarations;
* `omit`/`include` lines are adjusted.
Declarations that bind their own generic prime `(p : ℕ)` are left alone (they are reported).
Run from the repository root: python3 scripts/f1b_residue_char.py
"""
import pathlib
import re

ROOT = pathlib.Path('FontaineWintenberger')
RES = r'\((?:IsLocalRing\.)?ResidueField\s*\(NormedField\.valuation \(K := K\)\)\.valuationSubring\)'
RES_NOPAREN = r'(?:IsLocalRing\.)?ResidueField\s*\(NormedField\.valuation \(K := K\)\)\.valuationSubring'
PBLOCK = re.compile(r'^variable \(p : ℕ\) \[Fact p\.Prime\]\s*\[CharP ' + RES + r' p\]\n', re.M)
PBLOCK2 = re.compile(r'^variable \(p : ℕ\) \[Fact p\.Prime\]\n', re.M)
CHARP_K = re.compile(r'\s*\[CharP ' + RES + r' p\]')
PF_K = re.compile(r'\s*\[PerfectField ' + RES + r'\]')
KHDR = re.compile(r'^(variable [({]K[^\n]*[)}] \[NontriviallyNormedField K\] )\[IsCompleteDiscreteValuedField K\]', re.M)
DECL = re.compile(r'^(@\[[^\n]*\]\s*)?((?:private |protected |noncomputable |local |scoped )*(?:theorem|lemma|def|abbrev|instance)\b)', re.M)
KEEP_HEADS = {'Nat.Coprime', 'IsPGroup', 'CharP', 'ZMod', 'Fact', 'Nat.Prime', 'Prime', 'ringChar', 'Nat.cast',
              'Polynomial.X', 'pow', 'nsmul', 'Irreducible', 'Nat.card', 'Fintype.card', 'Sylow', 'orderOf',
              'Nat.factorization', 'padicValNat', 'multiplicity', 'emultiplicity', 'Nat.lt', 'Nat.le'}
KEYWORDS = {'exact', 'apply', 'refine', "refine'", 'have', 'show', 'from', 'using', 'by', 'fun', 'intro', 'at',
            'with', 'obtain', 'rcases', 'simpa', 'calc', 'rw', 'simp', 'exacts', 'convert', 'use', 'let',
            'haveI', 'letI', 'then', 'else', 'if', 'of', 'in', 'rintro', 'induction', 'cases', 'suffices',
            'specialize', 'absurd', 'change', 'generalize', 'subst', 'revert', 'clear', 'set', 'omit',
            'include', 'variable', 'open', 'local', 'notation', 'match', 'return', 'do', 'where'}


FIELD_TOK = r"(?:[A-ZΩ][\w'.]*|\((?:[^()]|\([^()]*\))*\))"
KCHAIN = re.compile(r'(?<![\w\'.])(K(?: ' + FIELD_TOK + r')*) p\b(?![\w\'])')


def strip_p(line):
    """Remove `p` where it is passed to a project declaration: these calls always have the shape
    `K <field names> p` (e.g. `normLimitField K L p`, `finiteNormLimitRingHom K L N.val p`).
    Mathlib lemmas and generic-prime project lemmas never take `p` right after a chain of fields
    starting with `K`, so they keep their argument (the local notation `p` still denotes it)."""
    return KCHAIN.sub(lambda m: m.group(1), line)


DECL_LINE = re.compile(r'^(?:@\[[^\n]*\]\s*)?(?:private |protected |noncomputable |local |scoped )*(?:theorem|lemma|def|abbrev|instance)\s+([\w.\'₀-₉]+)', re.M)
BLOCK_START = re.compile(r'^(theorem|lemma|def|abbrev|instance|noncomputable|private|protected|local instance|scoped|@\[|/--|/-!|end|section|namespace|variable|omit|include|open|local notation|attribute|set_option)\b')


def blocks(lines):
    """(start, end, name) for every declaration block."""
    res = []
    i = 0
    while i < len(lines):
        m = DECL_LINE.match(lines[i])
        if m:
            j = i + 1
            while j < len(lines) and not BLOCK_START.match(lines[j]):
                j += 1
            res.append((i, j, m.group(1)))
            i = j
        else:
            i += 1
    return res


def remove_binders(s):
    s = KHDR.sub(lambda m: m.group(1) + '[IsPerfectResidueLocalField K]', s)
    s = PF_K.sub('', s)
    s = PBLOCK.sub('', s)
    s = re.sub(r' \(p : ℕ\) \[Fact p\.Prime\]\s*\[CharP ' + RES + r' p\]', '', s)
    s = CHARP_K.sub('', s)
    s = PBLOCK2.sub('', s)
    # tidy variable / omit / include commands
    s = re.sub(r'^variable[ \t]*\n(?=\n|[^ \t])', '', s, flags=re.M)
    s = re.sub(r'^(variable|omit|include)[ \t]*\n([ \t]+)(?=\S)', r'\1 ', s, flags=re.M)
    s = re.sub(r'^include p\n', '', s, flags=re.M)
    s = re.sub(r'^include p in\n', '', s, flags=re.M)
    s = re.sub(r'^omit p ', 'omit ', s, flags=re.M)
    s = re.sub(r'^omit p\n', '', s, flags=re.M)
    s = re.sub(r'^(include [^\n]*?) p\b', r'\1', s, flags=re.M)
    s = re.sub(r'\[IsCompleteDiscreteValuedField K\]', '[IsPerfectResidueLocalField K]', s)
    s = re.sub(r'^omit\s+in\n', '', s, flags=re.M)
    s = re.sub(r'^omit\s*\n', '', s, flags=re.M)
    return s


def add_notation(s):
    """`local notation "p" => residueChar K` after every bundled K header not already covered."""
    lines = s.split('\n')
    out = []
    depth = 0
    covered = []  # depths at which a notation is active
    i = 0
    while i < len(lines):
        ln = lines[i]
        out.append(ln)
        if re.match(r'^(section|namespace)\b', ln):
            depth += 1
        elif re.match(r'^end\b', ln):
            depth -= 1
            covered = [d for d in covered if d <= depth]
        if re.match(r'^variable [({]K[^\n]*[)}] \[NontriviallyNormedField K\] \[IsPerfectResidueLocalField K\]', ln):
            j = i + 1
            while j < len(lines) and lines[j].startswith((' ', '\t')) and lines[j].strip():
                out.append(lines[j])
                j += 1
            if not covered:
                out.append('')
                out.append('local notation "p" => residueChar K')
                covered.append(depth)
            i = j
            continue
        i += 1
    s = '\n'.join(out)
    return re.sub(r'\n{3,}', '\n\n', s)


def is_processed(s):
    return re.search(r'CharP ' + RES + r' p\]', s) is not None


def rename_generic(lines, blks):
    for a, b, _ in blks:
        blk = '\n'.join(lines[a:b])
        if re.search(r'\(p : ℕ\)', blk):
            blk = re.sub(r"(?<![\w'.])p(?![\w'])", 'q', blk)
            lines[a:b] = blk.split('\n')
    return lines



def sub(path, pairs):
    p = pathlib.Path(path)
    s = p.read_text()
    for a, b in pairs:
        assert a in s, (path, a[:60])
        s = s.replace(a, b, 1)
    p.write_text(s)


def strip_file(path):
    f = pathlib.Path(path)
    t = f.read_text()
    f.write_text('\n'.join(l if re.match(r'^\s*(variable|omit|include|open|local notation)\b', l) else strip_p(l).rstrip()
                           for l in t.split('\n')))


def manual():
    # residue characteristic of a finite Galois Ω/K is that of K
    sub('FontaineWintenberger/FieldOfNorms/TameNorms.lean', [(
        """variable (K Ω : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
""", """variable (K Ω : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
"""), ("""variable (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField (spectralIntegerRing K Ω)) p]
    (H : Subgroup (Ω ≃ₐ[K] Ω))
""", """variable (H : Subgroup (Ω ≃ₐ[K] Ω))
""")])
    f = pathlib.Path('FontaineWintenberger/FieldOfNorms/TameNorms.lean')
    f.write_text(add_notation(f.read_text()))
    strip_file('FontaineWintenberger/FieldOfNorms/TameNorms.lean')
    sub('FontaineWintenberger/FieldOfNorms/TameNorms.lean', [(
        'exists_apfRamificationBound_wild_compositum_of_totallyRamified K Ω H he n hd hdegree',
        'exists_apfRamificationBound_wild_compositum_of_totallyRamified K Ω p H he n hd hdegree')])


if __name__ == '__main__':
    files = sorted(ROOT.rglob('*.lean'))
    texts = {f: f.read_text() for f in files}
    processed = {f for f, t in texts.items() if is_processed(t)}
    # phase 1: binder removal in processed files; collect generic-prime declaration names everywhere
    generic = set()
    for f in files:
        t = texts[f]
        if f in processed:
            if not KHDR.search(t):
                print('!! no K header:', f)
                processed.discard(f)
                continue
            t = add_notation(remove_binders(t))
            texts[f] = t
        lines = t.split('\n')
        for a, b, name in blocks(lines):
            if re.search(r'\(p : ℕ\)', '\n'.join(lines[a:b])):
                generic.add(name)
    generic_pat = re.compile(r'\b(' + '|'.join(sorted(map(re.escape, generic), key=len, reverse=True)) + r')\b') if generic else None
    # phase 2: strip `p` arguments and rename generic binders
    changed = 0
    for f in processed:
        lines = texts[f].split('\n')
        blks = blocks(lines)
        lines = rename_generic(lines, blks)
        out = []
        for ln in lines:
            if re.match(r'^\s*(variable|omit|include|open|local notation)\b', ln) or ln.lstrip().startswith('--'):
                out.append(ln)
            elif generic_pat and generic_pat.search(ln):
                out.append(ln.rstrip())
            else:
                out.append(strip_p(ln).rstrip())
        t = '\n'.join(out)
        t = re.sub(r' +\)', ')', t)
        f.write_text(t)
        changed += 1
    manual()
    print('files changed:', changed)
    print('generic-prime declarations:', len(generic))
