#!/usr/bin/env python3
"""D1: bring every module docstring to the Mathlib template by appending `## Main definitions`,
`## Main results` and `## References` sections (when missing) generated from the file's
top-level declarations and their docstrings. Existing prose and section headers are kept."""
import re, pathlib, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
SRC = ROOT / 'FontaineWintenberger'
LAYER_REF = {
    'Mathlib': '* Mathlib; this file is an upstream candidate and has no project-specific reference.',
    'LocalField': '* Serre, *Local Fields*, Chapters I–II (discrete valuation rings, completions, '
                  'unramified and totally ramified extensions).',
    'Ramification': '* Serre, *Local Fields*, Chapter IV (ramification groups, Herbrand functions, the '
                    'different).',
    'APF': '* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; '
           'applications*, §1 (extensions arithmétiquement profinies).',
    'FieldOfNorms': '* Wintenberger, *Le corps des normes de certaines extensions infinies de corps '
                    'locaux; applications*, §2–3 (le corps des normes, fonctorialité).',
}
DECL = re.compile(
    r'^(?P<doc>/--(?:(?!-/)(?:.|\n))*-/\n)?(?:@\[[^\]]*\]\n)?(?:private |protected )?(?:noncomputable )?'
    r'(?P<kind>def|abbrev|structure|class|instance|theorem|lemma) (?P<name>[^\s(:\[{]+)', re.M)

def first_sentence(doc: str) -> str:
    body = doc.strip()[3:-2].strip()
    body = re.sub(r'\s+', ' ', body)
    m = re.match(r'(.*?[.!?])(\s|$)', body)
    return (m.group(1) if m else body).strip()

def wrap(line: str, width: int = 100, indent: str = '  ') -> str:
    words = line.split(' '); out = []; cur = ''
    for w in words:
        if cur and len(cur) + 1 + len(w) > width:
            out.append(cur); cur = indent + w
        else:
            cur = (cur + ' ' + w) if cur else w
    out.append(cur)
    return '\n'.join(out)

def strip_generated(body: str, layer: str) -> str:
    """Remove sections produced by an earlier run, so the script is idempotent."""
    for header in ('## Main definitions', '## Main results'):
        while header in body:
            i = body.index(header)
            j = body.find('\n## ', i + 1)
            body = body[:i].rstrip('\n') + ('\n\n' + body[j + 1:] if j != -1 else '\n')
    ref = '## References\n\n' + wrap(LAYER_REF[layer])
    if body.rstrip('\n').endswith(ref):
        body = body.rstrip('\n')[:-len(ref)].rstrip('\n') + '\n'
    return body

# files whose `## Main …` sections are written by hand
SKIP = {'LocalField/Basic.lean', 'Mathlib/FieldTheory/AbsoluteGaloisGroup.lean'}

def process(path: pathlib.Path) -> bool:
    if str(path.relative_to(SRC)) in SKIP:
        return False
    text = path.read_text()
    m = re.search(r'^/-!\n(?P<body>(?:.|\n)*?)^-/\n', text, re.M)
    if not m:
        return False
    body = strip_generated(m.group('body'), path.relative_to(SRC).parts[0])
    rest = text[m.end():]
    rest = re.sub(r'/-!(?:.|\n)*?-/', '', rest)  # ignore nested doc blocks
    defs, thms = [], []
    for d in DECL.finditer(rest):
        if d.group('kind') == 'instance':
            continue
        name = d.group('name')
        if name.startswith('_root_.'):
            name = name[len('_root_.'):]
        sent = first_sentence(d.group('doc')) if d.group('doc') else ''
        bucket = thms if d.group('kind') in ('theorem', 'lemma') else defs
        if all(n != name for n, _ in bucket):
            bucket.append((name, sent))
    layer = path.relative_to(SRC).parts[0]
    sections = []
    if defs:
        items = [f'* `{n}`' + (f': {s}' if s else '') for n, s in defs[:8]]
        sections.append('## Main definitions\n\n' + '\n'.join(wrap(i) for i in items))
    if thms:
        with_doc = [t for t in thms if t[1]] or thms
        items = [f'* `{n}`' + (f': {s}' if s else '') for n, s in with_doc[:8]]
        sections.append('## Main results\n\n' + '\n'.join(wrap(i) for i in items))
    new_body = body.rstrip('\n')
    if '## References' in new_body:
        i = new_body.index('## References')
        new_body = new_body[:i].rstrip('\n') + '\n\n' + '\n\n'.join(sections) + '\n\n' + new_body[i:]
    else:
        ref = LAYER_REF[layer]
        new_body = new_body + '\n\n' + '\n\n'.join(sections + ['## References\n\n' + wrap(ref)])
    text = text[:m.start()] + '/-!\n' + new_body + '\n-/\n' + text[m.end():]
    path.write_text(text)
    return True

if __name__ == '__main__':
    n = 0
    for layer in LAYER_REF:
        for f in sorted((SRC / layer).rglob('*.lean')):
            n += process(f)
    print('files updated:', n)
