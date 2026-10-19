#!/usr/bin/env python3
"""Structural checks on the source tree (run in CI):

* every `.lean` file under `FontaineWintenberger/<Layer>/` is imported by its layer's aggregate file
  `FontaineWintenberger/<Layer>.lean`, and the root `FontaineWintenberger.lean` imports every aggregate;
  files under `FontaineWintenberger/Attic/` are exempt (built through the lakefile glob, not imported);
* a layer imports only layers above it in the order
  Mathlib < LocalField < Ramification < APF < FieldOfNorms < Attic.

Exit status 1 on any violation."""
import pathlib, re, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
SRC = ROOT / 'FontaineWintenberger'
LAYERS = ['Mathlib', 'LocalField', 'Ramification', 'APF', 'FieldOfNorms']
IMPORT = re.compile(r'^(?:public )?import (FontaineWintenberger\.[\w.]+)', re.M)

def module(path: pathlib.Path) -> str:
    return 'FontaineWintenberger.' + '.'.join(path.relative_to(SRC).with_suffix('').parts)

bad = []
for layer in LAYERS:
    agg = SRC / f'{layer}.lean'
    if not agg.exists():
        bad.append(f'missing aggregate {agg}'); continue
    imported = set(IMPORT.findall(agg.read_text()))
    for f in sorted((SRC / layer).rglob('*.lean')):
        if module(f) not in imported:
            bad.append(f'{f.relative_to(ROOT)} is not imported by {agg.relative_to(ROOT)}')
    for m in imported:
        if not m.startswith(f'FontaineWintenberger.{layer}.'):
            bad.append(f'{agg.relative_to(ROOT)} imports {m} outside its layer')
RANK = {layer: i for i, layer in enumerate(LAYERS + ['Attic'])}
for f in sorted(SRC.rglob('*.lean')):
    parts = f.relative_to(SRC).parts
    if len(parts) < 2 or parts[0] not in RANK:
        continue
    for m in re.findall(r'^(?:public )?import FontaineWintenberger\.(\w+)', f.read_text(), re.M):
        if m in RANK and RANK[m] > RANK[parts[0]]:
            bad.append(f'{f.relative_to(ROOT)} imports the lower layer {m}')
root = ROOT / 'FontaineWintenberger.lean'
root_imports = set(IMPORT.findall(root.read_text()))
for layer in LAYERS:
    if f'FontaineWintenberger.{layer}' not in root_imports:
        bad.append(f'FontaineWintenberger.lean does not import FontaineWintenberger.{layer}')
for name in bad:
    print(name)
print(f'{len(bad)} problem(s)' if bad else 'aggregate coverage and layering OK')
sys.exit(1 if bad else 0)
