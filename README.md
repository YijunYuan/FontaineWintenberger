# FontaineWintenberger

Lean 4 formalization of the Fontaine–Wintenberger field-of-norms theory.

## Build

Install [elan](https://github.com/leanprover/elan), then run from this directory:

```sh
lake exe cache get
lake build
```

Lean is pinned to `leanprover/lean4:v4.35.0`. Mathlib is pinned to
`f0b4c8150aa0dbc758aff1291410c5ae335aff3a`; all transitive dependency commits
are recorded in `lake-manifest.json`. Dependencies are stored locally in
`.lake/packages`. This project does not require the original Arithmetic workspace.

The public entry point is `FontaineWintenberger.lean`. Blueprint sources and
their shared preamble and bibliography are in `blueprint/src/`.
