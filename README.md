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
are recorded in `lake-manifest.json`.

The public entry point is `FontaineWintenberger.lean`. See `CLAUDE.md` for the module
layout, standing hypotheses and conventions, `docs/REFACTOR_PLAN.md` for the design and
its rationale, and `docs/MATHLIB_REUSE.md` for what is taken from Mathlib.

The source paper (Wintenberger, *Le corps des normes de certaines extensions infinies de
corps locaux; applications*, Ann. Sci. ENS 16 (1983)) and Serre's *Local Fields* are not
distributed with this repository.

## License

Apache 2.0, see `LICENSE`.
