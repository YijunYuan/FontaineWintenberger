# FontaineWintenberger

Lean 4 + Mathlib formalization of Wintenberger, *Le corps des normes de certaines extensions
infinies de corps locaux; applications* (Ann. Sci. ENS 16, 1983): arithmetically profinite
extensions, the field of norms `X_K(L)`, and its Galois-theoretic properties. The
ramification-theoretic foundations follow Serre, *Local Fields*, Chapter IV.

## The five targets

All five are stated in `FontaineWintenberger/Main.lean` as one-line consequences of library
declarations. Throughout, `K` is a complete discretely valued field with perfect residue field of
characteristic `p` (`IsPerfectResidueLocalField K`) and `L/K` is a separable extension.

| Target | Statement in `Main.lean` |
|---|---|
| 1. APF and strictly APF extensions (Wintenberger 1.2.1) | `IsAPF K L`, `isAPF_iff_isOpen_absoluteGaloisGroup`; `IsStrictlyAPF K L`, `isStrictlyAPF_iff_liminf_pos` |
| 2. The field of norms (2.1.1) | `FieldOfNorms K L` with instances `Field`, `Valued _ ℤᵐ⁰`, `CharP _ p` |
| 3. Theorem 2.1.3 | `FieldOfNorms.charP`, `FieldOfNorms.completeSpace`, `FieldOfNorms.isDiscreteValuationRing`, `FieldOfNorms.residueFieldEquiv : 𝓀[L] ≃+* 𝓀[X_K(L)]` |
| 4. Theorem 3.1.2 and Corollary 3.2.3 | `FieldOfNorms.homEquiv : (M →ₐ[L] N) ≃ (X_K(M) →ₐ[X_K(L)] X_K(N))`, `FieldOfNorms.absoluteGaloisGroupEquiv : G_L ≃ₜ* G_{X_K(L)}` |
| 5. Remark 3.2.4 | `FieldOfNorms.aut`; for any separable closure `Ω` of `K`: `RelFieldOfNorms.absoluteAut : Gal(Ω/K) →* RingAut (X_{L/K}(Ω))`, `RelFieldOfNorms.ambientGaloisEquiv`; for `Ω = K^sep`: `RelFieldOfNorms.absoluteGaloisGroupAction`, `RelFieldOfNorms.absoluteGaloisGroupEquiv` on `G_K` |

## Layout

```
FontaineWintenberger/
  Mathlib/        general results with Mathlib naming and no project imports (upstream candidates)
  LocalField/     local fields, spectral norm, Hensel/Krasner, residue fields, Laurent coordinates
  Ramification/   Serre IV: lower/upper groups, Herbrand φ ψ, different, norms, embeddings
  APF/            Wintenberger §1: arithmetically profinite extensions
  FieldOfNorms/   Wintenberger §2–3: the field of norms, its structure, functoriality, Galois action
  Attic/          code without downstream use, built but not imported
  Main.lean       the five target statements
FontaineWintenberger.lean   imports one aggregate file per layer
```

A layer imports only layers above it in this list; `scripts/check_aggregates.py` enforces this and
checks that every file is reachable from its layer's aggregate.

## Build

Install [elan](https://github.com/leanprover/elan), then run from this directory:

```sh
lake exe cache get
lake build
```

Lean is pinned to `leanprover/lean4:v4.35.0`. Mathlib is pinned to
`f0b4c8150aa0dbc758aff1291410c5ae335aff3a`; all transitive dependency commits
are recorded in `lake-manifest.json`. The library contains no `sorry` and builds without
warnings under Mathlib's standard linter set; every file compiles in under a minute.

See `CLAUDE.md` for the standing hypotheses and conventions, `docs/REFACTOR_PLAN.md` for the
design and its rationale, and `docs/MATHLIB_REUSE.md` for what is taken from Mathlib.

The source paper and Serre's *Local Fields* are not distributed with this repository.

## License

Apache 2.0, see `LICENSE`.
