# FontaineWintenberger

Lean 4 + Mathlib formalization of Wintenberger, *Le corps des normes de certaines extensions
infinies de corps locaux; applications* (Ann. Sci. ENS 16, 1983): arithmetically profinite
extensions, the field of norms `X_K(L)`, and its Galois-theoretic properties. The
ramification-theoretic foundations follow Serre, *Local Fields*, Chapter IV.

## The five targets

Each result lives in its own module, as in Mathlib; the root file `FontaineWintenberger.lean`
lists them. Throughout, `K` is a complete discretely valued field with perfect residue field of
characteristic `p` (`IsPerfectResidueLocalField K`), `L/K` is a separable extension, and the
absolute Galois group is `Gal(K^sep/K)` (Mathlib's `Field.absoluteGaloisGroup K = Aut(K^alg/K)`
is isomorphic to it by restriction; see `Attic/AbsoluteGaloisGroupStatements.lean`).

| Target | Declaration (module) |
|---|---|
| 1. APF and strictly APF extensions (Wintenberger 1.2.1) | `IsAPF`, `isAPF_iff_isOpen_apfSubgroup` (`APF/Defs`); `IsStrictlyAPF`, `isStrictlyAPF_iff` (`APF/Strict`) |
| 2. The field of norms (2.1.1) | `FieldOfNorms K L` with instances `Field`, `Valued _ ℤᵐ⁰`, `CharP _ p` (`FieldOfNorms/Basic/Ring`) |
| 3. Theorem 2.1.3 | `CompleteSpace` (`Structure/Completeness`), `FieldOfNorms.instIsDiscreteValuationRing` (`Structure/Uniformizer`), `FieldOfNorms.residueEquiv : 𝓀[L] ≃+* 𝓀[X_K(L)]` (`Structure/ResidueEmbedding`) |
| 4. Theorem 3.1.2 and Corollary 3.2.3 | `FieldOfNorms.algHomEquiv : (M →ₐ[L] N) ≃ (X_K(M) →ₐ[X_K(L)] X_K(N))` (`Functor/FullyFaithful`), `FieldOfNorms.absoluteGaloisEquiv : Gal(L^sep/L) ≃ₜ* Gal(X_K(L)^sep/X_K(L))` (`Galois/AbsoluteGroup`) |
| 5. Remark 3.2.4 | `FieldOfNorms.aut` (`Functor/Map`); for any separable closure `Ω` of `K` containing `L`: `RelFieldOfNorms.absoluteAut : Gal(Ω/K) →* RingAut (X_{L/K}(Ω))` (`Galois/RelAction`), `RelFieldOfNorms.ambientGaloisEquiv : Gal(Ω/K) ≃* galoisSubgroup` (`Galois/Ambient`) |

## Layout

```
FontaineWintenberger/
  Mathlib/        general results with Mathlib naming and no project imports (upstream candidates)
  LocalField/     local fields, spectral norm, Hensel/Krasner, residue fields, Laurent coordinates
  Ramification/   Serre IV: lower/upper groups, Herbrand φ ψ, different, norms, embeddings
  APF/            Wintenberger §1: arithmetically profinite extensions
  FieldOfNorms/   Wintenberger §2–3: the field of norms, its structure, functoriality, Galois action
  Attic/          code without downstream use, built but not imported
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
`1e75e9dd53d483fa01eff9ac7d4ea0472ce9d1fa`; all transitive dependency commits
are recorded in `lake-manifest.json`. The library contains no `sorry` and builds without
warnings under Mathlib's standard linter set; every file compiles in under a minute.

See `CLAUDE.md` for the standing hypotheses and conventions, `docs/REFACTOR_PLAN.md` for the
design and its rationale, and `docs/MATHLIB_REUSE.md` for what is taken from Mathlib.

The source paper and Serre's *Local Fields* are not distributed with this repository.

## License

Apache 2.0, see `LICENSE`.
