# FontaineWintenberger — notes for agents and contributors

Lean 4 (`leanprover/lean4:v4.35.0`, module system) + Mathlib formalization of
Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
applications* (Ann. Sci. ENS 1983). Scope: the five targets in `docs/REFACTOR_PLAN.md` §0
(APF / strict APF, the field of norms X_K(L), Thm 2.1.3, Thm 3.1.2 + Cor 3.2.3, Rem 3.2.4).
Ramification-group foundations follow Serre, *Local Fields*, Chapter IV.

Code and docstrings are in English. Terminology: "arithmetically profinite (APF)",
"field of norms" (`FieldOfNorms`, never "norm limit").

## Build

```sh
lake exe cache get      # Mathlib oleans
lake build              # everything
lake build FontaineWintenberger.APF.Defs   # one module
```

**Performance red line: a single file must compile in under 60 s (target: under 20 s).**
When editing, build only the touched module with `timeout 120 lake build <Module>`.
A timeout means the design is wrong (usually an instance being rebuilt by `letI`), not that
you should wait longer. Timings of the last full build are in `.lake/standalone-build.log`.

No `sorry`, no `set_option maxHeartbeats`, no warnings (the lakefile enables Mathlib's
standard linter set).

## Layout and layering

```
FontaineWintenberger/
  Mathlib/        upstream candidates (zero project imports): GroupTheory, FieldTheory
                  (incl. FiniteIntermediateField), RingTheory, Analysis, Topology
  LocalField/     Basic (base-field classes), Spectral/, Hensel/, Residue/, Laurent/
  Ramification/   Serre IV: Lower/, Herbrand/, Upper/, Infinite/, Different/, Norm/, Fields/, Embedding/
  APF/            Wintenberger §1: Defs, Index, Herbrand, Strict, Finite/, BaseChange/, Elementary/, Tower/
  FieldOfNorms/   Wintenberger §2–3, in import order: Layers/, Estimates/, Basic/, Structure/,
                  Functor/, Relative/, Galois/
  Attic/          code without downstream use, kept for review; built, not imported
  Main.lean       the five final statements with clean signatures
FontaineWintenberger.lean   imports one aggregate file per layer
```

`scripts/b1_mapping.py` records where every pre-reorganization file went.
`python3 scripts/check_aggregates.py` (run in CI) verifies both rules above.

A layer may import only layers above it in this list. Never import `APF` or
`FieldOfNorms` from `Ramification` or `LocalField`. Every `.lean` file must be imported by
its layer's aggregate file (`FontaineWintenberger/<Layer>.lean`).

## Standing hypotheses and notation

```lean
open scoped NormedField Valued NNReal
variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]   -- or IsCompleteDiscreteValuedField K
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L] [IsAPF K L] [Fact (¬ Module.Finite K L)]
```

- `𝒪[K]`, `𝓀[K]`: scoped notations of `namespace FontaineWintenberger` (declared in
  `LocalField/Basic.lean`) for `(NormedField.valuation (K := K)).valuationSubring` and its residue
  field; definitionally Mathlib's `Valued.integer K` / `Valued.ResidueField K`. Do not write the
  expanded form by hand, and do not introduce file-local abbreviations (`OK`, `R`, `O`, …) for it.
  Files in `FontaineWintenberger/Mathlib/` do not import `LocalField/Basic.lean` and spell it out.
- `residueChar K := ringChar 𝓀[K]`; never thread a separate `(p : ℕ) [Fact p.Prime]`.
- Finite extensions `L/K` get their spectral norm from the scoped instances in
  `LocalField/Spectral/Instances.lean`; their integer ring is `𝒪[L]`.
- The absolute Galois group is `Gal(SeparableClosure K/K)` internally (Mathlib's `Gal(·/·)`
  notation) and `Field.absoluteGaloisGroup K` in public statements (K may be imperfect, so
  `K^alg/K` is not Galois and Mathlib's infinite Galois theory needs `K^sep`). The Galois
  action on the field of norms (`FieldOfNorms/Galois/`) is stated for an arbitrary separable
  closure `{Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]` with
  `L : IntermediateField K Ω`; only the definition of `IsAPF` (`APF/`) fixes `SeparableClosure K`.
- `IsAPF`, `IsStrictlyAPF` are classes. `FieldOfNorms K L`, `RelFieldOfNorms K L M` are `def`s
  with genuine instances (`Field`, `Valued _ ℤᵐ⁰`, `CharP`, `CompleteSpace`, …). Never install
  these with `letI`; if an instance is missing, add it where the type is defined.

## Naming

Mathlib conventions: `lowerCamelCase` for defs, `snake_case` for theorems, `IsFoo` for Prop
classes, dot-notation namespaces (`FieldOfNorms.coord`, `FieldOfNorms.map`). No filler words
("actual", "original", "genuine", "source") in identifiers or docstrings. Module docstrings
follow the Mathlib template with a `## References` section citing Serre IV §n or
Wintenberger §n.m.k.

## Working style

Discuss design changes before executing them; record decisions in `docs/REFACTOR_PLAN.md`.
Dead code is moved to `Attic/`, not deleted.
