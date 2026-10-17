# Mathlib reuse ledger

Pinned Mathlib: `f0b4c8150aa0dbc758aff1291410c5ae335aff3a` (Lean `v4.35.0`). This file records what
the project takes from Mathlib directly, what it wraps and should stop wrapping, and what it has
proved that belongs upstream. Keep it current when the pin moves.

## Used directly

| Role | Mathlib |
|---|---|
| Nonarchimedean normed field, valuation `‖·‖₊` | `NormedField.valuation`, `NormedField.toValued` (scoped), `IsUltrametricDist` |
| Integers and residue field | `𝒪[K]` = `Valued.integer`, `𝓀[K]` = `Valued.ResidueField` |
| Spectral norm on algebraic extensions | `spectralNorm`, `spectralNorm.nontriviallyNormedField`, `spectralNorm.normedAlgebra`, `spectralNorm.completeSpace` |
| Krasner's lemma | `IsKrasner`, `IsKrasner.of_completeSpace` |
| Henselian rings, adic completeness | `HenselianLocalRing`, `IsAdicComplete.henselianRing` |
| Discrete valuations | `IsDiscreteValuationRing`, `Valuation.IsRankOneDiscrete`, `Valuation.IsUniformizer`, `Valuation.valuationSubring_isDiscreteValuationRing` |
| Valuation extension | `Valuation.HasExtension` and its `integer` algebra instances |
| Decomposition and inertia | `ValuationSubring.decompositionSubgroup`, `ValuationSubring.inertiaSubgroup`, `Ideal.inertia`, `Ideal.card_inertia_eq_ramificationIdxIn`, `IsInertiaField` |
| Ramification index, inertia degree | `Ideal.ramificationIdx`, `Ideal.inertiaDeg`, `Ideal.ramificationIdx_tower`, `Ideal.inertiaDeg_eq_of_isMaximal` |
| Different, trace dual | `differentIdeal`, `conductor_mul_differentIdeal`, `aeval_derivative_mem_differentIdeal`, `traceDual` |
| Infinite Galois theory (on `K^sep`) | `InfiniteGalois.*`, `IntermediateField.fixingSubgroup`, `FiniteGaloisIntermediateField`, `krullTopology_t2` |
| Absolute Galois group | `Field.absoluteGaloisGroup` (public statements), `Gal(·/·)` notation |
| Separable closure | `SeparableClosure`, `IsSepClosed.lift`, `separableClosure.isPurelyInseparable`, `AlgEquiv.restrictNormalHom_surjective` |
| Laurent and power series | `LaurentSeries`, `PowerSeries`, `MvPowerSeries.continuous_subst` |
| Teichmüller | `Perfection.teichmuller₀` |
| Direct limits of fields | `DirectLimit`, `DirectLimit.Ring.of`, `DirectLimit.Ring.lift` |
| Order isomorphisms from strictly monotone maps | `StrictMonoOn.orderIsoOfSurjective` |

## Project wrappers to remove (replace by the Mathlib name)

`krasner_mem_adjoin` → `IsKrasner.krasner`; `local_ramificationIdx_tower` → `Ideal.ramificationIdx_tower`;
`local_inertiaDeg_eq_finrank_residueField` → `Ideal.inertiaDeg_eq_of_isMaximal`;
`localResidue_normal` → `Ideal.Quotient.normal`; `card_lowerRamificationGroup_zero` →
`Ideal.card_inertia_eq_ramificationIdxIn`; `IntermediateField.fixedField_isGaloisGroup` →
`IsGaloisGroup.subgroup`; `nonempty_separablyClosed_embeddings` → `IsSepClosed.lift`;
`exists_aut_extends_*` → `AlgHom.liftNormal`; `IntermediateField.completeSpace_of_finiteDimensional` →
`FiniteDimensional.complete`; `herbrandOrderIso` → `StrictMonoOn.orderIsoOfSurjective`;
`upperRamificationEquivToLimit` → align with `InfiniteGalois.mulEquivToLimit`;
`normLimitUniformizer_isUniformizer` → `Valuation.IsUniformizer`;
`[IsDiscreteValuationRing val.v.valuationSubring]` next to `[IsRankOneDiscrete val.v]` → redundant.

## Not in Mathlib (kept here, upstream candidates live in `FontaineWintenberger/Mathlib/`)

- Lower and upper ramification groups, Herbrand's φ and ψ, Herbrand's theorem (Serre IV).
- `Field.absoluteGaloisGroup K ≃ₜ* Gal(SeparableClosure K/K)` and `CompactSpace (absoluteGaloisGroup K)`
  for possibly imperfect `K`.
- Newton–Hensel with a non-unit derivative (generalising `NumberTheory/Padics/Hensel.lean`).
- Monogenicity of finite extensions of Henselian DVRs with separable residue extension (Serre III §6).
- `Polynomial.Monic.discr_map`, `Polynomial.sq_sub_dvd_discr`, `Algebra.norm` under base change.
- Linear disjointness from minimal-polynomial descent; normal closure of an arbitrary intermediate field.
- `isAdicComplete_of_isNilpotent_ideal`; equal-characteristic Cohen isomorphism `k⟦X⟧ ≃+* R`.
- Subgroup index lemmas (`relIndex_sup_sup_normal`, `finiteIndex_iff_comap_of_range`, prime chains).
- `fixingSubgroup_relIndex_eq_finrank`; `finiteGaloisMap`/`finiteGaloisLift` for `FiniteGaloisIntermediateField`.
- `Valued.completeSpace_of_completeSpace_valuationSubring`; sequential inverse limits.

## Deliberately not used

- `IsNonarchimedeanLocalField`: requires local compactness, i.e. a finite residue field. The project
  only assumes a perfect residue field (`IsPerfectResidueLocalField`).
- `ValuativeRel`-based discrete valuation classes: the spectral-norm API the project relies on is
  stated for normed fields. A bridge can be added if Mathlib's local-field API grows there.
