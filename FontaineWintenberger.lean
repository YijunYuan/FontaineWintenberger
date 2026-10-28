/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF
public import FontaineWintenberger.FieldOfNorms
public import FontaineWintenberger.LocalField
public import FontaineWintenberger.Mathlib
public import FontaineWintenberger.Ramification

/-!
# The field of norms (Fontaine–Wintenberger)

Formalization of Wintenberger, *Le corps des normes de certaines extensions infinies de corps
locaux; applications*. The main statements, for a complete discretely valued field `K`
with perfect residue field (`IsPerfectResidueLocalField K`) and a separable extension `L/K`.
The field-of-norms statements assume that `L/K` is infinite and APF; the ambient Galois action
in item 5 also assumes that `L/K` is Galois.

1. **Arithmetically profinite extensions** (1.2.1): `IsAPF K L`, `isAPF_iff_isOpen_apfSubgroup`;
   `IsStrictlyAPF K L`, `isStrictlyAPF_iff`.
2. **The field of norms** (2.1.1, 2.1.3): norm-compatible families `FieldOfNorms K L` with
   instances `Field`, `Valued _ ℤᵐ⁰`, `CharP _ (residueChar K)`.
3. **Theorem 2.1.3**: `CompleteSpace (FieldOfNorms K L)`,
   `FieldOfNorms.instIsDiscreteValuationRing`, `FieldOfNorms.residueEquiv : 𝓀[L] ≃+* 𝓀[X_K(L)]`.
4. **Theorem 3.2.2 (ii) and Corollary 3.2.3**: `FieldOfNorms.algHomEquiv` for finite separable
   extensions of `L`,
   `FieldOfNorms.absoluteGaloisEquiv : Gal(L^sep/L) ≃ₜ* Gal(X_K(L)^sep/X_K(L))`.
5. **Remark 3.2.4**: `FieldOfNorms.aut`, `RelFieldOfNorms.absoluteAut`,
   `RelFieldOfNorms.ambientGaloisEquiv`, for any separable closure `[IsSepClosure K Ω]`.
6. **The elementary tower (§1.4.1)**: `apfElementaryStage`, `apfElementaryLevel`,
   `isElementaryStep_apfElementaryStage`, `iSup_apfElementaryStage`,
   `tendsto_apfElementaryLevel`; the formulas `apfRamificationBound_eq_apfElementaryLevel`
   and `apfStrictnessConstant_eq_iInf_apfElementaryLevel` assume a positive first bound.
   `isStrictlyAPF_iff_apfElementaryLevel_div_finrank` also allows an initial tame part.
   `apfFiniteElementaryStage` and `apfStrictnessConstant_eq_iInf_apfFiniteElementaryLevel`
   handle finite terminating towers.
7. **Remark 1.4.2**: `isAPF_iSup_iff_tendsto_of_elementary_tower`, the weighted formula
   `apfPhi_eq_sum_of_isElementaryStep`, and the canonical identification
   `apfElementaryStage_iSup_eq_of_isElementaryStep`; finite towers are identified by
   `exists_apfFiniteElementaryStage_eq_of_isElementaryStep`.
8. **Corollary 3.3.6**: `RelFieldOfNorms.map_normUpperRamificationGroup` compares upper
   ramification through `RelFieldOfNorms.autEquiv`, for any Galois extension `M/K` containing `L`.
-/
