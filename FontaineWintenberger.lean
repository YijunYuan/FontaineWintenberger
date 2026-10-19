/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Mathlib
public import FontaineWintenberger.LocalField
public import FontaineWintenberger.Ramification
public import FontaineWintenberger.APF
public import FontaineWintenberger.FieldOfNorms

/-!
# The field of norms (Fontaine–Wintenberger)

Formalization of Wintenberger, *Le corps des normes de certaines extensions infinies de corps
locaux; applications*. The five main statements, for a complete discretely valued field `K`
with perfect residue field (`IsPerfectResidueLocalField K`) and a separable extension `L/K`:

1. **Arithmetically profinite extensions** (1.2.1): `IsAPF K L`, `isAPF_iff_isOpen_apfSubgroup`;
   `IsStrictlyAPF K L`, `isStrictlyAPF_iff`.
2. **The field of norms** (2.1.1): `FieldOfNorms K L` with instances `Field`, `Valued _ ℤᵐ⁰`,
   `CharP _ (residueChar K)`.
3. **Theorem 2.1.3**: `CompleteSpace (FieldOfNorms K L)`,
   `FieldOfNorms.instIsDiscreteValuationRing`, `FieldOfNorms.residueEquiv : 𝓀[L] ≃+* 𝓀[X_K(L)]`.
4. **Theorem 3.1.2 and Corollary 3.2.3**: `FieldOfNorms.algHomEquiv`,
   `FieldOfNorms.absoluteGaloisEquiv : Gal(L^sep/L) ≃ₜ* Gal(X_K(L)^sep/X_K(L))`.
5. **Remark 3.2.4**: `FieldOfNorms.aut`, `RelFieldOfNorms.absoluteAut`,
   `RelFieldOfNorms.ambientGaloisEquiv`, for any separable closure `[IsSepClosure K Ω]`.
-/
