/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.BaseChange.Strict
public import FontaineWintenberger.APF.Finite.Nonnormal
public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Ramification.Embedding.Basic
public import FontaineWintenberger.Ramification.Upper.CosetMax

/-!
# Nonnormal finite embedding comparisons

Tate averages, maximal fixing cosets, intrinsic Herbrand bounds and strict
pair comparisons use the finite spectral integer rings. Intermediate
fields need neither be normal nor be preserved by the chosen automorphism.

## Main results

* `min_integralEmbeddingOrder_le`: Three ring maps satisfy the ultrametric inequality on their full
  integral displacement infima.
* `integralEmbeddingOrder_eq_min_of_ne`: Distinct displacement orders force equality in the pair
  ultrametric inequality, without automorphism or stability hypotheses.
* `generator_pair_sub_dvd`: A generator controls displacements of two arbitrary algebra maps,
  including maps with different images.
* `generator_pair_sub_dvd_eval_map`: Coefficient displacements give the first divisibility of the
  arbitrary-embedding Tate identity in the ambient integer ring.
* `eval_map_minpoly_dvd_generator_pair_sub`: Monic division proves the reverse Tate divisibility for
  an embedding into the ambient ring; the intermediate field need not be stable.
* `associated_generator_pair_sub_eval_map_minpoly`: Both arbitrary-embedding Tate displacements are
  associated, including the zero and identical-embedding cases.
* `addVal_generator_pair_sub_eq_eval_map_minpoly`: Tate's arbitrary-map displacements have equal
  normalized valuation; no extension-stability or automorphism premise is present.
* `eval_map_minpoly_eq_prod_displacements_embedding`: The Galois product can be twisted into the
  ambient ring by an automorphism which need not preserve the intermediate field.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §1 (extensions arithmétiquement profinies).
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

open scoped ENNReal

section PairTriangle

variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain S]
    [IsDiscreteValuationRing S]

/-- Three ring maps satisfy the ultrametric inequality on their
full integral displacement infima. -/
theorem min_integralEmbeddingOrder_le (f g h : R →+* S) :
    min (integralEmbeddingOrder f g) (integralEmbeddingOrder g h) ≤
      integralEmbeddingOrder f h := by
  apply le_iInf
  intro x
  have he : f x - h x = (f x - g x) + (g x - h x) := by ring
  rw [he]
  exact (min_le_min (integralEmbeddingOrder_le f g x)
    (integralEmbeddingOrder_le g h x)).trans (IsDiscreteValuationRing.addVal_add (R := S))

/-- Distinct displacement orders force equality in the pair
ultrametric inequality, without automorphism or stability hypotheses. -/
theorem integralEmbeddingOrder_eq_min_of_ne (f g h : R →+* S)
    (hne : integralEmbeddingOrder f g ≠ integralEmbeddingOrder g h) :
    integralEmbeddingOrder f h =
      min (integralEmbeddingOrder f g) (integralEmbeddingOrder g h) := by
  have h₁ := min_integralEmbeddingOrder_le f g h
  have h₂ := min_integralEmbeddingOrder_le f h g
  have h₃ := min_integralEmbeddingOrder_le g f h
  rw [integralEmbeddingOrder_comm h g] at h₂
  rw [integralEmbeddingOrder_comm g f] at h₃
  rcases lt_or_gt_of_ne hne with hlt | hlt <;> order

end PairTriangle

section EmbeddingTate

open Polynomial

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

omit [Algebra A B] [IsScalarTower R A B] in
/-- A generator controls displacements of two arbitrary algebra maps,
including maps with different images. -/
theorem generator_pair_sub_dvd (f g : A →ₐ[R] B) {y : A}
    (hy : Algebra.adjoin R {y} = ⊤) (c : A) : f y - g y ∣ f c - g c := by
  apply Ideal.mem_span_singleton.mp
  exact ((forall_sub_mem_iff_generator f g hy (Ideal.span {f y - g y})).mpr
    (Ideal.subset_span (by simp))) c

/-- Coefficient displacements give the first divisibility of the
arbitrary-embedding Tate identity in the ambient integer ring. -/
theorem generator_pair_sub_dvd_eval_map (f : A →ₐ[R] B) {y : A}
    (hy : Algebra.adjoin R {y} = ⊤) (x : B) (P : A[X])
    (hP : aeval x P = 0) :
    f y - algebraMap A B y ∣ (P.map f.toRingHom).eval x := by
  have hd : C (f y - algebraMap A B y) ∣
      P.map f.toRingHom - P.map (algebraMap A B) := by
    apply (C_dvd_iff_dvd_coeff _ _).mpr
    intro n
    simp only [coeff_sub, coeff_map]
    exact generator_pair_sub_dvd f (IsScalarTower.toAlgHom R A B) hy (P.coeff n)
  have he := Polynomial.eval_dvd (x := x) hd
  simpa only [eval_C, eval_sub, eval_map, ← aeval_def, hP, sub_zero] using he

variable [IsDomain A] [IsIntegrallyClosed A] [IsDomain B] [Module.IsTorsionFree A B]

/-- Monic division proves the reverse Tate divisibility for an
embedding into the ambient ring; the intermediate field need not be stable. -/
theorem eval_map_minpoly_dvd_generator_pair_sub (f : A →ₐ[R] B) {x : B}
    (hx : Algebra.adjoin R {x} = ⊤) (hint : IsIntegral A x) (y : A) :
    ((minpoly A x).map f.toRingHom).eval x ∣ f y - algebraMap A B y := by
  have hsurj := hx
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top] at hsurj
  obtain ⟨g, hg⟩ := hsurj (algebraMap A B y)
  have hz : aeval x (g.map (algebraMap R A) - C y) = 0 := by
    rw [map_sub, aeval_map_algebraMap, aeval_C, hg, sub_self]
  obtain ⟨q, hq⟩ := minpoly.isIntegrallyClosed_dvd hint hz
  have hfix : (g.map (algebraMap R A)).map f.toRingHom =
      g.map (algebraMap R B) := by
    rw [map_map]
    congr 1
    ext r
    exact f.commutes r
  have h := congrArg (fun P : A[X] => (P.map f.toRingHom).eval x) hq
  rw [Polynomial.map_sub, Polynomial.map_C, hfix, eval_sub, eval_map,
    ← aeval_def, hg, eval_C, Polynomial.map_mul, eval_mul] at h
  have hd : ((minpoly A x).map f.toRingHom).eval x ∣ algebraMap A B y - f y := ⟨_, h⟩
  simpa only [neg_sub] using dvd_neg.mpr hd

/-- Both arbitrary-embedding Tate displacements are associated,
including the zero and identical-embedding cases. -/
theorem associated_generator_pair_sub_eval_map_minpoly (f : A →ₐ[R] B)
    {x : B} {y : A} (hx : Algebra.adjoin R {x} = ⊤)
    (hy : Algebra.adjoin R {y} = ⊤) (hint : IsIntegral A x) :
    Associated (f y - algebraMap A B y) (((minpoly A x).map f.toRingHom).eval x) :=
  associated_of_dvd_dvd
    (generator_pair_sub_dvd_eval_map f hy x (minpoly A x) (minpoly.aeval A x))
    (eval_map_minpoly_dvd_generator_pair_sub f hx hint y)

/-- Tate's arbitrary-map displacements have equal normalized
valuation; no extension-stability or automorphism premise is present. -/
theorem addVal_generator_pair_sub_eq_eval_map_minpoly [IsDiscreteValuationRing B]
    (f : A →ₐ[R] B) {x : B} {y : A} (hx : Algebra.adjoin R {x} = ⊤)
    (hy : Algebra.adjoin R {y} = ⊤) (hint : IsIntegral A x) :
    IsDiscreteValuationRing.addVal B (f y - algebraMap A B y) =
      IsDiscreteValuationRing.addVal B (((minpoly A x).map f.toRingHom).eval x) := by
  have h := associated_generator_pair_sub_eval_map_minpoly f hx hy hint
  exact le_antisymm (IsDiscreteValuationRing.addVal_le_iff_dvd.mpr h.dvd)
    (IsDiscreteValuationRing.addVal_le_iff_dvd.mpr h.symm.dvd)

/-- The Galois product can be twisted into the ambient ring by
an automorphism which need not preserve the intermediate field. -/
theorem eval_map_minpoly_eq_prod_displacements_embedding
    (H : Type*) [Group H] [Fintype H] [MulSemiringAction H B] [IsGaloisGroup H A B]
    (σ : B ≃ₐ[R] B) {x : B} (hx : Algebra.adjoin R {x} = ⊤) :
    ((minpoly A x).map (σ.toRingHom.comp (algebraMap A B))).eval x =
      ∏ h : H, (x - σ (h • x)) := by
  rw [← map_map, map_minpoly_eq_prod_conjugates H
    (adjoin_singleton_eq_top_over_intermediate hx)]
  simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    eval_prod, eval_sub, eval_X, eval_C]
  rfl

/-- The full raw pair infimum is the coset sum, including nonnormal
intermediate fields and intermediate fields not preserved by the chosen element. -/
theorem integralEmbeddingOrder_eq_sum_coset [IsDiscreteValuationRing B]
    (G : Type*) [Group G] [MulSemiringAction G B] [SMulCommClass G R B]
    (H : Subgroup G) [Fintype H] [IsGaloisGroup H A B] (σ : G)
    {x : B} {y : A} (hx : Algebra.adjoin R {x} = ⊤)
    (hy : Algebra.adjoin R {y} = ⊤) :
    integralEmbeddingOrder
        ((MulSemiringAction.toAlgAut G R B σ).toAlgHom.comp
          (IsScalarTower.toAlgHom R A B)).toRingHom
        (IsScalarTower.toAlgHom R A B).toRingHom =
      ∑ h : H, ramificationOrder (R := B) G (σ * h.1) := by
  have := Algebra.IsInvariant.isIntegral A B H
  rw [integralEmbeddingOrder_eq_generator _ _ hy]
  change IsDiscreteValuationRing.addVal B
    (((MulSemiringAction.toAlgAut G R B σ).toAlgHom.comp
      (IsScalarTower.toAlgHom R A B)) y - algebraMap A B y) = _
  rw [addVal_generator_pair_sub_eq_eval_map_minpoly
    ((MulSemiringAction.toAlgAut G R B σ).toAlgHom.comp
      (IsScalarTower.toAlgHom R A B)) hx hy (Algebra.IsIntegral.isIntegral x)]
  change IsDiscreteValuationRing.addVal B
    (((minpoly A x).map ((MulSemiringAction.toAlgAut G R B σ).toRingHom.comp
      (algebraMap A B))).eval x) = _
  rw [eval_map_minpoly_eq_prod_displacements_embedding (A := A) H
    (MulSemiringAction.toAlgAut G R B σ) hx]
  calc
    _ = ∑ h : H, IsDiscreteValuationRing.addVal B
        (x - (MulSemiringAction.toAlgAut G R B σ) (h • x)) :=
      map_prod (IsDiscreteValuationRing.addVal B).toMonoidHom _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro h _
      rw [← neg_sub ((MulSemiringAction.toAlgAut G R B σ) (h • x)) x,
        AddValuation.map_neg]
      change IsDiscreteValuationRing.addVal B (σ • (h.1 • x) - x) = _
      simpa only [mul_smul] using (ramificationOrder_eq_generator G hx (σ * h.1)).symm

end EmbeddingTate

section FiniteGaloisAmbient

variable (K Ω : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
    [Field Ω] [Algebra K Ω] [FiniteDimensional K Ω] [IsGalois K Ω]
variable (H : Subgroup (Ω ≃ₐ[K] Ω))

local notation "F₀" => IntermediateField.fixedField H
local notation "A₀" => spectralIntegerRing K F₀
local notation "B₀" => spectralIntegerRing K Ω

/-- Galois descent on the spectral integer rings of the
fixed field, without any normality hypothesis on the fixing subgroup. -/
theorem fixedField_spectralInteger_isGaloisGroup :
    letI : Algebra A₀ B₀ := (spectralIntegerInclusion K (F₀).val).toRingHom.toAlgebra
    IsGaloisGroup H A₀ B₀ := by
  let : Algebra A₀ B₀ := (spectralIntegerInclusion K (F₀).val).toRingHom.toAlgebra
  let : IsScalarTower 𝒪[K] A₀ B₀ := IsScalarTower.of_algebraMap_eq (fun r => by
    exact ((spectralIntegerInclusion K (F₀).val).commutes r).symm)
  let : IsScalarTower A₀ F₀ Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower A₀ B₀ Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : Algebra.IsIntegral A₀ B₀ := Algebra.IsIntegral.tower_top 𝒪[K]
  let : SMulDistribClass H B₀ Ω :=
    { smul_distrib_smul := fun h x z => by
        change (h : Ω ≃ₐ[K] Ω) ((x : Ω) * z) =
          ((h • x : B₀) : Ω) * (h : Ω ≃ₐ[K] Ω) z
        exact map_mul (h : Ω ≃ₐ[K] Ω) (x : Ω) z }
  exact IsGaloisGroup.of_isFractionRing H A₀ B₀ F₀ Ω

/-- The arbitrary-embedding coset identity on finite spectral
integers; in particular the fixed field need not be preserved. -/
theorem embeddingIntegralOrder_fixedField_eq_sum (σ : Ω ≃ₐ[K] Ω) :
    letI := Fintype.ofFinite H
    embeddingIntegralOrder K (σ.toAlgHom.comp (F₀).val) (F₀).val =
      ∑ h : H, ramificationOrder (R := B₀) (Ω ≃ₐ[K] Ω) (σ * h.1) := by
  let : Algebra A₀ B₀ := (spectralIntegerInclusion K (F₀).val).toRingHom.toAlgebra
  let : IsScalarTower 𝒪[K] A₀ B₀ := IsScalarTower.of_algebraMap_eq (fun r => by
    exact ((spectralIntegerInclusion K (F₀).val).commutes r).symm)
  let := Fintype.ofFinite H
  let : IsGaloisGroup H A₀ B₀ := fixedField_spectralInteger_isGaloisGroup K Ω H
  let : FaithfulSMul A₀ B₀ := (faithfulSMul_iff_algebraMap_injective A₀ B₀).mpr (by
    intro a b hab
    apply Subtype.ext
    exact (F₀).val.injective (congrArg (fun z : B₀ => (z : Ω)) hab))
  obtain ⟨x, hx⟩ := spectralIntegerRing_exists_generator K Ω
  obtain ⟨y, hy⟩ := spectralIntegerRing_exists_generator K F₀
  have hf : spectralIntegerInclusion K (σ.toAlgHom.comp (F₀).val) =
      (MulSemiringAction.toAlgAut (Ω ≃ₐ[K] Ω) 𝒪[K] B₀ σ).toAlgHom.comp
        (IsScalarTower.toAlgHom 𝒪[K] A₀ B₀) := by
    ext a
    rfl
  have hg : spectralIntegerInclusion K (F₀).val = IsScalarTower.toAlgHom 𝒪[K] A₀ B₀ := by
    ext a
    rfl
  rw [embeddingIntegralOrder, hf, hg]
  exact integralEmbeddingOrder_eq_sum_coset (Ω ≃ₐ[K] Ω) H σ hx hy

/-- The normalized arbitrary-embedding average has the
relative ramification index as its positive finite denominator. -/
theorem embeddingRamificationOrder_fixedField_eq_sum_div (σ : Ω ≃ₐ[K] Ω) :
    letI := Fintype.ofFinite H
    embeddingRamificationOrder K (σ.toAlgHom.comp (F₀).val) (F₀).val =
      (∑ h : H, (ramificationOrder (R := B₀) (Ω ≃ₐ[K] Ω) (σ * h.1) : ℝ≥0∞)) /
        embeddingRamificationIdx K (F₀).val := by
  let := Fintype.ofFinite H
  rw [embeddingRamificationOrder, embeddingIntegralOrder_fixedField_eq_sum K Ω H σ,
    embeddingRamificationIdx_eq K (σ.toAlgHom.comp (F₀).val) (F₀).val]
  congr 1
  exact map_sum ENat.toENNRealRingHom _ _

/-- The subgroup inertia has the same canonical index as the
denominator of the normalized pair average, without subgroup normality. -/
theorem fixedField_spectral_card_inertia :
    Nat.card (lowerRamificationGroup H (IsLocalRing.maximalIdeal B₀) 0) =
      embeddingRamificationIdx K (F₀).val := by
  let : Algebra A₀ B₀ := (spectralIntegerInclusion K (F₀).val).toRingHom.toAlgebra
  let : IsScalarTower 𝒪[K] A₀ B₀ := IsScalarTower.of_algebraMap_eq (fun r =>
    ((spectralIntegerInclusion K (F₀).val).commutes r).symm)
  let : FaithfulSMul A₀ B₀ := (faithfulSMul_iff_algebraMap_injective A₀ B₀).mpr (by
    intro a b hab
    apply Subtype.ext
    exact (F₀).val.injective (congrArg (fun z : B₀ => (z : Ω)) hab))
  let : IsLocalHom (algebraMap A₀ B₀) :=
    ⟨(spectralIntegerInclusion_isLocalHom K (F₀).val).map_nonunit⟩
  let : Module.Finite A₀ B₀ := Module.Finite.of_restrictScalars_finite 𝒪[K] A₀ B₀
  let : IsGaloisGroup H A₀ B₀ := fixedField_spectralInteger_isGaloisGroup K Ω H
  have := hasSeparableResidueFieldsAt_maximalIdeal A₀ B₀
  exact card_lowerRamificationGroup_zero A₀ B₀ H

omit [IsPerfectResidueLocalField K]
  [FiniteDimensional K Ω] [IsGalois K Ω] in
@[simp]
theorem mul_subgroup_fixedField_comp (s : Ω ≃ₐ[K] Ω) (h : H) :
    (s * h.1).toAlgHom.comp (F₀).val = s.toAlgHom.comp (F₀).val := by
  ext x
  change s (h.1 (x : Ω)) = s (x : Ω)
  exact congrArg s (x.2 h)

/-- Every nonidentity embedding coset has an attained finite maximum;
the subgroup is arbitrary and no restriction automorphism is postulated. -/
theorem exists_embedding_coset_order_max (s : Ω ≃ₐ[K] Ω)
    (hs : s.toAlgHom.comp (F₀).val ≠ (F₀).val) :
    ∃ r : Ω ≃ₐ[K] Ω, r.toAlgHom.comp (F₀).val = s.toAlgHom.comp (F₀).val ∧
      ramificationOrder (R := B₀) (Ω ≃ₐ[K] Ω) r ≠ ⊤ ∧
      ∀ h : H, ramificationOrder (R := B₀) (Ω ≃ₐ[K] Ω) (r * h.1) ≤
        ramificationOrder (R := B₀) (Ω ≃ₐ[K] Ω) r := by
  classical
  let := Fintype.ofFinite H
  obtain ⟨h, _, hh⟩ := Finset.exists_max_image Finset.univ
    (fun h : H => ramificationOrder (R := B₀) (Ω ≃ₐ[K] Ω) (s * h.1))
    ⟨1, Finset.mem_univ _⟩
  refine ⟨s * h.1, mul_subgroup_fixedField_comp K Ω H s h, ?_, ?_⟩
  · apply (ramificationOrder_eq_top_iff (Ω ≃ₐ[K] Ω) (s * h.1)).not.mpr
    intro he
    apply hs
    rw [← mul_subgroup_fixedField_comp K Ω H s h, he]
    rfl
  · intro h'
    simpa only [Subgroup.coe_mul, mul_assoc] using hh (h * h') (Finset.mem_univ _)

/-- A maximal representative computes the normalized pair order
by the subgroup Herbrand function, even when it moves the fixed field. -/
theorem embeddingOrder_toReal_sub_one_eq_herbrand (s : Ω ≃ₐ[K] Ω)
    (hs : s.toAlgHom.comp (F₀).val ≠ (F₀).val)
    (hmax : ∀ h : H, ramificationOrder (R := B₀) (Ω ≃ₐ[K] Ω) (s * h.1) ≤
      ramificationOrder (R := B₀) (Ω ≃ₐ[K] Ω) s) :
    (embeddingRamificationOrder K (s.toAlgHom.comp (F₀).val) (F₀).val).toReal - 1 =
      herbrandFunction (R := B₀) H
        ((ramificationOrder (R := B₀) (Ω ≃ₐ[K] Ω) s).toNat - 1) := by
  classical
  let := Fintype.ofFinite H
  have hsfinite : ramificationOrder (R := B₀) (Ω ≃ₐ[K] Ω) s ≠ ⊤ := by
    apply (ramificationOrder_eq_top_iff (Ω ≃ₐ[K] Ω) s).not.mpr
    intro h
    apply hs
    rw [h]
    rfl
  have hnat := ENat.natCast_toNat hsfinite
  have havg := congrArg ENNReal.toReal
    (embeddingRamificationOrder_fixedField_eq_sum_div K Ω H s)
  rw [ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_sum] at havg
  · rw [herbrandFunction_eq_sum H (by
      have : (0 : ℝ) ≤ (ramificationOrder (R := B₀) (Ω ≃ₐ[K] Ω) s).toNat :=
        Nat.cast_nonneg _
      linarith), herbrandSum, fixedField_spectral_card_inertia K Ω H, havg]
    congr 2
    apply Finset.sum_congr rfl
    intro h _
    exact (truncatedRamificationOrder_eq_coset_order (Ω ≃ₐ[K] Ω) H s
      hnat.symm hmax h).symm
  · intro h _
    exact ENat.toENNReal_ne_top.mpr (ne_top_of_le_ne_top hsfinite (hmax h))

/-- Signed nonnormal embedding numbers have the coset-maximum
Herbrand formula on the finite ambient field. -/
theorem embeddingNumber_fixedField_eq_herbrand (s : Ω ≃ₐ[K] Ω)
    (hs : s.toAlgHom.comp (F₀).val ≠ (F₀).val)
    (hmax : ∀ h : H, ramificationOrder (R := B₀) (Ω ≃ₐ[K] Ω) (s * h.1) ≤
      ramificationOrder (R := B₀) (Ω ≃ₐ[K] Ω) s) :
    embeddingRamificationNumber K (s.toAlgHom.comp (F₀).val) (F₀).val =
      (herbrandFunction (R := B₀) H
        ((ramificationOrder (R := B₀) (Ω ≃ₐ[K] Ω) s).toNat - 1) : EReal) := by
  rw [← embeddingOrder_toReal_sub_one_eq_herbrand K Ω H s hs hmax,
    EReal.coe_sub, EReal.coe_one,
    EReal.coe_ennreal_toReal (embeddingRamificationOrder_lt_top K hs).ne]
  rfl

/-- Every nonidentity finite embedding has a finite
maximal ambient representative and its exact signed Herbrand value. -/
theorem exists_embeddingNumber_fixedField_eq_herbrand (s : Ω ≃ₐ[K] Ω)
    (hs : s.toAlgHom.comp (F₀).val ≠ (F₀).val) :
    ∃ r : Ω ≃ₐ[K] Ω, r.toAlgHom.comp (F₀).val = s.toAlgHom.comp (F₀).val ∧
      ramificationOrder (R := B₀) (Ω ≃ₐ[K] Ω) r ≠ ⊤ ∧
      (∀ h : H, ramificationOrder (R := B₀) (Ω ≃ₐ[K] Ω) (r * h.1) ≤
        ramificationOrder (R := B₀) (Ω ≃ₐ[K] Ω) r) ∧
      embeddingRamificationNumber K (s.toAlgHom.comp (F₀).val) (F₀).val =
        (herbrandFunction (R := B₀) H
          ((ramificationOrder (R := B₀) (Ω ≃ₐ[K] Ω) r).toNat - 1) : EReal) := by
  obtain ⟨r, hr, hrfin, hrmax⟩ := exists_embedding_coset_order_max K Ω H s hs
  refine ⟨r, hr, hrfin, hrmax, ?_⟩
  rw [← hr]
  exact embeddingNumber_fixedField_eq_herbrand K Ω H r (hr ▸ hs) hrmax

end FiniteGaloisAmbient

section EmbeddingRestriction

variable (K Ω : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
    [Field Ω] [Algebra K Ω] [FiniteDimensional K Ω] [IsGalois K Ω]

local notation "G₁" => Ω ≃ₐ[K] Ω
local notation "O₁" => spectralIntegerRing K Ω

omit [IsPerfectResidueLocalField K]
  [IsGalois K Ω] in
/-- Equality of embeddings is exactly membership in the
right fixing coset, without normality of the intermediate field. -/
theorem fixedField_comp_eq_iff_inv_mul_mem (H : Subgroup G₁) (r s : G₁) :
    s.toAlgHom.comp (IntermediateField.fixedField H).val =
      r.toAlgHom.comp (IntermediateField.fixedField H).val ↔ r⁻¹ * s ∈ H := by
  conv_rhs => rw [← IntermediateField.fixingSubgroup_fixedField H]
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro he x hx
    have h := AlgHom.congr_fun he ⟨x, hx⟩
    change r⁻¹ (s x) = x
    change s x = r x at h
    rw [h]
    exact r.symm_apply_apply x
  · intro he
    ext x
    have h := he (x : Ω) x.2
    change r⁻¹ (s (x : Ω)) = (x : Ω) at h
    exact (r.symm_apply_eq).mp h

/-- A maximal fixing-coset representative bounds all automorphisms
with that same embedding, rather than only a postulated restriction group. -/
theorem ramificationOrder_le_of_fixedField_comp_eq (H : Subgroup G₁) (r s : G₁)
    (hmax : ∀ h : H, ramificationOrder (R := O₁) G₁ (r * h.1) ≤
      ramificationOrder (R := O₁) G₁ r)
    (he : s.toAlgHom.comp (IntermediateField.fixedField H).val =
      r.toAlgHom.comp (IntermediateField.fixedField H).val) :
    ramificationOrder (R := O₁) G₁ s ≤ ramificationOrder (R := O₁) G₁ r := by
  have hm := (fixedField_comp_eq_iff_inv_mul_mem K Ω H r s).mp he
  simpa only [mul_inv_cancel_left] using hmax ⟨r⁻¹ * s, hm⟩

/-- The exact coset formula applies to every intermediate field,
including a field moved by the chosen ambient automorphism. -/
theorem exists_embeddingNumber_intermediate_eq_herbrand (E : IntermediateField K Ω)
    (s : G₁) (hs : s.toAlgHom.comp E.val ≠ E.val) :
    ∃ r : G₁, r.toAlgHom.comp E.val = s.toAlgHom.comp E.val ∧
      ramificationOrder (R := O₁) G₁ r ≠ ⊤ ∧
      (∀ h : E.fixingSubgroup, ramificationOrder (R := O₁) G₁ (r * h.1) ≤
        ramificationOrder (R := O₁) G₁ r) ∧
      embeddingRamificationNumber K (s.toAlgHom.comp E.val) E.val =
        (herbrandFunction (R := O₁) E.fixingSubgroup
          ((ramificationOrder (R := O₁) G₁ r).toNat - 1) : EReal) := by
  obtain ⟨H, rfl⟩ : ∃ H : Subgroup G₁, IntermediateField.fixedField H = E :=
    ⟨E.fixingSubgroup, IsGalois.fixedField_fixingSubgroup E⟩
  rw [IntermediateField.fixingSubgroup_fixedField]
  exact exists_embeddingNumber_fixedField_eq_herbrand K Ω H s hs

/-- Arbitrary restriction is bounded by the fixing-subgroup
change of parameter. Neither field must be preserved by the automorphism. -/
theorem embeddingNumber_restriction_le_herbrand_composite
    (E F : IntermediateField K Ω) (hEF : E ≤ F) (s : G₁)
    (hs : s.toAlgHom.comp E.val ≠ E.val) :
    embeddingRamificationNumber K (s.toAlgHom.comp F.val) F.val ≤
      (herbrandFunction (R := O₁) F.fixingSubgroup
        (inverseHerbrandFunction (R := O₁) E.fixingSubgroup
          (embeddingRamificationNumber K (s.toAlgHom.comp E.val) E.val).toReal) : EReal) := by
  have hsF : s.toAlgHom.comp F.val ≠ F.val := by
    intro he
    apply hs
    exact congrArg (fun f : F →ₐ[K] Ω => f.comp (IntermediateField.inclusion hEF)) he
  obtain ⟨r, hr, hrfin, hrmax, hri⟩ :=
    exists_embeddingNumber_intermediate_eq_herbrand K Ω E s hs
  obtain ⟨t, ht, _, _, hti⟩ :=
    exists_embeddingNumber_intermediate_eq_herbrand K Ω F s hsF
  have htr : t.toAlgHom.comp E.val = r.toAlgHom.comp E.val := by
    have htE := congrArg (fun f : F →ₐ[K] Ω =>
      f.comp (IntermediateField.inclusion hEF)) ht
    exact htE.trans hr.symm
  have htrord : ramificationOrder (R := O₁) G₁ t ≤
      ramificationOrder (R := O₁) G₁ r := by
    apply ramificationOrder_le_of_fixedField_comp_eq K Ω E.fixingSubgroup r t hrmax
    rw [IsGalois.fixedField_fixingSubgroup E]
    exact htr
  have htnat := ENat.toNat_le_toNat htrord hrfin
  have hmn : ((ramificationOrder (R := O₁) G₁ t).toNat : ℝ) - 1 ≤
      ((ramificationOrder (R := O₁) G₁ r).toNat : ℝ) - 1 := by
    exact sub_le_sub_right (Nat.cast_le.mpr htnat) 1
  have hdom (a : G₁) : -1 ≤ ((ramificationOrder (R := O₁) G₁ a).toNat : ℝ) - 1 := by
    linarith [Nat.cast_nonneg (α := ℝ) (ramificationOrder (R := O₁) G₁ a).toNat]
  rw [hri, EReal.toReal_coe, inverseHerbrandFunction_herbrandFunction _ (hdom r), hti]
  exact EReal.coe_le_coe_iff.mpr
    ((strictMonoOn_herbrandFunction (R := O₁) F.fixingSubgroup).monotoneOn
      (hdom t) (hdom r) hmn)

end EmbeddingRestriction

section RelativeParameter

variable (K Ω : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
    [Field Ω] [Algebra K Ω] [FiniteDimensional K Ω] [IsGalois K Ω]

/-- The fixing-subgroup composite is the intrinsic relative APF function
on the scalar extension of the finite intermediate field. -/
theorem apfPsi_extendScalars_eq_fixing_herbrand
    (E F : IntermediateField K Ω) (hEF : E ≤ F) {u : ℝ} (hu : -1 ≤ u) :
    letI := spectralNorm.nontriviallyNormedField K Ω
    letI := spectralNorm.normedAlgebra K Ω
    letI := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
      (isNonarchimedean_spectralNorm (K := K) (L := Ω))
    letI : CompleteSpace E := FiniteDimensional.complete K E
    letI := normedAlgebra_isCompleteDiscreteValuedField K E
    letI := Algebra.isSeparable_tower_top_of_isSeparable K E Ω
    let F' := IntermediateField.extendScalars hEF
    letI : FiniteDimensional K F' := inferInstanceAs (FiniteDimensional K F)
    letI : FiniteDimensional E F' := Module.Finite.right K E F'
    apfPsi E F' u =
      herbrandFunction (R := spectralIntegerRing K Ω) F.fixingSubgroup
        (inverseHerbrandFunction (R := spectralIntegerRing K Ω) E.fixingSubgroup u) := by
  let := spectralNorm.nontriviallyNormedField K Ω
  let := spectralNorm.normedAlgebra K Ω
  let := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := Ω))
  let : CompleteSpace E := FiniteDimensional.complete K E
  let := normedAlgebra_isCompleteDiscreteValuedField K E
  let := Algebra.isSeparable_tower_top_of_isSeparable K E Ω
  let F' := IntermediateField.extendScalars hEF
  let : FiniteDimensional K F' := inferInstanceAs (FiniteDimensional K F)
  let : FiniteDimensional E F' := Module.Finite.right K E F'
  let : IsScalarTower K E F' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : Algebra.IsSeparable K F' := inferInstanceAs (Algebra.IsSeparable K F)
  have hcomp := IsAPF.apfPsi_finiteBase_comp_of_normedAlgebra K E F'
    (apfPhi K E u)
  rw [apfPsi_apfPhi] at hcomp
  dsimp only
  rw [hcomp]
  change apfPsi K F (apfPhi K E u) = _
  rw [apfPhi_eq_herbrand_comp_subgroup_inverse_of_finiteGalois K Ω E hu,
    apfPsi_eq_subgroup_herbrand_comp_inverse_of_finiteGalois K Ω F
      (herbrandFunction_mem_Ici _ (inverseHerbrandFunction_mem_Ici _ u)),
    inverseHerbrandFunction_herbrandFunction _ (inverseHerbrandFunction_mem_Ici _ u)]

/-- The intrinsic relative Herbrand bound holds for every finite
restriction, including fields not preserved by the ambient automorphism. -/
theorem embeddingNumber_restriction_le_apfPsi
    (E F : IntermediateField K Ω) (hEF : E ≤ F) (s : Ω ≃ₐ[K] Ω)
    (hs : s.toAlgHom.comp E.val ≠ E.val) :
    letI := spectralNorm.nontriviallyNormedField K Ω
    letI := spectralNorm.normedAlgebra K Ω
    letI := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
      (isNonarchimedean_spectralNorm (K := K) (L := Ω))
    letI : CompleteSpace E := FiniteDimensional.complete K E
    letI := normedAlgebra_isCompleteDiscreteValuedField K E
    letI := Algebra.isSeparable_tower_top_of_isSeparable K E Ω
    let F' := IntermediateField.extendScalars hEF
    letI : FiniteDimensional K F' := inferInstanceAs (FiniteDimensional K F)
    letI : FiniteDimensional E F' := Module.Finite.right K E F'
    embeddingRamificationNumber K (s.toAlgHom.comp F.val) F.val ≤
      (apfPsi E F'
        (embeddingRamificationNumber K (s.toAlgHom.comp E.val) E.val).toReal : EReal) := by
  let := spectralNorm.nontriviallyNormedField K Ω
  let := spectralNorm.normedAlgebra K Ω
  let := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := Ω))
  let : CompleteSpace E := FiniteDimensional.complete K E
  let := normedAlgebra_isCompleteDiscreteValuedField K E
  let := Algebra.isSeparable_tower_top_of_isSeparable K E Ω
  let F' := IntermediateField.extendScalars hEF
  let : FiniteDimensional K F' := inferInstanceAs (FiniteDimensional K F)
  let : FiniteDimensional E F' := Module.Finite.right K E F'
  have hu : -1 ≤ (embeddingRamificationNumber K (s.toAlgHom.comp E.val) E.val).toReal := by
    obtain ⟨u, hu⟩ := embeddingRamificationNumber_exists_real K hs
    have hbound := neg_one_le_embeddingRamificationNumber K (s.toAlgHom.comp E.val) E.val
    rw [hu, EReal.toReal_coe]
    rw [hu] at hbound
    exact EReal.coe_le_coe_iff.mp
      (show ((-1 : ℝ) : EReal) ≤ (u : EReal) by
        simpa only [EReal.coe_neg, EReal.coe_one] using hbound)
  dsimp only
  rw [apfPsi_extendScalars_eq_fixing_herbrand K Ω E F hEF hu]
  exact embeddingNumber_restriction_le_herbrand_composite K Ω E F hEF s hs

end RelativeParameter

section FirstEmbeddingBound

variable (K Ω : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
    [Field Ω] [Algebra K Ω] [FiniteDimensional K Ω] [IsGalois K Ω]

local notation "G₂" => Ω ≃ₐ[K] Ω
local notation "O₂" => spectralIntegerRing K Ω

/-- Every finite embedding is bounded below by the intrinsic first
ramification bound. The extension and its intermediate field may be nonnormal. -/
theorem apfRamificationBound_le_embeddingNumber
    (F : IntermediateField K Ω) (s : G₂) :
    apfRamificationBound K F ≤ embeddingRamificationNumber K (s.toAlgHom.comp F.val) F.val := by
  by_cases hs : s.toAlgHom.comp F.val = F.val
  · rw [hs, embeddingRamificationNumber_self]
    exact le_top
  obtain ⟨r, hr, hrfin, hrmax, hri⟩ :=
    exists_embeddingNumber_intermediate_eq_herbrand K Ω F s hs
  rw [apfRamificationBound_eq_sSup_fixingSubgroup_sup_upper K Ω F]
  apply sSup_le
  rintro x ⟨u, hu, hfull, rfl⟩
  have hsmem : s⁻¹ ∈ F.fixingSubgroup ⊔ upperRamificationGroup (R := O₂) G₂ u :=
    hfull ▸ Subgroup.mem_top s⁻¹
  obtain ⟨h, hh, v, hv, he⟩ := Subgroup.mem_sup_of_normal_right.mp hsmem
  have he' : v⁻¹ = s * h := by
    have hs' : s = (h * v)⁻¹ := by rw [he, inv_inv]
    rw [hs']
    group
  have hve : (v⁻¹).toAlgHom.comp F.val = r.toAlgHom.comp F.val := by
    rw [he']
    have h := mul_subgroup_fixedField_comp K Ω F.fixingSubgroup s ⟨h, hh⟩
    rw [IsGalois.fixedField_fixingSubgroup F] at h
    exact h.trans hr.symm
  have hvr : ramificationOrder (R := O₂) G₂ v⁻¹ ≤ ramificationOrder (R := O₂) G₂ r := by
    apply ramificationOrder_le_of_fixedField_comp_eq K Ω F.fixingSubgroup r v⁻¹ hrmax
    rw [IsGalois.fixedField_fixingSubgroup F]
    exact hve
  have hv' := (upperRamificationGroup (R := O₂) G₂ u).inv_mem hv
  rw [upperRamificationGroup, mem_lowerRamificationGroupReal_iff_le_order] at hv'
  have hraw : ENNReal.ofReal (inverseHerbrandFunction (R := O₂) G₂ u + 1) ≤
      (ramificationOrder (R := O₂) G₂ r : ℝ≥0∞) :=
    hv'.trans (ENat.toENNReal_mono hvr)
  rw [← ENat.natCast_toNat hrfin, ENat.toENNReal_coe,
    ENNReal.ofReal_le_natCast] at hraw
  have harg : inverseHerbrandFunction (R := O₂) G₂ u ≤
      ((ramificationOrder (R := O₂) G₂ r).toNat : ℝ) - 1 := by linarith
  have hdom : -1 ≤ ((ramificationOrder (R := O₂) G₂ r).toNat : ℝ) - 1 := by
    linarith [Nat.cast_nonneg (α := ℝ) (ramificationOrder (R := O₂) G₂ r).toNat]
  rw [hri]
  apply EReal.coe_le_coe_iff.mpr
  calc
    u ≤ apfPsi K F u := IsAPF.le_apfPsi K F u
    _ = _ := apfPsi_eq_subgroup_herbrand_comp_inverse_of_finiteGalois K Ω F hu
    _ ≤ _ := (strictMonoOn_herbrandFunction (R := O₂) F.fixingSubgroup).monotoneOn
      (inverseHerbrandFunction_mem_Ici _ u) hdom harg

end FirstEmbeddingBound

section FiniteCosetAverages

/-- Double counting right multiplication inside a finite subgroup.
This retains arbitrary, possibly nonnormal, smaller subgroups. -/
theorem sum_sum_right_mul_subgroup {G A : Type*} [Group G] [AddCommMonoid A]
    (D H : Subgroup G) [Fintype D] [Fintype H] (hHD : H ≤ D) (f : G → A) (s : G) :
    (∑ d : D, ∑ h : H, f (s * d.1 * h.1)) =
      Fintype.card H • ∑ d : D, f (s * d.1) := by
  rw [Finset.sum_comm]
  calc
    _ = ∑ _h : H, ∑ d : D, f (s * d.1) := by
      apply Finset.sum_congr rfl
      intro h _
      have hperm := (Equiv.mulRight (⟨h.1, hHD h.2⟩ : D)).sum_comp Finset.univ
        (fun d : D => f (s * d.1)) (by simp)
      change (∑ d : D, f (s * ((d * ⟨h.1, hHD h.2⟩ : D) : G))) = _ at hperm
      simpa only [Subgroup.coe_mul, mul_assoc] using hperm
    _ = _ := by simp

/-- A finite right-coset average has a representative at most the whole
average when the inertia and group cardinalities have the total ratio. -/
theorem exists_right_coset_average_le {G : Type*} [Group G]
    (D H : Subgroup G) [Fintype D] [Fintype H] (hHD : H ≤ D)
    (f : G → ℝ) (s : G) (eD eH : ℝ) (heD : 0 < eD) (heH : 0 < eH)
    (hscale : (Fintype.card D : ℝ) * eH = Fintype.card H * eD) :
    ∃ d : D, (∑ h : H, f (s * d.1 * h.1)) / eH ≤
      (∑ d' : D, f (s * d'.1)) / eD := by
  classical
  let c := (∑ d' : D, f (s * d'.1)) / eD
  have hsum : (∑ d : D, (∑ h : H, f (s * d.1 * h.1)) / eH) =
      Fintype.card D * c := by
    rw [← Finset.sum_div, sum_sum_right_mul_subgroup D H hHD, nsmul_eq_mul]
    dsimp [c]
    apply (div_eq_iff heH.ne').mpr
    have h := congrArg (fun a : ℝ => a * ∑ d : D, f (s * d.1)) hscale
    field_simp [heD.ne']
    nlinarith [h]
  by_contra hno
  push Not at hno
  have hlt : Fintype.card D * c <
      ∑ d : D, (∑ h : H, f (s * d.1 * h.1)) / eH := by
    calc
      _ = ∑ _d : D, c := by simp
      _ < _ := Finset.sum_lt_sum (fun d _ => (hno d).le)
        ⟨1, Finset.mem_univ _, hno 1⟩
  exact (ne_of_lt hlt) hsum.symm

end FiniteCosetAverages

section FiniteAverages

variable (K Ω : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
    [Field Ω] [Algebra K Ω] [FiniteDimensional K Ω] [IsGalois K Ω]

local notation "G₃" => Ω ≃ₐ[K] Ω
local notation "O₃" => spectralIntegerRing K Ω

/-- The finite embedding average over its full fixing subgroup. -/
theorem embeddingOrder_intermediate_eq_sum_div
    (E : IntermediateField K Ω) (s : G₃) :
    letI := Fintype.ofFinite E.fixingSubgroup
    embeddingRamificationOrder K (s.toAlgHom.comp E.val) E.val =
      (∑ h : E.fixingSubgroup, (ramificationOrder (R := O₃) G₃ (s * h.1) : ℝ≥0∞)) /
        embeddingRamificationIdx K E.val := by
  obtain ⟨H, rfl⟩ : ∃ H : Subgroup G₃, IntermediateField.fixedField H = E :=
    ⟨E.fixingSubgroup, IsGalois.fixedField_fixingSubgroup E⟩
  rw [IntermediateField.fixingSubgroup_fixedField]
  exact embeddingRamificationOrder_fixedField_eq_sum_div K Ω H s

/-- A nonidentity restriction has its finite real coset average. -/
theorem embeddingOrder_toReal_eq_coset_average
    (E : IntermediateField K Ω) (s : G₃) (hs : s.toAlgHom.comp E.val ≠ E.val) :
    letI := Fintype.ofFinite E.fixingSubgroup
    (embeddingRamificationOrder K (s.toAlgHom.comp E.val) E.val).toReal =
      (∑ h : E.fixingSubgroup,
        (ramificationOrder (R := O₃) G₃ (s * h.1) : ℝ≥0∞).toReal) /
          embeddingRamificationIdx K E.val := by
  let := Fintype.ofFinite E.fixingSubgroup
  have havg := congrArg ENNReal.toReal (embeddingOrder_intermediate_eq_sum_div K Ω E s)
  rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_sum] at havg
  · exact havg
  · intro h _
    apply ENat.toENNReal_ne_top.mpr
    apply (ramificationOrder_eq_top_iff G₃ (s * h.1)).not.mpr
    intro he
    apply hs
    have hc := mul_subgroup_fixedField_comp K Ω E.fixingSubgroup s h
    rw [IsGalois.fixedField_fixingSubgroup E, he] at hc
    exact hc.symm

/-- Ordinary total ramification gives an extension embedding whose
number is at most the restricted number, by the finite Tate average. -/
theorem exists_embedding_extension_number_le_of_totallyRamified
    (E F : IntermediateField K Ω) (hEF : E ≤ F)
    (htotal : embeddingRamificationIdx K (IntermediateField.inclusion hEF) =
      Module.finrank E (IntermediateField.extendScalars hEF))
    (s : G₃) (hs : s.toAlgHom.comp E.val ≠ E.val) :
    ∃ d : E.fixingSubgroup,
      embeddingRamificationNumber K ((s * d.1).toAlgHom.comp F.val) F.val ≤
        embeddingRamificationNumber K (s.toAlgHom.comp E.val) E.val := by
  classical
  let D := E.fixingSubgroup
  let H := F.fixingSubgroup
  let := Fintype.ofFinite D
  let := Fintype.ofFinite H
  let F' := IntermediateField.extendScalars hEF
  let : FiniteDimensional K F' := inferInstanceAs (FiniteDimensional K F)
  let : FiniteDimensional E F' := Module.Finite.right K E F'
  let : FiniteDimensional E Ω := Module.Finite.right K E Ω
  have he := embeddingRamificationIdx_comp K (IntermediateField.inclusion hEF) F.val
  change embeddingRamificationIdx K E.val =
    embeddingRamificationIdx K (IntermediateField.inclusion hEF) *
      embeddingRamificationIdx K F.val at he
  rw [htotal] at he
  have hc := Module.finrank_mul_finrank E F' Ω
  change Module.finrank E F' * Module.finrank F Ω = Module.finrank E Ω at hc
  have hscaleNat : Nat.card D * embeddingRamificationIdx K F.val =
      Nat.card H * embeddingRamificationIdx K E.val := by
    rw [IsGalois.card_fixingSubgroup_eq_finrank E,
      IsGalois.card_fixingSubgroup_eq_finrank F]
    nlinarith [he, hc]
  have hscale : (Fintype.card D : ℝ) * embeddingRamificationIdx K F.val =
      Fintype.card H * embeddingRamificationIdx K E.val := by
    exact_mod_cast (show Fintype.card D * embeddingRamificationIdx K F.val =
      Fintype.card H * embeddingRamificationIdx K E.val by
        simpa only [Nat.card_eq_fintype_card] using hscaleNat)
  obtain ⟨d, hd⟩ := exists_right_coset_average_le D H
    (IntermediateField.fixingSubgroup_le hEF)
    (fun g => (ramificationOrder (R := O₃) G₃ g : ℝ≥0∞).toReal) s
    (embeddingRamificationIdx K E.val) (embeddingRamificationIdx K F.val)
    (Nat.cast_pos.mpr (embeddingRamificationIdx_pos K E.val))
    (Nat.cast_pos.mpr (embeddingRamificationIdx_pos K F.val)) hscale
  have hsE : (s * d.1).toAlgHom.comp E.val = s.toAlgHom.comp E.val := by
    have h := mul_subgroup_fixedField_comp K Ω D s d
    rw [IsGalois.fixedField_fixingSubgroup E] at h
    exact h
  have hsF : (s * d.1).toAlgHom.comp F.val ≠ F.val := by
    intro hf
    apply hs
    have hfE := congrArg (fun f : F →ₐ[K] Ω =>
      f.comp (IntermediateField.inclusion hEF)) hf
    exact hsE.symm.trans hfE
  have havg : (embeddingRamificationOrder K ((s * d.1).toAlgHom.comp F.val) F.val).toReal ≤
      (embeddingRamificationOrder K (s.toAlgHom.comp E.val) E.val).toReal := by
    rw [embeddingOrder_toReal_eq_coset_average K Ω F (s * d.1) hsF,
      embeddingOrder_toReal_eq_coset_average K Ω E s hs]
    exact hd
  refine ⟨d, ?_⟩
  rw [embeddingRamificationNumber, embeddingRamificationNumber,
    ← EReal.coe_ennreal_toReal (embeddingRamificationOrder_lt_top K hsF).ne,
    ← EReal.coe_ennreal_toReal (embeddingRamificationOrder_lt_top K hs).ne]
  exact EReal.sub_le_sub (EReal.coe_le_coe_iff.mpr havg) le_rfl

end FiniteAverages

section StrictPairComparison

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

variable {E N : Type*} [Field E] [Field N] [Algebra K E] [Algebra K N]
    [FiniteDimensional K E] [FiniteDimensional K N]
    [Algebra.IsSeparable K E] [Algebra.IsSeparable K N]

/-- Strict separation of two embeddings forces equal displacement
from a third embedding, with the normalized source-field index. -/
theorem embeddingNumber_eq_of_lt_pair (α β ι : E →ₐ[K] N)
    (hlt : embeddingRamificationNumber K α ι < embeddingRamificationNumber K α β) :
    embeddingRamificationNumber K β ι = embeddingRamificationNumber K α ι := by
  have hj := EReal.add_lt_add_right_coe hlt 1
  rw [EReal.coe_one, embeddingRamificationNumber_add_one,
    embeddingRamificationNumber_add_one] at hj
  have hj' := EReal.coe_ennreal_lt_coe_ennreal_iff.mp hj
  rw [embeddingRamificationOrder, embeddingRamificationOrder] at hj'
  have he0 : (embeddingRamificationIdx K α : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr (embeddingRamificationIdx_pos K α).ne'
  have hraw := ENat.toENNReal_lt.mp
    ((ENNReal.div_lt_div_iff_left he0 (ENNReal.natCast_ne_top _)).mp hj')
  have hβα : embeddingIntegralOrder K β α = embeddingIntegralOrder K α β :=
    integralEmbeddingOrder_comm _ _
  have hraw' : embeddingIntegralOrder K β ι = embeddingIntegralOrder K α ι := by
    change integralEmbeddingOrder (spectralIntegerInclusion K β).toRingHom
      (spectralIntegerInclusion K ι).toRingHom = _
    rw [integralEmbeddingOrder_eq_min_of_ne
      (spectralIntegerInclusion K β).toRingHom (spectralIntegerInclusion K α).toRingHom
      (spectralIntegerInclusion K ι).toRingHom (by
        change embeddingIntegralOrder K β α ≠ embeddingIntegralOrder K α ι
        rw [hβα]
        exact hraw.ne')]
    change min (embeddingIntegralOrder K β α) (embeddingIntegralOrder K α ι) = _
    rw [hβα, min_eq_right hraw.le]
  rw [embeddingRamificationNumber, embeddingRamificationNumber,
    embeddingRamificationOrder, embeddingRamificationOrder, hraw',
    embeddingRamificationIdx_eq K β α]

end StrictPairComparison

section LocalIndexTransport

variable {R S R' S' : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [CommRing S'] [IsDomain S'] [IsDiscreteValuationRing S']
    [Algebra R S] [Algebra R' S']
    [FaithfulSMul R S] [IsLocalHom (algebraMap R S)]
    [FaithfulSMul R' S'] [IsLocalHom (algebraMap R' S')]

/-- A commuting isomorphism of local DVR maps preserves the
canonical local-length ramification index. -/
theorem local_ramificationIdx_ringEquiv (r : R ≃+* R') (s : S ≃+* S')
    (hs : ∀ x : R, s (algebraMap R S x) = algebraMap R' S' (r x)) :
    (IsLocalRing.maximalIdeal S').ramificationIdx R' =
      (IsLocalRing.maximalIdeal S).ramificationIdx R := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπ' : Irreducible (r π) := (MulEquiv.irreducible_iff r).mpr hπ
  have h := addVal_algebraMap R S π
  have h' := addVal_algebraMap R' S' (r π)
  rw [IsDiscreteValuationRing.addVal_uniformizer hπ, mul_one] at h
  rw [IsDiscreteValuationRing.addVal_uniformizer hπ', mul_one, ← hs,
    addVal_ringEquiv] at h'
  exact ENat.natCast_inj.mp (h'.symm.trans h)

end LocalIndexTransport

section Equivalence

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

variable {E F N : Type*} [Field E] [Field F] [Field N]
    [Algebra K E] [Algebra K F] [Algebra K N]
    [FiniteDimensional K E] [FiniteDimensional K F] [FiniteDimensional K N]
    [Algebra.IsSeparable K E] [Algebra.IsSeparable K F] [Algebra.IsSeparable K N]

/-- An isomorphism between finite fields has relative index one. -/
theorem embeddingRamificationIdx_algEquiv (e : E ≃ₐ[K] F) :
    embeddingRamificationIdx K e.toAlgHom = 1 := by
  have h := embeddingRamificationIdx_comp K e.toAlgHom e.symm.toAlgHom
  have hi : e.symm.toAlgHom.comp e.toAlgHom = AlgHom.id K E := by
    ext x
    exact e.symm_apply_apply x
  rw [hi] at h
  have hid : embeddingRamificationIdx K (AlgHom.id K E) = 1 :=
    embeddingRamificationIdx_aut K (AlgEquiv.refl : E ≃ₐ[K] E)
  rw [hid] at h
  exact Nat.dvd_one.mp ⟨embeddingRamificationIdx K e.symm.toAlgHom, h⟩

omit [FiniteDimensional K E] [FiniteDimensional K F] in
/-- Reparametrizing the finite field preserves its full
integral displacement infimum, including the identical pair. -/
theorem embeddingIntegralOrder_precomp_algEquiv (e : E ≃ₐ[K] F)
    (α β : F →ₐ[K] N) :
    embeddingIntegralOrder K (α.comp e.toAlgHom) (β.comp e.toAlgHom) =
      embeddingIntegralOrder K α β := by
  unfold embeddingIntegralOrder integralEmbeddingOrder
  apply (spectralIntegerRingEquiv K e).toEquiv.iInf_congr
  intro x
  apply congrArg (IsDiscreteValuationRing.addVal (spectralIntegerRing K N))
  apply congrArg₂ (fun a b : spectralIntegerRing K N => a - b)
  · apply Subtype.ext
    change α (spectralIntegerRingEquiv K e x : F) = α (e (x : E))
    rw [coe_spectralIntegerRingEquiv]
  · apply Subtype.ext
    change β (spectralIntegerRingEquiv K e x : F) = β (e (x : E))
    rw [coe_spectralIntegerRingEquiv]

/-- Finite-source isomorphisms preserve normalized embedding orders. -/
theorem embeddingOrder_precomp_algEquiv (e : E ≃ₐ[K] F) (α β : F →ₐ[K] N) :
    embeddingRamificationOrder K (α.comp e.toAlgHom) (β.comp e.toAlgHom) =
      embeddingRamificationOrder K α β := by
  rw [embeddingRamificationOrder, embeddingRamificationOrder,
    embeddingIntegralOrder_precomp_algEquiv, embeddingRamificationIdx_comp,
    embeddingRamificationIdx_algEquiv, one_mul]

/-- Signed intrinsic numbers are invariant under finite-source
isomorphisms, without selecting a replacement valuation or field carrier. -/
theorem embeddingNumber_precomp_algEquiv (e : E ≃ₐ[K] F) (α β : F →ₐ[K] N) :
    embeddingRamificationNumber K (α.comp e.toAlgHom) (β.comp e.toAlgHom) =
      embeddingRamificationNumber K α β := by
  rw [embeddingRamificationNumber, embeddingRamificationNumber,
    embeddingOrder_precomp_algEquiv]

end Equivalence

section FiniteBaseInvariance

variable (K Ω : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
    [Field Ω] [Algebra K Ω] [FiniteDimensional K Ω] [IsGalois K Ω]

/-- Changing to a finite intermediate base preserves the same intrinsic
embedding number. Both integer rings are identified by their unit balls;
the canonical local indices are proved equal through the commuting ring maps. -/
theorem embeddingNumber_rebase
    (E F : IntermediateField K Ω) (hEF : E ≤ F) :
    letI := spectralNorm.nontriviallyNormedField K Ω
    letI := spectralNorm.normedAlgebra K Ω
    letI := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
      (isNonarchimedean_spectralNorm (K := K) (L := Ω))
    letI : CompleteSpace E := FiniteDimensional.complete K E
    letI := normedAlgebra_isPerfectResidueLocalField K E
    letI := Algebra.isSeparable_tower_top_of_isSeparable K E Ω
    letI : FiniteDimensional E Ω := Module.Finite.right K E Ω
    let F' := IntermediateField.extendScalars hEF
    letI : FiniteDimensional K F' := inferInstanceAs (FiniteDimensional K F)
    letI : FiniteDimensional E F' := Module.Finite.right K E F'
    ∀ s : Ω ≃ₐ[E] Ω,
      embeddingRamificationNumber K ((s.restrictScalars K).toAlgHom.comp F.val) F.val =
        embeddingRamificationNumber E (s.toAlgHom.comp F'.val) F'.val := by
  let := spectralNorm.nontriviallyNormedField K Ω
  let := spectralNorm.normedAlgebra K Ω
  let := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := Ω))
  let : CompleteSpace E := FiniteDimensional.complete K E
  let := normedAlgebra_isPerfectResidueLocalField K E
  let := Algebra.isSeparable_tower_top_of_isSeparable K E Ω
  let : FiniteDimensional E Ω := Module.Finite.right K E Ω
  let F' := IntermediateField.extendScalars hEF
  let : FiniteDimensional K F' := inferInstanceAs (FiniteDimensional K F)
  let : FiniteDimensional E F' := Module.Finite.right K E F'
  dsimp only
  intro s
  let A := spectralIntegerRing K F
  let B := spectralIntegerRing K Ω
  let A' := spectralIntegerRing E F'
  let B' := spectralIntegerRing E Ω
  have hA : spectralIntegerRing K F = spectralIntegerRing E F' :=
    (spectralIntegerRing_eq_normedUnitBall K F).trans
      (spectralIntegerRing_eq_normedUnitBall E F').symm
  let rF : A ≃+* A' := RingEquiv.subringCongr
    (congrArg ValuationSubring.toSubring hA)
  let rΩ : B ≃+* B' := finiteBaseSpectralIntegerRingEquiv K Ω E
  let : Algebra A B := (spectralIntegerInclusion K F.val).toRingHom.toAlgebra
  let : Algebra A' B' := (spectralIntegerInclusion E F'.val).toRingHom.toAlgebra
  let : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr (by
    intro a b hab
    apply Subtype.ext
    exact F.val.injective (congrArg (fun z : B => (z : Ω)) hab))
  let : FaithfulSMul A' B' := (faithfulSMul_iff_algebraMap_injective A' B').mpr (by
    intro a b hab
    apply Subtype.ext
    exact F'.val.injective (congrArg (fun z : B' => (z : Ω)) hab))
  let : IsLocalHom (algebraMap A B) :=
    ⟨(spectralIntegerInclusion_isLocalHom K F.val).map_nonunit⟩
  let : IsLocalHom (algebraMap A' B') :=
    ⟨(spectralIntegerInclusion_isLocalHom E F'.val).map_nonunit⟩
  have hidx : embeddingRamificationIdx E F'.val = embeddingRamificationIdx K F.val :=
    local_ramificationIdx_ringEquiv rF rΩ (fun _ => Subtype.ext rfl)
  have hraw : embeddingIntegralOrder K ((s.restrictScalars K).toAlgHom.comp F.val) F.val =
      embeddingIntegralOrder E (s.toAlgHom.comp F'.val) F'.val := by
    unfold embeddingIntegralOrder integralEmbeddingOrder
    apply rF.toEquiv.iInf_congr
    intro x
    have he : rΩ
        (spectralIntegerInclusion K ((s.restrictScalars K).toAlgHom.comp F.val) x -
          spectralIntegerInclusion K F.val x) =
        spectralIntegerInclusion E (s.toAlgHom.comp F'.val) (rF x) -
          spectralIntegerInclusion E F'.val (rF x) := Subtype.ext rfl
    change IsDiscreteValuationRing.addVal B'
      (spectralIntegerInclusion E (s.toAlgHom.comp F'.val) (rF x) -
        spectralIntegerInclusion E F'.val (rF x)) =
      IsDiscreteValuationRing.addVal B
        (spectralIntegerInclusion K ((s.restrictScalars K).toAlgHom.comp F.val) x -
          spectralIntegerInclusion K F.val x)
    rw [← he, addVal_ringEquiv]
  rw [embeddingRamificationNumber, embeddingRamificationNumber,
    embeddingRamificationOrder, embeddingRamificationOrder, hraw,
    embeddingRamificationIdx_eq K ((s.restrictScalars K).toAlgHom.comp F.val) F.val,
    embeddingRamificationIdx_eq E (s.toAlgHom.comp F'.val) F'.val, hidx]

end FiniteBaseInvariance

section RelativeEmbeddingBounds

variable (K Ω : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
    [Field Ω] [Algebra K Ω] [FiniteDimensional K Ω] [IsGalois K Ω]

/-- The relative first bound controls every base-fixing
embedding, with its number computed on the old-base integer rings. -/
theorem apfRelativeBound_le_embeddingNumber
    (E F : IntermediateField K Ω) (hEF : E ≤ F) :
    letI := spectralNorm.nontriviallyNormedField K Ω
    letI := spectralNorm.normedAlgebra K Ω
    letI := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
      (isNonarchimedean_spectralNorm (K := K) (L := Ω))
    letI : CompleteSpace E := FiniteDimensional.complete K E
    letI := normedAlgebra_isPerfectResidueLocalField K E
    letI := Algebra.isSeparable_tower_top_of_isSeparable K E Ω
    letI : FiniteDimensional E Ω := Module.Finite.right K E Ω
    let F' := IntermediateField.extendScalars hEF
    letI : FiniteDimensional K F' := inferInstanceAs (FiniteDimensional K F)
    letI : FiniteDimensional E F' := Module.Finite.right K E F'
    ∀ d : E.fixingSubgroup, apfRamificationBound E F' ≤
      embeddingRamificationNumber K (d.1.toAlgHom.comp F.val) F.val := by
  let := spectralNorm.nontriviallyNormedField K Ω
  let := spectralNorm.normedAlgebra K Ω
  let := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := Ω))
  let : CompleteSpace E := FiniteDimensional.complete K E
  let := normedAlgebra_isPerfectResidueLocalField K E
  let := Algebra.isSeparable_tower_top_of_isSeparable K E Ω
  let : FiniteDimensional E Ω := Module.Finite.right K E Ω
  let F' := IntermediateField.extendScalars hEF
  let : FiniteDimensional K F' := inferInstanceAs (FiniteDimensional K F)
  let : FiniteDimensional E F' := Module.Finite.right K E F'
  let : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
  dsimp only
  intro d
  have h := apfRamificationBound_le_embeddingNumber E Ω F' (E.fixingSubgroupEquiv d)
  rw [← embeddingNumber_rebase K Ω E F hEF (E.fixingSubgroupEquiv d)] at h
  exact h

/-- Two ambient maps with the same restriction to the smaller
field are separated by at least the relative first bound. -/
theorem apfRelativeBound_le_pairNumber
    (E F : IntermediateField K Ω) (hEF : E ≤ F)
    (s t : Ω ≃ₐ[K] Ω) (hst : s.toAlgHom.comp E.val = t.toAlgHom.comp E.val) :
    letI := spectralNorm.nontriviallyNormedField K Ω
    letI := spectralNorm.normedAlgebra K Ω
    letI := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
      (isNonarchimedean_spectralNorm (K := K) (L := Ω))
    letI : CompleteSpace E := FiniteDimensional.complete K E
    letI := normedAlgebra_isCompleteDiscreteValuedField K E
    letI := Algebra.isSeparable_tower_top_of_isSeparable K E Ω
    letI : FiniteDimensional E Ω := Module.Finite.right K E Ω
    let F' := IntermediateField.extendScalars hEF
    letI : FiniteDimensional K F' := inferInstanceAs (FiniteDimensional K F)
    letI : FiniteDimensional E F' := Module.Finite.right K E F'
    apfRamificationBound E F' ≤
      embeddingRamificationNumber K (s.toAlgHom.comp F.val) (t.toAlgHom.comp F.val) := by
  have hd : t⁻¹ * s ∈ E.fixingSubgroup := by
    apply (fixedField_comp_eq_iff_inv_mul_mem K Ω E.fixingSubgroup t s).mp
    rw [IsGalois.fixedField_fixingSubgroup E]
    exact hst
  have h := apfRelativeBound_le_embeddingNumber K Ω E F hEF ⟨t⁻¹ * s, hd⟩
  have he := embeddingRamificationNumber_comp K (s.toAlgHom.comp F.val)
    (t.toAlgHom.comp F.val) t.symm.toAlgHom
  have he' :
      embeddingRamificationNumber K ((t⁻¹ * s).toAlgHom.comp F.val) F.val =
        embeddingRamificationNumber K (s.toAlgHom.comp F.val) (t.toAlgHom.comp F.val) := by
    convert he using 1
    exact congrArg (embeddingRamificationNumber K ((t⁻¹ * s).toAlgHom.comp F.val))
      (AlgHom.ext fun x => (t.symm_apply_apply (x : Ω)).symm)
  exact h.trans_eq he'

end RelativeEmbeddingBounds

section TotalFiberAverage

variable (K Ω : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
    [Field Ω] [Algebra K Ω] [FiniteDimensional K Ω] [IsGalois K Ω]

/-- Under ordinary total ramification, the true average over all extensions
of a nonidentity embedding is its normalized order. -/
theorem sum_embedding_extension_order_of_totallyRamified
    (E F : IntermediateField K Ω) (hEF : E ≤ F)
    (htotal : embeddingRamificationIdx K (IntermediateField.inclusion hEF) =
      Module.finrank E (IntermediateField.extendScalars hEF))
    (s : Ω ≃ₐ[K] Ω) (hs : s.toAlgHom.comp E.val ≠ E.val) :
    letI := Fintype.ofFinite E.fixingSubgroup
    (∑ d : E.fixingSubgroup,
      (embeddingRamificationOrder K ((s * d.1).toAlgHom.comp F.val) F.val).toReal) =
      Fintype.card E.fixingSubgroup *
        (embeddingRamificationOrder K (s.toAlgHom.comp E.val) E.val).toReal := by
  classical
  let D := E.fixingSubgroup
  let H := F.fixingSubgroup
  let := Fintype.ofFinite D
  let := Fintype.ofFinite H
  let F' := IntermediateField.extendScalars hEF
  let : FiniteDimensional K F' := inferInstanceAs (FiniteDimensional K F)
  let : FiniteDimensional E F' := Module.Finite.right K E F'
  let : FiniteDimensional E Ω := Module.Finite.right K E Ω
  have he := embeddingRamificationIdx_comp K (IntermediateField.inclusion hEF) F.val
  change embeddingRamificationIdx K E.val =
    embeddingRamificationIdx K (IntermediateField.inclusion hEF) *
      embeddingRamificationIdx K F.val at he
  rw [htotal] at he
  have hc := Module.finrank_mul_finrank E F' Ω
  change Module.finrank E F' * Module.finrank F Ω = Module.finrank E Ω at hc
  have hscaleNat : Nat.card D * embeddingRamificationIdx K F.val =
      Nat.card H * embeddingRamificationIdx K E.val := by
    rw [IsGalois.card_fixingSubgroup_eq_finrank E,
      IsGalois.card_fixingSubgroup_eq_finrank F]
    nlinarith [he, hc]
  have hscale : (Fintype.card D : ℝ) * embeddingRamificationIdx K F.val =
      Fintype.card H * embeddingRamificationIdx K E.val := by
    exact_mod_cast (show Fintype.card D * embeddingRamificationIdx K F.val =
      Fintype.card H * embeddingRamificationIdx K E.val by
        simpa only [Nat.card_eq_fintype_card] using hscaleNat)
  have hsF (d : D) : (s * d.1).toAlgHom.comp F.val ≠ F.val := by
    intro hf
    apply hs
    have heq := mul_subgroup_fixedField_comp K Ω D s d
    rw [IsGalois.fixedField_fixingSubgroup E] at heq
    exact heq.symm.trans
      (congrArg (fun f : F →ₐ[K] Ω => f.comp (IntermediateField.inclusion hEF)) hf)
  simp_rw [embeddingOrder_toReal_eq_coset_average K Ω F _ (hsF _)]
  rw [← Finset.sum_div,
    sum_sum_right_mul_subgroup D H (IntermediateField.fixingSubgroup_le hEF)
      (fun g : Ω ≃ₐ[K] Ω =>
        (ramificationOrder (R := spectralIntegerRing K Ω) (Ω ≃ₐ[K] Ω) g : ℝ≥0∞).toReal) s,
    nsmul_eq_mul, embeddingOrder_toReal_eq_coset_average K Ω E s hs]
  apply (div_eq_iff (Nat.cast_ne_zero.mpr (embeddingRamificationIdx_pos K F.val).ne')).mpr
  have h := congrArg (fun a : ℝ => a * ∑ d : D,
    (ramificationOrder (R := spectralIntegerRing K Ω) (Ω ≃ₐ[K] Ω) (s * d.1) : ℝ≥0∞).toReal)
      hscale
  field_simp [(Nat.cast_ne_zero.mpr (embeddingRamificationIdx_pos K E.val).ne' :
    (embeddingRamificationIdx K E.val : ℝ) ≠ 0)]
  nlinarith [h]

/-- Below the relative first bound, ordinary total ramification
forces every extension embedding to retain the restricted number. Neither
intermediate field is required to be normal or stable. -/
theorem embeddingNumber_eq_restriction_of_lt_relativeBound
    (E F : IntermediateField K Ω) (hEF : E ≤ F)
    (htotal : embeddingRamificationIdx K (IntermediateField.inclusion hEF) =
      Module.finrank E (IntermediateField.extendScalars hEF))
    (s : Ω ≃ₐ[K] Ω) (hs : s.toAlgHom.comp E.val ≠ E.val) :
    letI := spectralNorm.nontriviallyNormedField K Ω
    letI := spectralNorm.normedAlgebra K Ω
    letI := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
      (isNonarchimedean_spectralNorm (K := K) (L := Ω))
    letI : CompleteSpace E := FiniteDimensional.complete K E
    letI := normedAlgebra_isCompleteDiscreteValuedField K E
    letI := Algebra.isSeparable_tower_top_of_isSeparable K E Ω
    letI : FiniteDimensional E Ω := Module.Finite.right K E Ω
    let F' := IntermediateField.extendScalars hEF
    letI : FiniteDimensional K F' := inferInstanceAs (FiniteDimensional K F)
    letI : FiniteDimensional E F' := Module.Finite.right K E F'
    embeddingRamificationNumber K (s.toAlgHom.comp E.val) E.val <
      apfRamificationBound E F' →
      embeddingRamificationNumber K (s.toAlgHom.comp F.val) F.val =
        embeddingRamificationNumber K (s.toAlgHom.comp E.val) E.val := by
  classical
  let := spectralNorm.nontriviallyNormedField K Ω
  let := spectralNorm.normedAlgebra K Ω
  let := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := Ω))
  let : CompleteSpace E := FiniteDimensional.complete K E
  let := normedAlgebra_isCompleteDiscreteValuedField K E
  let := Algebra.isSeparable_tower_top_of_isSeparable K E Ω
  let : FiniteDimensional E Ω := Module.Finite.right K E Ω
  let F' := IntermediateField.extendScalars hEF
  let : FiniteDimensional K F' := inferInstanceAs (FiniteDimensional K F)
  let : FiniteDimensional E F' := Module.Finite.right K E F'
  dsimp only
  intro hsmall
  let D := E.fixingSubgroup
  let := Fintype.ofFinite D
  obtain ⟨d₀, hd₀⟩ :=
    exists_embedding_extension_number_le_of_totallyRamified K Ω E F hEF htotal s hs
  have hrestr (d : D) : (s * d.1).toAlgHom.comp E.val = s.toAlgHom.comp E.val := by
    have h := mul_subgroup_fixedField_comp K Ω D s d
    rw [IsGalois.fixedField_fixingSubgroup E] at h
    exact h
  have hconst (d : D) :
      embeddingRamificationNumber K ((s * d.1).toAlgHom.comp F.val) F.val =
        embeddingRamificationNumber K ((s * d₀.1).toAlgHom.comp F.val) F.val := by
    apply embeddingNumber_eq_of_lt_pair
    exact (hd₀.trans_lt hsmall).trans_le
      (apfRelativeBound_le_pairNumber K Ω E F hEF (s * d₀.1) (s * d.1)
        ((hrestr d₀).trans (hrestr d).symm))
  have hJ (d : D) :
      embeddingRamificationOrder K ((s * d.1).toAlgHom.comp F.val) F.val =
        embeddingRamificationOrder K ((s * d₀.1).toAlgHom.comp F.val) F.val := by
    apply EReal.coe_ennreal_injective
    have h := congrArg (fun a : EReal => a + 1) (hconst d)
    simpa only [embeddingRamificationNumber_add_one] using h
  have hsum := sum_embedding_extension_order_of_totallyRamified K Ω E F hEF htotal s hs
  simp_rw [hJ] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have heq :
      (embeddingRamificationOrder K ((s * d₀.1).toAlgHom.comp F.val) F.val).toReal =
        (embeddingRamificationOrder K (s.toAlgHom.comp E.val) E.val).toReal := by
    exact (mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero) :
      (Fintype.card D : ℝ) ≠ 0)) hsum
  have hsF : s.toAlgHom.comp F.val ≠ F.val := by
    intro hf
    exact hs (congrArg (fun f : F →ₐ[K] Ω =>
      f.comp (IntermediateField.inclusion hEF)) hf)
  have hj : embeddingRamificationOrder K (s.toAlgHom.comp F.val) F.val =
      embeddingRamificationOrder K (s.toAlgHom.comp E.val) E.val := by
    apply (ENNReal.toReal_eq_toReal_iff' (embeddingRamificationOrder_lt_top K hsF).ne
      (embeddingRamificationOrder_lt_top K hs).ne).mp
    have h := congrArg ENNReal.toReal (hJ (1 : D))
    simpa only [Subgroup.coe_one, mul_one] using h.trans heq
  exact congrArg (fun j : ℝ≥0∞ => ((j : EReal) - 1)) hj

end TotalFiberAverage

end FontaineWintenberger
