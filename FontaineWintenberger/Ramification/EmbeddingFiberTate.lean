/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Ramification.EmbeddingComparison
public import FontaineWintenberger.Algebra.SeparableEmbeddings

/-!
# Tate averages over distinct restriction fibers

The indexing type consists of actual finite-field embeddings with the prescribed
restriction. Genuine fixing-group torsors remove repeated coset representatives.
No normality or stability of either intermediate field is required.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

open scoped ENNReal

section RestrictionFibers

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

/-- The actual embeddings of the upper field with a prescribed actual
restriction to the lower field. -/
def embeddingRestrictionFiber {E F : IntermediateField K Ω} (hEF : E ≤ F)
    (f : E →ₐ[K] Ω) :=
  {τ : F →ₐ[K] Ω // τ.comp (IntermediateField.inclusion hEF) = f}

instance embeddingRestrictionFiber_finite {E F : IntermediateField K Ω}
    [FiniteDimensional K F] (hEF : E ≤ F)
    (f : E →ₐ[K] Ω) : Finite (embeddingRestrictionFiber hEF f) :=
  inferInstanceAs (Finite {τ : F →ₐ[K] Ω // τ.comp (IntermediateField.inclusion hEF) = f})

variable [FiniteDimensional K Ω] [Normal K Ω]

/-- Right multiplication by the lower fixing group gives the original
restriction fiber; this is an actual map of embeddings, not a quotient model. -/
def fixingRestrictionMap {E F : IntermediateField K Ω} (hEF : E ≤ F)
    (s : Ω ≃ₐ[K] Ω) (d : E.fixingSubgroup) :
    embeddingRestrictionFiber hEF (s.toAlgHom.comp E.val) :=
  ⟨(s * d.1).toAlgHom.comp F.val, by
    ext x
    change s (d.1 (x : Ω)) = s (x : Ω)
    exact congrArg s ((IntermediateField.mem_fixingSubgroup_iff _ _).mp d.2 x x.2)⟩

omit [FiniteDimensional K Ω] in
/-- Every actual upper embedding with the given lower restriction has an
actual ambient automorphism representative in the required fixing coset. -/
theorem fixingRestrictionMap_surjective {E F : IntermediateField K Ω} (hEF : E ≤ F)
    (s : Ω ≃ₐ[K] Ω) : Function.Surjective (fixingRestrictionMap hEF s) := by
  intro τ
  obtain ⟨r, hr⟩ := exists_aut_extends_intermediate_embedding K Ω F τ.1
  have he (x : E) : r (x : Ω) = s (x : Ω) :=
    (hr (IntermediateField.inclusion hEF x)).trans (AlgHom.congr_fun τ.2 x)
  let d : E.fixingSubgroup := ⟨s⁻¹ * r,
    (IntermediateField.mem_fixingSubgroup_iff _ _).mpr (fun x hx => by
      change s.symm (r x) = x
      rw [he ⟨x, hx⟩]
      exact s.symm_apply_apply x)⟩
  refine ⟨d, Subtype.ext (AlgHom.ext fun x => ?_)⟩
  change s (s.symm (r (x : Ω))) = τ.1 x
  rw [s.apply_symm_apply]
  exact hr x

omit [FiniteDimensional K Ω] in
/-- Each genuine restriction fiber is a right torsor for the upper
fixing subgroup, so all multiplicities are proved equal to its actual size. -/
theorem fixingRestrictionMap_fiber_card {E F : IntermediateField K Ω} (hEF : E ≤ F)
    (s : Ω ≃ₐ[K] Ω) (τ : embeddingRestrictionFiber hEF (s.toAlgHom.comp E.val)) :
    Nat.card {d : E.fixingSubgroup // fixingRestrictionMap hEF s d = τ} =
      Nat.card F.fixingSubgroup := by
  classical
  obtain ⟨d₀, hd₀⟩ := fixingRestrictionMap_surjective hEF s τ
  let hHD := IntermediateField.fixingSubgroup_le hEF
  let φ : F.fixingSubgroup →
      {d : E.fixingSubgroup // fixingRestrictionMap hEF s d = τ} := fun h =>
    ⟨d₀ * ⟨h.1, hHD h.2⟩, by
      apply Eq.trans _ hd₀
      apply Subtype.ext
      ext x
      change s (d₀.1 (h.1 (x : Ω))) = s (d₀.1 (x : Ω))
      rw [(IntermediateField.mem_fixingSubgroup_iff _ _).mp h.2 x x.2]⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro h₁ h₂ he
      have h := congrArg (fun z => z.1) he
      have h' : d₀.1 * h₁.1 = d₀.1 * h₂.1 := congrArg Subtype.val h
      exact Subtype.ext (mul_left_cancel h')
    · intro d
      have he : (s * d.1.1).toAlgHom.comp F.val =
          (s * d₀.1).toAlgHom.comp F.val := congrArg Subtype.val (d.2.trans hd₀.symm)
      have hm : d₀.1⁻¹ * d.1.1 ∈ F.fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro x hx
        have hx' := AlgHom.congr_fun he (⟨x, hx⟩ : F)
        change s (d.1.1 x) = s (d₀.1 x) at hx'
        have hx'' := s.injective hx'
        change d₀.1.symm (d.1.1 x) = x
        rw [hx'']
        exact d₀.1.symm_apply_apply x
      refine ⟨⟨d₀.1⁻¹ * d.1.1, hm⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact mul_inv_cancel_left _ _
  exact (Nat.card_congr (Equiv.ofBijective φ hφ)).symm

/-- Summing any function over distinct embeddings removes exactly the
proved fixing-group multiplicity, even for infinite extended-real values. -/
theorem sum_fixingRestrictionMap {E F : IntermediateField K Ω} (hEF : E ≤ F)
    (s : Ω ≃ₐ[K] Ω) (a : embeddingRestrictionFiber hEF (s.toAlgHom.comp E.val) → ℝ≥0∞) :
    letI := Fintype.ofFinite E.fixingSubgroup
    letI := Fintype.ofFinite (embeddingRestrictionFiber hEF (s.toAlgHom.comp E.val))
    (∑ d : E.fixingSubgroup, a (fixingRestrictionMap hEF s d)) =
      Nat.card F.fixingSubgroup * ∑ τ, a τ := by
  classical
  let := Fintype.ofFinite E.fixingSubgroup
  let := Fintype.ofFinite (embeddingRestrictionFiber hEF (s.toAlgHom.comp E.val))
  rw [← Fintype.sum_fiberwise' (fixingRestrictionMap hEF s) a]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp_rw [← Nat.card_eq_fintype_card, fixingRestrictionMap_fiber_card hEF s]
  exact (Finset.mul_sum ..).symm

end RestrictionFibers

section FiniteTateFiber

variable (K Ω : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
    [Field Ω] [Algebra K Ω] [FiniteDimensional K Ω] [IsGalois K Ω]

local notation "G" => Ω ≃ₐ[K] Ω
local notation "O" => spectralIntegerRing K Ω

/-- The repeated-representative sum for an arbitrary finite tower, without
any total-ramification condition and including the infinite endpoint. -/
theorem sum_embeddingOrder_fixing_restrictions
    (E F : IntermediateField K Ω) (hEF : E ≤ F) (s : G) :
    letI := Fintype.ofFinite E.fixingSubgroup
    (∑ d : E.fixingSubgroup,
      embeddingRamificationOrder K ((s * d.1).toAlgHom.comp F.val) F.val) =
      Nat.card F.fixingSubgroup *
        (∑ d : E.fixingSubgroup, (ramificationOrder (R := O) G (s * d.1) : ℝ≥0∞)) /
          embeddingRamificationIdx K F.val := by
  classical
  let := Fintype.ofFinite E.fixingSubgroup
  let := Fintype.ofFinite F.fixingSubgroup
  simp_rw [embeddingOrder_intermediate_eq_sum_div K Ω F]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, sum_sum_right_mul_subgroup E.fixingSubgroup F.fixingSubgroup
    (IntermediateField.fixingSubgroup_le hEF)
    (fun t : G => (ramificationOrder (R := O) G t : ℝ≥0∞)) s]
  simp only [nsmul_eq_mul, Nat.card_eq_fintype_card]

/-- Tate's exact average over distinct actual restriction embeddings in an
arbitrary finite separable tower. Neither field need be stable under `s`. -/
theorem embeddingOrder_eq_sum_restrictionFiber
    (E F : IntermediateField K Ω) (hEF : E ≤ F) (s : G) :
    letI := Fintype.ofFinite (embeddingRestrictionFiber hEF (s.toAlgHom.comp E.val))
    embeddingRamificationOrder K (s.toAlgHom.comp E.val) E.val =
      (∑ τ : embeddingRestrictionFiber hEF (s.toAlgHom.comp E.val),
        embeddingRamificationOrder K τ.1 F.val) /
          embeddingRamificationIdx K (IntermediateField.inclusion hEF) := by
  classical
  let := Fintype.ofFinite E.fixingSubgroup
  let := Fintype.ofFinite F.fixingSubgroup
  let := Fintype.ofFinite (embeddingRestrictionFiber hEF (s.toAlgHom.comp E.val))
  have hdup := sum_fixingRestrictionMap hEF s
    (fun τ => embeddingRamificationOrder K τ.1 F.val)
  have hsum := sum_embeddingOrder_fixing_restrictions K Ω E F hEF s
  have hc0 : (Nat.card F.fixingSubgroup : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := F.fixingSubgroup)).ne'
  have hcard : (Nat.card F.fixingSubgroup : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hdist : (∑ τ : embeddingRestrictionFiber hEF (s.toAlgHom.comp E.val),
      embeddingRamificationOrder K τ.1 F.val) =
        (∑ d : E.fixingSubgroup, (ramificationOrder (R := O) G (s * d.1) : ℝ≥0∞)) /
          embeddingRamificationIdx K F.val := by
    apply (ENNReal.mul_right_inj hc0 hcard).mp
    rw [← hdup]
    exact hsum.trans (mul_div_assoc _ _ _)
  have he := embeddingRamificationIdx_comp K (IntermediateField.inclusion hEF) F.val
  change embeddingRamificationIdx K E.val =
    embeddingRamificationIdx K (IntermediateField.inclusion hEF) *
      embeddingRamificationIdx K F.val at he
  rw [hdist, embeddingOrder_intermediate_eq_sum_div K Ω E, he, Nat.cast_mul]
  simp only [div_eq_mul_inv, mul_assoc]
  congr 1
  rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
    (Or.inl (ENNReal.natCast_ne_top _)), mul_comm]

/-- The distinct-fiber formula applies to any original finite embedding,
by its genuine extension to the finite normal ambient field. -/
theorem embeddingOrder_restriction_eq_sum
    (E F : IntermediateField K Ω) (hEF : E ≤ F) (σ : F →ₐ[K] Ω) :
    letI := Fintype.ofFinite
      (embeddingRestrictionFiber hEF (σ.comp (IntermediateField.inclusion hEF)))
    embeddingRamificationOrder K (σ.comp (IntermediateField.inclusion hEF)) E.val =
      (∑ τ : embeddingRestrictionFiber hEF (σ.comp (IntermediateField.inclusion hEF)),
        embeddingRamificationOrder K τ.1 F.val) /
          embeddingRamificationIdx K (IntermediateField.inclusion hEF) := by
  obtain ⟨s, hs⟩ := exists_aut_extends_intermediate_embedding K Ω F σ
  have hsF : s.toAlgHom.comp F.val = σ := AlgHom.ext hs
  subst σ
  exact embeddingOrder_eq_sum_restrictionFiber K Ω E F hEF s

end FiniteTateFiber

section IndexSquare

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    {E E' F F' : Type*} [Field E] [Field E'] [Field F] [Field F']
    [Algebra K E] [Algebra K E'] [Algebra K F] [Algebra K F']
    [FiniteDimensional K E] [FiniteDimensional K E']
    [FiniteDimensional K F] [FiniteDimensional K F']
    [Algebra.IsSeparable K E] [Algebra.IsSeparable K E']
    [Algebra.IsSeparable K F] [Algebra.IsSeparable K F']

/-- The actual local ramification index is unchanged by a commuting
square of genuine source and target field isomorphisms. -/
theorem embeddingRamificationIdx_isomorphic_square
    (eE : E ≃ₐ[K] E') (eF : F ≃ₐ[K] F') (u : E' →ₐ[K] F') (v : E →ₐ[K] F)
    (hcomm : u.comp eE.toAlgHom = eF.toAlgHom.comp v) :
    embeddingRamificationIdx K u = embeddingRamificationIdx K v := by
  have ha := embeddingRamificationIdx_comp K eE.toAlgHom u
  have hb := embeddingRamificationIdx_comp K v eF.toAlgHom
  rw [embeddingRamificationIdx_algEquiv K eE, one_mul] at ha
  rw [embeddingRamificationIdx_algEquiv K eF, mul_one] at hb
  exact ha.symm.trans ((congrArg (embeddingRamificationIdx K) hcomm).trans hb)

end IndexSquare

section ClosureRestriction

variable (K : Type*) [Field K]
    (E F : IntermediateField K (SeparableClosure K)) [FiniteDimensional K F] (hEF : E ≤ F)

local notation "Ω" => finiteGaloisNormalClosure K F
local notation "hFΩ" => le_finiteGaloisNormalClosure K F
local notation "hEΩ" => hEF.trans hFΩ
local notation "E₀" => IntermediateField.restrict hEΩ
local notation "F₀" => IntermediateField.restrict hFΩ
local notation "eE" => IntermediateField.restrictAlgEquiv hEΩ
local notation "eF" => IntermediateField.restrictAlgEquiv hFΩ

/-- Restricting two original nested fields to their actual finite normal
closure preserves their actual inclusion. -/
theorem normalClosureRestriction_le : E₀ ≤ F₀ := fun x hx =>
  (IntermediateField.mem_restrict hFΩ x).mpr
    (hEF ((IntermediateField.mem_restrict hEΩ x).mp hx))

/-- The canonical original-field equivalences commute with the original
inclusion, on the actual carriers. -/
theorem normalClosureRestriction_inclusion :
    (IntermediateField.inclusion (normalClosureRestriction_le K E F hEF)).comp (eE).toAlgHom =
      (eF).toAlgHom.comp (IntermediateField.inclusion hEF) := by
  apply AlgHom.ext
  intro x
  rfl

omit E hEF in
/-- Every original closure embedding lands in the actual finite normal
closure; this is supplied by the canonical normal-closure construction. -/
def restrictedNormalClosureEmbedding (τ : F →ₐ[K] SeparableClosure K) : F₀ →ₐ[K] Ω :=
  (τ.codRestrict (Ω).toIntermediateField.toSubalgebra
    (fun x => τ.fieldRange_le_normalClosure ⟨x, rfl⟩)).comp (eF).symm.toAlgHom

omit E hEF in
@[simp]
theorem coe_restrictedNormalClosureEmbedding (τ : F →ₐ[K] SeparableClosure K) (x : F₀) :
    (restrictedNormalClosureEmbedding K F τ x : SeparableClosure K) = τ ((eF).symm x) := rfl

/-- The finite ambient and intrinsic closure fibers are canonically
bijective through the actual original field equivalences. -/
def normalClosureRestrictionFiberEquiv (σ : F →ₐ[K] SeparableClosure K) :
    embeddingRestrictionFiber (normalClosureRestriction_le K E F hEF)
      ((restrictedNormalClosureEmbedding K F σ).comp
        (IntermediateField.inclusion (normalClosureRestriction_le K E F hEF))) ≃
      embeddingRestrictionFiber hEF (σ.comp (IntermediateField.inclusion hEF)) := by
  let h₀ := normalClosureRestriction_le K E F hEF
  have hcomm := normalClosureRestriction_inclusion K E F hEF
  have harg (x : E) : IntermediateField.inclusion h₀ (eE x) =
      eF (IntermediateField.inclusion hEF x) := AlgHom.congr_fun hcomm x
  have harg_inv (x : E₀) : (eF).symm (IntermediateField.inclusion h₀ x) =
      IntermediateField.inclusion hEF ((eE).symm x) := by
    apply (eF).injective
    simpa only [AlgEquiv.apply_symm_apply] using harg ((eE).symm x)
  exact {
    toFun := fun τ => ⟨(Ω).toIntermediateField.val.comp (τ.1.comp (eF).toAlgHom), by
      apply AlgHom.ext
      intro x
      have h := AlgHom.congr_fun τ.2 (eE x)
      have h' := congrArg (fun z : Ω => (z : SeparableClosure K)) h
      change (τ.1 (IntermediateField.inclusion h₀ (eE x)) : SeparableClosure K) =
        σ ((eF).symm (IntermediateField.inclusion h₀ (eE x))) at h'
      rw [harg x, (eF).symm_apply_apply] at h'
      exact h'⟩
    invFun := fun τ => ⟨restrictedNormalClosureEmbedding K F τ.1, by
      apply AlgHom.ext
      intro x
      apply Subtype.ext
      change τ.1 ((eF).symm (IntermediateField.inclusion h₀ x)) =
        σ ((eF).symm (IntermediateField.inclusion h₀ x))
      rw [harg_inv]
      exact AlgHom.congr_fun τ.2 ((eE).symm x)⟩
    left_inv := fun τ => by
      apply Subtype.ext
      apply AlgHom.ext
      intro x
      apply Subtype.ext
      change (τ.1 (eF ((eF).symm x)) : SeparableClosure K) = (τ.1 x : SeparableClosure K)
      rw [(eF).apply_symm_apply]
    right_inv := fun τ => by
      apply Subtype.ext
      apply AlgHom.ext
      intro x
      change τ.1 ((eF).symm (eF x)) = τ.1 x
      rw [(eF).symm_apply_apply] }

@[simp]
theorem normalClosureRestrictionFiberEquiv_apply (σ : F →ₐ[K] SeparableClosure K)
    (τ : embeddingRestrictionFiber (normalClosureRestriction_le K E F hEF)
      ((restrictedNormalClosureEmbedding K F σ).comp
        (IntermediateField.inclusion (normalClosureRestriction_le K E F hEF)))) :
    (normalClosureRestrictionFiberEquiv K E F hEF σ τ).1 =
      (Ω).toIntermediateField.val.comp (τ.1.comp (eF).toAlgHom) := rfl

/-- Factoring through the actual finite normal closure retains the original
lower restriction, rather than replacing it by an unrelated embedding. -/
theorem restrictedNormalClosureEmbedding_inclusion (σ : F →ₐ[K] SeparableClosure K) :
    (Ω).toIntermediateField.val.comp
      (((restrictedNormalClosureEmbedding K F σ).comp
        (IntermediateField.inclusion (normalClosureRestriction_le K E F hEF))).comp
          (eE).toAlgHom) = σ.comp (IntermediateField.inclusion hEF) := by
  apply AlgHom.ext
  intro x
  change σ ((eF).symm (IntermediateField.inclusion
    (normalClosureRestriction_le K E F hEF) (eE x))) = σ _
  rw [show IntermediateField.inclusion (normalClosureRestriction_le K E F hEF) (eE x) =
    eF (IntermediateField.inclusion hEF x) from
      AlgHom.congr_fun (normalClosureRestriction_inclusion K E F hEF) x,
    (eF).symm_apply_apply]
  rfl

end ClosureRestriction

section ClosureTateFiber

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
    (E F : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [FiniteDimensional K F] (hEF : E ≤ F)

local notation "Ω" => finiteGaloisNormalClosure K F
local notation "hFΩ" => le_finiteGaloisNormalClosure K F
local notation "hEΩ" => hEF.trans hFΩ
local notation "E₀" => IntermediateField.restrict hEΩ
local notation "F₀" => IntermediateField.restrict hFΩ
local notation "eE" => IntermediateField.restrictAlgEquiv hEΩ
local notation "eF" => IntermediateField.restrictAlgEquiv hFΩ
local notation "h₀" => normalClosureRestriction_le K E F hEF

omit [PerfectField (IsLocalRing.ResidueField
  (NormedField.valuation (K := K)).valuationSubring)] in
/-- The original ramification index is preserved by the actual normal
closure presentation, by two genuine source isomorphisms and the index tower. -/
theorem embeddingRamificationIdx_normalClosureRestriction :
    embeddingRamificationIdx K (IntermediateField.inclusion h₀) =
      embeddingRamificationIdx K (IntermediateField.inclusion hEF) := by
  exact embeddingRamificationIdx_isomorphic_square K eE eF _ _
    (normalClosureRestriction_inclusion K E F hEF)

/-- The full distinct-fiber Tate formula in the actual separable closure.
Its contract retains all original embeddings and has no finite-ambient choice. -/
theorem closureEmbeddingOrder_restriction_eq_sum
    (σ : F →ₐ[K] SeparableClosure K) :
    letI := Fintype.ofFinite
      (embeddingRestrictionFiber hEF (σ.comp (IntermediateField.inclusion hEF)))
    closureEmbeddingOrder K (σ.comp (IntermediateField.inclusion hEF)) E.val =
      (∑ τ : embeddingRestrictionFiber hEF (σ.comp (IntermediateField.inclusion hEF)),
        closureEmbeddingOrder K τ.1 F.val) /
          embeddingRamificationIdx K (IntermediateField.inclusion hEF) := by
  classical
  let σ₀ := restrictedNormalClosureEmbedding K F σ
  let Ξ := embeddingRestrictionFiber hEF (σ.comp (IntermediateField.inclusion hEF))
  let Ξ₀ := embeddingRestrictionFiber h₀ (σ₀.comp (IntermediateField.inclusion h₀))
  let ξ := normalClosureRestrictionFiberEquiv K E F hEF σ
  let := Fintype.ofFinite Ξ
  let := Fintype.ofFinite Ξ₀
  have horder (τ : Ξ₀) : closureEmbeddingOrder K (ξ τ).1 F.val =
      embeddingRamificationOrder K τ.1 (F₀).val := by
    rw [normalClosureRestrictionFiberEquiv_apply]
    have h := closureEmbeddingOrder_comp K (τ.1.comp (eF).toAlgHom)
      ((F₀).val.comp (eF).toAlgHom) (Ω).toIntermediateField.val
    exact h.trans (embeddingOrder_precomp_algEquiv K eF τ.1 (F₀).val)
  have hsum : (∑ τ : Ξ, closureEmbeddingOrder K τ.1 F.val) =
      ∑ τ : Ξ₀, embeddingRamificationOrder K τ.1 (F₀).val :=
    ((ξ.sum_comp _).symm).trans (Finset.sum_congr rfl fun τ _ => horder τ)
  have hbase : closureEmbeddingOrder K (σ.comp (IntermediateField.inclusion hEF)) E.val =
      embeddingRamificationOrder K (σ₀.comp (IntermediateField.inclusion h₀)) (E₀).val := by
    have h := closureEmbeddingOrder_comp K
      ((σ₀.comp (IntermediateField.inclusion h₀)).comp (eE).toAlgHom)
      ((E₀).val.comp (eE).toAlgHom) (Ω).toIntermediateField.val
    rw [restrictedNormalClosureEmbedding_inclusion] at h
    exact h.trans (embeddingOrder_precomp_algEquiv K eE _ _)
  rw [hsum, hbase, ← embeddingRamificationIdx_normalClosureRestriction K E F hEF]
  exact embeddingOrder_restriction_eq_sum K Ω E₀ F₀ h₀ σ₀

/-- The signed distinct-fiber identity, with its positive original index
cleared. All terms are nonnegative shifted numbers, so infinity is retained. -/
theorem closureEmbeddingNumber_restriction_mul_index_eq_sum
    (σ : F →ₐ[K] SeparableClosure K) :
    letI := Fintype.ofFinite
      (embeddingRestrictionFiber hEF (σ.comp (IntermediateField.inclusion hEF)))
    (embeddingRamificationIdx K (IntermediateField.inclusion hEF) : EReal) *
      (closureEmbeddingNumber K (σ.comp (IntermediateField.inclusion hEF)) E.val + 1) =
        ∑ τ : embeddingRestrictionFiber hEF (σ.comp (IntermediateField.inclusion hEF)),
          (closureEmbeddingNumber K τ.1 F.val + 1) := by
  classical
  let := Fintype.ofFinite
    (embeddingRestrictionFiber hEF (σ.comp (IntermediateField.inclusion hEF)))
  have h := congrArg (fun r : ℝ≥0∞ =>
    r * embeddingRamificationIdx K (IntermediateField.inclusion hEF))
      (closureEmbeddingOrder_restriction_eq_sum K E F hEF σ)
  rw [ENNReal.div_mul_cancel
    (Nat.cast_ne_zero.mpr (embeddingRamificationIdx_pos K
      (IntermediateField.inclusion hEF)).ne') (ENNReal.natCast_ne_top _)] at h
  have h' := congrArg (fun r : ℝ≥0∞ => (r : EReal)) h
  let c : ℝ≥0∞ →+ EReal :=
    ⟨⟨(↑), EReal.coe_ennreal_zero⟩, EReal.coe_ennreal_add⟩
  have hsum := map_sum c (fun τ : embeddingRestrictionFiber hEF
    (σ.comp (IntermediateField.inclusion hEF)) => closureEmbeddingOrder K τ.1 F.val) Finset.univ
  rw [EReal.coe_ennreal_mul, ENNReal.toEReal_natCast] at h'
  have h'' := h'.trans hsum
  simpa only [closureEmbeddingNumber_add_one, EReal.mul_comm, c, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk] using h''

end ClosureTateFiber

end FontaineWintenberger
