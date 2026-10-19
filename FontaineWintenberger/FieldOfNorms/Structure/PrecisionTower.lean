/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.APF.Tower.Stages
public import FontaineWintenberger.APF.Tower.PrimeValuation
public import FontaineWintenberger.FieldOfNorms.Basic.Valuation
public import FontaineWintenberger.FieldOfNorms.Estimates.Truncated

/-!
# Deep cofinal finite towers

The abstract APF extension supplies an increasing cofinal sequence
of finite subfields with growing norm precision. Every stage contains
the wild and stable-valuation witnesses and the residue prime lies in
the required maximal-ideal power.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K

variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- Finite composita enlarge any prescribed sequence of finite intermediate fields
inside a monotone cofinal sequence of the APF extension. -/
theorem IsAPF.exists_monotone_cofinal_finiteIntermediateFields_ge [IsAPF K L]
    (A : ℕ → FiniteIntermediateField K L) :
    ∃ E : ℕ → FiniteIntermediateField K L, Monotone E ∧ (∀ n, A n ≤ E n) ∧
      ∀ D : FiniteIntermediateField K L, ∃ n : ℕ, D ≤ E n := by
  obtain ⟨C, _hCmono, hC⟩ := IsAPF.exists_monotone_cofinal_finiteIntermediateFields K L
  let B (n : ℕ) := FiniteIntermediateField.sup (A n) (C n)
  let E : ℕ → FiniteIntermediateField K L :=
    Nat.rec (B 0) (fun n D => FiniteIntermediateField.sup D (B (n + 1)))
  have hBE (n : ℕ) : B n ≤ E n := by
    cases n with
    | zero => exact le_rfl
    | succ n => exact FiniteIntermediateField.le_sup_right (E n) (B (n + 1))
  refine ⟨E, monotone_nat_of_le_succ (fun n => ?_), fun n => ?_, fun D => ?_⟩
  · exact FiniteIntermediateField.le_sup_left (E n) (B (n + 1))
  · exact (FiniteIntermediateField.le_sup_left (A n) (C n)).trans (hBE n)
  · obtain ⟨n, hn⟩ := hC D
    exact ⟨n, hn.trans ((FiniteIntermediateField.le_sup_right (A n) (C n)).trans (hBE n))⟩

/-- The deep first-bound parameter at the growing integer precision. -/
def deepFiniteTowerBound (n : ℕ) : ℝ :=
  (p : ℝ) / ((p - 1 : ℕ) : ℝ) * (n + 2)

/-- The chosen real first bound gives exactly the required integer precision. -/
@[simp]
theorem ceil_deepFiniteTowerBound (n : ℕ) :
    ⌈((p - 1 : ℕ) : ℝ) / p * deepFiniteTowerBound K n⌉₊ = n + 2 := by
  have hp : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero
  have hp₁ : ((p - 1 : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by have := (Fact.out : Nat.Prime p).two_le; omega)
  have hc : ((p - 1 : ℕ) : ℝ) / p * deepFiniteTowerBound K n = ((n + 2 : ℕ) : ℝ) := by
    dsimp only [deepFiniteTowerBound]
    push_cast
    field_simp
  rw [hc, Nat.ceil_natCast]

/-- An infinite abstract APF extension has an increasing
cofinal tower with growing precision, the stable valuation, an
entire wild tail, and all later relative first bounds. -/
theorem IsAPF.exists_deep_finiteTower [IsAPF K L]
    [Fact (¬ Module.Finite K L)] (D : FiniteIntermediateField K L) :
    ∃ E : ℕ → FiniteIntermediateField K L, Monotone E ∧ (∀ n, D ≤ E n) ∧
      (∀ F : FiniteIntermediateField K L, ∃ n : ℕ, F ≤ E n) ∧
      (∀ n α, FieldOfNorms.valuation K L α = FieldOfNorms.coordinateValuation K L (E n) α) ∧
      (∀ n, (p : spectralIntegerRing K (E n).val) ∈
        IsLocalRing.maximalIdeal (spectralIntegerRing K (E n).val) ^ (n + 2)) ∧
      (∀ A B : FiniteIntermediateField K L, E 0 ≤ A → ∀ hAB : A ≤ B,
        Function.Surjective (spectralResidueInclusion K (IntermediateField.inclusion hAB)) ∧
          (∃ d : ℕ, Module.finrank A.val (IntermediateField.extendScalars hAB) = p ^ d) ∧
          letI : Algebra A.val B.val := (IntermediateField.inclusion hAB).toRingHom.toAlgebra
          letI : IsScalarTower K A.val B.val := IsScalarTower.of_algebraMap_eq' rfl
          letI := spectralValuation_hasExtension_tower K (E := A.val) (L := B.val)
          (IsLocalRing.maximalIdeal (spectralIntegerRing K B.val)).ramificationIdx
            (spectralIntegerRing K A.val) =
              Module.finrank A.val (IntermediateField.extendScalars hAB)) ∧
      (∀ n (F : FiniteIntermediateField K L) (hEF : E n ≤ F),
        letI := spectralNorm.nontriviallyNormedField K (E n).val
        letI := spectralNorm.normedAlgebra K (E n).val
        letI := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
          (isNonarchimedean_spectralNorm (K := K) (L := (E n).val))
        letI := spectralNorm.completeSpace K (E n).val
        letI := normedAlgebra_isCompleteDiscreteValuedField K (E n).val
        (deepFiniteTowerBound K n : EReal) ≤
          apfRamificationBound (E n).val (IntermediateField.extendScalars hEF)) := by
  obtain ⟨W, hW⟩ := IsAPF.exists_finiteIntermediateField_wild_tail K L
  obtain ⟨V, hV⟩ := IsAPF.exists_fieldOfNormsValuation_eq_coordinate K L
  choose T hT using fun n : ℕ =>
    IsAPF.exists_finiteIntermediateField_relativeFirstBound_ge K L (deepFiniteTowerBound K n)
  choose P hP using fun n : ℕ =>
    IsAPF.exists_finiteIntermediateField_natCast_mem_maximalIdeal_pow K L (n + 2)
  let A (n : ℕ) := FiniteIntermediateField.sup D (FiniteIntermediateField.sup W
    (FiniteIntermediateField.sup V (FiniteIntermediateField.sup (T n) (P n))))
  obtain ⟨E, hmono, hA, hcofinal⟩ :=
    IsAPF.exists_monotone_cofinal_finiteIntermediateFields_ge K L A
  have hD (n : ℕ) : D ≤ E n :=
    (FiniteIntermediateField.le_sup_left _ _).trans (hA n)
  have hWn (n : ℕ) : W ≤ E n :=
    (FiniteIntermediateField.le_sup_left W _).trans ((FiniteIntermediateField.le_sup_right D
        _).trans (hA n))
  have hVn (n : ℕ) : V ≤ E n :=
    (FiniteIntermediateField.le_sup_left V _).trans ((FiniteIntermediateField.le_sup_right W
        _).trans
      ((FiniteIntermediateField.le_sup_right D _).trans (hA n)))
  have hTn (n : ℕ) : T n ≤ E n :=
    (FiniteIntermediateField.le_sup_left (T n) (P n)).trans ((FiniteIntermediateField.le_sup_right
        V _).trans
      ((FiniteIntermediateField.le_sup_right W _).trans ((FiniteIntermediateField.le_sup_right D
          _).trans (hA n))))
  have hPn (n : ℕ) : P n ≤ E n :=
    (FiniteIntermediateField.le_sup_right (T n) (P n)).trans ((FiniteIntermediateField.le_sup_right
        V _).trans
      ((FiniteIntermediateField.le_sup_right W _).trans ((FiniteIntermediateField.le_sup_right D
          _).trans (hA n))))
  exact ⟨E, hmono, hD, hcofinal, fun n => hV (E n) (hVn n),
    fun n => hP n (E n) (hPn n),
    fun A B hEA hAB => hW A B ((hWn 0).trans hEA) hAB,
    fun n F hEF => hT n (E n) F (hTn n) hEF⟩

/-- A choice of the proved deep finite tower, with no tower hypothesis. -/
def deepFiniteTower [IsAPF K L] [Fact (¬ Module.Finite K L)]
    (D : FiniteIntermediateField K L) : ℕ → FiniteIntermediateField K L :=
  (IsAPF.exists_deep_finiteTower K L D).choose

variable [IsAPF K L] [Fact (¬ Module.Finite K L)] (D : FiniteIntermediateField K L)

local notation "𝔈" => deepFiniteTower K L D

/-- The selected deep tower is increasing. -/
theorem deepFiniteTower_monotone : Monotone 𝔈 :=
  (IsAPF.exists_deep_finiteTower K L D).choose_spec.1

/-- Every selected stage contains the specified finite intermediate field. -/
theorem le_deepFiniteTower (n : ℕ) : D ≤ 𝔈 n :=
  (IsAPF.exists_deep_finiteTower K L D).choose_spec.2.1 n

/-- The selected tower is cofinal among all finite subfields. -/
theorem deepFiniteTower_cofinal (F : FiniteIntermediateField K L) : ∃ n, F ≤ 𝔈 n :=
  (IsAPF.exists_deep_finiteTower K L D).choose_spec.2.2.1 F

/-- Every selected finite coordinate computes the stable valuation. -/
theorem FieldOfNorms.valuation_eq_deepFiniteTower (n : ℕ) (α : FieldOfNorms K L) :
    FieldOfNorms.valuation K L α = FieldOfNorms.coordinateValuation K L (𝔈 n) α :=
  (IsAPF.exists_deep_finiteTower K L D).choose_spec.2.2.2.1 n α

/-- The residue prime is in the required ideal power at every selected stage. -/
theorem natCast_mem_deepFiniteTower_maximalIdeal_pow (n : ℕ) :
    (p : spectralIntegerRing K (𝔈 n).val) ∈
      IsLocalRing.maximalIdeal (spectralIntegerRing K (𝔈 n).val) ^ (n + 2) :=
  (IsAPF.exists_deep_finiteTower K L D).choose_spec.2.2.2.2.1 n

/-- The first selected finite stage begins an entire wild tail. -/
theorem deepFiniteTower_wild_tail (A B : FiniteIntermediateField K L) (hEA : 𝔈 0 ≤ A) (hAB : A ≤ B)
    :
    Function.Surjective (spectralResidueInclusion K (IntermediateField.inclusion hAB)) ∧
      (∃ d : ℕ, Module.finrank A.val (IntermediateField.extendScalars hAB) = p ^ d) ∧
      letI : Algebra A.val B.val := (IntermediateField.inclusion hAB).toRingHom.toAlgebra
      letI : IsScalarTower K A.val B.val := IsScalarTower.of_algebraMap_eq' rfl
      letI := spectralValuation_hasExtension_tower K (E := A.val) (L := B.val)
      (IsLocalRing.maximalIdeal (spectralIntegerRing K B.val)).ramificationIdx
        (spectralIntegerRing K A.val) =
          Module.finrank A.val (IntermediateField.extendScalars hAB) :=
  (IsAPF.exists_deep_finiteTower K L D).choose_spec.2.2.2.2.2.1 A B hEA hAB

/-- Every later finite extension has the requested first bound. -/
theorem deepFiniteTower_relativeFirstBound_ge (n : ℕ) (F : FiniteIntermediateField K L) (hEF : 𝔈 n
    ≤ F) :
    letI := spectralNorm.nontriviallyNormedField K (𝔈 n).val
    letI := spectralNorm.normedAlgebra K (𝔈 n).val
    letI := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
      (isNonarchimedean_spectralNorm (K := K) (L := (𝔈 n).val))
    letI := spectralNorm.completeSpace K (𝔈 n).val
    letI := normedAlgebra_isCompleteDiscreteValuedField K (𝔈 n).val
    (deepFiniteTowerBound K n : EReal) ≤
      apfRamificationBound (𝔈 n).val (IntermediateField.extendScalars hEF) :=
  (IsAPF.exists_deep_finiteTower K L D).choose_spec.2.2.2.2.2.2 n F hEF

/-- The integer-ring quotient at the stage's growing precision. -/
abbrev deepFiniteTowerQuotient (n : ℕ) :=
  spectralIntegerRing K (𝔈 n).val ⧸
    IsLocalRing.maximalIdeal (spectralIntegerRing K (𝔈 n).val) ^ (n + 2)

instance deepFiniteTowerQuotient_nontrivial (n : ℕ) :
    Nontrivial (deepFiniteTowerQuotient K L D n) :=
  Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top
      (Ideal.pow_le_self (by omega)))

instance deepFiniteTowerQuotient_isLocalRing (n : ℕ) :
    IsLocalRing (deepFiniteTowerQuotient K L D n) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

instance deepFiniteTowerQuotient_charP (n : ℕ) :
    CharP (deepFiniteTowerQuotient K L D n) p := by
  apply (CharP.charP_iff_prime_eq_zero (Fact.out : Nat.Prime p)).mpr
  rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]
  exact natCast_mem_deepFiniteTower_maximalIdeal_pow K L D n

/-- The quotient's maximal ideal vanishes to its stated precision. -/
theorem deepFiniteTowerQuotient_maximalIdeal_pow (n : ℕ) :
    IsLocalRing.maximalIdeal (deepFiniteTowerQuotient K L D n) ^ (n + 2) = ⊥ := by
  rw [← IsLocalRing.map_maximalIdeal_of_surjective
    (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective, ← Ideal.map_pow,
    Ideal.map_quotient_self]

/-- The exponent of the finite relative degree, chosen from the proved wild tail. -/
def deepFiniteTowerRelativeDegree (n : ℕ) (F : FiniteIntermediateField K L) (hEF : 𝔈 n ≤ F) : ℕ :=
  (deepFiniteTower_wild_tail K L D (𝔈 n) F
    (deepFiniteTower_monotone K L D (Nat.zero_le n)) hEF).2.1.choose

/-- The selected degree exponent computes the finite field degree. -/
theorem deepFiniteTower_finrank (n : ℕ) (F : FiniteIntermediateField K L) (hEF : 𝔈 n ≤ F) :
    Module.finrank (𝔈 n).val (IntermediateField.extendScalars hEF) =
      p ^ deepFiniteTowerRelativeDegree K L D n F hEF :=
  (deepFiniteTower_wild_tail K L D (𝔈 n) F
    (deepFiniteTower_monotone K L D (Nat.zero_le n)) hEF).2.1.choose_spec

/-- Every later finite intermediate field has a quotient norm at this
stage's precision; the map is induced by the integer norm. -/
def deepFiniteTowerNorm (n : ℕ) (F : FiniteIntermediateField K L) (hEF : 𝔈 n ≤ F)
    (s : ℕ) (hs : n + 2 ≤ s) :
    (spectralIntegerRing K F.val ⧸ IsLocalRing.maximalIdeal (spectralIntegerRing K F.val) ^ s) →+*
      deepFiniteTowerQuotient K L D n :=
  FiniteIntermediateField.truncatedNorm (𝔈 n) F hEF
    (deepFiniteTowerRelativeDegree K L D n F hEF)
    (deepFiniteTowerBound K n)
    (deepFiniteTower_wild_tail K L D (𝔈 n) F
      (deepFiniteTower_monotone K L D (Nat.zero_le n)) hEF).2.2
    (deepFiniteTower_finrank K L D n F hEF)
    (deepFiniteTower_relativeFirstBound_ge K L D n F hEF)
    (n + 2) s hs (by rw [ceil_deepFiniteTowerBound])

@[simp]
theorem deepFiniteTowerNorm_mk (n : ℕ) (F : FiniteIntermediateField K L) (hEF : 𝔈 n ≤ F)
    (s : ℕ) (hs : n + 2 ≤ s) (x : spectralIntegerRing K F.val) :
    deepFiniteTowerNorm K L D n F hEF s hs (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (FiniteIntermediateField.integerNorm (𝔈 n) F hEF x) := rfl

/-- Perfect-residue norm digits prove surjectivity from every later finite intermediate
    field. -/
theorem deepFiniteTowerNorm_surjective (n : ℕ) (F : FiniteIntermediateField K L) (hEF : 𝔈 n ≤ F)
    (s : ℕ) (hs : n + 2 ≤ s) :
    Function.Surjective (deepFiniteTowerNorm K L D n F hEF s hs) :=
  FiniteIntermediateField.truncatedNorm_surjective (𝔈 n) F hEF
    (deepFiniteTowerRelativeDegree K L D n F hEF)
    (deepFiniteTowerBound K n)
    (deepFiniteTower_wild_tail K L D (𝔈 n) F
      (deepFiniteTower_monotone K L D (Nat.zero_le n)) hEF).2.2
    (deepFiniteTower_finrank K L D n F hEF)
    (deepFiniteTower_relativeFirstBound_ge K L D n F hEF)
    (n + 2) s hs (by rw [ceil_deepFiniteTowerBound])

/-- Every later finite norm is additive to the tower stage's precision. -/
theorem deepFiniteTower_integerNorm_add_congruence (n : ℕ) (F : FiniteIntermediateField K L)
    (hEF : 𝔈 n ≤ F) (x y : spectralIntegerRing K F.val) :
    FiniteIntermediateField.integerNorm (𝔈 n) F hEF (x + y) -
      FiniteIntermediateField.integerNorm (𝔈 n) F hEF x - FiniteIntermediateField.integerNorm (𝔈 n)
          F hEF y ∈
        IsLocalRing.maximalIdeal (spectralIntegerRing K (𝔈 n).val) ^ (n + 2) := by
  let q := deepFiniteTowerNorm K L D n F hEF (n + 2) le_rfl
  have h := q.map_add (Ideal.Quotient.mk _ x) (Ideal.Quotient.mk _ y)
  change q (Ideal.Quotient.mk _ (x + y)) =
    q (Ideal.Quotient.mk _ x) + q (Ideal.Quotient.mk _ y) at h
  simp only [q, deepFiniteTowerNorm_mk] at h
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  simp only [map_sub]
  linear_combination h

/-- The norms induce the ring transition maps between tower stages. -/
def deepFiniteTowerTransition (n m : ℕ) (hnm : n ≤ m) :
    deepFiniteTowerQuotient K L D m →+*
      deepFiniteTowerQuotient K L D n :=
  deepFiniteTowerNorm K L D n (𝔈 m)
    (deepFiniteTower_monotone K L D hnm) (m + 2) (by omega)

@[simp]
theorem deepFiniteTowerTransition_mk (n m : ℕ) (hnm : n ≤ m)
    (x : spectralIntegerRing K (𝔈 m).val) :
    deepFiniteTowerTransition K L D n m hnm (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (FiniteIntermediateField.integerNorm (𝔈 n) (𝔈 m)
        (deepFiniteTower_monotone K L D hnm) x) := rfl

/-- Every transition in the constructed tower is surjective. -/
theorem deepFiniteTowerTransition_surjective (n m : ℕ) (hnm : n ≤ m) :
    Function.Surjective (deepFiniteTowerTransition K L D n m hnm) :=
  deepFiniteTowerNorm_surjective K L D n (𝔈 m)
    (deepFiniteTower_monotone K L D hnm) (m + 2) (by omega)

/-- Norm transitivity gives the exact quotient transition tower law. -/
theorem deepFiniteTowerTransition_comp (i n m : ℕ) (hin : i ≤ n) (hnm : n ≤ m) :
    (deepFiniteTowerTransition K L D i n hin).comp
        (deepFiniteTowerTransition K L D n m hnm) =
      deepFiniteTowerTransition K L D i m (hin.trans hnm) := by
  apply Ideal.Quotient.ringHom_ext
  ext x
  simp only [RingHom.comp_apply, deepFiniteTowerTransition_mk]
  rw [FiniteIntermediateField.integerNorm_integerNorm]

/-- The identity step induces the identity map at the same precision. -/
@[simp]
theorem deepFiniteTowerTransition_self (n : ℕ) :
    deepFiniteTowerTransition K L D n n le_rfl =
      RingHom.id (deepFiniteTowerQuotient K L D n) := by
  apply Ideal.Quotient.ringHom_ext
  ext x
  simp only [RingHom.comp_apply, deepFiniteTowerTransition_mk,
    FiniteIntermediateField.integerNorm_self, RingHom.id_apply]

/-- The quotient transitions preserve normalized valuation truncated
at the target precision, including zero and the identity step. -/
theorem deepFiniteTowerTransition_truncatedAddVal (n m : ℕ) (hnm : n ≤ m)
    (x : deepFiniteTowerQuotient K L D m) :
    truncatedAddVal (spectralIntegerRing K (𝔈 n).val) (n + 2)
        (deepFiniteTowerTransition K L D n m hnm x) =
      min (truncatedAddVal (spectralIntegerRing K (𝔈 m).val) (m + 2) x)
        ((n + 2 : ℕ) : ℕ∞) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [deepFiniteTowerTransition_mk, truncatedAddVal_mk, truncatedAddVal_mk,
    FiniteIntermediateField.addVal_integerNorm_of_totallyRamified (𝔈 n) (𝔈 m)
      (deepFiniteTower_monotone K L D hnm)
      (deepFiniteTower_wild_tail K L D (𝔈 n) (𝔈 m)
        (deepFiniteTower_monotone K L D (Nat.zero_le n))
        (deepFiniteTower_monotone K L D hnm)).2.2,
    min_assoc, min_eq_right (show ((n + 2 : ℕ) : ℕ∞) ≤ (m + 2 : ℕ) by exact_mod_cast (show n + 2 ≤ m
        + 2 by omega))]

end FontaineWintenberger
