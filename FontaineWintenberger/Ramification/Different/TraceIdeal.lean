/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Ramification.Different.Hilbert

/-!
# Trace ideals and the codifferent

The trace-containment test uses the canonical different and the trace
map. Scaling by a nonzero base-field element converts containment in a
principal fractional ideal to containment in the codifferent.
-/

@[expose] public section

namespace FontaineWintenberger

open scoped nonZeroDivisors

section General

variable (A B K L : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing B] [IsDedekindDomain B]
    [Field K] [Field L] [Algebra A B] [Module.IsTorsionFree A B]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L]

/-- A fractional ideal has integral traces exactly when it is contained in
the inverse different. Its ideal property supplies all products in
the trace pairing. -/
theorem trace_integral_iff_le_codifferent (I : FractionalIdeal B⁰ L) :
    (∀ x ∈ I, Algebra.trace K L x ∈ (1 : Submodule A K)) ↔
      I ≤ (differentIdeal A B : FractionalIdeal B⁰ L)⁻¹ := by
  rw [coeIdeal_differentIdeal A K L B, inv_inv,
    ← FractionalIdeal.coe_le_coe, FractionalIdeal.coe_dual_one,
    Submodule.le_traceDual_iff_map_le_one, mul_one]
  exact Iff.symm Submodule.map_le_iff_le_comap

omit [IsDomain A] [IsIntegrallyClosed A] in
private theorem mem_principal_iff_inv_mul {a x : K} (ha : a ≠ 0) :
    x ∈ FractionalIdeal.spanSingleton A⁰ a ↔
      a⁻¹ * x ∈ (1 : FractionalIdeal A⁰ K) := by
  rw [← mul_one (FractionalIdeal.spanSingleton A⁰ a), FractionalIdeal.mem_singleton_mul]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [ha] using hy
  · intro hx
    exact ⟨a⁻¹ * x, hx, by simp [ha]⟩

/-- Trace containment in a principal base fractional ideal is
equivalent to containment in that ideal times the codifferent. -/
theorem trace_principal_iff_le_mul_codifferent (I : FractionalIdeal B⁰ L)
    {a : K} (ha : a ≠ 0) :
    (∀ x ∈ I, Algebra.trace K L x ∈ FractionalIdeal.spanSingleton A⁰ a) ↔
      I ≤ FractionalIdeal.spanSingleton B⁰ (algebraMap K L a) *
        (differentIdeal A B : FractionalIdeal B⁰ L)⁻¹ := by
  let α : L := algebraMap K L a
  have hα : α ≠ 0 := by simpa [α] using (algebraMap K L).injective.ne ha
  have htrace (x : L) : Algebra.trace K L (α⁻¹ * x) = a⁻¹ * Algebra.trace K L x := by
    change Algebra.trace K L ((algebraMap K L a)⁻¹ * x) = _
    rw [← map_inv₀]
    simpa [Algebra.smul_def] using (Algebra.trace K L).map_smul a⁻¹ x
  have hscale :
      (∀ x ∈ I, Algebra.trace K L x ∈ FractionalIdeal.spanSingleton A⁰ a) ↔
      ∀ z ∈ FractionalIdeal.spanSingleton B⁰ α⁻¹ * I,
        Algebra.trace K L z ∈ (1 : Submodule A K) := by
    constructor
    · intro h z hz
      obtain ⟨x, hx, rfl⟩ := FractionalIdeal.mem_singleton_mul.mp hz
      rw [htrace]
      simpa only [← FractionalIdeal.mem_coe, FractionalIdeal.coe_one] using
        (mem_principal_iff_inv_mul A K ha).mp (h x hx)
    · intro h x hx
      apply (mem_principal_iff_inv_mul A K ha).mpr
      rw [← htrace]
      simpa only [← FractionalIdeal.mem_coe, FractionalIdeal.coe_one] using
        h _ (FractionalIdeal.mem_singleton_mul.mpr ⟨x, hx, rfl⟩)
  rw [hscale, trace_integral_iff_le_codifferent A B K L,
    FractionalIdeal.spanSingleton_mul_le_iff, FractionalIdeal.le_spanSingleton_mul_iff]
  dsimp [α] at hα ⊢
  constructor
  · intro h x hx
    exact ⟨_, h x hx, by simp [hα]⟩
  · intro h x hx
    obtain ⟨y, hy, hxy⟩ := h x hx
    rw [← hxy]
    simpa [hα] using hy

/-- Multiplying by the different clears the codifferent in the
trace-containment test. -/
theorem trace_principal_iff_mul_different_le (I : FractionalIdeal B⁰ L)
    {a : K} (ha : a ≠ 0) :
    (∀ x ∈ I, Algebra.trace K L x ∈ FractionalIdeal.spanSingleton A⁰ a) ↔
      I * (differentIdeal A B : FractionalIdeal B⁰ L) ≤
        FractionalIdeal.spanSingleton B⁰ (algebraMap K L a) := by
  have hD : (differentIdeal A B : FractionalIdeal B⁰ L) ≠ 0 := by
    rw [coeIdeal_differentIdeal A K L B]
    exact inv_ne_zero (FractionalIdeal.dual_ne_zero A K (I := (1 : FractionalIdeal B⁰ L))
        one_ne_zero)
  rw [trace_principal_iff_le_mul_codifferent A B K L I ha, ← div_eq_mul_inv]
  exact FractionalIdeal.le_div_iff_mul_le hD

variable [Module.Finite A B]

include K L in
/-- The integral trace sends an integral ideal into a principal base
ideal exactly when its product with the different is contained in
the extended base ideal. -/
theorem intTrace_mem_principal_iff_mul_different_le (I : Ideal B)
    {a : A} (ha : a ≠ 0) :
    (∀ x ∈ I, Algebra.intTrace A B x ∈ Ideal.span {a}) ↔
      I * differentIdeal A B ≤ (Ideal.span {a}).map (algebraMap A B) := by
  have haK : algebraMap A K a ≠ 0 := by
    simpa using (IsFractionRing.injective A K).ne ha
  have hmem (x : A) :
      algebraMap A K x ∈ FractionalIdeal.spanSingleton A⁰ (algebraMap A K a) ↔
        x ∈ Ideal.span {a} := by
    rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.mem_coeIdeal]
    constructor
    · rintro ⟨y, hy, he⟩
      exact (IsFractionRing.injective A K he) ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have htrace :
      (∀ x ∈ I, Algebra.intTrace A B x ∈ Ideal.span {a}) ↔
      ∀ x ∈ (I : FractionalIdeal B⁰ L),
        Algebra.trace K L x ∈ FractionalIdeal.spanSingleton A⁰ (algebraMap A K a) := by
    constructor
    · intro h x hx
      obtain ⟨y, hy, rfl⟩ := (FractionalIdeal.mem_coeIdeal B⁰).mp hx
      rw [← Algebra.algebraMap_intTrace (A := A) (B := B) (K := K) (L := L), hmem]
      exact h y hy
    · intro h x hx
      rw [← hmem, Algebra.algebraMap_intTrace (A := A) (B := B) (K := K) (L := L)]
      exact h _ (FractionalIdeal.mem_coeIdeal_of_mem B⁰ hx)
  rw [htrace, trace_principal_iff_mul_different_le A B K L _ haK]
  rw [← FractionalIdeal.coeIdeal_mul, ← IsScalarTower.algebraMap_apply A K L,
    IsScalarTower.algebraMap_eq A B L, RingHom.comp_apply,
    ← FractionalIdeal.coeIdeal_span_singleton, Ideal.map_span, Set.image_singleton]
  exact FractionalIdeal.coeIdeal_le_coeIdeal L

end General

section DVR

open IsLocalRing IsDiscreteValuationRing

variable (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
    [FaithfulSMul A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]

/-- The trace ideal is the image of the given ideal under integral
trace, with its canonical base-module structure. -/
noncomputable def intTraceIdeal (I : Ideal B) : Ideal A :=
  (I.restrictScalars A).map (Algebra.intTrace A B)

omit [IsLocalHom (algebraMap A B)] in
theorem intTraceIdeal_le_iff (I : Ideal B) (J : Ideal A) :
    intTraceIdeal A B I ≤ J ↔ ∀ x ∈ I, Algebra.intTrace A B x ∈ J :=
  Submodule.map_le_iff_le_comap

private theorem maximalIdeal_pow_le_pow_iff (m n : ℕ) :
    IsLocalRing.maximalIdeal B ^ m ≤ IsLocalRing.maximalIdeal B ^ n ↔ n ≤ m := by
  constructor
  · intro h
    obtain ⟨π, hπ⟩ := exists_irreducible B
    have hm : π ^ m ∈ IsLocalRing.maximalIdeal B ^ m := by
      rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
      exact Ideal.subset_span (by simp)
    have hv := (mem_maximalIdeal_pow_iff_addVal (π ^ m) n).mp (h hm)
    rw [hπ.addVal_pow] at hv
    exact_mod_cast hv
  · exact Ideal.pow_le_pow_right

/-- A nonzero DVR ideal is the power given by its canonical maximal
ideal multiplicity. -/
theorem ideal_eq_pow_emultiplicity (I : Ideal B) (hI : I ≠ ⊥) :
    I = IsLocalRing.maximalIdeal B ^ (emultiplicity (IsLocalRing.maximalIdeal B) I).toNat := by
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_eq_of_principal B
    (inferInstance : (IsLocalRing.maximalIdeal B).IsPrincipal) I hI
  obtain ⟨π, hπ⟩ := exists_irreducible B
  have hpow : IsLocalRing.maximalIdeal B ^ n = Ideal.span {π ^ n} := by
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
  have horder : emultiplicity (IsLocalRing.maximalIdeal B) I = n := by
    rw [hn, hpow, maximalIdeal_emultiplicity_span, hπ.addVal_pow]
  simpa only [horder, ENat.toNat_natCast] using hn

variable (K L : Type*) [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L]

include K L in
/-- The exact power-containment criterion for the trace image, using the
canonical ramification index and different multiplicity. -/
theorem intTraceIdeal_pow_le_pow_iff (n s : ℕ) :
    intTraceIdeal A B (IsLocalRing.maximalIdeal B ^ n) ≤ IsLocalRing.maximalIdeal A ^ s ↔
      (IsLocalRing.maximalIdeal B).ramificationIdx A * s ≤
        (emultiplicity (IsLocalRing.maximalIdeal B) (differentIdeal A B)).toNat + n := by
  have hD : differentIdeal A B ≠ ⊥ := by
    intro h
    have hz : (differentIdeal A B : FractionalIdeal B⁰ L) = 0 := by simp [h]
    rw [coeIdeal_differentIdeal A K L B] at hz
    exact (inv_ne_zero (FractionalIdeal.dual_ne_zero A K
      (I := (1 : FractionalIdeal B⁰ L)) one_ne_zero)) hz
  rw [intTraceIdeal_le_iff]
  obtain ⟨π, hπ⟩ := exists_irreducible A
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow,
    intTrace_mem_principal_iff_mul_different_le A B K L _ (pow_ne_zero s hπ.ne_zero)]
  conv_lhs => rw [ideal_eq_pow_emultiplicity B (differentIdeal A B) hD]
  rw [← pow_add,
    ← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq, Ideal.map_pow,
    map_maximalIdeal_eq_pow_ramificationIdx A B, ← pow_mul,
    maximalIdeal_pow_le_pow_iff, Nat.add_comm]

include K L in
/-- The trace ideal of every nonnegative maximal-ideal power, with
the exact floor exponent and no residue-field finiteness or Galois hypothesis. -/
theorem intTraceIdeal_pow (n : ℕ) :
    intTraceIdeal A B (IsLocalRing.maximalIdeal B ^ n) =
      IsLocalRing.maximalIdeal A ^
        (((emultiplicity (IsLocalRing.maximalIdeal B) (differentIdeal A B)).toNat + n) /
          (IsLocalRing.maximalIdeal B).ramificationIdx A) := by
  have he := local_ramificationIdx_pos A B
  have hnonzero : intTraceIdeal A B (IsLocalRing.maximalIdeal B ^ n) ≠ ⊥ := by
    intro hzero
    have hlarge := (intTraceIdeal_pow_le_pow_iff A B K L n
      ((emultiplicity (IsLocalRing.maximalIdeal B) (differentIdeal A B)).toNat + n + 1)).mp
        (by simp only [hzero, bot_le])
    nlinarith
  obtain ⟨s, hs⟩ := exists_maximalIdeal_pow_eq_of_principal A
    (inferInstance : (IsLocalRing.maximalIdeal A).IsPrincipal) _ hnonzero
  apply le_antisymm
  · apply (intTraceIdeal_pow_le_pow_iff A B K L n _).mpr
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self
      ((emultiplicity (IsLocalRing.maximalIdeal B) (differentIdeal A B)).toNat + n)
      ((IsLocalRing.maximalIdeal B).ramificationIdx A)
  · rw [hs, maximalIdeal_pow_le_pow_iff]
    apply (Nat.le_div_iff_mul_le he).mpr
    have hh := (intTraceIdeal_pow_le_pow_iff A B K L n s).mp (by rw [hs])
    simpa only [Nat.mul_comm] using hh

end DVR

section ChosenExtension

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]

variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ)
    [(NormedField.valuation (K := K)).HasExtension w]

local notation "OL" => Valuation.valuationSubring w

/-- The exact trace-ideal formula on every compatible extension
valuation ring, over an arbitrary residue field. -/
theorem extensionValuationSubring_intTraceIdeal_pow (n : ℕ) :
    letI := extensionValuationSubring_isDiscreteValuationRing K L w
    intTraceIdeal 𝒪[K] OL (IsLocalRing.maximalIdeal OL ^ n) =
      IsLocalRing.maximalIdeal 𝒪[K] ^
        (((emultiplicity (IsLocalRing.maximalIdeal OL) (differentIdeal 𝒪[K] OL)).toNat + n) /
          (IsLocalRing.maximalIdeal OL).ramificationIdx 𝒪[K]) := by
  have := extensionValuationSubring_isDiscreteValuationRing K L w
  exact intTraceIdeal_pow 𝒪[K] OL K L n

end ChosenExtension

end FontaineWintenberger
