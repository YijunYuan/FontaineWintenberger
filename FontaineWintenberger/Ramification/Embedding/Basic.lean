/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Ramification.Lower.Generator
public import FontaineWintenberger.Ramification.Lower.ResidueDigits
public import FontaineWintenberger.Ramification.Lower.SpectralMaps
public import FontaineWintenberger.Ramification.Lower.Teichmuller
public import FontaineWintenberger.Ramification.Lower.Tower
public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.Basic.Real.ENatENNReal
public import Mathlib.Data.EReal.Operations
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.LinearAlgebra.SModEq.Pow

/-!
# Ramification orders of pairs of finite-field embeddings

The raw order uses the integer-ring maps. Dividing by their
ramification index normalizes it in the field, independently of the
finite ambient field. No normality or finite-residue assumption is used.

## Main definitions

* `integralEmbeddingOrder`: The displacement infimum for two maps into a DVR.
* `embeddingRamificationIdx`: The canonical local-length index of the integer map of an embedding.
* `embeddingIntegralOrder`: The raw order is computed on the spectral integer rings.
* `embeddingRamificationOrder`: The pair order normalized in the field, including infinity.
* `embeddingPairField`: The finite compositum of the two images in the separable closure.
* `embeddingPairLeft`: The first embedding factored through the compositum.
* `embeddingPairRight`: The second embedding factored through the compositum.
* `closureEmbeddingOrder`: Closure-pair order computed in its finite image compositum.
* `embeddingRamificationNumber`, `closureEmbeddingNumber`: Wintenberger's signed ramification
  numbers, obtained by subtracting one from the corresponding orders.

## Main results

* `forall_sub_mem_iff_generator`: Congruence of two algebra maps is detected on any algebra
  generator.
* `integralEmbeddingOrder_eq_generator`: An integral algebra generator attains the displacement
  infimum.
* `forall_sub_mem_pow_iff_uniformizer`: Equal residue maps and a uniformizer congruence control
  every integral element.
* `integralEmbeddingOrder_eq_uniformizer`: The raw pair order is attained on every uniformizer when
  the residue maps agree.
* `addVal_spectralIntegerInclusion`: Normalized integral values restrict by the relative index.
* `embeddingRamificationIdx_comp`: The relative index multiplies under composition of embeddings.
* `embeddingRamificationIdx_eq`: The relative index is independent of the chosen source embedding.
* `embeddingRamificationOrder_aut`: The general embedding order retains the full automorphism order.

## References

* Serre, *Local Fields*, Chapter IV (ramification groups, Herbrand functions, the different).
* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §1.1.1.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal

section Integral

variable {S T : Type*} [CommRing S] [CommRing T] [IsDomain T]
    [IsDiscreteValuationRing T]

/-- The displacement infimum for two maps into a DVR. -/
def integralEmbeddingOrder (f g : S →+* T) : ℕ∞ :=
  ⨅ x : S, addVal T (f x - g x)

theorem integralEmbeddingOrder_le (f g : S →+* T) (x : S) :
    integralEmbeddingOrder f g ≤ addVal T (f x - g x) :=
  iInf_le _ x

@[simp]
theorem integralEmbeddingOrder_self (f : S →+* T) :
    integralEmbeddingOrder f f = ⊤ := by
  simp only [integralEmbeddingOrder, sub_self, addVal_zero, iInf_const]

theorem integralEmbeddingOrder_eq_top_iff (f g : S →+* T) :
    integralEmbeddingOrder f g = ⊤ ↔ f = g := by
  constructor
  · intro h
    ext x
    have hx : addVal T (f x - g x) = ⊤ :=
      top_unique (h ▸ integralEmbeddingOrder_le f g x)
    exact sub_eq_zero.mp (addVal_eq_top_iff.mp hx)
  · rintro rfl
    exact integralEmbeddingOrder_self f

theorem integralEmbeddingOrder_comm (f g : S →+* T) :
    integralEmbeddingOrder f g = integralEmbeddingOrder g f := by
  apply iInf_congr
  intro x
  rw [show f x - g x = -(g x - f x) by ring, (addVal T).map_neg]

variable {R : Type*} [CommRing R] [Algebra R S] [Algebra R T]

omit [IsDomain T] [IsDiscreteValuationRing T] in
/-- Congruence of two algebra maps is detected on any algebra generator. -/
theorem forall_sub_mem_iff_generator (f g : S →ₐ[R] T)
    {x : S} (hx : Algebra.adjoin R {x} = ⊤) (I : Ideal T) :
    (∀ a : S, f a - g a ∈ I) ↔ f x - g x ∈ I := by
  constructor
  · intro h
    exact h x
  · intro h a
    have ha : a ∈ Algebra.adjoin R {x} := hx ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem z hz => simpa only [Set.mem_singleton_iff.mp hz] using h
    | algebraMap r => simp only [f.commutes, g.commutes, sub_self, I.zero_mem]
    | add y z hy hz ihy ihz =>
      simpa only [map_add, add_sub_add_comm] using I.add_mem ihy ihz
    | mul y z hy hz ihy ihz =>
      simpa only [map_mul] using I.mul_sub_mul_mem ihy ihz

/-- An integral algebra generator attains the displacement infimum. -/
theorem integralEmbeddingOrder_eq_generator (f g : S →ₐ[R] T)
    {x : S} (hx : Algebra.adjoin R {x} = ⊤) :
    integralEmbeddingOrder f.toRingHom g.toRingHom = addVal T (f x - g x) := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  rw [integralEmbeddingOrder, le_iInf_iff]
  simp only [← mem_maximalIdeal_pow_iff_addVal]
  exact forall_sub_mem_iff_generator f g hx (IsLocalRing.maximalIdeal T ^ n)

end Integral

section PairUniformizer

variable {S T : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
variable (f g : S →+* T) [IsLocalHom g]
variable (p : ℕ) [Fact p.Prime] [CharP (ResidueField S) p]
    [PerfectField (ResidueField S)]

/-- Equal residue maps and a uniformizer congruence control every integral element. -/
theorem forall_sub_mem_pow_iff_uniformizer
    (hp : (p : T) ∈ IsLocalRing.maximalIdeal T)
    (hres : ∀ a : S, f a - g a ∈ IsLocalRing.maximalIdeal T)
    {π : S} (hπ : Irreducible π) (m : ℕ) :
    (∀ a : S, f a - g a ∈ IsLocalRing.maximalIdeal T ^ m) ↔
      f π - g π ∈ IsLocalRing.maximalIdeal T ^ m := by
  constructor
  · intro h
    exact h π
  · intro h a
    let I := IsLocalRing.maximalIdeal T
    let q := Ideal.Quotient.mk (I ^ m)
    have hπeq : q (f π) = q (g π) := Ideal.Quotient.eq.mpr h
    have hcoeff (b : S) : q (f b) ^ (p ^ m) = q (g b) ^ (p ^ m) := by
      have hb := (SModEq.sub_mem.mpr (hres b)).pow_pow_add_one hp m
      have hb' : f b ^ (p ^ m) - g b ^ (p ^ m) ∈ I ^ m :=
        Ideal.pow_le_pow_right (by omega) (SModEq.sub_mem.mp hb)
      simpa only [map_pow] using (Ideal.Quotient.eq.mpr hb' :
        q (f b ^ (p ^ m)) = q (g b ^ (p ^ m)))
    have hgπ : g π ∈ I := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hg
      exact hπ.not_isUnit ((inferInstance : IsLocalHom g).map_nonunit π hg)
    have hgπm : q (g π) ^ m = 0 := by
      rw [← map_pow]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow hgπ m)
    obtain ⟨b, c, ha⟩ := exists_pow_digits_uniformizer p hπ m m a
    apply Ideal.Quotient.eq.mp
    change q (f a) = q (g a)
    rw [ha]
    simp only [map_add, map_sum, map_mul, map_pow, hcoeff, hπeq, hgπm,
      zero_mul, add_zero]

/-- The raw pair order is attained on every uniformizer when the residue maps agree. -/
theorem integralEmbeddingOrder_eq_uniformizer
    (hp : (p : T) ∈ IsLocalRing.maximalIdeal T)
    (hres : ∀ a : S, f a - g a ∈ IsLocalRing.maximalIdeal T)
    {π : S} (hπ : Irreducible π) :
    integralEmbeddingOrder f g = addVal T (f π - g π) := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro m
  rw [integralEmbeddingOrder, le_iInf_iff]
  simp only [← mem_maximalIdeal_pow_iff_addVal]
  exact forall_sub_mem_pow_iff_uniformizer f g p hp hres hπ m

end PairUniformizer

section Spectral

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable {E N : Type*} [Field E] [Field N] [Algebra K E] [Algebra K N]
    [FiniteDimensional K E] [FiniteDimensional K N]
    [Algebra.IsSeparable K E] [Algebra.IsSeparable K N]

local notation "OE" => spectralIntegerRing K E
local notation "ON" => spectralIntegerRing K N

/-- The canonical local-length index of the integer map of an embedding. -/
def embeddingRamificationIdx (σ : E →ₐ[K] N) : ℕ :=
  letI : Algebra OE ON := (spectralIntegerInclusion K σ).toRingHom.toAlgebra
  (IsLocalRing.maximalIdeal ON).ramificationIdx OE

/-- The raw order is computed on the spectral integer rings. -/
def embeddingIntegralOrder (σ τ : E →ₐ[K] N) : ℕ∞ :=
  integralEmbeddingOrder (spectralIntegerInclusion K σ).toRingHom
    (spectralIntegerInclusion K τ).toRingHom

/-- The pair order normalized in the field, including infinity. -/
def embeddingRamificationOrder (σ τ : E →ₐ[K] N) : ℝ≥0∞ :=
  (embeddingIntegralOrder K σ τ : ℝ≥0∞) / embeddingRamificationIdx K σ

theorem embeddingRamificationIdx_pos (σ : E →ₐ[K] N) :
    0 < embeddingRamificationIdx K σ := by
  let : Algebra OE ON := (spectralIntegerInclusion K σ).toRingHom.toAlgebra
  let : FaithfulSMul OE ON := (faithfulSMul_iff_algebraMap_injective OE ON).mpr (by
    intro a b hab
    apply Subtype.ext
    exact σ.injective (congrArg (fun x : ON => (x : N)) hab))
  let : IsLocalHom (algebraMap OE ON) :=
    ⟨(spectralIntegerInclusion_isLocalHom K σ).map_nonunit⟩
  exact local_ramificationIdx_pos OE ON

/-- Normalized integral values restrict by the relative index. -/
theorem addVal_spectralIntegerInclusion (σ : E →ₐ[K] N) (x : OE) :
    addVal ON (spectralIntegerInclusion K σ x) =
      (embeddingRamificationIdx K σ : ℕ∞) * addVal OE x := by
  let : Algebra OE ON := (spectralIntegerInclusion K σ).toRingHom.toAlgebra
  let : FaithfulSMul OE ON := (faithfulSMul_iff_algebraMap_injective OE ON).mpr (by
    intro a b hab
    apply Subtype.ext
    exact σ.injective (congrArg (fun x : ON => (x : N)) hab))
  let : IsLocalHom (algebraMap OE ON) :=
    ⟨(spectralIntegerInclusion_isLocalHom K σ).map_nonunit⟩
  exact addVal_algebraMap OE ON x

omit [FiniteDimensional K E] in
theorem embeddingIntegralOrder_eq_top_iff (σ τ : E →ₐ[K] N) :
    embeddingIntegralOrder K σ τ = ⊤ ↔ σ = τ := by
  rw [embeddingIntegralOrder, integralEmbeddingOrder_eq_top_iff]
  constructor
  · intro h
    apply AlgHom.toRingHom_injective
    apply IsFractionRing.ringHom_ext (A := OE)
    intro x
    exact congrArg (fun y : ON => (y : N)) (RingHom.congr_fun h x)
  · rintro rfl
    rfl

omit [FiniteDimensional K E] in
@[simp]
theorem embeddingIntegralOrder_self (σ : E →ₐ[K] N) :
    embeddingIntegralOrder K σ σ = ⊤ :=
  (embeddingIntegralOrder_eq_top_iff K σ σ).mpr rfl

theorem embeddingRamificationOrder_eq_top_iff (σ τ : E →ₐ[K] N) :
    embeddingRamificationOrder K σ τ = ⊤ ↔ σ = τ := by
  have he : (embeddingRamificationIdx K σ : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (embeddingRamificationIdx_pos K σ).ne'
  rw [embeddingRamificationOrder, ENNReal.div_eq_top]
  constructor
  · rintro (h | h)
    · exact False.elim (he h.2)
    · exact (embeddingIntegralOrder_eq_top_iff K σ τ).mp
        (ENat.toENNReal_eq_top.mp h.1)
  · rintro rfl
    exact Or.inr ⟨by simp only [embeddingIntegralOrder_self, ENat.toENNReal_top],
      ENNReal.natCast_ne_top _⟩

@[simp]
theorem embeddingRamificationOrder_self (σ : E →ₐ[K] N) :
    embeddingRamificationOrder K σ σ = ⊤ :=
  (embeddingRamificationOrder_eq_top_iff K σ σ).mpr rfl

theorem embeddingRamificationOrder_lt_top {σ τ : E →ₐ[K] N} (h : σ ≠ τ) :
    embeddingRamificationOrder K σ τ < ⊤ :=
  lt_top_iff_ne_top.mpr (fun ht => h ((embeddingRamificationOrder_eq_top_iff K σ τ).mp ht))

variable {M : Type*} [Field M] [Algebra K M] [FiniteDimensional K M]
    [Algebra.IsSeparable K M]

omit [FiniteDimensional K E] in
/-- The relative index multiplies under composition of embeddings. -/
theorem embeddingRamificationIdx_comp (σ : E →ₐ[K] N) (u : N →ₐ[K] M) :
    embeddingRamificationIdx K (u.comp σ) =
      embeddingRamificationIdx K σ * embeddingRamificationIdx K u := by
  let : Algebra OE ON := (spectralIntegerInclusion K σ).toRingHom.toAlgebra
  let : Algebra ON (spectralIntegerRing K M) :=
    (spectralIntegerInclusion K u).toRingHom.toAlgebra
  let : Algebra OE (spectralIntegerRing K M) :=
    (spectralIntegerInclusion K (u.comp σ)).toRingHom.toAlgebra
  let : IsScalarTower OE ON (spectralIntegerRing K M) :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  let : FaithfulSMul ON (spectralIntegerRing K M) :=
    (faithfulSMul_iff_algebraMap_injective ON (spectralIntegerRing K M)).mpr (by
      intro a b hab
      apply Subtype.ext
      exact u.injective (congrArg (fun x : spectralIntegerRing K M => (x : M)) hab))
  let : IsLocalHom (algebraMap ON (spectralIntegerRing K M)) :=
    ⟨(spectralIntegerInclusion_isLocalHom K u).map_nonunit⟩
  exact local_ramificationIdx_tower OE ON (spectralIntegerRing K M)

/-- The relative index is independent of the chosen source embedding. -/
theorem embeddingRamificationIdx_eq (σ τ : E →ₐ[K] N) :
    embeddingRamificationIdx K σ = embeddingRamificationIdx K τ := by
  have ht (ι : E →ₐ[K] N) :
      (IsLocalRing.maximalIdeal ON).ramificationIdx 𝒪[K] =
        (IsLocalRing.maximalIdeal OE).ramificationIdx 𝒪[K] * embeddingRamificationIdx K ι := by
    let : Algebra OE ON := (spectralIntegerInclusion K ι).toRingHom.toAlgebra
    let : IsScalarTower 𝒪[K] OE ON :=
      IsScalarTower.of_algebraMap_eq (fun r => (spectralIntegerInclusion K ι).commutes r |>.symm)
    let : FaithfulSMul OE ON := (faithfulSMul_iff_algebraMap_injective OE ON).mpr (by
      intro a b hab
      apply Subtype.ext
      exact ι.injective (congrArg (fun x : ON => (x : N)) hab))
    let : IsLocalHom (algebraMap OE ON) :=
      ⟨(spectralIntegerInclusion_isLocalHom K ι).map_nonunit⟩
    exact local_ramificationIdx_tower 𝒪[K] OE ON
  exact Nat.eq_of_mul_eq_mul_left (local_ramificationIdx_pos 𝒪[K] OE)
    ((ht σ).symm.trans (ht τ))

omit [FiniteDimensional K E] in
theorem embeddingIntegralOrder_comm (σ τ : E →ₐ[K] N) :
    embeddingIntegralOrder K σ τ = embeddingIntegralOrder K τ σ :=
  integralEmbeddingOrder_comm _ _

theorem embeddingRamificationOrder_comm (σ τ : E →ₐ[K] N) :
    embeddingRamificationOrder K σ τ = embeddingRamificationOrder K τ σ := by
  rw [embeddingRamificationOrder, embeddingRamificationOrder,
    embeddingIntegralOrder_comm K σ τ, embeddingRamificationIdx_eq K σ τ]

theorem embeddingIntegralOrder_aut (s : E ≃ₐ[K] E) :
    embeddingIntegralOrder K s.toAlgHom (AlgHom.id K E) =
      ramificationOrder (R := OE) (E ≃ₐ[K] E) s := rfl

@[simp]
theorem embeddingRamificationIdx_aut (s : E ≃ₐ[K] E) :
    embeddingRamificationIdx K s.toAlgHom = 1 := by
  have hc := embeddingRamificationIdx_comp K (AlgHom.id K E) (AlgHom.id K E)
  have hp := embeddingRamificationIdx_pos K (AlgHom.id K E)
  have hi : embeddingRamificationIdx K (AlgHom.id K E) = 1 := by
    change embeddingRamificationIdx K (AlgHom.id K E) =
      embeddingRamificationIdx K (AlgHom.id K E) *
        embeddingRamificationIdx K (AlgHom.id K E) at hc
    nlinarith
  exact (embeddingRamificationIdx_eq K s.toAlgHom (AlgHom.id K E)).trans hi

/-- The general embedding order retains the full automorphism order. -/
theorem embeddingRamificationOrder_aut (s : E ≃ₐ[K] E) :
    embeddingRamificationOrder K s.toAlgHom (AlgHom.id K E) =
      (ramificationOrder (R := OE) (E ≃ₐ[K] E) s : ℝ≥0∞) := by
  rw [embeddingRamificationOrder, embeddingRamificationIdx_aut,
    Nat.cast_one, div_one, embeddingIntegralOrder_aut]

omit [FiniteDimensional K E] in
/-- Inertia for a pair means equality of its residue embeddings. -/
theorem one_le_embeddingIntegralOrder_iff (σ τ : E →ₐ[K] N) :
    1 ≤ embeddingIntegralOrder K σ τ ↔
      spectralResidueInclusion K σ = spectralResidueInclusion K τ := by
  constructor
  · intro h
    ext a
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective a
    have ha := h.trans (integralEmbeddingOrder_le
      (spectralIntegerInclusion K σ).toRingHom
      (spectralIntegerInclusion K τ).toRingHom a)
    change (1 : ℕ∞) ≤ addVal ON
      (spectralIntegerInclusion K σ a - spectralIntegerInclusion K τ a) at ha
    have hm : spectralIntegerInclusion K σ a - spectralIntegerInclusion K τ a ∈
        IsLocalRing.maximalIdeal ON := by
      have hm := (mem_maximalIdeal_pow_iff_addVal
        (spectralIntegerInclusion K σ a - spectralIntegerInclusion K τ a) 1).mpr ha
      simpa only [pow_one] using hm
    exact Ideal.Quotient.eq.mpr hm
  · intro h
    rw [embeddingIntegralOrder, integralEmbeddingOrder, le_iInf_iff]
    intro a
    have ha := congrArg (fun f => f (IsLocalRing.residue OE a)) h
    have hm : spectralIntegerInclusion K σ a - spectralIntegerInclusion K τ a ∈
        IsLocalRing.maximalIdeal ON := Ideal.Quotient.eq.mp ha
    change (1 : ℕ∞) ≤ addVal ON
      (spectralIntegerInclusion K σ a - spectralIntegerInclusion K τ a)
    exact (mem_maximalIdeal_pow_iff_addVal _ 1).mp (by simpa only [pow_one] using hm)

omit [FiniteDimensional K E] in
theorem embeddingIntegralOrder_eq_zero_of_residue_ne {σ τ : E →ₐ[K] N}
    (h : spectralResidueInclusion K σ ≠ spectralResidueInclusion K τ) :
    embeddingIntegralOrder K σ τ = 0 := by
  by_contra hz
  exact h ((one_le_embeddingIntegralOrder_iff K σ τ).mp
    (Order.one_le_iff_ne_zero.mpr hz))

omit [FiniteDimensional K E] in
theorem embeddingRamificationOrder_eq_zero_of_residue_ne {σ τ : E →ₐ[K] N}
    (h : spectralResidueInclusion K σ ≠ spectralResidueInclusion K τ) :
    embeddingRamificationOrder K σ τ = 0 := by
  rw [embeddingRamificationOrder, embeddingIntegralOrder_eq_zero_of_residue_ne K h,
    ENat.toENNReal_zero, ENNReal.zero_div]

omit [FiniteDimensional K E] in
theorem embeddingIntegralOrder_eq_generator (σ τ : E →ₐ[K] N)
    {x : OE} (hx : Algebra.adjoin 𝒪[K] {x} = ⊤) :
    embeddingIntegralOrder K σ τ =
      addVal ON (spectralIntegerInclusion K σ x - spectralIntegerInclusion K τ x) :=
  integralEmbeddingOrder_eq_generator _ _ hx

omit [FiniteDimensional K E] in
theorem embeddingRamificationOrder_eq_generator (σ τ : E →ₐ[K] N)
    {x : OE} (hx : Algebra.adjoin 𝒪[K] {x} = ⊤) :
    embeddingRamificationOrder K σ τ =
      (addVal ON (spectralIntegerInclusion K σ x - spectralIntegerInclusion K τ x) : ℝ≥0∞) /
        embeddingRamificationIdx K σ := by
  rw [embeddingRamificationOrder, embeddingIntegralOrder_eq_generator K σ τ hx]

/-- Integral generation supplies one element computing every embedding pair. -/
theorem exists_embeddingIntegralOrder_generator :
    ∃ x : OE, Algebra.adjoin 𝒪[K] {x} = ⊤ ∧ ∀ σ τ : E →ₐ[K] N,
      embeddingIntegralOrder K σ τ =
        addVal ON (spectralIntegerInclusion K σ x - spectralIntegerInclusion K τ x) := by
  obtain ⟨x, hx⟩ := spectralIntegerRing_exists_generator K E
  exact ⟨x, hx, fun σ τ => embeddingIntegralOrder_eq_generator K σ τ hx⟩

/-- The normalized finite-pair definition is the infimum of the normalized
integral displacements; attainment proves this also for identical embeddings. -/
theorem embeddingRamificationOrder_eq_iInf (σ τ : E →ₐ[K] N) :
    embeddingRamificationOrder K σ τ =
      ⨅ x : OE,
        (addVal ON (spectralIntegerInclusion K σ x - spectralIntegerInclusion K τ x) : ℝ≥0∞) /
          embeddingRamificationIdx K σ := by
  apply le_antisymm
  · apply le_iInf
    intro x
    exact ENNReal.div_le_div_right
      (ENat.toENNReal_mono (integralEmbeddingOrder_le
        (spectralIntegerInclusion K σ).toRingHom
        (spectralIntegerInclusion K τ).toRingHom x)) _
  · obtain ⟨x, hx⟩ := spectralIntegerRing_exists_generator K E
    rw [embeddingRamificationOrder_eq_generator K σ τ hx]
    exact iInf_le _ x

/-- Ambient enlargement scales the raw order by its relative index. -/
theorem embeddingIntegralOrder_comp (σ τ : E →ₐ[K] N) (u : N →ₐ[K] M) :
    embeddingIntegralOrder K (u.comp σ) (u.comp τ) =
      (embeddingRamificationIdx K u : ℕ∞) * embeddingIntegralOrder K σ τ := by
  obtain ⟨x, hx⟩ := spectralIntegerRing_exists_generator K E
  rw [embeddingIntegralOrder_eq_generator K _ _ hx,
    embeddingIntegralOrder_eq_generator K _ _ hx,
    ← addVal_spectralIntegerInclusion K u]
  congr 1
  apply Subtype.ext
  exact (map_sub u (σ (x : E)) (τ (x : E))).symm

/-- Normalization in the field removes all ambient scaling. -/
theorem embeddingRamificationOrder_comp (σ τ : E →ₐ[K] N) (u : N →ₐ[K] M) :
    embeddingRamificationOrder K (u.comp σ) (u.comp τ) =
      embeddingRamificationOrder K σ τ := by
  rw [embeddingRamificationOrder, embeddingIntegralOrder_comp,
    embeddingRamificationIdx_comp, ENat.toENNReal_mul, ENat.toENNReal_coe, Nat.cast_mul,
    mul_comm (embeddingRamificationIdx K σ : ℝ≥0∞)]
  have he : (embeddingRamificationIdx K u : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (embeddingRamificationIdx_pos K u).ne'
  exact ENNReal.mul_div_mul_left _ _ he (ENNReal.natCast_ne_top _)

/-- Residue agreement makes every uniformizer compute the pair order. -/
theorem embeddingIntegralOrder_eq_uniformizer (σ τ : E →ₐ[K] N)
    (hres : spectralResidueInclusion K σ = spectralResidueInclusion K τ)
    {π : OE} (hπ : Irreducible π) :
    embeddingIntegralOrder K σ τ =
      addVal ON (spectralIntegerInclusion K σ π - spectralIntegerInclusion K τ π) := by
  let : IsLocalHom (spectralIntegerInclusion K τ).toRingHom :=
    ⟨(spectralIntegerInclusion_isLocalHom K τ).map_nonunit⟩
  have hp : (p : ON) ∈ IsLocalRing.maximalIdeal ON := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change IsLocalRing.residue ON (p : ON) = 0
    rw [map_natCast, CharP.cast_eq_zero]
  apply integralEmbeddingOrder_eq_uniformizer _ _ p hp _ hπ
  intro a
  have ha := congrArg (fun f => f (IsLocalRing.residue OE a)) hres
  exact Ideal.Quotient.eq.mp ha

theorem embeddingRamificationOrder_eq_uniformizer (σ τ : E →ₐ[K] N)
    (hres : spectralResidueInclusion K σ = spectralResidueInclusion K τ)
    {π : OE} (hπ : Irreducible π) :
    embeddingRamificationOrder K σ τ =
      (addVal ON (spectralIntegerInclusion K σ π - spectralIntegerInclusion K τ π) : ℝ≥0∞) /
        embeddingRamificationIdx K σ := by
  rw [embeddingRamificationOrder, embeddingIntegralOrder_eq_uniformizer K σ τ hres hπ]

end Spectral

section PairField

variable (K : Type*) [Field K]
variable {E : Type*} [Field E] [Algebra K E]

/-- The finite compositum of the two images in the separable closure. -/
def embeddingPairField (σ τ : E →ₐ[K] SeparableClosure K) :
    IntermediateField K (SeparableClosure K) := σ.fieldRange ⊔ τ.fieldRange

instance embeddingPairField_finiteDimensional [FiniteDimensional K E]
    (σ τ : E →ₐ[K] SeparableClosure K) :
    FiniteDimensional K (embeddingPairField K σ τ) := by
  let : FiniteDimensional K σ.fieldRange := σ.toLinearMap.finiteDimensional_range
  let : FiniteDimensional K τ.fieldRange := τ.toLinearMap.finiteDimensional_range
  exact IntermediateField.finiteDimensional_sup _ _

/-- The first embedding factored through the compositum. -/
def embeddingPairLeft (σ τ : E →ₐ[K] SeparableClosure K) :
    E →ₐ[K] embeddingPairField K σ τ :=
  σ.codRestrict _ (fun x =>
    (le_sup_left : σ.fieldRange ≤ embeddingPairField K σ τ) ⟨x, rfl⟩)

/-- The second embedding factored through the compositum. -/
def embeddingPairRight (σ τ : E →ₐ[K] SeparableClosure K) :
    E →ₐ[K] embeddingPairField K σ τ :=
  τ.codRestrict _ (fun x =>
    (le_sup_right : τ.fieldRange ≤ embeddingPairField K σ τ) ⟨x, rfl⟩)

@[simp]
theorem coe_embeddingPairLeft (σ τ : E →ₐ[K] SeparableClosure K) (x : E) :
    (embeddingPairLeft K σ τ x : SeparableClosure K) = σ x := rfl

@[simp]
theorem coe_embeddingPairRight (σ τ : E →ₐ[K] SeparableClosure K) (x : E) :
    (embeddingPairRight K σ τ x : SeparableClosure K) = τ x := rfl

end PairField

section Closure

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable {E : Type*} [Field E] [Algebra K E] [FiniteDimensional K E]
    [Algebra.IsSeparable K E]

/-- Closure-pair order computed in its finite image compositum. -/
def closureEmbeddingOrder (σ τ : E →ₐ[K] SeparableClosure K) : ℝ≥0∞ :=
  embeddingRamificationOrder K (embeddingPairLeft K σ τ) (embeddingPairRight K σ τ)

theorem closureEmbeddingOrder_eq_top_iff (σ τ : E →ₐ[K] SeparableClosure K) :
    closureEmbeddingOrder K σ τ = ⊤ ↔ σ = τ := by
  rw [closureEmbeddingOrder, embeddingRamificationOrder_eq_top_iff]
  constructor
  · intro h
    apply AlgHom.ext
    intro x
    exact congrArg (fun y : embeddingPairField K σ τ => (y : SeparableClosure K))
      (AlgHom.congr_fun h x)
  · rintro rfl
    rfl

theorem closureEmbeddingOrder_lt_top {σ τ : E →ₐ[K] SeparableClosure K} (h : σ ≠ τ) :
    closureEmbeddingOrder K σ τ < ⊤ :=
  lt_top_iff_ne_top.mpr (fun ht => h ((closureEmbeddingOrder_eq_top_iff K σ τ).mp ht))

/-- The closure formulation uses the same integral elements and finite-ambient
normalized valuation, with no valuation or norm instance added on the closure. -/
theorem closureEmbeddingOrder_eq_iInf (σ τ : E →ₐ[K] SeparableClosure K) :
    closureEmbeddingOrder K σ τ =
      ⨅ x : spectralIntegerRing K E,
        (addVal (spectralIntegerRing K (embeddingPairField K σ τ))
          (spectralIntegerInclusion K (embeddingPairLeft K σ τ) x -
            spectralIntegerInclusion K (embeddingPairRight K σ τ) x) : ℝ≥0∞) /
          embeddingRamificationIdx K (embeddingPairLeft K σ τ) :=
  embeddingRamificationOrder_eq_iInf K _ _

/-- Any finite ambient subfield computes the same closure order. -/
theorem closureEmbeddingOrder_eq_finite (F : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K F] (σ τ : E →ₐ[K] F) :
    closureEmbeddingOrder K (F.val.comp σ) (F.val.comp τ) =
      embeddingRamificationOrder K σ τ := by
  have hF : embeddingPairField K (F.val.comp σ) (F.val.comp τ) ≤ F := by
    apply sup_le
    · rintro y ⟨x, rfl⟩
      exact (σ x).property
    · rintro y ⟨x, rfl⟩
      exact (τ x).property
  let u := IntermediateField.inclusion hF
  have hσ : u.comp (embeddingPairLeft K (F.val.comp σ) (F.val.comp τ)) = σ := by
    ext x
    rfl
  have hτ : u.comp (embeddingPairRight K (F.val.comp σ) (F.val.comp τ)) = τ := by
    ext x
    rfl
  have h := embeddingRamificationOrder_comp K
    (embeddingPairLeft K (F.val.comp σ) (F.val.comp τ))
    (embeddingPairRight K (F.val.comp σ) (F.val.comp τ)) u
  rw [hσ, hτ] at h
  exact h.symm

/-- The finite-ambient comparison applies to any finite field and embedding
into the closure, using its field range rather than a replacement model. -/
theorem closureEmbeddingOrder_comp {N : Type*} [Field N] [Algebra K N]
    [FiniteDimensional K N] [Algebra.IsSeparable K N]
    (σ τ : E →ₐ[K] N) (u : N →ₐ[K] SeparableClosure K) :
    closureEmbeddingOrder K (u.comp σ) (u.comp τ) =
      embeddingRamificationOrder K σ τ := by
  let : FiniteDimensional K u.fieldRange := u.toLinearMap.finiteDimensional_range
  have hσ : u.fieldRange.val.comp (u.equivFieldRange.toAlgHom.comp σ) = u.comp σ := by
    apply AlgHom.ext
    intro x
    rfl
  have hτ : u.fieldRange.val.comp (u.equivFieldRange.toAlgHom.comp τ) = u.comp τ := by
    apply AlgHom.ext
    intro x
    rfl
  have h := closureEmbeddingOrder_eq_finite K u.fieldRange
    (u.equivFieldRange.toAlgHom.comp σ) (u.equivFieldRange.toAlgHom.comp τ)
  rw [hσ, hτ] at h
  exact h.trans (embeddingRamificationOrder_comp K σ τ u.equivFieldRange.toAlgHom)

theorem closureEmbeddingOrder_comm (σ τ : E →ₐ[K] SeparableClosure K) :
    closureEmbeddingOrder K σ τ = closureEmbeddingOrder K τ σ := by
  have h := closureEmbeddingOrder_eq_finite K (embeddingPairField K σ τ)
    (embeddingPairRight K σ τ) (embeddingPairLeft K σ τ)
  change closureEmbeddingOrder K τ σ = _ at h
  exact (embeddingRamificationOrder_comm K _ _).trans h.symm

/-- The automorphism order agrees with its closure-valued embedding formulation. -/
theorem closureEmbeddingOrder_aut (s : E ≃ₐ[K] E)
    (u : E →ₐ[K] SeparableClosure K) :
    closureEmbeddingOrder K (u.comp s.toAlgHom) u =
      (ramificationOrder (R := spectralIntegerRing K E) (E ≃ₐ[K] E) s : ℝ≥0∞) := by
  have h := closureEmbeddingOrder_comp K s.toAlgHom (AlgHom.id K E) u
  rw [AlgHom.comp_id] at h
  exact h.trans (embeddingRamificationOrder_aut K s)

end Closure

section Signed

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable {E N : Type*} [Field E] [Field N] [Algebra K E] [Algebra K N]
    [FiniteDimensional K E] [FiniteDimensional K N]
    [Algebra.IsSeparable K E] [Algebra.IsSeparable K N]

/-- Wintenberger's signed ramification number: the normalized order minus one
(Wintenberger 1.1.1). Equal embeddings have number `⊤`; distinct residue maps give `-1`. -/
def embeddingRamificationNumber (σ τ : E →ₐ[K] N) : EReal :=
  (embeddingRamificationOrder K σ τ : EReal) - 1

omit [FiniteDimensional K E] in
theorem embeddingRamificationNumber_add_one (σ τ : E →ₐ[K] N) :
    embeddingRamificationNumber K σ τ + 1 =
      (embeddingRamificationOrder K σ τ : EReal) :=
  EReal.sub_add_cancel (b := (1 : ℝ))

omit [FiniteDimensional K E] in
theorem neg_one_le_embeddingRamificationNumber (σ τ : E →ₐ[K] N) :
    -1 ≤ embeddingRamificationNumber K σ τ := by
  simpa only [embeddingRamificationNumber, zero_sub] using
    EReal.sub_le_sub (EReal.coe_ennreal_nonneg (embeddingRamificationOrder K σ τ))
      (show (1 : EReal) ≤ 1 from le_rfl)

omit [FiniteDimensional K E] in
theorem embeddingRamificationNumber_ne_bot (σ τ : E →ₐ[K] N) :
    embeddingRamificationNumber K σ τ ≠ ⊥ :=
  ne_bot_of_le_ne_bot (EReal.coe_ne_bot (-1)) (neg_one_le_embeddingRamificationNumber K σ τ)

theorem embeddingRamificationNumber_eq_top_iff (σ τ : E →ₐ[K] N) :
    embeddingRamificationNumber K σ τ = ⊤ ↔ σ = τ := by
  rw [embeddingRamificationNumber, sub_eq_add_neg, ← EReal.coe_one, ← EReal.coe_neg,
    EReal.add_eq_top_iff_eq_top_left (EReal.coe_ne_bot (-1)) (EReal.coe_ne_top (-1)),
    EReal.coe_ennreal_eq_top_iff, embeddingRamificationOrder_eq_top_iff]

@[simp]
theorem embeddingRamificationNumber_self (σ : E →ₐ[K] N) :
    embeddingRamificationNumber K σ σ = ⊤ :=
  (embeddingRamificationNumber_eq_top_iff K σ σ).mpr rfl

theorem embeddingRamificationNumber_exists_real {σ τ : E →ₐ[K] N} (h : σ ≠ τ) :
    ∃ r : ℝ, embeddingRamificationNumber K σ τ = r := by
  have ht : embeddingRamificationNumber K σ τ ≠ ⊤ :=
    fun ht => h ((embeddingRamificationNumber_eq_top_iff K σ τ).mp ht)
  exact ⟨(embeddingRamificationNumber K σ τ).toReal,
    (EReal.coe_toReal ht (embeddingRamificationNumber_ne_bot K σ τ)).symm⟩

omit [FiniteDimensional K E] in
theorem embeddingRamificationNumber_eq_neg_one_of_residue_ne {σ τ : E →ₐ[K] N}
    (h : spectralResidueInclusion K σ ≠ spectralResidueInclusion K τ) :
    embeddingRamificationNumber K σ τ = -1 := by
  rw [embeddingRamificationNumber, embeddingRamificationOrder_eq_zero_of_residue_ne K h,
    EReal.coe_ennreal_zero, zero_sub]

theorem embeddingRamificationNumber_aut (s : E ≃ₐ[K] E) :
    embeddingRamificationNumber K s.toAlgHom (AlgHom.id K E) =
      ((ramificationOrder (R := spectralIntegerRing K E) (E ≃ₐ[K] E) s : ℝ≥0∞) : EReal) - 1 := by
  rw [embeddingRamificationNumber, embeddingRamificationOrder_aut]

/-- Signed closure order on the finite image compositum. -/
def closureEmbeddingNumber (σ τ : E →ₐ[K] SeparableClosure K) : EReal :=
  embeddingRamificationNumber K (embeddingPairLeft K σ τ) (embeddingPairRight K σ τ)

theorem closureEmbeddingNumber_eq (σ τ : E →ₐ[K] SeparableClosure K) :
    closureEmbeddingNumber K σ τ = (closureEmbeddingOrder K σ τ : EReal) - 1 := rfl

theorem closureEmbeddingNumber_add_one (σ τ : E →ₐ[K] SeparableClosure K) :
    closureEmbeddingNumber K σ τ + 1 = (closureEmbeddingOrder K σ τ : EReal) :=
  embeddingRamificationNumber_add_one K _ _

theorem neg_one_le_closureEmbeddingNumber (σ τ : E →ₐ[K] SeparableClosure K) :
    -1 ≤ closureEmbeddingNumber K σ τ :=
  neg_one_le_embeddingRamificationNumber K _ _

theorem closureEmbeddingNumber_ne_bot (σ τ : E →ₐ[K] SeparableClosure K) :
    closureEmbeddingNumber K σ τ ≠ ⊥ :=
  embeddingRamificationNumber_ne_bot K _ _

theorem closureEmbeddingNumber_eq_top_iff (σ τ : E →ₐ[K] SeparableClosure K) :
    closureEmbeddingNumber K σ τ = ⊤ ↔ σ = τ := by
  rw [closureEmbeddingNumber, embeddingRamificationNumber_eq_top_iff,
    ← embeddingRamificationOrder_eq_top_iff,
    ← closureEmbeddingOrder, closureEmbeddingOrder_eq_top_iff]

@[simp]
theorem closureEmbeddingNumber_self (σ : E →ₐ[K] SeparableClosure K) :
    closureEmbeddingNumber K σ σ = ⊤ :=
  (closureEmbeddingNumber_eq_top_iff K σ σ).mpr rfl

theorem closureEmbeddingNumber_exists_real {σ τ : E →ₐ[K] SeparableClosure K} (h : σ ≠ τ) :
    ∃ r : ℝ, closureEmbeddingNumber K σ τ = r := by
  have ht : closureEmbeddingNumber K σ τ ≠ ⊤ :=
    fun ht => h ((closureEmbeddingNumber_eq_top_iff K σ τ).mp ht)
  exact ⟨(closureEmbeddingNumber K σ τ).toReal,
    (EReal.coe_toReal ht (closureEmbeddingNumber_ne_bot K σ τ)).symm⟩

theorem embeddingRamificationNumber_comm (σ τ : E →ₐ[K] N) :
    embeddingRamificationNumber K σ τ = embeddingRamificationNumber K τ σ := by
  rw [embeddingRamificationNumber, embeddingRamificationNumber,
    embeddingRamificationOrder_comm K σ τ]

theorem embeddingRamificationNumber_comp {M : Type*} [Field M] [Algebra K M]
    [FiniteDimensional K M] [Algebra.IsSeparable K M]
    (σ τ : E →ₐ[K] N) (u : N →ₐ[K] M) :
    embeddingRamificationNumber K (u.comp σ) (u.comp τ) =
      embeddingRamificationNumber K σ τ := by
  rw [embeddingRamificationNumber, embeddingRamificationNumber,
    embeddingRamificationOrder_comp K σ τ u]

theorem closureEmbeddingNumber_comp (σ τ : E →ₐ[K] N)
    (u : N →ₐ[K] SeparableClosure K) :
    closureEmbeddingNumber K (u.comp σ) (u.comp τ) =
      embeddingRamificationNumber K σ τ := by
  rw [closureEmbeddingNumber_eq, closureEmbeddingOrder_comp K σ τ u,
    embeddingRamificationNumber]

theorem closureEmbeddingNumber_comm (σ τ : E →ₐ[K] SeparableClosure K) :
    closureEmbeddingNumber K σ τ = closureEmbeddingNumber K τ σ := by
  rw [closureEmbeddingNumber_eq, closureEmbeddingNumber_eq, closureEmbeddingOrder_comm K σ τ]

theorem closureEmbeddingNumber_aut (s : E ≃ₐ[K] E)
    (u : E →ₐ[K] SeparableClosure K) :
    closureEmbeddingNumber K (u.comp s.toAlgHom) u =
      ((ramificationOrder (R := spectralIntegerRing K E) (E ≃ₐ[K] E) s : ℝ≥0∞) : EReal) - 1 := by
  rw [closureEmbeddingNumber_eq, closureEmbeddingOrder_aut]

theorem embeddingRamificationNumber_nonneg (σ τ : E →ₐ[K] N)
    (hres : spectralResidueInclusion K σ = spectralResidueInclusion K τ) :
    0 ≤ embeddingRamificationNumber K σ τ := by
  obtain ⟨π, hπ⟩ := exists_irreducible (spectralIntegerRing K E)
  have hv := (addVal (spectralIntegerRing K N)).map_sub
    (spectralIntegerInclusion K σ π) (spectralIntegerInclusion K τ π)
  rw [addVal_spectralIntegerInclusion, addVal_spectralIntegerInclusion,
    addVal_uniformizer hπ, mul_one, mul_one, embeddingRamificationIdx_eq K τ σ,
    min_self, ← embeddingIntegralOrder_eq_uniformizer K σ τ hres hπ] at hv
  have he : (embeddingRamificationIdx K σ : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (embeddingRamificationIdx_pos K σ).ne'
  have hj : (1 : ℝ≥0∞) ≤ embeddingRamificationOrder K σ τ := by
    have h := ENNReal.div_le_div_right (ENat.toENNReal_mono hv)
      (embeddingRamificationIdx K σ : ℝ≥0∞)
    simpa only [embeddingRamificationOrder, ENat.toENNReal_coe,
      ENNReal.div_self he (ENNReal.natCast_ne_top _)] using h
  apply (EReal.sub_nonneg (Or.inr (EReal.coe_ne_top 1))
    (Or.inr (EReal.coe_ne_bot 1))).mpr
  exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr hj

theorem embeddingRamificationNumber_eq_uniformizer (σ τ : E →ₐ[K] N)
    (hres : spectralResidueInclusion K σ = spectralResidueInclusion K τ)
    {π : spectralIntegerRing K E} (hπ : Irreducible π) :
    embeddingRamificationNumber K σ τ =
      (((addVal (spectralIntegerRing K N)
        (spectralIntegerInclusion K σ π - spectralIntegerInclusion K τ π) : ℝ≥0∞) /
          embeddingRamificationIdx K σ : ℝ≥0∞) : EReal) - 1 := by
  rw [embeddingRamificationNumber, embeddingRamificationOrder_eq_uniformizer K σ τ hres hπ]

end Signed

end FontaineWintenberger
