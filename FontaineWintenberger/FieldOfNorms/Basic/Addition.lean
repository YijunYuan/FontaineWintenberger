/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Basic.Valuation
public import FontaineWintenberger.FieldOfNorms.Estimates.Herbrand
public import FontaineWintenberger.FieldOfNorms.Estimates.Topology
public import FontaineWintenberger.APF.Tower.Wild
public import FontaineWintenberger.APF.Tower.Stages
public import FontaineWintenberger.FieldOfNorms.Estimates.FiniteLayer

/-!
# Addition on the field of norms

## Addition on the multiplicative field of norms

The norm-sum nets are indexed by all finite intermediate fields above
a fixed field. Uniform Herbrand control transfers their deep-tail
norm defects to a Cauchy estimate in that complete finite field.

## Convergence of the norm-sum nets

Deep finite-layer estimates and the intrinsic Herbrand modulus prove
the Cauchy property in each complete finite field.

## The field of norms addition operation

Multiplicative scaling of the proved integral convergence constructs addition
on the multiplicative carrier.

## Asymptotic coordinate approximation of the field of norms addition

The existing normalized valuations control multiplicative scaling of integral
coordinate errors on the fields.

## Separation of the norm families by deep coordinate precision

Actual Herbrand continuity transports deep coordinate errors to a fixed finite
base before its Hausdorff separation is used.
-/

@[expose] public section

namespace FontaineWintenberger

noncomputable section

open Filter

section FiniteIntermediateFieldNets

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
/-- The norm-sum net over all finite fields containing E. -/
def normSumNet (E : FiniteIntermediateField K L) (α β : FieldOfNorms K L) (F : Set.Ici E) : E.val :=
  FiniteIntermediateField.norm E F.val F.property
    (FieldOfNorms.coord K L F.val α + FieldOfNorms.coord K L F.val β)

@[simp]
theorem normSumNet_zero_left (E : FiniteIntermediateField K L) (α : FieldOfNorms K L) (F : Set.Ici
    E) :
    normSumNet K L E 0 α F = FieldOfNorms.coord K L E α := by
  simp only [normSumNet, map_zero, zero_add]
  exact FieldOfNorms.coord_norm K L E F.val F.property α

@[simp]
theorem normSumNet_zero_right (E : FiniteIntermediateField K L) (α : FieldOfNorms K L) (F : Set.Ici
    E) :
    normSumNet K L E α 0 F = FieldOfNorms.coord K L E α := by
  simp only [normSumNet, map_zero, add_zero]
  exact FieldOfNorms.coord_norm K L E F.val F.property α
/-- Norm transitivity compares the same norm-sum net at two fixed bases. -/
theorem norm_normSumNet (E F : FiniteIntermediateField K L) (hEF : E ≤ F)
    (α β : FieldOfNorms K L) (G : Set.Ici F) :
    FiniteIntermediateField.norm E F hEF (normSumNet K L F α β G) =
      normSumNet K L E α β ⟨G.val, hEF.trans G.property⟩ := by
  exact FiniteIntermediateField.norm_norm E F G.val hEF G.property _

end FiniteIntermediateFieldNets

section NormSumLimits

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- A limit at a larger finite base descends by its continuous norm,
because the corresponding index is an entire tail of the smaller-base net. -/
theorem tendsto_normSumNet_of_upper (E F : FiniteIntermediateField K L) (hEF : E ≤ F)
    (α β : FieldOfNorms K L) (z : F.val) :
    let := spectralNorm.nontriviallyNormedField K E.val
    let := spectralNorm.nontriviallyNormedField K F.val
    Tendsto (normSumNet K L F α β) atTop (nhds z) →
      Tendsto (normSumNet K L E α β) atTop (nhds (FiniteIntermediateField.norm E F hEF z)) := by
  let := spectralNorm.nontriviallyNormedField K E.val
  let := spectralNorm.nontriviallyNormedField K F.val
  dsimp only
  intro hz
  have hc := ((FiniteIntermediateField.continuous_norm E F hEF).tendsto z).comp hz
  change map (normSumNet K L E α β) atTop ≤ _
  rw [← FiniteIntermediateField.map_Ici_inclusion_atTop K L E F hEF, map_map]
  simpa only [Tendsto, Function.comp_def, norm_normSumNet] using hc

/-- Uniqueness in the Hausdorff finite fields makes the
norm-sum limits compatible under every finite-layer norm. -/
theorem norm_of_normSumNet_tendsto (E F : FiniteIntermediateField K L) (hEF : E ≤ F)
    (α β : FieldOfNorms K L) (x : E.val) (y : F.val) :
    let := spectralNorm.nontriviallyNormedField K E.val
    let := spectralNorm.nontriviallyNormedField K F.val
    Tendsto (normSumNet K L E α β) atTop (nhds x) →
      Tendsto (normSumNet K L F α β) atTop (nhds y) →
        FiniteIntermediateField.norm E F hEF y = x := by
  let := spectralNorm.nontriviallyNormedField K E.val
  let := spectralNorm.nontriviallyNormedField K F.val
  dsimp only
  intro hx hy
  exact tendsto_nhds_unique (tendsto_normSumNet_of_upper K L E F hEF α β y hy) hx

/-- Convergence above one finite intermediate field gives convergence at every
finite base by descent from its compositum with that layer. -/
theorem exists_tendsto_normSumNet_of_upper_tail (T : FiniteIntermediateField K L)
    (α β : FieldOfNorms K L)
    (h : ∀ F : FiniteIntermediateField K L, T ≤ F → ∃ z : F.val,
      letI := spectralNorm.nontriviallyNormedField K F.val
      Tendsto (normSumNet K L F α β) atTop (nhds z)) :
    ∀ E : FiniteIntermediateField K L, ∃ z : E.val,
      letI := spectralNorm.nontriviallyNormedField K E.val
      Tendsto (normSumNet K L E α β) atTop (nhds z) := by
  intro E
  let F := FiniteIntermediateField.sup E T
  have hEF : E ≤ F := FiniteIntermediateField.le_sup_left E T
  obtain ⟨z, hz⟩ := h F (FiniteIntermediateField.le_sup_right E T)
  exact ⟨FiniteIntermediateField.norm E F hEF z,
    tendsto_normSumNet_of_upper K L E F hEF α β z hz⟩

/-- When the norm-sum nets converge, their unique limits
are represented by the same zero-adjoined unit field of norms. -/
theorem existsUnique_fieldOfNorms_of_normSumNet_tendsto (α β : FieldOfNorms K L)
    (h : ∀ E : FiniteIntermediateField K L, ∃ z : E.val,
      letI := spectralNorm.nontriviallyNormedField K E.val
      Tendsto (normSumNet K L E α β) atTop (nhds z)) :
    ∃! γ : FieldOfNorms K L, ∀ E : FiniteIntermediateField K L,
      letI := spectralNorm.nontriviallyNormedField K E.val
      Tendsto (normSumNet K L E α β) atTop (nhds (FieldOfNorms.coord K L E γ)) := by
  choose z hz using h
  have hnorm (E F : FiniteIntermediateField K L) (hEF : E ≤ F) :
      FiniteIntermediateField.norm E F hEF (z F) = z E :=
    norm_of_normSumNet_tendsto K L E F hEF α β (z E) (z F) (hz E) (hz F)
  obtain ⟨γ, hγ, huniq⟩ := existsUnique_fieldOfNorms_of_compatible K L z hnorm
  refine ⟨γ, fun E => ?_, fun δ hδ => ?_⟩
  · rw [hγ E]
    exact hz E
  · apply huniq δ
    intro E
    let := spectralNorm.nontriviallyNormedField K E.val
    exact tendsto_nhds_unique (hδ E) (hz E)

end NormSumLimits

section IntegralFamilies

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- The proved stable coordinate valuation makes integral norm families
integral on one finite tail, simultaneously for every family. -/
theorem IsAPF.exists_finiteIntermediateField_coord_mem_of_le_one [IsAPF K L] :
    ∃ T : FiniteIntermediateField K L, ∀ E : FiniteIntermediateField K L, T ≤ E → ∀ x :
        FieldOfNorms K L,
      FieldOfNorms.valuation K L x ≤ 1 →
        FieldOfNorms.coord K L E x ∈ spectralIntegerRing K E.val := by
  obtain ⟨T, hT⟩ := FieldOfNorms.exists_valuation_eq_coordinateValuation K L
  refine ⟨T, fun E hE x hx => ?_⟩
  rw [hT E hE x] at hx
  change FieldOfNorms.coord K L E x ∈
    ((IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K E.val)).valuation
      E.val).valuationSubring at hx
  rw [ValuationSubring.normalizedValuation_valuationSubring] at hx
  exact hx

/-- Every coordinate is integral if the same stable field of norms
valuation is integral: integral norms descend from a common tail. -/
theorem FieldOfNorms.coord_mem_of_valuation_le_one [IsAPF K L] (x : FieldOfNorms K L)
    (hx : FieldOfNorms.valuation K L x ≤ 1) (E : FiniteIntermediateField K L) :
    FieldOfNorms.coord K L E x ∈ spectralIntegerRing K E.val := by
  obtain ⟨T, hT⟩ := IsAPF.exists_finiteIntermediateField_coord_mem_of_le_one K L
  let F := FiniteIntermediateField.sup E T
  have hEF : E ≤ F := FiniteIntermediateField.le_sup_left E T
  let xF : spectralIntegerRing K F.val :=
    ⟨FieldOfNorms.coord K L F x, hT F (FiniteIntermediateField.le_sup_right E T) x hx⟩
  have h := (FiniteIntermediateField.integerNorm E F hEF xF).property
  rw [FiniteIntermediateField.coe_integerNorm] at h
  change FiniteIntermediateField.norm E F hEF (FieldOfNorms.coord K L F x) ∈
    spectralIntegerRing K E.val at h
  rw [FieldOfNorms.coord_norm] at h
  exact h

/-- The integral part of the stable valuation is exactly the families
with integral coordinates in every finite field. -/
theorem FieldOfNorms.valuation_le_one_iff [IsAPF K L] (x : FieldOfNorms K L) :
    FieldOfNorms.valuation K L x ≤ 1 ↔
      ∀ E : FiniteIntermediateField K L, FieldOfNorms.coord K L E x ∈ spectralIntegerRing K E.val
          := by
  constructor
  · exact fun hx E => FieldOfNorms.coord_mem_of_valuation_le_one K L x hx E
  · intro hx
    let T := (FieldOfNorms.exists_coordinateValuation_stable K L).choose
    change FieldOfNorms.coord K L T x ∈
      ((IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K T.val)).valuation
        T.val).valuationSubring
    rw [ValuationSubring.normalizedValuation_valuationSubring]
    exact hx T

/-- Every term of an integral-family norm-sum net is an integer of the
fixed finite field. -/
theorem normSumNet_mem_of_valuation_le_one [IsAPF K L] (α β : FieldOfNorms K L)
    (hα : FieldOfNorms.valuation K L α ≤ 1) (hβ : FieldOfNorms.valuation K L β ≤ 1)
    (E : FiniteIntermediateField K L) (F : Set.Ici E) :
    normSumNet K L E α β F ∈ spectralIntegerRing K E.val := by
  let x : spectralIntegerRing K F.val.val :=
    ⟨FieldOfNorms.coord K L F.val α, FieldOfNorms.coord_mem_of_valuation_le_one K L α hα F.val⟩
  let y : spectralIntegerRing K F.val.val :=
    ⟨FieldOfNorms.coord K L F.val β, FieldOfNorms.coord_mem_of_valuation_le_one K L β hβ F.val⟩
  have h := (FiniteIntermediateField.integerNorm E F.val F.property (x + y)).property
  rw [FiniteIntermediateField.coe_integerNorm E F.val F.property (x + y)] at h
  exact h

/-- A convergent integral-family norm-sum net has an integral limit, in
the finite field and its closed integer ring. -/
theorem normSumNet_limit_mem_of_valuation_le_one [IsAPF K L] (α β : FieldOfNorms K L)
    (hα : FieldOfNorms.valuation K L α ≤ 1) (hβ : FieldOfNorms.valuation K L β ≤ 1)
    (E : FiniteIntermediateField K L) (z : E.val) :
    letI := spectralNorm.nontriviallyNormedField K E.val
    Tendsto (normSumNet K L E α β) atTop (nhds z) →
      z ∈ spectralIntegerRing K E.val := by
  let := spectralNorm.nontriviallyNormedField K E.val
  intro hz
  have hz' := (FiniteIntermediateField.isClosed_image_maximalIdeal_pow E 0).mem_of_tendsto hz
    (Eventually.of_forall fun F => ⟨⟨normSumNet K L E α β F,
      normSumNet_mem_of_valuation_le_one K L α β hα hβ E F⟩, by simp, rfl⟩)
  obtain ⟨w, _, hw⟩ := hz'
  exact hw ▸ w.property

end IntegralFamilies

section IdealPowerCauchy

variable (E : Type*) [NontriviallyNormedField E] [IsUltrametricDist E]
    [IsDiscreteValuationRing 𝒪[E]]
variable {ι : Type*} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]

/-- Ideal-power control on pairs of a net proves the
Cauchy condition for its field uniformity. -/
theorem cauchy_map_of_eventually_sub_mem_maximalIdeal_pow (f : ι → E)
    (h : ∀ n : ℕ, ∃ a : ι, ∀ b, a ≤ b → ∀ c, a ≤ c →
      f b - f c ∈ (fun x : 𝒪[E] => (x : E)) ''
        ((IsLocalRing.maximalIdeal 𝒪[E] ^ n : Ideal 𝒪[E]) : Set 𝒪[E])) :
    Cauchy (map f atTop) := by
  apply (IsUniformAddGroup.cauchy_map_iff_tendsto atTop f).mpr
  refine ⟨inferInstance, (nhds_zero_hasBasis_maximalIdeal_pow E).tendsto_right_iff.mpr ?_⟩
  intro n _
  obtain ⟨a, ha⟩ := h n
  filter_upwards [(eventually_ge_atTop a).prod_mk (eventually_ge_atTop a)] with x hx
  exact ha x.1 hx.1 x.2 hx.2

/-- Completeness gives an original-field limit from the ideal-power
Cauchy estimates. -/
theorem exists_tendsto_of_eventually_sub_mem_maximalIdeal_pow [CompleteSpace E]
    (f : ι → E)
    (h : ∀ n : ℕ, ∃ a : ι, ∀ b, a ≤ b → ∀ c, a ≤ c →
      f b - f c ∈ (fun x : 𝒪[E] => (x : E)) ''
        ((IsLocalRing.maximalIdeal 𝒪[E] ^ n : Ideal 𝒪[E]) : Set 𝒪[E])) :
    ∃ z : E, Tendsto f atTop (nhds z) :=
  cauchy_map_iff_exists_tendsto.mp
    (cauchy_map_of_eventually_sub_mem_maximalIdeal_pow E f h)

end IdealPowerCauchy

end

end FontaineWintenberger

noncomputable section

namespace FontaineWintenberger

open Filter

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- Every requested integral precision is attained by the additive
norm defect on an entire finite-layer tail. -/
theorem IsAPF.exists_finiteIntermediateField_integerNorm_add_congruence
    [IsAPF K L] (s : ℕ) :
    ∃ T : FiniteIntermediateField K L, ∀ E F : FiniteIntermediateField K L, T ≤ E → ∀ hEF : E ≤ F,
      ∀ x y : spectralIntegerRing K F.val,
        FiniteIntermediateField.integerNorm E F hEF (x + y) - FiniteIntermediateField.integerNorm E
            F hEF x -
          FiniteIntermediateField.integerNorm E F hEF y ∈
            IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ s := by
  let c : ℝ := (p : ℝ) / ((p - 1 : ℕ) : ℝ) * s
  obtain ⟨T₀, hT₀⟩ := IsAPF.exists_finiteIntermediateField_wild_tail K L
  obtain ⟨T₁, hT₁⟩ := IsAPF.exists_finiteIntermediateField_relativeFirstBound_ge K L c
  refine ⟨FiniteIntermediateField.sup T₀ T₁, fun E F hE hEF x y => ?_⟩
  let : Algebra E.val F.val := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
  let : IsScalarTower K E.val F.val := IsScalarTower.of_algebraMap_eq' rfl
  let := spectralValuation_hasExtension_tower K (E := E.val) (L := F.val)
  let := spectralNorm.nontriviallyNormedField K E.val
  let := spectralNorm.normedAlgebra K E.val
  let := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := E.val))
  let := spectralNorm.completeSpace K E.val
  let := normedAlgebra_isCompleteDiscreteValuedField K E.val
  obtain ⟨_, ⟨n, hd⟩, he⟩ := hT₀ E F ((FiniteIntermediateField.le_sup_left T₀ T₁).trans hE) hEF
  have hb := hT₁ E F ((FiniteIntermediateField.le_sup_right T₀ T₁).trans hE) hEF
  have h := FiniteIntermediateField.integerNorm_add_congruence_of_le_apfRamificationBound
    E F hEF he n hd c hb x y
  have hp : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero
  have hp₁ : ((p - 1 : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by have := (Fact.out : Nat.Prime p).two_le; omega)
  have hc : ((p - 1 : ℕ) : ℝ) / p * c = (s : ℝ) := by
    dsimp only [c]
    field_simp
  simpa only [hc, Nat.ceil_natCast] using h

/-- The norm-sum term differs from the two integral
coordinates by any requested precision on one entire finite-layer tail. -/
theorem IsAPF.exists_finiteIntermediateField_normSumNet_sub_mem [IsAPF K L] (s : ℕ) :
    ∃ T : FiniteIntermediateField K L, ∀ E : FiniteIntermediateField K L, T ≤ E →
      ∀ α β : FieldOfNorms K L,
      FieldOfNorms.valuation K L α ≤ 1 → FieldOfNorms.valuation K L β ≤ 1 →
      ∀ F : Set.Ici E,
        normSumNet K L E α β F - FieldOfNorms.coord K L E α - FieldOfNorms.coord K L E β ∈
          (fun x : spectralIntegerRing K E.val => (x : E.val)) ''
            ((IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ s :
              Ideal (spectralIntegerRing K E.val)) : Set (spectralIntegerRing K E.val)) := by
  obtain ⟨T, hT⟩ := IsAPF.exists_finiteIntermediateField_integerNorm_add_congruence K L s
  refine ⟨T, fun E hE α β hα hβ F => ?_⟩
  let x : spectralIntegerRing K F.val.val :=
    ⟨FieldOfNorms.coord K L F.val α, FieldOfNorms.coord_mem_of_valuation_le_one K L α hα F.val⟩
  let y : spectralIntegerRing K F.val.val :=
    ⟨FieldOfNorms.coord K L F.val β, FieldOfNorms.coord_mem_of_valuation_le_one K L β hβ F.val⟩
  refine ⟨FiniteIntermediateField.integerNorm E F.val F.property (x + y) -
    FiniteIntermediateField.integerNorm E F.val F.property x -
    FiniteIntermediateField.integerNorm E F.val F.property y, hT E F.val hE F.property x y, ?_⟩
  change (FiniteIntermediateField.integerNorm E F.val F.property (x + y) : E.val) -
      (FiniteIntermediateField.integerNorm E F.val F.property x : E.val) -
      (FiniteIntermediateField.integerNorm E F.val F.property y : E.val) = _
  rw [FiniteIntermediateField.coe_integerNorm E F.val F.property (x + y),
    FiniteIntermediateField.coe_integerNorm E F.val F.property x,
    FiniteIntermediateField.coe_integerNorm E F.val F.property y]
  change normSumNet K L E α β F -
    FiniteIntermediateField.norm E F.val F.property (FieldOfNorms.coord K L F.val α) -
    FiniteIntermediateField.norm E F.val F.property (FieldOfNorms.coord K L F.val β) = _
  rw [FieldOfNorms.coord_norm K L E F.val F.property α,
    FieldOfNorms.coord_norm K L E F.val F.property β]

/-- On a wild tail, every integral-family norm-sum net is Cauchy
in its fixed finite field. All finite precision estimates are proved. -/
theorem IsAPF.exists_finiteIntermediateField_normSumNet_cauchy [IsAPF K L] :
    ∃ T : FiniteIntermediateField K L, ∀ E : FiniteIntermediateField K L, T ≤ E →
      ∀ α β : FieldOfNorms K L,
      FieldOfNorms.valuation K L α ≤ 1 → FieldOfNorms.valuation K L β ≤ 1 →
      letI := spectralNorm.nontriviallyNormedField K E.val
      Cauchy (map (normSumNet K L E α β) atTop) := by
  obtain ⟨T, hT⟩ := IsAPF.exists_finiteIntermediateField_wild_tail K L
  refine ⟨T, fun E hE α β hα hβ => ?_⟩
  let := spectralNorm.nontriviallyNormedField K E.val
  let := spectralNorm.normedAlgebra K E.val
  let := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := E.val))
  let := spectralNorm.completeSpace K E.val
  let := normedAlgebra_isCompleteDiscreteValuedField K E.val
  let := Algebra.isSeparable_tower_top_of_isSeparable K E.val L
  let a (F : FiniteIntermediateField K L) : spectralIntegerRing K F.val :=
    ⟨FieldOfNorms.coord K L F α, FieldOfNorms.coord_mem_of_valuation_le_one K L α hα F⟩
  let b (F : FiniteIntermediateField K L) : spectralIntegerRing K F.val :=
    ⟨FieldOfNorms.coord K L F β, FieldOfNorms.coord_mem_of_valuation_le_one K L β hβ F⟩
  have ha (F G : FiniteIntermediateField K L) (hFG : F ≤ G) :
      FiniteIntermediateField.integerNorm F G hFG (a G) = a F := by
    apply Subtype.ext
    rw [FiniteIntermediateField.coe_integerNorm]
    exact FieldOfNorms.coord_norm K L F G hFG α
  have hb (F G : FiniteIntermediateField K L) (hFG : F ≤ G) :
      FiniteIntermediateField.integerNorm F G hFG (b G) = b F := by
    apply Subtype.ext
    rw [FiniteIntermediateField.coe_integerNorm]
    exact FieldOfNorms.coord_norm K L F G hFG β
  apply cauchy_map_of_eventually_sub_mem_maximalIdeal_pow E.val
  intro N
  let s := ⌈apfPsi E.val L (N : ℝ)⌉₊
  have hs : apfPsi E.val L (N : ℝ) ≤ (s : ℝ) := Nat.le_ceil _
  obtain ⟨U, hU⟩ := IsAPF.exists_finiteIntermediateField_integerNorm_add_congruence K L s
  let A : Set.Ici E := ⟨FiniteIntermediateField.sup E U, FiniteIntermediateField.le_sup_left E U⟩
  have hstep (B C : FiniteIntermediateField K L) (hEB : E ≤ B) (hBC : B ≤ C) (hUB : U ≤ B) :
      normSumNet K L E α β ⟨C, hEB.trans hBC⟩ -
        normSumNet K L E α β ⟨B, hEB⟩ ∈
      (fun x : spectralIntegerRing K E.val => (x : E.val)) ''
        ((IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ N :
          Ideal (spectralIntegerRing K E.val)) : Set (spectralIntegerRing K E.val)) := by
    let : Algebra E.val B.val := (IntermediateField.inclusion hEB).toRingHom.toAlgebra
    let : IsScalarTower K E.val B.val := IsScalarTower.of_algebraMap_eq' rfl
    let := spectralValuation_hasExtension_tower K (E := E.val) (L := B.val)
    let x := FiniteIntermediateField.integerNorm B C hBC (a C + b C)
    let y := a B + b B
    have hxy : x - y ∈ IsLocalRing.maximalIdeal (spectralIntegerRing K B.val) ^ s := by
      have h := hU B C hUB hBC (a C) (b C)
      rw [ha B C hBC, hb B C hBC] at h
      simpa only [x, y, sub_sub] using h
    obtain ⟨_, ⟨n, hd⟩, he⟩ := hT E B hE hEB
    have h := FiniteIntermediateField.integerNorm_sub_congruence_of_totallyRamified
      E B hEB he n hd s x y hxy
    have hprecision := FiniteIntermediateField.le_ceil_apfPhi_of_apfPsi_le K L E B hEB N s hs
    have hmem := Ideal.pow_le_pow_right hprecision h
    refine ⟨FiniteIntermediateField.integerNorm E B hEB x - FiniteIntermediateField.integerNorm E B
        hEB y,
      hmem, ?_⟩
    change (FiniteIntermediateField.integerNorm E B hEB x : E.val) -
      (FiniteIntermediateField.integerNorm E B hEB y : E.val) = _
    rw [FiniteIntermediateField.coe_integerNorm E B hEB x, FiniteIntermediateField.coe_integerNorm
        E B hEB y]
    dsimp only [x, y]
    rw [FiniteIntermediateField.coe_integerNorm B C hBC (a C + b C)]
    change FiniteIntermediateField.norm E B hEB
        (FiniteIntermediateField.norm B C hBC (FieldOfNorms.coord K L C α + FieldOfNorms.coord K L
            C β)) -
      FiniteIntermediateField.norm E B hEB (FieldOfNorms.coord K L B α + FieldOfNorms.coord K L B
          β) = _
    rw [FiniteIntermediateField.norm_norm]
    rfl
  refine ⟨A, fun B hB C hC => ?_⟩
  let D := FiniteIntermediateField.sup B.val C.val
  have hUB : U ≤ B.val := (FiniteIntermediateField.le_sup_right E U).trans hB
  have hUC : U ≤ C.val := (FiniteIntermediateField.le_sup_right E U).trans hC
  obtain ⟨zB, hzB, heqB⟩ := hstep B.val D B.property (FiniteIntermediateField.le_sup_left _ _) hUB
  obtain ⟨zC, hzC, heqC⟩ := hstep C.val D C.property (FiniteIntermediateField.le_sup_right _ _) hUC
  refine ⟨zC - zB, Ideal.sub_mem _ hzC hzB, ?_⟩
  change (zC : E.val) - (zB : E.val) = _
  linear_combination heqC - heqB

/-- Integral-family norm-sum nets converge at every finite
base, including bases below or incomparable with the wild tail. -/
theorem exists_tendsto_normSumNet_of_valuation_le_one [IsAPF K L]
    (α β : FieldOfNorms K L) (hα : FieldOfNorms.valuation K L α ≤ 1)
    (hβ : FieldOfNorms.valuation K L β ≤ 1) :
    ∀ E : FiniteIntermediateField K L, ∃ z : E.val,
      letI := spectralNorm.nontriviallyNormedField K E.val
      Tendsto (normSumNet K L E α β) atTop (nhds z) := by
  obtain ⟨T, hT⟩ := IsAPF.exists_finiteIntermediateField_normSumNet_cauchy K L
  apply exists_tendsto_normSumNet_of_upper_tail K L T α β
  intro E hE
  let := spectralNorm.nontriviallyNormedField K E.val
  let := spectralNorm.completeSpace K E.val
  exact cauchy_map_iff_exists_tendsto.mp (hT E hE α β hα hβ)

/-- The field of norms contains the unique integral sum family.
Its finite-coordinate approximation is proved by closed ideal powers. -/
theorem existsUnique_fieldOfNorms_integral_add [IsAPF K L]
    (α β : FieldOfNorms K L) (hα : FieldOfNorms.valuation K L α ≤ 1)
    (hβ : FieldOfNorms.valuation K L β ≤ 1) :
    ∃! γ : FieldOfNorms K L, FieldOfNorms.valuation K L γ ≤ 1 ∧
      (∀ E : FiniteIntermediateField K L,
        letI := spectralNorm.nontriviallyNormedField K E.val
        Tendsto (normSumNet K L E α β) atTop (nhds (FieldOfNorms.coord K L E γ))) ∧
      ∀ s : ℕ, ∃ T : FiniteIntermediateField K L, ∀ E : FiniteIntermediateField K L, T ≤ E →
        FieldOfNorms.coord K L E γ - FieldOfNorms.coord K L E α - FieldOfNorms.coord K L E β ∈
          (fun x : spectralIntegerRing K E.val => (x : E.val)) ''
            ((IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ s :
              Ideal (spectralIntegerRing K E.val)) : Set (spectralIntegerRing K E.val)) := by
  obtain ⟨γ, hγ, huniq⟩ := existsUnique_fieldOfNorms_of_normSumNet_tendsto K L α β
    (exists_tendsto_normSumNet_of_valuation_le_one K L α β hα hβ)
  refine ⟨γ, ⟨?_, hγ, ?_⟩, fun δ hδ => huniq δ hδ.2.1⟩
  · rw [FieldOfNorms.valuation_le_one_iff K L γ]
    intro E
    exact normSumNet_limit_mem_of_valuation_le_one K L α β hα hβ E _ (hγ E)
  · intro s
    obtain ⟨T, hT⟩ := IsAPF.exists_finiteIntermediateField_normSumNet_sub_mem K L s
    refine ⟨T, fun E hE => ?_⟩
    let := spectralNorm.nontriviallyNormedField K E.val
    exact (FiniteIntermediateField.isClosed_image_maximalIdeal_pow E s).mem_of_tendsto
      (((hγ E).sub_const (FieldOfNorms.coord K L E α)).sub_const (FieldOfNorms.coord K L E β))
      (Eventually.of_forall (hT E hE α β hα hβ))

end FontaineWintenberger

noncomputable section

namespace FontaineWintenberger

open Filter

section ScalarCovariance

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- Multiplicative scaling is an exact identity on the norm-sum
nets, before any limits or additive structure are chosen on the carrier. -/
theorem normSumNet_mul_left (E : FiniteIntermediateField K L) (δ α β : FieldOfNorms K L)
    (F : Set.Ici E) :
    normSumNet K L E (δ * α) (δ * β) F =
      FieldOfNorms.coord K L E δ * normSumNet K L E α β F := by
  simp only [normSumNet, map_mul]
  rw [← mul_add, map_mul, FieldOfNorms.coord_norm K L E F.val F.property δ]

end ScalarCovariance

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- Every pair of norm-compatible families has convergent
norm-sum nets; existing nonzero families themselves provide the scaling. -/
theorem exists_tendsto_normSumNet [IsAPF K L] (α β : FieldOfNorms K L) :
    ∀ E : FiniteIntermediateField K L, ∃ z : E.val,
      letI := spectralNorm.nontriviallyNormedField K E.val
      Tendsto (normSumNet K L E α β) atTop (nhds z) := by
  by_cases hα : α = 0
  · intro E
    let := spectralNorm.nontriviallyNormedField K E.val
    refine ⟨FieldOfNorms.coord K L E β, ?_⟩
    have heq : normSumNet K L E α β = fun _ => FieldOfNorms.coord K L E β := by
      funext F
      simp only [hα, normSumNet_zero_left]
    rw [heq]
    exact tendsto_const_nhds
  by_cases hβ : β = 0
  · intro E
    let := spectralNorm.nontriviallyNormedField K E.val
    refine ⟨FieldOfNorms.coord K L E α, ?_⟩
    have heq : normSumNet K L E α β = fun _ => FieldOfNorms.coord K L E α := by
      funext F
      simp only [hβ, normSumNet_zero_right]
    rw [heq]
    exact tendsto_const_nhds
  let w := FieldOfNorms.valuation K L
  have hαw : w α ≠ 0 := fun h => hα ((FieldOfNorms.valuation_eq_zero_iff K L α).mp h)
  have hβw : w β ≠ 0 := fun h => hβ ((FieldOfNorms.valuation_eq_zero_iff K L β).mp h)
  have hscale : ∃ δ : FieldOfNorms K L, δ ≠ 0 ∧ w (α / δ) ≤ 1 ∧ w (β / δ) ≤ 1 := by
    rcases le_total (w α) (w β) with h | h
    · refine ⟨β, hβ, ?_, ?_⟩
      · rw [map_div₀]
        exact (div_le_one₀ (pos_iff_ne_zero.mpr hβw)).mpr h
      · simp only [div_self hβ, map_one, le_refl]
    · refine ⟨α, hα, ?_, ?_⟩
      · simp only [div_self hα, map_one, le_refl]
      · rw [map_div₀]
        exact (div_le_one₀ (pos_iff_ne_zero.mpr hαw)).mpr h
  obtain ⟨δ, hδ, ha, hb⟩ := hscale
  have hδα : δ * (α / δ) = α := by
    simp [div_eq_mul_inv, mul_left_comm, hδ]
  have hδβ : δ * (β / δ) = β := by
    simp [div_eq_mul_inv, mul_left_comm, hδ]
  intro E
  let := spectralNorm.nontriviallyNormedField K E.val
  obtain ⟨z, hz⟩ := exists_tendsto_normSumNet_of_valuation_le_one
    K L (α / δ) (β / δ) ha hb E
  refine ⟨FieldOfNorms.coord K L E δ * z, ?_⟩
  simpa only [← normSumNet_mul_left, hδα, hδβ] using
    hz.const_mul (FieldOfNorms.coord K L E δ)

/-- The field of norms contains the unique sum family of any
pair of its elements, characterized by the norm-sum limits. -/
theorem existsUnique_fieldOfNorms_add [IsAPF K L] (α β : FieldOfNorms K L) :
    ∃! γ : FieldOfNorms K L, ∀ E : FiniteIntermediateField K L,
      letI := spectralNorm.nontriviallyNormedField K E.val
      Tendsto (normSumNet K L E α β) atTop (nhds (FieldOfNorms.coord K L E γ)) :=
  existsUnique_fieldOfNorms_of_normSumNet_tendsto K L α β
    (exists_tendsto_normSumNet K L α β)

/-- Addition on the multiplicative field of norms carrier,
characterized by the norm-sum limits at every finite base. -/
def FieldOfNorms.add [IsAPF K L] (α β : FieldOfNorms K L) : FieldOfNorms K L :=
  (existsUnique_fieldOfNorms_add K L α β).choose

/-- Every coordinate of the sum is its norm-sum limit. -/
theorem FieldOfNorms.tendsto_normSumNet_add [IsAPF K L] (α β : FieldOfNorms K L)
    (E : FiniteIntermediateField K L) :
    letI := spectralNorm.nontriviallyNormedField K E.val
    Tendsto (normSumNet K L E α β) atTop
      (nhds (FieldOfNorms.coord K L E (FieldOfNorms.add K L α β))) :=
  (existsUnique_fieldOfNorms_add K L α β).choose_spec.1 E

/-- The norm-sum limits uniquely characterize the same sum operation. -/
theorem FieldOfNorms.eq_add_of_tendsto [IsAPF K L] (α β γ : FieldOfNorms K L)
    (hγ : ∀ E : FiniteIntermediateField K L,
      letI := spectralNorm.nontriviallyNormedField K E.val
      Tendsto (normSumNet K L E α β) atTop (nhds (FieldOfNorms.coord K L E γ))) :
    γ = FieldOfNorms.add K L α β :=
  (existsUnique_fieldOfNorms_add K L α β).choose_spec.2 γ hγ

/-- Commutativity follows from the exact finite-field sums in the defining nets. -/
theorem FieldOfNorms.add_comm [IsAPF K L] (α β : FieldOfNorms K L) :
    FieldOfNorms.add K L α β = FieldOfNorms.add K L β α := by
  symm
  apply FieldOfNorms.eq_add_of_tendsto K L α β
  intro E
  let := spectralNorm.nontriviallyNormedField K E.val
  have heq : normSumNet K L E α β = normSumNet K L E β α := by
    funext F
    simp only [normSumNet, _root_.add_comm]
  rw [heq]
  exact FieldOfNorms.tendsto_normSumNet_add K L β α E

/-- The zero is the left identity for the field of norms addition. -/
theorem FieldOfNorms.add_zero_left [IsAPF K L] (α : FieldOfNorms K L) :
    FieldOfNorms.add K L 0 α = α := by
  symm
  apply FieldOfNorms.eq_add_of_tendsto K L 0 α α
  intro E
  let := spectralNorm.nontriviallyNormedField K E.val
  have heq : normSumNet K L E 0 α = fun _ => FieldOfNorms.coord K L E α :=
    funext (normSumNet_zero_left K L E α)
  rw [heq]
  exact tendsto_const_nhds

/-- The zero is the right identity for the field of norms addition. -/
theorem FieldOfNorms.add_zero_right [IsAPF K L] (α : FieldOfNorms K L) :
    FieldOfNorms.add K L α 0 = α := by
  rw [FieldOfNorms.add_comm, FieldOfNorms.add_zero_left]

/-- Exact norm multiplicativity gives distributivity of the
multiplication over the field of norms addition. -/
theorem FieldOfNorms.left_distrib [IsAPF K L] (δ α β : FieldOfNorms K L) :
    δ * FieldOfNorms.add K L α β =
      FieldOfNorms.add K L (δ * α) (δ * β) := by
  apply FieldOfNorms.eq_add_of_tendsto K L (δ * α) (δ * β)
  intro E
  let := spectralNorm.nontriviallyNormedField K E.val
  rw [map_mul]
  simpa only [← normSumNet_mul_left] using
    (FieldOfNorms.tendsto_normSumNet_add K L α β E).const_mul (FieldOfNorms.coord K L E δ)

/-- Integral inputs have an integral sum, on the same stable valuation. -/
theorem FieldOfNorms.valuation_add_le_one [IsAPF K L] (α β : FieldOfNorms K L)
    (hα : FieldOfNorms.valuation K L α ≤ 1) (hβ : FieldOfNorms.valuation K L β ≤ 1) :
    FieldOfNorms.valuation K L (FieldOfNorms.add K L α β) ≤ 1 := by
  rw [FieldOfNorms.valuation_le_one_iff K L]
  intro E
  exact normSumNet_limit_mem_of_valuation_le_one K L α β hα hβ E _
    (FieldOfNorms.tendsto_normSumNet_add K L α β E)

/-- The sum of integral inputs has the proved eventual coordinate
approximation at every finite precision. -/
theorem FieldOfNorms.add_sub_mem_of_valuation_le_one [IsAPF K L] (α β : FieldOfNorms K L)
    (hα : FieldOfNorms.valuation K L α ≤ 1) (hβ : FieldOfNorms.valuation K L β ≤ 1) :
    ∀ s : ℕ, ∃ T : FiniteIntermediateField K L, ∀ E : FiniteIntermediateField K L, T ≤ E →
      FieldOfNorms.coord K L E (FieldOfNorms.add K L α β) -
        FieldOfNorms.coord K L E α - FieldOfNorms.coord K L E β ∈
        (fun x : spectralIntegerRing K E.val => (x : E.val)) ''
          ((IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ s :
            Ideal (spectralIntegerRing K E.val)) : Set (spectralIntegerRing K E.val)) := by
  obtain ⟨γ, hγ, _⟩ := existsUnique_fieldOfNorms_integral_add K L α β hα hβ
  have heq := FieldOfNorms.eq_add_of_tendsto K L α β γ hγ.2.1
  simpa only [heq] using hγ.2.2

end FontaineWintenberger

noncomputable section

namespace ValuationSubring

variable {E : Type*} [Field E] (A : ValuationSubring E) [IsDiscreteValuationRing A]

/-- An ambient-field ideal-power bound is exactly the bound for the existing
canonical normalized valuation, including its integrality consequence. -/
theorem mem_image_maximalIdeal_pow_iff_normalizedValuation (x : E) (n : ℕ) :
    x ∈ (fun a : A => (a : E)) ''
        ((IsLocalRing.maximalIdeal A ^ n : Ideal A) : Set A) ↔
      (IsDiscreteValuationRing.maximalIdeal A).valuation E x ≤ WithZero.exp (-(n : ℤ)) := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (mem_maximalIdeal_pow_iff_normalizedValuation A a n).mp ha
  · intro hx
    have hbound : WithZero.exp (-(n : ℤ)) ≤ (1 : WithZero (Multiplicative ℤ)) := by
      rw [← WithZero.exp_zero]
      exact WithZero.exp_le_exp.mpr (by omega)
    have hmem : x ∈ A := by
      rw [← normalizedValuation_valuationSubring A]
      exact hx.trans hbound
    exact ⟨⟨x, hmem⟩,
      (mem_maximalIdeal_pow_iff_normalizedValuation A ⟨x, hmem⟩ n).mpr hx, rfl⟩

end ValuationSubring

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- The sum of arbitrary norm families agrees with coordinate
addition to every eventual ideal-power precision. -/
theorem FieldOfNorms.add_sub_mem [IsAPF K L] (α β : FieldOfNorms K L) :
    ∀ n : ℕ, ∃ T : FiniteIntermediateField K L, ∀ E : FiniteIntermediateField K L, T ≤ E →
      FieldOfNorms.coord K L E (FieldOfNorms.add K L α β) -
        FieldOfNorms.coord K L E α - FieldOfNorms.coord K L E β ∈
        (fun x : spectralIntegerRing K E.val => (x : E.val)) ''
          ((IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ n :
            Ideal (spectralIntegerRing K E.val)) : Set (spectralIntegerRing K E.val)) := by
  classical
  let w := FieldOfNorms.valuation K L
  let S : Finset (FieldOfNorms K L) := {1, α, β}
  obtain ⟨δ, _, hmax⟩ := Finset.exists_max_image S w ⟨1, by simp [S]⟩
  have hone : 1 ≤ w δ := by simpa only [_root_.map_one] using hmax 1 (by simp [S])
  have hδpos : 0 < w δ := zero_lt_one.trans_le hone
  have hδ : δ ≠ 0 := by
    intro hz
    rw [hz, _root_.map_zero] at hone
    exact not_le_of_gt zero_lt_one hone
  have ha : w (α / δ) ≤ 1 := by
    rw [map_div₀]
    exact (div_le_one₀ hδpos).mpr (hmax α (by simp [S]))
  have hb : w (β / δ) ≤ 1 := by
    rw [map_div₀]
    exact (div_le_one₀ hδpos).mpr (hmax β (by simp [S]))
  have hδα : δ * (α / δ) = α := by
    simp [div_eq_mul_inv, mul_left_comm, hδ]
  have hδβ : δ * (β / δ) = β := by
    simp [div_eq_mul_inv, mul_left_comm, hδ]
  let q := (WithZero.log (w δ)).toNat
  have hδbound : w δ ≤ WithZero.exp (q : ℤ) :=
    WithZero.le_exp_log.trans (WithZero.exp_le_exp.mpr (Int.self_le_toNat _))
  obtain ⟨T₀, hT₀⟩ := FieldOfNorms.exists_valuation_eq_coordinateValuation K L
  intro n
  obtain ⟨T₁, hT₁⟩ := FieldOfNorms.add_sub_mem_of_valuation_le_one
    K L (α / δ) (β / δ) ha hb (n + q)
  refine ⟨FiniteIntermediateField.sup T₀ T₁, fun E hE => ?_⟩
  have hE₀ := (FiniteIntermediateField.le_sup_left T₀ T₁).trans hE
  have hE₁ := (FiniteIntermediateField.le_sup_right T₀ T₁).trans hE
  let v := (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K E.val)).valuation E.val
  have hvδ : v (FieldOfNorms.coord K L E δ) ≤ WithZero.exp (q : ℤ) := by
    change FieldOfNorms.coordinateValuation K L E δ ≤ _
    rw [← hT₀ E hE₀ δ]
    exact hδbound
  have hvε : v (FieldOfNorms.coord K L E (FieldOfNorms.add K L (α / δ) (β / δ)) -
      FieldOfNorms.coord K L E (α / δ) - FieldOfNorms.coord K L E (β / δ)) ≤
        WithZero.exp (-((n + q : ℕ) : ℤ)) :=
    (ValuationSubring.mem_image_maximalIdeal_pow_iff_normalizedValuation
      (spectralIntegerRing K E.val) _ (n + q)).mp (hT₁ E hE₁)
  apply (ValuationSubring.mem_image_maximalIdeal_pow_iff_normalizedValuation
    (spectralIntegerRing K E.val) _ n).mpr
  have hs := congrArg (FieldOfNorms.coord K L E)
    (FieldOfNorms.left_distrib K L δ (α / δ) (β / δ))
  rw [_root_.map_mul, hδα, hδβ] at hs
  have hαE : FieldOfNorms.coord K L E δ * FieldOfNorms.coord K L E (α / δ) =
      FieldOfNorms.coord K L E α := by rw [← _root_.map_mul, hδα]
  have hβE : FieldOfNorms.coord K L E δ * FieldOfNorms.coord K L E (β / δ) =
      FieldOfNorms.coord K L E β := by rw [← _root_.map_mul, hδβ]
  have heq : FieldOfNorms.coord K L E (FieldOfNorms.add K L α β) -
      FieldOfNorms.coord K L E α - FieldOfNorms.coord K L E β =
      FieldOfNorms.coord K L E δ *
        (FieldOfNorms.coord K L E (FieldOfNorms.add K L (α / δ) (β / δ)) -
          FieldOfNorms.coord K L E (α / δ) - FieldOfNorms.coord K L E (β / δ)) := by
    rw [← hs, ← hαE, ← hβE]
    ring
  change v _ ≤ _
  rw [heq, _root_.map_mul]
  calc
    _ ≤ WithZero.exp (q : ℤ) * WithZero.exp (-((n + q : ℕ) : ℤ)) :=
      mul_le_mul' hvδ hvε
    _ = WithZero.exp (-(n : ℤ)) := by
      rw [← WithZero.exp_add]
      congr 1
      omega

end FontaineWintenberger

noncomputable section

namespace FontaineWintenberger

open Filter

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- Deep ideal-power agreement of integral families gives equality by
transporting every precision to one fixed finite base. -/
theorem FieldOfNorms.ext_of_integral_eventually_sub_mem [IsAPF K L]
    (α β : FieldOfNorms K L) (hα : FieldOfNorms.valuation K L α ≤ 1)
    (hβ : FieldOfNorms.valuation K L β ≤ 1)
    (h : ∀ n : ℕ, ∃ T : FiniteIntermediateField K L, ∀ F : FiniteIntermediateField K L, T ≤ F →
      FieldOfNorms.coord K L F α - FieldOfNorms.coord K L F β ∈
        (fun x : spectralIntegerRing K F.val => (x : F.val)) ''
          ((IsLocalRing.maximalIdeal (spectralIntegerRing K F.val) ^ n :
            Ideal (spectralIntegerRing K F.val)) : Set (spectralIntegerRing K F.val))) :
    α = β := by
  obtain ⟨T, hT⟩ := IsAPF.exists_finiteIntermediateField_wild_tail K L
  apply FieldOfNorms.ext K L
  intro D
  let B := FiniteIntermediateField.sup D T
  have hTB : T ≤ B := FiniteIntermediateField.le_sup_right D T
  have hDB : D ≤ B := FiniteIntermediateField.le_sup_left D T
  let := spectralNorm.nontriviallyNormedField K B.val
  let := spectralNorm.normedAlgebra K B.val
  let := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := B.val))
  let := spectralNorm.completeSpace K B.val
  let := normedAlgebra_isCompleteDiscreteValuedField K B.val
  let := Algebra.isSeparable_tower_top_of_isSeparable K B.val L
  have hmem (N : ℕ) :
      FieldOfNorms.coord K L B α - FieldOfNorms.coord K L B β ∈
        (fun x : spectralIntegerRing K B.val => (x : B.val)) ''
          ((IsLocalRing.maximalIdeal (spectralIntegerRing K B.val) ^ N :
            Ideal (spectralIntegerRing K B.val)) : Set (spectralIntegerRing K B.val)) := by
    let s := ⌈apfPsi B.val L (N : ℝ)⌉₊
    have hs : apfPsi B.val L (N : ℝ) ≤ (s : ℝ) := Nat.le_ceil _
    obtain ⟨U, hU⟩ := h s
    let F := FiniteIntermediateField.sup B U
    have hBF : B ≤ F := FiniteIntermediateField.le_sup_left B U
    let : Algebra B.val F.val := (IntermediateField.inclusion hBF).toRingHom.toAlgebra
    let : IsScalarTower K B.val F.val := IsScalarTower.of_algebraMap_eq' rfl
    let := spectralValuation_hasExtension_tower K (E := B.val) (L := F.val)
    let x : spectralIntegerRing K F.val :=
      ⟨FieldOfNorms.coord K L F α, FieldOfNorms.coord_mem_of_valuation_le_one K L α hα F⟩
    let y : spectralIntegerRing K F.val :=
      ⟨FieldOfNorms.coord K L F β, FieldOfNorms.coord_mem_of_valuation_le_one K L β hβ F⟩
    obtain ⟨d, hd, heq⟩ := hU F (FiniteIntermediateField.le_sup_right B U)
    have hxy : x - y ∈ IsLocalRing.maximalIdeal (spectralIntegerRing K F.val) ^ s := by
      have heq' : x - y = d := Subtype.ext heq.symm
      rw [heq']
      exact hd
    obtain ⟨_, ⟨n, hn⟩, he⟩ := hT B F hTB hBF
    have hc := FiniteIntermediateField.integerNorm_sub_congruence_of_totallyRamified
      B F hBF he n hn s x y hxy
    have hprecision := FiniteIntermediateField.le_ceil_apfPhi_of_apfPsi_le K L B F hBF N s hs
    refine ⟨FiniteIntermediateField.integerNorm B F hBF x - FiniteIntermediateField.integerNorm B F
        hBF y,
      Ideal.pow_le_pow_right hprecision hc, ?_⟩
    change (FiniteIntermediateField.integerNorm B F hBF x : B.val) -
      (FiniteIntermediateField.integerNorm B F hBF y : B.val) = _
    rw [FiniteIntermediateField.coe_integerNorm B F hBF x, FiniteIntermediateField.coe_integerNorm
        B F hBF y]
    exact congrArg₂ (fun a b : B.val => a - b)
      (FieldOfNorms.coord_norm K L B F hBF α) (FieldOfNorms.coord_norm K L B F hBF β)
  have hz : FieldOfNorms.coord K L B α - FieldOfNorms.coord K L B β = 0 := by
    have ht : Tendsto (fun _ : ℕ => FieldOfNorms.coord K L B α - FieldOfNorms.coord K L B β)
        atTop (nhds 0) :=
      (FiniteIntermediateField.nhds_zero_hasBasis_maximalIdeal_pow B).tendsto_right_iff.mpr
        (fun N _ => Eventually.of_forall fun _ => hmem N)
    exact tendsto_nhds_unique tendsto_const_nhds ht
  have hB := sub_eq_zero.mp hz
  have hnorm := congrArg (FiniteIntermediateField.norm D B hDB) hB
  simpa only [FieldOfNorms.coord_norm] using hnorm

/-- Asymptotic ideal-power agreement separates arbitrary norm
families. An existing maximal-valued family makes all normalization integral. -/
theorem FieldOfNorms.ext_of_eventually_sub_mem [IsAPF K L]
    (α β : FieldOfNorms K L)
    (h : ∀ n : ℕ, ∃ T : FiniteIntermediateField K L, ∀ F : FiniteIntermediateField K L, T ≤ F →
      FieldOfNorms.coord K L F α - FieldOfNorms.coord K L F β ∈
        (fun x : spectralIntegerRing K F.val => (x : F.val)) ''
          ((IsLocalRing.maximalIdeal (spectralIntegerRing K F.val) ^ n :
            Ideal (spectralIntegerRing K F.val)) : Set (spectralIntegerRing K F.val))) :
    α = β := by
  classical
  let w := FieldOfNorms.valuation K L
  let S : Finset (FieldOfNorms K L) := {1, α, β}
  obtain ⟨δ, _, hmax⟩ := Finset.exists_max_image S w ⟨1, by simp [S]⟩
  have hone : 1 ≤ w δ := by simpa only [_root_.map_one] using hmax 1 (by simp [S])
  have hδpos : 0 < w δ := zero_lt_one.trans_le hone
  have hδ : δ ≠ 0 := by
    intro hδ
    rw [hδ, _root_.map_zero] at hone
    exact not_le_of_gt zero_lt_one hone
  have ha : w (α / δ) ≤ 1 := by
    rw [map_div₀]
    exact (div_le_one₀ hδpos).mpr (hmax α (by simp [S]))
  have hb : w (β / δ) ≤ 1 := by
    rw [map_div₀]
    exact (div_le_one₀ hδpos).mpr (hmax β (by simp [S]))
  have hi : w δ⁻¹ ≤ 1 := by
    rw [map_inv₀]
    exact inv_le_one_of_one_le₀ hone
  have heq := FieldOfNorms.ext_of_integral_eventually_sub_mem K L
    (α / δ) (β / δ) ha hb (fun n => ?_)
  · simpa [div_eq_mul_inv, mul_assoc, hδ] using
      congrArg (fun x : FieldOfNorms K L => x * δ) heq
  · obtain ⟨T, hT⟩ := h n
    refine ⟨T, fun F hF => ?_⟩
    obtain ⟨d, hd, hdeq⟩ := hT F hF
    let z : spectralIntegerRing K F.val :=
      ⟨FieldOfNorms.coord K L F δ⁻¹, FieldOfNorms.coord_mem_of_valuation_le_one K L δ⁻¹ hi F⟩
    refine ⟨z * d, Ideal.mul_mem_left _ z hd, ?_⟩
    change FieldOfNorms.coord K L F δ⁻¹ * (d : F.val) = _
    change (d : F.val) = FieldOfNorms.coord K L F α - FieldOfNorms.coord K L F β at hdeq
    rw [hdeq, map_inv₀, map_div₀, map_div₀]
    simp only [div_eq_mul_inv]
    ring

end FontaineWintenberger
