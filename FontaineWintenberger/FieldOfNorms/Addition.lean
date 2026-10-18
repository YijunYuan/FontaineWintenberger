/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Valuation
public import FontaineWintenberger.FieldOfNorms.HerbrandControl
public import FontaineWintenberger.FieldOfNorms.Topology
public import FontaineWintenberger.APF.WildTail
public import FontaineWintenberger.APF.DeepTail
public import FontaineWintenberger.FieldOfNorms.FiniteLayerNormEstimates

/-!
# Addition on the original multiplicative field of norms

The actual norm-sum nets are indexed by all finite intermediate fields above
a fixed original field. Uniform Herbrand control transfers their deep-tail
norm defects to a Cauchy estimate in that original complete finite field.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

open Filter

section FiniteIntermediateFieldNets

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

instance FiniteIntermediateField.instNonempty : Nonempty (FiniteIntermediateField K L) :=
    ⟨FiniteIntermediateField.bottom⟩

instance FiniteIntermediateField.instIsDirectedOrder : IsDirectedOrder (FiniteIntermediateField K
    L) :=
  ⟨fun E F => ⟨FiniteIntermediateField.sup E F, FiniteIntermediateField.le_sup_left E F,
    FiniteIntermediateField.le_sup_right E F⟩⟩

instance FiniteIntermediateField.instIciIsDirectedOrder (E : FiniteIntermediateField K L) :
    IsDirectedOrder (Set.Ici E) :=
  ⟨fun F G => ⟨⟨FiniteIntermediateField.sup F.val G.val,
    F.property.trans (FiniteIntermediateField.le_sup_left F.val G.val)⟩,
    FiniteIntermediateField.le_sup_left F.val G.val, FiniteIntermediateField.le_sup_right F.val
        G.val⟩⟩

/-- The original norm-sum net over all actual finite fields containing E. -/
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

/-- Every further original finite-field tail is cofinal in the norm-sum index. -/
theorem FiniteIntermediateField.tendsto_Ici_inclusion (E F : FiniteIntermediateField K L) (hEF : E
    ≤ F) :
    Tendsto (fun G : Set.Ici F => (⟨G.val, hEF.trans G.property⟩ : Set.Ici E)) atTop atTop := by
  apply tendsto_atTop.mpr
  intro T
  refine eventually_atTop.mpr ⟨⟨FiniteIntermediateField.sup F T.val,
    FiniteIntermediateField.le_sup_left F T.val⟩, fun G hG => ?_⟩
  exact (FiniteIntermediateField.le_sup_right F T.val).trans hG

/-- Passing to any actual finite-field tail preserves the entire tail filter. -/
theorem FiniteIntermediateField.map_Ici_inclusion_atTop (E F : FiniteIntermediateField K L) (hEF :
    E ≤ F) :
    map (fun G : Set.Ici F => (⟨G.val, hEF.trans G.property⟩ : Set.Ici E)) atTop = atTop := by
  apply le_antisymm (FiniteIntermediateField.tendsto_Ici_inclusion K L E F hEF)
  intro s hs
  obtain ⟨a, ha⟩ := eventually_atTop.mp hs
  refine eventually_atTop.mpr ⟨⟨a.val, hEF.trans a.property⟩, fun b hb => ?_⟩
  exact ha ⟨b.val, a.property.trans (show a.val ≤ b.val from hb)⟩ hb

/-- Actual norm transitivity compares the same norm-sum net at two fixed bases. -/
theorem norm_normSumNet (E F : FiniteIntermediateField K L) (hEF : E ≤ F)
    (α β : FieldOfNorms K L) (G : Set.Ici F) :
    FiniteIntermediateField.norm E F hEF (normSumNet K L F α β G) =
      normSumNet K L E α β ⟨G.val, hEF.trans G.property⟩ := by
  exact FiniteIntermediateField.norm_norm E F G.val hEF G.property _

end FiniteIntermediateFieldNets

section NormSumLimits

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- A limit at a larger original finite base descends by its continuous norm,
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

/-- Uniqueness in the original Hausdorff finite fields makes the actual
norm-sum limits compatible under every original finite-layer norm. -/
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

/-- Convergence above one actual finite intermediate field gives convergence at every
original finite base by descent from its compositum with that layer. -/
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

/-- When the actual original norm-sum nets converge, their unique limits
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
integral on one actual finite tail, simultaneously for every family. -/
theorem IsAPF.exists_finiteIntermediateField_fieldOfNormsEval_mem_of_le_one [IsAPF K L] :
    ∃ T : FiniteIntermediateField K L, ∀ E : FiniteIntermediateField K L, T ≤ E → ∀ x :
        FieldOfNorms K L,
      FieldOfNorms.valuation K L x ≤ 1 →
        FieldOfNorms.coord K L E x ∈ spectralIntegerRing K E.val := by
  obtain ⟨T, hT⟩ := IsAPF.exists_fieldOfNormsValuation_eq_coordinate K L
  refine ⟨T, fun E hE x hx => ?_⟩
  rw [hT E hE x] at hx
  change FieldOfNorms.coord K L E x ∈
    ((IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K E.val)).valuation
      E.val).valuationSubring at hx
  rw [ValuationSubring.normalizedValuation_valuationSubring] at hx
  exact hx

/-- Every original coordinate is integral if the same stable field of norms
valuation is integral: actual integral norms descend from a common tail. -/
theorem FieldOfNorms.coord_mem_of_valuation_le_one [IsAPF K L] (x : FieldOfNorms K L)
    (hx : FieldOfNorms.valuation K L x ≤ 1) (E : FiniteIntermediateField K L) :
    FieldOfNorms.coord K L E x ∈ spectralIntegerRing K E.val := by
  obtain ⟨T, hT⟩ := IsAPF.exists_finiteIntermediateField_fieldOfNormsEval_mem_of_le_one K L
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
with integral coordinates in every original finite field. -/
theorem FieldOfNorms.valuation_le_one_iff [IsAPF K L] (x : FieldOfNorms K L) :
    FieldOfNorms.valuation K L x ≤ 1 ↔
      ∀ E : FiniteIntermediateField K L, FieldOfNorms.coord K L E x ∈ spectralIntegerRing K E.val
          := by
  constructor
  · exact fun hx E => FieldOfNorms.coord_mem_of_valuation_le_one K L x hx E
  · intro hx
    let T := (IsAPF.exists_fieldOfNormsCoordinateValuation_stable K L).choose
    change FieldOfNorms.coord K L T x ∈
      ((IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K T.val)).valuation
        T.val).valuationSubring
    rw [ValuationSubring.normalizedValuation_valuationSubring]
    exact hx T

/-- Every term of an integral-family norm-sum net is an integer of the
original fixed finite field. -/
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
the same original finite field and its actual closed integer ring. -/
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
    [IsDiscreteValuationRing (NormedField.valuation (K := E)).valuationSubring]
local notation "R" => Valuation.valuationSubring (NormedField.valuation (K := E))
variable {ι : Type*} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]

/-- Actual ideal-power control on pairs of an original net proves the
Cauchy condition for its original field uniformity. -/
theorem cauchy_map_of_eventually_sub_mem_maximalIdeal_pow (f : ι → E)
    (h : ∀ n : ℕ, ∃ a : ι, ∀ b, a ≤ b → ∀ c, a ≤ c →
      f b - f c ∈ (fun x : R => (x : E)) ''
        ((IsLocalRing.maximalIdeal R ^ n : Ideal R) : Set R)) :
    Cauchy (map f atTop) := by
  apply (IsUniformAddGroup.cauchy_map_iff_tendsto atTop f).mpr
  refine ⟨inferInstance, (nhds_zero_hasBasis_maximalIdeal_pow E).tendsto_right_iff.mpr ?_⟩
  intro n _
  obtain ⟨a, ha⟩ := h n
  filter_upwards [(eventually_ge_atTop a).prod_mk (eventually_ge_atTop a)] with x hx
  exact ha x.1 hx.1 x.2 hx.2

/-- Completeness gives an original-field limit from the actual ideal-power
Cauchy estimates. -/
theorem exists_tendsto_of_eventually_sub_mem_maximalIdeal_pow [CompleteSpace E]
    (f : ι → E)
    (h : ∀ n : ℕ, ∃ a : ι, ∀ b, a ≤ b → ∀ c, a ≤ c →
      f b - f c ∈ (fun x : R => (x : E)) ''
        ((IsLocalRing.maximalIdeal R ^ n : Ideal R) : Set R)) :
    ∃ z : E, Tendsto f atTop (nhds z) :=
  cauchy_map_iff_exists_tendsto.mp
    (cauchy_map_of_eventually_sub_mem_maximalIdeal_pow E f h)

end IdealPowerCauchy

end FontaineWintenberger
