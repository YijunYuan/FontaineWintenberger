/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.FieldOfNorms.Valuation
public import FontaineWintenberger.FieldOfNorms.HerbrandControl
public import FontaineWintenberger.FieldOfNorms.Topology
public import FontaineWintenberger.APF.WildTail
public import FontaineWintenberger.APF.DeepTail
public import FontaineWintenberger.FieldOfNorms.FiniteLayerNormEstimates

/-!
# Addition on the original multiplicative norm limit

The actual norm-sum nets are indexed by all finite intermediate fields above
a fixed original field. Uniform Herbrand control transfers their deep-tail
norm defects to a Cauchy estimate in that original complete finite field.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

open Filter

section FiniteLayerNets

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

instance FiniteLayer.instNonempty : Nonempty (FiniteLayer K L) := ⟨FiniteLayer.bottom⟩

instance FiniteLayer.instIsDirectedOrder : IsDirectedOrder (FiniteLayer K L) :=
  ⟨fun E F => ⟨FiniteLayer.sup E F, FiniteLayer.le_sup_left E F,
    FiniteLayer.le_sup_right E F⟩⟩

instance FiniteLayer.instIciIsDirectedOrder (E : FiniteLayer K L) :
    IsDirectedOrder (Set.Ici E) :=
  ⟨fun F G => ⟨⟨FiniteLayer.sup F.val G.val,
    F.property.trans (FiniteLayer.le_sup_left F.val G.val)⟩,
    FiniteLayer.le_sup_left F.val G.val, FiniteLayer.le_sup_right F.val G.val⟩⟩

/-- The original norm-sum net over all actual finite fields containing E. -/
def normSumNet (E : FiniteLayer K L) (α β : NormLimit K L) (F : Set.Ici E) : E.val :=
  FiniteLayer.norm E F.val F.property
    (normLimitEval K L F.val α + normLimitEval K L F.val β)

@[simp]
theorem normSumNet_zero_left (E : FiniteLayer K L) (α : NormLimit K L) (F : Set.Ici E) :
    normSumNet K L E 0 α F = normLimitEval K L E α := by
  simp only [normSumNet, map_zero, zero_add]
  exact normLimitEval_norm K L E F.val F.property α

@[simp]
theorem normSumNet_zero_right (E : FiniteLayer K L) (α : NormLimit K L) (F : Set.Ici E) :
    normSumNet K L E α 0 F = normLimitEval K L E α := by
  simp only [normSumNet, map_zero, add_zero]
  exact normLimitEval_norm K L E F.val F.property α

/-- Every further original finite-field tail is cofinal in the norm-sum index. -/
theorem FiniteLayer.tendsto_Ici_inclusion (E F : FiniteLayer K L) (hEF : E ≤ F) :
    Tendsto (fun G : Set.Ici F => (⟨G.val, hEF.trans G.property⟩ : Set.Ici E)) atTop atTop := by
  apply tendsto_atTop.mpr
  intro T
  refine eventually_atTop.mpr ⟨⟨FiniteLayer.sup F T.val,
    FiniteLayer.le_sup_left F T.val⟩, fun G hG => ?_⟩
  exact (FiniteLayer.le_sup_right F T.val).trans hG

/-- Passing to any actual finite-field tail preserves the entire tail filter. -/
theorem FiniteLayer.map_Ici_inclusion_atTop (E F : FiniteLayer K L) (hEF : E ≤ F) :
    map (fun G : Set.Ici F => (⟨G.val, hEF.trans G.property⟩ : Set.Ici E)) atTop = atTop := by
  apply le_antisymm (FiniteLayer.tendsto_Ici_inclusion K L E F hEF)
  intro s hs
  obtain ⟨a, ha⟩ := eventually_atTop.mp hs
  refine eventually_atTop.mpr ⟨⟨a.val, hEF.trans a.property⟩, fun b hb => ?_⟩
  exact ha ⟨b.val, a.property.trans (show a.val ≤ b.val from hb)⟩ hb

/-- Actual norm transitivity compares the same norm-sum net at two fixed bases. -/
theorem norm_normSumNet (E F : FiniteLayer K L) (hEF : E ≤ F)
    (α β : NormLimit K L) (G : Set.Ici F) :
    FiniteLayer.norm E F hEF (normSumNet K L F α β G) =
      normSumNet K L E α β ⟨G.val, hEF.trans G.property⟩ := by
  exact FiniteLayer.norm_norm E F G.val hEF G.property _

end FiniteLayerNets

section NormSumLimits

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- A limit at a larger original finite base descends by its continuous norm,
because the corresponding index is an entire tail of the smaller-base net. -/
theorem tendsto_normSumNet_of_upper (E F : FiniteLayer K L) (hEF : E ≤ F)
    (α β : NormLimit K L) (z : F.val) :
    let := spectralNorm.nontriviallyNormedField K E.val
    let := spectralNorm.nontriviallyNormedField K F.val
    Tendsto (normSumNet K L F α β) atTop (nhds z) →
      Tendsto (normSumNet K L E α β) atTop (nhds (FiniteLayer.norm E F hEF z)) := by
  let := spectralNorm.nontriviallyNormedField K E.val
  let := spectralNorm.nontriviallyNormedField K F.val
  dsimp only
  intro hz
  have hc := ((FiniteLayer.continuous_norm E F hEF).tendsto z).comp hz
  change map (normSumNet K L E α β) atTop ≤ _
  rw [← FiniteLayer.map_Ici_inclusion_atTop K L E F hEF, map_map]
  simpa only [Tendsto, Function.comp_def, norm_normSumNet] using hc

/-- Uniqueness in the original Hausdorff finite fields makes the actual
norm-sum limits compatible under every original finite-layer norm. -/
theorem norm_of_normSumNet_tendsto (E F : FiniteLayer K L) (hEF : E ≤ F)
    (α β : NormLimit K L) (x : E.val) (y : F.val) :
    let := spectralNorm.nontriviallyNormedField K E.val
    let := spectralNorm.nontriviallyNormedField K F.val
    Tendsto (normSumNet K L E α β) atTop (nhds x) →
      Tendsto (normSumNet K L F α β) atTop (nhds y) →
        FiniteLayer.norm E F hEF y = x := by
  let := spectralNorm.nontriviallyNormedField K E.val
  let := spectralNorm.nontriviallyNormedField K F.val
  dsimp only
  intro hx hy
  exact tendsto_nhds_unique (tendsto_normSumNet_of_upper K L E F hEF α β y hy) hx

/-- Convergence above one actual finite layer gives convergence at every
original finite base by descent from its compositum with that layer. -/
theorem exists_tendsto_normSumNet_of_upper_tail (T : FiniteLayer K L)
    (α β : NormLimit K L)
    (h : ∀ F : FiniteLayer K L, T ≤ F → ∃ z : F.val,
      letI := spectralNorm.nontriviallyNormedField K F.val
      Tendsto (normSumNet K L F α β) atTop (nhds z)) :
    ∀ E : FiniteLayer K L, ∃ z : E.val,
      letI := spectralNorm.nontriviallyNormedField K E.val
      Tendsto (normSumNet K L E α β) atTop (nhds z) := by
  intro E
  let F := FiniteLayer.sup E T
  have hEF : E ≤ F := FiniteLayer.le_sup_left E T
  obtain ⟨z, hz⟩ := h F (FiniteLayer.le_sup_right E T)
  exact ⟨FiniteLayer.norm E F hEF z,
    tendsto_normSumNet_of_upper K L E F hEF α β z hz⟩

/-- When the actual original norm-sum nets converge, their unique limits
are represented by the same zero-adjoined unit norm limit. -/
theorem existsUnique_normLimit_of_normSumNet_tendsto (α β : NormLimit K L)
    (h : ∀ E : FiniteLayer K L, ∃ z : E.val,
      letI := spectralNorm.nontriviallyNormedField K E.val
      Tendsto (normSumNet K L E α β) atTop (nhds z)) :
    ∃! γ : NormLimit K L, ∀ E : FiniteLayer K L,
      letI := spectralNorm.nontriviallyNormedField K E.val
      Tendsto (normSumNet K L E α β) atTop (nhds (normLimitEval K L E γ)) := by
  choose z hz using h
  have hnorm (E F : FiniteLayer K L) (hEF : E ≤ F) :
      FiniteLayer.norm E F hEF (z F) = z E :=
    norm_of_normSumNet_tendsto K L E F hEF α β (z E) (z F) (hz E) (hz F)
  obtain ⟨γ, hγ, huniq⟩ := existsUnique_normLimit_of_compatible K L z hnorm
  refine ⟨γ, fun E => ?_, fun δ hδ => ?_⟩
  · rw [hγ E]
    exact hz E
  · apply huniq δ
    intro E
    let := spectralNorm.nontriviallyNormedField K E.val
    exact tendsto_nhds_unique (hδ E) (hz E)

end NormSumLimits

section IntegralFamilies

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- The proved stable coordinate valuation makes integral norm families
integral on one actual finite tail, simultaneously for every family. -/
theorem IsAPF.exists_finiteLayer_normLimitEval_mem_of_le_one (hL : IsAPF K L) :
    ∃ T : FiniteLayer K L, ∀ E : FiniteLayer K L, T ≤ E → ∀ x : NormLimit K L,
      normLimitValuation K L hL x ≤ 1 →
        normLimitEval K L E x ∈ spectralIntegerRing K E.val := by
  obtain ⟨T, hT⟩ := IsAPF.exists_normLimitValuation_eq_coordinate K L hL
  refine ⟨T, fun E hE x hx => ?_⟩
  rw [hT E hE x] at hx
  change normLimitEval K L E x ∈
    ((IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K E.val)).valuation
      E.val).valuationSubring at hx
  rw [ValuationSubring.normalizedValuation_valuationSubring] at hx
  exact hx

/-- Every original coordinate is integral if the same stable norm-limit
valuation is integral: actual integral norms descend from a common tail. -/
theorem normLimitEval_mem_of_valuation_le_one (hL : IsAPF K L) (x : NormLimit K L)
    (hx : normLimitValuation K L hL x ≤ 1) (E : FiniteLayer K L) :
    normLimitEval K L E x ∈ spectralIntegerRing K E.val := by
  obtain ⟨T, hT⟩ := IsAPF.exists_finiteLayer_normLimitEval_mem_of_le_one K L hL
  let F := FiniteLayer.sup E T
  have hEF : E ≤ F := FiniteLayer.le_sup_left E T
  let xF : spectralIntegerRing K F.val :=
    ⟨normLimitEval K L F x, hT F (FiniteLayer.le_sup_right E T) x hx⟩
  have h := (FiniteLayer.integerNorm E F hEF xF).property
  rw [FiniteLayer.coe_integerNorm] at h
  change FiniteLayer.norm E F hEF (normLimitEval K L F x) ∈
    spectralIntegerRing K E.val at h
  rw [normLimitEval_norm] at h
  exact h

/-- The integral part of the stable valuation is exactly the families
with integral coordinates in every original finite field. -/
theorem normLimitValuation_le_one_iff (hL : IsAPF K L) (x : NormLimit K L) :
    normLimitValuation K L hL x ≤ 1 ↔
      ∀ E : FiniteLayer K L, normLimitEval K L E x ∈ spectralIntegerRing K E.val := by
  constructor
  · exact fun hx E => normLimitEval_mem_of_valuation_le_one K L hL x hx E
  · intro hx
    let T := (IsAPF.exists_normLimitCoordinateValuation_stable K L hL).choose
    change normLimitEval K L T x ∈
      ((IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K T.val)).valuation
        T.val).valuationSubring
    rw [ValuationSubring.normalizedValuation_valuationSubring]
    exact hx T

/-- Every term of an integral-family norm-sum net is an integer of the
original fixed finite field. -/
theorem normSumNet_mem_of_valuation_le_one (hL : IsAPF K L) (α β : NormLimit K L)
    (hα : normLimitValuation K L hL α ≤ 1) (hβ : normLimitValuation K L hL β ≤ 1)
    (E : FiniteLayer K L) (F : Set.Ici E) :
    normSumNet K L E α β F ∈ spectralIntegerRing K E.val := by
  let x : spectralIntegerRing K F.val.val :=
    ⟨normLimitEval K L F.val α, normLimitEval_mem_of_valuation_le_one K L hL α hα F.val⟩
  let y : spectralIntegerRing K F.val.val :=
    ⟨normLimitEval K L F.val β, normLimitEval_mem_of_valuation_le_one K L hL β hβ F.val⟩
  have h := (FiniteLayer.integerNorm E F.val F.property (x + y)).property
  rw [FiniteLayer.coe_integerNorm E F.val F.property (x + y)] at h
  exact h

/-- A convergent integral-family norm-sum net has an integral limit, in
the same original finite field and its actual closed integer ring. -/
theorem normSumNet_limit_mem_of_valuation_le_one (hL : IsAPF K L) (α β : NormLimit K L)
    (hα : normLimitValuation K L hL α ≤ 1) (hβ : normLimitValuation K L hL β ≤ 1)
    (E : FiniteLayer K L) (z : E.val) :
    letI := spectralNorm.nontriviallyNormedField K E.val
    Tendsto (normSumNet K L E α β) atTop (nhds z) →
      z ∈ spectralIntegerRing K E.val := by
  let := spectralNorm.nontriviallyNormedField K E.val
  intro hz
  have hz' := (FiniteLayer.isClosed_image_maximalIdeal_pow E 0).mem_of_tendsto hz
    (Eventually.of_forall fun F => ⟨⟨normSumNet K L E α β F,
      normSumNet_mem_of_valuation_le_one K L hL α β hα hβ E F⟩, by simp, rfl⟩)
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
