module

public import FontaineWintenberger.APF.IndexTransport
public import FontaineWintenberger.Ramification.InfiniteEquiv

/-!
# The intrinsic Galois APF criterion

Ordinary absolute restriction is onto, with the actual fixing subgroup as
kernel. Its upper images identify both APF openness and the actual inertia
index with those inside the abstract extension's own Galois group.
-/

@[expose] public section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]

theorem isOpen_upperRamificationGroupInfinite_iff_finiteIndex
    (L : Type*) [Field L] [Algebra K L] [IsGalois K L] (u : ℝ) :
    IsOpen (upperRamificationGroupInfinite K L u : Set (L ≃ₐ[K] L)) ↔
      (upperRamificationGroupInfinite K L u).FiniteIndex := by
  constructor
  · intro h
    let := (upperRamificationGroupInfinite K L u).quotient_finite_of_isOpen h
    exact Subgroup.finiteIndex_of_finite_quotient
  · intro h
    let := h
    exact (upperRamificationGroupInfinite K L u).isOpen_of_isClosed_of_finiteIndex
      (isClosed_upperRamificationGroupInfinite K L u)

variable [PerfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := K)).valuationSubring)]

theorem apfSubgroup_eq_comap_upperInfinite
    (L : IntermediateField K (SeparableClosure K)) [IsGalois K L] {u : ℝ} (hu : -1 ≤ u) :
    apfSubgroup K L u =
      (upperRamificationGroupInfinite K L u).comap (AlgEquiv.restrictNormalHom L) := by
  rw [← absolute_restrict_map_upperRamificationGroupInfinite K L u hu,
    Subgroup.comap_map_eq, IntermediateField.restrictNormalHom_ker L]
  exact sup_comm _ _

theorem apfInertiaIndex_eq_upperInfiniteRelIndex
    (L : IntermediateField K (SeparableClosure K)) [IsGalois K L] {u : ℝ} (hu : 0 ≤ u) :
    apfInertiaIndex K L u =
      (upperRamificationGroupInfinite K L u).relIndex (upperRamificationGroupInfinite K L 0) := by
  unfold apfInertiaIndex
  rw [apfInertiaSubgroup_eq_inf K L u hu, Subgroup.inf_relIndex_right,
    apfSubgroup_eq_comap_upperInfinite K L (by linarith), Subgroup.relIndex_comap,
    absolute_restrict_map_upperRamificationGroupInfinite K L 0 (by norm_num)]

theorem isAPFSubextension_iff_upperInfinite_finiteIndex
    (L : IntermediateField K (SeparableClosure K)) [IsGalois K L] :
    IsAPFSubextension K L ↔
      ∀ u : ℝ, -1 ≤ u → (upperRamificationGroupInfinite K L u).FiniteIndex := by
  rw [isAPFSubextension_iff_finiteIndex]
  apply forall_congr'
  intro u
  apply forall_congr'
  intro hu
  rw [apfSubgroup_eq_comap_upperInfinite K L hu, Subgroup.finiteIndex_iff,
    Subgroup.finiteIndex_iff, Subgroup.index_comap_of_surjective _
      (AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) (SeparableClosure K))]

variable (L : Type*) [Field L] [Algebra K L] [IsGalois K L]

/-- APF is finite index of every actual upper group inside the abstract Galois group. -/
theorem isAPF_iff_upperInfinite_finiteIndex :
    IsAPF K L ↔ ∀ u : ℝ, -1 ≤ u → (upperRamificationGroupInfinite K L u).FiniteIndex := by
  let i : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let := IsGalois.of_algEquiv i.equivFieldRange
  rw [isAPF_iff_embedding K L i, isAPFSubextension_iff_upperInfinite_finiteIndex]
  apply forall_congr'
  intro u
  apply forall_congr'
  intro hu
  rw [← upperRamificationGroupInfinite_map_autCongr K i.equivFieldRange hu]
  simp only [Subgroup.finiteIndex_iff]
  exact Iff.of_eq (congrArg (fun n : ℕ ↦ n ≠ 0)
    (Subgroup.index_map_equiv (upperRamificationGroupInfinite K L u) i.equivFieldRange.autCongr))

/-- The actual Krull-topological openness criterion for an abstract Galois extension. -/
theorem isAPF_iff_upperInfinite_isOpen :
    IsAPF K L ↔ ∀ u : ℝ, -1 ≤ u →
      IsOpen (upperRamificationGroupInfinite K L u : Set (L ≃ₐ[K] L)) := by
  simp only [isAPF_iff_upperInfinite_finiteIndex,
    isOpen_upperRamificationGroupInfinite_iff_finiteIndex]

/-- The intrinsic index agrees with the actual upper index, including infinite indices. -/
theorem apfIndex_eq_upperInfiniteRelIndex {u : ℝ} (hu : 0 ≤ u) :
    apfIndex K L u =
      (upperRamificationGroupInfinite K L u).relIndex (upperRamificationGroupInfinite K L 0) := by
  let i : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let := IsGalois.of_algEquiv i.equivFieldRange
  rw [apfIndex_eq_embedding K L i, apfInertiaIndex_eq_upperInfiniteRelIndex K i.fieldRange hu,
    ← upperRamificationGroupInfinite_map_autCongr K i.equivFieldRange (by linarith : -1 ≤ u),
    ← upperRamificationGroupInfinite_map_autCongr K i.equivFieldRange (by norm_num : -1 ≤ (0 : ℝ))]
  exact Subgroup.relIndex_map_map_of_injective _ _ i.equivFieldRange.autCongr.injective

end FontaineWintenberger
