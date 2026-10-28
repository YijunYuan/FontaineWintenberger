/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.FieldOfNorms.Galois.Upper

/-!
# Upper ramification in the relative field of norms

The upper filtration on the relative norm-field Galois group is tested on all finite
Galois stages. Finite descent compares this filtration with the absolute upper filtration
of the original field, with the inverse Herbrand change of parameter.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, Corollary 3.3.6.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

section Relative

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
variable (L Ω : Type*) [Field L] [Field Ω] [Algebra K L] [Algebra K Ω]
    [Algebra L Ω] [IsScalarTower K L Ω] [Algebra.IsSeparable K L]
    [Algebra.IsSeparable K Ω] [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- Upper ramification on the relative field of norms, expressed on the original Galois
group through its restrictions to all finite Galois norm fields. -/
def RelFieldOfNorms.upperRamificationGroup (u : ℝ) : Subgroup (Ω ≃ₐ[L] Ω) := by
  let : Algebra.IsSeparable L Ω :=
    Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  exact ⨅ N : FiniteGaloisIntermediateField L Ω,
    (FieldOfNorms.upperRamificationGroup K L N u).comap (AlgEquiv.restrictNormalHom N)

/-- Membership in the relative upper filtration is detected on every finite Galois stage. -/
theorem RelFieldOfNorms.mem_upperRamificationGroup (u : ℝ) (σ : Ω ≃ₐ[L] Ω) :
    letI : Algebra.IsSeparable L Ω :=
      Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    σ ∈ RelFieldOfNorms.upperRamificationGroup K L Ω u ↔
      ∀ N : FiniteGaloisIntermediateField L Ω,
        σ.restrictNormal N ∈ FieldOfNorms.upperRamificationGroup K L N u := by
  simp only [RelFieldOfNorms.upperRamificationGroup, Subgroup.mem_iInf, Subgroup.mem_comap]
  rfl

end Relative

section Overfield

variable (K L Ω : Type*) [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra K Ω]
    [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]

/-- A finite old-base field is contained in a finite Galois extension of the larger base. -/
private theorem exists_finiteGalois_containing_finite_oldBase
    (E : FiniteGaloisIntermediateField K Ω) :
    ∃ N : FiniteGaloisIntermediateField L Ω,
      E.toIntermediateField ≤ N.toIntermediateField.restrictScalars K := by
  let : IsGalois L Ω := IsGalois.tower_top_of_isGalois K L Ω
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K E
  let M := IntermediateField.adjoin L {(α : Ω)}
  have : FiniteDimensional L M :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (α : Ω))
  let N : FiniteGaloisIntermediateField L Ω :=
    { IntermediateField.normalClosure L M Ω with }
  refine ⟨N, ?_⟩
  have hE : IntermediateField.adjoin K {(α : Ω)} = E.toIntermediateField := by
    have h := congrArg (IntermediateField.map E.toIntermediateField.val) hα
    simpa only [IntermediateField.adjoin_map, Set.image_singleton,
      ← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val,
      IntermediateField.coe_val] using h
  rw [← hE]
  apply IntermediateField.adjoin_simple_le_iff.mpr
  exact IntermediateField.le_normalClosure M
    (IntermediateField.mem_adjoin_simple_self L (α : Ω))

end Overfield

section AmbientComparison

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
variable (L M : Type*) [Field L] [Field M] [Algebra K L] [Algebra K M]
    [Algebra L M] [IsScalarTower K L M] [Algebra.IsSeparable K L] [IsGalois K M]
    [IsAPF K L] [Fact (¬ Module.Finite K L)]
    [Algebra L (SeparableClosure K)] [Algebra M (SeparableClosure K)]
    [IsScalarTower K L (SeparableClosure K)] [IsScalarTower K M (SeparableClosure K)]
    [IsScalarTower L M (SeparableClosure K)]

attribute [local instance]
  FiniteIntermediateField.instNontriviallyNormedField
  FiniteIntermediateField.instNormedAlgebra
  FiniteIntermediateField.instIsUltrametricDist
  FiniteIntermediateField.instCompleteSpace
  FiniteIntermediateField.instIsPerfectResidueLocalField
  FiniteIntermediateField.instIsSeparable

/-- Finite norm-field upper conditions imply the original absolute upper condition. -/
theorem RelFieldOfNorms.restrictScalars_mem_upperRamificationGroupInfinite_tower
    {u : ℝ} (hu : -1 ≤ u) (σ : M ≃ₐ[L] M)
    (hσ : σ ∈ RelFieldOfNorms.upperRamificationGroup K L M
      (apfPsi K L u)) :
    σ.restrictScalars K ∈ upperRamificationGroupInfinite K M u := by
  let : Algebra.IsSeparable L M :=
    Algebra.isSeparable_tower_top_of_isSeparable K L M
  rw [mem_upperRamificationGroupInfinite]
  intro E
  obtain ⟨N, hEN⟩ := exists_finiteGalois_containing_finite_oldBase K L M E
  let jE : E →ₐ[K] N := IntermediateField.inclusion hEN
  let E' : FiniteIntermediateField K N :=
    ⟨jE.fieldRange, Module.Finite.equiv jE.equivFieldRange.toLinearEquiv⟩
  obtain ⟨D, hD, _, hs, ⟨α, hαD, hα⟩, hψ, hr⟩ :=
    exists_galois_stable_goodFiniteLayer_apfPsi_eq K L N E' u
  let C := FiniteIntermediateField.pullbackLayer K L D
  let : Algebra C.val D.val := FiniteIntermediateField.pullbackAlgebra K L D
  let : IsScalarTower K C.val D.val := FiniteIntermediateField.pullback_scalarTower K L D
  let : FiniteDimensional C.val D.val := FiniteIntermediateField.overPullback_finite K L D
  let : IsScalarTower C.val D.val M :=
    IsScalarTower.of_algebraMap_eq fun x ↦ IsScalarTower.algebraMap_apply L N M x
  let : IsGalois C.val D.val := isGalois_galoisStableFiniteLayer K L N D hs
  let := MulSemiringAction.compHom (spectralIntegerRing K D.val)
    (AlgEquiv.restrictScalarsHom K (S := C.val) (A := D.val))
  let e : (N ≃ₐ[L] N) ≃* (D.val ≃ₐ[C.val] D.val) :=
    galoisFiniteLayerEquiv K L N D hs α hα hαD
  let s : D.val ≃ₐ[C.val] D.val := e (σ.restrictNormal N)
  have hm : (FieldOfNorms.upperRamificationGroup K L N (apfPsi K L u)).map
        e.toMonoidHom =
      FontaineWintenberger.upperRamificationGroup (R := spectralIntegerRing K D.val)
        (D.val ≃ₐ[C.val] D.val) (apfPsi K L u) :=
    galoisFiniteLayerEquiv_map_upperRamificationGroup K L N D hs α hα hαD hr
      (IsAPF.apfPsi_mem_Ici K L hu)
  have hsupper : s ∈ FontaineWintenberger.upperRamificationGroup
      (R := spectralIntegerRing K D.val)
      (D.val ≃ₐ[C.val] D.val) (apfPsi K L u) := by
    rw [← hm]
    exact Subgroup.mem_map.mpr ⟨σ.restrictNormal N,
      (RelFieldOfNorms.mem_upperRamificationGroup K L M _ σ).mp hσ N, rfl⟩
  change apfPsi K C.val u = apfPsi K L u at hψ
  have hv : -1 ≤ apfPsi K C.val u := IsAPF.apfPsi_mem_Ici K C.val hu
  rw [← hψ, upperRamificationGroup_restrictScalars_eq K C.val D.val hv] at hsupper
  let : IsGalois C.val M :=
    IsGalois.tower_top_of_isGalois K C.val M
  obtain ⟨τ, hτ, hτD⟩ := exists_lift_upperRamificationGroup_of_finite C.val
    M D.val hv s hsupper
  have hτK : τ.restrictScalars K ∈ upperRamificationGroupInfinite K M u :=
    (mem_upperRamificationGroupInfinite_finiteBase_tower_iff K C.val M hu τ).mp hτ
  have hτE := (mem_upperRamificationGroupInfinite K M u
    (τ.restrictScalars K)).mp hτK E
  have he : (τ.restrictScalars K).restrictNormal E = (σ.restrictScalars K).restrictNormal E := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    let y : D.val := ⟨jE x, hD ⟨x, rfl⟩⟩
    have hxy : algebraMap D.val M y = (x : M) := rfl
    have ht := congrArg (fun f : D.val ≃ₐ[C.val] D.val ↦
      algebraMap D.val M (f y)) hτD
    rw [AlgEquiv.restrictNormal_commutes] at ht
    have hsval : algebraMap D.val M (s y) = σ (x : M) := by
      change ((σ.restrictNormal N (y : N) : N) : M) = _
      exact AlgEquiv.restrictNormal_commutes σ N (y : N)
    rw [hxy, hsval] at ht
    exact (AlgEquiv.restrictNormal_commutes (τ.restrictScalars K) E x).trans
      (ht.trans (AlgEquiv.restrictNormal_commutes (σ.restrictScalars K) E x).symm)
  exact he ▸ hτE

end AmbientComparison

end FontaineWintenberger

namespace FontaineWintenberger

section RamificationComparison

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
variable (L M : Type*) [Field L] [Field M] [Algebra K L] [Algebra K M]
    [Algebra L M] [IsScalarTower K L M] [Algebra.IsSeparable K L] [IsGalois K M]
    [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- **Wintenberger, Corollary 3.3.6.** The upper ramification filtration of the relative
field of norms agrees with the original upper filtration after the change of parameter
`ψ_{L/K}` and restriction to the automorphisms fixing `L`. -/
theorem RelFieldOfNorms.upperRamificationGroup_eq_comap {u : ℝ} (hu : -1 ≤ u) :
    RelFieldOfNorms.upperRamificationGroup K L M (apfPsi K L u) =
      (upperRamificationGroupInfinite K M u).comap (AlgEquiv.restrictScalarsHom K) := by
  let : Algebra.IsSeparable L M :=
    Algebra.isSeparable_tower_top_of_isSeparable K L M
  obtain ⟨j⟩ := nonempty_separableClosure_embeddings K M
  let : Algebra M (SeparableClosure K) := j.toRingHom.toAlgebra
  let : IsScalarTower K M (SeparableClosure K) := IsScalarTower.of_algHom j
  let jL := j.comp (IsScalarTower.toAlgHom K L M)
  let : Algebra L (SeparableClosure K) := jL.toRingHom.toAlgebra
  let : IsScalarTower K L (SeparableClosure K) := IsScalarTower.of_algHom jL
  let : IsScalarTower L M (SeparableClosure K) := IsScalarTower.of_algebraMap_eq' rfl
  ext σ
  change σ ∈ RelFieldOfNorms.upperRamificationGroup K L M (apfPsi K L u) ↔
    σ.restrictScalars K ∈ upperRamificationGroupInfinite K M u
  constructor
  · exact RelFieldOfNorms.restrictScalars_mem_upperRamificationGroupInfinite_tower K L M hu σ
  · intro hσ
    apply (RelFieldOfNorms.mem_upperRamificationGroup K L M _ σ).mpr
    intro N
    exact FieldOfNorms.restrictNormal_mem_upperRamificationGroup_tower K L N M hu σ hσ

/-- The intersection form `H^{ψ_{L/K}(u)} = G^u ∩ H` of Wintenberger's Corollary 3.3.6,
with `H = Gal(M/L)` embedded in `G = Gal(M/K)` by scalar restriction. -/
theorem RelFieldOfNorms.map_upperRamificationGroup {u : ℝ} (hu : -1 ≤ u) :
    (RelFieldOfNorms.upperRamificationGroup K L M (apfPsi K L u)).map
        (AlgEquiv.restrictScalarsHom K) =
      upperRamificationGroupInfinite K M u ⊓
        (AlgEquiv.restrictScalarsHom K (S := L) (A := M)).range := by
  rw [RelFieldOfNorms.upperRamificationGroup_eq_comap K L M hu, Subgroup.map_comap_eq, inf_comm]

end RamificationComparison

end FontaineWintenberger
