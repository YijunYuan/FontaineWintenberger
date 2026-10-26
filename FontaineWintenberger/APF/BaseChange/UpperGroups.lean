/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.BaseClosure
public import FontaineWintenberger.APF.Finite.Nonnormal
public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.LocalField.Residue.Basic
public import FontaineWintenberger.Ramification.Infinite.Basic
public import FontaineWintenberger.Ramification.Infinite.Restriction
public import FontaineWintenberger.Ramification.Upper.BaseChange

/-!
# Upper ramification groups after finite base change

The two spectral constructions give the same integer subring. The
fixing-subgroup equivalence acts by the field automorphisms, so the
subgroup change of parameter transports to the group over the new base.

The scalar tower and its field image are identified by the canonical
surjective scalar-change equivalence. The own-ring actions are preserved.

Finite upper conditions are tested on the cofinal old-base normal overfields.
Every finite comparison uses the scalar-tower and integer-ring actions.

## Main definitions

* `finiteTowerAutEquivImage`: Changing from the abstract scalar field to its image preserves
  automorphisms.
* `finiteTowerSpectralIntegerRingEquiv`: The field identity gives the integer-ring equivalence for
  scalar change.

## Main results

* `finiteBase_upperRamificationGroup_of_finiteGalois`: Finite base change for the own-ring upper
  groups, with no normality of the base.
* `finiteBase_upperRamificationGroup`: Finite base change for the own-ring upper groups, with no
  normality of the base.
* `finiteTower_spectralIntegerRing_eq`: The own spectral constructions over an embedded field and
  its image agree as subrings.
* `finiteTowerSpectralIntegerRingEquiv_smul`: Scalar change and integer-ring identification
  preserve the field action.
* `finiteTower_upper_map_autEquivImage`: Scalar change transports the own-ring upper group to the
  image-base upper group.
* `finiteTower_fixingSubtype_comp`: The canonical image-base automorphism equivalence restricts to
  the field map.
* `finiteTower_range_restrictScalarsHom`: The restriction-of-scalars image is the subgroup fixing
  the embedded scalar field.
* `finiteTower_upper_map_restrictScalars`: Finite base change for the abstract embedded base, mapped
  to its fixing subgroup.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §1 (extensions arithmétiquement profinies).
-/

@[expose] public section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (E : Type*) [NontriviallyNormedField E] [NormedAlgebra K E]
    [IsUltrametricDist E] [FiniteDimensional K E] [IsGalois K E]

variable (M : IntermediateField K E)

local instance finiteOverfieldBase_completeSpace : CompleteSpace M :=
    IntermediateField.completeSpace_of_finiteDimensional M

local instance finiteOverfieldBase_discreteValuationRing : IsCompleteDiscreteValuedField M :=
  normedAlgebra_isCompleteDiscreteValuedField K M

variable [PerfectField 𝓀[K]]

/-- Finite base change for the own-ring upper groups, with no normality of the base. -/
theorem finiteBase_upperRamificationGroup_of_finiteGalois {u : ℝ} (hu : -1 ≤ u) :
    upperRamificationGroup (R := spectralIntegerRing M E) (E ≃ₐ[M] E)
        (apfPsi K M u) =
      ((upperRamificationGroup (R := spectralIntegerRing K E) (E ≃ₐ[K] E) u).subgroupOf
        M.fixingSubgroup).map M.fixingSubgroupEquiv.toMonoidHom := by
  have hpsi : -1 ≤ apfPsi K M u := by
    rw [apfPsi_eq_subgroup_herbrand_comp_inverse_of_finiteGalois K E M hu]
    exact herbrandFunction_mem_Ici _ (inverseHerbrandFunction_mem_Ici _ u)
  rw [← finiteBase_upper_map_fixingSubgroupEquiv K E M hpsi]
  congr 1
  unfold upperRamificationGroup
  rw [apfPsi_eq_subgroup_herbrand_comp_inverse_of_finiteGalois K E M hu,
    inverseHerbrandFunction_herbrandFunction _ (inverseHerbrandFunction_mem_Ici _ u),
    lowerRamificationGroupReal_subgroupOf]

end FontaineWintenberger

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (E : FiniteGaloisIntermediateField K (SeparableClosure K))

/-- The spectral norm on a finite Galois layer for upper ramification groups. -/
noncomputable local instance finiteUpperNormedField : NontriviallyNormedField E :=
  spectralNorm.nontriviallyNormedField K E

/-- The spectral norm makes the finite Galois layer a normed algebra over `K`. -/
noncomputable local instance finiteUpperNormedAlgebra : NormedAlgebra K E :=
  spectralNorm.normedAlgebra K E

local instance : IsUltrametricDist E :=
  IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := E))

variable (M : IntermediateField K E)

local instance : CompleteSpace M := IntermediateField.completeSpace_of_finiteDimensional M

local instance : IsCompleteDiscreteValuedField M :=
  normedAlgebra_isCompleteDiscreteValuedField K M

variable [PerfectField 𝓀[K]]

/-- Finite base change for the own-ring upper groups, with no normality of the base. -/
theorem finiteBase_upperRamificationGroup {u : ℝ} (hu : -1 ≤ u) :
    upperRamificationGroup (R := spectralIntegerRing M E) (E ≃ₐ[M] E)
        (apfPsi K M u) =
      ((upperRamificationGroup (R := spectralIntegerRing K E) (E ≃ₐ[K] E) u).subgroupOf
        M.fixingSubgroup).map M.fixingSubgroupEquiv.toMonoidHom :=
  finiteBase_upperRamificationGroup_of_finiteGalois K E M hu

end FontaineWintenberger

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (E : FiniteGaloisIntermediateField K (SeparableClosure K))

/-- The spectral norm on a finite Galois layer containing an abstract base. -/
noncomputable local instance finiteTowerNormedField : NontriviallyNormedField E :=
  spectralNorm.nontriviallyNormedField K E
/-- The normed algebra structure over `K` on the finite Galois layer. -/
noncomputable local instance finiteTowerNormedAlgebra : NormedAlgebra K E :=
  spectralNorm.normedAlgebra K E
local instance : IsUltrametricDist E :=
  IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := E))

variable (M : Type*) [NontriviallyNormedField M] [IsUltrametricDist M]
    [NormedAlgebra K M] [CompleteSpace M]
    [Algebra M E] [IsScalarTower K M E]

local instance : FiniteDimensional M E := Module.Finite.right K M E

local instance : Algebra.IsAlgebraic M E := Algebra.IsAlgebraic.tower_top (K := K) M

/-- The compatible normed algebra structure over the abstract finite base. -/
noncomputable local instance finiteTowerRelativeNormedAlgebra : NormedAlgebra M E :=
  spectralNorm.normedAlgebra' K M E

local notation "S₀" => AlgHom.fieldRange (IsScalarTower.toAlgHom K M E)
local notation "e₀" => AlgHom.equivFieldRange (IsScalarTower.toAlgHom K M E)

/-- The algebra structure on the image of the abstract finite base. -/
noncomputable local instance finiteTowerImageAlgebra : Algebra M S₀ :=
  (e₀).toAlgHom.toRingHom.toAlgebra
local instance : IsScalarTower K M S₀ := IsScalarTower.of_algHom (e₀).toAlgHom
local instance : IsScalarTower M S₀ E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
local instance : FiniteDimensional S₀ E := Module.Finite.right K S₀ E
local instance : Algebra.IsAlgebraic S₀ E := Algebra.IsAlgebraic.tower_top (K := K) S₀
local instance : CompleteSpace S₀ := IntermediateField.completeSpace_of_finiteDimensional S₀

/-- The action over the image of the finite base on its spectral integer ring. -/
noncomputable local instance finiteTowerImageGaloisAction :
    MulSemiringAction (E ≃ₐ[S₀] E) (spectralIntegerRing S₀ E) :=
  spectralIntegerRingGaloisAction S₀ E

/-- Changing from the abstract scalar field to its image preserves automorphisms. -/
noncomputable def finiteTowerAutEquivImage : (E ≃ₐ[M] E) ≃* (E ≃ₐ[S₀] E) :=
  AlgEquiv.extendScalarsHomOfSurjective (R := M) (S := S₀) (A := E) (e₀).surjective

/-- The own spectral constructions over an embedded field and its image agree as subrings. -/
theorem finiteTower_spectralIntegerRing_eq :
    spectralIntegerRing M E = spectralIntegerRing S₀ E :=
  (spectralIntegerRing_eq_normedUnitBall M E).trans
    (spectralIntegerRing_eq_normedUnitBall S₀ E).symm

/-- The field identity gives the integer-ring equivalence for scalar change. -/
noncomputable def finiteTowerSpectralIntegerRingEquiv :
    spectralIntegerRing M E ≃+* spectralIntegerRing S₀ E :=
  RingEquiv.subringCongr
    (congrArg ValuationSubring.toSubring (finiteTower_spectralIntegerRing_eq K E M))

/-- Scalar change and integer-ring identification preserve the field action. -/
theorem finiteTowerSpectralIntegerRingEquiv_smul (g : E ≃ₐ[M] E)
    (x : spectralIntegerRing M E) :
    finiteTowerSpectralIntegerRingEquiv K E M (g • x) =
      finiteTowerAutEquivImage K E M g • finiteTowerSpectralIntegerRingEquiv K E M x := by
  apply Subtype.ext
  rfl

local instance : IsDiscreteValuationRing (spectralIntegerRing M E) := by
  rw [spectralIntegerRing_eq_normedUnitBall M E,
    ← spectralIntegerRing_eq_normedUnitBall K E]
  infer_instance

local instance : IsDiscreteValuationRing (spectralIntegerRing S₀ E) := by
  rw [spectralIntegerRing_eq_normedUnitBall S₀ E,
    ← spectralIntegerRing_eq_normedUnitBall K E]
  infer_instance

/-- Scalar change transports the own-ring upper group to the image-base upper group. -/
theorem finiteTower_upper_map_autEquivImage {v : ℝ} (hv : -1 ≤ v) :
    (upperRamificationGroup (R := spectralIntegerRing M E) (E ≃ₐ[M] E) v).map
        (finiteTowerAutEquivImage K E M).toMonoidHom =
      upperRamificationGroup (R := spectralIntegerRing S₀ E) (E ≃ₐ[S₀] E) v :=
  upperRamificationGroup_map_equivariant
    (finiteTowerSpectralIntegerRingEquiv K E M) (finiteTowerAutEquivImage K E M)
    (finiteTowerSpectralIntegerRingEquiv_smul K E M) hv

omit [IsCompleteDiscreteValuedField K] [IsUltrametricDist M] [CompleteSpace M]
     in
/-- The canonical image-base automorphism equivalence restricts to the field map. -/
theorem finiteTower_fixingSubtype_comp :
    (S₀).fixingSubgroup.subtype.comp
        ((S₀).fixingSubgroupEquiv.symm.toMonoidHom.comp
          (finiteTowerAutEquivImage K E M).toMonoidHom) =
      AlgEquiv.restrictScalarsHom K (S := M) (A := E) := by
  ext g x
  rfl

omit [IsCompleteDiscreteValuedField K] [IsUltrametricDist M] [CompleteSpace M]
     in
/-- The restriction-of-scalars image is the subgroup fixing the embedded scalar field. -/
theorem finiteTower_range_restrictScalarsHom :
    (AlgEquiv.restrictScalarsHom K (S := M) (A := E)).range = (S₀).fixingSubgroup := by
  rw [← finiteTower_fixingSubtype_comp K E M, MonoidHom.range_comp]
  have hs : Function.Surjective
      ((S₀).fixingSubgroupEquiv.symm.toMonoidHom.comp
        (finiteTowerAutEquivImage K E M).toMonoidHom) :=
    (S₀).fixingSubgroupEquiv.symm.surjective.comp
      (finiteTowerAutEquivImage K E M).surjective
  rw [MonoidHom.range_eq_top.mpr hs, Subgroup.map_top, Subgroup.range_subtype]

variable [FiniteDimensional K M] [Algebra.IsSeparable K M]

variable [PerfectField 𝓀[K]]

/-- Finite base change for the abstract embedded base, mapped to its fixing subgroup. -/
theorem finiteTower_upper_map_restrictScalars {u : ℝ} (hu : -1 ≤ u) :
    (upperRamificationGroup (R := spectralIntegerRing M E) (E ≃ₐ[M] E)
      (apfPsi K M u)).map (AlgEquiv.restrictScalarsHom K) =
      upperRamificationGroup (R := spectralIntegerRing K E) (E ≃ₐ[K] E) u ⊓
        (S₀).fixingSubgroup := by
  have hpsi : apfPsi K M u = apfPsi K S₀ u := apfPsi_algEquiv K M e₀ u
  have hnonneg : -1 ≤ apfPsi K M u :=
    IsAPF.apfPsi_mem_Ici K M hu
  rw [← finiteTower_fixingSubtype_comp K E M, ← Subgroup.map_map,
    ← Subgroup.map_map, finiteTower_upper_map_autEquivImage K E M hnonneg, hpsi,
    finiteBase_upperRamificationGroup K E S₀ hu, Subgroup.map_map]
  have hc : ((S₀).fixingSubgroup.subtype.comp
      (S₀).fixingSubgroupEquiv.symm.toMonoidHom).comp
        (S₀).fixingSubgroupEquiv.toMonoidHom = (S₀).fixingSubgroup.subtype := by
    ext g x
    rfl
  rw [Subgroup.map_map, hc, Subgroup.subgroupOf_map_subtype]

/-- The upper-group image is the intersection with the restriction-of-scalars range. -/
theorem finiteTower_upper_map_restrictScalars_range {u : ℝ} (hu : -1 ≤ u) :
    (upperRamificationGroup (R := spectralIntegerRing M E) (E ≃ₐ[M] E)
      (apfPsi K M u)).map (AlgEquiv.restrictScalarsHom K) =
      (AlgEquiv.restrictScalarsHom K (S := M) (A := E)).range ⊓
        upperRamificationGroup (R := spectralIntegerRing K E) (E ≃ₐ[K] E) u := by
  rw [finiteTower_range_restrictScalarsHom K E M,
    finiteTower_upper_map_restrictScalars K E M hu, inf_comm]

/-- Membership in an own-ring upper group is detected by the scalar restriction. -/
theorem finiteTower_mem_upper_iff_restrictScalars {u : ℝ} (hu : -1 ≤ u)
    (g : E ≃ₐ[M] E) :
    g ∈ upperRamificationGroup (R := spectralIntegerRing M E) (E ≃ₐ[M] E)
        (apfPsi K M u) ↔
      g.restrictScalars K ∈
        upperRamificationGroup (R := spectralIntegerRing K E) (E ≃ₐ[K] E) u := by
  have hm := finiteTower_upper_map_restrictScalars_range K E M hu
  constructor
  · intro h
    have hmap : g.restrictScalars K ∈
        (upperRamificationGroup (R := spectralIntegerRing M E) (E ≃ₐ[M] E)
          (apfPsi K M u)).map (AlgEquiv.restrictScalarsHom K) :=
      Subgroup.mem_map.mpr ⟨g, h, rfl⟩
    rw [hm] at hmap
    exact hmap.2
  · intro h
    have hmap : g.restrictScalars K ∈
        (upperRamificationGroup (R := spectralIntegerRing M E) (E ≃ₐ[M] E)
          (apfPsi K M u)).map (AlgEquiv.restrictScalarsHom K) := by
      rw [hm]
      exact ⟨⟨g, rfl⟩, h⟩
    obtain ⟨a, ha, hag⟩ := Subgroup.mem_map.mp hmap
    have hag' : a = g := by
      apply AlgEquiv.ext
      intro x
      exact congrArg (fun f : E ≃ₐ[K] E => f x) hag
    exact hag' ▸ ha

end FontaineWintenberger

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField 𝓀[K]]
variable (M : IntermediateField K (SeparableClosure K)) [FiniteDimensional K M]

/-- The spectral norm on the finite base for absolute upper ramification groups. -/
noncomputable local instance absoluteUpperBaseNormedField : NontriviallyNormedField M :=
  spectralNorm.nontriviallyNormedField K M
/-- The normed algebra structure on the finite base for absolute upper groups. -/
noncomputable local instance absoluteUpperBaseNormedAlgebra : NormedAlgebra K M :=
  spectralNorm.normedAlgebra K M
local instance : IsUltrametricDist M :=
  IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := M))
local instance : CompleteSpace M := spectralNorm.completeSpace K M
local instance : IsCompleteDiscreteValuedField M :=
  normedAlgebra_isCompleteDiscreteValuedField K M
local instance : PerfectField 𝓀[M] :=
  normedAlgebra_residueField_perfectField K M

/-- New-base upper conditions can be tested on the old-base normal overfields. -/
theorem mem_upperRamificationGroupInfinite_base_iff
    {v : ℝ} (hv : -1 ≤ v) (g : SeparableClosure K ≃ₐ[M] SeparableClosure K) :
    g ∈ upperRamificationGroupInfinite M (SeparableClosure K) v ↔
      ∀ (E : FiniteGaloisIntermediateField K (SeparableClosure K))
        (hME : M ≤ E.toIntermediateField),
        g.restrictNormal (finiteGaloisLayerOverBase K M E hME) ∈
          upperRamificationGroup
            (R := spectralIntegerRing M (finiteGaloisLayerOverBase K M E hME))
            (finiteGaloisLayerOverBase K M E hME ≃ₐ[M]
              finiteGaloisLayerOverBase K M E hME) v := by
  let F (j : {E : FiniteGaloisIntermediateField K (SeparableClosure K) //
      M ≤ E.toIntermediateField}) := finiteGaloisLayerOverBase K M j.1 j.2
  have hF : ∀ D : FiniteGaloisIntermediateField M (SeparableClosure K), ∃ j, D ≤ F j := by
    intro D
    obtain ⟨E, hME, hDE⟩ := exists_finiteGalois_over_base_layer K M D
    exact ⟨⟨E, hME⟩, hDE⟩
  rw [mem_upperRamificationGroupInfinite_iff_cofinal M (SeparableClosure K) F hF hv g]
  exact ⟨fun h E hME => h ⟨E, hME⟩, fun h j => h j.1 j.2⟩

/-- Old-base upper conditions can be tested on finite intermediate fields containing the new
base. -/
theorem mem_upperRamificationGroupInfinite_containing_base_iff
    {u : ℝ} (hu : -1 ≤ u) (g : SeparableClosure K ≃ₐ[K] SeparableClosure K) :
    g ∈ upperRamificationGroupInfinite K (SeparableClosure K) u ↔
      ∀ (E : FiniteGaloisIntermediateField K (SeparableClosure K))
        (_ : M ≤ E.toIntermediateField),
        g.restrictNormal E ∈
          upperRamificationGroup (R := spectralIntegerRing K E) (E ≃ₐ[K] E) u := by
  let F (j : {E : FiniteGaloisIntermediateField K (SeparableClosure K) //
      M ≤ E.toIntermediateField}) := j.1
  have hF : ∀ D : FiniteGaloisIntermediateField K (SeparableClosure K), ∃ j, D ≤ F j := by
    intro D
    obtain ⟨E, hME, hDE⟩ := exists_finiteGalois_containing_base K M D
    exact ⟨⟨E, hME⟩, hDE⟩
  rw [mem_upperRamificationGroupInfinite_iff_cofinal K (SeparableClosure K) F hF hu g]
  exact ⟨fun h E hME => h ⟨E, hME⟩, fun h j => h j.1 j.2⟩

/-- Finite restrictions compare the two own-ring upper conditions. -/
theorem finiteBase_restriction_mem_upper_iff
    (E : FiniteGaloisIntermediateField K (SeparableClosure K))
    (hME : M ≤ E.toIntermediateField) {u : ℝ} (hu : -1 ≤ u)
    (g : SeparableClosure K ≃ₐ[M] SeparableClosure K) :
    g.restrictNormal (finiteGaloisLayerOverBase K M E hME) ∈
        upperRamificationGroup
          (R := spectralIntegerRing M (finiteGaloisLayerOverBase K M E hME))
          (finiteGaloisLayerOverBase K M E hME ≃ₐ[M]
            finiteGaloisLayerOverBase K M E hME) (apfPsi K M u) ↔
      (g.restrictScalars K).restrictNormal E ∈
        upperRamificationGroup (R := spectralIntegerRing K E) (E ≃ₐ[K] E) u := by
  let : Algebra M E := (IntermediateField.inclusion hME).toRingHom.toAlgebra
  let : IsScalarTower K M E := IsScalarTower.of_algHom (IntermediateField.inclusion hME)
  let _ : Module M E := Algebra.toModule
  let : FiniteDimensional M E := Module.Finite.right K M E
  let : Algebra.IsSeparable M E := Algebra.isSeparable_tower_top_of_isSeparable K M E
  let : Algebra.IsAlgebraic M E := Algebra.IsAlgebraic.tower_top (K := K) M
  let q : E ≃ₐ[M] E := g.restrictNormal (finiteGaloisLayerOverBase K M E hME)
  have hq : q.restrictScalars K = (g.restrictScalars K).restrictNormal E := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    exact (AlgEquiv.restrictNormal_commutes g
      (finiteGaloisLayerOverBase K M E hME) x).trans
        (AlgEquiv.restrictNormal_commutes (g.restrictScalars K) E x).symm
  change q ∈ upperRamificationGroup (R := spectralIntegerRing M E) (E ≃ₐ[M] E)
    (apfPsi K M u) ↔ _
  rw [finiteTower_mem_upper_iff_restrictScalars K E M hu q, hq]

/-- Changing the finite base changes the parameter in the common-closure upper group. -/
theorem mem_upperRamificationGroupInfinite_finiteBase_iff
    {u : ℝ} (hu : -1 ≤ u) (g : SeparableClosure K ≃ₐ[M] SeparableClosure K) :
    g ∈ upperRamificationGroupInfinite M (SeparableClosure K) (apfPsi K M u) ↔
      g.restrictScalars K ∈ upperRamificationGroupInfinite K (SeparableClosure K) u := by
  have hv := IsAPF.apfPsi_mem_Ici K M hu
  rw [mem_upperRamificationGroupInfinite_base_iff K M hv g,
    mem_upperRamificationGroupInfinite_containing_base_iff K M hu (g.restrictScalars K)]
  exact forall_congr' fun E => forall_congr' fun hME =>
    finiteBase_restriction_mem_upper_iff K M E hME hu g

/-- The separable-closure identification preserves the finite-base parameter change. -/
theorem absoluteGaloisBaseChange_mem_upper_iff
    {u : ℝ} (hu : -1 ≤ u) (g : SeparableClosure M ≃ₐ[M] SeparableClosure M) :
    g ∈ upperRamificationGroupInfinite M (SeparableClosure M) (apfPsi K M u) ↔
      (absoluteGaloisBaseChangeEquiv K M g).1 ∈
        upperRamificationGroupInfinite K (SeparableClosure K) u := by
  have hv := IsAPF.apfPsi_mem_Ici K M hu
  exact (mem_upperRamificationGroupInfinite_autCongr_iff M
    (separableClosureBaseChangeEquiv K M) hv g).symm.trans
      (mem_upperRamificationGroupInfinite_finiteBase_iff K M hu
        ((separableClosureBaseChangeEquiv K M).autCongr g))

/-- The absolute new-base upper group maps onto the old upper group's fixing intersection. -/
theorem absoluteGaloisBaseChange_map_upper {u : ℝ} (hu : -1 ≤ u) :
    (upperRamificationGroupInfinite M (SeparableClosure M) (apfPsi K M u)).map
        (M.fixingSubgroup.subtype.comp (absoluteGaloisBaseChangeEquiv K M).toMonoidHom) =
      M.fixingSubgroup ⊓ upperRamificationGroupInfinite K (SeparableClosure K) u := by
  ext s
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨(absoluteGaloisBaseChangeEquiv K M g).property,
      (absoluteGaloisBaseChange_mem_upper_iff K M hu g).mp hg⟩
  · intro hs
    let g := (absoluteGaloisBaseChangeEquiv K M).symm ⟨s, hs.1⟩
    have hgs : (absoluteGaloisBaseChangeEquiv K M g).1 = s :=
      congrArg Subtype.val ((absoluteGaloisBaseChangeEquiv K M).apply_symm_apply ⟨s, hs.1⟩)
    refine ⟨g, ?_, hgs⟩
    apply (absoluteGaloisBaseChange_mem_upper_iff K M hu g).mpr
    rw [hgs]
    exact hs.2

end FontaineWintenberger
