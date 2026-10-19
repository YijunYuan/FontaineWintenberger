/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Ramification.Upper.Transport

/-!
# Upper ramification groups of infinite Galois extensions

## Infinite upper ramification inside Galois groups

The upper groups are intersections of preimages of the finite
upper groups under ordinary restriction, with the existing Krull topology.

## Testing infinite upper groups on cofinal finite intermediate fields
-/

@[expose] public section

namespace FontaineWintenberger

variable (K Ω : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [Field Ω] [Algebra K Ω]

/-- Infinite upper numbering in the Galois group, using ordinary finite restrictions. -/
noncomputable def upperRamificationGroupInfinite (u : ℝ) : Subgroup (Ω ≃ₐ[K] Ω) :=
  ⨅ E : FiniteGaloisIntermediateField K Ω,
    (upperRamificationGroup (R := spectralIntegerRing K E) (E ≃ₐ[K] E) u).comap
      (AlgEquiv.restrictNormalHom E)

theorem mem_upperRamificationGroupInfinite (u : ℝ) (s : Ω ≃ₐ[K] Ω) :
    s ∈ upperRamificationGroupInfinite K Ω u ↔
      ∀ E : FiniteGaloisIntermediateField K Ω,
        s.restrictNormal E ∈
          upperRamificationGroup (R := spectralIntegerRing K E) (E ≃ₐ[K] E) u := by
  simp only [upperRamificationGroupInfinite, Subgroup.mem_iInf, Subgroup.mem_comap]
  rfl

instance upperRamificationGroupInfinite_normal (u : ℝ) :
    (upperRamificationGroupInfinite K Ω u).Normal := by
  unfold upperRamificationGroupInfinite
  exact Subgroup.normal_iInf_normal (fun _ => inferInstance)

theorem upperRamificationGroupInfinite_antitoneOn :
    AntitoneOn (upperRamificationGroupInfinite K Ω) (Set.Ici (-1)) := by
  intro u hu v hv huv s hs
  rw [mem_upperRamificationGroupInfinite] at hs ⊢
  intro E
  exact upperRamificationGroup_antitoneOn (R := spectralIntegerRing K E)
    (E ≃ₐ[K] E) hu hv huv (hs E)

@[simp]
theorem upperRamificationGroupInfinite_neg_one :
    upperRamificationGroupInfinite K Ω (-1) = ⊤ := by
  simp [upperRamificationGroupInfinite]

theorem isClosed_upperRamificationGroupInfinite (u : ℝ) :
    IsClosed (upperRamificationGroupInfinite K Ω u : Set (Ω ≃ₐ[K] Ω)) := by
  rw [upperRamificationGroupInfinite, Subgroup.coe_iInf]
  apply isClosed_iInter
  intro E
  exact (isClosed_discrete _).preimage
    (InfiniteGalois.restrictNormalHom_continuous E.toIntermediateField)

theorem map_upperRamificationGroupInfinite_le (E : FiniteGaloisIntermediateField K Ω) (u : ℝ) :
    (upperRamificationGroupInfinite K Ω u).map (AlgEquiv.restrictNormalHom E) ≤
      upperRamificationGroup (R := spectralIntegerRing K E) (E ≃ₐ[K] E) u := by
  apply Subgroup.map_le_iff_le_comap.mpr
  exact iInf_le _ E

variable [IsGalois K Ω]

theorem isCompact_upperRamificationGroupInfinite (u : ℝ) :
    IsCompact (upperRamificationGroupInfinite K Ω u : Set (Ω ≃ₐ[K] Ω)) :=
  (isClosed_upperRamificationGroupInfinite K Ω u).isCompact

variable [PerfectField 𝓀[K]]

/-- Finitely many upper conditions can be lifted together with one prescribed finite restriction. -/
theorem exists_lift_finite_upper_conditions (E : FiniteGaloisIntermediateField K Ω)
    (S : Finset (FiniteGaloisIntermediateField K Ω)) (u : ℝ) (hu : -1 ≤ u)
    (q : E ≃ₐ[K] E)
    (hq : q ∈ upperRamificationGroup (R := spectralIntegerRing K E) (E ≃ₐ[K] E) u) :
    ∃ s : Ω ≃ₐ[K] Ω, s.restrictNormal E = q ∧
      ∀ D ∈ S, s.restrictNormal D ∈
        upperRamificationGroup (R := spectralIntegerRing K D) (D ≃ₐ[K] D) u := by
  classical
  let M := E ⊔ S.sup id
  let fME : Opposite.op M ⟶ Opposite.op E :=
    (CategoryTheory.homOfLE (show E ≤ M from le_sup_left)).op
  have hq' : q ∈
      (upperRamificationGroup (R := spectralIntegerRing K M) (M ≃ₐ[K] M) u).map
        (finGaloisGroupMap fME).hom.hom := by
    rw [finGaloisGroupMap_map_upperRamificationGroup K Ω fME u hu]
    exact hq
  obtain ⟨r, hr, hrq⟩ := Subgroup.mem_map.mp hq'
  obtain ⟨s, hs⟩ := AlgEquiv.restrictNormalHom_surjective
    (F := K) (K₁ := M) (E := Ω) r
  change s.restrictNormal M = r at hs
  have hresE := (InfiniteGalois.algEquivToLimit K Ω s).property fME
  change (finGaloisGroupMap fME).hom.hom (s.restrictNormal M) = s.restrictNormal E at hresE
  rw [hs] at hresE
  refine ⟨s, hresE.symm.trans hrq, ?_⟩
  intro D hD
  have hDM : D ≤ M := (Finset.le_sup (f := id) hD).trans le_sup_right
  let fMD : Opposite.op M ⟶ Opposite.op D := (CategoryTheory.homOfLE hDM).op
  have hresD := (InfiniteGalois.algEquivToLimit K Ω s).property fMD
  change (finGaloisGroupMap fMD).hom.hom (s.restrictNormal M) = s.restrictNormal D at hresD
  rw [hs] at hresD
  rw [← finGaloisGroupMap_map_upperRamificationGroup K Ω fMD u hu]
  exact Subgroup.mem_map.mpr ⟨r, hr, hresD⟩

/-- Compactness lifts every finite upper automorphism through all finite upper conditions. -/
theorem exists_lift_upperRamificationGroupInfinite (E : FiniteGaloisIntermediateField K Ω)
    (u : ℝ) (hu : -1 ≤ u) (q : E ≃ₐ[K] E)
    (hq : q ∈ upperRamificationGroup (R := spectralIntegerRing K E) (E ≃ₐ[K] E) u) :
    ∃ s ∈ upperRamificationGroupInfinite K Ω u, s.restrictNormal E = q := by
  let C : Set (Ω ≃ₐ[K] Ω) := {s | s.restrictNormal E = q}
  let T (D : FiniteGaloisIntermediateField K Ω) : Set (Ω ≃ₐ[K] Ω) :=
    (AlgEquiv.restrictNormalHom D) ⁻¹'
      (upperRamificationGroup (R := spectralIntegerRing K D) (D ≃ₐ[K] D) u)
  have hC : IsClosed C := isClosed_singleton.preimage
    (InfiniteGalois.restrictNormalHom_continuous E.toIntermediateField)
  have hT (D : FiniteGaloisIntermediateField K Ω) : IsClosed (T D) :=
    (isClosed_discrete _).preimage
      (InfiniteGalois.restrictNormalHom_continuous D.toIntermediateField)
  have hfinite (S : Finset (FiniteGaloisIntermediateField K Ω)) :
      (C ∩ ⋂ D ∈ S, T D).Nonempty := by
    obtain ⟨s, hs, hS⟩ := exists_lift_finite_upper_conditions K Ω E S u hu q hq
    refine ⟨s, hs, ?_⟩
    simp only [Set.mem_iInter]
    exact hS
  obtain ⟨s, hsC, hsT⟩ := hC.isCompact.inter_iInter_nonempty T hT hfinite
  refine ⟨s, (mem_upperRamificationGroupInfinite K Ω u s).mpr ?_, hsC⟩
  exact Set.mem_iInter.mp hsT

/-- Every finite upper group is the image of the infinite upper group. -/
theorem map_upperRamificationGroupInfinite (E : FiniteGaloisIntermediateField K Ω)
    (u : ℝ) (hu : -1 ≤ u) :
    (upperRamificationGroupInfinite K Ω u).map (AlgEquiv.restrictNormalHom E) =
      upperRamificationGroup (R := spectralIntegerRing K E) (E ≃ₐ[K] E) u := by
  apply le_antisymm (map_upperRamificationGroupInfinite_le K Ω E u)
  intro q hq
  obtain ⟨s, hs, hres⟩ := exists_lift_upperRamificationGroupInfinite K Ω E u hu q hq
  exact Subgroup.mem_map.mpr ⟨s, hs, hres⟩

end FontaineWintenberger

namespace FontaineWintenberger

variable (K Ω : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [Field Ω] [Algebra K Ω]
    [PerfectField 𝓀[K]]

/-- A cofinal family of finite intermediate fields tests all infinite upper conditions. -/
theorem mem_upperRamificationGroupInfinite_iff_cofinal
    {ι : Type*} (E : ι → FiniteGaloisIntermediateField K Ω)
    (hE : ∀ D : FiniteGaloisIntermediateField K Ω, ∃ j, D ≤ E j)
    {u : ℝ} (hu : -1 ≤ u) (g : Ω ≃ₐ[K] Ω) :
    g ∈ upperRamificationGroupInfinite K Ω u ↔
      ∀ j, g.restrictNormal (E j) ∈
        upperRamificationGroup (R := spectralIntegerRing K (E j)) (E j ≃ₐ[K] E j) u := by
  rw [mem_upperRamificationGroupInfinite]
  constructor
  · exact fun h j => h (E j)
  · intro h D
    obtain ⟨j, hj⟩ := hE D
    let f : Opposite.op (E j) ⟶ Opposite.op D := (CategoryTheory.homOfLE hj).op
    have hres := (InfiniteGalois.algEquivToLimit K Ω g).property f
    change (finGaloisGroupMap f).hom.hom (g.restrictNormal (E j)) =
      g.restrictNormal D at hres
    rw [← finGaloisGroupMap_map_upperRamificationGroup K Ω f u hu]
    exact Subgroup.mem_map.mpr ⟨g.restrictNormal (E j), h j, hres⟩

end FontaineWintenberger
