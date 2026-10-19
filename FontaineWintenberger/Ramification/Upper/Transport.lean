/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Ramification.Upper.Basic
public import Mathlib.FieldTheory.Galois.Profinite

/-!
# Transport of ramification along equivariant isomorphisms

## Equivariant relabelling of intrinsic ramification

Changing the acting group's presentation preserves actual displacements,
lower groups, the integral Herbrand function, its inverse and upper groups.

## Ramification under equivariant DVR isomorphisms

Normalized valuations are preserved by actual ring isomorphisms. This
transports the intrinsic orders and both numberings between isomorphic
integral rings, retaining their actual displacement definitions.

## Field isomorphisms and intrinsic ramification

The canonical integral-closure equivalence restricts the original field
isomorphism, and is equivariant for conjugation of actual automorphisms.

## Upper ramification under ordinary restriction in finite Galois towers

Each field keeps its own spectral integers. The canonical field-range
isomorphism identifies the ordinary restriction maps pointwise.
-/

@[expose] public section

namespace FontaineWintenberger

section ActionEquiv

variable {G G' R : Type*} [Group G] [Group G'] [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [MulSemiringAction G R] [MulSemiringAction G' R]
variable (e : G ≃* G') (he : ∀ (g : G) (a : R), e g • a = g • a)

include e he

theorem ramificationOrder_mulEquiv (g : G) :
    ramificationOrder (R := R) G' (e g) = ramificationOrder (R := R) G g := by
  simp only [ramificationOrder, he]

theorem lowerRamificationGroup_map_mulEquiv (n : ℤ) :
    (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) n).map e.toMonoidHom =
      lowerRamificationGroup G' (IsLocalRing.maximalIdeal R) n := by
  ext g
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    change e h ∈ lowerRamificationGroup G' (IsLocalRing.maximalIdeal R) n
    rw [mem_lowerRamificationGroup_iff_le_order, ramificationOrder_mulEquiv e he]
    exact (mem_lowerRamificationGroup_iff_le_order G n h).mp hh
  · intro hg
    refine ⟨e.symm g, ?_, e.apply_symm_apply g⟩
    rw [mem_lowerRamificationGroup_iff_le_order,
      ← ramificationOrder_mulEquiv e he, e.apply_symm_apply]
    exact (mem_lowerRamificationGroup_iff_le_order G' n g).mp hg

theorem lowerRamificationGroupReal_map_mulEquiv (t : ℝ) :
    (lowerRamificationGroupReal G (IsLocalRing.maximalIdeal R) t).map e.toMonoidHom =
      lowerRamificationGroupReal G' (IsLocalRing.maximalIdeal R) t :=
  lowerRamificationGroup_map_mulEquiv e he _

theorem card_lowerRamificationGroupReal_mulEquiv (t : ℝ) :
    Nat.card (lowerRamificationGroupReal G' (IsLocalRing.maximalIdeal R) t) =
      Nat.card (lowerRamificationGroupReal G (IsLocalRing.maximalIdeal R) t) := by
  rw [← lowerRamificationGroupReal_map_mulEquiv e he t]
  exact Subgroup.card_map_of_injective e.injective

theorem herbrandFunction_mulEquiv (t : ℝ) :
    herbrandFunction (R := R) G' t = herbrandFunction (R := R) G t := by
  have hzero : Nat.card (lowerRamificationGroup G' (IsLocalRing.maximalIdeal R) 0) =
      Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0) := by
    simpa [lowerRamificationGroupReal] using card_lowerRamificationGroupReal_mulEquiv e he 0
  simp only [herbrandFunction, hzero, card_lowerRamificationGroupReal_mulEquiv e he]

variable [Finite G] [Finite G']

theorem inverseHerbrandFunction_mulEquiv {u : ℝ} (hu : -1 ≤ u) :
    inverseHerbrandFunction (R := R) G' u = inverseHerbrandFunction (R := R) G u := by
  apply (strictMonoOn_herbrandFunction (R := R) G).injOn
    (inverseHerbrandFunction_mem_Ici G' u) (inverseHerbrandFunction_mem_Ici G u)
  rw [← herbrandFunction_mulEquiv e he, herbrandFunction_inverseHerbrandFunction G' hu,
    herbrandFunction_inverseHerbrandFunction G hu]

theorem upperRamificationGroup_map_mulEquiv {u : ℝ} (hu : -1 ≤ u) :
    (upperRamificationGroup (R := R) G u).map e.toMonoidHom =
      upperRamificationGroup (R := R) G' u := by
  rw [upperRamificationGroup, upperRamificationGroup,
    lowerRamificationGroupReal_map_mulEquiv e he, inverseHerbrandFunction_mulEquiv e he hu]

end ActionEquiv

section IntermediateField

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (L : Type*) [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
variable (F : IntermediateField K L) [IsGalois K F]

local notation "A₀" => Valuation.valuationSubring
  (Valuation.comap (algebraMap F L) (spectralValuation K L))
local notation "B₀" => spectralIntegerRing K L
local notation "D₀" => ValuationSubring.decompositionSubgroup K A₀

/-- Ordinary field restriction preserves the actual restricted intermediate integer ring. -/
theorem restrictNormal_mem_intermediate_decomposition (s : L ≃ₐ[K] L) :
    s.restrictNormal F ∈ D₀ := by
  generalize hH : F.fixingSubgroup = H
  have : H.Normal := hH ▸ inferInstance
  have hF : IntermediateField.fixedField H = F := by
    rw [← hH]
    exact IsGalois.fixedField_fixingSubgroup F
  subst F
  exact restrictNormal_mem_fixedField_decomposition K L H s

noncomputable def intermediateDecompositionRestriction : (L ≃ₐ[K] L) →* D₀ :=
  (AlgEquiv.restrictNormalHom F).codRestrict _
    (restrictNormal_mem_intermediate_decomposition K L F)

variable [PerfectField (IsLocalRing.ResidueField
  (NormedField.valuation (K := K)).valuationSubring)]

/-- The actual quotient theorem on an arbitrary Galois intermediate field's pullback ring. -/
theorem intermediate_map_upperRamificationGroup (u : ℝ) (hu : -1 ≤ u) :
    letI := intermediate_spectral_isDiscreteValuationRing K L F
    (upperRamificationGroup (R := B₀) (L ≃ₐ[K] L) u).map
      (intermediateDecompositionRestriction K L F) =
        upperRamificationGroup (R := A₀) D₀ u := by
  have := intermediate_spectral_isDiscreteValuationRing K L F
  generalize hH : F.fixingSubgroup = H
  have : H.Normal := hH ▸ inferInstance
  have hF : IntermediateField.fixedField H = F := by
    rw [← hH]
    exact IsGalois.fixedField_fixingSubgroup F
  subst F
  simpa only [fixedFieldDecompositionRestriction, intermediateDecompositionRestriction] using
    fixedField_map_upperRamificationGroup K L H u hu

/-- Ordinary field restriction maps actual spectral upper groups onto actual spectral upper
groups. -/
theorem restrictNormalHom_map_upperRamificationGroup (u : ℝ) (hu : -1 ≤ u) :
    (upperRamificationGroup (R := B₀) (L ≃ₐ[K] L) u).map (AlgEquiv.restrictNormalHom F) =
      upperRamificationGroup (R := spectralIntegerRing K F) (F ≃ₐ[K] F) u := by
  have := intermediate_spectral_isDiscreteValuationRing K L F
  have h := congrArg (Subgroup.map (D₀).subtype)
    (intermediate_map_upperRamificationGroup K L F u hu)
  rw [Subgroup.map_map] at h
  have hcomp : (D₀).subtype.comp (intermediateDecompositionRestriction K L F) =
      AlgEquiv.restrictNormalHom F := by
    ext s
    rfl
  rw [hcomp] at h
  have := intermediate_spectral_hasExtension K L F
  have hring := spectralIntegerRing_eq_extension_valuationSubring K F
    (Valuation.comap (algebraMap F L) (spectralValuation K L))
  have htransport (A : ValuationSubring F) [IsDiscreteValuationRing A]
      (hA : A = spectralIntegerRing K F) :
      (upperRamificationGroup (R := A) (A.decompositionSubgroup K) u).map
        (A.decompositionSubgroup K).subtype =
          upperRamificationGroup (R := spectralIntegerRing K F) (F ≃ₐ[K] F) u := by
    subst A
    exact upperRamificationGroup_map_mulEquiv
      (spectralDecompositionEquiv K F) (fun _ _ => rfl) hu
  exact h.trans (htransport A₀ hring.symm)

end IntermediateField

end FontaineWintenberger

namespace FontaineWintenberger

section RingEquiv

variable {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]

theorem addVal_ringEquiv (r : R ≃+* S) (x : R) :
    IsDiscreteValuationRing.addVal S (r x) = IsDiscreteValuationRing.addVal R x := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  rw [← mem_maximalIdeal_pow_iff_addVal, ← mem_maximalIdeal_pow_iff_addVal]
  have hmap : (IsLocalRing.maximalIdeal R ^ n).map r = IsLocalRing.maximalIdeal S ^ n := by
    rw [Ideal.map_pow]
    exact congrArg (fun I : Ideal S => I ^ n)
      (IsLocalRing.map_maximalIdeal_of_surjective r.toRingHom r.surjective)
  rw [← hmap, Ideal.mem_map_iff_of_surjective r r.surjective]
  constructor
  · rintro ⟨y, hy, h⟩
    exact r.injective h ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

variable {G G' : Type*} [Group G] [Group G']
    [MulSemiringAction G R] [MulSemiringAction G' S]
variable (r : R ≃+* S) (e : G ≃* G')
    (he : ∀ (g : G) (a : R), r (g • a) = e g • r a)

include r e he

theorem ramificationOrder_equivariant (g : G) :
    ramificationOrder (R := S) G' (e g) = ramificationOrder (R := R) G g := by
  unfold ramificationOrder
  symm
  apply r.toEquiv.iInf_congr
  intro x
  change IsDiscreteValuationRing.addVal S (e g • r x - r x) =
    IsDiscreteValuationRing.addVal R (g • x - x)
  rw [← he, ← map_sub, addVal_ringEquiv]

theorem lowerRamificationGroupReal_map_equivariant (t : ℝ) :
    (lowerRamificationGroupReal G (IsLocalRing.maximalIdeal R) t).map e.toMonoidHom =
      lowerRamificationGroupReal G' (IsLocalRing.maximalIdeal S) t := by
  ext g
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    change e h ∈ lowerRamificationGroupReal G' (IsLocalRing.maximalIdeal S) t
    rw [mem_lowerRamificationGroupReal_iff_le_order, ramificationOrder_equivariant r e he]
    exact (mem_lowerRamificationGroupReal_iff_le_order G t h).mp hh
  · intro hg
    refine ⟨e.symm g, ?_, e.apply_symm_apply g⟩
    rw [mem_lowerRamificationGroupReal_iff_le_order,
      ← ramificationOrder_equivariant r e he, e.apply_symm_apply]
    exact (mem_lowerRamificationGroupReal_iff_le_order G' t g).mp hg

theorem card_lowerRamificationGroupReal_equivariant (t : ℝ) :
    Nat.card (lowerRamificationGroupReal G' (IsLocalRing.maximalIdeal S) t) =
      Nat.card (lowerRamificationGroupReal G (IsLocalRing.maximalIdeal R) t) := by
  rw [← lowerRamificationGroupReal_map_equivariant r e he t]
  exact Subgroup.card_map_of_injective e.injective

theorem herbrandFunction_equivariant (t : ℝ) :
    herbrandFunction (R := S) G' t = herbrandFunction (R := R) G t := by
  have hzero : Nat.card (lowerRamificationGroup G' (IsLocalRing.maximalIdeal S) 0) =
      Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0) := by
    simpa [lowerRamificationGroupReal] using card_lowerRamificationGroupReal_equivariant r e he 0
  simp only [herbrandFunction, hzero, card_lowerRamificationGroupReal_equivariant r e he]

variable [Finite G] [Finite G']

theorem inverseHerbrandFunction_equivariant {u : ℝ} (hu : -1 ≤ u) :
    inverseHerbrandFunction (R := S) G' u = inverseHerbrandFunction (R := R) G u := by
  apply (strictMonoOn_herbrandFunction (R := R) G).injOn
    (inverseHerbrandFunction_mem_Ici G' u) (inverseHerbrandFunction_mem_Ici G u)
  rw [← herbrandFunction_equivariant r e he,
    herbrandFunction_inverseHerbrandFunction G' hu,
    herbrandFunction_inverseHerbrandFunction G hu]

theorem upperRamificationGroup_map_equivariant {u : ℝ} (hu : -1 ≤ u) :
    (upperRamificationGroup (R := R) G u).map e.toMonoidHom =
      upperRamificationGroup (R := S) G' u := by
  rw [upperRamificationGroup, upperRamificationGroup,
    lowerRamificationGroupReal_map_equivariant r e he,
    inverseHerbrandFunction_equivariant r e he hu]

end RingEquiv

end FontaineWintenberger

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable {L M : Type*} [Field L] [Field M] [Algebra K L] [Algebra K M]
    [Algebra.IsAlgebraic K L] [Algebra.IsAlgebraic K M]

local notation "R₀" => Valuation.valuationSubring (NormedField.valuation (K := K))
local notation "OL" => spectralIntegerRing K L
local notation "OM" => spectralIntegerRing K M

/-- A field isomorphism restricts canonically to the actual spectral integer rings. -/
noncomputable def spectralIntegerRingEquiv (f : L ≃ₐ[K] M) : OL ≃ₐ[R₀] OM :=
  ((IsIntegralClosure.equiv R₀ OL L (integralClosure R₀ L)).trans
    (f.restrictScalars R₀).mapIntegralClosure).trans
      (IsIntegralClosure.equiv R₀ (integralClosure R₀ M) M OM)

@[simp]
theorem coe_spectralIntegerRingEquiv (f : L ≃ₐ[K] M) (x : OL) :
    ((spectralIntegerRingEquiv K f x : OM) : M) = f (x : L) := by
  unfold spectralIntegerRingEquiv
  simp only [AlgEquiv.trans_apply]
  rw [show ∀ y : integralClosure R₀ M,
    ((IsIntegralClosure.equiv R₀ (integralClosure R₀ M) M OM y : OM) : M) = (y : M) from
      IsIntegralClosure.algebraMap_equiv R₀ (integralClosure R₀ M) M OM]
  change f (((IsIntegralClosure.equiv R₀ OL L (integralClosure R₀ L)) x :
    integralClosure R₀ L) : L) = f (x : L)
  exact congrArg f (IsIntegralClosure.algebraMap_equiv R₀ OL L (integralClosure R₀ L) x)

/-- The integer-ring equivalence intertwines the original field actions under conjugation. -/
theorem spectralIntegerRingEquiv_smul (f : L ≃ₐ[K] M) (s : L ≃ₐ[K] L) (x : OL) :
    spectralIntegerRingEquiv K f (s • x) = f.autCongr s • spectralIntegerRingEquiv K f x := by
  apply Subtype.ext
  simp only [coe_spectralIntegerRingEquiv, coe_spectralIntegerRing_galois_smul,
    AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]

variable [FiniteDimensional K L] [FiniteDimensional K M]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable K M]

theorem spectralIntegerRingEquiv_addVal (f : L ≃ₐ[K] M) (x : OL) :
    IsDiscreteValuationRing.addVal OM (spectralIntegerRingEquiv K f x) =
      IsDiscreteValuationRing.addVal OL x :=
  addVal_ringEquiv (spectralIntegerRingEquiv K f).toRingEquiv x

theorem ramificationOrder_autCongr (f : L ≃ₐ[K] M) (s : L ≃ₐ[K] L) :
    ramificationOrder (R := OM) (M ≃ₐ[K] M) (f.autCongr s) =
      ramificationOrder (R := OL) (L ≃ₐ[K] L) s :=
  ramificationOrder_equivariant (spectralIntegerRingEquiv K f).toRingEquiv
    f.autCongr (spectralIntegerRingEquiv_smul K f) s

theorem herbrandFunction_autCongr (f : L ≃ₐ[K] M) (t : ℝ) :
    herbrandFunction (R := OM) (M ≃ₐ[K] M) t =
      herbrandFunction (R := OL) (L ≃ₐ[K] L) t :=
  herbrandFunction_equivariant (spectralIntegerRingEquiv K f).toRingEquiv
    f.autCongr (spectralIntegerRingEquiv_smul K f) t

theorem upperRamificationGroup_map_autCongr (f : L ≃ₐ[K] M) {u : ℝ} (hu : -1 ≤ u) :
    (upperRamificationGroup (R := OL) (L ≃ₐ[K] L) u).map f.autCongr.toMonoidHom =
      upperRamificationGroup (R := OM) (M ≃ₐ[K] M) u :=
  upperRamificationGroup_map_equivariant (spectralIntegerRingEquiv K f).toRingEquiv
    f.autCongr (spectralIntegerRingEquiv_smul K f) hu

end FontaineWintenberger

namespace FontaineWintenberger

section Tower

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (F L : Type*) [Field F] [Field L] [Algebra K F] [Algebra K L]
    [Algebra F L] [IsScalarTower K F L] [IsGalois K F] [IsGalois K L]
    [FiniteDimensional K F] [FiniteDimensional K L]
variable [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]

/-- Ordinary restriction preserves actual upper groups in every finite Galois field tower. -/
theorem restrictNormalHom_map_upperRamificationGroup_tower (u : ℝ) (hu : -1 ≤ u) :
    (upperRamificationGroup (R := spectralIntegerRing K L) (L ≃ₐ[K] L) u).map
      (AlgEquiv.restrictNormalHom F) =
        upperRamificationGroup (R := spectralIntegerRing K F) (F ≃ₐ[K] F) u := by
  let i := IsScalarTower.toAlgHom K F L
  let E := i.fieldRange
  let e : F ≃ₐ[K] E := i.equivFieldRange
  have : IsGalois K E := IsGalois.of_algEquiv e
  have hcomp : e.autCongr.toMonoidHom.comp
      (AlgEquiv.restrictNormalHom F : (L ≃ₐ[K] L) →* (F ≃ₐ[K] F)) =
        AlgEquiv.restrictNormalHom E := by
    ext s x
    obtain ⟨y, rfl⟩ := e.surjective x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
    change algebraMap F L (s.restrictNormal F y) =
      algebraMap E L (s.restrictNormal E (e y))
    rw [AlgEquiv.restrictNormal_commutes]
    exact (AlgEquiv.restrictNormal_commutes s E (e y)).symm
  apply Subgroup.map_injective (f := e.autCongr.toMonoidHom) e.autCongr.injective
  rw [Subgroup.map_map, hcomp, restrictNormalHom_map_upperRamificationGroup K L E u hu,
    upperRamificationGroup_map_autCongr K e hu]

end Tower

section FiniteIntermediateFields

open CategoryTheory Opposite

variable (K Ω : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [Field Ω] [Algebra K Ω]
variable [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]

/-- Mathlib's actual finite Galois transition maps preserve the actual upper groups. -/
theorem finGaloisGroupMap_map_upperRamificationGroup
    {A B : (FiniteGaloisIntermediateField K Ω)ᵒᵖ} (f : A ⟶ B)
    (u : ℝ) (hu : -1 ≤ u) :
    (upperRamificationGroup (R := spectralIntegerRing K A.unop) (A.unop ≃ₐ[K] A.unop) u).map
      (finGaloisGroupMap f).hom.hom =
        upperRamificationGroup (R := spectralIntegerRing K B.unop) (B.unop ≃ₐ[K] B.unop) u := by
  let : Algebra B.unop A.unop :=
    RingHom.toAlgebra (Subsemiring.inclusion (leOfHom f.1))
  have : IsScalarTower K B.unop A.unop := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  exact restrictNormalHom_map_upperRamificationGroup_tower K B.unop A.unop u hu

end FiniteIntermediateFields

end FontaineWintenberger
