/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.FieldOfNorms.Estimates.Transfer
public import FontaineWintenberger.FieldOfNorms.Layers.GaloisGood
public import FontaineWintenberger.Ramification.Upper.Order

/-!
# Ramification on finite Galois extensions of the field of norms

Ramification transfer can be made simultaneous for the finite relative Galois group.
Consequently the group and its ramification numbers descend to one stable good finite layer.
All larger finite layers retain the same ramification numbers.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, Proposition 3.3.2 and the proof of Corollary 3.3.6.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]
variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- The action on the field of norms restricts to a group action on its valuation ring. -/
def FieldOfNorms.integerAutHom :
    (L ≃ₐ[K] L) →* RingAut (FieldOfNorms.fieldValuation K L).valuationSubring where
  toFun := FieldOfNorms.integerAut K L
  map_one' := by
    apply RingEquiv.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun f : RingAut (FieldOfNorms K L) ↦ f x) (map_one (FieldOfNorms.aut K L))
  map_mul' σ τ := by
    apply RingEquiv.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun f : RingAut (FieldOfNorms K L) ↦ f x)
      (map_mul (FieldOfNorms.aut K L) σ τ)

/-- A finite family of automorphisms has a common tail on which all ramification numbers
agree with their intrinsic field-of-norms ramification numbers. -/
theorem exists_finiteIntermediateField_forall_ramificationNumber_eq
    {ι : Type*} [Finite ι] (σ : ι → L ≃ₐ[K] L) :
    ∃ E : FiniteIntermediateField K L, ∀ F : FiniteIntermediateField K L, E ≤ F →
      ∀ i, FiniteIntermediateField.ramificationNumber K L (σ i) F =
        FieldOfNorms.ramificationNumber K L (σ i) := by
  choose E hE using fun i ↦ exists_finiteIntermediateField_ramificationNumber_eq K L (σ i)
  obtain ⟨D, hD⟩ := Finite.exists_le E
  exact ⟨D, fun F hDF i ↦ hE i F ((hD i).trans hDF)⟩

variable (N : Type*) [Field N] [Algebra K N] [Algebra L N] [IsScalarTower K L N]
variable [Module.Finite L N] [IsGalois L N] [Algebra.IsSeparable K N]
variable [IsAPF K N] [Fact (¬ Module.Finite K N)]

/-- The relative Galois action on the integer ring of the field of norms. -/
@[instance_reducible]
def FieldOfNorms.integerGaloisAction :
    MulSemiringAction (N ≃ₐ[L] N) (FieldOfNorms.fieldValuation K N).valuationSubring :=
  MulSemiringAction.compHom _
    ((FieldOfNorms.integerAutHom K N).comp (AlgEquiv.restrictScalarsHom K))

/-- The integer action is the restriction of the existing norm-field Galois
correspondence to its valuation ring. -/
theorem FieldOfNorms.coe_integerGaloisAction_smul
    (σ : N ≃ₐ[L] N) (x : (FieldOfNorms.fieldValuation K N).valuationSubring) :
    letI := (FieldOfNorms.inclusion K L N).toAlgebra
    letI := FieldOfNorms.integerGaloisAction K L N
    ((σ • x : (FieldOfNorms.fieldValuation K N).valuationSubring) : FieldOfNorms K N) =
      FieldOfNorms.autEquiv K L N σ x := rfl

/-- Upper ramification of the finite relative Galois group, computed on its field of norms.
The action is the one identified with the norm-field Galois group by
`FieldOfNorms.autEquiv`. -/
def FieldOfNorms.upperRamificationGroup (u : ℝ) : Subgroup (N ≃ₐ[L] N) :=
  letI := FieldOfNorms.integerGaloisAction K L N
  FontaineWintenberger.upperRamificationGroup
    (R := (FieldOfNorms.fieldValuation K N).valuationSubring) (N ≃ₐ[L] N) u

omit [Algebra.IsSeparable K L] [IsAPF K L] [Fact (¬ Module.Finite K L)] in
/-- A finite Galois extension descends above any prescribed finite layer, with every
ramification number preserved simultaneously. The good-layer condition states that the
canonical tensor map is an isomorphism. -/
theorem exists_galois_stable_goodFiniteLayer_ramificationNumber_eq
    (E : FiniteIntermediateField K N) :
    ∃ D : FiniteIntermediateField K N, E ≤ D ∧ IsGoodFiniteLayer K L D ∧
      (∀ σ : N ≃ₐ[L] N, D.val.map (σ.restrictScalars K).toAlgHom = D.val) ∧
      (∃ α : N, α ∈ D.val ∧ IntermediateField.adjoin L {α} = ⊤) ∧
      ∀ F : FiniteIntermediateField K N, D ≤ F → ∀ σ : N ≃ₐ[L] N,
        FiniteIntermediateField.ramificationNumber K N (σ.restrictScalars K) F =
          FieldOfNorms.ramificationNumber K N (σ.restrictScalars K) := by
  obtain ⟨A, hA⟩ := exists_finiteIntermediateField_forall_ramificationNumber_eq K N
    (fun σ : N ≃ₐ[L] N ↦ σ.restrictScalars K)
  obtain ⟨D, hD, hg, hs, hα⟩ := exists_galois_stable_goodFiniteLayer_ge K L N
    (FiniteIntermediateField.sup E A)
  exact ⟨D, (FiniteIntermediateField.le_sup_left E A).trans hD, hg, hs, hα,
    fun F hDF σ ↦ hA F (((FiniteIntermediateField.le_sup_right E A).trans hD).trans hDF) σ⟩

/-- The relative Galois group acts on the spectral integers of a stable finite layer. -/
@[instance_reducible]
def galoisFiniteLayerIntegerAction (D : FiniteIntermediateField K N)
    (hD : ∀ σ : N ≃ₐ[L] N, D.val.map (σ.restrictScalars K).toAlgHom = D.val) :
    MulSemiringAction (N ≃ₐ[L] N) (spectralIntegerRing K D.val) :=
  MulSemiringAction.compHom _ ((AlgEquiv.restrictScalarsHom K).comp
    (galoisFiniteLayerRestrict K L N D hD))

omit [Algebra.IsSeparable K L] [IsAPF K L] [Fact (¬ Module.Finite K L)]
    [Module.Finite L N] [IsGalois L N] in
/-- Simultaneous transfer identifies the displacement orders on the finite layer and the
norm field, for their actions of the same relative Galois group. -/
theorem galoisFiniteLayer_ramificationOrder_eq (D : FiniteIntermediateField K N)
    (hD : ∀ σ : N ≃ₐ[L] N, D.val.map (σ.restrictScalars K).toAlgHom = D.val)
    (h : ∀ σ : N ≃ₐ[L] N,
      FiniteIntermediateField.ramificationNumber K N (σ.restrictScalars K) D =
        FieldOfNorms.ramificationNumber K N (σ.restrictScalars K))
    (σ : N ≃ₐ[L] N) :
    letI := galoisFiniteLayerIntegerAction K L N D hD
    letI := FieldOfNorms.integerGaloisAction K L N
    ramificationOrder (R := spectralIntegerRing K D.val) (N ≃ₐ[L] N) σ =
      ramificationOrder (R := (FieldOfNorms.fieldValuation K N).valuationSubring)
        (N ≃ₐ[L] N) σ := by
  let := galoisFiniteLayerIntegerAction K L N D hD
  let := FieldOfNorms.integerGaloisAction K L N
  have he := (FiniteIntermediateField.ramificationNumber_eq_aut K N
    (σ.restrictScalars K) D
    ((galoisFiniteLayerRestrict K L N D hD σ).restrictScalars K) (fun _ ↦ rfl)).symm.trans (h σ)
  have he' := congrArg (fun x : EReal ↦ x + (1 : ℝ)) he
  simp only [FieldOfNorms.ramificationNumber, ← EReal.coe_one, EReal.sub_add_cancel] at he'
  exact ENat.toENNReal_inj.mp (EReal.coe_ennreal_injective he')

omit [Algebra.IsSeparable K L] [IsAPF K L] [Fact (¬ Module.Finite K L)] [IsGalois L N] in
/-- The ramification-preserving finite descent identifies the upper filtrations at every
parameter. This compares their intrinsic Herbrand constructions. -/
theorem galoisFiniteLayer_upperRamificationGroup_eq (D : FiniteIntermediateField K N)
    (hD : ∀ σ : N ≃ₐ[L] N, D.val.map (σ.restrictScalars K).toAlgHom = D.val)
    (h : ∀ σ : N ≃ₐ[L] N,
      FiniteIntermediateField.ramificationNumber K N (σ.restrictScalars K) D =
        FieldOfNorms.ramificationNumber K N (σ.restrictScalars K))
    {u : ℝ} (hu : -1 ≤ u) :
    letI := galoisFiniteLayerIntegerAction K L N D hD
    upperRamificationGroup (R := spectralIntegerRing K D.val) (N ≃ₐ[L] N) u =
      FieldOfNorms.upperRamificationGroup K L N u := by
  let := galoisFiniteLayerIntegerAction K L N D hD
  let := FieldOfNorms.integerGaloisAction K L N
  exact upperRamificationGroup_eq_of_order_eq (N ≃ₐ[L] N)
    (galoisFiniteLayer_ramificationOrder_eq K L N D hD h) hu

omit [IsAPF K L] [Fact (¬ Module.Finite K L)] [IsAPF K N]
    [Fact (¬ Module.Finite K N)] [Algebra.IsSeparable K L] [Algebra.IsSeparable K N]
    [IsPerfectResidueLocalField K] in
/-- A stable finite layer is Galois over its intersection with the relative base field. -/
theorem isGalois_galoisStableFiniteLayer (D : FiniteIntermediateField K N)
    (hD : ∀ σ : N ≃ₐ[L] N, D.val.map (σ.restrictScalars K).toAlgHom = D.val) :
    IsGalois (FiniteIntermediateField.pullback K L D) D.val := by
  apply IsGalois.of_fixedField_eq_bot
  apply bot_unique
  exact (IntermediateField.fixedField_le (show
    (galoisFiniteLayerRestrict K L N D hD).range ≤ ⊤ from le_top)).trans_eq
      (galoisFiniteLayerRestrict_fixedField K L N D hD)

omit [IsAPF K L] [Fact (¬ Module.Finite K L)] [IsAPF K N]
    [Fact (¬ Module.Finite K N)] [Algebra.IsSeparable K L] [Algebra.IsSeparable K N]
    [IsPerfectResidueLocalField K] in
/-- On a stable layer containing a primitive element, relative restriction is a bijection. -/
theorem galoisFiniteLayerRestrict_bijective (D : FiniteIntermediateField K N)
    (hD : ∀ σ : N ≃ₐ[L] N, D.val.map (σ.restrictScalars K).toAlgHom = D.val)
    (α : N) (hα : IntermediateField.adjoin L {α} = ⊤) (hαD : α ∈ D.val) :
    Function.Bijective (galoisFiniteLayerRestrict K L N D hD) := by
  let := isGalois_galoisStableFiniteLayer K L N D hD
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨galoisFiniteLayerRestrict_injective K L N D hD α hα hαD, ?_⟩
  rw [IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank,
    finrank_galois_stableFiniteLayer K L N D hD α hα hαD]

/-- Restriction identifies the finite relative Galois group with the Galois group of a
stable good descent layer. -/
def galoisFiniteLayerEquiv (D : FiniteIntermediateField K N)
    (hD : ∀ σ : N ≃ₐ[L] N, D.val.map (σ.restrictScalars K).toAlgHom = D.val)
    (α : N) (hα : IntermediateField.adjoin L {α} = ⊤) (hαD : α ∈ D.val) :
    (N ≃ₐ[L] N) ≃* (D.val ≃ₐ[FiniteIntermediateField.pullback K L D] D.val) :=
  MulEquiv.ofBijective (galoisFiniteLayerRestrict K L N D hD)
    (galoisFiniteLayerRestrict_bijective K L N D hD α hα hαD)

omit [Algebra.IsSeparable K L] [IsAPF K L] [Fact (¬ Module.Finite K L)] in
/-- A ramification-preserving descent identifies the upper groups under the ordinary
Galois restriction isomorphism. -/
theorem galoisFiniteLayerEquiv_map_upperRamificationGroup
    (D : FiniteIntermediateField K N)
    (hD : ∀ σ : N ≃ₐ[L] N, D.val.map (σ.restrictScalars K).toAlgHom = D.val)
    (α : N) (hα : IntermediateField.adjoin L {α} = ⊤) (hαD : α ∈ D.val)
    (h : ∀ σ : N ≃ₐ[L] N,
      FiniteIntermediateField.ramificationNumber K N (σ.restrictScalars K) D =
        FieldOfNorms.ramificationNumber K N (σ.restrictScalars K))
    {u : ℝ} (hu : -1 ≤ u) :
    letI := MulSemiringAction.compHom (spectralIntegerRing K D.val)
      (AlgEquiv.restrictScalarsHom K
        (S := FiniteIntermediateField.pullback K L D) (A := D.val))
    (FieldOfNorms.upperRamificationGroup K L N u).map
        (galoisFiniteLayerEquiv K L N D hD α hα hαD).toMonoidHom =
      upperRamificationGroup (R := spectralIntegerRing K D.val)
        (D.val ≃ₐ[FiniteIntermediateField.pullback K L D] D.val) u := by
  let := MulSemiringAction.compHom (spectralIntegerRing K D.val)
    (AlgEquiv.restrictScalarsHom K
      (S := FiniteIntermediateField.pullback K L D) (A := D.val))
  let := galoisFiniteLayerIntegerAction K L N D hD
  rw [← galoisFiniteLayer_upperRamificationGroup_eq K L N D hD h hu]
  exact upperRamificationGroup_map_mulEquiv (galoisFiniteLayerEquiv K L N D hD α hα hαD)
    (fun _ _ ↦ rfl) hu

omit [Algebra.IsSeparable K L] [IsAPF K L] [Fact (¬ Module.Finite K L)] in
/-- Above any prescribed finite field there is a Galois descent layer whose intrinsic
upper filtration agrees with that on the field of norms, at all upper parameters. -/
theorem exists_galois_stable_goodFiniteLayer_upperRamificationGroup_eq
    (E : FiniteIntermediateField K N) :
    ∃ (D : FiniteIntermediateField K N), E ≤ D ∧ IsGoodFiniteLayer K L D ∧
      ∃ hD : ∀ σ : N ≃ₐ[L] N, D.val.map (σ.restrictScalars K).toAlgHom = D.val,
        ∃ α : N, ∃ hα : IntermediateField.adjoin L {α} = ⊤, ∃ hαD : α ∈ D.val,
          ∀ u : ℝ, -1 ≤ u →
            letI := MulSemiringAction.compHom (spectralIntegerRing K D.val)
              (AlgEquiv.restrictScalarsHom K
                (S := FiniteIntermediateField.pullback K L D) (A := D.val))
            (FieldOfNorms.upperRamificationGroup K L N u).map
                (galoisFiniteLayerEquiv K L N D hD α hα hαD).toMonoidHom =
              upperRamificationGroup (R := spectralIntegerRing K D.val)
                (D.val ≃ₐ[FiniteIntermediateField.pullback K L D] D.val) u := by
  obtain ⟨D, hED, hg, hD, ⟨α, hαD, hα⟩, hr⟩ :=
    exists_galois_stable_goodFiniteLayer_ramificationNumber_eq K L N E
  exact ⟨D, hED, hg, hD, α, hα, hαD, fun _ hu ↦
    galoisFiniteLayerEquiv_map_upperRamificationGroup K L N D hD α hα hαD (hr D le_rfl) hu⟩

end FontaineWintenberger
