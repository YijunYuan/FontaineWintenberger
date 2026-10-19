/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Galois.Action
public import FontaineWintenberger.FieldOfNorms.Relative.Hom
public import FontaineWintenberger.FieldOfNorms.Galois.RelAction

/-!
# The ambient Galois group of the relative field of norms

## The ambient Galois group and the original norm-union automorphism subgroup

The target is the actual subgroup of ring automorphisms of the same union
whose restriction to the actual base image is an original norm-field action.
Faithfulness gives a unique original base restriction; its kernel consists
of the actual base-algebra automorphisms.

Reference: Wintenberger, Remark 3.2.4.

## The original base automorphism selected by a norm-union automorphism

The checked subgroup membership theorem supplies an actual original base
automorphism and its exact square on the original norm field.

Reference: Wintenberger, Remark 3.2.4.

## The original base automorphism selected by a norm-union automorphism

The checked subgroup membership theorem supplies an actual original base
automorphism and its exact square on the original norm field.

Reference: Wintenberger, Remark 3.2.4.

## Relative automorphisms of the original norm union

Forgetting the base algebra gives a canonical homomorphism into the original
norm-union target subgroup.

Reference: Wintenberger, Remark 3.2.4.

## The original ambient Galois group of the relative field of norms

The actual same-union action identifies the original absolute Galois group
with the actual subgroup whose base restriction is an original norm-field action.
The restriction square and relative kernel comparison are retained literally.

Reference: Wintenberger, Remark 3.2.4.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : IntermediateField K (SeparableClosure K))
variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

local notation "Ω" => SeparableClosure K
local notation "X" => FieldOfNorms K L
local notation "U" => RelFieldOfNorms K L Ω
local notation "ι" => RelFieldOfNorms.baseHom K L Ω
local notation "ρ" => FieldOfNorms.aut K L

/-- The literal source target, inside ring automorphisms of the same union. -/
def RelFieldOfNorms.galoisSubgroup :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    Subgroup (RingAut U) := by
  letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  exact
    { carrier := {β | ∃ σ : L ≃ₐ[K] L, ∀ x : X, β (ι x) = ι (ρ σ x)}
      one_mem' := by
        refine ⟨1, ?_⟩
        intro x
        change ι x = ι ((ρ) 1 x)
        rw [(ρ).map_one]
        rfl
      mul_mem' := by
        rintro β γ ⟨σ, hσ⟩ ⟨τ, hτ⟩
        refine ⟨σ * τ, ?_⟩
        intro x
        change β (γ (ι x)) = ι (ρ (σ * τ) x)
        rw [hτ, hσ, map_mul]
        rfl
      inv_mem' := by
        rintro β ⟨σ, hσ⟩
        refine ⟨σ⁻¹, ?_⟩
        intro x
        apply β.injective
        change β (β.symm (ι x)) = β (ι (ρ (σ⁻¹) x))
        rw [β.apply_symm_apply, hσ, map_inv]
        change ι x = ι ((ρ σ) ((ρ σ).symm x))
        rw [RingEquiv.apply_symm_apply] }

/-- Membership means an actual commuting square with an original automorphism. -/
theorem mem_relFieldOfNormsGaloisSubgroup :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    ∀ β : RingAut U, β ∈ RelFieldOfNorms.galoisSubgroup K L ↔
      ∃ σ : L ≃ₐ[K] L, ∀ x : X, β (ι x) = ι (ρ σ x) := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  intro β
  rfl

/-- The base square determines its original automorphism uniquely. -/
theorem RelFieldOfNorms.galoisSubgroup_base_unique :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    ∀ (β : RingAut U) (σ τ : L ≃ₐ[K] L),
      (∀ x : X, β (ι x) = ι (ρ σ x)) →
      (∀ x : X, β (ι x) = ι (ρ τ x)) → σ = τ := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  intro β σ τ hσ hτ
  apply FieldOfNorms.aut_injective K L
  apply RingEquiv.ext
  intro x
  apply (ι).injective
  exact (hσ x).symm.trans (hτ x)

/-- The existential square is exactly preservation of the actual base image
and membership of its transported restriction in the actual action image. -/
theorem mem_relFieldOfNormsGaloisSubgroup_iff_stable_image :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    ∀ β : RingAut U, β ∈ RelFieldOfNorms.galoisSubgroup K L ↔
      β '' Set.range ι = Set.range ι ∧
        ∃ a ∈ (ρ).range, ∀ x : X, β (ι x) = ι (a x) := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  intro β
  rw [mem_relFieldOfNormsGaloisSubgroup]
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨?_, ρ σ, ⟨σ, rfl⟩, hσ⟩
    apply Set.Subset.antisymm
    · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨ρ σ x, (hσ x).symm⟩
    · rintro _ ⟨x, rfl⟩
      refine ⟨ι ((ρ σ).symm x), ⟨_, rfl⟩, ?_⟩
      rw [hσ, RingEquiv.apply_symm_apply]
  · rintro ⟨_, a, ⟨σ, rfl⟩, ha⟩
    exact ⟨σ, ha⟩

end FontaineWintenberger

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : IntermediateField K (SeparableClosure K))
variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

local notation "Ω" => SeparableClosure K
local notation "X" => FieldOfNorms K L
local notation "U" => RelFieldOfNorms K L Ω
local notation "ι" => RelFieldOfNorms.baseHom K L Ω
local notation "ρ" => FieldOfNorms.aut K L

local notation "S" => RelFieldOfNorms.galoisSubgroup K L

/-- The original automorphism supplied by the actual subgroup membership theorem. -/
def RelFieldOfNorms.galoisRestrictionFun (β : S) : L ≃ₐ[K] L :=
  Classical.choose ((mem_relFieldOfNormsGaloisSubgroup K L β.val).mp β.property)

/-- The chosen original automorphism has the actual base square on every element. -/
theorem RelFieldOfNorms.galoisRestrictionFun_base :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    ∀ (β : S) (x : X), β.val (ι x) =
      ι (ρ (RelFieldOfNorms.galoisRestrictionFun K L β) x) := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  intro β x
  exact Classical.choose_spec
    ((mem_relFieldOfNormsGaloisSubgroup K L β.val).mp β.property) x

end FontaineWintenberger

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : IntermediateField K (SeparableClosure K))
variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

local notation "Ω" => SeparableClosure K
local notation "X" => FieldOfNorms K L
local notation "U" => RelFieldOfNorms K L Ω
local notation "ι" => RelFieldOfNorms.baseHom K L Ω
local notation "ρ" => FieldOfNorms.aut K L

local notation "S" => RelFieldOfNorms.galoisSubgroup K L

local notation "f" => RelFieldOfNorms.galoisRestrictionFun K L

/-- The actual restriction preserves multiplication in the canonical
homomorphism domain structure. -/
theorem RelFieldOfNorms.galoisRestrictionFun_mul :
    let : Mul S := (inferInstance : MulOne S).toMul
    ∀ β γ : S, f (β * γ) = f β * f γ := by
  let : Mul S := (inferInstance : MulOne S).toMul
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  dsimp only
  intro β γ
  apply RelFieldOfNorms.galoisSubgroup_base_unique K L
    (β * γ).val (f (β * γ)) (f β * f γ)
    (RelFieldOfNorms.galoisRestrictionFun_base K L (β * γ))
  intro x
  calc
    (β * γ).val (ι x) = β.val (γ.val (ι x)) :=
      congrArg (fun a => a (ι x)) ((Subgroup.subtype S).map_mul β γ)
    _ = ι (ρ (f β) (ρ (f γ) x)) :=
      (congrArg β.val (RelFieldOfNorms.galoisRestrictionFun_base K L γ x)).trans
        (RelFieldOfNorms.galoisRestrictionFun_base K L β (ρ (f γ) x))
    _ = ι (ρ (f β * f γ) x) := by
      rw [(ρ).map_mul]
      rfl

/-- The actual original base restriction, as a group homomorphism. -/
def RelFieldOfNorms.galoisRestriction : S →* (L ≃ₐ[K] L) :=
  MonoidHom.mk' f (RelFieldOfNorms.galoisRestrictionFun_mul K L)

local notation "r" => RelFieldOfNorms.galoisRestriction K L

/-- The restriction retains the actual base square on every element. -/
theorem RelFieldOfNorms.galoisRestriction_base :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    ∀ (β : S) (x : X), β.val (ι x) = ι (ρ (r β) x) := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  intro β x
  exact RelFieldOfNorms.galoisRestrictionFun_base K L β x

/-- The original automorphism is determined by its genuine base square. -/
theorem RelFieldOfNorms.galoisRestriction_eq_iff :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    ∀ (β : S) (σ : L ≃ₐ[K] L), r β = σ ↔
      ∀ x : X, β.val (ι x) = ι (ρ σ x) := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  intro β σ
  constructor
  · rintro rfl
    exact RelFieldOfNorms.galoisRestriction_base K L β
  · intro hσ
    exact RelFieldOfNorms.galoisSubgroup_base_unique K L β.val (r β) σ
      (RelFieldOfNorms.galoisRestriction_base K L β) hσ

/-- The kernel consists exactly of automorphisms fixing the actual base pointwise. -/
theorem mem_relFieldOfNormsGaloisRestriction_ker_iff :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    ∀ β : S, β ∈ (r).ker ↔ ∀ x : X, β.val (ι x) = ι x := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  intro β
  rw [MonoidHom.mem_ker, RelFieldOfNorms.galoisRestriction_eq_iff]
  simp only [map_one, RingAut.one_apply]

end FontaineWintenberger

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : IntermediateField K (SeparableClosure K))
variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

local notation "Ω" => SeparableClosure K
local notation "X" => FieldOfNorms K L
local notation "U" => RelFieldOfNorms K L Ω
local notation "ι" => RelFieldOfNorms.baseHom K L Ω
local notation "ρ" => FieldOfNorms.aut K L

local notation "S" => RelFieldOfNorms.galoisSubgroup K L

local notation "r" => RelFieldOfNorms.galoisRestriction K L

/-- Forgetting the base algebra gives an actual member of the source target. -/
def RelFieldOfNorms.galoisRelativeHom :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    (U ≃ₐ[X] U) →* S := by
  letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  exact
    (MulSemiringAction.toRingEquiv (U ≃ₐ[X] U) U).codRestrict S fun β => by
      apply (mem_relFieldOfNormsGaloisSubgroup K L β.toRingEquiv).mpr
      refine ⟨1, ?_⟩
      intro x
      change β (ι x) = ι ((ρ) 1 x)
      rw [(ρ).map_one]
      exact β.commutes x

/-- The canonical forgetful map is injective, retaining the actual ring automorphism. -/
theorem RelFieldOfNorms.galoisRelativeHom_injective :
    Function.Injective (RelFieldOfNorms.galoisRelativeHom K L) := by
  intro β γ h
  exact DFunLike.ext β γ fun z => congrArg (fun η : S => η.val z) h

/-- Actual base-algebra automorphisms have trivial original base restriction. -/
theorem RelFieldOfNorms.galoisRelativeHom_mem_ker :
    ∀ β, RelFieldOfNorms.galoisRelativeHom K L β ∈ (r).ker := by
  intro β
  apply (mem_relFieldOfNormsGaloisRestriction_ker_iff K L _).mpr
  cases β
  assumption

/-- Every genuine kernel element is induced by a base-algebra automorphism. -/
theorem RelFieldOfNorms.galoisRelativeHom_surjective_ker :
    Function.Surjective
      ((RelFieldOfNorms.galoisRelativeHom K L).codRestrict (r).ker
        (RelFieldOfNorms.galoisRelativeHom_mem_ker K L)) := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  intro β
  have hfix := (mem_relFieldOfNormsGaloisRestriction_ker_iff K L β.val).mp
    β.property
  refine ⟨{ β.val.val with commutes' := hfix }, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply DFunLike.ext
  intro z
  rfl

/-- The relative algebra automorphism group is precisely the genuine kernel. -/
def RelFieldOfNorms.galoisRelativeKernelEquiv :=
  MulEquiv.ofBijective
    ((RelFieldOfNorms.galoisRelativeHom K L).codRestrict (r).ker
      (RelFieldOfNorms.galoisRelativeHom_mem_ker K L))
    ⟨(MonoidHom.injective_codRestrict
        (RelFieldOfNorms.galoisRelativeHom K L) (r).ker
        (RelFieldOfNorms.galoisRelativeHom_mem_ker K L)).mpr
        (RelFieldOfNorms.galoisRelativeHom_injective K L),
      RelFieldOfNorms.galoisRelativeHom_surjective_ker K L⟩

/-- The canonical kernel comparison retains the same underlying automorphism. -/
theorem RelFieldOfNorms.galoisRelativeKernelEquiv_apply :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    ∀ β, (RelFieldOfNorms.galoisRelativeKernelEquiv K L β).val.val =
      β.toRingEquiv := by
  intro β
  apply DFunLike.ext
  intro z
  rfl

/-- The original relative Galois group identifies with that same actual kernel. -/
def RelFieldOfNorms.galoisKernelEquiv :=
  letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  letI : Semiring Ω :=
    @CommSemiring.toSemiring Ω
      (@Semifield.toCommSemiring Ω
        (@Field.toSemifield Ω (separableClosure K (AlgebraicClosure K)).toField))
  (RelFieldOfNorms.autEquiv K L Ω).trans
    (RelFieldOfNorms.galoisRelativeKernelEquiv K L)

/-- The relative-kernel equivalence is the original union map on every element. -/
theorem RelFieldOfNorms.galoisKernelEquiv_apply :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    letI : Semiring Ω :=
      @CommSemiring.toSemiring Ω
        (@Semifield.toCommSemiring Ω
          (@Field.toSemifield Ω (separableClosure K (AlgebraicClosure K)).toField))
    ∀ σ z, (RelFieldOfNorms.galoisKernelEquiv K L σ).val.val z =
      RelFieldOfNorms.map K L Ω Ω σ.toAlgHom z := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  let : Semiring Ω :=
    @CommSemiring.toSemiring Ω
      (@Semifield.toCommSemiring Ω
        (@Field.toSemifield Ω (separableClosure K (AlgebraicClosure K)).toField))
  intro σ z
  have h := RelFieldOfNorms.galoisRelativeKernelEquiv_apply K L
    (RelFieldOfNorms.autEquiv K L Ω σ)
  exact (DFunLike.congr_fun h z).trans
    (RelFieldOfNorms.autEquiv_apply K L Ω σ z)

end FontaineWintenberger

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : IntermediateField K (SeparableClosure K)) [Normal K L]
variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

local notation "Ω" => SeparableClosure K
local notation "X" => FieldOfNorms K L
local notation "U" => RelFieldOfNorms K L Ω
local notation "ι" => RelFieldOfNorms.baseHom K L Ω
local notation "ρ" => FieldOfNorms.aut K L
local notation "S" => RelFieldOfNorms.galoisSubgroup K L
local notation "A" => RelFieldOfNorms.absoluteAut K L
local notation "r" => RelFieldOfNorms.galoisRestriction K L
local notation "κ" => RelFieldOfNorms.galoisKernelEquiv K L

/-- The actual ambient action takes values in the original semilinear subgroup. -/
def RelFieldOfNorms.ambientGaloisHom :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    (Ω ≃ₐ[K] Ω) →* S := by
  letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  refine (A).codRestrict S ?_
  intro σ
  apply (mem_relFieldOfNormsGaloisSubgroup K L (A σ)).mpr
  refine ⟨AlgEquiv.restrictNormalHom L σ, ?_⟩
  intro x
  simpa only [FieldOfNorms.absoluteAut_apply] using
    (RelFieldOfNorms.absoluteAut_base K L σ x)

local notation "Φ" => RelFieldOfNorms.ambientGaloisHom K L

/-- The subgroup-valued homomorphism retains the original action on every union element. -/
theorem RelFieldOfNorms.ambientGaloisHom_apply :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    ∀ (σ : Ω ≃ₐ[K] Ω) (z : U), (Φ σ).val z = A σ z := by
  intro σ z
  rfl

/-- Its actual base restriction is ordinary Galois restriction. -/
theorem RelFieldOfNorms.ambientGaloisHom_restriction :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    ∀ σ : Ω ≃ₐ[K] Ω, r (Φ σ) = AlgEquiv.restrictNormalHom L σ := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  intro σ
  apply (RelFieldOfNorms.galoisRestriction_eq_iff K L _ _).mpr
  intro x
  change A σ (ι x) = ι (FieldOfNorms.absoluteAut K L σ x)
  exact RelFieldOfNorms.absoluteAut_base K L σ x

/-- On the original relative Galois subgroup it is exactly the proved kernel correspondence. -/
theorem RelFieldOfNorms.ambientGaloisHom_relative :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    ∀ (τ :
      letI : Semiring Ω :=
        @CommSemiring.toSemiring Ω
          (@Semifield.toCommSemiring Ω
            (@Field.toSemifield Ω (separableClosure K (AlgebraicClosure K)).toField))
      Ω ≃ₐ[L] Ω),
      Φ (τ.restrictScalars K) = (κ τ).val := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  intro τ
  apply Subtype.ext
  apply RingEquiv.ext
  intro z
  change A (τ.restrictScalars K) z = (κ τ).val.val z
  exact (RelFieldOfNorms.absoluteAut_restrictScalars K L τ z).trans
    (RelFieldOfNorms.galoisKernelEquiv_apply K L τ z).symm

/-- The actual ambient action is faithful on the same union. -/
theorem RelFieldOfNorms.ambientGaloisHom_injective :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    Function.Injective (Φ) := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  apply (injective_iff_map_eq_one (Φ)).mpr
  intro σ hσ
  have hr : AlgEquiv.restrictNormalHom L σ = 1 := by
    rw [← RelFieldOfNorms.ambientGaloisHom_restriction K L σ, hσ, map_one]
  have hfix : σ ∈ L.fixingSubgroup := by
    rw [← L.restrictNormalHom_ker]
    exact hr
  let τ := L.fixingSubgroupEquiv ⟨σ, hfix⟩
  have ht : τ.restrictScalars K = σ := by
    apply AlgEquiv.ext
    intro z
    rfl
  have hk : (κ τ).val = 1 :=
    (RelFieldOfNorms.ambientGaloisHom_relative K L τ).symm.trans
      ((congrArg (Φ) ht).trans hσ)
  have hk_mem : κ τ = 1 := Subtype.ext hk
  have hτ : τ = 1 := (κ).injective (hk_mem.trans (κ).map_one.symm)
  have hτK : τ.restrictScalars K = 1 := by
    rw [hτ]
    rfl
  exact ht.symm.trans hτK

/-- Every automorphism with original base restriction is an actual ambient Galois action. -/
theorem RelFieldOfNorms.ambientGaloisHom_surjective :
    Function.Surjective (RelFieldOfNorms.ambientGaloisHom K L) := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  intro β
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective
    (F := K) (K₁ := L) Ω (r β)
  let δ : S := β * (Φ σ)⁻¹
  have hδ : δ ∈ (r).ker := by
    change r δ = 1
    simp only [δ, map_mul, map_inv,
      RelFieldOfNorms.ambientGaloisHom_restriction K L, hσ, mul_inv_cancel]
  let d : (r).ker := ⟨δ, hδ⟩
  obtain ⟨τ, hτ⟩ := (κ).surjective d
  have hrel : Φ (τ.restrictScalars K) = δ :=
    (RelFieldOfNorms.ambientGaloisHom_relative K L τ).trans
      (congrArg Subtype.val hτ)
  refine ⟨τ.restrictScalars K * σ, ?_⟩
  exact ((Φ).map_mul (τ.restrictScalars K) σ).trans
    ((congrArg (fun z : S => z * Φ σ) hrel).trans (inv_mul_cancel_right β (Φ σ)))

/-- Wintenberger’s actual ambient Galois group isomorphism for the original union. -/
def RelFieldOfNorms.ambientGaloisEquiv :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    (Ω ≃ₐ[K] Ω) ≃* S := by
  letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  exact MulEquiv.ofBijective (Φ)
    ⟨RelFieldOfNorms.ambientGaloisHom_injective K L,
      RelFieldOfNorms.ambientGaloisHom_surjective K L⟩

/-- The final group isomorphism is the literal original same-union action. -/
theorem RelFieldOfNorms.ambientGaloisEquiv_apply :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    ∀ (σ : Ω ≃ₐ[K] Ω) (z : U),
      (RelFieldOfNorms.ambientGaloisEquiv K L σ).val z = A σ z := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  intro σ z
  rfl

end FontaineWintenberger
