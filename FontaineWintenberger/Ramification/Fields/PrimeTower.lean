/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Mathlib.FieldTheory.RelIndex
public import FontaineWintenberger.Ramification.Lower.Wild
public import FontaineWintenberger.Ramification.Lower.GaloisGroup
public import FontaineWintenberger.LocalField.Spectral.FiniteExtension

/-!
# Actual cyclic prime-degree intermediate-field towers

Normal prime-index steps in the actual fixing groups become genuine cyclic
prime-degree field extensions through Galois correspondence.
-/

@[expose] public section

namespace FontaineWintenberger

section Fields

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

omit [FiniteDimensional K L] in
/-- Relative normality of the actual fixing groups makes the actual
intermediate-field extension Galois. -/
theorem isGalois_extendScalars_of_fixing_normal (M N : IntermediateField K L) (hMN : M ≤ N)
    (hn : (N.fixingSubgroup.subgroupOf M.fixingSubgroup).Normal) :
    IsGalois M (IntermediateField.extendScalars hMN) := by
  have hfix : (N.fixingSubgroup.subgroupOf M.fixingSubgroup).comap
      M.fixingSubgroupEquiv.symm.toMonoidHom =
        (IntermediateField.extendScalars hMN).fixingSubgroup := by
    ext g
    rfl
  apply (InfiniteGalois.normal_iff_isGalois (IntermediateField.extendScalars hMN)).mp
  rw [← hfix]
  let := hn
  infer_instance

/-- A normal prime-index fixing-group step supplies the actual Galois and
cyclic field step with its actual relative degree. -/
theorem cyclic_prime_extendScalars_of_fixing_step (p : ℕ) [Fact p.Prime]
    (M N : IntermediateField K L) (hMN : M ≤ N)
    (hn : (N.fixingSubgroup.subgroupOf M.fixingSubgroup).Normal)
    (hi : (N.fixingSubgroup.subgroupOf M.fixingSubgroup).index = p) :
    IsGalois M (IntermediateField.extendScalars hMN) ∧
      Module.finrank M (IntermediateField.extendScalars hMN) = p ∧
      IsCyclic ((IntermediateField.extendScalars hMN) ≃ₐ[M]
        IntermediateField.extendScalars hMN) := by
  have hg := isGalois_extendScalars_of_fixing_normal K L M N hMN hn
  let := hg
  have hd : Module.finrank M (IntermediateField.extendScalars hMN) = p := by
    rw [← fixingSubgroup_relIndex_eq_finrank K M N hMN]
    exact hi
  refine ⟨hg, hd, ?_⟩
  apply isCyclic_of_card_dvd_prime (p := p)
  rw [IsGalois.card_aut_eq_finrank, hd]

/-- The actual intermediate fields over a p-group fixing field have a finite
tower whose actual relative extensions are cyclic Galois of prime degree. -/
theorem relative_prime_field_chain (p : ℕ) [Fact p.Prime]
    (E M : IntermediateField K L) (hEM : E ≤ M) (hE : IsPGroup p E.fixingSubgroup) :
    Relation.ReflTransGen
      (fun A B : IntermediateField K L => ∃ hAB : A ≤ B,
        IsGalois A (IntermediateField.extendScalars hAB) ∧
        Module.finrank A (IntermediateField.extendScalars hAB) = p ∧
        IsCyclic ((IntermediateField.extendScalars hAB) ≃ₐ[A]
          IntermediateField.extendScalars hAB)) E M := by
  have hchain := subgroup_prime_chain_of_isPGroup E.fixingSubgroup M.fixingSubgroup hE
    (IntermediateField.fixingSubgroup_le hEM)
  have h := Relation.ReflTransGen.lift
    (r := fun S T : Subgroup (L ≃ₐ[K] L) => T ≤ S ∧
      (T.subgroupOf S).Normal ∧ (T.subgroupOf S).index = p)
    (p := fun A B : IntermediateField K L => ∃ hAB : A ≤ B,
      IsGalois A (IntermediateField.extendScalars hAB) ∧
      Module.finrank A (IntermediateField.extendScalars hAB) = p ∧
      IsCyclic ((IntermediateField.extendScalars hAB) ≃ₐ[A]
        IntermediateField.extendScalars hAB))
    (IntermediateField.fixedField (F := K) (E := L)) (by
      intro S T hST
      let hAB := IntermediateField.fixedField_le hST.1
      refine ⟨hAB, cyclic_prime_extendScalars_of_fixing_step K L p _ _ hAB ?_ ?_⟩
      · exact Eq.mpr (congrArg₂ (fun A B : Subgroup (L ≃ₐ[K] L) =>
          (B.subgroupOf A).Normal) (IntermediateField.fixingSubgroup_fixedField S)
          (IntermediateField.fixingSubgroup_fixedField T)) hST.2.1
      · exact (congrArg₂ (fun A B : Subgroup (L ≃ₐ[K] L) =>
          (B.subgroupOf A).index) (IntermediateField.fixingSubgroup_fixedField S)
          (IntermediateField.fixingSubgroup_fixedField T)).trans hST.2.2)
    E.fixingSubgroup M.fixingSubgroup hchain
  change Relation.ReflTransGen _ (IntermediateField.fixedField E.fixingSubgroup)
    (IntermediateField.fixedField M.fixingSubgroup) at h
  simpa only [IsGalois.fixedField_fixingSubgroup] using h

end Fields

section Valued

variable (K L : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]


local notation "W" => lowerRamificationGroup (L ≃ₐ[K] L)
  (IsLocalRing.maximalIdeal (spectralIntegerRing K L)) 1

/-- The actual wild fixed field has a cyclic prime-degree tower to every
actual intermediate field containing it. No total-ramification or finite-residue
hypothesis is added to this producer. -/
theorem wild_relative_prime_field_chain (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField (spectralIntegerRing K L)) p]
    (M : IntermediateField K L) (hM : IntermediateField.fixedField W ≤ M) :
    Relation.ReflTransGen
      (fun A B : IntermediateField K L => ∃ hAB : A ≤ B,
        IsGalois A (IntermediateField.extendScalars hAB) ∧
        Module.finrank A (IntermediateField.extendScalars hAB) = p ∧
        IsCyclic ((IntermediateField.extendScalars hAB) ≃ₐ[A]
          IntermediateField.extendScalars hAB))
      (IntermediateField.fixedField W) M := by
  apply relative_prime_field_chain K L p _ M hM
  rw [IntermediateField.fixingSubgroup_fixedField]
  exact lowerRamificationGroup_one_isPGroup (L ≃ₐ[K] L) p

end Valued

end FontaineWintenberger
