/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Ramification.Lower.Degree
public import FontaineWintenberger.Ramification.Lower.Generator
public import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# Inertia for finite extensions of complete discrete valuation fields

The full field automorphism action on the actual spectral integers has the
base integers as its invariant ring. Mathlib's ideal inertia theorem then
identifies the order of the zero lower group with the canonical local index.
-/

@[expose] public section

namespace FontaineWintenberger

/-- Perfect local residue fields supply Mathlib's prime-wise separability interface. -/
theorem hasSeparableResidueFieldsAt_maximalIdeal
    (R S : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
    [FaithfulSMul R S] [IsLocalHom (algebraMap R S)] [Module.Finite R S]
    [PerfectField (IsLocalRing.ResidueField R)] :
    Algebra.HasSeparableResidueFieldsAt R S (IsLocalRing.maximalIdeal R) where
  isSeparable' q _ _ := by
    have hp : Ideal.primesOver (IsLocalRing.maximalIdeal R) S =
        {IsLocalRing.maximalIdeal S} := IsLocalRing.primesOver_eq (A := S) (R := R)
          (IsDiscreteValuationRing.maximalIdeal R).ne_bot
    have hq : q ∈ Ideal.primesOver (IsLocalRing.maximalIdeal R) S :=
      ⟨inferInstance, inferInstance⟩
    have he : q = IsLocalRing.maximalIdeal S := by simpa [hp] using hq
    subst q
    let := Localization.AtPrime.algebraOfLiesOver
      (IsLocalRing.maximalIdeal R) (IsLocalRing.maximalIdeal S)
    apply Algebra.isSeparable_residueField_iff.mpr
    exact (inferInstance : Algebra.IsSeparable
      (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))

section LocalRings

variable (R S G : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
    [FaithfulSMul R S] [IsLocalHom (algebraMap R S)] [Module.Finite R S]
    [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]
    [Algebra.HasSeparableResidueFieldsAt R S (IsLocalRing.maximalIdeal R)]

/-- Zero lower inertia has the actual canonical local ramification index as its order. -/
theorem card_lowerRamificationGroup_zero :
    Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal S) 0) =
      (IsLocalRing.maximalIdeal S).ramificationIdx R := by
  rw [lowerRamificationGroup_zero,
    Ideal.card_inertia_eq_ramificationIdxIn (IsLocalRing.maximalIdeal R),
    Ideal.ramificationIdxIn_eq_ramificationIdx (IsLocalRing.maximalIdeal R)
      (IsLocalRing.maximalIdeal S) G]

end LocalRings

section ResidueReduction

variable (R S G : Type*) [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]

/-- The actual residue automorphism induced by an automorphism of a local algebra. -/
noncomputable def localResidueGaloisHom :
    G →* (IsLocalRing.ResidueField S ≃ₐ[IsLocalRing.ResidueField R]
      IsLocalRing.ResidueField S) :=
  (Ideal.Quotient.stabilizerHom (IsLocalRing.maximalIdeal S)
    (IsLocalRing.maximalIdeal R) G).comp
      { toFun := fun g => ⟨g, smul_maximalIdeal G g⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }

omit [Finite G] in
@[simp]
theorem localResidueGaloisHom_residue (g : G) (x : S) :
    localResidueGaloisHom R S G g (IsLocalRing.residue S x) =
      IsLocalRing.residue S (g • x) := rfl

/-- The actual reduction homomorphism is onto the actual residue automorphism group. -/
theorem localResidueGaloisHom_surjective :
    Function.Surjective (localResidueGaloisHom R S G) := by
  intro σ
  obtain ⟨g, hg⟩ := Ideal.Quotient.stabilizerHom_surjective G
    (IsLocalRing.maximalIdeal R) (IsLocalRing.maximalIdeal S) σ
  exact ⟨g.1, hg⟩

omit [Finite G] in
/-- The residue reduction kernel is exactly the intrinsic zero lower group. -/
theorem ker_localResidueGaloisHom :
    (localResidueGaloisHom R S G).ker =
      lowerRamificationGroup G (IsLocalRing.maximalIdeal S) 0 := by
  ext g
  rw [MonoidHom.mem_ker, lowerRamificationGroup_zero_eq_ker_residue, MonoidHom.mem_ker]
  constructor
  · intro hg
    ext x
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
    exact congrArg (fun σ => σ (IsLocalRing.residue S x)) hg
  · intro hg
    ext x
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
    exact congrArg (fun σ => σ (IsLocalRing.residue S x)) hg

/-- The residue automorphism group is the actual quotient by the zero lower group. -/
noncomputable def localResidueGaloisEquiv :
    G ⧸ lowerRamificationGroup G (IsLocalRing.maximalIdeal S) 0 ≃*
      (IsLocalRing.ResidueField S ≃ₐ[IsLocalRing.ResidueField R]
        IsLocalRing.ResidueField S) :=
  QuotientGroup.liftEquiv (N := lowerRamificationGroup G (IsLocalRing.maximalIdeal S) 0)
    (localResidueGaloisHom_surjective R S G)
    (ker_localResidueGaloisHom R S G).symm

@[simp]
theorem localResidueGaloisEquiv_mk (g : G) :
    localResidueGaloisEquiv R S G g = localResidueGaloisHom R S G g := rfl

include G in
/-- Normality of the actual local residue-field extension. -/
theorem localResidue_normal : Normal (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
  Ideal.Quotient.normal G (IsLocalRing.maximalIdeal R) (IsLocalRing.maximalIdeal S)

end ResidueReduction

section Spectral

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

local notation "R" => Valuation.valuationSubring (NormedField.valuation (K := K))
local notation "S" => spectralIntegerRing K L
local notation "G" => L ≃ₐ[K] L

instance spectralIntegerRing_galois_smulDistribClass : SMulDistribClass G S L where
  smul_distrib_smul g x y := by
    change g ((x : L) * y) = ((g • x : S) : L) * g y
    exact map_mul g (x : L) y

/-- The proved full action has the actual base integer ring as its fixed ring. -/
instance spectralIntegerRing_isGaloisGroup : IsGaloisGroup G R S :=
  IsGaloisGroup.of_isFractionRing G R S K L

variable [PerfectField (IsLocalRing.ResidueField
  (NormedField.valuation (K := K)).valuationSubring)]

/-- The actual residue extension is Galois, without a finite-residue assumption. -/
instance spectralIntegerRing_residue_isGalois :
    IsGalois (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) where
  __ := localResidue_normal R S G

/-- Inertia order for the actual full Galois action on the actual spectral integers. -/
theorem spectralIntegerRing_card_lower_zero :
    Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal S) 0) =
      (IsLocalRing.maximalIdeal S).ramificationIdx R := by
  have := hasSeparableResidueFieldsAt_maximalIdeal R S
  exact card_lowerRamificationGroup_zero R S G

end Spectral

end FontaineWintenberger
