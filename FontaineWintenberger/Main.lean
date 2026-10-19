/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Mathlib.FieldTheory.AbsoluteGaloisGroup
public import FontaineWintenberger.APF.Strict
public import FontaineWintenberger.FieldOfNorms.Structure.Residue
public import FontaineWintenberger.FieldOfNorms.Structure.Completeness
public import FontaineWintenberger.FieldOfNorms.Functor.FullyFaithful
public import FontaineWintenberger.FieldOfNorms.Galois.AbsoluteGroup
public import FontaineWintenberger.FieldOfNorms.Galois.Ambient

/-!
# The field of norms: main statements

The five targets of the formalization, stated with clean signatures. Each is a direct
consequence of a declaration in the library; this file adds no mathematics.

Throughout, `K` is a complete discretely valued field with perfect residue field of
characteristic `p = residueChar K` (`IsPerfectResidueLocalField K`), and `L/K` is a separable
extension.

1. **Arithmetically profinite extensions** (Wintenberger 1.2.1). `IsAPF K L` says that
   `G_K^u · G_L` is open in the absolute Galois group `G_K = Field.absoluteGaloisGroup K` for
   every `u ≥ -1` (`isAPF_iff_isOpen_absoluteGaloisGroup`); `IsStrictlyAPF K L` adds that the
   strictness ratio `ψ(u) / [G_K^0 : G_K^u G_L]` stays bounded below.
2. **The field of norms** (2.1.1). `FieldOfNorms K L` carries global instances
   `Field`, `Valued _ ℤᵐ⁰`, `CharP _ p`.
3. **Theorem 2.1.3.** `FieldOfNorms K L` is a complete discretely valued field of
   characteristic `p`, with residue field the residue field of `L`
   (`FieldOfNorms.residueFieldEquiv`).
4. **Theorem 3.1.2 and Corollary 3.2.3.** The field of norms is fully faithful on finite
   separable extensions of `L` (`FieldOfNorms.finiteHomEquiv`), and
   `G_L ≃ G_{X_K(L)}` as topological groups (`FieldOfNorms.absoluteGaloisGroupEquiv`).
5. **Remark 3.2.4.** For `L/K` Galois, `Gal(L/K)` acts on `X_K(L)` (`FieldOfNorms.aut`), and
   `G_K` acts on `X_K(L)^sep` extending this action, identifying `G_K` with the subgroup of
   automorphisms of `X_K(L)^sep` that normalize `X_K(L)` through this action
   (`RelFieldOfNorms.absoluteGaloisGroupEquiv`).

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, Ann. Sci. ENS 16 (1983), §§1.2, 2.1, 3.1–3.2.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

open Field.absoluteGaloisGroup

section APF

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- The subgroup `G_K^u · G_L` of the absolute Galois group, for an embedding `i : L → K^sep`. -/
def apfAbsoluteSubgroup (i : L →ₐ[K] SeparableClosure K) (u : ℝ) :
    Subgroup (Field.absoluteGaloisGroup K) :=
  (apfSubgroup K i.fieldRange u).comap (sepEquiv K).toMonoidHom

/-- **Target 1.** `L/K` is arithmetically profinite iff `G_K^u · G_L` is open in `G_K` for all
`u ≥ -1` (Wintenberger 1.2.1); the condition does not depend on the embedding of `L`. -/
theorem isAPF_iff_isOpen_absoluteGaloisGroup :
    IsAPF K L ↔ ∀ (i : L →ₐ[K] SeparableClosure K) (u : ℝ), -1 ≤ u →
      IsOpen (apfAbsoluteSubgroup K L i u : Set (Field.absoluteGaloisGroup K)) := by
  constructor
  · intro h i u hu
    have := (h.isAPFSubextension i).isOpen_apfSubgroup u hu
    exact (sepEquiv K).toHomeomorph.isOpen_preimage.mpr this
  · intro h
    exact ⟨fun i => ⟨fun u hu => (sepEquiv K).toHomeomorph.isOpen_preimage.mp (h i u hu)⟩⟩

/-- **Target 1, strict version.** `L/K` is strictly APF iff it is APF and the strictness ratios
`ψ_{L/K}(u) / [G_K^0 : G_K^u G_L]` are bounded below by a positive constant as `u → ∞`. -/
theorem isStrictlyAPF_iff_liminf_pos :
    IsStrictlyAPF K L ↔ IsAPF K L ∧ 0 < Filter.liminf (apfStrictnessRatio K L) Filter.atTop :=
  isStrictlyAPF_iff K L

end APF

section FieldOfNorms

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]
variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- **Target 2.** The field of norms is a field. -/
example : Field (FieldOfNorms K L) := inferInstance

/-- **Target 2.** The field of norms is a valued field with value group `ℤ`. -/
example : Valued (FieldOfNorms K L) (WithZero (Multiplicative ℤ)) := inferInstance

/-- **Theorem 2.1.3 (i).** The field of norms has characteristic `p`. -/
theorem FieldOfNorms.charP : CharP (FieldOfNorms K L) (residueChar K) := inferInstance

/-- **Theorem 2.1.3 (ii).** The field of norms is complete. -/
theorem FieldOfNorms.completeSpace : CompleteSpace (FieldOfNorms K L) := inferInstance

/-- **Theorem 2.1.3 (ii).** Its valuation ring is a discrete valuation ring. -/
theorem FieldOfNorms.isDiscreteValuationRing :
    IsDiscreteValuationRing
      (Valued.v : Valuation (FieldOfNorms K L) (WithZero (Multiplicative ℤ))).valuationSubring :=
  inferInstance

/-- **Theorem 2.1.3 (iii).** The residue field of the field of norms is the residue field
`k_L` of `L`, the residue field of the integral closure of `𝒪_K` in `L`. -/
def FieldOfNorms.residueFieldEquiv :
    IsLocalRing.ResidueField
        (Valued.v : Valuation (FieldOfNorms K L) (WithZero (Multiplicative ℤ))).valuationSubring
      ≃+* IsLocalRing.ResidueField
        (integralClosure (NormedField.valuation (K := K)).valuationSubring L) :=
  FieldOfNorms.residueEquiv K L

end FieldOfNorms

section Functoriality

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]
variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- **Theorem 3.1.2.** For finite separable extensions `M`, `N` of `L`, the field of norms gives a
bijection `Hom_L(M, N) ≃ Hom_{X_K(L)}(X_K(M), X_K(N))`. -/
def FieldOfNorms.homEquiv (M N : Type*) [Field M] [Field N] [Algebra K M] [Algebra K N]
    [Algebra L M] [Algebra L N] [IsScalarTower K L M] [IsScalarTower K L N]
    [Algebra.IsSeparable K M] [Algebra.IsSeparable K N] [Module.Finite L M] [Module.Finite L N] :
    haveI : IsAPF K M := (isAPF_finite_extension_iff K M L).mpr ‹_›
    haveI : IsAPF K N := (isAPF_finite_extension_iff K N L).mpr ‹_›
    haveI : Fact (¬ Module.Finite K M) := ⟨RelFieldOfNorms.ambient_infinite K L M⟩
    haveI : Fact (¬ Module.Finite K N) := ⟨RelFieldOfNorms.ambient_infinite K L N⟩
    letI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
    letI : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
    letI := (FieldOfNorms.finiteRingHom K L M).toAlgebra
    letI := (FieldOfNorms.finiteRingHom K L N).toAlgebra
    (M →ₐ[L] N) ≃ (FieldOfNorms K M →ₐ[FieldOfNorms K L] FieldOfNorms K N) :=
  FieldOfNorms.finiteHomEquiv K L M N

/-- **Corollary 3.2.3.** The absolute Galois groups of `L` and of `X_K(L)` are isomorphic as
topological groups. -/
def FieldOfNorms.absoluteGaloisGroupEquiv :
    Field.absoluteGaloisGroup L ≃ₜ* Field.absoluteGaloisGroup (FieldOfNorms K L) :=
  ((sepEquiv L).trans (fieldOfNormsAbsoluteGaloisEquiv K L)).trans
    (sepEquiv (FieldOfNorms K L)).symm

end Functoriality

section GaloisAction

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
variable (L : IntermediateField K (SeparableClosure K)) [Normal K L]
variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- **Remark 3.2.4 (i).** For `L/K` Galois, `Gal(L/K)` acts on `X_K(L)` by field automorphisms. -/
example : (L ≃ₐ[K] L) →* (FieldOfNorms K L ≃+* FieldOfNorms K L) := FieldOfNorms.aut K L

/-- **Remark 3.2.4 (ii).** The absolute Galois group `G_K` acts on
`X_{L/K}(K^sep) = X_K(L)^sep`, extending the action of `Gal(L/K)` on `X_K(L)`. -/
def RelFieldOfNorms.absoluteGaloisGroupAction :
    Field.absoluteGaloisGroup K →* RingAut (RelFieldOfNorms K L (SeparableClosure K)) :=
  (RelFieldOfNorms.absoluteAut K L).comp (sepEquiv K).toMonoidHom

/-- **Remark 3.2.4 (iii).** This action identifies `G_K` with the group of automorphisms of
`X_K(L)^sep` that restrict to `X_K(L)` through the action of some element of `Gal(L/K)`. -/
def RelFieldOfNorms.absoluteGaloisGroupEquiv :
    Field.absoluteGaloisGroup K ≃* RelFieldOfNorms.galoisSubgroup K L :=
  (sepEquiv K).toMulEquiv.trans (RelFieldOfNorms.ambientGaloisEquiv K L)

end GaloisAction

end FontaineWintenberger
