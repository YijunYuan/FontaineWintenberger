/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Ramification.Lower.Inertia

/-!
# Inertia over a base with finite residue field

For a finite Galois extension `L/K` of a local field with finite residue field, the residue
field of `L` is finite, the image of `Gal(L/K)` in the residue Galois group is cyclic, and every
commutator lies in the inertia group `Gal(L/K)_0`.

## References

* Serre, *Local Fields*, Chapter IV, §1.
-/

@[expose] public section

namespace FontaineWintenberger

open scoped commutatorElement

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
variable [Finite 𝓀[K]]

instance spectralIntegerRing_residueField_finite :
    Finite (IsLocalRing.ResidueField (spectralIntegerRing K L)) :=
  Module.finite_of_finite 𝓀[K]

theorem isCyclic_localResidueGaloisHom_range :
    IsCyclic (localResidueGaloisHom 𝒪[K] (spectralIntegerRing K L) (L ≃ₐ[K] L)).range :=
  inferInstance

theorem commutatorElement_mem_lowerRamificationGroup_zero (g h : L ≃ₐ[K] L) :
    ⁅g, h⁆ ∈ lowerRamificationGroup (L ≃ₐ[K] L)
      (IsLocalRing.maximalIdeal (spectralIntegerRing K L)) 0 := by
  let := IsCyclic.commGroup (α := IsLocalRing.ResidueField (spectralIntegerRing K L) ≃ₐ[𝓀[K]]
    IsLocalRing.ResidueField (spectralIntegerRing K L))
  rw [← ker_localResidueGaloisHom 𝒪[K] (spectralIntegerRing K L) (L ≃ₐ[K] L),
    MonoidHom.mem_ker, map_commutatorElement]
  simp [commutatorElement_def]

end FontaineWintenberger
