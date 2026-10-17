/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.FixedField

/-!
# Spectral integer and residue maps along actual field embeddings

The exact restriction of the spectral norm produces local maps on the
actual spectral integer rings, retaining the original base residue algebra.
The construction applies to algebraic extensions of arbitrary degree.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

section SpectralMaps

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {E L : Type*} [Field E] [Field L] [Algebra K E] [Algebra K L]
    [Algebra.IsAlgebraic K E] [Algebra.IsAlgebraic K L]

/-- The exact spectral norm restriction gives compatibility of valuations
in any algebraic field tower, including an infinite ambient extension. -/
theorem spectralValuation_hasExtension_tower [Algebra E L] [IsScalarTower K E L] :
    (spectralValuation K E).HasExtension (spectralValuation K L) where
  val_isEquiv_comap := by
    intro x y
    change spectralNorm K E x ≤ spectralNorm K E y ↔
      spectralNorm K L (algebraMap E L x) ≤ spectralNorm K L (algebraMap E L y)
    rw [← spectralNorm.eq_of_tower x, ← spectralNorm.eq_of_tower y]

/-- The original field embedding restricts to the actual spectral integer
rings as an algebra map over the original base integer ring. -/
def spectralIntegerInclusion (i : E →ₐ[K] L) :
    spectralIntegerRing K E →ₐ[(NormedField.valuation (K := K)).valuationSubring]
      spectralIntegerRing K L := by
  let : Algebra E L := i.toRingHom.toAlgebra
  let : IsScalarTower K E L := IsScalarTower.of_algebraMap_eq (fun r ↦ (i.commutes r).symm)
  let := spectralValuation_hasExtension_tower K (E := E) (L := L)
  let := Valuation.HasExtension.valuationSubring_isScalarTower
    (NormedField.valuation (K := K)) (spectralValuation K E) (spectralValuation K L)
  exact IsScalarTower.toAlgHom _ _ _

@[simp]
theorem coe_spectralIntegerInclusion (i : E →ₐ[K] L) (x : spectralIntegerRing K E) :
    (spectralIntegerInclusion K i x : L) = i (x : E) := rfl

/-- The original integer-ring inclusion is local without any finiteness
or discreteness assumption on the ambient extension. -/
theorem spectralIntegerInclusion_isLocalHom (i : E →ₐ[K] L) :
    IsLocalHom (spectralIntegerInclusion K i) := by
  let : Algebra E L := i.toRingHom.toAlgebra
  let : IsScalarTower K E L := IsScalarTower.of_algebraMap_eq (fun r ↦ (i.commutes r).symm)
  let := spectralValuation_hasExtension_tower K (E := E) (L := L)
  constructor
  intro x hx
  exact (isUnit_map_iff (algebraMap (spectralIntegerRing K E) (spectralIntegerRing K L)) x).mp hx

/-- The actual residue map induced by the original embedding retains the
original base residue algebra. -/
def spectralResidueInclusion (i : E →ₐ[K] L) :
    IsLocalRing.ResidueField (spectralIntegerRing K E) →ₐ[
      IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring]
        IsLocalRing.ResidueField (spectralIntegerRing K L) := by
  let := spectralIntegerInclusion_isLocalHom K i
  exact IsLocalRing.ResidueField.mapAlgHom' (spectralIntegerInclusion K i)

@[simp]
theorem spectralResidueInclusion_residue (i : E →ₐ[K] L) (x : spectralIntegerRing K E) :
    spectralResidueInclusion K i (IsLocalRing.residue _ x) =
      IsLocalRing.residue _ (spectralIntegerInclusion K i x) := rfl

theorem spectralResidueInclusion_injective (i : E →ₐ[K] L) :
    Function.Injective (spectralResidueInclusion K i) :=
  (spectralResidueInclusion K i).injective

variable {M : Type*} [Field M] [Algebra K M] [Algebra.IsAlgebraic K M]

theorem spectralIntegerInclusion_comp (i : E →ₐ[K] L) (j : L →ₐ[K] M) :
    spectralIntegerInclusion K (j.comp i) =
      (spectralIntegerInclusion K j).comp (spectralIntegerInclusion K i) := by
  ext x
  rfl

/-- Residue inclusions compose along the original field inclusions. -/
theorem spectralResidueInclusion_comp (i : E →ₐ[K] L) (j : L →ₐ[K] M) :
    spectralResidueInclusion K (j.comp i) =
      (spectralResidueInclusion K j).comp (spectralResidueInclusion K i) := by
  ext x
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
  simp only [AlgHom.comp_apply, spectralResidueInclusion_residue]
  rw [spectralIntegerInclusion_comp]
  rfl

end SpectralMaps

end FontaineWintenberger
