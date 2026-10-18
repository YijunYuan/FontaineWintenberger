/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.APF.FiniteExtension
public import FontaineWintenberger.APF.AbstractFiniteBase
public import FontaineWintenberger.FieldOfNorms.Multiplicative

/-!
# Uniform Herbrand precision below an abstract APF extension

Actual embedding invariance transports the existing inertia-index comparison.
The inverse comparison gives one input precision for every finite subextension.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]

variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

variable {M : Type*} [Field M] [Algebra K M] [Algebra.IsSeparable K M]

/-- The intrinsic Herbrand integral increases along every actual embedding
into an abstract APF extension. -/
theorem apfPsi_le_of_algHom [IsAPF K L] (f : M →ₐ[K] L)
    {u : ℝ} (hu : 0 ≤ u) : apfPsi K M u ≤ apfPsi K L u := by
  let j : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let i := j.comp f
  have hij : i.fieldRange ≤ j.fieldRange := by
    rintro x ⟨y, rfl⟩
    exact ⟨f y, rfl⟩
  rw [apfPsi_algEquiv K M i.equivFieldRange, apfPsi_algEquiv K L j.equivFieldRange]
  have := (isAPF_algEquiv K j.equivFieldRange).mp ‹_›
  exact apfPsi_mono_extension K i.fieldRange j.fieldRange hij hu

/-- Inverting the actual integral comparison reverses the extension-field
inequality for nonnegative parameters. -/
theorem apfPhi_le_of_algHom [IsAPF K L] (f : M →ₐ[K] L)
    {u : ℝ} (hu : 0 ≤ u) :
    have := IsAPF.of_algHom K f
    apfPhi K L u ≤ apfPhi K M u := by
  have := IsAPF.of_algHom K f
  have hv : 0 ≤ apfPhi K L u := by
    simpa only [apfPhi_of_nonpos K L le_rfl] using
      (strictMono_apfPhi K L).monotone hu
  apply (IsAPF.strictMono_apfPsi K M).le_iff_le.mp
  rw [apfPsi_apfPhi]
  exact (apfPsi_le_of_algHom K L f hv).trans_eq (apfPsi_apfPhi K L u)

/-- A single intrinsic APF precision controls the inverse Herbrand function
of every embedded subextension. -/
theorem le_ceil_apfPhi_of_apfPsi_le [IsAPF K L] (f : M →ₐ[K] L)
    (N s : ℕ) (hs : apfPsi K L (N : ℝ) ≤ (s : ℝ)) :
    have := IsAPF.of_algHom K f
    N ≤ ⌈apfPhi K M (s : ℝ)⌉₊ := by
  have := IsAPF.of_algHom K f
  have h : (N : ℝ) ≤ apfPhi K M (s : ℝ) := by
    calc
      (N : ℝ) = apfPhi K L (apfPsi K L (N : ℝ)) :=
        (apfPhi_apfPsi K L (N : ℝ)).symm
      _ ≤ apfPhi K L (s : ℝ) := (strictMono_apfPhi K L).monotone hs
      _ ≤ apfPhi K M (s : ℝ) :=
        apfPhi_le_of_algHom K L f (Nat.cast_nonneg s)
  exact_mod_cast h.trans (Nat.le_ceil _)

variable [PerfectField (IsLocalRing.ResidueField
  (NormedField.valuation (K := K)).valuationSubring)]

/-- Uniform precision for the actual relative finite fields, with the
canonical spectral norm on their original finite base. -/
theorem FiniteIntermediateField.le_ceil_apfPhi_of_apfPsi_le [IsAPF K L]
    (E F : FiniteIntermediateField K L) (hEF : E ≤ F) :
    letI := spectralNorm.nontriviallyNormedField K E.val
    letI := spectralNorm.normedAlgebra K E.val
    letI := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
      (isNonarchimedean_spectralNorm (K := K) (L := E.val))
    letI := spectralNorm.completeSpace K E.val
    letI := normedAlgebra_isCompleteDiscreteValuedField K E.val
    letI := Algebra.isSeparable_tower_top_of_isSeparable K E.val L
    let F' := IntermediateField.extendScalars hEF
    letI : FiniteDimensional K F' := F.property
    letI : FiniteDimensional E.val F' := Module.Finite.right K E.val F'
    ∀ (N s : ℕ), apfPsi E.val L (N : ℝ) ≤ (s : ℝ) →
      N ≤ ⌈apfPhi E.val F' (s : ℝ)⌉₊ := by
  let := spectralNorm.nontriviallyNormedField K E.val
  let := spectralNorm.normedAlgebra K E.val
  let := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := E.val))
  let := spectralNorm.completeSpace K E.val
  let := normedAlgebra_isCompleteDiscreteValuedField K E.val
  let := Algebra.isSeparable_tower_top_of_isSeparable K E.val L
  let F' := IntermediateField.extendScalars hEF
  have : FiniteDimensional K F' := F.property
  have : FiniteDimensional E.val F' := Module.Finite.right K E.val F'
  dsimp only
  intro N s hs
  have hrelative : IsAPF E.val L :=
    (isAPF_finiteBase_iff_of_normedAlgebra K E.val L).mp ‹_›
  exact FontaineWintenberger.le_ceil_apfPhi_of_apfPsi_le E.val L F'.val N s hs

end FontaineWintenberger
