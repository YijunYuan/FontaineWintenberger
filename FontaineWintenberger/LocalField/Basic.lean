/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Valuation.Discrete.RankOne
public import Mathlib.FieldTheory.Perfect
public import Mathlib.Algebra.CharP.Basic

/-!
# Local fields in the sense of Wintenberger

Throughout Wintenberger's paper a *local field* is a field complete for a discrete valuation whose
residue field is perfect of characteristic `p > 0`; the residue field is never assumed finite.
This file packages those standing hypotheses into two `Prop` classes.

The field is presented by its norm (`NontriviallyNormedField`) because Mathlib's spectral-norm
machinery, which supplies the canonical norm on algebraic extensions, is stated for normed fields.
The ring of integers `𝒪[K]` and residue field `𝓀[K]` are Mathlib's `Valued.integer` and
`Valued.ResidueField`, obtained through the scoped instance `NormedField.toValued`; files using them
should `open scoped NormedField Valued NNReal`. (The switch to that notation is step F1b.)

## Main definitions

* `IsCompleteDiscreteValuedField K`: `K` is nonarchimedean, complete and `𝒪[K]` is a discrete
  valuation ring.
* `IsPerfectResidueLocalField K`: in addition `𝓀[K]` is perfect of prime characteristic.
* `residueChar K`: the residue characteristic `p = ringChar 𝓀[K]`.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, introduction ("tous les corps locaux considérés ont un corps résiduel parfait de
  caractéristique `p`").
-/

@[expose] public section

open scoped NormedField Valued NNReal

namespace FontaineWintenberger

/-- A complete, nonarchimedean, discretely valued field, presented by its norm. -/
class IsCompleteDiscreteValuedField (K : Type*) [NontriviallyNormedField K] : Prop
    extends IsUltrametricDist K, CompleteSpace K,
      IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring

/-- Wintenberger's standing assumption on a local field: complete, discretely valued, with a
perfect residue field of prime characteristic. Unlike Mathlib's `IsNonarchimedeanLocalField`, the
residue field need not be finite. -/
class IsPerfectResidueLocalField (K : Type*) [NontriviallyNormedField K] : Prop
    extends IsCompleteDiscreteValuedField K,
      PerfectField (IsLocalRing.ResidueField
        (NormedField.valuation (K := K)).valuationSubring) where
  residueChar_prime :
    (ringChar (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring)).Prime

variable (K : Type*) [NontriviallyNormedField K]

/-- The residue characteristic of a local field. -/
noncomputable abbrev residueChar [IsPerfectResidueLocalField K] : ℕ :=
  ringChar (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring)

instance [IsPerfectResidueLocalField K] : Fact (residueChar K).Prime :=
  ⟨IsPerfectResidueLocalField.residueChar_prime⟩

theorem residueChar_eq [IsPerfectResidueLocalField K] (p : ℕ)
    [CharP (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring) p] :
    residueChar K = p :=
  CharP.eq _ (ringChar.charP _) ‹_›

/-- Build the local-field structure from the individual hypotheses. -/
theorem IsPerfectResidueLocalField.of_charP [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring)]
    (p : ℕ) [hp : Fact p.Prime]
    [CharP (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring) p] :
    IsPerfectResidueLocalField K where
  residueChar_prime := by rw [ringChar.eq _ p]; exact hp.out

end FontaineWintenberger
