/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.LocalField.Spectral.Henselian
public import FontaineWintenberger.Ramification.Lower.SpectralMaps
public import Mathlib.RingTheory.Teichmuller

/-!
# Multiplicative representatives of arbitrary perfect residue fields

The canonical section is Mathlib's Teichmüller limit, applied to the
perfection of the residue field. No finite residue field is assumed.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

section Adic

variable (R : Type*) [CommRing R] [IsLocalRing R]
variable (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField R) p]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

/-- Reduction is injective on multiplicative maps from a perfect monoid
into the adically complete ring. This is the uniqueness in the
canonical Teichmüller limit, using Mathlib's perfection equivalence. -/
theorem residue_comp_monoidHom_injective (A : Type*) [CommMonoid A] [PerfectRing A p] :
    Function.Injective (fun s : A →* R => (IsLocalRing.residue R).toMonoidHom.comp s) := by
  intro s t h
  let : CharP (R ⧸ IsLocalRing.maximalIdeal R) p :=
    ‹CharP (IsLocalRing.ResidueField R) p›
  apply (Perfection.liftMonoidHom p A R).injective
  apply MonoidHom.ext
  intro x
  apply (Perfection.quotientMulEquiv p (IsLocalRing.maximalIdeal R)).injective
  apply Perfection.extMonoid
  intro n
  change IsLocalRing.residue R (s ((powMulEquiv A (p ^ n)).symm x)) =
    IsLocalRing.residue R (t ((powMulEquiv A (p ^ n)).symm x))
  exact DFunLike.congr_fun h _

variable [PerfectField (IsLocalRing.ResidueField R)]

/-- The canonical multiplicative representatives of the perfect
residue field, constructed by Mathlib's Teichmüller limit. -/
def residueTeichmuller : IsLocalRing.ResidueField R →*₀ R := by
  letI : CharP (R ⧸ IsLocalRing.maximalIdeal R) p :=
    ‹CharP (IsLocalRing.ResidueField R) p›
  exact (Perfection.teichmuller₀ p (IsLocalRing.maximalIdeal R)).comp
    (PerfectionMap.id p (IsLocalRing.ResidueField R)).equiv.toMonoidWithZeroHom

/-- The canonical representatives reduce to the residue class. -/
@[simp]
theorem residue_residueTeichmuller (x : IsLocalRing.ResidueField R) :
    IsLocalRing.residue R (residueTeichmuller R p x) = x := by
  let : CharP (R ⧸ IsLocalRing.maximalIdeal R) p :=
    ‹CharP (IsLocalRing.ResidueField R) p›
  change Ideal.Quotient.mk _ (Perfection.teichmuller₀ p _
    ((PerfectionMap.id p (IsLocalRing.ResidueField R)).equiv x)) = x
  exact (Perfection.mk_teichmuller₀
    (show Perfection (R ⧸ IsLocalRing.maximalIdeal R) p from
      (PerfectionMap.id p (IsLocalRing.ResidueField R)).equiv x)).trans rfl

/-- There is only one multiplicative section of the reduction. -/
theorem residueTeichmuller_unique (s : IsLocalRing.ResidueField R →*₀ R)
    (hs : ∀ x, IsLocalRing.residue R (s x) = x) : s = residueTeichmuller R p := by
  have h : s.toMonoidHom = (residueTeichmuller R p).toMonoidHom :=
    residue_comp_monoidHom_injective R p (IsLocalRing.ResidueField R)
      (MonoidHom.ext fun x => (hs x).trans (residue_residueTeichmuller R p x).symm)
  exact MonoidWithZeroHom.ext (fun x => DFunLike.congr_fun h x)

/-- The canonical representatives commute with every natural power,
in particular with Frobenius. -/
theorem residueTeichmuller_pow (x : IsLocalRing.ResidueField R) (n : ℕ) :
    residueTeichmuller R p (x ^ n) = residueTeichmuller R p x ^ n :=
  map_pow (residueTeichmuller R p) x n

/-- Zero and one are the zero and one representatives. -/
@[simp]
theorem residueTeichmuller_zero : residueTeichmuller R p 0 = 0 :=
  map_zero (residueTeichmuller R p)

@[simp]
theorem residueTeichmuller_one : residueTeichmuller R p 1 = 1 :=
  map_one (residueTeichmuller R p)

/-- Frobenius is preserved, for every residue prime including two. -/
theorem residueTeichmuller_frobenius (x : IsLocalRing.ResidueField R) :
    residueTeichmuller R p (frobenius _ p x) = residueTeichmuller R p x ^ p :=
  residueTeichmuller_pow R p x p

/-- The canonical section is the same canonical limit of powers of arbitrary
lifts of inverse Frobenius coordinates used in the construction. -/
theorem residueTeichmuller_sModEq (x : IsLocalRing.ResidueField R) (n : ℕ) (y : R)
    (hy : IsLocalRing.residue R y = Perfection.coeff (IsLocalRing.ResidueField R) p n
      ((PerfectionMap.id p (IsLocalRing.ResidueField R)).equiv x)) :
    residueTeichmuller R p x ≡ y ^ p ^ n
      [SMOD IsLocalRing.maximalIdeal R ^ (n + 1)] := by
  let : CharP (R ⧸ IsLocalRing.maximalIdeal R) p :=
    ‹CharP (IsLocalRing.ResidueField R) p›
  exact Perfection.teichmuller₀_sModEq
    (show Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) y =
      Perfection.coeff (R ⧸ IsLocalRing.maximalIdeal R) p n
        ((PerfectionMap.id p (IsLocalRing.ResidueField R)).equiv x) from hy)

variable (S : Type*) [CommRing S] [IsLocalRing S]
    [CharP (IsLocalRing.ResidueField S) p] [PerfectField (IsLocalRing.ResidueField S)]
    [IsAdicComplete (IsLocalRing.maximalIdeal S) S]

/-- Every local ring map commutes with canonical multiplicative
representatives; continuity is supplied by adic uniqueness itself. -/
theorem residueTeichmuller_naturality (f : R →+* S) [IsLocalHom f]
    (x : IsLocalRing.ResidueField R) :
    f (residueTeichmuller R p x) =
      residueTeichmuller S p (IsLocalRing.ResidueField.map f x) := by
  have h : f.toMonoidHom.comp (residueTeichmuller R p).toMonoidHom =
      (residueTeichmuller S p).toMonoidHom.comp
        (IsLocalRing.ResidueField.map f).toMonoidHom := by
    apply residue_comp_monoidHom_injective S p (IsLocalRing.ResidueField R)
    apply MonoidHom.ext
    intro z
    change IsLocalRing.residue S (f (residueTeichmuller R p z)) =
      IsLocalRing.residue S (residueTeichmuller S p (IsLocalRing.ResidueField.map f z))
    rw [← IsLocalRing.ResidueField.map_residue, residue_residueTeichmuller,
      residue_residueTeichmuller]
  exact DFunLike.congr_fun h x

end Adic

section FiniteExtension

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K

variable (E : Type*) [Field E] [Algebra K E] [FiniteDimensional K E]
    [Algebra.IsSeparable K E]

/-- The finite spectral integer ring is complete for its
maximal ideal, by the already proved unit-ball adic completeness. -/
instance spectralIntegerRing_isAdicComplete :
    IsAdicComplete (IsLocalRing.maximalIdeal (spectralIntegerRing K E))
      (spectralIntegerRing K E) := by
  let : NormedField E := spectralNorm.normedField K E
  have : IsUltrametricDist E :=
    IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
      (isNonarchimedean_spectralNorm (K := K) (L := E))
  have : CompleteSpace E := spectralNorm.completeSpace (K := K) (L := E)
  have hval : NormedField.valuation (K := E) = spectralValuation K E := by
    ext x
    rfl
  have : IsDiscreteValuationRing (NormedField.valuation (K := E)).valuationSubring := by
    rw [hval]
    exact spectralIntegerRing_isDiscreteValuationRing K E
  exact unitBall_isAdicComplete E

/-- The finite spectral residue extension of a perfect base is perfect. -/
instance spectralResidueField_perfectField :
    PerfectField (IsLocalRing.ResidueField (spectralIntegerRing K E)) :=
  Algebra.IsAlgebraic.perfectField
    (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring)

/-- The finite residue inclusion preserves the residue characteristic. -/
instance spectralResidueField_charP :
    CharP (IsLocalRing.ResidueField (spectralIntegerRing K E)) p :=
  charP_of_injective_algebraMap
    (algebraMap (IsLocalRing.ResidueField (NormedField.valuation (K := K)).valuationSubring)
      (IsLocalRing.ResidueField (spectralIntegerRing K E))).injective p

/-- The canonical multiplicative representatives in the finite
spectral integer ring, with arbitrary perfect residue field. -/
def spectralTeichmuller : IsLocalRing.ResidueField (spectralIntegerRing K E) →*₀
    spectralIntegerRing K E := residueTeichmuller (spectralIntegerRing K E) p

/-- The finite representative has the specified residue. -/
@[simp]
theorem residue_spectralTeichmuller (x : IsLocalRing.ResidueField (spectralIntegerRing K E)) :
    IsLocalRing.residue _ (spectralTeichmuller K E x) = x :=
  residue_residueTeichmuller (spectralIntegerRing K E) p x

/-- The finite representatives are the unique multiplicative section. -/
theorem spectralTeichmuller_unique
    (s : IsLocalRing.ResidueField (spectralIntegerRing K E) →*₀ spectralIntegerRing K E)
    (hs : ∀ x, IsLocalRing.residue _ (s x) = x) : s = spectralTeichmuller K E :=
  residueTeichmuller_unique (spectralIntegerRing K E) p s hs

variable {F : Type*} [Field F] [Algebra K F] [FiniteDimensional K F]
    [Algebra.IsSeparable K F]

/-- The canonical representatives commute with the finite
valued-field inclusions and their induced residue inclusions. -/
theorem spectralTeichmuller_naturality (i : E →ₐ[K] F)
    (x : IsLocalRing.ResidueField (spectralIntegerRing K E)) :
    spectralIntegerInclusion K i (spectralTeichmuller K E x) =
      spectralTeichmuller K F (spectralResidueInclusion K i x) := by
  let : IsLocalHom (spectralIntegerInclusion K i).toRingHom :=
    ⟨(spectralIntegerInclusion_isLocalHom K i).map_nonunit⟩
  exact residueTeichmuller_naturality (spectralIntegerRing K E) p
    (spectralIntegerRing K F) (spectralIntegerInclusion K i).toRingHom x

/-- The same naturality statement holds as an equality in the field. -/
theorem coe_spectralTeichmuller_naturality (i : E →ₐ[K] F)
    (x : IsLocalRing.ResidueField (spectralIntegerRing K E)) :
    i (spectralTeichmuller K E x : E) =
      (spectralTeichmuller K F (spectralResidueInclusion K i x) : F) :=
  congrArg (fun z : spectralIntegerRing K F => (z : F))
    (spectralTeichmuller_naturality K E i x)

end FiniteExtension

end FontaineWintenberger
