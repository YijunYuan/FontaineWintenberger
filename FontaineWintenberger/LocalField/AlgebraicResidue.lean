/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.Residue

/-!
# The intrinsic residue field of an algebraic APF extension

The canonical integral closure of the original base integer ring in the
original algebraic field is a valuation ring. Its finite residue inclusions
become isomorphisms on the actual APF residue-stable tail.

The finite-layer representative argument generalizes the diagonal-layer
argument in `FalseTateExtension.Padic.FiniteGaloisStructure`.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

local notation "R₀" => Valuation.valuationSubring (NormedField.valuation (K := K))

section Algebraic

variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- The canonical integral closure and the original spectral integer ring
are identified by the identity in the original algebraic field. -/
def integralClosureSpectralEquiv :
    integralClosure R₀ L ≃ₐ[R₀] spectralIntegerRing K L :=
  IsIntegralClosure.equiv R₀ (integralClosure R₀ L) L (spectralIntegerRing K L)

@[simp]
theorem coe_integralClosureSpectralEquiv (x : integralClosure R₀ L) :
    (integralClosureSpectralEquiv K L x : L) = (x : L) :=
  IsIntegralClosure.algebraMap_equiv R₀ (integralClosure R₀ L) L
    (spectralIntegerRing K L) x

@[simp]
theorem coe_integralClosureSpectralEquiv_symm (x : spectralIntegerRing K L) :
    ((integralClosureSpectralEquiv K L).symm x : L) = (x : L) := by
  simpa only [AlgEquiv.apply_symm_apply] using
    (coe_integralClosureSpectralEquiv K L ((integralClosureSpectralEquiv K L).symm x)).symm

/-- The actual canonical integral closure in the original algebraic field
is a valuation ring, without a finiteness assumption on the extension. -/
instance integralClosure_valuationRing : ValuationRing (integralClosure R₀ L) :=
  Function.Surjective.valuationRing (integralClosureSpectralEquiv K L).symm.toRingHom
    (integralClosureSpectralEquiv K L).symm.surjective

/-- For every original field element, it or its inverse is integral. -/
theorem mem_or_inv_mem_integralClosure (x : L) :
    x ∈ integralClosure R₀ L ∨ x⁻¹ ∈ integralClosure R₀ L := by
  change IsIntegral R₀ x ∨ IsIntegral R₀ x⁻¹
  have h := (spectralIntegerRing K L).mem_or_inv_mem x
  simpa only [mem_spectralIntegerRing, ← isIntegral_iff_spectralNorm_le_one] using h

/-- The canonical inclusion of the original base integers is local. -/
instance integralClosure_algebraMap_isLocalHom :
    IsLocalHom (algebraMap R₀ (integralClosure R₀ L)) where
  map_nonunit x hx := by
    have h : IsUnit (integralClosureSpectralEquiv K L (algebraMap R₀ _ x)) :=
      hx.map (integralClosureSpectralEquiv K L).toMonoidHom
    rw [(integralClosureSpectralEquiv K L).commutes] at h
    exact (isUnit_map_iff (algebraMap R₀ (spectralIntegerRing K L)) x).mp h

end Algebraic

section Inclusions

variable {E L : Type*} [Field E] [Field L] [Algebra K E] [Algebra K L]
    [Algebra.IsAlgebraic K E] [Algebra.IsAlgebraic K L]

/-- The actual original field embedding on canonical integral closures. -/
def integralClosureInclusion (i : E →ₐ[K] L) :
    integralClosure R₀ E →ₐ[R₀] integralClosure R₀ L :=
  (i.restrictScalars R₀).mapIntegralClosure

omit [CompleteSpace K] [Algebra.IsAlgebraic K E] [Algebra.IsAlgebraic K L] in
@[simp]
theorem coe_integralClosureInclusion (i : E →ₐ[K] L) (x : integralClosure R₀ E) :
    (integralClosureInclusion K i x : L) = i (x : E) := rfl

omit [CompleteSpace K] [Algebra.IsAlgebraic K E] [Algebra.IsAlgebraic K L] in
/-- Pulling back the canonical integral closure gives exactly the original
source integral closure, without normality or finiteness assumptions. -/
theorem mem_integralClosure_inclusion_iff (i : E →ₐ[K] L) (x : E) :
    i x ∈ integralClosure R₀ L ↔ x ∈ integralClosure R₀ E :=
  isIntegral_algHom_iff (i.restrictScalars R₀) i.injective

omit [Algebra.IsAlgebraic K L] in
/-- The intersection with an original embedded algebraic subfield is
exactly its original spectral integer ring, including every finite layer. -/
theorem mem_integralClosure_embedding_iff_spectral (i : E →ₐ[K] L) (x : E) :
    i x ∈ integralClosure R₀ L ↔ x ∈ spectralIntegerRing K E := by
  exact (mem_integralClosure_inclusion_iff K i x).trans
    (isIntegral_iff_spectralNorm_le_one K x)

/-- Canonical closure inclusions and spectral integer inclusions form the
actual commuting square inside the original fields. -/
theorem integralClosureSpectralEquiv_inclusion (i : E →ₐ[K] L)
    (x : integralClosure R₀ E) :
    integralClosureSpectralEquiv K L (integralClosureInclusion K i x) =
      spectralIntegerInclusion K i (integralClosureSpectralEquiv K E x) := by
  apply Subtype.ext
  simp only [coe_integralClosureSpectralEquiv, coe_integralClosureInclusion,
    coe_spectralIntegerInclusion]

/-- The canonical closure map is local for the original maximal ideals. -/
instance integralClosureInclusion_isLocalHom (i : E →ₐ[K] L) :
    IsLocalHom (integralClosureInclusion K i) := by
  let := spectralIntegerInclusion_isLocalHom K i
  constructor
  intro x hx
  have h : IsUnit (integralClosureSpectralEquiv K L (integralClosureInclusion K i x)) :=
    hx.map (integralClosureSpectralEquiv K L).toMonoidHom
  rw [integralClosureSpectralEquiv_inclusion] at h
  have h' := (isUnit_map_iff (spectralIntegerInclusion K i) _).mp h
  have h'' : IsUnit ((integralClosureSpectralEquiv K E).symm
      (integralClosureSpectralEquiv K E x)) :=
    h'.map (integralClosureSpectralEquiv K E).symm.toMonoidHom
  simpa only [AlgEquiv.symm_apply_apply] using h''

/-- The original maximal ideal contracts to exactly the source maximal
ideal along each actual field embedding. -/
theorem integralClosureInclusion_maximalIdeal_comap (i : E →ₐ[K] L) :
    Ideal.comap (integralClosureInclusion K i).toRingHom
        (IsLocalRing.maximalIdeal (integralClosure R₀ L)) =
      IsLocalRing.maximalIdeal (integralClosure R₀ E) := by
  ext x
  change ¬ IsUnit (integralClosureInclusion K i x) ↔ ¬ IsUnit x
  exact not_congr (isUnit_map_iff (integralClosureInclusion K i) x)

/-- The actual residue map on canonical original integral closures. -/
def integralClosureResidueInclusion (i : E →ₐ[K] L) :
    IsLocalRing.ResidueField (integralClosure R₀ E) →ₐ[IsLocalRing.ResidueField R₀]
      IsLocalRing.ResidueField (integralClosure R₀ L) :=
  IsLocalRing.ResidueField.mapAlgHom' (integralClosureInclusion K i)

@[simp]
theorem integralClosureResidueInclusion_residue (i : E →ₐ[K] L)
    (x : integralClosure R₀ E) :
    integralClosureResidueInclusion K i (IsLocalRing.residue _ x) =
      IsLocalRing.residue _ (integralClosureInclusion K i x) := rfl

/-- The canonical closure and spectral integer descriptions induce the
same intrinsic residue field over the original base residue field. -/
def integralClosureSpectralResidueEquiv :
    IsLocalRing.ResidueField (integralClosure R₀ L) ≃ₐ[IsLocalRing.ResidueField R₀]
      IsLocalRing.ResidueField (spectralIntegerRing K L) :=
  IsLocalRing.ResidueField.mapAlgEquiv' (integralClosureSpectralEquiv K L)

@[simp]
theorem integralClosureSpectralResidueEquiv_residue (x : integralClosure R₀ L) :
    integralClosureSpectralResidueEquiv K (L := L) (IsLocalRing.residue _ x) =
      IsLocalRing.residue _ (integralClosureSpectralEquiv K L x) := rfl

/-- The actual residue inclusions commute with the identity-valued
canonical identifications of integer rings. -/
theorem integralClosureSpectralResidueEquiv_inclusion (i : E →ₐ[K] L)
    (z : IsLocalRing.ResidueField (integralClosure R₀ E)) :
    integralClosureSpectralResidueEquiv K (L := L)
        (integralClosureResidueInclusion K i z) =
      spectralResidueInclusion K i
        (integralClosureSpectralResidueEquiv K (L := E) z) := by
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
  simp only [integralClosureResidueInclusion_residue,
    integralClosureSpectralResidueEquiv_residue, spectralResidueInclusion_residue,
    integralClosureSpectralEquiv_inclusion]

end Inclusions

section FiniteRepresentatives

variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- Every actual infinite residue class is represented in an actual finite
subfield of the original algebraic extension. -/
theorem exists_finiteLayer_spectralResidue_preimage
    (z : IsLocalRing.ResidueField (spectralIntegerRing K L)) :
    ∃ E : FiniteLayer K L,
      ∃ y : IsLocalRing.ResidueField (spectralIntegerRing K E.val),
        spectralResidueInclusion K E.val.val y = z := by
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
  let E : FiniteLayer K L := ⟨IntermediateField.adjoin K {(x : L)},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := K) (x : L))⟩
  let y : E.val := ⟨x, IntermediateField.mem_adjoin_simple_self K (x : L)⟩
  have hy : y ∈ spectralIntegerRing K E.val := by
    have hx : IsIntegral R₀ (x : L) :=
      (isIntegral_iff_spectralNorm_le_one K (x : L)).mpr x.property
    have hyint : IsIntegral R₀ y :=
      (isIntegral_algHom_iff (E.val.val.restrictScalars R₀) E.val.val.injective).mp hx
    exact (isIntegral_iff_spectralNorm_le_one K y).mp hyint
  refine ⟨E, IsLocalRing.residue _ ⟨y, hy⟩, ?_⟩
  rw [spectralResidueInclusion_residue]
  congr 1

end FiniteRepresentatives

section ResidueStabilization

variable [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- Every sufficiently large original finite layer maps bijectively onto
the residue field of the original algebraic extension. -/
theorem IsAPF.exists_finiteLayer_spectralResidueInclusion_bijective (hL : IsAPF K L) :
    ∃ T : FiniteLayer K L, ∀ E : FiniteLayer K L, T ≤ E →
      Function.Bijective (spectralResidueInclusion K E.val.val) := by
  obtain ⟨T, hT⟩ := IsAPF.exists_finiteLayer_residueInclusion_surjective K L hL
  refine ⟨T, fun E hE => ⟨(spectralResidueInclusion K E.val.val).injective, ?_⟩⟩
  intro z
  obtain ⟨F, y, hy⟩ := exists_finiteLayer_spectralResidue_preimage K L z
  let G := FiniteLayer.sup E F
  let i := IntermediateField.inclusion (FiniteLayer.le_sup_left E F)
  let j := IntermediateField.inclusion (FiniteLayer.le_sup_right E F)
  obtain ⟨a, ha⟩ := hT E G hE (FiniteLayer.le_sup_left E F)
    (spectralResidueInclusion K j y)
  have hi : (spectralResidueInclusion K G.val.val).comp
      (spectralResidueInclusion K i) = spectralResidueInclusion K E.val.val := by
    rw [← spectralResidueInclusion_comp]
    rfl
  have hj : (spectralResidueInclusion K G.val.val).comp
      (spectralResidueInclusion K j) = spectralResidueInclusion K F.val.val := by
    rw [← spectralResidueInclusion_comp]
    rfl
  refine ⟨a, ?_⟩
  calc
    spectralResidueInclusion K E.val.val a =
        spectralResidueInclusion K G.val.val (spectralResidueInclusion K i a) :=
      (congrArg (fun f => f a) hi).symm
    _ = spectralResidueInclusion K G.val.val (spectralResidueInclusion K j y) :=
      congrArg _ ha
    _ = spectralResidueInclusion K F.val.val y := congrArg (fun f => f y) hj
    _ = z := hy

/-- The actual finite spectral residue inclusion into the canonical
integral-closure residue field of the original extension. -/
def integralClosureResidueFromLayer (E : FiniteLayer K L) :
    IsLocalRing.ResidueField (spectralIntegerRing K E.val) →ₐ[IsLocalRing.ResidueField R₀]
      IsLocalRing.ResidueField (integralClosure R₀ L) :=
  (integralClosureSpectralResidueEquiv K (L := L)).symm.toAlgHom.comp
    (spectralResidueInclusion K E.val.val)

omit [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
  [PerfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := K)).valuationSubring)] in
@[simp]
theorem integralClosureResidueFromLayer_residue (E : FiniteLayer K L)
    (x : spectralIntegerRing K E.val) :
    integralClosureResidueFromLayer K L E (IsLocalRing.residue _ x) =
      IsLocalRing.residue _ ((integralClosureSpectralEquiv K L).symm
        (spectralIntegerInclusion K E.val.val x)) := rfl

/-- Actual APF residue stabilization identifies the intrinsic canonical
residue field with that of every sufficiently large original finite layer. -/
theorem IsAPF.exists_finiteLayer_integralClosureResidue_bijective (hL : IsAPF K L) :
    ∃ T : FiniteLayer K L, ∀ E : FiniteLayer K L, T ≤ E →
      Function.Bijective (integralClosureResidueFromLayer K L E) := by
  obtain ⟨T, hT⟩ := IsAPF.exists_finiteLayer_spectralResidueInclusion_bijective K L hL
  exact ⟨T, fun E hE =>
    (integralClosureSpectralResidueEquiv K (L := L)).symm.bijective.comp (hT E hE)⟩

/-- The actual residue-stable finite layer supplied by the proved APF theorem. -/
def apfResidueLayer (hL : IsAPF K L) : FiniteLayer K L :=
  (IsAPF.exists_finiteLayer_integralClosureResidue_bijective K L hL).choose

/-- The original finite inclusion is the residue-field isomorphism; no
residue-field equivalence is assumed. -/
def integralClosureResidueEquiv (hL : IsAPF K L) (E : FiniteLayer K L)
    (hE : apfResidueLayer K L hL ≤ E) :
    IsLocalRing.ResidueField (spectralIntegerRing K E.val) ≃ₐ[IsLocalRing.ResidueField R₀]
      IsLocalRing.ResidueField (integralClosure R₀ L) :=
  AlgEquiv.ofBijective (integralClosureResidueFromLayer K L E)
    ((IsAPF.exists_finiteLayer_integralClosureResidue_bijective K L hL).choose_spec E hE)

/-- The residue isomorphism acts by the original finite residue inclusion. -/
@[simp]
theorem integralClosureResidueEquiv_apply (hL : IsAPF K L) (E : FiniteLayer K L)
    (hE : apfResidueLayer K L hL ≤ E)
    (z : IsLocalRing.ResidueField (spectralIntegerRing K E.val)) :
    integralClosureResidueEquiv K L hL E hE z = integralClosureResidueFromLayer K L E z := rfl

/-- The intrinsic residue field of the original APF algebraic extension is
perfect, without a finiteness assumption on its cardinality. -/
theorem IsAPF.perfectField_integralClosureResidue (hL : IsAPF K L) :
    PerfectField (IsLocalRing.ResidueField (integralClosure R₀ L)) := by
  let E := apfResidueLayer K L hL
  let : PerfectField (IsLocalRing.ResidueField (spectralIntegerRing K E.val)) :=
    Algebra.IsAlgebraic.perfectField (IsLocalRing.ResidueField R₀)
  exact PerfectField.of_ringEquiv (integralClosureResidueEquiv K L hL E le_rfl).toRingEquiv

end ResidueStabilization

end FontaineWintenberger
