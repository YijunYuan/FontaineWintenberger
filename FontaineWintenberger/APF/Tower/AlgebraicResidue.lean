/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.Tower.Residue
public import FontaineWintenberger.LocalField.Basic

/-!
# The intrinsic residue field of an algebraic APF extension

The canonical integral closure of the base integer ring in the
algebraic field is a valuation ring. Its finite residue inclusions
become isomorphisms on the APF residue-stable tail.

The finite-layer representative argument generalizes the diagonal-layer
argument in `FalseTateExtension.Padic.FiniteGaloisStructure`.

## Main definitions

* `integralClosureSpectralEquiv`: The canonical integral closure and the spectral integer ring are
  identified by the identity in the algebraic field.
* `integralClosureInclusion`: The field embedding on canonical integral closures.
* `integralClosureResidueInclusion`: The residue map on canonical integral closures.
* `integralClosureSpectralResidueEquiv`: The canonical closure and spectral integer descriptions
  induce the same intrinsic residue field over the base residue field.
* `integralClosureResidueFromLayer`: The finite spectral residue inclusion into the canonical
  integral-closure residue field of the extension.
* `apfResidueLayer`: The residue-stable finite intermediate field supplied by the proved APF
  theorem.
* `integralClosureResidueEquiv`: The finite inclusion is the residue-field isomorphism; no
  residue-field equivalence is assumed.

## Main results

* `mem_or_inv_mem_integralClosure`: For every field element, it or its inverse is integral.
* `mem_integralClosure_inclusion_iff`: Pulling back the canonical integral closure gives exactly the
  integral closure, without normality or finiteness assumptions.
* `mem_integralClosure_embedding_iff_spectral`: The intersection with an embedded algebraic subfield
  is exactly its spectral integer ring, including every finite intermediate field.
* `integralClosureSpectralEquiv_inclusion`: Canonical closure inclusions and spectral integer
  inclusions form the commuting square inside the fields.
* `integralClosureInclusion_maximalIdeal_comap`: The maximal ideal contracts to exactly the maximal
  ideal along each field embedding.
* `integralClosureSpectralResidueEquiv_inclusion`: The residue inclusions commute with the
  identity-valued canonical identifications of integer rings.
* `exists_finiteIntermediateField_spectralResidue_preimage`: Every infinite residue class is
  represented in a finite subfield of the algebraic extension.
* `IsAPF.exists_finiteIntermediateField_spectralResidueInclusion_bijective`: Every sufficiently
  large finite intermediate field maps bijectively onto the residue field of the algebraic
  extension.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §1 (extensions arithmétiquement profinies).
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]

section Algebraic

variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- The canonical integral closure and the spectral integer ring
are identified by the identity in the algebraic field. -/
def integralClosureSpectralEquiv :
    integralClosure 𝒪[K] L ≃ₐ[𝒪[K]] spectralIntegerRing K L :=
  IsIntegralClosure.equiv 𝒪[K] (integralClosure 𝒪[K] L) L (spectralIntegerRing K L)

@[simp]
theorem coe_integralClosureSpectralEquiv (x : integralClosure 𝒪[K] L) :
    (integralClosureSpectralEquiv K L x : L) = (x : L) :=
  IsIntegralClosure.algebraMap_equiv 𝒪[K] (integralClosure 𝒪[K] L) L
    (spectralIntegerRing K L) x

@[simp]
theorem coe_integralClosureSpectralEquiv_symm (x : spectralIntegerRing K L) :
    ((integralClosureSpectralEquiv K L).symm x : L) = (x : L) := by
  simpa only [AlgEquiv.apply_symm_apply] using
    (coe_integralClosureSpectralEquiv K L ((integralClosureSpectralEquiv K L).symm x)).symm

/-- The canonical integral closure in the algebraic field
is a valuation ring, without a finiteness assumption on the extension. -/
instance integralClosure_valuationRing : ValuationRing (integralClosure 𝒪[K] L) :=
  Function.Surjective.valuationRing (integralClosureSpectralEquiv K L).symm.toRingHom
    (integralClosureSpectralEquiv K L).symm.surjective

/-- For every field element, it or its inverse is integral. -/
theorem mem_or_inv_mem_integralClosure (x : L) :
    x ∈ integralClosure 𝒪[K] L ∨ x⁻¹ ∈ integralClosure 𝒪[K] L := by
  change IsIntegral 𝒪[K] x ∨ IsIntegral 𝒪[K] x⁻¹
  have h := (spectralIntegerRing K L).mem_or_inv_mem x
  simpa only [mem_spectralIntegerRing, ← isIntegral_iff_spectralNorm_le_one] using h

/-- The canonical inclusion of the base integers is local. -/
instance integralClosure_algebraMap_isLocalHom :
    IsLocalHom (algebraMap 𝒪[K] (integralClosure 𝒪[K] L)) where
  map_nonunit x hx := by
    have h : IsUnit (integralClosureSpectralEquiv K L (algebraMap 𝒪[K] _ x)) :=
      hx.map (integralClosureSpectralEquiv K L).toMonoidHom
    rw [(integralClosureSpectralEquiv K L).commutes] at h
    exact (isUnit_map_iff (algebraMap 𝒪[K] (spectralIntegerRing K L)) x).mp h

end Algebraic

section Inclusions

variable {E L : Type*} [Field E] [Field L] [Algebra K E] [Algebra K L]
    [Algebra.IsAlgebraic K E] [Algebra.IsAlgebraic K L]

/-- The field embedding on canonical integral closures. -/
def integralClosureInclusion (i : E →ₐ[K] L) :
    integralClosure 𝒪[K] E →ₐ[𝒪[K]] integralClosure 𝒪[K] L :=
  (i.restrictScalars 𝒪[K]).mapIntegralClosure

omit [Algebra.IsAlgebraic K E] [Algebra.IsAlgebraic K L] in
@[simp]
theorem coe_integralClosureInclusion (i : E →ₐ[K] L) (x : integralClosure 𝒪[K] E) :
    (integralClosureInclusion K i x : L) = i (x : E) := rfl

omit [Algebra.IsAlgebraic K E] [Algebra.IsAlgebraic K L] in
/-- Pulling back the canonical integral closure gives exactly the
integral closure, without normality or finiteness assumptions. -/
theorem mem_integralClosure_inclusion_iff (i : E →ₐ[K] L) (x : E) :
    i x ∈ integralClosure 𝒪[K] L ↔ x ∈ integralClosure 𝒪[K] E :=
  isIntegral_algHom_iff (i.restrictScalars 𝒪[K]) i.injective

omit [Algebra.IsAlgebraic K L] in
/-- The intersection with an embedded algebraic subfield is
exactly its spectral integer ring, including every finite intermediate field. -/
theorem mem_integralClosure_embedding_iff_spectral (i : E →ₐ[K] L) (x : E) :
    i x ∈ integralClosure 𝒪[K] L ↔ x ∈ spectralIntegerRing K E := by
  exact (mem_integralClosure_inclusion_iff K i x).trans
    (isIntegral_iff_spectralNorm_le_one K x)

/-- Canonical closure inclusions and spectral integer inclusions form the
commuting square inside the fields. -/
theorem integralClosureSpectralEquiv_inclusion (i : E →ₐ[K] L)
    (x : integralClosure 𝒪[K] E) :
    integralClosureSpectralEquiv K L (integralClosureInclusion K i x) =
      spectralIntegerInclusion K i (integralClosureSpectralEquiv K E x) := by
  apply Subtype.ext
  simp only [coe_integralClosureSpectralEquiv, coe_integralClosureInclusion,
    coe_spectralIntegerInclusion]

/-- The canonical closure map is local for the maximal ideals. -/
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

/-- The maximal ideal contracts to exactly the maximal
ideal along each field embedding. -/
theorem integralClosureInclusion_maximalIdeal_comap (i : E →ₐ[K] L) :
    Ideal.comap (integralClosureInclusion K i).toRingHom
        (IsLocalRing.maximalIdeal (integralClosure 𝒪[K] L)) =
      IsLocalRing.maximalIdeal (integralClosure 𝒪[K] E) := by
  ext x
  change ¬ IsUnit (integralClosureInclusion K i x) ↔ ¬ IsUnit x
  exact not_congr (isUnit_map_iff (integralClosureInclusion K i) x)

/-- The residue map on canonical integral closures. -/
def integralClosureResidueInclusion (i : E →ₐ[K] L) :
    IsLocalRing.ResidueField (integralClosure 𝒪[K] E) →ₐ[IsLocalRing.ResidueField 𝒪[K]]
      IsLocalRing.ResidueField (integralClosure 𝒪[K] L) :=
  IsLocalRing.ResidueField.mapAlgHom' (integralClosureInclusion K i)

@[simp]
theorem integralClosureResidueInclusion_residue (i : E →ₐ[K] L)
    (x : integralClosure 𝒪[K] E) :
    integralClosureResidueInclusion K i (IsLocalRing.residue _ x) =
      IsLocalRing.residue _ (integralClosureInclusion K i x) := rfl

/-- The canonical closure and spectral integer descriptions induce the
same intrinsic residue field over the base residue field. -/
def integralClosureSpectralResidueEquiv :
    IsLocalRing.ResidueField (integralClosure 𝒪[K] L) ≃ₐ[IsLocalRing.ResidueField 𝒪[K]]
      IsLocalRing.ResidueField (spectralIntegerRing K L) :=
  IsLocalRing.ResidueField.mapAlgEquiv' (integralClosureSpectralEquiv K L)

@[simp]
theorem integralClosureSpectralResidueEquiv_residue (x : integralClosure 𝒪[K] L) :
    integralClosureSpectralResidueEquiv K (L := L) (IsLocalRing.residue _ x) =
      IsLocalRing.residue _ (integralClosureSpectralEquiv K L x) := rfl

/-- The residue inclusions commute with the identity-valued
canonical identifications of integer rings. -/
theorem integralClosureSpectralResidueEquiv_inclusion (i : E →ₐ[K] L)
    (z : IsLocalRing.ResidueField (integralClosure 𝒪[K] E)) :
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

/-- Every infinite residue class is represented in a finite
subfield of the algebraic extension. -/
theorem exists_finiteIntermediateField_spectralResidue_preimage
    (z : IsLocalRing.ResidueField (spectralIntegerRing K L)) :
    ∃ E : FiniteIntermediateField K L,
      ∃ y : IsLocalRing.ResidueField (spectralIntegerRing K E.val),
        spectralResidueInclusion K E.val.val y = z := by
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
  let E : FiniteIntermediateField K L := ⟨IntermediateField.adjoin K {(x : L)},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := K) (x : L))⟩
  let y : E.val := ⟨x, IntermediateField.mem_adjoin_simple_self K (x : L)⟩
  have hy : y ∈ spectralIntegerRing K E.val := by
    have hx : IsIntegral 𝒪[K] (x : L) :=
      (isIntegral_iff_spectralNorm_le_one K (x : L)).mpr x.property
    have hyint : IsIntegral 𝒪[K] y :=
      (isIntegral_algHom_iff (E.val.val.restrictScalars 𝒪[K]) E.val.val.injective).mp hx
    exact (isIntegral_iff_spectralNorm_le_one K y).mp hyint
  refine ⟨E, IsLocalRing.residue _ ⟨y, hy⟩, ?_⟩
  rw [spectralResidueInclusion_residue]
  congr 1

end FiniteRepresentatives

section ResidueStabilization

variable [PerfectField 𝓀[K]]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- Every sufficiently large finite intermediate field maps bijectively onto
the residue field of the algebraic extension. -/
theorem IsAPF.exists_finiteIntermediateField_spectralResidueInclusion_bijective [IsAPF K L] :
    ∃ T : FiniteIntermediateField K L, ∀ E : FiniteIntermediateField K L, T ≤ E →
      Function.Bijective (spectralResidueInclusion K E.val.val) := by
  obtain ⟨T, hT⟩ := IsAPF.exists_finiteIntermediateField_residueInclusion_surjective K L
  refine ⟨T, fun E hE => ⟨(spectralResidueInclusion K E.val.val).injective, ?_⟩⟩
  intro z
  obtain ⟨F, y, hy⟩ := exists_finiteIntermediateField_spectralResidue_preimage K L z
  let G := FiniteIntermediateField.sup E F
  let i := IntermediateField.inclusion (FiniteIntermediateField.le_sup_left E F)
  let j := IntermediateField.inclusion (FiniteIntermediateField.le_sup_right E F)
  obtain ⟨a, ha⟩ := hT E G hE (FiniteIntermediateField.le_sup_left E F)
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

/-- The finite spectral residue inclusion into the canonical
integral-closure residue field of the extension. -/
def integralClosureResidueFromLayer (E : FiniteIntermediateField K L) :
    IsLocalRing.ResidueField (spectralIntegerRing K E.val) →ₐ[IsLocalRing.ResidueField 𝒪[K]]
      IsLocalRing.ResidueField (integralClosure 𝒪[K] L) :=
  (integralClosureSpectralResidueEquiv K (L := L)).symm.toAlgHom.comp
    (spectralResidueInclusion K E.val.val)

omit [PerfectField 𝓀[K]] in
@[simp]
theorem integralClosureResidueFromLayer_residue (E : FiniteIntermediateField K L)
    (x : spectralIntegerRing K E.val) :
    integralClosureResidueFromLayer K L E (IsLocalRing.residue _ x) =
      IsLocalRing.residue _ ((integralClosureSpectralEquiv K L).symm
        (spectralIntegerInclusion K E.val.val x)) := rfl

/-- Actual APF residue stabilization identifies the intrinsic canonical
residue field with that of every sufficiently large finite intermediate field. -/
theorem IsAPF.exists_finiteIntermediateField_integralClosureResidue_bijective [IsAPF K L] :
    ∃ T : FiniteIntermediateField K L, ∀ E : FiniteIntermediateField K L, T ≤ E →
      Function.Bijective (integralClosureResidueFromLayer K L E) := by
  obtain ⟨T, hT⟩ := IsAPF.exists_finiteIntermediateField_spectralResidueInclusion_bijective K L
  exact ⟨T, fun E hE =>
    (integralClosureSpectralResidueEquiv K (L := L)).symm.bijective.comp (hT E hE)⟩

/-- The residue-stable finite intermediate field supplied by the proved APF theorem. -/
def apfResidueLayer [IsAPF K L] : FiniteIntermediateField K L :=
  (IsAPF.exists_finiteIntermediateField_integralClosureResidue_bijective K L).choose

/-- The finite inclusion is the residue-field isomorphism; no
residue-field equivalence is assumed. -/
def integralClosureResidueEquiv [IsAPF K L] (E : FiniteIntermediateField K L)
    (hE : apfResidueLayer K L ≤ E) :
    IsLocalRing.ResidueField (spectralIntegerRing K E.val) ≃ₐ[IsLocalRing.ResidueField 𝒪[K]]
      IsLocalRing.ResidueField (integralClosure 𝒪[K] L) :=
  AlgEquiv.ofBijective (integralClosureResidueFromLayer K L E)
    ((IsAPF.exists_finiteIntermediateField_integralClosureResidue_bijective K L).choose_spec E hE)

/-- The residue isomorphism acts by the finite residue inclusion. -/
@[simp]
theorem integralClosureResidueEquiv_apply [IsAPF K L] (E : FiniteIntermediateField K L)
    (hE : apfResidueLayer K L ≤ E)
    (z : IsLocalRing.ResidueField (spectralIntegerRing K E.val)) :
    integralClosureResidueEquiv K L E hE z = integralClosureResidueFromLayer K L E z := rfl

/-- The intrinsic residue field of the APF algebraic extension is
perfect, without a finiteness assumption on its cardinality. -/
theorem IsAPF.perfectField_integralClosureResidue [IsAPF K L] :
    PerfectField (IsLocalRing.ResidueField (integralClosure 𝒪[K] L)) := by
  let E := apfResidueLayer K L
  let : PerfectField (IsLocalRing.ResidueField (spectralIntegerRing K E.val)) :=
    Algebra.IsAlgebraic.perfectField (IsLocalRing.ResidueField 𝒪[K])
  exact PerfectField.of_ringEquiv (integralClosureResidueEquiv K L E le_rfl).toRingEquiv

end ResidueStabilization

end FontaineWintenberger
