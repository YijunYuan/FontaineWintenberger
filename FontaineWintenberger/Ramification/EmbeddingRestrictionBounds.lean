module

public import FontaineWintenberger.Ramification.EmbeddingFiniteBase
public import FontaineWintenberger.Ramification.EmbeddingFiberTate

/-!
# Restriction bounds over the original finite normed base

Finite-base composition identifies the relative Herbrand function using the
original compatible norm on the smaller field. Actual field-range equivalences
then transport the finite fixing-subgroup comparison.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

section OriginalFieldImages

variable (K M F Ω : Type*) [Field K] [Field M] [Field F] [Field Ω]
    [Algebra K M] [Algebra K F] [Algebra K Ω] [Algebra M F] [Algebra M Ω]
    [IsScalarTower K M F] [IsScalarTower K M Ω]

/-- The original base image lies in the actual image of each original
base-linear embedding of the upper field. -/
theorem fieldRange_base_le (i : F →ₐ[M] Ω) :
    (IsScalarTower.toAlgHom K M Ω).fieldRange ≤ (i.restrictScalars K).fieldRange := by
  rintro x ⟨m, rfl⟩
  exact ⟨algebraMap M F m, i.commutes m⟩

end OriginalFieldImages

section OriginalFiniteBase

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable (M : Type*) [NontriviallyNormedField M] [IsUltrametricDist M]
    [NormedAlgebra K M] [CompleteSpace M] [FiniteDimensional K M]
    [Algebra.IsSeparable K M]
variable (F : Type*) [Field F] [Algebra K F] [Algebra M F] [IsScalarTower K M F]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]

/-- The intrinsic relative function over the actual original finite
normed base is the absolute function composed with its actual inverse. -/
theorem apfPsi_eq_absolute_comp_apfPhi_of_normedAlgebra (u : ℝ) :
    letI := normedAlgebra_unitBall_isDiscreteValuationRing K M
    letI := Algebra.isSeparable_tower_top_of_isSeparable K M F
    apfPsi M F u = apfPsi K F (apfPhi K M (isAPF_of_finite K M) u) := by
  let := normedAlgebra_unitBall_isDiscreteValuationRing K M
  let := Algebra.isSeparable_tower_top_of_isSeparable K M F
  have h := IsAPF.apfPsi_finiteBase_comp_of_normedAlgebra K M F
    (isAPF_of_finite K F) (apfPhi K M (isAPF_of_finite K M) u)
  rwa [apfPsi_apfPhi] at h

end OriginalFiniteBase

section OriginalAmbientBase

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable (M : Type*) [NontriviallyNormedField M] [IsUltrametricDist M]
    [NormedAlgebra K M] [CompleteSpace M] [FiniteDimensional K M]
    [Algebra.IsSeparable K M]
variable (F Ω : Type*) [Field F] [Field Ω] [Algebra K F] [Algebra K Ω]
    [Algebra M F] [Algebra M Ω] [IsScalarTower K M F] [IsScalarTower K M Ω]
    [FiniteDimensional K F] [FiniteDimensional K Ω]
    [Algebra.IsSeparable K F] [IsGalois K Ω]

local notation "jM" => IsScalarTower.toAlgHom K M Ω

/-- The fixing-subgroup change of parameter computes the actual original
relative function, without changing the norm on the abstract smaller field. -/
theorem apfPsi_originalBase_eq_fixing_herbrand (i : F →ₐ[M] Ω)
    {u : ℝ} (hu : -1 ≤ u) :
    letI := normedAlgebra_unitBall_isDiscreteValuationRing K M
    letI := Algebra.isSeparable_tower_top_of_isSeparable K M F
    letI : FiniteDimensional K (jM).fieldRange :=
      Module.Finite.equiv (jM).equivFieldRange.toLinearEquiv
    letI : FiniteDimensional K (i.restrictScalars K).fieldRange :=
      Module.Finite.equiv (i.restrictScalars K).equivFieldRange.toLinearEquiv
    apfPsi M F u =
      herbrandFunction (R := spectralIntegerRing K Ω) (i.restrictScalars K).fieldRange.fixingSubgroup
        (inverseHerbrandFunction (R := spectralIntegerRing K Ω) (jM).fieldRange.fixingSubgroup u) := by
  let := normedAlgebra_unitBall_isDiscreteValuationRing K M
  let := Algebra.isSeparable_tower_top_of_isSeparable K M F
  let : FiniteDimensional K (jM).fieldRange :=
    Module.Finite.equiv (jM).equivFieldRange.toLinearEquiv
  let : FiniteDimensional K (i.restrictScalars K).fieldRange :=
    Module.Finite.equiv (i.restrictScalars K).equivFieldRange.toLinearEquiv
  rw [apfPsi_eq_absolute_comp_apfPhi_of_normedAlgebra K M F,
    apfPhi_algEquiv K M (jM).equivFieldRange (isAPF_of_finite K M)
      (isAPF_of_finite K (jM).fieldRange),
    apfPsi_algEquiv K F (i.restrictScalars K).equivFieldRange]
  have hv := apfPhi_mem_Ici K (jM).fieldRange (isAPF_of_finite K (jM).fieldRange) hu
  rw [apfPsi_eq_subgroup_herbrand_comp_inverse_of_finiteGalois K Ω
      (i.restrictScalars K).fieldRange hv,
    apfPhi_eq_herbrand_comp_subgroup_inverse_of_finiteGalois K Ω (jM).fieldRange hu,
    inverseHerbrandFunction_herbrandFunction _ (inverseHerbrandFunction_mem_Ici _ u)]

/-- The original smaller field, with its actual supplied compatible norm,
gives the restriction inequality for arbitrary moved upper images. -/
theorem embeddingNumber_restriction_le_apfPsi_of_normedAlgebra
    (i : F →ₐ[M] Ω) (s : Ω ≃ₐ[K] Ω)
    (hs : s.toAlgHom.comp jM ≠ jM) :
    letI := normedAlgebra_unitBall_isDiscreteValuationRing K M
    letI := Algebra.isSeparable_tower_top_of_isSeparable K M F
    embeddingRamificationNumber K (s.toAlgHom.comp (i.restrictScalars K))
        (i.restrictScalars K) ≤
      (apfPsi M F (embeddingRamificationNumber K (s.toAlgHom.comp jM) jM).toReal : EReal) := by
  let := normedAlgebra_unitBall_isDiscreteValuationRing K M
  let := Algebra.isSeparable_tower_top_of_isSeparable K M F
  let E₀ := (jM).fieldRange
  let F₀ := (i.restrictScalars K).fieldRange
  let : FiniteDimensional K E₀ := Module.Finite.equiv (jM).equivFieldRange.toLinearEquiv
  let : FiniteDimensional K F₀ :=
    Module.Finite.equiv (i.restrictScalars K).equivFieldRange.toLinearEquiv
  have hE := embeddingNumber_precomp_algEquiv K (jM).equivFieldRange
    (s.toAlgHom.comp E₀.val) E₀.val
  have hF := embeddingNumber_precomp_algEquiv K (i.restrictScalars K).equivFieldRange
    (s.toAlgHom.comp F₀.val) F₀.val
  have hsE : s.toAlgHom.comp E₀.val ≠ E₀.val := by
    intro he
    exact hs (congrArg (fun f : E₀ →ₐ[K] Ω => f.comp (jM).equivFieldRange.toAlgHom) he)
  have hu : -1 ≤ (embeddingRamificationNumber K (s.toAlgHom.comp jM) jM).toReal := by
    obtain ⟨u, hu⟩ := embeddingRamificationNumber_exists_real K hs
    have hb := neg_one_le_embeddingRamificationNumber K (s.toAlgHom.comp jM) jM
    rw [hu, EReal.toReal_coe]
    rw [hu] at hb
    exact EReal.coe_le_coe_iff.mp (show ((-1 : ℝ) : EReal) ≤ (u : EReal) by
      simpa only [EReal.coe_neg, EReal.coe_one] using hb)
  have hbound := embeddingNumber_restriction_le_herbrand_composite K Ω E₀ F₀
    (fieldRange_base_le K M F Ω i) s hsE
  rw [← hE, ← hF] at hbound
  exact hbound.trans_eq (congrArg (fun r : ℝ => (r : EReal))
    (apfPsi_originalBase_eq_fixing_herbrand K M F Ω i hu).symm)

end OriginalAmbientBase

section OriginalClosureLift

variable (K : Type*) [Field K] (F : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K F]

/-- The actual canonical finite normal closure contains a genuine lift
of every original embedding of the upper field. -/
theorem exists_normalClosure_aut_lift (σ : F →ₐ[K] SeparableClosure K) :
    ∃ s : (finiteGaloisNormalClosure K F) ≃ₐ[K] (finiteGaloisNormalClosure K F),
      (finiteGaloisNormalClosure K F).toIntermediateField.val.comp
        (s.toAlgHom.comp (IntermediateField.inclusion (le_finiteGaloisNormalClosure K F))) = σ := by
  let Ω := finiteGaloisNormalClosure K F
  let F₀ := IntermediateField.restrict (le_finiteGaloisNormalClosure K F)
  let eF := IntermediateField.restrictAlgEquiv (le_finiteGaloisNormalClosure K F)
  obtain ⟨s, hs⟩ := exists_aut_extends_intermediate_embedding K Ω F₀
    (restrictedNormalClosureEmbedding K F σ)
  refine ⟨s, AlgHom.ext fun x => ?_⟩
  have h := congrArg (fun z : Ω => (z : SeparableClosure K)) (hs (eF x))
  change (s (IntermediateField.inclusion (le_finiteGaloisNormalClosure K F) x) :
    SeparableClosure K) = σ (eF.symm (eF x)) at h
  rw [eF.symm_apply_apply] at h
  exact h

end OriginalClosureLift

section OriginalClosureBound

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
    (E F : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [FiniteDimensional K F] (hEF : E ≤ F)

/-- The original finite fields and their actual separable-closure embeddings
satisfy the full relative Herbrand restriction bound. -/
theorem closureEmbeddingNumber_restriction_le_apfPsi
    (σ : F →ₐ[K] SeparableClosure K)
    (hs : σ.comp (IntermediateField.inclusion hEF) ≠ E.val) :
    letI := spectralNorm.nontriviallyNormedField K E
    letI := spectralNorm.normedAlgebra K E
    letI := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
      (isNonarchimedean_spectralNorm (K := K) (L := E))
    letI : CompleteSpace E := FiniteDimensional.complete K E
    letI := normedAlgebra_unitBall_isDiscreteValuationRing K E
    let F' := IntermediateField.extendScalars hEF
    letI : FiniteDimensional K F' := inferInstanceAs (FiniteDimensional K F)
    letI : Algebra.IsSeparable K F' := inferInstanceAs (Algebra.IsSeparable K F)
    letI := Algebra.isSeparable_tower_top_of_isSeparable K E F'
    closureEmbeddingNumber K σ F.val ≤
      (apfPsi E F' (closureEmbeddingNumber K
        (σ.comp (IntermediateField.inclusion hEF)) E.val).toReal : EReal) := by
  let := spectralNorm.nontriviallyNormedField K E
  let := spectralNorm.normedAlgebra K E
  let := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := E))
  let : CompleteSpace E := FiniteDimensional.complete K E
  let := normedAlgebra_unitBall_isDiscreteValuationRing K E
  let F' := IntermediateField.extendScalars hEF
  let : FiniteDimensional K F' := inferInstanceAs (FiniteDimensional K F)
  let : Algebra.IsSeparable K F' := inferInstanceAs (Algebra.IsSeparable K F)
  let := Algebra.isSeparable_tower_top_of_isSeparable K E F'
  let Ω := finiteGaloisNormalClosure K F
  have hFΩ := le_finiteGaloisNormalClosure K F
  have hEΩ := hEF.trans hFΩ
  let jE := IntermediateField.inclusion hEΩ
  let : Algebra E Ω := jE.toRingHom.toAlgebra
  let : IsScalarTower K E Ω := IsScalarTower.of_algHom jE
  let i : F' →ₐ[E] Ω :=
    { (IntermediateField.inclusion hFΩ).toRingHom with commutes' := fun _ => rfl }
  obtain ⟨s, hsF⟩ := exists_normalClosure_aut_lift K F σ
  have hsE : Ω.toIntermediateField.val.comp (s.toAlgHom.comp jE) =
      σ.comp (IntermediateField.inclusion hEF) :=
    congrArg (fun f : F →ₐ[K] SeparableClosure K =>
      f.comp (IntermediateField.inclusion hEF)) hsF
  have hsn : s.toAlgHom.comp (IsScalarTower.toAlgHom K E Ω) ≠
      IsScalarTower.toAlgHom K E Ω := by
    intro he
    apply hs
    exact hsE.symm.trans (congrArg (fun f : E →ₐ[K] Ω => Ω.toIntermediateField.val.comp f) he)
  have hnumF := closureEmbeddingNumber_comp K (s.toAlgHom.comp (i.restrictScalars K))
    (i.restrictScalars K) Ω.toIntermediateField.val
  change closureEmbeddingNumber K (Ω.toIntermediateField.val.comp
    (s.toAlgHom.comp (IntermediateField.inclusion hFΩ))) F.val = _ at hnumF
  rw [hsF] at hnumF
  have hnumE := closureEmbeddingNumber_comp K (s.toAlgHom.comp jE) jE
    Ω.toIntermediateField.val
  rw [hsE] at hnumE
  change closureEmbeddingNumber K (σ.comp (IntermediateField.inclusion hEF)) E.val = _ at hnumE
  have hbound := embeddingNumber_restriction_le_apfPsi_of_normedAlgebra K E F' Ω i s hsn
  rw [← hnumF] at hbound
  change closureEmbeddingNumber K σ F.val ≤
    (apfPsi E F' (embeddingRamificationNumber K (s.toAlgHom.comp jE) jE).toReal : EReal) at hbound
  rw [← hnumE] at hbound
  exact hbound

end OriginalClosureBound

end FontaineWintenberger
