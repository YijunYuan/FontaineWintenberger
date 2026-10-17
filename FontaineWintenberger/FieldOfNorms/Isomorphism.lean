module

public import FontaineWintenberger.FieldOfNorms.Valued
public import FontaineWintenberger.Ramification.FieldEquiv
public import FontaineWintenberger.LocalField.UniformContinuity

/-!
# Isomorphisms of the original norm fields

Actual field isomorphisms reindex the original finite norm families.
Their original norm-sum limits and stable valuations are preserved.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

section Multiplicative

variable {K L M N : Type*} [Field K] [Field L] [Field M] [Field N]
    [Algebra K L] [Algebra K M] [Algebra K N]

namespace FiniteLayer

/-- The image of an actual finite layer under a specified field embedding. -/
def map (i : L →ₐ[K] M) (E : FiniteLayer K L) : FiniteLayer K M :=
  ⟨E.val.map i, Module.Finite.equiv (IntermediateField.equivMap E.val i).toLinearEquiv⟩

/-- The original embedding restricts to the actual finite image field. -/
def equivMap (i : L →ₐ[K] M) (E : FiniteLayer K L) : E.val ≃ₐ[K] (map i E).val :=
  IntermediateField.equivMap E.val i

@[simp]
theorem coe_equivMap (i : L →ₐ[K] M) (E : FiniteLayer K L) (x : E.val) :
    (equivMap i E x : M) = i (x : L) := rfl

theorem map_mono (i : L →ₐ[K] M) {E F : FiniteLayer K L} (hEF : E ≤ F) :
    map i E ≤ map i F := IntermediateField.map_mono i hEF

@[simp]
theorem map_id (E : FiniteLayer K L) : map (AlgHom.id K L) E = E := by
  apply Subtype.ext
  exact IntermediateField.map_id E.val

@[simp]
theorem map_map (i : L →ₐ[K] M) (j : M →ₐ[K] N) (E : FiniteLayer K L) :
    map j (map i E) = map (j.comp i) E := by
  apply Subtype.ext
  exact IntermediateField.map_map E.val i j

/-- A field isomorphism gives the actual order isomorphism on finite layers. -/
def mapOrderIso (e : L ≃ₐ[K] M) : FiniteLayer K L ≃o FiniteLayer K M where
  toFun := map e.toAlgHom
  invFun := map e.symm.toAlgHom
  left_inv E := by simp
  right_inv E := by simp
  map_rel_iff' := by
    intro E F
    constructor
    · intro h x hx
      exact (F.val.map_mem_map e.toAlgHom).mp
        (h ((E.val.map_mem_map e.toAlgHom).mpr hx))
    · exact map_mono e.toAlgHom

/-- Actual relative field norms commute with two compatible restrictions
of the original field isomorphism, with no normality hypothesis. -/
theorem equivMap_norm (i : L →ₐ[K] M) (E F : FiniteLayer K L)
    (hEF : E ≤ F) (x : F.val) :
    equivMap i E (norm E F hEF x) =
      norm (map i E) (map i F) (map_mono i hEF) (equivMap i F x) := by
  let : Algebra E.val F.val := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
  let : Algebra (map i E).val (map i F).val :=
    (IntermediateField.inclusion (map_mono i hEF)).toRingHom.toAlgebra
  have he : (algebraMap (map i E).val (map i F).val).comp
      (equivMap i E).toRingEquiv.toRingHom =
      (equivMap i F).toRingEquiv.toRingHom.comp (algebraMap E.val F.val) := by
    ext a
    rfl
  apply (equivMap i E).symm.injective
  change (equivMap i E).symm (equivMap i E (Algebra.norm E.val x)) =
    (equivMap i E).symm (Algebra.norm (map i E).val (equivMap i F x))
  rw [AlgEquiv.symm_apply_apply]
  exact Algebra.norm_eq_of_equiv_equiv (equivMap i E).toRingEquiv
    (equivMap i F).toRingEquiv he x

end FiniteLayer

/-- The transported actual coordinates satisfy the original finite norm equations. -/
theorem normLimitMap_compatible (e : L ≃ₐ[K] M) (x : NormLimit K L)
    (E F : FiniteLayer K M) (hEF : E ≤ F) :
    FiniteLayer.norm E F hEF
        ((FiniteLayer.equivMap e.symm.toAlgHom F).symm
          (normLimitEval K L (FiniteLayer.map e.symm.toAlgHom F) x)) =
      (FiniteLayer.equivMap e.symm.toAlgHom E).symm
        (normLimitEval K L (FiniteLayer.map e.symm.toAlgHom E) x) := by
  apply (FiniteLayer.equivMap e.symm.toAlgHom E).injective
  rw [FiniteLayer.equivMap_norm, AlgEquiv.apply_symm_apply,
    normLimitEval_norm, AlgEquiv.apply_symm_apply]

/-- The actual field isomorphism reindexes the original norm families,
with their original zero and multiplication. -/
def normLimitMap (e : L ≃ₐ[K] M) (x : NormLimit K L) : NormLimit K M :=
  (existsUnique_normLimit_of_compatible K M
    (fun E => (FiniteLayer.equivMap e.symm.toAlgHom E).symm
      (normLimitEval K L (FiniteLayer.map e.symm.toAlgHom E) x))
    (normLimitMap_compatible e x)).choose

/-- Actual evaluation of the transported family in its original finite field. -/
theorem normLimitEval_normLimitMap (e : L ≃ₐ[K] M) (x : NormLimit K L)
    (E : FiniteLayer K M) :
    normLimitEval K M E (normLimitMap e x) =
      (FiniteLayer.equivMap e.symm.toAlgHom E).symm
        (normLimitEval K L (FiniteLayer.map e.symm.toAlgHom E) x) :=
  (existsUnique_normLimit_of_compatible K M _ (normLimitMap_compatible e x)).choose_spec.1 E

/-- The original ambient-field formula, including finite layers moved by e. -/
@[simp]
theorem coe_normLimitEval_normLimitMap (e : L ≃ₐ[K] M) (x : NormLimit K L)
    (E : FiniteLayer K M) :
    (normLimitEval K M E (normLimitMap e x) : M) =
      e (normLimitEval K L (FiniteLayer.map e.symm.toAlgHom E) x : L) := by
  apply e.symm.injective
  rw [AlgEquiv.symm_apply_apply, normLimitEval_normLimitMap]
  exact congrArg (fun z : (FiniteLayer.map e.symm.toAlgHom E).val => (z : L))
    ((FiniteLayer.equivMap e.symm.toAlgHom E).apply_symm_apply _)

@[simp]
theorem normLimitMap_zero (e : L ≃ₐ[K] M) : normLimitMap e (0 : NormLimit K L) = 0 := by
  apply NormLimit.ext K M
  intro E
  rw [normLimitEval_normLimitMap]
  simp

@[simp]
theorem normLimitMap_one (e : L ≃ₐ[K] M) : normLimitMap e (1 : NormLimit K L) = 1 := by
  apply NormLimit.ext K M
  intro E
  rw [normLimitEval_normLimitMap]
  simp

theorem normLimitMap_mul (e : L ≃ₐ[K] M) (x y : NormLimit K L) :
    normLimitMap e (x * y) = normLimitMap e x * normLimitMap e y := by
  apply NormLimit.ext K M
  intro E
  simp only [map_mul, normLimitEval_normLimitMap]

@[simp]
theorem normLimitMap_symm_apply (e : L ≃ₐ[K] M) (x : NormLimit K L) :
    normLimitMap e.symm (normLimitMap e x) = x := by
  apply NormLimit.ext K L
  intro E
  apply Subtype.val_injective
  rw [coe_normLimitEval_normLimitMap, coe_normLimitEval_normLimitMap]
  simp only [AlgEquiv.symm_apply_apply]
  exact congrArg (fun D : FiniteLayer K L => (normLimitEval K L D x : L))
    ((FiniteLayer.mapOrderIso e).left_inv E)

@[simp]
theorem normLimitMap_apply_symm (e : L ≃ₐ[K] M) (x : NormLimit K M) :
    normLimitMap e (normLimitMap e.symm x) = x :=
  normLimitMap_symm_apply e.symm x

@[simp]
theorem normLimitMap_refl (x : NormLimit K L) :
    normLimitMap (AlgEquiv.refl : L ≃ₐ[K] L) x = x := by
  apply NormLimit.ext K L
  intro E
  apply Subtype.val_injective
  rw [coe_normLimitEval_normLimitMap]
  exact congrArg (fun D : FiniteLayer K L => (normLimitEval K L D x : L))
    (FiniteLayer.map_id E)

/-- The original coordinate transports respect composition. -/
theorem normLimitMap_trans (e : L ≃ₐ[K] M) (f : M ≃ₐ[K] N) (x : NormLimit K L) :
    normLimitMap f (normLimitMap e x) = normLimitMap (e.trans f) x := by
  apply NormLimit.ext K N
  intro E
  apply Subtype.val_injective
  rw [coe_normLimitEval_normLimitMap, coe_normLimitEval_normLimitMap,
    coe_normLimitEval_normLimitMap]
  exact congrArg (fun D : FiniteLayer K L => f (e (normLimitEval K L D x : L)))
    (FiniteLayer.map_map f.symm.toAlgHom e.symm.toAlgHom E)

/-- The transported norm families form a multiplicative equivalence on
the same original carriers, before any APF or additive assumptions. -/
def normLimitMulEquiv (e : L ≃ₐ[K] M) : NormLimit K L ≃* NormLimit K M where
  toFun := normLimitMap e
  invFun := normLimitMap e.symm
  left_inv := normLimitMap_symm_apply e
  right_inv := normLimitMap_apply_symm e
  map_mul' := normLimitMap_mul e

@[simp]
theorem normLimitMulEquiv_apply (e : L ≃ₐ[K] M) (x : NormLimit K L) :
    normLimitMulEquiv e x = normLimitMap e x := rfl

/-- The actual finite-layer map restricted to the original upper tail. -/
def FiniteLayer.mapIci (i : L →ₐ[K] M) (E : FiniteLayer K L) (F : Set.Ici E) :
    Set.Ici (FiniteLayer.map i E) :=
  ⟨FiniteLayer.map i F.val, FiniteLayer.map_mono i F.property⟩

/-- A field isomorphism takes the original finite upper-tail filter to
the corresponding upper-tail filter. -/
theorem FiniteLayer.tendsto_mapIci (e : L ≃ₐ[K] M) (E : FiniteLayer K L) :
    Filter.Tendsto (FiniteLayer.mapIci e.toAlgHom E) Filter.atTop Filter.atTop := by
  apply Filter.tendsto_Ici_atTop.mpr
  have hv : Filter.Tendsto (Subtype.val : Set.Ici E → FiniteLayer K L)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_Ici_atTop.mp (Filter.tendsto_id :
      Filter.Tendsto (id : Set.Ici E → Set.Ici E) Filter.atTop Filter.atTop)
  exact (FiniteLayer.mapOrderIso e).tendsto_atTop.comp hv

/-- Original norm-sum nets are taken to the original target nets by the
actual finite field restrictions and actual finite-layer reindexing. -/
theorem normSumNet_normLimitMap (e : L ≃ₐ[K] M) (x y : NormLimit K L)
    (E : FiniteLayer K M) (F : Set.Ici E) :
    normSumNet K M E (normLimitMap e x) (normLimitMap e y) F =
      (FiniteLayer.equivMap e.symm.toAlgHom E).symm
        (normSumNet K L (FiniteLayer.map e.symm.toAlgHom E) x y
          (FiniteLayer.mapIci e.symm.toAlgHom E F)) := by
  apply (FiniteLayer.equivMap e.symm.toAlgHom E).injective
  have hEF : E ≤ F.val := F.property
  have hm := FiniteLayer.map_mono e.symm.toAlgHom hEF
  change (FiniteLayer.equivMap e.symm.toAlgHom E)
      (FiniteLayer.norm E F.val hEF
        (normLimitEval K M F.val (normLimitMap e x) +
          normLimitEval K M F.val (normLimitMap e y))) =
    (FiniteLayer.equivMap e.symm.toAlgHom E)
      ((FiniteLayer.equivMap e.symm.toAlgHom E).symm
        (FiniteLayer.norm _ _ hm
          (normLimitEval K L (FiniteLayer.map e.symm.toAlgHom F.val) x +
            normLimitEval K L (FiniteLayer.map e.symm.toAlgHom F.val) y)))
  rw [FiniteLayer.equivMap_norm, map_add, normLimitEval_normLimitMap,
    normLimitEval_normLimitMap, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply,
    AlgEquiv.apply_symm_apply]

end Multiplicative


section ValuedFields

open Filter

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable {L M : Type*} [Field L] [Field M] [Algebra K L] [Algebra K M]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable K M]

omit [PerfectField (IsLocalRing.ResidueField
  (NormedField.valuation (K := K)).valuationSubring)] in
/-- Original finite field isomorphisms preserve the actual normalized
DVR valuations, on integral and nonintegral elements alike. -/
theorem spectral_normalizedValuation_algEquiv [FiniteDimensional K L]
    [FiniteDimensional K M] (e : L ≃ₐ[K] M) (x : L) :
    (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K M)).valuation M (e x) =
      (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K L)).valuation L x := by
  have hi (a : spectralIntegerRing K L) :
      (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K M)).valuation M
          (e (a : L)) =
        (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K L)).valuation L
          (a : L) := by
    rw [← coe_spectralIntegerRingEquiv K e a]
    change (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K M)).valuation M
        (algebraMap (spectralIntegerRing K M) M (spectralIntegerRingEquiv K e a)) =
      (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K L)).valuation L
        (algebraMap (spectralIntegerRing K L) L a)
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDiscreteValuationRing.intValuation_maximalIdeal,
      IsDiscreteValuationRing.intValuation_maximalIdeal, spectralIntegerRingEquiv_addVal]
  rcases (spectralIntegerRing K L).mem_or_inv_mem x with hx | hx
  · exact hi ⟨x, hx⟩
  · have h := hi ⟨x⁻¹, hx⟩
    simpa only [map_inv₀, inv_inj] using h

/-- The literal reindexing preserves the original stable normalized
valuation, using genuine finite coordinates on both stable tails. -/
theorem normLimitValuation_normLimitMap (hL : IsAPF K L) (hM : IsAPF K M)
    (e : L ≃ₐ[K] M) (x : NormLimit K L) :
    normLimitValuation K M hM (normLimitMap e x) = normLimitValuation K L hL x := by
  obtain ⟨D, hD⟩ := IsAPF.exists_normLimitValuation_eq_coordinate K L hL
  obtain ⟨E, hE⟩ := IsAPF.exists_normLimitValuation_eq_coordinate K M hM
  let F := FiniteLayer.sup E (FiniteLayer.map e.toAlgHom D)
  let P := FiniteLayer.map e.symm.toAlgHom F
  have hDP : D ≤ P := by
    calc
      D = FiniteLayer.map e.symm.toAlgHom (FiniteLayer.map e.toAlgHom D) :=
        ((FiniteLayer.mapOrderIso e).left_inv D).symm
      _ ≤ P := FiniteLayer.map_mono e.symm.toAlgHom (FiniteLayer.le_sup_right E _)
  rw [hE F (FiniteLayer.le_sup_left E _) (normLimitMap e x), hD P hDP x]
  change (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K F.val)).valuation
      F.val (normLimitEval K M F (normLimitMap e x)) =
    (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K P.val)).valuation P.val
      (normLimitEval K L P x)
  rw [normLimitEval_normLimitMap]
  exact spectral_normalizedValuation_algEquiv K
    (FiniteLayer.equivMap e.symm.toAlgHom F).symm (normLimitEval K L P x)

/-- Continuity of the actual finite restrictions and cofinal reindexing
take the original source sum-net limits to the original target limits. -/
theorem normLimitMap_add (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]
    (hL : IsAPF K L) (hM : IsAPF K M) (e : L ≃ₐ[K] M) (x y : NormLimit K L) :
    normLimitMap e (normLimitAdd K L p hL x y) =
      normLimitAdd K M p hM (normLimitMap e x) (normLimitMap e y) := by
  apply eq_normLimitAdd_of_tendsto K M p hM (normLimitMap e x) (normLimitMap e y)
  intro E
  let D := FiniteLayer.map e.symm.toAlgHom E
  let := spectralNorm.nontriviallyNormedField K E.val
  let := spectralNorm.nontriviallyNormedField K D.val
  let := spectralNorm.normedAlgebra K E.val
  let := spectralNorm.normedAlgebra K D.val
  have hc : Continuous (FiniteLayer.equivMap e.symm.toAlgHom E).symm :=
    (FiniteLayer.equivMap e.symm.toAlgHom E).symm.toLinearEquiv.toLinearMap
      |>.continuous_of_finiteDimensional
  rw [normLimitEval_normLimitMap]
  have ht := hc.continuousAt.tendsto.comp
    ((tendsto_normSumNet_normLimitAdd K L p hL x y D).comp
      (FiniteLayer.tendsto_mapIci e.symm E))
  convert ht using 1
  funext F
  exact normSumNet_normLimitMap e x y E F

variable (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]

/-- An actual field isomorphism induces a ring isomorphism between the
same original norm fields with their already constructed field structures. -/
def normLimitRingEquiv (hL : IsAPF K L) (hM : IsAPF K M)
    (hInfiniteL : ¬ Module.Finite K L) (hInfiniteM : ¬ Module.Finite K M)
    (e : L ≃ₐ[K] M) :
    letI := normLimitField K L p hL hInfiniteL
    letI := normLimitField K M p hM hInfiniteM
    NormLimit K L ≃+* NormLimit K M := by
  letI := normLimitField K L p hL hInfiniteL
  letI := normLimitField K M p hM hInfiniteM
  exact { normLimitMulEquiv e with
    map_add' := normLimitMap_add K p hL hM e }

@[simp]
theorem normLimitRingEquiv_apply (hL : IsAPF K L) (hM : IsAPF K M)
    (hInfiniteL : ¬ Module.Finite K L) (hInfiniteM : ¬ Module.Finite K M)
    (e : L ≃ₐ[K] M) (x : NormLimit K L) :
    letI := normLimitField K L p hL hInfiniteL
    letI := normLimitField K M p hM hInfiniteM
    normLimitRingEquiv K p hL hM hInfiniteL hInfiniteM e x = normLimitMap e x := rfl

/-- The actual original automorphism group acts by ring automorphisms
of the original norm field, with literal coordinate transport. -/
def normLimitAut (hL : IsAPF K L) (hInfinite : ¬ Module.Finite K L) :
    letI := normLimitField K L p hL hInfinite
    (L ≃ₐ[K] L) →* (NormLimit K L ≃+* NormLimit K L) := by
  letI := normLimitField K L p hL hInfinite
  exact {
    toFun := normLimitRingEquiv K p hL hL hInfinite hInfinite
    map_one' := by
      apply RingEquiv.ext
      intro x
      exact normLimitMap_refl x
    map_mul' := by
      intro e f
      apply RingEquiv.ext
      intro x
      exact (normLimitMap_trans f e x).symm }

@[simp]
theorem normLimitAut_apply (hL : IsAPF K L) (hInfinite : ¬ Module.Finite K L)
    (e : L ≃ₐ[K] L) (x : NormLimit K L) :
    letI := normLimitField K L p hL hInfinite
    normLimitAut K p hL hInfinite e x = normLimitMap e x := rfl

/-- The ring isomorphism is uniformly continuous for the existing
valuation uniformities on the original two fields. -/
theorem uniformContinuous_normLimitRingEquiv (hL : IsAPF K L) (hM : IsAPF K M)
    (hInfiniteL : ¬ Module.Finite K L) (hInfiniteM : ¬ Module.Finite K M)
    (e : L ≃ₐ[K] M) :
    letI := normLimitField K L p hL hInfiniteL
    letI := normLimitField K M p hM hInfiniteM
    letI := normLimitValued K L p hL hInfiniteL
    letI := normLimitValued K M p hM hInfiniteM
    UniformContinuous (normLimitRingEquiv K p hL hM hInfiniteL hInfiniteM e) := by
  let := normLimitField K L p hL hInfiniteL
  let := normLimitField K M p hM hInfiniteM
  let := normLimitValued K L p hL hInfiniteL
  let := normLimitValued K M p hM hInfiniteM
  apply valuedRingEquiv_uniformContinuous
  intro x
  change normLimitValuation K M hM (normLimitMap e x) = normLimitValuation K L hL x
  exact normLimitValuation_normLimitMap K hL hM e x

/-- The literal norm-field isomorphism and its literal inverse preserve
the existing uniform spaces; no alternate topology is introduced. -/
def normLimitUniformEquiv (hL : IsAPF K L) (hM : IsAPF K M)
    (hInfiniteL : ¬ Module.Finite K L) (hInfiniteM : ¬ Module.Finite K M)
    (e : L ≃ₐ[K] M) :
    letI := normLimitField K L p hL hInfiniteL
    letI := normLimitField K M p hM hInfiniteM
    letI := normLimitValued K L p hL hInfiniteL
    letI := normLimitValued K M p hM hInfiniteM
    NormLimit K L ≃ᵤ NormLimit K M := by
  letI := normLimitField K L p hL hInfiniteL
  letI := normLimitField K M p hM hInfiniteM
  letI := normLimitValued K L p hL hInfiniteL
  letI := normLimitValued K M p hM hInfiniteM
  exact {
    toEquiv := (normLimitRingEquiv K p hL hM hInfiniteL hInfiniteM e).toEquiv
    uniformContinuous_toFun :=
      uniformContinuous_normLimitRingEquiv K p hL hM hInfiniteL hInfiniteM e
    uniformContinuous_invFun :=
      uniformContinuous_normLimitRingEquiv K p hM hL hInfiniteM hInfiniteL e.symm }

@[simp]
theorem normLimitUniformEquiv_apply (hL : IsAPF K L) (hM : IsAPF K M)
    (hInfiniteL : ¬ Module.Finite K L) (hInfiniteM : ¬ Module.Finite K M)
    (e : L ≃ₐ[K] M) (x : NormLimit K L) :
    letI := normLimitField K L p hL hInfiniteL
    letI := normLimitField K M p hM hInfiniteM
    letI := normLimitValued K L p hL hInfiniteL
    letI := normLimitValued K M p hM hInfiniteM
    normLimitUniformEquiv K p hL hM hInfiniteL hInfiniteM e x = normLimitMap e x := rfl

/-- Every actual original automorphism acts by an automorphism preserving
the original stable normalized valuation. -/
theorem normLimitAut_valuation (hL : IsAPF K L) (hInfinite : ¬ Module.Finite K L)
    (e : L ≃ₐ[K] L) (x : NormLimit K L) :
    letI := normLimitField K L p hL hInfinite
    normLimitValuation K L hL (normLimitAut K p hL hInfinite e x) =
      normLimitValuation K L hL x :=
  normLimitValuation_normLimitMap K hL hL e x

end ValuedFields

end FontaineWintenberger
