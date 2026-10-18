/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
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

namespace FiniteIntermediateField

/-- The image of an actual finite intermediate field under a specified field embedding. -/
def map (i : L →ₐ[K] M) (E : FiniteIntermediateField K L) : FiniteIntermediateField K M :=
  ⟨E.val.map i, Module.Finite.equiv (IntermediateField.equivMap E.val i).toLinearEquiv⟩

/-- The original embedding restricts to the actual finite image field. -/
def equivMap (i : L →ₐ[K] M) (E : FiniteIntermediateField K L) : E.val ≃ₐ[K] (map i E).val :=
  IntermediateField.equivMap E.val i

@[simp]
theorem coe_equivMap (i : L →ₐ[K] M) (E : FiniteIntermediateField K L) (x : E.val) :
    (equivMap i E x : M) = i (x : L) := rfl

theorem map_mono (i : L →ₐ[K] M) {E F : FiniteIntermediateField K L} (hEF : E ≤ F) :
    map i E ≤ map i F := IntermediateField.map_mono i hEF

@[simp]
theorem map_id (E : FiniteIntermediateField K L) : map (AlgHom.id K L) E = E := by
  apply Subtype.ext
  exact IntermediateField.map_id E.val

@[simp]
theorem map_map (i : L →ₐ[K] M) (j : M →ₐ[K] N) (E : FiniteIntermediateField K L) :
    map j (map i E) = map (j.comp i) E := by
  apply Subtype.ext
  exact IntermediateField.map_map E.val i j

/-- A field isomorphism gives the actual order isomorphism on finite intermediate fields. -/
def mapOrderIso (e : L ≃ₐ[K] M) : FiniteIntermediateField K L ≃o FiniteIntermediateField K M where
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
theorem equivMap_norm (i : L →ₐ[K] M) (E F : FiniteIntermediateField K L)
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

end FiniteIntermediateField

/-- The transported actual coordinates satisfy the original finite norm equations. -/
theorem FieldOfNorms.map_compatible (e : L ≃ₐ[K] M) (x : FieldOfNorms K L)
    (E F : FiniteIntermediateField K M) (hEF : E ≤ F) :
    FiniteIntermediateField.norm E F hEF
        ((FiniteIntermediateField.equivMap e.symm.toAlgHom F).symm
          (FieldOfNorms.coord K L (FiniteIntermediateField.map e.symm.toAlgHom F) x)) =
      (FiniteIntermediateField.equivMap e.symm.toAlgHom E).symm
        (FieldOfNorms.coord K L (FiniteIntermediateField.map e.symm.toAlgHom E) x) := by
  apply (FiniteIntermediateField.equivMap e.symm.toAlgHom E).injective
  rw [FiniteIntermediateField.equivMap_norm, AlgEquiv.apply_symm_apply,
    FieldOfNorms.coord_norm, AlgEquiv.apply_symm_apply]

/-- The actual field isomorphism reindexes the original norm families,
with their original zero and multiplication. -/
def FieldOfNorms.map (e : L ≃ₐ[K] M) (x : FieldOfNorms K L) : FieldOfNorms K M :=
  (existsUnique_fieldOfNorms_of_compatible K M
    (fun E => (FiniteIntermediateField.equivMap e.symm.toAlgHom E).symm
      (FieldOfNorms.coord K L (FiniteIntermediateField.map e.symm.toAlgHom E) x))
    (FieldOfNorms.map_compatible e x)).choose

/-- Actual evaluation of the transported family in its original finite field. -/
theorem FieldOfNorms.coord_fieldOfNormsMap (e : L ≃ₐ[K] M) (x : FieldOfNorms K L)
    (E : FiniteIntermediateField K M) :
    FieldOfNorms.coord K M E (FieldOfNorms.map e x) =
      (FiniteIntermediateField.equivMap e.symm.toAlgHom E).symm
        (FieldOfNorms.coord K L (FiniteIntermediateField.map e.symm.toAlgHom E) x) :=
  (existsUnique_fieldOfNorms_of_compatible K M _ (FieldOfNorms.map_compatible e x)).choose_spec.1 E

/-- The original ambient-field formula, including finite intermediate fields moved by e. -/
@[simp]
theorem coe_fieldOfNormsEval_fieldOfNormsMap (e : L ≃ₐ[K] M) (x : FieldOfNorms K L)
    (E : FiniteIntermediateField K M) :
    (FieldOfNorms.coord K M E (FieldOfNorms.map e x) : M) =
      e (FieldOfNorms.coord K L (FiniteIntermediateField.map e.symm.toAlgHom E) x : L) := by
  apply e.symm.injective
  rw [AlgEquiv.symm_apply_apply, FieldOfNorms.coord_fieldOfNormsMap]
  exact congrArg (fun z : (FiniteIntermediateField.map e.symm.toAlgHom E).val => (z : L))
    ((FiniteIntermediateField.equivMap e.symm.toAlgHom E).apply_symm_apply _)

@[simp]
theorem FieldOfNorms.map_zero (e : L ≃ₐ[K] M) : FieldOfNorms.map e (0 : FieldOfNorms K L) = 0 := by
  apply FieldOfNorms.ext K M
  intro E
  rw [FieldOfNorms.coord_fieldOfNormsMap]
  simp

@[simp]
theorem FieldOfNorms.map_one (e : L ≃ₐ[K] M) : FieldOfNorms.map e (1 : FieldOfNorms K L) = 1 := by
  apply FieldOfNorms.ext K M
  intro E
  rw [FieldOfNorms.coord_fieldOfNormsMap]
  simp

theorem FieldOfNorms.map_mul (e : L ≃ₐ[K] M) (x y : FieldOfNorms K L) :
    FieldOfNorms.map e (x * y) = FieldOfNorms.map e x * FieldOfNorms.map e y := by
  apply FieldOfNorms.ext K M
  intro E
  simp only [_root_.map_mul, FieldOfNorms.coord_fieldOfNormsMap]

@[simp]
theorem FieldOfNorms.map_symm_apply (e : L ≃ₐ[K] M) (x : FieldOfNorms K L) :
    FieldOfNorms.map e.symm (FieldOfNorms.map e x) = x := by
  apply FieldOfNorms.ext K L
  intro E
  apply Subtype.val_injective
  rw [coe_fieldOfNormsEval_fieldOfNormsMap, coe_fieldOfNormsEval_fieldOfNormsMap]
  simp only [AlgEquiv.symm_apply_apply]
  exact congrArg (fun D : FiniteIntermediateField K L => (FieldOfNorms.coord K L D x : L))
    ((FiniteIntermediateField.mapOrderIso e).left_inv E)

@[simp]
theorem FieldOfNorms.map_apply_symm (e : L ≃ₐ[K] M) (x : FieldOfNorms K M) :
    FieldOfNorms.map e (FieldOfNorms.map e.symm x) = x :=
  FieldOfNorms.map_symm_apply e.symm x

@[simp]
theorem FieldOfNorms.map_refl (x : FieldOfNorms K L) :
    FieldOfNorms.map (AlgEquiv.refl : L ≃ₐ[K] L) x = x := by
  apply FieldOfNorms.ext K L
  intro E
  apply Subtype.val_injective
  rw [coe_fieldOfNormsEval_fieldOfNormsMap]
  exact congrArg (fun D : FiniteIntermediateField K L => (FieldOfNorms.coord K L D x : L))
    (FiniteIntermediateField.map_id E)

/-- The original coordinate transports respect composition. -/
theorem FieldOfNorms.map_trans (e : L ≃ₐ[K] M) (f : M ≃ₐ[K] N) (x : FieldOfNorms K L) :
    FieldOfNorms.map f (FieldOfNorms.map e x) = FieldOfNorms.map (e.trans f) x := by
  apply FieldOfNorms.ext K N
  intro E
  apply Subtype.val_injective
  rw [coe_fieldOfNormsEval_fieldOfNormsMap, coe_fieldOfNormsEval_fieldOfNormsMap,
    coe_fieldOfNormsEval_fieldOfNormsMap]
  exact congrArg (fun D : FiniteIntermediateField K L => f (e (FieldOfNorms.coord K L D x : L)))
    (FiniteIntermediateField.map_map f.symm.toAlgHom e.symm.toAlgHom E)

/-- The transported norm families form a multiplicative equivalence on
the same original carriers, before any APF or additive assumptions. -/
def FieldOfNorms.mulEquiv (e : L ≃ₐ[K] M) : FieldOfNorms K L ≃* FieldOfNorms K M where
  toFun := FieldOfNorms.map e
  invFun := FieldOfNorms.map e.symm
  left_inv := FieldOfNorms.map_symm_apply e
  right_inv := FieldOfNorms.map_apply_symm e
  map_mul' := FieldOfNorms.map_mul e

@[simp]
theorem FieldOfNorms.mulEquiv_apply (e : L ≃ₐ[K] M) (x : FieldOfNorms K L) :
    FieldOfNorms.mulEquiv e x = FieldOfNorms.map e x := rfl

/-- The actual finite-layer map restricted to the original upper tail. -/
def FiniteIntermediateField.mapIci (i : L →ₐ[K] M) (E : FiniteIntermediateField K L) (F : Set.Ici
    E) :
    Set.Ici (FiniteIntermediateField.map i E) :=
  ⟨FiniteIntermediateField.map i F.val, FiniteIntermediateField.map_mono i F.property⟩

/-- A field isomorphism takes the original finite upper-tail filter to
the corresponding upper-tail filter. -/
theorem FiniteIntermediateField.tendsto_mapIci (e : L ≃ₐ[K] M) (E : FiniteIntermediateField K L) :
    Filter.Tendsto (FiniteIntermediateField.mapIci e.toAlgHom E) Filter.atTop Filter.atTop := by
  apply Filter.tendsto_Ici_atTop.mpr
  have hv : Filter.Tendsto (Subtype.val : Set.Ici E → FiniteIntermediateField K L)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_Ici_atTop.mp (Filter.tendsto_id :
      Filter.Tendsto (id : Set.Ici E → Set.Ici E) Filter.atTop Filter.atTop)
  exact (FiniteIntermediateField.mapOrderIso e).tendsto_atTop.comp hv

/-- Original norm-sum nets are taken to the original target nets by the
actual finite field restrictions and actual finite-layer reindexing. -/
theorem normSumNet_fieldOfNormsMap (e : L ≃ₐ[K] M) (x y : FieldOfNorms K L)
    (E : FiniteIntermediateField K M) (F : Set.Ici E) :
    normSumNet K M E (FieldOfNorms.map e x) (FieldOfNorms.map e y) F =
      (FiniteIntermediateField.equivMap e.symm.toAlgHom E).symm
        (normSumNet K L (FiniteIntermediateField.map e.symm.toAlgHom E) x y
          (FiniteIntermediateField.mapIci e.symm.toAlgHom E F)) := by
  apply (FiniteIntermediateField.equivMap e.symm.toAlgHom E).injective
  have hEF : E ≤ F.val := F.property
  have hm := FiniteIntermediateField.map_mono e.symm.toAlgHom hEF
  change (FiniteIntermediateField.equivMap e.symm.toAlgHom E)
      (FiniteIntermediateField.norm E F.val hEF
        (FieldOfNorms.coord K M F.val (FieldOfNorms.map e x) +
          FieldOfNorms.coord K M F.val (FieldOfNorms.map e y))) =
    (FiniteIntermediateField.equivMap e.symm.toAlgHom E)
      ((FiniteIntermediateField.equivMap e.symm.toAlgHom E).symm
        (FiniteIntermediateField.norm _ _ hm
          (FieldOfNorms.coord K L (FiniteIntermediateField.map e.symm.toAlgHom F.val) x +
            FieldOfNorms.coord K L (FiniteIntermediateField.map e.symm.toAlgHom F.val) y)))
  rw [FiniteIntermediateField.equivMap_norm, map_add, FieldOfNorms.coord_fieldOfNormsMap,
    FieldOfNorms.coord_fieldOfNormsMap, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply,
    AlgEquiv.apply_symm_apply]

end Multiplicative

section ValuedFields

open Filter

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable {L M : Type*} [Field L] [Field M] [Algebra K L] [Algebra K M]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable K M]

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
theorem FieldOfNorms.valuation_fieldOfNormsMap [IsAPF K L] [IsAPF K M]
    (e : L ≃ₐ[K] M) (x : FieldOfNorms K L) :
    FieldOfNorms.valuation K M (FieldOfNorms.map e x) = FieldOfNorms.valuation K L x := by
  obtain ⟨D, hD⟩ := IsAPF.exists_fieldOfNormsValuation_eq_coordinate K L
  obtain ⟨E, hE⟩ := IsAPF.exists_fieldOfNormsValuation_eq_coordinate K M
  let F := FiniteIntermediateField.sup E (FiniteIntermediateField.map e.toAlgHom D)
  let P := FiniteIntermediateField.map e.symm.toAlgHom F
  have hDP : D ≤ P := by
    calc
      D = FiniteIntermediateField.map e.symm.toAlgHom (FiniteIntermediateField.map e.toAlgHom D) :=
        ((FiniteIntermediateField.mapOrderIso e).left_inv D).symm
      _ ≤ P := FiniteIntermediateField.map_mono e.symm.toAlgHom
          (FiniteIntermediateField.le_sup_right E _)
  rw [hE F (FiniteIntermediateField.le_sup_left E _) (FieldOfNorms.map e x), hD P hDP x]
  change (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K F.val)).valuation
      F.val (FieldOfNorms.coord K M F (FieldOfNorms.map e x)) =
    (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K P.val)).valuation P.val
      (FieldOfNorms.coord K L P x)
  rw [FieldOfNorms.coord_fieldOfNormsMap]
  exact spectral_normalizedValuation_algEquiv K
    (FiniteIntermediateField.equivMap e.symm.toAlgHom F).symm (FieldOfNorms.coord K L P x)

/-- Continuity of the actual finite restrictions and cofinal reindexing
take the original source sum-net limits to the original target limits. -/
theorem FieldOfNorms.map_add
    [IsAPF K L] [IsAPF K M] (e : L ≃ₐ[K] M) (x y : FieldOfNorms K L) :
    FieldOfNorms.map e (FieldOfNorms.add K L x y) =
      FieldOfNorms.add K M (FieldOfNorms.map e x) (FieldOfNorms.map e y) := by
  apply eq_fieldOfNormsAdd_of_tendsto K M (FieldOfNorms.map e x) (FieldOfNorms.map e y)
  intro E
  let D := FiniteIntermediateField.map e.symm.toAlgHom E
  let := spectralNorm.nontriviallyNormedField K E.val
  let := spectralNorm.nontriviallyNormedField K D.val
  let := spectralNorm.normedAlgebra K E.val
  let := spectralNorm.normedAlgebra K D.val
  have hc : Continuous (FiniteIntermediateField.equivMap e.symm.toAlgHom E).symm :=
    (FiniteIntermediateField.equivMap e.symm.toAlgHom E).symm.toLinearEquiv.toLinearMap
      |>.continuous_of_finiteDimensional
  rw [FieldOfNorms.coord_fieldOfNormsMap]
  have ht := hc.continuousAt.tendsto.comp
    ((tendsto_normSumNet_fieldOfNormsAdd K L x y D).comp
      (FiniteIntermediateField.tendsto_mapIci e.symm E))
  convert ht using 1
  funext F
  exact normSumNet_fieldOfNormsMap e x y E F

/-- An actual field isomorphism induces a ring isomorphism between the
same original norm fields with their already constructed field structures. -/
def FieldOfNorms.ringEquiv [IsAPF K L] [IsAPF K M]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    (e : L ≃ₐ[K] M) :
    FieldOfNorms K L ≃+* FieldOfNorms K M := by
  exact { FieldOfNorms.mulEquiv e with
    map_add' := FieldOfNorms.map_add K e }

@[simp]
theorem FieldOfNorms.ringEquiv_apply [IsAPF K L] [IsAPF K M]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    (e : L ≃ₐ[K] M) (x : FieldOfNorms K L) :
    FieldOfNorms.ringEquiv K e x = FieldOfNorms.map e x := rfl

variable (L) in
/-- The actual original automorphism group acts by ring automorphisms
of the original norm field, with literal coordinate transport. -/
def FieldOfNorms.aut [IsAPF K L] [Fact (¬ Module.Finite K L)] :
    (L ≃ₐ[K] L) →* (FieldOfNorms K L ≃+* FieldOfNorms K L) := by
  exact {
    toFun := FieldOfNorms.ringEquiv K
    map_one' := by
      apply RingEquiv.ext
      intro x
      exact FieldOfNorms.map_refl x
    map_mul' := by
      intro e f
      apply RingEquiv.ext
      intro x
      exact (FieldOfNorms.map_trans f e x).symm }

@[simp]
theorem FieldOfNorms.aut_apply [IsAPF K L] [Fact (¬ Module.Finite K L)]
    (e : L ≃ₐ[K] L) (x : FieldOfNorms K L) :
    FieldOfNorms.aut K L e x = FieldOfNorms.map e x := rfl

/-- The ring isomorphism is uniformly continuous for the existing
valuation uniformities on the original two fields. -/
theorem uniformContinuous_fieldOfNormsRingEquiv [IsAPF K L] [IsAPF K M]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    (e : L ≃ₐ[K] M) :
    UniformContinuous (FieldOfNorms.ringEquiv K e) := by
  apply valuedRingEquiv_uniformContinuous
  intro x
  change FieldOfNorms.valuation K M (FieldOfNorms.map e x) = FieldOfNorms.valuation K L x
  exact FieldOfNorms.valuation_fieldOfNormsMap K e x

/-- The literal norm-field isomorphism and its literal inverse preserve
the existing uniform spaces; no alternate topology is introduced. -/
def FieldOfNorms.uniformEquiv [IsAPF K L] [IsAPF K M]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    (e : L ≃ₐ[K] M) :
    FieldOfNorms K L ≃ᵤ FieldOfNorms K M := by
  exact {
    toEquiv := (FieldOfNorms.ringEquiv K e).toEquiv
    uniformContinuous_toFun :=
      uniformContinuous_fieldOfNormsRingEquiv K e
    uniformContinuous_invFun :=
      uniformContinuous_fieldOfNormsRingEquiv K e.symm }

@[simp]
theorem FieldOfNorms.uniformEquiv_apply [IsAPF K L] [IsAPF K M]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]
    (e : L ≃ₐ[K] M) (x : FieldOfNorms K L) :
    FieldOfNorms.uniformEquiv K e x = FieldOfNorms.map e x := rfl

/-- Every actual original automorphism acts by an automorphism preserving
the original stable normalized valuation. -/
theorem FieldOfNorms.aut_valuation [IsAPF K L] [Fact (¬ Module.Finite K L)]
    (e : L ≃ₐ[K] L) (x : FieldOfNorms K L) :
    FieldOfNorms.valuation K L (FieldOfNorms.aut K L e x) =
      FieldOfNorms.valuation K L x :=
  FieldOfNorms.valuation_fieldOfNormsMap K e x

end ValuedFields

end FontaineWintenberger
