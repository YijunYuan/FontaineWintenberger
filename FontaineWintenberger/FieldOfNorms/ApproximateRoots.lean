/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.DiscriminantStability
public import FontaineWintenberger.FieldOfNorms.SeparableBaseChange
public import FontaineWintenberger.FieldOfNorms.FiniteSeparable
public import FontaineWintenberger.FieldOfNorms.SeparableNormUnion

/-!
# Approximate roots on the original finite norm fields

An actual full upper stage and an actual finite root adjunction give a good
original coordinate. The surjective high-break quotient map then lifts that
root to an integral element of the same original norm field.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

open Polynomial
open scoped TensorProduct

section OriginalRootLayer

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
    {M : Type*} [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/-- The original finite root field over an original finite source field,
retained as an index in the original target extension. -/
def rootFiniteLayer (E : FiniteLayer K L) (x : M) (hx : IsIntegral E.val x) :
    FiniteLayer K M := by
  let D := IntermediateField.adjoin E.val {x}
  let : Module.Finite E.val D := IntermediateField.adjoin.finiteDimensional hx
  have hfinite : Module.Finite K D := Module.Finite.trans E.val D
  exact ⟨D.restrictScalars K, hfinite⟩

/-- The canonical pullback of the original root field is exactly the
original coefficient field, by the actual linear-disjoint intersection. -/
theorem finiteLayerPullback_rootFiniteLayer (E : FiniteLayer K L)
    (x : M) (hx : IsIntegral E.val x)
    (hld : (IntermediateField.adjoin E.val {x}).LinearDisjoint L) :
    finiteLayerPullback K L (rootFiniteLayer K L E x hx) = E.val := by
  let D := IntermediateField.adjoin E.val {x}
  have hi : D ⊓ (IsScalarTower.toAlgHom E.val L M).fieldRange = ⊥ :=
    IntermediateField.toSubalgebra_injective (Subalgebra.LinearDisjoint.inf_eq_bot hld)
  exact finiteLayerPullback_eq_of_inf K L E.val D
    (rootFiniteLayer K L E x hx).property hi

/-- Actual linear disjointness and actual primitive generation make
the same original root field a good finite coordinate. -/
theorem isGoodFiniteLayer_rootFiniteLayer (E : FiniteLayer K L)
    (x : M) (hx : IsIntegral E.val x)
    (hld : (IntermediateField.adjoin E.val {x}).LinearDisjoint L)
    (hgen : Algebra.adjoin L {x} = ⊤) :
    IsGoodFiniteLayer K L (rootFiniteLayer K L E x hx) := by
  let D := IntermediateField.adjoin E.val {x}
  let : Module.Finite E.val D := IntermediateField.adjoin.finiteDimensional hx
  apply isGoodFiniteLayer_of_descent K L (rootFiniteLayer K L E x hx) E.val D rfl
    (finiteLayerPullback_rootFiniteLayer K L E x hx hld) hld
  let φ := AlgHom.liftEquiv E.val L D M D.val
  have htop : (⊤ : Subalgebra L M) ≤ φ.range := by
    rw [← hgen]
    apply Algebra.adjoin_le
    intro y hy
    have hyx : y = x := Set.mem_singleton_iff.mp hy
    subst y
    refine ⟨1 ⊗ₜ[E.val] ⟨x, IntermediateField.mem_adjoin_simple_self E.val x⟩, ?_⟩
    change (1 : L) • x = x
    exact one_smul L x
  intro y
  exact htop trivial

omit [Algebra K M] [IsScalarTower K L M] in
/-- The actual linear disjointness of an original simple field can be
checked after any injective ambient field embedding, by transporting its
actual power basis and reflecting linear independence. -/
theorem linearDisjoint_adjoin_of_injective_algHom
    {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
    (E : FiniteLayer K L) (x : M) (hx : IsIntegral E.val x) (i : M →ₐ[L] Ω)
    (hld : (IntermediateField.adjoin E.val {i x}).LinearDisjoint L) :
    (IntermediateField.adjoin E.val {x}).LinearDisjoint L := by
  let D := IntermediateField.adjoin E.val {x}
  let D' := IntermediateField.adjoin E.val {i x}
  let b := IntermediateField.adjoin.powerBasis hx
  let j : D →ₐ[E.val] D' :=
    ((i.restrictScalars E.val).comp D.val).codRestrict D'.toSubalgebra fun a => by
      have hm : i (a : M) ∈ D.map (i.restrictScalars E.val) := ⟨a, a.property, rfl⟩
      change i (a : M) ∈ IntermediateField.adjoin E.val {i x}
      simpa only [D, IntermediateField.adjoin_map, Set.image_singleton,
        AlgHom.restrictScalars_apply] using hm
  have hlin : LinearIndependent E.val (fun t => j (b.basis t)) :=
    b.basis.linearIndependent.map' j.toLinearMap (LinearMap.ker_eq_bot.mpr j.injective)
  have hlinL := hld.linearIndependent_left hlin
  apply IntermediateField.LinearDisjoint.of_basis_left b.basis
  exact LinearIndependent.of_comp i.toLinearMap hlinL

end OriginalRootLayer

section CommonRootCompositum

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
    {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]

/-- The literal original root compositum has the same field range as root
adjunction to the literal original scalar image in a common ambient field. -/
theorem fieldRange_rootCompositum (x : Ω) :
    ((IntermediateField.adjoin L {x}).val.restrictScalars K).fieldRange =
      (IntermediateField.adjoin (IsScalarTower.toAlgHom K L Ω).fieldRange {x}).restrictScalars K :=
          by
  let A := (IsScalarTower.toAlgHom K L Ω).fieldRange
  let M := IntermediateField.adjoin L {x}
  let R := IntermediateField.adjoin A {x}
  let Rₗ : IntermediateField L Ω :=
    { R.toSubfield with algebraMap_mem' := fun r => R.algebraMap_mem ⟨_, ⟨r, rfl⟩⟩ }
  have hMR : M ≤ Rₗ := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro y hy
    have hyx : y = x := Set.mem_singleton_iff.mp hy
    subst y
    exact IntermediateField.mem_adjoin_simple_self A x
  let Mₐ : IntermediateField A Ω :=
    { M.toSubfield with
      algebraMap_mem' := fun a => by
        obtain ⟨l, hl⟩ := a.property
        change (a : Ω) ∈ M
        rw [← hl]
        exact M.algebraMap_mem l }
  have hRM : R ≤ Mₐ := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro y hy
    have hyx : y = x := Set.mem_singleton_iff.mp hy
    subst y
    exact IntermediateField.mem_adjoin_simple_self L x
  ext y
  constructor
  · rintro ⟨m, rfl⟩
    exact hMR m.property
  · intro hy
    exact ⟨⟨y, hRM hy⟩, rfl⟩

end CommonRootCompositum

section FiniteRamificationBound

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    (E F : Type*) [Field E] [Field F] [Algebra K E] [Algebra K F]
    [FiniteDimensional K E] [FiniteDimensional K F]
    [Algebra.IsSeparable K E] [Algebra.IsSeparable K F]
    [Algebra E F] [IsScalarTower K E F]

/-- The actual relative index of an original finite-field inclusion is at
most its actual relative degree, by the local fundamental degree formula. -/
theorem embeddingRamificationIdx_le_finrank_of_tower :
    embeddingRamificationIdx K (IsScalarTower.toAlgHom K E F) ≤ Module.finrank E F := by
  let : FiniteDimensional E F := Module.Finite.right K E F
  let := spectralValuation_hasExtension_tower K (E := E) (L := F)
  let := Valuation.HasExtension.valuationSubring_isScalarTower
    (NormedField.valuation (K := K)) (spectralValuation K E) (spectralValuation K F)
  let : Module.Finite (spectralIntegerRing K E) (spectralIntegerRing K F) :=
    Module.Finite.of_restrictScalars_finite
      (NormedField.valuation (K := K)).valuationSubring _ _
  let : IsScalarTower (spectralIntegerRing K E) E F :=
    Valuation.HasExtension.instIsScalarTower_valuationSubring
      (L := F) (spectralValuation K E)
  let : IsScalarTower (spectralIntegerRing K E) (spectralIntegerRing K F) F :=
    Valuation.HasExtension.instIsScalarTower_valuationSubring'
      (spectralValuation K E) (spectralValuation K F)
  have he : embeddingRamificationIdx K (IsScalarTower.toAlgHom K E F) =
      (IsLocalRing.maximalIdeal (spectralIntegerRing K F)).ramificationIdx
        (spectralIntegerRing K E) := rfl
  rw [he, ← local_ramificationIdx_mul_residueDegree_eq_finrank
    (spectralIntegerRing K E) (spectralIntegerRing K F) E F]
  exact Nat.le_mul_of_pos_right _ Module.finrank_pos

end FiniteRamificationBound

section AbstractRootDisjointness

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    (L : Type*) [Field L] [Algebra K L]
    {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    [Algebra L Ω] [IsScalarTower K L Ω]

local notation "OK" => Valuation.valuationSubring (NormedField.valuation (K := K))

/-- A proved original full-upper product is full in any chosen common
separable closure with the original scalar embedding. -/
theorem fullUpper_commonClosure_of_embedding
    (i : L →ₐ[K] SeparableClosure K) {b : ℝ} (hb : -1 ≤ b)
    (h : apfSubgroup K i.fieldRange b = ⊤) :
    (IsScalarTower.toAlgHom K L Ω).fieldRange.fixingSubgroup ⊔
      upperRamificationGroupInfinite K Ω b = ⊤ := by
  let : Algebra.IsSeparable K L := Algebra.isSeparable_tower_bot_of_isSeparable K L Ω
  let e := IsSepClosure.equiv K (SeparableClosure K) Ω
  let j := e.symm.toAlgHom.comp (IsScalarTower.toAlgHom K L Ω)
  have hj := (apfSubgroup_fieldRange_eq_top_iff K L i j b).mp h
  have hm := congrArg (fun A => A.map e.autCongr.toMonoidHom) hj
  change (apfSubgroup K j.fieldRange b).map e.autCongr.toMonoidHom = _ at hm
  rw [apfSubgroup, Subgroup.map_sup, fixingSubgroup_map_autCongr,
    upperRamificationGroupInfinite_map_autCongr K e hb, Subgroup.map_top] at hm
  have he : e.toAlgHom.comp j = IsScalarTower.toAlgHom K L Ω := by
    apply AlgHom.ext
    intro x
    exact e.apply_symm_apply _
  rw [AlgHom.map_fieldRange, he] at hm
  exact hm.trans (MonoidHom.range_eq_top.mpr e.autCongr.surjective)

/-- The common-closure root-disjointness theorem applies to the original
abstract field: its literal field range has precisely its original scalar
image, so linear disjointness is reflected without replacing the field. -/
theorem linearDisjoint_root_of_fullUpper_abstract
    (f : OK[X]) (hf : f.Monic) (hsep : (f.map (algebraMap OK K)).Separable)
    {b : ℝ} (hb : (f.natDegree.factorial : ℝ) *
      (IsDiscreteValuationRing.addVal OK f.discr).toNat ≤ b)
    (htop : (IsScalarTower.toAlgHom K L Ω).fieldRange.fixingSubgroup ⊔
      upperRamificationGroupInfinite K Ω b = ⊤)
    (x : Ω) (hx : aeval x f = 0) :
    (IntermediateField.adjoin K {x}).LinearDisjoint L := by
  have hld := linearDisjoint_root_of_fullUpper_commonClosure K
    (IsScalarTower.toAlgHom K L Ω).fieldRange f hf hsep hb htop x hx
  rw [IntermediateField.linearDisjoint_iff]
  have h := IntermediateField.linearDisjoint_iff'.mp hld
  simpa only [AlgHom.fieldRange_toSubalgebra] using h

/-- The full source subgroup product for the original abstract root
compositum, on the same original automorphisms of the common closure. -/
theorem upperProduct_rootCompositum_fieldRange_eq
    (f : OK[X]) (hf : f.Monic) (hsep : (f.map (algebraMap OK K)).Separable)
    {b : ℝ} (hb : (f.natDegree.factorial : ℝ) *
      (IsDiscreteValuationRing.addVal OK f.discr).toNat ≤ b)
    (htop : (IsScalarTower.toAlgHom K L Ω).fieldRange.fixingSubgroup ⊔
      upperRamificationGroupInfinite K Ω b = ⊤)
    (x : Ω) (hx : aeval x f = 0) :
    ((IntermediateField.adjoin L {x}).val.restrictScalars K).fieldRange.fixingSubgroup ⊔
      upperRamificationGroupInfinite K Ω b = (IntermediateField.adjoin K {x}).fixingSubgroup := by
  rw [fieldRange_rootCompositum K L x]
  exact upperProduct_root_compositum_eq_commonClosure K
    (IsScalarTower.toAlgHom K L Ω).fieldRange f hf hsep hb htop x hx

end AbstractRootDisjointness

section GoodRootStages

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
    (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]
    {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    [Algebra L Ω] [IsScalarTower K L Ω]

attribute [local instance]
  FiniteLayer.instNontriviallyNormedField
  FiniteLayer.instNormedAlgebra
  FiniteLayer.instIsUltrametricDist
  FiniteLayer.instCompleteSpace
  FiniteLayer.instIsDiscreteValuationRing
  FiniteLayer.instPerfectFieldResidueField
  FiniteLayer.instIsSeparable

omit [PerfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := K)).valuationSubring)] in
/-- An actual root at a full-upper stage produces an actual good finite
coordinate in the original root compositum, with the exact original pullback
and the genuine degree bound. No goodness or disjointness is assumed. -/
theorem exists_good_rootFiniteLayer_of_fullUpper
    (E : FiniteLayer K L)
    (f : (Valuation.valuationSubring (NormedField.valuation (K := E.val)))[X])
    (hf : f.Monic)
    (hsep : (f.map (algebraMap _ E.val)).Separable)
    {b : ℝ} (hb : 0 < b)
    (hcut : (f.natDegree.factorial : ℝ) *
      (IsDiscreteValuationRing.addVal
        (NormedField.valuation (K := E.val)).valuationSubring f.discr).toNat ≤ b)
    (hE : E.HasFullUpper K L b)
    (x : Ω) (hx : aeval x f = 0) :
    let M := IntermediateField.adjoin L {x}
    let xM : M := ⟨x, IntermediateField.mem_adjoin_simple_self L x⟩
    ∃ D : FiniteLayer K M, finiteLayerPullback K L D = E.val ∧
      IsGoodFiniteLayer K L D ∧ xM ∈ D.val ∧ Module.finrank L M ≤ f.natDegree := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  let : Algebra.IsSeparable E.val Ω := Algebra.isSeparable_tower_top_of_isSeparable K E.val Ω
  let : IsSepClosed Ω := (isSepClosure_iff.mp (inferInstance : IsSepClosure K Ω)).1
  let : IsSepClosure E.val Ω := isSepClosure_iff.mpr ⟨inferInstance, inferInstance⟩
  let M := IntermediateField.adjoin L {x}
  let xM : M := ⟨x, IntermediateField.mem_adjoin_simple_self L x⟩
  have hxM : aeval xM f = 0 := by
    let j : M →ₐ[(NormedField.valuation (K := E.val)).valuationSubring] Ω :=
      M.val.restrictScalars _
    apply j.injective
    change j (aeval xM f) = 0
    rw [← aeval_algHom_apply]
    exact hx
  have hxi : IsIntegral E.val xM := by
    refine ⟨f.map (algebraMap _ E.val), hf.map _, ?_⟩
    change aeval xM (f.map (algebraMap _ E.val)) = 0
    rwa [aeval_map_algebraMap]
  have ht := fullUpper_commonClosure_of_embedding E.val L (Ω := Ω)
    (IsSepClosed.lift : L →ₐ[E.val] SeparableClosure E.val) (by linarith : -1 ≤ b) hE
  have hldΩ := linearDisjoint_root_of_fullUpper_abstract E.val L f hf hsep hcut ht x hx
  have hld := linearDisjoint_adjoin_of_injective_algHom K L E xM hxi M.val hldΩ
  have hgen : Algebra.adjoin L {xM} = ⊤ := by
    exact (IntermediateField.adjoin.powerBasis (Algebra.IsIntegral.isIntegral (R := L)
        x)).adjoin_gen_eq_top
  refine ⟨rootFiniteLayer K L E xM hxi,
    finiteLayerPullback_rootFiniteLayer K L E xM hxi hld,
    isGoodFiniteLayer_rootFiniteLayer K L E xM hxi hld hgen,
    IntermediateField.mem_adjoin_simple_self E.val xM, ?_⟩
  rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral (R := L) x)]
  have hxL : aeval x (f.map (algebraMap _ L)) = 0 := by rwa [aeval_map_algebraMap]
  have hd := natDegree_le_of_dvd (minpoly.dvd L x hxL) (hf.map (algebraMap _ L)).ne_zero
  simpa only [hf.natDegree_map] using hd

end GoodRootStages

section IntegralInclusion

variable (K L M : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
    [Field L] [Field M] [Algebra K L] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M] [Algebra.IsSeparable K L] [Algebra.IsSeparable K M]
    [Module.Finite L M]
variable (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]
variable [IsAPF K L] [IsAPF K M]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]

attribute [local instance]
  FiniteLayer.instNontriviallyNormedField
  FiniteLayer.instNormedAlgebra
  FiniteLayer.instIsUltrametricDist
  FiniteLayer.instCompleteSpace
  FiniteLayer.instIsDiscreteValuationRing
  FiniteLayer.instPerfectFieldResidueField
  FiniteLayer.instIsSeparable

omit [Module.Finite L M] [IsAPF K L] [IsAPF K M]
  [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)] in
/-- A fixing-subgroup inclusion in the actual pullback closure gives the
full upper product over the same original target coordinate, at its actual
finite-base inverse Herbrand parameter. -/
theorem FiniteLayer.hasFullUpper_of_pullback_fixing_le (D : FiniteLayer K M) :
    let C := finiteLayerPullback K L D
    letI := spectralNorm.nontriviallyNormedField K C
    letI := spectralNorm.normedAlgebra K C
    letI : IsUltrametricDist C :=
      IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
        (isNonarchimedean_spectralNorm (K := K) (L := C))
    letI := spectralNorm.completeSpace K C
    letI := normedAlgebra_isCompleteDiscreteValuedField K C
    letI := normedAlgebra_residueField_perfectField K C
    letI : Algebra.IsSeparable C D.val := Algebra.isSeparable_tower_top_of_isSeparable K C D.val
    ∀ (i : M →ₐ[C] SeparableClosure C) {b : ℝ}, -1 ≤ b →
      (i.comp (IsScalarTower.toAlgHom C D.val M)).fieldRange.fixingSubgroup ≤
        apfSubgroup C i.fieldRange b →
      D.HasFullUpper K M (apfPsi C D.val b) := by
  let C := finiteLayerPullback K L D
  let := spectralNorm.nontriviallyNormedField K C
  let := spectralNorm.normedAlgebra K C
  let : IsUltrametricDist C :=
    IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
      (isNonarchimedean_spectralNorm (K := K) (L := C))
  let := spectralNorm.completeSpace K C
  let := normedAlgebra_isCompleteDiscreteValuedField K C
  let := normedAlgebra_residueField_perfectField K C
  let : Algebra.IsSeparable C D.val := Algebra.isSeparable_tower_top_of_isSeparable K C D.val
  dsimp only
  intro i b hb hfix
  let : NormedAlgebra C D.val := spectralNorm.normedAlgebra' (K := K) C D.val
  let : Algebra.IsSeparable C M := Algebra.isSeparable_tower_top_of_isSeparable K C M
  let jD := i.comp (IsScalarTower.toAlgHom C D.val M)
  let : Algebra D.val (SeparableClosure C) := jD.toRingHom.toAlgebra
  let : IsScalarTower C D.val (SeparableClosure C) := IsScalarTower.of_algHom jD
  let j : M →ₐ[D.val] SeparableClosure C :=
    { i.toRingHom with commutes' := fun _ => rfl }
  let e := AbstractFiniteBase.closureEquiv C D.val
  let j' := e.symm.toAlgHom.comp j
  have he : AbstractFiniteBase.embedding C D.val j' = i := by
    apply AlgHom.ext
    intro x
    exact e.apply_symm_apply (i x)
  have hc := AbstractFiniteBase.comap_apf C D.val j' hb
  rw [he] at hc
  have hr : (AbstractFiniteBase.closureHom C D.val).range = jD.fieldRange.fixingSubgroup :=
    AbstractFiniteBase.closureHom_range C D.val
  have ht : (apfSubgroup C i.fieldRange b).comap (AbstractFiniteBase.closureHom C D.val) = ⊤ := by
    apply top_unique
    intro g _
    exact hfix (hr ▸ ⟨g, rfl⟩)
  have hi : apfSubgroup D.val j'.fieldRange (apfPsi C D.val b) = ⊤ := by
    rw [← hc, ht]
  exact (D.hasFullUpper_iff_embedding K M j' (apfPsi C D.val b)).mpr hi

local notation "Oₗ" => Valuation.valuationSubring
  (normLimitFieldValuation K L p)
local notation "Oₘ" => Valuation.valuationSubring
  (normLimitFieldValuation K M p)

omit [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)] in
/-- The original finite norm-field map has a proved positive valuation
exponent bounded by the original field degree. Both bounds are computed
in an actual good finite field on the stable original tails. -/
theorem exists_finiteNormLimitMap_valuation_scaling_le_finrank :
    letI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
    ∃ e : ℕ, 0 < e ∧ e ≤ Module.finrank L M ∧ ∀ x : NormLimit K L,
      normLimitValuation K M (finiteNormLimitMap K L M x) =
        normLimitValuation K L x ^ e := by
  let : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  obtain ⟨D, hD, he, hv⟩ := exists_goodFiniteLayer_finiteNormLimitMap_valuation K L M
  have hb : embeddingRamificationIdx K (finiteLayerPullbackTo K L D) ≤ Module.finrank L M := by
    calc
      embeddingRamificationIdx K (finiteLayerPullbackTo K L D) ≤
          Module.finrank (finiteLayerPullback K L D) D.val :=
        embeddingRamificationIdx_le_finrank_of_tower K (finiteLayerPullback K L D) D.val
      _ = Module.finrank L M := finrank_goodFiniteLayer K L D hD
  exact ⟨embeddingRamificationIdx K (finiteLayerPullbackTo K L D), he, hb, hv⟩

omit [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)] in
/-- On actual full-upper good coordinates the valuation exponent is the
index of that very same original finite-field inclusion. -/
theorem normLimitValuation_finiteNormLimitMap_of_fullUpper
    (D : FiniteLayer K M) (hD : IsGoodFiniteLayer K L D)
    {bL bM : ℝ} (hbL : 0 < bL) (hbM : 0 < bM)
    (hC : (finiteLayerPullbackLayer K L D).HasFullUpper K L bL)
    (hF : D.HasFullUpper K M bM) :
    letI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
    ∀ x : NormLimit K L,
      normLimitValuation K M (finiteNormLimitMap K L M x) =
        normLimitValuation K L x ^ embeddingRamificationIdx K (finiteLayerPullbackTo K L D) := by
  let : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  intro x
  rw [normLimitValuation_eq_coordinate_of_fullUpper K M hbM hF,
    normLimitValuation_eq_coordinate_of_fullUpper K L hbL hC]
  change (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K D.val)).valuation D.val
      (normLimitEval K M D (finiteNormLimitMap K L M x)) = _
  rw [normLimitEval_finiteNormLimitMap K L M D hD]
  exact spectral_normalizedValuation_algHom K (finiteLayerPullbackTo K L D)
    (normLimitEval K L (finiteLayerPullbackLayer K L D) x)

/-- The original finite norm-field inclusion restricts to the original
valuation rings, by its proved positive integral valuation scaling. -/
def finiteNormLimitIntegralRingHom :
    letI := normLimitField K L p
    letI := normLimitField K M p
    Oₗ →+* Oₘ := by
  let := normLimitField K L p
  let := normLimitField K M p
  let : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  let φ := finiteNormLimitRingHom K L M p
  refine (φ.comp (Oₗ).subtype).codRestrict (Oₘ).toSubring ?_
  intro a
  obtain ⟨e, _, he⟩ := exists_finiteNormLimitMap_valuation_scaling K L M
  change normLimitValuation K M (finiteNormLimitMap K L M a.val) ≤ 1
  rw [he]
  exact pow_le_one₀ zero_le a.property

/-- Restriction does not change the actual finite-inclusion field map. -/
@[simp]
theorem coe_finiteNormLimitIntegralRingHom :
    letI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
    letI := normLimitField K L p
    letI := normLimitField K M p
    ∀ a : Oₗ,
      (finiteNormLimitIntegralRingHom K L M p a : NormLimit K M) =
        finiteNormLimitMap K L M a.val := by
  let := normLimitField K L p
  let := normLimitField K M p
  let : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  intro a
  rfl

/-- At an actual good target field, integral restriction has precisely the
original pullback coordinate followed by the original integer inclusion. -/
theorem normLimitIntegralCoordinateAt_finiteNormLimitIntegralRingHom
    (D : FiniteLayer K M) (hD : IsGoodFiniteLayer K L D) :
    letI := normLimitField K L p
    letI := normLimitField K M p
    ∀ a : Oₗ,
      normLimitIntegralCoordinateAt K M p D
          (finiteNormLimitIntegralRingHom K L M p a) =
        spectralIntegerInclusion K (finiteLayerPullbackTo K L D)
          (normLimitIntegralCoordinateAt K L p
            (finiteLayerPullbackLayer K L D) a) := by
  let := normLimitField K L p
  let := normLimitField K M p
  let : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  intro a
  apply Subtype.ext
  exact normLimitEval_finiteNormLimitMap K L M D hD a.val

/-- Reduction of the mapped original polynomial is the reduction of its
actual pullback-coordinate polynomial, with the original finite inclusion. -/
theorem map_normLimitCoordinatePolynomial_finiteNormLimitIntegralRingHom
    (D : FiniteLayer K M) (hD : IsGoodFiniteLayer K L D)
    {b : ℝ} (hb : 0 < b) (h : D.HasFullUpper K M b)
    (r : ℕ) (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) :
    letI := normLimitField K L p
    letI := normLimitField K M p
    ∀ f : Oₗ[X],
      (f.map (finiteNormLimitIntegralRingHom K L M p)).map
          (normLimitHighBreakProjection K M p hb h r hrb) =
        ((normLimitCoordinatePolynomial K L p
          (finiteLayerPullbackLayer K L D) f).map
            (spectralIntegerInclusion K (finiteLayerPullbackTo K L D)).toRingHom).map
              (Ideal.Quotient.mk
                (IsLocalRing.maximalIdeal (spectralIntegerRing K D.val) ^ r)) := by
  let := normLimitField K L p
  let := normLimitField K M p
  intro f
  dsimp only [finiteLayerPullbackLayer]
  ext i
  simp only [coeff_map, normLimitHighBreakProjection_apply]
  rw [coeff_normLimitCoordinatePolynomial,
    normLimitIntegralCoordinateAt_finiteNormLimitIntegralRingHom
      K L M p D hD]
  rfl

/-- An actual root in an actual good finite coordinate lifts through the
proved high-break surjection to an original integral norm family whose
original polynomial residual has at least the prescribed normalized depth. -/
theorem exists_normLimit_approximate_root_of_good_coordinate
    (D : FiniteLayer K M) (hD : IsGoodFiniteLayer K L D)
    {b : ℝ} (hb : 0 < b) (h : D.HasFullUpper K M b)
    (r : ℕ) (hrb : r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊) :
    letI := normLimitField K L p
    letI := normLimitField K M p
    ∀ (f : Oₗ[X]) (x : spectralIntegerRing K D.val),
      ((normLimitCoordinatePolynomial K L p
        (finiteLayerPullbackLayer K L D) f).map
          (spectralIntegerInclusion K (finiteLayerPullbackTo K L D)).toRingHom).eval x = 0 →
      ∃ z : Oₘ,
        normLimitValuation K M
          (((f.map (finiteNormLimitIntegralRingHom K L M p)).eval z :
            Oₘ) : NormLimit K M) ≤ WithZero.exp (-(r : ℤ)) := by
  let := normLimitField K L p
  let := normLimitField K M p
  intro f x hx
  let q := normLimitHighBreakProjection K M p hb h r hrb
  let qD := Ideal.Quotient.mk
    (IsLocalRing.maximalIdeal (spectralIntegerRing K D.val) ^ r)
  obtain ⟨z, hz⟩ := normLimitHighBreakProjection_surjective K M p hb h r hrb (qD x)
  refine ⟨z, (normLimitHighBreakProjection_eq_zero_iff K M p hb h r hrb _).mp ?_⟩
  rw [← Polynomial.eval_map_apply]
  rw [map_normLimitCoordinatePolynomial_finiteNormLimitIntegralRingHom
    K L M p D hD hb h r hrb f, hz,
    Polynomial.eval_map_apply, hx, map_zero]

end IntegralInclusion

section FullUpperRootStages

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
    (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]
    {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    [Algebra L Ω] [IsScalarTower K L Ω]

attribute [local instance]
  FiniteLayer.instNontriviallyNormedField
  FiniteLayer.instNormedAlgebra
  FiniteLayer.instIsUltrametricDist
  FiniteLayer.instCompleteSpace
  FiniteLayer.instIsDiscreteValuationRing
  FiniteLayer.instPerfectFieldResidueField
  FiniteLayer.instIsSeparable

/-- The actual good root coordinate has the full original relative upper
product at the original depth. The root-field fixing inclusion discharges
the finite-base criterion on this same original index. -/
theorem exists_good_fullUpper_rootFiniteLayer
    (E : FiniteLayer K L)
    (f : (Valuation.valuationSubring (NormedField.valuation (K := E.val)))[X])
    (hf : f.Monic) (hsep : (f.map (algebraMap _ E.val)).Separable)
    {b : ℝ} (hb : 0 < b)
    (hcut : (f.natDegree.factorial : ℝ) *
      (IsDiscreteValuationRing.addVal
        (NormedField.valuation (K := E.val)).valuationSubring f.discr).toNat ≤ b)
    (hE : E.HasFullUpper K L b) (x : Ω) (hx : aeval x f = 0) :
    let M := IntermediateField.adjoin L {x}
    letI : IsScalarTower K M Ω := IsScalarTower.to₁₃₄ K L M Ω
    letI : Algebra.IsSeparable K M := Algebra.isSeparable_tower_bot_of_isSeparable K M Ω
    let xM : M := ⟨x, IntermediateField.mem_adjoin_simple_self L x⟩
    ∃ D : FiniteLayer K M, finiteLayerPullback K L D = E.val ∧
      IsGoodFiniteLayer K L D ∧ xM ∈ D.val ∧ Module.finrank L M ≤ f.natDegree ∧
        D.HasFullUpper K M b := by
  let M := IntermediateField.adjoin L {x}
  let : IsScalarTower K M Ω := IsScalarTower.to₁₃₄ K L M Ω
  let : Algebra.IsSeparable K M := Algebra.isSeparable_tower_bot_of_isSeparable K M Ω
  let xM : M := ⟨x, IntermediateField.mem_adjoin_simple_self L x⟩
  obtain ⟨D, hC, hD, hxD, hdeg⟩ :=
    exists_good_rootFiniteLayer_of_fullUpper K L E f hf hsep hb hcut hE x hx
  have hindex : finiteLayerPullbackLayer K L D = E := Subtype.ext hC
  cases hindex
  let C := finiteLayerPullback K L D
  let := spectralNorm.nontriviallyNormedField K C
  let := spectralNorm.normedAlgebra K C
  let : IsUltrametricDist C :=
    IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
      (isNonarchimedean_spectralNorm (K := K) (L := C))
  let := spectralNorm.completeSpace K C
  let := normedAlgebra_isCompleteDiscreteValuedField K C
  let := normedAlgebra_residueField_perfectField K C
  let : Algebra.IsSeparable C D.val := Algebra.isSeparable_tower_top_of_isSeparable K C D.val
  let : Algebra.IsSeparable C Ω := Algebra.isSeparable_tower_top_of_isSeparable K C Ω
  let : IsSepClosed Ω := (isSepClosure_iff.mp (inferInstance : IsSepClosure K Ω)).1
  let : IsSepClosure C Ω := isSepClosure_iff.mpr ⟨inferInstance, inferInstance⟩
  have ht := fullUpper_commonClosure_of_embedding C L (Ω := Ω)
    (IsSepClosed.lift : L →ₐ[C] SeparableClosure C) (by linarith : -1 ≤ b) hE
  have hprod := upperProduct_rootCompositum_fieldRange_eq C L f hf hsep hcut ht x hx
  let jM := M.val.restrictScalars C
  let jD := jM.comp (IsScalarTower.toAlgHom C D.val M)
  have hroot : IntermediateField.adjoin C {x} ≤ jD.fieldRange := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro y hy
    have hyx : y = x := Set.mem_singleton_iff.mp hy
    subst y
    exact ⟨⟨xM, hxD⟩, rfl⟩
  have hfix : jD.fieldRange.fixingSubgroup ≤
      jM.fieldRange.fixingSubgroup ⊔ upperRamificationGroupInfinite C Ω b :=
    (IntermediateField.fixingSubgroup_le hroot).trans_eq hprod.symm
  let e := IsSepClosure.equiv C (SeparableClosure C) Ω
  let i := e.symm.toAlgHom.comp jM
  have hm := Subgroup.map_mono (f := e.symm.autCongr.toMonoidHom) hfix
  rw [fixingSubgroup_map_autCongr, Subgroup.map_sup, fixingSubgroup_map_autCongr,
    upperRamificationGroupInfinite_map_autCongr C e.symm (by linarith : -1 ≤ b),
    AlgHom.map_fieldRange, AlgHom.map_fieldRange] at hm
  have hcanonical : (i.comp (IsScalarTower.toAlgHom C D.val M)).fieldRange.fixingSubgroup ≤
      apfSubgroup C i.fieldRange b := by
    simpa only [i, jD, AlgHom.comp_assoc, apfSubgroup] using hm
  have hfull := D.hasFullUpper_of_pullback_fixing_le K L M i
    (by linarith : -1 ≤ b) hcanonical
  refine ⟨D, rfl, hD, hxD, hdeg, ?_⟩
  have : FiniteDimensional C D.val := Module.Finite.right K C D.val
  exact hfull.of_le K M hb.le (IsAPF.le_apfPsi C D.val b)

end FullUpperRootStages

section CoordinatePrecision

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
    (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]
    [IsAPF K L] [Fact (¬ Module.Finite K L)]

attribute [local instance]
  FiniteLayer.instNontriviallyNormedField
  FiniteLayer.instNormedAlgebra
  FiniteLayer.instIsUltrametricDist
  FiniteLayer.instCompleteSpace
  FiniteLayer.instIsDiscreteValuationRing
  FiniteLayer.instPerfectFieldResidueField
  FiniteLayer.instIsSeparable

local notation "Oₓ" => Valuation.valuationSubring
  (normLimitFieldValuation K L p)

/-- Actual deep coordinate polynomials simultaneously satisfy every requested
quotient precision and the factorial discriminant cutoff. The displayed field
identity bridges their original spectral integers and the same finite field's
unit ball by the identity on elements. -/
theorem exists_normLimitCoordinatePolynomial_root_stage (r : ℕ) :
    letI := normLimitField K L p
    ∀ f : Oₓ[X], f.Monic → (f.map (algebraMap Oₓ (NormLimit K L))).Separable →
      ∃ (E : FiniteLayer K L) (b : ℝ)
        (g : (NormedField.valuation (K := E.val)).valuationSubring[X]),
        0 < b ∧ E.HasFullUpper K L b ∧ g.Monic ∧ g.natDegree = f.natDegree ∧
        (g.map (algebraMap _ E.val)).Separable ∧
        g.map (algebraMap _ E.val) =
          (normLimitCoordinatePolynomial K L p E f).map
            (algebraMap _ E.val) ∧
        r ≤ ⌈((p - 1 : ℕ) : ℝ) / p * b⌉₊ ∧
        (g.natDegree.factorial : ℝ) *
          (IsDiscreteValuationRing.addVal
            (NormedField.valuation (K := E.val)).valuationSubring g.discr).toNat ≤ b := by
  let := normLimitField K L p
  intro f hf hsep
  obtain ⟨r₀, hr₀⟩ := exists_normLimit_discr_precision K L p f hf hsep
  obtain ⟨F, _, hF, _, hstable⟩ :=
    exists_cofinal_normLimitCoordinatePolynomial_discr_stable K L p
  let α : ℝ := ((p - 1 : ℕ) : ℝ) / p
  have hα : 0 < α := by
    have hp := (Fact.out : p.Prime).two_le
    exact div_pos (by exact_mod_cast (by omega : 0 < p - 1))
      (by exact_mod_cast (Fact.out : p.Prime).pos)
  obtain ⟨N, hN⟩ := exists_nat_gt (max ((r : ℝ) / α) ((f.natDegree.factorial : ℝ) * r₀))
  obtain ⟨n, hn, hval, hsepE⟩ :=
    ((Filter.eventually_ge_atTop N).and (hstable f hf hsep)).exists
  let E := F n
  let fE := normLimitCoordinatePolynomial K L p E f
  let e : spectralIntegerRing K E.val ≃+*
      (NormedField.valuation (K := E.val)).valuationSubring :=
    RingEquiv.subringCongr (congrArg ValuationSubring.toSubring
      (spectralIntegerRing_eq_normedUnitBall K E.val))
  let g := fE.map e.toRingHom
  have hfE : fE.Monic := monic_normLimitCoordinatePolynomial K L p E f hf
  have hg : g.Monic := hfE.map _
  have hdeg : g.natDegree = f.natDegree := by
    rw [hfE.natDegree_map]
    exact natDegree_normLimitCoordinatePolynomial K L p E f hf
  have hmap : g.map (algebraMap _ E.val) = fE.map (algebraMap _ E.val) := by
    rw [Polynomial.map_map]
    congr 1
  have hδ : (IsDiscreteValuationRing.addVal (spectralIntegerRing K E.val) fE.discr).toNat ≤ r₀ := by
    apply ENat.toNat_le_of_le_natCast
    apply le_of_lt
    apply lt_of_not_ge
    intro hm
    have hm' := (mem_maximalIdeal_pow_iff_addVal fE.discr r₀).mpr hm
    have hv := (ValuationSubring.mem_maximalIdeal_pow_iff_normalizedValuation
      (spectralIntegerRing K E.val) fE.discr r₀).mp hm'
    exact (not_lt_of_ge hv) (hr₀.trans_eq hval.symm)
  have hδg : (IsDiscreteValuationRing.addVal
      (NormedField.valuation (K := E.val)).valuationSubring g.discr).toNat ≤ r₀ := by
    rw [show g.discr = e fE.discr from monic_discr_map fE hfE e.toRingHom,
      addVal_ringEquiv]
    exact hδ
  have hnb : ((r : ℝ) / α) < (n : ℝ) + 1 := by
    have hNN : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith [lt_of_le_of_lt (le_max_left _ _) hN]
  have hcut : (f.natDegree.factorial : ℝ) * r₀ ≤ (n : ℝ) + 1 := by
    have hNN : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith [lt_of_le_of_lt (le_max_right _ _) hN]
  refine ⟨E, (n : ℝ) + 1, g, by positivity, hF n, hg, hdeg, ?_, hmap, ?_, ?_⟩
  · rw [hmap]
    exact hsepE
  · have hrn : (r : ℝ) ≤ α * ((n : ℝ) + 1) := by
      simpa only [mul_comm] using ((div_lt_iff₀ hα).mp hnb).le
    exact_mod_cast hrn.trans (Nat.le_ceil _)
  · rw [hdeg]
    exact (mul_le_mul_of_nonneg_left (by exact_mod_cast hδg) (by positivity)).trans hcut

variable {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    [Algebra L Ω] [IsScalarTower K L Ω]

/-- At every prescribed original normalized depth, an actual finite root
adjunction in the chosen common separable closure supplies an integral
approximate root in its same original norm field. -/
theorem exists_normLimit_approximate_root_at_precision (r : ℕ) :
    letI := normLimitField K L p
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    ∀ f : Oₓ[X], f.Monic → (f.map (algebraMap Oₓ (NormLimit K L))).Separable →
      0 < f.natDegree →
      ∃ N : FiniteLayer L Ω, Module.finrank L N.val ≤ f.natDegree ∧
        letI : Algebra.IsSeparable K N.val := Algebra.IsSeparable.trans K L N.val
        have := separableNormUnionStage_isAPF K L Ω N
        have : Fact (¬ Module.Finite K N.val) := ⟨separableNormUnionStage_infinite K L Ω N⟩
        letI := separableNormUnionStageField K L Ω p N
        ∃ z : (normLimitFieldValuation K N.val p).valuationSubring,
          normLimitValuation K N.val
            (((f.map (finiteNormLimitIntegralRingHom K L N.val p)).eval z :
              (normLimitFieldValuation K N.val p).valuationSubring) : NormLimit K N.val) ≤
            WithZero.exp (-(r : ℤ)) := by
  let := normLimitField K L p
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  intro f hf hsep hdegree
  obtain ⟨E, b, g, hb, hE, hg, hdeg, hsepE, hmap, hr, hcut⟩ :=
    exists_normLimitCoordinatePolynomial_root_stage K L p r f hf hsep
  let : IsSepClosed Ω := (isSepClosure_iff.mp (inferInstance : IsSepClosure K Ω)).1
  have hsplit := IsSepClosed.splits_codomain
    (f := algebraMap E.val Ω) (g.map (algebraMap _ E.val)) hsepE
  have hpos : 0 < ((g.map (algebraMap _ E.val)).map (algebraMap E.val Ω)).natDegree := by
    rw [(hg.map _).natDegree_map, hg.natDegree_map, hdeg]
    exact hdegree
  obtain ⟨x, hx⟩ := hsplit.exists_eval_eq_zero
    (degree_ne_of_natDegree_ne (Nat.ne_of_gt hpos))
  have hxg : aeval x g = 0 := by
    simpa only [Polynomial.map_map, Polynomial.eval_map_algebraMap,
      ← IsScalarTower.algebraMap_eq (NormedField.valuation (K := E.val)).valuationSubring E.val Ω]
          using hx
  let M := IntermediateField.adjoin L {x}
  let : Module.Finite L M := IntermediateField.adjoin.finiteDimensional
    (Algebra.IsIntegral.isIntegral (R := L) x)
  let : IsScalarTower K M Ω := IsScalarTower.to₁₃₄ K L M Ω
  let : Algebra.IsSeparable K M := Algebra.IsSeparable.trans K L M
  obtain ⟨D, hC, hgood, hxD, hdegreeM, hfull⟩ :=
    exists_good_fullUpper_rootFiniteLayer K L E g hg hsepE hb hcut hE x hxg
  let N : FiniteLayer L Ω := ⟨M, inferInstance⟩
  have hindex : finiteLayerPullbackLayer K L D = E := Subtype.ext hC
  cases hindex
  let C := finiteLayerPullbackLayer K L D
  let fC := normLimitCoordinatePolynomial K L p C f
  let fD := fC.map (spectralIntegerInclusion K (finiteLayerPullbackTo K L D)).toRingHom
  let xM : M := ⟨x, IntermediateField.mem_adjoin_simple_self L x⟩
  let xD : D.val := ⟨xM, hxD⟩
  have hxC : aeval x fC = 0 := by
    have h := congrArg (fun q : C.val[X] => aeval x q) hmap
    rw [aeval_map_algebraMap, aeval_map_algebraMap] at h
    exact h.symm.trans hxg
  have hxfield : aeval xD fD = 0 := by
    let j : D.val →ₐ[K] Ω := (M.val.restrictScalars K).comp D.val.val
    apply j.injective
    change j (aeval xD fD) = 0
    have hcomp :
        (j.toRingHom.comp (algebraMap (spectralIntegerRing K D.val) D.val)).comp
          (spectralIntegerInclusion K (finiteLayerPullbackTo K L D)).toRingHom =
        algebraMap (spectralIntegerRing K C.val) Ω := by
      ext a
      rfl
    change j.toRingHom (Polynomial.eval₂ (algebraMap _ D.val) xD fD) = 0
    rw [Polynomial.hom_eval₂]
    dsimp only [fD]
    erw [Polynomial.eval₂_map, hcomp]
    exact hxC
  have hfd : fD.Monic := (monic_normLimitCoordinatePolynomial K L p
    (finiteLayerPullbackLayer K L D) f hf).map _
  let a : spectralIntegerRing K D.val :=
    ⟨xD, monic_root_valuation_le_one (spectralValuation K D.val) fD hfd xD hxfield⟩
  have ha : fD.eval a = 0 := by
    apply Subtype.val_injective
    change (algebraMap (spectralIntegerRing K D.val) D.val) (fD.eval a) = 0
    rw [← Polynomial.eval₂_at_apply]
    exact hxfield
  have := separableNormUnionStage_isAPF K L Ω N
  have : Fact (¬ Module.Finite K N.val) := ⟨separableNormUnionStage_infinite K L Ω N⟩
  refine ⟨N, hdegreeM.trans_eq hdeg, ?_⟩
  exact exists_normLimit_approximate_root_of_good_coordinate K L N.val p
    D hgood hb hfull r hr f a ha

end CoordinatePrecision

section IntegralRamification

variable (K L M : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
    [Field L] [Field M] [Algebra K L] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M] [Algebra.IsSeparable K L] [Algebra.IsSeparable K M]
    [Module.Finite L M]
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]
    [IsAPF K L] [IsAPF K M]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]

local notation "Oₗ" => Valuation.valuationSubring (normLimitFieldValuation K L p)
local notation "Oₘ" => Valuation.valuationSubring (normLimitFieldValuation K M p)

/-- The restriction of the actual original finite field map is local:
positive valuation scaling reflects units in the original valuation rings. -/
theorem isLocalHom_finiteNormLimitIntegralRingHom :
    letI := normLimitField K L p
    letI := normLimitField K M p
    IsLocalHom (finiteNormLimitIntegralRingHom K L M p) := by
  let := normLimitField K L p
  let := normLimitField K M p
  let : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  obtain ⟨e, he, hv⟩ := exists_finiteNormLimitMap_valuation_scaling K L M
  constructor
  intro a ha
  have hu := (Valuation.valuationSubring.integers (normLimitFieldValuation K M p
)).isUnit_iff_valuation_eq_one.mp ha
  change normLimitValuation K M (finiteNormLimitMap K L M a.val) = 1 at hu
  rw [hv] at hu
  apply (Valuation.valuationSubring.integers (normLimitFieldValuation K L p
)).isUnit_iff_valuation_eq_one.mpr
  change normLimitValuation K L a.val = 1
  apply le_antisymm a.property
  apply (pow_le_pow_iff_left₀ zero_le zero_le he.ne').mp
  simp only [hu, one_pow, le_refl]

/-- The canonical local-length ramification index of the actual original
valuation-ring map is its original field-valuation scaling exponent. -/
theorem finiteNormLimitIntegralRingHom_ramificationIdx_scaling :
    letI := normLimitField K L p
    letI := normLimitField K M p
    letI := (finiteNormLimitIntegralRingHom K L M p).toAlgebra
    letI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
    ∀ x : NormLimit K L,
      normLimitValuation K M (finiteNormLimitMap K L M x) =
        normLimitValuation K L x ^ (IsLocalRing.maximalIdeal Oₘ).ramificationIdx Oₗ := by
  let := normLimitField K L p
  let := normLimitField K M p
  let := normLimitFieldValuation_isDiscreteValuationRing K L p
  let := normLimitFieldValuation_isDiscreteValuationRing K M p
  let : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  let φ := finiteNormLimitRingHom K L M p
  let ρ := finiteNormLimitIntegralRingHom K L M p
  let : Algebra Oₗ Oₘ := ρ.toAlgebra
  let : Algebra (NormLimit K L) (NormLimit K M) := φ.toAlgebra
  let : Algebra Oₗ (NormLimit K M) := (φ.comp (Oₗ).subtype).toAlgebra
  let : IsScalarTower Oₗ (NormLimit K L) (NormLimit K M) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower Oₗ Oₘ (NormLimit K M) := IsScalarTower.of_algebraMap_eq' rfl
  let : IsLocalHom (algebraMap Oₗ Oₘ) :=
    isLocalHom_finiteNormLimitIntegralRingHom K L M p
  let : FaithfulSMul Oₗ Oₘ := (faithfulSMul_iff_algebraMap_injective Oₗ Oₘ).mpr (by
    intro a b hab
    apply Subtype.val_injective
    apply φ.injective
    exact congrArg Subtype.val hab)
  intro x
  have h := normalizedValuation_algebraMap Oₗ Oₘ (NormLimit K L) (NormLimit K M) x
  rw [normLimitFieldValuation_eq_normalized K L p,
    normLimitFieldValuation_eq_normalized K M p] at h
  exact h

end IntegralRamification

section StageNormalization

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
    (L Ω : Type*) [Field L] [Field Ω] [Algebra K L] [Algebra K Ω]
    [Algebra L Ω] [IsScalarTower K L Ω] [Algebra.IsSeparable K L]
    [Algebra.IsSeparable L Ω]
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]
    [IsAPF K L] [Fact (¬ Module.Finite K L)]

include p in
/-- The canonical original finite-stage exponent is bounded by the actual
finite extension degree, using its proved unique uniformizer value. -/
theorem separableNormUnionStageExponent_le_finrank (N : FiniteLayer L Ω) :
    separableNormUnionStageExponent K L Ω N ≤ Module.finrank L N.val := by
  let : Algebra.IsSeparable K N.val := Algebra.IsSeparable.trans K L N.val
  obtain ⟨e, _, he, hv⟩ := exists_finiteNormLimitMap_valuation_scaling_le_finrank
    K L N.val
  have h := separableNormUnionStageExponent_unique K L Ω p N e hv
  exact h ▸ he

/-- The chosen positive original stage exponent is exactly the canonical
ramification index of the actual original valuation-ring inclusion. -/
theorem separableNormUnionStageExponent_eq_ramificationIdx (N : FiniteLayer L Ω) :
    letI := normLimitField K L p
    letI : Algebra.IsSeparable K N.val := Algebra.IsSeparable.trans K L N.val
    haveI := separableNormUnionStage_isAPF K L Ω N
    haveI : Fact (¬ Module.Finite K N.val) := ⟨separableNormUnionStage_infinite K L Ω N⟩
    letI := separableNormUnionStageField K L Ω p N
    letI := (finiteNormLimitIntegralRingHom K L N.val p).toAlgebra
    separableNormUnionStageExponent K L Ω N =
      (IsLocalRing.maximalIdeal
        (normLimitFieldValuation K N.val p).valuationSubring).ramificationIdx
          (normLimitFieldValuation K L p).valuationSubring := by
  let := normLimitField K L p
  let : Algebra.IsSeparable K N.val := Algebra.IsSeparable.trans K L N.val
  have := separableNormUnionStage_isAPF K L Ω N
  have : Fact (¬ Module.Finite K N.val) := ⟨separableNormUnionStage_infinite K L Ω N⟩
  let := separableNormUnionStageField K L Ω p N
  let := (finiteNormLimitIntegralRingHom K L N.val p).toAlgebra
  symm
  apply separableNormUnionStageExponent_unique K L Ω p N
  exact finiteNormLimitIntegralRingHom_ramificationIdx_scaling K L N.val p

end StageNormalization

section NormalizedApproximation

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
    (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]
    {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    [Algebra L Ω] [IsScalarTower K L Ω]
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]
    [IsAPF K L] [Fact (¬ Module.Finite K L)]

local notation "Oₓ" => Valuation.valuationSubring
  (normLimitFieldValuation K L p)

/-- Original approximate roots have both their prescribed integer depth and
the source-normalized depth divided by the actual degree bound. Every finite
stage, integral element and positive ramification exponent is genuine. -/
theorem exists_normLimit_approximate_root_normalized (r : ℕ) :
    letI := normLimitField K L p
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    ∀ f : Oₓ[X], f.Monic → (f.map (algebraMap Oₓ (NormLimit K L))).Separable →
      0 < f.natDegree →
      ∃ N : FiniteLayer L Ω,
        0 < separableNormUnionStageExponent K L Ω N ∧
        separableNormUnionStageExponent K L Ω N ≤ Module.finrank L N.val ∧
        Module.finrank L N.val ≤ f.natDegree ∧
        letI : Algebra.IsSeparable K N.val := Algebra.IsSeparable.trans K L N.val
        have := separableNormUnionStage_isAPF K L Ω N
        have : Fact (¬ Module.Finite K N.val) := ⟨separableNormUnionStage_infinite K L Ω N⟩
        letI := separableNormUnionStageField K L Ω p N
        let φ := finiteNormLimitRingHom K L N.val p
        ∃ z : NormLimit K N.val,
          normLimitValuation K N.val z ≤ 1 ∧
          normLimitValuation K N.val ((f.map (φ.comp (Oₓ).subtype)).eval z) ≤
            WithZero.exp (-(r : ℤ)) ∧
          separableNormUnionStageValuation K L Ω p N
              ((f.map (φ.comp (Oₓ).subtype)).eval z) ≤
            WithZero.exp (-(r : ℚ) / (f.natDegree : ℚ)) := by
  let := normLimitField K L p
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  intro f hf hsep hdegree
  obtain ⟨N, hdeg, hz⟩ := exists_normLimit_approximate_root_at_precision
    K L p (Ω := Ω) r f hf hsep hdegree
  let : Algebra.IsSeparable K N.val := Algebra.IsSeparable.trans K L N.val
  have := separableNormUnionStage_isAPF K L Ω N
  have : Fact (¬ Module.Finite K N.val) := ⟨separableNormUnionStage_infinite K L Ω N⟩
  let := separableNormUnionStageField K L Ω p N
  let φ := finiteNormLimitRingHom K L N.val p
  let ρ := finiteNormLimitIntegralRingHom K L N.val p
  obtain ⟨z, hz⟩ := hz
  have he := separableNormUnionStageExponent_pos K L Ω N
  have hedegree := separableNormUnionStageExponent_le_finrank K L Ω p N
  have hcoeval :
      (algebraMap (normLimitFieldValuation K N.val p).valuationSubring (NormLimit K N.val))
          ((f.map ρ).eval z) = (f.map (φ.comp (Oₓ).subtype)).eval z.val := by
    rw [← Polynomial.eval₂_at_apply, Polynomial.eval₂_map, Polynomial.eval_map]
    rfl
  have hw : normLimitValuation K N.val
      ((f.map (φ.comp (Oₓ).subtype)).eval z.val) ≤ WithZero.exp (-(r : ℤ)) := by
    rw [← hcoeval]
    exact hz
  refine ⟨N, he, hedegree, hdeg, z.val, z.property, hw, ?_⟩
  rw [separableNormUnionStageValuation_apply]
  calc
    separableNormUnionValueMap (separableNormUnionStageExponent K L Ω N)
        (normLimitValuation K N.val ((f.map (φ.comp (Oₓ).subtype)).eval z.val)) ≤
        separableNormUnionValueMap (separableNormUnionStageExponent K L Ω N)
          (WithZero.exp (-(r : ℤ))) :=
      (separableNormUnionValueMap _).monotone' hw
    _ = WithZero.exp (-(r : ℚ) / (separableNormUnionStageExponent K L Ω N : ℚ)) := by
      rw [separableNormUnionValueMap_exp]
      simp only [Int.cast_neg, Int.cast_natCast]
    _ ≤ WithZero.exp (-(r : ℚ) / (f.natDegree : ℚ)) := by
      apply WithZero.exp_le_exp.mpr
      apply (div_le_div_iff₀ (by exact_mod_cast he : (0 : ℚ) < _)
        (by exact_mod_cast hdegree : (0 : ℚ) < _)).mpr
      exact mul_le_mul_of_nonpos_left (by exact_mod_cast hedegree.trans hdeg)
        (neg_nonpos.mpr (Nat.cast_nonneg r))

/-- The finite-precision source assertion for every real bound: the same
original residual has integer depth at least `degree * n`, strictly greater
than the actual ramification index times the prescribed bound. Its valuation
extending the base normalized valuation has depth at least `n > B`. -/
theorem exists_normLimit_approximate_root (B : ℝ) :
    letI := normLimitField K L p
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    ∀ f : Oₓ[X], f.Monic → (f.map (algebraMap Oₓ (NormLimit K L))).Separable →
      0 < f.natDegree →
      ∃ N : FiniteLayer L Ω,
        0 < separableNormUnionStageExponent K L Ω N ∧
        separableNormUnionStageExponent K L Ω N ≤ Module.finrank L N.val ∧
        Module.finrank L N.val ≤ f.natDegree ∧
        ∃ n : ℕ, B < n ∧
        (separableNormUnionStageExponent K L Ω N : ℝ) * B < f.natDegree * n ∧
        letI : Algebra.IsSeparable K N.val := Algebra.IsSeparable.trans K L N.val
        have := separableNormUnionStage_isAPF K L Ω N
        have : Fact (¬ Module.Finite K N.val) := ⟨separableNormUnionStage_infinite K L Ω N⟩
        letI := separableNormUnionStageField K L Ω p N
        let φ := finiteNormLimitRingHom K L N.val p
        ∃ z : NormLimit K N.val,
          normLimitValuation K N.val z ≤ 1 ∧
          normLimitValuation K N.val ((f.map (φ.comp (Oₓ).subtype)).eval z) ≤
            WithZero.exp (-((f.natDegree * n : ℕ) : ℤ)) ∧
          separableNormUnionStageValuation K L Ω p N
              ((f.map (φ.comp (Oₓ).subtype)).eval z) ≤ WithZero.exp (-(n : ℚ)) := by
  let := normLimitField K L p
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  intro f hf hsep hdegree
  obtain ⟨n, hn⟩ := exists_nat_gt B
  obtain ⟨N, he, hedegree, hdeg, hz⟩ := exists_normLimit_approximate_root_normalized
    K L p (Ω := Ω) (f.natDegree * n) f hf hsep hdegree
  have hB : (separableNormUnionStageExponent K L Ω N : ℝ) * B < f.natDegree * n := by
    calc
      _ < (separableNormUnionStageExponent K L Ω N : ℝ) * n :=
        mul_lt_mul_of_pos_left hn (by exact_mod_cast he)
      _ ≤ (f.natDegree : ℝ) * n :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hedegree.trans hdeg) (Nat.cast_nonneg n)
  refine ⟨N, he, hedegree, hdeg, n, hn, hB, ?_⟩
  let : Algebra.IsSeparable K N.val := Algebra.IsSeparable.trans K L N.val
  let := separableNormUnionStageField K L Ω p N
  obtain ⟨z, hint, hw, hs⟩ := hz
  refine ⟨z, hint, hw, ?_⟩
  have hk : (f.natDegree : ℚ) ≠ 0 := by exact_mod_cast hdegree.ne'
  have hcancel : -((f.natDegree * n : ℕ) : ℚ) / (f.natDegree : ℚ) = -(n : ℚ) := by
    push_cast
    field_simp
  simpa only [hcancel] using hs

/-- The actual finite root fields and original integral approximate roots
may be chosen simultaneously for any sequence of prescribed integer depths.
Both the original depth and the corrected normalized `1 / degree` bound
hold at every index, with no further existence assumptions. -/
theorem exists_normLimit_approximate_root_sequence (r : ℕ → ℕ) :
    letI := normLimitField K L p
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    ∀ f : Oₓ[X], f.Monic → (f.map (algebraMap Oₓ (NormLimit K L))).Separable →
      0 < f.natDegree →
      ∃ N : ℕ → FiniteLayer L Ω, (∀ n, Module.finrank L (N n).val ≤ f.natDegree) ∧
        ∃ z : ∀ n, NormLimit K (N n).val, ∀ n,
          letI : Algebra.IsSeparable K (N n).val := Algebra.IsSeparable.trans K L (N n).val
          letI := separableNormUnionStage_isAPF K L Ω (N n)
          letI : Fact (¬ Module.Finite K (N n).val) :=
            ⟨separableNormUnionStage_infinite K L Ω (N n)⟩
          letI := separableNormUnionStageField K L Ω p (N n)
          let φ := finiteNormLimitRingHom K L (N n).val p
          normLimitValuation K (N n).val (z n) ≤ 1 ∧
          normLimitValuation K (N n).val ((f.map (φ.comp (Oₓ).subtype)).eval (z n)) ≤
            WithZero.exp (-(r n : ℤ)) ∧
          separableNormUnionStageValuation K L Ω p (N n)
              ((f.map (φ.comp (Oₓ).subtype)).eval (z n)) ≤
            WithZero.exp (-(r n : ℚ) / (f.natDegree : ℚ)) := by
  let := normLimitField K L p
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  intro f hf hsep hdegree
  choose N _ _ hdeg hz using fun n => exists_normLimit_approximate_root_normalized
    K L p (Ω := Ω) (r n) f hf hsep hdegree
  refine ⟨N, hdeg, fun n => Classical.choose (hz n), ?_⟩
  intro n
  exact Classical.choose_spec (hz n)

/-- The corrected original-coordinate precision divided by the degree tends
to infinity at every prime, for every prescribed depth sequence tending to
infinity. No residue-field cardinality is involved. -/
theorem normLimit_approximation_precision_tendsto (k : ℕ) (hk : 0 < k)
    (b : ℕ → ℝ) (hb : Filter.Tendsto b Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun n => (⌈((p - 1 : ℕ) : ℝ) / p * b n⌉₊ : ℝ) / (k : ℝ))
      Filter.atTop Filter.atTop := by
  have hp : 0 < ((p - 1 : ℕ) : ℝ) / p := by
    have hp' := (Fact.out : p.Prime).two_le
    exact div_pos (by exact_mod_cast (by omega : 0 < p - 1))
      (by exact_mod_cast (Fact.out : p.Prime).pos)
  have hmul := Filter.Tendsto.const_mul_atTop hp hb
  have hceil := Filter.tendsto_atTop_mono (fun n => Nat.le_ceil
    (((p - 1 : ℕ) : ℝ) / p * b n)) hmul
  have h := Filter.Tendsto.const_mul_atTop (inv_pos.mpr (by exact_mod_cast hk : (0 : ℝ) < k)) hceil
  simpa only [div_eq_mul_inv, mul_comm] using h

end NormalizedApproximation

end FontaineWintenberger
