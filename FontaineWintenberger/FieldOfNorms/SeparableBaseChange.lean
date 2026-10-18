/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Ramification.PolynomialSplitting
public import FontaineWintenberger.Algebra.FiniteDescentTower
public import FontaineWintenberger.APF.AbstractFiniteBase
public import FontaineWintenberger.APF.FiniteExtension
public import FontaineWintenberger.APF.Bound

/-!
# Disjoint root adjunction at an actual full upper stage

The original full upper product makes the original conjugates of a root
remain conjugate over the original APF field. Its actual minimal polynomial
therefore keeps its degree, giving the original tensor isomorphism. The same
subgroup product, restricted to the root field, gives the finite-base first
ramification bound.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

open Polynomial

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]


local notation "OK" => Valuation.valuationSubring (NormedField.valuation (K := K))

/-- Every original conjugate of a root is attained by an automorphism fixing
the original field when its actual upper product is full. -/
theorem exists_fixing_aut_root_of_fullUpper
    (L : IntermediateField K (SeparableClosure K))
    (f : OK[X]) (hf : f.Monic) (hsep : (f.map (algebraMap OK K)).Separable)
    {b : ℝ} (hb : (f.natDegree.factorial : ℝ) *
      (IsDiscreteValuationRing.addVal OK f.discr).toNat ≤ b)
    (htop : apfSubgroup K L b = ⊤)
    (x : SeparableClosure K) (hx : aeval x f = 0)
    (y : SeparableClosure K) (hy : aeval y (minpoly K x) = 0) :
    ∃ h : SeparableClosure K ≃ₐ[K] SeparableClosure K,
      h ∈ L.fixingSubgroup ∧ h x = y := by
  obtain ⟨g, hg⟩ := minpoly.exists_algEquiv_of_root'
    (Algebra.IsAlgebraic.isAlgebraic (R := K) x) hy
  have hmem : g ∈ L.fixingSubgroup ⊔ absoluteUpperRamificationGroup K b := by
    change g ∈ apfSubgroup K L b
    rw [htop]
    trivial
  obtain ⟨h, hh, u, hu, hmul⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
  have hux := absoluteUpperRamificationGroup_fixes_integral_polynomial_root K f hf hsep hb u hu x hx
  refine ⟨h, hh, ?_⟩
  calc
    h x = h (u x) := congrArg h hux.symm
    _ = g x := by rw [← hmul]; rfl
    _ = y := hg

/-- The original minimal polynomial keeps its degree under root adjunction
to a field with full actual upper product. -/
theorem minpoly_natDegree_eq_of_fullUpper
    (L : IntermediateField K (SeparableClosure K))
    (f : OK[X]) (hf : f.Monic) (hsep : (f.map (algebraMap OK K)).Separable)
    {b : ℝ} (hb : (f.natDegree.factorial : ℝ) *
      (IsDiscreteValuationRing.addVal OK f.discr).toNat ≤ b)
    (htop : apfSubgroup K L b = ⊤)
    (x : SeparableClosure K) (hx : aeval x f = 0) :
    (minpoly L x).natDegree = (minpoly K x).natDegree := by
  let : Algebra.IsSeparable L (SeparableClosure K) :=
    Algebra.isSeparable_tower_top_of_isSeparable K L (SeparableClosure K)
  have hroots : (minpoly K x).rootSet (SeparableClosure K) ⊆
      (minpoly L x).rootSet (SeparableClosure K) := by
    intro y hy
    obtain ⟨h, hh, hxy⟩ := exists_fixing_aut_root_of_fullUpper K L f hf hsep hb htop x hx y
      (aeval_eq_zero_of_mem_rootSet hy)
    let hL := L.fixingSubgroupEquiv ⟨h, hh⟩
    apply (minpoly.monic (Algebra.IsIntegral.isIntegral (R := L) x)).mem_rootSet.mpr
    rw [← hxy]
    change aeval (hL x) (minpoly L x) = 0
    rw [aeval_algHom_apply, minpoly.aeval, map_zero]
  have hdeg : (minpoly K x).natDegree ≤ (minpoly L x).natDegree := by
    rw [← card_rootSet_eq_natDegree (K := SeparableClosure K) (Algebra.IsSeparable.isSeparable K x)
      (IsSepClosed.splits_codomain _ (Algebra.IsSeparable.isSeparable K x)),
      ← card_rootSet_eq_natDegree (K := SeparableClosure K) (Algebra.IsSeparable.isSeparable L x)
      (IsSepClosed.splits_codomain _ (Algebra.IsSeparable.isSeparable L x))]
    exact Fintype.card_le_of_injective (Set.inclusion hroots) (Set.inclusion_injective hroots)
  apply le_antisymm _ hdeg
  have hdvd := minpoly.dvd_map_of_isScalarTower K L x
  have hd := natDegree_le_of_dvd hdvd
    ((minpoly.monic (Algebra.IsIntegral.isIntegral (R := K) x)).map (algebraMap K L)).ne_zero
  simpa only [natDegree_map] using hd

/-- The literal mapped minimal polynomial equals the original minimal
polynomial over the APF field, by the proved degree equality. -/
theorem minpoly_map_eq_of_fullUpper
    (L : IntermediateField K (SeparableClosure K))
    (f : OK[X]) (hf : f.Monic) (hsep : (f.map (algebraMap OK K)).Separable)
    {b : ℝ} (hb : (f.natDegree.factorial : ℝ) *
      (IsDiscreteValuationRing.addVal OK f.discr).toNat ≤ b)
    (htop : apfSubgroup K L b = ⊤)
    (x : SeparableClosure K) (hx : aeval x f = 0) :
    (minpoly K x).map (algebraMap K L) = minpoly L x := by
  apply eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic (Algebra.IsIntegral.isIntegral (R := L) x))
    ((minpoly.monic (Algebra.IsIntegral.isIntegral (R := K) x)).map (algebraMap K L))
    (minpoly.dvd_map_of_isScalarTower K L x)
  rw [natDegree_map, minpoly_natDegree_eq_of_fullUpper K L f hf hsep hb htop x hx]

/-- The original finite root field is linearly disjoint from the original
APF field, with no normality hypothesis on either field. -/
theorem linearDisjoint_root_of_fullUpper
    (L : IntermediateField K (SeparableClosure K))
    (f : OK[X]) (hf : f.Monic) (hsep : (f.map (algebraMap OK K)).Separable)
    {b : ℝ} (hb : (f.natDegree.factorial : ℝ) *
      (IsDiscreteValuationRing.addVal OK f.discr).toNat ≤ b)
    (htop : apfSubgroup K L b = ⊤)
    (x : SeparableClosure K) (hx : aeval x f = 0) :
    (IntermediateField.adjoin K {x}).LinearDisjoint L :=
  linearDisjoint_adjoin_of_minpoly_lifts x (Algebra.IsIntegral.isIntegral (R := K) x)
    ⟨minpoly K x, minpoly_map_eq_of_fullUpper K L f hf hsep hb htop x hx⟩

/-- The actual simple compositum has exactly the original root-field degree. -/
theorem finrank_root_adjunction_eq_of_fullUpper
    (L : IntermediateField K (SeparableClosure K))
    (f : OK[X]) (hf : f.Monic) (hsep : (f.map (algebraMap OK K)).Separable)
    {b : ℝ} (hb : (f.natDegree.factorial : ℝ) *
      (IsDiscreteValuationRing.addVal OK f.discr).toNat ≤ b)
    (htop : apfSubgroup K L b = ⊤)
    (x : SeparableClosure K) (hx : aeval x f = 0) :
    Module.finrank L (IntermediateField.adjoin L {x}) =
      Module.finrank K (IntermediateField.adjoin K {x}) := by
  rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral (R := L) x),
    IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral (R := K) x)]
  exact minpoly_natDegree_eq_of_fullUpper K L f hf hsep hb htop x hx

/-- The actual original root field has degree at most the original polynomial. -/
theorem finrank_root_adjunction_le_polynomial_degree
    {Ω : Type*} [Field Ω] [Algebra K Ω]
    (f : OK[X]) (hf : f.Monic) (x : Ω) (hx : aeval x f = 0) :
    Module.finrank K (IntermediateField.adjoin K {x}) ≤ f.natDegree := by
  have hxK : aeval x (f.map (algebraMap OK K)) = 0 := by rwa [aeval_map_algebraMap]
  have hxint : IsIntegral K x := ⟨f.map (algebraMap OK K), hf.map _, hxK⟩
  rw [IntermediateField.adjoin.finrank hxint]
  have hd := natDegree_le_of_dvd (minpoly.dvd K x hxK) ((hf.map (algebraMap OK K)).ne_zero)
  simpa only [hf.natDegree_map] using hd

open scoped TensorProduct

/-- Inclusion of the original root field into the original simple compositum;
the map sends every element to that very same element. -/
def rootFieldToCompositum {Ω : Type*} [Field Ω] [Algebra K Ω]
    (L : IntermediateField K Ω) (x : Ω) :
    IntermediateField.adjoin K {x} →ₐ[K] IntermediateField.adjoin L {x} := by
  have h : IntermediateField.adjoin K {x} ≤
      (IntermediateField.adjoin L {x}).restrictScalars K := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro y (rfl : y = x)
    exact IntermediateField.mem_adjoin_simple_self L y
  exact
    { toFun := fun d => ⟨d, h d.property⟩
      map_zero' := Subtype.ext rfl
      map_one' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      commutes' := fun r => Subtype.ext (IsScalarTower.algebraMap_apply K L Ω r).symm }

/-- The original multiplication map on the original two fields. -/
def rootAdjunctionTensorMap {Ω : Type*} [Field Ω] [Algebra K Ω]
    (L : IntermediateField K Ω) (x : Ω) :
    L ⊗[K] (IntermediateField.adjoin K {x}) →ₐ[L] IntermediateField.adjoin L {x} :=
  AlgHom.liftEquiv K L (IntermediateField.adjoin K {x}) (IntermediateField.adjoin L {x})
    (rootFieldToCompositum K L x)

/-- The actual canonical multiplication map is bijective, using the proved
minimal-polynomial descent and the original primitive root. -/
theorem rootAdjunctionTensorMap_bijective_of_fullUpper
    (L : IntermediateField K (SeparableClosure K))
    (f : OK[X]) (hf : f.Monic) (hsep : (f.map (algebraMap OK K)).Separable)
    {b : ℝ} (hb : (f.natDegree.factorial : ℝ) *
      (IsDiscreteValuationRing.addVal OK f.discr).toNat ≤ b)
    (htop : apfSubgroup K L b = ⊤)
    (x : SeparableClosure K) (hx : aeval x f = 0) :
    Function.Bijective (rootAdjunctionTensorMap K L x) := by
  let D := IntermediateField.adjoin K {x}
  let M := IntermediateField.adjoin L {x}
  let φ := rootAdjunctionTensorMap K L x
  have hcomp : M.val.comp φ = AlgHom.liftEquiv K L D (SeparableClosure K) D.val := by
    ext d
    rfl
  constructor
  · intro u v huv
    apply injective_adjoin_tensor_lift x (Algebra.IsIntegral.isIntegral (R := K) x)
      ⟨minpoly K x, minpoly_map_eq_of_fullUpper K L f hf hsep hb htop x hx⟩
    rw [← hcomp]
    exact congrArg M.val huv
  · let q := IntermediateField.adjoin.powerBasis (Algebra.IsIntegral.isIntegral (R := L) x)
    have htopφ : (⊤ : Subalgebra L M) ≤ φ.range := by
      rw [← q.adjoin_gen_eq_top]
      apply Algebra.adjoin_le
      rintro y (rfl : y = q.gen)
      refine ⟨1 ⊗ₜ[K] ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩, ?_⟩
      apply Subtype.ext
      change (1 : L) • x = x
      exact one_smul L x
    intro y
    exact htopφ trivial

/-- The original multiplication isomorphism, with all conclusions proved
from the full upper stage rather than supplied as certificates. -/
def rootAdjunctionTensorEquivOfFullUpper
    (L : IntermediateField K (SeparableClosure K))
    (f : OK[X]) (hf : f.Monic) (hsep : (f.map (algebraMap OK K)).Separable)
    {b : ℝ} (hb : (f.natDegree.factorial : ℝ) *
      (IsDiscreteValuationRing.addVal OK f.discr).toNat ≤ b)
    (htop : apfSubgroup K L b = ⊤)
    (x : SeparableClosure K) (hx : aeval x f = 0) :
    L ⊗[K] (IntermediateField.adjoin K {x}) ≃ₐ[L] IntermediateField.adjoin L {x} :=
  AlgEquiv.ofBijective (rootAdjunctionTensorMap K L x)
    (rootAdjunctionTensorMap_bijective_of_fullUpper K L f hf hsep hb htop x hx)

@[simp]
theorem rootAdjunctionTensorEquivOfFullUpper_tmul
    (L : IntermediateField K (SeparableClosure K))
    (f : OK[X]) (hf : f.Monic) (hsep : (f.map (algebraMap OK K)).Separable)
    {b : ℝ} (hb : (f.natDegree.factorial : ℝ) *
      (IsDiscreteValuationRing.addVal OK f.discr).toNat ≤ b)
    (htop : apfSubgroup K L b = ⊤)
    (x : SeparableClosure K) (hx : aeval x f = 0)
    (l : L) (d : IntermediateField.adjoin K {x}) :
    (rootAdjunctionTensorEquivOfFullUpper K L f hf hsep hb htop x hx (l ⊗ₜ[K] d) :
      SeparableClosure K) = (l : SeparableClosure K) * d := by
  change (l : SeparableClosure K) * d = (l : SeparableClosure K) * d
  rfl

/-- The actual absolute upper group fixes the whole original root field. -/
theorem absoluteUpper_le_root_fixingSubgroup
    (f : OK[X]) (hf : f.Monic) (hsep : (f.map (algebraMap OK K)).Separable)
    {b : ℝ} (hb : (f.natDegree.factorial : ℝ) *
      (IsDiscreteValuationRing.addVal OK f.discr).toNat ≤ b)
    (x : SeparableClosure K) (hx : aeval x f = 0) :
    absoluteUpperRamificationGroup K b ≤ (IntermediateField.adjoin K {x}).fixingSubgroup := by
  apply (IntermediateField.le_iff_le _ _).mp
  apply IntermediateField.adjoin_simple_le_iff.mpr
  intro g
  exact absoluteUpperRamificationGroup_fixes_integral_polynomial_root K f hf hsep hb
    g.val g.property x hx

/-- Restricting the full product to the root-field fixing group gives the
actual compositum product, on the original ambient automorphisms. -/
theorem apfSubgroup_root_compositum_eq_fixingSubgroup
    (L : IntermediateField K (SeparableClosure K))
    (f : OK[X]) (hf : f.Monic) (hsep : (f.map (algebraMap OK K)).Separable)
    {b : ℝ} (hb : (f.natDegree.factorial : ℝ) *
      (IsDiscreteValuationRing.addVal OK f.discr).toNat ≤ b)
    (htop : apfSubgroup K L b = ⊤)
    (x : SeparableClosure K) (hx : aeval x f = 0) :
    apfSubgroup K ((IntermediateField.adjoin L {x}).restrictScalars K) b =
      (IntermediateField.adjoin K {x}).fixingSubgroup := by
  have hU := absoluteUpper_le_root_fixingSubgroup K f hf hsep hb x hx
  rw [IntermediateField.restrictScalars_adjoin_eq_sup, apfSubgroup,
    IntermediateField.fixingSubgroup_sup]
  apply le_antisymm (sup_le inf_le_right hU)
  intro g hg
  have hm : g ∈ L.fixingSubgroup ⊔ absoluteUpperRamificationGroup K b := by
    change g ∈ apfSubgroup K L b
    rw [htop]
    trivial
  obtain ⟨h, hh, u, hu, hmul⟩ := Subgroup.mem_sup_of_normal_right.mp hm
  have hhJ : h ∈ (IntermediateField.adjoin K {x}).fixingSubgroup := by
    have hmJ := (IntermediateField.adjoin K {x}).fixingSubgroup.mul_mem hg
      ((IntermediateField.adjoin K {x}).fixingSubgroup.inv_mem (hU hu))
    rw [← hmul, mul_inv_cancel_right] at hmJ
    exact hmJ
  exact Subgroup.mem_sup_of_normal_right.mpr ⟨h, ⟨hh, hhJ⟩, u, hu, hmul⟩

section RootStructures

variable {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (x : Ω)

local notation "D" => IntermediateField.adjoin K (Singleton.singleton x : Set Ω)

local instance rootField_finite : FiniteDimensional K D :=
  IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := K) x)
local instance rootField_normedField : NontriviallyNormedField D :=
  spectralNorm.nontriviallyNormedField K D
local instance rootField_normedAlgebra : NormedAlgebra K D := spectralNorm.normedAlgebra K D
local instance rootField_ultrametric : IsUltrametricDist D :=
  IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := D))
local instance rootField_complete : CompleteSpace D := spectralNorm.completeSpace K D
local instance rootField_discrete :
    IsCompleteDiscreteValuedField D :=
  normedAlgebra_isCompleteDiscreteValuedField K D
local instance rootField_separableClosureAlgebra : Algebra D (SeparableClosure D) :=
  (separableClosure D (AlgebraicClosure D)).algebra'

variable [PerfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := K)).valuationSubring)]

local instance rootField_residuePerfect : PerfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := D)).valuationSubring) :=
  normedAlgebra_residueField_perfectField K D

variable (L : IntermediateField K Ω)

local notation "M" => IntermediateField.adjoin L (Singleton.singleton x : Set Ω)

local instance rootCompositum_algebra : Algebra D M :=
  (rootFieldToCompositum K L x).toRingHom.toAlgebra
local instance rootCompositum_tower : IsScalarTower K D M :=
  IsScalarTower.of_algHom (rootFieldToCompositum K L x)
local instance rootCompositum_towerTop : IsScalarTower D M Ω :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)
local instance rootCompositum_separable : Algebra.IsSeparable D M :=
  Algebra.IsSeparable.of_algHom D Ω
    ({ (M).val.toRingHom with commutes' := fun _ => rfl } : M →ₐ[D] Ω)
local instance rootCompositum_separableBase : Algebra.IsSeparable K M :=
  Algebra.IsSeparable.of_algHom K Ω ((M).val.restrictScalars K)
local instance rootCompositum_finite : FiniteDimensional L M :=
  IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := L) x)

end RootStructures

section RelativeRoot

variable (x : SeparableClosure K)
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
    (L : IntermediateField K (SeparableClosure K))

attribute [local instance] rootField_finite rootField_normedField rootField_normedAlgebra
  rootField_ultrametric rootField_complete rootField_discrete rootField_separableClosureAlgebra
  rootField_residuePerfect rootCompositum_algebra rootCompositum_tower rootCompositum_towerTop
  rootCompositum_separable rootCompositum_separableBase rootCompositum_finite

local notation "D" => IntermediateField.adjoin K (Singleton.singleton x : Set (SeparableClosure K))
local notation "M" => IntermediateField.adjoin L (Singleton.singleton x : Set (SeparableClosure K))

omit [PerfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := K)).valuationSubring)] in
/-- The actual finite separable root adjunction remains APF over the original base. -/
theorem isAPF_rootAdjunction (hL : IsAPF K L) : IsAPF K M :=
  (isAPF_finite_extension_iff K M L).mpr hL

omit [IsCompleteDiscreteValuedField K] [PerfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := K)).valuationSubring)]
      in
/-- The original infinite field embeds in its actual simple compositum,
so that compositum still has infinite degree over the original base. -/
theorem rootAdjunction_not_finite (hL : ¬ Module.Finite K L) : ¬ Module.Finite K M := by
  intro hM
  let : Module.Finite K M := hM
  exact hL (Module.Finite.of_injective (IsScalarTower.toAlgHom K L M).toLinearMap
    (IsScalarTower.toAlgHom K L M).injective)

/-- The original compositum has full relative upper product over the original
root field at the original finite-base Herbrand parameter. -/
theorem rootAdjunction_fullUpper
    (f : OK[X]) (hf : f.Monic) (hsep : (f.map (algebraMap OK K)).Separable)
    {b : ℝ} (hb : (f.natDegree.factorial : ℝ) *
      (IsDiscreteValuationRing.addVal OK f.discr).toNat ≤ b)
    (htop : apfSubgroup K L b = ⊤) (hx : aeval x f = 0) :
    apfSubgroup D (IsSepClosed.lift : M →ₐ[D] SeparableClosure D).fieldRange
      (apfPsi K D b) = ⊤ := by
  have hb0 : 0 ≤ b := (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)).trans hb
  have hu : -1 ≤ b := by linarith
  let e := AbstractFiniteBase.closureEquiv K D
  let j : M →ₐ[D] SeparableClosure K :=
    { (M).val.toRingHom with commutes' := fun _ => rfl }
  let i := e.symm.toAlgHom.comp j
  have he : AbstractFiniteBase.embedding K D i = (M).val.restrictScalars K := by
    apply AlgHom.ext
    intro y
    exact e.apply_symm_apply (j y)
  have hr : (AbstractFiniteBase.embedding K D i).fieldRange = (M).restrictScalars K := by
    rw [he]
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact z.property
    · intro hy
      exact ⟨⟨y, hy⟩, rfl⟩
  have hc := AbstractFiniteBase.comap_apf K D i hu
  rw [hr, apfSubgroup_root_compositum_eq_fixingSubgroup K L f hf hsep hb htop x hx] at hc
  have hrange : (AbstractFiniteBase.closureHom K D).range = (D).fixingSubgroup := by
    simpa only [show IsScalarTower.toAlgHom K D (SeparableClosure K) = (D).val from rfl,
      IntermediateField.fieldRange_val] using AbstractFiniteBase.closureHom_range K D
  have hi : apfSubgroup D i.fieldRange (apfPsi K D b) = ⊤ := by
    rw [← hc, ← hrange]
    apply top_unique
    intro g _
    exact ⟨g, rfl⟩
  exact (apfSubgroup_fieldRange_eq_top_iff D M i IsSepClosed.lift (apfPsi K D b)).mp hi

/-- The same original relative upper product gives the actual extended
first-bound estimate, including a trivial original root field. -/
theorem apfPsi_le_rootAdjunction_firstBound
    (f : OK[X]) (hf : f.Monic) (hsep : (f.map (algebraMap OK K)).Separable)
    {b : ℝ} (hb : (f.natDegree.factorial : ℝ) *
      (IsDiscreteValuationRing.addVal OK f.discr).toNat ≤ b)
    (htop : apfSubgroup K L b = ⊤) (hx : aeval x f = 0) :
    (apfPsi K D b : EReal) ≤ apfRamificationBound D M := by
  have hb0 : 0 ≤ b := (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)).trans hb
  exact le_apfRamificationBound D M IsSepClosed.lift
    (IsAPF.apfPsi_mem_Ici K D (isAPF_of_finite K D) (by linarith))
    (rootAdjunction_fullUpper K x L f hf hsep hb htop hx)

/-- The actual new-base first bound is at least the original full-product
parameter, by the proved finite-base Herbrand lower bound. -/
theorem le_rootAdjunction_firstBound
    (f : OK[X]) (hf : f.Monic) (hsep : (f.map (algebraMap OK K)).Separable)
    {b : ℝ} (hb : (f.natDegree.factorial : ℝ) *
      (IsDiscreteValuationRing.addVal OK f.discr).toNat ≤ b)
    (htop : apfSubgroup K L b = ⊤) (hx : aeval x f = 0) :
    (b : EReal) ≤ apfRamificationBound D M :=
  (EReal.coe_le_coe_iff.mpr (IsAPF.le_apfPsi K D (isAPF_of_finite K D) b)).trans
    (apfPsi_le_rootAdjunction_firstBound K x L f hf hsep hb htop hx)

end RelativeRoot

section CommonClosure

variable {Ω : Type*} [Field Ω] [Algebra K Ω]

/-- The original full product in any chosen common closure pulls back to
the actual full product in the canonical separable closure. -/
theorem apfSubgroup_comap_closureEquiv_eq_top
    (e : SeparableClosure K ≃ₐ[K] Ω) (L : IntermediateField K Ω)
    {b : ℝ} (hb : -1 ≤ b)
    (htop : L.fixingSubgroup ⊔ upperRamificationGroupInfinite K Ω b = ⊤) :
    apfSubgroup K (L.comap e.toAlgHom) b = ⊤ := by
  have hmap : (apfSubgroup K (L.comap e.toAlgHom) b).map e.autCongr.toMonoidHom =
      L.fixingSubgroup ⊔ upperRamificationGroupInfinite K Ω b := by
    rw [apfSubgroup, Subgroup.map_sup, fixingSubgroup_map_autCongr,
      IntermediateField.map_comap_eq_self_of_surjective e.surjective,
      upperRamificationGroupInfinite_map_autCongr K e hb]
  apply top_unique
  intro g _
  have hg : e.autCongr g ∈ (apfSubgroup K (L.comap e.toAlgHom) b).map e.autCongr.toMonoidHom := by
    rw [hmap, htop]
    trivial
  obtain ⟨h, hh, he⟩ := hg
  exact e.autCongr.injective he ▸ hh

variable [IsSepClosure K Ω]

/-- Disjoint root adjunction retains the same original fields and root in
any chosen separable closure, through the proved actual closure isomorphism. -/
theorem linearDisjoint_root_of_fullUpper_commonClosure
    (L : IntermediateField K Ω)
    (f : OK[X]) (hf : f.Monic) (hsep : (f.map (algebraMap OK K)).Separable)
    {b : ℝ} (hb : (f.natDegree.factorial : ℝ) *
      (IsDiscreteValuationRing.addVal OK f.discr).toNat ≤ b)
    (htop : L.fixingSubgroup ⊔ upperRamificationGroupInfinite K Ω b = ⊤)
    (x : Ω) (hx : aeval x f = 0) :
    (IntermediateField.adjoin K {x}).LinearDisjoint L := by
  let e := IsSepClosure.equiv K (SeparableClosure K) Ω
  let y := e.symm x
  have hy : aeval y f = 0 := by
    apply e.injective
    rw [map_zero]
    change (e.restrictScalars OK) (aeval y f) = 0
    rw [← aeval_algHom_apply]
    change aeval (e (e.symm x)) f = 0
    rw [e.apply_symm_apply]
    exact hx
  have hb0 : 0 ≤ b := (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)).trans hb
  have hL := apfSubgroup_comap_closureEquiv_eq_top K e L (by linarith) htop
  have hld := (linearDisjoint_root_of_fullUpper K (L.comap e.toAlgHom) f hf hsep hb hL y hy).map
    e.toAlgHom
  have hxy : e.toAlgHom y = x := e.apply_symm_apply x
  rw [IntermediateField.adjoin_map, Set.image_singleton, hxy,
    IntermediateField.map_comap_eq_self_of_surjective (f := e.toAlgHom) e.surjective] at hld
  exact hld

omit [IsCompleteDiscreteValuedField K] in
/-- The original primitive root makes the canonical multiplication map onto
the original simple compositum, in any common ambient field. -/
theorem rootAdjunctionTensorMap_surjective_commonClosure
    (L : IntermediateField K Ω) (x : Ω) :
    Function.Surjective (rootAdjunctionTensorMap K L x) := by
  let M := IntermediateField.adjoin L {x}
  let φ := rootAdjunctionTensorMap K L x
  let q := IntermediateField.adjoin.powerBasis (Algebra.IsIntegral.isIntegral (R := L) x)
  have htopφ : (⊤ : Subalgebra L M) ≤ φ.range := by
    rw [← q.adjoin_gen_eq_top]
    apply Algebra.adjoin_le
    rintro y (rfl : y = q.gen)
    refine ⟨1 ⊗ₜ[K] ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩, ?_⟩
    apply Subtype.ext
    change (1 : L) • x = x
    exact one_smul L x
  intro y
  exact htopφ trivial

/-- The original canonical tensor map is bijective in every chosen common
separable closure; the carrier is the actual simple compositum there. -/
theorem rootAdjunctionTensorMap_bijective_commonClosure
    (L : IntermediateField K Ω)
    (f : OK[X]) (hf : f.Monic) (hsep : (f.map (algebraMap OK K)).Separable)
    {b : ℝ} (hb : (f.natDegree.factorial : ℝ) *
      (IsDiscreteValuationRing.addVal OK f.discr).toNat ≤ b)
    (htop : L.fixingSubgroup ⊔ upperRamificationGroupInfinite K Ω b = ⊤)
    (x : Ω) (hx : aeval x f = 0) :
    Function.Bijective (rootAdjunctionTensorMap K L x) := by
  let D := IntermediateField.adjoin K {x}
  let M := IntermediateField.adjoin L {x}
  let : FiniteDimensional K D :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := K) x)
  have hld := linearDisjoint_root_of_fullUpper_commonClosure K L f hf hsep hb htop x hx
  have hcomp : M.val.comp (rootAdjunctionTensorMap K L x) =
      AlgHom.liftEquiv K L D Ω D.val := by
    ext d
    rfl
  refine ⟨?_, rootAdjunctionTensorMap_surjective_commonClosure K L x⟩
  intro u v huv
  apply injective_tensor_lift_of_linearDisjoint D hld
  rw [← hcomp]
  exact congrArg M.val huv

/-- Canonical multiplication identifies the tensor of the same original
fields with their same original simple compositum in the chosen closure. -/
def rootAdjunctionTensorEquivCommonClosure
    (L : IntermediateField K Ω)
    (f : OK[X]) (hf : f.Monic) (hsep : (f.map (algebraMap OK K)).Separable)
    {b : ℝ} (hb : (f.natDegree.factorial : ℝ) *
      (IsDiscreteValuationRing.addVal OK f.discr).toNat ≤ b)
    (htop : L.fixingSubgroup ⊔ upperRamificationGroupInfinite K Ω b = ⊤)
    (x : Ω) (hx : aeval x f = 0) :
    L ⊗[K] (IntermediateField.adjoin K {x}) ≃ₐ[L] IntermediateField.adjoin L {x} :=
  AlgEquiv.ofBijective (rootAdjunctionTensorMap K L x)
    (rootAdjunctionTensorMap_bijective_commonClosure K L f hf hsep hb htop x hx)

@[simp]
theorem rootAdjunctionTensorEquivCommonClosure_tmul
    (L : IntermediateField K Ω)
    (f : OK[X]) (hf : f.Monic) (hsep : (f.map (algebraMap OK K)).Separable)
    {b : ℝ} (hb : (f.natDegree.factorial : ℝ) *
      (IsDiscreteValuationRing.addVal OK f.discr).toNat ≤ b)
    (htop : L.fixingSubgroup ⊔ upperRamificationGroupInfinite K Ω b = ⊤)
    (x : Ω) (hx : aeval x f = 0) (l : L) (d : IntermediateField.adjoin K {x}) :
    (rootAdjunctionTensorEquivCommonClosure K L f hf hsep hb htop x hx (l ⊗ₜ[K] d) : Ω) =
      (l : Ω) * d := rfl

/-- The source degree equality holds on the same original fields in any
chosen common separable closure. -/
theorem finrank_root_adjunction_eq_commonClosure
    (L : IntermediateField K Ω)
    (f : OK[X]) (hf : f.Monic) (hsep : (f.map (algebraMap OK K)).Separable)
    {b : ℝ} (hb : (f.natDegree.factorial : ℝ) *
      (IsDiscreteValuationRing.addVal OK f.discr).toNat ≤ b)
    (htop : L.fixingSubgroup ⊔ upperRamificationGroupInfinite K Ω b = ⊤)
    (x : Ω) (hx : aeval x f = 0) :
    Module.finrank L (IntermediateField.adjoin L {x}) =
      Module.finrank K (IntermediateField.adjoin K {x}) := by
  have he := (rootAdjunctionTensorEquivCommonClosure K L f hf hsep hb htop x
      hx).toLinearEquiv.finrank_eq
  simpa only [Module.finrank_tensorProduct, Module.finrank_self, one_mul] using he.symm

/-- The original upper group in the chosen common closure fixes the whole
original root field there. -/
theorem upper_le_root_fixingSubgroup_commonClosure
    (f : OK[X]) (hf : f.Monic) (hsep : (f.map (algebraMap OK K)).Separable)
    {b : ℝ} (hb : (f.natDegree.factorial : ℝ) *
      (IsDiscreteValuationRing.addVal OK f.discr).toNat ≤ b)
    (x : Ω) (hx : aeval x f = 0) :
    upperRamificationGroupInfinite K Ω b ≤ (IntermediateField.adjoin K {x}).fixingSubgroup := by
  let e := IsSepClosure.equiv K (SeparableClosure K) Ω
  let y := e.symm x
  have hy : aeval y f = 0 := by
    apply e.injective
    rw [map_zero]
    change (e.restrictScalars OK) (aeval y f) = 0
    rw [← aeval_algHom_apply]
    change aeval (e (e.symm x)) f = 0
    rwa [e.apply_symm_apply]
  have hb0 : 0 ≤ b := (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)).trans hb
  have hle := Subgroup.map_mono (f := e.autCongr.toMonoidHom)
    (absoluteUpper_le_root_fixingSubgroup K f hf hsep hb y hy)
  have hxy : e.toAlgHom y = x := e.apply_symm_apply x
  rw [upperRamificationGroupInfinite_map_autCongr K e (by linarith),
    fixingSubgroup_map_autCongr, IntermediateField.adjoin_map, Set.image_singleton, hxy] at hle
  exact hle

/-- The actual compositum upper product is the root-field fixing subgroup,
on the same original automorphisms in the chosen common closure. -/
theorem upperProduct_root_compositum_eq_commonClosure
    (L : IntermediateField K Ω)
    (f : OK[X]) (hf : f.Monic) (hsep : (f.map (algebraMap OK K)).Separable)
    {b : ℝ} (hb : (f.natDegree.factorial : ℝ) *
      (IsDiscreteValuationRing.addVal OK f.discr).toNat ≤ b)
    (htop : L.fixingSubgroup ⊔ upperRamificationGroupInfinite K Ω b = ⊤)
    (x : Ω) (hx : aeval x f = 0) :
    ((IntermediateField.adjoin L {x}).restrictScalars K).fixingSubgroup ⊔
      upperRamificationGroupInfinite K Ω b = (IntermediateField.adjoin K {x}).fixingSubgroup := by
  have hU := upper_le_root_fixingSubgroup_commonClosure K f hf hsep hb x hx
  rw [IntermediateField.restrictScalars_adjoin_eq_sup, IntermediateField.fixingSubgroup_sup]
  apply le_antisymm (sup_le inf_le_right hU)
  intro g hg
  have hm : g ∈ L.fixingSubgroup ⊔ upperRamificationGroupInfinite K Ω b := htop ▸ Subgroup.mem_top g
  obtain ⟨h, hh, u, hu, hmul⟩ := Subgroup.mem_sup_of_normal_right.mp hm
  have hhJ : h ∈ (IntermediateField.adjoin K {x}).fixingSubgroup := by
    have hmJ := (IntermediateField.adjoin K {x}).fixingSubgroup.mul_mem hg
      ((IntermediateField.adjoin K {x}).fixingSubgroup.inv_mem (hU hu))
    rw [← hmul, mul_inv_cancel_right] at hmJ
    exact hmJ
  exact Subgroup.mem_sup_of_normal_right.mpr ⟨h, ⟨hh, hhJ⟩, u, hu, hmul⟩

section RelativeCommonClosure

variable (x : Ω) [PerfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := K)).valuationSubring)] (L : IntermediateField K Ω)

attribute [local instance] rootField_finite rootField_normedField rootField_normedAlgebra
  rootField_ultrametric rootField_complete rootField_discrete rootField_separableClosureAlgebra
  rootField_residuePerfect rootCompositum_algebra rootCompositum_tower rootCompositum_towerTop
  rootCompositum_separable rootCompositum_separableBase rootCompositum_finite

local notation "D" => IntermediateField.adjoin K (Singleton.singleton x : Set Ω)
local notation "M" => IntermediateField.adjoin L (Singleton.singleton x : Set Ω)

omit [PerfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := K)).valuationSubring)] in
/-- The same original root compositum in the chosen common closure remains APF. -/
theorem isAPF_rootAdjunction_commonClosure (hL : IsAPF K L) : IsAPF K M :=
  (isAPF_finite_extension_iff K M L).mpr hL

omit [IsCompleteDiscreteValuedField K] [PerfectField (IsLocalRing.ResidueField
    (NormedField.valuation (K := K)).valuationSubring)]
      [IsSepClosure K Ω] in
/-- Infinite degree is retained by the same original root compositum in the
chosen common closure. -/
theorem rootAdjunction_not_finite_commonClosure (hL : ¬ Module.Finite K L) :
    ¬ Module.Finite K M := by
  intro hM
  let : Module.Finite K M := hM
  exact hL (Module.Finite.of_injective (IsScalarTower.toAlgHom K L M).toLinearMap
    (IsScalarTower.toAlgHom K L M).injective)

/-- The full relative upper product over the actual root field in the
chosen common closure. All field carriers remain the original carriers. -/
theorem rootAdjunction_fullUpper_commonClosure
    (f : OK[X]) (hf : f.Monic) (hsep : (f.map (algebraMap OK K)).Separable)
    {b : ℝ} (hb : (f.natDegree.factorial : ℝ) *
      (IsDiscreteValuationRing.addVal OK f.discr).toNat ≤ b)
    (htop : L.fixingSubgroup ⊔ upperRamificationGroupInfinite K Ω b = ⊤)
    (hx : aeval x f = 0) :
    apfSubgroup D (IsSepClosed.lift : M →ₐ[D] SeparableClosure D).fieldRange
      (apfPsi K D b) = ⊤ := by
  have hb0 : 0 ≤ b := (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)).trans hb
  have hu : -1 ≤ b := by linarith
  let eK := IsSepClosure.equiv K (SeparableClosure K) Ω
  let jD := eK.symm.toAlgHom.comp (D).val
  let : Algebra D (SeparableClosure K) := jD.toRingHom.toAlgebra
  let : IsScalarTower K D (SeparableClosure K) := IsScalarTower.of_algHom jD
  let j : M →ₐ[D] SeparableClosure K :=
    { (eK.symm.toAlgHom.comp ((M).val.restrictScalars K)).toRingHom with
      commutes' := fun _ => rfl }
  let e := AbstractFiniteBase.closureEquiv K D
  let i := e.symm.toAlgHom.comp j
  have he : AbstractFiniteBase.embedding K D i =
      eK.symm.toAlgHom.comp ((M).val.restrictScalars K) := by
    apply AlgHom.ext
    intro y
    exact e.apply_symm_apply (j y)
  have hr : (AbstractFiniteBase.embedding K D i).fieldRange =
      ((M).restrictScalars K).map eK.symm.toAlgHom := by
    rw [he]
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z.val, z.property, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
  have hgroup := congrArg (fun A => A.map eK.symm.autCongr.toMonoidHom)
    (upperProduct_root_compositum_eq_commonClosure K L f hf hsep hb htop x hx)
  rw [Subgroup.map_sup, fixingSubgroup_map_autCongr,
    upperRamificationGroupInfinite_map_autCongr K eK.symm hu,
    fixingSubgroup_map_autCongr] at hgroup
  have hc := AbstractFiniteBase.comap_apf K D i hu
  rw [hr, show apfSubgroup K (((M).restrictScalars K).map eK.symm.toAlgHom) b =
    ((D).map eK.symm.toAlgHom).fixingSubgroup from hgroup] at hc
  have hD : (IsScalarTower.toAlgHom K D (SeparableClosure K)).fieldRange =
      (D).map eK.symm.toAlgHom := by
    change jD.fieldRange = _
    exact IntermediateField.fieldRange_comp_val (D) eK.symm.toAlgHom
  have hrange : (AbstractFiniteBase.closureHom K D).range =
      ((D).map eK.symm.toAlgHom).fixingSubgroup := by
    rw [AbstractFiniteBase.closureHom_range K D, hD]
  have hi : apfSubgroup D i.fieldRange (apfPsi K D b) = ⊤ := by
    rw [← hc, ← hrange]
    apply top_unique
    intro g _
    exact ⟨g, rfl⟩
  exact (apfSubgroup_fieldRange_eq_top_iff D M i IsSepClosed.lift (apfPsi K D b)).mp hi

/-- The actual relative first bound in the chosen common closure dominates
the original finite-base Herbrand parameter. -/
theorem apfPsi_le_rootAdjunction_firstBound_commonClosure
    (f : OK[X]) (hf : f.Monic) (hsep : (f.map (algebraMap OK K)).Separable)
    {b : ℝ} (hb : (f.natDegree.factorial : ℝ) *
      (IsDiscreteValuationRing.addVal OK f.discr).toNat ≤ b)
    (htop : L.fixingSubgroup ⊔ upperRamificationGroupInfinite K Ω b = ⊤)
    (hx : aeval x f = 0) :
    (apfPsi K D b : EReal) ≤ apfRamificationBound D M := by
  have hb0 : 0 ≤ b := (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)).trans hb
  exact le_apfRamificationBound D M IsSepClosed.lift
    (IsAPF.apfPsi_mem_Ici K D (isAPF_of_finite K D) (by linarith))
    (rootAdjunction_fullUpper_commonClosure K x L f hf hsep hb htop hx)

/-- The same original new-base first bound also dominates the original
parameter, since the actual finite-base inverse Herbrand function does. -/
theorem le_rootAdjunction_firstBound_commonClosure
    (f : OK[X]) (hf : f.Monic) (hsep : (f.map (algebraMap OK K)).Separable)
    {b : ℝ} (hb : (f.natDegree.factorial : ℝ) *
      (IsDiscreteValuationRing.addVal OK f.discr).toNat ≤ b)
    (htop : L.fixingSubgroup ⊔ upperRamificationGroupInfinite K Ω b = ⊤)
    (hx : aeval x f = 0) :
    (b : EReal) ≤ apfRamificationBound D M :=
  (EReal.coe_le_coe_iff.mpr (IsAPF.le_apfPsi K D (isAPF_of_finite K D) b)).trans
    (apfPsi_le_rootAdjunction_firstBound_commonClosure K x L f hf hsep hb htop hx)

end RelativeCommonClosure

end CommonClosure

end FontaineWintenberger
