/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Residue
public import FontaineWintenberger.LocalField.Teichmuller
public import FontaineWintenberger.APF.MaximalTame
public import FontaineWintenberger.LocalField.TruncatedCoefficients

/-!
# Source-normalized residue constants in the original norm limit

Compatible tail coordinates extend through actual finite composita and field
norms to the original zero-adjoined multiplicative norm-limit carrier.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

section CofinalTail

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- The actual norm of an original element from the smaller finite field
is its power by the genuine relative field degree. -/
theorem FiniteLayer.norm_inclusion (E F : FiniteLayer K L) (hEF : E ≤ F) (x : E.val) :
    FiniteLayer.norm E F hEF (IntermediateField.inclusion hEF x) =
      x ^ Module.finrank E.val (IntermediateField.extendScalars hEF) := by
  let F' := IntermediateField.extendScalars hEF
  have : FiniteDimensional K F' := F.property
  have : FiniteDimensional E.val F' := Module.Finite.right K E.val F'
  let : Module.Free E.val F' := Module.Free.of_divisionRing E.val F'
  change Algebra.norm E.val (algebraMap E.val F' x) = _
  exact Algebra.norm_algebraMap x

/-- Actual evaluations on the cofinal tail above any finite layer already
distinguish elements of the original norm-limit carrier. -/
theorem NormLimit.ext_tail (D : FiniteLayer K L) {α β : NormLimit K L}
    (h : ∀ E : FiniteLayer K L, D ≤ E → normLimitEval K L E α = normLimitEval K L E β) :
    α = β := by
  apply NormLimit.ext K L
  intro E
  rw [← normLimitEval_norm K L E (FiniteLayer.sup E D) (FiniteLayer.le_sup_left E D) α,
    ← normLimitEval_norm K L E (FiniteLayer.sup E D) (FiniteLayer.le_sup_left E D) β,
    h (FiniteLayer.sup E D) (FiniteLayer.le_sup_right E D)]

/-- A compatible family on an actual cofinal finite-layer tail extends
uniquely to an element of the original multiplicative norm limit. -/
theorem existsUnique_normLimit_of_compatible_tail (D : FiniteLayer K L)
    (x : ∀ E : FiniteLayer K L, D ≤ E → E.val)
    (hx : ∀ (E F : FiniteLayer K L) (hDE : D ≤ E) (hDF : D ≤ F) (hEF : E ≤ F),
      FiniteLayer.norm E F hEF (x F hDF) = x E hDE) :
    ∃! α : NormLimit K L, ∀ (E : FiniteLayer K L) (hDE : D ≤ E),
      normLimitEval K L E α = x E hDE := by
  let f (E : FiniteLayer K L) := FiniteLayer.norm E (FiniteLayer.sup E D)
    (FiniteLayer.le_sup_left E D) (x (FiniteLayer.sup E D) (FiniteLayer.le_sup_right E D))
  have hf (E F : FiniteLayer K L) (hEF : E ≤ F) : FiniteLayer.norm E F hEF (f F) = f E := by
    have hs : FiniteLayer.sup E D ≤ FiniteLayer.sup F D :=
      (show E.val ⊔ D.val ≤ F.val ⊔ D.val from sup_le_sup hEF le_rfl)
    dsimp only [f]
    rw [FiniteLayer.norm_norm, ← FiniteLayer.norm_norm E (FiniteLayer.sup E D)
      (FiniteLayer.sup F D) (FiniteLayer.le_sup_left E D) hs]
    rw [hx (FiniteLayer.sup E D) (FiniteLayer.sup F D)
      (FiniteLayer.le_sup_right E D) (FiniteLayer.le_sup_right F D) hs]
  obtain ⟨α, hα, _⟩ := existsUnique_normLimit_of_compatible K L f hf
  refine ⟨α, ?_, ?_⟩
  · intro E hDE
    exact (hα E).trans (hx E (FiniteLayer.sup E D) hDE (FiniteLayer.le_sup_right E D)
      (FiniteLayer.le_sup_left E D))
  · intro β hβ
    apply NormLimit.ext_tail K L D
    intro E hDE
    exact (hβ E hDE).trans ((hα E).trans
      (hx E (FiniteLayer.sup E D) hDE (FiniteLayer.le_sup_right E D)
        (FiniteLayer.le_sup_left E D))).symm

/-- The unique extension of an actual compatible cofinal tail. -/
def normLimitOfTail (D : FiniteLayer K L)
    (x : ∀ E : FiniteLayer K L, D ≤ E → E.val)
    (hx : ∀ (E F : FiniteLayer K L) (hDE : D ≤ E) (hDF : D ≤ F) (hEF : E ≤ F),
      FiniteLayer.norm E F hEF (x F hDF) = x E hDE) : NormLimit K L :=
  (existsUnique_normLimit_of_compatible_tail K L D x hx).choose

/-- The extension retains every specified original tail coordinate. -/
@[simp]
theorem normLimitEval_normLimitOfTail (D : FiniteLayer K L)
    (x : ∀ E : FiniteLayer K L, D ≤ E → E.val)
    (hx : ∀ (E F : FiniteLayer K L) (hDE : D ≤ E) (hDF : D ≤ F) (hEF : E ≤ F),
      FiniteLayer.norm E F hEF (x F hDF) = x E hDE)
    (E : FiniteLayer K L) (hDE : D ≤ E) :
    normLimitEval K L E (normLimitOfTail K L D x hx) = x E hDE :=
  (existsUnique_normLimit_of_compatible_tail K L D x hx).choose_spec.1 E hDE

/-- At any original finite layer, the extension is an actual finite norm
from the finite compositum with the specified starting field. -/
theorem normLimitEval_normLimitOfTail_any (D : FiniteLayer K L)
    (x : ∀ E : FiniteLayer K L, D ≤ E → E.val)
    (hx : ∀ (E F : FiniteLayer K L) (hDE : D ≤ E) (hDF : D ≤ F) (hEF : E ≤ F),
      FiniteLayer.norm E F hEF (x F hDF) = x E hDE) (E : FiniteLayer K L) :
    normLimitEval K L E (normLimitOfTail K L D x hx) =
      FiniteLayer.norm E (FiniteLayer.sup E D) (FiniteLayer.le_sup_left E D)
        (x (FiniteLayer.sup E D) (FiniteLayer.le_sup_right E D)) := by
  rw [← normLimitEval_norm K L E (FiniteLayer.sup E D) (FiniteLayer.le_sup_left E D),
    normLimitEval_normLimitOfTail]

end CofinalTail

section SourceConstants

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]
variable (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField
  (NormedField.valuation (K := K)).valuationSubring) p]
variable (hL : IsAPF K L)

local notation "K₀" => apfMaximalUnramified K L hL
local notation "K₁" => apfMaximalTame K L hL
local notation "κL" => IsLocalRing.ResidueField
  (integralClosure (Valuation.valuationSubring (NormedField.valuation (K := K))) L)

/-- The exponent of the actual finite degree over the actual maximal tame
part, supplied by the proved original-field wild-tail theorem. -/
def sourceResidueDegree (E : FiniteLayer K L) (hE : K₁ ≤ E) : ℕ :=
  (finrank_eq_prime_pow_of_apfMaximalTame_le K L p hL K₁ E le_rfl hE).choose

/-- The chosen exponent computes the genuine original relative field degree. -/
theorem sourceResidueDegree_spec (E : FiniteLayer K L) (hE : K₁ ≤ E) :
    Module.finrank (K₁).val (IntermediateField.extendScalars hE) =
      p ^ sourceResidueDegree K L p hL E hE :=
  (finrank_eq_prime_pow_of_apfMaximalTame_le K L p hL K₁ E le_rfl hE).choose_spec

/-- The actual source-normalized residue root, transported from the
intrinsic residue field to the actual maximal unramified field. -/
def sourceResidueRoot (E : FiniteLayer K L) (hE : K₁ ≤ E) : κL ≃+* (IsLocalRing.ResidueField
    (spectralIntegerRing K (K₀).val)) :=
  (apfMaximalUnramifiedResidueEquiv K L hL).symm.toRingEquiv.trans
    (iterateFrobeniusEquiv (IsLocalRing.ResidueField (spectralIntegerRing K (K₀).val)) p
        (sourceResidueDegree K L p hL E hE)).symm

/-- Transported back to the intrinsic original residue field, the actual
source root has precisely the prescribed p-power degree as its exponent. -/
theorem sourceResidueRoot_pow (E : FiniteLayer K L) (hE : K₁ ≤ E) (x : κL) :
    apfMaximalUnramifiedResidueEquiv K L hL (sourceResidueRoot K L p hL E hE x) ^
      p ^ sourceResidueDegree K L p hL E hE = x := by
  rw [← map_pow]
  exact (congrArg (apfMaximalUnramifiedResidueEquiv K L hL)
    ((iterateFrobeniusEquiv _ p (sourceResidueDegree K L p hL E hE)).apply_symm_apply
      ((apfMaximalUnramifiedResidueEquiv K L hL).symm x))).trans
        ((apfMaximalUnramifiedResidueEquiv K L hL).apply_symm_apply x)

/-- The source coordinate is already in the actual finite integer ring,
by the original inclusion from the actual maximal unramified part. -/
def sourceResidueIntegralCoordinate (E : FiniteLayer K L) (hE : K₁ ≤ E) :
    κL →*₀ spectralIntegerRing K E.val :=
  (spectralIntegerInclusion K (IntermediateField.inclusion
    ((apfMaximalUnramified_le_maximalTame K L hL).trans hE))).toMonoidWithZeroHom.comp
      ((spectralTeichmuller K (K₀).val p).comp
        (sourceResidueRoot K L p hL E hE).toMonoidWithZeroHom)

/-- Reduction of the actual integral coordinate is the actual finite
residue inclusion applied to the prescribed inverse Frobenius root. -/
@[simp]
theorem residue_sourceResidueIntegralCoordinate (E : FiniteLayer K L) (hE : K₁ ≤ E) (x : κL) :
    IsLocalRing.residue _ (sourceResidueIntegralCoordinate K L p hL E hE x) =
      spectralResidueInclusion K (IntermediateField.inclusion
        ((apfMaximalUnramified_le_maximalTame K L hL).trans hE))
        (sourceResidueRoot K L p hL E hE x) := by
  change IsLocalRing.residue _ (spectralIntegerInclusion K _
    (spectralTeichmuller K (K₀).val p (sourceResidueRoot K L p hL E hE x))) = _
  rw [← spectralResidueInclusion_residue, residue_spectralTeichmuller]

/-- The actual coordinate reduction has the source's inverse-Frobenius
degree normalization. It is an isomorphism, with the actual original
residue inclusion as its second factor. -/
def sourceResidueCoordinateEquiv (E : FiniteLayer K L) (hE : K₁ ≤ E) :
    κL ≃+* IsLocalRing.ResidueField (spectralIntegerRing K E.val) :=
  (sourceResidueRoot K L p hL E hE).trans
    (AlgEquiv.ofBijective
      (spectralResidueInclusion K (IntermediateField.inclusion
        ((apfMaximalUnramified_le_maximalTame K L hL).trans hE)))
      ⟨(spectralResidueInclusion K _).injective,
        spectralResidueInclusion_surjective_of_apfMaximalUnramified_le K L hL
          K₀ E le_rfl ((apfMaximalUnramified_le_maximalTame K L hL).trans hE)⟩).toRingEquiv

/-- The normalization is exactly reduction of the actual original integral
source coordinate, including the finite-stage inverse Frobenius twist. -/
@[simp]
theorem sourceResidueCoordinateEquiv_apply (E : FiniteLayer K L) (hE : K₁ ≤ E) (x : κL) :
    sourceResidueCoordinateEquiv K L p hL E hE x =
      IsLocalRing.residue _ (sourceResidueIntegralCoordinate K L p hL E hE x) :=
  (residue_sourceResidueIntegralCoordinate K L p hL E hE x).symm

/-- The original finite inclusion preserves the actual canonical section,
so the source integral coordinate is the finite field's own Teichmüller lift. -/
theorem sourceResidueIntegralCoordinate_eq_spectralTeichmuller
    (E : FiniteLayer K L) (hE : K₁ ≤ E) (x : κL) :
    sourceResidueIntegralCoordinate K L p hL E hE x =
      spectralTeichmuller K E.val p (sourceResidueCoordinateEquiv K L p hL E hE x) :=
  spectralTeichmuller_naturality K (K₀).val p
    (IntermediateField.inclusion ((apfMaximalUnramified_le_maximalTame K L hL).trans hE))
    (sourceResidueRoot K L p hL E hE x)

/-- The original finite coordinate prescribed by the source: the inverse
Frobenius degree root's canonical representative already lies in K₀. -/
def sourceResidueCoordinate (E : FiniteLayer K L) (hE : K₁ ≤ E) : κL →*₀ E.val :=
  (spectralIntegerRing K E.val).subtype.toMonoidWithZeroHom.comp
    (sourceResidueIntegralCoordinate K L p hL E hE)

/-- The actual source degree exponents add in each original finite tower
above K₁; the step exponent is supplied by the proved wild-tail theorem. -/
theorem sourceResidueDegree_step (E F : FiniteLayer K L) (hE : K₁ ≤ E) (hEF : E ≤ F) :
    ∃ d : ℕ, Module.finrank E.val (IntermediateField.extendScalars hEF) = p ^ d ∧
      sourceResidueDegree K L p hL F (hE.trans hEF) =
        d + sourceResidueDegree K L p hL E hE := by
  obtain ⟨d, hd⟩ := finrank_eq_prime_pow_of_apfMaximalTame_le K L p hL E F hE hEF
  refine ⟨d, hd, ?_⟩
  have ht := IntermediateField.relfinrank_mul_relfinrank hE hEF
  rw [IntermediateField.relfinrank_eq_finrank_of_le hE,
    IntermediateField.relfinrank_eq_finrank_of_le hEF,
    IntermediateField.relfinrank_eq_finrank_of_le (hE.trans hEF),
    sourceResidueDegree_spec, sourceResidueDegree_spec, hd] at ht
  apply Nat.pow_right_injective (Fact.out : p.Prime).two_le
  change p ^ sourceResidueDegree K L p hL F (hE.trans hEF) =
    p ^ (d + sourceResidueDegree K L p hL E hE)
  rw [pow_add, Nat.mul_comm]
  exact ht.symm

/-- The actual source coordinates satisfy the genuine original relative
norm equations; all degree hypotheses come from the actual maximal tame part. -/
theorem sourceResidueCoordinate_norm (E F : FiniteLayer K L)
    (hE : K₁ ≤ E) (hF : K₁ ≤ F) (hEF : E ≤ F) (x : κL) :
    FiniteLayer.norm E F hEF (sourceResidueCoordinate K L p hL F hF x) =
      sourceResidueCoordinate K L p hL E hE x := by
  obtain ⟨d, hd, hadd⟩ := sourceResidueDegree_step K L p hL E F hE hEF
  have hr : sourceResidueRoot K L p hL F hF x ^ p ^ d =
      sourceResidueRoot K L p hL E hE x := by
    change (iterateFrobeniusEquiv _ p (sourceResidueDegree K L p hL F hF)).symm
      ((apfMaximalUnramifiedResidueEquiv K L hL).symm x) ^ p ^ d = _
    rw [hadd, iterateFrobeniusEquiv_symm_add_apply]
    exact (iterateFrobeniusEquiv _ p d).apply_symm_apply _
  have ht : spectralTeichmuller K (K₀).val p (sourceResidueRoot K L p hL F hF x) ^ p ^ d =
      spectralTeichmuller K (K₀).val p (sourceResidueRoot K L p hL E hE x) := by
    rw [← map_pow, hr]
  change FiniteLayer.norm E F hEF (IntermediateField.inclusion hEF
    (IntermediateField.inclusion ((apfMaximalUnramified_le_maximalTame K L hL).trans hE)
      (spectralTeichmuller K (K₀).val p (sourceResidueRoot K L p hL F hF x) : (K₀).val))) = _
  rw [FiniteLayer.norm_inclusion, hd, ← map_pow]
  apply congrArg (IntermediateField.inclusion
    ((apfMaximalUnramified_le_maximalTame K L hL).trans hE))
  exact congrArg (fun z : spectralIntegerRing K (K₀).val => (z : (K₀).val)) ht

/-- The actual source-normalized multiplicative constants on the same
original norm-limit carrier, extending the proved compatible finite tail. -/
def sourceResidueConstants : κL →*₀ NormLimit K L := by
  let f (x : κL) := normLimitOfTail K L K₁
    (fun E hE => sourceResidueCoordinate K L p hL E hE x)
    (fun E F hE hF hEF => sourceResidueCoordinate_norm K L p hL E F hE hF hEF x)
  have he (E : FiniteLayer K L) (hE : K₁ ≤ E) (x : κL) :
      normLimitEval K L E (f x) = sourceResidueCoordinate K L p hL E hE x :=
    normLimitEval_normLimitOfTail K L K₁
      (fun E hE => sourceResidueCoordinate K L p hL E hE x)
      (fun E F hE hF hEF => sourceResidueCoordinate_norm K L p hL E F hE hF hEF x) E hE
  exact {
    toFun := f
    map_zero' := by
      apply NormLimit.ext_tail K L K₁
      intro E hE
      rw [he E hE, map_zero, map_zero]
    map_one' := by
      apply NormLimit.ext_tail K L K₁
      intro E hE
      rw [he E hE, map_one, map_one]
    map_mul' := fun x y => by
      apply NormLimit.ext_tail K L K₁
      intro E hE
      rw [map_mul, he E hE, he E hE, he E hE, map_mul] }

/-- Every tail coordinate of the actual source constants is exactly its
prescribed inverse-Frobenius Teichmüller representative. -/
@[simp]
theorem normLimitEval_sourceResidueConstants (E : FiniteLayer K L) (hE : K₁ ≤ E) (x : κL) :
    normLimitEval K L E (sourceResidueConstants K L p hL x) =
      sourceResidueCoordinate K L p hL E hE x :=
  normLimitEval_normLimitOfTail K L K₁
    (fun E hE => sourceResidueCoordinate K L p hL E hE x)
    (fun E F hE hF hEF => sourceResidueCoordinate_norm K L p hL E F hE hF hEF x) E hE

/-- At every original finite field, including those incomparable with K₁,
the source constant is the actual norm from the finite compositum. -/
theorem normLimitEval_sourceResidueConstants_any (E : FiniteLayer K L) (x : κL) :
    normLimitEval K L E (sourceResidueConstants K L p hL x) =
      FiniteLayer.norm E (FiniteLayer.sup E K₁) (FiniteLayer.le_sup_left E K₁)
        (sourceResidueCoordinate K L p hL (FiniteLayer.sup E K₁)
          (FiniteLayer.le_sup_right E K₁) x) :=
  normLimitEval_normLimitOfTail_any K L K₁
    (fun E hE => sourceResidueCoordinate K L p hL E hE x)
    (fun E F hE hF hEF => sourceResidueCoordinate_norm K L p hL E F hE hF hEF x) E

/-- The actual source constants are injective already as a multiplicative
map, by an original finite coordinate and its genuine residue section. -/
theorem sourceResidueConstants_injective :
    Function.Injective (sourceResidueConstants K L p hL) := by
  intro x y hxy
  have hc := congrArg (normLimitEval K L K₁) hxy
  rw [normLimitEval_sourceResidueConstants K L p hL K₁ le_rfl,
    normLimitEval_sourceResidueConstants K L p hL K₁ le_rfl] at hc
  have hi : sourceResidueIntegralCoordinate K L p hL K₁ le_rfl x =
      sourceResidueIntegralCoordinate K L p hL K₁ le_rfl y := Subtype.ext hc
  have hr := congrArg (IsLocalRing.residue (spectralIntegerRing K (K₁).val)) hi
  rw [residue_sourceResidueIntegralCoordinate, residue_sourceResidueIntegralCoordinate] at hr
  exact (sourceResidueRoot K L p hL K₁ le_rfl).injective
    ((spectralResidueInclusion K (IntermediateField.inclusion
      (apfMaximalUnramified_le_maximalTame K L hL))).injective hr)

/-- The source constants are integral for the same original stable valuation. -/
theorem sourceResidueConstants_valuation_le_one (x : κL) :
    normLimitValuation K L hL (sourceResidueConstants K L p hL x) ≤ 1 := by
  obtain ⟨T, hT⟩ := IsAPF.exists_normLimitValuation_eq_coordinate K L hL
  let E := FiniteLayer.sup T K₁
  have hE : K₁ ≤ E := FiniteLayer.le_sup_right T K₁
  rw [hT E (FiniteLayer.le_sup_left T K₁)]
  change (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K E.val)).valuation E.val
    (normLimitEval K L E (sourceResidueConstants K L p hL x)) ≤ 1
  rw [normLimitEval_sourceResidueConstants K L p hL E hE]
  exact (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K E.val)).valuation_le_one
    (sourceResidueIntegralCoordinate K L p hL E hE x)

variable (hInfinite : ¬ Module.Finite K L)

local notation "𝔈" => deepFiniteTower K L p hL hInfinite K₁
local notation "𝔅" => deepFiniteTowerQuotient K L p hL hInfinite K₁

/-- The actual quotient projection identifies the original finite residue
field with the residue field of the actual deep truncated ring. -/
def sourceDeepResidueEquiv (n : ℕ) :
    IsLocalRing.ResidueField (spectralIntegerRing K (𝔈 n).val) ≃+*
      IsLocalRing.ResidueField (𝔅 n) := by
  let q : spectralIntegerRing K (𝔈 n).val →+* 𝔅 n := Ideal.Quotient.mk _
  let : IsLocalHom q := Ideal.Quotient.mk_surjective.isLocalHom
  let f := IsLocalRing.ResidueField.map q
  refine RingEquiv.ofBijective f ⟨f.injective, ?_⟩
  intro y
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact ⟨IsLocalRing.residue _ x, rfl⟩

/-- The quotient-residue equivalence is induced by the actual quotient map. -/
@[simp]
theorem sourceDeepResidueEquiv_residue (n : ℕ) (x : spectralIntegerRing K (𝔈 n).val) :
    sourceDeepResidueEquiv K L p hL hInfinite n (IsLocalRing.residue _ x) =
      IsLocalRing.residue (𝔅 n) (Ideal.Quotient.mk _ x) := rfl

/-- The actual deep truncated residue field is perfect, by the actual
finite residue inclusion, without any finiteness-of-cardinality assumption. -/
instance sourceDeepResidue_perfectField (n : ℕ) :
    PerfectField (IsLocalRing.ResidueField (𝔅 n)) :=
  PerfectField.of_ringEquiv (sourceDeepResidueEquiv K L p hL hInfinite n)

/-- The actual deep residue field has the original residue characteristic. -/
instance sourceDeepResidue_charP (n : ℕ) :
    CharP (IsLocalRing.ResidueField (𝔅 n)) p :=
  charP_of_injective_ringHom (sourceDeepResidueEquiv K L p hL hInfinite n).injective p

/-- The actual source constants, restricted to the original norm-limit
valuation ring using their proved integrality. -/
def sourceResidueConstantsInteger :
    letI := normLimitField K L p hL hInfinite
    κL →*₀ (normLimitFieldValuation K L p hL hInfinite).valuationSubring := by
  letI := normLimitField K L p hL hInfinite
  exact {
    toFun := fun x => ⟨sourceResidueConstants K L p hL x,
      sourceResidueConstants_valuation_le_one K L p hL x⟩
    map_zero' := Subtype.ext (map_zero (sourceResidueConstants K L p hL))
    map_one' := Subtype.ext (map_one (sourceResidueConstants K L p hL))
    map_mul' := fun x y => Subtype.ext (map_mul (sourceResidueConstants K L p hL) x y) }

/-- The original integral deep coordinate of a source constant is its
actual finite integral source representative. -/
theorem normLimitIntegralCoordinate_sourceResidueConstantsInteger (n : ℕ) (x : κL) :
    letI := normLimitField K L p hL hInfinite
    normLimitIntegralCoordinate K L p hL hInfinite K₁
      (sourceResidueConstantsInteger K L p hL hInfinite x) n =
      sourceResidueIntegralCoordinate K L p hL (deepFiniteTower K L p hL hInfinite K₁ n)
        (le_deepFiniteTower K L p hL hInfinite K₁ n) x := by
  let := normLimitField K L p hL hInfinite
  apply Subtype.ext
  exact normLimitEval_sourceResidueConstants K L p hL _
    (le_deepFiniteTower K L p hL hInfinite K₁ n) x

/-- The maximal ideal of each actual truncated coordinate ring is nilpotent. -/
theorem sourceDeep_maximalIdeal_isNilpotent (n : ℕ) :
    IsNilpotent (IsLocalRing.maximalIdeal (𝔅 n)) :=
  ⟨n + 2, deepFiniteTowerQuotient_maximalIdeal_pow K L p hL hInfinite K₁ n⟩

/-- The actual truncated source coordinate is a unital ring map: inverse
Frobenius and original residue inclusions feed the canonical coefficient section. -/
def sourceResidueTruncatedHom (n : ℕ) : κL →+* 𝔅 n :=
  (truncatedResidueCoefficients (𝔅 n) p
    (sourceDeep_maximalIdeal_isNilpotent K L p hL hInfinite n)).comp
      ((sourceDeepResidueEquiv K L p hL hInfinite n).toRingHom.comp
        (sourceResidueCoordinateEquiv K L p hL (𝔈 n)
          (le_deepFiniteTower K L p hL hInfinite K₁ n)).toRingHom)

/-- The ring-valued truncated coordinate is exactly the truncation of the
actual original source constant. This uses the existing Teichmüller section's
actual naturality under the original quotient projection. -/
theorem normLimitTruncation_sourceResidueConstantsInteger (n : ℕ) (x : κL) :
    letI := normLimitField K L p hL hInfinite
    normLimitTruncation K L p hL hInfinite K₁ n
      (sourceResidueConstantsInteger K L p hL hInfinite x) =
      sourceResidueTruncatedHom K L p hL hInfinite n x := by
  let := normLimitField K L p hL hInfinite
  let q : spectralIntegerRing K (𝔈 n).val →+* 𝔅 n := Ideal.Quotient.mk _
  let : IsLocalHom q := Ideal.Quotient.mk_surjective.isLocalHom
  let := isAdicComplete_of_isNilpotent_ideal (IsLocalRing.maximalIdeal (𝔅 n))
    (sourceDeep_maximalIdeal_isNilpotent K L p hL hInfinite n)
  rw [normLimitTruncation_apply, normLimitIntegralCoordinate_sourceResidueConstantsInteger,
    sourceResidueIntegralCoordinate_eq_spectralTeichmuller]
  change q (residueTeichmuller (spectralIntegerRing K (𝔈 n).val) p
      (sourceResidueCoordinateEquiv K L p hL (𝔈 n)
        (le_deepFiniteTower K L p hL hInfinite K₁ n) x)) =
    residueTeichmuller (𝔅 n) p (IsLocalRing.ResidueField.map q
      (sourceResidueCoordinateEquiv K L p hL (𝔈 n)
        (le_deepFiniteTower K L p hL hInfinite K₁ n) x))
  exact residueTeichmuller_naturality (spectralIntegerRing K (𝔈 n).val) p (𝔅 n) q _

/-- The actual integral source constants are additive: their actual deep
truncations are additive ring maps, and the actual truncation equivalence is injective. -/
theorem sourceResidueConstantsInteger_add (x y : κL) :
    letI := normLimitField K L p hL hInfinite
    sourceResidueConstantsInteger K L p hL hInfinite (x + y) =
      sourceResidueConstantsInteger K L p hL hInfinite x +
        sourceResidueConstantsInteger K L p hL hInfinite y := by
  let := normLimitField K L p hL hInfinite
  apply (normLimitTruncationEquiv K L p hL hInfinite K₁).injective
  apply Subtype.ext
  funext n
  change normLimitTruncation K L p hL hInfinite K₁ n
    (sourceResidueConstantsInteger K L p hL hInfinite (x + y)) =
    normLimitTruncation K L p hL hInfinite K₁ n
      (sourceResidueConstantsInteger K L p hL hInfinite x +
        sourceResidueConstantsInteger K L p hL hInfinite y)
  rw [map_add (normLimitTruncation K L p hL hInfinite K₁ n),
    normLimitTruncation_sourceResidueConstantsInteger,
    normLimitTruncation_sourceResidueConstantsInteger,
    normLimitTruncation_sourceResidueConstantsInteger]
  exact map_add (sourceResidueTruncatedHom K L p hL hInfinite n) x y

/-- The actual integral source constants as a unital ring map. -/
def sourceResidueConstantsIntegerHom :
    letI := normLimitField K L p hL hInfinite
    κL →+* (normLimitFieldValuation K L p hL hInfinite).valuationSubring := by
  letI := normLimitField K L p hL hInfinite
  exact { sourceResidueConstantsInteger K L p hL hInfinite with
    map_add' := sourceResidueConstantsInteger_add K L p hL hInfinite }

/-- The source-normalized coefficient field embedding into the same original
field of norms, with the original addition and multiplication. -/
def sourceResidueConstantsFieldEmbedding :
    letI := normLimitField K L p hL hInfinite
    κL →+* NormLimit K L := by
  letI := normLimitField K L p hL hInfinite
  exact (normLimitFieldValuation K L p hL hInfinite).valuationSubring.subtype.comp
    (sourceResidueConstantsIntegerHom K L p hL hInfinite)

/-- The field embedding's underlying function is exactly the original
source-normalized norm-compatible family already constructed. -/
@[simp]
theorem sourceResidueConstantsFieldEmbedding_apply (x : κL) :
    letI := normLimitField K L p hL hInfinite
    sourceResidueConstantsFieldEmbedding K L p hL hInfinite x =
      sourceResidueConstants K L p hL x := rfl

/-- The actual source coefficient map is an injective field homomorphism. -/
theorem sourceResidueConstantsFieldEmbedding_injective :
    letI := normLimitField K L p hL hInfinite
    Function.Injective (sourceResidueConstantsFieldEmbedding K L p hL hInfinite) :=
  sourceResidueConstants_injective K L p hL

/-- Under the actual original residue-field identification, the reduction
of a source constant is precisely the inverse-Frobenius-normalized coordinate. -/
theorem normLimitResidueLayerEquiv_sourceResidueConstantsInteger (x : κL) :
    letI := normLimitField K L p hL hInfinite
    normLimitResidueLayerEquiv K L p hL hInfinite K₁
      (IsLocalRing.residue _ (sourceResidueConstantsInteger K L p hL hInfinite x)) =
      sourceResidueCoordinateEquiv K L p hL (deepFiniteTower K L p hL hInfinite K₁ 0)
        (le_deepFiniteTower K L p hL hInfinite K₁ 0) x := by
  let := normLimitField K L p hL hInfinite
  rw [normLimitResidueLayerEquiv_residue,
    normLimitIntegralCoordinate_sourceResidueConstantsInteger,
    sourceResidueCoordinateEquiv_apply]

/-- The actual source constants identify the intrinsic original residue
field with the entire original norm-limit residue field, retaining the
finite starting-stage Frobenius normalization. -/
def sourceResidueConstantsResidueEquiv :
    letI := normLimitField K L p hL hInfinite
    κL ≃+* IsLocalRing.ResidueField
      (normLimitFieldValuation K L p hL hInfinite).valuationSubring := by
  letI := normLimitField K L p hL hInfinite
  exact (sourceResidueCoordinateEquiv K L p hL (deepFiniteTower K L p hL hInfinite K₁ 0)
    (le_deepFiniteTower K L p hL hInfinite K₁ 0)).trans
      (normLimitResidueLayerEquiv K L p hL hInfinite K₁).symm

/-- This residue isomorphism is induced by the actual original source
constants, rather than by a new coefficient model. -/
@[simp]
theorem sourceResidueConstantsResidueEquiv_apply (x : κL) :
    letI := normLimitField K L p hL hInfinite
    sourceResidueConstantsResidueEquiv K L p hL hInfinite x =
      IsLocalRing.residue _ (sourceResidueConstantsInteger K L p hL hInfinite x) := by
  let := normLimitField K L p hL hInfinite
  apply (normLimitResidueLayerEquiv K L p hL hInfinite K₁).injective
  exact (normLimitResidueLayerEquiv K L p hL hInfinite K₁).apply_symm_apply _ |>.trans
    (normLimitResidueLayerEquiv_sourceResidueConstantsInteger K L p hL hInfinite x).symm

end SourceConstants

end FontaineWintenberger
