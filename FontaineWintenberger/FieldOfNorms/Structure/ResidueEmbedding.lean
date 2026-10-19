/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Structure.Residue
public import FontaineWintenberger.Ramification.Lower.Teichmuller
public import FontaineWintenberger.APF.Tower.Tame
public import FontaineWintenberger.Ramification.Lower.TruncatedCoefficients

/-!
# Source-normalized residue constants in the field of norms

Compatible tail coordinates extend through finite composita and field
norms to the zero-adjoined multiplicative field of norms carrier.

## Main definitions

* `FieldOfNorms.ofTail`: The unique extension of a compatible cofinal tail.
* `residueDegree`: The exponent of the finite degree over the maximal tame part, supplied by the
  proved original-field wild-tail theorem.
* `residueRoot`: The source-normalized residue root, transported from the intrinsic residue field to
  the maximal unramified field.
* `residueIntegralCoordinate`: The coordinate is already in the finite integer ring, by the
  inclusion from the maximal unramified part.
* `residueCoordinateEquiv`: The coordinate reduction has the source's inverse-Frobenius degree
  normalization.
* `residueCoordinate`: The finite coordinate prescribed by the source: the inverse Frobenius degree
  root's canonical representative already lies in K₀.
* `residueConstants`: The source-normalized multiplicative constants on the same field of norms
  carrier, extending the proved compatible finite tail.
* `deepResidueEquiv`: The quotient projection identifies the finite residue field with the residue
  field of the deep truncated ring.

## Main results

* `FiniteIntermediateField.norm_inclusion`: The norm of an element from the smaller finite field is
  its power by the relative field degree.
* `FieldOfNorms.ext_tail`: Evaluations on the cofinal tail above any finite intermediate field
  already distinguish elements of the field of norms carrier.
* `existsUnique_fieldOfNorms_of_compatible_tail`: A compatible family on a cofinal finite-layer tail
  extends uniquely to an element of the multiplicative field of norms.
* `FieldOfNorms.coord_ofTail`: The extension retains every specified tail coordinate.
* `FieldOfNorms.coord_ofTail_of_le`: At any finite intermediate field, the extension is a finite
  norm from the finite compositum with the specified starting field.
* `residueDegree_spec`: The chosen exponent computes the relative field degree.
* `residueRoot_pow`: Transported back to the intrinsic residue field, the source root has precisely
  the prescribed p-power degree as its exponent.
* `residue_residueIntegralCoordinate`: Reduction of the integral coordinate is the finite residue
  inclusion applied to the prescribed inverse Frobenius root.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §2–3 (le corps des normes, fonctorialité).
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

section CofinalTail

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- The norm of an element from the smaller finite field
is its power by the relative field degree. -/
theorem FiniteIntermediateField.norm_inclusion (E F : FiniteIntermediateField K L) (hEF : E ≤ F) (x
    : E.val) :
    FiniteIntermediateField.norm E F hEF (IntermediateField.inclusion hEF x) =
      x ^ Module.finrank E.val (IntermediateField.extendScalars hEF) := by
  let F' := IntermediateField.extendScalars hEF
  have : FiniteDimensional K F' := F.property
  have : FiniteDimensional E.val F' := Module.Finite.right K E.val F'
  let : Module.Free E.val F' := Module.Free.of_divisionRing E.val F'
  change Algebra.norm E.val (algebraMap E.val F' x) = _
  exact Algebra.norm_algebraMap x

/-- Evaluations on the cofinal tail above any finite intermediate field already
distinguish elements of the field of norms carrier. -/
theorem FieldOfNorms.ext_tail (D : FiniteIntermediateField K L) {α β : FieldOfNorms K L}
    (h : ∀ E : FiniteIntermediateField K L, D ≤ E → FieldOfNorms.coord K L E α = FieldOfNorms.coord
        K L E β) :
    α = β := by
  apply FieldOfNorms.ext K L
  intro E
  rw [← FieldOfNorms.coord_norm K L E (FiniteIntermediateField.sup E D)
      (FiniteIntermediateField.le_sup_left E D) α,
    ← FieldOfNorms.coord_norm K L E (FiniteIntermediateField.sup E D)
        (FiniteIntermediateField.le_sup_left E D) β,
    h (FiniteIntermediateField.sup E D) (FiniteIntermediateField.le_sup_right E D)]

/-- A compatible family on a cofinal finite-layer tail extends
uniquely to an element of the multiplicative field of norms. -/
theorem existsUnique_fieldOfNorms_of_compatible_tail (D : FiniteIntermediateField K L)
    (x : ∀ E : FiniteIntermediateField K L, D ≤ E → E.val)
    (hx : ∀ (E F : FiniteIntermediateField K L) (hDE : D ≤ E) (hDF : D ≤ F) (hEF : E ≤ F),
      FiniteIntermediateField.norm E F hEF (x F hDF) = x E hDE) :
    ∃! α : FieldOfNorms K L, ∀ (E : FiniteIntermediateField K L) (hDE : D ≤ E),
      FieldOfNorms.coord K L E α = x E hDE := by
  let f (E : FiniteIntermediateField K L) := FiniteIntermediateField.norm E
      (FiniteIntermediateField.sup E D)
    (FiniteIntermediateField.le_sup_left E D) (x (FiniteIntermediateField.sup E D)
        (FiniteIntermediateField.le_sup_right E D))
  have hf (E F : FiniteIntermediateField K L) (hEF : E ≤ F) : FiniteIntermediateField.norm E F hEF
      (f F) = f E := by
    have hs : FiniteIntermediateField.sup E D ≤ FiniteIntermediateField.sup F D :=
      (show E.val ⊔ D.val ≤ F.val ⊔ D.val from sup_le_sup hEF le_rfl)
    dsimp only [f]
    rw [FiniteIntermediateField.norm_norm, ← FiniteIntermediateField.norm_norm E
        (FiniteIntermediateField.sup E D)
      (FiniteIntermediateField.sup F D) (FiniteIntermediateField.le_sup_left E D) hs]
    rw [hx (FiniteIntermediateField.sup E D) (FiniteIntermediateField.sup F D)
      (FiniteIntermediateField.le_sup_right E D) (FiniteIntermediateField.le_sup_right F D) hs]
  obtain ⟨α, hα, _⟩ := existsUnique_fieldOfNorms_of_compatible K L f hf
  refine ⟨α, ?_, ?_⟩
  · intro E hDE
    exact (hα E).trans (hx E (FiniteIntermediateField.sup E D) hDE
        (FiniteIntermediateField.le_sup_right E D)
      (FiniteIntermediateField.le_sup_left E D))
  · intro β hβ
    apply FieldOfNorms.ext_tail K L D
    intro E hDE
    exact (hβ E hDE).trans ((hα E).trans
      (hx E (FiniteIntermediateField.sup E D) hDE (FiniteIntermediateField.le_sup_right E D)
        (FiniteIntermediateField.le_sup_left E D))).symm

/-- The unique extension of a compatible cofinal tail. -/
def FieldOfNorms.ofTail (D : FiniteIntermediateField K L)
    (x : ∀ E : FiniteIntermediateField K L, D ≤ E → E.val)
    (hx : ∀ (E F : FiniteIntermediateField K L) (hDE : D ≤ E) (hDF : D ≤ F) (hEF : E ≤ F),
      FiniteIntermediateField.norm E F hEF (x F hDF) = x E hDE) : FieldOfNorms K L :=
  (existsUnique_fieldOfNorms_of_compatible_tail K L D x hx).choose

/-- The extension retains every specified tail coordinate. -/
@[simp]
theorem FieldOfNorms.coord_ofTail (D : FiniteIntermediateField K L)
    (x : ∀ E : FiniteIntermediateField K L, D ≤ E → E.val)
    (hx : ∀ (E F : FiniteIntermediateField K L) (hDE : D ≤ E) (hDF : D ≤ F) (hEF : E ≤ F),
      FiniteIntermediateField.norm E F hEF (x F hDF) = x E hDE)
    (E : FiniteIntermediateField K L) (hDE : D ≤ E) :
    FieldOfNorms.coord K L E (FieldOfNorms.ofTail K L D x hx) = x E hDE :=
  (existsUnique_fieldOfNorms_of_compatible_tail K L D x hx).choose_spec.1 E hDE

/-- At any finite intermediate field, the extension is a finite norm
from the finite compositum with the specified starting field. -/
theorem FieldOfNorms.coord_ofTail_of_le (D : FiniteIntermediateField K L)
    (x : ∀ E : FiniteIntermediateField K L, D ≤ E → E.val)
    (hx : ∀ (E F : FiniteIntermediateField K L) (hDE : D ≤ E) (hDF : D ≤ F) (hEF : E ≤ F),
      FiniteIntermediateField.norm E F hEF (x F hDF) = x E hDE) (E : FiniteIntermediateField K L) :
    FieldOfNorms.coord K L E (FieldOfNorms.ofTail K L D x hx) =
      FiniteIntermediateField.norm E (FiniteIntermediateField.sup E D)
          (FiniteIntermediateField.le_sup_left E D)
        (x (FiniteIntermediateField.sup E D) (FiniteIntermediateField.le_sup_right E D)) := by
  rw [← FieldOfNorms.coord_norm K L E (FiniteIntermediateField.sup E D)
      (FiniteIntermediateField.le_sup_left E D),
    FieldOfNorms.coord_ofTail]

end CofinalTail

section Constants

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]
variable [IsAPF K L]

local notation "K₀" => apfMaximalUnramified K L
local notation "K₁" => apfMaximalTame K L
local notation "κL" => IsLocalRing.ResidueField
  (integralClosure 𝒪[K] L)

/-- The exponent of the finite degree over the maximal tame
part, supplied by the proved original-field wild-tail theorem. -/
def residueDegree (E : FiniteIntermediateField K L) (hE : K₁ ≤ E) : ℕ :=
  (finrank_eq_prime_pow_of_apfMaximalTame_le K L K₁ E le_rfl hE).choose

/-- The chosen exponent computes the relative field degree. -/
theorem residueDegree_spec (E : FiniteIntermediateField K L) (hE : K₁ ≤ E) :
    Module.finrank (K₁).val (IntermediateField.extendScalars hE) =
      p ^ residueDegree K L E hE :=
  (finrank_eq_prime_pow_of_apfMaximalTame_le K L K₁ E le_rfl hE).choose_spec

/-- The source-normalized residue root, transported from the
intrinsic residue field to the maximal unramified field. -/
def residueRoot (E : FiniteIntermediateField K L) (hE : K₁ ≤ E) : κL ≃+*
    (IsLocalRing.ResidueField
    (spectralIntegerRing K (K₀).val)) :=
  (apfMaximalUnramifiedResidueEquiv K L).symm.toRingEquiv.trans
    (iterateFrobeniusEquiv (IsLocalRing.ResidueField (spectralIntegerRing K (K₀).val)) p
        (residueDegree K L E hE)).symm

/-- Transported back to the intrinsic residue field, the
source root has precisely the prescribed p-power degree as its exponent. -/
theorem residueRoot_pow (E : FiniteIntermediateField K L) (hE : K₁ ≤ E) (x : κL) :
    apfMaximalUnramifiedResidueEquiv K L (residueRoot K L E hE x) ^
      p ^ residueDegree K L E hE = x := by
  rw [← map_pow]
  exact (congrArg (apfMaximalUnramifiedResidueEquiv K L)
    ((iterateFrobeniusEquiv _ p (residueDegree K L E hE)).apply_symm_apply
      ((apfMaximalUnramifiedResidueEquiv K L).symm x))).trans
        ((apfMaximalUnramifiedResidueEquiv K L).apply_symm_apply x)

/-- The coordinate is already in the finite integer ring,
by the inclusion from the maximal unramified part. -/
def residueIntegralCoordinate (E : FiniteIntermediateField K L) (hE : K₁ ≤ E) :
    κL →*₀ spectralIntegerRing K E.val :=
  (spectralIntegerInclusion K (IntermediateField.inclusion
    ((apfMaximalUnramified_le_maximalTame K L).trans hE))).toMonoidWithZeroHom.comp
      ((spectralTeichmuller K (K₀).val).comp
        (residueRoot K L E hE).toMonoidWithZeroHom)

/-- Reduction of the integral coordinate is the finite
residue inclusion applied to the prescribed inverse Frobenius root. -/
@[simp]
theorem residue_residueIntegralCoordinate (E : FiniteIntermediateField K L) (hE : K₁ ≤ E) (x
    : κL) :
    IsLocalRing.residue _ (residueIntegralCoordinate K L E hE x) =
      spectralResidueInclusion K (IntermediateField.inclusion
        ((apfMaximalUnramified_le_maximalTame K L).trans hE))
        (residueRoot K L E hE x) := by
  change IsLocalRing.residue _ (spectralIntegerInclusion K _
    (spectralTeichmuller K (K₀).val (residueRoot K L E hE x))) = _
  rw [← spectralResidueInclusion_residue, residue_spectralTeichmuller]

/-- The coordinate reduction has the source's inverse-Frobenius
degree normalization. It is an isomorphism, with the
residue inclusion as its second factor. -/
def residueCoordinateEquiv (E : FiniteIntermediateField K L) (hE : K₁ ≤ E) :
    κL ≃+* IsLocalRing.ResidueField (spectralIntegerRing K E.val) :=
  (residueRoot K L E hE).trans
    (AlgEquiv.ofBijective
      (spectralResidueInclusion K (IntermediateField.inclusion
        ((apfMaximalUnramified_le_maximalTame K L).trans hE)))
      ⟨(spectralResidueInclusion K _).injective,
        spectralResidueInclusion_surjective_of_apfMaximalUnramified_le K L
          K₀ E le_rfl ((apfMaximalUnramified_le_maximalTame K L).trans hE)⟩).toRingEquiv

/-- The normalization is exactly reduction of the integral
coordinate, including the finite-stage inverse Frobenius twist. -/
@[simp]
theorem residueCoordinateEquiv_apply (E : FiniteIntermediateField K L) (hE : K₁ ≤ E) (x : κL)
    :
    residueCoordinateEquiv K L E hE x =
      IsLocalRing.residue _ (residueIntegralCoordinate K L E hE x) :=
  (residue_residueIntegralCoordinate K L E hE x).symm

/-- The finite inclusion preserves the canonical section,
so the integral coordinate is the finite field's own Teichmüller lift. -/
theorem residueIntegralCoordinate_eq_spectralTeichmuller
    (E : FiniteIntermediateField K L) (hE : K₁ ≤ E) (x : κL) :
    residueIntegralCoordinate K L E hE x =
      spectralTeichmuller K E.val (residueCoordinateEquiv K L E hE x) :=
  spectralTeichmuller_naturality K (K₀).val
    (IntermediateField.inclusion ((apfMaximalUnramified_le_maximalTame K L).trans hE))
    (residueRoot K L E hE x)

/-- The finite coordinate prescribed by the source: the inverse
Frobenius degree root's canonical representative already lies in K₀. -/
def residueCoordinate (E : FiniteIntermediateField K L) (hE : K₁ ≤ E) : κL →*₀ E.val :=
  (spectralIntegerRing K E.val).subtype.toMonoidWithZeroHom.comp
    (residueIntegralCoordinate K L E hE)

/-- The degree exponents add in each finite tower
above K₁; the step exponent is supplied by the proved wild-tail theorem. -/
theorem residueDegree_step (E F : FiniteIntermediateField K L) (hE : K₁ ≤ E) (hEF : E ≤ F) :
    ∃ d : ℕ, Module.finrank E.val (IntermediateField.extendScalars hEF) = p ^ d ∧
      residueDegree K L F (hE.trans hEF) =
        d + residueDegree K L E hE := by
  obtain ⟨d, hd⟩ := finrank_eq_prime_pow_of_apfMaximalTame_le K L E F hE hEF
  refine ⟨d, hd, ?_⟩
  have ht := IntermediateField.relfinrank_mul_relfinrank hE hEF
  rw [IntermediateField.relfinrank_eq_finrank_of_le hE,
    IntermediateField.relfinrank_eq_finrank_of_le hEF,
    IntermediateField.relfinrank_eq_finrank_of_le (hE.trans hEF),
    residueDegree_spec, residueDegree_spec, hd] at ht
  apply Nat.pow_right_injective (Fact.out : Nat.Prime p).two_le
  change p ^ residueDegree K L F (hE.trans hEF) =
    p ^ (d + residueDegree K L E hE)
  rw [pow_add, Nat.mul_comm]
  exact ht.symm

/-- The coordinates satisfy the relative
norm equations; all degree hypotheses come from the maximal tame part. -/
theorem residueCoordinate_norm (E F : FiniteIntermediateField K L)
    (hE : K₁ ≤ E) (hF : K₁ ≤ F) (hEF : E ≤ F) (x : κL) :
    FiniteIntermediateField.norm E F hEF (residueCoordinate K L F hF x) =
      residueCoordinate K L E hE x := by
  obtain ⟨d, hd, hadd⟩ := residueDegree_step K L E F hE hEF
  have hr : residueRoot K L F hF x ^ p ^ d =
      residueRoot K L E hE x := by
    change (iterateFrobeniusEquiv _ p (residueDegree K L F hF)).symm
      ((apfMaximalUnramifiedResidueEquiv K L).symm x) ^ p ^ d = _
    rw [hadd, iterateFrobeniusEquiv_symm_add_apply]
    exact (iterateFrobeniusEquiv _ p d).apply_symm_apply _
  have ht : spectralTeichmuller K (K₀).val (residueRoot K L F hF x) ^ p ^ d =
      spectralTeichmuller K (K₀).val (residueRoot K L E hE x) := by
    rw [← map_pow, hr]
  change FiniteIntermediateField.norm E F hEF (IntermediateField.inclusion hEF
    (IntermediateField.inclusion ((apfMaximalUnramified_le_maximalTame K L).trans hE)
      (spectralTeichmuller K (K₀).val (residueRoot K L F hF x) : (K₀).val))) = _
  rw [FiniteIntermediateField.norm_inclusion, hd, ← map_pow]
  apply congrArg (IntermediateField.inclusion
    ((apfMaximalUnramified_le_maximalTame K L).trans hE))
  exact congrArg (fun z : spectralIntegerRing K (K₀).val => (z : (K₀).val)) ht

/-- The source-normalized multiplicative constants on the same
field of norms carrier, extending the proved compatible finite tail. -/
def residueConstants : κL →*₀ FieldOfNorms K L := by
  let f (x : κL) := FieldOfNorms.ofTail K L K₁
    (fun E hE => residueCoordinate K L E hE x)
    (fun E F hE hF hEF => residueCoordinate_norm K L E F hE hF hEF x)
  have he (E : FiniteIntermediateField K L) (hE : K₁ ≤ E) (x : κL) :
      FieldOfNorms.coord K L E (f x) = residueCoordinate K L E hE x :=
    FieldOfNorms.coord_ofTail K L K₁
      (fun E hE => residueCoordinate K L E hE x)
      (fun E F hE hF hEF => residueCoordinate_norm K L E F hE hF hEF x) E hE
  exact {
    toFun := f
    map_zero' := by
      apply FieldOfNorms.ext_tail K L K₁
      intro E hE
      rw [he E hE, map_zero, map_zero]
    map_one' := by
      apply FieldOfNorms.ext_tail K L K₁
      intro E hE
      rw [he E hE, map_one, map_one]
    map_mul' := fun x y => by
      apply FieldOfNorms.ext_tail K L K₁
      intro E hE
      rw [map_mul, he E hE, he E hE, he E hE, map_mul] }

/-- Every tail coordinate of the constants is exactly its
prescribed inverse-Frobenius Teichmüller representative. -/
@[simp]
theorem FieldOfNorms.coord_residueConstants (E : FiniteIntermediateField K L) (hE : K₁ ≤ E)
    (x : κL) :
    FieldOfNorms.coord K L E (residueConstants K L x) =
      residueCoordinate K L E hE x :=
  FieldOfNorms.coord_ofTail K L K₁
    (fun E hE => residueCoordinate K L E hE x)
    (fun E F hE hF hEF => residueCoordinate_norm K L E F hE hF hEF x) E hE

/-- At every finite field, including those incomparable with K₁,
the constant is the norm from the finite compositum. -/
theorem FieldOfNorms.coord_residueConstants_any (E : FiniteIntermediateField K L) (x : κL) :
    FieldOfNorms.coord K L E (residueConstants K L x) =
      FiniteIntermediateField.norm E (FiniteIntermediateField.sup E K₁)
          (FiniteIntermediateField.le_sup_left E K₁)
        (residueCoordinate K L (FiniteIntermediateField.sup E K₁)
          (FiniteIntermediateField.le_sup_right E K₁) x) :=
  FieldOfNorms.coord_ofTail_of_le K L K₁
    (fun E hE => residueCoordinate K L E hE x)
    (fun E F hE hF hEF => residueCoordinate_norm K L E F hE hF hEF x) E

/-- The constants are injective already as a multiplicative
map, by a finite coordinate and its residue section. -/
theorem residueConstants_injective :
    Function.Injective (residueConstants K L) := by
  intro x y hxy
  have hc := congrArg (FieldOfNorms.coord K L K₁) hxy
  rw [FieldOfNorms.coord_residueConstants K L K₁ le_rfl,
    FieldOfNorms.coord_residueConstants K L K₁ le_rfl] at hc
  have hi : residueIntegralCoordinate K L K₁ le_rfl x =
      residueIntegralCoordinate K L K₁ le_rfl y := Subtype.ext hc
  have hr := congrArg (IsLocalRing.residue (spectralIntegerRing K (K₁).val)) hi
  rw [residue_residueIntegralCoordinate, residue_residueIntegralCoordinate] at hr
  exact (residueRoot K L K₁ le_rfl).injective
    ((spectralResidueInclusion K (IntermediateField.inclusion
      (apfMaximalUnramified_le_maximalTame K L))).injective hr)

/-- The constants are integral for the stable valuation. -/
theorem residueConstants_valuation_le_one (x : κL) :
    FieldOfNorms.valuation K L (residueConstants K L x) ≤ 1 := by
  obtain ⟨T, hT⟩ := FieldOfNorms.exists_valuation_eq_coordinateValuation K L
  let E := FiniteIntermediateField.sup T K₁
  have hE : K₁ ≤ E := FiniteIntermediateField.le_sup_right T K₁
  rw [hT E (FiniteIntermediateField.le_sup_left T K₁)]
  change (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K E.val)).valuation E.val
    (FieldOfNorms.coord K L E (residueConstants K L x)) ≤ 1
  rw [FieldOfNorms.coord_residueConstants K L E hE]
  exact (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K E.val)).valuation_le_one
    (residueIntegralCoordinate K L E hE x)

variable [Fact (¬ Module.Finite K L)]

local notation "𝔈" => deepFiniteTower K L K₁
local notation "𝔅" => deepFiniteTowerQuotient K L K₁

/-- The quotient projection identifies the finite residue
field with the residue field of the deep truncated ring. -/
def deepResidueEquiv (n : ℕ) :
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

/-- The quotient-residue equivalence is induced by the quotient map. -/
@[simp]
theorem deepResidueEquiv_residue (n : ℕ) (x : spectralIntegerRing K (𝔈 n).val) :
    deepResidueEquiv K L n (IsLocalRing.residue _ x) =
      IsLocalRing.residue (𝔅 n) (Ideal.Quotient.mk _ x) := rfl

/-- The deep truncated residue field is perfect, by the
finite residue inclusion, without any finiteness-of-cardinality assumption. -/
instance deepResidue_perfectField (n : ℕ) :
    PerfectField (IsLocalRing.ResidueField (𝔅 n)) :=
  PerfectField.of_ringEquiv (deepResidueEquiv K L n)

/-- The deep residue field has the residue characteristic. -/
instance deepResidue_charP (n : ℕ) :
    CharP (IsLocalRing.ResidueField (𝔅 n)) p :=
  charP_of_injective_ringHom (deepResidueEquiv K L n).injective p

/-- The constants, restricted to the field of norms
valuation ring using their proved integrality. -/
def residueConstantsInteger :
    κL →*₀ (FieldOfNorms.fieldValuation K L).valuationSubring := by
  exact {
    toFun := fun x => ⟨residueConstants K L x,
      residueConstants_valuation_le_one K L x⟩
    map_zero' := Subtype.ext (map_zero (residueConstants K L))
    map_one' := Subtype.ext (map_one (residueConstants K L))
    map_mul' := fun x y => Subtype.ext (map_mul (residueConstants K L) x y) }

/-- The integral deep coordinate of a constant is its
finite integral representative. -/
theorem FieldOfNorms.integralCoordinate_residueConstantsInteger (n : ℕ) (x : κL) :
    FieldOfNorms.integralCoordinate K L K₁
      (residueConstantsInteger K L x) n =
      residueIntegralCoordinate K L (deepFiniteTower K L K₁ n)
        (le_deepFiniteTower K L K₁ n) x := by
  apply Subtype.ext
  exact FieldOfNorms.coord_residueConstants K L _
    (le_deepFiniteTower K L K₁ n) x

/-- The maximal ideal of each truncated coordinate ring is nilpotent. -/
theorem deep_maximalIdeal_isNilpotent (n : ℕ) :
    IsNilpotent (IsLocalRing.maximalIdeal (𝔅 n)) :=
  ⟨n + 2, deepFiniteTowerQuotient_maximalIdeal_pow K L K₁ n⟩

/-- The truncated coordinate is an unital ring map: inverse
Frobenius and residue inclusions feed the canonical coefficient section. -/
def residueTruncatedHom (n : ℕ) : κL →+* 𝔅 n :=
  (truncatedResidueCoefficients (𝔅 n) p
    (deep_maximalIdeal_isNilpotent K L n)).comp
      ((deepResidueEquiv K L n).toRingHom.comp
        (residueCoordinateEquiv K L (𝔈 n)
          (le_deepFiniteTower K L K₁ n)).toRingHom)

/-- The ring-valued truncated coordinate is exactly the truncation of the
constant. This uses the existing Teichmüller section's
naturality under the quotient projection. -/
theorem FieldOfNorms.truncation_residueConstantsInteger (n : ℕ) (x : κL) :
    FieldOfNorms.truncation K L K₁ n
      (residueConstantsInteger K L x) =
      residueTruncatedHom K L n x := by
  let q : spectralIntegerRing K (𝔈 n).val →+* 𝔅 n := Ideal.Quotient.mk _
  let : IsLocalHom q := Ideal.Quotient.mk_surjective.isLocalHom
  let := isAdicComplete_of_isNilpotent_ideal (IsLocalRing.maximalIdeal (𝔅 n))
    (deep_maximalIdeal_isNilpotent K L n)
  rw [FieldOfNorms.truncation_apply, FieldOfNorms.integralCoordinate_residueConstantsInteger,
    residueIntegralCoordinate_eq_spectralTeichmuller]
  change q (residueTeichmuller (spectralIntegerRing K (𝔈 n).val) p
      (residueCoordinateEquiv K L (𝔈 n)
        (le_deepFiniteTower K L K₁ n) x)) =
    residueTeichmuller (𝔅 n) p (IsLocalRing.ResidueField.map q
      (residueCoordinateEquiv K L (𝔈 n)
        (le_deepFiniteTower K L K₁ n) x))
  exact residueTeichmuller_naturality (spectralIntegerRing K (𝔈 n).val) p (𝔅 n) q _

/-- The integral constants are additive: their deep
truncations are additive ring maps, and the truncation equivalence is injective. -/
theorem residueConstantsInteger_add (x y : κL) :
    residueConstantsInteger K L (x + y) =
      residueConstantsInteger K L x +
        residueConstantsInteger K L y := by
  apply (FieldOfNorms.truncationEquiv K L K₁).injective
  apply Subtype.ext
  funext n
  change FieldOfNorms.truncation K L K₁ n
    (residueConstantsInteger K L (x + y)) =
    FieldOfNorms.truncation K L K₁ n
      (residueConstantsInteger K L x +
        residueConstantsInteger K L y)
  rw [map_add (FieldOfNorms.truncation K L K₁ n),
    FieldOfNorms.truncation_residueConstantsInteger,
    FieldOfNorms.truncation_residueConstantsInteger,
    FieldOfNorms.truncation_residueConstantsInteger]
  exact map_add (residueTruncatedHom K L n) x y

/-- The integral constants as an unital ring map. -/
def residueConstantsIntegerHom :
    κL →+* (FieldOfNorms.fieldValuation K L).valuationSubring := by
  exact { residueConstantsInteger K L with
    map_add' := residueConstantsInteger_add K L }

/-- The source-normalized coefficient field embedding into the same
field of norms, with the addition and multiplication. -/
def residueConstantsFieldEmbedding :
    κL →+* FieldOfNorms K L := by
  exact (FieldOfNorms.fieldValuation K L).valuationSubring.subtype.comp
    (residueConstantsIntegerHom K L)

/-- The field embedding's underlying function is exactly the
source-normalized norm-compatible family already constructed. -/
@[simp]
theorem residueConstantsFieldEmbedding_apply (x : κL) :
    residueConstantsFieldEmbedding K L x =
      residueConstants K L x := rfl

/-- The coefficient map is an injective field homomorphism. -/
theorem residueConstantsFieldEmbedding_injective :
    Function.Injective (residueConstantsFieldEmbedding K L) :=
  residueConstants_injective K L

/-- Under the residue-field identification, the reduction
of a constant is precisely the inverse-Frobenius-normalized coordinate. -/
theorem FieldOfNorms.residueLayerEquiv_residueConstantsInteger (x : κL) :
    FieldOfNorms.residueLayerEquiv K L K₁
      (IsLocalRing.residue _ (residueConstantsInteger K L x)) =
      residueCoordinateEquiv K L (deepFiniteTower K L K₁ 0)
        (le_deepFiniteTower K L K₁ 0) x := by
  rw [FieldOfNorms.residueLayerEquiv_residue,
    FieldOfNorms.integralCoordinate_residueConstantsInteger,
    residueCoordinateEquiv_apply]

/-- **Theorem 2.1.3 (iii).** The residue field of `X_K(L)` is the residue field `k_L` of `L`
(the residue field of the integral closure of `𝒪_K` in `L`); the isomorphism is induced by the
constants `residueConstants`. -/
def FieldOfNorms.residueEquiv :
    κL ≃+* IsLocalRing.ResidueField
      (FieldOfNorms.fieldValuation K L).valuationSubring := by
  exact (residueCoordinateEquiv K L (deepFiniteTower K L K₁ 0)
    (le_deepFiniteTower K L K₁ 0)).trans
      (FieldOfNorms.residueLayerEquiv K L K₁).symm

/-- This residue isomorphism is induced by the source
constants, rather than by a new coefficient model. -/
@[simp]
theorem FieldOfNorms.residueEquiv_apply (x : κL) :
    FieldOfNorms.residueEquiv K L x =
      IsLocalRing.residue _ (residueConstantsInteger K L x) := by
  apply (FieldOfNorms.residueLayerEquiv K L K₁).injective
  exact (FieldOfNorms.residueLayerEquiv K L K₁).apply_symm_apply _ |>.trans
    (FieldOfNorms.residueLayerEquiv_residueConstantsInteger K L x).symm

end Constants

end FontaineWintenberger
