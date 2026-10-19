/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.Functor.Separable
public import FontaineWintenberger.FieldOfNorms.Functor.Map
public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.Data.Fintype.Order
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Field.ULift

/-!
# The relative field of norms

## Directed unions of the original finite norm fields

The stages are the original norm fields of actual finite intermediate fields
over the given infinite APF extension. The transition maps are the already
constructed original finite-inclusion maps. Mathlib's directed colimit supplies
the single union carrier.

Reference: Wintenberger, paragraph 3.2.1. The compatible union valuation uses
the rational normalization of the proved finite-stage valuation exponents.

## Isomorphisms of original norm-field unions

An isomorphism of the original separable algebraic extensions induces an
algebra isomorphism of their same canonical norm-field unions. The inverse
is induced by the original inverse, using the actual union-map laws.

Reference: Wintenberger, §§3.2.1 and 3.2.6.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

section Fields

variable (K L M : Type*) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/-- No intermediate field of `M/L` is finite over `K` when `L/K` is infinite. -/
theorem RelFieldOfNorms.stage_infinite [Fact (¬ Module.Finite K L)]
    (E : IntermediateField L M) : ¬ Module.Finite K E := by
  intro h
  let : Module.Finite K E := h
  exact (Fact.out : ¬ Module.Finite K L) (FiniteDimensional.of_injective
    (IsScalarTower.toAlgHom K L E).toLinearMap (algebraMap L E).injective)

/-- Keyed on an arbitrary `IntermediateField L M` so that it fires on `N.val` for
`N : FiniteIntermediateField L M` and on explicitly constructed stages alike. -/
instance RelFieldOfNorms.instFactNotFiniteStage [Fact (¬ Module.Finite K L)]
    (E : IntermediateField L M) : Fact (¬ Module.Finite K E) :=
  ⟨RelFieldOfNorms.stage_infinite K L M E⟩

/-- Every intermediate field of a separable tower `K ⊆ L ⊆ M` is separable over `K`. Keyed on an
arbitrary `IntermediateField L M` so that it also fires on explicitly constructed stages
`(⟨E, _⟩ : FiniteIntermediateField L M).val`. -/
instance intermediateField_isSeparable_of_tower [Algebra.IsSeparable K L]
    [Algebra.IsSeparable L M] (E : IntermediateField L M) : Algebra.IsSeparable K E :=
  Algebra.IsSeparable.trans K L E

/-- An ambient extension of the infinite original extension is infinite over `K`. -/
theorem RelFieldOfNorms._ambient_infinite [Fact (¬ Module.Finite K L)] :
    ¬ Module.Finite K M := by
  intro h
  let : Module.Finite K M := h
  exact (Fact.out : ¬ Module.Finite K L) (FiniteDimensional.of_injective
    (IsScalarTower.toAlgHom K L M).toLinearMap (algebraMap L M).injective)

end Fields

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L M : Type*) [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable L M]

/-- Finite extension of the original APF extension supplies APF at every finite stage. -/
instance RelFieldOfNorms.instIsAPFStage [IsAPF K L] (E : IntermediateField L M)
    [FiniteDimensional L E] : IsAPF K E :=
  (isAPF_finite_extension_iff K E L).mpr ‹_›

variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- The transition homomorphism is the existing original finite-inclusion map. -/
def RelFieldOfNorms.transition (N P : FiniteIntermediateField L M) (h : N ≤ P) :
    FieldOfNorms K N.val →+* FieldOfNorms K P.val := by
  letI : Algebra N.val P.val := (IntermediateField.inclusion h).toRingHom.toAlgebra
  letI : IsScalarTower L N.val P.val := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower K N.val P.val := IsScalarTower.of_algebraMap_eq' rfl
  letI : Module.Finite N.val P.val := Module.Finite.right L N.val P.val
  letI : Algebra.IsSeparable N.val P.val :=
    Algebra.isSeparable_tower_top_of_isSeparable L N.val P.val
  exact FieldOfNorms.finiteRingHom K N.val P.val

/-- The original identity law is retained at the actual finite stage. -/
@[simp]
theorem RelFieldOfNorms.transition_self (N : FiniteIntermediateField L M) :
    RelFieldOfNorms.transition K L M N N le_rfl =
      RingHom.id (FieldOfNorms K N.val) := by
  apply RingHom.ext
  intro x
  exact FieldOfNorms.finiteMap_refl K N.val x

/-- Composition retains the original finite norm-family maps in the same tower. -/
theorem RelFieldOfNorms.transition_comp (N P Q : FiniteIntermediateField L M)
    (hNP : N ≤ P) (hPQ : P ≤ Q) :
    (RelFieldOfNorms.transition K L M P Q hPQ).comp
        (RelFieldOfNorms.transition K L M N P hNP) =
      RelFieldOfNorms.transition K L M N Q (hNP.trans hPQ) := by
  let : Algebra N.val P.val := (IntermediateField.inclusion hNP).toRingHom.toAlgebra
  let : Algebra P.val Q.val := (IntermediateField.inclusion hPQ).toRingHom.toAlgebra
  let : Algebra N.val Q.val :=
    (IntermediateField.inclusion (hNP.trans hPQ)).toRingHom.toAlgebra
  let : IsScalarTower L N.val P.val := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower L N.val Q.val := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower L P.val Q.val := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K N.val P.val := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K N.val Q.val := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K P.val Q.val := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower N.val P.val Q.val := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite N.val P.val := Module.Finite.right L N.val P.val
  let : Module.Finite P.val Q.val := Module.Finite.right L P.val Q.val
  let : Algebra.IsSeparable N.val P.val :=
    Algebra.isSeparable_tower_top_of_isSeparable L N.val P.val
  let : Algebra.IsSeparable P.val Q.val :=
    Algebra.isSeparable_tower_top_of_isSeparable L P.val Q.val
  apply RingHom.ext
  intro x
  exact FieldOfNorms.finiteMap_trans K N.val P.val Q.val x

/-- The proved original identity and composition laws give the directed system. -/
instance RelFieldOfNorms.instDirectedSystem :
    DirectedSystem (fun N : FiniteIntermediateField L M => FieldOfNorms K N.val)
      (RelFieldOfNorms.transition K L M · · ·) where
  map_self {i} x := by
    exact congrArg (fun f : FieldOfNorms K i.val →+* FieldOfNorms K i.val => f x)
      (RelFieldOfNorms.transition_self K L M i)
  map_map {k j i} hij hjk x := by
    exact congrArg (fun f : FieldOfNorms K i.val →+* FieldOfNorms K k.val => f x)
      (RelFieldOfNorms.transition_comp K L M i j k hij hjk)

/-- The single canonical directed colimit of the original finite norm fields.

A `def`, not an `abbrev`: its structures are global instances keyed on `RelFieldOfNorms`. -/
def RelFieldOfNorms :=
  DirectLimit (fun N : FiniteIntermediateField L M => FieldOfNorms K N.val)
    (RelFieldOfNorms.transition K L M)

/-- Mathlib's field structure on this directed colimit of the original fields. -/
instance RelFieldOfNorms.instField : Field (RelFieldOfNorms K L M) :=
  inferInstanceAs (Field (DirectLimit (fun N : FiniteIntermediateField L M => FieldOfNorms K N.val)
    (RelFieldOfNorms.transition K L M)))

/-- The canonical structural embedding of an original finite-stage norm field. -/
def RelFieldOfNorms.of (N : FiniteIntermediateField L M) :
    FieldOfNorms K N.val →+* RelFieldOfNorms K L M := by
  exact DirectLimit.Ring.of (fun P : FiniteIntermediateField L M => FieldOfNorms K P.val)
    (RelFieldOfNorms.transition K L M) N

/-- Every original finite-stage structural map is injective. -/
theorem RelFieldOfNorms.of_injective (N : FiniteIntermediateField L M) :
    Function.Injective (RelFieldOfNorms.of K L M N) := by
  exact (RelFieldOfNorms.of K L M N).injective

/-- Structural embeddings identify each original transition with its source. -/
theorem RelFieldOfNorms.of_transition (N P : FiniteIntermediateField L M) (hNP : N ≤ P)
    (x : FieldOfNorms K N.val) :
    RelFieldOfNorms.of K L M P
        (RelFieldOfNorms.transition K L M N P hNP x) =
      RelFieldOfNorms.of K L M N x := by
  exact DirectLimit.Ring.of_f
    (f := RelFieldOfNorms.transition K L M) hNP x

/-- Every union element is represented by an actual original finite-stage family. -/
theorem RelFieldOfNorms._exists_stage (z : RelFieldOfNorms K L M) :
    ∃ (N : FiniteIntermediateField L M) (x : FieldOfNorms K N.val),
      RelFieldOfNorms.of K L M N x = z := by
  obtain ⟨N, x, hx⟩ := DirectLimit.exists_eq_mk
    (RelFieldOfNorms.transition K L M) z
  exact ⟨N, x, hx.symm⟩

/-- Any finite family of union elements lies in one actual original finite stage. -/
theorem RelFieldOfNorms._exists_finiteStage {α : Type*} [Finite α]
    (z : α → RelFieldOfNorms K L M) :
    ∃ (N : FiniteIntermediateField L M) (x : α → FieldOfNorms K N.val),
      ∀ a, RelFieldOfNorms.of K L M N (x a) = z a := by
  classical
  choose N x hx using fun a => RelFieldOfNorms._exists_stage K L M (z a)
  obtain ⟨P, hP⟩ := Finite.exists_le N
  refine ⟨P, fun a => RelFieldOfNorms.transition K L M
    (N a) P (hP a) (x a), ?_⟩
  intro a
  exact (RelFieldOfNorms.of_transition K L M (N a) P (hP a) (x a)).trans
    (hx a)

/-- Every polynomial over the union descends along an actual finite-stage embedding. -/
theorem RelFieldOfNorms._exists_polynomial :
    ∀ F : Polynomial (RelFieldOfNorms K L M),
      ∃ N : FiniteIntermediateField L M,
        ∃ f : Polynomial (FieldOfNorms K N.val),
          f.map (RelFieldOfNorms.of K L M N) = F := by
  intro F
  obtain ⟨N, x, hx⟩ := RelFieldOfNorms._exists_finiteStage K L M
    (fun a : F.coeffs => (a : RelFieldOfNorms K L M))
  have hm : F ∈ Polynomial.lifts (RelFieldOfNorms.of K L M N) :=
    (Polynomial.lifts_iff_coeffs_subset_range F).mpr (by
      intro a ha
      exact ⟨x ⟨a, ha⟩, hx ⟨a, ha⟩⟩)
  obtain ⟨f, hf⟩ := (Polynomial.mem_lifts F).mp hm
  exact ⟨N, f, hf⟩

/-- The original finite-inclusion map from the base norm field to a stage. -/
def RelFieldOfNorms.baseToStage (N : FiniteIntermediateField L M) :
    FieldOfNorms K L →+* FieldOfNorms K N.val := by
  exact FieldOfNorms.finiteRingHom K L N.val

/-- Transition maps commute with the actual finite maps from the base field. -/
theorem RelFieldOfNorms.transition_base (N P : FiniteIntermediateField L M) (hNP : N ≤ P) :
    (RelFieldOfNorms.transition K L M N P hNP).comp
        (RelFieldOfNorms.baseToStage K L M N) =
      RelFieldOfNorms.baseToStage K L M P := by
  let : Algebra N.val P.val := (IntermediateField.inclusion hNP).toRingHom.toAlgebra
  let : IsScalarTower L N.val P.val := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K N.val P.val := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite N.val P.val := Module.Finite.right L N.val P.val
  let : Algebra.IsSeparable N.val P.val :=
    Algebra.isSeparable_tower_top_of_isSeparable L N.val P.val
  apply RingHom.ext
  intro x
  exact FieldOfNorms.finiteMap_trans K L N.val P.val x

/-- The canonical base embedding into the same directed union. -/
def RelFieldOfNorms.baseHom :
    FieldOfNorms K L →+* RelFieldOfNorms K L M := by
  exact (RelFieldOfNorms.of K L M (FiniteIntermediateField.bottom)).comp
    (RelFieldOfNorms.baseToStage K L M (FiniteIntermediateField.bottom))

/-- Every finite-stage structural embedding gives that same actual base map. -/
theorem RelFieldOfNorms.of_base (N : FiniteIntermediateField L M) (x : FieldOfNorms K L) :
    RelFieldOfNorms.of K L M N
        (RelFieldOfNorms.baseToStage K L M N x) =
      RelFieldOfNorms.baseHom K L M x := by
  have hc := congrArg (fun f : FieldOfNorms K L →+* FieldOfNorms K N.val => f x)
    (RelFieldOfNorms.transition_base K L M
      (FiniteIntermediateField.bottom) N (FiniteIntermediateField.bottom_le N))
  change RelFieldOfNorms.of K L M N
      (RelFieldOfNorms.baseToStage K L M N x) =
    RelFieldOfNorms.of K L M (FiniteIntermediateField.bottom)
      (RelFieldOfNorms.baseToStage K L M (FiniteIntermediateField.bottom) x)
  rw [← hc]
  exact RelFieldOfNorms.of_transition K L M (FiniteIntermediateField.bottom) N
    (FiniteIntermediateField.bottom_le N) _

/-- The finite-stage algebra is induced by its original finite norm-field map. -/
instance RelFieldOfNorms.instAlgebraStage (N : FiniteIntermediateField L M) :
    Algebra (FieldOfNorms K L) (FieldOfNorms K N.val) :=
  (RelFieldOfNorms.baseToStage K L M N).toAlgebra

/-- The sole base algebra structure comes from the canonical original base map. -/
instance RelFieldOfNorms.instAlgebra :
    Algebra (FieldOfNorms K L) (RelFieldOfNorms K L M) :=
  (RelFieldOfNorms.baseHom K L M).toAlgebra

/-- The original finite-stage embedding as an algebra homomorphism over the base. -/
def RelFieldOfNorms.ofAlgHom (N : FiniteIntermediateField L M) :
    FieldOfNorms K N.val →ₐ[FieldOfNorms K L] RelFieldOfNorms K L M := by
  exact { RelFieldOfNorms.of K L M N with
    commutes' := RelFieldOfNorms.of_base K L M N }

/-- Actual finite-stage separability makes the same union separable algebraic. -/
theorem RelFieldOfNorms._isSeparable :
    Algebra.IsSeparable (FieldOfNorms K L) (RelFieldOfNorms K L M) := by
  constructor
  intro z
  obtain ⟨N, x, rfl⟩ := RelFieldOfNorms._exists_stage K L M z
  let : Algebra.IsSeparable (FieldOfNorms K L) (FieldOfNorms K N.val) :=
    (FieldOfNorms.finite_finite_separable_degree K L N.val
).2.1
  exact IsSeparable.map (RelFieldOfNorms.ofAlgHom K L M N)
    (RelFieldOfNorms.ofAlgHom K L M N).injective
    (Algebra.IsSeparable.isSeparable (FieldOfNorms K L) x)

/-- Rational rescaling of the existing integer valuation group, with zero preserved. -/
def RelFieldOfNorms.valueMap (e : ℕ) :
    WithZero (Multiplicative ℤ) →*₀o WithZero (Multiplicative ℚ) := by
  let a : ℤ →+ ℚ :=
    { toFun := fun z => (z : ℚ) / (e : ℚ)
      map_zero' := by simp
      map_add' := by intro x y; simp only [Int.cast_add, add_div] }
  let f : Multiplicative ℤ →* Multiplicative ℚ := a.toMultiplicative
  refine { WithZero.map' f with monotone' := WithZero.map'_mono ?_ }
  intro x y hxy
  change (x.toAdd : ℚ) / (e : ℚ) ≤ (y.toAdd : ℚ) / (e : ℚ)
  exact div_le_div_of_nonneg_right (by exact_mod_cast hxy) (Nat.cast_nonneg e)

/-- Rescaling retains the literal exponential coordinates of the original value group. -/
@[simp]
theorem RelFieldOfNorms.valueMap_exp (e : ℕ) (z : ℤ) :
    RelFieldOfNorms.valueMap e (WithZero.exp z) =
      WithZero.exp ((z : ℚ) / (e : ℚ)) := rfl

/-- Rational normalization cancels a positive finite-inclusion scaling exponent. -/
theorem RelFieldOfNorms.valueMap_pow (e c : ℕ) (he : 0 < e) (hc : 0 < c)
    (x : WithZero (Multiplicative ℤ)) :
    RelFieldOfNorms.valueMap (e * c) (x ^ c) = RelFieldOfNorms.valueMap e x := by
  induction x using WithZero.recZeroCoe with
  | zero => simp [Nat.ne_of_gt hc]
  | coe x =>
      change RelFieldOfNorms.valueMap (e * c) ((WithZero.exp x.toAdd) ^ c) =
        RelFieldOfNorms.valueMap e (WithZero.exp x.toAdd)
      rw [← WithZero.exp_nsmul, RelFieldOfNorms.valueMap_exp,
        RelFieldOfNorms.valueMap_exp]
      congr 1
      have he' : (e : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt he)
      have hc' : (c : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hc)
      push_cast
      field_simp
      simp only [nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]

/-- The actual positive scaling exponent of the original finite map from the base. -/
def RelFieldOfNorms.stageExponent (N : FiniteIntermediateField L M) : ℕ :=
  Classical.choose (exists_finiteFieldOfNormsMap_valuation_scaling K L N.val
)

omit [Fact (¬ Module.Finite K L)] in
/-- Positivity is supplied by the original finite-embedding theorem. -/
theorem RelFieldOfNorms.stageExponent_pos (N : FiniteIntermediateField L M) :
    0 < RelFieldOfNorms.stageExponent K L M N :=
  (Classical.choose_spec (exists_finiteFieldOfNormsMap_valuation_scaling K L N.val
)).1

omit [Fact (¬ Module.Finite K L)] in
/-- The chosen exponent satisfies the proved original finite-map valuation identity. -/
theorem RelFieldOfNorms.stageExponent_spec (N : FiniteIntermediateField L M) (x : FieldOfNorms K L)
    :
    FieldOfNorms.valuation K N.val
        (FieldOfNorms.finiteMap K L N.val x) =
      FieldOfNorms.valuation K L x ^ RelFieldOfNorms.stageExponent K L M N :=
  (Classical.choose_spec (exists_finiteFieldOfNormsMap_valuation_scaling K L N.val
)).2 x

/-- The original base uniformizer makes the finite-stage scaling exponent unique. -/
theorem RelFieldOfNorms.stageExponent_unique (N : FiniteIntermediateField L M) (c : ℕ)
    (hc : ∀ x : FieldOfNorms K L,
      FieldOfNorms.valuation K N.val
        (FieldOfNorms.finiteMap K L N.val x) = FieldOfNorms.valuation K L x ^ c) :
    c = RelFieldOfNorms.stageExponent K L M N := by
  have h := (hc (FieldOfNorms.uniformizer K L)).symm.trans
    (RelFieldOfNorms.stageExponent_spec K L M N
      (FieldOfNorms.uniformizer K L))
  rw [FieldOfNorms.valuation_fieldOfNormsUniformizer, ← WithZero.exp_nsmul,
    ← WithZero.exp_nsmul] at h
  have hn := WithZero.exp_injective h
  simp only [nsmul_eq_mul, mul_neg, mul_one] at hn
  exact_mod_cast neg_injective hn

/-- The genuine relative scaling exponent also gives the base-exponent cocycle. -/
theorem RelFieldOfNorms.transition_valuation_scaling (N P : FiniteIntermediateField L M)
    (hNP : N ≤ P) :
    ∃ c : ℕ, 0 < c ∧
      RelFieldOfNorms.stageExponent K L M P =
        RelFieldOfNorms.stageExponent K L M N * c ∧
      ∀ x : FieldOfNorms K N.val,
        FieldOfNorms.valuation K P.val
            (RelFieldOfNorms.transition K L M N P hNP x) =
          FieldOfNorms.valuation K N.val x ^ c := by
  let : Algebra N.val P.val := (IntermediateField.inclusion hNP).toRingHom.toAlgebra
  let : IsScalarTower L N.val P.val := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K N.val P.val := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite N.val P.val := Module.Finite.right L N.val P.val
  let : Algebra.IsSeparable N.val P.val :=
    Algebra.isSeparable_tower_top_of_isSeparable L N.val P.val
  obtain ⟨c, hc, hv⟩ := exists_finiteFieldOfNormsMap_valuation_scaling K N.val P.val
  refine ⟨c, hc, ?_, hv⟩
  apply (RelFieldOfNorms.stageExponent_unique K L M P
    (RelFieldOfNorms.stageExponent K L M N * c) ?_).symm
  intro x
  rw [← FieldOfNorms.finiteMap_trans K L N.val P.val x, hv,
    RelFieldOfNorms.stageExponent_spec, pow_mul]

/-- The original stage valuation, rationally normalized over the base norm field. -/
def RelFieldOfNorms.stageValuation (N : FiniteIntermediateField L M) :
    Valuation (FieldOfNorms K N.val) (WithZero (Multiplicative ℚ)) := by
  exact (FieldOfNorms.fieldValuation K N.val
).map
      (RelFieldOfNorms.valueMap (RelFieldOfNorms.stageExponent K L M N))

/-- The rational stage valuation is computed from the same original integer valuation. -/
@[simp]
theorem RelFieldOfNorms.stageValuation_apply (N : FiniteIntermediateField L M)
    (x : FieldOfNorms K N.val) :
    RelFieldOfNorms.stageValuation K L M N x =
      RelFieldOfNorms.valueMap (RelFieldOfNorms.stageExponent K L M N)
        (FieldOfNorms.valuation K N.val x) := rfl

/-- The rationally normalized valuations are strictly compatible with actual transitions. -/
theorem RelFieldOfNorms.stageValuation_transition (N P : FiniteIntermediateField L M)
    (hNP : N ≤ P) (x : FieldOfNorms K N.val) :
    RelFieldOfNorms.stageValuation K L M P
        (RelFieldOfNorms.transition K L M N P hNP x) =
      RelFieldOfNorms.stageValuation K L M N x := by
  obtain ⟨c, hc, he, hv⟩ := RelFieldOfNorms.transition_valuation_scaling
    K L M N P hNP
  rw [RelFieldOfNorms.stageValuation_apply, RelFieldOfNorms.stageValuation_apply,
    hv x, he]
  exact RelFieldOfNorms.valueMap_pow _ _ (RelFieldOfNorms.stageExponent_pos K L M N)
    hc _

/-- Every normalized finite-stage valuation extends the original base valuation. -/
theorem RelFieldOfNorms.stageValuation_base (N : FiniteIntermediateField L M) (x : FieldOfNorms K
    L) :
    RelFieldOfNorms.stageValuation K L M N
        (RelFieldOfNorms.baseToStage K L M N x) =
      RelFieldOfNorms.valueMap 1 (FieldOfNorms.valuation K L x) := by
  rw [RelFieldOfNorms.stageValuation_apply]
  change RelFieldOfNorms.valueMap (RelFieldOfNorms.stageExponent K L M N)
      (FieldOfNorms.valuation K N.val
        (FieldOfNorms.finiteMap K L N.val x)) = _
  rw [RelFieldOfNorms.stageExponent_spec]
  simpa only [one_mul] using RelFieldOfNorms.valueMap_pow 1
    (RelFieldOfNorms.stageExponent K L M N) (by decide)
    (RelFieldOfNorms.stageExponent_pos K L M N) (FieldOfNorms.valuation K L x)

/-- The strictly compatible rational valuations descend on the same relative field of norms. -/
def RelFieldOfNorms.valuation :
    Valuation (RelFieldOfNorms K L M) (WithZero (Multiplicative ℚ)) := by
  let f := RelFieldOfNorms.transition K L M
  let v := RelFieldOfNorms.stageValuation K L M
  let hv : ∀ (N P : FiniteIntermediateField L M) (hNP : N ≤ P) (x : FieldOfNorms K N.val),
      v N x = v P (f N P hNP x) := fun N P hNP x =>
    (RelFieldOfNorms.stageValuation_transition K L M N P hNP x).symm
  refine
    { toFun := DirectLimit.lift f (fun N => v N) hv
      map_zero' := DirectLimit.lift_zero (f := f) v hv
      map_one' := DirectLimit.lift_one (f := f) v hv
      map_mul' := DirectLimit.lift_mul (f := f) v hv
      map_add_le_max' := ?_ }
  intro x y
  refine DirectLimit.induction₂ f (fun N a b => ?_) x y
  have hs : RelFieldOfNorms.of K L M N a + RelFieldOfNorms.of K L M N b =
      RelFieldOfNorms.of K L M N (a + b) :=
    ((RelFieldOfNorms.of K L M N).map_add a b).symm
  change DirectLimit.lift f (fun N => v N) hv
      (RelFieldOfNorms.of K L M N a + RelFieldOfNorms.of K L M N b) ≤ _
  rw [hs]
  exact (v N).map_add a b

/-- The descended valuation retains its exact original finite-stage formula. -/
@[simp]
theorem RelFieldOfNorms.valuation_of (N : FiniteIntermediateField L M) (x : FieldOfNorms K N.val) :
    RelFieldOfNorms.valuation K L M
        (RelFieldOfNorms.of K L M N x) =
      RelFieldOfNorms.stageValuation K L M N x := rfl

/-- The same union valuation extends the original valuation on the base norm field. -/
theorem RelFieldOfNorms.valuation_base (x : FieldOfNorms K L) :
    RelFieldOfNorms.valuation K L M
        (RelFieldOfNorms.baseHom K L M x) =
      RelFieldOfNorms.valueMap 1 (FieldOfNorms.valuation K L x) := by
  rw [← RelFieldOfNorms.of_base K L M (FiniteIntermediateField.bottom) x,
    RelFieldOfNorms.valuation_of, RelFieldOfNorms.stageValuation_base]

/-- The canonical valuation equips the same original union with its valuation topology. -/
instance RelFieldOfNorms.instValued :
    Valued (RelFieldOfNorms K L M) (WithZero (Multiplicative ℚ)) :=
  Valued.mk' (RelFieldOfNorms.valuation K L M)

section FiniteAmbient

variable [Module.Finite L M]

/-- The terminal finite stage is the entire given finite extension. -/
abbrev RelFieldOfNorms.top : FiniteIntermediateField L M := ⟨⊤, inferInstance⟩

/-- The actual terminal structural map is bijective, without changing the union. -/
theorem RelFieldOfNorms.of_top_bijective : Function.Bijective
    (RelFieldOfNorms.of K L M (RelFieldOfNorms.top L M)) := by
  refine ⟨RelFieldOfNorms.of_injective K L M _, ?_⟩
  intro z
  obtain ⟨N, x, hx⟩ := RelFieldOfNorms._exists_stage K L M z
  have hNT : N ≤ RelFieldOfNorms.top L M :=
    show N.val ≤ (⊤ : IntermediateField L M) from le_top
  refine ⟨RelFieldOfNorms.transition K L M N
    (RelFieldOfNorms.top L M) hNT x, ?_⟩
  exact (RelFieldOfNorms.of_transition K L M N
    (RelFieldOfNorms.top L M) hNT x).trans hx

/-- For a finite ambient extension, its terminal norm field is the same union. -/
def RelFieldOfNorms.topEquiv :
    FieldOfNorms K (RelFieldOfNorms.top L M).val ≃+*
      RelFieldOfNorms K L M := by
  exact RingEquiv.ofBijective
    (RelFieldOfNorms.of K L M (RelFieldOfNorms.top L M))
    (RelFieldOfNorms.of_top_bijective K L M)

/-- The terminal equivalence is literally the existing structural map. -/
@[simp]
theorem RelFieldOfNorms.topEquiv_apply
    (x : FieldOfNorms K (RelFieldOfNorms.top L M).val) :
    RelFieldOfNorms.topEquiv K L M x =
      RelFieldOfNorms.of K L M (RelFieldOfNorms.top L M) x := rfl

/-- The same finite union is canonically the original norm field of the ambient extension. -/
def RelFieldOfNorms.finiteEquiv :
    letI : Algebra.IsSeparable K M := Algebra.IsSeparable.trans K L M
    letI : IsAPF K M := (isAPF_finite_extension_iff K M L).mpr ‹_›
    letI : Fact (¬ Module.Finite K M) := ⟨RelFieldOfNorms._ambient_infinite K L M⟩
    letI : IsAPF K M := (isAPF_finite_extension_iff K M L).mpr ‹_›
    letI : Fact (¬ Module.Finite K M) := ⟨RelFieldOfNorms._ambient_infinite K L M⟩
    RelFieldOfNorms K L M ≃+* FieldOfNorms K M := by
  letI : Algebra.IsSeparable K M := Algebra.IsSeparable.trans K L M
  letI : IsAPF K M := (isAPF_finite_extension_iff K M L).mpr ‹_›
  letI : Fact (¬ Module.Finite K M) := ⟨RelFieldOfNorms._ambient_infinite K L M⟩
  letI : Algebra.IsSeparable K (RelFieldOfNorms.top L M).val :=
    Algebra.IsSeparable.trans K L (RelFieldOfNorms.top L M).val
  letI : IsAPF K M := (isAPF_finite_extension_iff K M L).mpr ‹_›
  letI : Fact (¬ Module.Finite K M) := ⟨RelFieldOfNorms._ambient_infinite K L M⟩
  exact (RelFieldOfNorms.topEquiv K L M).symm.trans
    (FieldOfNorms.ringEquiv K
      ((IntermediateField.topEquiv :
        (⊤ : IntermediateField L M) ≃ₐ[L] M).restrictScalars K))

/-- The terminal comparison sends each original terminal family by literal transport. -/
@[simp]
theorem RelFieldOfNorms.finiteEquiv_of_top
    (x : FieldOfNorms K (RelFieldOfNorms.top L M).val) :
    RelFieldOfNorms.finiteEquiv K L M
        (RelFieldOfNorms.of K L M (RelFieldOfNorms.top L M) x) =
      FieldOfNorms.map ((IntermediateField.topEquiv :
        (⊤ : IntermediateField L M) ≃ₐ[L] M).restrictScalars K) x := by
  change FieldOfNorms.map ((IntermediateField.topEquiv :
      (⊤ : IntermediateField L M) ≃ₐ[L] M).restrictScalars K)
    ((RelFieldOfNorms.topEquiv K L M).symm
      (RelFieldOfNorms.topEquiv K L M x)) = _
  rw [RingEquiv.symm_apply_apply]

/-- The finite comparison retains every original finite-inclusion map. -/
theorem RelFieldOfNorms.finiteEquiv_of (N : FiniteIntermediateField L M) (x : FieldOfNorms K N.val)
    :
    letI : Module.Finite N.val M := Module.Finite.right L N.val M
    letI : Algebra.IsSeparable N.val M :=
      Algebra.isSeparable_tower_top_of_isSeparable L N.val M
    letI : IsScalarTower K N.val M := IsScalarTower.of_algebraMap_eq' rfl
    RelFieldOfNorms.finiteEquiv K L M
        (RelFieldOfNorms.of K L M N x) =
      FieldOfNorms.finiteMap K N.val M x := by
  let : Module.Finite N.val M := Module.Finite.right L N.val M
  let : Algebra.IsSeparable N.val M :=
    Algebra.isSeparable_tower_top_of_isSeparable L N.val M
  let : IsScalarTower K N.val M := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra N.val (RelFieldOfNorms.top L M).val :=
    (IntermediateField.inclusion (show N.val ≤ ⊤ from le_top)).toRingHom.toAlgebra
  let : IsScalarTower L N.val (RelFieldOfNorms.top L M).val :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K N.val (RelFieldOfNorms.top L M).val :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite N.val (RelFieldOfNorms.top L M).val :=
    Module.Finite.right L N.val (RelFieldOfNorms.top L M).val
  let : Algebra.IsSeparable N.val (RelFieldOfNorms.top L M).val :=
    Algebra.isSeparable_tower_top_of_isSeparable L N.val (RelFieldOfNorms.top L M).val
  have hNT : N ≤ RelFieldOfNorms.top L M :=
    show N.val ≤ (⊤ : IntermediateField L M) from le_top
  rw [← RelFieldOfNorms.of_transition K L M N
    (RelFieldOfNorms.top L M) hNT x, RelFieldOfNorms.finiteEquiv_of_top]
  simpa only [FieldOfNorms.map_refl, RelFieldOfNorms.transition, FieldOfNorms.finiteRingHom_apply]
    using FieldOfNorms.finiteMap_naturality K
    (AlgEquiv.refl : N.val ≃ₐ[K] N.val)
    ((IntermediateField.topEquiv :
      (⊤ : IntermediateField L M) ≃ₐ[L] M).restrictScalars K) (fun _ => rfl) x

/-- The same finite comparison commutes with the actual original base inclusion. -/
theorem RelFieldOfNorms.finiteEquiv_base (x : FieldOfNorms K L) :
    RelFieldOfNorms.finiteEquiv K L M
        (RelFieldOfNorms.baseHom K L M x) =
      FieldOfNorms.finiteMap K L M x := by
  rw [← RelFieldOfNorms.of_base K L M (RelFieldOfNorms.top L M) x,
    RelFieldOfNorms.finiteEquiv_of_top]
  simpa only [FieldOfNorms.map_refl, RelFieldOfNorms.baseToStage, FieldOfNorms.finiteRingHom_apply]
    using FieldOfNorms.finiteMap_naturality K
    (AlgEquiv.refl : L ≃ₐ[K] L)
    ((IntermediateField.topEquiv :
      (⊤ : IntermediateField L M) ≃ₐ[L] M).restrictScalars K) (fun _ => rfl) x

/-- The finite comparison retains the rational normalization over the original base. -/
theorem RelFieldOfNorms.finiteEquiv_valuation
    (z : RelFieldOfNorms K L M) :
    letI : Algebra.IsSeparable K M := Algebra.IsSeparable.trans K L M
    letI : IsAPF K M := (isAPF_finite_extension_iff K M L).mpr ‹_›
    letI : Fact (¬ Module.Finite K M) := ⟨RelFieldOfNorms._ambient_infinite K L M⟩
    RelFieldOfNorms.valueMap
        (RelFieldOfNorms.stageExponent K L M (RelFieldOfNorms.top L M))
        (FieldOfNorms.valuation K M
          (RelFieldOfNorms.finiteEquiv K L M z)) =
      RelFieldOfNorms.valuation K L M z := by
  let : Algebra.IsSeparable K M := Algebra.IsSeparable.trans K L M
  let : IsAPF K M := (isAPF_finite_extension_iff K M L).mpr ‹_›
  let : Fact (¬ Module.Finite K M) := ⟨RelFieldOfNorms._ambient_infinite K L M⟩
  let : Algebra.IsSeparable K (RelFieldOfNorms.top L M).val :=
    Algebra.IsSeparable.trans K L (RelFieldOfNorms.top L M).val
  obtain ⟨x, rfl⟩ :=
    (RelFieldOfNorms.of_top_bijective K L M).surjective z
  rw [RelFieldOfNorms.finiteEquiv_of_top, FieldOfNorms.valuation_fieldOfNormsMap,
    RelFieldOfNorms.valuation_of, RelFieldOfNorms.stageValuation_apply]

/-- Finite comparison over the same base and its original finite-inclusion algebra. -/
def RelFieldOfNorms.finiteAlgEquiv :
    letI : Algebra.IsSeparable K M := Algebra.IsSeparable.trans K L M
    letI : IsAPF K M := (isAPF_finite_extension_iff K M L).mpr ‹_›
    letI : Fact (¬ Module.Finite K M) := ⟨RelFieldOfNorms._ambient_infinite K L M⟩
    letI : IsAPF K M := (isAPF_finite_extension_iff K M L).mpr ‹_›
    letI : Fact (¬ Module.Finite K M) := ⟨RelFieldOfNorms._ambient_infinite K L M⟩
    letI := (FieldOfNorms.finiteRingHom K L M
).toAlgebra
    RelFieldOfNorms K L M ≃ₐ[FieldOfNorms K L] FieldOfNorms K M := by
  letI : Algebra.IsSeparable K M := Algebra.IsSeparable.trans K L M
  letI : IsAPF K M := (isAPF_finite_extension_iff K M L).mpr ‹_›
  letI : Fact (¬ Module.Finite K M) := ⟨RelFieldOfNorms._ambient_infinite K L M⟩
  letI : IsAPF K M := (isAPF_finite_extension_iff K M L).mpr ‹_›
  letI : Fact (¬ Module.Finite K M) := ⟨RelFieldOfNorms._ambient_infinite K L M⟩
  letI := (FieldOfNorms.finiteRingHom K L M
).toAlgebra
  exact { RelFieldOfNorms.finiteEquiv K L M with
    commutes' := RelFieldOfNorms.finiteEquiv_base K L M }

/-- Algebra bundling preserves the same canonical finite comparison. -/
@[simp]
theorem RelFieldOfNorms.finiteAlgEquiv_apply
    (z : RelFieldOfNorms K L M) :
    RelFieldOfNorms.finiteAlgEquiv K L M z =
      RelFieldOfNorms.finiteEquiv K L M z := rfl

end FiniteAmbient

section Embeddings

variable (M' : Type*) [Field M'] [Algebra K M'] [Algebra L M']
    [IsScalarTower K L M'] [Algebra.IsSeparable L M']
variable (t : M →ₐ[L] M')

/-- An actual ambient embedding transports each original finite-stage norm field. -/
def RelFieldOfNorms.stageMap (N : FiniteIntermediateField L M) :
    FieldOfNorms K N.val ≃+* FieldOfNorms K (FiniteIntermediateField.map t N).val := by
  letI : Algebra.IsSeparable K (FiniteIntermediateField.map t N).val :=
    Algebra.IsSeparable.trans K L (FiniteIntermediateField.map t N).val
  exact FieldOfNorms.ringEquiv K
    ((FiniteIntermediateField.equivMap t N).restrictScalars K)

/-- Stage transport is the existing literal norm-family isomorphism. -/
@[simp]
theorem RelFieldOfNorms.stageMap_apply (N : FiniteIntermediateField L M) (x : FieldOfNorms K N.val)
    :
    RelFieldOfNorms.stageMap K L M M' t N x =
      FieldOfNorms.map ((FiniteIntermediateField.equivMap t N).restrictScalars K) x := rfl

/-- Transport of the actual finite image commutes with the original base inclusion. -/
theorem RelFieldOfNorms.stageMap_base (N : FiniteIntermediateField L M) (x : FieldOfNorms K L) :
    RelFieldOfNorms.stageMap K L M M' t N
        (RelFieldOfNorms.baseToStage K L M N x) =
      RelFieldOfNorms.baseToStage K L M' (FiniteIntermediateField.map t N) x := by
  rw [RelFieldOfNorms.stageMap_apply]
  simpa only [RelFieldOfNorms.baseToStage, FieldOfNorms.finiteRingHom_apply,
    FieldOfNorms.map_refl] using FieldOfNorms.finiteMap_naturality K
    (AlgEquiv.refl : L ≃ₐ[K] L) ((FiniteIntermediateField.equivMap t N).restrictScalars K)
    (fun a => (FiniteIntermediateField.equivMap t N).commutes a) x

/-- Actual stage transport commutes with every original finite-stage transition. -/
theorem RelFieldOfNorms.stageMap_transition (N P : FiniteIntermediateField L M)
    (hNP : N ≤ P) (x : FieldOfNorms K N.val) :
    RelFieldOfNorms.stageMap K L M M' t P
        (RelFieldOfNorms.transition K L M N P hNP x) =
      RelFieldOfNorms.transition K L M'
        (FiniteIntermediateField.map t N) (FiniteIntermediateField.map t P)
            (FiniteIntermediateField.map_mono t hNP)
        (RelFieldOfNorms.stageMap K L M M' t N x) := by
  let : Algebra.IsSeparable K (FiniteIntermediateField.map t N).val :=
    Algebra.IsSeparable.trans K L (FiniteIntermediateField.map t N).val
  let : Algebra N.val P.val := (IntermediateField.inclusion hNP).toRingHom.toAlgebra
  let : IsScalarTower K N.val P.val := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite N.val P.val := Module.Finite.right L N.val P.val
  let : Algebra.IsSeparable N.val P.val :=
    Algebra.isSeparable_tower_top_of_isSeparable L N.val P.val
  let : Algebra (FiniteIntermediateField.map t N).val (FiniteIntermediateField.map t P).val :=
    (IntermediateField.inclusion (FiniteIntermediateField.map_mono t hNP)).toRingHom.toAlgebra
  let : IsScalarTower K (FiniteIntermediateField.map t N).val (FiniteIntermediateField.map t P).val
      :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite (FiniteIntermediateField.map t N).val (FiniteIntermediateField.map t P).val :=
    Module.Finite.right L (FiniteIntermediateField.map t N).val (FiniteIntermediateField.map t
        P).val
  let : Algebra.IsSeparable (FiniteIntermediateField.map t N).val (FiniteIntermediateField.map t
      P).val :=
    Algebra.isSeparable_tower_top_of_isSeparable L
      (FiniteIntermediateField.map t N).val (FiniteIntermediateField.map t P).val
  rw [RelFieldOfNorms.stageMap_apply, RelFieldOfNorms.stageMap_apply]
  simpa only [RelFieldOfNorms.transition, FieldOfNorms.finiteRingHom_apply] using
    FieldOfNorms.finiteMap_naturality K ((FiniteIntermediateField.equivMap t N).restrictScalars K)
      ((FiniteIntermediateField.equivMap t P).restrictScalars K)
      (fun _ => by apply Subtype.ext; rfl) x

/-- Original image isomorphisms retain the genuine base scaling exponents. -/
theorem RelFieldOfNorms.stageExponent_map (N : FiniteIntermediateField L M) :
    RelFieldOfNorms.stageExponent K L M' (FiniteIntermediateField.map t N) =
      RelFieldOfNorms.stageExponent K L M N := by
  let : Algebra.IsSeparable K (FiniteIntermediateField.map t N).val :=
    Algebra.IsSeparable.trans K L (FiniteIntermediateField.map t N).val
  apply (RelFieldOfNorms.stageExponent_unique K L M'
    (FiniteIntermediateField.map t N) (RelFieldOfNorms.stageExponent K L M N) ?_).symm
  intro x
  have h := FieldOfNorms.valuation_fieldOfNormsMap K
    ((FiniteIntermediateField.equivMap t N).restrictScalars K)
    (RelFieldOfNorms.baseToStage K L M N x)
  rw [← RelFieldOfNorms.stageMap_apply K L M M' t N,
    RelFieldOfNorms.stageMap_base K L M M' t N] at h
  simp only [RelFieldOfNorms.baseToStage, FieldOfNorms.finiteRingHom_apply] at h
  exact h.trans (RelFieldOfNorms.stageExponent_spec K L M N x)

/-- The actual stage isomorphisms preserve the rationally normalized valuations. -/
theorem RelFieldOfNorms.stageMap_valuation (N : FiniteIntermediateField L M)
    (x : FieldOfNorms K N.val) :
    RelFieldOfNorms.stageValuation K L M' (FiniteIntermediateField.map t N)
        (RelFieldOfNorms.stageMap K L M M' t N x) =
      RelFieldOfNorms.stageValuation K L M N x := by
  let : Algebra.IsSeparable K (FiniteIntermediateField.map t N).val :=
    Algebra.IsSeparable.trans K L (FiniteIntermediateField.map t N).val
  rw [RelFieldOfNorms.stageValuation_apply, RelFieldOfNorms.stageValuation_apply,
    RelFieldOfNorms.stageMap_apply, FieldOfNorms.valuation_fieldOfNormsMap,
    RelFieldOfNorms.stageExponent_map K L M M' t N]

/-- The actual compatible finite-image maps induce a map on the same canonical unions. -/
def RelFieldOfNorms.map :
    RelFieldOfNorms K L M →+*
      RelFieldOfNorms K L M' := by
  refine DirectLimit.Ring.lift (fun N : FiniteIntermediateField L M => FieldOfNorms K N.val)
    (RelFieldOfNorms.transition K L M)
    (RelFieldOfNorms K L M')
    (fun N => (RelFieldOfNorms.of K L M' (FiniteIntermediateField.map t N)).comp
      (RelFieldOfNorms.stageMap K L M M' t N).toRingHom) ?_
  intro N P hNP x
  change RelFieldOfNorms.of K L M' (FiniteIntermediateField.map t P)
      (RelFieldOfNorms.stageMap K L M M' t P
        (RelFieldOfNorms.transition K L M N P hNP x)) = _
  rw [RelFieldOfNorms.stageMap_transition, RelFieldOfNorms.of_transition]
  rfl

/-- Evaluation on an original finite family is the literal finite-image formula. -/
@[simp]
theorem RelFieldOfNorms.map_of (N : FiniteIntermediateField L M) (x : FieldOfNorms K N.val) :
    RelFieldOfNorms.map K L M M' t
        (RelFieldOfNorms.of K L M N x) =
      RelFieldOfNorms.of K L M' (FiniteIntermediateField.map t N)
        (RelFieldOfNorms.stageMap K L M M' t N x) := rfl

/-- The original unital finite-stage maps induce an embedding of the actual fields. -/
theorem RelFieldOfNorms.map_injective :
    Function.Injective (RelFieldOfNorms.map K L M M' t) := by
  exact (RelFieldOfNorms.map K L M M' t).injective

/-- The induced union map fixes the original base norm field. -/
theorem RelFieldOfNorms.map_base (x : FieldOfNorms K L) :
    RelFieldOfNorms.map K L M M' t
        (RelFieldOfNorms.baseHom K L M x) =
      RelFieldOfNorms.baseHom K L M' x := by
  rw [← RelFieldOfNorms.of_base K L M FiniteIntermediateField.bottom x,
    RelFieldOfNorms.map_of, RelFieldOfNorms.stageMap_base, RelFieldOfNorms.of_base]

/-- The actual induced embedding preserves the canonical rational union valuation. -/
theorem RelFieldOfNorms.map_valuation (z : RelFieldOfNorms K L M) :
    RelFieldOfNorms.valuation K L M'
        (RelFieldOfNorms.map K L M M' t z) =
      RelFieldOfNorms.valuation K L M z := by
  obtain ⟨N, x, rfl⟩ := RelFieldOfNorms._exists_stage K L M z
  rw [RelFieldOfNorms.map_of, RelFieldOfNorms.valuation_of,
    RelFieldOfNorms.valuation_of, RelFieldOfNorms.stageMap_valuation]

/-- The actual induced map is an algebra embedding over the original base norm field. -/
def RelFieldOfNorms.algMap :
    RelFieldOfNorms K L M →ₐ[FieldOfNorms K L]
      RelFieldOfNorms K L M' := by
  exact { RelFieldOfNorms.map K L M M' t with
    commutes' := RelFieldOfNorms.map_base K L M M' t }

/-- Algebra bundling preserves the same literal map on the same union carrier. -/
@[simp]
theorem RelFieldOfNorms.algMap_apply (z : RelFieldOfNorms K L M) :
    RelFieldOfNorms.algMap K L M M' t z =
      RelFieldOfNorms.map K L M M' t z := rfl

/-- Equal actual image stages and equal ambient transports give the same union element. -/
theorem RelFieldOfNorms.of_transport_congr {D : Type*} [Field D] [Algebra K D]
    (P Q : FiniteIntermediateField L M') (e : D ≃ₐ[K] P.val) (f : D ≃ₐ[K] Q.val)
    (hPQ : P = Q) (hef : ∀ a : D, (e a : M') = (f a : M'))
    (x : FieldOfNorms K D) :
    RelFieldOfNorms.of K L M' P (FieldOfNorms.map e x) =
      RelFieldOfNorms.of K L M' Q (FieldOfNorms.map f x) := by
  subst Q
  have heq : e = f := by
    apply AlgEquiv.ext
    intro a
    exact Subtype.ext (hef a)
  rw [heq]

/-- The actual identity extension embedding induces the identity on the same union. -/
@[simp]
theorem RelFieldOfNorms.map_id :
    RelFieldOfNorms.map K L M M (AlgHom.id L M) =
      RingHom.id (RelFieldOfNorms K L M) := by
  apply RingHom.ext
  intro z
  obtain ⟨N, x, rfl⟩ := RelFieldOfNorms._exists_stage K L M z
  change RelFieldOfNorms.map K L M M (AlgHom.id L M)
      (RelFieldOfNorms.of K L M N x) =
    RelFieldOfNorms.of K L M N x
  rw [RelFieldOfNorms.map_of, RelFieldOfNorms.stageMap_apply]
  calc
    _ = RelFieldOfNorms.of K L M N
        (FieldOfNorms.map (AlgEquiv.refl : N.val ≃ₐ[K] N.val) x) := by
      apply RelFieldOfNorms.of_transport_congr
      · exact FiniteIntermediateField.map_id N
      · intro a
        rfl
    _ = _ := by rw [FieldOfNorms.map_refl]

variable (M'' : Type*) [Field M''] [Algebra K M''] [Algebra L M'']
    [IsScalarTower K L M''] [Algebra.IsSeparable L M'']
variable (s : M' →ₐ[L] M'')

/-- Actual composition of ambient embeddings gives composition of the same union maps. -/
theorem RelFieldOfNorms.map_comp :
    (RelFieldOfNorms.map K L M' M'' s).comp
        (RelFieldOfNorms.map K L M M' t) =
      RelFieldOfNorms.map K L M M'' (s.comp t) := by
  apply RingHom.ext
  intro z
  obtain ⟨N, x, rfl⟩ := RelFieldOfNorms._exists_stage K L M z
  change RelFieldOfNorms.map K L M' M'' s
      (RelFieldOfNorms.map K L M M' t
        (RelFieldOfNorms.of K L M N x)) = _
  rw [RelFieldOfNorms.map_of, RelFieldOfNorms.map_of, RelFieldOfNorms.map_of]
  simp only [RelFieldOfNorms.stageMap_apply]
  rw [FieldOfNorms.map_trans]
  apply RelFieldOfNorms.of_transport_congr
  · exact FiniteIntermediateField.map_map t s N
  · intro a
    rfl

end Embeddings

end FontaineWintenberger

noncomputable section

namespace FontaineWintenberger

universe u v w w' w'' z

variable (K : Type u) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : Type v) (M : Type w) (N : Type w') [Field L] [Field M] [Field N]
    [Algebra K L] [Algebra K M] [Algebra K N] [Algebra L M] [Algebra L N]
    [IsScalarTower K L M] [IsScalarTower K L N]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable L M] [Algebra.IsSeparable L N]
variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- An original algebra isomorphism induces the original isomorphism of the same unions. -/
def RelFieldOfNorms.congr (e : M ≃ₐ[L] N) :
    RelFieldOfNorms K L M ≃ₐ[FieldOfNorms K L]
      RelFieldOfNorms K L N := by
  refine AlgEquiv.ofAlgHom
    (RelFieldOfNorms.algMap K L M N e.toAlgHom)
    (RelFieldOfNorms.algMap K L N M e.symm.toAlgHom) ?_ ?_
  · apply AlgHom.ext
    intro x
    change RelFieldOfNorms.map K L M N e.toAlgHom
      (RelFieldOfNorms.map K L N M e.symm.toAlgHom x) = x
    have h := congrArg
      (fun f : RelFieldOfNorms K L N →+*
        RelFieldOfNorms K L N => f x)
      (RelFieldOfNorms.map_comp K L N M e.symm.toAlgHom N e.toAlgHom)
    simpa only [RingHom.comp_apply, AlgEquiv.comp_symm, RelFieldOfNorms.map_id,
      RingHom.id_apply] using h
  · apply AlgHom.ext
    intro x
    change RelFieldOfNorms.map K L N M e.symm.toAlgHom
      (RelFieldOfNorms.map K L M N e.toAlgHom x) = x
    have h := congrArg
      (fun f : RelFieldOfNorms K L M →+*
        RelFieldOfNorms K L M => f x)
      (RelFieldOfNorms.map_comp K L M N e.toAlgHom M e.symm.toAlgHom)
    simpa only [RingHom.comp_apply, AlgEquiv.symm_comp, RelFieldOfNorms.map_id,
      RingHom.id_apply] using h

/-- The comparison has exactly the original induced algebra homomorphism. -/
@[simp]
theorem RelFieldOfNorms.congr_toAlgHom (e : M ≃ₐ[L] N) :
    (RelFieldOfNorms.congr K L M N e).toAlgHom =
      RelFieldOfNorms.algMap K L M N e.toAlgHom := rfl

/-- The comparison acts by the original map on the original union carrier. -/
@[simp]
theorem RelFieldOfNorms.congr_apply (e : M ≃ₐ[L] N)
    (x : RelFieldOfNorms K L M) :
    RelFieldOfNorms.congr K L M N e x =
      RelFieldOfNorms.map K L M N e.toAlgHom x := rfl

/-- The inverse comparison is induced by the original inverse isomorphism. -/
@[simp]
theorem RelFieldOfNorms.congr_symm_apply (e : M ≃ₐ[L] N)
    (x : RelFieldOfNorms K L N) :
    (RelFieldOfNorms.congr K L M N e).symm x =
      RelFieldOfNorms.map K L N M e.symm.toAlgHom x := rfl

/-- The actual union comparison preserves the original rational valuation. -/
theorem RelFieldOfNorms.congr_valuation (e : M ≃ₐ[L] N)
    (x : RelFieldOfNorms K L M) :
    RelFieldOfNorms.valuation K L N
        (RelFieldOfNorms.congr K L M N e x) =
      RelFieldOfNorms.valuation K L M x :=
  RelFieldOfNorms.map_valuation K L M N e.toAlgHom x

/-- The identity original isomorphism acts as the identity on the actual union. -/
@[simp]
theorem RelFieldOfNorms.congr_refl_apply
    (x : RelFieldOfNorms K L M) :
    RelFieldOfNorms.congr K L M M (AlgEquiv.refl : M ≃ₐ[L] M) x = x := by
  change RelFieldOfNorms.map K L M M (AlgHom.id L M) x = x
  exact DFunLike.congr_fun (RelFieldOfNorms.map_id K L M) x

variable (P : Type w'') [Field P] [Algebra K P] [Algebra L P]
    [IsScalarTower K L P] [Algebra.IsSeparable L P]

/-- The actual comparison of a composite is the composite of the actual comparisons. -/
theorem RelFieldOfNorms.congr_trans_apply (e : M ≃ₐ[L] N) (f : N ≃ₐ[L] P)
    (x : RelFieldOfNorms K L M) :
    RelFieldOfNorms.congr K L M P (e.trans f) x =
      RelFieldOfNorms.congr K L N P f
        (RelFieldOfNorms.congr K L M N e x) := by
  change RelFieldOfNorms.map K L M P (f.toAlgHom.comp e.toAlgHom) x =
    RelFieldOfNorms.map K L N P f.toAlgHom
      (RelFieldOfNorms.map K L M N e.toAlgHom x)
  exact (DFunLike.congr_fun
    (RelFieldOfNorms.map_comp K L M N e.toAlgHom P f.toAlgHom) x).symm

/-- The actual union of a universe-lifted original extension is canonically the same field. -/
abbrev RelFieldOfNorms.uLiftEquiv :
    letI : Algebra.IsSeparable L (ULift.{z} M) :=
      AlgEquiv.Algebra.isSeparable (ULift.algEquiv.{v, w, z} (R := L) (A := M)).symm
    RelFieldOfNorms K L (ULift.{z} M) ≃ₐ[FieldOfNorms K L]
      RelFieldOfNorms K L M := by
  letI : Algebra.IsSeparable L (ULift.{z} M) :=
    AlgEquiv.Algebra.isSeparable (ULift.algEquiv.{v, w, z} (R := L) (A := M)).symm
  exact RelFieldOfNorms.congr K L (ULift.{z} M) M
    ULift.algEquiv.{v, w, z}

end FontaineWintenberger
