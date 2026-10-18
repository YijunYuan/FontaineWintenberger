/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.FiniteSeparable
public import FontaineWintenberger.FieldOfNorms.FiniteFunctorLaws
public import FontaineWintenberger.FieldOfNorms.FiniteNaturality
public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.Data.Fintype.Order
public import Mathlib.Algebra.Order.GroupWithZero.Canonical

/-!
# Directed unions of the original finite norm fields

The stages are the original norm fields of actual finite intermediate fields
over the given infinite APF extension. The transition maps are the already
constructed original finite-inclusion maps. Mathlib's directed colimit supplies
the single union carrier.

Reference: Wintenberger, paragraph 3.2.1. The compatible union valuation uses
the rational normalization of the proved finite-stage valuation exponents.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

section Fields

variable (K L M : Type*) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/-- No finite stage over the infinite original extension is finite over `K`. -/
theorem separableNormUnionStage_infinite [Fact (¬ Module.Finite K L)]
    (N : FiniteLayer L M) : ¬ Module.Finite K N.val := by
  intro h
  let : Module.Finite K N.val := h
  exact (Fact.out : ¬ Module.Finite K L) (FiniteDimensional.of_injective
    (IsScalarTower.toAlgHom K L N.val).toLinearMap (algebraMap L N.val).injective)

instance separableNormUnionStage_fact_infinite [Fact (¬ Module.Finite K L)]
    (N : FiniteLayer L M) : Fact (¬ Module.Finite K N.val) :=
  ⟨separableNormUnionStage_infinite K L M N⟩

/-- An ambient extension of the infinite original extension is infinite over `K`. -/
theorem separableNormUnion_ambient_infinite [Fact (¬ Module.Finite K L)] :
    ¬ Module.Finite K M := by
  intro h
  let : Module.Finite K M := h
  exact (Fact.out : ¬ Module.Finite K L) (FiniteDimensional.of_injective
    (IsScalarTower.toAlgHom K L M).toLinearMap (algebraMap L M).injective)

end Fields

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
variable (L M : Type*) [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable L M]

/-- Every actual finite stage over `L` remains separable over the original base. -/
local instance normUnionStageSeparable (N : FiniteLayer L M) :
    Algebra.IsSeparable K N.val := Algebra.IsSeparable.trans K L N.val

omit [PerfectField (IsLocalRing.ResidueField
  (NormedField.valuation (K := K)).valuationSubring)] in
/-- Finite extension of the original APF extension supplies APF at every stage. -/
instance separableNormUnionStage_isAPF [IsAPF K L] (N : FiniteLayer L M) :
    IsAPF K N.val :=
  (isAPF_finite_extension_iff K N.val L).mpr ‹_›

variable (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]
variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- The field structure at each stage is exactly its existing original norm field. -/
abbrev separableNormUnionStageField (N : FiniteLayer L M) : Field (NormLimit K N.val) :=
  normLimitField K N.val p

/-- The transition homomorphism is the existing original finite-inclusion map. -/
def separableNormUnionTransition (N P : FiniteLayer L M) (h : N ≤ P) :
    letI := separableNormUnionStageField K L M p N
    letI := separableNormUnionStageField K L M p P
    NormLimit K N.val →+* NormLimit K P.val := by
  letI := separableNormUnionStageField K L M p N
  letI := separableNormUnionStageField K L M p P
  letI : Algebra N.val P.val := (IntermediateField.inclusion h).toRingHom.toAlgebra
  letI : IsScalarTower L N.val P.val := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower K N.val P.val := IsScalarTower.of_algebraMap_eq' rfl
  letI : Module.Finite N.val P.val := Module.Finite.right L N.val P.val
  letI : Algebra.IsSeparable N.val P.val :=
    Algebra.isSeparable_tower_top_of_isSeparable L N.val P.val
  exact finiteNormLimitRingHom K N.val P.val p

/-- The original identity law is retained at the actual finite stage. -/
@[simp]
theorem separableNormUnionTransition_self (N : FiniteLayer L M) :
    letI := separableNormUnionStageField K L M p N
    separableNormUnionTransition K L M p N N le_rfl =
      RingHom.id (NormLimit K N.val) := by
  let := separableNormUnionStageField K L M p N
  apply RingHom.ext
  intro x
  exact finiteNormLimitMap_refl K N.val x

/-- Composition retains the original finite norm-family maps in the same tower. -/
theorem separableNormUnionTransition_comp (N P Q : FiniteLayer L M)
    (hNP : N ≤ P) (hPQ : P ≤ Q) :
    letI := separableNormUnionStageField K L M p N
    letI := separableNormUnionStageField K L M p P
    letI := separableNormUnionStageField K L M p Q
    (separableNormUnionTransition K L M p P Q hPQ).comp
        (separableNormUnionTransition K L M p N P hNP) =
      separableNormUnionTransition K L M p N Q (hNP.trans hPQ) := by
  let := separableNormUnionStageField K L M p N
  let := separableNormUnionStageField K L M p P
  let := separableNormUnionStageField K L M p Q
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
  exact finiteNormLimitMap_trans K N.val P.val Q.val x

/-- The proved original identity and composition laws give the directed system. -/
instance separableNormUnionDirectedSystem :
    DirectedSystem (fun N : FiniteLayer L M => NormLimit K N.val)
      (separableNormUnionTransition K L M p · · ·) where
  map_self {i} x := by
    let := separableNormUnionStageField K L M p i
    exact congrArg (fun f : NormLimit K i.val →+* NormLimit K i.val => f x)
      (separableNormUnionTransition_self K L M p i)
  map_map {k j i} hij hjk x := by
    let := separableNormUnionStageField K L M p i
    let := separableNormUnionStageField K L M p j
    let := separableNormUnionStageField K L M p k
    exact congrArg (fun f : NormLimit K i.val →+* NormLimit K k.val => f x)
      (separableNormUnionTransition_comp K L M p i j k hij hjk)

/-- The single canonical directed colimit of the original finite norm fields. -/
abbrev SeparableNormUnion :=
  DirectLimit (fun N : FiniteLayer L M => NormLimit K N.val)
    (separableNormUnionTransition K L M p)

/-- Mathlib's field structure on this directed colimit of the original fields. -/
abbrev separableNormUnionField : Field (SeparableNormUnion K L M p) := by
  letI (N : FiniteLayer L M) : Field (NormLimit K N.val) :=
    separableNormUnionStageField K L M p N
  exact inferInstanceAs (Field (DirectLimit (fun N : FiniteLayer L M => NormLimit K N.val)
    (separableNormUnionTransition K L M p)))

/-- The canonical structural embedding of an original finite-stage norm field. -/
def separableNormUnionOf (N : FiniteLayer L M) :
    letI := separableNormUnionStageField K L M p N
    letI := separableNormUnionField K L M p
    NormLimit K N.val →+* SeparableNormUnion K L M p := by
  letI (P : FiniteLayer L M) : Field (NormLimit K P.val) :=
    separableNormUnionStageField K L M p P
  letI := separableNormUnionField K L M p
  exact DirectLimit.Ring.of (fun P : FiniteLayer L M => NormLimit K P.val)
    (separableNormUnionTransition K L M p) N

/-- Every original finite-stage structural map is injective. -/
theorem separableNormUnionOf_injective (N : FiniteLayer L M) :
    Function.Injective (separableNormUnionOf K L M p N) := by
  let := separableNormUnionStageField K L M p N
  let := separableNormUnionField K L M p
  exact (separableNormUnionOf K L M p N).injective

/-- Structural embeddings identify each original transition with its source. -/
theorem separableNormUnionOf_transition (N P : FiniteLayer L M) (hNP : N ≤ P)
    (x : NormLimit K N.val) :
    separableNormUnionOf K L M p P
        (separableNormUnionTransition K L M p N P hNP x) =
      separableNormUnionOf K L M p N x := by
  let (Q : FiniteLayer L M) : Field (NormLimit K Q.val) :=
    separableNormUnionStageField K L M p Q
  let := separableNormUnionField K L M p
  exact DirectLimit.Ring.of_f
    (f := separableNormUnionTransition K L M p) hNP x

/-- Every union element is represented by an actual original finite-stage family. -/
theorem separableNormUnion_exists_stage (z : SeparableNormUnion K L M p) :
    ∃ (N : FiniteLayer L M) (x : NormLimit K N.val),
      separableNormUnionOf K L M p N x = z := by
  obtain ⟨N, x, hx⟩ := DirectLimit.exists_eq_mk
    (separableNormUnionTransition K L M p) z
  exact ⟨N, x, hx.symm⟩

/-- Any finite family of union elements lies in one actual original finite stage. -/
theorem separableNormUnion_exists_finiteStage {α : Type*} [Finite α]
    (z : α → SeparableNormUnion K L M p) :
    ∃ (N : FiniteLayer L M) (x : α → NormLimit K N.val),
      ∀ a, separableNormUnionOf K L M p N (x a) = z a := by
  classical
  choose N x hx using fun a => separableNormUnion_exists_stage K L M p (z a)
  obtain ⟨P, hP⟩ := Finite.exists_le N
  refine ⟨P, fun a => separableNormUnionTransition K L M p
    (N a) P (hP a) (x a), ?_⟩
  intro a
  exact (separableNormUnionOf_transition K L M p (N a) P (hP a) (x a)).trans
    (hx a)

/-- Every polynomial over the union descends along an actual finite-stage embedding. -/
theorem separableNormUnion_exists_polynomial :
    letI := separableNormUnionField K L M p
    ∀ F : Polynomial (SeparableNormUnion K L M p),
      ∃ N : FiniteLayer L M,
        letI := separableNormUnionStageField K L M p N
        ∃ f : Polynomial (NormLimit K N.val),
          f.map (separableNormUnionOf K L M p N) = F := by
  let (N : FiniteLayer L M) : Field (NormLimit K N.val) :=
    separableNormUnionStageField K L M p N
  let := separableNormUnionField K L M p
  intro F
  obtain ⟨N, x, hx⟩ := separableNormUnion_exists_finiteStage K L M p
    (fun a : F.coeffs => (a : SeparableNormUnion K L M p))
  have hm : F ∈ Polynomial.lifts (separableNormUnionOf K L M p N) :=
    (Polynomial.lifts_iff_coeffs_subset_range F).mpr (by
      intro a ha
      exact ⟨x ⟨a, ha⟩, hx ⟨a, ha⟩⟩)
  obtain ⟨f, hf⟩ := (Polynomial.mem_lifts F).mp hm
  exact ⟨N, f, hf⟩

/-- The original finite-inclusion map from the base norm field to a stage. -/
def separableNormUnionBaseToStage (N : FiniteLayer L M) :
    letI := normLimitField K L p
    letI := separableNormUnionStageField K L M p N
    NormLimit K L →+* NormLimit K N.val := by
  letI := normLimitField K L p
  letI := separableNormUnionStageField K L M p N
  exact finiteNormLimitRingHom K L N.val p

/-- Transition maps commute with the actual finite maps from the base field. -/
theorem separableNormUnionTransition_base (N P : FiniteLayer L M) (hNP : N ≤ P) :
    letI := normLimitField K L p
    letI := separableNormUnionStageField K L M p N
    letI := separableNormUnionStageField K L M p P
    (separableNormUnionTransition K L M p N P hNP).comp
        (separableNormUnionBaseToStage K L M p N) =
      separableNormUnionBaseToStage K L M p P := by
  let := normLimitField K L p
  let := separableNormUnionStageField K L M p N
  let := separableNormUnionStageField K L M p P
  let : Algebra N.val P.val := (IntermediateField.inclusion hNP).toRingHom.toAlgebra
  let : IsScalarTower L N.val P.val := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K N.val P.val := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite N.val P.val := Module.Finite.right L N.val P.val
  let : Algebra.IsSeparable N.val P.val :=
    Algebra.isSeparable_tower_top_of_isSeparable L N.val P.val
  apply RingHom.ext
  intro x
  exact finiteNormLimitMap_trans K L N.val P.val x

/-- The canonical base embedding into the same directed union. -/
def separableNormUnionBaseHom :
    letI := normLimitField K L p
    letI := separableNormUnionField K L M p
    NormLimit K L →+* SeparableNormUnion K L M p := by
  letI := normLimitField K L p
  letI := separableNormUnionField K L M p
  letI := separableNormUnionStageField K L M p (FiniteLayer.bottom)
  exact (separableNormUnionOf K L M p (FiniteLayer.bottom)).comp
    (separableNormUnionBaseToStage K L M p (FiniteLayer.bottom))

/-- Every finite-stage structural embedding gives that same actual base map. -/
theorem separableNormUnionOf_base (N : FiniteLayer L M) (x : NormLimit K L) :
    separableNormUnionOf K L M p N
        (separableNormUnionBaseToStage K L M p N x) =
      separableNormUnionBaseHom K L M p x := by
  let := normLimitField K L p
  let := separableNormUnionField K L M p
  let := separableNormUnionStageField K L M p N
  let := separableNormUnionStageField K L M p (FiniteLayer.bottom)
  have hc := congrArg (fun f : NormLimit K L →+* NormLimit K N.val => f x)
    (separableNormUnionTransition_base K L M p
      (FiniteLayer.bottom) N (FiniteLayer.bottom_le N))
  change separableNormUnionOf K L M p N
      (separableNormUnionBaseToStage K L M p N x) =
    separableNormUnionOf K L M p (FiniteLayer.bottom)
      (separableNormUnionBaseToStage K L M p (FiniteLayer.bottom) x)
  rw [← hc]
  exact separableNormUnionOf_transition K L M p (FiniteLayer.bottom) N
    (FiniteLayer.bottom_le N) _

/-- The finite-stage algebra is induced by its original finite norm-field map. -/
abbrev separableNormUnionStageAlgebra (N : FiniteLayer L M) :
    letI := normLimitField K L p
    letI := separableNormUnionStageField K L M p N
    Algebra (NormLimit K L) (NormLimit K N.val) := by
  letI := normLimitField K L p
  letI := separableNormUnionStageField K L M p N
  exact (separableNormUnionBaseToStage K L M p N).toAlgebra

/-- The sole base algebra structure comes from the canonical original base map. -/
abbrev separableNormUnionAlgebra :
    letI := normLimitField K L p
    letI := separableNormUnionField K L M p
    Algebra (NormLimit K L) (SeparableNormUnion K L M p) := by
  letI := normLimitField K L p
  letI := separableNormUnionField K L M p
  exact (separableNormUnionBaseHom K L M p).toAlgebra

/-- The original finite-stage embedding as an algebra homomorphism over the base. -/
def separableNormUnionOfAlgHom (N : FiniteLayer L M) :
    letI := normLimitField K L p
    letI := separableNormUnionStageField K L M p N
    letI := separableNormUnionField K L M p
    letI := separableNormUnionStageAlgebra K L M p N
    letI := separableNormUnionAlgebra K L M p
    NormLimit K N.val →ₐ[NormLimit K L] SeparableNormUnion K L M p := by
  letI := normLimitField K L p
  letI := separableNormUnionStageField K L M p N
  letI := separableNormUnionField K L M p
  letI := separableNormUnionStageAlgebra K L M p N
  letI := separableNormUnionAlgebra K L M p
  exact { separableNormUnionOf K L M p N with
    commutes' := separableNormUnionOf_base K L M p N }

/-- Actual finite-stage separability makes the same union separable algebraic. -/
theorem separableNormUnion_isSeparable :
    letI := normLimitField K L p
    letI := separableNormUnionField K L M p
    letI := separableNormUnionAlgebra K L M p
    Algebra.IsSeparable (NormLimit K L) (SeparableNormUnion K L M p) := by
  let := normLimitField K L p
  let := separableNormUnionField K L M p
  let := separableNormUnionAlgebra K L M p
  constructor
  intro z
  obtain ⟨N, x, rfl⟩ := separableNormUnion_exists_stage K L M p z
  let := separableNormUnionStageField K L M p N
  let := separableNormUnionStageAlgebra K L M p N
  let : Algebra.IsSeparable (NormLimit K L) (NormLimit K N.val) :=
    (finiteNormLimit_finite_separable_degree K L N.val p
      ).2.1
  exact IsSeparable.map (separableNormUnionOfAlgHom K L M p N)
    (separableNormUnionOfAlgHom K L M p N).injective
    (Algebra.IsSeparable.isSeparable (NormLimit K L) x)

/-- Rational rescaling of the existing integer valuation group, with zero preserved. -/
def separableNormUnionValueMap (e : ℕ) :
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
theorem separableNormUnionValueMap_exp (e : ℕ) (z : ℤ) :
    separableNormUnionValueMap e (WithZero.exp z) =
      WithZero.exp ((z : ℚ) / (e : ℚ)) := rfl

/-- Rational normalization cancels a positive finite-inclusion scaling exponent. -/
theorem separableNormUnionValueMap_pow (e c : ℕ) (he : 0 < e) (hc : 0 < c)
    (x : WithZero (Multiplicative ℤ)) :
    separableNormUnionValueMap (e * c) (x ^ c) = separableNormUnionValueMap e x := by
  induction x using WithZero.recZeroCoe with
  | zero => simp [Nat.ne_of_gt hc]
  | coe x =>
      change separableNormUnionValueMap (e * c) ((WithZero.exp x.toAdd) ^ c) =
        separableNormUnionValueMap e (WithZero.exp x.toAdd)
      rw [← WithZero.exp_nsmul, separableNormUnionValueMap_exp,
        separableNormUnionValueMap_exp]
      congr 1
      have he' : (e : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt he)
      have hc' : (c : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hc)
      push_cast
      field_simp
      simp only [nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]

/-- The actual positive scaling exponent of the original finite map from the base. -/
def separableNormUnionStageExponent (N : FiniteLayer L M) : ℕ :=
  Classical.choose (exists_finiteNormLimitMap_valuation_scaling K L N.val
    )

omit [Fact (¬ Module.Finite K L)] in
/-- Positivity is supplied by the original finite-embedding theorem. -/
theorem separableNormUnionStageExponent_pos (N : FiniteLayer L M) :
    0 < separableNormUnionStageExponent K L M N :=
  (Classical.choose_spec (exists_finiteNormLimitMap_valuation_scaling K L N.val
    )).1

omit [Fact (¬ Module.Finite K L)] in
/-- The chosen exponent satisfies the proved original finite-map valuation identity. -/
theorem separableNormUnionStageExponent_spec (N : FiniteLayer L M) (x : NormLimit K L) :
    normLimitValuation K N.val
        (finiteNormLimitMap K L N.val x) =
      normLimitValuation K L x ^ separableNormUnionStageExponent K L M N :=
  (Classical.choose_spec (exists_finiteNormLimitMap_valuation_scaling K L N.val
    )).2 x

include p in
/-- The original base uniformizer makes the finite-stage scaling exponent unique. -/
theorem separableNormUnionStageExponent_unique (N : FiniteLayer L M) (c : ℕ)
    (hc : ∀ x : NormLimit K L,
      normLimitValuation K N.val
        (finiteNormLimitMap K L N.val x) = normLimitValuation K L x ^ c) :
    c = separableNormUnionStageExponent K L M N := by
  have h := (hc (normLimitUniformizer K L p)).symm.trans
    (separableNormUnionStageExponent_spec K L M N
      (normLimitUniformizer K L p))
  rw [normLimitValuation_normLimitUniformizer, ← WithZero.exp_nsmul,
    ← WithZero.exp_nsmul] at h
  have hn := WithZero.exp_injective h
  simp only [nsmul_eq_mul, mul_neg, mul_one] at hn
  exact_mod_cast neg_injective hn

/-- The genuine relative scaling exponent also gives the base-exponent cocycle. -/
theorem separableNormUnionTransition_valuation_scaling (N P : FiniteLayer L M)
    (hNP : N ≤ P) :
    ∃ c : ℕ, 0 < c ∧
      separableNormUnionStageExponent K L M P =
        separableNormUnionStageExponent K L M N * c ∧
      ∀ x : NormLimit K N.val,
        normLimitValuation K P.val
            (separableNormUnionTransition K L M p N P hNP x) =
          normLimitValuation K N.val x ^ c := by
  let : Algebra N.val P.val := (IntermediateField.inclusion hNP).toRingHom.toAlgebra
  let : IsScalarTower L N.val P.val := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K N.val P.val := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite N.val P.val := Module.Finite.right L N.val P.val
  let : Algebra.IsSeparable N.val P.val :=
    Algebra.isSeparable_tower_top_of_isSeparable L N.val P.val
  obtain ⟨c, hc, hv⟩ := exists_finiteNormLimitMap_valuation_scaling K N.val P.val
  refine ⟨c, hc, ?_, hv⟩
  apply (separableNormUnionStageExponent_unique K L M p P
    (separableNormUnionStageExponent K L M N * c) ?_).symm
  intro x
  rw [← finiteNormLimitMap_trans K L N.val P.val x, hv,
    separableNormUnionStageExponent_spec, pow_mul]

/-- The original stage valuation, rationally normalized over the base norm field. -/
def separableNormUnionStageValuation (N : FiniteLayer L M) :
    letI := separableNormUnionStageField K L M p N
    Valuation (NormLimit K N.val) (WithZero (Multiplicative ℚ)) := by
  letI := separableNormUnionStageField K L M p N
  exact (normLimitFieldValuation K N.val p
    ).map
      (separableNormUnionValueMap (separableNormUnionStageExponent K L M N))

/-- The rational stage valuation is computed from the same original integer valuation. -/
@[simp]
theorem separableNormUnionStageValuation_apply (N : FiniteLayer L M)
    (x : NormLimit K N.val) :
    separableNormUnionStageValuation K L M p N x =
      separableNormUnionValueMap (separableNormUnionStageExponent K L M N)
        (normLimitValuation K N.val x) := rfl

/-- The rationally normalized valuations are strictly compatible with actual transitions. -/
theorem separableNormUnionStageValuation_transition (N P : FiniteLayer L M)
    (hNP : N ≤ P) (x : NormLimit K N.val) :
    separableNormUnionStageValuation K L M p P
        (separableNormUnionTransition K L M p N P hNP x) =
      separableNormUnionStageValuation K L M p N x := by
  obtain ⟨c, hc, he, hv⟩ := separableNormUnionTransition_valuation_scaling
    K L M p N P hNP
  rw [separableNormUnionStageValuation_apply, separableNormUnionStageValuation_apply,
    hv x, he]
  exact separableNormUnionValueMap_pow _ _ (separableNormUnionStageExponent_pos K L M N)
    hc _

/-- Every normalized finite-stage valuation extends the original base valuation. -/
theorem separableNormUnionStageValuation_base (N : FiniteLayer L M) (x : NormLimit K L) :
    separableNormUnionStageValuation K L M p N
        (separableNormUnionBaseToStage K L M p N x) =
      separableNormUnionValueMap 1 (normLimitValuation K L x) := by
  rw [separableNormUnionStageValuation_apply]
  change separableNormUnionValueMap (separableNormUnionStageExponent K L M N)
      (normLimitValuation K N.val
        (finiteNormLimitMap K L N.val x)) = _
  rw [separableNormUnionStageExponent_spec]
  simpa only [one_mul] using separableNormUnionValueMap_pow 1
    (separableNormUnionStageExponent K L M N) (by decide)
    (separableNormUnionStageExponent_pos K L M N) (normLimitValuation K L x)

/-- The strictly compatible rational valuations descend on the same canonical union. -/
def separableNormUnionValuation :
    letI := separableNormUnionField K L M p
    Valuation (SeparableNormUnion K L M p) (WithZero (Multiplicative ℚ)) := by
  letI (N : FiniteLayer L M) : Field (NormLimit K N.val) :=
    separableNormUnionStageField K L M p N
  letI := separableNormUnionField K L M p
  let f := separableNormUnionTransition K L M p
  let v := separableNormUnionStageValuation K L M p
  let addUnion : Add (SeparableNormUnion K L M p) :=
    (separableNormUnionField K L M p).toAdd
  let hv : ∀ (N P : FiniteLayer L M) (hNP : N ≤ P) (x : NormLimit K N.val),
      v N x = v P (f N P hNP x) := fun N P hNP x =>
    (separableNormUnionStageValuation_transition K L M p N P hNP x).symm
  refine
    { toFun := DirectLimit.lift f (fun N => v N) hv
      map_zero' := DirectLimit.lift_zero (f := f) v hv
      map_one' := DirectLimit.lift_one (f := f) v hv
      map_mul' := DirectLimit.lift_mul (f := f) v hv
      map_add_le_max' := ?_ }
  intro x y
  refine DirectLimit.induction₂ f (fun N a b => ?_) x y
  have hs : @Add.add (SeparableNormUnion K L M p) addUnion
        (separableNormUnionOf K L M p N a)
        (separableNormUnionOf K L M p N b) =
      separableNormUnionOf K L M p N (a + b) :=
    ((separableNormUnionOf K L M p N).map_add a b).symm
  change DirectLimit.lift f (fun N => v N) hv
      (@Add.add (SeparableNormUnion K L M p) addUnion
        (separableNormUnionOf K L M p N a)
        (separableNormUnionOf K L M p N b)) ≤ _
  rw [hs]
  exact (v N).map_add a b

/-- The descended valuation retains its exact original finite-stage formula. -/
@[simp]
theorem separableNormUnionValuation_of (N : FiniteLayer L M) (x : NormLimit K N.val) :
    separableNormUnionValuation K L M p
        (separableNormUnionOf K L M p N x) =
      separableNormUnionStageValuation K L M p N x := rfl

/-- The same union valuation extends the original valuation on the base norm field. -/
theorem separableNormUnionValuation_base (x : NormLimit K L) :
    separableNormUnionValuation K L M p
        (separableNormUnionBaseHom K L M p x) =
      separableNormUnionValueMap 1 (normLimitValuation K L x) := by
  rw [← separableNormUnionOf_base K L M p (FiniteLayer.bottom) x,
    separableNormUnionValuation_of, separableNormUnionStageValuation_base]

/-- The canonical valuation equips the same original union with its valuation topology. -/
@[instance_reducible]
def separableNormUnionValued :
    letI := separableNormUnionField K L M p
    Valued (SeparableNormUnion K L M p) (WithZero (Multiplicative ℚ)) := by
  letI := separableNormUnionField K L M p
  exact Valued.mk' (separableNormUnionValuation K L M p)

section FiniteAmbient

variable [Module.Finite L M]


/-- The terminal finite stage is the entire given finite extension. -/
abbrev separableNormUnionTop : FiniteLayer L M := ⟨⊤, inferInstance⟩

local instance top_isSeparable : Algebra.IsSeparable K (⊤ : IntermediateField L M) :=
  Algebra.IsSeparable.trans K L (⊤ : IntermediateField L M)
local instance top_isAPF : IsAPF K (⊤ : IntermediateField L M) :=
  separableNormUnionStage_isAPF K L M (separableNormUnionTop L M)
local instance top_fact_infinite : Fact (¬ Module.Finite K (⊤ : IntermediateField L M)) :=
  ⟨separableNormUnionStage_infinite K L M (separableNormUnionTop L M)⟩

/-- The actual terminal structural map is bijective, without changing the union. -/
theorem separableNormUnionOf_top_bijective : Function.Bijective
    (separableNormUnionOf K L M p (separableNormUnionTop L M)) := by
  refine ⟨separableNormUnionOf_injective K L M p _, ?_⟩
  intro z
  obtain ⟨N, x, hx⟩ := separableNormUnion_exists_stage K L M p z
  have hNT : N ≤ separableNormUnionTop L M :=
    show N.val ≤ (⊤ : IntermediateField L M) from le_top
  refine ⟨separableNormUnionTransition K L M p N
    (separableNormUnionTop L M) hNT x, ?_⟩
  exact (separableNormUnionOf_transition K L M p N
    (separableNormUnionTop L M) hNT x).trans hx

/-- For a finite ambient extension, its terminal norm field is the same union. -/
def separableNormUnionTopEquiv :
    letI := separableNormUnionStageField K L M p (separableNormUnionTop L M)
    letI := separableNormUnionField K L M p
    letI : Add (SeparableNormUnion K L M p) :=
      (separableNormUnionField K L M p).toAdd
    letI : Mul (SeparableNormUnion K L M p) :=
      (separableNormUnionField K L M p).toMul
    NormLimit K (separableNormUnionTop L M).val ≃+*
      SeparableNormUnion K L M p := by
  letI := separableNormUnionStageField K L M p (separableNormUnionTop L M)
  letI := separableNormUnionField K L M p
  exact RingEquiv.ofBijective
    (separableNormUnionOf K L M p (separableNormUnionTop L M))
    (separableNormUnionOf_top_bijective K L M p)

/-- The terminal equivalence is literally the existing structural map. -/
@[simp]
theorem separableNormUnionTopEquiv_apply
    (x : NormLimit K (separableNormUnionTop L M).val) :
    separableNormUnionTopEquiv K L M p x =
      separableNormUnionOf K L M p (separableNormUnionTop L M) x := rfl

/-- The same finite union is canonically the original norm field of the ambient extension. -/
def separableNormUnionFiniteEquiv :
    letI : Algebra.IsSeparable K M := Algebra.IsSeparable.trans K L M
    letI : IsAPF K M := (isAPF_finite_extension_iff K M L).mpr ‹_›
    letI : Fact (¬ Module.Finite K M) := ⟨separableNormUnion_ambient_infinite K L M⟩
    letI := separableNormUnionField K L M p
    letI : Add (SeparableNormUnion K L M p) :=
      (separableNormUnionField K L M p).toAdd
    letI : Mul (SeparableNormUnion K L M p) :=
      (separableNormUnionField K L M p).toMul
    letI : IsAPF K M := (isAPF_finite_extension_iff K M L).mpr ‹_›
    letI : Fact (¬ Module.Finite K M) := ⟨separableNormUnion_ambient_infinite K L M⟩
    letI := normLimitField K M p
    SeparableNormUnion K L M p ≃+* NormLimit K M := by
  letI : Algebra.IsSeparable K M := Algebra.IsSeparable.trans K L M
  letI : IsAPF K M := (isAPF_finite_extension_iff K M L).mpr ‹_›
  letI : Fact (¬ Module.Finite K M) := ⟨separableNormUnion_ambient_infinite K L M⟩
  letI : Algebra.IsSeparable K (separableNormUnionTop L M).val :=
    Algebra.IsSeparable.trans K L (separableNormUnionTop L M).val
  letI := separableNormUnionField K L M p
  letI : Add (SeparableNormUnion K L M p) :=
    (separableNormUnionField K L M p).toAdd
  letI : Mul (SeparableNormUnion K L M p) :=
    (separableNormUnionField K L M p).toMul
  letI : IsAPF K M := (isAPF_finite_extension_iff K M L).mpr ‹_›
  letI : Fact (¬ Module.Finite K M) := ⟨separableNormUnion_ambient_infinite K L M⟩
  letI := normLimitField K M p
  letI := separableNormUnionStageField K L M p (separableNormUnionTop L M)
  exact (separableNormUnionTopEquiv K L M p).symm.trans
    (normLimitRingEquiv K p
      ((IntermediateField.topEquiv :
        (⊤ : IntermediateField L M) ≃ₐ[L] M).restrictScalars K))

/-- The terminal comparison sends each original terminal family by literal transport. -/
@[simp]
theorem separableNormUnionFiniteEquiv_of_top
    (x : NormLimit K (separableNormUnionTop L M).val) :
    separableNormUnionFiniteEquiv K L M p
        (separableNormUnionOf K L M p (separableNormUnionTop L M) x) =
      normLimitMap ((IntermediateField.topEquiv :
        (⊤ : IntermediateField L M) ≃ₐ[L] M).restrictScalars K) x := by
  let := separableNormUnionStageField K L M p (separableNormUnionTop L M)
  let : Add (SeparableNormUnion K L M p) :=
    (separableNormUnionField K L M p).toAdd
  let : Mul (SeparableNormUnion K L M p) :=
    (separableNormUnionField K L M p).toMul
  change normLimitMap ((IntermediateField.topEquiv :
      (⊤ : IntermediateField L M) ≃ₐ[L] M).restrictScalars K)
    ((separableNormUnionTopEquiv K L M p).symm
      (separableNormUnionTopEquiv K L M p x)) = _
  rw [RingEquiv.symm_apply_apply]

/-- The finite comparison retains every original finite-inclusion map. -/
theorem separableNormUnionFiniteEquiv_of (N : FiniteLayer L M) (x : NormLimit K N.val) :
    letI : Module.Finite N.val M := Module.Finite.right L N.val M
    letI : Algebra.IsSeparable N.val M :=
      Algebra.isSeparable_tower_top_of_isSeparable L N.val M
    letI : IsScalarTower K N.val M := IsScalarTower.of_algebraMap_eq' rfl
    separableNormUnionFiniteEquiv K L M p
        (separableNormUnionOf K L M p N x) =
      finiteNormLimitMap K N.val M x := by
  let : Module.Finite N.val M := Module.Finite.right L N.val M
  let : Algebra.IsSeparable N.val M :=
    Algebra.isSeparable_tower_top_of_isSeparable L N.val M
  let : IsScalarTower K N.val M := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra N.val (separableNormUnionTop L M).val :=
    (IntermediateField.inclusion (show N.val ≤ ⊤ from le_top)).toRingHom.toAlgebra
  let : IsScalarTower L N.val (separableNormUnionTop L M).val :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K N.val (separableNormUnionTop L M).val :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite N.val (separableNormUnionTop L M).val :=
    Module.Finite.right L N.val (separableNormUnionTop L M).val
  let : Algebra.IsSeparable N.val (separableNormUnionTop L M).val :=
    Algebra.isSeparable_tower_top_of_isSeparable L N.val (separableNormUnionTop L M).val
  have hNT : N ≤ separableNormUnionTop L M :=
    show N.val ≤ (⊤ : IntermediateField L M) from le_top
  rw [← separableNormUnionOf_transition K L M p N
    (separableNormUnionTop L M) hNT x, separableNormUnionFiniteEquiv_of_top]
  simpa only [normLimitMap_refl, separableNormUnionTransition, finiteNormLimitRingHom_apply]
    using finiteNormLimitMap_naturality K
    (AlgEquiv.refl : N.val ≃ₐ[K] N.val)
    ((IntermediateField.topEquiv :
      (⊤ : IntermediateField L M) ≃ₐ[L] M).restrictScalars K) (fun _ => rfl) x

/-- The same finite comparison commutes with the actual original base inclusion. -/
theorem separableNormUnionFiniteEquiv_base (x : NormLimit K L) :
    separableNormUnionFiniteEquiv K L M p
        (separableNormUnionBaseHom K L M p x) =
      finiteNormLimitMap K L M x := by
  rw [← separableNormUnionOf_base K L M p (separableNormUnionTop L M) x,
    separableNormUnionFiniteEquiv_of_top]
  simpa only [normLimitMap_refl, separableNormUnionBaseToStage, finiteNormLimitRingHom_apply]
    using finiteNormLimitMap_naturality K
    (AlgEquiv.refl : L ≃ₐ[K] L)
    ((IntermediateField.topEquiv :
      (⊤ : IntermediateField L M) ≃ₐ[L] M).restrictScalars K) (fun _ => rfl) x

/-- The finite comparison retains the rational normalization over the original base. -/
theorem separableNormUnionFiniteEquiv_valuation
    (z : SeparableNormUnion K L M p) :
    letI : Algebra.IsSeparable K M := Algebra.IsSeparable.trans K L M
    letI : IsAPF K M := (isAPF_finite_extension_iff K M L).mpr ‹_›
    letI : Fact (¬ Module.Finite K M) := ⟨separableNormUnion_ambient_infinite K L M⟩
    separableNormUnionValueMap
        (separableNormUnionStageExponent K L M (separableNormUnionTop L M))
        (normLimitValuation K M
          (separableNormUnionFiniteEquiv K L M p z)) =
      separableNormUnionValuation K L M p z := by
  let : Algebra.IsSeparable K M := Algebra.IsSeparable.trans K L M
  let : IsAPF K M := (isAPF_finite_extension_iff K M L).mpr ‹_›
  let : Fact (¬ Module.Finite K M) := ⟨separableNormUnion_ambient_infinite K L M⟩
  let : Algebra.IsSeparable K (separableNormUnionTop L M).val :=
    Algebra.IsSeparable.trans K L (separableNormUnionTop L M).val
  obtain ⟨x, rfl⟩ :=
    (separableNormUnionOf_top_bijective K L M p).surjective z
  rw [separableNormUnionFiniteEquiv_of_top, normLimitValuation_normLimitMap,
    separableNormUnionValuation_of, separableNormUnionStageValuation_apply]

/-- Finite comparison over the same base and its original finite-inclusion algebra. -/
def separableNormUnionFiniteAlgEquiv :
    letI : Algebra.IsSeparable K M := Algebra.IsSeparable.trans K L M
    letI : IsAPF K M := (isAPF_finite_extension_iff K M L).mpr ‹_›
    letI : Fact (¬ Module.Finite K M) := ⟨separableNormUnion_ambient_infinite K L M⟩
    letI := normLimitField K L p
    letI := separableNormUnionField K L M p
    letI : IsAPF K M := (isAPF_finite_extension_iff K M L).mpr ‹_›
    letI : Fact (¬ Module.Finite K M) := ⟨separableNormUnion_ambient_infinite K L M⟩
    letI := normLimitField K M p
    letI := separableNormUnionAlgebra K L M p
    letI := (finiteNormLimitRingHom K L M p
      ).toAlgebra
    SeparableNormUnion K L M p ≃ₐ[NormLimit K L] NormLimit K M := by
  letI : Algebra.IsSeparable K M := Algebra.IsSeparable.trans K L M
  letI : IsAPF K M := (isAPF_finite_extension_iff K M L).mpr ‹_›
  letI : Fact (¬ Module.Finite K M) := ⟨separableNormUnion_ambient_infinite K L M⟩
  letI := normLimitField K L p
  letI := separableNormUnionField K L M p
  letI : IsAPF K M := (isAPF_finite_extension_iff K M L).mpr ‹_›
  letI : Fact (¬ Module.Finite K M) := ⟨separableNormUnion_ambient_infinite K L M⟩
  letI := normLimitField K M p
  letI := separableNormUnionAlgebra K L M p
  letI := (finiteNormLimitRingHom K L M p
    ).toAlgebra
  exact { separableNormUnionFiniteEquiv K L M p with
    commutes' := separableNormUnionFiniteEquiv_base K L M p }

/-- Algebra bundling preserves the same canonical finite comparison. -/
@[simp]
theorem separableNormUnionFiniteAlgEquiv_apply
    (z : SeparableNormUnion K L M p) :
    separableNormUnionFiniteAlgEquiv K L M p z =
      separableNormUnionFiniteEquiv K L M p z := rfl

end FiniteAmbient

section Embeddings

variable (M' : Type*) [Field M'] [Algebra K M'] [Algebra L M']
    [IsScalarTower K L M'] [Algebra.IsSeparable L M']
variable (t : M →ₐ[L] M')

/-- An actual ambient embedding transports each original finite-stage norm field. -/
def separableNormUnionStageMap (N : FiniteLayer L M) :
    letI := separableNormUnionStageField K L M p N
    letI := separableNormUnionStageField K L M' p (FiniteLayer.map t N)
    NormLimit K N.val ≃+* NormLimit K (FiniteLayer.map t N).val := by
  letI : Algebra.IsSeparable K N.val := Algebra.IsSeparable.trans K L N.val
  letI : Algebra.IsSeparable K (FiniteLayer.map t N).val :=
    Algebra.IsSeparable.trans K L (FiniteLayer.map t N).val
  exact normLimitRingEquiv K p
    ((FiniteLayer.equivMap t N).restrictScalars K)

/-- Stage transport is the existing literal norm-family isomorphism. -/
@[simp]
theorem separableNormUnionStageMap_apply (N : FiniteLayer L M) (x : NormLimit K N.val) :
    separableNormUnionStageMap K L M p M' t N x =
      normLimitMap ((FiniteLayer.equivMap t N).restrictScalars K) x := rfl

/-- Transport of the actual finite image commutes with the original base inclusion. -/
theorem separableNormUnionStageMap_base (N : FiniteLayer L M) (x : NormLimit K L) :
    separableNormUnionStageMap K L M p M' t N
        (separableNormUnionBaseToStage K L M p N x) =
      separableNormUnionBaseToStage K L M' p (FiniteLayer.map t N) x := by
  rw [separableNormUnionStageMap_apply]
  simpa only [separableNormUnionBaseToStage, finiteNormLimitRingHom_apply,
    normLimitMap_refl] using finiteNormLimitMap_naturality K
    (AlgEquiv.refl : L ≃ₐ[K] L) ((FiniteLayer.equivMap t N).restrictScalars K)
    (fun a => (FiniteLayer.equivMap t N).commutes a) x

/-- Actual stage transport commutes with every original finite-stage transition. -/
theorem separableNormUnionStageMap_transition (N P : FiniteLayer L M)
    (hNP : N ≤ P) (x : NormLimit K N.val) :
    separableNormUnionStageMap K L M p M' t P
        (separableNormUnionTransition K L M p N P hNP x) =
      separableNormUnionTransition K L M' p
        (FiniteLayer.map t N) (FiniteLayer.map t P) (FiniteLayer.map_mono t hNP)
        (separableNormUnionStageMap K L M p M' t N x) := by
  let : Algebra.IsSeparable K N.val := Algebra.IsSeparable.trans K L N.val
  let : Algebra.IsSeparable K (FiniteLayer.map t N).val :=
    Algebra.IsSeparable.trans K L (FiniteLayer.map t N).val
  let : Algebra N.val P.val := (IntermediateField.inclusion hNP).toRingHom.toAlgebra
  let : IsScalarTower K N.val P.val := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite N.val P.val := Module.Finite.right L N.val P.val
  let : Algebra.IsSeparable N.val P.val :=
    Algebra.isSeparable_tower_top_of_isSeparable L N.val P.val
  let : Algebra (FiniteLayer.map t N).val (FiniteLayer.map t P).val :=
    (IntermediateField.inclusion (FiniteLayer.map_mono t hNP)).toRingHom.toAlgebra
  let : IsScalarTower K (FiniteLayer.map t N).val (FiniteLayer.map t P).val :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite (FiniteLayer.map t N).val (FiniteLayer.map t P).val :=
    Module.Finite.right L (FiniteLayer.map t N).val (FiniteLayer.map t P).val
  let : Algebra.IsSeparable (FiniteLayer.map t N).val (FiniteLayer.map t P).val :=
    Algebra.isSeparable_tower_top_of_isSeparable L
      (FiniteLayer.map t N).val (FiniteLayer.map t P).val
  rw [separableNormUnionStageMap_apply, separableNormUnionStageMap_apply]
  simpa only [separableNormUnionTransition, finiteNormLimitRingHom_apply] using
    finiteNormLimitMap_naturality K ((FiniteLayer.equivMap t N).restrictScalars K)
      ((FiniteLayer.equivMap t P).restrictScalars K)
      (fun _ => by apply Subtype.ext; rfl) x

include p in
/-- Original image isomorphisms retain the genuine base scaling exponents. -/
theorem separableNormUnionStageExponent_map (N : FiniteLayer L M) :
    separableNormUnionStageExponent K L M' (FiniteLayer.map t N) =
      separableNormUnionStageExponent K L M N := by
  let : Algebra.IsSeparable K N.val := Algebra.IsSeparable.trans K L N.val
  let : Algebra.IsSeparable K (FiniteLayer.map t N).val :=
    Algebra.IsSeparable.trans K L (FiniteLayer.map t N).val
  apply (separableNormUnionStageExponent_unique K L M' p
    (FiniteLayer.map t N) (separableNormUnionStageExponent K L M N) ?_).symm
  intro x
  have h := normLimitValuation_normLimitMap K
    ((FiniteLayer.equivMap t N).restrictScalars K)
    (separableNormUnionBaseToStage K L M p N x)
  rw [← separableNormUnionStageMap_apply K L M p M' t N,
    separableNormUnionStageMap_base K L M p M' t N] at h
  simp only [separableNormUnionBaseToStage, finiteNormLimitRingHom_apply] at h
  exact h.trans (separableNormUnionStageExponent_spec K L M N x)

/-- The actual stage isomorphisms preserve the rationally normalized valuations. -/
theorem separableNormUnionStageMap_valuation (N : FiniteLayer L M)
    (x : NormLimit K N.val) :
    separableNormUnionStageValuation K L M' p (FiniteLayer.map t N)
        (separableNormUnionStageMap K L M p M' t N x) =
      separableNormUnionStageValuation K L M p N x := by
  let : Algebra.IsSeparable K N.val := Algebra.IsSeparable.trans K L N.val
  let : Algebra.IsSeparable K (FiniteLayer.map t N).val :=
    Algebra.IsSeparable.trans K L (FiniteLayer.map t N).val
  rw [separableNormUnionStageValuation_apply, separableNormUnionStageValuation_apply,
    separableNormUnionStageMap_apply, normLimitValuation_normLimitMap,
    separableNormUnionStageExponent_map K L M p M' t N]

/-- The actual compatible finite-image maps induce a map on the same canonical unions. -/
def separableNormUnionMap :
    letI := separableNormUnionField K L M p
    letI := separableNormUnionField K L M' p
    SeparableNormUnion K L M p →+*
      SeparableNormUnion K L M' p := by
  letI (N : FiniteLayer L M) : Field (NormLimit K N.val) :=
    separableNormUnionStageField K L M p N
  letI (N : FiniteLayer L M') : Field (NormLimit K N.val) :=
    separableNormUnionStageField K L M' p N
  letI := separableNormUnionField K L M p
  letI := separableNormUnionField K L M' p
  refine DirectLimit.Ring.lift (fun N : FiniteLayer L M => NormLimit K N.val)
    (separableNormUnionTransition K L M p)
    (SeparableNormUnion K L M' p)
    (fun N => (separableNormUnionOf K L M' p (FiniteLayer.map t N)).comp
      (separableNormUnionStageMap K L M p M' t N).toRingHom) ?_
  intro N P hNP x
  change separableNormUnionOf K L M' p (FiniteLayer.map t P)
      (separableNormUnionStageMap K L M p M' t P
        (separableNormUnionTransition K L M p N P hNP x)) = _
  rw [separableNormUnionStageMap_transition, separableNormUnionOf_transition]
  rfl

/-- Evaluation on an original finite family is the literal finite-image formula. -/
@[simp]
theorem separableNormUnionMap_of (N : FiniteLayer L M) (x : NormLimit K N.val) :
    separableNormUnionMap K L M p M' t
        (separableNormUnionOf K L M p N x) =
      separableNormUnionOf K L M' p (FiniteLayer.map t N)
        (separableNormUnionStageMap K L M p M' t N x) := rfl

/-- The original unital finite-stage maps induce an embedding of the actual fields. -/
theorem separableNormUnionMap_injective :
    Function.Injective (separableNormUnionMap K L M p M' t) := by
  let := separableNormUnionField K L M p
  let := separableNormUnionField K L M' p
  exact (separableNormUnionMap K L M p M' t).injective

/-- The induced union map fixes the original base norm field. -/
theorem separableNormUnionMap_base (x : NormLimit K L) :
    separableNormUnionMap K L M p M' t
        (separableNormUnionBaseHom K L M p x) =
      separableNormUnionBaseHom K L M' p x := by
  rw [← separableNormUnionOf_base K L M p FiniteLayer.bottom x,
    separableNormUnionMap_of, separableNormUnionStageMap_base, separableNormUnionOf_base]

/-- The actual induced embedding preserves the canonical rational union valuation. -/
theorem separableNormUnionMap_valuation (z : SeparableNormUnion K L M p) :
    separableNormUnionValuation K L M' p
        (separableNormUnionMap K L M p M' t z) =
      separableNormUnionValuation K L M p z := by
  obtain ⟨N, x, rfl⟩ := separableNormUnion_exists_stage K L M p z
  rw [separableNormUnionMap_of, separableNormUnionValuation_of,
    separableNormUnionValuation_of, separableNormUnionStageMap_valuation]

/-- The actual induced map is an algebra embedding over the original base norm field. -/
def separableNormUnionAlgMap :
    letI := normLimitField K L p
    letI := separableNormUnionField K L M p
    letI := separableNormUnionField K L M' p
    letI := separableNormUnionAlgebra K L M p
    letI := separableNormUnionAlgebra K L M' p
    SeparableNormUnion K L M p →ₐ[NormLimit K L]
      SeparableNormUnion K L M' p := by
  letI := normLimitField K L p
  letI := separableNormUnionField K L M p
  letI := separableNormUnionField K L M' p
  letI := separableNormUnionAlgebra K L M p
  letI := separableNormUnionAlgebra K L M' p
  exact { separableNormUnionMap K L M p M' t with
    commutes' := separableNormUnionMap_base K L M p M' t }

/-- Algebra bundling preserves the same literal map on the same union carrier. -/
@[simp]
theorem separableNormUnionAlgMap_apply (z : SeparableNormUnion K L M p) :
    separableNormUnionAlgMap K L M p M' t z =
      separableNormUnionMap K L M p M' t z := rfl

/-- Equal actual image stages and equal ambient transports give the same union element. -/
theorem separableNormUnionOf_transport_congr {D : Type*} [Field D] [Algebra K D]
    (P Q : FiniteLayer L M') (e : D ≃ₐ[K] P.val) (f : D ≃ₐ[K] Q.val)
    (hPQ : P = Q) (hef : ∀ a : D, (e a : M') = (f a : M'))
    (x : NormLimit K D) :
    separableNormUnionOf K L M' p P (normLimitMap e x) =
      separableNormUnionOf K L M' p Q (normLimitMap f x) := by
  subst Q
  have heq : e = f := by
    apply AlgEquiv.ext
    intro a
    exact Subtype.ext (hef a)
  rw [heq]

/-- The actual identity extension embedding induces the identity on the same union. -/
@[simp]
theorem separableNormUnionMap_id :
    letI := separableNormUnionField K L M p
    separableNormUnionMap K L M p M (AlgHom.id L M) =
      RingHom.id (SeparableNormUnion K L M p) := by
  let := separableNormUnionField K L M p
  apply RingHom.ext
  intro z
  obtain ⟨N, x, rfl⟩ := separableNormUnion_exists_stage K L M p z
  change separableNormUnionMap K L M p M (AlgHom.id L M)
      (separableNormUnionOf K L M p N x) =
    separableNormUnionOf K L M p N x
  rw [separableNormUnionMap_of, separableNormUnionStageMap_apply]
  calc
    _ = separableNormUnionOf K L M p N
        (normLimitMap (AlgEquiv.refl : N.val ≃ₐ[K] N.val) x) := by
      apply separableNormUnionOf_transport_congr
      · exact FiniteLayer.map_id N
      · intro a
        rfl
    _ = _ := by rw [normLimitMap_refl]

variable (M'' : Type*) [Field M''] [Algebra K M''] [Algebra L M'']
    [IsScalarTower K L M''] [Algebra.IsSeparable L M'']
variable (s : M' →ₐ[L] M'')

/-- Actual composition of ambient embeddings gives composition of the same union maps. -/
theorem separableNormUnionMap_comp :
    letI := separableNormUnionField K L M p
    letI := separableNormUnionField K L M' p
    letI := separableNormUnionField K L M'' p
    (separableNormUnionMap K L M' p M'' s).comp
        (separableNormUnionMap K L M p M' t) =
      separableNormUnionMap K L M p M'' (s.comp t) := by
  let := separableNormUnionField K L M p
  let := separableNormUnionField K L M' p
  let := separableNormUnionField K L M'' p
  apply RingHom.ext
  intro z
  obtain ⟨N, x, rfl⟩ := separableNormUnion_exists_stage K L M p z
  change separableNormUnionMap K L M' p M'' s
      (separableNormUnionMap K L M p M' t
        (separableNormUnionOf K L M p N x)) = _
  rw [separableNormUnionMap_of, separableNormUnionMap_of, separableNormUnionMap_of]
  simp only [separableNormUnionStageMap_apply]
  rw [normLimitMap_trans]
  apply separableNormUnionOf_transport_congr
  · exact FiniteLayer.map_map t s N
  · intro a
    rfl

end Embeddings

end FontaineWintenberger
