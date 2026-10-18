/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.Algebra.GroupWithZero.WithZero

/-!
# The multiplicative norm limit over all finite intermediate fields

No normality or APF assumption is needed for this multiplicative construction.
The transition maps are actual field norms on genuinely finite extensions.
-/

@[expose] public section

namespace FontaineWintenberger

noncomputable section

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- All finite intermediate fields, including nonnormal ones. -/
abbrev FiniteLayer := {E : IntermediateField K L // FiniteDimensional K E}

namespace FiniteLayer

variable {K L}

instance finiteDimensional (E : FiniteLayer K L) : FiniteDimensional K E.val := E.property

/-- The bottom finite layer is the actual image of the base field. -/
def bottom : FiniteLayer K L := ⟨⊥, inferInstance⟩

theorem bottom_le (E : FiniteLayer K L) : bottom ≤ E :=
  (show (⊥ : IntermediateField K L) ≤ E.val from bot_le)

/-- Finite composita supply upper bounds for the full finite-layer index set. -/
def sup (E F : FiniteLayer K L) : FiniteLayer K L := ⟨E.val ⊔ F.val, inferInstance⟩

theorem le_sup_left (E F : FiniteLayer K L) : E ≤ sup E F :=
  (show E.val ≤ E.val ⊔ F.val from _root_.le_sup_left)

theorem le_sup_right (E F : FiniteLayer K L) : F ≤ sup E F :=
  (show F.val ≤ E.val ⊔ F.val from _root_.le_sup_right)

/-- The canonical norm for an actual inclusion of finite intermediate fields. -/
def norm (E F : FiniteLayer K L) (h : E ≤ F) : F.val →* E.val :=
  Algebra.norm E.val (S := IntermediateField.extendScalars h)

theorem norm_eq_zero_iff (E F : FiniteLayer K L) (h : E ≤ F) (x : F.val) :
    norm E F h x = 0 ↔ x = 0 := by
  let F' := IntermediateField.extendScalars h
  have : FiniteDimensional K F' := F.property
  have : FiniteDimensional E.val F' := Module.Finite.right K E.val F'
  exact Algebra.norm_eq_zero_iff (R := E.val) (S := F')

@[simp]
theorem norm_self (E : FiniteLayer K L) (x : E.val) : norm E E le_rfl x = x := by
  change Algebra.norm E.val x = x
  simp

theorem norm_norm (E F G : FiniteLayer K L) (hEF : E ≤ F) (hFG : F ≤ G) (x : G.val) :
    norm E F hEF (norm F G hFG x) = norm E G (hEF.trans hFG) x := by
  let : Algebra E.val F.val := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
  let : Algebra F.val G.val := (IntermediateField.inclusion hFG).toRingHom.toAlgebra
  let : Algebra E.val G.val :=
    (IntermediateField.inclusion (hEF.trans hFG)).toRingHom.toAlgebra
  have : IsScalarTower E.val F.val G.val := IsScalarTower.of_algebraMap_eq' rfl
  change Algebra.norm E.val (Algebra.norm F.val x) = Algebra.norm E.val x
  exact Algebra.norm_norm

/-- The actual norm on units. -/
def normUnits (E F : FiniteLayer K L) (h : E ≤ F) : F.valˣ →* E.valˣ :=
  Units.map (norm E F h)

@[simp]
theorem normUnits_val (E F : FiniteLayer K L) (h : E ≤ F) (x : F.valˣ) :
    (normUnits E F h x : E.val) = norm E F h (x : F.val) := rfl

@[simp]
theorem normUnits_self (E : FiniteLayer K L) (x : E.valˣ) : normUnits E E le_rfl x = x :=
  Units.ext (norm_self E (x : E.val))

theorem normUnits_normUnits (E F G : FiniteLayer K L) (hEF : E ≤ F) (hFG : F ≤ G)
    (x : G.valˣ) :
    normUnits E F hEF (normUnits F G hFG x) = normUnits E G (hEF.trans hFG) x :=
  Units.ext (norm_norm E F G hEF hFG (x : G.val))

end FiniteLayer

/-- The actual subgroup of norm-compatible families of units over all finite layers. -/
def normLimitGroup : Subgroup (∀ E : FiniteLayer K L, E.valˣ) where
  carrier := {x | ∀ (E F : FiniteLayer K L) (h : E ≤ F), FiniteLayer.normUnits E F h (x F) = x E}
  one_mem' := by intro E F h; exact map_one _
  mul_mem' := by
    intro x y hx hy E F h
    change FiniteLayer.normUnits E F h (x F * y F) = x E * y E
    rw [map_mul, hx E F h, hy E F h]
  inv_mem' := by
    intro x hx E F h
    change FiniteLayer.normUnits E F h ((x F)⁻¹) = (x E)⁻¹
    rw [map_inv, hx E F h]

/-- The single multiplicative carrier for the field of norms: its actual unit
limit with an absorbing zero adjoined.

This is a `def`, not an `abbrev`: every algebraic structure on it (the group with zero here,
the addition, field, valuation, ... in later files) is a global instance keyed on `NormLimit`,
so instance search never unfolds the carrier. -/
def NormLimit := WithZero (normLimitGroup K L)

instance NormLimit.instCommGroupWithZero : CommGroupWithZero (NormLimit K L) :=
  inferInstanceAs (CommGroupWithZero (WithZero (normLimitGroup K L)))

instance NormLimit.instNontrivial : Nontrivial (NormLimit K L) :=
  inferInstanceAs (Nontrivial (WithZero (normLimitGroup K L)))

/-- The coercion of a norm-compatible unit family into the carrier. -/
instance NormLimit.instCoeTC : CoeTC (normLimitGroup K L) (NormLimit K L) := ⟨WithZero.coe⟩

namespace NormLimit

variable {K L}

theorem coe_injective : Function.Injective ((↑) : normLimitGroup K L → NormLimit K L) :=
  WithZero.coe_injective

@[simp]
theorem coe_inj {x y : normLimitGroup K L} : (x : NormLimit K L) = y ↔ x = y :=
  WithZero.coe_inj

@[simp]
theorem coe_ne_zero {x : normLimitGroup K L} : (x : NormLimit K L) ≠ 0 :=
  WithZero.coe_ne_zero

@[simp]
theorem zero_ne_coe {x : normLimitGroup K L} : (0 : NormLimit K L) ≠ x :=
  WithZero.zero_ne_coe

@[simp]
theorem coe_mul (x y : normLimitGroup K L) :
    ((x * y : normLimitGroup K L) : NormLimit K L) = x * y := rfl

@[simp]
theorem coe_one : ((1 : normLimitGroup K L) : NormLimit K L) = 1 := rfl

@[simp]
theorem coe_inv (x : normLimitGroup K L) :
    ((x⁻¹ : normLimitGroup K L) : NormLimit K L) = (x : NormLimit K L)⁻¹ := rfl

/-- Case analysis on the carrier: zero or a coerced unit family. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
protected def recZeroCoe {motive : NormLimit K L → Sort*} (zero : motive 0)
    (coe : ∀ x : normLimitGroup K L, motive x) : ∀ x : NormLimit K L, motive x :=
  WithZero.recZeroCoe zero coe

end NormLimit

/-- Evaluation at an actual finite layer, extended by zero. -/
def normLimitEval (E : FiniteLayer K L) : NormLimit K L →*₀ E.val :=
  WithZero.lift'
    { toFun := fun x => (x.val E : E.val)
      map_one' := rfl
      map_mul' _ _ := rfl }

@[simp]
theorem normLimitEval_coe (E : FiniteLayer K L) (x : normLimitGroup K L) :
    normLimitEval K L E (x : NormLimit K L) = (x.val E : E.val) := rfl

/-- Every individual evaluation detects zero, even though it need not be injective. -/
@[simp]
theorem normLimitEval_eq_zero_iff (E : FiniteLayer K L) (x : NormLimit K L) :
    normLimitEval K L E x = 0 ↔ x = 0 := by
  induction x using NormLimit.recZeroCoe with
  | zero => simp
  | coe x => exact iff_of_false (Units.ne_zero (x.val E)) WithZero.coe_ne_zero

/-- The evaluations jointly distinguish all elements of the multiplicative limit. -/
@[ext]
theorem NormLimit.ext {x y : NormLimit K L}
    (h : ∀ E, normLimitEval K L E x = normLimitEval K L E y) : x = y := by
  induction x using NormLimit.recZeroCoe with
  | zero =>
      have hy := (normLimitEval_eq_zero_iff K L (FiniteLayer.bottom) y).mp
        (by simpa using (h FiniteLayer.bottom).symm)
      exact hy.symm
  | coe x =>
      induction y using NormLimit.recZeroCoe with
      | zero =>
          have hx := (normLimitEval_eq_zero_iff K L (FiniteLayer.bottom)
            (x : NormLimit K L)).mp (by simpa using h FiniteLayer.bottom)
          exact hx
      | coe y =>
          congr 1
          apply Subtype.ext
          funext E
          exact Units.ext (h E)

/-- The actual coordinates satisfy the actual finite-layer norm equations. -/
theorem normLimitEval_norm (E F : FiniteLayer K L) (h : E ≤ F) (x : NormLimit K L) :
    FiniteLayer.norm E F h (normLimitEval K L F x) = normLimitEval K L E x := by
  induction x using NormLimit.recZeroCoe with
  | zero =>
      exact (FiniteLayer.norm_eq_zero_iff E F h 0).mpr rfl
  | coe x =>
      exact congrArg Units.val (x.property E F h)

/-- Every actual compatible field family is represented uniquely by the single
zero-adjoined unit limit. No additional family carrier is introduced. -/
theorem existsUnique_normLimit_of_compatible (f : ∀ E : FiniteLayer K L, E.val)
    (hf : ∀ (E F : FiniteLayer K L) (h : E ≤ F), FiniteLayer.norm E F h (f F) = f E) :
    ∃! x : NormLimit K L, ∀ E, normLimitEval K L E x = f E := by
  suffices ∃ x : NormLimit K L, ∀ E, normLimitEval K L E x = f E by
    obtain ⟨x, hx⟩ := this
    exact ⟨x, hx, fun y hy => NormLimit.ext K L (fun E => (hy E).trans (hx E).symm)⟩
  by_cases hzero : f FiniteLayer.bottom = 0
  · have hE (E : FiniteLayer K L) : f E = 0 :=
      (FiniteLayer.norm_eq_zero_iff FiniteLayer.bottom E (FiniteLayer.bottom_le E) (f E)).mp
        ((hf _ _ _).trans hzero)
    exact ⟨0, fun E => by simp [hE E]⟩
  · have hE (E : FiniteLayer K L) : f E ≠ 0 := by
      intro hx
      apply hzero
      rw [← hf FiniteLayer.bottom E (FiniteLayer.bottom_le E), hx]
      exact (FiniteLayer.norm_eq_zero_iff _ _ _ 0).mpr rfl
    let x : normLimitGroup K L :=
      ⟨fun E => Units.mk0 (f E) (hE E), fun E F h => Units.ext (hf E F h)⟩
    exact ⟨(x : NormLimit K L), fun _ => rfl⟩

end

end FontaineWintenberger
