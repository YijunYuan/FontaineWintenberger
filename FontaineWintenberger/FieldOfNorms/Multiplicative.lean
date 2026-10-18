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
# The multiplicative field of norms over all finite intermediate fields

No normality or APF assumption is needed for this multiplicative construction.
The transition maps are actual field norms on genuinely finite extensions.
-/

@[expose] public section

namespace FontaineWintenberger

noncomputable section

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- All finite intermediate fields, including nonnormal ones. -/
abbrev FiniteIntermediateField := {E : IntermediateField K L // FiniteDimensional K E}

namespace FiniteIntermediateField

variable {K L}

instance finiteDimensional (E : FiniteIntermediateField K L) : FiniteDimensional K E.val :=
    E.property

/-- The bottom finite intermediate field is the actual image of the base field. -/
def bottom : FiniteIntermediateField K L := ⟨⊥, inferInstance⟩

theorem bottom_le (E : FiniteIntermediateField K L) : bottom ≤ E :=
  (show (⊥ : IntermediateField K L) ≤ E.val from bot_le)

/-- Finite composita supply upper bounds for the full finite-layer index set. -/
def sup (E F : FiniteIntermediateField K L) : FiniteIntermediateField K L := ⟨E.val ⊔ F.val,
    inferInstance⟩

theorem le_sup_left (E F : FiniteIntermediateField K L) : E ≤ sup E F :=
  (show E.val ≤ E.val ⊔ F.val from _root_.le_sup_left)

theorem le_sup_right (E F : FiniteIntermediateField K L) : F ≤ sup E F :=
  (show F.val ≤ E.val ⊔ F.val from _root_.le_sup_right)

/-- The canonical norm for an actual inclusion of finite intermediate fields. -/
def norm (E F : FiniteIntermediateField K L) (h : E ≤ F) : F.val →* E.val :=
  Algebra.norm E.val (S := IntermediateField.extendScalars h)

theorem norm_eq_zero_iff (E F : FiniteIntermediateField K L) (h : E ≤ F) (x : F.val) :
    norm E F h x = 0 ↔ x = 0 := by
  let F' := IntermediateField.extendScalars h
  have : FiniteDimensional K F' := F.property
  have : FiniteDimensional E.val F' := Module.Finite.right K E.val F'
  exact Algebra.norm_eq_zero_iff (R := E.val) (S := F')

@[simp]
theorem norm_self (E : FiniteIntermediateField K L) (x : E.val) : norm E E le_rfl x = x := by
  change Algebra.norm E.val x = x
  simp

theorem norm_norm (E F G : FiniteIntermediateField K L) (hEF : E ≤ F) (hFG : F ≤ G) (x : G.val) :
    norm E F hEF (norm F G hFG x) = norm E G (hEF.trans hFG) x := by
  let : Algebra E.val F.val := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
  let : Algebra F.val G.val := (IntermediateField.inclusion hFG).toRingHom.toAlgebra
  let : Algebra E.val G.val :=
    (IntermediateField.inclusion (hEF.trans hFG)).toRingHom.toAlgebra
  have : IsScalarTower E.val F.val G.val := IsScalarTower.of_algebraMap_eq' rfl
  change Algebra.norm E.val (Algebra.norm F.val x) = Algebra.norm E.val x
  exact Algebra.norm_norm

/-- The actual norm on units. -/
def normUnits (E F : FiniteIntermediateField K L) (h : E ≤ F) : F.valˣ →* E.valˣ :=
  Units.map (norm E F h)

@[simp]
theorem normUnits_val (E F : FiniteIntermediateField K L) (h : E ≤ F) (x : F.valˣ) :
    (normUnits E F h x : E.val) = norm E F h (x : F.val) := rfl

@[simp]
theorem normUnits_self (E : FiniteIntermediateField K L) (x : E.valˣ) : normUnits E E le_rfl x = x
    :=
  Units.ext (norm_self E (x : E.val))

theorem normUnits_normUnits (E F G : FiniteIntermediateField K L) (hEF : E ≤ F) (hFG : F ≤ G)
    (x : G.valˣ) :
    normUnits E F hEF (normUnits F G hFG x) = normUnits E G (hEF.trans hFG) x :=
  Units.ext (norm_norm E F G hEF hFG (x : G.val))

end FiniteIntermediateField

/-- The actual subgroup of norm-compatible families of units over all finite intermediate fields. -/
def FieldOfNorms.normCompatibleUnits : Subgroup (∀ E : FiniteIntermediateField K L, E.valˣ) where
  carrier := {x | ∀ (E F : FiniteIntermediateField K L) (h : E ≤ F),
      FiniteIntermediateField.normUnits E F h (x F) = x E}
  one_mem' := by intro E F h; exact _root_.map_one _
  mul_mem' := by
    intro x y hx hy E F h
    change FiniteIntermediateField.normUnits E F h (x F * y F) = x E * y E
    rw [_root_.map_mul, hx E F h, hy E F h]
  inv_mem' := by
    intro x hx E F h
    change FiniteIntermediateField.normUnits E F h ((x F)⁻¹) = (x E)⁻¹
    rw [map_inv, hx E F h]

/-- The single multiplicative carrier for the field of norms: its actual unit
limit with an absorbing zero adjoined.

This is a `def`, not an `abbrev`: every algebraic structure on it (the group with zero here,
the addition, field, valuation, ... in later files) is a global instance keyed on `FieldOfNorms`,
so instance search never unfolds the carrier. -/
def FieldOfNorms := WithZero (FieldOfNorms.normCompatibleUnits K L)

instance FieldOfNorms.instCommGroupWithZero : CommGroupWithZero (FieldOfNorms K L) :=
  inferInstanceAs (CommGroupWithZero (WithZero (FieldOfNorms.normCompatibleUnits K L)))

instance FieldOfNorms.instNontrivial : Nontrivial (FieldOfNorms K L) :=
  inferInstanceAs (Nontrivial (WithZero (FieldOfNorms.normCompatibleUnits K L)))

/-- The coercion of a norm-compatible unit family into the carrier. -/
instance FieldOfNorms.instCoeTC : CoeTC (FieldOfNorms.normCompatibleUnits K L) (FieldOfNorms K L)
    := ⟨WithZero.coe⟩

namespace FieldOfNorms

variable {K L}

theorem coe_injective : Function.Injective ((↑) : FieldOfNorms.normCompatibleUnits K L →
    FieldOfNorms K L) :=
  WithZero.coe_injective

@[simp]
theorem coe_inj {x y : FieldOfNorms.normCompatibleUnits K L} : (x : FieldOfNorms K L) = y ↔ x = y :=
  WithZero.coe_inj

@[simp]
theorem coe_ne_zero {x : FieldOfNorms.normCompatibleUnits K L} : (x : FieldOfNorms K L) ≠ 0 :=
  WithZero.coe_ne_zero

@[simp]
theorem zero_ne_coe {x : FieldOfNorms.normCompatibleUnits K L} : (0 : FieldOfNorms K L) ≠ x :=
  WithZero.zero_ne_coe

@[simp]
theorem coe_mul (x y : FieldOfNorms.normCompatibleUnits K L) :
    ((x * y : FieldOfNorms.normCompatibleUnits K L) : FieldOfNorms K L) = x * y := rfl

@[simp]
theorem coe_one : ((1 : FieldOfNorms.normCompatibleUnits K L) : FieldOfNorms K L) = 1 := rfl

@[simp]
theorem coe_inv (x : FieldOfNorms.normCompatibleUnits K L) :
    ((x⁻¹ : FieldOfNorms.normCompatibleUnits K L) : FieldOfNorms K L) = (x : FieldOfNorms K L)⁻¹ :=
        rfl

/-- Case analysis on the carrier: zero or a coerced unit family. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
protected def recZeroCoe {motive : FieldOfNorms K L → Sort*} (zero : motive 0)
    (coe : ∀ x : FieldOfNorms.normCompatibleUnits K L, motive x) : ∀ x : FieldOfNorms K L, motive x
        :=
  WithZero.recZeroCoe zero coe

end FieldOfNorms

/-- Evaluation at an actual finite intermediate field, extended by zero. -/
def FieldOfNorms.coord (E : FiniteIntermediateField K L) : FieldOfNorms K L →*₀ E.val :=
  WithZero.lift'
    { toFun := fun x => (x.val E : E.val)
      map_one' := rfl
      map_mul' _ _ := rfl }

@[simp]
theorem FieldOfNorms.coord_coe (E : FiniteIntermediateField K L) (x :
    FieldOfNorms.normCompatibleUnits K L) :
    FieldOfNorms.coord K L E (x : FieldOfNorms K L) = (x.val E : E.val) := rfl

/-- Every individual evaluation detects zero, even though it need not be injective. -/
@[simp]
theorem FieldOfNorms.coord_eq_zero_iff (E : FiniteIntermediateField K L) (x : FieldOfNorms K L) :
    FieldOfNorms.coord K L E x = 0 ↔ x = 0 := by
  induction x using FieldOfNorms.recZeroCoe with
  | zero => simp
  | coe x => exact iff_of_false (Units.ne_zero (x.val E)) WithZero.coe_ne_zero

/-- The evaluations jointly distinguish all elements of the multiplicative limit. -/
@[ext]
theorem FieldOfNorms.ext {x y : FieldOfNorms K L}
    (h : ∀ E, FieldOfNorms.coord K L E x = FieldOfNorms.coord K L E y) : x = y := by
  induction x using FieldOfNorms.recZeroCoe with
  | zero =>
      have hy := (FieldOfNorms.coord_eq_zero_iff K L (FiniteIntermediateField.bottom) y).mp
        (by simpa using (h FiniteIntermediateField.bottom).symm)
      exact hy.symm
  | coe x =>
      induction y using FieldOfNorms.recZeroCoe with
      | zero =>
          have hx := (FieldOfNorms.coord_eq_zero_iff K L (FiniteIntermediateField.bottom)
            (x : FieldOfNorms K L)).mp (by simpa using h FiniteIntermediateField.bottom)
          exact hx
      | coe y =>
          congr 1
          apply Subtype.ext
          funext E
          exact Units.ext (h E)

/-- The actual coordinates satisfy the actual finite-layer norm equations. -/
theorem FieldOfNorms.coord_norm (E F : FiniteIntermediateField K L) (h : E ≤ F) (x : FieldOfNorms K
    L) :
    FiniteIntermediateField.norm E F h (FieldOfNorms.coord K L F x) = FieldOfNorms.coord K L E x :=
        by
  induction x using FieldOfNorms.recZeroCoe with
  | zero =>
      exact (FiniteIntermediateField.norm_eq_zero_iff E F h 0).mpr rfl
  | coe x =>
      exact congrArg Units.val (x.property E F h)

/-- Every actual compatible field family is represented uniquely by the single
zero-adjoined unit limit. No additional family carrier is introduced. -/
theorem existsUnique_fieldOfNorms_of_compatible (f : ∀ E : FiniteIntermediateField K L, E.val)
    (hf : ∀ (E F : FiniteIntermediateField K L) (h : E ≤ F), FiniteIntermediateField.norm E F h (f
        F) = f E) :
    ∃! x : FieldOfNorms K L, ∀ E, FieldOfNorms.coord K L E x = f E := by
  suffices ∃ x : FieldOfNorms K L, ∀ E, FieldOfNorms.coord K L E x = f E by
    obtain ⟨x, hx⟩ := this
    exact ⟨x, hx, fun y hy => FieldOfNorms.ext K L (fun E => (hy E).trans (hx E).symm)⟩
  by_cases hzero : f FiniteIntermediateField.bottom = 0
  · have hE (E : FiniteIntermediateField K L) : f E = 0 :=
      (FiniteIntermediateField.norm_eq_zero_iff FiniteIntermediateField.bottom E
          (FiniteIntermediateField.bottom_le E) (f E)).mp
        ((hf _ _ _).trans hzero)
    exact ⟨0, fun E => by simp [hE E]⟩
  · have hE (E : FiniteIntermediateField K L) : f E ≠ 0 := by
      intro hx
      apply hzero
      rw [← hf FiniteIntermediateField.bottom E (FiniteIntermediateField.bottom_le E), hx]
      exact (FiniteIntermediateField.norm_eq_zero_iff _ _ _ 0).mpr rfl
    let x : FieldOfNorms.normCompatibleUnits K L :=
      ⟨fun E => Units.mk0 (f E) (hE E), fun E F h => Units.ext (hf E F h)⟩
    exact ⟨(x : FieldOfNorms K L), fun _ => rfl⟩

end

end FontaineWintenberger
