/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Mathlib.FieldTheory.FiniteIntermediateField
public import Mathlib.Algebra.GroupWithZero.WithZero

/-!
# The field of norms: multiplicative structure

## The multiplicative field of norms over all finite intermediate fields

No normality or APF assumption is needed for this multiplicative construction.
The transition maps are field norms on finite extensions.

## Extension from cofinal norm coordinates

Any cofinal set of finite fields determines and constructs
the same zero-adjoined unit field of norms. This supplies the covariant finite
functor before its additive and topological properties.
-/

@[expose] public section

namespace FontaineWintenberger

noncomputable section

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
/-- The subgroup of norm-compatible families of units over all finite intermediate fields. -/
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

/-- The single multiplicative carrier for the field of norms: its unit
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

/-- Evaluation at a finite intermediate field, extended by zero. -/
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

/-- The coordinates satisfy the finite-layer norm equations. -/
theorem FieldOfNorms.coord_norm (E F : FiniteIntermediateField K L) (h : E ≤ F) (x : FieldOfNorms K
    L) :
    FiniteIntermediateField.norm E F h (FieldOfNorms.coord K L F x) = FieldOfNorms.coord K L E x :=
        by
  induction x using FieldOfNorms.recZeroCoe with
  | zero =>
      exact (FiniteIntermediateField.norm_eq_zero_iff E F h 0).mpr rfl
  | coe x =>
      exact congrArg Units.val (x.property E F h)

/-- Every compatible field family is represented uniquely by the single
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

noncomputable section

namespace FontaineWintenberger

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- Evaluations on any cofinal set already distinguish
elements of the zero-adjoined unit limit. -/
theorem FieldOfNorms.ext_cofinal (P : FiniteIntermediateField K L → Prop)
    (hP : ∀ E, ∃ F, P F ∧ E ≤ F) {α β : FieldOfNorms K L}
    (h : ∀ E, P E → FieldOfNorms.coord K L E α = FieldOfNorms.coord K L E β) : α = β := by
  apply FieldOfNorms.ext K L
  intro E
  obtain ⟨F, hF, hEF⟩ := hP E
  rw [← FieldOfNorms.coord_norm K L E F hEF α,
    ← FieldOfNorms.coord_norm K L E F hEF β, h F hF]

/-- Any compatible cofinal coordinate family extends uniquely to the
same field of norms, using finite field norms. -/
theorem existsUnique_fieldOfNorms_of_compatible_cofinal (P : FiniteIntermediateField K L → Prop)
    (hP : ∀ E, ∃ F, P F ∧ E ≤ F)
    (x : ∀ E, P E → E.val)
    (hx : ∀ (E F : FiniteIntermediateField K L) (hE : P E) (hF : P F) (hEF : E ≤ F),
      FiniteIntermediateField.norm E F hEF (x F hF) = x E hE) :
    ∃! α : FieldOfNorms K L, ∀ (E : FiniteIntermediateField K L) (hE : P E),
      FieldOfNorms.coord K L E α = x E hE := by
  let u (E : FiniteIntermediateField K L) := (hP E).choose
  have hu (E : FiniteIntermediateField K L) : P (u E) := (hP E).choose_spec.1
  have hEu (E : FiniteIntermediateField K L) : E ≤ u E := (hP E).choose_spec.2
  let f (E : FiniteIntermediateField K L) := FiniteIntermediateField.norm E (u E) (hEu E) (x (u E)
      (hu E))
  have hf (E F : FiniteIntermediateField K L) (hEF : E ≤ F) :
      FiniteIntermediateField.norm E F hEF (f F) = f E := by
    obtain ⟨G, hG, hUG⟩ := hP (FiniteIntermediateField.sup (u E) (u F))
    have hEG : u E ≤ G := (FiniteIntermediateField.le_sup_left (u E) (u F)).trans hUG
    have hFG : u F ≤ G := (FiniteIntermediateField.le_sup_right (u E) (u F)).trans hUG
    dsimp only [f]
    rw [← hx (u E) G (hu E) hG hEG, ← hx (u F) G (hu F) hG hFG]
    simp only [FiniteIntermediateField.norm_norm]
  obtain ⟨α, hα, _⟩ := existsUnique_fieldOfNorms_of_compatible K L f hf
  have hαP (E : FiniteIntermediateField K L) (hE : P E) : FieldOfNorms.coord K L E α = x E hE :=
    (hα E).trans (hx E (u E) hE (hu E) (hEu E))
  refine ⟨α, hαP, ?_⟩
  intro β hβ
  apply FieldOfNorms.ext_cofinal K L P hP
  intro E hE
  exact (hβ E hE).trans (hαP E hE).symm

/-- The canonical extension of compatible cofinal coordinates. -/
def FieldOfNorms.ofCofinal (P : FiniteIntermediateField K L → Prop)
    (hP : ∀ E, ∃ F, P F ∧ E ≤ F)
    (x : ∀ E, P E → E.val)
    (hx : ∀ (E F : FiniteIntermediateField K L) (hE : P E) (hF : P F) (hEF : E ≤ F),
      FiniteIntermediateField.norm E F hEF (x F hF) = x E hE) : FieldOfNorms K L :=
  (existsUnique_fieldOfNorms_of_compatible_cofinal K L P hP x hx).choose

/-- Every prescribed cofinal coordinate is retained exactly. -/
@[simp]
theorem FieldOfNorms.coord_ofCofinal (P : FiniteIntermediateField K L → Prop)
    (hP : ∀ E, ∃ F, P F ∧ E ≤ F)
    (x : ∀ E, P E → E.val)
    (hx : ∀ (E F : FiniteIntermediateField K L) (hE : P E) (hF : P F) (hEF : E ≤ F),
      FiniteIntermediateField.norm E F hEF (x F hF) = x E hE)
    (E : FiniteIntermediateField K L) (hE : P E) :
    FieldOfNorms.coord K L E (FieldOfNorms.ofCofinal K L P hP x hx) = x E hE :=
  (existsUnique_fieldOfNorms_of_compatible_cofinal K L P hP x hx).choose_spec.1 E hE

/-- Any finite field is computed from any prescribed cofinal upper
field by its norm, independently of the choice. -/
theorem FieldOfNorms.coord_ofCofinal_of_le (P : FiniteIntermediateField K L → Prop)
    (hP : ∀ E, ∃ F, P F ∧ E ≤ F)
    (x : ∀ E, P E → E.val)
    (hx : ∀ (E F : FiniteIntermediateField K L) (hE : P E) (hF : P F) (hEF : E ≤ F),
      FiniteIntermediateField.norm E F hEF (x F hF) = x E hE)
    (E F : FiniteIntermediateField K L) (hF : P F) (hEF : E ≤ F) :
    FieldOfNorms.coord K L E (FieldOfNorms.ofCofinal K L P hP x hx) =
      FiniteIntermediateField.norm E F hEF (x F hF) := by
  rw [← FieldOfNorms.coord_norm K L E F hEF, FieldOfNorms.coord_ofCofinal]

end FontaineWintenberger
