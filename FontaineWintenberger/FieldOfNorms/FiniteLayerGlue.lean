/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.FieldOfNorms.Multiplicative
public import Mathlib.Algebra.Algebra.Subalgebra.Directed

/-!
# Gluing algebra homomorphisms on the actual finite intermediate fields

An algebraic field extension is the directed union of its finite intermediate
fields. Compatible algebra homomorphisms on these fields therefore give a unique
algebra homomorphism on the original extension.
-/

@[expose] public section

namespace FontaineWintenberger

noncomputable section

open IntermediateField

namespace FiniteIntermediateField

variable {L M N : Type*} [Field L] [Field M] [Field N]
  [Algebra L M] [Algebra L N]

/-- The actual finite intermediate fields form a directed family of subalgebras. -/
theorem directed_toSubalgebra :
    Directed (· ≤ ·) (fun Q : FiniteIntermediateField L M => Q.val.toSubalgebra) := by
  intro Q R
  exact ⟨sup Q R, le_sup_left Q R, le_sup_right Q R⟩

/-- Every element of an algebraic extension lies in an actual finite intermediate field. -/
theorem exists_mem [Algebra.IsAlgebraic L M] (x : M) :
    ∃ Q : FiniteIntermediateField L M, x ∈ Q.val := by
  exact ⟨⟨L⟮x⟯, IntermediateField.adjoin.finiteDimensional
    (Algebra.IsIntegral.isIntegral x)⟩, IntermediateField.mem_adjoin_simple_self L x⟩

/-- The directed supremum of all actual finite intermediate fields is the original extension. -/
theorem iSup_toSubalgebra_eq_top [Algebra.IsAlgebraic L M] :
    (⨆ Q : FiniteIntermediateField L M, Q.val.toSubalgebra) = ⊤ := by
  apply le_antisymm le_top
  intro x _
  obtain ⟨Q, hx⟩ := exists_mem (L := L) x
  exact (le_iSup (fun Q : FiniteIntermediateField L M => Q.val.toSubalgebra) Q) hx

variable [Algebra.IsAlgebraic L M]
  (f : ∀ Q : FiniteIntermediateField L M, Q.val →ₐ[L] N)
  (hf : ∀ (Q R : FiniteIntermediateField L M) (h : Q ≤ R),
    f Q = (f R).comp (IntermediateField.inclusion h))

/-- Glue compatible maps on finite intermediate fields to an algebra homomorphism
on the original algebraic extension. -/
def liftAlgHom : M →ₐ[L] N := by
  letI : Nonempty (FiniteIntermediateField L M) := ⟨bottom⟩
  exact (Subalgebra.iSupLift (fun Q : FiniteIntermediateField L M => Q.val.toSubalgebra)
    directed_toSubalgebra f hf ⊤ (by rw [iSup_toSubalgebra_eq_top])).comp
      Subalgebra.topEquiv.symm.toAlgHom

/-- The glued map agrees with the supplied map on every actual finite intermediate field. -/
@[simp]
theorem liftAlgHom_apply (Q : FiniteIntermediateField L M) (x : Q.val) :
    liftAlgHom f hf (x : M) = f Q x := by
  let : Nonempty (FiniteIntermediateField L M) := ⟨bottom⟩
  change Subalgebra.iSupLift (fun Q : FiniteIntermediateField L M => Q.val.toSubalgebra)
    directed_toSubalgebra f hf ⊤ _ ⟨x, Algebra.mem_top⟩ = f Q x
  exact Subalgebra.iSupLift_mk (f := f) (hf := hf) (x := x) (hx := Algebra.mem_top)

/-- Restricting the glued map to a finite intermediate field gives the original component. -/
@[simp]
theorem liftAlgHom_comp_val (Q : FiniteIntermediateField L M) :
    (liftAlgHom f hf).comp Q.val.val = f Q := by
  ext x
  exact liftAlgHom_apply f hf Q x

/-- Algebra homomorphisms from an algebraic extension are determined by their
restrictions to its actual finite intermediate fields. -/
theorem algHom_ext {g h : M →ₐ[L] N}
    (hgh : ∀ Q : FiniteIntermediateField L M, g.comp Q.val.val = h.comp Q.val.val) : g = h := by
  ext x
  obtain ⟨Q, hx⟩ := exists_mem (L := L) x
  exact AlgHom.congr_fun (hgh Q) ⟨x, hx⟩

/-- The glued map is the unique algebra homomorphism with the given restrictions. -/
theorem liftAlgHom_unique (g : M →ₐ[L] N)
    (hg : ∀ Q : FiniteIntermediateField L M, g.comp Q.val.val = f Q) : g = liftAlgHom f hf := by
  apply algHom_ext
  intro Q
  rw [hg Q, liftAlgHom_comp_val]

end FiniteIntermediateField

end

end FontaineWintenberger
