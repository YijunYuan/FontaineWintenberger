/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.AtTopBot.Map
public import Mathlib.Algebra.Algebra.Subalgebra.Directed

/-!
# Finite intermediate fields of a field extension

## The multiplicative field of norms over all finite intermediate fields

No normality or APF assumption is needed for this multiplicative construction.
The transition maps are actual field norms on genuinely finite extensions.

## Addition on the original multiplicative field of norms

The actual norm-sum nets are indexed by all finite intermediate fields above
a fixed original field. Uniform Herbrand control transfers their deep-tail
norm defects to a Cauchy estimate in that original complete finite field.

## Isomorphisms of the original norm fields

Actual field isomorphisms reindex the original finite norm families.
Their original norm-sum limits and stable valuations are preserved.

## Gluing algebra homomorphisms on the actual finite intermediate fields

An algebraic field extension is the directed union of its finite intermediate
fields. Compatible algebra homomorphisms on these fields therefore give a unique
algebra homomorphism on the original extension.
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

end

end FontaineWintenberger

namespace FontaineWintenberger

open Filter

section Nets

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

instance FiniteIntermediateField.instNonempty : Nonempty (FiniteIntermediateField K L) :=
    ⟨FiniteIntermediateField.bottom⟩

instance FiniteIntermediateField.instIsDirectedOrder : IsDirectedOrder (FiniteIntermediateField K
    L) :=
  ⟨fun E F => ⟨FiniteIntermediateField.sup E F, FiniteIntermediateField.le_sup_left E F,
    FiniteIntermediateField.le_sup_right E F⟩⟩

instance FiniteIntermediateField.instIciIsDirectedOrder (E : FiniteIntermediateField K L) :
    IsDirectedOrder (Set.Ici E) :=
  ⟨fun F G => ⟨⟨FiniteIntermediateField.sup F.val G.val,
    F.property.trans (FiniteIntermediateField.le_sup_left F.val G.val)⟩,
    FiniteIntermediateField.le_sup_left F.val G.val, FiniteIntermediateField.le_sup_right F.val
        G.val⟩⟩
/-- Every further original finite-field tail is cofinal in the norm-sum index. -/
theorem FiniteIntermediateField.tendsto_Ici_inclusion (E F : FiniteIntermediateField K L) (hEF : E
    ≤ F) :
    Tendsto (fun G : Set.Ici F => (⟨G.val, hEF.trans G.property⟩ : Set.Ici E)) atTop atTop := by
  apply tendsto_atTop.mpr
  intro T
  refine eventually_atTop.mpr ⟨⟨FiniteIntermediateField.sup F T.val,
    FiniteIntermediateField.le_sup_left F T.val⟩, fun G hG => ?_⟩
  exact (FiniteIntermediateField.le_sup_right F T.val).trans hG

/-- Passing to any actual finite-field tail preserves the entire tail filter. -/
theorem FiniteIntermediateField.map_Ici_inclusion_atTop (E F : FiniteIntermediateField K L) (hEF :
    E ≤ F) :
    map (fun G : Set.Ici F => (⟨G.val, hEF.trans G.property⟩ : Set.Ici E)) atTop = atTop := by
  apply le_antisymm (FiniteIntermediateField.tendsto_Ici_inclusion K L E F hEF)
  intro s hs
  obtain ⟨a, ha⟩ := eventually_atTop.mp hs
  refine eventually_atTop.mpr ⟨⟨a.val, hEF.trans a.property⟩, fun b hb => ?_⟩
  exact ha ⟨b.val, a.property.trans (show a.val ≤ b.val from hb)⟩ hb

end Nets

end FontaineWintenberger

namespace FontaineWintenberger

noncomputable section

variable {K L M N : Type*} [Field K] [Field L] [Field M] [Field N]
    [Algebra K L] [Algebra K M] [Algebra K N]
namespace FiniteIntermediateField

/-- The image of an actual finite intermediate field under a specified field embedding. -/
def map (i : L →ₐ[K] M) (E : FiniteIntermediateField K L) : FiniteIntermediateField K M :=
  ⟨E.val.map i, Module.Finite.equiv (IntermediateField.equivMap E.val i).toLinearEquiv⟩

/-- The original embedding restricts to the actual finite image field. -/
def equivMap (i : L →ₐ[K] M) (E : FiniteIntermediateField K L) : E.val ≃ₐ[K] (map i E).val :=
  IntermediateField.equivMap E.val i

@[simp]
theorem coe_equivMap (i : L →ₐ[K] M) (E : FiniteIntermediateField K L) (x : E.val) :
    (equivMap i E x : M) = i (x : L) := rfl

theorem map_mono (i : L →ₐ[K] M) {E F : FiniteIntermediateField K L} (hEF : E ≤ F) :
    map i E ≤ map i F := IntermediateField.map_mono i hEF

@[simp]
theorem map_id (E : FiniteIntermediateField K L) : map (AlgHom.id K L) E = E := by
  apply Subtype.ext
  exact IntermediateField.map_id E.val

@[simp]
theorem map_map (i : L →ₐ[K] M) (j : M →ₐ[K] N) (E : FiniteIntermediateField K L) :
    map j (map i E) = map (j.comp i) E := by
  apply Subtype.ext
  exact IntermediateField.map_map E.val i j

/-- A field isomorphism gives the actual order isomorphism on finite intermediate fields. -/
def mapOrderIso (e : L ≃ₐ[K] M) : FiniteIntermediateField K L ≃o FiniteIntermediateField K M where
  toFun := map e.toAlgHom
  invFun := map e.symm.toAlgHom
  left_inv E := by simp
  right_inv E := by simp
  map_rel_iff' := by
    intro E F
    constructor
    · intro h x hx
      exact (F.val.map_mem_map e.toAlgHom).mp
        (h ((E.val.map_mem_map e.toAlgHom).mpr hx))
    · exact map_mono e.toAlgHom

/-- Actual relative field norms commute with two compatible restrictions
of the original field isomorphism, with no normality hypothesis. -/
theorem equivMap_norm (i : L →ₐ[K] M) (E F : FiniteIntermediateField K L)
    (hEF : E ≤ F) (x : F.val) :
    equivMap i E (norm E F hEF x) =
      norm (map i E) (map i F) (map_mono i hEF) (equivMap i F x) := by
  let : Algebra E.val F.val := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
  let : Algebra (map i E).val (map i F).val :=
    (IntermediateField.inclusion (map_mono i hEF)).toRingHom.toAlgebra
  have he : (algebraMap (map i E).val (map i F).val).comp
      (equivMap i E).toRingEquiv.toRingHom =
      (equivMap i F).toRingEquiv.toRingHom.comp (algebraMap E.val F.val) := by
    ext a
    rfl
  apply (equivMap i E).symm.injective
  change (equivMap i E).symm (equivMap i E (Algebra.norm E.val x)) =
    (equivMap i E).symm (Algebra.norm (map i E).val (equivMap i F x))
  rw [AlgEquiv.symm_apply_apply]
  exact Algebra.norm_eq_of_equiv_equiv (equivMap i E).toRingEquiv
    (equivMap i F).toRingEquiv he x

end FiniteIntermediateField
/-- The actual finite-layer map restricted to the original upper tail. -/
def FiniteIntermediateField.mapIci (i : L →ₐ[K] M) (E : FiniteIntermediateField K L) (F : Set.Ici
    E) :
    Set.Ici (FiniteIntermediateField.map i E) :=
  ⟨FiniteIntermediateField.map i F.val, FiniteIntermediateField.map_mono i F.property⟩

/-- A field isomorphism takes the original finite upper-tail filter to
the corresponding upper-tail filter. -/
theorem FiniteIntermediateField.tendsto_mapIci (e : L ≃ₐ[K] M) (E : FiniteIntermediateField K L) :
    Filter.Tendsto (FiniteIntermediateField.mapIci e.toAlgHom E) Filter.atTop Filter.atTop := by
  apply Filter.tendsto_Ici_atTop.mpr
  have hv : Filter.Tendsto (Subtype.val : Set.Ici E → FiniteIntermediateField K L)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_Ici_atTop.mp (Filter.tendsto_id :
      Filter.Tendsto (id : Set.Ici E → Set.Ici E) Filter.atTop Filter.atTop)
  exact (FiniteIntermediateField.mapOrderIso e).tendsto_atTop.comp hv

end

end FontaineWintenberger

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
