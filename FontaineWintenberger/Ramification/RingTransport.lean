/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.Ramification.Transport

/-!
# Ramification under equivariant DVR isomorphisms

Normalized valuations are preserved by actual ring isomorphisms. This
transports the intrinsic orders and both numberings between isomorphic
integral rings, retaining their actual displacement definitions.
-/

@[expose] public section

namespace FontaineWintenberger

section RingEquiv

variable {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]

theorem addVal_ringEquiv (r : R ≃+* S) (x : R) :
    IsDiscreteValuationRing.addVal S (r x) = IsDiscreteValuationRing.addVal R x := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  rw [← mem_maximalIdeal_pow_iff_addVal, ← mem_maximalIdeal_pow_iff_addVal]
  have hmap : (IsLocalRing.maximalIdeal R ^ n).map r = IsLocalRing.maximalIdeal S ^ n := by
    rw [Ideal.map_pow]
    exact congrArg (fun I : Ideal S => I ^ n)
      (IsLocalRing.map_maximalIdeal_of_surjective r.toRingHom r.surjective)
  rw [← hmap, Ideal.mem_map_iff_of_surjective r r.surjective]
  constructor
  · rintro ⟨y, hy, h⟩
    exact r.injective h ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

variable {G G' : Type*} [Group G] [Group G']
    [MulSemiringAction G R] [MulSemiringAction G' S]
variable (r : R ≃+* S) (e : G ≃* G')
    (he : ∀ (g : G) (a : R), r (g • a) = e g • r a)

include r e he

theorem ramificationOrder_equivariant (g : G) :
    ramificationOrder (R := S) G' (e g) = ramificationOrder (R := R) G g := by
  unfold ramificationOrder
  symm
  apply r.toEquiv.iInf_congr
  intro x
  change IsDiscreteValuationRing.addVal S (e g • r x - r x) =
    IsDiscreteValuationRing.addVal R (g • x - x)
  rw [← he, ← map_sub, addVal_ringEquiv]

theorem lowerRamificationGroupReal_map_equivariant (t : ℝ) :
    (lowerRamificationGroupReal G (IsLocalRing.maximalIdeal R) t).map e.toMonoidHom =
      lowerRamificationGroupReal G' (IsLocalRing.maximalIdeal S) t := by
  ext g
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    change e h ∈ lowerRamificationGroupReal G' (IsLocalRing.maximalIdeal S) t
    rw [mem_lowerRamificationGroupReal_iff_le_order, ramificationOrder_equivariant r e he]
    exact (mem_lowerRamificationGroupReal_iff_le_order G t h).mp hh
  · intro hg
    refine ⟨e.symm g, ?_, e.apply_symm_apply g⟩
    rw [mem_lowerRamificationGroupReal_iff_le_order,
      ← ramificationOrder_equivariant r e he, e.apply_symm_apply]
    exact (mem_lowerRamificationGroupReal_iff_le_order G' t g).mp hg

theorem card_lowerRamificationGroupReal_equivariant (t : ℝ) :
    Nat.card (lowerRamificationGroupReal G' (IsLocalRing.maximalIdeal S) t) =
      Nat.card (lowerRamificationGroupReal G (IsLocalRing.maximalIdeal R) t) := by
  rw [← lowerRamificationGroupReal_map_equivariant r e he t]
  exact Subgroup.card_map_of_injective e.injective

theorem herbrandFunction_equivariant (t : ℝ) :
    herbrandFunction (R := S) G' t = herbrandFunction (R := R) G t := by
  have hzero : Nat.card (lowerRamificationGroup G' (IsLocalRing.maximalIdeal S) 0) =
      Nat.card (lowerRamificationGroup G (IsLocalRing.maximalIdeal R) 0) := by
    simpa [lowerRamificationGroupReal] using card_lowerRamificationGroupReal_equivariant r e he 0
  simp only [herbrandFunction, hzero, card_lowerRamificationGroupReal_equivariant r e he]

variable [Finite G] [Finite G']

theorem inverseHerbrandFunction_equivariant {u : ℝ} (hu : -1 ≤ u) :
    inverseHerbrandFunction (R := S) G' u = inverseHerbrandFunction (R := R) G u := by
  apply (strictMonoOn_herbrandFunction (R := R) G).injOn
    (inverseHerbrandFunction_mem_Ici G' u) (inverseHerbrandFunction_mem_Ici G u)
  rw [← herbrandFunction_equivariant r e he,
    herbrandFunction_inverseHerbrandFunction G' hu,
    herbrandFunction_inverseHerbrandFunction G hu]

theorem upperRamificationGroup_map_equivariant {u : ℝ} (hu : -1 ≤ u) :
    (upperRamificationGroup (R := R) G u).map e.toMonoidHom =
      upperRamificationGroup (R := S) G' u := by
  rw [upperRamificationGroup, upperRamificationGroup,
    lowerRamificationGroupReal_map_equivariant r e he,
    inverseHerbrandFunction_equivariant r e he hu]

end RingEquiv

end FontaineWintenberger
