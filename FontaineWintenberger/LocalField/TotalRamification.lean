module

public import FontaineWintenberger.Ramification.Degree
public import FontaineWintenberger.Ramification.Tower

/-!
# Total ramification in actual local towers

The actual residue map factors through the actual intermediate residue
field. Its surjectivity is equivalent to surjectivity of both factors,
which gives total ramification of every step of a totally ramified tower.
-/

@[expose] public section

namespace FontaineWintenberger

variable (R S T : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [FaithfulSMul R S] [FaithfulSMul S T]
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S T)]
    [IsLocalHom (algebraMap R T)] [Module.Finite R S] [Module.Finite S T]

/-- Total ramification of an actual local DVR tower is equivalent to total
ramification of both actual steps. -/
theorem ramificationIdx_eq_finrank_tower_iff :
    (IsLocalRing.maximalIdeal T).ramificationIdx R = Module.finrank R T ↔
      (IsLocalRing.maximalIdeal S).ramificationIdx R = Module.finrank R S ∧
      (IsLocalRing.maximalIdeal T).ramificationIdx S = Module.finrank S T := by
  let : Module.Finite R T := Module.Finite.trans S T
  let : FaithfulSMul R T := FaithfulSMul.trans R S T
  rw [ramificationIdx_eq_finrank_iff_residue_surjective R T,
    ramificationIdx_eq_finrank_iff_residue_surjective R S,
    ramificationIdx_eq_finrank_iff_residue_surjective S T]
  constructor
  · intro h
    constructor
    · intro s
      obtain ⟨r, hr⟩ := h (algebraMap (IsLocalRing.ResidueField S)
        (IsLocalRing.ResidueField T) s)
      refine ⟨r, (algebraMap (IsLocalRing.ResidueField S)
        (IsLocalRing.ResidueField T)).injective ?_⟩
      rw [← IsScalarTower.algebraMap_apply (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField S) (IsLocalRing.ResidueField T)]
      exact hr
    · intro t
      obtain ⟨r, hr⟩ := h t
      refine ⟨algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) r, ?_⟩
      rw [← IsScalarTower.algebraMap_apply (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField S) (IsLocalRing.ResidueField T)]
      exact hr
  · rintro ⟨hRS, hST⟩ t
    obtain ⟨s, hs⟩ := hST t
    obtain ⟨r, rfl⟩ := hRS s
    refine ⟨r, ?_⟩
    rw [IsScalarTower.algebraMap_apply (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S) (IsLocalRing.ResidueField T)]
    exact hs

end FontaineWintenberger
