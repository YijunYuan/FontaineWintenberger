/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.Ramification.Different.TraceIdeal
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.RingTheory.Norm.Transitivity

/-!
# Norm congruence in prime degree

The middle subsets in the product expansion form free orbits under left
translation. Each orbit contributes a trace of an integral element.
-/

@[expose] public section

namespace FontaineWintenberger

open scoped Pointwise

noncomputable section

private def middleSubsets (G : Type*) [Group G] [Fintype G] [DecidableEq G] :
    SubMulAction G (Finset G) where
  carrier := {s | s.Nonempty ∧ s ≠ Finset.univ}
  smul_mem' g s hs := by
    refine ⟨hs.1.smul_finset, ?_⟩
    intro h
    have hinv := congrArg (fun t : Finset G => g⁻¹ • t) h
    rw [inv_smul_smul, Finset.smul_finset_univ] at hinv
    exact hs.2 hinv

private instance middleSubsetsFintype (G : Type*) [Group G] [Fintype G] [DecidableEq G] :
    Fintype (middleSubsets G) := Fintype.ofFinite _

private theorem middleSubsets_stabilizer_eq_bot (G : Type*)
    [Group G] [Fintype G] [DecidableEq G] [Fact (Nat.card G).Prime]
    (s : middleSubsets G) : MulAction.stabilizer G s = ⊥ := by
  rcases (MulAction.stabilizer G s).eq_bot_or_eq_top_of_prime_card with h | h
  · exact h
  · exfalso
    apply s.property.2
    apply Finset.eq_univ_iff_forall.mpr
    intro x
    obtain ⟨y, hy⟩ := s.property.1
    have hfix : (x * y⁻¹) • s = s :=
      (MulAction.mem_stabilizer_iff).mp (by rw [h]; trivial)
    have hval : (x * y⁻¹) • s.val = s.val := congrArg Subtype.val hfix
    have hx := Finset.smul_mem_smul_finset (a := x * y⁻¹) hy
    rw [hval] at hx
    simpa only [smul_eq_mul, inv_mul_cancel_right] using hx

private def freeOrbitEquiv (G X : Type*) [Group G] [MulAction G X]
    (hfree : ∀ x : X, MulAction.stabilizer G x = ⊥) (x : X) :
    G ≃ MulAction.orbit G x :=
  Equiv.ofBijective (fun g => ⟨g • x, MulAction.mem_orbit x g⟩) (by
    constructor
    · intro g h hgh
      have hsmul : g • x = h • x := congrArg Subtype.val hgh
      have hmem : h⁻¹ * g ∈ MulAction.stabilizer G x := by
        rw [MulAction.mem_stabilizer_iff, mul_smul, hsmul, inv_smul_smul]
      have heq : h⁻¹ * g = 1 := by simpa only [hfree x, Subgroup.mem_bot] using hmem
      exact (inv_mul_eq_one.mp heq).symm
    · rintro ⟨y, g, rfl⟩
      exact ⟨g, rfl⟩)

private theorem sum_eq_sum_smul_of_free (G X B : Type*)
    [Group G] [Fintype G] [Finite X] [MulAction G X]
    [CommRing B] [MulSemiringAction G B]
    (hfree : ∀ x : X, MulAction.stabilizer G x = ⊥)
    (f : X → B) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)
    (I : Ideal B) (hfI : ∀ x : X, f x ∈ I) :
    letI := Fintype.ofFinite X
    ∃ z ∈ I, (∑ x : X, f x) = ∑ g : G, g • z := by
  classical
  let := Fintype.ofFinite X
  let Q := Quotient (MulAction.orbitRel G X)
  let := Fintype.ofFinite Q
  let := fun q : Q => Fintype.ofFinite (MulAction.orbit G q.out)
  refine ⟨∑ q : Q, f q.out, I.sum_mem (fun q _ => hfI q.out), ?_⟩
  calc
    (∑ x : X, f x) = ∑ q : Q, ∑ y : MulAction.orbit G q.out, f y.val := by
      rw [← Fintype.sum_sigma (fun y : Σ q : Q, MulAction.orbit G q.out => f y.2.val)]
      exact (Equiv.sum_comp (MulAction.selfEquivSigmaOrbits G X).symm f).symm
    _ = ∑ q : Q, ∑ g : G, g • f q.out := by
      apply Finset.sum_congr rfl
      intro q _
      rw [← Equiv.sum_comp (freeOrbitEquiv G X hfree q.out) (fun y => f y.val)]
      exact Finset.sum_congr rfl (fun g _ => hf g q.out)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro g _
      exact (map_sum (MulSemiringAction.toRingHom G B g) (fun q : Q => f q.out) Finset.univ).symm

private def subsetMonomial (G B : Type*) [Group G] [Fintype G] [DecidableEq G]
    [CommRing B] [MulSemiringAction G B] (α β : B) (s : Finset G) : B :=
  (∏ g ∈ s, g • α) * ∏ g ∈ Finset.univ \ s, g • β

private theorem prod_smul_finset (G B : Type*) [Group G] [DecidableEq G]
    [CommRing B] [MulSemiringAction G B] (g : G) (s : Finset G) (α : B) :
    (∏ h ∈ g • s, h • α) = g • (∏ h ∈ s, h • α) := by
  rw [Finset.smul_finset_def, Finset.prod_image (MulAction.injective g).injOn]
  simp only [smul_eq_mul, mul_smul]
  exact (map_prod (MulSemiringAction.toRingHom G B g) (fun h => h • α) s).symm

private theorem subsetMonomial_smul (G B : Type*) [Group G] [Fintype G] [DecidableEq G]
    [CommRing B] [MulSemiringAction G B] (α β : B) (g : G) (s : Finset G) :
    subsetMonomial G B α β (g • s) = g • subsetMonomial G B α β s := by
  unfold subsetMonomial
  have hc : Finset.univ \ g • s = g • (Finset.univ \ s) := by
    rw [Finset.smul_finset_sdiff, Finset.smul_finset_univ]
  rw [hc, prod_smul_finset G B, prod_smul_finset G B]
  exact (smul_mul' g _ _).symm

private theorem prod_add_sub_eq_sum_middle (G B : Type*)
    [Group G] [Fintype G] [DecidableEq G] [CommRing B] [MulSemiringAction G B]
    (α β : B) :
    (∏ g : G, g • (α + β)) - (∏ g : G, g • α) - (∏ g : G, g • β) =
      ∑ s : middleSubsets G, subsetMonomial G B α β s.val := by
  classical
  let f := subsetMonomial G B α β
  have hexp : (∏ g : G, g • (α + β)) = ∑ s : Finset G, f s := by
    simp only [smul_add]
    rw [Finset.prod_add, Finset.powerset_univ]
    rfl
  have hmid : ((Finset.univ : Finset (Finset G)).erase ∅).erase Finset.univ =
      Finset.univ.filter (fun s : Finset G => s.Nonempty ∧ s ≠ Finset.univ) := by
    ext s
    simp [Finset.nonempty_iff_ne_empty, and_comm]
  have huniv : (Finset.univ : Finset G) ≠ ∅ :=
    Finset.nonempty_iff_ne_empty.mp ⟨1, Finset.mem_univ 1⟩
  have hsum := Finset.sum_erase_add (Finset.univ : Finset (Finset G)) f
    (Finset.mem_univ (∅ : Finset G))
  have hsum' := Finset.sum_erase_add ((Finset.univ : Finset (Finset G)).erase ∅) f
    (show (Finset.univ : Finset G) ∈ (Finset.univ : Finset (Finset G)).erase ∅ by simp [huniv])
  have hempty : f ∅ = ∏ g : G, g • β := by simp [f, subsetMonomial]
  have hfull : f Finset.univ = ∏ g : G, g • α := by simp [f, subsetMonomial]
  rw [hmid] at hsum'
  have hsub := Finset.sum_subtype (p := fun s : Finset G => s ∈ middleSubsets G)
    (F := middleSubsetsFintype G) (Finset.univ.filter
    (fun s : Finset G => s.Nonempty ∧ s ≠ Finset.univ))
    (fun s => by
      change (s ∈ Finset.univ.filter (fun s : Finset G => s.Nonempty ∧ s ≠ Finset.univ)) ↔
        (s.Nonempty ∧ s ≠ Finset.univ)
      simp) f
  rw [hsub] at hsum'
  rw [hexp]
  rw [hempty] at hsum
  rw [hfull] at hsum'
  linear_combination -hsum - hsum'

/-- For a prime-order action, the defect of multiplicativity across addition
is a transfer of an element of the same ring. -/
theorem exists_prod_add_sub_eq_sum_smul (G B : Type*)
    [Group G] [Fintype G] [Fact (Nat.card G).Prime]
    [CommRing B] [MulSemiringAction G B] (α β : B) :
    ∃ z : B, (∏ g : G, g • (α + β)) - (∏ g : G, g • α) - (∏ g : G, g • β) =
      ∑ g : G, g • z := by
  classical
  obtain ⟨z, _hzI, hz⟩ := sum_eq_sum_smul_of_free G (middleSubsets G) B
    (middleSubsets_stabilizer_eq_bot G)
    (fun s => subsetMonomial G B α β s.val)
    (fun g s => subsetMonomial_smul G B α β g s.val) ⊤ (fun _ => trivial)
  exact ⟨z, (prod_add_sub_eq_sum_middle G B α β).trans hz⟩

/-- The transfer representative stays in any stable ideal containing
one input. This controls the precision of the prime norm defect. -/
theorem exists_prod_add_sub_eq_sum_smul_mem (G B : Type*)
    [Group G] [Fintype G] [Fact (Nat.card G).Prime]
    [CommRing B] [MulSemiringAction G B] (I : Ideal B)
    (hI : ∀ (g : G) (x : B), x ∈ I → g • x ∈ I) (α β : B) (hα : α ∈ I) :
    ∃ z ∈ I, (∏ g : G, g • (α + β)) - (∏ g : G, g • α) - (∏ g : G, g • β) =
      ∑ g : G, g • z := by
  classical
  have hm (s : middleSubsets G) : subsetMonomial G B α β s.val ∈ I := by
    obtain ⟨g, hg⟩ := s.property.1
    exact I.mul_mem_right _ (I.prod_mem hg (hI g α hα))
  obtain ⟨z, hzI, hz⟩ := sum_eq_sum_smul_of_free G (middleSubsets G) B
    (middleSubsets_stabilizer_eq_bot G)
    (fun s => subsetMonomial G B α β s.val)
    (fun g s => subsetMonomial_smul G B α β g s.val) I hm
  exact ⟨z, hzI, (prod_add_sub_eq_sum_middle G B α β).trans hz⟩

section Spectral

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

local notation "OK" => Valuation.valuationSubring (NormedField.valuation (K := K))
local notation "OL" => spectralIntegerRing K L
local notation "GL" => L ≃ₐ[K] L

/-- The integral norm on the spectral integers is the product
over the full field Galois action. -/
theorem spectralIntegerRing_algebraMap_intNorm_eq_prod (x : OL) :
    algebraMap OK OL (Algebra.intNorm OK OL x) = ∏ g : GL, g • x := by
  apply FaithfulSMul.algebraMap_injective OL L
  rw [← IsScalarTower.algebraMap_apply OK OL L,
    IsScalarTower.algebraMap_apply OK K L, Algebra.algebraMap_intNorm (L := L),
    Algebra.norm_eq_prod_automorphisms, map_prod]
  rfl

/-- The integral trace is the transfer under the same field action. -/
theorem spectralIntegerRing_algebraMap_intTrace_eq_sum (x : OL) :
    algebraMap OK OL (Algebra.intTrace OK OL x) = ∑ g : GL, g • x := by
  apply FaithfulSMul.algebraMap_injective OL L
  rw [← IsScalarTower.algebraMap_apply OK OL L,
    IsScalarTower.algebraMap_apply OK K L, Algebra.algebraMap_intTrace (L := L),
    trace_eq_sum_automorphisms, map_sum]
  rfl

/-- The integral norm defect in prime degree is the trace
of an element of the same integral closure. -/
theorem spectralIntegerRing_exists_intNorm_add_sub_eq_intTrace
    (hp : (Module.finrank K L).Prime) (α β : OL) :
    ∃ z : OL, Algebra.intNorm OK OL (α + β) - Algebra.intNorm OK OL α -
      Algebra.intNorm OK OL β = Algebra.intTrace OK OL z := by
  classical
  have : Fact (Nat.card GL).Prime := ⟨by rwa [IsGalois.card_aut_eq_finrank K L]⟩
  obtain ⟨z, hz⟩ := exists_prod_add_sub_eq_sum_smul GL OL α β
  refine ⟨z, (FaithfulSMul.algebraMap_injective OK OL) ?_⟩
  simpa only [map_sub, spectralIntegerRing_algebraMap_intNorm_eq_prod,
    spectralIntegerRing_algebraMap_intTrace_eq_sum] using hz

/-- The prime-degree trace representative retains every prescribed
maximal-ideal power of the first input. -/
theorem spectralIntegerRing_exists_intNorm_add_sub_eq_intTrace_mem_pow
    (hp : (Module.finrank K L).Prime) (r : ℕ) (α β : OL)
    (hα : α ∈ IsLocalRing.maximalIdeal OL ^ r) :
    ∃ z ∈ IsLocalRing.maximalIdeal OL ^ r,
      Algebra.intNorm OK OL (α + β) - Algebra.intNorm OK OL α - Algebra.intNorm OK OL β =
        Algebra.intTrace OK OL z := by
  classical
  have : Fact (Nat.card GL).Prime := ⟨by rwa [IsGalois.card_aut_eq_finrank K L]⟩
  have hI (g : GL) (x : OL) (hx : x ∈ IsLocalRing.maximalIdeal OL ^ r) :
      g • x ∈ IsLocalRing.maximalIdeal OL ^ r := by
    rw [mem_maximalIdeal_pow_iff_addVal, addVal_smul]
    exact (mem_maximalIdeal_pow_iff_addVal x r).mp hx
  obtain ⟨z, hzI, hz⟩ := exists_prod_add_sub_eq_sum_smul_mem GL OL
    (IsLocalRing.maximalIdeal OL ^ r) hI α β hα
  refine ⟨z, hzI, (FaithfulSMul.algebraMap_injective OK OL) ?_⟩
  simpa only [map_sub, spectralIntegerRing_algebraMap_intNorm_eq_prod,
    spectralIntegerRing_algebraMap_intTrace_eq_sum] using hz

/-- The difference of two integral norms has a controlled trace
error after the norm of their difference is removed. -/
theorem spectralIntegerRing_intNorm_sub_sub_mem_intTraceIdeal_pow
    (hp : (Module.finrank K L).Prime) (r : ℕ) (α β : OL)
    (hδ : α - β ∈ IsLocalRing.maximalIdeal OL ^ r) :
    Algebra.intNorm OK OL α - Algebra.intNorm OK OL β - Algebra.intNorm OK OL (α - β) ∈
      intTraceIdeal OK OL (IsLocalRing.maximalIdeal OL ^ r) := by
  obtain ⟨z, hzI, hz⟩ :=
    spectralIntegerRing_exists_intNorm_add_sub_eq_intTrace_mem_pow K L hp r (α - β) β hδ
  have he : Algebra.intNorm OK OL α - Algebra.intNorm OK OL β -
      Algebra.intNorm OK OL (α - β) = Algebra.intTrace OK OL z := by
    simp only [sub_add_cancel] at hz
    linear_combination hz
  rw [he, intTraceIdeal, Submodule.mem_map]
  exact ⟨z, hzI, rfl⟩

/-- The congruence uses the trace ideal, without a residue-field
finiteness, total-ramification, or characteristic-zero assumption. -/
theorem spectralIntegerRing_intNorm_add_sub_mem_intTraceIdeal
    (hp : (Module.finrank K L).Prime) (α β : OL) :
    Algebra.intNorm OK OL (α + β) - Algebra.intNorm OK OL α - Algebra.intNorm OK OL β ∈
      intTraceIdeal OK OL ⊤ := by
  obtain ⟨z, hz⟩ := spectralIntegerRing_exists_intNorm_add_sub_eq_intTrace K L hp α β
  rw [intTraceIdeal, Submodule.mem_map]
  exact ⟨z, by trivial, hz.symm⟩


end Spectral

end

end FontaineWintenberger
