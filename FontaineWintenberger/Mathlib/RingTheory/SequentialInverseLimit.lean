/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Data.Nat.Init
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.UniformSpace.Pi

/-!
# Sequential inverse limits of truncated rings

The inverse limit is the intersection of the canonical ring equalizers
inside the coefficient product. Surjective transition maps give
surjective projections without any finiteness assumption on the rings.
The discrete product uniformity supplies Hausdorffness and completeness.
-/

@[expose] public section

noncomputable section

open scoped Topology

namespace FontaineWintenberger.SequentialInverseLimit

universe u

variable (B : ℕ → Type u) [∀ n, CommRing (B n)]
    (q : ∀ n, B (n + 1) →+* B n)

/-- The compatible-family subring is the intersection of the
canonical equalizer subrings in the product. -/
def subring : Subring (∀ n, B n) :=
  ⨅ n, RingHom.eqLocus ((q n).comp (Pi.evalRingHom B (n + 1))) (Pi.evalRingHom B n)

@[simp]
theorem mem_subring (a : ∀ n, B n) :
    a ∈ subring B q ↔ ∀ n, q n (a (n + 1)) = a n := by
  simp [subring]

/-- Evaluation on the compatible-family subring. -/
def projection (n : ℕ) : subring B q →+* B n :=
  (Pi.evalRingHom B n).comp (subring B q).subtype

@[simp]
theorem projection_apply (n : ℕ) (a : subring B q) : projection B q n a = a.val n := rfl

/-- Adjacent compatibility holds on the family. -/
theorem compatible (a : subring B q) (n : ℕ) :
    q n (projection B q (n + 1) a) = projection B q n a :=
  (mem_subring B q a.val).mp a.property n

/-- The finite composite of the adjacent transition homomorphisms. -/
def transition (i j : ℕ) (hij : i ≤ j) : B j →+* B i :=
  Nat.leRecOn (C := fun j => B j →+* B i) hij
    (fun {j} f => f.comp (q j)) (RingHom.id (B i))

@[simp]
theorem transition_self (i : ℕ) : transition B q i i le_rfl = RingHom.id (B i) := by
  simp only [transition, Nat.leRecOn_self]

theorem transition_succ (i j : ℕ) (hij : i ≤ j) :
    transition B q i (j + 1) (hij.trans (Nat.le_succ j)) =
      (transition B q i j hij).comp (q j) := by
  simp only [transition, Nat.leRecOn_succ hij]

@[simp]
theorem transition_succ_self (i : ℕ) :
    transition B q i (i + 1) (Nat.le_succ i) = q i := by
  rw [transition_succ B q i i le_rfl, transition_self, RingHom.id_comp]

/-- Removing the first adjacent map from a finite downward composite. -/
theorem transition_succ_left (i j : ℕ) (hij : i + 1 ≤ j) :
    (q i).comp (transition B q (i + 1) j hij) =
      transition B q i j ((Nat.le_succ i).trans hij) := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hj ih =>
      rw [transition_succ B q (i + 1) j hj, ← RingHom.comp_assoc, ih,
        transition_succ B q i j ((Nat.le_succ i).trans hj)]

/-- Every finite transition evaluates the compatible family. -/
theorem transition_projection (i j : ℕ) (hij : i ≤ j) (a : subring B q) :
    transition B q i j hij (projection B q j a) = projection B q i a := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hj ih =>
      rw [transition_succ B q i j hj, RingHom.comp_apply, compatible]
      exact ih

private def liftSequence (hs : ∀ n, Function.Surjective (q n)) (n : ℕ) (b : B n) :
    ∀ i, B i :=
  Nat.rec (transition B q 0 n (Nat.zero_le n) b)
    (fun i a => if hi : i < n then transition B q (i + 1) n (by omega) b
      else Function.surjInv (hs i) a)

private theorem liftSequence_succ (hs : ∀ n, Function.Surjective (q n))
    (n : ℕ) (b : B n) (i : ℕ) :
    liftSequence B q hs n b (i + 1) =
      if hi : i < n then transition B q (i + 1) n (by omega) b
      else Function.surjInv (hs i) (liftSequence B q hs n b i) := rfl

private theorem liftSequence_of_le (hs : ∀ n, Function.Surjective (q n))
    (n : ℕ) (b : B n) (i : ℕ) (hi : i ≤ n) :
    liftSequence B q hs n b i = transition B q i n hi b := by
  cases i with
  | zero => rfl
  | succ i => rw [liftSequence_succ, dite_eq_left (by omega)]

private theorem liftSequence_compatible (hs : ∀ n, Function.Surjective (q n))
    (n : ℕ) (b : B n) (i : ℕ) :
    q i (liftSequence B q hs n b (i + 1)) = liftSequence B q hs n b i := by
  by_cases hi : i < n
  · rw [liftSequence_succ, dite_eq_left hi,
      liftSequence_of_le B q hs n b i (by omega)]
    exact RingHom.congr_fun (transition_succ_left B q i n (by omega)) b
  · rw [liftSequence_succ, dite_eq_right hi, Function.surjInv_eq (hs i)]

/-- Every projection is onto by recursive lifting along the
surjective adjacent maps. The coefficient rings need not be finite. -/
theorem projection_surjective (hs : ∀ n, Function.Surjective (q n)) (n : ℕ) :
    Function.Surjective (projection B q n) := by
  intro b
  let a := liftSequence B q hs n b
  refine ⟨⟨a, (mem_subring B q a).mpr (fun i => liftSequence_compatible B q hs n b i)⟩, ?_⟩
  change liftSequence B q hs n b n = b
  rw [liftSequence_of_le B q hs n b n le_rfl, transition_self]
  rfl

section Uniformity

variable [∀ n, UniformSpace (B n)] [∀ n, DiscreteUniformity (B n)]

/-- The compatible-family subring is closed in the product of
the discrete coefficient rings. -/
theorem isClosed_subring : IsClosed (subring B q : Set (∀ n, B n)) := by
  have hq (n : ℕ) : Continuous (q n) := continuous_of_discreteTopology
  have hclosed := isClosed_iInter (fun n =>
    isClosed_eq ((hq n).comp (continuous_apply (n + 1))) (continuous_apply n))
  convert hclosed using 1
  ext a
  simp only [Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe, mem_subring,
    Function.comp_apply]

/-- Completeness belongs to the inherited discrete-product uniformity
on the subring, without a separate completion. -/
theorem completeSpace : CompleteSpace (subring B q) :=
  (isClosed_subring B q).isComplete.completeSpace_coe

/-- The same inherited uniformity is Hausdorff. -/
theorem t2Space : T2Space (subring B q) := inferInstance

omit [∀ n, DiscreteUniformity (B n)] in
/-- The coordinate projections are continuous. -/
theorem continuous_projection (n : ℕ) : Continuous (projection B q n) :=
  (continuous_apply n).comp continuous_subtype_val

omit [∀ n, DiscreteUniformity (B n)] in
/-- The coordinate projections are uniformly continuous for
the same product-induced uniformity. -/
theorem uniformContinuous_projection (n : ℕ) : UniformContinuous (projection B q n) := by
  have h : UniformContinuous (fun a : ∀ i, B i => a n) :=
    uniformContinuous_pi.mp uniformContinuous_id n
  exact h.comp uniformContinuous_subtype_val

/-- The kernels of the individual projections are a cofinal
zero-neighborhood basis. Compatibility reduces finitely many coordinates
to their largest index. -/
theorem nhds_zero_hasBasis_ker_projection :
    Filter.HasBasis (nhds (0 : subring B q)) (fun _ : ℕ => True)
      (fun n => (RingHom.ker (projection B q n) : Set (subring B q))) := by
  classical
  have hp : Filter.HasBasis (nhds (0 : ∀ n, B n)) Set.Finite
      (fun I => {a | ∀ i ∈ I, a i = 0}) := by
    simpa only [nhds_pi, nhds_discrete, Pi.zero_apply] using
      Filter.hasBasis_pi_pure (0 : ∀ n, B n)
  have hA : Filter.HasBasis (nhds (0 : subring B q)) Set.Finite
      (fun I => {a : subring B q | ∀ i ∈ I, a.val i = 0}) := by
    rw [nhds_subtype]
    convert hp.comap (Subtype.val : subring B q → ∀ n, B n) using 1
    rfl
  apply hA.to_hasBasis
  · intro I hI
    refine ⟨hI.toFinset.sup id, trivial, ?_⟩
    intro a ha i hi
    have hiN : i ≤ hI.toFinset.sup id :=
      Finset.le_sup (f := id) (b := i) (by simpa only [Set.Finite.mem_toFinset] using hi)
    change projection B q i a = 0
    rw [← transition_projection B q i _ hiN a, RingHom.mem_ker.mp ha, map_zero]
  · intro n _
    refine ⟨{n}, Set.finite_singleton n, ?_⟩
    intro a ha
    exact RingHom.mem_ker.mpr (ha n (Set.mem_singleton n))

end Uniformity

end FontaineWintenberger.SequentialInverseLimit
