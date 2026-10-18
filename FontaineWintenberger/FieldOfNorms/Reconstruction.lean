/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.DeepTruncatedTower
public import FontaineWintenberger.FieldOfNorms.TruncatedInverseLimit
public import FontaineWintenberger.FieldOfNorms.Convergence

/-!
# Reconstruction from the actual deep truncated norm tower

Compatible classes are represented by actual integers of the original finite
fields. Their norms converge at each fixed original finite base and recover
one family on the original zero-adjoined multiplicative norm limit.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

open Filter

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]
variable [IsAPF K L] [Fact (¬ Module.Finite K L)] (D : FiniteLayer K L)

local notation "𝔈" => deepFiniteTower K L D
local notation "𝔅" => deepFiniteTowerQuotient K L D

/-- The actual deep quotient tower specialized to the canonical compatible-family subring. -/
abbrev deepNormInverseLimit :=
  SequentialInverseLimit.subring (fun n => 𝔅 n)
    (fun n => deepFiniteTowerTransition K L D n (n + 1) (Nat.le_succ n))

local notation "𝒜" => deepNormInverseLimit K L D

/-- Finite composites in the canonical sequential inverse limit are the actual norms. -/
theorem deepNormInverseLimit_transition (i j : ℕ) (hij : i ≤ j) :
    SequentialInverseLimit.transition (fun n => 𝔅 n)
        (fun n => deepFiniteTowerTransition K L D n (n + 1) (Nat.le_succ n))
        i j hij = deepFiniteTowerTransition K L D i j hij := by
  induction j, hij using Nat.le_induction with
  | base => rw [SequentialInverseLimit.transition_self, deepFiniteTowerTransition_self]
  | succ j hj ih =>
      rw [SequentialInverseLimit.transition_succ _ _ i j hj, ih]
      exact deepFiniteTowerTransition_comp K L D i j (j + 1) hj (Nat.le_succ j)

/-- Every pair of coordinates of the actual compatible subring satisfies the original norm. -/
theorem deepNormInverseLimit_compatible (a : 𝒜) (i j : ℕ) (hij : i ≤ j) :
    deepFiniteTowerTransition K L D i j hij (a.val j) = a.val i := by
  rw [← deepNormInverseLimit_transition K L D i j hij]
  exact SequentialInverseLimit.transition_projection _ _ i j hij a

/-- An actual integral representative of each original quotient coordinate. -/
def deepNormRepresentative (a : 𝒜) (n : ℕ) : spectralIntegerRing K (𝔈 n).val :=
  (Ideal.Quotient.mk_surjective (a.val n)).choose

@[simp]
theorem deepNormRepresentative_mk (a : 𝒜) (n : ℕ) :
    Ideal.Quotient.mk _ (deepNormRepresentative K L D a n) = a.val n :=
  (Ideal.Quotient.mk_surjective (a.val n)).choose_spec

/-- Any actual integral representatives obey the required original norm congruences. -/
theorem deepNormRepresentative_norm_sub_mem (a : 𝒜)
    (x : ∀ n, spectralIntegerRing K (𝔈 n).val)
    (hx : ∀ n, Ideal.Quotient.mk _ (x n) = a.val n)
    (n m : ℕ) (hnm : n ≤ m) :
    FiniteLayer.integerNorm (𝔈 n) (𝔈 m)
        (deepFiniteTower_monotone K L D hnm) (x m) - x n ∈
      IsLocalRing.maximalIdeal (spectralIntegerRing K (𝔈 n).val) ^ (n + 2) := by
  have h := deepNormInverseLimit_compatible K L D a n m hnm
  rw [← hx m, ← hx n, deepFiniteTowerTransition_mk] at h
  exact Ideal.Quotient.eq.mp h

/-- Norms of integral representatives into one fixed original finite tower field.
The initial constant segment only extends the same eventual norm sequence. -/
def deepNormSequence (x : ∀ n, spectralIntegerRing K (𝔈 n).val) (j n : ℕ) : (𝔈 j).val :=
  if hjn : j ≤ n then
    FiniteLayer.norm (𝔈 j) (𝔈 n)
      (deepFiniteTower_monotone K L D hjn) (x n)
  else x j

/-- On its actual tail the fixed-base norm sequence is the original norm without reindexing. -/
theorem deepNormSequence_of_le (x : ∀ n, spectralIntegerRing K (𝔈 n).val)
    (j n : ℕ) (hjn : j ≤ n) :
    deepNormSequence K L D x j n =
      FiniteLayer.norm (𝔈 j) (𝔈 n)
        (deepFiniteTower_monotone K L D hjn) (x n) := by
  rw [deepNormSequence, dite_eq_left hjn]

/-- Every term of the actual fixed-base norm sequence remains integral. -/
theorem deepNormSequence_mem (x : ∀ n, spectralIntegerRing K (𝔈 n).val) (j n : ℕ) :
    deepNormSequence K L D x j n ∈ spectralIntegerRing K (𝔈 j).val := by
  by_cases hjn : j ≤ n
  · rw [deepNormSequence_of_le K L D x j n hjn]
    have h := (FiniteLayer.integerNorm (𝔈 j) (𝔈 n)
      (deepFiniteTower_monotone K L D hjn) (x n)).property
    rw [FiniteLayer.coe_integerNorm] at h
    exact h
  · rw [deepNormSequence, dite_eq_right hjn]
    exact (x j).property

/-- Actual representative norm sequences are Cauchy in each fixed original finite field. -/
theorem deepNormSequence_cauchy (a : 𝒜)
    (x : ∀ n, spectralIntegerRing K (𝔈 n).val)
    (hx : ∀ n, Ideal.Quotient.mk _ (x n) = a.val n) (j : ℕ) :
    letI := spectralNorm.nontriviallyNormedField K (𝔈 j).val
    Cauchy (map (deepNormSequence K L D x j) atTop) := by
  let := spectralNorm.nontriviallyNormedField K (𝔈 j).val
  let := spectralNorm.normedAlgebra K (𝔈 j).val
  let := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := (𝔈 j).val))
  let := spectralNorm.completeSpace K (𝔈 j).val
  let := normedAlgebra_isCompleteDiscreteValuedField K (𝔈 j).val
  let := Algebra.isSeparable_tower_top_of_isSeparable K (𝔈 j).val L
  apply cauchy_map_of_eventually_sub_mem_maximalIdeal_pow (𝔈 j).val
  intro N
  let s := ⌈apfPsi (𝔈 j).val L (N : ℝ)⌉₊
  let n₀ := max j s
  have hstep (n m : ℕ) (hn : n₀ ≤ n) (hnm : n ≤ m) :
      deepNormSequence K L D x j m -
        deepNormSequence K L D x j n ∈
      (fun z : spectralIntegerRing K (𝔈 j).val => (z : (𝔈 j).val)) ''
        ((IsLocalRing.maximalIdeal (spectralIntegerRing K (𝔈 j).val) ^ N :
          Ideal (spectralIntegerRing K (𝔈 j).val)) : Set (spectralIntegerRing K (𝔈 j).val)) := by
    have hjn : j ≤ n := (le_max_left j s).trans hn
    have hjm : j ≤ m := hjn.trans hnm
    let hEjn := deepFiniteTower_monotone K L D hjn
    let hEnm := deepFiniteTower_monotone K L D hnm
    let : Algebra (𝔈 j).val (𝔈 n).val :=
      (IntermediateField.inclusion hEjn).toRingHom.toAlgebra
    let : IsScalarTower K (𝔈 j).val (𝔈 n).val := IsScalarTower.of_algebraMap_eq' rfl
    let := spectralValuation_hasExtension_tower K (E := (𝔈 j).val) (L := (𝔈 n).val)
    let u := FiniteLayer.integerNorm (𝔈 n) (𝔈 m) hEnm (x m)
    have hu : u - x n ∈
        IsLocalRing.maximalIdeal (spectralIntegerRing K (𝔈 n).val) ^ (n + 2) :=
      deepNormRepresentative_norm_sub_mem K L D a x hx n m hnm
    obtain ⟨_, ⟨d, hd⟩, he⟩ := deepFiniteTower_wild_tail K L D
      (𝔈 j) (𝔈 n) (deepFiniteTower_monotone K L D (Nat.zero_le j)) hEjn
    have h := FiniteLayer.integerNorm_sub_congruence_of_totallyRamified
      (𝔈 j) (𝔈 n) hEjn he d hd (n + 2) u (x n) hu
    have hs : apfPsi (𝔈 j).val L (N : ℝ) ≤ ((n + 2 : ℕ) : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast
        (show s ≤ n + 2 from (le_max_right j s).trans (hn.trans (by omega))))
    have hp := FiniteLayer.le_ceil_apfPhi_of_apfPsi_le K L (𝔈 j) (𝔈 n) hEjn N (n + 2) hs
    refine ⟨FiniteLayer.integerNorm (𝔈 j) (𝔈 n) hEjn u -
      FiniteLayer.integerNorm (𝔈 j) (𝔈 n) hEjn (x n), Ideal.pow_le_pow_right hp h, ?_⟩
    change (FiniteLayer.integerNorm (𝔈 j) (𝔈 n) hEjn u : (𝔈 j).val) -
      (FiniteLayer.integerNorm (𝔈 j) (𝔈 n) hEjn (x n) : (𝔈 j).val) = _
    rw [FiniteLayer.coe_integerNorm, FiniteLayer.coe_integerNorm,
      deepNormSequence_of_le K L D x j m hjm,
      deepNormSequence_of_le K L D x j n hjn]
    rw [FiniteLayer.coe_integerNorm (𝔈 j) (𝔈 n) hEjn (x n), FiniteLayer.norm_norm]
  refine ⟨n₀, fun n hn m hm => ?_⟩
  rcases le_total n m with hnm | hmn
  · obtain ⟨z, hz, heq⟩ := hstep n m hn hnm
    refine ⟨-z, (IsLocalRing.maximalIdeal (spectralIntegerRing K (𝔈 j).val) ^ N).neg_mem hz, ?_⟩
    change -(z : (𝔈 j).val) = _
    linear_combination -heq
  · exact hstep m n hm hmn

/-- Completeness of the same original finite field gives an actual norm-sequence limit. -/
theorem exists_tendsto_deepNormSequence (a : 𝒜)
    (x : ∀ n, spectralIntegerRing K (𝔈 n).val)
    (hx : ∀ n, Ideal.Quotient.mk _ (x n) = a.val n) (j : ℕ) :
    ∃ z : (𝔈 j).val, letI := spectralNorm.nontriviallyNormedField K (𝔈 j).val
      Tendsto (deepNormSequence K L D x j) atTop (nhds z) := by
  let := spectralNorm.nontriviallyNormedField K (𝔈 j).val
  let := spectralNorm.completeSpace K (𝔈 j).val
  exact cauchy_map_iff_exists_tendsto.mp
    (deepNormSequence_cauchy K L D a x hx j)

/-- The actual fixed-base limit, chosen from the proved convergence of genuine representatives. -/
def deepNormCoordinate (a : 𝒜) (j : ℕ) : (𝔈 j).val :=
  (exists_tendsto_deepNormSequence K L D a
    (deepNormRepresentative K L D a)
    (deepNormRepresentative_mk K L D a) j).choose

/-- The defining genuine representative norms converge to the selected original-field limit. -/
theorem tendsto_deepNormCoordinate (a : 𝒜) (j : ℕ) :
    letI := spectralNorm.nontriviallyNormedField K (𝔈 j).val
    Tendsto (deepNormSequence K L D
      (deepNormRepresentative K L D a) j) atTop
        (nhds (deepNormCoordinate K L D a j)) :=
  (exists_tendsto_deepNormSequence K L D a
    (deepNormRepresentative K L D a)
    (deepNormRepresentative_mk K L D a) j).choose_spec

/-- Closedness of the original integer ring keeps the actual fixed-base limit integral. -/
theorem deepNormCoordinate_mem (a : 𝒜) (j : ℕ) :
    deepNormCoordinate K L D a j ∈ spectralIntegerRing K (𝔈 j).val := by
  let := spectralNorm.nontriviallyNormedField K (𝔈 j).val
  obtain ⟨z, _hz, heq⟩ := (FiniteLayer.isClosed_image_maximalIdeal_pow (𝔈 j) 0).mem_of_tendsto
    (tendsto_deepNormCoordinate K L D a j)
    (Eventually.of_forall fun n => ⟨⟨_, deepNormSequence_mem K L D
      (deepNormRepresentative K L D a) j n⟩, by simp, rfl⟩)
  exact heq ▸ z.property

/-- Actual original norm continuity and transitivity make the fixed-base limits compatible. -/
theorem deepNormCoordinate_norm (a : 𝒜) (i j : ℕ) (hij : i ≤ j) :
    FiniteLayer.norm (𝔈 i) (𝔈 j) (deepFiniteTower_monotone K L D hij)
      (deepNormCoordinate K L D a j) =
        deepNormCoordinate K L D a i := by
  let := spectralNorm.nontriviallyNormedField K (𝔈 i).val
  let := spectralNorm.nontriviallyNormedField K (𝔈 j).val
  let x := deepNormRepresentative K L D a
  have hc := ((FiniteLayer.continuous_norm (𝔈 i) (𝔈 j)
    (deepFiniteTower_monotone K L D hij)).tendsto
      (deepNormCoordinate K L D a j)).comp
        (tendsto_deepNormCoordinate K L D a j)
  have heq : (fun n => FiniteLayer.norm (𝔈 i) (𝔈 j)
      (deepFiniteTower_monotone K L D hij)
      (deepNormSequence K L D x j n)) =ᶠ[atTop]
        deepNormSequence K L D x i := by
    filter_upwards [eventually_ge_atTop j] with n hn
    rw [deepNormSequence_of_le K L D x j n hn,
      deepNormSequence_of_le K L D x i n (hij.trans hn),
      FiniteLayer.norm_norm]
  exact tendsto_nhds_unique (hc.congr' heq) (tendsto_deepNormCoordinate K L D a i)

/-- The fixed original ideal power is closed, so the actual limit retains its quotient class. -/
theorem deepNormCoordinate_sub_mem (a : 𝒜) (j : ℕ) :
    deepNormCoordinate K L D a j -
      (deepNormRepresentative K L D a j : (𝔈 j).val) ∈
    (fun z : spectralIntegerRing K (𝔈 j).val => (z : (𝔈 j).val)) ''
      ((IsLocalRing.maximalIdeal (spectralIntegerRing K (𝔈 j).val) ^ (j + 2) :
        Ideal (spectralIntegerRing K (𝔈 j).val)) : Set (spectralIntegerRing K (𝔈 j).val)) := by
  let := spectralNorm.nontriviallyNormedField K (𝔈 j).val
  let x := deepNormRepresentative K L D a
  apply (FiniteLayer.isClosed_image_maximalIdeal_pow (𝔈 j) (j + 2)).mem_of_tendsto
    ((tendsto_deepNormCoordinate K L D a j).sub_const (x j))
  filter_upwards [eventually_ge_atTop j] with n hn
  refine ⟨FiniteLayer.integerNorm (𝔈 j) (𝔈 n)
      (deepFiniteTower_monotone K L D hn) (x n) - x j,
    deepNormRepresentative_norm_sub_mem K L D a x
      (deepNormRepresentative_mk K L D a) j n hn, ?_⟩
  change (FiniteLayer.integerNorm (𝔈 j) (𝔈 n) _ (x n) : (𝔈 j).val) - (x j : (𝔈 j).val) = _
  rw [FiniteLayer.coe_integerNorm, deepNormSequence_of_le K L D x j n hn]

/-- A proved cofinal index for any specified original finite layer. -/
def deepNormFamilyIndex (F : FiniteLayer K L) : ℕ :=
  (deepFiniteTower_cofinal K L D F).choose

theorem le_deepNormFamilyIndex (F : FiniteLayer K L) :
    F ≤ 𝔈 (deepNormFamilyIndex K L D F) :=
  (deepFiniteTower_cofinal K L D F).choose_spec

/-- The actual original-field family obtained by norm descent of the proved fixed-base limits. -/
def deepNormFamily (a : 𝒜) (F : FiniteLayer K L) : F.val :=
  FiniteLayer.norm F (𝔈 (deepNormFamilyIndex K L D F))
    (le_deepNormFamilyIndex K L D F)
      (deepNormCoordinate K L D a (deepNormFamilyIndex K L D F))

/-- Descent to an original finite field is independent of its cofinal containing index. -/
theorem deepNormFamily_eq_norm (a : 𝒜) (F : FiniteLayer K L) (j : ℕ) (hFj : F ≤ 𝔈 j) :
    deepNormFamily K L D a F =
      FiniteLayer.norm F (𝔈 j) hFj (deepNormCoordinate K L D a j) := by
  let n := deepNormFamilyIndex K L D F
  let k := max n j
  have hnk : n ≤ k := le_max_left n j
  have hjk : j ≤ k := le_max_right n j
  have hFn := le_deepNormFamilyIndex K L D F
  have hEnk := deepFiniteTower_monotone K L D hnk
  have hEjk := deepFiniteTower_monotone K L D hjk
  calc
    deepNormFamily K L D a F =
        FiniteLayer.norm F (𝔈 n) hFn
          (FiniteLayer.norm (𝔈 n) (𝔈 k) hEnk (deepNormCoordinate K L D a k)) :=
      congrArg (FiniteLayer.norm F (𝔈 n) hFn)
        (deepNormCoordinate_norm K L D a n k hnk).symm
    _ = FiniteLayer.norm F (𝔈 k) (hFn.trans hEnk)
        (deepNormCoordinate K L D a k) := FiniteLayer.norm_norm _ _ _ _ _ _
    _ = FiniteLayer.norm F (𝔈 j) hFj
        (FiniteLayer.norm (𝔈 j) (𝔈 k) hEjk (deepNormCoordinate K L D a k)) :=
      (FiniteLayer.norm_norm F (𝔈 j) (𝔈 k) hFj hEjk _).symm
    _ = FiniteLayer.norm F (𝔈 j) hFj (deepNormCoordinate K L D a j) :=
      congrArg (FiniteLayer.norm F (𝔈 j) hFj)
        (deepNormCoordinate_norm K L D a j k hjk)

/-- The descended family satisfies all original finite-field norm equations. -/
theorem deepNormFamily_norm (a : 𝒜) (F G : FiniteLayer K L) (hFG : F ≤ G) :
    FiniteLayer.norm F G hFG (deepNormFamily K L D a G) =
      deepNormFamily K L D a F := by
  obtain ⟨j, hGj⟩ := deepFiniteTower_cofinal K L D G
  rw [deepNormFamily_eq_norm K L D a G j hGj,
    deepNormFamily_eq_norm K L D a F j (hFG.trans hGj),
    FiniteLayer.norm_norm]

/-- Every descended coordinate is integral in its original finite field. -/
theorem deepNormFamily_mem (a : 𝒜) (F : FiniteLayer K L) :
    deepNormFamily K L D a F ∈ spectralIntegerRing K F.val := by
  let n := deepNormFamilyIndex K L D F
  let z : spectralIntegerRing K (𝔈 n).val :=
    ⟨deepNormCoordinate K L D a n, deepNormCoordinate_mem K L D a n⟩
  have h := (FiniteLayer.integerNorm F (𝔈 n) (le_deepNormFamilyIndex K L D F)
      z).property
  rw [FiniteLayer.coe_integerNorm] at h
  exact h

/-- The same original norm-limit carrier contains a unique integral family
with the proved fixed-base representative limits. -/
theorem existsUnique_normLimit_deepNormCoordinate (a : 𝒜) :
    ∃! γ : NormLimit K L, normLimitValuation K L γ ≤ 1 ∧
      ∀ j, normLimitEval K L (𝔈 j) γ = deepNormCoordinate K L D a j := by
  obtain ⟨γ, hγ, huniq⟩ := existsUnique_normLimit_of_compatible K L
    (deepNormFamily K L D a) (deepNormFamily_norm K L D a)
  refine ⟨γ, ⟨?_, ?_⟩, fun δ hδ => huniq δ (fun F => ?_)⟩
  · rw [normLimitValuation_le_one_iff K L]
    intro F
    rw [hγ F]
    exact deepNormFamily_mem K L D a F
  · intro j
    rw [hγ, deepNormFamily_eq_norm K L D a (𝔈 j) j le_rfl,
      FiniteLayer.norm_self]
  · obtain ⟨j, hFj⟩ := deepFiniteTower_cofinal K L D F
    rw [← normLimitEval_norm K L F (𝔈 j) hFj δ, hδ.2 j,
      deepNormFamily_eq_norm K L D a F j hFj]

/-- Reconstruction is the proved actual integral family on the original norm-limit carrier. -/
def deepNormReconstruction (a : 𝒜) : NormLimit K L :=
  (existsUnique_normLimit_deepNormCoordinate K L D a).choose

/-- The reconstructed original family is integral for the same stable valuation. -/
theorem deepNormReconstruction_valuation_le_one (a : 𝒜) :
    normLimitValuation K L (deepNormReconstruction K L D a) ≤ 1 :=
  (existsUnique_normLimit_deepNormCoordinate K L D a).choose_spec.1.1

/-- Reconstruction has precisely the original fixed-base limits as its actual coordinates. -/
theorem normLimitEval_deepNormReconstruction (a : 𝒜) (j : ℕ) :
    normLimitEval K L (𝔈 j) (deepNormReconstruction K L D a) =
      deepNormCoordinate K L D a j :=
  (existsUnique_normLimit_deepNormCoordinate K L D a).choose_spec.1.2 j

/-- The actual reconstructed family retains every original quotient truncation. -/
theorem deepNormReconstruction_sub_mem (a : 𝒜) (j : ℕ) :
    normLimitEval K L (𝔈 j) (deepNormReconstruction K L D a) -
      (deepNormRepresentative K L D a j : (𝔈 j).val) ∈
    (fun z : spectralIntegerRing K (𝔈 j).val => (z : (𝔈 j).val)) ''
      ((IsLocalRing.maximalIdeal (spectralIntegerRing K (𝔈 j).val) ^ (j + 2) :
        Ideal (spectralIntegerRing K (𝔈 j).val)) : Set (spectralIntegerRing K (𝔈 j).val)) := by
  rw [normLimitEval_deepNormReconstruction]
  exact deepNormCoordinate_sub_mem K L D a j

/-- Two choices of genuine representatives have norm sequences whose difference
tends to zero in one fixed original finite field. -/
theorem deepNormSequence_sub_tendsto_zero (a : 𝒜)
    (x y : ∀ n, spectralIntegerRing K (𝔈 n).val)
    (hx : ∀ n, Ideal.Quotient.mk _ (x n) = a.val n)
    (hy : ∀ n, Ideal.Quotient.mk _ (y n) = a.val n) (j : ℕ) :
    letI := spectralNorm.nontriviallyNormedField K (𝔈 j).val
    Tendsto (fun n => deepNormSequence K L D x j n -
      deepNormSequence K L D y j n) atTop (nhds 0) := by
  let := spectralNorm.nontriviallyNormedField K (𝔈 j).val
  let := spectralNorm.normedAlgebra K (𝔈 j).val
  let := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := (𝔈 j).val))
  let := spectralNorm.completeSpace K (𝔈 j).val
  let := normedAlgebra_isCompleteDiscreteValuedField K (𝔈 j).val
  let := Algebra.isSeparable_tower_top_of_isSeparable K (𝔈 j).val L
  apply (FiniteLayer.nhds_zero_hasBasis_maximalIdeal_pow (𝔈 j)).tendsto_right_iff.mpr
  intro N _
  let s := ⌈apfPsi (𝔈 j).val L (N : ℝ)⌉₊
  filter_upwards [eventually_ge_atTop (max j s)] with n hn
  have hjn : j ≤ n := (le_max_left j s).trans hn
  let hEjn := deepFiniteTower_monotone K L D hjn
  let : Algebra (𝔈 j).val (𝔈 n).val :=
    (IntermediateField.inclusion hEjn).toRingHom.toAlgebra
  let : IsScalarTower K (𝔈 j).val (𝔈 n).val := IsScalarTower.of_algebraMap_eq' rfl
  let := spectralValuation_hasExtension_tower K (E := (𝔈 j).val) (L := (𝔈 n).val)
  have hxy : x n - y n ∈
      IsLocalRing.maximalIdeal (spectralIntegerRing K (𝔈 n).val) ^ (n + 2) :=
    Ideal.Quotient.eq.mp ((hx n).trans (hy n).symm)
  obtain ⟨_, ⟨d, hd⟩, he⟩ := deepFiniteTower_wild_tail K L D
    (𝔈 j) (𝔈 n) (deepFiniteTower_monotone K L D (Nat.zero_le j)) hEjn
  have h := FiniteLayer.integerNorm_sub_congruence_of_totallyRamified
    (𝔈 j) (𝔈 n) hEjn he d hd (n + 2) (x n) (y n) hxy
  have hs : apfPsi (𝔈 j).val L (N : ℝ) ≤ ((n + 2 : ℕ) : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast
      (show s ≤ n + 2 from (le_max_right j s).trans (hn.trans (by omega))))
  have hp := FiniteLayer.le_ceil_apfPhi_of_apfPsi_le K L (𝔈 j) (𝔈 n) hEjn N (n + 2) hs
  refine ⟨FiniteLayer.integerNorm (𝔈 j) (𝔈 n) hEjn (x n) -
    FiniteLayer.integerNorm (𝔈 j) (𝔈 n) hEjn (y n), Ideal.pow_le_pow_right hp h, ?_⟩
  change (FiniteLayer.integerNorm (𝔈 j) (𝔈 n) hEjn (x n) : (𝔈 j).val) -
    (FiniteLayer.integerNorm (𝔈 j) (𝔈 n) hEjn (y n) : (𝔈 j).val) = _
  rw [FiniteLayer.coe_integerNorm (𝔈 j) (𝔈 n) hEjn (x n),
    FiniteLayer.coe_integerNorm (𝔈 j) (𝔈 n) hEjn (y n),
    deepNormSequence_of_le K L D x j n hjn,
    deepNormSequence_of_le K L D y j n hjn]

/-- Every choice of actual representatives converges to the same original-field limit. -/
theorem deepNormSequence_tendsto (a : 𝒜)
    (x : ∀ n, spectralIntegerRing K (𝔈 n).val)
    (hx : ∀ n, Ideal.Quotient.mk _ (x n) = a.val n) (j : ℕ) :
    letI := spectralNorm.nontriviallyNormedField K (𝔈 j).val
    Tendsto (deepNormSequence K L D x j) atTop
      (nhds (deepNormCoordinate K L D a j)) := by
  let := spectralNorm.nontriviallyNormedField K (𝔈 j).val
  have hd := deepNormSequence_sub_tendsto_zero K L D a x
    (deepNormRepresentative K L D a) hx
    (deepNormRepresentative_mk K L D a) j
  simpa only [sub_add_cancel, zero_add] using
    hd.add (tendsto_deepNormCoordinate K L D a j)

/-- Reconstruction is independent of representatives in the strong sense that
all their actual original norm sequences converge to its coordinates. -/
theorem deepNormReconstruction_tendsto (a : 𝒜)
    (x : ∀ n, spectralIntegerRing K (𝔈 n).val)
    (hx : ∀ n, Ideal.Quotient.mk _ (x n) = a.val n) (j : ℕ) :
    letI := spectralNorm.nontriviallyNormedField K (𝔈 j).val
    Tendsto (deepNormSequence K L D x j) atTop
      (nhds (normLimitEval K L (𝔈 j) (deepNormReconstruction K L D a))) := by
  rw [normLimitEval_deepNormReconstruction]
  exact deepNormSequence_tendsto K L D a x hx j

/-- Every actual representative has the required congruence with the reconstructed coordinate. -/
theorem deepNormReconstruction_sub_mem_of_representative (a : 𝒜)
    (x : ∀ n, spectralIntegerRing K (𝔈 n).val)
    (hx : ∀ n, Ideal.Quotient.mk _ (x n) = a.val n) (j : ℕ) :
    normLimitEval K L (𝔈 j) (deepNormReconstruction K L D a) - (x j : (𝔈 j).val) ∈
    (fun z : spectralIntegerRing K (𝔈 j).val => (z : (𝔈 j).val)) ''
      ((IsLocalRing.maximalIdeal (spectralIntegerRing K (𝔈 j).val) ^ (j + 2) :
        Ideal (spectralIntegerRing K (𝔈 j).val)) : Set (spectralIntegerRing K (𝔈 j).val)) := by
  let := spectralNorm.nontriviallyNormedField K (𝔈 j).val
  apply (FiniteLayer.isClosed_image_maximalIdeal_pow (𝔈 j) (j + 2)).mem_of_tendsto
    ((deepNormReconstruction_tendsto K L D a x hx j).sub_const (x j))
  filter_upwards [eventually_ge_atTop j] with n hn
  refine ⟨FiniteLayer.integerNorm (𝔈 j) (𝔈 n)
      (deepFiniteTower_monotone K L D hn) (x n) - x j,
    deepNormRepresentative_norm_sub_mem K L D a x hx j n hn, ?_⟩
  change (FiniteLayer.integerNorm (𝔈 j) (𝔈 n) _ (x n) : (𝔈 j).val) - (x j : (𝔈 j).val) = _
  rw [FiniteLayer.coe_integerNorm, deepNormSequence_of_le K L D x j n hn]

/-- Every actual compatible quotient family reconstructs uniquely on the
original norm-limit carrier, with convergence for every representative choice. -/
theorem existsUnique_normLimit_of_truncatedNorms (a : 𝒜) :
    ∃! γ : NormLimit K L, normLimitValuation K L γ ≤ 1 ∧
      ∀ (x : ∀ n, spectralIntegerRing K (𝔈 n).val),
        (∀ n, Ideal.Quotient.mk _ (x n) = a.val n) → ∀ j,
        letI := spectralNorm.nontriviallyNormedField K (𝔈 j).val
        Tendsto (deepNormSequence K L D x j) atTop
          (nhds (normLimitEval K L (𝔈 j) γ)) := by
  refine ⟨deepNormReconstruction K L D a,
    ⟨deepNormReconstruction_valuation_le_one K L D a,
      fun x hx j => deepNormReconstruction_tendsto K L D a x hx j⟩, ?_⟩
  intro δ hδ
  apply (existsUnique_normLimit_deepNormCoordinate K L D a).choose_spec.2 δ
  refine ⟨hδ.1, fun j => ?_⟩
  let := spectralNorm.nontriviallyNormedField K (𝔈 j).val
  exact tendsto_nhds_unique
    (hδ.2 (deepNormRepresentative K L D a)
      (deepNormRepresentative_mk K L D a) j)
    (tendsto_deepNormCoordinate K L D a j)

end FontaineWintenberger
