module

public import FontaineWintenberger.APF.FiniteStages

/-!
# Countable cofinal finite layers of an APF extension

The genuine APF fixed fields at integer parameters pull back to a monotone
cofinal sequence in the original abstract extension. No finite-residue or
normality assumption is used.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- The actual integer-parameter APF stages give a monotone cofinal
sequence of original finite fields, with exact original embedded images. -/
theorem IsAPF.exists_monotone_cofinal_finiteLayers_map (hL : IsAPF K L)
    (j : L →ₐ[K] SeparableClosure K) :
    ∃ E : ℕ → FiniteLayer K L, Monotone E ∧
      (∀ n : ℕ, (E n).val.map j = apfFiniteStage K j.fieldRange (n : ℝ)) ∧
      ∀ D : FiniteLayer K L, ∃ n : ℕ, D ≤ E n := by
  choose E hE using fun n : ℕ =>
    exists_finiteLayer_map_eq_apfFiniteStage K L hL j
      (by have := Nat.cast_nonneg (α := ℝ) n; linarith : -1 ≤ (n : ℝ))
  refine ⟨E, ?_, hE, ?_⟩
  · intro m n hmn x hx
    have hjx : j x ∈ apfFiniteStage K j.fieldRange (m : ℝ) := by
      rw [← hE m]
      exact ⟨x, hx, rfl⟩
    have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have hstage := apfFiniteStage_mono K j.fieldRange
      (by have := Nat.cast_nonneg (α := ℝ) m; linarith : -1 ≤ (m : ℝ))
      (by have := Nat.cast_nonneg (α := ℝ) n; linarith : -1 ≤ (n : ℝ)) hmn'
    have hxn := hstage hjx
    rw [← hE n] at hxn
    obtain ⟨y, hy, he⟩ := hxn
    exact (j.injective he) ▸ hy
  · intro D
    have : FiniteDimensional K (D.val.map j) :=
      Module.Finite.equiv (IntermediateField.equivMap D.val j).toLinearEquiv
    have hDL : D.val.map j ≤ j.fieldRange := by
      rintro x ⟨y, _, rfl⟩
      exact ⟨y, rfl⟩
    obtain ⟨U, _hU, hUstage⟩ := exists_le_apfFiniteStage K j.fieldRange (D.val.map j) hDL
    refine ⟨Nat.ceil U, fun x hx => ?_⟩
    have hjx := hUstage (Nat.ceil U) (Nat.le_ceil U) ⟨x, hx, rfl⟩
    rw [← hE (Nat.ceil U)] at hjx
    obtain ⟨y, hy, he⟩ := hjx
    exact (j.injective he) ▸ hy

/-- Every original abstract separable APF extension has a countable
monotone cofinal sequence among all of its actual finite layers. -/
theorem IsAPF.exists_monotone_cofinal_finiteLayers (hL : IsAPF K L) :
    ∃ E : ℕ → FiniteLayer K L, Monotone E ∧ ∀ D : FiniteLayer K L, ∃ n : ℕ, D ≤ E n := by
  obtain ⟨j⟩ := nonempty_separableClosure_embeddings K L
  obtain ⟨E, hmono, _hmap, hcofinal⟩ :=
    IsAPF.exists_monotone_cofinal_finiteLayers_map K L hL j
  exact ⟨E, hmono, hcofinal⟩

end FontaineWintenberger
