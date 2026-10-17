module

public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-!
# Completeness from the original valuation ring

The inherited valuation-ring uniformity determines completeness of the
original valued field. A Cauchy filter is eventually contained in a translate
of the original complete valuation ring.
-/

@[expose] public section

namespace Valued

open Filter
open scoped Topology

variable (F : Type*) [Field F] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    [hv : Valued F Γ₀]

/-- Completeness of the original valuation ring for its inherited uniformity
implies completeness of the original valued field. -/
theorem completeSpace_of_completeSpace_valuationSubring
    [CompleteSpace hv.v.valuationSubring] : CompleteSpace F where
  complete {f} hf := by
    have : f.NeBot := hf.1
    have hO : IsComplete (hv.v.valuationSubring : Set F) :=
      completeSpace_coe_iff_isComplete.mp inferInstance
    have hOmem : (hv.v.valuationSubring : Set F) ∈ nhds (0 : F) :=
      (isOpen_valuationSubring F).mem_nhds hv.v.valuationSubring.zero_mem
    obtain ⟨a, ha⟩ : ∃ a : F, ∀ᶠ y in f, y - a ∈ hv.v.valuationSubring :=
      ((IsUniformAddGroup.cauchy_iff_tendsto_swapped f).mp hf).2.eventually_mem hOmem
        |>.curry.exists
    have htranslate : IsComplete
        ((fun y : F => y + a) '' (hv.v.valuationSubring : Set F)) :=
      (isComplete_image_iff (isUniformEmbedding_translate_add a).isUniformInducing).mpr hO
    obtain ⟨b, _hbmem, hb⟩ := htranslate f hf (by
      rw [le_principal_iff]
      filter_upwards [ha] with y hy
      exact ⟨y - a, hy, sub_add_cancel y a⟩)
    exact ⟨b, hb⟩

/-- For the original valuation uniformity, the field is complete exactly
when its valuation ring with the inherited subtype uniformity is complete. -/
theorem completeSpace_iff_completeSpace_valuationSubring :
    CompleteSpace F ↔ CompleteSpace hv.v.valuationSubring := by
  constructor
  · intro h
    let := h
    exact (isClosed_valuationSubring F).isComplete.completeSpace_coe
  · intro h
    let := h
    exact completeSpace_of_completeSpace_valuationSubring F

end Valued
