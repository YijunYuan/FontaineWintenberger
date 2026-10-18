#!/usr/bin/env python3
"""A2 core: turn `IsAPFSubextension`, `IsAPF`, `IsStrictlyAPF` into classes in APF/Basic,
APF/Abstract, APF/Strict. Run before scripts/a2_isapf_class.py."""
import pathlib


def patch(path, pairs):
    p = pathlib.Path(path)
    s = p.read_text()
    for a, b in pairs:
        assert a in s, (path, a[:60])
        s = s.replace(a, b)
    p.write_text(s)


patch('FontaineWintenberger/APF/Basic.lean', [
    ('''/-- Arithmetic profiniteness for an arbitrary separable extension inside the fixed separable
closure. -/
def IsAPFSubextension (L : IntermediateField K (SeparableClosure K)) : Prop :=
  ∀ u : ℝ, -1 ≤ u →
    IsOpen (apfSubgroup K L u : Set (SeparableClosure K ≃ₐ[K] SeparableClosure K))
''', '''/-- Arithmetic profiniteness for an arbitrary separable extension inside the fixed separable
closure: `G_K^u · G_L` is open in `G_K` for every `u ≥ -1` (Wintenberger 1.2.1). -/
class IsAPFSubextension (L : IntermediateField K (SeparableClosure K)) : Prop where
  isOpen_apfSubgroup : ∀ u : ℝ, -1 ≤ u →
    IsOpen (apfSubgroup K L u : Set (SeparableClosure K ≃ₐ[K] SeparableClosure K))

theorem isAPFSubextension_iff (L : IntermediateField K (SeparableClosure K)) :
    IsAPFSubextension K L ↔ ∀ u : ℝ, -1 ≤ u →
      IsOpen (apfSubgroup K L u : Set (SeparableClosure K ≃ₐ[K] SeparableClosure K)) :=
  ⟨fun h => h.isOpen_apfSubgroup, fun h => ⟨h⟩⟩
'''),
    ('  simp only [IsAPFSubextension, isOpen_apfSubgroup_iff_finiteIndex]',
     '  simp only [isAPFSubextension_iff, isOpen_apfSubgroup_iff_finiteIndex]'),
    ('''theorem IsAPFSubextension.index_pos {L : IntermediateField K (SeparableClosure K)} (hL :
    IsAPFSubextension K L)
    (u : ℝ) (hu : -1 ≤ u) : 0 < (apfSubgroup K L u).index := by''',
     '''theorem IsAPFSubextension.index_pos {L : IntermediateField K (SeparableClosure K)}
    [hL : IsAPFSubextension K L]
    (u : ℝ) (hu : -1 ≤ u) : 0 < (apfSubgroup K L u).index := by'''),
    ('''theorem isAPFSubextension_of_finite (L : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K L] :
    IsAPFSubextension K L := by
  intro u _
''', '''instance isAPFSubextension_of_finite (L : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K L] :
    IsAPFSubextension K L := by
  refine ⟨fun u _ => ?_⟩
'''),
    ('''    (hL : IsAPFSubextension K L) (hML : M ≤ L) : IsAPFSubextension K M := by
  intro u hu
  exact Subgroup.isOpen_mono
    (sup_le_sup_right (IntermediateField.fixingSubgroup_le hML) _) (hL u hu)''',
     '''    [hL : IsAPFSubextension K L] (hML : M ≤ L) : IsAPFSubextension K M := by
  refine ⟨fun u hu => ?_⟩
  exact Subgroup.isOpen_mono
    (sup_le_sup_right (IntermediateField.fixingSubgroup_le hML) _) (hL.isOpen_apfSubgroup u hu)'''),
])

p = pathlib.Path('FontaineWintenberger/APF/Abstract.lean')
s = p.read_text()
i = s.index('/-- Arithmetic profiniteness of an abstract separable field extension. -/')
j = s.index('end FontaineWintenberger')
s = s[:i] + '''/-- Arithmetic profiniteness of an abstract separable field extension `L/K`
(Wintenberger 1.2.1): the image of every `K`-embedding `L → K^sep` is an APF subextension. -/
class IsAPF (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L] : Prop where
  isAPFSubextension (i : L →ₐ[K] SeparableClosure K) : IsAPFSubextension K i.fieldRange

attribute [instance] IsAPF.isAPFSubextension

/-- The public APF predicate can be tested using any specified embedding. -/
theorem isAPF_iff_embedding (i : L →ₐ[K] SeparableClosure K) :
    IsAPF K L ↔ IsAPFSubextension K i.fieldRange := by
  constructor
  · exact fun h ↦ h.isAPFSubextension i
  · intro h
    exact ⟨fun j => (isAPFSubextension_fieldRange_iff K L i j).mp h⟩

/-- The embedding quantifier in `IsAPF` is nonvacuous. -/
theorem isAPF_iff_exists_embedding :
    IsAPF K L ↔ ∃ i : L →ₐ[K] SeparableClosure K, IsAPFSubextension K i.fieldRange := by
  constructor
  · intro h
    obtain ⟨i⟩ := nonempty_separableClosure_embeddings K L
    exact ⟨i, h.isAPFSubextension i⟩
  · rintro ⟨i, hi⟩
    exact (isAPF_iff_embedding K L i).mpr hi

theorem isAPF_iff_subextension (E : IntermediateField K (SeparableClosure K)) :
    IsAPF K E ↔ IsAPFSubextension K E := by
  simpa only [IntermediateField.fieldRange_val] using isAPF_iff_embedding K E E.val

instance (E : IntermediateField K (SeparableClosure K)) [IsAPFSubextension K E] : IsAPF K E :=
  (isAPF_iff_subextension K E).mpr ‹_›

instance (E : IntermediateField K (SeparableClosure K)) [IsAPF K E] : IsAPFSubextension K E :=
  (isAPF_iff_subextension K E).mp ‹_›

/-- Every finite separable abstract extension is APF (Wintenberger 1.2.2). -/
instance isAPF_of_finite [FiniteDimensional K L] : IsAPF K L := by
  refine ⟨fun i => ?_⟩
  let : FiniteDimensional K i.fieldRange := Module.Finite.equiv i.equivFieldRange.toLinearEquiv
  exact isAPFSubextension_of_finite K i.fieldRange

variable {L}
variable {M : Type*} [Field M] [Algebra K M] [Algebra.IsSeparable K M]

/-- APF descends along every algebra embedding, including nonnormal subextensions
(Wintenberger 1.2.3 (iii)). -/
theorem IsAPF.of_algHom [hL : IsAPF K L] (f : M →ₐ[K] L) : IsAPF K M := by
  obtain ⟨i⟩ := nonempty_separableClosure_embeddings K L
  have hr : (i.comp f).fieldRange ≤ i.fieldRange := by
    intro x hx
    obtain ⟨a, ha⟩ := AlgHom.mem_fieldRange.mp hx
    exact AlgHom.mem_fieldRange.mpr ⟨f a, ha⟩
  haveI := hL.isAPFSubextension i
  exact (isAPF_iff_embedding K M (i.comp f)).mpr (IsAPFSubextension.of_le K hr)

/-- Every intermediate field of an APF extension is APF over the base. -/
instance IsAPF.intermediateField [IsAPF K L] (E : IntermediateField K L) : IsAPF K E :=
  IsAPF.of_algHom K E.val

theorem isAPF_algEquiv (e : L ≃ₐ[K] M) : IsAPF K L ↔ IsAPF K M := by
  constructor
  · exact fun h ↦ haveI := h; IsAPF.of_algHom K e.symm.toAlgHom
  · exact fun h ↦ haveI := h; IsAPF.of_algHom K e.toAlgHom

''' + s[j:]
p.write_text(s)

patch('FontaineWintenberger/APF/Strict.lean', [
    ('''/-- Strict arithmetic profiniteness of an abstract separable extension. -/
def IsStrictlyAPF : Prop :=
  IsAPF K L ∧ 0 < liminf (apfStrictnessRatio K L) atTop''',
     '''/-- Strict arithmetic profiniteness of an abstract separable extension (Wintenberger 1.2.1):
APF, and the ratio `ψ_{L/K}(u) / (G_K^0 : G_L^0 G_K^u)` stays bounded below as `u → ∞`. -/
class IsStrictlyAPF : Prop extends IsAPF K L where
  liminf_pos : 0 < liminf (apfStrictnessRatio K L) atTop

theorem isStrictlyAPF_iff :
    IsStrictlyAPF K L ↔ IsAPF K L ∧ 0 < liminf (apfStrictnessRatio K L) atTop :=
  ⟨fun h => ⟨h.toIsAPF, h.liminf_pos⟩, fun h => { toIsAPF := h.1, liminf_pos := h.2 }⟩'''),
    ('  simp only [IsStrictlyAPF, isAPF_algEquiv K e,',
     '  simp only [isStrictlyAPF_iff, isAPF_algEquiv K e,'),
])
print('core converted')
