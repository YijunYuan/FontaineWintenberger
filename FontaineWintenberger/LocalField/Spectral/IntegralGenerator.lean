/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.LocalField.Spectral.Henselian
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import Mathlib.RingTheory.Nakayama

/-!
# Integral generators of finite extensions of complete discrete valuation fields

The argument lifts a primitive residue element by Hensel, adds a uniformizer,
and uses Nakayama to pass from residue generation to the entire integer ring.
-/

@[expose] public section

open IsLocalRing

namespace FontaineWintenberger

variable {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]

/-- Residue surjectivity and one uniformizer suffice to generate a finite DVR extension. -/
theorem subalgebra_eq_top_of_residue_surjective [Module.Finite R S] [FaithfulSMul R S]
    (A : Subalgebra R S) {z : S} (hz : Irreducible z) (hzA : z ∈ A)
    (hres : ∀ b : S, ∃ a ∈ A, residue S a = residue S b) : A = ⊤ := by
  have hexp (n : ℕ) (b : S) : ∃ a ∈ A, ∃ c : S, b = a + z ^ n * c := by
    induction n generalizing b with
    | zero => exact ⟨0, A.zero_mem, b, by simp⟩
    | succ n ih =>
      obtain ⟨a, ha, c, hc⟩ := ih b
      obtain ⟨d, hd, hdc⟩ := hres c
      have hcd : c - d ∈ maximalIdeal S := by
        rw [← residue_eq_zero_iff, map_sub, hdc, sub_self]
      rw [hz.maximalIdeal_eq, Ideal.mem_span_singleton] at hcd
      obtain ⟨c', hc'⟩ := hcd
      refine ⟨a + z ^ n * d, A.add_mem ha (A.mul_mem (A.pow_mem hzA n) hd), c', ?_⟩
      rw [hc]
      linear_combination z ^ n * hc'
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπ0 : algebraMap R S π ≠ 0 :=
    by simpa using (FaithfulSMul.algebraMap_injective R S).ne hπ.ne_zero
  obtain ⟨e, u, he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hπ0 hz
  apply top_unique
  change (⊤ : Submodule R S) ≤ A.toSubmodule
  apply Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
    (maximalIdeal_le_jacobson ⊥)
  intro b _
  obtain ⟨a, ha, c, hc⟩ := hexp e b
  refine Submodule.mem_sup.mpr ⟨a, ha, z ^ e * c, ?_, hc.symm⟩
  have hπmem : π ∈ maximalIdeal R := hπ.not_isUnit
  have hm : π • ((↑(u⁻¹) : S) * c) ∈ maximalIdeal R • (⊤ : Submodule R S) :=
    Submodule.smul_mem_smul hπmem (Submodule.mem_top)
  convert hm using 1
  rw [Algebra.smul_def, he]
  calc
    z ^ e * c = (↑u * ↑(u⁻¹) : S) * (z ^ e * c) := by simp
    _ = _ := by ring

omit [IsDomain S] [IsDiscreteValuationRing S] in
/-- Lift a separable residue element to a simple root of a monic base polynomial. -/
theorem exists_monic_root_of_residue [Module.Finite R S]
    [IsLocalHom (algebraMap R S)] [HenselianLocalRing S]
    (α : ResidueField S) (hα : IsSeparable (ResidueField R) α) :
    ∃ f : Polynomial R, f.Monic ∧ ∃ a : S,
      Polynomial.aeval a f = 0 ∧ residue S a = α ∧
        IsUnit (Polynomial.aeval a f.derivative) := by
  let p := minpoly (ResidueField R) α
  have hp : p.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral α)
  obtain ⟨f, hfp, -, hf⟩ := Polynomial.lifts_and_degree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective (residue_surjective (R := R)) p) hp
  let g := f.map (algebraMap R S)
  have hmap : g.map (residue S) = p.map (algebraMap (ResidueField R) (ResidueField S)) := by
    dsimp [g]
    rw [Polynomial.map_map, ← hfp, Polynomial.map_map]
    rfl
  have hroot : Polynomial.aeval α g = 0 := by
    rw [← Polynomial.eval_map_algebraMap, ResidueField.algebraMap_eq, hmap,
      Polynomial.eval_map_algebraMap]
    exact minpoly.aeval (ResidueField R) α
  have hder : Polynomial.aeval α g.derivative ≠ 0 := by
    rw [← Polynomial.eval_map_algebraMap, ResidueField.algebraMap_eq,
      ← Polynomial.derivative_map, hmap,
      Polynomial.derivative_map, Polynomial.eval_map_algebraMap]
    exact hα.aeval_derivative_ne_zero (minpoly.aeval (ResidueField R) α)
  have hlift := ((HenselianLocalRing.TFAE S).out 1 2).mp
    (inferInstance : HenselianLocalRing S)
  obtain ⟨a, ha, haα⟩ := hlift g (hf.map _) α hroot hder
  refine ⟨f, hf, a, ?_, haα, ?_⟩
  · simpa only [Polynomial.IsRoot, g, Polynomial.eval_map_algebraMap] using ha
  · have hu : IsUnit (g.derivative.eval a) := by
      apply (residue_ne_zero_iff_isUnit _).mp
      simpa only [← haα, ← Polynomial.eval_map_algebraMap, ResidueField.algebraMap_eq,
        Polynomial.eval_map_apply] using hder
    simpa only [g, Polynomial.derivative_map, Polynomial.eval_map_algebraMap] using hu

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- Adding a uniformizer to a simple root makes its polynomial value a uniformizer. -/
theorem irreducible_aeval_add_of_isRoot {f : Polynomial R} {a z : S}
    (ha : Polynomial.aeval a f = 0) (hder : IsUnit (Polynomial.aeval a f.derivative))
    (hz : Irreducible z) : Irreducible (Polynomial.aeval (a + z) f) := by
  obtain ⟨c, hc⟩ := (f.map (algebraMap R S)).exists_mul_sq_add_linear_part_eq_eval_add a z
  simp only [Polynomial.eval_map_algebraMap, Polynomial.derivative_map] at hc
  have heq : Polynomial.aeval (a + z) f = z * (c * z + Polynomial.aeval a f.derivative) := by
    linear_combination -hc + ha
  have hunit : IsUnit (c * z + Polynomial.aeval a f.derivative) := by
    apply (residue_ne_zero_iff_isUnit _).mp
    have hz0 := (residue_eq_zero_iff z).mpr hz.not_isUnit
    simpa only [map_add, map_mul, hz0, mul_zero, zero_add] using
      (residue_ne_zero_iff_isUnit _).mpr hder
  rw [heq]
  exact (irreducible_mul_isUnit hunit).mpr hz

/-- Finite extensions of Henselian DVRs with separable residue extension are monogenic. -/
theorem exists_integral_generator [Module.Finite R S] [FaithfulSMul R S]
    [IsLocalHom (algebraMap R S)] [HenselianLocalRing S]
    [Algebra.IsSeparable (ResidueField R) (ResidueField S)] :
    ∃ x : S, Algebra.adjoin R {x} = ⊤ := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (ResidueField R) (ResidueField S)
  obtain ⟨f, hf, a, ha, haα, hder⟩ := exists_monic_root_of_residue (R := R) α
    (Algebra.IsSeparable.isSeparable _ _)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible S
  let x := a + π
  have hx : residue S x = α := by
    dsimp [x]
    rw [map_add, haα, (residue_eq_zero_iff π).mpr hπ.not_isUnit, add_zero]
  refine ⟨x, subalgebra_eq_top_of_residue_surjective (Algebra.adjoin R {x})
    (irreducible_aeval_add_of_isRoot ha hder hπ) ?_ ?_⟩
  · exact Polynomial.aeval_mem_adjoin_singleton _ _
  · have htop : Algebra.adjoin (ResidueField R) {residue S x} = ⊤ := by
      rw [hx, ← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
        (IsAlgebraic.of_finite _ _), hα, IntermediateField.top_toSubalgebra]
    rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top] at htop
    intro b
    obtain ⟨p, hp⟩ := htop (residue S b)
    obtain ⟨q, rfl⟩ := Polynomial.map_surjective _ (residue_surjective (R := R)) p
    refine ⟨Polynomial.aeval x q, Polynomial.aeval_mem_adjoin_singleton _ _, ?_⟩
    rw [← Polynomial.map_aeval_eq_aeval_map (ψ := residue S) (φ := residue R) rfl] at hp
    exact hp

/-- Every uniformizer generates when the map on residue fields is surjective. -/
theorem adjoin_uniformizer_eq_top [Module.Finite R S] [FaithfulSMul R S]
    [IsLocalHom (algebraMap R S)]
    (hres : Function.Surjective (algebraMap (ResidueField R) (ResidueField S)))
    {π : S} (hπ : Irreducible π) : Algebra.adjoin R {π} = ⊤ := by
  apply subalgebra_eq_top_of_residue_surjective (Algebra.adjoin R {π}) hπ
    (Algebra.subset_adjoin (by simp))
  intro b
  obtain ⟨a₀, ha₀⟩ := hres (residue S b)
  obtain ⟨a, rfl⟩ := residue_surjective (R := R) a₀
  exact ⟨algebraMap R S a, (Algebra.adjoin R {π}).algebraMap_mem a, ha₀⟩

section Spectral

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
variable [PerfectField (ResidueField (NormedField.valuation (K := K)).valuationSubring)]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
variable [Algebra.IsSeparable K L]

/-- The actual spectral integer ring of a finite separable extension is monogenic. -/
theorem spectralIntegerRing_exists_generator :
    ∃ x : spectralIntegerRing K L,
      Algebra.adjoin (NormedField.valuation (K := K)).valuationSubring {x} = ⊤ :=
  exists_integral_generator

end Spectral

end FontaineWintenberger
