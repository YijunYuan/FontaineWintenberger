/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.APF.Tower.PrimeValuation
public import FontaineWintenberger.FieldOfNorms.Basic.Addition
public import FontaineWintenberger.LocalField.Basic
public import Mathlib.Algebra.Ring.MinimalAxioms

/-!
# The field of norms as a valued field

The addition constructed from norm-sum limits satisfies the ring laws by coordinate
approximation and separation at a fixed finite field. Diverging ramification bounds force the
residue characteristic `p` to vanish; the `(p - 1)`-fold sum then gives additive inverses.

Together with the multiplicative structure and stable coordinate valuation, this makes the
field of norms a valued field of characteristic `p`, as in Wintenberger, Theorem 2.1.3 (ii).
The file also proves coordinate estimates for finite sums and differences.

## Main definitions

* `FieldOfNorms.fieldValuation`: The same stable map, now bundled as a field valuation for the
  constructed field.

## Main results

* `FieldOfNorms.add_assoc`: Associativity of the field of norms addition follows from four
  coordinate approximations and separation at a fixed finite base.
* `FieldOfNorms.valuation_sum_le_one`: Finite sums of integral families remain integral for the
  already constructed additive structure.
* `FieldOfNorms.coord_sum_sub_mem`: Every finite sum of families approximates the ordinary sum of
  its coordinates on a finite tail at each prescribed precision.
* `FieldOfNorms.coord_nsmul_sub_mem`: Repeated addition approximates ordinary coordinate repeated
  addition.
* `FieldOfNorms.natCast_prime_eq_zero`: The residue prime vanishes in the field of norms semiring,
  by coordinate approximation and ramification divergence.
* `FieldOfNorms.pred_nsmul_add_eq_zero`: The (p-1)-fold sum is an additive inverse, including p=2.
* `FieldOfNorms.field_toCommSemiring`: The field structure extends the semiring structure
  definitionally: there is a single addition, `natCast` and `nsmul` on the carrier.
* `FieldOfNorms.field_add`: The field addition is definitionally the field of norms sum operation.

## Notation

The following notation is local to this file.

* `p` denotes the residue characteristic `residueChar K`.

## References

* Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux;
  applications*, §2–3 (le corps des normes, fonctorialité).
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- Associativity of the field of norms addition follows from four
coordinate approximations and separation at a fixed finite base. -/
theorem FieldOfNorms.add_assoc [IsAPF K L] (α β γ : FieldOfNorms K L) :
    FieldOfNorms.add K L (FieldOfNorms.add K L α β) γ =
      FieldOfNorms.add K L α (FieldOfNorms.add K L β γ) := by
  apply FieldOfNorms.ext_of_eventually_sub_mem K L
  intro n
  obtain ⟨T₁, hT₁⟩ := FieldOfNorms.add_sub_mem K L (FieldOfNorms.add K L α β) γ n
  obtain ⟨T₂, hT₂⟩ := FieldOfNorms.add_sub_mem K L α β n
  obtain ⟨T₃, hT₃⟩ := FieldOfNorms.add_sub_mem K L α (FieldOfNorms.add K L β γ) n
  obtain ⟨T₄, hT₄⟩ := FieldOfNorms.add_sub_mem K L β γ n
  refine ⟨FiniteIntermediateField.sup (FiniteIntermediateField.sup T₁ T₂)
      (FiniteIntermediateField.sup T₃ T₄), fun E hE => ?_⟩
  have hE₁₂ := (FiniteIntermediateField.le_sup_left (FiniteIntermediateField.sup T₁ T₂)
    (FiniteIntermediateField.sup T₃ T₄)).trans hE
  have hE₃₄ := (FiniteIntermediateField.le_sup_right (FiniteIntermediateField.sup T₁ T₂)
    (FiniteIntermediateField.sup T₃ T₄)).trans hE
  obtain ⟨d₁, hd₁, heq₁⟩ := hT₁ E ((FiniteIntermediateField.le_sup_left T₁ T₂).trans hE₁₂)
  obtain ⟨d₂, hd₂, heq₂⟩ := hT₂ E ((FiniteIntermediateField.le_sup_right T₁ T₂).trans hE₁₂)
  obtain ⟨d₃, hd₃, heq₃⟩ := hT₃ E ((FiniteIntermediateField.le_sup_left T₃ T₄).trans hE₃₄)
  obtain ⟨d₄, hd₄, heq₄⟩ := hT₄ E ((FiniteIntermediateField.le_sup_right T₃ T₄).trans hE₃₄)
  refine ⟨d₁ + d₂ - d₃ - d₄,
    Ideal.sub_mem _ (Ideal.sub_mem _ (Ideal.add_mem _ hd₁ hd₂) hd₃) hd₄, ?_⟩
  change (d₁ : E.val) + (d₂ : E.val) - (d₃ : E.val) - (d₄ : E.val) = _
  linear_combination heq₁ + heq₂ - heq₃ - heq₄

/-- The zero and the constructed addition form a commutative monoid
on the same carrier. Low priority: when `L/K` is infinite the `Field` instance supplies the
same structure, and instance search should go through it so that all paths agree syntactically. -/
instance (priority := low) FieldOfNorms.instAddCommMonoid [IsAPF K L] :
    AddCommMonoid (FieldOfNorms K L) where
  zero := 0
  add := FieldOfNorms.add K L
  add_assoc := FieldOfNorms.add_assoc K L
  zero_add := FieldOfNorms.zero_add K L
  add_zero := FieldOfNorms.add_zero K L
  add_comm := FieldOfNorms.add_comm K L
  nsmul := @nsmulRec (FieldOfNorms K L) inferInstance ⟨FieldOfNorms.add K L⟩

end FontaineWintenberger

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- Finite sums of integral families remain integral for the
already constructed additive structure. -/
theorem FieldOfNorms.valuation_sum_le_one [IsAPF K L] {ι : Type*}
    (s : Finset ι) (a : ι → FieldOfNorms K L)
    (ha : ∀ i ∈ s, FieldOfNorms.valuation K L (a i) ≤ 1) :
    FieldOfNorms.valuation K L (∑ i ∈ s, a i) ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact FieldOfNorms.valuation_add_le_one K L _ _
      (ha i (Finset.mem_insert_self i s)) (ih (fun j hj => ha j (Finset.mem_insert_of_mem hj)))

/-- Every finite sum of families approximates the ordinary sum
of its coordinates on a finite tail at each prescribed precision. -/
theorem FieldOfNorms.coord_sum_sub_mem [IsAPF K L] {ι : Type*}
    (s : Finset ι) (a : ι → FieldOfNorms K L) :
    ∀ n : ℕ, ∃ T : FiniteIntermediateField K L, ∀ E : FiniteIntermediateField K L, T ≤ E →
      FieldOfNorms.coord K L E (∑ i ∈ s, a i) - ∑ i ∈ s, FieldOfNorms.coord K L E (a i) ∈
        (fun x : spectralIntegerRing K E.val => (x : E.val)) ''
          ((IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ n :
            Ideal (spectralIntegerRing K E.val)) : Set (spectralIntegerRing K E.val)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro n
    refine ⟨FiniteIntermediateField.bottom, fun E _ => ?_⟩
    simp only [Finset.sum_empty, _root_.map_zero, sub_self]
    exact ⟨0, Ideal.zero_mem _, rfl⟩
  | @insert i s hi ih =>
    intro n
    obtain ⟨T₁, hT₁⟩ := FieldOfNorms.add_sub_mem K L (a i) (∑ j ∈ s, a j) n
    obtain ⟨T₂, hT₂⟩ := ih n
    refine ⟨FiniteIntermediateField.sup T₁ T₂, fun E hE => ?_⟩
    obtain ⟨d₁, hd₁, heq₁⟩ := hT₁ E ((FiniteIntermediateField.le_sup_left T₁ T₂).trans hE)
    obtain ⟨d₂, hd₂, heq₂⟩ := hT₂ E ((FiniteIntermediateField.le_sup_right T₁ T₂).trans hE)
    refine ⟨d₁ + d₂, Ideal.add_mem _ hd₁ hd₂, ?_⟩
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    change (d₁ : E.val) + (d₂ : E.val) = _
    linear_combination heq₁ + heq₂

/-- Repeated addition approximates ordinary coordinate repeated addition. -/
theorem FieldOfNorms.coord_nsmul_sub_mem [IsAPF K L] (m : ℕ) (α : FieldOfNorms K L) :
    ∀ n : ℕ, ∃ T : FiniteIntermediateField K L, ∀ E : FiniteIntermediateField K L, T ≤ E →
      FieldOfNorms.coord K L E (m • α) - m • FieldOfNorms.coord K L E α ∈
        (fun x : spectralIntegerRing K E.val => (x : E.val)) ''
          ((IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ n :
            Ideal (spectralIntegerRing K E.val)) : Set (spectralIntegerRing K E.val)) := by
  simpa only [Finset.sum_const, Finset.card_range] using
    FieldOfNorms.coord_sum_sub_mem K L (Finset.range m) (fun _ => α)

end FontaineWintenberger

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- The field of norms addition and multiplication give a named
commutative semiring, preserving the multiplicative structure. -/
instance (priority := low) FieldOfNorms.instCommSemiring [IsAPF K L] :
    CommSemiring (FieldOfNorms K L) where
  __ := (inferInstance : CommMonoidWithZero (FieldOfNorms K L))
  __ := FieldOfNorms.instAddCommMonoid K L
  left_distrib := FieldOfNorms.mul_add K L
  right_distrib := fun a b c => by
    change FieldOfNorms.add K L a b * c =
      FieldOfNorms.add K L (a * c) (b * c)
    rw [mul_comm _ c, FieldOfNorms.mul_add, mul_comm c a, mul_comm c b]
  natCast := fun n => n • (1 : FieldOfNorms K L)
  natCast_zero := zero_nsmul _
  natCast_succ := fun n => AddMonoid.nsmul_succ n _

end FontaineWintenberger

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- The residue prime vanishes in the field of norms semiring, by
coordinate approximation and ramification divergence. -/
theorem FieldOfNorms.natCast_prime_eq_zero [IsAPF K L]
    [Fact (¬ Module.Finite K L)] :
    (p : FieldOfNorms K L) = 0 := by
  apply FieldOfNorms.ext_of_eventually_sub_mem K L
  intro n
  obtain ⟨T₁, hT₁⟩ := FieldOfNorms.coord_nsmul_sub_mem K L p 1 n
  obtain ⟨T₂, hT₂⟩ := IsAPF.exists_finiteIntermediateField_natCast_mem_image_maximalIdeal_pow
    K L n
  refine ⟨FiniteIntermediateField.sup T₁ T₂, fun E hE => ?_⟩
  obtain ⟨d₁, hd₁, heq₁⟩ := hT₁ E ((FiniteIntermediateField.le_sup_left T₁ T₂).trans hE)
  obtain ⟨d₂, hd₂, heq₂⟩ := hT₂ E ((FiniteIntermediateField.le_sup_right T₁ T₂).trans hE)
  refine ⟨d₁ + d₂, Ideal.add_mem _ hd₁ hd₂, ?_⟩
  change (d₁ : E.val) + (d₂ : E.val) = _
  simp only [_root_.map_one, nsmul_eq_mul, mul_one] at heq₁
  rw [_root_.map_zero, sub_zero]
  change (d₁ : E.val) + (d₂ : E.val) = FieldOfNorms.coord K L E (p • (1 : FieldOfNorms K L))
  linear_combination heq₁ + heq₂

/-- The (p-1)-fold sum is an additive inverse, including p=2. -/
theorem FieldOfNorms.pred_nsmul_add_eq_zero [IsAPF K L]
    [Fact (¬ Module.Finite K L)] (α : FieldOfNorms K L) :
    (p - 1) • α + α = 0 := by
  rw [← AddMonoid.nsmul_succ, Nat.sub_add_cancel (Fact.out : Nat.Prime p).one_le]
  rw [nsmul_eq_mul, FieldOfNorms.natCast_prime_eq_zero K L, zero_mul]

/-- The multiplicative field of norms is a field under the
addition. Every additive inverse is its (p-1)-fold sum. -/
instance FieldOfNorms.instNeg [IsAPF K L] [Fact (¬ Module.Finite K L)] :
    Neg (FieldOfNorms K L) where
  neg α := (p - 1) • α

/-- **Theorem 2.1.3 (ii).** The field of norms of an infinite APF extension is a field. -/
instance FieldOfNorms.instField [IsAPF K L] [Fact (¬ Module.Finite K L)] :
    Field (FieldOfNorms K L) where
  __ := FieldOfNorms.instCommSemiring K L
  __ := FieldOfNorms.instCommGroupWithZero K L
  __ := FieldOfNorms.instNeg K L
  neg_add_cancel := FieldOfNorms.pred_nsmul_add_eq_zero K L
  zsmul := zsmulRec
  nnqsmul := _
  qsmul := _

/-- The field structure extends the semiring structure definitionally: there is a single
addition, `natCast` and `nsmul` on the carrier. -/
theorem FieldOfNorms.field_toCommSemiring [IsAPF K L] [Fact (¬ Module.Finite K L)] :
    @Semifield.toCommSemiring _ (FieldOfNorms.instField K L).toSemifield =
        FieldOfNorms.instCommSemiring K L :=
  rfl

/-- **Theorem 2.1.3 (ii).** The field of norms has characteristic `p`, the residue characteristic
of `K`. -/
instance FieldOfNorms.instCharP [IsAPF K L] [Fact (¬ Module.Finite K L)] :
    CharP (FieldOfNorms K L) p := by
  have h := FieldOfNorms.natCast_prime_eq_zero K L
  change p • (1 : FieldOfNorms K L) = 0 at h
  exact (CharP.charP_iff_prime_eq_zero (R := FieldOfNorms K L) (Fact.out : Nat.Prime p)).mpr
    (by simpa only [nsmul_one] using h)

/-- The field addition is definitionally the field of norms sum operation. -/
@[simp]
theorem FieldOfNorms.field_add [IsAPF K L] [Fact (¬ Module.Finite K L)]
    (α β : FieldOfNorms K L) :
    α + β = FieldOfNorms.add K L α β := rfl

/-- The entire commutative group with zero is retained definitionally
by the field structure, including multiplication, inversion and division. -/
theorem FieldOfNorms.field_toCommGroupWithZero [IsAPF K L]
    [Fact (¬ Module.Finite K L)] :
    @Semifield.toCommGroupWithZero _ (FieldOfNorms.instField K L).toSemifield =
      FieldOfNorms.instCommGroupWithZero K L := rfl

end FontaineWintenberger

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- The stable multiplicative valuation is ultrametric for the
field of norms addition, before any valuation topology is chosen. -/
theorem FieldOfNorms.valuation_add_le_max [IsAPF K L] (α β : FieldOfNorms K L) :
    FieldOfNorms.valuation K L (FieldOfNorms.add K L α β) ≤
      max (FieldOfNorms.valuation K L α) (FieldOfNorms.valuation K L β) := by
  by_cases hα : α = 0
  · simp only [hα, FieldOfNorms.zero_add, _root_.map_zero, zero_le, max_eq_right, le_refl]
  by_cases hβ : β = 0
  · simp only [hβ, FieldOfNorms.add_zero, _root_.map_zero, zero_le, max_eq_left, le_refl]
  let w := FieldOfNorms.valuation K L
  have hαw : w α ≠ 0 := fun h => hα ((FieldOfNorms.valuation_eq_zero_iff K L α).mp h)
  have hβw : w β ≠ 0 := fun h => hβ ((FieldOfNorms.valuation_eq_zero_iff K L β).mp h)
  have hscale : ∃ δ : FieldOfNorms K L, δ ≠ 0 ∧ w δ = max (w α) (w β) ∧
      w (α / δ) ≤ 1 ∧ w (β / δ) ≤ 1 := by
    rcases le_total (w α) (w β) with h | h
    · refine ⟨β, hβ, (max_eq_right h).symm, ?_, ?_⟩
      · rw [map_div₀]
        exact (div_le_one₀ (pos_iff_ne_zero.mpr hβw)).mpr h
      · simp only [div_self hβ, _root_.map_one, le_refl]
    · refine ⟨α, hα, (max_eq_left h).symm, ?_, ?_⟩
      · simp only [div_self hα, _root_.map_one, le_refl]
      · rw [map_div₀]
        exact (div_le_one₀ (pos_iff_ne_zero.mpr hαw)).mpr h
  obtain ⟨δ, hδ, hmax, ha, hb⟩ := hscale
  have hδα : δ * (α / δ) = α := by simp [div_eq_mul_inv, mul_left_comm, hδ]
  have hδβ : δ * (β / δ) = β := by simp [div_eq_mul_inv, mul_left_comm, hδ]
  have hsum := FieldOfNorms.valuation_add_le_one K L (α / δ) (β / δ) ha hb
  have heq := FieldOfNorms.mul_add K L δ (α / δ) (β / δ)
  rw [hδα, hδβ] at heq
  change w (FieldOfNorms.add K L α β) ≤ max (w α) (w β)
  rw [← heq, _root_.map_mul, ← hmax]
  simpa only [mul_one] using mul_le_mul' (le_refl (w δ)) hsum

/-- The same stable map, now bundled as a field valuation for the
constructed field. No new map or alternate field carrier is introduced. -/
def FieldOfNorms.fieldValuation [IsAPF K L] [Fact (¬ Module.Finite K L)] :
    Valuation (FieldOfNorms K L) (WithZero (Multiplicative ℤ)) where
  __ := FieldOfNorms.valuation K L
  map_add_le_max' := FieldOfNorms.valuation_add_le_max K L

/-- Bundling the field valuation preserves exactly the existing stable map. -/
@[simp]
theorem FieldOfNorms.fieldValuation_apply [IsAPF K L]
    [Fact (¬ Module.Finite K L)] (α : FieldOfNorms K L) :
    FieldOfNorms.fieldValuation K L α = FieldOfNorms.valuation K L α := rfl

/-- **Theorem 2.1.3 (ii).** The field of norms is a valued field with value group `ℤ`, the
valuation being the stable normalized valuation of the coordinates. -/
instance FieldOfNorms.instValued [IsAPF K L] [Fact (¬ Module.Finite K L)] :
    Valued (FieldOfNorms K L) (WithZero (Multiplicative ℤ)) :=
  Valued.mk' (FieldOfNorms.fieldValuation K L)

end FontaineWintenberger

noncomputable section

namespace FontaineWintenberger

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- Norm-field subtraction agrees with ordinary coordinate subtraction
to every ideal-power precision on a finite tail. -/
theorem FieldOfNorms.coord_sub_sub_mem [IsAPF K L]
    [Fact (¬ Module.Finite K L)] :
    ∀ (α β : FieldOfNorms K L) (n : ℕ),
      ∃ T : FiniteIntermediateField K L, ∀ E : FiniteIntermediateField K L, T ≤ E →
        FieldOfNorms.coord K L E (α - β) - FieldOfNorms.coord K L E α +
          FieldOfNorms.coord K L E β ∈
          (fun x : spectralIntegerRing K E.val => (x : E.val)) ''
            ((IsLocalRing.maximalIdeal (spectralIntegerRing K E.val) ^ n :
              Ideal (spectralIntegerRing K E.val)) : Set (spectralIntegerRing K E.val)) := by
  intro α β n
  obtain ⟨T, hT⟩ := FieldOfNorms.add_sub_mem K L (α - β) β n
  have hs : FieldOfNorms.add K L (α - β) β = α := sub_add_cancel α β
  refine ⟨T, fun E hE => ?_⟩
  obtain ⟨z, hz, heq⟩ := hT E hE
  rw [hs] at heq
  refine ⟨-z, neg_mem hz, ?_⟩
  change -(z : E.val) = _
  linear_combination -heq

/-- Cofinal exact valuations of finite-coordinate differences compute
the norm-field valuation, for every signed displacement order. -/
theorem FieldOfNorms.valuation_sub_eq_of_cofinal_coordinate [IsAPF K L]
    [Fact (¬ Module.Finite K L)] :
    ∀ (α β : FieldOfNorms K L) (n : ℤ),
      (∀ T : FiniteIntermediateField K L, ∃ E : FiniteIntermediateField K L, T ≤ E ∧
        (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K E.val)).valuation E.val
          (FieldOfNorms.coord K L E α - FieldOfNorms.coord K L E β) = WithZero.exp (-n)) →
      FieldOfNorms.valuation K L (α - β) = WithZero.exp (-n) := by
  intro α β n hcofinal
  let s : ℕ := n.toNat + 1
  obtain ⟨T₀, hT₀⟩ := FieldOfNorms.exists_valuation_eq_coordinateValuation K L
  obtain ⟨T₁, hT₁⟩ := FieldOfNorms.coord_sub_sub_mem K L α β s
  obtain ⟨E, hE, hval⟩ := hcofinal (FiniteIntermediateField.sup T₀ T₁)
  have hE₀ := (FiniteIntermediateField.le_sup_left T₀ T₁).trans hE
  have hE₁ := (FiniteIntermediateField.le_sup_right T₀ T₁).trans hE
  let v := (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K E.val)).valuation E.val
  have hbound : v (FieldOfNorms.coord K L E (α - β) - FieldOfNorms.coord K L E α +
      FieldOfNorms.coord K L E β) ≤ WithZero.exp (-(s : ℤ)) :=
    (ValuationSubring.mem_image_maximalIdeal_pow_iff_normalizedValuation
      (spectralIntegerRing K E.val) _ s).mp (hT₁ E hE₁)
  have hlt : WithZero.exp (-(s : ℤ)) < WithZero.exp (-n) := by
    apply WithZero.exp_lt_exp.mpr
    dsimp [s]
    omega
  have hclose : v (FieldOfNorms.coord K L E (α - β) -
      (FieldOfNorms.coord K L E α - FieldOfNorms.coord K L E β)) <
        v (FieldOfNorms.coord K L E α - FieldOfNorms.coord K L E β) := by
    rw [hval]
    have heq : FieldOfNorms.coord K L E (α - β) -
        (FieldOfNorms.coord K L E α - FieldOfNorms.coord K L E β) =
        FieldOfNorms.coord K L E (α - β) - FieldOfNorms.coord K L E α +
          FieldOfNorms.coord K L E β := by ring
    rw [heq]
    exact hbound.trans_lt hlt
  rw [hT₀ E hE₀]
  change v (FieldOfNorms.coord K L E (α - β)) = _
  exact (v.map_eq_of_sub_lt hclose).trans hval

end FontaineWintenberger
