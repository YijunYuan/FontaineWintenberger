module

public import FontaineWintenberger.Ramification.Lower
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Lower groups and normalized integral valuations

For a discrete valuation ring, ideal-power membership agrees with a lower
bound on mathlib's canonical normalized additive valuation `addVal`.
-/

@[expose] public section

namespace FontaineWintenberger

open IsDiscreteValuationRing IsLocalRing
open scoped Pointwise

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- A power of the maximal ideal is a closed ball for the normalized additive
valuation, including at zero and at exponent zero. -/
theorem mem_maximalIdeal_pow_iff_addVal (x : R) (n : ℕ) :
    x ∈ maximalIdeal R ^ n ↔ (n : ℕ∞) ≤ addVal R x := by
  obtain ⟨π, hπ⟩ := exists_irreducible R
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← addVal_le_iff_dvd, hπ.addVal_pow]

variable (G : Type*) [Group G] [MulSemiringAction G R]

/-- Ring automorphisms preserve the canonical normalized integral valuation. -/
@[simp]
theorem addVal_smul (g : G) (x : R) : addVal R (g • x) = addVal R x := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  rw [← mem_maximalIdeal_pow_iff_addVal, ← mem_maximalIdeal_pow_iff_addVal]
  have h : g • (maximalIdeal R ^ n) = maximalIdeal R ^ n := by
    change (maximalIdeal R ^ n).map (MulSemiringAction.toRingHom G R g) = _
    rw [Ideal.map_pow, ← Ideal.pointwise_smul_def, smul_maximalIdeal]
  simpa only [h] using
    (Ideal.smul_mem_pointwise_smul_iff (a := g) (S := maximalIdeal R ^ n) (x := x))

/-- The ideal-inertia definition is the normalized valuation definition. -/
theorem mem_lowerRamificationGroup_iff_addVal (n : ℤ) (g : G) :
    g ∈ lowerRamificationGroup G (maximalIdeal R) n ↔
      ∀ x : R, ((n + 1).toNat : ℕ∞) ≤ addVal R (g • x - x) := by
  simp only [mem_lowerRamificationGroup_iff, mem_maximalIdeal_pow_iff_addVal]

/-- Natural lower indices have the source's unshifted valuation bound `n + 1`. -/
theorem mem_lowerRamificationGroup_nat_iff_addVal (n : ℕ) (g : G) :
    g ∈ lowerRamificationGroup G (maximalIdeal R) n ↔
      ∀ x : R, (n + 1 : ℕ∞) ≤ addVal R (g • x - x) := by
  simpa using mem_lowerRamificationGroup_iff_addVal G (n : ℤ) g

/-- Serre's unshifted order: the infimum of the valuations of all integral
displacements. This uses the intrinsic ring, rather than a chosen generator. -/
noncomputable def ramificationOrder (g : G) : ℕ∞ :=
  ⨅ x : R, addVal R (g • x - x)

theorem ramificationOrder_le (g : G) (x : R) :
    ramificationOrder (R := R) G g ≤ addVal R (g • x - x) :=
  iInf_le _ x

theorem mem_lowerRamificationGroup_iff_le_order (n : ℤ) (g : G) :
    g ∈ lowerRamificationGroup G (maximalIdeal R) n ↔
      ((n + 1).toNat : ℕ∞) ≤ ramificationOrder (R := R) G g := by
  rw [mem_lowerRamificationGroup_iff_addVal, ramificationOrder, le_iInf_iff]

@[simp]
theorem ramificationOrder_one : ramificationOrder (R := R) G 1 = ⊤ := by
  simp [ramificationOrder]

@[simp]
theorem ramificationOrder_inv (g : G) :
    ramificationOrder (R := R) G g⁻¹ = ramificationOrder (R := R) G g := by
  apply iInf_congr
  intro x
  rw [← addVal_smul G g (g⁻¹ • x - x), smul_sub, smul_inv_smul,
    ← neg_sub (g • x) x, AddValuation.map_neg]

theorem ramificationOrder_le_conj (r g : G) :
    ramificationOrder (R := R) G g ≤ ramificationOrder (R := R) G (r * g * r⁻¹) := by
  apply le_iInf
  intro x
  have h : (r * g * r⁻¹) • x - x = r • (g • (r⁻¹ • x) - r⁻¹ • x) := by
    simp [smul_sub, mul_smul]
  rw [h, addVal_smul]
  exact ramificationOrder_le G g _

@[simp]
theorem ramificationOrder_conj (r g : G) :
    ramificationOrder (R := R) G (r * g * r⁻¹) = ramificationOrder (R := R) G g := by
  apply le_antisymm
  · simpa [mul_assoc] using ramificationOrder_le_conj (R := R) G r⁻¹ (r * g * r⁻¹)
  · exact ramificationOrder_le_conj G r g

theorem min_order_le_order_mul (g h : G) :
    min (ramificationOrder (R := R) G g) (ramificationOrder (R := R) G h) ≤
      ramificationOrder (R := R) G (g * h) := by
  apply le_iInf
  intro x
  have he : (g * h) • x - x = (g • (h • x) - h • x) + (h • x - x) := by
    simp [mul_smul]
  rw [he]
  exact (min_le_min (ramificationOrder_le G g (h • x)) (ramificationOrder_le G h x)).trans
    (addVal_add (R := R))

theorem ramificationOrder_mul_of_ne (g h : G)
    (hne : ramificationOrder (R := R) G g ≠ ramificationOrder (R := R) G h) :
    ramificationOrder (R := R) G (g * h) =
      min (ramificationOrder (R := R) G g) (ramificationOrder (R := R) G h) := by
  have h₁ := min_order_le_order_mul (R := R) G g h
  have h₂ := min_order_le_order_mul (R := R) G (g * h) h⁻¹
  have h₃ := min_order_le_order_mul (R := R) G g⁻¹ (g * h)
  simp only [ramificationOrder_inv, mul_inv_cancel_right, inv_mul_cancel_left] at h₂ h₃
  rcases lt_or_gt_of_ne hne with hlt | hlt <;> order

theorem ramificationOrder_eq_top_iff [FaithfulSMul G R] (g : G) :
    ramificationOrder (R := R) G g = ⊤ ↔ g = 1 := by
  constructor
  · intro hg
    apply FaithfulSMul.eq_of_smul_eq_smul (α := R)
    intro x
    have hv : addVal R (g • x - x) = ⊤ :=
      top_le_iff.mp (hg ▸ ramificationOrder_le G g x)
    simpa only [sub_eq_zero, one_smul] using addVal_eq_top_iff.mp hv
  · rintro rfl
    exact ramificationOrder_one G

/-- A finite faithful action has eventually trivial lower groups. -/
theorem lowerRamificationGroup_eventually_eq_bot [Finite G] [FaithfulSMul G R] :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → lowerRamificationGroup G (maximalIdeal R) n = ⊥ := by
  classical
  let := Fintype.ofFinite G
  let N := Finset.univ.sup (fun g : G => (ramificationOrder (R := R) G g).toNat)
  refine ⟨N, fun n hn => ?_⟩
  apply le_antisymm _ bot_le
  intro g hg
  change g = 1
  by_contra hne
  have hfinite : ramificationOrder (R := R) G g ≠ ⊤ :=
    (ramificationOrder_eq_top_iff G g).not.mpr hne
  have hbound : (ramificationOrder (R := R) G g).toNat ≤ N :=
    Finset.le_sup (f := fun g : G => (ramificationOrder (R := R) G g).toNat) (Finset.mem_univ g)
  have hmem := (mem_lowerRamificationGroup_iff_le_order G (n : ℤ) g).mp hg
  have : (n + 1 : ℕ∞) ≤ (ramificationOrder (R := R) G g).toNat := by
    simpa [ENat.natCast_toNat hfinite] using hmem
  have : n + 1 ≤ (ramificationOrder (R := R) G g).toNat := by exact_mod_cast this
  omega

end FontaineWintenberger

namespace ValuationSubring

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
variable (A : ValuationSubring L) [IsDiscreteValuationRing A]

/-- Intrinsic unshifted integral order for the decomposition-group action. -/
noncomputable def ramificationOrder (g : A.decompositionSubgroup K) : ℕ∞ :=
  FontaineWintenberger.ramificationOrder (R := A) (A.decompositionSubgroup K) g

theorem mem_lowerRamificationGroup_iff_addVal (n : ℤ) (g : A.decompositionSubgroup K) :
    g ∈ A.lowerRamificationGroup K n ↔
      ∀ x : A, ((n + 1).toNat : ℕ∞) ≤ IsDiscreteValuationRing.addVal A (g • x - x) :=
  FontaineWintenberger.mem_lowerRamificationGroup_iff_addVal _ n g

theorem mem_lowerRamificationGroup_iff_le_order (n : ℤ) (g : A.decompositionSubgroup K) :
    g ∈ A.lowerRamificationGroup K n ↔ ((n + 1).toNat : ℕ∞) ≤ A.ramificationOrder K g :=
  FontaineWintenberger.mem_lowerRamificationGroup_iff_le_order _ n g

@[simp]
theorem ramificationOrder_eq_top_iff (g : A.decompositionSubgroup K) :
    A.ramificationOrder K g = ⊤ ↔ g = 1 :=
  FontaineWintenberger.ramificationOrder_eq_top_iff _ g

theorem lowerRamificationGroup_eventually_eq_bot [Finite (L ≃ₐ[K] L)] :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → A.lowerRamificationGroup K n = ⊥ :=
  FontaineWintenberger.lowerRamificationGroup_eventually_eq_bot _

end ValuationSubring
