module

public import FontaineWintenberger.LocalField.UniformContinuity
public import Mathlib.RingTheory.PowerSeries.Evaluation
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.Topology.Algebra.Valued.WithZeroMulInt

/-!
# Laurent coordinates from an actual coefficient section and a uniformizer

Evaluation in the original valuation ring is bijective by residue-digit
recursion. Its fraction-field extension preserves the original valuation.
-/

@[expose] public section

noncomputable section

open Filter WithZero
open scoped Topology PowerSeries.WithPiTopology LaurentSeries RatFunc

namespace FontaineWintenberger

section CompleteIntegerRing

variable {k R : Type*} [Field k] [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (c : k →+* R) (e : k ≃+* IsLocalRing.ResidueField R)
    (hc : ∀ a, IsLocalRing.residue R (c a) = e a)
variable (π : R) (hπ : Irreducible π)

/-- The residue digit in the actual coefficient section. -/
def residueDigit (x : R) : k := e.symm (IsLocalRing.residue R x)

include hc hπ in
/-- Subtracting the actual residue digit leaves a multiple of the original
uniformizer in the original integer ring. -/
theorem exists_residue_quotient (x : R) :
    ∃ q : R, x - c (residueDigit e x) = π * q := by
  have hm : x - c (residueDigit e x) ∈ IsLocalRing.maximalIdeal R := by
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    change IsLocalRing.residue R (x - c (residueDigit e x)) = 0
    rw [map_sub, hc]
    exact sub_eq_zero.mpr (e.apply_symm_apply _).symm
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
  exact hm

/-- The quotient after subtracting the actual residue digit. -/
def residueQuotient (x : R) : R :=
  (exists_residue_quotient c e hc π hπ x).choose

/-- The digit and quotient satisfy the actual subtraction identity. -/
theorem residueQuotient_spec (x : R) :
    x - c (residueDigit e x) = π * residueQuotient c e hc π hπ x :=
  (exists_residue_quotient c e hc π hπ x).choose_spec

/-- Repeated actual subtraction and division by the uniformizer. -/
def residueRemainder (x : R) : ℕ → R
  | 0 => x
  | n + 1 => residueQuotient c e hc π hπ (residueRemainder x n)

/-- The power series obtained from the actual residue-digit recursion. -/
def residueExpansion (x : R) : PowerSeries k :=
  PowerSeries.mk (fun n => residueDigit e (residueRemainder c e hc π hπ x n))

/-- The finite residue-digit expansion has exactly the original integral
remainder multiplied by the corresponding power of the uniformizer. -/
theorem residueExpansion_remainder (x : R) (n : ℕ) :
    x - ∑ j ∈ Finset.range n, c ((residueExpansion c e hc π hπ x).coeff j) * π ^ j =
      π ^ n * residueRemainder c e hc π hπ x n := by
  induction n with
  | zero => simp [residueRemainder]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← sub_sub, ih, pow_succ]
    simp only [residueExpansion, PowerSeries.coeff_mk, residueRemainder]
    rw [mul_assoc, ← residueQuotient_spec c e hc π hπ]
    ring

variable [UniformSpace k] [DiscreteUniformity k]
variable [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]
    [CompleteSpace R] [T2Space R] [IsLinearTopology R R]
variable (hπtop : PowerSeries.HasEval π)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsUniformAddGroup R]
    [IsTopologicalRing R] [CompleteSpace R] [T2Space R] in
include hπtop in
/-- Multiplication by arbitrary elements of the integer ring does not
spoil convergence of uniformizer powers in its actual linear topology. -/
theorem tendsto_uniformizer_pow_mul (q : ℕ → R) :
    Tendsto (fun n : ℕ => π ^ n * q n) atTop (𝓝 0) := by
  rw [(IsLinearTopology.hasBasis_submodule R).tendsto_right_iff]
  intro U hU
  filter_upwards [hπtop.eventually hU] with n hn
  change π ^ n * q n ∈ U
  simpa only [smul_eq_mul, mul_comm] using U.smul_mem (q n) hn

omit [UniformSpace k] [DiscreteUniformity k] [IsUniformAddGroup R]
    [CompleteSpace R] [T2Space R] in
include hπtop in
/-- The actual partial sums of the residue expansion converge to the
original element of the original complete ring. -/
theorem tendsto_residueExpansion_partialSums (x : R) :
    Tendsto (fun n : ℕ =>
      ∑ j ∈ Finset.range n, c ((residueExpansion c e hc π hπ x).coeff j) * π ^ j)
      atTop (𝓝 x) := by
  have h := tendsto_uniformizer_pow_mul π hπtop
    (residueRemainder c e hc π hπ x)
  have hs := (tendsto_const_nhds (x := x)).sub h
  simpa only [← residueExpansion_remainder c e hc π hπ x, sub_sub_cancel, sub_zero] using hs

include hπtop in
/-- Evaluation of the actual residue expansion is the original element. -/
theorem eval₂_residueExpansion (x : R) :
    PowerSeries.eval₂ c π (residueExpansion c e hc π hπ x) = x := by
  exact tendsto_nhds_unique
    ((PowerSeries.hasSum_eval₂ (continuous_of_discreteTopology : Continuous c)
      hπtop _).tendsto_sum_nat)
    (tendsto_residueExpansion_partialSums c e hc π hπ hπtop x)

include e hc hπ hπtop in
/-- Every integral element is represented by the power series produced by
actual residue-digit recursion, without assuming an expansion certificate. -/
theorem powerSeries_eval₂_surjective : Function.Surjective (PowerSeries.eval₂ c π) :=
  fun x => ⟨residueExpansion c e hc π hπ x,
    eval₂_residueExpansion c e hc π hπ hπtop x⟩

include hπ hπtop in
/-- The first nonzero coefficient factors out a uniformizer power and leaves
a unit, so evaluation cannot annihilate a nonzero power series. -/
theorem powerSeries_eval₂_ne_zero (f : PowerSeries k) (hf : f ≠ 0) :
    PowerSeries.eval₂ c π f ≠ 0 := by
  let φ := PowerSeries.eval₂Hom (continuous_of_discreteTopology : Continuous c) hπtop
  have hu := (PowerSeries.isUnit_divided_by_X_pow_order hf).map φ
  have heval : (φ : PowerSeries k → R) = PowerSeries.eval₂ c π :=
    PowerSeries.coe_eval₂Hom _ hπtop
  rw [← heval]
  rw [← PowerSeries.X_pow_order_mul_divXPowOrder (f := f), map_mul, map_pow]
  have hX : φ PowerSeries.X = π := by
    rw [heval]
    exact PowerSeries.eval₂_X c π
  rw [hX]
  exact mul_ne_zero (pow_ne_zero _ hπ.ne_zero) hu.ne_zero

include hπ hπtop in
/-- Evaluation is injective by the actual first-nonzero-coefficient factorization. -/
theorem powerSeries_eval₂_injective : Function.Injective (PowerSeries.eval₂ c π) := by
  let φ := PowerSeries.eval₂Hom (continuous_of_discreteTopology : Continuous c) hπtop
  intro f g hfg
  apply sub_eq_zero.mp
  by_contra hne
  have hn := powerSeries_eval₂_ne_zero c π hπ hπtop (f - g) hne
  have heval : (φ : PowerSeries k → R) = PowerSeries.eval₂ c π :=
    PowerSeries.coe_eval₂Hom _ hπtop
  rw [← heval] at hn hfg
  exact hn (by rw [map_sub, hfg, sub_self])

/-- The actual residue-digit evaluation isomorphism for the given
coefficient section and original uniformizer. -/
def powerSeriesUniformizerEquiv : PowerSeries k ≃+* R :=
  RingEquiv.ofBijective
    (PowerSeries.eval₂Hom (continuous_of_discreteTopology : Continuous c) hπtop)
    (by
      simpa only [Function.Bijective, PowerSeries.coe_eval₂Hom] using
        And.intro (powerSeries_eval₂_injective c π hπ hπtop)
          (powerSeries_eval₂_surjective c e hc π hπ hπtop))

/-- The isomorphism is the original convergent evaluation. -/
theorem powerSeriesUniformizerEquiv_apply (f : PowerSeries k) :
    powerSeriesUniformizerEquiv c e hc π hπ hπtop f = PowerSeries.eval₂ c π f :=
  congrFun (PowerSeries.coe_eval₂Hom
    (continuous_of_discreteTopology : Continuous c) hπtop) f

/-- Constants are the prescribed original coefficient representatives. -/
@[simp]
theorem powerSeriesUniformizerEquiv_C (a : k) :
    powerSeriesUniformizerEquiv c e hc π hπ hπtop (PowerSeries.C a) = c a :=
  (powerSeriesUniformizerEquiv_apply c e hc π hπ hπtop _).trans
    (PowerSeries.eval₂_C c π a)

/-- The parameter is sent to the chosen original uniformizer. -/
@[simp]
theorem powerSeriesUniformizerEquiv_X :
    powerSeriesUniformizerEquiv c e hc π hπ hπtop PowerSeries.X = π :=
  (powerSeriesUniformizerEquiv_apply c e hc π hπ hπtop _).trans
    (PowerSeries.eval₂_X c π)

/-- Evaluation uses the inherited topology of the original integer ring. -/
theorem continuous_powerSeriesUniformizerEquiv :
    Continuous (powerSeriesUniformizerEquiv c e hc π hπ hπtop) := by
  have heval : (powerSeriesUniformizerEquiv c e hc π hπ hπtop : PowerSeries k → R) =
      PowerSeries.eval₂ c π := funext (powerSeriesUniformizerEquiv_apply c e hc π hπ hπtop)
  rw [heval]
  exact PowerSeries.continuous_eval₂ (continuous_of_discreteTopology : Continuous c) hπtop

/-- Polynomial density characterizes evaluation among continuous ring maps
with the same actual constants and parameter. -/
theorem powerSeriesUniformizerEquiv_unique (f : PowerSeries k →+* R)
    (hf : Continuous f) (hC : ∀ a, f (PowerSeries.C a) = c a)
    (hX : f PowerSeries.X = π) :
    f = (powerSeriesUniformizerEquiv c e hc π hπ hπtop).toRingHom := by
  have hp : f.comp Polynomial.coeToPowerSeries.ringHom = Polynomial.eval₂RingHom c π := by
    apply Polynomial.ringHom_ext
    · intro a
      simpa only [RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply,
        Polynomial.coe_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C] using hC a
    · simpa only [RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply,
        Polynomial.coe_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] using hX
  have hu := PowerSeries.eval₂_unique (continuous_of_discreteTopology : Continuous c)
    hπtop hf (fun q => DFunLike.congr_fun hp q)
  apply RingHom.ext
  intro A
  exact (congrFun hu A).trans (powerSeriesUniformizerEquiv_apply c e hc π hπ hπtop A).symm

end CompleteIntegerRing

section OriginalValuationRing

variable (F : Type*) [Field F] [hv : Valued F ℤᵐ⁰]

/-- The actual valuation ring inherits the original topological ring structure. -/
instance valuationSubring_isTopologicalRing : IsTopologicalRing hv.v.valuationSubring :=
  inferInstanceAs (IsTopologicalRing hv.v.integer)

/-- The inherited additive uniformity on the actual valuation ring. -/
instance valuationSubring_isUniformAddGroup : IsUniformAddGroup hv.v.valuationSubring :=
  IsUniformAddGroup.comap hv.v.valuationSubring.subtype.toAddMonoidHom

/-- The original valuation-ring topology has a basis of actual ideals,
obtained by restricting the original field valuation balls. -/
instance valuationSubring_isLinearTopology :
    IsLinearTopology hv.v.valuationSubring hv.v.valuationSubring := by
  let O := hv.v.valuationSubring
  let E := MonoidWithZeroHom.ValueGroup₀.embedding (f := (hv.v : F →*₀ ℤᵐ⁰))
  have hb := (Valued.hasBasis_nhds_zero F ℤᵐ⁰).comap (fun x : O => (x : F))
  rw [← nhds_subtype_eq_comap] at hb
  have hbi : (𝓝 (0 : O)).HasBasis (fun _ : hv.v.ValueGroup₀ˣ => True)
      (fun γ => (hv.v.ltIdeal (Units.map E γ) : Set O)) := by
    convert hb using 1
    funext γ
    ext x
    exact (Valuation.restrict_lt_iff_lt_embedding hv.v).symm
  exact IsLinearTopology.mk_of_hasBasis O hbi

/-- Completeness is inherited from the actual closed valuation ring. -/
instance valuationSubring_completeSpace [CompleteSpace F] :
    CompleteSpace hv.v.valuationSubring :=
  (Valued.isClosed_valuationSubring F).completeSpace_coe

/-- A normalized original uniformizer is topologically nilpotent in the
inherited valuation-ring topology. -/
theorem hasEval_of_valuation_exp_neg_one (π : hv.v.valuationSubring)
    (hπ : hv.v (π : F) = WithZero.exp (-1 : ℤ)) : PowerSeries.HasEval π := by
  apply (Topology.IsInducing.subtypeVal).tendsto_nhds_iff.mpr
  exact Valued.tendsto_zero_pow_of_le_exp_neg_one hπ.le

/-- In the normalized integer value group, every value strictly below one
is bounded by the value of a normalized uniformizer. -/
theorem intValue_le_exp_neg_one {z : ℤᵐ⁰} (hz : z < 1) : z ≤ exp (-1 : ℤ) := by
  by_cases hzero : z = 0
  · simp [hzero]
  · have hlog : log z < 0 := (log_lt_iff_lt_exp hzero).mpr (by simpa using hz)
    exact (log_le_iff_le_exp hzero).mp (by omega)

/-- A value `exp (-1)` generates the actual maximal ideal of the original
valuation ring. -/
theorem maximalIdeal_eq_span_of_valuation_exp_neg_one (π : hv.v.valuationSubring)
    (hπ : hv.v (π : F) = exp (-1 : ℤ)) :
    IsLocalRing.maximalIdeal hv.v.valuationSubring = Ideal.span {π} := by
  apply le_antisymm
  · intro x hx
    apply Ideal.mem_span_singleton.mpr
    apply (Valuation.valuationSubring.integers hv.v).dvd_iff_le.mpr
    change hv.v (x : F) ≤ hv.v (π : F)
    rw [hπ]
    exact intValue_le_exp_neg_one ((Valuation.mem_maximalIdeal_iff (v := hv.v)).mp hx)
  · apply Ideal.span_le.mpr
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    apply (Valuation.mem_maximalIdeal_iff (v := hv.v)).mpr
    rw [hπ]
    simp

/-- A normalized uniformizer makes the actual integer-valued valuation
nontrivial, so its original valuation ring is a DVR. -/
theorem valuationSubring_isDiscreteValuationRing_of_uniformizer
    (π : hv.v.valuationSubring) (hπ : hv.v (π : F) = exp (-1 : ℤ)) :
    IsDiscreteValuationRing hv.v.valuationSubring := by
  have hv0 : hv.v (π : F) ≠ 0 := by simp [hπ]
  let g : ℤᵐ⁰ˣ := Units.mk0 (hv.v (π : F)) hv0
  have hG : Nontrivial hv.v.valueGroup := by
    rw [Subgroup.nontrivial_iff_exists_ne_one]
    refine ⟨g, ?_, ?_⟩
    · apply MonoidWithZeroHom.mem_valueGroup
      exact ⟨(π : F), rfl⟩
    · intro hg
      have he := congrArg (fun u : ℤᵐ⁰ˣ => (u : ℤᵐ⁰)) hg
      change hv.v (π : F) = 1 at he
      rw [hπ] at he
      simp at he
  exact @Valuation.valuationSubring_isDiscreteValuationRing _ _ _ _ hv.v inferInstance hG

/-- Every normalized original uniformizer is irreducible in its actual DVR. -/
theorem irreducible_of_valuation_exp_neg_one
    [IsDiscreteValuationRing hv.v.valuationSubring] (π : hv.v.valuationSubring)
    (hπ : hv.v (π : F) = exp (-1 : ℤ)) : Irreducible π :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr
    (maximalIdeal_eq_span_of_valuation_exp_neg_one F π hπ)

variable {k : Type*} [Field k] [UniformSpace k] [DiscreteUniformity k]
variable [CompleteSpace F]
variable (c : k →+* hv.v.valuationSubring)
    (e : k ≃+* IsLocalRing.ResidueField hv.v.valuationSubring)
    (hc : ∀ a, IsLocalRing.residue hv.v.valuationSubring (c a) = e a)
variable (π : hv.v.valuationSubring) (hπ : hv.v (π : F) = exp (-1 : ℤ))

/-- Coordinates in the actual inherited valuation ring for every normalized
uniformizer, with precisely the prescribed coefficient section. -/
def valuedPowerSeriesEquiv : PowerSeries k ≃+* hv.v.valuationSubring := by
  letI := valuationSubring_isDiscreteValuationRing_of_uniformizer F π hπ
  exact powerSeriesUniformizerEquiv c e hc π
    (irreducible_of_valuation_exp_neg_one F π hπ)
    (hasEval_of_valuation_exp_neg_one F π hπ)

@[simp]
theorem valuedPowerSeriesEquiv_C (a : k) : valuedPowerSeriesEquiv F c e hc π hπ
    (PowerSeries.C a) = c a := by
  let := valuationSubring_isDiscreteValuationRing_of_uniformizer F π hπ
  exact powerSeriesUniformizerEquiv_C c e hc π _ _ a

@[simp]
theorem valuedPowerSeriesEquiv_X : valuedPowerSeriesEquiv F c e hc π hπ PowerSeries.X = π := by
  let := valuationSubring_isDiscreteValuationRing_of_uniformizer F π hπ
  exact powerSeriesUniformizerEquiv_X c e hc π _ _

/-- The exact original valuation is determined by the first nonzero power
series coefficient; the remaining factor is an actual ring unit. -/
theorem valuation_valuedPowerSeriesEquiv (f : PowerSeries k) (hf : f ≠ 0) :
    hv.v (valuedPowerSeriesEquiv F c e hc π hπ f : F) = exp (-(f.order.toNat : ℤ)) := by
  let φ := valuedPowerSeriesEquiv F c e hc π hπ
  have hu : hv.v (φ (PowerSeries.divXPowOrder f) : F) = 1 :=
    (Valuation.valuationSubring.integers hv.v).one_of_isUnit
      ((PowerSeries.isUnit_divided_by_X_pow_order hf).map φ.toRingHom)
  have heq : φ f = π ^ f.order.toNat * φ (PowerSeries.divXPowOrder f) := by
    conv_lhs => rw [← PowerSeries.X_pow_order_mul_divXPowOrder (f := f)]
    rw [map_mul, map_pow, valuedPowerSeriesEquiv_X]
  change hv.v (φ f : F) = _
  rw [heq]
  change hv.v ((π : F) ^ f.order.toNat * (φ (PowerSeries.divXPowOrder f) : F)) = _
  rw [map_mul, map_pow, hπ, hu, mul_one, ← exp_nsmul]
  congr 1
  simp

/-- Canonical extension of the actual power-series coordinate isomorphism
to the existing Laurent-series field and original field of fractions. -/
def laurentUniformizerEquiv : LaurentSeries k ≃+* F :=
  IsFractionRing.ringEquivOfRingEquiv (valuedPowerSeriesEquiv F c e hc π hπ)

/-- The field map extends the original integral evaluation. -/
theorem laurentUniformizerEquiv_powerSeries (f : PowerSeries k) :
    laurentUniformizerEquiv F c e hc π hπ (algebraMap (PowerSeries k) (LaurentSeries k) f) =
      (valuedPowerSeriesEquiv F c e hc π hπ f : F) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ f

omit [UniformSpace k] [DiscreteUniformity k] in
/-- The standard original Laurent valuation of an integral series is its
first nonzero coefficient order, obtained from its actual unit factor. -/
theorem laurent_valuation_powerSeries_order (f : PowerSeries k) (hf : f ≠ 0) :
    (Valued.v (algebraMap (PowerSeries k) (LaurentSeries k) f) : ℤᵐ⁰) =
      exp (-(f.order.toNat : ℤ)) := by
  let j := algebraMap (PowerSeries k) (LaurentSeries k)
  have hu : (Valued.v (j (PowerSeries.divXPowOrder f)) : ℤᵐ⁰) = 1 :=
    Valuation.Integers.one_of_isUnit' (PowerSeries.isUnit_divided_by_X_pow_order hf)
      (PowerSeries.idealX k).valuation_le_one
  have heq : j f = j PowerSeries.X ^ f.order.toNat * j (PowerSeries.divXPowOrder f) := by
    conv_lhs => rw [← PowerSeries.X_pow_order_mul_divXPowOrder (f := f)]
    rw [map_mul, map_pow]
  rw [heq, map_mul, hu, mul_one]
  exact LaurentSeries.valuation_X_pow k f.order.toNat

/-- The canonical fraction-field extension preserves the actual original
valuations on every Laurent series, including zero and negative orders. -/
theorem valuation_laurentUniformizerEquiv (f : LaurentSeries k) :
    hv.v (laurentUniformizerEquiv F c e hc π hπ f) = Valued.v f := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (PowerSeries k) f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  by_cases ha : a = 0
  · simp [ha]
  · rw [map_div₀, map_div₀, laurentUniformizerEquiv_powerSeries,
      laurentUniformizerEquiv_powerSeries, map_div₀,
      valuation_valuedPowerSeriesEquiv F c e hc π hπ a ha,
      valuation_valuedPowerSeriesEquiv F c e hc π hπ b hb0,
      laurent_valuation_powerSeries_order a ha, laurent_valuation_powerSeries_order b hb0]

/-- Constants remain the original prescribed coefficient embedding in the
actual fraction-field extension. -/
@[simp]
theorem laurentUniformizerEquiv_C (a : k) :
    laurentUniformizerEquiv F c e hc π hπ (algebraMap k (LaurentSeries k) a) = (c a : F) := by
  have heq : algebraMap k (LaurentSeries k) a =
      algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.C a) := by
    rfl
  rw [heq, laurentUniformizerEquiv_powerSeries]
  exact congrArg (fun z : hv.v.valuationSubring => (z : F))
    (valuedPowerSeriesEquiv_C F c e hc π hπ a)

/-- The original Laurent parameter is the chosen original field uniformizer. -/
@[simp]
theorem laurentUniformizerEquiv_X :
    laurentUniformizerEquiv F c e hc π hπ
      (algebraMap (PowerSeries k) (LaurentSeries k) PowerSeries.X) = (π : F) := by
  rw [laurentUniformizerEquiv_powerSeries, valuedPowerSeriesEquiv_X]

/-- The field coordinates preserve the existing original valuation uniformities. -/
theorem uniformContinuous_laurentUniformizerEquiv :
    UniformContinuous (laurentUniformizerEquiv F c e hc π hπ) :=
  valuedRingEquiv_uniformContinuous _ (valuation_laurentUniformizerEquiv F c e hc π hπ)

/-- The inverse map preserves precisely the same original uniformities. -/
theorem uniformContinuous_laurentUniformizerEquiv_symm :
    UniformContinuous (laurentUniformizerEquiv F c e hc π hπ).symm := by
  apply valuedRingEquiv_uniformContinuous
  intro x
  exact (valuation_laurentUniformizerEquiv F c e hc π hπ
    ((laurentUniformizerEquiv F c e hc π hπ).symm x)).symm.trans
      (congrArg hv.v ((laurentUniformizerEquiv F c e hc π hπ).apply_symm_apply x))

/-- The Laurent coordinates and their inverse are continuous for the
original valuation topologies. -/
theorem continuous_laurentUniformizerEquiv :
    Continuous (laurentUniformizerEquiv F c e hc π hπ) :=
  (uniformContinuous_laurentUniformizerEquiv F c e hc π hπ).continuous

/-- Continuity of the actual inverse coordinate expansion. -/
theorem continuous_laurentUniformizerEquiv_symm :
    Continuous (laurentUniformizerEquiv F c e hc π hπ).symm :=
  (uniformContinuous_laurentUniformizerEquiv_symm F c e hc π hπ).continuous

/-- The extension is uniquely determined by its values on the actual
integral power-series subring. -/
theorem laurentUniformizerEquiv_unique_of_powerSeries (f : LaurentSeries k →+* F)
    (hf : ∀ A : PowerSeries k,
      f (algebraMap (PowerSeries k) (LaurentSeries k) A) =
        (valuedPowerSeriesEquiv F c e hc π hπ A : F)) :
    f = (laurentUniformizerEquiv F c e hc π hπ).toRingHom := by
  apply IsFractionRing.ringHom_ext (A := PowerSeries k)
  intro A
  exact (hf A).trans (laurentUniformizerEquiv_powerSeries F c e hc π hπ A).symm

/-- Among continuous field maps, constants and the Laurent parameter
uniquely determine the actual coordinate map. -/
theorem laurentUniformizerEquiv_unique (f : LaurentSeries k →+* F) (hf : Continuous f)
    (hC : ∀ a, f (algebraMap k (LaurentSeries k) a) = (c a : F))
    (hX : f (algebraMap (PowerSeries k) (LaurentSeries k) PowerSeries.X) = (π : F)) :
    f = (laurentUniformizerEquiv F c e hc π hπ).toRingHom := by
  let j := algebraMap (RatFunc k) (LaurentSeries k)
  let g := laurentUniformizerEquiv F c e hc π hπ
  have hp : (f.comp j).comp (algebraMap (Polynomial k) (RatFunc k)) =
      (g.toRingHom.comp j).comp (algebraMap (Polynomial k) (RatFunc k)) := by
    apply Polynomial.ringHom_ext
    · intro a
      change f (j (algebraMap (Polynomial k) (RatFunc k) (Polynomial.C a))) =
        g (j (algebraMap (Polynomial k) (RatFunc k) (Polynomial.C a)))
      dsimp only [j]
      rw [← IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) (LaurentSeries k)]
      rw [Polynomial.algebraMap_hahnSeries_apply, Polynomial.coe_C,
        HahnSeries.ofPowerSeries_C, ← LaurentSeries.algebraMap_apply]
      exact (hC a).trans (laurentUniformizerEquiv_C F c e hc π hπ a).symm
    · change f (j (algebraMap (Polynomial k) (RatFunc k) Polynomial.X)) =
        g (j (algebraMap (Polynomial k) (RatFunc k) Polynomial.X))
      dsimp only [j]
      rw [← IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) (LaurentSeries k)]
      rw [Polynomial.algebraMap_hahnSeries_apply, Polynomial.coe_X]
      exact hX.trans (laurentUniformizerEquiv_X F c e hc π hπ).symm
  have hrat : f.comp j = g.toRingHom.comp j :=
    IsFractionRing.ringHom_ext (A := Polynomial k) (fun a => DFunLike.congr_fun hp a)
  have heq : (f : LaurentSeries k → F) = g :=
    (LaurentSeries.coe_range_dense (K := k)).equalizer hf
      (continuous_laurentUniformizerEquiv F c e hc π hπ)
      (funext fun a => DFunLike.congr_fun hrat a)
  exact RingHom.ext (congrFun heq)

end OriginalValuationRing

end FontaineWintenberger
