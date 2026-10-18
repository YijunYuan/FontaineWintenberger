/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.ApproximateRoots
public import FontaineWintenberger.FieldOfNorms.Completeness
public import FontaineWintenberger.LocalField.SeparableRootExtraction
public import Mathlib.RingTheory.Polynomial.ScaleRoots

/-!
# The original relative field of norms is a separable closure

Actual finite-coordinate approximations and discriminant root extraction
supply roots in the same canonical directed union of original norm fields.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

open Polynomial

section FiniteValuation

variable (K L M : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
    [Field L] [Field M] [Algebra K L] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M] [Algebra.IsSeparable K L] [Algebra.IsSeparable K M]
    [Module.Finite L M]

local notation "p" => residueChar K

variable [IsAPF K L] [IsAPF K M]
    [Fact (¬ Module.Finite K L)] [Fact (¬ Module.Finite K M)]

/-- Positive actual finite-map scaling makes the original target valuation
an extension of the original source valuation, on their same field map. -/
theorem FieldOfNorms.finiteFieldValuation_hasExtension :
    letI : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
    letI := (FieldOfNorms.finiteRingHom K L M).toAlgebra
    (FieldOfNorms.fieldValuation K L).HasExtension
      (FieldOfNorms.fieldValuation K M) := by
  let : Algebra.IsSeparable L M := Algebra.isSeparable_tower_top_of_isSeparable K L M
  let := (FieldOfNorms.finiteRingHom K L M).toAlgebra
  obtain ⟨e, he, hv⟩ := exists_finiteFieldOfNormsMap_valuation_scaling K L M
  constructor
  intro x y
  change FieldOfNorms.valuation K L x ≤ FieldOfNorms.valuation K L y ↔
    FieldOfNorms.valuation K M (FieldOfNorms.finiteMap K L M x) ≤
      FieldOfNorms.valuation K M (FieldOfNorms.finiteMap K L M y)
  rw [hv, hv]
  exact (pow_le_pow_iff_left₀ zero_le zero_le he.ne').symm

end FiniteValuation

section IntegralRoots

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
    (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]
    {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    [Algebra L Ω] [IsScalarTower K L Ω]

local notation "p" => residueChar K

variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

local notation "Oₓ" => Valuation.valuationSubring
  (FieldOfNorms.fieldValuation K L)

/-- A monic integral separable polynomial has an exact root in an actual
finite original norm field in the prescribed common separable closure.
All approximation and valuation-extension hypotheses of Newton--Krasner
extraction are produced on the actual original fields. -/
theorem exists_finite_fieldOfNorms_exact_root :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    ∀ f : Oₓ[X], f.Monic → (f.map (algebraMap Oₓ (FieldOfNorms K L))).Separable →
      0 < f.natDegree →
      ∃ N : FiniteIntermediateField L Ω, Module.finrank L N.val ≤ f.natDegree ∧
        letI := (FieldOfNorms.finiteRingHom K L N.val).toAlgebra
        ∃ a : FieldOfNorms K N.val, aeval a (f.map (algebraMap Oₓ (FieldOfNorms K L))) = 0 := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  intro f hf hsep hdegree
  obtain ⟨d, hd⟩ := exists_fieldOfNorms_discr_precision K L f hf hsep
  let r := 2 * f.natDegree * d + 1
  obtain ⟨N, hdegreeN, hz⟩ := exists_fieldOfNorms_approximate_root_at_precision
    K L (Ω := Ω) r f hf hsep hdegree
  let φ := FieldOfNorms.finiteRingHom K L N.val
  let : Algebra (FieldOfNorms K L) (FieldOfNorms K N.val) := φ.toAlgebra
  let : Algebra Oₓ (FieldOfNorms K N.val) := (φ.comp (Oₓ).subtype).toAlgebra
  let : IsScalarTower Oₓ (FieldOfNorms K L) (FieldOfNorms K N.val) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let ρ := FieldOfNorms.finiteIntegralRingHom K L N.val
  obtain ⟨z, hz⟩ := hz
  obtain ⟨e, he, hedegree, hv⟩ := exists_finiteFieldOfNormsMap_valuation_scaling_le_finrank
    K L N.val
  have hek : e ≤ f.natDegree := hedegree.trans hdegreeN
  let w := FieldOfNorms.fieldValuation K N.val
  have heval : (((f.map ρ).eval z : w.valuationSubring) : FieldOfNorms K N.val) = aeval z.val f :=
      by
    change (algebraMap w.valuationSubring (FieldOfNorms K N.val)) ((f.map ρ).eval z) = _
    rw [← Polynomial.eval₂_at_apply, Polynomial.eval₂_map, aeval_def]
    rfl
  have hres : w (aeval z.val f) ≤ WithZero.exp (-(r : ℤ)) := by
    rw [← heval]
    exact hz
  have hdelta : WithZero.exp (-((d : ℤ) * (e * 2 : ℕ))) <
      w (algebraMap (FieldOfNorms K L) (FieldOfNorms K N.val) (f.discr : FieldOfNorms K L)) ^ 2 :=
          by
    change _ < FieldOfNorms.valuation K N.val (FieldOfNorms.finiteMap K L N.val _) ^ 2
    rw [hv, ← pow_mul]
    have h := pow_lt_pow_left₀ hd zero_le (by omega : e * 2 ≠ 0)
    rw [← WithZero.exp_nsmul] at h
    simpa only [nsmul_eq_mul, mul_neg, neg_mul, mul_comm] using h
  have hcut : WithZero.exp (-(r : ℤ)) < WithZero.exp (-((d : ℤ) * (e * 2 : ℕ))) := by
    apply WithZero.exp_lt_exp.mpr
    have hmul : e * d ≤ f.natDegree * d := Nat.mul_le_mul_right d hek
    dsimp only [r]
    push_cast
    have hmul' : (e : ℤ) * d ≤ (f.natDegree : ℤ) * d := by exact_mod_cast hmul
    nlinarith
  obtain ⟨hfinite, hseparable, _⟩ := FieldOfNorms.finite_finite_separable_degree
    K L N.val
  let : Module.Finite (FieldOfNorms K L) (FieldOfNorms K N.val) := hfinite
  let : Algebra.IsSeparable (FieldOfNorms K L) (FieldOfNorms K N.val) := hseparable
  let : (FieldOfNorms.fieldValuation K L).HasExtension w :=
    FieldOfNorms.finiteFieldValuation_hasExtension K L N.val
  obtain ⟨a, ha, _, _, _⟩ := discreteValued_exists_root_mem_adjoin_of_discr
    (FieldOfNorms K L) (WithZero (Multiplicative ℤ)) (FieldOfNorms K N.val) w
      f hf hdegree z.val z.property (hres.trans_lt (hcut.trans hdelta))
  refine ⟨N, hdegreeN, a, ?_⟩
  rwa [aeval_map_algebraMap]

end IntegralRoots

section PolynomialScaling

variable {F : Type*} [Field F]

/-- Scaling by a nonzero element preserves separability, by the injective
scaling of the actual root multiset in the separable closure. -/
theorem separable_scaleRoots_of_monic (f : F[X]) (hf : f.Monic) (hsep : f.Separable)
    (s : F) (hs : s ≠ 0) : (f.scaleRoots s).Separable := by
  let S := SeparableClosure F
  let i := algebraMap F S
  have hs' : i s ≠ 0 := (map_ne_zero i).mpr hs
  apply (separable_map i).mp
  rw [map_scaleRoots f s i (by rw [hf.leadingCoeff, map_one]; exact one_ne_zero)]
  have hsplit := (IsSepClosed.splits_codomain (f := i) f hsep).scaleRoots (i s)
  apply (nodup_roots_iff_of_splits
    ((monic_scaleRoots_iff (i s)).mpr (hf.map i)).ne_zero hsplit).mp
  rw [roots_scaleRoots _ (isUnit_iff_ne_zero.mpr hs')]
  exact (Polynomial.nodup_roots (p := f.map i) hsep.map).map (mul_right_injective₀ hs')

/-- A positive power of the supplied normalized uniformizer scales every
coefficient of a monic polynomial into the same actual valuation ring. -/
theorem exists_integral_scaleRoots_of_uniformizer
    (v : Valuation F (WithZero (Multiplicative ℤ))) (π : F)
    (hπ : v π = WithZero.exp (-1 : ℤ)) (f : F[X]) (hf : f.Monic) :
    ∃ s : F, s ≠ 0 ∧ ∃ m : ℕ, 0 < m ∧ s = π ^ m ∧
      ∀ i : ℕ, v ((f.scaleRoots s).coeff i) ≤ 1 := by
  classical
  let m := f.support.sup (fun i => (WithZero.log (v (f.coeff i))).toNat)
  have hπ0 : π ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hc (i : ℕ) : v (f.coeff i) ≤ WithZero.exp (m : ℤ) := by
    by_cases hi : f.coeff i = 0
    · simp only [hi, map_zero, zero_le]
    · apply WithZero.le_exp_of_log_le
      have hsup : (WithZero.log (v (f.coeff i))).toNat ≤ m :=
        Finset.le_sup (f := fun i => (WithZero.log (v (f.coeff i))).toNat)
          (Polynomial.mem_support_iff.mpr hi)
      have hself : WithZero.log (v (f.coeff i)) ≤
          ((WithZero.log (v (f.coeff i))).toNat : ℤ) := Int.self_le_toNat _
      exact hself.trans (by exact_mod_cast hsup)
  refine ⟨π ^ (m + 1), pow_ne_zero _ hπ0, m + 1, by omega, rfl, ?_⟩
  intro i
  rw [coeff_scaleRoots]
  rcases lt_trichotomy i f.natDegree with hi | hi | hi
  · have hdiff : 1 ≤ f.natDegree - i := by omega
    rw [map_mul, map_pow, map_pow, hπ, ← WithZero.exp_nsmul, ← WithZero.exp_nsmul]
    have hsmall : WithZero.exp ((f.natDegree - i) • ((m + 1) • (-1 : ℤ))) ≤
        WithZero.exp (-(m : ℤ)) := by
      apply WithZero.exp_le_exp.mpr
      simp only [nsmul_eq_mul]
      have hdiff' : (1 : ℤ) ≤ ((f.natDegree - i : ℕ) : ℤ) := by exact_mod_cast hdiff
      have hm : (0 : ℤ) ≤ m := by positivity
      push_cast
      nlinarith
    calc
      _ ≤ WithZero.exp (m : ℤ) * WithZero.exp (-(m : ℤ)) := mul_le_mul' (hc i) hsmall
      _ = 1 := by rw [← WithZero.exp_add]; simp
  · subst i
    simp only [hf.coeff_natDegree, tsub_self, pow_zero, mul_one, map_one, le_refl]
  · simp only [coeff_eq_zero_of_natDegree_lt hi, zero_mul, map_zero, zero_le]

/-- A genuine root of the scaled polynomial gives a genuine root of the
original polynomial after division by the same nonzero scalar. -/
theorem aeval_div_eq_zero_of_scaleRoots {E : Type*} [Field E] [Algebra F E]
    (f : F[X]) {s : F} (hs : s ≠ 0) (a : E)
    (ha : aeval a (f.scaleRoots s) = 0) :
    aeval (a / algebraMap F E s) f = 0 := by
  have ht : algebraMap F E s ≠ 0 := (_root_.map_ne_zero _).mpr hs
  have hcancel : algebraMap F E s * (a / algebraMap F E s) = a := by field_simp
  have hscale := scaleRoots_eval₂_mul (p := f) (algebraMap F E)
    (a / algebraMap F E s) s
  rw [hcancel] at hscale
  exact (mul_eq_zero.mp (hscale.symm.trans ha)).resolve_left (pow_ne_zero _ ht)

end PolynomialScaling

section MonicRoots

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
    (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]
    {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    [Algebra L Ω] [IsScalarTower K L Ω]

local notation "p" => residueChar K

variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

local notation "Oₓ" => Valuation.valuationSubring
  (FieldOfNorms.fieldValuation K L)

/-- Positive actual uniformizer scaling reduces every monic separable
polynomial to the proved integral case, then divides its genuine root by
the same nonzero scalar in the same original finite norm field. -/
theorem exists_finite_fieldOfNorms_root_of_monic :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    ∀ f : (FieldOfNorms K L)[X], f.Monic → f.Separable → 0 < f.natDegree →
      ∃ N : FiniteIntermediateField L Ω, Module.finrank L N.val ≤ f.natDegree ∧
        letI := (FieldOfNorms.finiteRingHom K L N.val).toAlgebra
        ∃ a : FieldOfNorms K N.val, aeval a f = 0 := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  intro f hf hsep hdegree
  let π := FieldOfNorms.uniformizer K L
  obtain ⟨s, hs, m, _, _, hcoeff⟩ := exists_integral_scaleRoots_of_uniformizer
    (FieldOfNorms.fieldValuation K L) π
      (FieldOfNorms.valuation_fieldOfNormsUniformizer K L) f hf
  have hsub : algebraMap Oₓ (FieldOfNorms K L) = (Oₓ).subtype := by
    rfl
  have hlifts : f.scaleRoots s ∈ Polynomial.lifts (algebraMap Oₓ (FieldOfNorms K L)) :=
    (Polynomial.lifts_iff_coeff_lifts _).mpr (fun i =>
      ⟨⟨_, hcoeff i⟩, rfl⟩)
  obtain ⟨g, hgmap⟩ := (Polynomial.mem_lifts _).mp hlifts
  have hg : g.Monic := Polynomial.monic_of_injective
    (Oₓ).subtype_injective (by rw [← hsub, hgmap]; exact (monic_scaleRoots_iff s).mpr hf)
  have hgdegree : g.natDegree = f.natDegree := by
    rw [← hg.natDegree_map (algebraMap Oₓ (FieldOfNorms K L)), hgmap, natDegree_scaleRoots]
  have hgsep : (g.map (algebraMap Oₓ (FieldOfNorms K L))).Separable := by
    rw [hgmap]
    exact separable_scaleRoots_of_monic f hf hsep s hs
  obtain ⟨N, hdegreeN, ha⟩ := exists_finite_fieldOfNorms_exact_root
    K L (Ω := Ω) g hg hgsep (by rwa [hgdegree])
  let := (FieldOfNorms.finiteRingHom K L N.val).toAlgebra
  obtain ⟨a, ha⟩ := ha
  rw [hgmap] at ha
  refine ⟨N, hdegreeN.trans_eq hgdegree, a / algebraMap (FieldOfNorms K L) (FieldOfNorms K N.val)
      s, ?_⟩
  exact aeval_div_eq_zero_of_scaleRoots f hs a ha

end MonicRoots

section UnionRoots

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
    (L Ω : Type*) [Field L] [Field Ω] [Algebra K L] [Algebra.IsSeparable K L]
    [Algebra K Ω] [IsSepClosure K Ω] [Algebra L Ω] [IsScalarTower K L Ω]

local notation "p" => residueChar K

variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

local notation "U" => RelFieldOfNorms K L Ω

/-- Every nonconstant monic separable polynomial over the same canonical
relative field of norms has an actual root there. Its actual finite coefficients
are descended, the produced finite original root stage is retained, and
original finite-map composition gives the literal union inclusion square. -/
theorem RelFieldOfNorms._exists_root_of_monic :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    ∀ F : U[X], F.Monic → F.Separable → 0 < F.natDegree → ∃ a : U, F.eval a = 0 := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  intro F hF hsep hdegree
  obtain ⟨N, f, hfmap⟩ := RelFieldOfNorms._exists_polynomial K L Ω F
  let : IsScalarTower K N.val Ω := IsScalarTower.to₁₃₄ K L N.val Ω
  let i := RelFieldOfNorms.of K L Ω N
  have hf : f.Monic := Polynomial.monic_of_injective i.injective (by rwa [hfmap])
  have hfsep : f.Separable := (separable_map i).mp (by rwa [hfmap])
  have hfdegree : 0 < f.natDegree := by
    rw [← hf.natDegree_map i, hfmap]
    exact hdegree
  obtain ⟨Q, _, ha⟩ := exists_finite_fieldOfNorms_root_of_monic
    K N.val (Ω := Ω) f hf hfsep hfdegree
  let : IsScalarTower L N.val Q.val := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K N.val Q.val := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K L Q.val := IsScalarTower.to₁₂₄ K L N.val Q.val
  have hfinite : Module.Finite L Q.val := Module.Finite.trans N.val Q.val
  let R : FiniteIntermediateField L Ω := ⟨Q.val.restrictScalars L, hfinite⟩
  have hNR : N ≤ R := by
    intro x hx
    exact Q.val.algebraMap_mem ⟨x, hx⟩
  let : Algebra.IsSeparable K Q.val := Algebra.IsSeparable.trans K N.val Q.val
  let originalAlgebras := ((inferInstance : Algebra K Q.val), (inferInstance : Algebra N.val Q.val))
  have originalTower : IsScalarTower K N.val Q.val := inferInstance
  have originalFinite : Module.Finite N.val Q.val := inferInstance
  have originalSeparable : Algebra.IsSeparable N.val Q.val := inferInstance
  let φ := FieldOfNorms.finiteRingHom K N.val Q.val
  let := φ.toAlgebra
  obtain ⟨a, ha⟩ := ha
  let : Module.Finite L R.val := R.property
  let e : Q.val ≃ₐ[K] R.val :=
    { RingEquiv.refl Q.val with
      commutes' x := by
        apply Subtype.ext
        rfl }
  let eX := FieldOfNorms.ringEquiv K e
  let j := (RelFieldOfNorms.of K L Ω R).comp eX.toRingHom
  let : Algebra N.val R.val := (IntermediateField.inclusion hNR).toRingHom.toAlgebra
  let : IsScalarTower K N.val R.val := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower L N.val R.val := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite N.val R.val := Module.Finite.right L N.val R.val
  let : Algebra.IsSeparable N.val R.val :=
    Algebra.isSeparable_tower_top_of_isSeparable L N.val R.val
  have hcomm : j.comp φ = i := by
    apply RingHom.ext
    intro x
    have hn := @FieldOfNorms.finiteMap_naturality K N.val Q.val _ _ _ _ originalAlgebras.1
      N.val R.val _ _ _ _ originalAlgebras.2 (inferInstance : Algebra N.val R.val)
      originalTower (inferInstance : IsScalarTower K N.val R.val)
      _ _ originalFinite _ originalSeparable _
      (AlgEquiv.refl : N.val ≃ₐ[K] N.val) e (fun _ => rfl) x
    have hv : FieldOfNorms.map e (φ x) =
        RelFieldOfNorms.transition K L Ω N R hNR x := by
      simpa only [FieldOfNorms.map_refl, φ, RelFieldOfNorms.transition,
        FieldOfNorms.finiteRingHom_apply] using hn
    change RelFieldOfNorms.of K L Ω R
      (FieldOfNorms.map e (φ x)) = i x
    rw [hv]
    exact RelFieldOfNorms.of_transition K L Ω N R hNR x
  have hroot := congrArg j ha
  change j (Polynomial.eval₂ (algebraMap (FieldOfNorms K N.val) (FieldOfNorms K Q.val)) a f) =
    j 0 at hroot
  rw [map_zero, Polynomial.hom_eval₂] at hroot
  change f.eval₂ (j.comp φ) (j a) = 0 at hroot
  rw [hcomm] at hroot
  refine ⟨j a, ?_⟩
  rw [← hfmap, Polynomial.eval_map]
  exact hroot

/-- The actual relative field of norms is separably closed, by the proved original
root construction and Mathlib's monic irreducible root criterion. -/
theorem RelFieldOfNorms._isSepClosed :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    IsSepClosed U := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  apply IsSepClosed.of_exists_root
  intro F hF hirr hsep
  exact RelFieldOfNorms._exists_root_of_monic K L Ω
    F hF hsep hirr.natDegree_pos

/-- The same relative field of norms, with its original base algebra, is a genuine
separable closure of the original norm field. -/
theorem RelFieldOfNorms._isSepClosure :
    letI : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
    IsSepClosure (FieldOfNorms K L) U := by
  let : Algebra.IsSeparable L Ω := Algebra.isSeparable_tower_top_of_isSeparable K L Ω
  let : IsSepClosed U := RelFieldOfNorms._isSepClosed K L Ω
  let : Algebra.IsSeparable (FieldOfNorms K L) U :=
    RelFieldOfNorms._isSeparable K L Ω
  exact isSepClosure_iff.mpr ⟨inferInstance, inferInstance⟩

end UnionRoots

end FontaineWintenberger
