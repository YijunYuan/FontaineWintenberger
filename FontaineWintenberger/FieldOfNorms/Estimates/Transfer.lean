/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.APF.BaseChange.EmbeddingFiniteBase
public import FontaineWintenberger.Ramification.Embedding.Valued
public import FontaineWintenberger.FieldOfNorms.Functor.Galois
public import FontaineWintenberger.FieldOfNorms.Basic.Ring
public import FontaineWintenberger.FieldOfNorms.Estimates.Herbrand
public import FontaineWintenberger.APF.Tower.Stages

/-!
# Ramification transfer on the norm field

Finite embedding comparisons retain their valuation rings and finite
ambient fields, including fields not stable under the automorphism.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

open scoped ENNReal

section Action

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]

local notation "p" => residueChar K
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L]

/-- The norm-field automorphism restricts to its
valuation ring, using its proved preservation of the same stable valuation. -/
def FieldOfNorms.integerAut [IsAPF K L] [Fact (¬ Module.Finite K L)]
    (σ : L ≃ₐ[K] L) :
    (FieldOfNorms.fieldValuation K L).valuationSubring ≃+*
      (FieldOfNorms.fieldValuation K L).valuationSubring := by
  let g := FieldOfNorms.aut K L σ
  have hv (x : FieldOfNorms K L) :
      FieldOfNorms.valuation K L (g x) = FieldOfNorms.valuation K L x :=
    FieldOfNorms.aut_valuation K σ x
  have hvi (x : FieldOfNorms K L) :
      FieldOfNorms.valuation K L (g.symm x) = FieldOfNorms.valuation K L x := by
    have h := hv (g.symm x)
    simpa only [RingEquiv.apply_symm_apply] using h.symm
  exact {
    toFun := fun x => ⟨g x, by change FieldOfNorms.valuation K L (g x) ≤ 1; rw [hv]; exact x.2⟩
    invFun := fun x => ⟨g.symm x, by
      change FieldOfNorms.valuation K L (g.symm x) ≤ 1
      rw [hvi]
      exact x.2⟩
    left_inv := fun x => Subtype.ext (g.symm_apply_apply x)
    right_inv := fun x => Subtype.ext (g.apply_symm_apply x)
    map_mul' := fun x y => Subtype.ext (g.map_mul x y)
    map_add' := fun x y => Subtype.ext (g.map_add x y) }

@[simp]
theorem FieldOfNorms.coe_integerAut [IsAPF K L] [Fact (¬ Module.Finite K L)]
    (σ : L ≃ₐ[K] L) :
    ∀ x : (FieldOfNorms.fieldValuation K L).valuationSubring,
      (FieldOfNorms.integerAut K L σ x : FieldOfNorms K L) =
        FieldOfNorms.aut K L σ x := by
  intro x
  rfl

/-- The signed intrinsic ramification number of the action,
with infinity retained in the standard extended reals. -/
def FieldOfNorms.ramificationNumber [IsAPF K L] [Fact (¬ Module.Finite K L)]
    (σ : L ≃ₐ[K] L) : EReal := by
  let O := (FieldOfNorms.fieldValuation K L).valuationSubring
  exact ((ramificationOrder (R := O) (O ≃+* O)
    (FieldOfNorms.integerAut K L σ) : ℝ≥0∞) : EReal) - 1

/-- Restricting the action agrees with the general
valuation-preserving restriction on the valuation ring. -/
theorem FieldOfNorms.integerAut_eq_valuationIntegerAut [IsAPF K L]
    [Fact (¬ Module.Finite K L)] (σ : L ≃ₐ[K] L) :
    FieldOfNorms.integerAut K L σ =
      valuationIntegerAut (FieldOfNorms.fieldValuation K L)
        (FieldOfNorms.aut K L σ)
        (FieldOfNorms.aut_valuation K σ) := by
  apply RingEquiv.ext
  intro x
  rfl

/-- The generic intrinsic number specializes to the existing
norm-field number, with the same field, valuation and automorphism. -/
theorem FieldOfNorms.ramificationNumber_eq_valuedRamificationNumber [IsAPF K L]
    [Fact (¬ Module.Finite K L)] (σ : L ≃ₐ[K] L) :
    FieldOfNorms.ramificationNumber K L σ =
      valuedRamificationNumber (FieldOfNorms.fieldValuation K L)
        (FieldOfNorms.aut K L σ)
        (FieldOfNorms.aut_valuation K σ) := by
  change integerRamificationNumber (FieldOfNorms.integerAut K L σ) = _
  rw [FieldOfNorms.integerAut_eq_valuationIntegerAut]
  rfl

/-- Restriction to the valuation ring retains the proved
faithfulness of the norm-field action. -/
theorem FieldOfNorms.integerAut_eq_one_iff [IsAPF K L]
    [Fact (¬ Module.Finite K L)] (σ : L ≃ₐ[K] L) :
    FieldOfNorms.integerAut K L σ = 1 ↔ σ = 1 := by
  let O := (FieldOfNorms.fieldValuation K L).valuationSubring
  constructor
  · intro hg
    apply (FieldOfNorms.aut_injective K L)
    rw [_root_.map_one]
    apply RingEquiv.toRingHom_injective
    apply IsFractionRing.ringHom_ext (A := O)
    intro a
    exact congrArg (fun z : O => (z : FieldOfNorms K L))
      (congrArg (fun f : O ≃+* O => f a) hg)
  · rintro rfl
    apply RingEquiv.ext
    intro a
    apply Subtype.ext
    change FieldOfNorms.aut K L 1 (a : FieldOfNorms K L) = a
    rw [_root_.map_one]
    rfl

theorem FieldOfNorms.neg_one_le_ramificationNumber [IsAPF K L]
    [Fact (¬ Module.Finite K L)] (σ : L ≃ₐ[K] L) :
    -1 ≤ FieldOfNorms.ramificationNumber K L σ := by
  unfold FieldOfNorms.ramificationNumber
  simpa only [zero_sub] using
    EReal.sub_le_sub (EReal.coe_ennreal_nonneg _)
      (show (1 : EReal) ≤ 1 from le_rfl)

/-- Infinity occurs precisely at the identity automorphism. -/
theorem FieldOfNorms.ramificationNumber_eq_top_iff [IsAPF K L]
    [Fact (¬ Module.Finite K L)] (σ : L ≃ₐ[K] L) :
    FieldOfNorms.ramificationNumber K L σ = ⊤ ↔ σ = 1 := by
  let O := (FieldOfNorms.fieldValuation K L).valuationSubring
  change ((ramificationOrder (R := O) (O ≃+* O)
    (FieldOfNorms.integerAut K L σ) : ℝ≥0∞) : EReal) - 1 = ⊤ ↔ _
  rw [sub_eq_add_neg, ← EReal.coe_one, ← EReal.coe_neg,
    EReal.add_eq_top_iff_eq_top_left (EReal.coe_ne_bot (-1)) (EReal.coe_ne_top (-1)),
    EReal.coe_ennreal_eq_top_iff, ENat.toENNReal_eq_top,
    ramificationOrder_eq_top_iff, FieldOfNorms.integerAut_eq_one_iff]

@[simp]
theorem FieldOfNorms.ramificationNumber_one [IsAPF K L]
    [Fact (¬ Module.Finite K L)] :
    FieldOfNorms.ramificationNumber K L 1 = ⊤ :=
  (FieldOfNorms.ramificationNumber_eq_top_iff K L 1).mpr rfl

/-- Every nonidentity automorphism has a finite real
ramification number; no stabilizing finite-layer order is assumed. -/
theorem FieldOfNorms.ramificationNumber_exists_real [IsAPF K L]
    [Fact (¬ Module.Finite K L)] {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) :
    ∃ r : ℝ, FieldOfNorms.ramificationNumber K L σ = r := by
  have ht : FieldOfNorms.ramificationNumber K L σ ≠ ⊤ :=
    fun ht => hσ ((FieldOfNorms.ramificationNumber_eq_top_iff K L σ).mp ht)
  have hb : FieldOfNorms.ramificationNumber K L σ ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot (-1))
      (FieldOfNorms.neg_one_le_ramificationNumber K L σ)
  exact ⟨_, (EReal.coe_toReal ht hb).symm⟩

/-- The canonical residue automorphism induced by the action
on its valuation ring. -/
def FieldOfNorms.residueAut [IsAPF K L] [Fact (¬ Module.Finite K L)]
    (σ : L ≃ₐ[K] L) :
    IsLocalRing.ResidueField (FieldOfNorms.fieldValuation K L).valuationSubring ≃+*
      IsLocalRing.ResidueField (FieldOfNorms.fieldValuation K L).valuationSubring := by
  exact IsLocalRing.ResidueField.mapEquiv (FieldOfNorms.integerAut K L σ)

@[simp]
theorem FieldOfNorms.residueAut_residue [IsAPF K L] [Fact (¬ Module.Finite K L)]
    (σ : L ≃ₐ[K] L) :
    ∀ a : (FieldOfNorms.fieldValuation K L).valuationSubring,
      FieldOfNorms.residueAut K L σ (IsLocalRing.residue _ a) =
        IsLocalRing.residue _ (FieldOfNorms.integerAut K L σ a) := by
  intro a
  rfl

/-- Triviality of the residue action is precisely congruence of all
integral elements modulo the maximal ideal. -/
theorem FieldOfNorms.residueAut_eq_refl_iff [IsAPF K L]
    [Fact (¬ Module.Finite K L)] (σ : L ≃ₐ[K] L) :
    FieldOfNorms.residueAut K L σ = RingEquiv.refl _ ↔
      ∀ a : (FieldOfNorms.fieldValuation K L).valuationSubring,
        FieldOfNorms.integerAut K L σ a - a ∈ IsLocalRing.maximalIdeal _ := by
  let O := (FieldOfNorms.fieldValuation K L).valuationSubring
  constructor
  · intro h a
    have ha := congrArg (fun e => e (IsLocalRing.residue O a)) h
    exact Ideal.Quotient.eq.mp ha
  · intro h
    apply RingEquiv.ext
    intro a
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective (R := O) a
    exact Ideal.Quotient.eq.mpr (h b)

/-- For an inertial action, every uniformizer computes its
intrinsic ramification number; this includes the identity and infinity. -/
theorem FieldOfNorms.ramificationNumber_eq_uniformizer [IsAPF K L]
    [Fact (¬ Module.Finite K L)] (σ : L ≃ₐ[K] L) :
    ∀ (_hres : FieldOfNorms.residueAut K L σ = RingEquiv.refl _)
      (π : (FieldOfNorms.fieldValuation K L).valuationSubring),
      Irreducible π → FieldOfNorms.ramificationNumber K L σ =
        (((IsDiscreteValuationRing.addVal _
          (FieldOfNorms.integerAut K L σ π - π) : ℝ≥0∞) : EReal) - 1) := by
  let O := (FieldOfNorms.fieldValuation K L).valuationSubring
  let : CharP O p :=
    (algebraMap O (FieldOfNorms K L)).charP Subtype.val_injective p
  let : CharP (IsLocalRing.ResidueField O) p :=
    CharP.of_ringHom_of_ne_zero (IsLocalRing.residue O) p (Fact.out : Nat.Prime p).ne_zero
  intro hres π hπ
  exact integerRamificationNumber_eq_uniformizer p
    (FieldOfNorms.integerAut K L σ) hres hπ

/-- The general valued-field uniformizer ratio computes the existing
intrinsic norm-field number on its same field. -/
theorem FieldOfNorms.ramificationNumber_eq_uniformizer_ratio [IsAPF K L]
    [Fact (¬ Module.Finite K L)] (σ : L ≃ₐ[K] L) :
    ∀ (_hres : FieldOfNorms.residueAut K L σ = RingEquiv.refl _)
      (π : (FieldOfNorms.fieldValuation K L).valuationSubring),
      Irreducible π → FieldOfNorms.ramificationNumber K L σ =
        normalizedAdditiveValue
          (FieldOfNorms.fieldValuation K L).valuationSubring
          (FieldOfNorms.aut K L σ (π : FieldOfNorms K L) /
            (π : FieldOfNorms K L) - 1) := by
  let O := (FieldOfNorms.fieldValuation K L).valuationSubring
  let : CharP O p :=
    (algebraMap O (FieldOfNorms K L)).charP Subtype.val_injective p
  let : CharP (IsLocalRing.ResidueField O) p :=
    CharP.of_ringHom_of_ne_zero (IsLocalRing.residue O) p (Fact.out : Nat.Prime p).ne_zero
  intro hres π hπ
  change IsLocalRing.ResidueField.mapEquiv (FieldOfNorms.integerAut K L σ) =
    RingEquiv.refl _ at hres
  rw [FieldOfNorms.integerAut_eq_valuationIntegerAut] at hres
  rw [FieldOfNorms.ramificationNumber_eq_valuedRamificationNumber]
  exact valuedRamificationNumber_eq_uniformizer_ratio
    (FieldOfNorms.fieldValuation K L)
    (FieldOfNorms.aut K L σ) (FieldOfNorms.aut_valuation K σ)
    p hres hπ

/-- Noninertia is detected on the residue field and has signed
ramification number minus one. -/
theorem FieldOfNorms.ramificationNumber_eq_neg_one_of_residue_ne [IsAPF K L]
    [Fact (¬ Module.Finite K L)] (σ : L ≃ₐ[K] L) :
    FieldOfNorms.residueAut K L σ ≠ RingEquiv.refl _ →
      FieldOfNorms.ramificationNumber K L σ = -1 := by
  let O := (FieldOfNorms.fieldValuation K L).valuationSubring
  let g := FieldOfNorms.integerAut K L σ
  intro hres
  have hzero : ramificationOrder (R := O) (O ≃+* O) g = 0 := by
    by_contra hn
    have hraw := Order.one_le_iff_ne_zero.mpr hn
    apply hres
    apply (FieldOfNorms.residueAut_eq_refl_iff K L σ).mpr
    intro a
    have ha := hraw.trans (ramificationOrder_le (R := O) (O ≃+* O) g a)
    simpa only [pow_one] using (mem_maximalIdeal_pow_iff_addVal (g a - a) 1).mpr ha
  change (((ramificationOrder (R := O) (O ≃+* O) g : ℝ≥0∞) : EReal) - 1) = -1
  rw [hzero]
  simp

/-- A nonidentity action has a finite integer number,
namely a natural integral displacement order minus one. -/
theorem FieldOfNorms.ramificationNumber_eq_nat_sub_one [IsAPF K L]
    [Fact (¬ Module.Finite K L)] {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) :
    ∃ n : ℕ, FieldOfNorms.ramificationNumber K L σ = (n : EReal) - 1 := by
  let O := (FieldOfNorms.fieldValuation K L).valuationSubring
  let g := FieldOfNorms.integerAut K L σ
  have hg : g ≠ 1 := fun h => hσ ((FieldOfNorms.integerAut_eq_one_iff K L σ).mp h)
  have hfin : ramificationOrder (R := O) (O ≃+* O) g ≠ ⊤ :=
    (ramificationOrder_eq_top_iff (R := O) (O ≃+* O) g).not.mpr hg
  refine ⟨(ramificationOrder (R := O) (O ≃+* O) g).toNat, ?_⟩
  change (((ramificationOrder (R := O) (O ≃+* O) g : ℝ≥0∞) : EReal) - 1) = _
  rw [← ENat.natCast_toNat hfin, ENat.toENNReal_coe]
  norm_cast

/-- The automorphism acts on the intrinsic residue field through
its map on the integral closure of the base integers. -/
def algebraicResidueAut (σ : L ≃ₐ[K] L) :
    IsLocalRing.ResidueField
      (integralClosure 𝒪[K] L) ≃+*
    IsLocalRing.ResidueField
      (integralClosure 𝒪[K] L) :=
  IsLocalRing.ResidueField.mapEquiv
    (σ.restrictScalars (NormedField.valuation (K :=
        K)).valuationSubring).mapIntegralClosure.toRingEquiv

@[simp]
theorem algebraicResidueAut_residue (σ : L ≃ₐ[K] L)
    (a : integralClosure 𝒪[K] L) :
    algebraicResidueAut K L σ (IsLocalRing.residue _ a) =
      IsLocalRing.residue _
        ((σ.restrictScalars 𝒪[K]).mapIntegralClosure a)
            := rfl

/-- Ordinary finite residue inclusions commute with the intrinsic
residue inclusion of the algebraic extension. -/
theorem integralClosureResidueFromLayer_inclusion (E F : FiniteIntermediateField K L) (hEF : E ≤ F)
    (a : IsLocalRing.ResidueField (spectralIntegerRing K E.val)) :
    integralClosureResidueFromLayer K L F
      (spectralResidueInclusion K (IntermediateField.inclusion hEF) a) =
        integralClosureResidueFromLayer K L E a := by
  change (integralClosureSpectralResidueEquiv K (L := L)).symm
    (spectralResidueInclusion K F.val.val
      (spectralResidueInclusion K (IntermediateField.inclusion hEF) a)) = _
  rw [← AlgHom.comp_apply, ← spectralResidueInclusion_comp]
  rfl

/-- A finite restriction and the infinite automorphism
induce the same maps on the same intrinsic residue field. -/
theorem algebraicResidueAut_fromLayer (σ : L ≃ₐ[K] L) (E : FiniteIntermediateField K L)
    (s : E.val ≃ₐ[K] E.val) (hs : ∀ a : E.val, (s a : L) = σ (a : L))
    (a : IsLocalRing.ResidueField (spectralIntegerRing K E.val)) :
    algebraicResidueAut K L σ (integralClosureResidueFromLayer K L E a) =
      integralClosureResidueFromLayer K L E (spectralResidueInclusion K s.toAlgHom a) := by
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective a
  rw [integralClosureResidueFromLayer_residue, algebraicResidueAut_residue,
    spectralResidueInclusion_residue, integralClosureResidueFromLayer_residue]
  congr 1
  apply Subtype.ext
  change σ (((integralClosureSpectralEquiv K L).symm
      (spectralIntegerInclusion K E.val.val x) :
        integralClosure 𝒪[K] L) : L) = _
  simp only [coe_integralClosureSpectralEquiv_symm, coe_spectralIntegerInclusion]
  exact (hs (x : E.val)).symm

/-- The source-coordinate residue has exactly the inverse
Frobenius normalization after inclusion into the intrinsic residue field. -/
theorem residueCoordinateEquiv_pow [IsAPF K L]
    (E : FiniteIntermediateField K L) (hE : apfMaximalTame K L ≤ E)
    (a : IsLocalRing.ResidueField
      (integralClosure 𝒪[K] L)) :
    integralClosureResidueFromLayer K L E (residueCoordinateEquiv K L E hE a) ^
      p ^ residueDegree K L E hE = a := by
  rw [residueCoordinateEquiv_apply, residue_residueIntegralCoordinate,
    integralClosureResidueFromLayer_inclusion]
  exact residueRoot_pow K L E hE a

/-- On a stable finite restriction, the prescribed inverse
Frobenius residue root commutes with the residue action. -/
theorem residueCoordinateEquiv_aut [IsAPF K L]
    (σ : L ≃ₐ[K] L) (E : FiniteIntermediateField K L) (hE : apfMaximalTame K L ≤ E)
    (s : E.val ≃ₐ[K] E.val) (hs : ∀ a : E.val, (s a : L) = σ (a : L))
    (a : IsLocalRing.ResidueField
      (integralClosure 𝒪[K] L)) :
    spectralResidueInclusion K s.toAlgHom (residueCoordinateEquiv K L E hE a) =
      residueCoordinateEquiv K L E hE (algebraicResidueAut K L σ a) := by
  let κ := IsLocalRing.ResidueField
    (integralClosure 𝒪[K] L)
  let : PerfectField κ := IsAPF.perfectField_integralClosureResidue K L
  let : CharP κ p := charP_of_injective_algebraMap
    (algebraMap 𝓀[K] κ).injective p
  apply (integralClosureResidueFromLayer K L E).injective
  apply (iterateFrobeniusEquiv κ p (residueDegree K L E hE)).injective
  change integralClosureResidueFromLayer K L E
      (spectralResidueInclusion K s.toAlgHom
        (residueCoordinateEquiv K L E hE a)) ^
        p ^ residueDegree K L E hE =
      integralClosureResidueFromLayer K L E
        (residueCoordinateEquiv K L E hE (algebraicResidueAut K L σ a)) ^
          p ^ residueDegree K L E hE
  rw [← algebraicResidueAut_fromLayer K L σ E s hs, ← map_pow,
    residueCoordinateEquiv_pow, residueCoordinateEquiv_pow]

/-- Finite Teichmüller naturality transports the full
coordinate, not only its residue class. -/
theorem residueIntegralCoordinate_aut [IsAPF K L]
    (σ : L ≃ₐ[K] L) (E : FiniteIntermediateField K L) (hE : apfMaximalTame K L ≤ E)
    (s : E.val ≃ₐ[K] E.val) (hs : ∀ a : E.val, (s a : L) = σ (a : L))
    (a : IsLocalRing.ResidueField
      (integralClosure 𝒪[K] L)) :
    spectralIntegerInclusion K s.toAlgHom (residueIntegralCoordinate K L E hE a) =
      residueIntegralCoordinate K L E hE (algebraicResidueAut K L σ a) := by
  rw [residueIntegralCoordinate_eq_spectralTeichmuller,
    spectralTeichmuller_naturality, residueCoordinateEquiv_aut K L σ E hE s hs,
    ← residueIntegralCoordinate_eq_spectralTeichmuller]

/-- Coordinate covariance on the cofinal stable fields
proves equivariance of the same source-normalized constants in the
multiplicative field of norms. No normality of the ambient extension is used. -/
theorem FieldOfNorms.mapEquiv_residueConstants [IsAPF K L] [Fact (¬ Module.Finite K L)]
    (σ : L ≃ₐ[K] L)
    (a : IsLocalRing.ResidueField
      (integralClosure 𝒪[K] L)) :
    FieldOfNorms.mapEquiv σ (residueConstants K L a) =
      residueConstants K L (algebraicResidueAut K L σ a) := by
  apply FieldOfNorms.ext
  intro T
  let D := FiniteIntermediateField.sup T (apfMaximalTame K L)
  let E : FiniteIntermediateField K L := ⟨IntermediateField.normalClosure K D.val L, inferInstance⟩
  let s := IntermediateField.normalClosureRestrict D.val σ
  have hTE : T ≤ E :=
    (FiniteIntermediateField.le_sup_left T (apfMaximalTame K L)).trans
      (IntermediateField.le_normalClosure D.val)
  have hE : apfMaximalTame K L ≤ E :=
    (FiniteIntermediateField.le_sup_right T (apfMaximalTame K L)).trans
      (IntermediateField.le_normalClosure D.val)
  have hEinv : FiniteIntermediateField.map σ.symm.toAlgHom E = E :=
    Subtype.ext (IntermediateField.map_normalClosure_eq D.val σ.symm)
  have hcoord : FieldOfNorms.coord K L E (FieldOfNorms.mapEquiv σ (residueConstants K L a)) =
      FieldOfNorms.coord K L E
        (residueConstants K L (algebraicResidueAut K L σ a)) := by
    apply Subtype.val_injective
    rw [FieldOfNorms.coe_coord_mapEquiv, hEinv,
      FieldOfNorms.coord_residueConstants K L E hE,
      FieldOfNorms.coord_residueConstants K L E hE]
    have h := residueIntegralCoordinate_aut K L σ E hE s (fun _ => rfl) a
    exact congrArg (fun z : spectralIntegerRing K E.val => ((z : E.val) : L)) h
  have h := congrArg (FiniteIntermediateField.norm T E hTE) hcoord
  simpa only [FieldOfNorms.coord_norm] using h

/-- The same exact source-constant covariance holds inside the
norm-field valuation ring. -/
theorem FieldOfNorms.integerAut_residueConstantsInteger [IsAPF K L]
    [Fact (¬ Module.Finite K L)] (σ : L ≃ₐ[K] L) :
    ∀ a, FieldOfNorms.integerAut K L σ
      (residueConstantsInteger K L a) =
        residueConstantsInteger K L (algebraicResidueAut K L σ a) := by
  intro a
  apply Subtype.ext
  change FieldOfNorms.mapEquiv σ (residueConstants K L a) =
    residueConstants K L (algebraicResidueAut K L σ a)
  exact FieldOfNorms.mapEquiv_residueConstants K L σ a

/-- The residue isomorphism induced by the same constants
intertwines the two residue actions. -/
theorem FieldOfNorms.residueAut_residueEquiv [IsAPF K L]
    [Fact (¬ Module.Finite K L)] (σ : L ≃ₐ[K] L) :
    ∀ a, FieldOfNorms.residueAut K L σ
      (FieldOfNorms.residueEquiv K L a) =
        FieldOfNorms.residueEquiv K L (algebraicResidueAut K L σ a) := by
  intro a
  rw [FieldOfNorms.residueEquiv_apply, FieldOfNorms.residueAut_residue,
    FieldOfNorms.integerAut_residueConstantsInteger,
    ← FieldOfNorms.residueEquiv_apply]

/-- Inertia is exactly inertia on the norm field. -/
theorem FieldOfNorms.residueAut_eq_refl_iff_algebraicResidueAut [IsAPF K L]
    [Fact (¬ Module.Finite K L)] (σ : L ≃ₐ[K] L) :
    FieldOfNorms.residueAut K L σ = RingEquiv.refl _ ↔
      algebraicResidueAut K L σ = RingEquiv.refl _ := by
  let e := FieldOfNorms.residueEquiv K L
  constructor
  · intro h
    apply RingEquiv.ext
    intro a
    apply e.injective
    have hc := FieldOfNorms.residueAut_residueEquiv K L σ a
    simpa only [h, RingEquiv.refl_apply] using hc.symm
  · intro h
    apply RingEquiv.ext
    intro b
    obtain ⟨a, rfl⟩ := e.surjective b
    have hc := FieldOfNorms.residueAut_residueEquiv K L σ a
    simpa only [h, RingEquiv.refl_apply] using hc

/-- The residue of a moved finite embedding is the
residue action composed with its residue inclusion. -/
theorem algebraicResidueAut_fromLayer_embedding (σ : L ≃ₐ[K] L) (E : FiniteIntermediateField K L)
    (a : IsLocalRing.ResidueField (spectralIntegerRing K E.val)) :
    algebraicResidueAut K L σ (integralClosureResidueFromLayer K L E a) =
      (integralClosureSpectralResidueEquiv K (L := L)).symm
        (spectralResidueInclusion K (σ.toAlgHom.comp E.val.val) a) := by
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective a
  rw [integralClosureResidueFromLayer_residue, algebraicResidueAut_residue,
    spectralResidueInclusion_residue]
  change IsLocalRing.residue _ _ = IsLocalRing.residue _
    ((integralClosureSpectralEquiv K L).symm
      (spectralIntegerInclusion K (σ.toAlgHom.comp E.val.val) x))
  congr 1
  apply Subtype.ext
  simp only [AlgEquiv.coe_mapIntegralClosure, coe_integralClosureSpectralEquiv_symm,
    coe_spectralIntegerInclusion]
  rfl

/-- Every finite field above the tame part detects inertia,
including fields not preserved by the automorphism. -/
theorem FiniteIntermediateField.residue_eq_iff_algebraicResidueAut [IsAPF K L]
    (σ : L ≃ₐ[K] L) (E : FiniteIntermediateField K L) (hE : apfMaximalTame K L ≤ E) :
    spectralResidueInclusion K (σ.toAlgHom.comp E.val.val) =
        spectralResidueInclusion K E.val.val ↔
      algebraicResidueAut K L σ = RingEquiv.refl _ := by
  have hsurj := (integralClosureResidueFromLayer_bijective_of_apfMaximalUnramified_le
    K L E ((apfMaximalUnramified_le_maximalTame K L).trans hE)).surjective
  constructor
  · intro h
    apply RingEquiv.ext
    intro a
    obtain ⟨b, rfl⟩ := hsurj a
    rw [algebraicResidueAut_fromLayer_embedding, h]
    rfl
  · intro h
    ext a
    apply (integralClosureSpectralResidueEquiv K (L := L)).symm.injective
    have hc := algebraicResidueAut_fromLayer_embedding K L σ E a
    rw [h] at hc
    exact hc.symm

/-- The finite compositum of a layer and its moved image
inside the abstract extension. -/
def FiniteIntermediateField.autPairField (σ : L ≃ₐ[K] L) (E : FiniteIntermediateField K L) :
    FiniteIntermediateField K L :=
  FiniteIntermediateField.sup E (FiniteIntermediateField.map σ.toAlgHom E)

/-- The inclusion of the finite intermediate field into its pair field. -/
def FiniteIntermediateField.autPairLeft (σ : L ≃ₐ[K] L) (E : FiniteIntermediateField K L) :
    E.val →ₐ[K] (FiniteIntermediateField.autPairField K L σ E).val :=
  IntermediateField.inclusion (FiniteIntermediateField.le_sup_left E (FiniteIntermediateField.map
      σ.toAlgHom E))

/-- The moved embedding into the same finite compositum. -/
def FiniteIntermediateField.autPairRight (σ : L ≃ₐ[K] L) (E : FiniteIntermediateField K L) :
    E.val →ₐ[K] (FiniteIntermediateField.autPairField K L σ E).val :=
  (IntermediateField.inclusion (FiniteIntermediateField.le_sup_right E (FiniteIntermediateField.map
      σ.toAlgHom E))).comp
    (FiniteIntermediateField.equivMap σ.toAlgHom E).toAlgHom

omit [IsPerfectResidueLocalField K] [Algebra.IsSeparable K L] in
@[simp]
theorem coe_finiteIntermediateFieldAutPairLeft (σ : L ≃ₐ[K] L) (E : FiniteIntermediateField K L) (x
    : E.val) :
    (FiniteIntermediateField.autPairLeft K L σ E x : L) = x := rfl

omit [IsPerfectResidueLocalField K] [Algebra.IsSeparable K L] in
@[simp]
theorem coe_finiteIntermediateFieldAutPairRight (σ : L ≃ₐ[K] L) (E : FiniteIntermediateField K L)
    (x : E.val) :
    (FiniteIntermediateField.autPairRight K L σ E x : L) = σ (x : L) := rfl

/-- The intrinsic signed number of the finite restriction, computed
in the finite image compositum, even when the layer is not stable. -/
def FiniteIntermediateField.ramificationNumber (σ : L ≃ₐ[K] L) (E : FiniteIntermediateField K L) :
    EReal :=
  embeddingRamificationNumber K (FiniteIntermediateField.autPairRight K L σ E)
      (FiniteIntermediateField.autPairLeft K L σ E)

/-- The intrinsic finite number is infinite precisely when the
automorphism fixes every element of that finite intermediate field. -/
theorem FiniteIntermediateField.ramificationNumber_eq_top_iff (σ : L ≃ₐ[K] L) (E :
    FiniteIntermediateField K L) :
    FiniteIntermediateField.ramificationNumber K L σ E = ⊤ ↔ σ.toAlgHom.comp E.val.val = E.val.val
        := by
  rw [FiniteIntermediateField.ramificationNumber, embeddingRamificationNumber_eq_top_iff]
  constructor
  · intro h
    ext x
    exact congrArg (fun f => ((f x : (FiniteIntermediateField.autPairField K L σ E).val) : L)) h
  · intro h
    ext x
    exact congrArg (fun f : E.val →ₐ[K] L => f x) h

@[simp]
theorem FiniteIntermediateField.ramificationNumber_one (E : FiniteIntermediateField K L) :
    FiniteIntermediateField.ramificationNumber K L 1 E = ⊤ :=
  (FiniteIntermediateField.ramificationNumber_eq_top_iff K L 1 E).mpr (by ext x; rfl)

/-- Comparing residues in the finite pair field is equivalent to
comparing the embeddings in the algebraic extension. -/
theorem FiniteIntermediateField.autPair_residue_eq_iff (σ : L ≃ₐ[K] L) (E : FiniteIntermediateField
    K L) :
    spectralResidueInclusion K (FiniteIntermediateField.autPairRight K L σ E) =
        spectralResidueInclusion K (FiniteIntermediateField.autPairLeft K L σ E) ↔
      spectralResidueInclusion K (σ.toAlgHom.comp E.val.val) =
        spectralResidueInclusion K E.val.val := by
  let j := (FiniteIntermediateField.autPairField K L σ E).val.val
  have hr : (spectralResidueInclusion K j).comp
      (spectralResidueInclusion K (FiniteIntermediateField.autPairRight K L σ E)) =
        spectralResidueInclusion K (σ.toAlgHom.comp E.val.val) := by
    rw [← spectralResidueInclusion_comp]
    rfl
  have hl : (spectralResidueInclusion K j).comp
      (spectralResidueInclusion K (FiniteIntermediateField.autPairLeft K L σ E)) =
        spectralResidueInclusion K E.val.val := by
    rw [← spectralResidueInclusion_comp]
    rfl
  constructor
  · intro h
    rw [← hr, ← hl, h]
  · intro h
    ext a
    apply (spectralResidueInclusion K j).injective
    have hc := congrArg (fun f => f a) h
    rw [← hr, ← hl] at hc
    exact hc

/-- Above the tame part, the noninertial automorphism has
number minus one at every finite intermediate field, including nonstable layers. -/
theorem FiniteIntermediateField.ramificationNumber_eq_neg_one_of_residue_ne [IsAPF K L]
    (σ : L ≃ₐ[K] L) (E : FiniteIntermediateField K L) (hE : apfMaximalTame K L ≤ E)
    (hres : algebraicResidueAut K L σ ≠ RingEquiv.refl _) :
    FiniteIntermediateField.ramificationNumber K L σ E = -1 := by
  apply embeddingRamificationNumber_eq_neg_one_of_residue_ne K
  intro h
  apply hres
  exact (FiniteIntermediateField.residue_eq_iff_algebraicResidueAut K L σ E hE).mp
    ((FiniteIntermediateField.autPair_residue_eq_iff K L σ E).mp h)

/-- The noninertial automorphism has number minus one on the
norm field. -/
theorem FieldOfNorms.ramificationNumber_eq_neg_one_of_algebraicResidue_ne [IsAPF K L]
    [Fact (¬ Module.Finite K L)] (σ : L ≃ₐ[K] L)
    (hres : algebraicResidueAut K L σ ≠ RingEquiv.refl _) :
    FieldOfNorms.ramificationNumber K L σ = -1 := by
  apply FieldOfNorms.ramificationNumber_eq_neg_one_of_residue_ne K L σ
  exact fun h => hres
    ((FieldOfNorms.residueAut_eq_refl_iff_algebraicResidueAut K L σ).mp h)

/-- Embedding the extension in its separable closure does
not change the intrinsic number of any finite restriction. -/
theorem FiniteIntermediateField.ramificationNumber_eq_closure (σ : L ≃ₐ[K] L)
    (E : FiniteIntermediateField K L) (j : L →ₐ[K] SeparableClosure K) :
    FiniteIntermediateField.ramificationNumber K L σ E =
      closureEmbeddingNumber K ((j.comp σ.toAlgHom).comp E.val.val) (j.comp E.val.val) := by
  have h := closureEmbeddingNumber_comp K (FiniteIntermediateField.autPairRight K L σ E)
    (FiniteIntermediateField.autPairLeft K L σ E) (j.comp (FiniteIntermediateField.autPairField K L
        σ E).val.val)
  exact h.symm

/-- A stable finite restriction computes the same intrinsic number
as the moved-image pair; no stability of other layers is required. -/
theorem FiniteIntermediateField.ramificationNumber_eq_aut (σ : L ≃ₐ[K] L) (E :
    FiniteIntermediateField K L)
    (s : E.val ≃ₐ[K] E.val) (hs : ∀ a : E.val, (s a : L) = σ (a : L)) :
    FiniteIntermediateField.ramificationNumber K L σ E =
      ((ramificationOrder (R := spectralIntegerRing K E.val) (E.val ≃ₐ[K] E.val) s :
        ℝ≥0∞) : EReal) - 1 := by
  have he : (FiniteIntermediateField.autPairLeft K L σ E).comp s.toAlgHom =
      FiniteIntermediateField.autPairRight K L σ E := by
    ext a
    exact hs a
  have h := embeddingRamificationNumber_comp K s.toAlgHom (AlgHom.id K E.val)
    (FiniteIntermediateField.autPairLeft K L σ E)
  rw [he] at h
  exact h.trans (embeddingRamificationNumber_aut K s)

/-- Triviality on the intrinsic residue field forces
residue triviality on each stable finite restriction. -/
theorem spectralResidueInclusion_eq_id_of_algebraicResidueAut_eq_refl
    (σ : L ≃ₐ[K] L) (E : FiniteIntermediateField K L) (s : E.val ≃ₐ[K] E.val)
    (hs : ∀ a : E.val, (s a : L) = σ (a : L))
    (hres : algebraicResidueAut K L σ = RingEquiv.refl _) :
    spectralResidueInclusion K s.toAlgHom = AlgHom.id _ _ := by
  ext a
  apply (integralClosureResidueFromLayer K L E).injective
  change integralClosureResidueFromLayer K L E
    (spectralResidueInclusion K s.toAlgHom a) = integralClosureResidueFromLayer K L E a
  rw [← algebraicResidueAut_fromLayer K L σ E s hs, hres]
  rfl

/-- Every uniformizer computes the number of an inertial stable
finite restriction, including the identity with its infinite number. -/
theorem FiniteIntermediateField.ramificationNumber_eq_uniformizer (σ : L ≃ₐ[K] L)
    (E : FiniteIntermediateField K L) (s : E.val ≃ₐ[K] E.val)
    (hs : ∀ a : E.val, (s a : L) = σ (a : L))
    (hres : algebraicResidueAut K L σ = RingEquiv.refl _)
    {π : spectralIntegerRing K E.val} (hπ : Irreducible π) :
    FiniteIntermediateField.ramificationNumber K L σ E =
      (((IsDiscreteValuationRing.addVal (spectralIntegerRing K E.val)
        (spectralIntegerInclusion K s.toAlgHom π - π) : ℝ≥0∞) : EReal) - 1) := by
  rw [FiniteIntermediateField.ramificationNumber_eq_aut K L σ E s hs,
    ← embeddingRamificationNumber_aut K s,
    embeddingRamificationNumber_eq_uniformizer K s.toAlgHom (AlgHom.id K E.val)]
  · rw [embeddingRamificationIdx_aut, Nat.cast_one, div_one]
    rfl
  · rw [spectralResidueInclusion_eq_id_of_algebraicResidueAut_eq_refl K L σ E s hs hres]
    ext a
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective a
    rw [spectralResidueInclusion_residue]
    rfl
  · exact hπ

/-- The intrinsic inertia action has nonnegative number on every
finite intermediate field, whether or not that layer is stable. -/
theorem FiniteIntermediateField.ramificationNumber_nonneg (σ : L ≃ₐ[K] L)
    (hres : algebraicResidueAut K L σ = RingEquiv.refl _) (E : FiniteIntermediateField K L) :
    0 ≤ FiniteIntermediateField.ramificationNumber K L σ E := by
  apply embeddingRamificationNumber_nonneg K
  apply (FiniteIntermediateField.autPair_residue_eq_iff K L σ E).mpr
  ext a
  apply (integralClosureSpectralResidueEquiv K (L := L)).symm.injective
  change (integralClosureSpectralResidueEquiv K (L := L)).symm
    (spectralResidueInclusion K (σ.toAlgHom.comp E.val.val) a) =
      integralClosureResidueFromLayer K L E a
  rw [← algebraicResidueAut_fromLayer_embedding K L σ E a, hres]
  rfl

/-- Every finite restriction has a finite Galois ambient
presentation, simultaneously for all of its subfields. The normal
closure is taken only after embedding the image compositum in the
separable closure, so the extension need not be normal. -/
theorem exists_finiteGalois_embedding_restrictions (σ : L ≃ₐ[K] L)
    (F : FiniteIntermediateField K L) :
    ∃ (Ω : FiniteGaloisIntermediateField K (SeparableClosure K))
      (i : F.val →ₐ[K] Ω) (s : Ω ≃ₐ[K] Ω),
      ∀ (E : FiniteIntermediateField K L) (hEF : E ≤ F),
        FiniteIntermediateField.ramificationNumber K L σ E =
          embeddingRamificationNumber K
            (s.toAlgHom.comp (i.comp (IntermediateField.inclusion hEF)))
            (i.comp (IntermediateField.inclusion hEF)) := by
  let j : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let P := FiniteIntermediateField.autPairField K L σ F
  let jP := j.comp P.val.val
  let : FiniteDimensional K jP.fieldRange :=
    Module.Finite.equiv jP.equivFieldRange.toLinearEquiv
  let Ω := finiteGaloisNormalClosure K jP.fieldRange
  let u : P.val →ₐ[K] Ω := jP.codRestrict Ω.toIntermediateField.toSubalgebra
    (fun x => le_finiteGaloisNormalClosure K jP.fieldRange ⟨x, rfl⟩)
  let i := u.comp (FiniteIntermediateField.autPairLeft K L σ F)
  let t := u.comp (FiniteIntermediateField.autPairRight K L σ F)
  let e := i.equivFieldRange
  obtain ⟨s, hs⟩ := exists_aut_comp_intermediate K Ω i.fieldRange
    (t.comp e.symm.toAlgHom)
  have hsi : s.toAlgHom.comp i = t := by
    apply AlgHom.ext
    intro x
    have h := congrArg (fun f : i.fieldRange →ₐ[K] Ω => f (e x)) hs
    change s (i x) = t (e.symm (e x)) at h
    exact h.trans (congrArg t (e.symm_apply_apply x))
  refine ⟨Ω, i, s, fun E hEF => ?_⟩
  rw [FiniteIntermediateField.ramificationNumber_eq_closure K L σ E j]
  have hr : s.toAlgHom.comp (i.comp (IntermediateField.inclusion hEF)) =
      t.comp (IntermediateField.inclusion hEF) := by
    apply AlgHom.ext
    intro x
    exact congrArg (fun f : F.val →ₐ[K] Ω => f (IntermediateField.inclusion hEF x)) hsi
  have h := closureEmbeddingNumber_comp K
    (s.toAlgHom.comp (i.comp (IntermediateField.inclusion hEF)))
    (i.comp (IntermediateField.inclusion hEF)) Ω.toIntermediateField.val
  rw [hr] at h ⊢
  exact h

/-- The finite image inclusion has exactly the local index. -/
theorem FiniteIntermediateField.fieldRange_ramificationIdx
    {Ω : Type*} [Field Ω] [Algebra K Ω] [FiniteDimensional K Ω]
    [Algebra.IsSeparable K Ω] (E F : FiniteIntermediateField K L) (hEF : E ≤ F)
    (i : F.val →ₐ[K] Ω) :
    letI : FiniteDimensional K i.fieldRange := Module.Finite.equiv i.equivFieldRange.toLinearEquiv
    let iE := i.comp (IntermediateField.inclusion hEF)
    letI : FiniteDimensional K iE.fieldRange :=
      Module.Finite.equiv iE.equivFieldRange.toLinearEquiv
    let hmap : iE.fieldRange ≤ i.fieldRange := fun _ ⟨x, hx⟩ =>
      ⟨IntermediateField.inclusion hEF x, hx⟩
    embeddingRamificationIdx K (IntermediateField.inclusion hmap) =
      embeddingRamificationIdx K (IntermediateField.inclusion hEF) := by
  let : FiniteDimensional K i.fieldRange := Module.Finite.equiv i.equivFieldRange.toLinearEquiv
  let iE := i.comp (IntermediateField.inclusion hEF)
  let : FiniteDimensional K iE.fieldRange := Module.Finite.equiv iE.equivFieldRange.toLinearEquiv
  let hmap : iE.fieldRange ≤ i.fieldRange := fun _ ⟨x, hx⟩ =>
    ⟨IntermediateField.inclusion hEF x, hx⟩
  let eE := iE.equivFieldRange
  let eF := i.equivFieldRange
  have hcomm : (IntermediateField.inclusion hmap).comp eE.toAlgHom =
      eF.toAlgHom.comp (IntermediateField.inclusion hEF) := by
    ext x
    rfl
  have ha := embeddingRamificationIdx_comp K eE.toAlgHom (IntermediateField.inclusion hmap)
  have hb := embeddingRamificationIdx_comp K (IntermediateField.inclusion hEF) eF.toAlgHom
  rw [embeddingRamificationIdx_algEquiv, one_mul, hcomm] at ha
  rw [embeddingRamificationIdx_algEquiv, mul_one] at hb
  exact ha.symm.trans hb

omit [IsPerfectResidueLocalField K] in
/-- The relative degree of the finite image step is the degree. -/
theorem FiniteIntermediateField.fieldRange_finrank
    {Ω : Type*} [Field Ω] [Algebra K Ω] [FiniteDimensional K Ω]
    [Algebra.IsSeparable K Ω] (E F : FiniteIntermediateField K L) (hEF : E ≤ F)
    (i : F.val →ₐ[K] Ω) :
    letI : FiniteDimensional K i.fieldRange := Module.Finite.equiv i.equivFieldRange.toLinearEquiv
    let iE := i.comp (IntermediateField.inclusion hEF)
    letI : FiniteDimensional K iE.fieldRange :=
      Module.Finite.equiv iE.equivFieldRange.toLinearEquiv
    let hmap : iE.fieldRange ≤ i.fieldRange := fun _ ⟨x, hx⟩ =>
      ⟨IntermediateField.inclusion hEF x, hx⟩
    Module.finrank iE.fieldRange (IntermediateField.extendScalars hmap) =
      Module.finrank E.val (IntermediateField.extendScalars hEF) := by
  let : FiniteDimensional K i.fieldRange := Module.Finite.equiv i.equivFieldRange.toLinearEquiv
  let iE := i.comp (IntermediateField.inclusion hEF)
  let : FiniteDimensional K iE.fieldRange := Module.Finite.equiv iE.equivFieldRange.toLinearEquiv
  let hmap : iE.fieldRange ≤ i.fieldRange := fun _ ⟨x, hx⟩ =>
    ⟨IntermediateField.inclusion hEF x, hx⟩
  let F' := IntermediateField.extendScalars hEF
  let D' := IntermediateField.extendScalars hmap
  let : FiniteDimensional K F' := inferInstanceAs (FiniteDimensional K F.val)
  let : FiniteDimensional E.val F' := Module.Finite.right K E.val F'
  let : FiniteDimensional K D' := inferInstanceAs (FiniteDimensional K i.fieldRange)
  let : FiniteDimensional iE.fieldRange D' := Module.Finite.right K iE.fieldRange D'
  have ht := Module.finrank_mul_finrank K E.val F'
  have ht' := Module.finrank_mul_finrank K iE.fieldRange D'
  have hE := iE.equivFieldRange.toLinearEquiv.finrank_eq
  have hF := i.equivFieldRange.toLinearEquiv.finrank_eq
  have hpos : 0 < Module.finrank K E.val := Module.finrank_pos
  change Module.finrank K E.val * Module.finrank E.val F' = Module.finrank K F.val at ht
  change Module.finrank K iE.fieldRange * Module.finrank iE.fieldRange D' =
    Module.finrank K i.fieldRange at ht'
  rw [← hE, ← hF] at ht'
  nlinarith [ht, ht', hpos]

/-- On every finite step above the tame part, strictness
below the relative first bound forces equality of the intrinsic
embedding numbers. Neither layer is required to be stable. -/
theorem FiniteIntermediateField.ramificationNumber_eq_of_lt_relativeFirstBound
    [IsAPF K L] (σ : L ≃ₐ[K] L) (E F : FiniteIntermediateField K L)
    (hE : apfMaximalTame K L ≤ E) (hEF : E ≤ F)
    (hσE : σ.toAlgHom.comp E.val.val ≠ E.val.val) :
    letI := spectralNorm.nontriviallyNormedField K E.val
    letI := spectralNorm.normedAlgebra K E.val
    letI := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
      (isNonarchimedean_spectralNorm (K := K) (L := E.val))
    letI := normedAlgebra_isCompleteDiscreteValuedField K E.val
    FiniteIntermediateField.ramificationNumber K L σ E <
      apfRamificationBound E.val (IntermediateField.extendScalars hEF) →
      FiniteIntermediateField.ramificationNumber K L σ F =
          FiniteIntermediateField.ramificationNumber K L σ E := by
  let := spectralNorm.nontriviallyNormedField K E.val
  let := spectralNorm.normedAlgebra K E.val
  let := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := E.val))
  let := normedAlgebra_isCompleteDiscreteValuedField K E.val
  let : Algebra E.val F.val := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
  let : IsScalarTower K E.val F.val := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.IsSeparable E.val F.val :=
    Algebra.isSeparable_tower_top_of_isSeparable K E.val F.val
  let : FiniteDimensional E.val F.val := Module.Finite.right K E.val F.val
  intro hsmall
  obtain ⟨Ω, i, s, hmodel⟩ := exists_finiteGalois_embedding_restrictions K L σ F
  let : FiniteDimensional K i.fieldRange := Module.Finite.equiv i.equivFieldRange.toLinearEquiv
  let iE := i.comp (IntermediateField.inclusion hEF)
  let : FiniteDimensional K iE.fieldRange := Module.Finite.equiv iE.equivFieldRange.toLinearEquiv
  let hmap : iE.fieldRange ≤ i.fieldRange := fun _ ⟨x, hx⟩ =>
    ⟨IntermediateField.inclusion hEF x, hx⟩
  have hFmodel : FiniteIntermediateField.ramificationNumber K L σ F =
      embeddingRamificationNumber K (s.toAlgHom.comp i) i := hmodel F le_rfl
  have hFnum := hFmodel.trans (embeddingNumber_precomp_algEquiv K i.equivFieldRange
    (s.toAlgHom.comp i.fieldRange.val) i.fieldRange.val)
  have hEnum := (hmodel E hEF).trans (embeddingNumber_precomp_algEquiv K iE.equivFieldRange
    (s.toAlgHom.comp iE.fieldRange.val) iE.fieldRange.val)
  have hs : s.toAlgHom.comp iE.fieldRange.val ≠ iE.fieldRange.val := by
    intro h
    apply hσE
    apply (FiniteIntermediateField.ramificationNumber_eq_top_iff K L σ E).mp
    rw [hEnum, h, embeddingRamificationNumber_self]
  have htotal : embeddingRamificationIdx K (IntermediateField.inclusion hEF) =
      Module.finrank E.val (IntermediateField.extendScalars hEF) :=
    (apfMaximalTame_wild_tail K L E F hE hEF).2.2
  have htotal' : embeddingRamificationIdx K (IntermediateField.inclusion hmap) =
      Module.finrank iE.fieldRange (IntermediateField.extendScalars hmap) :=
    (FiniteIntermediateField.fieldRange_ramificationIdx K L E F hEF i).trans
      (htotal.trans (FiniteIntermediateField.fieldRange_finrank K L E F hEF i).symm)
  have hM : ∀ m : E.val, (i.equivFieldRange (algebraMap E.val F.val m) : Ω) ∈ iE.fieldRange :=
    fun m => ⟨m, rfl⟩
  have hsmall' : embeddingRamificationNumber K (s.toAlgHom.comp iE.fieldRange.val)
      iE.fieldRange.val < apfRamificationBound E.val F.val := by
    rw [← hEnum]
    exact hsmall
  have h := embeddingNumber_eq_restriction_of_lt_bound K E.val
    iE.fieldRange i.fieldRange hmap i.equivFieldRange hM htotal' s hs hsmall'
  exact hFnum.trans (h.trans hEnum.symm)

/-- A finite nonzero displacement on the norm field is computed
by the ordinary difference of its coordinates at every sufficiently
deep finite field, with no stability assumption on those fields. -/
theorem FieldOfNorms.valuation_sub_eventually_coordinate [IsAPF K L]
    [Fact (¬ Module.Finite K L)] :
    ∀ (α β : FieldOfNorms K L) (n : ℤ),
      FieldOfNorms.valuation K L (α - β) = WithZero.exp (-n) →
      ∃ T : FiniteIntermediateField K L, ∀ E : FiniteIntermediateField K L, T ≤ E →
        (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K E.val)).valuation E.val
          (FieldOfNorms.coord K L E α - FieldOfNorms.coord K L E β) = WithZero.exp (-n) := by
  intro α β n hn
  let s : ℕ := n.toNat + 1
  obtain ⟨T₀, hT₀⟩ := FieldOfNorms.exists_valuation_eq_coordinateValuation K L
  obtain ⟨T₁, hT₁⟩ := FieldOfNorms.coord_sub_sub_mem K L α β s
  refine ⟨FiniteIntermediateField.sup T₀ T₁, fun E hE => ?_⟩
  have hE₀ := (FiniteIntermediateField.le_sup_left T₀ T₁).trans hE
  have hE₁ := (FiniteIntermediateField.le_sup_right T₀ T₁).trans hE
  let v := (IsDiscreteValuationRing.maximalIdeal (spectralIntegerRing K E.val)).valuation E.val
  have hval : v (FieldOfNorms.coord K L E (α - β)) = WithZero.exp (-n) :=
    (hT₀ E hE₀ (α - β)).symm.trans hn
  have hbound : v (FieldOfNorms.coord K L E (α - β) - FieldOfNorms.coord K L E α +
      FieldOfNorms.coord K L E β) ≤ WithZero.exp (-(s : ℤ)) :=
    (ValuationSubring.mem_image_maximalIdeal_pow_iff_normalizedValuation
      (spectralIntegerRing K E.val) _ s).mp (hT₁ E hE₁)
  have hlt : WithZero.exp (-(s : ℤ)) < WithZero.exp (-n) := by
    apply WithZero.exp_lt_exp.mpr
    dsimp [s]
    omega
  have heq : FieldOfNorms.coord K L E α - FieldOfNorms.coord K L E β -
      FieldOfNorms.coord K L E (α - β) =
        -(FieldOfNorms.coord K L E (α - β) - FieldOfNorms.coord K L E α +
          FieldOfNorms.coord K L E β) := by ring
  have hclose : v (FieldOfNorms.coord K L E α - FieldOfNorms.coord K L E β -
      FieldOfNorms.coord K L E (α - β)) < v (FieldOfNorms.coord K L E (α - β)) := by
    rw [heq, v.map_neg, hval]
    exact hbound.trans_lt hlt
  exact (v.map_eq_of_sub_lt hclose).trans hval

/-- On a finite tail, every stable finite restriction has
exactly the ramification number of the norm-field action. -/
theorem exists_finiteIntermediateField_stableRamificationNumber_eq [IsAPF K L]
    [Fact (¬ Module.Finite K L)] (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (hres : algebraicResidueAut K L σ = RingEquiv.refl _) :
    ∃ T : FiniteIntermediateField K L, ∀ E : FiniteIntermediateField K L, T ≤ E →
      FiniteIntermediateField.map σ.toAlgHom E = E →
      FiniteIntermediateField.ramificationNumber K L σ E =
        FieldOfNorms.ramificationNumber K L σ := by
  let O := (FieldOfNorms.fieldValuation K L).valuationSubring
  let π := FieldOfNorms.uniformizerInteger K L
  let g := FieldOfNorms.integerAut K L σ
  let δ : O := g π - π
  have hπ : Irreducible π := FieldOfNorms.uniformizerInteger_irreducible K L
  have hresX := (FieldOfNorms.residueAut_eq_refl_iff_algebraicResidueAut
    K L σ).mpr hres
  have hformula := FieldOfNorms.ramificationNumber_eq_uniformizer
    K L σ hresX π hπ
  change FieldOfNorms.ramificationNumber K L σ =
    (((IsDiscreteValuationRing.addVal O δ : ℝ≥0∞) : EReal) - 1) at hformula
  have hntop : FieldOfNorms.ramificationNumber K L σ ≠ ⊤ :=
    fun h => hσ ((FieldOfNorms.ramificationNumber_eq_top_iff K L σ).mp h)
  have hfin : IsDiscreteValuationRing.addVal O δ ≠ ⊤ := by
    intro ht
    apply hntop
    rw [hformula, ht]
    exact EReal.top_sub_coe 1
  let n : ℕ := (IsDiscreteValuationRing.addVal O δ).toNat
  have hn : IsDiscreteValuationRing.addVal O δ = (n : ℕ∞) :=
    (ENat.natCast_toNat hfin).symm
  have hnum : FieldOfNorms.ramificationNumber K L σ = (n : EReal) - 1 := by
    rw [hformula, hn]
    norm_cast
  have hδval : (IsDiscreteValuationRing.maximalIdeal O).valuation (FieldOfNorms K L)
      (δ : FieldOfNorms K L) = WithZero.exp (-(n : ℤ)) := by
    change (IsDiscreteValuationRing.maximalIdeal O).valuation (FieldOfNorms K L)
      (algebraMap O (FieldOfNorms K L) δ) = _
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDiscreteValuationRing.intValuation_maximalIdeal, hn]
    rfl
  rw [FieldOfNorms.fieldValuation_eq_normalized K L] at hδval
  change FieldOfNorms.valuation K L
    (FieldOfNorms.aut K L σ (FieldOfNorms.uniformizer K L) -
      FieldOfNorms.uniformizer K L) = WithZero.exp (-(n : ℤ)) at hδval
  obtain ⟨T, hT⟩ := FieldOfNorms.valuation_sub_eventually_coordinate K L
    (FieldOfNorms.aut K L σ (FieldOfNorms.uniformizer K L))
    (FieldOfNorms.uniformizer K L) (n : ℤ) hδval
  refine ⟨FiniteIntermediateField.sup (apfMaximalTame K L) T, fun E hE hStable => ?_⟩
  have hK₁ := (FiniteIntermediateField.le_sup_left (apfMaximalTame K L) T).trans hE
  have hTE := (FiniteIntermediateField.le_sup_right (apfMaximalTame K L) T).trans hE
  let s : E.val ≃ₐ[K] E.val := (FiniteIntermediateField.equivMap σ.toAlgHom E).trans
    (IntermediateField.equivOfEq (congrArg Subtype.val hStable))
  have hs : ∀ a : E.val, (s a : L) = σ (a : L) := fun _ => rfl
  have hEinv : FiniteIntermediateField.map σ.symm.toAlgHom E = E := by
    have h := (FiniteIntermediateField.mapOrderIso σ).left_inv E
    change FiniteIntermediateField.map σ.symm.toAlgHom (FiniteIntermediateField.map σ.toAlgHom E) =
        E at h
    rwa [hStable] at h
  have hcoor : FieldOfNorms.coord K L E
      (FieldOfNorms.aut K L σ (FieldOfNorms.uniformizer K L)) =
        s (FieldOfNorms.coord K L E (FieldOfNorms.uniformizer K L)) := by
    apply Subtype.val_injective
    change (FieldOfNorms.coord K L E
      (FieldOfNorms.mapEquiv σ (FieldOfNorms.uniformizer K L)) : L) = _
    rw [FieldOfNorms.coe_coord_mapEquiv, hEinv, hs]
  let πE := FieldOfNorms.uniformizerCoordinateInteger K L E
  let R := spectralIntegerRing K E.val
  let δE : R := spectralIntegerInclusion K s.toAlgHom πE - πE
  have hπE : Irreducible πE := FieldOfNorms.uniformizerCoordinateInteger_irreducible K L
    E ((apfMaximalUnramified_le_maximalTame K L).trans hK₁)
  have hδEVal : (IsDiscreteValuationRing.maximalIdeal R).valuation E.val
      (δE : E.val) = WithZero.exp (-(n : ℤ)) := by
    have h := hT E hTE
    rw [hcoor] at h
    exact h
  have hδENat : IsDiscreteValuationRing.addVal R δE = (n : ℕ∞) := by
    change (IsDiscreteValuationRing.maximalIdeal R).valuation E.val
      (algebraMap R E.val δE) = _ at hδEVal
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDiscreteValuationRing.intValuation_maximalIdeal] at hδEVal
    induction h : IsDiscreteValuationRing.addVal R δE using ENat.recTopCoe with
    | top =>
      rw [h] at hδEVal
      change (0 : WithZero (Multiplicative ℤ))⁻¹ = WithZero.exp (-(n : ℤ)) at hδEVal
      rw [inv_zero] at hδEVal
      exact False.elim (WithZero.exp_ne_zero hδEVal.symm)
    | coe m =>
      rw [h] at hδEVal
      change WithZero.exp (-(m : ℤ)) = WithZero.exp (-(n : ℤ)) at hδEVal
      have hm : m = n := by exact_mod_cast neg_injective (WithZero.exp_injective hδEVal)
      simp only [hm]
  rw [FiniteIntermediateField.ramificationNumber_eq_uniformizer K L σ E s hs hres hπE, hnum]
  change (((IsDiscreteValuationRing.addVal R δE : ℝ≥0∞) : EReal) - 1) = _
  rw [hδENat]
  norm_cast

/-- The inertia action has a finite constant number on
EVERY finite field above one stable field. The constant is
the number of the norm-field action. -/
theorem exists_finiteIntermediateField_inertial_ramificationNumber_eq [IsAPF K L]
    [Fact (¬ Module.Finite K L)] (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (hres : algebraicResidueAut K L σ = RingEquiv.refl _) :
    ∃ (E : FiniteIntermediateField K L) (c : ℝ), FiniteIntermediateField.map σ.toAlgHom E = E ∧
      0 ≤ c ∧ FieldOfNorms.ramificationNumber K L σ = (c : EReal) ∧
      ∀ F : FiniteIntermediateField K L, E ≤ F → FiniteIntermediateField.ramificationNumber K L σ F
          = (c : EReal) := by
  obtain ⟨T, hT⟩ := exists_finiteIntermediateField_stableRamificationNumber_eq K L σ hσ hres
  obtain ⟨n, hn⟩ := FieldOfNorms.ramificationNumber_eq_nat_sub_one K L hσ
  let c : ℝ := n - 1
  have hc : FieldOfNorms.ramificationNumber K L σ = (c : EReal) := by
    rw [hn]
    dsimp [c]
  obtain ⟨D, hD⟩ := IsAPF.exists_finiteIntermediateField_relativeFirstBound_ge K L (c + 1)
  let A := FiniteIntermediateField.sup (FiniteIntermediateField.sup T D) (apfMaximalTame K L)
  let E : FiniteIntermediateField K L := ⟨IntermediateField.normalClosure K A.val L, inferInstance⟩
  have hAE : A ≤ E := IntermediateField.le_normalClosure A.val
  have hTE : T ≤ E := (FiniteIntermediateField.le_sup_left T D).trans
    ((FiniteIntermediateField.le_sup_left (FiniteIntermediateField.sup T D) (apfMaximalTame K
        L)).trans hAE)
  have hDE : D ≤ E := (FiniteIntermediateField.le_sup_right T D).trans
    ((FiniteIntermediateField.le_sup_left (FiniteIntermediateField.sup T D) (apfMaximalTame K
        L)).trans hAE)
  have hK₁ : apfMaximalTame K L ≤ E :=
    (FiniteIntermediateField.le_sup_right (FiniteIntermediateField.sup T D) (apfMaximalTame K
        L)).trans hAE
  have hStable : FiniteIntermediateField.map σ.toAlgHom E = E :=
    Subtype.ext (IntermediateField.map_normalClosure_eq A.val σ)
  have hEnum : FiniteIntermediateField.ramificationNumber K L σ E = (c : EReal) :=
    (hT E hTE hStable).trans hc
  have hc₀ : 0 ≤ c := by
    have h := FiniteIntermediateField.ramificationNumber_nonneg K L σ hres E
    rw [hEnum] at h
    exact_mod_cast h
  refine ⟨E, c, hStable, hc₀, hc, fun F hEF => ?_⟩
  let := spectralNorm.nontriviallyNormedField K E.val
  let := spectralNorm.normedAlgebra K E.val
  let := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.mpr
    (isNonarchimedean_spectralNorm (K := K) (L := E.val))
  let := normedAlgebra_isCompleteDiscreteValuedField K E.val
  have hσE : σ.toAlgHom.comp E.val.val ≠ E.val.val := by
    intro hfix
    have ht := (FiniteIntermediateField.ramificationNumber_eq_top_iff K L σ E).mpr hfix
    rw [hEnum] at ht
    exact EReal.coe_ne_top c ht
  have hsmall : FiniteIntermediateField.ramificationNumber K L σ E <
      apfRamificationBound E.val (IntermediateField.extendScalars hEF) := by
    rw [hEnum]
    have hlt : (c : EReal) < ((c + 1 : ℝ) : EReal) :=
      EReal.coe_lt_coe_iff.mpr (by linarith)
    exact hlt.trans_le (hD E F hDE hEF)
  exact (FiniteIntermediateField.ramificationNumber_eq_of_lt_relativeFirstBound K L σ E F
    hK₁ hEF hσE hsmall).trans hEnum

/-- Wintenberger's ramification transfer on the norm field:
one finite field controls EVERY upper finite field,
including those moved by the automorphism. -/
theorem exists_finiteIntermediateField_ramificationNumber_eq [IsAPF K L]
    [Fact (¬ Module.Finite K L)] (σ : L ≃ₐ[K] L) :
    ∃ E : FiniteIntermediateField K L, ∀ F : FiniteIntermediateField K L, E ≤ F →
      FiniteIntermediateField.ramificationNumber K L σ F =
        FieldOfNorms.ramificationNumber K L σ := by
  by_cases hσ : σ = 1
  · subst σ
    refine ⟨⟨⊥, inferInstance⟩, fun F _ => ?_⟩
    rw [FiniteIntermediateField.ramificationNumber_one, FieldOfNorms.ramificationNumber_one]
  by_cases hres : algebraicResidueAut K L σ = RingEquiv.refl _
  · obtain ⟨E, c, _, _, hc, hE⟩ :=
      exists_finiteIntermediateField_inertial_ramificationNumber_eq K L σ hσ hres
    exact ⟨E, fun F hEF => (hE F hEF).trans hc.symm⟩
  · refine ⟨apfMaximalTame K L, fun F hF => ?_⟩
    rw [FiniteIntermediateField.ramificationNumber_eq_neg_one_of_residue_ne K L σ F hF hres,
      FieldOfNorms.ramificationNumber_eq_neg_one_of_algebraicResidue_ne K L σ hres]

end Action

end FontaineWintenberger
