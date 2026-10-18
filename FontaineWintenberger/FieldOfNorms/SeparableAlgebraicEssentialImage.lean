/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import FontaineWintenberger.LocalField.Basic
public import FontaineWintenberger.FieldOfNorms.SeparableEssentialImage
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-!
# Actual algebraic essential image of the original norm-field union

Unique reconstruction of finite original subfields gives a directed family.
Its original intermediate-field supremum has precisely the prescribed image
under the same canonical norm-field union embedding.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

section DirectedFields

variable {L Ω : Type*} [Field L] [Field Ω] [Algebra L Ω]

/-- Every finite original subfield of a directed union lies in a single
member, by the compactness of its finitely generated intermediate field. -/
theorem FiniteLayer.exists_le_of_le_directed_iSup {ι : Type*} [Nonempty ι]
    (A : ι → IntermediateField L Ω) (hA : Directed (· ≤ ·) A)
    (Q : FiniteLayer L Ω) (hQ : Q.val ≤ ⨆ i, A i) :
    ∃ i, Q.val ≤ A i := by
  have hfg : Q.val.FG := IntermediateField.essFiniteType_iff.mp inferInstance
  obtain ⟨s, hs⟩ := hfg
  have hc : IsCompactElement Q.val :=
    hs ▸ IntermediateField.adjoin_finset_isCompactElement s
  obtain ⟨B, ⟨i, rfl⟩, hi⟩ := hc (Set.range A) (⨆ i, A i)
    (Set.range_nonempty A) hA.directedOn_range isLUB_iSup hQ
  exact ⟨i, hi⟩

end DirectedFields

section OriginalImages

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
    (L Ω : Type*) [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable L Ω]
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]
    [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- A finite original subfield contained in an original intermediate field
has its entire canonical norm-field image in that intermediate union's
original inclusion map. -/
theorem separableNormUnionFiniteImage_le_fieldRange_of_le
    (M : IntermediateField L Ω) (N : FiniteLayer L Ω) (hNM : N.val ≤ M) :
    letI := normLimitField K L p
    letI := separableNormUnionField K L M p
    letI := separableNormUnionField K L Ω p
    letI := separableNormUnionAlgebra K L M p
    letI := separableNormUnionAlgebra K L Ω p
    separableNormUnionFiniteImage K L Ω p N ≤
      (separableNormUnionAlgMap K L M p Ω M.val).fieldRange := by
  let := normLimitField K L p
  let := separableNormUnionField K L M p
  let := separableNormUnionField K L Ω p
  let := separableNormUnionAlgebra K L M p
  let := separableNormUnionAlgebra K L Ω p
  let Q₀ := N.val.comap M.val
  let q : Q₀ →ₐ[L] N.val :=
    { toFun := fun a => ⟨(a.val : Ω), a.property⟩
      map_zero' := rfl
      map_one' := rfl
      map_add' _ _ := rfl
      map_mul' _ _ := rfl
      commutes' _ := rfl }
  have hq : Function.Surjective q := by
    intro a
    exact ⟨⟨⟨a.val, hNM a.property⟩, a.property⟩, rfl⟩
  let e := AlgEquiv.ofBijective q ⟨q.injective, hq⟩
  let Q : FiniteLayer L M := ⟨Q₀, Module.Finite.equiv e.symm.toLinearEquiv⟩
  have hmap : FiniteLayer.map M.val Q = N := by
    apply Subtype.ext
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact hb
    · intro ha
      exact ⟨⟨a, hNM ha⟩, ha, rfl⟩
  intro z hz
  obtain ⟨a, rfl⟩ := (mem_separableNormUnionFiniteImage K L Ω p N z).mp hz
  obtain ⟨b, hb⟩ := (normLimitMulEquiv (e.restrictScalars K)).surjective a
  refine ⟨separableNormUnionOf K L M p Q b, ?_⟩
  change separableNormUnionMap K L M p Ω M.val
    (separableNormUnionOf K L M p Q b) = _
  rw [separableNormUnionMap_of, separableNormUnionStageMap_apply]
  have h := separableNormUnionOf_transport_congr K L p Ω
    (FiniteLayer.map M.val Q) N ((FiniteLayer.equivMap M.val Q).restrictScalars K)
    (e.restrictScalars K) hmap (fun _ => rfl) b
  exact h.trans (congrArg (separableNormUnionOf K L Ω p N) hb)

end OriginalImages

section Reconstruction

variable (K : Type*) [NontriviallyNormedField K] [IsCompleteDiscreteValuedField K]
    [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]
    (L Ω : Type*) [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
    [Algebra.IsSeparable K L] [IsSepClosure L Ω]
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring) p]
    [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- Every actual intermediate field of the same canonical closure union
is the literal image of the canonical union of an original intermediate
field. The original field is the directed supremum of the unique finite
original preimages, with inclusion supplied by finite reconstruction. -/
theorem separableNormUnion_exists_subfield_preimage :
    letI := normLimitField K L p
    letI := separableNormUnionField K L Ω p
    letI := separableNormUnionAlgebra K L Ω p
    letI : Module (NormLimit K L) (SeparableNormUnion K L Ω p) := Algebra.toModule
    letI : MulAction (NormLimit K L) (SeparableNormUnion K L Ω p) :=
      (Algebra.toModule : Module (NormLimit K L)
        (SeparableNormUnion K L Ω p)).toDistribMulAction.toMulAction
    ∀ D : IntermediateField (NormLimit K L) (SeparableNormUnion K L Ω p),
      ∃ M : IntermediateField L Ω,
        letI := separableNormUnionField K L M p
        letI := separableNormUnionAlgebra K L M p
        (separableNormUnionAlgMap K L M p Ω M.val).fieldRange = D := by
  classical
  let := normLimitField K L p
  let := separableNormUnionField K L Ω p
  let := separableNormUnionAlgebra K L Ω p
  let : Module (NormLimit K L) (SeparableNormUnion K L Ω p) := Algebra.toModule
  let : MulAction (NormLimit K L) (SeparableNormUnion K L Ω p) :=
    (Algebra.toModule : Module (NormLimit K L)
      (SeparableNormUnion K L Ω p)).toDistribMulAction.toMulAction
  let : Algebra.IsSeparable (NormLimit K L) (SeparableNormUnion K L Ω p) :=
    separableNormUnion_isSeparable K L Ω p
  intro D
  have hpre (P : FiniteLayer (NormLimit K L) D) :
      ∃ N : FiniteLayer L Ω, separableNormUnionFiniteImage K L Ω p N =
        (FiniteLayer.map D.val P).val := by
    exact (separableNormUnion_existsUnique_finite_subfield_preimage
      K L Ω p (FiniteLayer.map D.val P).val).exists
  choose A hA using hpre
  have hmono : Monotone A := by
    intro P Q hPQ
    apply (separableNormUnionFiniteImage_le_iff K L Ω p (A P) (A Q)).mp
    rw [hA P, hA Q]
    exact FiniteLayer.map_mono D.val hPQ
  have hdir : Directed (· ≤ ·) (fun P => (A P).val) := by
    intro P Q
    exact ⟨FiniteLayer.sup P Q, hmono (FiniteLayer.le_sup_left P Q),
      hmono (FiniteLayer.le_sup_right P Q)⟩
  let M : IntermediateField L Ω := ⨆ P, (A P).val
  let := separableNormUnionField K L M p
  let := separableNormUnionAlgebra K L M p
  let j := separableNormUnionAlgMap K L M p Ω M.val
  refine ⟨M, ?_⟩
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨Q, a, rfl⟩ := separableNormUnion_exists_stage K L M p x
    let Q' := FiniteLayer.map M.val Q
    have hQ' : Q'.val ≤ M := by
      rintro b ⟨c, hc, rfl⟩
      exact c.property
    obtain ⟨P, hQP⟩ := FiniteLayer.exists_le_of_le_directed_iSup
      (fun P => (A P).val) hdir Q' hQ'
    have hQA := (separableNormUnionFiniteImage_le_iff K L Ω p Q' (A P)).mpr hQP
    have hAD : separableNormUnionFiniteImage K L Ω p (A P) ≤ D := by
      rw [hA P]
      rintro b ⟨c, hc, rfl⟩
      exact c.property
    apply hAD
    apply hQA
    change separableNormUnionMap K L M p Ω M.val
      (separableNormUnionOf K L M p Q a) ∈ _
    rw [separableNormUnionMap_of]
    exact (mem_separableNormUnionFiniteImage K L Ω p Q' _).mpr ⟨_, rfl⟩
  · intro hz
    obtain ⟨P, hP⟩ := FiniteLayer.exists_mem (L := NormLimit K L) (M := D) ⟨z, hz⟩
    have hzP : z ∈ (FiniteLayer.map D.val P).val := ⟨⟨z, hz⟩, hP, rfl⟩
    have hzA : z ∈ separableNormUnionFiniteImage K L Ω p (A P) :=
      (hA P).symm ▸ hzP
    exact separableNormUnionFiniteImage_le_fieldRange_of_le
      K L Ω p M (A P) (le_iSup (fun P => (A P).val) P) hzA

set_option synthInstance.maxHeartbeats 80000 in
-- TODO(F5): remove once `SeparableNormUnion` is a `def` with genuine instances; as an
-- `abbrev` of `DirectLimit`, instance search tries the generic `DirectLimit` instances first.
/-- Every actual separable algebraic target is the same canonical union
of an actual original intermediate field in the prescribed separable
closure. Both identifications are the actual canonical image maps. -/
theorem exists_separableNormUnion_algEquiv_of_separableClosure :
    letI := normLimitField K L p
    ∀ (F : Type*) [Field F] [Algebra (NormLimit K L) F]
      [Algebra.IsSeparable (NormLimit K L) F],
      ∃ M : IntermediateField L Ω,
        letI := separableNormUnionField K L M p
        letI := separableNormUnionAlgebra K L M p
        Nonempty (SeparableNormUnion K L M p ≃ₐ[NormLimit K L] F) := by
  let := normLimitField K L p
  intro F _ _ _
  let : IsSepClosure K Ω :=
    ⟨IsSepClosure.sep_closed L, Algebra.IsSeparable.trans K L Ω⟩
  let := separableNormUnionField K L Ω p
  let := separableNormUnionAlgebra K L Ω p
  let : IsSepClosed (SeparableNormUnion K L Ω p) :=
    separableNormUnion_isSepClosed K L Ω p
  let t : F →ₐ[NormLimit K L] SeparableNormUnion K L Ω p := IsSepClosed.lift
  obtain ⟨M, hM⟩ := separableNormUnion_exists_subfield_preimage
    K L Ω p t.fieldRange
  let := separableNormUnionField K L M p
  let := separableNormUnionAlgebra K L M p
  let j := separableNormUnionAlgMap K L M p Ω M.val
  exact ⟨M, ⟨j.equivFieldRange.trans ((IntermediateField.equivOfEq hM).trans
    t.equivFieldRange.symm)⟩⟩

/-- The actual algebraic essential image with no prescribed original
closure: the standard original separable closure supplies that choice. -/
abbrev exists_separableNormUnion_algEquiv :=
  exists_separableNormUnion_algEquiv_of_separableClosure
    K L (SeparableClosure L) p

end Reconstruction

end FontaineWintenberger
