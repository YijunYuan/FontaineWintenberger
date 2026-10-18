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
# Actual algebraic essential image of the original relative field of norms

Unique reconstruction of finite original subfields gives a directed family.
Its original intermediate-field supremum has precisely the prescribed image
under the same canonical relative field of norms embedding.
-/

@[expose] public section

noncomputable section

namespace FontaineWintenberger

section DirectedFields

variable {L Ω : Type*} [Field L] [Field Ω] [Algebra L Ω]

/-- Every finite original subfield of a directed union lies in a single
member, by the compactness of its finitely generated intermediate field. -/
theorem FiniteIntermediateField.exists_le_of_le_directed_iSup {ι : Type*} [Nonempty ι]
    (A : ι → IntermediateField L Ω) (hA : Directed (· ≤ ·) A)
    (Q : FiniteIntermediateField L Ω) (hQ : Q.val ≤ ⨆ i, A i) :
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

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
    (L Ω : Type*) [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable L Ω]

local notation "p" => residueChar K

variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- A finite original subfield contained in an original intermediate field
has its entire canonical norm-field image in that intermediate union's
original inclusion map. -/
theorem RelFieldOfNorms.finiteImage_le_fieldRange_of_le
    (M : IntermediateField L Ω) (N : FiniteIntermediateField L Ω) (hNM : N.val ≤ M) :
    RelFieldOfNorms.finiteImage K L Ω N ≤
      (RelFieldOfNorms.algMap K L M Ω M.val).fieldRange := by
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
  let Q : FiniteIntermediateField L M := ⟨Q₀, Module.Finite.equiv e.symm.toLinearEquiv⟩
  have hmap : FiniteIntermediateField.map M.val Q = N := by
    apply Subtype.ext
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact hb
    · intro ha
      exact ⟨⟨a, hNM ha⟩, ha, rfl⟩
  intro z hz
  obtain ⟨a, rfl⟩ := (mem_relFieldOfNormsFiniteImage K L Ω N z).mp hz
  obtain ⟨b, hb⟩ := (FieldOfNorms.mulEquiv (e.restrictScalars K)).surjective a
  refine ⟨RelFieldOfNorms.of K L M Q b, ?_⟩
  change RelFieldOfNorms.map K L M Ω M.val
    (RelFieldOfNorms.of K L M Q b) = _
  rw [RelFieldOfNorms.map_of, RelFieldOfNorms.stageMap_apply]
  have h := RelFieldOfNorms.of_transport_congr K L Ω
    (FiniteIntermediateField.map M.val Q) N ((FiniteIntermediateField.equivMap M.val
        Q).restrictScalars K)
    (e.restrictScalars K) hmap (fun _ => rfl) b
  exact h.trans (congrArg (RelFieldOfNorms.of K L Ω N) hb)

end OriginalImages

section Reconstruction

variable (K : Type*) [NontriviallyNormedField K] [IsPerfectResidueLocalField K]
    (L Ω : Type*) [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
    [Algebra.IsSeparable K L] [IsSepClosure L Ω]

local notation "p" => residueChar K

variable [IsAPF K L] [Fact (¬ Module.Finite K L)]

/-- Every actual intermediate field of the same canonical closure union
is the literal image of the relative field of norms of an original intermediate
field. The original field is the directed supremum of the unique finite
original preimages, with inclusion supplied by finite reconstruction. -/
theorem RelFieldOfNorms._exists_subfield_preimage :
    ∀ D : IntermediateField (FieldOfNorms K L) (RelFieldOfNorms K L Ω),
      ∃ M : IntermediateField L Ω,
        (RelFieldOfNorms.algMap K L M Ω M.val).fieldRange = D := by
  classical
  let : Algebra.IsSeparable (FieldOfNorms K L) (RelFieldOfNorms K L Ω) :=
    RelFieldOfNorms._isSeparable K L Ω
  intro D
  have hpre (P : FiniteIntermediateField (FieldOfNorms K L) D) :
      ∃ N : FiniteIntermediateField L Ω, RelFieldOfNorms.finiteImage K L Ω N =
        (FiniteIntermediateField.map D.val P).val := by
    exact (RelFieldOfNorms._existsUnique_finite_subfield_preimage
      K L Ω (FiniteIntermediateField.map D.val P).val).exists
  choose A hA using hpre
  have hmono : Monotone A := by
    intro P Q hPQ
    apply (RelFieldOfNorms.finiteImage_le_iff K L Ω (A P) (A Q)).mp
    rw [hA P, hA Q]
    exact FiniteIntermediateField.map_mono D.val hPQ
  have hdir : Directed (· ≤ ·) (fun P => (A P).val) := by
    intro P Q
    exact ⟨FiniteIntermediateField.sup P Q, hmono (FiniteIntermediateField.le_sup_left P Q),
      hmono (FiniteIntermediateField.le_sup_right P Q)⟩
  let M : IntermediateField L Ω := ⨆ P, (A P).val
  let j := RelFieldOfNorms.algMap K L M Ω M.val
  refine ⟨M, ?_⟩
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨Q, a, rfl⟩ := RelFieldOfNorms._exists_stage K L M x
    let Q' := FiniteIntermediateField.map M.val Q
    have hQ' : Q'.val ≤ M := by
      rintro b ⟨c, hc, rfl⟩
      exact c.property
    obtain ⟨P, hQP⟩ := FiniteIntermediateField.exists_le_of_le_directed_iSup
      (fun P => (A P).val) hdir Q' hQ'
    have hQA := (RelFieldOfNorms.finiteImage_le_iff K L Ω Q' (A P)).mpr hQP
    have hAD : RelFieldOfNorms.finiteImage K L Ω (A P) ≤ D := by
      rw [hA P]
      rintro b ⟨c, hc, rfl⟩
      exact c.property
    apply hAD
    apply hQA
    change RelFieldOfNorms.map K L M Ω M.val
      (RelFieldOfNorms.of K L M Q a) ∈ _
    rw [RelFieldOfNorms.map_of]
    exact (mem_relFieldOfNormsFiniteImage K L Ω Q' _).mpr ⟨_, rfl⟩
  · intro hz
    obtain ⟨P, hP⟩ := FiniteIntermediateField.exists_mem (L := FieldOfNorms K L) (M := D) ⟨z, hz⟩
    have hzP : z ∈ (FiniteIntermediateField.map D.val P).val := ⟨⟨z, hz⟩, hP, rfl⟩
    have hzA : z ∈ RelFieldOfNorms.finiteImage K L Ω (A P) :=
      (hA P).symm ▸ hzP
    exact RelFieldOfNorms.finiteImage_le_fieldRange_of_le
      K L Ω M (A P) (le_iSup (fun P => (A P).val) P) hzA

/-- Every actual separable algebraic target is the same relative field of norms
of an actual original intermediate field in the prescribed separable
closure. Both identifications are the actual canonical image maps. -/
theorem exists_relFieldOfNorms_algEquiv_of_separableClosure :
    ∀ (F : Type*) [Field F] [Algebra (FieldOfNorms K L) F]
      [Algebra.IsSeparable (FieldOfNorms K L) F],
      ∃ M : IntermediateField L Ω,
        Nonempty (RelFieldOfNorms K L M ≃ₐ[FieldOfNorms K L] F) := by
  intro F _ _ _
  let : IsSepClosure K Ω :=
    ⟨IsSepClosure.sep_closed L, Algebra.IsSeparable.trans K L Ω⟩
  let : IsSepClosed (RelFieldOfNorms K L Ω) :=
    RelFieldOfNorms._isSepClosed K L Ω
  let t : F →ₐ[FieldOfNorms K L] RelFieldOfNorms K L Ω := IsSepClosed.lift
  obtain ⟨M, hM⟩ := RelFieldOfNorms._exists_subfield_preimage
    K L Ω t.fieldRange
  let j := RelFieldOfNorms.algMap K L M Ω M.val
  exact ⟨M, ⟨j.equivFieldRange.trans ((IntermediateField.equivOfEq hM).trans
    t.equivFieldRange.symm)⟩⟩

/-- The actual algebraic essential image with no prescribed original
closure: the standard original separable closure supplies that choice. -/
abbrev exists_relFieldOfNorms_algEquiv :=
  exists_relFieldOfNorms_algEquiv_of_separableClosure
    K L (SeparableClosure L)

end Reconstruction

end FontaineWintenberger
