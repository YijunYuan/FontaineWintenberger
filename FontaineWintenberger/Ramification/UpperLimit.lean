module

public import FontaineWintenberger.Ramification.Absolute

/-!
# The canonical inverse limit of actual finite upper ramification groups

The objects are actual finite upper subgroups with their inherited Krull
topology. The limit is mathlib's `ProfiniteGrp.limit`.
-/

@[expose] public section

namespace FontaineWintenberger

open CategoryTheory Opposite

variable (K Ω : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [Field Ω] [Algebra K Ω]
variable [IsDiscreteValuationRing (NormedField.valuation (K := K)).valuationSubring]
variable [PerfectField (IsLocalRing.ResidueField
      (NormedField.valuation (K := K)).valuationSubring)]

/-- Ordinary finite restriction, restricted to the actual upper subgroups. -/
noncomputable def finiteUpperRamificationGroupMap
    {A B : (FiniteGaloisIntermediateField K Ω)ᵒᵖ} (f : A ⟶ B)
    (u : ℝ) (hu : -1 ≤ u) :
    upperRamificationGroup (R := spectralIntegerRing K A.unop) (A.unop ≃ₐ[K] A.unop) u →ₜ*
      upperRamificationGroup (R := spectralIntegerRing K B.unop) (B.unop ≃ₐ[K] B.unop) u where
  toFun s := ⟨(finGaloisGroupMap f).hom.hom s.val, by
    rw [← finGaloisGroupMap_map_upperRamificationGroup K Ω f u hu]
    exact Subgroup.mem_map.mpr ⟨s.val, s.property, rfl⟩⟩
  map_one' := Subtype.ext (map_one (finGaloisGroupMap f).hom.hom)
  map_mul' s t := Subtype.ext (map_mul (finGaloisGroupMap f).hom.hom s.val t.val)
  continuous_toFun := continuous_of_discreteTopology

@[simp]
theorem coe_finiteUpperRamificationGroupMap
    {A B : (FiniteGaloisIntermediateField K Ω)ᵒᵖ} (f : A ⟶ B)
    (u : ℝ) (hu : -1 ≤ u)
    (s : upperRamificationGroup (R := spectralIntegerRing K A.unop)
      (A.unop ≃ₐ[K] A.unop) u) :
    (finiteUpperRamificationGroupMap K Ω f u hu s).val =
      (finGaloisGroupMap f).hom.hom s.val := rfl

theorem finiteUpperRamificationGroupMap_id (E : (FiniteGaloisIntermediateField K Ω)ᵒᵖ)
    (u : ℝ) (hu : -1 ≤ u) :
    finiteUpperRamificationGroupMap K Ω (𝟙 E) u hu = ContinuousMonoidHom.id _ := by
  apply ContinuousMonoidHom.ext
  intro s
  apply Subtype.ext
  change (finGaloisGroupMap (𝟙 E)).hom.hom s.val = s.val
  rw [finGaloisGroupMap.map_id]
  rfl

theorem finiteUpperRamificationGroupMap_comp
    {A B C : (FiniteGaloisIntermediateField K Ω)ᵒᵖ} (f : A ⟶ B) (g : B ⟶ C)
    (u : ℝ) (hu : -1 ≤ u) :
    finiteUpperRamificationGroupMap K Ω (f ≫ g) u hu =
      (finiteUpperRamificationGroupMap K Ω g u hu).comp
        (finiteUpperRamificationGroupMap K Ω f u hu) := by
  apply ContinuousMonoidHom.ext
  intro s
  apply Subtype.ext
  change (finGaloisGroupMap (f ≫ g)).hom.hom s.val =
    (finGaloisGroupMap g).hom.hom ((finGaloisGroupMap f).hom.hom s.val)
  rw [finGaloisGroupMap.map_comp]
  rfl

/-- The actual finite upper groups and their ordinary restriction maps. -/
noncomputable def finiteUpperRamificationGroupFunctor (u : ℝ) (hu : -1 ≤ u) :
    (FiniteGaloisIntermediateField K Ω)ᵒᵖ ⥤ ProfiniteGrp where
  obj E := ProfiniteGrp.of
    (upperRamificationGroup (R := spectralIntegerRing K E.unop) (E.unop ≃ₐ[K] E.unop) u)
  map f := ProfiniteGrp.ofHom (finiteUpperRamificationGroupMap K Ω f u hu)
  map_id E := ProfiniteGrp.Hom.ext (finiteUpperRamificationGroupMap_id K Ω E u hu)
  map_comp f g := ProfiniteGrp.Hom.ext (finiteUpperRamificationGroupMap_comp K Ω f g u hu)

/-- The canonical map from actual infinite upper automorphisms to the actual upper inverse limit. -/
noncomputable def upperRamificationToLimit (u : ℝ) (hu : -1 ≤ u) :
    upperRamificationGroupInfinite K Ω u →*
      ProfiniteGrp.limit (finiteUpperRamificationGroupFunctor K Ω u hu) where
  toFun s := ⟨fun E => ⟨s.val.restrictNormal E.unop,
      (mem_upperRamificationGroupInfinite K Ω u s.val).mp s.property E.unop⟩,
    fun {_ _} f => Subtype.ext ((InfiniteGalois.algEquivToLimit K Ω s.val).property f)⟩
  map_one' := by
    apply ProfiniteGrp.limit_ext
    intro E
    apply Subtype.ext
    exact map_one (AlgEquiv.restrictNormalHom E.unop)
  map_mul' s t := by
    apply ProfiniteGrp.limit_ext
    intro E
    apply Subtype.ext
    exact map_mul (AlgEquiv.restrictNormalHom E.unop) s.val t.val

/-- Forget upper membership while retaining the existing canonical compatible Galois tuple. -/
noncomputable def upperRamificationLimitForget (u : ℝ) (hu : -1 ≤ u) :
    ProfiniteGrp.limit (finiteUpperRamificationGroupFunctor K Ω u hu) →*
      ProfiniteGrp.limit (InfiniteGalois.asProfiniteGaloisGroupFunctor K Ω) where
  toFun q := ⟨fun E => (q.val E).val,
    fun {_ _} f => congrArg Subtype.val (q.property f)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem upperRamificationLimitForget_toLimit (u : ℝ) (hu : -1 ≤ u)
    (s : upperRamificationGroupInfinite K Ω u) :
    upperRamificationLimitForget K Ω u hu (upperRamificationToLimit K Ω u hu s) =
      InfiniteGalois.algEquivToLimit K Ω s.val := rfl

theorem continuous_upperRamificationToLimit (u : ℝ) (hu : -1 ≤ u) :
    Continuous (upperRamificationToLimit K Ω u hu) := by
  rw [continuous_induced_rng]
  apply continuous_pi
  intro E
  exact ((InfiniteGalois.restrictNormalHom_continuous E.unop.toIntermediateField).comp
    continuous_subtype_val).subtype_mk _

variable [IsGalois K Ω]

theorem upperRamificationToLimit_bijective (u : ℝ) (hu : -1 ≤ u) :
    Function.Bijective (upperRamificationToLimit K Ω u hu) := by
  constructor
  · intro s t h
    apply Subtype.ext
    apply (InfiniteGalois.mulEquivToLimit K Ω).injective
    change InfiniteGalois.algEquivToLimit K Ω s.val = InfiniteGalois.algEquivToLimit K Ω t.val
    exact congrArg (upperRamificationLimitForget K Ω u hu) h
  · intro q
    let g := (InfiniteGalois.mulEquivToLimit K Ω).symm (upperRamificationLimitForget K Ω u hu q)
    have hg : InfiniteGalois.algEquivToLimit K Ω g = upperRamificationLimitForget K Ω u hu q :=
      (InfiniteGalois.mulEquivToLimit K Ω).apply_symm_apply _
    have hgE (E : FiniteGaloisIntermediateField K Ω) :
        g.restrictNormal E = (q.val (op E)).val :=
      congrArg (fun r : ProfiniteGrp.limit (InfiniteGalois.asProfiniteGaloisGroupFunctor K Ω) =>
        r.val (op E)) hg
    have hgu : g ∈ upperRamificationGroupInfinite K Ω u := by
      rw [mem_upperRamificationGroupInfinite]
      intro E
      rw [hgE E]
      exact (q.val (op E)).property
    refine ⟨⟨g, hgu⟩, ?_⟩
    apply ProfiniteGrp.limit_ext
    intro E
    apply Subtype.ext
    exact hgE E.unop

/-- The actual upper group is canonically the existing inverse limit of its actual finite groups. -/
noncomputable def upperRamificationEquivToLimit (u : ℝ) (hu : -1 ≤ u) :
    upperRamificationGroupInfinite K Ω u ≃ₜ*
      ProfiniteGrp.limit (finiteUpperRamificationGroupFunctor K Ω u hu) := by
  let e := MulEquiv.ofBijective (upperRamificationToLimit K Ω u hu)
    (upperRamificationToLimit_bijective K Ω u hu)
  letI : CompactSpace (upperRamificationGroupInfinite K Ω u) :=
    isCompact_iff_compactSpace.mp (isCompact_upperRamificationGroupInfinite K Ω u)
  exact { e with
    continuous_toFun := continuous_upperRamificationToLimit K Ω u hu
    continuous_invFun :=
      Continuous.continuous_symm_of_equiv_compact_to_t2 (f := e.toEquiv)
        (continuous_upperRamificationToLimit K Ω u hu) }

/-- Every coordinate of the canonical equivalence is ordinary finite restriction. -/
@[simp]
theorem upperRamificationEquivToLimit_apply_val (u : ℝ) (hu : -1 ≤ u)
    (s : upperRamificationGroupInfinite K Ω u) (E : FiniteGaloisIntermediateField K Ω) :
    ((upperRamificationEquivToLimit K Ω u hu s).val (op E)).val =
      s.val.restrictNormal E := rfl

end FontaineWintenberger
