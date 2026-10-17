# Finite ramification API audit

The pinned mathlib provides valuation, inertia, ideal ramification indices,
normal restriction and finite inverse limits. Integer lower groups, their
normalized integral-valuation bridge, and the intrinsic order identities are
implemented in `FontaineWintenberger/Ramification/{Lower,Valuation}.lean`.
Integral generation and its every-uniformizer total-ramification clause are
proved for arbitrary chosen compatible finite separable extensions. The canonical
inertia fixed field is proved unramified, with its actual residue isomorphism.
Actual infinite upper groups,
ordinary finite/infinite Galois restriction and their canonical inverse limit are proved.
Finite Herbrand lower/upper quotients, transitivity and the inverse index integral
are proved. The actual
fixed-field Tate average, residue quotient and inertia cardinality are proved.
The actual spectral integral-closure, finite-free DVR and Henselian
foundations are now implemented in `FontaineWintenberger/LocalField/`.
Their mathematical route is in `src/chapters/ramification.tex`.

## Revision and scope

- Lean: `leanprover/lean4:v4.35.0`.
- mathlib: `f0b4c8150aa0dbc758aff1291410c5ae335aff3a`, verified against
  both `lake-manifest.json` and the checkout at workspace-root
  `.lake/packages/mathlib`.
- Fields: complete discrete valuation, **arbitrary perfect** residue field
  of characteristic `p`. Finite residue fields are not a standing hypothesis.
- Evidence: Horizon declaration-index searches followed by inspection of
  the pinned source signatures and checked project consumers. The table
  distinguishes upstream APIs from the proved project bridges.

From the project directory, repeat the initial lookup with
`"$HORIZON_BIN" search "ramification" --json`, then name searches such as
`"$HORIZON_BIN" search --name inertia --json` and
`"$HORIZON_BIN" search --name restrictNormalHom --json`.
Source paths below are relative to the pinned mathlib checkout.

## Existing APIs and their boundaries

| Mathematical role | Module and declarations | Hypotheses and integration boundary |
| --- | --- | --- |
| Decomposition and inertia for a valuation ring | `RingTheory/Valuation/RamificationGroup.lean`: `ValuationSubring.decompositionSubgroup`, `ValuationSubring.inertiaSubgroup` | Fields `K`, `L`, an algebra `K → L`, and a valuation subring of `L`. Inertia is a subgroup of the decomposition subgroup. Identify the latter with the full Galois group using invariance of the extended valuation. |
| Kernel of action modulo an ideal | `RingTheory/Ideal/Defs.lean`: `Ideal.inertia`, `Ideal.mem_inertia` | Ring action by a group; membership means `∀ x, σ • x - x ∈ I`. For the valuation ring, `(𝔪 ^ (n + 1)).inertia G` is a natural existing abstraction for the integer lower group. Establish the ring action and bridge ideal-power membership to normalized valuation inequalities. |
| Subgroup restriction and monotonicity | `Algebra/Group/Subgroup/Basic.lean`: `AddSubgroup.inertia_mono`, `AddSubgroup.subgroupOf_inertia`, `AddSubgroup.inertia_map_subtype` | `inertia_map_subtype` identifies the image of subgroup inertia with ambient inertia intersected with the subgroup. Normality additionally needs invariance of the ideal under the ambient action. |
| Inertia under quotient restriction | `RingTheory/Invariant/Basic.lean`: `Ideal.map_inertia_of_surjective`, `Ideal.inertia_quotient` | Compatible semiring actions on `R → S`, an invariant subring for a finite subgroup `H`, prime `q` lying over `p`, and a surjective group map whose kernel contains `H`. The quotient version also assumes `H.Normal`. This is the **zero-level** theorem. Higher ideal powers need not be prime and restriction rescales valuations, so this theorem does not establish Herbrand compatibility. |
| Ramification index and residue degree | `RingTheory/RamificationInertia/Ramification.lean`: `Ideal.ramificationIdx`, `Ideal.ramificationIdx_tower`; `RingTheory/RamificationInertia/Inertia.lean`: `Ideal.inertiaDeg` | The index is defined by a localized module length, with a junk value for nonprime ideals. The tower identity assumes lying-over and flatness in a scalar tower. Relate this index to the normalized-valuation scaling factor. The older `Ideal.ramificationIdx'` is a separate ideal-power definition. |
| Inertia cardinality | `NumberTheory/RamificationInertia/Galois.lean`: `Ideal.card_inertia_eq_ramificationIdxIn`, `Ideal.card_stabilizer_eq`, `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn` | Finite Galois group action on a finite flat extension of domains, appropriate prime ideals and lying-over; inertia cardinality also requires `Algebra.HasSeparableResidueFieldsAt`. Localize to the unique valuation-ring prime and supply the integral-closure/action bridges. |
| Extension, uniqueness and invariance of norms | `Analysis/Normed/Unbundled/SpectralNorm.lean`: `spectralNorm_unique`, `spectralMulAlgNorm`, `spectralNorm.normedField`, `spectralNorm.completeSpace`, `spectralNorm_eq_of_equiv` | The extension/uniqueness results use a complete nontrivially normed ultrametric base and an algebraic field extension. Completeness of the extension additionally uses finite dimensionality. `spectralNorm_eq_of_equiv` itself needs only a normed base field and a `K`-algebra automorphism of the extension field, without completeness. Bridge the spectral norm to the discrete normalized valuations used here. |
| Compatible valuation rings | `RingTheory/Valuation/Extension.lean`: `Valuation.HasExtension`, `Valuation.instAlgebra_valuationSubring`, `Valuation.val_map_le_iff`, `Valuation.val_map_lt_iff`, `Valuation.val_map_le_one_iff` | `HasExtension` records equivalence of valuations after comapping, rather than equality of normalized values. The file supplies the valuation-ring algebra, local hom and maximal-ideal lying-over. |
| Integral closure finiteness | `RingTheory/DedekindDomain/IntegralClosure.lean`: `IsIntegralClosure.finite` | Finite separable fraction-field extension over an integrally closed Noetherian domain. This does not by itself identify the integral closure with the selected extended valuation ring. |
| Monogenicity in the unramified stage | `RingTheory/LocalRing/Etale.lean`: `IsLocalRing.exists_adjoin_eq_top` | Finite faithful formally unramified extension of commutative local rings. It does not assert monogenicity of arbitrary ramified valuation-ring extensions. |
| Eisenstein integral generation | `RingTheory/Polynomial/Eisenstein/IsIntegral.lean`: `mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt` | Integrally closed domain `R` with fraction field `K`, a compatible field extension, an integral power-basis generator, prime `p`, and an Eisenstein minimal polynomial at `(p)`. Removes a power-of-`p` denominator for an integral element already known to lie in the generated algebra after multiplication. The local-field structural bridge is still needed. |
| Galois restriction | `FieldTheory/Normal/Defs.lean`: `AlgEquiv.restrictNormalHom`; `FieldTheory/Normal/Basic.lean`: `AlgEquiv.restrictNormalHom_surjective` | Compatible field-algebra towers. Surjectivity holds for restriction from a normal ambient extension to a normal intermediate extension; no finite-dimensional assumption is needed. |
| Profinite Galois realization | `FieldTheory/Galois/Profinite.lean`: `InfiniteGalois.restrictNormalHom_continuous`, `InfiniteGalois.profiniteGalGrpIsoLimit` | Supplies continuous restriction and the inverse-limit description over finite Galois intermediate extensions. |
| Surjective finite inverse-limit projections | `CategoryTheory/CofilteredSystem.lean`: `CategoryTheory.Functor.eval_section_surjective_of_surjective` | Cofiltered or empty index category, finite nonempty object sets, and surjective transition maps. Once finite upper compatibility is proved, this supplies the inverse-system compactness step without a new general theorem. |

`NumberTheory/LocalField/Basic.lean` also supplies useful DVR and completeness
instances for `IsNonarchimedeanLocalField`, but that class entails finite
residue fields and cannot alone represent the scope of this blueprint.

## Project bridges beyond the pinned mathlib API

`RingTheory/Valuation/RamificationGroup.lean` explicitly lists
“Define higher ramification groups in lower numbering” as a TODO. Declaration
searches found no higher filtration or Herbrand theorem, and a whole-tree
search for the known string `Herbrand` returned no occurrence at this pin.
The project now supplies the following route beyond those pinned APIs:

1. The complete discrete valuation extension model and its bridges to
   integral closure, normalized ramification index and the full Galois action.
   No turnkey declaration combining all these structures was located; this
   is a search result, rather than a claim that every constituent is absent.
2. Integer lower groups, the order function, generator evaluation and the
   valuation/ideal membership bridge; subgroup compatibility reuses inertia.
3. Integral generators in the full ramified setting and Tate's coset averaging
   identity, proved from the actual integral generators and conjugate products.
4. Real ceiling indexing, positive piecewise affine Herbrand functions and
   inverses, the finite-sum formula, the largest-order formula in a coset,
   and transitivity. Finite affine partitions supply the required integral
   formulas directly.
5. Upper quotient compatibility, then absolute projections and APF index
   identities using the existing finite inverse-limit infrastructure.

The blueprint takes the finite CDVF structure theorem, Hensel's lemma,
Nakayama's lemma and ordinary Galois/profinite theory as foundational inputs.
The project supplies the required local structural bridges as actual Lean
producers; these foundations are not missing theorem hypotheses in a context record.

## Producer and consumer route

All arrows below represent a dependency actually used in a written proof.

| Producer | Substantive consumer |
| --- | --- |
| `fw:integral-generator` | `fw:lower-ramification-properties`, `fw:coset-ramification-average` evaluate differences on a generator. |
| `fw:local-inertia-size` and `fw:fixed-field-integers` | `fw:coset-ramification-average` replaces the canonical relative index by the actual subgroup inertia order. |
| `fw:inertia-quotient` and `fw:ramification-subgroups` | `fw:uniformizer-ramification` evaluates inertia on any uniformizer. |
| `fw:coset-ramification-average` and `fw:herbrand-functions` | `fw:herbrand-coset-max` identifies the quotient order with a Herbrand value. |
| `fw:herbrand-coset-max` | `fw:herbrand-lower-quotients` converts coset membership to the changed lower index. |
| `fw:herbrand-lower-quotients` | `fw:herbrand-transitivity` compares slopes through an exact sequence of lower groups. |
| `fw:herbrand-lower-quotients` and `fw:herbrand-functions` | `fw:ramification-fixed-quotient` proves the actual quotient truncation and trivial tail for a lower fixed group. |
| `fw:herbrand-transitivity` | `fw:herbrand-quotients` identifies the two upper indices. |
| `fw:herbrand-quotients` | `fw:absolute-upper-projections` establishes finite satisfiability of prescribed restriction conditions. |
| `fw:absolute-upper-projections` and `fw:upper-inverse-integral` | `fw:finite-apf-indices` proves equality of the absolute index integral and the finite inverse function; `fw:galois-apf-criterion` identifies APF with finite-level upper openness. |


The spectral norm is an explicitly attached imported mathlib boundary. The
project proves that the spectral integer ring is the actual integral closure,
and supplies its finite-free, DVR, Henselian and monogenic properties. It then
identifies these with any compatible original extension valuation ring.
No finite residue-field hypothesis is introduced by these bridges.

## Proved project producers

| Producer group | Actual result and downstream use |
| --- | --- |
| `LocalField/` and `Ramification/{Lower,Valuation,Index,Tower,Degree}.lean` | Original integer rings, ideal-inertia lower groups, intrinsic orders, normalized index scaling, tower multiplicativity, fundamental degree and every-uniformizer total-ramification generation. These support generator evaluation and the finite ramification calculations. |
| `Ramification/{Inertia,InertiaFixedField,FixedField,Tate,Coset}.lean` | Actual residue quotient/inertia cardinality, unramified inertia fixed field, fixed-field integers, conjugate factorization and Tate coset averaging with canonical denominators. |
| `Ramification/{Real,Herbrand,HerbrandOrder,HerbrandAffine,CosetMax,HerbrandQuotient,HerbrandTransitivity,Upper,HerbrandInverse}.lean` | Real lower indexing, integral/sum Herbrand formulas, continuous inverses, affine partitions, coset maxima, quotient compatibility and transitivity. All 85 finite ramification source obligations are checked. |
| `Ramification/{FiniteRestriction,Absolute,InfiniteRestriction,UpperLimit,AbsoluteGalois}.lean` | Coherent finite restrictions, actual infinite upper groups, onto ordinary Galois projections and the canonical inverse-limit description. |
| `APF/` | Abstract separable APF via actual embedding existence/conjugacy; intrinsic index integrals, bounds, strict APF and all four inheritance clauses. General finite-base/finite-extension equivalences do not assume a norm or normality on the abstract top field. |
| Different, trace, tame and prime-tower modules in `Ramification/` | Exact different/trace formulas, actual prime-degree breaks, wild/tame structure and nonnormal base change. These produce both finite wild norm estimates and intrinsic Herbrand norm continuity. |
| Norm estimates, cofinal towers and reconstruction in `FieldOfNorms/` | Addition, characteristic-p field operations, stable valuation, completeness, original DVR, prescribed coefficient embedding and residue isomorphism on the same original multiplicative norm limit. |
| Finite descent and norm base change in `Algebra/` | Original intersection/compositum fields, tensor determinant identity, cofinal good finite pairs and actual finite-inclusion maps. These feed the full arbitrary-embedding functor. |
| Finite functor, approximate roots and embedding correspondence in `FieldOfNorms/` | Identity/composition, degree/separability, full finite/algebraic Hom correspondence, original Galois/Krull maps and ramification transfer, including nonstable finite layers and every uniformizer. |
| Separable norm union and categorical modules in `FieldOfNorms/` | Actual separable closedness, unique finite-subfield reconstruction, finite and separable-algebraic essential image, intrinsic absolute Galois equivalence and the original fully faithful categorical equivalence. |
| `FieldOfNorms/NormUnionAbsoluteAction.lean` and `FieldOfNorms/NormUnionGalois{Action,RestrictionFun,Restriction,Equiv,Isomorphism}.lean` | The original ambient action, actual stable-base-image subgroup, original restriction homomorphism, genuine relative kernel and the actual ambient absolute-Galois group isomorphism, with literal base and relative-map formulas. |

These producers retain the original fields, norm-compatible families, finite
stages, structure embeddings and normalized valuations. The arbitrary perfect
residue-field scope is preserved. The optional Sen/Lie route (`fw:lie-apf`, `ft:inertia-residue`,
`ft:lie-structure`) and two unused wild/tame aggregates
(`fw:apf-wild-ramification`, `fw:nonnormal-tame-norm-reduction`) remain explicitly
unformalized outside the chosen instruction route. None supplies a hypothesis
of these results.

Open PRs and Akwardbro/RamificationGroup were mathematical/API references.
No wholesale PR code or external ramification dependency was imported.

## Validation

The public roots expose the checked declarations across all three projects.
The workspace-root `horizon check` and
`horizon check --lean scripts/AuditAxioms.lean` reproduce the configured build
and final public type/transitive-axiom audit. Its exact target set was generated
from actual compiler indices for the ambient integration plus the 42 actual
Theorem A coefficient APIs. Their transitive dependencies use only `propext`,
`Classical.choice` and `Quot.sound`. Generated notation syntax is excluded from
the mathematical source API count; cached proof constants remain covered
transitively. Compiled-value occurrences require separate semantic
adjudication before they count as substantive dependency edges.

`python3 scripts/sync_graphs.py` and `python3 scripts/check_setup.py` from the
workspace root validate graph structure and pinned source provenance. Each
project's `blueprint/src` builds with
`latexmk -xelatex -outdir=../build -interaction=nonstopmode -halt-on-error print.tex`.
All cited source anchors resolve in `references/manifest.yaml`.
Document/graph checks establish structure and provenance; faithful Lean builds,
exact axiom audits and matching source/semantic reviews establish proof evidence.
