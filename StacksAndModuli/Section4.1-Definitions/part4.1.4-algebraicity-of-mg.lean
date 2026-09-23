module

public import StacksAndModuli.«Section4.1-Definitions».«part4.1.3-fiber-products»
public import StacksAndModuli.«Section2.1-Intro».«part2.1.4-hilbert-representability-via-quot»
public import StacksAndModuli.«Section3.1-Descent».«part3.1.6-local-properties»
public import StacksAndModuli.«Section6.1-Smooth».«part6.1.2-families-of-smooth-curves»
public import StacksAndModuli.«Section4.4-Equivalence-Relations».«part4.4.4-algebraicity»
public import StacksAndModuli.API.ClassifyingPrestack
public import StacksAndModuli.API.EtaleTargetLocal
public import StacksAndModuli.API.GeometricallyConnectedDescent
public import StacksAndModuli.API.RelativeDifferentialsAffineChart
public import StacksAndModuli.API.RepresentableSheafStackBridge
public import StacksAndModuli.API.SteinFactorizationObject
public import StacksAndModuli.API.ProjectiveLinearGroupPresheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksAndModuli.API.SmoothCancellationEtale
public import StacksAndModuli.API.SmoothRelativeDimensionDescent

/-!
# Algebraicity of `ℳ_g`

This module follows the end of the subsection "Algebraicity of quotient stacks" and the
subsection "Algebraicity of `ℳ_g`" of §4.1 (Definitions of
algebraic spaces and stacks) of *Stacks and Moduli*,
section label `sec:algebraic-spaces-and-stacks`.

Two earlier labels are continued here, because this is the first point in the library at
which the genus is available in usable form (it is supplied by §6.1, see the COMMENTARY
entry on the forward import):

* `ex:moduli-prestack-of-smooth-curves` (**Example 3.4.10**, §3.4) introduced the prestack
  of families of smooth curves and, as an abstract base-change-stable parameter `Q`, the
  genus refinement cutting out `ℳ_g`. `moduliOfCurves g` is that refinement made concrete.
* `prop:mg-is-a-stack` (**Proposition 3.5.14**, §3.5) asserts that `ℳ_g` is a stack over
  `Sch_ét` for `g ≥ 2`; its statement is recorded here for the same reason.

## Book-facing definitions

- `AlgebraicGeometry.Scheme.moduliOfCurves`: the prestack `ℳ_g` of families of smooth
  curves of genus `g` (continuing `ex:moduli-prestack-of-smooth-curves`).

## Supporting definitions for Theorem 4.1.17
- `AlgebraicGeometry.Scheme.tricanonicalDim`, `.tricanonicalRank`,
  `.tricanonicalHilbertPolynomial`: the numerical data of the tricanonical embedding used
  in the proof of Theorem 4.1.17 — the ambient `ℙ^{5g-6}`, the group `PGL_{5g-5}`, and the
  Hilbert polynomial `P(n) = (6n-1)(g-1)`.
- `AlgebraicGeometry.Scheme.tricanonicalHilbertScheme`: a projective scheme representing
  the corresponding fixed-polynomial Hilbert functor, supplied by Theorem 2.1.2.
- `AlgebraicGeometry.Scheme.tricanonicalUniversalCurve`: its universal closed family.
- `AlgebraicGeometry.Scheme.TricanonicalChartDimensionAgreesWithHilbertPolynomial`: the
  exact missing dimension-detection input for the tricanonical Hilbert open.
- `AlgebraicGeometry.Scheme.tricanonicalUniversalCurveRelativeDifferentials`: the actual
  relative differential sheaf of that universal family.
- `AlgebraicGeometry.Scheme.tricanonicalFiberwiseSmoothLocus`: the open subscheme of the
  Hilbert scheme over which the universal family is smooth.
- `AlgebraicGeometry.Scheme.tricanonicalGeometricallyConnectedFiberSet`: the exact set of
  Hilbert points whose universal fibres are geometrically connected.
- `AlgebraicGeometry.Scheme.tricanonicalGeometricallyConnectedOpenLocus`: the largest open
  over which the universal family is geometrically connected.

## Book results and supporting proof API

- `AlgebraicGeometry.Scheme.moduliOfCurves_isFiberedInGroupoids`: `ℳ_g` is a prestack
  (proved).
- `AlgebraicGeometry.Scheme.moduliOfCurvesι`: the inclusion `ℳ_g ↪ 𝔐` into the prestack of
  all families of smooth curves, and its fullness — the "full subcategory" clause of
  Example 3.4.10 (proved).
- `isLocal_representableByPropertyULift_smoothCurveGenus_of_effectiveRepresentability`:
  effective scheme descent plus target-locality of the curve conditions gives the exact
  locality hypothesis needed for the representable-sheaf stack reduction.
- `smoothCurveGenusProperty_isLocalAtTarget_etale_of_genusDescent`: all conditions except
  fixed genus are already etale-local; the remaining hypothesis is stated only for smooth
  proper geometrically connected curve families.
- `isStack_moduliOfCurves_of_representableSheafDescent`: that locality hypothesis implies
  the stack assertion, using the relative-Yoneda equivalence internally.
- `AlgebraicGeometry.Scheme.isStack_moduliOfCurves`: **Proposition 3.5.14**
  (`prop:mg-is-a-stack`) — statement, proof an outstanding obligation.
- `AlgebraicGeometry.Scheme.isAlgebraicStack_moduliOfCurves`: **Theorem 4.1.17**
  (`thm:mg-is-algebraic`) — derived from Algebraicity of Quotients by Groupoids
  (Theorem 4.4.13, a forward import of §4.4) applied to the single outstanding
  obligation `exists_smooth_groupoid_presentation_moduliOfCurves`.
- `AlgebraicGeometry.Scheme.tricanonicalUniversalCurveπ_restrict_fiberwiseSmoothLocus_smooth`:
  the universal Hilbert family is smooth over its fibrewise-smooth open locus (proved).
- `AlgebraicGeometry.Scheme.tricanonicalUniversalCurveπ_restrict_smoothGeometricallyConnectedLocus`:
  over the intersection of the smooth locus and the maximal geometrically connected open,
  the universal family is both smooth and geometrically connected (proved).
- `AlgebraicGeometry.Scheme.tricanonicalSmoothLocus_smoothOfRelativeDimension_one_reduction`:
  the exact chart-dimension/Hilbert-degree comparison implies that this family is smooth
  of relative dimension one (proved conditionally).
- `AlgebraicGeometry.Scheme.tricanonicalSmoothLocus_affineDifferentials_reduction`:
  smoothness supplies standard-smooth affine charts, on which the two explicit affine
  comparison obligations imply finite local freeness of the relative differentials.
- `AlgebraicGeometry.Scheme.tricanonicalSmoothLocus_globalDifferentials_reduction`:
  adding the explicit chart-to-global compatibility transports finite local freeness back
  to the restriction of the global relative differential sheaf.
- `AlgebraicGeometry.Scheme.tricanonicalSmoothLocus_rankOneDifferentials_reduction`:
  the analogous rank-one reduction, conditional on the precise existing property
  `SmoothOfRelativeDimension 1`.
- `AlgebraicGeometry.Scheme.actionQuotientMap`: **Exercise 4.1.16**
  (`exer:morphisms-of-quotient-stacks`), the morphism `[U/G] → [V/G]` induced by a
  `G`-equivariant morphism, over `BG` (proved).
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme

section ExerMorphismsOfQuotientStacks

open CategoryTheory CategoryTheory.MonObj

/-- **Exercise 4.1.16** (`exer:morphisms-of-quotient-stacks`): a `G`-equivariant morphism
`U ⟶ V` of `S`-schemes induces a morphism of quotient stacks `[U/G] ⟶ [V/G]`.

On objects — a principal `G`-bundle `P → T` together with a `G`-equivariant map `P → U` —
the induced morphism postcomposes the equivariant map with `φ`; the bundle, and hence the
image in `BG`, is untouched. That is the content of `actionQuotientMap_comp_forget` below,
which is the "morphism over `BG`" half of the exercise. -/
noncomputable def actionQuotientMap {S : Scheme.{u}} {G : CategoryTheory.Over S}
    [CategoryTheory.GrpObj G] {U V : CategoryTheory.Over S}
    [CategoryTheory.ModObj G U] [CategoryTheory.ModObj G V] (φ : U ⟶ V)
    [CategoryTheory.IsModHom G φ] :
    actionQuotientPrestack G U ⥤ᵇ actionQuotientPrestack G V where
  obj x :=
    { carrier := x.carrier
      map := x.map ≫ φ
      equivariant := by
        haveI := x.equivariant
        infer_instance }
  map q :=
    { carrier := q.carrier
      map_naturality := by
        change q.carrier.total ≫ (_ ≫ φ) = _ ≫ φ
        rw [← Category.assoc, q.map_naturality] }
  map_id _ := rfl
  map_comp _ _ := rfl
  w := rfl

/-- API lemma for Exercise 4.1.16 (the "over `BG`" clause): the
morphism `[U/G] ⟶ [V/G]` induced by a `G`-equivariant morphism is a morphism over the
classifying stack `BG`, since it does not change the underlying principal bundle. -/
lemma actionQuotientMap_comp_forget {S : Scheme.{u}} {G : CategoryTheory.Over S}
    [CategoryTheory.GrpObj G] {U V : CategoryTheory.Over S}
    [CategoryTheory.ModObj G U] [CategoryTheory.ModObj G V] (φ : U ⟶ V)
    [CategoryTheory.IsModHom G φ] :
    (actionQuotientMap φ).comp actionQuotientPrestack.forget =
      (actionQuotientPrestack.forget : actionQuotientPrestack G U ⥤ᵇ _) :=
  rfl

end ExerMorphismsOfQuotientStacks

section ExModuliPrestackOfSmoothCurves

/-- **Example 3.4.10** (`ex:moduli-prestack-of-smooth-curves`) (the genus-`g` full
subcategory, made concrete): the prestack `ℳ_g` of families of smooth curves of genus `g`.

Its objects are smooth, proper, geometrically connected morphisms `𝒞 → S` all of whose
geometric fibres have genus `g`; its morphisms are cartesian squares; the projection
remembers the base `S`. §3.4 supplies the same object with the genus condition left as an
abstract base-change-stable parameter `Q`; `genusProperty g` of §6.1 is that parameter. -/
noncomputable abbrev moduliOfCurves (g : ℕ) : BasedCategory Scheme.{u} :=
  smoothCurveSubprestack (genusProperty.{u} g)

/-- `ℳ_g` is the full subcategory of cartesian arrows cut out by "family of smooth curves
of genus `g`". -/
lemma moduliOfCurves_eq (g : ℕ) :
    moduliOfCurves.{u} g =
      CategoryTheory.arrowCartesianProperty (smoothCurveGenusProperty.{u} g) :=
  rfl

/-- **Example 3.4.10** (`ex:moduli-prestack-of-smooth-curves`) (prestack assertion for
`ℳ_g`): families of smooth curves of genus `g` pull back along arbitrary morphisms, and
cartesian squares satisfy the required universal property. -/
instance moduliOfCurves_isFiberedInGroupoids (g : ℕ) :
    (moduliOfCurves.{u} g).p.IsFiberedInGroupoids :=
  inferInstance

/-- The objects of `ℳ_g` over a base `S` are exactly the families of smooth curves of
genus `g` over `S`. -/
lemma mem_moduliOfCurves_iff {g : ℕ} {X S : Scheme.{u}} (f : X ⟶ S) :
    (smoothCurveProperty.{u} ⊓ genusProperty.{u} g) f ↔
      (SmoothOfRelativeDimension 1 f ∧ IsProper f ∧ GeometricallyConnected f) ∧
        genusProperty.{u} g f :=
  Iff.rfl

/-- An object of `ℳ_g`: a family of smooth curves of genus `g`. -/
def moduliOfCurvesMk {g : ℕ} {C S : Scheme.{u}} (π : C ⟶ S)
    (hπ : smoothCurveGenusProperty.{u} g π) : (moduliOfCurves.{u} g).obj :=
  ⟨CategoryTheory.ArrowCartesian.mk π, hπ⟩

/-- The base of the object of `ℳ_g` attached to a family `π : 𝒞 ⟶ S` is `S`. -/
@[simp]
lemma moduliOfCurves_p_obj_mk {g : ℕ} {C S : Scheme.{u}} (π : C ⟶ S)
    (hπ : smoothCurveGenusProperty.{u} g π) :
    (moduliOfCurves.{u} g).p.obj (moduliOfCurvesMk π hπ) = S := rfl

/-- **Example 3.4.10** (`ex:moduli-prestack-of-smooth-curves`) (the "full subcategory"
clause): the inclusion of `ℳ_g` into the prestack `𝔐` of *all* families of smooth
curves. -/
def moduliOfCurvesι (g : ℕ) : moduliOfCurves.{u} g ⥤ᵇ smoothCurvePrestack.{u} :=
  CategoryTheory.arrowCartesianProperty.ιOfLE inf_le_left

/-- `ℳ_g ⊆ 𝔐` is a *full* subcategory, as the book says: a morphism of families of smooth
curves between two families of genus `g` is a morphism in `ℳ_g`. -/
instance moduliOfCurvesι_full (g : ℕ) : (moduliOfCurvesι.{u} g).toFunctor.Full :=
  inferInstanceAs (CategoryTheory.arrowCartesianProperty.ιOfLE _).toFunctor.Full

instance moduliOfCurvesι_faithful (g : ℕ) : (moduliOfCurvesι.{u} g).toFunctor.Faithful :=
  inferInstanceAs (CategoryTheory.arrowCartesianProperty.ιOfLE _).toFunctor.Faithful

/-- The inclusion `ℳ_g ↪ 𝔐` keeps the underlying family; only the genus condition is
forgotten. -/
@[simp]
lemma moduliOfCurvesι_obj (g : ℕ) (a : (moduliOfCurves.{u} g).obj) :
    ((moduliOfCurvesι.{u} g).obj a).obj = a.obj := rfl

end ExModuliPrestackOfSmoothCurves

section PropMgIsAStack

open CategoryTheory.GrothendieckTopology

/-- API lemma for Proposition 3.5.14 (smoothness locality input): being
smooth of relative dimension one is local on the target for arbitrary étale covering
families.

This combines faithfully flat descent of fixed relative dimension with the generic
passage from singleton fpqc descent to étale target-locality. -/
theorem smoothOfRelativeDimension_one_isLocalAtTarget_etale :
    MorphismProperty.IsLocalAtTarget
      (@SmoothOfRelativeDimension 1 : MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage := by
  let _ : MorphismProperty.IsStableUnderBaseChange
      (@SmoothOfRelativeDimension 1 : MorphismProperty Scheme.{u}) :=
    AlgebraicGeometry.smoothOfRelativeDimension_isStableUnderBaseChange 1
  let _ : IsZariskiLocalAtTarget
      (@SmoothOfRelativeDimension 1 : MorphismProperty Scheme.{u}) :=
    AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtTarget _
  exact Scheme.isLocalAtTarget_etalePrecoverage_of_descendsAlong _

/-- API lemma for Proposition 3.5.14 (properness locality input): being
proper is local on the target for arbitrary étale covering families.

This combines Proposition 3.1.26's fpqc descent theorem for properness with the generic
passage from singleton fpqc descent to étale target-locality. -/
theorem isProper_isLocalAtTarget_etale :
    MorphismProperty.IsLocalAtTarget
      (@IsProper : MorphismProperty Scheme.{u}) Scheme.etalePrecoverage := by
  let _ : MorphismProperty.DescendsAlong
      (@IsProper : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) :=
    Scheme.isProper_descendsAlong
  exact Scheme.isLocalAtTarget_etalePrecoverage_of_descendsAlong _

/-- API lemma for Proposition 3.5.14 (locality decomposition): target
locality for the four defining conditions of a smooth genus-`g` curve family implies
target locality for their conjunction.

This separates the standard morphism-property descent inputs (smooth relative dimension
one and properness) from the fibrewise inputs (geometric connectedness and genus). -/
theorem smoothCurveGenusProperty_isLocalAtTarget_etale_of_components
    (g : ℕ)
    [MorphismProperty.IsLocalAtTarget
      (@SmoothOfRelativeDimension 1 : MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage]
    [MorphismProperty.IsLocalAtTarget
      (@IsProper : MorphismProperty Scheme.{u}) Scheme.etalePrecoverage]
    [MorphismProperty.IsLocalAtTarget
      (@GeometricallyConnected : MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage]
    [MorphismProperty.IsLocalAtTarget (genusProperty.{u} g)
      Scheme.etalePrecoverage] :
    MorphismProperty.IsLocalAtTarget (smoothCurveGenusProperty.{u} g)
      Scheme.etalePrecoverage := by
  change MorphismProperty.IsLocalAtTarget
    (((@SmoothOfRelativeDimension 1 : MorphismProperty Scheme.{u}) ⊓
      ((@IsProper : MorphismProperty Scheme.{u}) ⊓
        (@GeometricallyConnected : MorphismProperty Scheme.{u}))) ⊓
      genusProperty.{u} g) Scheme.etalePrecoverage
  infer_instance

/-- API lemma for Proposition 3.5.14 (fibrewise-locality reduction): the
standard morphism conditions in a family of smooth curves are already étale-local on the
target.  Consequently, target-locality of geometric connectedness and fixed genus implies
target-locality of the full smooth genus-`g` curve condition. -/
theorem smoothCurveGenusProperty_isLocalAtTarget_etale_of_fiberwise
    (g : ℕ)
    [MorphismProperty.IsLocalAtTarget
      (@GeometricallyConnected : MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage]
    [MorphismProperty.IsLocalAtTarget (genusProperty.{u} g)
      Scheme.etalePrecoverage] :
    MorphismProperty.IsLocalAtTarget (smoothCurveGenusProperty.{u} g)
      Scheme.etalePrecoverage := by
  let _ : MorphismProperty.IsLocalAtTarget
      (@SmoothOfRelativeDimension 1 : MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage :=
    smoothOfRelativeDimension_one_isLocalAtTarget_etale
  let _ : MorphismProperty.IsLocalAtTarget
      (@IsProper : MorphismProperty Scheme.{u}) Scheme.etalePrecoverage :=
    isProper_isLocalAtTarget_etale
  exact smoothCurveGenusProperty_isLocalAtTarget_etale_of_components g

/-- Background definition for Proposition 3.5.14 (the remaining genus input): fixed
genus descends for étale-locally smooth, proper, geometrically connected curve families.

This is deliberately weaker than asking `genusProperty g` to be target-local on every
scheme morphism: the local hypotheses include all four defining conditions of a smooth
genus-`g` curve family.  With genus formulated on geometric fibres, this follows formally:
an algebraically closed point lifts to one member of an étale cover, and pullback
associativity identifies the two fibres. -/
def GenusEtaleDescentForSmoothCurves (g : ℕ) : Prop :=
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Precoverage.ZeroHypercover.{u + 1} Scheme.etalePrecoverage Y),
    (∀ i, smoothCurveGenusProperty g (pullback.snd f (U.f i))) →
      genusProperty g f

/-- API lemma for Proposition 3.5.14 (genus descent): fixed genus on
geometric fibres descends through arbitrary étale covering families. -/
theorem genusEtaleDescentForSmoothCurves (g : ℕ) :
    GenusEtaleDescentForSmoothCurves.{u} g := by
  intro X Y f U h
  exact MorphismProperty.IsLocalAtTarget.of_zeroHypercover
    (P := genusProperty.{u} g) U (fun i ↦ (h i).2)

/-- API lemma for Proposition 3.5.14 (exact geometric-locality reduction):
the smooth relative-dimension-one, proper, and geometrically connected conditions are
already étale-local on the target. Thus the specialized genus-descent statement above
implies target-locality of the complete smooth genus-`g` curve condition. -/
theorem smoothCurveGenusProperty_isLocalAtTarget_etale_of_genusDescent
    (g : ℕ) (hgenus : GenusEtaleDescentForSmoothCurves.{u} g) :
    MorphismProperty.IsLocalAtTarget (smoothCurveGenusProperty.{u} g)
      Scheme.etalePrecoverage := by
  let _ : MorphismProperty.IsLocalAtTarget
      (@SmoothOfRelativeDimension 1 : MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage :=
    smoothOfRelativeDimension_one_isLocalAtTarget_etale
  let _ : MorphismProperty.IsLocalAtTarget
      (@IsProper : MorphismProperty Scheme.{u}) Scheme.etalePrecoverage :=
    isProper_isLocalAtTarget_etale
  let _ : MorphismProperty.IsLocalAtTarget
      (@GeometricallyConnected : MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage :=
    Scheme.geometricallyConnected_isLocalAtTarget_etalePrecoverage
  apply MorphismProperty.IsLocalAtTarget.mk_of_isStableUnderBaseChange
  intro X Y f U h
  refine ⟨?_, hgenus f U h⟩
  refine ⟨
    MorphismProperty.IsLocalAtTarget.of_zeroHypercover
      (P := (@SmoothOfRelativeDimension 1 : MorphismProperty Scheme.{u})) U
      (fun i ↦ (h i).1.1),
    MorphismProperty.IsLocalAtTarget.of_zeroHypercover
      (P := (@IsProper : MorphismProperty Scheme.{u})) U
      (fun i ↦ (h i).1.2.1),
    MorphismProperty.IsLocalAtTarget.of_zeroHypercover
      (P := (@GeometricallyConnected : MorphismProperty Scheme.{u})) U
      (fun i ↦ (h i).1.2.2)⟩

/-- API lemma for Proposition 3.5.14 (geometric locality): being a smooth,
proper, geometrically connected family of genus-`g` curves is étale-local on the
target. -/
theorem smoothCurveGenusProperty_isLocalAtTarget_etale (g : ℕ) :
    MorphismProperty.IsLocalAtTarget (smoothCurveGenusProperty.{u} g)
      Scheme.etalePrecoverage :=
  smoothCurveGenusProperty_isLocalAtTarget_etale_of_genusDescent g
    (genusEtaleDescentForSmoothCurves g)

/-- API lemma for Proposition 3.5.14 (effective-representability
reduction): if locally represented smooth genus-`g` curve sheaves have a global scheme
representative, and the defining curve property is local at the target, then
representability by a smooth genus-`g` curve is an étale-local object property.

The effective-representability hypothesis deliberately asks only for the global scheme;
the reusable relative-Yoneda argument recovers all properties of its structure morphism
from the local representatives. -/
theorem isLocal_representableByPropertyULift_smoothCurveGenus_of_effectiveRepresentability
    (g : ℕ)
    [MorphismProperty.IsLocalAtTarget (smoothCurveGenusProperty.{u} g)
      Scheme.etalePrecoverage]
    (hEffective :
      HasEffectiveRepresentabilityULift.{u + 1} Scheme.etalePrecoverage
        (smoothCurveGenusProperty.{u} g)) :
    Pseudofunctor.ObjectProperty.IsLocal
      (Scheme.etaleTopology.representableByPropertyULift.{u + 1}
        (smoothCurveGenusProperty.{u} g))
      Scheme.etaleTopology := by
  let _ : Scheme.etalePrecoverage.IsStableUnderComposition := by
    dsimp only [Scheme.etalePrecoverage]
    infer_instance
  let _ : Scheme.etalePrecoverage.IsStableUnderBaseChange := by
    dsimp only [Scheme.etalePrecoverage]
    infer_instance
  let _ : Scheme.etalePrecoverage.HasPullbacks := by
    dsimp only [Scheme.etalePrecoverage]
    infer_instance
  let _ : Scheme.etalePrecoverage.HasIsos := by
    dsimp only [Scheme.etalePrecoverage]
    infer_instance
  exact isLocal_representableByPropertyULift_of_effectiveRepresentability
    Scheme.etalePrecoverage (smoothCurveGenusProperty.{u} g) hEffective

/-- API lemma for Proposition 3.5.14 (categorical reduction): the stack
assertion for `ℳ_g` follows once being represented by a smooth proper geometrically
connected relative curve of genus `g` is local for the étale topology, and relative
Yoneda transfers the resulting stack of representable sheaves to the
cartesian-arrow model used to define `ℳ_g`.

The locality hypothesis is the precise geometric effective-descent input. Relative
Yoneda identifies the total pointwise core of the representable-sheaf pseudofunctor with
the cartesian-arrow model internally, so no additional categorical hypothesis is needed. -/
theorem isStack_moduliOfCurves_of_representableSheafDescent
    (g : ℕ)
    (hlocal :
      Pseudofunctor.ObjectProperty.IsLocal
        (Scheme.etaleTopology.representableByPropertyULift.{u + 1}
          (smoothCurveGenusProperty.{u} g))
        Scheme.etaleTopology) :
    CategoryTheory.BasedCategory.IsStack Scheme.etaleTopology
      (moduliOfCurves.{u} g) := by
  let _ :
      Pseudofunctor.ObjectProperty.IsLocal
        (Scheme.etaleTopology.representableByPropertyULift.{u + 1}
          (smoothCurveGenusProperty.{u} g))
        Scheme.etaleTopology := hlocal
  let _ :
      (Scheme.etaleTopology.pseudofunctorOver (Type (u + 1))).IsStack
        Scheme.etaleTopology :=
    Scheme.etaleTopology.isStack_pseudofunctorOver
  change CategoryTheory.BasedCategory.IsStack Scheme.etaleTopology
    (CategoryTheory.arrowCartesianProperty (smoothCurveGenusProperty.{u} g))
  exact
    isStack_arrowCartesianProperty_of_representableByPropertyULift_isLocal
      Scheme.etaleTopology (smoothCurveGenusProperty.{u} g)
        (CategoryTheory.GrothendieckTopology.representableSheafStackBridge.{u + 1, u}
          Scheme.etaleTopology (smoothCurveGenusProperty.{u} g))

/-- **Proposition 3.5.14** (`prop:mg-is-a-stack`) (Moduli stack of smooth curves): if
`g ≥ 2`, then `ℳ_g` is a stack over `Sch_ét`.

The statement is recorded in §4.1 rather than §3.5 because the genus condition entering
the definition of `ℳ_g` is supplied by §6.1; see this folder's COMMENTARY.md.

The proof (deferred) verifies the stack axioms for the finer fpqc topology and descends
them to `Sch_ét` (Exercise 3.5.4, reduces both
axioms to a single fpqc map `S' → S`). The gluing axiom for morphisms is Fpqc Descent for
Morphisms together with fpqc descent of the property of being an isomorphism. The gluing
axiom for objects is the geometric input: for `g ≥ 2` the tricanonical sheaf
`Ω_{𝒞'/S'}^{⊗ 3}` is relatively very ample and `π_*(Ω_{𝒞'/S'}^{⊗ 3})` is a vector bundle
of rank `5(g-1)` whose formation commutes with base change (Proposition 6.1.16), so `𝒞'` embeds in `ℙ(E')`; the descent datum on `𝒞'`
induces one on `E'`, which is effective by Fpqc Descent for Quasi-Coherent Sheaves, and
`𝒞` is recovered inside `ℙ(E)` by descent of closed subschemes.

**Blocked on**: the affine-localization and quasicoherence theory for the relative
differential sheaf `Ω_{X/S}`, and the pushforward properties of its tensor powers.  Two
ingredients formerly listed here now exist: the projective bundle `ℙ(E)`
(`StacksAndModuli/API/ProjectiveBundle.lean`, as `Gr(1, E)`) and the tensor powers `Ω^{⊗ k}`
(`Scheme.Modules.tensorPower`).  Proposition 6.1.16 part (2), the vector-bundle and
base-change statement for `π_*(Ω^{⊗ k})`, is now stated in §6.1 with its proof deferred to
Cohomology and Base Change.  The categorical reductions are complete:
the proof below discharges everything except the effective-descent statement
`HasEffectiveRepresentabilityULift Scheme.etalePrecoverage (smoothCurveGenusProperty g)`
— glueing an étale descent datum of genus-`g` curve families to a global family, exactly
the tricanonical-embedding input above — which remains the single recorded `sorry`. -/
theorem isStack_moduliOfCurves (g : ℕ) (hg : 2 ≤ g) :
    CategoryTheory.BasedCategory.IsStack Scheme.etaleTopology (moduliOfCurves.{u} g) := by
  let _ : MorphismProperty.IsLocalAtTarget (smoothCurveGenusProperty.{u} g)
      Scheme.etalePrecoverage :=
    smoothCurveGenusProperty_isLocalAtTarget_etale g
  apply isStack_moduliOfCurves_of_representableSheafDescent
  apply isLocal_representableByPropertyULift_smoothCurveGenus_of_effectiveRepresentability
  exact (sorry :
    HasEffectiveRepresentabilityULift.{u + 1} Scheme.etalePrecoverage
      (smoothCurveGenusProperty.{u} g))

end PropMgIsAStack

section ThmMgIsAlgebraic

/-- Background definition for Theorem 4.1.17 (the implicit numerical data: the ambient
projective space): a smooth connected projective curve of genus `g ≥ 2` is tricanonically
embedded in `ℙ^{5g-6}`, since `h⁰(C, Ω_C^{⊗ 3}) = 5(g-1)` by Riemann–Roch. -/
def tricanonicalDim (g : ℕ) : ℕ := 5 * g - 6

/-- Background definition for Theorem 4.1.17 (the implicit numerical data: the rank of
the tricanonical bundle of sections, equivalently the size of the projective linear group
`PGL_{5g-5}` acting): `5(g-1) = 5g - 5`. -/
def tricanonicalRank (g : ℕ) : ℕ := 5 * g - 5

/-- API lemma for Theorem 4.1.17 (compatibility of the numerical data):
for `g ≥ 2`, the vector-space dimension underlying `ℙ^{5g-6}` is `5g-5`. -/
lemma tricanonicalDim_add_one (g : ℕ) (hg : 2 ≤ g) :
    tricanonicalDim g + 1 = tricanonicalRank g := by
  unfold tricanonicalDim tricanonicalRank
  omega

/-- Background definition for Theorem 4.1.17 (the implicit numerical data: the Hilbert
polynomial): for a tricanonically embedded smooth curve `C ↪ ℙ^{5g-6}` of genus `g`,
Riemann–Roch (Theorem 6.1.2) gives

`P(n) = χ(𝒪_{C}(n)) = deg(Ω_C^{⊗ 3n}) + 1 - g = (6n-1)(g-1)`.

This is an actual polynomial over `ℚ`, rather than merely its integer-valued function,
so it can be passed directly to the fixed-polynomial Hilbert functor of Theorem 2.1.2. -/
noncomputable def tricanonicalHilbertPolynomial (g : ℕ) : Polynomial ℚ :=
  (6 * Polynomial.X - 1) * Polynomial.C ((g : ℚ) - 1)

/-- API lemma for Theorem 4.1.17 (evaluation of the implicit Hilbert
polynomial): evaluation at a natural number has the formula used in the book. -/
@[simp]
lemma tricanonicalHilbertPolynomial_eval_natCast (g n : ℕ) :
    (tricanonicalHilbertPolynomial g).eval (n : ℚ) =
      (6 * (n : ℚ) - 1) * ((g : ℚ) - 1) := by
  simp [tricanonicalHilbertPolynomial]

/-- API lemma for Theorem 4.1.17 (constant term of the implicit Hilbert
polynomial): `P(0) = 1-g`. -/
@[simp]
lemma tricanonicalHilbertPolynomial_zero (g : ℕ) :
    (tricanonicalHilbertPolynomial g).eval 0 = 1 - (g : ℚ) := by
  rw [show (0 : ℚ) = ((0 : ℕ) : ℚ) by rfl,
    tricanonicalHilbertPolynomial_eval_natCast]
  ring

/-- API lemma for Theorem 4.1.17 (degree-one value of the implicit Hilbert
polynomial): `P(1) = 5(g-1)`. -/
@[simp]
lemma tricanonicalHilbertPolynomial_one (g : ℕ) :
    (tricanonicalHilbertPolynomial g).eval 1 = 5 * ((g : ℚ) - 1) := by
  rw [show (1 : ℚ) = ((1 : ℕ) : ℚ) by rfl,
    tricanonicalHilbertPolynomial_eval_natCast]
  ring

/-- API lemma for Theorem 4.1.17 (rank comparison): the value
`P(1) = 5(g-1)` of the Hilbert polynomial is the rank `5g-5` of
`π_*(Ω_{𝒞/S}^{⊗ 3})`: the tricanonical embedding is by the complete linear series, so
degree-one hypersurface sections of `ℙ^{5g-6}` restrict isomorphically to
`H⁰(C, Ω_C^{⊗ 3})`. This is condition (b) of the proof of Theorem 4.1.17. -/
lemma tricanonicalHilbertPolynomial_one_eq_rank (g : ℕ) (hg : 2 ≤ g) :
    (tricanonicalHilbertPolynomial g).eval 1 = (tricanonicalRank g : ℚ) := by
  rw [tricanonicalHilbertPolynomial_one]
  unfold tricanonicalRank
  have h5 : 5 ≤ 5 * g := by omega
  rw [Nat.cast_sub h5, Nat.cast_mul]
  norm_num
  ring

/-- API lemma for Theorem 4.1.17 (dimension encoded by the implicit
Hilbert polynomial): for `g ≥ 2`, the tricanonical Hilbert polynomial is nonconstant
linear.  Its degree is therefore the expected relative dimension of the universal
curve. -/
lemma tricanonicalHilbertPolynomial_natDegree (g : ℕ) (hg : 2 ≤ g) :
    (tricanonicalHilbertPolynomial g).natDegree = 1 := by
  have hgq : (g : ℚ) - 1 ≠ 0 := by
    have : (1 : ℚ) < g := by exact_mod_cast hg
    linarith
  have hlin : (6 * Polynomial.X - 1 : Polynomial ℚ) =
      Polynomial.C 6 * Polynomial.X - Polynomial.C 1 := by
    rfl
  have hlinDegree : (6 * Polynomial.X - 1 : Polynomial ℚ).natDegree = 1 := by
    rw [hlin, Polynomial.natDegree_sub_C,
      Polynomial.natDegree_C_mul (by norm_num), Polynomial.natDegree_X]
  have hlinNe : (6 * Polynomial.X - 1 : Polynomial ℚ) ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hlinDegree
    omega
  rw [tricanonicalHilbertPolynomial,
    Polynomial.natDegree_mul hlinNe (Polynomial.C_ne_zero.mpr hgq),
    hlinDegree, Polynomial.natDegree_C]

/-- API lemma for Theorem 4.1.17 (the projective Hilbert scheme used in
the proof): for `g ≥ 2`, the fixed-polynomial Hilbert functor
`Hilb^P(ℙ^{5g-6}_ℤ)` is represented by a scheme projective over `Spec ℤ`.

This is the direct specialization of Theorem 2.1.2 to
`P(n) = (6n-1)(g-1)`. Its geometric existence and projectivity are exactly the Chapter 2
input assumed in the proof of Theorem 4.1.17. -/
theorem exists_tricanonicalHilbertScheme (g : ℕ) (_hg : 2 ≤ g) :
    ∃ H : Over (Spec (CommRingCat.of (ULift.{u} ℤ))),
      Nonempty ((hilbFunctorP (tricanonicalDim g)
        (Spec (CommRingCat.of (ULift.{u} ℤ)))
        (tricanonicalHilbertPolynomial g)).RepresentableBy H) ∧
      IsHProjective H.hom := by
  letI : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ (ULift.ringEquiv.symm)
  letI : IsLocallyNoetherian (Spec (CommRingCat.of (ULift.{u} ℤ))) := inferInstance
  exact exists_hilbFunctorP_representableBy (tricanonicalDim g)
    (Spec (CommRingCat.of (ULift.{u} ℤ))) (tricanonicalHilbertPolynomial g)

/-- Background definition for Theorem 4.1.17 (the chosen Hilbert scheme): the projective
scheme `H = Hilb^P(ℙ^{5g-6}_ℤ)` used in the tricanonical proof of algebraicity. -/
noncomputable def tricanonicalHilbertScheme (g : ℕ) (hg : 2 ≤ g) :
    Over (Spec (CommRingCat.of (ULift.{u} ℤ))) :=
  (exists_tricanonicalHilbertScheme.{u} g hg).choose

/-- API lemma for Theorem 4.1.17 (the representing property): the chosen
tricanonical Hilbert scheme represents the fixed-polynomial Hilbert functor. -/
theorem tricanonicalHilbertScheme_represents (g : ℕ) (hg : 2 ≤ g) :
    Nonempty ((hilbFunctorP (tricanonicalDim g)
      (Spec (CommRingCat.of (ULift.{u} ℤ)))
      (tricanonicalHilbertPolynomial g)).RepresentableBy
        (tricanonicalHilbertScheme.{u} g hg)) :=
  (exists_tricanonicalHilbertScheme.{u} g hg).choose_spec.1

/-- API lemma for Theorem 4.1.17 (projectivity of the Hilbert scheme): the
chosen tricanonical Hilbert scheme is projective over `Spec ℤ`. -/
theorem tricanonicalHilbertScheme_isHProjective (g : ℕ) (hg : 2 ≤ g) :
    IsHProjective (tricanonicalHilbertScheme.{u} g hg).hom :=
  (exists_tricanonicalHilbertScheme.{u} g hg).choose_spec.2

/-- API lemma for Theorem 4.1.17 (properness of the Hilbert scheme): the
chosen tricanonical Hilbert scheme is proper over `Spec ℤ`. -/
theorem tricanonicalHilbertScheme_isProper (g : ℕ) (hg : 2 ≤ g) :
    IsProper (tricanonicalHilbertScheme.{u} g hg).hom :=
  (tricanonicalHilbertScheme_isHProjective.{u} g hg).isProper

/-- Background definition for Theorem 4.1.17 (the universal Hilbert point): the
universal embedded family is classified by the identity point of the chosen
tricanonical Hilbert scheme. -/
noncomputable def tricanonicalUniversalHilbertFamily (g : ℕ) (hg : 2 ≤ g) :
    (hilbFunctorP (tricanonicalDim g)
      (Spec (CommRingCat.of (ULift.{u} ℤ)))
      (tricanonicalHilbertPolynomial g)).obj
        (Opposite.op (tricanonicalHilbertScheme.{u} g hg)) :=
  (tricanonicalHilbertScheme_represents.{u} g hg).some.homEquiv
    (𝟙 (tricanonicalHilbertScheme.{u} g hg))

/-- API lemma for Theorem 4.1.17 (the fixed-polynomial datum carried by
the universal Hilbert point): the structure-sheaf quotient associated to the universal
embedded family has a representative whose every field fibre has tricanonical Hilbert
polynomial. -/
theorem exists_tricanonicalUniversalQuotientData_hasFiberwiseHilbertPolynomial
    (g : ℕ) (hg : 2 ≤ g) :
    ∃ a : Modules.QuotientPullbackData
        (SheafOfModules.unit
          (projectiveSpaceOver (tricanonicalDim g)
            (Spec (CommRingCat.of (ULift.{u} ℤ)))).ringCatSheaf)
        (projectiveSpaceOverπ (tricanonicalDim g)
          (Spec (CommRingCat.of (ULift.{u} ℤ))))
        (tricanonicalHilbertScheme.{u} g hg),
      Quotient.mk _ a =
          hilbertToStructureSheafQuotientAt
            (projectiveSpaceOverπ (tricanonicalDim g)
              (Spec (CommRingCat.of (ULift.{u} ℤ))))
            (tricanonicalHilbertScheme.{u} g hg)
            (tricanonicalUniversalHilbertFamily.{u} g hg).1 ∧
        a.HasFiberwiseHilbertPolynomial (tricanonicalHilbertPolynomial g) :=
  (tricanonicalUniversalHilbertFamily.{u} g hg).2

/-- Background definition for Theorem 4.1.17 (the universal closed subscheme): the
source `𝒞` of the universal embedded family over the tricanonical Hilbert scheme. -/
noncomputable def tricanonicalUniversalCurve (g : ℕ) (hg : 2 ≤ g) : Scheme.{u} :=
  (tricanonicalUniversalHilbertFamily.{u} g hg).1.1.subscheme

/-- Background definition for Theorem 4.1.17 (the universal closed immersion): the
universal curve is a closed subscheme of the base change of `ℙ^{5g-6}_ℤ` to the
tricanonical Hilbert scheme. -/
noncomputable def tricanonicalUniversalCurveι (g : ℕ) (hg : 2 ≤ g) :
    tricanonicalUniversalCurve.{u} g hg ⟶
      ((Over.pullback (projectiveSpaceOverπ (tricanonicalDim g)
        (Spec (CommRingCat.of (ULift.{u} ℤ))))).obj
        (tricanonicalHilbertScheme.{u} g hg)).left :=
  (tricanonicalUniversalHilbertFamily.{u} g hg).1.1.subschemeι

/-- Supporting instance for Theorem 4.1.17 (closedness of the universal immersion):
the universal Hilbert family is a closed subscheme of the ambient projective bundle. -/
instance tricanonicalUniversalCurveι_isClosedImmersion (g : ℕ) (hg : 2 ≤ g) :
    IsClosedImmersion (tricanonicalUniversalCurveι.{u} g hg) := by
  change IsClosedImmersion
    (tricanonicalUniversalHilbertFamily.{u} g hg).1.1.subschemeι
  infer_instance

/-- Background definition for Theorem 4.1.17 (the universal family): the projection
`𝒞 ⟶ H` of the universal closed subscheme to the tricanonical Hilbert scheme. -/
noncomputable def tricanonicalUniversalCurveπ (g : ℕ) (hg : 2 ≤ g) :
    tricanonicalUniversalCurve.{u} g hg ⟶
      (tricanonicalHilbertScheme.{u} g hg).left :=
  tricanonicalUniversalCurveι.{u} g hg ≫
    pullback.fst (tricanonicalHilbertScheme.{u} g hg).hom
      (projectiveSpaceOverπ (tricanonicalDim g)
        (Spec (CommRingCat.of (ULift.{u} ℤ))))

/-- Background definition for Theorem 4.1.17 (relative differentials of the universal
family): the sheaf `Ω_{𝒞/H}` used in the tricanonical construction. -/
noncomputable def tricanonicalUniversalCurveRelativeDifferentials
    (g : ℕ) (hg : 2 ≤ g) : (tricanonicalUniversalCurve.{u} g hg).Modules :=
  (tricanonicalUniversalCurveπ.{u} g hg).relativeDifferentials

/-- API lemma for Theorem 4.1.17 (flatness of the universal family): the
universal Hilbert family `𝒞 ⟶ H` is flat. -/
theorem tricanonicalUniversalCurveπ_flat (g : ℕ) (hg : 2 ≤ g) :
    Flat (tricanonicalUniversalCurveπ.{u} g hg) :=
  (tricanonicalUniversalHilbertFamily.{u} g hg).1.2.1

/-- Supporting instance for Theorem 4.1.17 (finite presentation of the universal
family): the universal Hilbert family `𝒞 ⟶ H` is locally of finite presentation. -/
instance tricanonicalUniversalCurveπ_locallyOfFinitePresentation
    (g : ℕ) (hg : 2 ≤ g) :
    LocallyOfFinitePresentation (tricanonicalUniversalCurveπ.{u} g hg) :=
  (tricanonicalUniversalHilbertFamily.{u} g hg).1.2.2.1

/-- Supporting instance for Theorem 4.1.17 (properness of the universal family): the
universal closed subscheme is proper over the tricanonical Hilbert scheme. -/
instance tricanonicalUniversalCurveπ_isProper (g : ℕ) (hg : 2 ≤ g) :
    IsProper (tricanonicalUniversalCurveπ.{u} g hg) := by
  change IsProper
    ((tricanonicalUniversalHilbertFamily.{u} g hg).1.1.subschemeι ≫
      pullback.fst (tricanonicalHilbertScheme.{u} g hg).hom
        (projectiveSpaceOverπ (tricanonicalDim g)
          (Spec (CommRingCat.of (ULift.{u} ℤ)))))
  infer_instance

/-- API lemma for Theorem 4.1.17 (quasi-compactness of the universal
family): the universal Hilbert family `𝒞 ⟶ H` is quasi-compact. -/
theorem tricanonicalUniversalCurveπ_quasiCompact (g : ℕ) (hg : 2 ≤ g) :
    QuasiCompact (tricanonicalUniversalCurveπ.{u} g hg) :=
  (tricanonicalUniversalHilbertFamily.{u} g hg).1.2.2.2.1

/-- API lemma for Theorem 4.1.17 (quasi-separatedness of the universal
family): the universal Hilbert family `𝒞 ⟶ H` is quasi-separated. -/
theorem tricanonicalUniversalCurveπ_quasiSeparated (g : ℕ) (hg : 2 ≤ g) :
    QuasiSeparated (tricanonicalUniversalCurveπ.{u} g hg) :=
  (tricanonicalUniversalHilbertFamily.{u} g hg).1.2.2.2.2

/-- Background definition for Theorem 4.1.17 (the smooth-fibre locus in the proof):
the complement in the Hilbert scheme of the image of the nonsmooth locus of the universal
curve. It is open because the universal curve is proper, hence a closed map. -/
noncomputable def tricanonicalFiberwiseSmoothLocus (g : ℕ) (hg : 2 ≤ g) :
    (tricanonicalHilbertScheme.{u} g hg).left.Opens := by
  let f := tricanonicalUniversalCurveπ.{u} g hg
  exact ⟨(f '' (f.smoothLocus : Set _)ᶜ)ᶜ,
    (f.isClosedMap _ f.smoothLocus.2.isClosed_compl).isOpen_compl⟩

/-- API lemma for Theorem 4.1.17 (pointwise description of the
smooth-fibre locus): a Hilbert point lies in the open locus exactly when every point of
its universal fibre belongs to the smooth locus. -/
theorem mem_tricanonicalFiberwiseSmoothLocus_iff (g : ℕ) (hg : 2 ≤ g)
    (y : (tricanonicalHilbertScheme.{u} g hg).left) :
    y ∈ tricanonicalFiberwiseSmoothLocus.{u} g hg ↔
      ∀ x : tricanonicalUniversalCurve.{u} g hg,
        tricanonicalUniversalCurveπ.{u} g hg x = y →
          x ∈ (tricanonicalUniversalCurveπ.{u} g hg).smoothLocus := by
  change y ∉ tricanonicalUniversalCurveπ.{u} g hg ''
      (((tricanonicalUniversalCurveπ.{u} g hg).smoothLocus : Set _))ᶜ ↔ _
  constructor
  · intro hy x hxy
    by_contra hx
    exact hy ⟨x, hx, hxy⟩
  · intro h hy
    obtain ⟨x, hx, hxy⟩ := hy
    exact hx (h x hxy)

/-- API lemma for Theorem 4.1.17 (smoothness over the open locus): after
restricting the universal Hilbert family to `tricanonicalFiberwiseSmoothLocus`, its
projection is smooth. -/
theorem tricanonicalUniversalCurveπ_restrict_fiberwiseSmoothLocus_smooth
    (g : ℕ) (hg : 2 ≤ g) :
    Smooth (tricanonicalUniversalCurveπ.{u} g hg ∣_
      tricanonicalFiberwiseSmoothLocus.{u} g hg) := by
  let f := tricanonicalUniversalCurveπ.{u} g hg
  let V := tricanonicalFiberwiseSmoothLocus.{u} g hg
  change Smooth (f ∣_ V)
  let i := (f ⁻¹ᵁ V).ι
  have hi : ((f ⁻¹ᵁ V : (tricanonicalUniversalCurve.{u} g hg).Opens) :
      Set (tricanonicalUniversalCurve.{u} g hg)) ⊆ f.smoothLocus := by
    intro x hx
    exact (mem_tricanonicalFiberwiseSmoothLocus_iff.{u} g hg (f x)).mp hx x rfl
  have hcomp : Smooth (i ≫ f) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff]
    rw [← Scheme.Hom.preimage_smoothLocus_eq i f]
    apply top_unique
    intro x _
    exact hi x.2
  apply AlgebraicGeometry.Smooth.of_comp_of_etale
    (f ∣_ V) V.ι
  · rwa [morphismRestrict_ι]
  · infer_instance

/-- Background definition for Theorem 4.1.17 (the geometrically connected-fibre
predicate in condition (a)): the set of Hilbert points whose universal geometric fibres
are connected.

The book proves that this set is open by Stein factorization.  It is kept separate from
`tricanonicalGeometricallyConnectedOpenLocus` below so that the still-missing Stein input
is not hidden in the definition of an open subscheme. -/
noncomputable def tricanonicalGeometricallyConnectedFiberSet
    (g : ℕ) (hg : 2 ≤ g) :
    Set (tricanonicalHilbertScheme.{u} g hg).left :=
  (tricanonicalUniversalCurveπ.{u} g hg).geometricallyConnectedFiberSet

/-- Background definition for Theorem 4.1.17 (the open part of the geometrically
connected locus in condition (a)): the largest open subset of the Hilbert scheme over
which the universal family is geometrically connected.

Stein factorization will identify this open with
`tricanonicalGeometricallyConnectedFiberSet`; until that theorem is available, this
definition records exactly the largest open on which the desired family property has
already been established. -/
noncomputable def tricanonicalGeometricallyConnectedOpenLocus
    (g : ℕ) (hg : 2 ≤ g) :
    (tricanonicalHilbertScheme.{u} g hg).left.Opens :=
  (tricanonicalUniversalCurveπ.{u} g hg).geometricallyConnectedOpenLocus

/-- API lemma for Theorem 4.1.17 (geometric connectedness on the open
locus): the universal Hilbert family is geometrically connected after restriction to its
maximal geometrically connected open. -/
theorem tricanonicalUniversalCurveπ_restrict_geometricallyConnectedOpenLocus
    (g : ℕ) (hg : 2 ≤ g) :
    GeometricallyConnected (tricanonicalUniversalCurveπ.{u} g hg ∣_
      tricanonicalGeometricallyConnectedOpenLocus.{u} g hg) :=
  Scheme.Hom.geometricallyConnected_restrict_openLocus
    (tricanonicalUniversalCurveπ.{u} g hg)

/-- API lemma for Theorem 4.1.17 (comparison with the exact fibre
predicate): every point of the maximal geometrically connected open has geometrically
connected universal fibre. -/
theorem tricanonicalGeometricallyConnectedOpenLocus_subset_fiberSet
    (g : ℕ) (hg : 2 ≤ g) :
    (tricanonicalGeometricallyConnectedOpenLocus.{u} g hg :
        Set (tricanonicalHilbertScheme.{u} g hg).left) ⊆
      tricanonicalGeometricallyConnectedFiberSet.{u} g hg :=
  Scheme.Hom.coe_geometricallyConnectedOpenLocus_subset_fiberSet
    (tricanonicalUniversalCurveπ.{u} g hg)

/-- API lemma for Theorem 4.1.17 (the formal consequence of the Stein
openness step): if the exact geometrically connected-fibre set is open, it is the
underlying set of the maximal geometrically connected open locus. -/
theorem tricanonicalGeometricallyConnectedOpenLocus_eq_fiberSet_of_isOpen
    (g : ℕ) (hg : 2 ≤ g)
    (hopen : IsOpen (tricanonicalGeometricallyConnectedFiberSet.{u} g hg)) :
    (tricanonicalGeometricallyConnectedOpenLocus.{u} g hg :
        Set (tricanonicalHilbertScheme.{u} g hg).left) =
      tricanonicalGeometricallyConnectedFiberSet.{u} g hg :=
  Scheme.Hom.coe_geometricallyConnectedOpenLocus_eq_fiberSet
    (tricanonicalUniversalCurveπ.{u} g hg) hopen

/-- Background definition for Theorem 4.1.17 (the currently constructed open part of
condition (a)): the intersection of the fibrewise-smooth open and the maximal open over
which the universal family is geometrically connected. -/
noncomputable def tricanonicalSmoothGeometricallyConnectedLocus
    (g : ℕ) (hg : 2 ≤ g) :
    (tricanonicalHilbertScheme.{u} g hg).left.Opens :=
  tricanonicalFiberwiseSmoothLocus.{u} g hg ⊓
    tricanonicalGeometricallyConnectedOpenLocus.{u} g hg

/-- API lemma for Theorem 4.1.17 (smoothness on the constructed part of
condition (a)): restricting further from the fibrewise-smooth locus to its intersection
with the geometrically connected open preserves smoothness. -/
theorem tricanonicalUniversalCurveπ_restrict_smoothGeometricallyConnectedLocus_smooth
    (g : ℕ) (hg : 2 ≤ g) :
    Smooth (tricanonicalUniversalCurveπ.{u} g hg ∣_
      tricanonicalSmoothGeometricallyConnectedLocus.{u} g hg) := by
  let f := tricanonicalUniversalCurveπ.{u} g hg
  exact IsZariskiLocalAtTarget.of_isPullback
    (f.isPullback_morphismRestrict_of_le
      (show tricanonicalSmoothGeometricallyConnectedLocus.{u} g hg ≤
        tricanonicalFiberwiseSmoothLocus.{u} g hg from inf_le_left)).flip
    (tricanonicalUniversalCurveπ_restrict_fiberwiseSmoothLocus_smooth.{u} g hg)

/-- API lemma for Theorem 4.1.17 (geometric connectedness on the
constructed part of condition (a)): restricting further to the intersection with the
fibrewise-smooth locus preserves geometric connectedness. -/
theorem tricanonicalUniversalCurveπ_restrict_smoothGeometricallyConnectedLocus_connected
    (g : ℕ) (hg : 2 ≤ g) :
    GeometricallyConnected (tricanonicalUniversalCurveπ.{u} g hg ∣_
      tricanonicalSmoothGeometricallyConnectedLocus.{u} g hg) := by
  let f := tricanonicalUniversalCurveπ.{u} g hg
  exact f.geometricallyConnected_restrict_of_le
    (tricanonicalUniversalCurveπ_restrict_geometricallyConnectedOpenLocus.{u} g hg)
    (show tricanonicalSmoothGeometricallyConnectedLocus.{u} g hg ≤
      tricanonicalGeometricallyConnectedOpenLocus.{u} g hg from inf_le_right)

/-- API lemma for Theorem 4.1.17 (condition (a) on the open constructed
so far): the universal family over the smooth/geometrically-connected open is both smooth
and geometrically connected. -/
theorem tricanonicalUniversalCurveπ_restrict_smoothGeometricallyConnectedLocus
    (g : ℕ) (hg : 2 ≤ g) :
    Smooth (tricanonicalUniversalCurveπ.{u} g hg ∣_
        tricanonicalSmoothGeometricallyConnectedLocus.{u} g hg) ∧
      GeometricallyConnected (tricanonicalUniversalCurveπ.{u} g hg ∣_
        tricanonicalSmoothGeometricallyConnectedLocus.{u} g hg) :=
  ⟨tricanonicalUniversalCurveπ_restrict_smoothGeometricallyConnectedLocus_smooth.{u}
      g hg,
    tricanonicalUniversalCurveπ_restrict_smoothGeometricallyConnectedLocus_connected.{u}
      g hg⟩

/-- Background definition for Theorem 4.1.17 (the remaining dimension-detection
hypothesis): on every nonempty standard-smooth affine chart of the constructed Hilbert
open, the chart's relative dimension agrees with the degree of the fixed Hilbert
polynomial.

The fixed-polynomial Hilbert datum and the fact that this degree is one are proved above.
What is not yet available in the library is the geometric theorem identifying the degree
of a projective subscheme's Hilbert polynomial with its dimension. -/
def TricanonicalChartDimensionAgreesWithHilbertPolynomial
    (g : ℕ) (hg : 2 ≤ g) : Prop :=
  let π := tricanonicalUniversalCurveπ.{u} g hg
  let W := tricanonicalSmoothGeometricallyConnectedLocus.{u} g hg
  let f := π ∣_ W
  ∀ (x : (π ⁻¹ᵁ W).toScheme)
    (U : W.toScheme.Opens) (_hU : IsAffineOpen U)
    (V : (π ⁻¹ᵁ W).toScheme.Opens) (_hV : IsAffineOpen V)
    (_ : x ∈ V) (e : V ≤ f ⁻¹ᵁ U) (n : ℕ),
      (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension n →
        n = (tricanonicalHilbertPolynomial g).natDegree

/-- API lemma for Theorem 4.1.17 (relative-dimension reduction): the
already-proved smoothness of the constructed Hilbert open, together with the exact
dimension-detection hypothesis above, makes the universal family smooth of relative
dimension one.

Thus the unformalized geometric input is no longer bundled into
`SmoothOfRelativeDimension 1`: it is precisely the comparison between standard-smooth
chart dimension and Hilbert-polynomial degree. -/
theorem tricanonicalSmoothLocus_smoothOfRelativeDimension_one_reduction
    (g : ℕ) (hg : 2 ≤ g)
    (hDimension : TricanonicalChartDimensionAgreesWithHilbertPolynomial.{u} g hg) :
    let π := tricanonicalUniversalCurveπ.{u} g hg
    let W := tricanonicalSmoothGeometricallyConnectedLocus.{u} g hg
    SmoothOfRelativeDimension 1 (π ∣_ W) := by
  dsimp only
  let π := tricanonicalUniversalCurveπ.{u} g hg
  let W := tricanonicalSmoothGeometricallyConnectedLocus.{u} g hg
  let f := π ∣_ W
  let _ : Smooth f :=
    tricanonicalUniversalCurveπ_restrict_smoothGeometricallyConnectedLocus_smooth.{u}
      g hg
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨U, hU, V, hV, hx, e, hφ⟩ := Smooth.exists_isStandardSmooth f x
  obtain ⟨n, hn⟩ := hφ.exists_isStandardSmoothOfRelativeDimension
  have hnOne : n = 1 :=
    (hDimension x U hU V hV hx e n hn).trans
      (tricanonicalHilbertPolynomial_natDegree g hg)
  subst n
  exact ⟨U, hU, V, hV, hx, e, hn⟩

/-- API lemma for Theorem 4.1.17 (affine differential reduction on the
smooth open locus): around every point of the currently constructed smooth universal
family there is a standard-smooth affine chart.  On that chart, the two remaining
affine-comparison obligations—invertibility on global differentials and localization of
the sheafified target—imply that the actual relative differential sheaf is finite locally
free.

This is deliberately a reduction, not an unconditional comparison theorem: it isolates
the precise missing affine geometry without hiding it behind a `sorry`. -/
theorem tricanonicalSmoothLocus_affineDifferentials_reduction
    (g : ℕ) (hg : 2 ≤ g) :
    let π := tricanonicalUniversalCurveπ.{u} g hg
    let W := tricanonicalSmoothGeometricallyConnectedLocus.{u} g hg
    let f := π ∣_ W
    ∀ x : (π ⁻¹ᵁ W).toScheme,
      ∃ (U : W.toScheme.Opens) (_ : IsAffineOpen U)
        (V : (π ⁻¹ᵁ W).toScheme.Opens) (_ : IsAffineOpen V)
        (_ : x ∈ V) (e : V ≤ f ⁻¹ᵁ U),
        let φ := f.appLE U V e
        φ.hom.IsStandardSmooth ∧
          (IsIso (affineGlobalRelativeDerivation φ).desc →
            IsLocalizing
              (modulesSpecToSheaf.obj (Spec.map φ).relativeDifferentials) →
            Modules.IsFiniteLocallyFree
              (Spec.map φ).relativeDifferentials) := by
  dsimp only
  intro x
  let π := tricanonicalUniversalCurveπ.{u} g hg
  let W := tricanonicalSmoothGeometricallyConnectedLocus.{u} g hg
  let f := π ∣_ W
  let _ : Smooth f :=
    tricanonicalUniversalCurveπ_restrict_smoothGeometricallyConnectedLocus_smooth.{u}
      g hg
  obtain ⟨U, hU, V, hV, hx, e, hφ⟩ := Smooth.exists_isStandardSmooth f x
  refine ⟨U, hU, V, hV, hx, e, hφ, ?_⟩
  intro hGlobal hTarget
  exact relativeDifferentials_isFiniteLocallyFree_of_affineCompatibility
    (f.appLE U V e) hφ hGlobal hTarget

/-- API lemma for Theorem 4.1.17 (global differential reduction on the
smooth open locus): around every point there is a standard-smooth affine chart.  If the
affine-coordinate transport of the global sheaf `Ω` agrees with the chart sheaf, then the
two affine comparison obligations imply finite local freeness of the restriction of the
global relative differential sheaf.

The chart compatibility is an explicit hypothesis rather than an unconditional claim; no
base-change theorem is hidden in this reduction. -/
theorem tricanonicalSmoothLocus_globalDifferentials_reduction
    (g : ℕ) (hg : 2 ≤ g) :
    let π := tricanonicalUniversalCurveπ.{u} g hg
    let W := tricanonicalSmoothGeometricallyConnectedLocus.{u} g hg
    let f := π ∣_ W
    ∀ x : (π ⁻¹ᵁ W).toScheme,
      ∃ (U : W.toScheme.Opens) (hU : IsAffineOpen U)
        (V : (π ⁻¹ᵁ W).toScheme.Opens) (hV : IsAffineOpen V)
        (_ : x ∈ V) (e : V ≤ f ⁻¹ᵁ U),
        let φ := f.appLE U V e
        φ.hom.IsStandardSmooth ∧
          (f.AffineRelativeDifferentialsCompatible ⟨U, hU⟩ ⟨V, hV⟩ e →
            IsIso (affineGlobalRelativeDerivation φ).desc →
            IsLocalizing
              (modulesSpecToSheaf.obj (Spec.map φ).relativeDifferentials) →
            Modules.IsFiniteLocallyFree
              ((Modules.pullback V.ι).obj f.relativeDifferentials)) := by
  dsimp only
  intro x
  let π := tricanonicalUniversalCurveπ.{u} g hg
  let W := tricanonicalSmoothGeometricallyConnectedLocus.{u} g hg
  let f := π ∣_ W
  let _ : Smooth f :=
    tricanonicalUniversalCurveπ_restrict_smoothGeometricallyConnectedLocus_smooth.{u}
      g hg
  obtain ⟨U, hU, V, hV, hx, e, hφ⟩ := Smooth.exists_isStandardSmooth f x
  refine ⟨U, hU, V, hV, hx, e, hφ, ?_⟩
  intro hCompat hGlobal hTarget
  exact relativeDifferentials_pullback_isFiniteLocallyFree_of_affineCompatibility
    f ⟨U, hU⟩ ⟨V, hV⟩ e hφ hCompat hGlobal hTarget

/-- API lemma for Theorem 4.1.17 (rank-one differential reduction):
`SmoothOfRelativeDimension 1` is the exact existing scheme-morphism property that makes
the standard-smooth charts have relative dimension one.  Under that property, chart-to-
global compatibility and the two affine comparison obligations imply that the restriction
of the global relative differential sheaf has rank one.

The relative-dimension hypothesis is not asserted for the current Hilbert open: deriving
it from the fixed Hilbert polynomial remains a separate geometric step. -/
theorem tricanonicalSmoothLocus_rankOneDifferentials_reduction
    (g : ℕ) (hg : 2 ≤ g) :
    let π := tricanonicalUniversalCurveπ.{u} g hg
    let W := tricanonicalSmoothGeometricallyConnectedLocus.{u} g hg
    let f := π ∣_ W
    SmoothOfRelativeDimension 1 f →
      ∀ x : (π ⁻¹ᵁ W).toScheme,
        ∃ (U : W.toScheme.Opens) (hU : IsAffineOpen U)
          (V : (π ⁻¹ᵁ W).toScheme.Opens) (hV : IsAffineOpen V)
          (_ : x ∈ V) (e : V ≤ f ⁻¹ᵁ U),
          let φ := f.appLE U V e
          φ.hom.IsStandardSmoothOfRelativeDimension 1 ∧
            (f.AffineRelativeDifferentialsCompatible ⟨U, hU⟩ ⟨V, hV⟩ e →
              IsIso (affineGlobalRelativeDerivation φ).desc →
              IsLocalizing
                (modulesSpecToSheaf.obj (Spec.map φ).relativeDifferentials) →
              Modules.IsProjectiveOfRank 1
                ((Modules.pullback V.ι).obj f.relativeDifferentials)) := by
  dsimp only
  intro hDim x
  let π := tricanonicalUniversalCurveπ.{u} g hg
  let W := tricanonicalSmoothGeometricallyConnectedLocus.{u} g hg
  let f := π ∣_ W
  obtain ⟨U, hU, V, hV, hx, e, hφ⟩ :=
    hDim.exists_isStandardSmoothOfRelativeDimension x
  refine ⟨U, hU, V, hV, hx, e, hφ, ?_⟩
  intro hCompat hGlobal hTarget
  let _ : Nonempty V := ⟨⟨x, hx⟩⟩
  exact relativeDifferentials_pullback_isProjectiveOfRank_of_affineCompatibility
    f 1 ⟨U, hU⟩ ⟨V, hV⟩ e hφ hCompat hGlobal hTarget

/-- Deferred obligation for Theorem 4.1.17 (**Stein factorization**, scheme case, used to
cut out condition 1): for a proper morphism of noetherian schemes, the relative-`Spec`
factorization `X → Spec_Y f_* 𝒪_X → Y` has finite second leg and geometrically connected
first-leg fibres.

The object `Spec_Y f_* 𝒪_X` is already available and needs no obligation: for any
universally closed qcqs morphism it *is* Mathlib's `f.normalization`
(`AlgebraicGeometry.Scheme.Hom.steinObjIso` in `StacksAndModuli/API/SteinFactorizationObject.lean`),
and `f = f.toNormalization ≫ f.fromNormalization` with the second leg integral is already
proved.  What is deferred is the genuinely cohomological half: finiteness of
`f.fromNormalization`, which is coherence of the proper pushforward `f_* 𝒪_X`, and
connectedness of the fibres of `f.toNormalization`, which is the Theorem on Formal
Functions.

The book uses exactly this at the point where it cuts the smooth, geometrically connected
locus out of the Hilbert scheme: the kernel and cokernel of `𝒪_H → π_* 𝒪_𝒞` have closed
support, so `H̃ → H` is an isomorphism over an open subscheme of `H`, which is precisely
where the fibres of `𝒞 → H` are geometrically connected. -/
theorem steinFactorization_isFinite_and_geometricallyConnected
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsNoetherian X] [IsNoetherian Y] :
    IsFinite f.fromNormalization ∧ GeometricallyConnected f.toNormalization := by
  sorry

/-- Deferred obligation for Theorem 4.1.17 (**representability of `PGL`**): the
automorphism presheaf `Aut_S(ℙⁿ_S)` of relative projective space is representable by a
smooth affine group scheme over `S` — the projective linear group `PGL_{n+1,S}`.

The presheaf and the representability predicate already exist
(`AlgebraicGeometry.Scheme.projectiveLinearGroupPresheaf`,
`AlgebraicGeometry.Scheme.IsProjectiveLinearGroupScheme` in
`StacksAndModuli/API/ProjectiveLinearGroupPresheaf.lean`), together with the internal group
structure that a representative automatically carries
(`IsProjectiveLinearGroupScheme.grpObj`); the algebraic seed of the coordinate construction
— that the generic determinant is a homogeneous form of degree `n + 1`, so that `PGL_{n+1}`
is the nonvanishing locus of a section on `ℙ(Mat_{n+1})` — is
`StacksAndModuli/API/GenericDeterminant.lean`.  What is deferred is the identification of that
scheme with the automorphism presheaf, which is the classification of automorphisms of
projective space and routes through `Pic(ℙⁿ_T) ≅ Pic(T) × ℤ`.

Smoothness and affineness are part of the obligation because they are what Algebraicity of
Quotients by Groupoids (Theorem 4.4.13) consumes when the action groupoid of `PGL_{5g-5}` on
the tricanonical locus is fed to it. -/
theorem exists_isProjectiveLinearGroupScheme (n : ℕ) (S : Scheme.{u}) :
    ∃ G : Over S, Scheme.IsProjectiveLinearGroupScheme n S G ∧
      Smooth G.hom ∧ IsAffineHom G.hom := by
  sorry

/-- Deferred obligation for Theorem 4.1.17, isolating the geometry of the tricanonical
construction: for `g ≥ 2` there is a smooth groupoid of algebraic spaces whose quotient
prestack has `ℳ_g` as its stackification. The intended witness is the action groupoid of
`PGL_{5g-5} = Aut(ℙ^{5g-6}_ℤ)` on the locally closed locus `H' ⊆ Hilb^P(ℙ^{5g-6}_ℤ)` of
tricanonically embedded curves, together with the comparison
`[H'/PGL_{5g-5}]^{pre} ⥤ᵇ ℳ_g` that forgets the embedding. `IsLocalStackification` for
that comparison packages Proposition 3.5.14 (`ℳ_g` is an étale stack), full faithfulness
(two tricanonical embeddings of the same family differ by a unique projective linear
transformation, since the embedding is by the complete linear series of `Ω^{⊗3}`), and
local essential surjectivity (étale — in fact Zariski — locally on the base, every family
of genus-`g` curves is tricanonically embeddable, by Proposition 6.1.16). The scheme-level
inputs still to be built are listed in the docstring of `isAlgebraicStack_moduliOfCurves`
below. -/
theorem exists_smooth_groupoid_presentation_moduliOfCurves (g : ℕ) (hg : 2 ≤ g) :
    ∃ (𝒢 : PresheafGroupoid.{u}) (i : 𝒢.quotientPrestack ⥤ᵇ moduliOfCurves.{u} g),
      𝒢.IsSmooth ∧ IsAlgebraicSpace 𝒢.U ∧ IsAlgebraicSpace 𝒢.R ∧
        BasedFunctor.IsLocalStackification (J := Scheme.etaleTopology) i := by
  sorry

/-- **Theorem 4.1.17** (`thm:mg-is-algebraic`) (Algebraicity of `ℳ_g`): if `g ≥ 2`, then
`ℳ_g` is an algebraic stack over `Spec ℤ`.

"Over `Spec ℤ`" is automatic in this formalization: `ℳ_g` is a based category over the
whole category of schemes, which is `Sch/Spec ℤ`.

The proof (deferred) is the tricanonical construction. Every smooth connected projective
curve `C` of genus `g ≥ 2` is embedded in `ℙ^{5g-6}` by the very ample line bundle
`Ω_C^{⊗ 3}` (`tricanonicalDim`), and by Riemann–Roch the Hilbert polynomial of the
embedded curve is `P(n) = (6n-1)(g-1)` (`tricanonicalHilbertPolynomial`). Let
`H = Hilb^P(ℙ^{5g-6}_ℤ)` (Theorem 2.1.2), with
universal family `π : 𝒞 → H`. There is a locally closed subscheme `H' ⊆ H` — unique with
the corresponding universal property — over which

1. every fibre `𝒞_h` is smooth and geometrically connected;
2. `p_{2,*} 𝒪_{ℙ^{5g-6} × H'}(1) → p_{2,*} 𝒪_{𝒞_{H'}}(1)` is an isomorphism, i.e. the
   embedding is by the complete linear series (`tricanonicalHilbertPolynomial_one_eq_rank`
   is the equality of ranks that reduces this to surjectivity);
3. `Ω_{𝒞_{H'}/H'}^{⊗ 3}` and `𝒪_{𝒞_{H'}}(1)` differ by the pullback of a line bundle
   from `H'`.

Condition 1 is open (fibrewise smoothness is open, plus
Stein factorization for geometric connectedness); condition 2 then cuts out an open
subscheme by Cohomology and Base Change (Theorem A.6.8); condition 3 cuts out a
closed subscheme by Proposition A.6.18 (line bundles pulled back from the base are
representable by a locally closed subscheme). The group scheme
`PGL_{5g-5} = Aut(ℙ^{5g-6}_ℤ)` acts on `H` preserving `H'`, and forgetting the embedding
gives an equivalence `ℳ_g ≅ [H'/PGL_{5g-5}]`; Algebraicity of Quotient Stacks
(Theorem 4.1.10) then concludes.

The proof below is genuine at the quotient-stack step: it applies Algebraicity of
Quotients by Groupoids (Theorem 4.4.13, formalized with upstream sorries; the book invokes its
specialization Theorem 4.1.10) to the deferred obligation
`exists_smooth_groupoid_presentation_moduliOfCurves`, which isolates all of the remaining
geometry — the construction of `H'`, the `PGL_{5g-5}` action, and the comparison
`ℳ_g ≅ [H'/PGL_{5g-5}]`.

**Blocked on**: affine localization, quasicoherence and the tricanonical positivity theory
for `Ω_{X/S}`; the action of `PGL_{5g-5}` on the Hilbert scheme; and Cohomology and Base
Change.  Several ingredients formerly listed here now exist or are typed obligations rather
than prose: the relative projective bundle `ℙ(E)` (`StacksAndModuli/API/ProjectiveBundle.lean`);
the Semicontinuity Theorem A.6.4, formalized in §A.6 with Theorem A.6.2 as its only
obligation, which is what makes conditions 1 and 2 cut out locally closed loci; the Stein
factorization used for condition 1
(`steinFactorization_isFinite_and_geometricallyConnected` above); and representability of
`PGL` (`exists_isProjectiveLinearGroupScheme` above).  The comparison
`ℳ_g ≅ [H'/PGL_{5g-5}]`, with `H'` locally closed in a projective Hilbert scheme, is still
recorded as prose only; see this folder's COMMENTARY.md. -/
theorem isAlgebraicStack_moduliOfCurves (g : ℕ) (hg : 2 ≤ g) :
    IsAlgebraicStack (moduliOfCurves.{u} g) := by
  obtain ⟨𝒢, i, hSm, hU, hR, hi⟩ :=
    exists_smooth_groupoid_presentation_moduliOfCurves g hg
  let _ : 𝒢.IsSmooth := hSm
  let _ : IsAlgebraicSpace 𝒢.U := hU
  let _ : IsAlgebraicSpace 𝒢.R := hR
  exact PresheafGroupoid.isAlgebraicStack_of_isStackification hi

/-!
**§4.1, after Theorem 4.1.17** (unlabelled remark): the whole prestack `𝔐` of families of
smooth curves is also algebraic, because `𝔐 = ∐_g ℳ_g`.

Not formalized: coproducts of based categories over `Sch` are not built in the library, and
the decomposition itself needs the genus of a family to be a locally constant function of
the base — which needs `Scheme.genus` to be known constant on connected families, i.e. the
local constancy of `h¹` in a flat proper family (Cohomology and Base Change). The inclusion
`ℳ_g ↪ 𝔐` of each piece *is* available, as `moduliOfCurvesι`.
-/

end ThmMgIsAlgebraic

end AlgebraicGeometry.Scheme
