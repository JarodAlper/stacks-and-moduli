module

public import StacksAndModuli.API.ArrowCartesianProperty
public import StacksAndModuli.API.GeometricFiberProperty
public import StacksAndModuli.API.MarkedGeometricFiberProperty
public import StacksAndModuli.API.NMarkedCartesianFamily
public import StacksAndModuli.«Section6.3-Stable».«part6.3.1-definition»
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Scheme-valued families of stable curves

This supporting API formalizes the scheme-valued specialization of Definition 6.3.20 from §6.3
(`sec:stable-curves`) of *Stacks and Moduli*. A family is
proper, flat, locally of finite presentation, and has the required property on every
geometric fibre. Both unpointed families and families with an indexed collection of
sections are packaged as cartesian-family prestacks. The book's algebraic-space
total-space formulation is implemented separately in `AlgebraicSpaceMarkedFamilies` and
the book-facing Definition 6.3.20; this file remains the stronger computational
specialization when the total space is known to be a scheme.
The componentwise semistable and stable family prestacks are kept distinct from the
existing stable-family API based on finite automorphism groups; identifying the two stable
notions remains part of Proposition 6.3.5.

The unpointed geometric-fibre conditions use `AlgebraicGeometry.geometricallyOver`, and
the marked conditions use `AlgebraicGeometry.markedGeometricallyOver`, rather than
Mathlib's bare-scheme `AlgebraicGeometry.geometrically`. Stability and `genusOver` depend
on the fibre's specified morphism to its algebraically closed field, while marked
stability also depends on the induced sections of that fibre.

## Main definitions

* `AlgebraicGeometry.Scheme.familyOfCurvesProperty`;
* `AlgebraicGeometry.Scheme.familyOfNodalCurvesProperty`;
* `AlgebraicGeometry.Scheme.familyOfStableCurvesProperty`;
* `AlgebraicGeometry.Scheme.familyOfStableCurvesOfGenusProperty`;
* `AlgebraicGeometry.Scheme.markedCurveFamilyPrestack` and
  `AlgebraicGeometry.Scheme.markedNodalCurveFamilyPrestack`;
* `AlgebraicGeometry.Scheme.prestableMarkedCurveFamilyPrestack` and its indexed,
  fixed-genus, and `Fin n` specializations;
* `AlgebraicGeometry.Scheme.semistableMarkedCurveOfGenusFamilyPrestack` and
  `AlgebraicGeometry.Scheme.componentwiseStableMarkedCurveOfGenusFamilyPrestack`;
* `AlgebraicGeometry.Scheme.stableMarkedCurveFamilyPrestack` and its fixed-genus and
  `Fin n` specializations.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits

universe u v

namespace AlgebraicGeometry.Scheme

-- Definition 6.3.20 allows algebraic-space total spaces. These explicitly named
-- specialization blocks therefore live in API rather than claiming the book labels.
section FamilyOfCurvesSchemeSpecialization

/-- Supporting scheme-valued definition for Definition 6.3.20 (unpointed scheme-valued
specialization): the predicate that a scheme over an algebraically closed field is a
curve over that specified field. -/
def curveGeometricFiberPredicate : GeometricFiberPredicate.{u} :=
  fun K _ _ Z _ ↦ IsCurveOver K Z

/-- Being a curve over an algebraically closed field is invariant under isomorphisms over
that field. -/
instance curveGeometricFiberPredicate_isClosedUnderIsomorphisms :
    curveGeometricFiberPredicate.{u}.IsClosedUnderIsomorphisms where
  of_iso e h := h.isoOver e

/-- The morphism property that every geometric fibre is a curve over its specified
algebraically closed field. -/
def curveFibersProperty : MorphismProperty Scheme.{u} :=
  geometricallyOver curveGeometricFiberPredicate.{u}

/-- The curve-fibre condition is stable under arbitrary base change. -/
instance curveFibersProperty_isStableUnderBaseChange :
    curveFibersProperty.{u}.IsStableUnderBaseChange := by
  unfold curveFibersProperty
  infer_instance

/-- The curve-fibre condition, evaluated on Mathlib's chosen geometric fibres. -/
lemma curveFibersProperty_iff {C S : Scheme.{u}} {f : C ⟶ S} :
    curveFibersProperty.{u} f ↔
      ∀ (K : Type u) [Field K] [IsAlgClosed K]
        (s : Spec (CommRingCat.of K) ⟶ S),
          @IsCurveOver K _ (pullback f s) ⟨pullback.snd f s⟩ := by
  unfold curveFibersProperty
  simpa only [curveGeometricFiberPredicate] using
    (geometricallyOver_iff (P := curveGeometricFiberPredicate.{u}) (f := f))

/-- Supporting scheme-valued definition for Definition 6.3.20 (unpointed scheme-valued
specialization): a family of curves is a proper, flat morphism locally of finite
presentation whose geometric fibres are curves.

For a proper scheme morphism, Mathlib's local finite-presentation condition is the scheme
translation of the book's finite-presentation condition: properness already supplies the
needed quasi-compactness and separatedness. -/
def familyOfCurvesProperty : MorphismProperty Scheme.{u} :=
  (@IsProper : MorphismProperty Scheme.{u}) ⊓
    ((@Flat : MorphismProperty Scheme.{u}) ⊓
      ((@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) ⊓
        curveFibersProperty.{u}))

/-- Membership in the family-of-curves property is exactly the four defining
conditions. -/
lemma mem_familyOfCurvesProperty_iff {C S : Scheme.{u}} (f : C ⟶ S) :
    familyOfCurvesProperty.{u} f ↔
      IsProper f ∧ Flat f ∧ LocallyOfFinitePresentation f ∧
        curveFibersProperty.{u} f :=
  Iff.rfl

/-- Families of curves remain families of curves after arbitrary base change. -/
instance familyOfCurvesProperty_isStableUnderBaseChange :
    familyOfCurvesProperty.{u}.IsStableUnderBaseChange := by
  unfold familyOfCurvesProperty
  infer_instance

/-- The defining curve condition on a geometric fibre presented by a pullback square. -/
lemma isCurveOver_of_familyOfCurvesProperty {C S : Scheme.{u}} {f : C ⟶ S}
    (hf : familyOfCurvesProperty.{u} f) {K : Type u} [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ S) {Z : Scheme.{u}}
    [Z.Over (Spec (CommRingCat.of K))] (toC : Z ⟶ C)
    (h : IsPullback toC (Z ↘ Spec (CommRingCat.of K)) f s) :
    IsCurveOver K Z :=
  of_geometricallyOver hf.2.2.2 s toC h

/-- The prestack of unpointed scheme-valued families of curves. -/
abbrev curveFamilyPrestack : BasedCategory Scheme.{u} :=
  CategoryTheory.arrowCartesianProperty familyOfCurvesProperty.{u}

/-- Cartesian pullback makes scheme-valued families of curves a category fibred in
groupoids. -/
instance curveFamilyPrestack_isFiberedInGroupoids :
    curveFamilyPrestack.{u}.p.IsFiberedInGroupoids :=
  inferInstance

/-- The prestack of scheme-valued families of curves with markings indexed by `I`. -/
abbrev markedCurveFamilyPrestack (I : Type v) : BasedCategory Scheme.{u} :=
  CategoryTheory.markedCartesianProperty I familyOfCurvesProperty.{u}

/-- Cartesian pullback makes indexed marked families of curves a category fibred in
groupoids. -/
instance markedCurveFamilyPrestack_isFiberedInGroupoids (I : Type v) :
    (markedCurveFamilyPrestack.{u} I).p.IsFiberedInGroupoids :=
  inferInstance

/-- Supporting scheme-valued definition for Definition 6.3.20 (`n`-pointed, scheme-valued
specialization): the prestack of families of curves equipped with `n` ordered sections. -/
abbrev nMarkedCurveFamilyPrestack (n : ℕ) : BasedCategory Scheme.{u} :=
  CategoryTheory.nMarkedCartesianProperty n familyOfCurvesProperty.{u}

end FamilyOfCurvesSchemeSpecialization

section FamilyOfNodalCurvesSchemeSpecialization

/-- Supporting scheme-valued definition for Definition 6.3.20 (unpointed scheme-valued
specialization): the predicate that a scheme over an algebraically closed field is a
nodal curve over that specified field. -/
def nodalCurveGeometricFiberPredicate : GeometricFiberPredicate.{u} :=
  fun K _ _ Z _ ↦ IsNodalCurveOver K Z

/-- Nodality is invariant under isomorphisms over the algebraically closed field. -/
instance nodalCurveGeometricFiberPredicate_isClosedUnderIsomorphisms :
    nodalCurveGeometricFiberPredicate.{u}.IsClosedUnderIsomorphisms where
  of_iso e h := h.isoOver e

/-- The morphism property that every geometric fibre is a nodal curve. -/
def nodalCurveFibersProperty : MorphismProperty Scheme.{u} :=
  geometricallyOver nodalCurveGeometricFiberPredicate.{u}

/-- The nodal-fibre condition is stable under arbitrary base change. -/
instance nodalCurveFibersProperty_isStableUnderBaseChange :
    nodalCurveFibersProperty.{u}.IsStableUnderBaseChange := by
  unfold nodalCurveFibersProperty
  infer_instance

/-- The nodal-fibre condition, evaluated on Mathlib's chosen geometric fibres. -/
lemma nodalCurveFibersProperty_iff {C S : Scheme.{u}} {f : C ⟶ S} :
    nodalCurveFibersProperty.{u} f ↔
      ∀ (K : Type u) [Field K] [IsAlgClosed K]
        (s : Spec (CommRingCat.of K) ⟶ S),
          @IsNodalCurveOver K _ _ (pullback f s) ⟨pullback.snd f s⟩ := by
  unfold nodalCurveFibersProperty
  simpa only [nodalCurveGeometricFiberPredicate] using
    (geometricallyOver_iff (P := nodalCurveGeometricFiberPredicate.{u}) (f := f))

/-- Supporting scheme-valued definition for Definition 6.3.20 (unpointed scheme-valued
specialization): a family of nodal curves is a family of curves all of whose geometric
fibres are nodal. -/
def familyOfNodalCurvesProperty : MorphismProperty Scheme.{u} :=
  familyOfCurvesProperty.{u} ⊓ nodalCurveFibersProperty.{u}

/-- Membership in the family-of-nodal-curves property is the family condition together
with nodality of every geometric fibre. -/
lemma mem_familyOfNodalCurvesProperty_iff {C S : Scheme.{u}} (f : C ⟶ S) :
    familyOfNodalCurvesProperty.{u} f ↔
      familyOfCurvesProperty.{u} f ∧ nodalCurveFibersProperty.{u} f :=
  Iff.rfl

/-- Families of nodal curves remain such after arbitrary base change. -/
instance familyOfNodalCurvesProperty_isStableUnderBaseChange :
    familyOfNodalCurvesProperty.{u}.IsStableUnderBaseChange := by
  unfold familyOfNodalCurvesProperty
  infer_instance

/-- The defining nodality condition on a geometric fibre presented by a pullback
square. -/
lemma isNodalCurveOver_of_familyOfNodalCurvesProperty {C S : Scheme.{u}} {f : C ⟶ S}
    (hf : familyOfNodalCurvesProperty.{u} f) {K : Type u} [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ S) {Z : Scheme.{u}}
    [Z.Over (Spec (CommRingCat.of K))] (toC : Z ⟶ C)
    (h : IsPullback toC (Z ↘ Spec (CommRingCat.of K)) f s) :
    IsNodalCurveOver K Z :=
  of_geometricallyOver hf.2 s toC h

/-- The prestack of unpointed scheme-valued families of nodal curves. -/
abbrev nodalCurveFamilyPrestack : BasedCategory Scheme.{u} :=
  CategoryTheory.arrowCartesianProperty familyOfNodalCurvesProperty.{u}

/-- Cartesian pullback makes scheme-valued families of nodal curves a category fibred in
groupoids. -/
instance nodalCurveFamilyPrestack_isFiberedInGroupoids :
    nodalCurveFamilyPrestack.{u}.p.IsFiberedInGroupoids :=
  inferInstance

/-- The prestack of scheme-valued nodal-curve families with markings indexed by `I`. -/
abbrev markedNodalCurveFamilyPrestack (I : Type v) : BasedCategory Scheme.{u} :=
  CategoryTheory.markedCartesianProperty I familyOfNodalCurvesProperty.{u}

/-- Cartesian pullback makes indexed marked nodal families a category fibred in
groupoids. -/
instance markedNodalCurveFamilyPrestack_isFiberedInGroupoids (I : Type v) :
    (markedNodalCurveFamilyPrestack.{u} I).p.IsFiberedInGroupoids :=
  inferInstance

/-- Supporting scheme-valued definition for Definition 6.3.20 (`n`-pointed, scheme-valued
specialization): the prestack of nodal families equipped with `n` ordered sections. -/
abbrev nMarkedNodalCurveFamilyPrestack (n : ℕ) : BasedCategory Scheme.{u} :=
  CategoryTheory.nMarkedCartesianProperty n familyOfNodalCurvesProperty.{u}

end FamilyOfNodalCurvesSchemeSpecialization

section FamilyOfPrestableCurvesMarkedSchemeSpecialization

/-- Supporting scheme-valued definition for Definition 6.3.20 (prestable, indexed-marked,
scheme-valued specialization): the predicate that a marked geometric fibre is a
prestable curve of some genus over its specified algebraically closed field. -/
def prestableMarkedCurveGeometricFiberPredicate (I : Type v) :
    MarkedGeometricFiberPredicate.{v, u} I :=
  fun K _ _ Z _ p ↦ ∃ g, IsPrestableMarkedCurveOfGenusOver K g Z p

/-- Indexed prestability is invariant under marked isomorphisms over the field. -/
instance prestableMarkedCurveGeometricFiberPredicate_isClosedUnderIsomorphisms
    (I : Type v) :
    (prestableMarkedCurveGeometricFiberPredicate.{u} I).IsClosedUnderIsomorphisms where
  of_iso e hmark h := by
    obtain ⟨g, hg⟩ := h
    exact ⟨g, hg.isoOver e hmark⟩

/-- The object property that every indexed marked geometric fibre is prestable. -/
def prestableMarkedCurveFibersProperty (I : Type v) :
    ObjectProperty (MarkedCartesianObj I familyOfCurvesProperty.{u}) :=
  markedGeometricallyOver (prestableMarkedCurveGeometricFiberPredicate.{u} I)

/-- Indexed prestable marked fibres remain prestable after pulling back the family. -/
instance prestableMarkedCurveFibersProperty_isStableUnderPullback (I : Type v) :
    MarkedCartesianObjectProperty.IsStableUnderPullback
      (prestableMarkedCurveFibersProperty.{u} I) := by
  unfold prestableMarkedCurveFibersProperty
  infer_instance

/-- The indexed prestable marked-fibre condition, evaluated on Mathlib's chosen pullback
fibre. -/
lemma prestableMarkedCurveFibersProperty_iff (I : Type v)
    (a : MarkedCartesianObj I familyOfCurvesProperty.{u}) :
    prestableMarkedCurveFibersProperty.{u} I a ↔
      ∀ (K : Type u) [Field K] [IsAlgClosed K]
        (y : Spec (CommRingCat.of K) ⟶ a.right),
          ∃ g, @IsPrestableMarkedCurveOfGenusOver K _ _ I g
            (pullback a.hom y) ⟨pullback.snd a.hom y⟩
              (a.pullbackGeometricFiberSection K y) := by
  unfold prestableMarkedCurveFibersProperty
  simpa only [prestableMarkedCurveGeometricFiberPredicate] using
    (markedGeometricallyOver_iff
      (Q := prestableMarkedCurveGeometricFiberPredicate.{u} I) (a := a))

/-- The defining indexed prestability condition on an arbitrary displayed marked
geometric fibre. -/
lemma exists_isPrestableMarkedCurveOfGenusOver_of_prestableMarkedCurveFibersProperty
    {I : Type v} {a : MarkedCartesianObj I familyOfCurvesProperty.{u}}
    (ha : prestableMarkedCurveFibersProperty.{u} I a)
    {K : Type u} [Field K] [IsAlgClosed K]
    (y : Spec (CommRingCat.of K) ⟶ a.right) {Z : Scheme.{u}}
    [Z.Over (Spec (CommRingCat.of K))] (fst : Z ⟶ a.left)
    (h : IsPullback fst (Z ↘ Spec (CommRingCat.of K)) a.hom y) :
    ∃ g, IsPrestableMarkedCurveOfGenusOver K g Z
      (fun i ↦ a.geometricFiberSection y fst h i) :=
  of_markedGeometricallyOver ha y fst h

/-- Supporting scheme-valued definition for Definition 6.3.20 (prestable, indexed-marked,
scheme-valued specialization): the prestack of curve families whose indexed marked
geometric fibres are prestable. -/
abbrev prestableMarkedCurveFamilyPrestack (I : Type v) : BasedCategory Scheme.{u} :=
  markedGeometricSubprestack familyOfCurvesProperty.{u}
    (prestableMarkedCurveGeometricFiberPredicate.{u} I)

/-- Indexed prestable marked curve families form a category fibred in groupoids. -/
instance prestableMarkedCurveFamilyPrestack_isFiberedInGroupoids (I : Type v) :
    (prestableMarkedCurveFamilyPrestack.{u} I).p.IsFiberedInGroupoids :=
  inferInstance

/-- Forgetting prestability regards an indexed prestable family as an indexed marked
nodal family, without discarding its markings. -/
noncomputable def prestableMarkedCurveFamilyPrestack.forgetPrestable (I : Type v) :
    BasedFunctor (prestableMarkedCurveFamilyPrestack.{u} I)
      (markedNodalCurveFamilyPrestack.{u} I) where
  obj a :=
    { left := a.obj.left
      right := a.obj.right
      hom := a.obj.hom
      property := ⟨a.obj.property, by
        intro K _ _ y Z fst snd h
        let _ : Z.Over (Spec (CommRingCat.of K)) := ⟨snd⟩
        obtain ⟨g, hg⟩ := of_markedGeometricallyOver a.property y fst h
        exact hg.nodal⟩
      mark := a.obj.mark
      mark_fac := a.obj.mark_fac }
  map {a b} f :=
    { left := f.hom.left
      right := f.hom.right
      isPullback := f.hom.isPullback
      mark_naturality := f.hom.mark_naturality }
  map_id _ := rfl
  map_comp _ _ := rfl
  w := rfl

/-- Forgetting indexed prestability is fully faithful. -/
noncomputable def prestableMarkedCurveFamilyPrestack.forgetPrestableFullyFaithful
    (I : Type v) :
    (prestableMarkedCurveFamilyPrestack.forgetPrestable.{u} I).toFunctor.FullyFaithful where
  preimage f := ObjectProperty.homMk
    { left := f.left
      right := f.right
      isPullback := f.isPullback
      mark_naturality := f.mark_naturality }
  map_preimage _ := rfl
  preimage_map _ := by
    apply ObjectProperty.hom_ext
    apply MarkedCartesianHom.ext <;> rfl

instance prestableMarkedCurveFamilyPrestack_forgetPrestable_faithful (I : Type v) :
    (prestableMarkedCurveFamilyPrestack.forgetPrestable.{u} I).toFunctor.Faithful :=
  (prestableMarkedCurveFamilyPrestack.forgetPrestableFullyFaithful.{u} I).faithful

instance prestableMarkedCurveFamilyPrestack_forgetPrestable_full (I : Type v) :
    (prestableMarkedCurveFamilyPrestack.forgetPrestable.{u} I).toFunctor.Full :=
  (prestableMarkedCurveFamilyPrestack.forgetPrestableFullyFaithful.{u} I).full

/-- The predicate that an indexed marked geometric fibre is prestable of genus `g`. -/
def prestableMarkedCurveOfGenusGeometricFiberPredicate (I : Type v) (g : ℕ) :
    MarkedGeometricFiberPredicate.{v, u} I :=
  fun K _ _ Z _ p ↦ IsPrestableMarkedCurveOfGenusOver K g Z p

/-- Fixed-genus indexed prestability is invariant under marked isomorphisms over the
field. -/
instance prestableMarkedCurveOfGenusGeometricFiberPredicate_isClosedUnderIsomorphisms
    (I : Type v) (g : ℕ) :
    (prestableMarkedCurveOfGenusGeometricFiberPredicate.{u} I g).IsClosedUnderIsomorphisms where
  of_iso e hmark h := h.isoOver e hmark

/-- The object property that every indexed marked geometric fibre is prestable of genus
`g`. -/
def prestableMarkedCurveOfGenusFibersProperty (I : Type v) (g : ℕ) :
    ObjectProperty (MarkedCartesianObj I familyOfCurvesProperty.{u}) :=
  markedGeometricallyOver
    (prestableMarkedCurveOfGenusGeometricFiberPredicate.{u} I g)

/-- Fixed-genus indexed prestable fibres remain such after pulling back the family. -/
instance prestableMarkedCurveOfGenusFibersProperty_isStableUnderPullback
    (I : Type v) (g : ℕ) :
    MarkedCartesianObjectProperty.IsStableUnderPullback
      (prestableMarkedCurveOfGenusFibersProperty.{u} I g) := by
  unfold prestableMarkedCurveOfGenusFibersProperty
  infer_instance

/-- The fixed-genus indexed prestable fibre condition, evaluated on Mathlib's chosen
pullback fibre. -/
lemma prestableMarkedCurveOfGenusFibersProperty_iff (I : Type v) (g : ℕ)
    (a : MarkedCartesianObj I familyOfCurvesProperty.{u}) :
    prestableMarkedCurveOfGenusFibersProperty.{u} I g a ↔
      ∀ (K : Type u) [Field K] [IsAlgClosed K]
        (y : Spec (CommRingCat.of K) ⟶ a.right),
          @IsPrestableMarkedCurveOfGenusOver K _ _ I g
            (pullback a.hom y) ⟨pullback.snd a.hom y⟩
              (a.pullbackGeometricFiberSection K y) := by
  unfold prestableMarkedCurveOfGenusFibersProperty
  simpa only [prestableMarkedCurveOfGenusGeometricFiberPredicate] using
    (markedGeometricallyOver_iff
      (Q := prestableMarkedCurveOfGenusGeometricFiberPredicate.{u} I g) (a := a))

/-- The defining fixed-genus indexed prestability condition on an arbitrary displayed
marked geometric fibre. -/
lemma isPrestableMarkedCurveOfGenusOver_of_prestableMarkedCurveOfGenusFibersProperty
    {I : Type v} {g : ℕ} {a : MarkedCartesianObj I familyOfCurvesProperty.{u}}
    (ha : prestableMarkedCurveOfGenusFibersProperty.{u} I g a)
    {K : Type u} [Field K] [IsAlgClosed K]
    (y : Spec (CommRingCat.of K) ⟶ a.right) {Z : Scheme.{u}}
    [Z.Over (Spec (CommRingCat.of K))] (fst : Z ⟶ a.left)
    (h : IsPullback fst (Z ↘ Spec (CommRingCat.of K)) a.hom y) :
    IsPrestableMarkedCurveOfGenusOver K g Z
      (fun i ↦ a.geometricFiberSection y fst h i) :=
  of_markedGeometricallyOver ha y fst h

/-- Fixed-genus indexed prestable fibres are prestable after forgetting the genus
witness. -/
lemma prestableMarkedCurveOfGenusFibersProperty_le_prestableMarkedCurveFibersProperty
    (I : Type v) (g : ℕ) :
    prestableMarkedCurveOfGenusFibersProperty.{u} I g ≤
      prestableMarkedCurveFibersProperty.{u} I := by
  intro a ha K _ _ y Z _ fst h
  exact ⟨g, ha y fst h⟩

/-- Supporting scheme-valued definition for Definition 6.3.20 (prestable genus-`g`,
indexed-marked, scheme-valued specialization): the prestack of curve families whose
indexed marked geometric fibres are prestable of genus `g`. -/
abbrev prestableMarkedCurveOfGenusFamilyPrestack (I : Type v) (g : ℕ) :
    BasedCategory Scheme.{u} :=
  markedGeometricSubprestack familyOfCurvesProperty.{u}
    (prestableMarkedCurveOfGenusGeometricFiberPredicate.{u} I g)

/-- Fixed-genus indexed prestable marked curve families form a category fibred in
groupoids. -/
instance prestableMarkedCurveOfGenusFamilyPrestack_isFiberedInGroupoids
    (I : Type v) (g : ℕ) :
    (prestableMarkedCurveOfGenusFamilyPrestack.{u} I g).p.IsFiberedInGroupoids :=
  inferInstance

/-- Forgetting the fixed genus gives an inclusion into arbitrary-genus indexed prestable
families. -/
def prestableMarkedCurveOfGenusFamilyPrestack.forgetGenus (I : Type v) (g : ℕ) :
    BasedFunctor (prestableMarkedCurveOfGenusFamilyPrestack.{u} I g)
      (prestableMarkedCurveFamilyPrestack.{u} I) where
  toFunctor := ObjectProperty.ιOfLE
    (prestableMarkedCurveOfGenusFibersProperty_le_prestableMarkedCurveFibersProperty.{u}
      I g)
  w := rfl

/-- Forgetting the genus of an indexed prestable family is fully faithful. -/
def prestableMarkedCurveOfGenusFamilyPrestack.forgetGenusFullyFaithful
    (I : Type v) (g : ℕ) :
    (prestableMarkedCurveOfGenusFamilyPrestack.forgetGenus.{u} I g).toFunctor.FullyFaithful :=
  ObjectProperty.fullyFaithfulιOfLE
    (prestableMarkedCurveOfGenusFibersProperty_le_prestableMarkedCurveFibersProperty.{u}
      I g)

instance prestableMarkedCurveOfGenusFamilyPrestack_forgetGenus_full
    (I : Type v) (g : ℕ) :
    (prestableMarkedCurveOfGenusFamilyPrestack.forgetGenus.{u} I g).toFunctor.Full :=
  (prestableMarkedCurveOfGenusFamilyPrestack.forgetGenusFullyFaithful.{u} I g).full

instance prestableMarkedCurveOfGenusFamilyPrestack_forgetGenus_faithful
    (I : Type v) (g : ℕ) :
    (prestableMarkedCurveOfGenusFamilyPrestack.forgetGenus.{u} I g).toFunctor.Faithful :=
  (prestableMarkedCurveOfGenusFamilyPrestack.forgetGenusFullyFaithful.{u} I g).faithful

/-- Supporting scheme-valued definition for Definition 6.3.20 (prestable, `n`-pointed,
scheme-valued specialization): the predicate that a marked geometric fibre is an
`n`-pointed prestable curve of some genus over its specified algebraically closed field.

The existential genus is appropriate before a genus stratum has been selected; the
fixed-genus version is `prestableNMarkedCurveOfGenusGeometricFiberPredicate`. -/
abbrev prestableNMarkedCurveGeometricFiberPredicate (n : ℕ) :
    MarkedGeometricFiberPredicate.{0, u} (Fin n) :=
  prestableMarkedCurveGeometricFiberPredicate.{u} (Fin n)

/-- Prestability of an `n`-pointed geometric fibre is invariant under marked
isomorphisms over the field. -/
instance prestableNMarkedCurveGeometricFiberPredicate_isClosedUnderIsomorphisms
    (n : ℕ) :
    (prestableNMarkedCurveGeometricFiberPredicate.{u} n).IsClosedUnderIsomorphisms :=
  inferInstance

/-- The object property that every marked geometric fibre is an `n`-pointed prestable
curve. -/
abbrev prestableNMarkedCurveFibersProperty (n : ℕ) :
    ObjectProperty (MarkedCartesianObj (Fin n) familyOfCurvesProperty.{u}) :=
  prestableMarkedCurveFibersProperty.{u} (Fin n)

/-- Prestable marked geometric fibres remain prestable after pulling back the family. -/
instance prestableNMarkedCurveFibersProperty_isStableUnderPullback (n : ℕ) :
    MarkedCartesianObjectProperty.IsStableUnderPullback
      (prestableNMarkedCurveFibersProperty.{u} n) :=
  inferInstance

/-- The prestable marked-fibre condition, evaluated on Mathlib's chosen pullback
fibre. -/
lemma prestableNMarkedCurveFibersProperty_iff (n : ℕ)
    (a : MarkedCartesianObj (Fin n) familyOfCurvesProperty.{u}) :
    prestableNMarkedCurveFibersProperty.{u} n a ↔
      ∀ (K : Type u) [Field K] [IsAlgClosed K]
        (y : Spec (CommRingCat.of K) ⟶ a.right),
          ∃ g, @IsPrestableNMarkedCurveOfGenusOver K _ _ g n
            (pullback a.hom y) ⟨pullback.snd a.hom y⟩
              (a.pullbackGeometricFiberSection K y) := by
  change prestableMarkedCurveFibersProperty.{u} (Fin n) a ↔ _
  rw [prestableMarkedCurveFibersProperty_iff]
  constructor
  · intro h K _ _ y
    let _ : (pullback a.hom y).Over (Spec (CommRingCat.of K)) :=
      ⟨pullback.snd a.hom y⟩
    obtain ⟨g, hg⟩ := h K y
    exact ⟨g,
      (isPrestableNMarkedCurveOfGenusOver_iff_isPrestableMarkedCurveOfGenusOver
        K g n _ _).mpr hg⟩
  · intro h K _ _ y
    let _ : (pullback a.hom y).Over (Spec (CommRingCat.of K)) :=
      ⟨pullback.snd a.hom y⟩
    obtain ⟨g, hg⟩ := h K y
    exact ⟨g,
      (isPrestableNMarkedCurveOfGenusOver_iff_isPrestableMarkedCurveOfGenusOver
        K g n _ _).mp hg⟩

/-- The defining prestability condition on an arbitrary displayed marked geometric
fibre. -/
lemma exists_isPrestableNMarkedCurveOfGenusOver_of_prestableNMarkedCurveFibersProperty
    {n : ℕ} {a : MarkedCartesianObj (Fin n) familyOfCurvesProperty.{u}}
    (ha : prestableNMarkedCurveFibersProperty.{u} n a)
    {K : Type u} [Field K] [IsAlgClosed K]
    (y : Spec (CommRingCat.of K) ⟶ a.right) {Z : Scheme.{u}}
    [Z.Over (Spec (CommRingCat.of K))] (fst : Z ⟶ a.left)
    (h : IsPullback fst (Z ↘ Spec (CommRingCat.of K)) a.hom y) :
    ∃ g, IsPrestableNMarkedCurveOfGenusOver K g n Z
      (fun i ↦ a.geometricFiberSection y fst h i) := by
  obtain ⟨g, hg⟩ :=
    exists_isPrestableMarkedCurveOfGenusOver_of_prestableMarkedCurveFibersProperty
      ha y fst h
  exact ⟨g,
    (isPrestableNMarkedCurveOfGenusOver_iff_isPrestableMarkedCurveOfGenusOver
      K g n Z _).mpr hg⟩

/-- Supporting scheme-valued definition for Definition 6.3.20 (prestable, `n`-pointed,
scheme-valued specialization): the prestack of curve families whose marked geometric
fibres are prestable. -/
abbrev prestableNMarkedCurveFamilyPrestack (n : ℕ) : BasedCategory Scheme.{u} :=
  prestableMarkedCurveFamilyPrestack.{u} (Fin n)

/-- Prestable `n`-marked curve families form a category fibred in groupoids. -/
instance prestableNMarkedCurveFamilyPrestack_isFiberedInGroupoids (n : ℕ) :
    (prestableNMarkedCurveFamilyPrestack.{u} n).p.IsFiberedInGroupoids :=
  inferInstance

/-- Forgetting prestability regards an `n`-pointed prestable family as an `n`-pointed
nodal family, without discarding its markings. -/
noncomputable def prestableNMarkedCurveFamilyPrestack.forgetPrestable (n : ℕ) :
    BasedFunctor (prestableNMarkedCurveFamilyPrestack.{u} n)
      (nMarkedNodalCurveFamilyPrestack.{u} n) :=
  prestableMarkedCurveFamilyPrestack.forgetPrestable.{u} (Fin n)

/-- Forgetting prestability is fully faithful. -/
noncomputable def prestableNMarkedCurveFamilyPrestack.forgetPrestableFullyFaithful
    (n : ℕ) :
    (prestableNMarkedCurveFamilyPrestack.forgetPrestable.{u} n).toFunctor.FullyFaithful :=
  prestableMarkedCurveFamilyPrestack.forgetPrestableFullyFaithful.{u} (Fin n)

instance prestableNMarkedCurveFamilyPrestack_forgetPrestable_faithful (n : ℕ) :
    (prestableNMarkedCurveFamilyPrestack.forgetPrestable.{u} n).toFunctor.Faithful :=
  (prestableNMarkedCurveFamilyPrestack.forgetPrestableFullyFaithful.{u} n).faithful

instance prestableNMarkedCurveFamilyPrestack_forgetPrestable_full (n : ℕ) :
    (prestableNMarkedCurveFamilyPrestack.forgetPrestable.{u} n).toFunctor.Full :=
  (prestableNMarkedCurveFamilyPrestack.forgetPrestableFullyFaithful.{u} n).full

/-- The predicate that an `n`-pointed marked geometric fibre is prestable of genus `g`. -/
abbrev prestableNMarkedCurveOfGenusGeometricFiberPredicate (g n : ℕ) :
    MarkedGeometricFiberPredicate.{0, u} (Fin n) :=
  prestableMarkedCurveOfGenusGeometricFiberPredicate.{u} (Fin n) g

/-- Fixed-genus prestability is invariant under marked isomorphisms over the field. -/
instance prestableNMarkedCurveOfGenusGeometricFiberPredicate_isClosedUnderIsomorphisms
    (g n : ℕ) :
    (prestableNMarkedCurveOfGenusGeometricFiberPredicate.{u} g n).IsClosedUnderIsomorphisms :=
  inferInstance

/-- The object property that every marked geometric fibre is prestable of genus `g`. -/
abbrev prestableNMarkedCurveOfGenusFibersProperty (g n : ℕ) :
    ObjectProperty (MarkedCartesianObj (Fin n) familyOfCurvesProperty.{u}) :=
  prestableMarkedCurveOfGenusFibersProperty.{u} (Fin n) g

/-- Fixed-genus prestable marked fibres remain such after pulling back the family. -/
instance prestableNMarkedCurveOfGenusFibersProperty_isStableUnderPullback
    (g n : ℕ) :
    MarkedCartesianObjectProperty.IsStableUnderPullback
      (prestableNMarkedCurveOfGenusFibersProperty.{u} g n) :=
  inferInstance

/-- The fixed-genus prestable marked-fibre condition, evaluated on Mathlib's chosen
pullback fibre. -/
lemma prestableNMarkedCurveOfGenusFibersProperty_iff (g n : ℕ)
    (a : MarkedCartesianObj (Fin n) familyOfCurvesProperty.{u}) :
    prestableNMarkedCurveOfGenusFibersProperty.{u} g n a ↔
      ∀ (K : Type u) [Field K] [IsAlgClosed K]
        (y : Spec (CommRingCat.of K) ⟶ a.right),
          @IsPrestableNMarkedCurveOfGenusOver K _ _ g n
            (pullback a.hom y) ⟨pullback.snd a.hom y⟩
              (a.pullbackGeometricFiberSection K y) := by
  change prestableMarkedCurveOfGenusFibersProperty.{u} (Fin n) g a ↔ _
  rw [prestableMarkedCurveOfGenusFibersProperty_iff]
  constructor
  · intro h K _ _ y
    let _ : (pullback a.hom y).Over (Spec (CommRingCat.of K)) :=
      ⟨pullback.snd a.hom y⟩
    exact (isPrestableNMarkedCurveOfGenusOver_iff_isPrestableMarkedCurveOfGenusOver
      K g n _ _).mpr (h K y)
  · intro h K _ _ y
    let _ : (pullback a.hom y).Over (Spec (CommRingCat.of K)) :=
      ⟨pullback.snd a.hom y⟩
    exact (isPrestableNMarkedCurveOfGenusOver_iff_isPrestableMarkedCurveOfGenusOver
      K g n _ _).mp (h K y)

/-- The defining fixed-genus prestability condition on an arbitrary displayed marked
geometric fibre. -/
lemma isPrestableNMarkedCurveOfGenusOver_of_prestableNMarkedCurveOfGenusFibersProperty
    {g n : ℕ} {a : MarkedCartesianObj (Fin n) familyOfCurvesProperty.{u}}
    (ha : prestableNMarkedCurveOfGenusFibersProperty.{u} g n a)
    {K : Type u} [Field K] [IsAlgClosed K]
    (y : Spec (CommRingCat.of K) ⟶ a.right) {Z : Scheme.{u}}
    [Z.Over (Spec (CommRingCat.of K))] (fst : Z ⟶ a.left)
    (h : IsPullback fst (Z ↘ Spec (CommRingCat.of K)) a.hom y) :
    IsPrestableNMarkedCurveOfGenusOver K g n Z
      (fun i ↦ a.geometricFiberSection y fst h i) :=
  (isPrestableNMarkedCurveOfGenusOver_iff_isPrestableMarkedCurveOfGenusOver
    K g n Z _).mpr
      (isPrestableMarkedCurveOfGenusOver_of_prestableMarkedCurveOfGenusFibersProperty
        ha y fst h)

/-- Fixed-genus prestable fibres are prestable after forgetting the genus witness. -/
lemma prestableNMarkedCurveOfGenusFibersProperty_le_prestableNMarkedCurveFibersProperty
    (g n : ℕ) :
    prestableNMarkedCurveOfGenusFibersProperty.{u} g n ≤
      prestableNMarkedCurveFibersProperty.{u} n :=
  prestableMarkedCurveOfGenusFibersProperty_le_prestableMarkedCurveFibersProperty
    (Fin n) g

/-- Supporting scheme-valued definition for Definition 6.3.20 (prestable genus-`g`,
`n`-pointed, scheme-valued specialization): the prestack of curve families whose marked
geometric fibres are prestable of genus `g`. -/
abbrev prestableNMarkedCurveOfGenusFamilyPrestack (g n : ℕ) :
    BasedCategory Scheme.{u} :=
  prestableMarkedCurveOfGenusFamilyPrestack.{u} (Fin n) g

/-- Fixed-genus prestable `n`-marked curve families form a category fibred in
groupoids. -/
instance prestableNMarkedCurveOfGenusFamilyPrestack_isFiberedInGroupoids
    (g n : ℕ) :
    (prestableNMarkedCurveOfGenusFamilyPrestack.{u} g n).p.IsFiberedInGroupoids :=
  inferInstance

/-- Forgetting the fixed genus gives an inclusion into arbitrary-genus prestable
`n`-marked families. -/
def prestableNMarkedCurveOfGenusFamilyPrestack.forgetGenus (g n : ℕ) :
    BasedFunctor (prestableNMarkedCurveOfGenusFamilyPrestack.{u} g n)
      (prestableNMarkedCurveFamilyPrestack.{u} n) :=
  prestableMarkedCurveOfGenusFamilyPrestack.forgetGenus.{u} (Fin n) g

/-- Forgetting the genus of a prestable marked family is fully faithful. -/
def prestableNMarkedCurveOfGenusFamilyPrestack.forgetGenusFullyFaithful
    (g n : ℕ) :
    (prestableNMarkedCurveOfGenusFamilyPrestack.forgetGenus.{u} g n).toFunctor.FullyFaithful :=
  prestableMarkedCurveOfGenusFamilyPrestack.forgetGenusFullyFaithful.{u} (Fin n) g

instance prestableNMarkedCurveOfGenusFamilyPrestack_forgetGenus_full (g n : ℕ) :
    (prestableNMarkedCurveOfGenusFamilyPrestack.forgetGenus.{u} g n).toFunctor.Full :=
  (prestableNMarkedCurveOfGenusFamilyPrestack.forgetGenusFullyFaithful.{u} g n).full

instance prestableNMarkedCurveOfGenusFamilyPrestack_forgetGenus_faithful (g n : ℕ) :
    (prestableNMarkedCurveOfGenusFamilyPrestack.forgetGenus.{u} g n).toFunctor.Faithful :=
  (prestableNMarkedCurveOfGenusFamilyPrestack.forgetGenusFullyFaithful.{u} g n).faithful

end FamilyOfPrestableCurvesMarkedSchemeSpecialization

section FamilyOfComponentwiseStableCurvesMarkedSchemeSpecialization

/-- The predicate that an indexed marked geometric fibre is semistable of some genus. -/
def semistableMarkedCurveGeometricFiberPredicate (I : Type v) :
    MarkedGeometricFiberPredicate.{v, u} I :=
  fun K _ _ Z _ p ↦ ∃ g, IsSemistableMarkedCurveOfGenusOver K g Z p

/-- Indexed semistability of unspecified genus is invariant under marked isomorphisms
over the field. -/
instance semistableMarkedCurveGeometricFiberPredicate_isClosedUnderIsomorphisms
    (I : Type v) :
    (semistableMarkedCurveGeometricFiberPredicate.{u} I).IsClosedUnderIsomorphisms where
  of_iso e hmark h := by
    obtain ⟨g, hg⟩ := h
    exact ⟨g, hg.isoOver e hmark⟩

/-- Supporting scheme-valued definition for Definition 6.3.20 (semistable, indexed-marked,
fixed-genus, scheme-valued specialization): the predicate that an indexed marked
geometric fibre is componentwise semistable of genus `g`. -/
def semistableMarkedCurveOfGenusGeometricFiberPredicate (I : Type v) (g : ℕ) :
    MarkedGeometricFiberPredicate.{v, u} I :=
  fun K _ _ Z _ p ↦ IsSemistableMarkedCurveOfGenusOver K g Z p

/-- Indexed semistability of fixed genus is invariant under marked isomorphisms over the
field. -/
instance semistableMarkedCurveOfGenusGeometricFiberPredicate_isClosedUnderIsomorphisms
    (I : Type v) (g : ℕ) :
    (semistableMarkedCurveOfGenusGeometricFiberPredicate.{u} I g).IsClosedUnderIsomorphisms where
  of_iso e hmark h := h.isoOver e hmark

/-- The object property that every indexed marked geometric fibre is semistable of genus
`g`. -/
def semistableMarkedCurveOfGenusFibersProperty (I : Type v) (g : ℕ) :
    ObjectProperty (MarkedCartesianObj I familyOfCurvesProperty.{u}) :=
  markedGeometricallyOver
    (semistableMarkedCurveOfGenusGeometricFiberPredicate.{u} I g)

/-- Fixed-genus indexed semistable fibres remain semistable after pulling back the
family. -/
instance semistableMarkedCurveOfGenusFibersProperty_isStableUnderPullback
    (I : Type v) (g : ℕ) :
    MarkedCartesianObjectProperty.IsStableUnderPullback
      (semistableMarkedCurveOfGenusFibersProperty.{u} I g) := by
  unfold semistableMarkedCurveOfGenusFibersProperty
  infer_instance

/-- The fixed-genus indexed semistable-fibre condition, evaluated on Mathlib's chosen
pullback fibre. -/
lemma semistableMarkedCurveOfGenusFibersProperty_iff (I : Type v) (g : ℕ)
    (a : MarkedCartesianObj I familyOfCurvesProperty.{u}) :
    semistableMarkedCurveOfGenusFibersProperty.{u} I g a ↔
      ∀ (K : Type u) [Field K] [IsAlgClosed K]
        (y : Spec (CommRingCat.of K) ⟶ a.right),
          @IsSemistableMarkedCurveOfGenusOver K _ _ I g
            (pullback a.hom y) ⟨pullback.snd a.hom y⟩
              (a.pullbackGeometricFiberSection K y) := by
  unfold semistableMarkedCurveOfGenusFibersProperty
  simpa only [semistableMarkedCurveOfGenusGeometricFiberPredicate] using
    (markedGeometricallyOver_iff
      (Q := semistableMarkedCurveOfGenusGeometricFiberPredicate.{u} I g) (a := a))

/-- The defining fixed-genus indexed semistability condition on an arbitrary displayed
marked geometric fibre. -/
lemma isSemistableMarkedCurveOfGenusOver_of_semistableMarkedCurveOfGenusFibersProperty
    {I : Type v} {g : ℕ} {a : MarkedCartesianObj I familyOfCurvesProperty.{u}}
    (ha : semistableMarkedCurveOfGenusFibersProperty.{u} I g a)
    {K : Type u} [Field K] [IsAlgClosed K]
    (y : Spec (CommRingCat.of K) ⟶ a.right) {Z : Scheme.{u}}
    [Z.Over (Spec (CommRingCat.of K))] (fst : Z ⟶ a.left)
    (h : IsPullback fst (Z ↘ Spec (CommRingCat.of K)) a.hom y) :
    IsSemistableMarkedCurveOfGenusOver K g Z
      (fun i ↦ a.geometricFiberSection y fst h i) :=
  of_markedGeometricallyOver ha y fst h

/-- Fixed-genus indexed semistable fibres are prestable. -/
lemma semistableMarkedCurveOfGenusFibersProperty_le_prestableMarkedCurveOfGenusFibersProperty
    (I : Type v) (g : ℕ) :
    semistableMarkedCurveOfGenusFibersProperty.{u} I g ≤
      prestableMarkedCurveOfGenusFibersProperty.{u} I g := by
  intro a ha K _ _ y Z _ fst h
  exact (ha y fst h).isPrestable

/-- Supporting scheme-valued definition for Definition 6.3.20 (semistable, indexed-marked,
fixed-genus, scheme-valued specialization): the prestack of curve families whose indexed
marked geometric fibres are semistable of genus `g`. -/
abbrev semistableMarkedCurveOfGenusFamilyPrestack (I : Type v) (g : ℕ) :
    BasedCategory Scheme.{u} :=
  markedGeometricSubprestack familyOfCurvesProperty.{u}
    (semistableMarkedCurveOfGenusGeometricFiberPredicate.{u} I g)

/-- Fixed-genus indexed semistable marked curve families form a category fibred in
groupoids. -/
instance semistableMarkedCurveOfGenusFamilyPrestack_isFiberedInGroupoids
    (I : Type v) (g : ℕ) :
    (semistableMarkedCurveOfGenusFamilyPrestack.{u} I g).p.IsFiberedInGroupoids :=
  inferInstance

/-- Forgetting semistability includes fixed-genus indexed semistable families into
prestable families. -/
def semistableMarkedCurveOfGenusFamilyPrestack.forgetSemistability
    (I : Type v) (g : ℕ) :
    BasedFunctor (semistableMarkedCurveOfGenusFamilyPrestack.{u} I g)
      (prestableMarkedCurveOfGenusFamilyPrestack.{u} I g) where
  toFunctor := ObjectProperty.ιOfLE
    (semistableMarkedCurveOfGenusFibersProperty_le_prestableMarkedCurveOfGenusFibersProperty.{u}
      I g)
  w := rfl

/-- Forgetting indexed semistability is fully faithful. -/
def semistableMarkedCurveOfGenusFamilyPrestack.forgetSemistabilityFullyFaithful
    (I : Type v) (g : ℕ) :
    CategoryTheory.Functor.FullyFaithful
      (semistableMarkedCurveOfGenusFamilyPrestack.forgetSemistability.{u} I g).toFunctor :=
  ObjectProperty.fullyFaithfulιOfLE
    (semistableMarkedCurveOfGenusFibersProperty_le_prestableMarkedCurveOfGenusFibersProperty.{u}
      I g)

instance semistableMarkedCurveOfGenusFamilyPrestack_forgetSemistability_full
    (I : Type v) (g : ℕ) :
    (semistableMarkedCurveOfGenusFamilyPrestack.forgetSemistability.{u} I g).toFunctor.Full :=
  (semistableMarkedCurveOfGenusFamilyPrestack.forgetSemistabilityFullyFaithful.{u}
    I g).full

instance semistableMarkedCurveOfGenusFamilyPrestack_forgetSemistability_faithful
    (I : Type v) (g : ℕ) :
    (semistableMarkedCurveOfGenusFamilyPrestack.forgetSemistability.{u} I g).toFunctor.Faithful :=
  (semistableMarkedCurveOfGenusFamilyPrestack.forgetSemistabilityFullyFaithful.{u}
    I g).faithful

/-- Supporting scheme-valued definition for Definition 6.3.20 (componentwise stable,
indexed-marked, fixed-genus, scheme-valued specialization): the predicate that an indexed
marked geometric fibre satisfies the book's three-special-point componentwise stability
condition. -/
def componentwiseStableMarkedCurveOfGenusGeometricFiberPredicate
    (I : Type v) (g : ℕ) : MarkedGeometricFiberPredicate.{v, u} I :=
  fun K _ _ Z _ p ↦ IsComponentwiseStableMarkedCurveOfGenusOver K g Z p

/-- Fixed-genus indexed componentwise stability is invariant under marked isomorphisms
over the field. -/
instance
    componentwiseStableMarkedCurveOfGenusGeometricFiberPredicate_isClosedUnderIsomorphisms
    (I : Type v) (g : ℕ) :
    MarkedGeometricFiberPredicate.IsClosedUnderIsomorphisms
      (componentwiseStableMarkedCurveOfGenusGeometricFiberPredicate.{u} I g) where
  of_iso e hmark h := h.isoOver e hmark

/-- The object property that every indexed marked geometric fibre is componentwise stable
of genus `g`. -/
def componentwiseStableMarkedCurveOfGenusFibersProperty (I : Type v) (g : ℕ) :
    ObjectProperty (MarkedCartesianObj I familyOfCurvesProperty.{u}) :=
  markedGeometricallyOver
    (componentwiseStableMarkedCurveOfGenusGeometricFiberPredicate.{u} I g)

/-- Fixed-genus indexed componentwise-stable fibres remain such after pulling back the
family. -/
instance componentwiseStableMarkedCurveOfGenusFibersProperty_isStableUnderPullback
    (I : Type v) (g : ℕ) :
    MarkedCartesianObjectProperty.IsStableUnderPullback
      (componentwiseStableMarkedCurveOfGenusFibersProperty.{u} I g) := by
  unfold componentwiseStableMarkedCurveOfGenusFibersProperty
  infer_instance

/-- The fixed-genus indexed componentwise-stable fibre condition, evaluated on Mathlib's
chosen pullback fibre. -/
lemma componentwiseStableMarkedCurveOfGenusFibersProperty_iff
    (I : Type v) (g : ℕ) (a : MarkedCartesianObj I familyOfCurvesProperty.{u}) :
    componentwiseStableMarkedCurveOfGenusFibersProperty.{u} I g a ↔
      ∀ (K : Type u) [Field K] [IsAlgClosed K]
        (y : Spec (CommRingCat.of K) ⟶ a.right),
          @IsComponentwiseStableMarkedCurveOfGenusOver K _ _ I g
            (pullback a.hom y) ⟨pullback.snd a.hom y⟩
              (a.pullbackGeometricFiberSection K y) := by
  unfold componentwiseStableMarkedCurveOfGenusFibersProperty
  simpa only [componentwiseStableMarkedCurveOfGenusGeometricFiberPredicate] using
    (markedGeometricallyOver_iff
      (Q := componentwiseStableMarkedCurveOfGenusGeometricFiberPredicate.{u} I g)
      (a := a))

/-- The defining fixed-genus indexed componentwise stability condition on an arbitrary
displayed marked geometric fibre. -/
lemma isComponentwiseStableMarkedCurveOfGenusOver_of_componentwiseStableFibersProperty
    {I : Type v} {g : ℕ} {a : MarkedCartesianObj I familyOfCurvesProperty.{u}}
    (ha : componentwiseStableMarkedCurveOfGenusFibersProperty.{u} I g a)
    {K : Type u} [Field K] [IsAlgClosed K]
    (y : Spec (CommRingCat.of K) ⟶ a.right) {Z : Scheme.{u}}
    [Z.Over (Spec (CommRingCat.of K))] (fst : Z ⟶ a.left)
    (h : IsPullback fst (Z ↘ Spec (CommRingCat.of K)) a.hom y) :
    IsComponentwiseStableMarkedCurveOfGenusOver K g Z
      (fun i ↦ a.geometricFiberSection y fst h i) :=
  of_markedGeometricallyOver ha y fst h

/-- Fixed-genus indexed componentwise-stable fibres are semistable. -/
lemma componentwiseStableFibersProperty_le_semistableFibersProperty
    (I : Type v) (g : ℕ) :
    componentwiseStableMarkedCurveOfGenusFibersProperty.{u} I g ≤
      semistableMarkedCurveOfGenusFibersProperty.{u} I g := by
  intro a ha K _ _ y Z _ fst h
  exact (ha y fst h).isSemistable

/-- Supporting scheme-valued definition for Definition 6.3.20 (componentwise stable,
indexed-marked, fixed-genus, scheme-valued specialization): the prestack of curve families
whose indexed marked geometric fibres satisfy the three-special-point stability
condition. -/
abbrev componentwiseStableMarkedCurveOfGenusFamilyPrestack
    (I : Type v) (g : ℕ) : BasedCategory Scheme.{u} :=
  markedGeometricSubprestack familyOfCurvesProperty.{u}
    (componentwiseStableMarkedCurveOfGenusGeometricFiberPredicate.{u} I g)

/-- Fixed-genus indexed componentwise-stable marked curve families form a category
fibred in groupoids. -/
instance componentwiseStableMarkedCurveOfGenusFamilyPrestack_isFiberedInGroupoids
    (I : Type v) (g : ℕ) :
    (componentwiseStableMarkedCurveOfGenusFamilyPrestack.{u} I g).p.IsFiberedInGroupoids :=
  inferInstance

/-- Forgetting componentwise stability includes such families into semistable families. -/
def componentwiseStableMarkedCurveOfGenusFamilyPrestack.forgetComponentwiseStability
    (I : Type v) (g : ℕ) :
    BasedFunctor (componentwiseStableMarkedCurveOfGenusFamilyPrestack.{u} I g)
      (semistableMarkedCurveOfGenusFamilyPrestack.{u} I g) where
  toFunctor := ObjectProperty.ιOfLE
    (componentwiseStableFibersProperty_le_semistableFibersProperty.{u} I g)
  w := rfl

/-- Forgetting indexed componentwise stability is fully faithful. -/
def
    componentwiseStableMarkedCurveOfGenusFamilyPrestack.forgetComponentwiseStabilityFullyFaithful
    (I : Type v) (g : ℕ) :
    (componentwiseStableMarkedCurveOfGenusFamilyPrestack.forgetComponentwiseStability.{u}
      I g).toFunctor.FullyFaithful :=
  ObjectProperty.fullyFaithfulιOfLE
    (componentwiseStableFibersProperty_le_semistableFibersProperty.{u} I g)

open componentwiseStableMarkedCurveOfGenusFamilyPrestack in
instance componentwiseStableMarkedCurveOfGenusFamilyPrestack_forgetComponentwiseStability_full
    (I : Type v) (g : ℕ) :
    (componentwiseStableMarkedCurveOfGenusFamilyPrestack.forgetComponentwiseStability.{u}
      I g).toFunctor.Full :=
  (forgetComponentwiseStabilityFullyFaithful.{u} I g).full

open componentwiseStableMarkedCurveOfGenusFamilyPrestack in
instance
    componentwiseStableMarkedCurveOfGenusFamilyPrestack_forgetComponentwiseStability_faithful
    (I : Type v) (g : ℕ) :
    (componentwiseStableMarkedCurveOfGenusFamilyPrestack.forgetComponentwiseStability.{u}
      I g).toFunctor.Faithful :=
  (forgetComponentwiseStabilityFullyFaithful.{u} I g).faithful

/-- Supporting scheme-valued definition for Definition 6.3.20 (semistable genus-`g`,
`n`-pointed, scheme-valued specialization): the exact ordered-marking specialization of
the indexed semistable geometric-fibre predicate. -/
abbrev semistableNMarkedCurveOfGenusGeometricFiberPredicate (g n : ℕ) :
    MarkedGeometricFiberPredicate.{0, u} (Fin n) :=
  semistableMarkedCurveOfGenusGeometricFiberPredicate.{u} (Fin n) g

/-- Exact `n`-pointed semistability of fixed genus is invariant under marked
isomorphisms. -/
instance semistableNMarkedCurveOfGenusGeometricFiberPredicate_isClosedUnderIsomorphisms
    (g n : ℕ) :
    MarkedGeometricFiberPredicate.IsClosedUnderIsomorphisms
      (semistableNMarkedCurveOfGenusGeometricFiberPredicate.{u} g n) :=
  inferInstance

/-- The object property that every exact `n`-pointed geometric fibre is semistable of
genus `g`. -/
abbrev semistableNMarkedCurveOfGenusFibersProperty (g n : ℕ) :
    ObjectProperty (MarkedCartesianObj (Fin n) familyOfCurvesProperty.{u}) :=
  semistableMarkedCurveOfGenusFibersProperty.{u} (Fin n) g

/-- Exact `n`-pointed fixed-genus semistable fibres remain such under pullback. -/
instance semistableNMarkedCurveOfGenusFibersProperty_isStableUnderPullback
    (g n : ℕ) :
    MarkedCartesianObjectProperty.IsStableUnderPullback
      (semistableNMarkedCurveOfGenusFibersProperty.{u} g n) :=
  inferInstance

/-- The exact `n`-pointed fixed-genus semistable-fibre condition on Mathlib's chosen
pullback fibre. -/
lemma semistableNMarkedCurveOfGenusFibersProperty_iff (g n : ℕ)
    (a : MarkedCartesianObj (Fin n) familyOfCurvesProperty.{u}) :
    semistableNMarkedCurveOfGenusFibersProperty.{u} g n a ↔
      ∀ (K : Type u) [Field K] [IsAlgClosed K]
        (y : Spec (CommRingCat.of K) ⟶ a.right),
          @IsSemistableNMarkedCurveOfGenusOver K _ _ g n
            (pullback a.hom y) ⟨pullback.snd a.hom y⟩
              (a.pullbackGeometricFiberSection K y) := by
  change semistableMarkedCurveOfGenusFibersProperty.{u} (Fin n) g a ↔ _
  rw [semistableMarkedCurveOfGenusFibersProperty_iff]
  constructor
  · intro h K _ _ y
    let _ : (pullback a.hom y).Over (Spec (CommRingCat.of K)) :=
      ⟨pullback.snd a.hom y⟩
    exact (isSemistableNMarkedCurveOfGenusOver_iff_isSemistableMarkedCurveOfGenusOver
      K g n _ _).mpr (h K y)
  · intro h K _ _ y
    let _ : (pullback a.hom y).Over (Spec (CommRingCat.of K)) :=
      ⟨pullback.snd a.hom y⟩
    exact (isSemistableNMarkedCurveOfGenusOver_iff_isSemistableMarkedCurveOfGenusOver
      K g n _ _).mp (h K y)

/-- The exact `n`-pointed fixed-genus semistability condition on an arbitrary displayed
marked geometric fibre. -/
lemma isSemistableNMarkedCurveOfGenusOver_of_semistableNMarkedCurveOfGenusFibersProperty
    {g n : ℕ} {a : MarkedCartesianObj (Fin n) familyOfCurvesProperty.{u}}
    (ha : semistableNMarkedCurveOfGenusFibersProperty.{u} g n a)
    {K : Type u} [Field K] [IsAlgClosed K]
    (y : Spec (CommRingCat.of K) ⟶ a.right) {Z : Scheme.{u}}
    [Z.Over (Spec (CommRingCat.of K))] (fst : Z ⟶ a.left)
    (h : IsPullback fst (Z ↘ Spec (CommRingCat.of K)) a.hom y) :
    IsSemistableNMarkedCurveOfGenusOver K g n Z
      (fun i ↦ a.geometricFiberSection y fst h i) :=
  (isSemistableNMarkedCurveOfGenusOver_iff_isSemistableMarkedCurveOfGenusOver
    K g n Z _).mpr
      (isSemistableMarkedCurveOfGenusOver_of_semistableMarkedCurveOfGenusFibersProperty
        ha y fst h)

/-- Supporting scheme-valued definition for Definition 6.3.20 (semistable genus-`g`,
`n`-pointed, scheme-valued specialization): the prestack of families whose ordered marked
geometric fibres are semistable of genus `g`. -/
abbrev semistableNMarkedCurveOfGenusFamilyPrestack (g n : ℕ) :
    BasedCategory Scheme.{u} :=
  semistableMarkedCurveOfGenusFamilyPrestack.{u} (Fin n) g

/-- Exact fixed-genus semistable `n`-marked families form a category fibred in
groupoids. -/
instance semistableNMarkedCurveOfGenusFamilyPrestack_isFiberedInGroupoids
    (g n : ℕ) :
    (semistableNMarkedCurveOfGenusFamilyPrestack.{u} g n).p.IsFiberedInGroupoids :=
  inferInstance

/-- Forgetting semistability includes exact `n`-pointed semistable families into
prestable families. -/
def semistableNMarkedCurveOfGenusFamilyPrestack.forgetSemistability (g n : ℕ) :
    BasedFunctor (semistableNMarkedCurveOfGenusFamilyPrestack.{u} g n)
      (prestableNMarkedCurveOfGenusFamilyPrestack.{u} g n) :=
  semistableMarkedCurveOfGenusFamilyPrestack.forgetSemistability.{u} (Fin n) g

/-- Forgetting exact `n`-pointed semistability is fully faithful. -/
def semistableNMarkedCurveOfGenusFamilyPrestack.forgetSemistabilityFullyFaithful
    (g n : ℕ) :
    (semistableNMarkedCurveOfGenusFamilyPrestack.forgetSemistability.{u}
      g n).toFunctor.FullyFaithful :=
  semistableMarkedCurveOfGenusFamilyPrestack.forgetSemistabilityFullyFaithful.{u}
    (Fin n) g

instance semistableNMarkedCurveOfGenusFamilyPrestack_forgetSemistability_full
    (g n : ℕ) :
    (semistableNMarkedCurveOfGenusFamilyPrestack.forgetSemistability.{u}
      g n).toFunctor.Full :=
  (semistableNMarkedCurveOfGenusFamilyPrestack.forgetSemistabilityFullyFaithful.{u}
    g n).full

instance semistableNMarkedCurveOfGenusFamilyPrestack_forgetSemistability_faithful
    (g n : ℕ) :
    (semistableNMarkedCurveOfGenusFamilyPrestack.forgetSemistability.{u}
      g n).toFunctor.Faithful :=
  (semistableNMarkedCurveOfGenusFamilyPrestack.forgetSemistabilityFullyFaithful.{u}
    g n).faithful

/-- Supporting scheme-valued definition for Definition 6.3.20 (componentwise stable
genus-`g`, `n`-pointed, scheme-valued specialization): the exact ordered-marking
specialization of the componentwise-stable geometric-fibre predicate. -/
abbrev componentwiseStableNMarkedCurveOfGenusGeometricFiberPredicate (g n : ℕ) :
    MarkedGeometricFiberPredicate.{0, u} (Fin n) :=
  componentwiseStableMarkedCurveOfGenusGeometricFiberPredicate.{u} (Fin n) g

/-- Exact `n`-pointed componentwise stability of fixed genus is invariant under marked
isomorphisms. -/
instance
    componentwiseStableNMarkedCurveOfGenusGeometricFiberPredicate_isClosedUnderIsomorphisms
    (g n : ℕ) :
    MarkedGeometricFiberPredicate.IsClosedUnderIsomorphisms
      (componentwiseStableNMarkedCurveOfGenusGeometricFiberPredicate.{u} g n) :=
  inferInstance

/-- The object property that every exact `n`-pointed geometric fibre is componentwise
stable of genus `g`. -/
abbrev componentwiseStableNMarkedCurveOfGenusFibersProperty (g n : ℕ) :
    ObjectProperty (MarkedCartesianObj (Fin n) familyOfCurvesProperty.{u}) :=
  componentwiseStableMarkedCurveOfGenusFibersProperty.{u} (Fin n) g

/-- Exact `n`-pointed fixed-genus componentwise-stable fibres remain such under
pullback. -/
instance componentwiseStableNMarkedCurveOfGenusFibersProperty_isStableUnderPullback
    (g n : ℕ) :
    MarkedCartesianObjectProperty.IsStableUnderPullback
      (componentwiseStableNMarkedCurveOfGenusFibersProperty.{u} g n) :=
  inferInstance

/-- The exact `n`-pointed fixed-genus componentwise-stable condition on Mathlib's chosen
pullback fibre. -/
lemma componentwiseStableNMarkedCurveOfGenusFibersProperty_iff (g n : ℕ)
    (a : MarkedCartesianObj (Fin n) familyOfCurvesProperty.{u}) :
    componentwiseStableNMarkedCurveOfGenusFibersProperty.{u} g n a ↔
      ∀ (K : Type u) [Field K] [IsAlgClosed K]
        (y : Spec (CommRingCat.of K) ⟶ a.right),
          @IsComponentwiseStableNMarkedCurveOfGenusOver K _ _ g n
            (pullback a.hom y) ⟨pullback.snd a.hom y⟩
              (a.pullbackGeometricFiberSection K y) := by
  change componentwiseStableMarkedCurveOfGenusFibersProperty.{u} (Fin n) g a ↔ _
  rw [componentwiseStableMarkedCurveOfGenusFibersProperty_iff]
  constructor
  · intro h K _ _ y
    let _ : (pullback a.hom y).Over (Spec (CommRingCat.of K)) :=
      ⟨pullback.snd a.hom y⟩
    exact
      (isComponentwiseStableNMarkedCurveOfGenusOver_iff_isComponentwiseStableMarkedCurveOfGenusOver
        K g n _ _).mpr (h K y)
  · intro h K _ _ y
    let _ : (pullback a.hom y).Over (Spec (CommRingCat.of K)) :=
      ⟨pullback.snd a.hom y⟩
    exact
      (isComponentwiseStableNMarkedCurveOfGenusOver_iff_isComponentwiseStableMarkedCurveOfGenusOver
        K g n _ _).mp (h K y)

/-- The exact `n`-pointed fixed-genus componentwise stability condition on an arbitrary
displayed marked geometric fibre. -/
lemma isComponentwiseStableNMarkedCurveOfGenusOver_of_componentwiseStableNFibersProperty
    {g n : ℕ} {a : MarkedCartesianObj (Fin n) familyOfCurvesProperty.{u}}
    (ha : componentwiseStableNMarkedCurveOfGenusFibersProperty.{u} g n a)
    {K : Type u} [Field K] [IsAlgClosed K]
    (y : Spec (CommRingCat.of K) ⟶ a.right) {Z : Scheme.{u}}
    [Z.Over (Spec (CommRingCat.of K))] (fst : Z ⟶ a.left)
    (h : IsPullback fst (Z ↘ Spec (CommRingCat.of K)) a.hom y) :
    IsComponentwiseStableNMarkedCurveOfGenusOver K g n Z
      (fun i ↦ a.geometricFiberSection y fst h i) :=
  (isComponentwiseStableNMarkedCurveOfGenusOver_iff_isComponentwiseStableMarkedCurveOfGenusOver
    K g n Z _).mpr
      (isComponentwiseStableMarkedCurveOfGenusOver_of_componentwiseStableFibersProperty
        ha y fst h)

/-- Exact componentwise-stable fibres are semistable after forgetting the
three-special-point condition. -/
lemma componentwiseStableNFibersProperty_le_semistableNFibersProperty
    (g n : ℕ) :
    componentwiseStableNMarkedCurveOfGenusFibersProperty.{u} g n ≤
      semistableNMarkedCurveOfGenusFibersProperty.{u} g n :=
  componentwiseStableFibersProperty_le_semistableFibersProperty (Fin n) g

/-- Supporting scheme-valued definition for Definition 6.3.20 (componentwise stable
genus-`g`, `n`-pointed, scheme-valued specialization): the prestack of families whose
ordered marked geometric fibres satisfy the three-special-point stability condition. -/
abbrev componentwiseStableNMarkedCurveOfGenusFamilyPrestack (g n : ℕ) :
    BasedCategory Scheme.{u} :=
  componentwiseStableMarkedCurveOfGenusFamilyPrestack.{u} (Fin n) g

/-- Exact fixed-genus componentwise-stable `n`-marked families form a category fibred in
groupoids. -/
instance componentwiseStableNMarkedCurveOfGenusFamilyPrestack_isFiberedInGroupoids
    (g n : ℕ) :
    CategoryTheory.Functor.IsFiberedInGroupoids
      (componentwiseStableNMarkedCurveOfGenusFamilyPrestack.{u} g n).p :=
  inferInstance

/-- Forgetting componentwise stability includes exact `n`-pointed stable families into
semistable families. -/
def
    componentwiseStableNMarkedCurveOfGenusFamilyPrestack.forgetComponentwiseStability
    (g n : ℕ) :
    BasedFunctor (componentwiseStableNMarkedCurveOfGenusFamilyPrestack.{u} g n)
      (semistableNMarkedCurveOfGenusFamilyPrestack.{u} g n) :=
  componentwiseStableMarkedCurveOfGenusFamilyPrestack.forgetComponentwiseStability.{u}
    (Fin n) g

/-- Forgetting exact `n`-pointed componentwise stability is fully faithful. -/
def componentwiseStableNMarkedCurveOfGenusFamilyPrestack.forgetComponentwiseStabilityFullyFaithful
    (g n : ℕ) :
    (componentwiseStableNMarkedCurveOfGenusFamilyPrestack.forgetComponentwiseStability.{u}
      g n).toFunctor.FullyFaithful :=
  componentwiseStableMarkedCurveOfGenusFamilyPrestack.forgetComponentwiseStabilityFullyFaithful.{u}
    (Fin n) g

open componentwiseStableNMarkedCurveOfGenusFamilyPrestack in
instance
    componentwiseStableNMarkedCurveOfGenusFamilyPrestack_forgetComponentwiseStability_full
    (g n : ℕ) :
    (componentwiseStableNMarkedCurveOfGenusFamilyPrestack.forgetComponentwiseStability.{u}
      g n).toFunctor.Full :=
  (forgetComponentwiseStabilityFullyFaithful.{u} g n).full

open componentwiseStableNMarkedCurveOfGenusFamilyPrestack in
instance
    componentwiseStableNMarkedCurveOfGenusFamilyPrestack_forgetComponentwiseStability_faithful
    (g n : ℕ) :
    (componentwiseStableNMarkedCurveOfGenusFamilyPrestack.forgetComponentwiseStability.{u}
      g n).toFunctor.Faithful :=
  (forgetComponentwiseStabilityFullyFaithful.{u} g n).faithful

end FamilyOfComponentwiseStableCurvesMarkedSchemeSpecialization

section FamilyOfStableCurvesSchemeSpecialization

/-- Supporting scheme-valued definition for Definition 6.3.20 (unpointed scheme-valued
specialization): the predicate that a scheme over an algebraically closed field is stable
over that specified field. -/
def stableCurveGeometricFiberPredicate : GeometricFiberPredicate.{u} :=
  fun K _ _ Z _ ↦ IsStableCurveOver K Z

/-- Stability is invariant under isomorphisms over the algebraically closed field. -/
instance stableCurveGeometricFiberPredicate_isClosedUnderIsomorphisms :
    stableCurveGeometricFiberPredicate.{u}.IsClosedUnderIsomorphisms where
  of_iso e h := h.isoOver e

/-- The morphism property that every geometric fibre is a stable curve. -/
def stableCurveFibersProperty : MorphismProperty Scheme.{u} :=
  geometricallyOver stableCurveGeometricFiberPredicate.{u}

/-- The stable-fibre condition is stable under arbitrary base change. -/
instance stableCurveFibersProperty_isStableUnderBaseChange :
    stableCurveFibersProperty.{u}.IsStableUnderBaseChange := by
  unfold stableCurveFibersProperty
  infer_instance

/-- The stable-fibre condition, evaluated on Mathlib's chosen geometric fibres. -/
lemma stableCurveFibersProperty_iff {C S : Scheme.{u}} {f : C ⟶ S} :
    stableCurveFibersProperty.{u} f ↔
      ∀ (K : Type u) [Field K] [IsAlgClosed K]
        (s : Spec (CommRingCat.of K) ⟶ S),
          @IsStableCurveOver K _ _ (pullback f s) ⟨pullback.snd f s⟩ := by
  unfold stableCurveFibersProperty
  simpa only [stableCurveGeometricFiberPredicate] using
    (geometricallyOver_iff (P := stableCurveGeometricFiberPredicate.{u}) (f := f))

/-- Supporting scheme-valued definition for Definition 6.3.20 (unpointed scheme-valued
specialization): a family of stable curves is a family of curves all of whose geometric
fibres are stable. -/
def familyOfStableCurvesProperty : MorphismProperty Scheme.{u} :=
  familyOfCurvesProperty.{u} ⊓ stableCurveFibersProperty.{u}

/-- Membership in the family-of-stable-curves property is the family condition together
with stability of every geometric fibre. -/
lemma mem_familyOfStableCurvesProperty_iff {C S : Scheme.{u}} (f : C ⟶ S) :
    familyOfStableCurvesProperty.{u} f ↔
      familyOfCurvesProperty.{u} f ∧ stableCurveFibersProperty.{u} f :=
  Iff.rfl

/-- Families of stable curves remain such after arbitrary base change. -/
instance familyOfStableCurvesProperty_isStableUnderBaseChange :
    familyOfStableCurvesProperty.{u}.IsStableUnderBaseChange := by
  unfold familyOfStableCurvesProperty
  infer_instance

/-- The defining stability condition on a geometric fibre presented by a pullback
square. -/
lemma isStableCurveOver_of_familyOfStableCurvesProperty {C S : Scheme.{u}} {f : C ⟶ S}
    (hf : familyOfStableCurvesProperty.{u} f) {K : Type u} [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ S) {Z : Scheme.{u}}
    [Z.Over (Spec (CommRingCat.of K))] (toC : Z ⟶ C)
    (h : IsPullback toC (Z ↘ Spec (CommRingCat.of K)) f s) :
    IsStableCurveOver K Z :=
  of_geometricallyOver hf.2 s toC h

/-- A stable family is, in particular, a nodal family. -/
lemma familyOfStableCurvesProperty_le_familyOfNodalCurvesProperty :
    familyOfStableCurvesProperty.{u} ≤ familyOfNodalCurvesProperty.{u} := by
  intro C S f hf
  refine ⟨hf.1, ?_⟩
  intro K _ _ s Z toC toK h
  exact (hf.2 s toC toK h).nodal

/-- The prestack of unpointed scheme-valued families of stable curves. -/
abbrev stableCurveFamilyPrestack : BasedCategory Scheme.{u} :=
  CategoryTheory.arrowCartesianProperty familyOfStableCurvesProperty.{u}

/-- Cartesian pullback makes scheme-valued families of stable curves a category fibred in
groupoids. -/
instance stableCurveFamilyPrestack_isFiberedInGroupoids :
    stableCurveFamilyPrestack.{u}.p.IsFiberedInGroupoids :=
  inferInstance

/-- Forgetting stability regards an unpointed stable family as a nodal family. -/
def stableCurveFamilyPrestack.forgetStability :
    BasedFunctor stableCurveFamilyPrestack.{u} nodalCurveFamilyPrestack.{u} :=
  CategoryTheory.arrowCartesianProperty.ιOfLE
    familyOfStableCurvesProperty_le_familyOfNodalCurvesProperty

/-- Forgetting stability is fully faithful. -/
def stableCurveFamilyPrestack.forgetStabilityFullyFaithful :
    stableCurveFamilyPrestack.forgetStability.{u}.toFunctor.FullyFaithful :=
  CategoryTheory.arrowCartesianProperty.fullyFaithfulιOfLE
    familyOfStableCurvesProperty_le_familyOfNodalCurvesProperty

instance stableCurveFamilyPrestack_forgetStability_full :
    stableCurveFamilyPrestack.forgetStability.{u}.toFunctor.Full :=
  stableCurveFamilyPrestack.forgetStabilityFullyFaithful.{u}.full

instance stableCurveFamilyPrestack_forgetStability_faithful :
    stableCurveFamilyPrestack.forgetStability.{u}.toFunctor.Faithful :=
  stableCurveFamilyPrestack.forgetStabilityFullyFaithful.{u}.faithful

/-- The predicate that a geometric fibre is a stable curve of genus `g` over its specified
algebraically closed field. -/
def stableCurveOfGenusGeometricFiberPredicate (g : ℕ) : GeometricFiberPredicate.{u} :=
  fun K _ _ Z _ ↦ IsStableCurveOfGenusOver K g Z

/-- Stability of fixed genus is invariant under isomorphisms over the algebraically closed
field. -/
instance stableCurveOfGenusGeometricFiberPredicate_isClosedUnderIsomorphisms (g : ℕ) :
    (stableCurveOfGenusGeometricFiberPredicate.{u} g).IsClosedUnderIsomorphisms where
  of_iso e h := h.isoOver e

/-- The morphism property that every geometric fibre is a stable curve of genus `g`. -/
def stableCurveOfGenusFibersProperty (g : ℕ) : MorphismProperty Scheme.{u} :=
  geometricallyOver (stableCurveOfGenusGeometricFiberPredicate.{u} g)

/-- Fixed-genus stable fibres are preserved by arbitrary base change. -/
instance stableCurveOfGenusFibersProperty_isStableUnderBaseChange (g : ℕ) :
    (stableCurveOfGenusFibersProperty.{u} g).IsStableUnderBaseChange := by
  unfold stableCurveOfGenusFibersProperty
  infer_instance

/-- The fixed-genus stable-fibre condition, evaluated on Mathlib's chosen geometric
fibres. -/
lemma stableCurveOfGenusFibersProperty_iff {g : ℕ} {C S : Scheme.{u}} {f : C ⟶ S} :
    stableCurveOfGenusFibersProperty.{u} g f ↔
      ∀ (K : Type u) [Field K] [IsAlgClosed K]
        (s : Spec (CommRingCat.of K) ⟶ S),
          @IsStableCurveOfGenusOver K _ _ g (pullback f s) ⟨pullback.snd f s⟩ := by
  unfold stableCurveOfGenusFibersProperty
  simpa only [stableCurveOfGenusGeometricFiberPredicate] using
    (geometricallyOver_iff
      (P := stableCurveOfGenusGeometricFiberPredicate.{u} g) (f := f))

/-- Supporting scheme-valued definition for Definition 6.3.20 (genus-`g`, unpointed,
scheme-valued specialization): a family of stable curves of genus `g` is a family of
curves whose every geometric fibre is stable of genus `g`. -/
def familyOfStableCurvesOfGenusProperty (g : ℕ) : MorphismProperty Scheme.{u} :=
  familyOfCurvesProperty.{u} ⊓ stableCurveOfGenusFibersProperty.{u} g

/-- Membership in the genus-`g` stable-family property. -/
lemma mem_familyOfStableCurvesOfGenusProperty_iff {g : ℕ} {C S : Scheme.{u}}
    (f : C ⟶ S) :
    familyOfStableCurvesOfGenusProperty.{u} g f ↔
      familyOfCurvesProperty.{u} f ∧ stableCurveOfGenusFibersProperty.{u} g f :=
  Iff.rfl

/-- Families of stable curves of genus `g` remain such after arbitrary base change. -/
instance familyOfStableCurvesOfGenusProperty_isStableUnderBaseChange (g : ℕ) :
    (familyOfStableCurvesOfGenusProperty.{u} g).IsStableUnderBaseChange := by
  unfold familyOfStableCurvesOfGenusProperty
  infer_instance

/-- The defining fixed-genus stability condition on a geometric fibre presented by a
pullback square. -/
lemma isStableCurveOfGenusOver_of_familyOfStableCurvesOfGenusProperty
    {g : ℕ} {C S : Scheme.{u}} {f : C ⟶ S}
    (hf : familyOfStableCurvesOfGenusProperty.{u} g f)
    {K : Type u} [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ S) {Z : Scheme.{u}}
    [Z.Over (Spec (CommRingCat.of K))] (toC : Z ⟶ C)
    (h : IsPullback toC (Z ↘ Spec (CommRingCat.of K)) f s) :
    IsStableCurveOfGenusOver K g Z :=
  of_geometricallyOver hf.2 s toC h

/-- A genus-`g` stable family is a stable family after forgetting its genus index. -/
lemma familyOfStableCurvesOfGenusProperty_le_familyOfStableCurvesProperty (g : ℕ) :
    familyOfStableCurvesOfGenusProperty.{u} g ≤ familyOfStableCurvesProperty.{u} := by
  intro C S f hf
  refine ⟨hf.1, ?_⟩
  intro K _ _ s Z toC toK h
  let _ : Z.Over (Spec (CommRingCat.of K)) := ⟨toK⟩
  exact (hf.2 s toC toK h).isStableCurveOver

/-- The prestack of unpointed scheme-valued families of stable curves of genus `g`. -/
abbrev stableCurveOfGenusFamilyPrestack (g : ℕ) : BasedCategory Scheme.{u} :=
  CategoryTheory.arrowCartesianProperty (familyOfStableCurvesOfGenusProperty.{u} g)

/-- Cartesian pullback makes genus-`g` stable families a category fibred in groupoids. -/
instance stableCurveOfGenusFamilyPrestack_isFiberedInGroupoids (g : ℕ) :
    (stableCurveOfGenusFamilyPrestack.{u} g).p.IsFiberedInGroupoids :=
  inferInstance

/-- Forgetting the fixed genus gives a fully faithful inclusion of unpointed stable-family
prestacks. -/
def stableCurveOfGenusFamilyPrestack.forgetGenus (g : ℕ) :
    BasedFunctor (stableCurveOfGenusFamilyPrestack.{u} g)
      stableCurveFamilyPrestack.{u} :=
  CategoryTheory.arrowCartesianProperty.ιOfLE
    (familyOfStableCurvesOfGenusProperty_le_familyOfStableCurvesProperty g)

/-- Forgetting the genus of an unpointed stable family is fully faithful. -/
def stableCurveOfGenusFamilyPrestack.forgetGenusFullyFaithful (g : ℕ) :
    (stableCurveOfGenusFamilyPrestack.forgetGenus.{u} g).toFunctor.FullyFaithful :=
  CategoryTheory.arrowCartesianProperty.fullyFaithfulιOfLE
    (familyOfStableCurvesOfGenusProperty_le_familyOfStableCurvesProperty g)

instance stableCurveOfGenusFamilyPrestack_forgetGenus_full (g : ℕ) :
    (stableCurveOfGenusFamilyPrestack.forgetGenus.{u} g).toFunctor.Full :=
  (stableCurveOfGenusFamilyPrestack.forgetGenusFullyFaithful.{u} g).full

instance stableCurveOfGenusFamilyPrestack_forgetGenus_faithful (g : ℕ) :
    (stableCurveOfGenusFamilyPrestack.forgetGenus.{u} g).toFunctor.Faithful :=
  (stableCurveOfGenusFamilyPrestack.forgetGenusFullyFaithful.{u} g).faithful

end FamilyOfStableCurvesSchemeSpecialization

section FamilyOfStableCurvesMarkedSchemeSpecialization

/-- Supporting scheme-valued definition for Definition 6.3.20 (scheme-valued marked
specialization): the predicate that an `I`-marked geometric fibre is stable, with its
specified maps to the algebraically closed field retained. -/
def stableMarkedCurveGeometricFiberPredicate (I : Type v) :
    MarkedGeometricFiberPredicate.{v, u} I :=
  fun K _ _ Z _ p ↦ IsStableMarkedCurveOver K Z p

/-- Marked stability is invariant under isomorphisms over the field that preserve every
marking. -/
instance stableMarkedCurveGeometricFiberPredicate_isClosedUnderIsomorphisms
    (I : Type v) :
    (stableMarkedCurveGeometricFiberPredicate.{u} I).IsClosedUnderIsomorphisms where
  of_iso e hmark h := h.isoOver e hmark

/-- The object property that every marked geometric fibre of an indexed marked family is
stable. -/
def stableMarkedCurveFibersProperty (I : Type v) :
    ObjectProperty (MarkedCartesianObj I familyOfCurvesProperty.{u}) :=
  markedGeometricallyOver (stableMarkedCurveGeometricFiberPredicate.{u} I)

/-- Marked geometric stability is preserved when a marked family is pulled back. -/
instance stableMarkedCurveFibersProperty_isStableUnderPullback (I : Type v) :
    MarkedCartesianObjectProperty.IsStableUnderPullback
      (stableMarkedCurveFibersProperty.{u} I) := by
  unfold stableMarkedCurveFibersProperty
  infer_instance

/-- The marked stable-fibre condition, evaluated on Mathlib's chosen pullback fibre. -/
lemma stableMarkedCurveFibersProperty_iff (I : Type v)
    (a : MarkedCartesianObj I familyOfCurvesProperty.{u}) :
    stableMarkedCurveFibersProperty.{u} I a ↔
      ∀ (K : Type u) [Field K] [IsAlgClosed K]
        (y : Spec (CommRingCat.of K) ⟶ a.right),
          @IsStableMarkedCurveOver K _ _ I (pullback a.hom y)
            ⟨pullback.snd a.hom y⟩ (a.pullbackGeometricFiberSection K y) := by
  unfold stableMarkedCurveFibersProperty
  simpa only [stableMarkedCurveGeometricFiberPredicate] using
    (markedGeometricallyOver_iff
      (Q := stableMarkedCurveGeometricFiberPredicate.{u} I) (a := a))

/-- The defining marked stability condition on an arbitrary displayed geometric fibre. -/
lemma isStableMarkedCurveOver_of_stableMarkedCurveFibersProperty
    {I : Type v} {a : MarkedCartesianObj I familyOfCurvesProperty.{u}}
    (ha : stableMarkedCurveFibersProperty.{u} I a)
    {K : Type u} [Field K] [IsAlgClosed K]
    (y : Spec (CommRingCat.of K) ⟶ a.right) {Z : Scheme.{u}}
    [Z.Over (Spec (CommRingCat.of K))] (fst : Z ⟶ a.left)
    (h : IsPullback fst (Z ↘ Spec (CommRingCat.of K)) a.hom y) :
    IsStableMarkedCurveOver K Z (fun i ↦ a.geometricFiberSection y fst h i) :=
  of_markedGeometricallyOver ha y fst h

/-- Supporting scheme-valued definition for Definition 6.3.20 (indexed, scheme-valued
specialization): the prestack of curve families whose marked geometric fibres are stable. -/
abbrev stableMarkedCurveFamilyPrestack (I : Type v) : BasedCategory Scheme.{u} :=
  markedGeometricSubprestack familyOfCurvesProperty.{u}
    (stableMarkedCurveGeometricFiberPredicate.{u} I)

/-- Marked stable curve families form a category fibred in groupoids. -/
instance stableMarkedCurveFamilyPrestack_isFiberedInGroupoids (I : Type v) :
    (stableMarkedCurveFamilyPrestack.{u} I).p.IsFiberedInGroupoids :=
  inferInstance

/-- Forgetting stability regards an indexed marked stable family as an indexed marked
nodal family, without discarding its markings. -/
noncomputable def stableMarkedCurveFamilyPrestack.forgetStability (I : Type v) :
    BasedFunctor (stableMarkedCurveFamilyPrestack.{u} I)
      (markedNodalCurveFamilyPrestack.{u} I) where
  obj a :=
    { left := a.obj.left
      right := a.obj.right
      hom := a.obj.hom
      property := ⟨a.obj.property, by
        intro K _ _ y Z fst snd h
        let _ : Z.Over (Spec (CommRingCat.of K)) := ⟨snd⟩
        exact (of_markedGeometricallyOver a.property y fst h).nodal⟩
      mark := a.obj.mark
      mark_fac := a.obj.mark_fac }
  map {a b} f :=
    { left := f.hom.left
      right := f.hom.right
      isPullback := f.hom.isPullback
      mark_naturality := f.hom.mark_naturality }
  map_id _ := rfl
  map_comp _ _ := rfl
  w := rfl

/-- Forgetting marked stability is fully faithful. -/
noncomputable def stableMarkedCurveFamilyPrestack.forgetStabilityFullyFaithful
    (I : Type v) :
    (stableMarkedCurveFamilyPrestack.forgetStability.{u} I).toFunctor.FullyFaithful where
  preimage f := ObjectProperty.homMk
    { left := f.left
      right := f.right
      isPullback := f.isPullback
      mark_naturality := f.mark_naturality }
  map_preimage _ := rfl
  preimage_map _ := by
    apply ObjectProperty.hom_ext
    apply MarkedCartesianHom.ext <;> rfl

instance stableMarkedCurveFamilyPrestack_forgetStability_faithful (I : Type v) :
    (stableMarkedCurveFamilyPrestack.forgetStability.{u} I).toFunctor.Faithful :=
  (stableMarkedCurveFamilyPrestack.forgetStabilityFullyFaithful.{u} I).faithful

instance stableMarkedCurveFamilyPrestack_forgetStability_full (I : Type v) :
    (stableMarkedCurveFamilyPrestack.forgetStability.{u} I).toFunctor.Full :=
  (stableMarkedCurveFamilyPrestack.forgetStabilityFullyFaithful.{u} I).full

/-- Supporting scheme-valued definition for Definition 6.3.20 (`n`-pointed, scheme-valued
specialization): the prestack of stable families with `n` ordered sections. -/
abbrev stableNMarkedCurveFamilyPrestack (n : ℕ) : BasedCategory Scheme.{u} :=
  stableMarkedCurveFamilyPrestack.{u} (Fin n)

/-- The predicate that an indexed marked geometric fibre is stable of genus `g`. -/
def stableMarkedCurveOfGenusGeometricFiberPredicate (I : Type v) (g : ℕ) :
    MarkedGeometricFiberPredicate.{v, u} I :=
  fun K _ _ Z _ p ↦ IsStableMarkedCurveOfGenusOver K g Z p

/-- Fixed-genus marked stability is invariant under marked isomorphisms over the field. -/
instance stableMarkedCurveOfGenusGeometricFiberPredicate_isClosedUnderIsomorphisms
    (I : Type v) (g : ℕ) :
    (stableMarkedCurveOfGenusGeometricFiberPredicate.{u} I g).IsClosedUnderIsomorphisms where
  of_iso e hmark h := h.isoOver e hmark

/-- The object property that every marked geometric fibre is stable of genus `g`. -/
def stableMarkedCurveOfGenusFibersProperty (I : Type v) (g : ℕ) :
    ObjectProperty (MarkedCartesianObj I familyOfCurvesProperty.{u}) :=
  markedGeometricallyOver (stableMarkedCurveOfGenusGeometricFiberPredicate.{u} I g)

/-- Fixed-genus marked geometric stability is preserved by pullback. -/
instance stableMarkedCurveOfGenusFibersProperty_isStableUnderPullback
    (I : Type v) (g : ℕ) :
    MarkedCartesianObjectProperty.IsStableUnderPullback
      (stableMarkedCurveOfGenusFibersProperty.{u} I g) := by
  unfold stableMarkedCurveOfGenusFibersProperty
  infer_instance

/-- The fixed-genus marked stable-fibre condition, evaluated on Mathlib's chosen
pullback fibre. -/
lemma stableMarkedCurveOfGenusFibersProperty_iff (I : Type v) (g : ℕ)
    (a : MarkedCartesianObj I familyOfCurvesProperty.{u}) :
    stableMarkedCurveOfGenusFibersProperty.{u} I g a ↔
      ∀ (K : Type u) [Field K] [IsAlgClosed K]
        (y : Spec (CommRingCat.of K) ⟶ a.right),
          @IsStableMarkedCurveOfGenusOver K _ _ I g (pullback a.hom y)
            ⟨pullback.snd a.hom y⟩ (a.pullbackGeometricFiberSection K y) := by
  unfold stableMarkedCurveOfGenusFibersProperty
  simpa only [stableMarkedCurveOfGenusGeometricFiberPredicate] using
    (markedGeometricallyOver_iff
      (Q := stableMarkedCurveOfGenusGeometricFiberPredicate.{u} I g) (a := a))

/-- The defining fixed-genus marked stability condition on an arbitrary displayed
geometric fibre. -/
lemma isStableMarkedCurveOfGenusOver_of_stableMarkedCurveOfGenusFibersProperty
    {I : Type v} {g : ℕ} {a : MarkedCartesianObj I familyOfCurvesProperty.{u}}
    (ha : stableMarkedCurveOfGenusFibersProperty.{u} I g a)
    {K : Type u} [Field K] [IsAlgClosed K]
    (y : Spec (CommRingCat.of K) ⟶ a.right) {Z : Scheme.{u}}
    [Z.Over (Spec (CommRingCat.of K))] (fst : Z ⟶ a.left)
    (h : IsPullback fst (Z ↘ Spec (CommRingCat.of K)) a.hom y) :
    IsStableMarkedCurveOfGenusOver K g Z
      (fun i ↦ a.geometricFiberSection y fst h i) :=
  of_markedGeometricallyOver ha y fst h

/-- Fixed-genus marked stable fibres are stable after forgetting the genus condition. -/
lemma stableMarkedCurveOfGenusFibersProperty_le_stableMarkedCurveFibersProperty
    (I : Type v) (g : ℕ) :
    stableMarkedCurveOfGenusFibersProperty.{u} I g ≤
      stableMarkedCurveFibersProperty.{u} I := by
  intro a ha K _ _ y Z _ fst h
  exact (ha y fst h).isStableMarkedCurveOver

/-- Supporting scheme-valued definition for Definition 6.3.20 (indexed genus-`g`,
scheme-valued specialization): the prestack of curve families whose marked geometric
fibres are stable of genus `g`. -/
abbrev stableMarkedCurveOfGenusFamilyPrestack (I : Type v) (g : ℕ) :
    BasedCategory Scheme.{u} :=
  markedGeometricSubprestack familyOfCurvesProperty.{u}
    (stableMarkedCurveOfGenusGeometricFiberPredicate.{u} I g)

/-- Fixed-genus marked stable curve families form a category fibred in groupoids. -/
instance stableMarkedCurveOfGenusFamilyPrestack_isFiberedInGroupoids
    (I : Type v) (g : ℕ) :
    (stableMarkedCurveOfGenusFamilyPrestack.{u} I g).p.IsFiberedInGroupoids :=
  inferInstance

/-- Supporting scheme-valued definition for Definition 6.3.20 (genus-`g`, `n`-pointed,
scheme-valued specialization): the prestack of genus-`g` stable families with `n` ordered
sections. -/
abbrev stableNMarkedCurveOfGenusFamilyPrestack (g n : ℕ) :
    BasedCategory Scheme.{u} :=
  stableMarkedCurveOfGenusFamilyPrestack.{u} (Fin n) g

/-- Forgetting the fixed genus gives a fully faithful inclusion of marked stable-family
prestacks. -/
def stableMarkedCurveOfGenusFamilyPrestack.forgetGenus (I : Type v) (g : ℕ) :
    BasedFunctor (stableMarkedCurveOfGenusFamilyPrestack.{u} I g)
      (stableMarkedCurveFamilyPrestack.{u} I) where
  toFunctor := ObjectProperty.ιOfLE
    (stableMarkedCurveOfGenusFibersProperty_le_stableMarkedCurveFibersProperty.{u} I g)
  w := rfl

/-- Forgetting the genus of a marked stable family is fully faithful. -/
def stableMarkedCurveOfGenusFamilyPrestack.forgetGenusFullyFaithful
    (I : Type v) (g : ℕ) :
    (stableMarkedCurveOfGenusFamilyPrestack.forgetGenus.{u} I g).toFunctor.FullyFaithful :=
  ObjectProperty.fullyFaithfulιOfLE
    (stableMarkedCurveOfGenusFibersProperty_le_stableMarkedCurveFibersProperty.{u} I g)

instance stableMarkedCurveOfGenusFamilyPrestack_forgetGenus_full
    (I : Type v) (g : ℕ) :
    (stableMarkedCurveOfGenusFamilyPrestack.forgetGenus.{u} I g).toFunctor.Full :=
  (stableMarkedCurveOfGenusFamilyPrestack.forgetGenusFullyFaithful.{u} I g).full

instance stableMarkedCurveOfGenusFamilyPrestack_forgetGenus_faithful
    (I : Type v) (g : ℕ) :
    (stableMarkedCurveOfGenusFamilyPrestack.forgetGenus.{u} I g).toFunctor.Faithful :=
  (stableMarkedCurveOfGenusFamilyPrestack.forgetGenusFullyFaithful.{u} I g).faithful

end FamilyOfStableCurvesMarkedSchemeSpecialization

end AlgebraicGeometry.Scheme
