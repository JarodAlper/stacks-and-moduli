module

public import Mathlib.AlgebraicGeometry.Geometrically.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Properties of geometric fibres with their base-field structure

Mathlib's `AlgebraicGeometry.geometrically` applies a property to the underlying scheme of
each field-valued fibre.  Some natural invariants instead use both an algebraically closed
field `K` and the fibre's specified structure morphism to `Spec K`; examples include
dimensions over `K` and the group of automorphisms over `K`.

This file provides the corresponding reusable morphism-property combinator.  Its definition
quantifies over arbitrary pullback presentations, so base-change stability is formal and does
not require an isomorphism-invariance hypothesis.  Such a hypothesis is needed only for the
more convenient characterization using Mathlib's chosen pullback objects.

## Main declarations

* `AlgebraicGeometry.GeometricFiberPredicate`: predicates on schemes over algebraically
  closed fields;
* `AlgebraicGeometry.geometricallyOver`: the morphism property asserting the predicate on
  every geometric fibre;
* `AlgebraicGeometry.geometricallyOver_isStableUnderBaseChange`: arbitrary base-change
  stability;
* `AlgebraicGeometry.geometricallyOver_iff`: evaluation on the chosen pullback fibres.
-/

@[expose] public section

open CategoryTheory Limits CommRingCat

universe u

namespace AlgebraicGeometry

/-- A predicate on a scheme equipped with a structure morphism to the spectrum of an
algebraically closed field.

The structure morphism is deliberately a typeclass argument, matching the standard
`Scheme.Over` API and allowing the predicate to mention constructions such as
`Scheme.AutOver`. -/
abbrev GeometricFiberPredicate :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (Z : Scheme.{u})
    [Z.Over (Spec (.of K))], Prop

namespace GeometricFiberPredicate

/-- A geometric-fibre predicate is closed under isomorphisms when it is invariant under
isomorphisms over the same algebraically closed field. -/
class IsClosedUnderIsomorphisms (P : GeometricFiberPredicate.{u}) : Prop where
  of_iso {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme.{u}}
    [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]
    (e : X.asOver (Spec (.of K)) ≅ Y.asOver (Spec (.of K))) : P K X → P K Y

/-- Transport a geometric-fibre predicate across an isomorphism over its field. -/
lemma prop_of_iso (P : GeometricFiberPredicate.{u}) [P.IsClosedUnderIsomorphisms]
    {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme.{u}}
    [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]
    (e : X.asOver (Spec (.of K)) ≅ Y.asOver (Spec (.of K))) (hX : P K X) : P K Y :=
  IsClosedUnderIsomorphisms.of_iso e hX

/-- For an isomorphism-invariant geometric-fibre predicate, the predicate holds on either
side of an isomorphism over the field if and only if it holds on the other. -/
lemma prop_iff_of_iso (P : GeometricFiberPredicate.{u}) [P.IsClosedUnderIsomorphisms]
    {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme.{u}}
    [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]
    (e : X.asOver (Spec (.of K)) ≅ Y.asOver (Spec (.of K))) : P K X ↔ P K Y :=
  ⟨P.prop_of_iso e, P.prop_of_iso e.symm⟩

/-- The pointwise conjunction of two geometric-fibre predicates. -/
def inf (P Q : GeometricFiberPredicate.{u}) : GeometricFiberPredicate.{u} :=
  fun K _ _ Z _ ↦ P K Z ∧ Q K Z

/-- Evaluating the conjunction of geometric-fibre predicates. -/
@[simp]
lemma inf_apply (P Q : GeometricFiberPredicate.{u}) (K : Type u) [Field K] [IsAlgClosed K]
    (Z : Scheme.{u}) [Z.Over (Spec (.of K))] : (P.inf Q) K Z ↔ P K Z ∧ Q K Z :=
  Iff.rfl

/-- The conjunction of two isomorphism-invariant geometric-fibre predicates is again
isomorphism-invariant. -/
instance inf_isClosedUnderIsomorphisms (P Q : GeometricFiberPredicate.{u})
    [P.IsClosedUnderIsomorphisms] [Q.IsClosedUnderIsomorphisms] :
    (inf P Q).IsClosedUnderIsomorphisms where
  of_iso e h := ⟨P.prop_of_iso e h.1, Q.prop_of_iso e h.2⟩

end GeometricFiberPredicate

/-- A morphism has property `geometricallyOver P` when every base change to the spectrum
of an algebraically closed field satisfies `P`, with the projection to that spectrum as its
specified field-scheme structure.

Quantifying over every pullback presentation makes this definition independent of chosen
limits without requiring `P` to be isomorphism-invariant. -/
def geometricallyOver (P : GeometricFiberPredicate.{u}) : MorphismProperty Scheme.{u} :=
  fun X Y f ↦ ∀ ⦃K : Type u⦄ [Field K] [IsAlgClosed K]
    (y : Spec (.of K) ⟶ Y) ⦃Z : Scheme.{u}⦄ (fst : Z ⟶ X) (snd : Z ⟶ Spec (.of K)),
      IsPullback fst snd f y → @P K _ _ Z ⟨snd⟩

/-- The quantifier form of `geometricallyOver`. -/
lemma geometricallyOver_def (P : GeometricFiberPredicate.{u}) :
    geometricallyOver P = fun X Y f ↦ ∀ ⦃K : Type u⦄ [Field K] [IsAlgClosed K]
      (y : Spec (.of K) ⟶ Y) ⦃Z : Scheme.{u}⦄ (fst : Z ⟶ X)
      (snd : Z ⟶ Spec (.of K)), IsPullback fst snd f y → @P K _ _ Z ⟨snd⟩ :=
  rfl

/-- Requiring two predicates on every geometric fibre is the conjunction of the two
associated morphism properties. -/
lemma geometricallyOver_inf (P Q : GeometricFiberPredicate.{u}) :
    geometricallyOver (P.inf Q) = geometricallyOver P ⊓ geometricallyOver Q := by
  ext X Y f
  constructor
  · intro h
    constructor
    · intro K _ _ y Z fst snd sq
      exact (h y fst snd sq).1
    · intro K _ _ y Z fst snd sq
      exact (h y fst snd sq).2
  · rintro ⟨hP, hQ⟩ K _ _ y Z fst snd sq
    exact ⟨hP y fst snd sq, hQ y fst snd sq⟩

/-- The defining property, evaluated on an arbitrary pullback square whose source already
carries the displayed structure morphism to `Spec K`. -/
lemma of_geometricallyOver {P : GeometricFiberPredicate.{u}} {X Y : Scheme.{u}}
    {f : X ⟶ Y} (hf : geometricallyOver P f) {K : Type u} [Field K] [IsAlgClosed K]
    (y : Spec (.of K) ⟶ Y) {Z : Scheme.{u}} [Z.Over (Spec (.of K))]
    (fst : Z ⟶ X) (h : IsPullback fst (Z ↘ Spec (.of K)) f y) : P K Z :=
  hf y fst _ h

/-- The defining property, evaluated on Mathlib's chosen pullback. -/
lemma pullback_of_geometricallyOver {P : GeometricFiberPredicate.{u}} {X Y : Scheme.{u}}
    {f : X ⟶ Y} (hf : geometricallyOver P f) (K : Type u) [Field K] [IsAlgClosed K]
    (y : Spec (.of K) ⟶ Y) :
    @P K _ _ (pullback f y) ⟨pullback.snd f y⟩ :=
  hf y _ _ (.of_hasPullback f y)

/-- The defining property, evaluated on the symmetrically ordered chosen pullback. -/
lemma pullback_of_geometricallyOver' {P : GeometricFiberPredicate.{u}} {X Y : Scheme.{u}}
    {f : X ⟶ Y} (hf : geometricallyOver P f) (K : Type u) [Field K] [IsAlgClosed K]
    (y : Spec (.of K) ⟶ Y) :
    @P K _ _ (pullback y f) ⟨pullback.fst y f⟩ :=
  hf y _ _ (.flip <| .of_hasPullback y f)

/-- A geometric-fibre predicate can be tested on Mathlib's chosen pullbacks once it is
invariant under isomorphisms over the algebraically closed field. -/
lemma geometricallyOver_iff {P : GeometricFiberPredicate.{u}}
    [P.IsClosedUnderIsomorphisms] {X Y : Scheme.{u}} {f : X ⟶ Y} :
    geometricallyOver P f ↔ ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (y : Spec (.of K) ⟶ Y), @P K _ _ (pullback f y) ⟨pullback.snd f y⟩ := by
  refine ⟨fun h K _ _ y ↦ pullback_of_geometricallyOver h K y, fun H ↦ ?_⟩
  intro K _ _ y Z fst snd h
  let e : Over.mk (pullback.snd f y) ≅ Over.mk snd :=
    Over.isoMk h.isoPullback.symm h.isoPullback_inv_snd
  exact @GeometricFiberPredicate.prop_of_iso P _ K _ _ (pullback f y) Z
    ⟨pullback.snd f y⟩ ⟨snd⟩ e (H K y)

/-- A morphism property constructed by `geometricallyOver` is preserved by arbitrary
base change. -/
instance geometricallyOver_isStableUnderBaseChange (P : GeometricFiberPredicate.{u}) :
    (geometricallyOver P).IsStableUnderBaseChange := by
  constructor
  intro X Y Y' S f g f' g' sq hg K _ _ y Z fst snd h
  exact hg (y ≫ f) (fst ≫ f') snd (h.paste_horiz sq)

/-- Over an algebraically closed field, the structure morphism itself satisfies `P` if it
satisfies `geometricallyOver P`. -/
lemma self_of_geometricallyOver {P : GeometricFiberPredicate.{u}} {K : Type u}
    [Field K] [IsAlgClosed K] {X : Scheme.{u}} [X.Over (Spec (.of K))]
    (h : geometricallyOver P (X ↘ Spec (.of K))) : P K X :=
  h (K := K) (y := 𝟙 _) (fst := 𝟙 X) (snd := X ↘ Spec (.of K))
    IsPullback.of_id_fst

end AlgebraicGeometry
