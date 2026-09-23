module

public import StacksAndModuli.API.AutFixing
public import StacksAndModuli.API.StableMarkedGraph
public import StacksAndModuli.«Section2.1-Intro».«part2.1.3-projective-space-and-hilbert-quot-functors»
public import StacksAndModuli.«Section6.2-Nodal»
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Endomorphism

/-!
# Stable curves: definition

This module follows the subsection "Definition and equivalences" of §6.3 (Stable curves)
of *Stacks and Moduli*, section label
`sec:stable-curves`.

The module defines the book's `n`-pointed prestable, semistable, and componentwise stable
curves of genus `g`. Rational subcurves are represented by closed immersions
`ℙ¹_k ⟶ C`, so the two componentwise conditions literally count their special points.
It also retains the finite-automorphism presentation selected as the primary stable-curve
interface, both unpointed and marked. Automorphisms are taken in the slice over `Spec k`,
and marked automorphisms fix every section.

The equivalence between componentwise stability and finite automorphisms is the content of
Proposition 6.3.5 and is not proved in this module.

## Canonical book declarations

- `AlgebraicGeometry.Scheme.IsPrestableNMarkedCurveOfGenusOver`: the exact
  `n`-pointed prestable-curve predicate of Definition 6.3.2.
- `AlgebraicGeometry.Scheme.IsSemistableNMarkedCurveOfGenusOver`: the exact
  semistable predicate.
- `AlgebraicGeometry.Scheme.IsComponentwiseStableNMarkedCurveOfGenusOver`: the exact
  componentwise stable predicate.
- `AlgebraicGeometry.Scheme.IsStableNMarkedCurveOfGenusOver`: the substantive
  finite-automorphism formulation of stability.
- `two_mul_genus_add_markings_le_two_iff_exceptional`: the numerical equivalence stated
  in Remark 6.3.3.

## Additional definitions

- `AlgebraicGeometry.Scheme.AutOver`: automorphisms of a scheme preserving its map to a
  fixed base scheme.
- `AlgebraicGeometry.Scheme.SectionOver`: sections of a scheme over a base.
- `AlgebraicGeometry.Scheme.IsSpecialPoint`: nodes and marked points of a marked curve.
- `AlgebraicGeometry.Scheme.IsPrestableMarkedCurveOfGenusOver`: a reusable
  arbitrary-index extension of prestability.
- `AlgebraicGeometry.Scheme.IsGeometricallyPrestableMarkedCurveOfGenusOver`: the
  arbitrary-field extension used by the rational-tail and bridge subsection, with
  geometric nodality in place of split nodality.
- `AlgebraicGeometry.Scheme.IsPrestableNMarkedCurveOfGenusOver`: the book's exact
  `n`-pointed prestable-curve predicate.
- `AlgebraicGeometry.Scheme.RationalSubcurveOver`: a copy of `ℙ¹_k` embedded as a closed
  subcurve, with its induced set of special points.
- `AlgebraicGeometry.Scheme.IsSemistableNMarkedCurveOfGenusOver`: the exact componentwise
  semistability predicate.
- `AlgebraicGeometry.Scheme.IsComponentwiseStableNMarkedCurveOfGenusOver`: the exact
  componentwise stability predicate, kept distinct from the finite-automorphism interface.
- `IsSemistableMarkedCurveOfGenusOver` and
  `IsComponentwiseStableMarkedCurveOfGenusOver`: their arbitrary-index extensions.
- `AlgebraicGeometry.Scheme.AutOverFixing`: base-preserving automorphisms fixing every
  section in an indexed family.
- `AlgebraicGeometry.Scheme.IsStableCurveOver`: a connected proper nodal curve over an
  algebraically closed field with finite automorphism group over that field.
- `AlgebraicGeometry.Scheme.IsStableCurveOfGenusOver`: the genus-`g` stable-curve predicate.
- `AlgebraicGeometry.Scheme.IsStableMarkedCurveOver` and
  `AlgebraicGeometry.Scheme.IsStableMarkedCurveOfGenusOver`: the corresponding predicates
  with distinct smooth markings.
- `VertexWeightedMarkedGraph` and `StableMarkedGraph`: reusable combinatorial models for
  the weighted marked graphs appearing later in the subsection.

## Supporting and derived results

- `AlgebraicGeometry.Scheme.isPrestableMarkedCurveOfGenusOver_isoOver_iff`: the reusable
  arbitrary-index predicate is invariant under marked isomorphisms.
- `AlgebraicGeometry.Scheme.isPrestableNMarkedCurveOfGenusOver_iff`: the prestable-curve
  conditions, unfolded.
- `isGeometricallyPrestableMarkedCurveOfGenusOver_iff_isPrestableMarkedCurveOfGenusOver`:
  over an algebraically closed field, the arbitrary-field and split-node prestable
  interfaces agree.
- `isPrestableNMarkedCurveOfGenusOver_iff_isPrestableMarkedCurveOfGenusOver`: the exact
  `Fin n` predicate agrees with the arbitrary-index extension.
- `AlgebraicGeometry.Scheme.isPrestableNMarkedCurveOfGenusOver_isoOver_iff`: prestability
  is invariant under marked isomorphisms over the ground field.
- `RationalSubcurveOver.two_le_specialPoints_encard_iff` and
  `RationalSubcurveOver.three_le_specialPoints_encard_iff`: witness forms of the two
  special-point bounds.
- `isSemistableNMarkedCurveOfGenusOver_iff_exists_two_specialPoints` and
  `isComponentwiseStableNMarkedCurveOfGenusOver_iff_exists_three_specialPoints`: the
  exact curve predicates in concrete witness form.
- `IsComponentwiseStableNMarkedCurveOfGenusOver.isSemistable`: componentwise stable curves
  are semistable.
- `isSemistableNMarkedCurveOfGenusOver_perm_iff` and
  `isComponentwiseStableNMarkedCurveOfGenusOver_perm_iff`: both exact predicates are
  invariant under permutations of their ordered markings.
- `isSemistableNMarkedCurveOfGenusOver_isoOver_iff` and
  `isComponentwiseStableNMarkedCurveOfGenusOver_isoOver_iff`: the exact componentwise
  predicates are invariant under marked isomorphisms.
- `IsPrestableNMarkedCurveOfGenusOver.isStableNMarkedCurveOfGenusOver_iff_finite_aut`:
  the finite-automorphism stability criterion under the exact prestable hypotheses.
- `AlgebraicGeometry.Scheme.isStableCurveOfGenusOver_iff`: the defining conditions,
  unfolded.
- `AlgebraicGeometry.Scheme.isStableCurveOfGenusOver_iff_geometricallyNodal`: the
  genus-`g` definition unfolded using the book's geometric node predicate.
- `AlgebraicGeometry.Scheme.isStableCurveOver_iff_geometricallyNodal`: the nodality field
  in the stable-curve definition is exactly the book's geometric node condition specialized
  to an algebraically closed field.
- `AlgebraicGeometry.Scheme.isStableCurveOfGenusOver_iff_finite_aut`: for a connected proper
  nodal curve of genus `g`, stability is equivalent to finiteness of its base-preserving
  automorphism group.
- `IsStableCurveOver.bijective_baseRingHom`: a stable curve has no nonconstant global
  functions, so its global-sections ring is its algebraically closed ground field.
- `IsStableCurveOver.genusOver_eq_genus` and
  `IsStableCurveOver.arithmeticGenus_eq_genusOver`: the three genus conventions agree for
  stable curves.
- `AlgebraicGeometry.Scheme.isStableMarkedCurveOfGenusOver_iff_finite_aut`: the indexed
  marked analogue using the automorphisms fixing every section.
- `IsStableCurveOver.marked` and `IsStableCurveOfGenusOver.marked`: adding distinct
  smooth sections to an unpointed stable curve preserves finite-automorphism stability.
- `IsStableMarkedCurveOver.of_subfamily`: enlarging a stable marking family by distinct
  smooth sections preserves stability.
- `AlgebraicGeometry.Scheme.finite_aut_over_iff_of_iso`: finiteness of the automorphism group
  is invariant under isomorphism over the base.
- `AlgebraicGeometry.Scheme.isStableMarkedCurveOver_reindex_iff`: marked stability is
  invariant under an equivalence of marking index types.
- `AlgebraicGeometry.Scheme.isStableMarkedCurveOver_iff_of_isEmpty`: empty marking families
  recover unpointed stability.
- `not_stableMarkedGraph_of_exceptional_pair`: the graph-level reduction toward the
  curve-level nonexistence assertion in Remark 6.3.3.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u v w

namespace AlgebraicGeometry.Scheme

section DefStableCurves

/-- **§6.3, unlabelled paragraph following Definition 6.3.2**: the abstract group of
automorphisms of a scheme `C` over a fixed base scheme `S`.

Bundling `C → S` as an object of `Over S` ensures that every automorphism commutes with
the structure morphism. In particular, for `S = Spec k` these are `k`-automorphisms, not
arbitrary automorphisms of the underlying scheme. -/
abbrev AutOver (C S : Scheme.{u}) [C.Over S] : Type u :=
  CategoryTheory.Aut (C.asOver S)

/-- Background definition for Definition 6.3.2 (unpointed, finite-automorphism formulation):
a stable curve over an algebraically closed field `k` is a connected proper nodal curve
whose abstract group of `k`-automorphisms is finite.

This uses the finite-automorphism condition equivalent to the book's componentwise
definition by Proposition 6.3.5. It treats the unpointed case
and uses properness in place of projectivity, as in the equivalent formulation selected
here. -/
class IsStableCurveOver (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))] : Prop where
  nodal : IsNodalCurveOver k C
  proper : IsProper (C ↘ Spec (CommRingCat.of k))
  connected : ConnectedSpace C
  finiteAut : Finite (C.AutOver (Spec (CommRingCat.of k)))

/-- API lemma for Definition 6.3.2, reducedness consequence: a stable curve
is reduced. -/
lemma IsStableCurveOver.isReduced {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    (h : IsStableCurveOver k C) : IsReduced C :=
  h.nodal.isReduced

/-- API lemma for Definition 6.3.2, curve consequence: a stable curve is a
curve over its ground field. -/
lemma IsStableCurveOver.isCurveOver {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    (h : IsStableCurveOver k C) : IsCurveOver k C :=
  h.nodal.isCurve

/-- API lemma for Definition 6.3.2, finiteness consequence: a stable curve is
Noetherian. -/
lemma IsStableCurveOver.isNoetherian {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    (h : IsStableCurveOver k C) : IsNoetherian C :=
  h.nodal.isNoetherian

/-- API lemma for Definition 6.3.2, global-functions consequence: the
structure map `k ⟶ Γ(C, 𝒯_C)` of a stable curve is bijective. -/
lemma IsStableCurveOver.bijective_baseRingHom
    {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    (h : IsStableCurveOver k C) :
    Function.Bijective (C.baseRingHom (CommRingCat.of k)) := by
  let _ : IsReduced C := h.isReduced
  let _ : ConnectedSpace C := h.connected
  let _ : IsProper (C ↘ Spec (CommRingCat.of k)) := h.proper
  exact bijective_baseRingHom_of_isAlgClosed_of_isReduced_of_connected k C

/-- API lemma for Definition 6.3.2, genus comparison: for a stable curve,
the `k`-linear genus used in the book agrees with the intrinsic genus. -/
lemma IsStableCurveOver.genusOver_eq_genus
    {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    (h : IsStableCurveOver k C) : genusOver k C = C.genus :=
  Scheme.genusOver_eq_genus k C h.bijective_baseRingHom

/-- API lemma for Definition 6.3.2, Euler-characteristic comparison: for a
stable curve, the book's arithmetic genus `1 - χ(C, 𝒯_C)` is its `k`-linear genus. -/
lemma IsStableCurveOver.arithmeticGenus_eq_genusOver
    {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    (h : IsStableCurveOver k C) :
    arithmeticGenus k C = (genusOver k C : ℤ) :=
  Scheme.arithmeticGenus_eq_genusOver k C h.bijective_baseRingHom

/-- API lemma for Definition 6.3.2, unfolded: stability means nodality,
properness, connectedness, and finiteness of the group of automorphisms over `Spec k`. -/
lemma isStableCurveOver_iff (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))] :
    IsStableCurveOver k C ↔
      IsNodalCurveOver k C ∧
        IsProper (C ↘ Spec (CommRingCat.of k)) ∧
          ConnectedSpace C ∧ Finite (C.AutOver (Spec (CommRingCat.of k))) :=
  ⟨fun h ↦ ⟨h.nodal, h.proper, h.connected, h.finiteAut⟩,
    fun h ↦ ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩

/-- API lemma for Definition 6.3.2, geometric-node formulation: over an
algebraically closed field, the finite-automorphism definition may equivalently use the
book's arbitrary-field geometric nodality predicate. -/
lemma isStableCurveOver_iff_geometricallyNodal
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))] :
    IsStableCurveOver k C ↔
      IsGeometricallyNodalCurveOver k C ∧
        IsProper (C ↘ Spec (CommRingCat.of k)) ∧
          ConnectedSpace C ∧ Finite (C.AutOver (Spec (CommRingCat.of k))) := by
  rw [isStableCurveOver_iff,
    isGeometricallyNodalCurveOver_iff_isNodalCurveOver]

/-- API lemma for Definition 6.3.2, geometric-node consequence: a stable
curve satisfies the book's arbitrary-field geometric nodality predicate. -/
lemma IsStableCurveOver.isGeometricallyNodalCurveOver
    {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    (h : IsStableCurveOver k C) : IsGeometricallyNodalCurveOver k C :=
  h.nodal.isGeometricallyNodalCurveOver

/-- Background definition for Definition 6.3.2 (genus-`g` unpointed form): a stable curve
of genus `g` is a stable curve whose `k`-genus `dim_k H¹(C, 𝒪_C)` equals `g`.

The genus is stated as `genusOver k C`, exactly the `k`-linear cohomological genus used
in the book. For stable curves this agrees with both the intrinsic genus and the
Euler-characteristic arithmetic genus; see `IsStableCurveOfGenusOver.intrinsic_genus_eq`
and `IsStableCurveOfGenusOver.arithmeticGenus_eq`. -/
def IsStableCurveOfGenusOver (k : Type u) [Field k] [IsAlgClosed k] (g : ℕ)
    (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))] : Prop :=
  IsStableCurveOver k C ∧ genusOver k C = g

/-- API lemma for Definition 6.3.2 (genus-`g` unpointed form), unfolded. -/
lemma isStableCurveOfGenusOver_iff (k : Type u) [Field k] [IsAlgClosed k] (g : ℕ)
    (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))] :
    IsStableCurveOfGenusOver k g C ↔
      IsNodalCurveOver k C ∧
        IsProper (C ↘ Spec (CommRingCat.of k)) ∧
          ConnectedSpace C ∧ genusOver k C = g ∧
            Finite (C.AutOver (Spec (CommRingCat.of k))) := by
  rw [IsStableCurveOfGenusOver, isStableCurveOver_iff]
  tauto

/-- API lemma for Definition 6.3.2 (genus-`g`, geometric-node
formulation): a stable curve of genus `g` is exactly a connected proper geometrically
nodal curve of `k`-genus `g` with finite automorphism group. -/
lemma isStableCurveOfGenusOver_iff_geometricallyNodal
    (k : Type u) [Field k] [IsAlgClosed k] (g : ℕ)
    (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))] :
    IsStableCurveOfGenusOver k g C ↔
      IsGeometricallyNodalCurveOver k C ∧
        IsProper (C ↘ Spec (CommRingCat.of k)) ∧
          ConnectedSpace C ∧ genusOver k C = g ∧
            Finite (C.AutOver (Spec (CommRingCat.of k))) := by
  rw [IsStableCurveOfGenusOver, isStableCurveOver_iff_geometricallyNodal]
  tauto

/-- A stable curve of genus `g` is stable after forgetting its specified genus. -/
lemma IsStableCurveOfGenusOver.isStableCurveOver {k : Type u} [Field k] [IsAlgClosed k]
    {g : ℕ} {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    (h : IsStableCurveOfGenusOver k g C) : IsStableCurveOver k C :=
  h.1

/-- A stable curve of genus `g` has `k`-genus equal to `g`. -/
lemma IsStableCurveOfGenusOver.genus_eq {k : Type u} [Field k] [IsAlgClosed k]
    {g : ℕ} {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    (h : IsStableCurveOfGenusOver k g C) : genusOver k C = g :=
  h.2

/-- A stable curve of genus `g` is nodal. -/
lemma IsStableCurveOfGenusOver.nodal {k : Type u} [Field k] [IsAlgClosed k]
    {g : ℕ} {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    (h : IsStableCurveOfGenusOver k g C) : IsNodalCurveOver k C :=
  h.isStableCurveOver.nodal

/-- A stable curve of genus `g` satisfies the book's geometric nodality predicate. -/
lemma IsStableCurveOfGenusOver.isGeometricallyNodalCurveOver
    {k : Type u} [Field k] [IsAlgClosed k]
    {g : ℕ} {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    (h : IsStableCurveOfGenusOver k g C) :
    IsGeometricallyNodalCurveOver k C :=
  h.isStableCurveOver.isGeometricallyNodalCurveOver

/-- API lemma for Definition 6.3.2, reducedness consequence: a stable curve
of fixed genus is reduced. -/
lemma IsStableCurveOfGenusOver.isReduced {k : Type u} [Field k] [IsAlgClosed k]
    {g : ℕ} {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    (h : IsStableCurveOfGenusOver k g C) : IsReduced C :=
  h.nodal.isReduced

/-- A stable curve of genus `g` is a curve over its ground field. -/
lemma IsStableCurveOfGenusOver.isCurveOver {k : Type u} [Field k] [IsAlgClosed k]
    {g : ℕ} {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    (h : IsStableCurveOfGenusOver k g C) : IsCurveOver k C :=
  h.nodal.isCurve

/-- A stable curve of genus `g` is Noetherian. -/
lemma IsStableCurveOfGenusOver.isNoetherian {k : Type u} [Field k] [IsAlgClosed k]
    {g : ℕ} {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    (h : IsStableCurveOfGenusOver k g C) : IsNoetherian C :=
  h.nodal.isNoetherian

/-- A stable curve of genus `g` has intrinsic genus `g`. -/
lemma IsStableCurveOfGenusOver.intrinsic_genus_eq
    {k : Type u} [Field k] [IsAlgClosed k]
    {g : ℕ} {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    (h : IsStableCurveOfGenusOver k g C) : C.genus = g := by
  rw [← h.isStableCurveOver.genusOver_eq_genus, h.genus_eq]

/-- A stable curve of genus `g` has arithmetic genus `g`. -/
lemma IsStableCurveOfGenusOver.arithmeticGenus_eq
    {k : Type u} [Field k] [IsAlgClosed k]
    {g : ℕ} {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    (h : IsStableCurveOfGenusOver k g C) : arithmeticGenus k C = g := by
  rw [h.isStableCurveOver.arithmeticGenus_eq_genusOver, h.genus_eq]

/-- A stable curve of genus `g` is proper over its ground field. -/
lemma IsStableCurveOfGenusOver.proper {k : Type u} [Field k] [IsAlgClosed k]
    {g : ℕ} {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    (h : IsStableCurveOfGenusOver k g C) : IsProper (C ↘ Spec (CommRingCat.of k)) :=
  h.isStableCurveOver.proper

/-- A stable curve of genus `g` is connected. -/
lemma IsStableCurveOfGenusOver.connected {k : Type u} [Field k] [IsAlgClosed k]
    {g : ℕ} {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    (h : IsStableCurveOfGenusOver k g C) : ConnectedSpace C :=
  h.isStableCurveOver.connected

/-- A stable curve of genus `g` has finitely many automorphisms over its ground field. -/
lemma IsStableCurveOfGenusOver.finiteAut {k : Type u} [Field k] [IsAlgClosed k]
    {g : ℕ} {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    (h : IsStableCurveOfGenusOver k g C) :
    Finite (C.AutOver (Spec (CommRingCat.of k))) :=
  h.isStableCurveOver.finiteAut

/-- In the finite-automorphism presentation selected for the definition, a connected proper
nodal curve of genus `g` is stable exactly when its abstract group of automorphisms over the
ground field is finite. -/
theorem isStableCurveOfGenusOver_iff_finite_aut (k : Type u) [Field k] [IsAlgClosed k]
    (g : ℕ) (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))]
    [IsNodalCurveOver k C] [IsProper (C ↘ Spec (CommRingCat.of k))]
    [ConnectedSpace C] (hg : genusOver k C = g) :
    IsStableCurveOfGenusOver k g C ↔
      Finite (C.AutOver (Spec (CommRingCat.of k))) := by
  constructor
  · exact fun h ↦ h.isStableCurveOver.finiteAut
  · intro h
    exact ⟨⟨inferInstance, inferInstance, inferInstance, h⟩, hg⟩

/-- Isomorphic schemes over a base have simultaneously finite automorphism groups over that
base. -/
lemma finite_aut_over_iff_of_iso {S C D : Scheme.{u}} [C.Over S] [D.Over S]
    (e : C.asOver S ≅ D.asOver S) :
    Finite (C.AutOver S) ↔ Finite (D.AutOver S) :=
  (CategoryTheory.Aut.autMulEquivOfIso e).finite_iff

/-- Stability is preserved by an isomorphism over the ground field. -/
theorem IsStableCurveOver.isoOver {k : Type u} [Field k] [IsAlgClosed k]
    {C D : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    [D.Over (Spec (CommRingCat.of k))] (h : IsStableCurveOver k C)
    (e : C.asOver (Spec (CommRingCat.of k)) ≅
      D.asOver (Spec (CommRingCat.of k))) :
    IsStableCurveOver k D := by
  let E : C ≅ D := (Over.forget (Spec (CommRingCat.of k))).mapIso e
  refine ⟨h.nodal.isoOver e, ?_, ?_, (finite_aut_over_iff_of_iso e).mp h.finiteAut⟩
  · let _ : IsProper (C ↘ Spec (CommRingCat.of k)) := h.proper
    have he : E.inv ≫ (C ↘ Spec (CommRingCat.of k)) =
        D ↘ Spec (CommRingCat.of k) := e.inv.w
    rw [← he]
    infer_instance
  · exact (E.hom.homeomorph.connectedSpace_iff).mp h.connected

/-- Isomorphic curves over an algebraically closed field are simultaneously stable. -/
theorem isStableCurveOver_isoOver_iff {k : Type u} [Field k] [IsAlgClosed k]
    {C D : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    [D.Over (Spec (CommRingCat.of k))]
    (e : C.asOver (Spec (CommRingCat.of k)) ≅
      D.asOver (Spec (CommRingCat.of k))) :
    IsStableCurveOver k C ↔ IsStableCurveOver k D :=
  ⟨fun h ↦ h.isoOver e, fun h ↦ h.isoOver e.symm⟩

/-- Stable curves of a fixed genus are preserved by isomorphisms over the ground field. -/
theorem IsStableCurveOfGenusOver.isoOver {k : Type u} [Field k] [IsAlgClosed k]
    {g : ℕ} {C D : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    [D.Over (Spec (CommRingCat.of k))] (h : IsStableCurveOfGenusOver k g C)
    (e : C.asOver (Spec (CommRingCat.of k)) ≅
      D.asOver (Spec (CommRingCat.of k))) :
    IsStableCurveOfGenusOver k g D :=
  ⟨h.isStableCurveOver.isoOver e, (genusOver_eq_of_isoOver k e).symm.trans h.genus_eq⟩

/-- Isomorphic curves over an algebraically closed field are simultaneously stable of genus
`g`. -/
theorem isStableCurveOfGenusOver_isoOver_iff {k : Type u} [Field k]
    [IsAlgClosed k] {g : ℕ} {C D : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [D.Over (Spec (CommRingCat.of k))]
    (e : C.asOver (Spec (CommRingCat.of k)) ≅
      D.asOver (Spec (CommRingCat.of k))) :
    IsStableCurveOfGenusOver k g C ↔ IsStableCurveOfGenusOver k g D :=
  ⟨fun h ↦ h.isoOver e, fun h ↦ h.isoOver e.symm⟩

/-- A section of a scheme `C` over a base scheme `S`, bundled as a morphism in `Over S`.

The source `Over.mk (𝟙 S)` represents `S` over itself, so the commutative-triangle
condition on an `Over` morphism is precisely the section equation. -/
abbrev SectionOver (C S : Scheme.{u}) [C.Over S] : Type u :=
  Over.mk (𝟙 S) ⟶ C.asOver S

/-- The underlying scheme morphism of a bundled section satisfies the section equation. -/
lemma SectionOver.fac {C S : Scheme.{u}} [C.Over S] (p : C.SectionOver S) :
    p.left ≫ (C ↘ S) = 𝟙 S :=
  p.w

/-- The underlying point of a section over the spectrum of a field. -/
noncomputable def SectionOver.point {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    (p : C.SectionOver (Spec (CommRingCat.of k))) : C :=
  p.left (IsLocalRing.closedPoint k)

/-- Corresponding sections under an isomorphism over a field determine corresponding
underlying points. -/
lemma SectionOver.map_point {k : Type u} [Field k] {C D : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [D.Over (Spec (CommRingCat.of k))]
    (e : C.asOver (Spec (CommRingCat.of k)) ≅
      D.asOver (Spec (CommRingCat.of k)))
    (p : C.SectionOver (Spec (CommRingCat.of k)))
    (q : D.SectionOver (Spec (CommRingCat.of k))) (h : p ≫ e.hom = q) :
    ((Over.forget (Spec (CommRingCat.of k))).mapIso e).hom p.point = q.point := by
  have hmap := congrArg
    (fun r : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
        D.asOver (Spec (CommRingCat.of k)) ↦
      r.left (IsLocalRing.closedPoint k)) h
  exact hmap

/-- **§6.3, unlabelled paragraph preceding Definition 6.3.2**: a point of a marked
curve is special when it is either a node or one of the marked points. -/
def IsSpecialPoint (k : Type u) [Field k] {I : Type v} (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))]
    (p : I → C.SectionOver (Spec (CommRingCat.of k))) (x : C) : Prop :=
  C.IsSplitNodeAt k x ∨ ∃ i, (p i).point = x

/-- The defining node-or-marking characterization of a special point. -/
lemma isSpecialPoint_iff (k : Type u) [Field k] {I : Type v} (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))]
    (p : I → C.SectionOver (Spec (CommRingCat.of k))) (x : C) :
    C.IsSpecialPoint k p x ↔ C.IsSplitNodeAt k x ∨ ∃ i, (p i).point = x :=
  Iff.rfl

/-- Reindexing a marking family by an equivalence does not change its special points. -/
theorem isSpecialPoint_reindex_iff {k : Type u} [Field k]
    {I : Type v} {J : Type w} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    (p : I → C.SectionOver (Spec (CommRingCat.of k))) (e : J ≃ I) (x : C) :
    C.IsSpecialPoint k (p ∘ e) x ↔ C.IsSpecialPoint k p x := by
  unfold IsSpecialPoint
  constructor
  · rintro (hnode | ⟨j, hj⟩)
    · exact Or.inl hnode
    · exact Or.inr ⟨e j, hj⟩
  · rintro (hnode | ⟨i, hi⟩)
    · exact Or.inl hnode
    · exact Or.inr ⟨e.symm i, by simpa using hi⟩

/-- Special points are preserved and reflected by marked isomorphisms over the ground
field. -/
theorem isSpecialPoint_isoOver_iff {k : Type u} [Field k]
    {I : Type v} {C D : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [D.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    {q : I → D.SectionOver (Spec (CommRingCat.of k))}
    (e : C.asOver (Spec (CommRingCat.of k)) ≅
      D.asOver (Spec (CommRingCat.of k)))
    (hpq : ∀ i, p i ≫ e.hom = q i) (x : C) :
    C.IsSpecialPoint k p x ↔
      D.IsSpecialPoint k q
        (((Over.forget (Spec (CommRingCat.of k))).mapIso e).hom x) := by
  let E : C ≅ D := (Over.forget (Spec (CommRingCat.of k))).mapIso e
  constructor
  · rintro (hnode | ⟨i, hi⟩)
    · exact Or.inl ((isSplitNodeAt_isoOver_iff e x).mp hnode)
    · refine Or.inr ⟨i, ?_⟩
      exact ((p i).map_point e (q i) (hpq i)).symm.trans (congrArg E.hom hi)
  · rintro (hnode | ⟨i, hi⟩)
    · exact Or.inl ((isSplitNodeAt_isoOver_iff e x).mpr hnode)
    · refine Or.inr ⟨i, ?_⟩
      apply E.hom.homeomorph.injective
      exact ((p i).map_point e (q i) (hpq i)).trans hi

/-- Background definition for Definition 6.3.2 (arbitrary-field extension used before
Lemma 6.3.13): an `I`-marked geometrically prestable curve of genus `g` is a connected,
geometrically nodal, H-projective curve of genus `g` with distinct smooth markings; in
genus one the marking type must be nonempty.

This is the exact arbitrary-field extension implicit in the rational-tail and bridge
subsection. Over an algebraically closed field it agrees with
`IsPrestableMarkedCurveOfGenusOver`. -/
class IsGeometricallyPrestableMarkedCurveOfGenusOver
    (k : Type u) [Field k] {I : Type v} (g : ℕ) (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))]
    (p : I → C.SectionOver (Spec (CommRingCat.of k))) : Prop where
  nodal : IsGeometricallyNodalCurveOver k C
  projective : IsHProjective (C ↘ Spec (CommRingCat.of k))
  connected : ConnectedSpace C
  genus_eq : genusOver k C = g
  nonempty_of_genus_eq_one : g = 1 → Nonempty I
  mark_point_injective : Function.Injective (fun i ↦ (p i).point)
  mark_smooth : ∀ i,
    ((C ↘ Spec (CommRingCat.of k)).stalkMap (p i).point).hom.FormallySmooth

/-- API lemma for Definition 6.3.2 (arbitrary-field extension), unfolded. -/
lemma isGeometricallyPrestableMarkedCurveOfGenusOver_iff
    (k : Type u) [Field k] {I : Type v} (g : ℕ) (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))]
    (p : I → C.SectionOver (Spec (CommRingCat.of k))) :
    IsGeometricallyPrestableMarkedCurveOfGenusOver k g C p ↔
      IsGeometricallyNodalCurveOver k C ∧
        IsHProjective (C ↘ Spec (CommRingCat.of k)) ∧
          ConnectedSpace C ∧ genusOver k C = g ∧ (g = 1 → Nonempty I) ∧
            Function.Injective (fun i ↦ (p i).point) ∧
              ∀ i, ((C ↘ Spec (CommRingCat.of k)).stalkMap
                (p i).point).hom.FormallySmooth := by
  constructor
  · intro h
    exact ⟨h.nodal, h.projective, h.connected, h.genus_eq,
      h.nonempty_of_genus_eq_one, h.mark_point_injective, h.mark_smooth⟩
  · rintro ⟨hnodal, hprojective, hconnected, hgenus, hnonempty, hinjective, hsmooth⟩
    exact ⟨hnodal, hprojective, hconnected, hgenus, hnonempty, hinjective, hsmooth⟩

/-- Background definition for Definition 6.3.2 (arbitrary-field extension): the exact
`n`-pointed specialization of geometric prestability. -/
abbrev IsGeometricallyPrestableNMarkedCurveOfGenusOver
    (k : Type u) [Field k] (g n : ℕ) (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))]
    (p : Fin n → C.SectionOver (Spec (CommRingCat.of k))) : Prop :=
  IsGeometricallyPrestableMarkedCurveOfGenusOver k g C p

/-- An arbitrary-field geometrically prestable marked curve is a curve over its ground
field. -/
lemma IsGeometricallyPrestableMarkedCurveOfGenusOver.isCurveOver
    {k : Type u} [Field k] {I : Type v} {g : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsGeometricallyPrestableMarkedCurveOfGenusOver k g C p) :
    IsCurveOver k C :=
  h.nodal.isCurve

/-- An arbitrary-field geometrically prestable marked curve is Noetherian. -/
lemma IsGeometricallyPrestableMarkedCurveOfGenusOver.isNoetherian
    {k : Type u} [Field k] {I : Type v} {g : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsGeometricallyPrestableMarkedCurveOfGenusOver k g C p) :
    IsNoetherian C :=
  h.nodal.isNoetherian

/-- An H-projective arbitrary-field geometrically prestable marked curve is proper. -/
lemma IsGeometricallyPrestableMarkedCurveOfGenusOver.proper
    {k : Type u} [Field k] {I : Type v} {g : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsGeometricallyPrestableMarkedCurveOfGenusOver k g C p) :
    IsProper (C ↘ Spec (CommRingCat.of k)) :=
  h.projective.isProper

/-- Reindexing an arbitrary-field geometrically prestable marking family by an
equivalence preserves geometric prestability. -/
theorem IsGeometricallyPrestableMarkedCurveOfGenusOver.reindex
    {k : Type u} [Field k] {I : Type v} {J : Type w}
    {g : ℕ} {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsGeometricallyPrestableMarkedCurveOfGenusOver k g C p) (e : J ≃ I) :
    IsGeometricallyPrestableMarkedCurveOfGenusOver k g C (p ∘ e) :=
  ⟨h.nodal, h.projective, h.connected, h.genus_eq,
    fun hg ↦ (h.nonempty_of_genus_eq_one hg).map e.symm,
    h.mark_point_injective.comp e.injective, fun j ↦ h.mark_smooth (e j)⟩

/-- Arbitrary-field geometric prestability is invariant under reindexing by an
equivalence. -/
theorem isGeometricallyPrestableMarkedCurveOfGenusOver_reindex_iff
    {k : Type u} [Field k] {I : Type v} {J : Type w}
    {g : ℕ} {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    (p : I → C.SectionOver (Spec (CommRingCat.of k))) (e : J ≃ I) :
    IsGeometricallyPrestableMarkedCurveOfGenusOver k g C (p ∘ e) ↔
      IsGeometricallyPrestableMarkedCurveOfGenusOver k g C p := by
  constructor
  · intro h
    have hp : (p ∘ e) ∘ e.symm = p := by
      funext i
      simp only [Function.comp_apply, e.apply_symm_apply]
    rw [← hp]
    exact h.reindex e.symm
  · exact fun h ↦ h.reindex e

/-- Arbitrary-field geometrically prestable marked curves are preserved by marked
isomorphisms over their ground field. -/
theorem IsGeometricallyPrestableMarkedCurveOfGenusOver.isoOver
    {k : Type u} [Field k] {I : Type v} {g : ℕ}
    {C D : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [D.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    {q : I → D.SectionOver (Spec (CommRingCat.of k))}
    (h : IsGeometricallyPrestableMarkedCurveOfGenusOver k g C p)
    (e : C.asOver (Spec (CommRingCat.of k)) ≅
      D.asOver (Spec (CommRingCat.of k)))
    (hpq : ∀ i, p i ≫ e.hom = q i) :
    IsGeometricallyPrestableMarkedCurveOfGenusOver k g D q := by
  let E : C ≅ D := (Over.forget (Spec (CommRingCat.of k))).mapIso e
  refine ⟨h.nodal.isoOver e, ?_, ?_, ?_, h.nonempty_of_genus_eq_one, ?_, ?_⟩
  · obtain ⟨m, ι, hι, hcomp⟩ := h.projective
    refine ⟨m, E.inv ≫ ι, ?_, ?_⟩
    · let _ : IsClosedImmersion ι := hι
      infer_instance
    · rw [Category.assoc, hcomp]
      exact e.inv.w
  · exact (E.hom.homeomorph.connectedSpace_iff).mp h.connected
  · exact (genusOver_eq_of_isoOver k e).symm.trans h.genus_eq
  · intro i j hij
    apply h.mark_point_injective
    apply E.hom.homeomorph.injective
    exact ((p i).map_point e (q i) (hpq i)).trans
      (hij.trans ((p j).map_point e (q j) (hpq j)).symm)
  · intro i
    have hpoint : E.hom (p i).point = (q i).point :=
      (p i).map_point e (q i) (hpq i)
    rw [← hpoint]
    exact (formallySmooth_stalkMap_isoOver_iff e (p i).point).mp
      (h.mark_smooth i)

/-- Background definition for Definition 6.3.2 (arbitrary-index extension of the
prestable part): an `I`-marked prestable curve of genus `g` is a connected nodal
H-projective curve of genus `g` with distinct smooth markings, and a genus-one such curve
must have at least one marking.

For `I = Fin n`, the last condition is equivalent to the book's literal exclusion
`(g,n) ≠ (1,0)`; see
`isPrestableNMarkedCurveOfGenusOver_iff_isPrestableMarkedCurveOfGenusOver`. -/
class IsPrestableMarkedCurveOfGenusOver
    (k : Type u) [Field k] [IsAlgClosed k] {I : Type v} (g : ℕ) (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))]
    (p : I → C.SectionOver (Spec (CommRingCat.of k))) : Prop where
  nodal : IsNodalCurveOver k C
  projective : IsHProjective (C ↘ Spec (CommRingCat.of k))
  connected : ConnectedSpace C
  genus_eq : genusOver k C = g
  nonempty_of_genus_eq_one : g = 1 → Nonempty I
  mark_point_injective : Function.Injective (fun i ↦ (p i).point)
  mark_smooth : ∀ i,
    ((C ↘ Spec (CommRingCat.of k)).stalkMap (p i).point).hom.FormallySmooth

/-- API lemma for Definition 6.3.2 (arbitrary-index extension of the
prestable part), unfolded. -/
lemma isPrestableMarkedCurveOfGenusOver_iff
    (k : Type u) [Field k] [IsAlgClosed k] {I : Type v} (g : ℕ) (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))]
    (p : I → C.SectionOver (Spec (CommRingCat.of k))) :
    IsPrestableMarkedCurveOfGenusOver k g C p ↔
      IsNodalCurveOver k C ∧
        IsHProjective (C ↘ Spec (CommRingCat.of k)) ∧
          ConnectedSpace C ∧ genusOver k C = g ∧ (g = 1 → Nonempty I) ∧
            Function.Injective (fun i ↦ (p i).point) ∧
              ∀ i, ((C ↘ Spec (CommRingCat.of k)).stalkMap
                (p i).point).hom.FormallySmooth := by
  constructor
  · intro h
    exact ⟨h.nodal, h.projective, h.connected, h.genus_eq,
      h.nonempty_of_genus_eq_one, h.mark_point_injective, h.mark_smooth⟩
  · rintro ⟨hnodal, hprojective, hconnected, hgenus, hnonempty, hinjective, hsmooth⟩
    exact ⟨hnodal, hprojective, hconnected, hgenus, hnonempty, hinjective, hsmooth⟩

/-- API lemma for Definition 6.3.2 (arbitrary-field comparison): over an
algebraically closed field, geometric prestability agrees with the established split-node
prestable predicate. -/
theorem isGeometricallyPrestableMarkedCurveOfGenusOver_iff_isPrestableMarkedCurveOfGenusOver
    (k : Type u) [Field k] [IsAlgClosed k] {I : Type v} (g : ℕ) (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))]
    (p : I → C.SectionOver (Spec (CommRingCat.of k))) :
    IsGeometricallyPrestableMarkedCurveOfGenusOver k g C p ↔
      IsPrestableMarkedCurveOfGenusOver k g C p := by
  constructor
  · intro h
    exact ⟨h.nodal.isNodalCurveOver, h.projective, h.connected, h.genus_eq,
      h.nonempty_of_genus_eq_one, h.mark_point_injective, h.mark_smooth⟩
  · intro h
    exact ⟨h.nodal.isGeometricallyNodalCurveOver, h.projective, h.connected,
      h.genus_eq, h.nonempty_of_genus_eq_one, h.mark_point_injective, h.mark_smooth⟩

/-- Over an algebraically closed field, a geometrically prestable marked curve is
prestable in the established split-node sense. -/
lemma IsGeometricallyPrestableMarkedCurveOfGenusOver.isPrestableMarkedCurveOfGenusOver
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {g : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsGeometricallyPrestableMarkedCurveOfGenusOver k g C p) :
    IsPrestableMarkedCurveOfGenusOver k g C p :=
  (isGeometricallyPrestableMarkedCurveOfGenusOver_iff_isPrestableMarkedCurveOfGenusOver
    k g C p).mp h

/-- Over an algebraically closed field, a split-node prestable marked curve is
geometrically prestable over the underlying field. -/
lemma IsPrestableMarkedCurveOfGenusOver.isGeometricallyPrestableMarkedCurveOfGenusOver
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {g : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableMarkedCurveOfGenusOver k g C p) :
    IsGeometricallyPrestableMarkedCurveOfGenusOver k g C p :=
  (isGeometricallyPrestableMarkedCurveOfGenusOver_iff_isPrestableMarkedCurveOfGenusOver
    k g C p).mpr h

/-- An arbitrary-index prestable marked curve is a curve over its ground field. -/
lemma IsPrestableMarkedCurveOfGenusOver.isCurveOver
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {g : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableMarkedCurveOfGenusOver k g C p) : IsCurveOver k C :=
  h.nodal.isCurve

/-- API lemma for Definition 6.3.2, reducedness consequence: an
arbitrary-index prestable marked curve is reduced. -/
lemma IsPrestableMarkedCurveOfGenusOver.isReduced
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {g : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableMarkedCurveOfGenusOver k g C p) : IsReduced C :=
  h.nodal.isReduced

/-- An H-projective arbitrary-index prestable curve is proper over its ground field. -/
lemma IsPrestableMarkedCurveOfGenusOver.proper
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {g : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableMarkedCurveOfGenusOver k g C p) :
    IsProper (C ↘ Spec (CommRingCat.of k)) :=
  h.projective.isProper

/-- Reindexing an arbitrary-index marking family by an equivalence preserves
prestability. -/
theorem IsPrestableMarkedCurveOfGenusOver.reindex
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {J : Type w}
    {g : ℕ} {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableMarkedCurveOfGenusOver k g C p) (e : J ≃ I) :
    IsPrestableMarkedCurveOfGenusOver k g C (p ∘ e) :=
  ⟨h.nodal, h.projective, h.connected, h.genus_eq,
    fun hg ↦ (h.nonempty_of_genus_eq_one hg).map e.symm,
    h.mark_point_injective.comp e.injective, fun j ↦ h.mark_smooth (e j)⟩

/-- Arbitrary-index prestability is invariant under reindexing by an equivalence. -/
theorem isPrestableMarkedCurveOfGenusOver_reindex_iff
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {J : Type w}
    {g : ℕ} {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    (p : I → C.SectionOver (Spec (CommRingCat.of k))) (e : J ≃ I) :
    IsPrestableMarkedCurveOfGenusOver k g C (p ∘ e) ↔
      IsPrestableMarkedCurveOfGenusOver k g C p := by
  constructor
  · intro h
    have hp : (p ∘ e) ∘ e.symm = p := by
      funext i
      simp only [Function.comp_apply, e.apply_symm_apply]
    rw [← hp]
    exact h.reindex e.symm
  · exact fun h ↦ h.reindex e

/-- Arbitrary-index prestable curves are preserved by marked isomorphisms over the
ground field. -/
theorem IsPrestableMarkedCurveOfGenusOver.isoOver
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {g : ℕ}
    {C D : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [D.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    {q : I → D.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableMarkedCurveOfGenusOver k g C p)
    (e : C.asOver (Spec (CommRingCat.of k)) ≅
      D.asOver (Spec (CommRingCat.of k)))
    (hpq : ∀ i, p i ≫ e.hom = q i) :
    IsPrestableMarkedCurveOfGenusOver k g D q := by
  let E : C ≅ D := (Over.forget (Spec (CommRingCat.of k))).mapIso e
  refine ⟨h.nodal.isoOver e, ?_, ?_, ?_, h.nonempty_of_genus_eq_one, ?_, ?_⟩
  · obtain ⟨m, ι, hι, hcomp⟩ := h.projective
    refine ⟨m, E.inv ≫ ι, ?_, ?_⟩
    · let _ : IsClosedImmersion ι := hι
      infer_instance
    · rw [Category.assoc, hcomp]
      exact e.inv.w
  · exact (E.hom.homeomorph.connectedSpace_iff).mp h.connected
  · exact (genusOver_eq_of_isoOver k e).symm.trans h.genus_eq
  · intro i j hij
    apply h.mark_point_injective
    apply E.hom.homeomorph.injective
    exact ((p i).map_point e (q i) (hpq i)).trans
      (hij.trans ((p j).map_point e (q j) (hpq j)).symm)
  · intro i
    have hpoint : E.hom (p i).point = (q i).point :=
      (p i).map_point e (q i) (hpq i)
    rw [← hpoint]
    exact (formallySmooth_stalkMap_isoOver_iff e (p i).point).mp (h.mark_smooth i)

/-- Marked-isomorphic curves are simultaneously prestable for an arbitrary marking
index type. -/
theorem isPrestableMarkedCurveOfGenusOver_isoOver_iff
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {g : ℕ}
    {C D : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [D.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    {q : I → D.SectionOver (Spec (CommRingCat.of k))}
    (e : C.asOver (Spec (CommRingCat.of k)) ≅
      D.asOver (Spec (CommRingCat.of k)))
    (hpq : ∀ i, p i ≫ e.hom = q i) :
    IsPrestableMarkedCurveOfGenusOver k g C p ↔
      IsPrestableMarkedCurveOfGenusOver k g D q := by
  constructor
  · exact fun h ↦ h.isoOver e hpq
  · intro h
    apply h.isoOver e.symm
    intro i
    rw [Iso.symm_hom, ← hpq i, Category.assoc, e.hom_inv_id, Category.comp_id]

/-- **Definition 6.3.2** (`def:stable-curves`) (prestable part): an `n`-pointed
prestable curve of genus `g` over an algebraically closed field is a connected nodal
H-projective curve of genus `g`, not of type `(g,n) = (1,0)`, whose ordered markings are
distinct smooth points. -/
class IsPrestableNMarkedCurveOfGenusOver
    (k : Type u) [Field k] [IsAlgClosed k] (g n : ℕ) (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))]
    (p : Fin n → C.SectionOver (Spec (CommRingCat.of k))) : Prop where
  nodal : IsNodalCurveOver k C
  projective : IsHProjective (C ↘ Spec (CommRingCat.of k))
  connected : ConnectedSpace C
  genus_eq : genusOver k C = g
  not_genus_one_unmarked : (g, n) ≠ (1, 0)
  mark_point_injective : Function.Injective (fun i ↦ (p i).point)
  mark_smooth : ∀ i,
    ((C ↘ Spec (CommRingCat.of k)).stalkMap (p i).point).hom.FormallySmooth

/-- API lemma for Definition 6.3.2 (prestable part), unfolded into the
ambient curve conditions and the two numbered conditions in the book. -/
lemma isPrestableNMarkedCurveOfGenusOver_iff
    (k : Type u) [Field k] [IsAlgClosed k] (g n : ℕ) (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))]
    (p : Fin n → C.SectionOver (Spec (CommRingCat.of k))) :
    IsPrestableNMarkedCurveOfGenusOver k g n C p ↔
      IsNodalCurveOver k C ∧
        IsHProjective (C ↘ Spec (CommRingCat.of k)) ∧
          ConnectedSpace C ∧ genusOver k C = g ∧ (g, n) ≠ (1, 0) ∧
            Function.Injective (fun i ↦ (p i).point) ∧
              ∀ i, ((C ↘ Spec (CommRingCat.of k)).stalkMap
                (p i).point).hom.FormallySmooth := by
  constructor
  · intro h
    exact ⟨h.nodal, h.projective, h.connected, h.genus_eq,
      h.not_genus_one_unmarked, h.mark_point_injective, h.mark_smooth⟩
  · rintro ⟨hnodal, hprojective, hconnected, hgenus, htype, hinjective, hsmooth⟩
    exact ⟨hnodal, hprojective, hconnected, hgenus, htype, hinjective, hsmooth⟩

/-- The arbitrary-index prestable predicate specializes to the exact `n`-pointed book
predicate when the marking type is `Fin n`. -/
theorem isPrestableNMarkedCurveOfGenusOver_iff_isPrestableMarkedCurveOfGenusOver
    (k : Type u) [Field k] [IsAlgClosed k] (g n : ℕ) (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))]
    (p : Fin n → C.SectionOver (Spec (CommRingCat.of k))) :
    IsPrestableNMarkedCurveOfGenusOver k g n C p ↔
      IsPrestableMarkedCurveOfGenusOver k g C p := by
  constructor
  · intro h
    refine ⟨h.nodal, h.projective, h.connected, h.genus_eq, ?_,
      h.mark_point_injective, h.mark_smooth⟩
    intro hg
    have hn : n ≠ 0 := by
      intro hn
      exact h.not_genus_one_unmarked (Prod.ext hg hn)
    exact ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  · intro h
    refine ⟨h.nodal, h.projective, h.connected, h.genus_eq, ?_,
      h.mark_point_injective, h.mark_smooth⟩
    intro hpair
    obtain ⟨i⟩ := h.nonempty_of_genus_eq_one (congrArg Prod.fst hpair)
    have hn : n = 0 := congrArg Prod.snd hpair
    subst n
    exact Fin.elim0 i

/-- An `n`-pointed prestable curve is a curve over its ground field. -/
lemma IsPrestableNMarkedCurveOfGenusOver.isCurveOver
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p) : IsCurveOver k C :=
  h.nodal.isCurve

/-- API lemma for Definition 6.3.2, reducedness consequence: an exact
`n`-pointed prestable curve is reduced. -/
lemma IsPrestableNMarkedCurveOfGenusOver.isReduced
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p) : IsReduced C :=
  h.nodal.isReduced

/-- An H-projective prestable curve is proper over its ground field. -/
lemma IsPrestableNMarkedCurveOfGenusOver.proper
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p) :
    IsProper (C ↘ Spec (CommRingCat.of k)) :=
  h.projective.isProper

/-- Permuting the ordered markings preserves prestability. -/
theorem IsPrestableNMarkedCurveOfGenusOver.perm
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p)
    (σ : Equiv.Perm (Fin n)) :
    IsPrestableNMarkedCurveOfGenusOver k g n C (p ∘ σ) :=
  ⟨h.nodal, h.projective, h.connected, h.genus_eq, h.not_genus_one_unmarked,
    h.mark_point_injective.comp σ.injective, fun i ↦ h.mark_smooth (σ i)⟩

/-- Prestability is invariant under permutations of the ordered markings. -/
theorem isPrestableNMarkedCurveOfGenusOver_perm_iff
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    (p : Fin n → C.SectionOver (Spec (CommRingCat.of k)))
    (σ : Equiv.Perm (Fin n)) :
    IsPrestableNMarkedCurveOfGenusOver k g n C (p ∘ σ) ↔
      IsPrestableNMarkedCurveOfGenusOver k g n C p := by
  constructor
  · intro h
    have hp : (p ∘ σ) ∘ σ.symm = p := by
      funext i
      simp only [Function.comp_apply, σ.apply_symm_apply]
    rw [← hp]
    exact h.perm σ.symm
  · exact fun h ↦ h.perm σ

/-- Prestable curves are preserved by marked isomorphisms over the ground field. -/
theorem IsPrestableNMarkedCurveOfGenusOver.isoOver
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C D : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [D.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    {q : Fin n → D.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p)
    (e : C.asOver (Spec (CommRingCat.of k)) ≅
      D.asOver (Spec (CommRingCat.of k)))
    (hpq : ∀ i, p i ≫ e.hom = q i) :
    IsPrestableNMarkedCurveOfGenusOver k g n D q := by
  let E : C ≅ D := (Over.forget (Spec (CommRingCat.of k))).mapIso e
  refine ⟨h.nodal.isoOver e, ?_, ?_, ?_, h.not_genus_one_unmarked, ?_, ?_⟩
  · obtain ⟨m, ι, hι, hcomp⟩ := h.projective
    refine ⟨m, E.inv ≫ ι, ?_, ?_⟩
    · let _ : IsClosedImmersion ι := hι
      infer_instance
    · rw [Category.assoc, hcomp]
      exact e.inv.w
  · exact (E.hom.homeomorph.connectedSpace_iff).mp h.connected
  · exact (genusOver_eq_of_isoOver k e).symm.trans h.genus_eq
  · intro i j hij
    apply h.mark_point_injective
    apply E.hom.homeomorph.injective
    exact ((p i).map_point e (q i) (hpq i)).trans
      (hij.trans ((p j).map_point e (q j) (hpq j)).symm)
  · intro i
    have hpoint : E.hom (p i).point = (q i).point :=
      (p i).map_point e (q i) (hpq i)
    rw [← hpoint]
    exact (formallySmooth_stalkMap_isoOver_iff e (p i).point).mp (h.mark_smooth i)

/-- Marked-isomorphic curves over the ground field are simultaneously prestable of the
same genus and with the same number of markings. -/
theorem isPrestableNMarkedCurveOfGenusOver_isoOver_iff
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C D : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [D.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    {q : Fin n → D.SectionOver (Spec (CommRingCat.of k))}
    (e : C.asOver (Spec (CommRingCat.of k)) ≅
      D.asOver (Spec (CommRingCat.of k)))
    (hpq : ∀ i, p i ≫ e.hom = q i) :
    IsPrestableNMarkedCurveOfGenusOver k g n C p ↔
      IsPrestableNMarkedCurveOfGenusOver k g n D q := by
  constructor
  · exact fun h ↦ h.isoOver e hpq
  · intro h
    apply h.isoOver e.symm
    intro i
    rw [Iso.symm_hom, ← hpq i, Category.assoc, e.hom_inv_id, Category.comp_id]

/-- Background definition for Definition 6.3.2 (implicit rational-subcurve datum):
a smooth irreducible rational subcurve of `C` over `k`, presented as a base-preserving
closed immersion `ℙ¹_k → C`.

The presentation remembers the parametrization only so that its special points can be
counted. The componentwise predicates below quantify over every such presentation. -/
structure RationalSubcurveOver (k : Type u) [Field k] (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))] where
  /-- The inclusion of the copy of `ℙ¹_k`, bundled over `Spec k`. -/
  ι : Over.mk (projectiveSpaceOverπ 1 (Spec (CommRingCat.of k))) ⟶
    C.asOver (Spec (CommRingCat.of k))
  /-- The inclusion is a closed immersion. -/
  isClosedImmersion : IsClosedImmersion ι.left

namespace RationalSubcurveOver

variable {k : Type u} [Field k] {C : Scheme.{u}}
  [C.Over (Spec (CommRingCat.of k))]

/-- The points of a rational subcurve that map to nodes or marked points of the ambient
curve. Extended cardinality is used downstream so the definition remains meaningful
without first proving this set finite. -/
def specialPoints {I : Type v} (E : RationalSubcurveOver k C)
    (p : I → C.SectionOver (Spec (CommRingCat.of k))) :
    Set (projectiveSpaceOver 1 (Spec (CommRingCat.of k))) :=
  {x | C.IsSpecialPoint k p (E.ι.left x)}

/-- Transport a rational subcurve through an isomorphism over the ground field. -/
noncomputable def mapIso {D : Scheme.{u}} [D.Over (Spec (CommRingCat.of k))]
    (E : RationalSubcurveOver k C)
    (e : C.asOver (Spec (CommRingCat.of k)) ≅
      D.asOver (Spec (CommRingCat.of k))) : RationalSubcurveOver k D where
  ι := E.ι ≫ e.hom
  isClosedImmersion := by
    change IsClosedImmersion (E.ι.left ≫ e.hom.left)
    let _ : IsClosedImmersion E.ι.left := E.isClosedImmersion
    infer_instance

/-- Transporting a rational subcurve and its markings through a marked isomorphism
preserves its set of special points. -/
theorem specialPoints_mapIso {D : Scheme.{u}}
    [D.Over (Spec (CommRingCat.of k))] {I : Type v}
    (E : RationalSubcurveOver k C)
    (e : C.asOver (Spec (CommRingCat.of k)) ≅
      D.asOver (Spec (CommRingCat.of k)))
    (p : I → C.SectionOver (Spec (CommRingCat.of k)))
    (q : I → D.SectionOver (Spec (CommRingCat.of k)))
    (hpq : ∀ i, p i ≫ e.hom = q i) :
    (E.mapIso e).specialPoints q = E.specialPoints p := by
  ext x
  change D.IsSpecialPoint k q
      (((Over.forget (Spec (CommRingCat.of k))).mapIso e).hom (E.ι.left x)) ↔
    C.IsSpecialPoint k p (E.ι.left x)
  exact (isSpecialPoint_isoOver_iff e hpq (E.ι.left x)).symm

/-- Reindexing the markings preserves the set of special points on a rational
subcurve. -/
theorem specialPoints_reindex {I : Type v} {J : Type w}
    (E : RationalSubcurveOver k C)
    (p : I → C.SectionOver (Spec (CommRingCat.of k))) (e : J ≃ I) :
    E.specialPoints (p ∘ e) = E.specialPoints p := by
  ext x
  exact isSpecialPoint_reindex_iff p e (E.ι.left x)

/-- API lemma for Definition 6.3.2: a rational subcurve contains at least
two special points exactly when it contains two distinct special points. -/
theorem two_le_specialPoints_encard_iff {I : Type v}
    (E : RationalSubcurveOver k C)
    (p : I → C.SectionOver (Spec (CommRingCat.of k))) :
    (2 : ℕ∞) ≤ (E.specialPoints p).encard ↔
      ∃ x y, x ∈ E.specialPoints p ∧ y ∈ E.specialPoints p ∧ x ≠ y := by
  rw [← Set.one_lt_encard_iff]
  simpa only [one_add_one_eq_two] using
    (ENat.add_one_le_iff ENat.one_ne_top
      (n := (E.specialPoints p).encard))

/-- API lemma for Definition 6.3.2: a rational subcurve contains at least
three special points exactly when it contains three pairwise distinct special points. -/
theorem three_le_specialPoints_encard_iff {I : Type v}
    (E : RationalSubcurveOver k C)
    (p : I → C.SectionOver (Spec (CommRingCat.of k))) :
    (3 : ℕ∞) ≤ (E.specialPoints p).encard ↔
      ∃ x y z, x ∈ E.specialPoints p ∧ y ∈ E.specialPoints p ∧
        z ∈ E.specialPoints p ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  let s := E.specialPoints p
  constructor
  · intro h
    have htwo : (2 : ℕ∞) ≤ s.encard :=
      (by norm_num : (2 : ℕ∞) ≤ 3).trans h
    have hone : (1 : ℕ∞) < s.encard := by
      apply (ENat.add_one_le_iff ENat.one_ne_top).mp
      rw [one_add_one_eq_two]
      exact htwo
    obtain ⟨x, y, hx, hy, hxy⟩ := Set.one_lt_encard_iff.mp hone
    have hthird : ∃ z ∈ s, z ≠ x ∧ z ≠ y := by
      by_contra! hnot
      have hsub : s ⊆ {x, y} := by
        intro z hz
        rcases eq_or_ne z x with rfl | hzx
        · simp
        · have hzy := hnot z hz hzx
          simp [hzy]
      have hle := Set.encard_le_encard hsub
      rw [Set.encard_pair hxy] at hle
      have : (3 : ℕ∞) ≤ 2 := h.trans hle
      norm_num at this
    obtain ⟨z, hz, hzx, hzy⟩ := hthird
    exact ⟨x, y, z, hx, hy, hz, hxy, hzx.symm, hzy.symm⟩
  · rintro ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩
    have hsub : ({x, y, z} : Set _) ⊆ s := by
      simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨hx, hy, hz⟩
    calc
      (3 : ℕ∞) = ({x, y, z} : Set _).encard :=
        (Set.encard_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩).symm
      _ ≤ s.encard := Set.encard_le_encard hsub

end RationalSubcurveOver

/-- Background definition for Definition 6.3.2 (arbitrary-index extension of
semistability): an `I`-marked prestable curve is componentwise semistable when every
smooth rational subcurve contains at least two special points. -/
def IsSemistableMarkedCurveOfGenusOver
    (k : Type u) [Field k] [IsAlgClosed k] {I : Type v} (g : ℕ) (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))]
    (p : I → C.SectionOver (Spec (CommRingCat.of k))) : Prop :=
  IsPrestableMarkedCurveOfGenusOver k g C p ∧
    ∀ E : RationalSubcurveOver k C, (2 : ℕ∞) ≤ (E.specialPoints p).encard

/-- Background definition for Definition 6.3.2 (arbitrary-index extension of the
componentwise stability condition): every smooth rational subcurve of an `I`-marked
prestable curve contains at least three special points. -/
def IsComponentwiseStableMarkedCurveOfGenusOver
    (k : Type u) [Field k] [IsAlgClosed k] {I : Type v} (g : ℕ) (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))]
    (p : I → C.SectionOver (Spec (CommRingCat.of k))) : Prop :=
  IsPrestableMarkedCurveOfGenusOver k g C p ∧
    ∀ E : RationalSubcurveOver k C, (3 : ℕ∞) ≤ (E.specialPoints p).encard

/-- **Definition 6.3.2** (`def:stable-curves`) (semistable part): an `n`-pointed
prestable curve is semistable when every smooth rational subcurve contains at least two
special points. -/
def IsSemistableNMarkedCurveOfGenusOver
    (k : Type u) [Field k] [IsAlgClosed k] (g n : ℕ) (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))]
    (p : Fin n → C.SectionOver (Spec (CommRingCat.of k))) : Prop :=
  IsPrestableNMarkedCurveOfGenusOver k g n C p ∧
    ∀ E : RationalSubcurveOver k C, (2 : ℕ∞) ≤ (E.specialPoints p).encard

/-- **Definition 6.3.2** (`def:stable-curves`) (componentwise stable part): an
`n`-pointed prestable curve is componentwise stable when every smooth rational subcurve
contains at least three special points.

This is distinguished by name from `IsStableNMarkedCurveOfGenusOver`, the
finite-automorphism presentation selected as the primary interface in this file. Their
equivalence is the still-separate content of Proposition 6.3.5. -/
def IsComponentwiseStableNMarkedCurveOfGenusOver
    (k : Type u) [Field k] [IsAlgClosed k] (g n : ℕ) (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))]
    (p : Fin n → C.SectionOver (Spec (CommRingCat.of k))) : Prop :=
  IsPrestableNMarkedCurveOfGenusOver k g n C p ∧
    ∀ E : RationalSubcurveOver k C, (3 : ℕ∞) ≤ (E.specialPoints p).encard

/-- API lemma for Definition 6.3.2 (arbitrary-index semistable extension),
unfolded. -/
lemma isSemistableMarkedCurveOfGenusOver_iff
    (k : Type u) [Field k] [IsAlgClosed k] {I : Type v} (g : ℕ) (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))]
    (p : I → C.SectionOver (Spec (CommRingCat.of k))) :
    IsSemistableMarkedCurveOfGenusOver k g C p ↔
      IsPrestableMarkedCurveOfGenusOver k g C p ∧
        ∀ E : RationalSubcurveOver k C, (2 : ℕ∞) ≤ (E.specialPoints p).encard :=
  Iff.rfl

/-- API lemma for Definition 6.3.2 (arbitrary-index componentwise stable
extension), unfolded. -/
lemma isComponentwiseStableMarkedCurveOfGenusOver_iff
    (k : Type u) [Field k] [IsAlgClosed k] {I : Type v} (g : ℕ) (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))]
    (p : I → C.SectionOver (Spec (CommRingCat.of k))) :
    IsComponentwiseStableMarkedCurveOfGenusOver k g C p ↔
      IsPrestableMarkedCurveOfGenusOver k g C p ∧
        ∀ E : RationalSubcurveOver k C, (3 : ℕ∞) ≤ (E.specialPoints p).encard :=
  Iff.rfl

/-- API lemma for Definition 6.3.2 (semistable part), unfolded. -/
lemma isSemistableNMarkedCurveOfGenusOver_iff
    (k : Type u) [Field k] [IsAlgClosed k] (g n : ℕ) (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))]
    (p : Fin n → C.SectionOver (Spec (CommRingCat.of k))) :
    IsSemistableNMarkedCurveOfGenusOver k g n C p ↔
      IsPrestableNMarkedCurveOfGenusOver k g n C p ∧
        ∀ E : RationalSubcurveOver k C, (2 : ℕ∞) ≤ (E.specialPoints p).encard :=
  Iff.rfl

/-- API lemma for Definition 6.3.2 (componentwise stable part), unfolded. -/
lemma isComponentwiseStableNMarkedCurveOfGenusOver_iff
    (k : Type u) [Field k] [IsAlgClosed k] (g n : ℕ) (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))]
    (p : Fin n → C.SectionOver (Spec (CommRingCat.of k))) :
    IsComponentwiseStableNMarkedCurveOfGenusOver k g n C p ↔
      IsPrestableNMarkedCurveOfGenusOver k g n C p ∧
        ∀ E : RationalSubcurveOver k C, (3 : ℕ∞) ≤ (E.specialPoints p).encard :=
  Iff.rfl

/-- API lemma for Definition 6.3.2 (arbitrary-index semistable extension):
semistability can be stated using two concrete distinct special points on every rational
subcurve. -/
theorem isSemistableMarkedCurveOfGenusOver_iff_exists_two_specialPoints
    (k : Type u) [Field k] [IsAlgClosed k] {I : Type v} (g : ℕ) (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))]
    (p : I → C.SectionOver (Spec (CommRingCat.of k))) :
    IsSemistableMarkedCurveOfGenusOver k g C p ↔
      IsPrestableMarkedCurveOfGenusOver k g C p ∧
        ∀ E : RationalSubcurveOver k C,
          ∃ x y, x ∈ E.specialPoints p ∧ y ∈ E.specialPoints p ∧ x ≠ y := by
  rw [isSemistableMarkedCurveOfGenusOver_iff]
  refine and_congr Iff.rfl ⟨?_, ?_⟩
  · exact fun h E ↦ (E.two_le_specialPoints_encard_iff p).mp (h E)
  · exact fun h E ↦ (E.two_le_specialPoints_encard_iff p).mpr (h E)

/-- API lemma for Definition 6.3.2 (arbitrary-index stable extension):
componentwise stability can be stated using three concrete pairwise-distinct special
points on every rational subcurve. -/
theorem isComponentwiseStableMarkedCurveOfGenusOver_iff_exists_three_specialPoints
    (k : Type u) [Field k] [IsAlgClosed k] {I : Type v} (g : ℕ) (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))]
    (p : I → C.SectionOver (Spec (CommRingCat.of k))) :
    IsComponentwiseStableMarkedCurveOfGenusOver k g C p ↔
      IsPrestableMarkedCurveOfGenusOver k g C p ∧
        ∀ E : RationalSubcurveOver k C,
          ∃ x y z, x ∈ E.specialPoints p ∧ y ∈ E.specialPoints p ∧
            z ∈ E.specialPoints p ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  rw [isComponentwiseStableMarkedCurveOfGenusOver_iff]
  refine and_congr Iff.rfl ⟨?_, ?_⟩
  · exact fun h E ↦ (E.three_le_specialPoints_encard_iff p).mp (h E)
  · exact fun h E ↦ (E.three_le_specialPoints_encard_iff p).mpr (h E)

/-- API lemma for Definition 6.3.2 (semistable part): exact `n`-pointed
semistability can be stated using two concrete distinct special points on every rational
subcurve. -/
theorem isSemistableNMarkedCurveOfGenusOver_iff_exists_two_specialPoints
    (k : Type u) [Field k] [IsAlgClosed k] (g n : ℕ) (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))]
    (p : Fin n → C.SectionOver (Spec (CommRingCat.of k))) :
    IsSemistableNMarkedCurveOfGenusOver k g n C p ↔
      IsPrestableNMarkedCurveOfGenusOver k g n C p ∧
        ∀ E : RationalSubcurveOver k C,
          ∃ x y, x ∈ E.specialPoints p ∧ y ∈ E.specialPoints p ∧ x ≠ y := by
  rw [isSemistableNMarkedCurveOfGenusOver_iff]
  refine and_congr Iff.rfl ⟨?_, ?_⟩
  · exact fun h E ↦ (E.two_le_specialPoints_encard_iff p).mp (h E)
  · exact fun h E ↦ (E.two_le_specialPoints_encard_iff p).mpr (h E)

/-- API lemma for Definition 6.3.2 (componentwise stable part): exact
`n`-pointed componentwise stability can be stated using three concrete pairwise-distinct
special points on every rational subcurve. -/
theorem isComponentwiseStableNMarkedCurveOfGenusOver_iff_exists_three_specialPoints
    (k : Type u) [Field k] [IsAlgClosed k] (g n : ℕ) (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))]
    (p : Fin n → C.SectionOver (Spec (CommRingCat.of k))) :
    IsComponentwiseStableNMarkedCurveOfGenusOver k g n C p ↔
      IsPrestableNMarkedCurveOfGenusOver k g n C p ∧
        ∀ E : RationalSubcurveOver k C,
          ∃ x y z, x ∈ E.specialPoints p ∧ y ∈ E.specialPoints p ∧
            z ∈ E.specialPoints p ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  rw [isComponentwiseStableNMarkedCurveOfGenusOver_iff]
  refine and_congr Iff.rfl ⟨?_, ?_⟩
  · exact fun h E ↦ (E.three_le_specialPoints_encard_iff p).mp (h E)
  · exact fun h E ↦ (E.three_le_specialPoints_encard_iff p).mpr (h E)

/-- For `Fin n` markings, exact semistability agrees with its arbitrary-index
extension. -/
theorem isSemistableNMarkedCurveOfGenusOver_iff_isSemistableMarkedCurveOfGenusOver
    (k : Type u) [Field k] [IsAlgClosed k] (g n : ℕ) (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))]
    (p : Fin n → C.SectionOver (Spec (CommRingCat.of k))) :
    IsSemistableNMarkedCurveOfGenusOver k g n C p ↔
      IsSemistableMarkedCurveOfGenusOver k g C p := by
  unfold IsSemistableNMarkedCurveOfGenusOver IsSemistableMarkedCurveOfGenusOver
  exact and_congr
    (isPrestableNMarkedCurveOfGenusOver_iff_isPrestableMarkedCurveOfGenusOver
      k g n C p) Iff.rfl

/-- For `Fin n` markings, exact componentwise stability agrees with its arbitrary-index
extension. -/
theorem
    isComponentwiseStableNMarkedCurveOfGenusOver_iff_isComponentwiseStableMarkedCurveOfGenusOver
    (k : Type u) [Field k] [IsAlgClosed k] (g n : ℕ) (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))]
    (p : Fin n → C.SectionOver (Spec (CommRingCat.of k))) :
    IsComponentwiseStableNMarkedCurveOfGenusOver k g n C p ↔
      IsComponentwiseStableMarkedCurveOfGenusOver k g C p := by
  unfold IsComponentwiseStableNMarkedCurveOfGenusOver
    IsComponentwiseStableMarkedCurveOfGenusOver
  exact and_congr
    (isPrestableNMarkedCurveOfGenusOver_iff_isPrestableMarkedCurveOfGenusOver
      k g n C p) Iff.rfl

/-- Helper lemma for Definition 6.3.2 (arbitrary-index implication): every
semistable curve is prestable. -/
lemma IsSemistableMarkedCurveOfGenusOver.isPrestable
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {g : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsSemistableMarkedCurveOfGenusOver k g C p) :
    IsPrestableMarkedCurveOfGenusOver k g C p :=
  h.1

/-- Helper lemma for Definition 6.3.2 (arbitrary-index implication): every
componentwise stable curve is prestable. -/
lemma IsComponentwiseStableMarkedCurveOfGenusOver.isPrestable
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {g : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsComponentwiseStableMarkedCurveOfGenusOver k g C p) :
    IsPrestableMarkedCurveOfGenusOver k g C p :=
  h.1

/-- Helper lemma for Definition 6.3.2 (arbitrary-index implication): every
componentwise stable curve is semistable. -/
theorem IsComponentwiseStableMarkedCurveOfGenusOver.isSemistable
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {g : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsComponentwiseStableMarkedCurveOfGenusOver k g C p) :
    IsSemistableMarkedCurveOfGenusOver k g C p := by
  refine ⟨h.1, fun E ↦ ?_⟩
  exact (by norm_num : (2 : ℕ∞) ≤ 3).trans (h.2 E)

/-- Reindexing by an equivalence preserves arbitrary-index semistability. -/
theorem IsSemistableMarkedCurveOfGenusOver.reindex
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {J : Type w}
    {g : ℕ} {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsSemistableMarkedCurveOfGenusOver k g C p) (e : J ≃ I) :
    IsSemistableMarkedCurveOfGenusOver k g C (p ∘ e) := by
  refine ⟨h.1.reindex e, ?_⟩
  intro E
  rw [E.specialPoints_reindex p e]
  exact h.2 E

/-- Reindexing by an equivalence preserves arbitrary-index componentwise stability. -/
theorem IsComponentwiseStableMarkedCurveOfGenusOver.reindex
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {J : Type w}
    {g : ℕ} {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsComponentwiseStableMarkedCurveOfGenusOver k g C p) (e : J ≃ I) :
    IsComponentwiseStableMarkedCurveOfGenusOver k g C (p ∘ e) := by
  refine ⟨h.1.reindex e, ?_⟩
  intro E
  rw [E.specialPoints_reindex p e]
  exact h.2 E

/-- Arbitrary-index semistability is invariant under reindexing by an equivalence. -/
theorem isSemistableMarkedCurveOfGenusOver_reindex_iff
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {J : Type w}
    {g : ℕ} {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    (p : I → C.SectionOver (Spec (CommRingCat.of k))) (e : J ≃ I) :
    IsSemistableMarkedCurveOfGenusOver k g C (p ∘ e) ↔
      IsSemistableMarkedCurveOfGenusOver k g C p := by
  constructor
  · intro h
    have hp : (p ∘ e) ∘ e.symm = p := by
      funext i
      simp only [Function.comp_apply, e.apply_symm_apply]
    rw [← hp]
    exact h.reindex e.symm
  · exact fun h ↦ h.reindex e

/-- Arbitrary-index componentwise stability is invariant under reindexing by an
equivalence. -/
theorem isComponentwiseStableMarkedCurveOfGenusOver_reindex_iff
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {J : Type w}
    {g : ℕ} {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    (p : I → C.SectionOver (Spec (CommRingCat.of k))) (e : J ≃ I) :
    IsComponentwiseStableMarkedCurveOfGenusOver k g C (p ∘ e) ↔
      IsComponentwiseStableMarkedCurveOfGenusOver k g C p := by
  constructor
  · intro h
    have hp : (p ∘ e) ∘ e.symm = p := by
      funext i
      simp only [Function.comp_apply, e.apply_symm_apply]
    rw [← hp]
    exact h.reindex e.symm
  · exact fun h ↦ h.reindex e

/-- Marked isomorphisms preserve arbitrary-index semistability. -/
theorem IsSemistableMarkedCurveOfGenusOver.isoOver
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {g : ℕ}
    {C D : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [D.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    {q : I → D.SectionOver (Spec (CommRingCat.of k))}
    (h : IsSemistableMarkedCurveOfGenusOver k g C p)
    (e : C.asOver (Spec (CommRingCat.of k)) ≅
      D.asOver (Spec (CommRingCat.of k)))
    (hpq : ∀ i, p i ≫ e.hom = q i) :
    IsSemistableMarkedCurveOfGenusOver k g D q := by
  refine ⟨h.1.isoOver e hpq, ?_⟩
  intro E
  have hqp : ∀ i, q i ≫ e.inv = p i := by
    intro i
    rw [← hpq i, Category.assoc, e.hom_inv_id, Category.comp_id]
  have hs := h.2 (E.mapIso e.symm)
  rw [E.specialPoints_mapIso e.symm q p hqp] at hs
  exact hs

/-- Marked isomorphisms preserve arbitrary-index componentwise stability. -/
theorem IsComponentwiseStableMarkedCurveOfGenusOver.isoOver
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {g : ℕ}
    {C D : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [D.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    {q : I → D.SectionOver (Spec (CommRingCat.of k))}
    (h : IsComponentwiseStableMarkedCurveOfGenusOver k g C p)
    (e : C.asOver (Spec (CommRingCat.of k)) ≅
      D.asOver (Spec (CommRingCat.of k)))
    (hpq : ∀ i, p i ≫ e.hom = q i) :
    IsComponentwiseStableMarkedCurveOfGenusOver k g D q := by
  refine ⟨h.1.isoOver e hpq, ?_⟩
  intro E
  have hqp : ∀ i, q i ≫ e.inv = p i := by
    intro i
    rw [← hpq i, Category.assoc, e.hom_inv_id, Category.comp_id]
  have hs := h.2 (E.mapIso e.symm)
  rw [E.specialPoints_mapIso e.symm q p hqp] at hs
  exact hs

/-- Marked-isomorphic curves are simultaneously semistable. -/
theorem isSemistableMarkedCurveOfGenusOver_isoOver_iff
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {g : ℕ}
    {C D : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [D.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    {q : I → D.SectionOver (Spec (CommRingCat.of k))}
    (e : C.asOver (Spec (CommRingCat.of k)) ≅
      D.asOver (Spec (CommRingCat.of k)))
    (hpq : ∀ i, p i ≫ e.hom = q i) :
    IsSemistableMarkedCurveOfGenusOver k g C p ↔
      IsSemistableMarkedCurveOfGenusOver k g D q := by
  constructor
  · exact fun h ↦ h.isoOver e hpq
  · intro h
    apply h.isoOver e.symm
    intro i
    rw [Iso.symm_hom, ← hpq i, Category.assoc, e.hom_inv_id, Category.comp_id]

/-- Marked-isomorphic curves are simultaneously componentwise stable. -/
theorem isComponentwiseStableMarkedCurveOfGenusOver_isoOver_iff
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {g : ℕ}
    {C D : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [D.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    {q : I → D.SectionOver (Spec (CommRingCat.of k))}
    (e : C.asOver (Spec (CommRingCat.of k)) ≅
      D.asOver (Spec (CommRingCat.of k)))
    (hpq : ∀ i, p i ≫ e.hom = q i) :
    IsComponentwiseStableMarkedCurveOfGenusOver k g C p ↔
      IsComponentwiseStableMarkedCurveOfGenusOver k g D q := by
  constructor
  · exact fun h ↦ h.isoOver e hpq
  · intro h
    apply h.isoOver e.symm
    intro i
    rw [Iso.symm_hom, ← hpq i, Category.assoc, e.hom_inv_id, Category.comp_id]

/-- Helper lemma for Definition 6.3.2 (implication display): every exact
`n`-pointed semistable curve is prestable. -/
lemma IsSemistableNMarkedCurveOfGenusOver.isPrestable
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsSemistableNMarkedCurveOfGenusOver k g n C p) :
    IsPrestableNMarkedCurveOfGenusOver k g n C p :=
  h.1

/-- Helper lemma for Definition 6.3.2 (implication display): every exact
`n`-pointed componentwise stable curve is prestable. -/
lemma IsComponentwiseStableNMarkedCurveOfGenusOver.isPrestable
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsComponentwiseStableNMarkedCurveOfGenusOver k g n C p) :
    IsPrestableNMarkedCurveOfGenusOver k g n C p :=
  h.1

/-- Helper lemma for Definition 6.3.2 (implication display): every exact
`n`-pointed componentwise stable curve is semistable. -/
theorem IsComponentwiseStableNMarkedCurveOfGenusOver.isSemistable
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsComponentwiseStableNMarkedCurveOfGenusOver k g n C p) :
    IsSemistableNMarkedCurveOfGenusOver k g n C p := by
  refine ⟨h.1, fun E ↦ ?_⟩
  exact (by norm_num : (2 : ℕ∞) ≤ 3).trans (h.2 E)

/-- Permuting the ordered markings preserves exact semistability. -/
theorem IsSemistableNMarkedCurveOfGenusOver.perm
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsSemistableNMarkedCurveOfGenusOver k g n C p)
    (e : Equiv.Perm (Fin n)) :
    IsSemistableNMarkedCurveOfGenusOver k g n C (p ∘ e) := by
  refine ⟨h.1.perm e, ?_⟩
  intro E
  rw [E.specialPoints_reindex p e]
  exact h.2 E

/-- Permuting the ordered markings preserves exact componentwise stability. -/
theorem IsComponentwiseStableNMarkedCurveOfGenusOver.perm
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsComponentwiseStableNMarkedCurveOfGenusOver k g n C p)
    (e : Equiv.Perm (Fin n)) :
    IsComponentwiseStableNMarkedCurveOfGenusOver k g n C (p ∘ e) := by
  refine ⟨h.1.perm e, ?_⟩
  intro E
  rw [E.specialPoints_reindex p e]
  exact h.2 E

/-- Exact `n`-pointed semistability is invariant under permutations of the ordered
markings. -/
theorem isSemistableNMarkedCurveOfGenusOver_perm_iff
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    (p : Fin n → C.SectionOver (Spec (CommRingCat.of k)))
    (e : Equiv.Perm (Fin n)) :
    IsSemistableNMarkedCurveOfGenusOver k g n C (p ∘ e) ↔
      IsSemistableNMarkedCurveOfGenusOver k g n C p := by
  constructor
  · intro h
    have hp : (p ∘ e) ∘ e.symm = p := by
      funext i
      simp only [Function.comp_apply, e.apply_symm_apply]
    rw [← hp]
    exact h.perm e.symm
  · exact fun h ↦ h.perm e

/-- Exact `n`-pointed componentwise stability is invariant under permutations of the
ordered markings. -/
theorem isComponentwiseStableNMarkedCurveOfGenusOver_perm_iff
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    (p : Fin n → C.SectionOver (Spec (CommRingCat.of k)))
    (e : Equiv.Perm (Fin n)) :
    IsComponentwiseStableNMarkedCurveOfGenusOver k g n C (p ∘ e) ↔
      IsComponentwiseStableNMarkedCurveOfGenusOver k g n C p := by
  constructor
  · intro h
    have hp : (p ∘ e) ∘ e.symm = p := by
      funext i
      simp only [Function.comp_apply, e.apply_symm_apply]
    rw [← hp]
    exact h.perm e.symm
  · exact fun h ↦ h.perm e

/-- Marked isomorphisms preserve exact `n`-pointed semistability. -/
theorem IsSemistableNMarkedCurveOfGenusOver.isoOver
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C D : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [D.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    {q : Fin n → D.SectionOver (Spec (CommRingCat.of k))}
    (h : IsSemistableNMarkedCurveOfGenusOver k g n C p)
    (e : C.asOver (Spec (CommRingCat.of k)) ≅
      D.asOver (Spec (CommRingCat.of k)))
    (hpq : ∀ i, p i ≫ e.hom = q i) :
    IsSemistableNMarkedCurveOfGenusOver k g n D q := by
  apply (isSemistableNMarkedCurveOfGenusOver_iff_isSemistableMarkedCurveOfGenusOver
    k g n D q).mpr
  exact ((isSemistableNMarkedCurveOfGenusOver_iff_isSemistableMarkedCurveOfGenusOver
    k g n C p).mp h).isoOver e hpq

/-- Marked isomorphisms preserve exact `n`-pointed componentwise stability. -/
theorem IsComponentwiseStableNMarkedCurveOfGenusOver.isoOver
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C D : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [D.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    {q : Fin n → D.SectionOver (Spec (CommRingCat.of k))}
    (h : IsComponentwiseStableNMarkedCurveOfGenusOver k g n C p)
    (e : C.asOver (Spec (CommRingCat.of k)) ≅
      D.asOver (Spec (CommRingCat.of k)))
    (hpq : ∀ i, p i ≫ e.hom = q i) :
    IsComponentwiseStableNMarkedCurveOfGenusOver k g n D q := by
  apply
    (isComponentwiseStableNMarkedCurveOfGenusOver_iff_isComponentwiseStableMarkedCurveOfGenusOver
      k g n D q).mpr
  exact
    ((isComponentwiseStableNMarkedCurveOfGenusOver_iff_isComponentwiseStableMarkedCurveOfGenusOver
      k g n C p).mp h).isoOver e hpq

/-- Marked-isomorphic curves are simultaneously exact `n`-pointed semistable curves. -/
theorem isSemistableNMarkedCurveOfGenusOver_isoOver_iff
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C D : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [D.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    {q : Fin n → D.SectionOver (Spec (CommRingCat.of k))}
    (e : C.asOver (Spec (CommRingCat.of k)) ≅
      D.asOver (Spec (CommRingCat.of k)))
    (hpq : ∀ i, p i ≫ e.hom = q i) :
    IsSemistableNMarkedCurveOfGenusOver k g n C p ↔
      IsSemistableNMarkedCurveOfGenusOver k g n D q := by
  constructor
  · exact fun h ↦ h.isoOver e hpq
  · intro h
    apply h.isoOver e.symm
    intro i
    rw [Iso.symm_hom, ← hpq i, Category.assoc, e.hom_inv_id, Category.comp_id]

/-- Marked-isomorphic curves are simultaneously exact `n`-pointed componentwise stable
curves. -/
theorem isComponentwiseStableNMarkedCurveOfGenusOver_isoOver_iff
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C D : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [D.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    {q : Fin n → D.SectionOver (Spec (CommRingCat.of k))}
    (e : C.asOver (Spec (CommRingCat.of k)) ≅
      D.asOver (Spec (CommRingCat.of k)))
    (hpq : ∀ i, p i ≫ e.hom = q i) :
    IsComponentwiseStableNMarkedCurveOfGenusOver k g n C p ↔
      IsComponentwiseStableNMarkedCurveOfGenusOver k g n D q := by
  constructor
  · exact fun h ↦ h.isoOver e hpq
  · intro h
    apply h.isoOver e.symm
    intro i
    rw [Iso.symm_hom, ← hpq i, Category.assoc, e.hom_inv_id, Category.comp_id]

/-- The group of automorphisms of `C` over `S` that fix every section `p i`. -/
abbrev AutOverFixing {I : Type v} (C S : Scheme.{u}) [C.Over S]
    (p : I → C.SectionOver S) : Type u :=
  CategoryTheory.Aut.Fixing p

/-- Background definition for Definition 6.3.2 (marked finite-automorphism
formulation): an `I`-marked stable curve is a connected proper nodal curve, equipped with
sections representing distinct smooth marked points, whose group of base-preserving
automorphisms fixing every section is finite. -/
class IsStableMarkedCurveOver (k : Type u) [Field k] [IsAlgClosed k]
    {I : Type v} (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))]
    (p : I → C.SectionOver (Spec (CommRingCat.of k))) : Prop where
  nodal : IsNodalCurveOver k C
  proper : IsProper (C ↘ Spec (CommRingCat.of k))
  connected : ConnectedSpace C
  mark_point_injective : Function.Injective (fun i ↦ (p i).point)
  mark_smooth : ∀ i,
    ((C ↘ Spec (CommRingCat.of k)).stalkMap (p i).point).hom.FormallySmooth
  finiteAut : Finite (C.AutOverFixing (Spec (CommRingCat.of k)) p)

/-- API lemma for Definition 6.3.2, reducedness consequence: an indexed
marked stable curve is reduced. -/
lemma IsStableMarkedCurveOver.isReduced
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsStableMarkedCurveOver k C p) : IsReduced C :=
  h.nodal.isReduced

/-- API lemma for Definition 6.3.2, curve consequence: an indexed marked
stable curve is a curve over its ground field. -/
lemma IsStableMarkedCurveOver.isCurveOver
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsStableMarkedCurveOver k C p) : IsCurveOver k C :=
  h.nodal.isCurve

/-- API lemma for Definition 6.3.2, finiteness consequence: an indexed
marked stable curve is Noetherian. -/
lemma IsStableMarkedCurveOver.isNoetherian
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsStableMarkedCurveOver k C p) : IsNoetherian C :=
  h.nodal.isNoetherian

/-- API lemma for Definition 6.3.2, geometric-node consequence: an indexed
marked stable curve satisfies the book's arbitrary-field geometric nodality predicate. -/
lemma IsStableMarkedCurveOver.isGeometricallyNodalCurveOver
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsStableMarkedCurveOver k C p) :
    IsGeometricallyNodalCurveOver k C :=
  h.nodal.isGeometricallyNodalCurveOver

/-- API lemma for Definition 6.3.2, global-functions consequence: the
structure map `k ⟶ Γ(C, 𝒯_C)` of an indexed marked stable curve is bijective. -/
lemma IsStableMarkedCurveOver.bijective_baseRingHom
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsStableMarkedCurveOver k C p) :
    Function.Bijective (C.baseRingHom (CommRingCat.of k)) := by
  let _ : IsReduced C := h.isReduced
  let _ : ConnectedSpace C := h.connected
  let _ : IsProper (C ↘ Spec (CommRingCat.of k)) := h.proper
  exact bijective_baseRingHom_of_isAlgClosed_of_isReduced_of_connected k C

/-- API lemma for Definition 6.3.2, genus comparison: for an indexed marked
stable curve, the `k`-linear genus used in the book agrees with the intrinsic genus. -/
lemma IsStableMarkedCurveOver.genusOver_eq_genus
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsStableMarkedCurveOver k C p) : genusOver k C = C.genus :=
  Scheme.genusOver_eq_genus k C h.bijective_baseRingHom

/-- API lemma for Definition 6.3.2, Euler-characteristic comparison: for an
indexed marked stable curve, `1 - χ(C, 𝒯_C)` is its `k`-linear genus. -/
lemma IsStableMarkedCurveOver.arithmeticGenus_eq_genusOver
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsStableMarkedCurveOver k C p) :
    arithmeticGenus k C = (genusOver k C : ℤ) :=
  Scheme.arithmeticGenus_eq_genusOver k C h.bijective_baseRingHom

/-- Background definition for Definition 6.3.2 (`n`-pointed finite-automorphism
formulation): the specialization of `IsStableMarkedCurveOver` whose ordered markings are
indexed by `Fin n`. -/
abbrev IsStableNMarkedCurveOver (k : Type u) [Field k] [IsAlgClosed k]
    (n : ℕ) (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))]
    (p : Fin n → C.SectionOver (Spec (CommRingCat.of k))) : Prop :=
  IsStableMarkedCurveOver k C p

/-- API lemma for Definition 6.3.2 (marked finite-automorphism formulation),
unfolded. -/
lemma isStableMarkedCurveOver_iff (k : Type u) [Field k] [IsAlgClosed k]
    {I : Type v} (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))]
    (p : I → C.SectionOver (Spec (CommRingCat.of k))) :
    IsStableMarkedCurveOver k C p ↔
      IsNodalCurveOver k C ∧ IsProper (C ↘ Spec (CommRingCat.of k)) ∧
        ConnectedSpace C ∧ Function.Injective (fun i ↦ (p i).point) ∧
          (∀ i, ((C ↘ Spec (CommRingCat.of k)).stalkMap (p i).point).hom.FormallySmooth) ∧
            Finite (C.AutOverFixing (Spec (CommRingCat.of k)) p) := by
  constructor
  · intro h
    exact
      ⟨h.nodal, h.proper, h.connected, h.mark_point_injective, h.mark_smooth, h.finiteAut⟩
  · rintro ⟨hnodal, hproper, hconnected, hinjective, hsmooth, hfinite⟩
    exact ⟨hnodal, hproper, hconnected, hinjective, hsmooth, hfinite⟩

/-- In the finite-automorphism presentation selected here, an indexed marked connected
proper nodal curve with distinct smooth markings is stable exactly when its fixing
automorphism group is finite. -/
theorem isStableMarkedCurveOver_iff_finite_aut
    (k : Type u) [Field k] [IsAlgClosed k] {I : Type v}
    (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))]
    [IsNodalCurveOver k C] [IsProper (C ↘ Spec (CommRingCat.of k))]
    [ConnectedSpace C] (p : I → C.SectionOver (Spec (CommRingCat.of k)))
    (hinjective : Function.Injective (fun i ↦ (p i).point))
    (hsmooth : ∀ i,
      ((C ↘ Spec (CommRingCat.of k)).stalkMap (p i).point).hom.FormallySmooth) :
    IsStableMarkedCurveOver k C p ↔
      Finite (C.AutOverFixing (Spec (CommRingCat.of k)) p) := by
  constructor
  · exact fun h ↦ h.finiteAut
  · intro h
    exact ⟨inferInstance, inferInstance, inferInstance, hinjective, hsmooth, h⟩

/-- Helper lemma for Definition 6.3.2 (adding markings): an unpointed stable
curve, equipped with any family of distinct smooth sections, is stable as a marked
curve. The fixing automorphism group is finite because it is a subgroup of the finite
unpointed automorphism group. -/
theorem IsStableCurveOver.marked
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v}
    {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    (h : IsStableCurveOver k C)
    (p : I → C.SectionOver (Spec (CommRingCat.of k)))
    (hinjective : Function.Injective (fun i ↦ (p i).point))
    (hsmooth : ∀ i,
      ((C ↘ Spec (CommRingCat.of k)).stalkMap (p i).point).hom.FormallySmooth) :
    IsStableMarkedCurveOver k C p := by
  refine ⟨h.nodal, h.proper, h.connected, hinjective, hsmooth, ?_⟩
  let _ : Finite (C.AutOver (Spec (CommRingCat.of k))) := h.finiteAut
  exact Finite.of_injective Subtype.val Subtype.val_injective

/-- Helper lemma for Definition 6.3.2 (adding markings): if a marked stable
curve's marking family occurs inside a larger family of distinct smooth sections, then
the larger marked curve is stable. Its fixing group embeds into the original finite
fixing group. -/
theorem IsStableMarkedCurveOver.of_subfamily
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {J : Type w}
    {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    {q : J → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsStableMarkedCurveOver k C p) (f : I → J)
    (hsub : ∀ i, p i = q (f i))
    (hinjective : Function.Injective (fun j ↦ (q j).point))
    (hsmooth : ∀ j,
      ((C ↘ Spec (CommRingCat.of k)).stalkMap (q j).point).hom.FormallySmooth) :
    IsStableMarkedCurveOver k C q :=
  ⟨h.nodal, h.proper, h.connected, hinjective, hsmooth,
    CategoryTheory.Aut.finite_fixing_of_finite_subfamily p q f hsub h.finiteAut⟩

/-- Background definition for Definition 6.3.2 (marked finite-automorphism formulation):
a marked stable curve of genus `g`. -/
def IsStableMarkedCurveOfGenusOver (k : Type u) [Field k] [IsAlgClosed k]
    {I : Type v} (g : ℕ) (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))]
    (p : I → C.SectionOver (Spec (CommRingCat.of k))) : Prop :=
  IsStableMarkedCurveOver k C p ∧ genusOver k C = g

/-- Helper lemma for Definition 6.3.2 (adding markings at fixed genus): a
stable curve of genus `g`, equipped with distinct smooth sections, is a marked stable
curve of the same genus. -/
theorem IsStableCurveOfGenusOver.marked
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {g : ℕ}
    {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    (h : IsStableCurveOfGenusOver k g C)
    (p : I → C.SectionOver (Spec (CommRingCat.of k)))
    (hinjective : Function.Injective (fun i ↦ (p i).point))
    (hsmooth : ∀ i,
      ((C ↘ Spec (CommRingCat.of k)).stalkMap (p i).point).hom.FormallySmooth) :
    IsStableMarkedCurveOfGenusOver k g C p :=
  ⟨h.isStableCurveOver.marked p hinjective hsmooth, h.genus_eq⟩

/-- Helper lemma for Definition 6.3.2 (adding markings at fixed genus):
enlarging the marking family of a stable curve preserves its specified genus. -/
theorem IsStableMarkedCurveOfGenusOver.of_subfamily
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {J : Type w} {g : ℕ}
    {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    {q : J → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsStableMarkedCurveOfGenusOver k g C p) (f : I → J)
    (hsub : ∀ i, p i = q (f i))
    (hinjective : Function.Injective (fun j ↦ (q j).point))
    (hsmooth : ∀ j,
      ((C ↘ Spec (CommRingCat.of k)).stalkMap (q j).point).hom.FormallySmooth) :
    IsStableMarkedCurveOfGenusOver k g C q :=
  ⟨h.1.of_subfamily f hsub hinjective hsmooth, h.2⟩

/-- **Definition 6.3.2** (`def:stable-curves`) (genus-`g`, `n`-pointed
finite-automorphism formulation): an `n`-pointed curve is stable when it is connected,
proper, and nodal of genus `g`, its ordered markings are distinct smooth points, and its
group of base-preserving automorphisms fixing every marking is finite.

This is the substantive finite-automorphism formulation proved equivalent to the book's
componentwise definition in Proposition 6.3.5. -/
abbrev IsStableNMarkedCurveOfGenusOver (k : Type u) [Field k] [IsAlgClosed k]
    (g n : ℕ) (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))]
    (p : Fin n → C.SectionOver (Spec (CommRingCat.of k))) : Prop :=
  IsStableMarkedCurveOfGenusOver k g C p

/-- API lemma for Definition 6.3.2 (marked finite-automorphism formulation),
with the fixed-genus condition unfolded. -/
lemma isStableMarkedCurveOfGenusOver_iff (k : Type u) [Field k] [IsAlgClosed k]
    {I : Type v} (g : ℕ) (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))]
    (p : I → C.SectionOver (Spec (CommRingCat.of k))) :
    IsStableMarkedCurveOfGenusOver k g C p ↔
      IsStableMarkedCurveOver k C p ∧ genusOver k C = g :=
  Iff.rfl

/-- A fixed-genus marked stable curve is stable after forgetting its genus index. -/
lemma IsStableMarkedCurveOfGenusOver.isStableMarkedCurveOver
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {g : ℕ}
    {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsStableMarkedCurveOfGenusOver k g C p) :
    IsStableMarkedCurveOver k C p :=
  h.1

/-- A fixed-genus marked stable curve has the specified genus. -/
lemma IsStableMarkedCurveOfGenusOver.genus_eq
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {g : ℕ}
    {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsStableMarkedCurveOfGenusOver k g C p) : genusOver k C = g :=
  h.2

/-- A fixed-genus marked stable curve is nodal. -/
lemma IsStableMarkedCurveOfGenusOver.nodal
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {g : ℕ}
    {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsStableMarkedCurveOfGenusOver k g C p) : IsNodalCurveOver k C :=
  h.isStableMarkedCurveOver.nodal

/-- API lemma for Definition 6.3.2, reducedness consequence: a fixed-genus
marked stable curve is reduced. -/
lemma IsStableMarkedCurveOfGenusOver.isReduced
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {g : ℕ}
    {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsStableMarkedCurveOfGenusOver k g C p) : IsReduced C :=
  h.nodal.isReduced

/-- A fixed-genus marked stable curve is a curve over its ground field. -/
lemma IsStableMarkedCurveOfGenusOver.isCurveOver
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {g : ℕ}
    {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsStableMarkedCurveOfGenusOver k g C p) : IsCurveOver k C :=
  h.nodal.isCurve

/-- A fixed-genus marked stable curve is Noetherian. -/
lemma IsStableMarkedCurveOfGenusOver.isNoetherian
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {g : ℕ}
    {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsStableMarkedCurveOfGenusOver k g C p) : IsNoetherian C :=
  h.nodal.isNoetherian

/-- A fixed-genus marked stable curve has intrinsic genus `g`. -/
lemma IsStableMarkedCurveOfGenusOver.intrinsic_genus_eq
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {g : ℕ}
    {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsStableMarkedCurveOfGenusOver k g C p) : C.genus = g := by
  rw [← h.isStableMarkedCurveOver.genusOver_eq_genus, h.genus_eq]

/-- A fixed-genus marked stable curve has arithmetic genus `g`. -/
lemma IsStableMarkedCurveOfGenusOver.arithmeticGenus_eq
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {g : ℕ}
    {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsStableMarkedCurveOfGenusOver k g C p) : arithmeticGenus k C = g := by
  rw [h.isStableMarkedCurveOver.arithmeticGenus_eq_genusOver, h.genus_eq]

/-- A fixed-genus marked stable curve is proper over its ground field. -/
lemma IsStableMarkedCurveOfGenusOver.proper
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {g : ℕ}
    {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsStableMarkedCurveOfGenusOver k g C p) :
    IsProper (C ↘ Spec (CommRingCat.of k)) :=
  h.isStableMarkedCurveOver.proper

/-- A fixed-genus marked stable curve is connected. -/
lemma IsStableMarkedCurveOfGenusOver.connected
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {g : ℕ}
    {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsStableMarkedCurveOfGenusOver k g C p) : ConnectedSpace C :=
  h.isStableMarkedCurveOver.connected

/-- The points underlying the markings of a fixed-genus stable curve are distinct. -/
lemma IsStableMarkedCurveOfGenusOver.mark_point_injective
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {g : ℕ}
    {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsStableMarkedCurveOfGenusOver k g C p) :
    Function.Injective (fun i ↦ (p i).point) :=
  h.isStableMarkedCurveOver.mark_point_injective

/-- Every marking of a fixed-genus marked stable curve is a smooth point. -/
lemma IsStableMarkedCurveOfGenusOver.mark_smooth
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {g : ℕ}
    {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsStableMarkedCurveOfGenusOver k g C p) (i : I) :
    ((C ↘ Spec (CommRingCat.of k)).stalkMap (p i).point).hom.FormallySmooth :=
  h.isStableMarkedCurveOver.mark_smooth i

/-- The fixing automorphism group of a fixed-genus marked stable curve is finite. -/
lemma IsStableMarkedCurveOfGenusOver.finiteAut
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {g : ℕ}
    {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsStableMarkedCurveOfGenusOver k g C p) :
    Finite (C.AutOverFixing (Spec (CommRingCat.of k)) p) :=
  h.isStableMarkedCurveOver.finiteAut

/-- With genus fixed, marked stability is again equivalent to finiteness of the fixing
automorphism group once the remaining defining conditions are supplied. -/
theorem isStableMarkedCurveOfGenusOver_iff_finite_aut
    (k : Type u) [Field k] [IsAlgClosed k] {I : Type v} (g : ℕ)
    (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))]
    [IsNodalCurveOver k C] [IsProper (C ↘ Spec (CommRingCat.of k))]
    [ConnectedSpace C] (p : I → C.SectionOver (Spec (CommRingCat.of k)))
    (hinjective : Function.Injective (fun i ↦ (p i).point))
    (hsmooth : ∀ i,
      ((C ↘ Spec (CommRingCat.of k)).stalkMap (p i).point).hom.FormallySmooth)
    (hg : genusOver k C = g) :
    IsStableMarkedCurveOfGenusOver k g C p ↔
      Finite (C.AutOverFixing (Spec (CommRingCat.of k)) p) := by
  rw [IsStableMarkedCurveOfGenusOver, and_iff_left hg]
  exact isStableMarkedCurveOver_iff_finite_aut k C p hinjective hsmooth

/-- For an arbitrary-index prestable marked curve of genus `g`, the selected
finite-automorphism presentation of stability is equivalent to finiteness of the group
fixing its markings.

This only bridges the two predicates defined in this file; it does not prove the
componentwise equivalence of Proposition 6.3.5. -/
theorem IsPrestableMarkedCurveOfGenusOver.isStableMarkedCurveOfGenusOver_iff_finite_aut
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} {g : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    (hpre : IsPrestableMarkedCurveOfGenusOver k g C p) :
    IsStableMarkedCurveOfGenusOver k g C p ↔
      Finite (C.AutOverFixing (Spec (CommRingCat.of k)) p) := by
  let _ : IsNodalCurveOver k C := hpre.nodal
  let _ : IsProper (C ↘ Spec (CommRingCat.of k)) := hpre.proper
  let _ : ConnectedSpace C := hpre.connected
  exact _root_.AlgebraicGeometry.Scheme.isStableMarkedCurveOfGenusOver_iff_finite_aut
    k g C p
    hpre.mark_point_injective hpre.mark_smooth hpre.genus_eq

/-- For an `n`-pointed prestable curve of genus `g`, the selected finite-automorphism
presentation of stability is equivalent to finiteness of the group fixing its markings.

This is a bridge between the literal prestable predicate and the finite-automorphism
definition of stability used in this file. It does not prove the equivalence between that
condition and the book's componentwise stability condition in Proposition 6.3.5. -/
theorem IsPrestableNMarkedCurveOfGenusOver.isStableNMarkedCurveOfGenusOver_iff_finite_aut
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (hpre : IsPrestableNMarkedCurveOfGenusOver k g n C p) :
    IsStableNMarkedCurveOfGenusOver k g n C p ↔
      Finite (C.AutOverFixing (Spec (CommRingCat.of k)) p) := by
  let _ : IsNodalCurveOver k C := hpre.nodal
  let _ : IsProper (C ↘ Spec (CommRingCat.of k)) := hpre.proper
  let _ : ConnectedSpace C := hpre.connected
  exact isStableMarkedCurveOfGenusOver_iff_finite_aut k g C p
    hpre.mark_point_injective hpre.mark_smooth hpre.genus_eq

/-- Reindexing the markings by an equivalence preserves stability. -/
theorem IsStableMarkedCurveOver.reindex {k : Type u} [Field k] [IsAlgClosed k]
    {I : Type v} {J : Type w} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsStableMarkedCurveOver k C p) (e : J ≃ I) :
    IsStableMarkedCurveOver k C (p ∘ e) := by
  refine ⟨h.nodal, h.proper, h.connected, ?_, ?_, ?_⟩
  · exact h.mark_point_injective.comp e.injective
  · exact fun j ↦ h.mark_smooth (e j)
  · exact (CategoryTheory.Aut.fixingMulEquivOfEquiv p e).toEquiv.finite_iff.mpr h.finiteAut

/-- Stability of marked curves is invariant under reindexing by an equivalence. -/
theorem isStableMarkedCurveOver_reindex_iff {k : Type u} [Field k] [IsAlgClosed k]
    {I : Type v} {J : Type w} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    (p : I → C.SectionOver (Spec (CommRingCat.of k))) (e : J ≃ I) :
    IsStableMarkedCurveOver k C (p ∘ e) ↔ IsStableMarkedCurveOver k C p := by
  constructor
  · intro h
    have hp : (p ∘ e) ∘ e.symm = p := by
      funext i
      simp only [Function.comp_apply, e.apply_symm_apply]
    rw [← hp]
    exact h.reindex e.symm
  · exact fun h ↦ h.reindex e

/-- Reindexing the markings by an equivalence preserves fixed-genus stability. -/
theorem IsStableMarkedCurveOfGenusOver.reindex
    {k : Type u} [Field k] [IsAlgClosed k]
    {I : Type v} {J : Type w} {g : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsStableMarkedCurveOfGenusOver k g C p) (e : J ≃ I) :
    IsStableMarkedCurveOfGenusOver k g C (p ∘ e) :=
  ⟨h.1.reindex e, h.2⟩

/-- Fixed-genus stability of marked curves is invariant under reindexing by an
equivalence. -/
theorem isStableMarkedCurveOfGenusOver_reindex_iff
    {k : Type u} [Field k] [IsAlgClosed k]
    {I : Type v} {J : Type w} {g : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    (p : I → C.SectionOver (Spec (CommRingCat.of k))) (e : J ≃ I) :
    IsStableMarkedCurveOfGenusOver k g C (p ∘ e) ↔
      IsStableMarkedCurveOfGenusOver k g C p :=
  and_congr (isStableMarkedCurveOver_reindex_iff p e) Iff.rfl

/-- Permuting the ordered markings of an `n`-marked curve preserves stability. -/
theorem isStableNMarkedCurveOver_perm_iff
    {k : Type u} [Field k] [IsAlgClosed k]
    {n : ℕ} {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    (p : Fin n → C.SectionOver (Spec (CommRingCat.of k))) (σ : Equiv.Perm (Fin n)) :
    IsStableNMarkedCurveOver k n C (p ∘ σ) ↔ IsStableNMarkedCurveOver k n C p :=
  isStableMarkedCurveOver_reindex_iff p σ

/-- Permuting the ordered markings of a fixed-genus `n`-marked curve preserves
stability. -/
theorem isStableNMarkedCurveOfGenusOver_perm_iff
    {k : Type u} [Field k] [IsAlgClosed k]
    {g n : ℕ} {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    (p : Fin n → C.SectionOver (Spec (CommRingCat.of k))) (σ : Equiv.Perm (Fin n)) :
    IsStableNMarkedCurveOfGenusOver k g n C (p ∘ σ) ↔
      IsStableNMarkedCurveOfGenusOver k g n C p :=
  isStableMarkedCurveOfGenusOver_reindex_iff p σ

/-- Stability of marked curves is preserved by a marked isomorphism over the ground
field. -/
theorem IsStableMarkedCurveOver.isoOver {k : Type u} [Field k] [IsAlgClosed k]
    {I : Type v} {C D : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    [D.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    {q : I → D.SectionOver (Spec (CommRingCat.of k))}
    (h : IsStableMarkedCurveOver k C p)
    (e : C.asOver (Spec (CommRingCat.of k)) ≅
      D.asOver (Spec (CommRingCat.of k)))
    (hpq : ∀ i, p i ≫ e.hom = q i) :
    IsStableMarkedCurveOver k D q := by
  let E : C ≅ D := (Over.forget (Spec (CommRingCat.of k))).mapIso e
  refine ⟨h.nodal.isoOver e, ?_, ?_, ?_, ?_, ?_⟩
  · let _ : IsProper (C ↘ Spec (CommRingCat.of k)) := h.proper
    have he : E.inv ≫ (C ↘ Spec (CommRingCat.of k)) =
        D ↘ Spec (CommRingCat.of k) := e.inv.w
    rw [← he]
    infer_instance
  · exact (E.hom.homeomorph.connectedSpace_iff).mp h.connected
  · intro i j hij
    apply h.mark_point_injective
    apply E.hom.homeomorph.injective
    exact ((p i).map_point e (q i) (hpq i)).trans
      (hij.trans ((p j).map_point e (q j) (hpq j)).symm)
  · intro i
    have hpoint : E.hom (p i).point = (q i).point :=
      (p i).map_point e (q i) (hpq i)
    rw [← hpoint]
    exact (formallySmooth_stalkMap_isoOver_iff e (p i).point).mp (h.mark_smooth i)
  · exact (CategoryTheory.Aut.fixingMulEquivOfIso e p q hpq).toEquiv.finite_iff.mp
      h.finiteAut

/-- Isomorphic marked curves over the ground field are simultaneously stable. -/
theorem isStableMarkedCurveOver_isoOver_iff {k : Type u} [Field k] [IsAlgClosed k]
    {I : Type v} {C D : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    [D.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    {q : I → D.SectionOver (Spec (CommRingCat.of k))}
    (e : C.asOver (Spec (CommRingCat.of k)) ≅
      D.asOver (Spec (CommRingCat.of k)))
    (hpq : ∀ i, p i ≫ e.hom = q i) :
    IsStableMarkedCurveOver k C p ↔ IsStableMarkedCurveOver k D q := by
  constructor
  · exact fun h ↦ h.isoOver e hpq
  · intro h
    apply h.isoOver e.symm
    intro i
    rw [Iso.symm_hom, ← hpq i, Category.assoc, e.hom_inv_id, Category.comp_id]

/-- Fixed-genus stability of marked curves is preserved by a marked isomorphism. -/
theorem IsStableMarkedCurveOfGenusOver.isoOver
    {k : Type u} [Field k] [IsAlgClosed k]
    {I : Type v} {g : ℕ} {C D : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [D.Over (Spec (CommRingCat.of k))]
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    {q : I → D.SectionOver (Spec (CommRingCat.of k))}
    (h : IsStableMarkedCurveOfGenusOver k g C p)
    (e : C.asOver (Spec (CommRingCat.of k)) ≅
      D.asOver (Spec (CommRingCat.of k)))
    (hpq : ∀ i, p i ≫ e.hom = q i) :
    IsStableMarkedCurveOfGenusOver k g D q :=
  ⟨h.1.isoOver e hpq, (genusOver_eq_of_isoOver k e).symm.trans h.2⟩

/-- With no markings, marked stability is equivalent to the unpointed definition. -/
theorem isStableMarkedCurveOver_iff_of_isEmpty
    {k : Type u} [Field k] [IsAlgClosed k]
    {I : Type v} [IsEmpty I] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    (p : I → C.SectionOver (Spec (CommRingCat.of k))) :
    IsStableMarkedCurveOver k C p ↔ IsStableCurveOver k C := by
  have hfix : CategoryTheory.Aut.fixingSubgroup p = ⊤ :=
    CategoryTheory.Aut.fixingSubgroup_eq_top_of_isEmpty p
  let E : C.AutOverFixing (Spec (CommRingCat.of k)) p ≃*
      C.AutOver (Spec (CommRingCat.of k)) :=
    (MulEquiv.subgroupCongr hfix).trans Subgroup.topEquiv
  constructor
  · intro h
    exact ⟨h.nodal, h.proper, h.connected, E.toEquiv.finite_iff.mp h.finiteAut⟩
  · intro h
    refine ⟨h.nodal, h.proper, h.connected, ?_, ?_, E.toEquiv.finite_iff.mpr h.finiteAut⟩
    · intro i
      exact isEmptyElim i
    · intro i
      exact isEmptyElim i

/-- A zero-pointed stable curve is exactly an unpointed stable curve. -/
theorem isStableNMarkedCurveOver_zero_iff
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    (p : Fin 0 → C.SectionOver (Spec (CommRingCat.of k))) :
    IsStableNMarkedCurveOver k 0 C p ↔ IsStableCurveOver k C :=
  isStableMarkedCurveOver_iff_of_isEmpty p

/-- A zero-pointed stable curve of fixed genus is exactly an unpointed stable curve of
that genus. -/
theorem isStableNMarkedCurveOfGenusOver_zero_iff
    {k : Type u} [Field k] [IsAlgClosed k] {g : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    (p : Fin 0 → C.SectionOver (Spec (CommRingCat.of k))) :
    IsStableNMarkedCurveOfGenusOver k g 0 C p ↔ IsStableCurveOfGenusOver k g C :=
  and_congr (isStableMarkedCurveOver_iff_of_isEmpty p) Iff.rfl

end DefStableCurves

section RemSemistablePrestableCurves

/-- API lemma for Remark 6.3.3, numerical form: a stable
vertex-weighted `n`-marked graph of genus `g` satisfies `2g - 2 + n > 0`.

This is the combinatorial calculation underlying the corresponding assertion for stable
curves. The geometric transfer is the stability-and-genus comparison with the dual graph
in Exercise 6.3.10. -/
theorem stableMarkedGraph_two_mul_genus_add_markings_sub_two_pos
    {n : ℕ} {VertexType : Type v} {EdgeType : Type w}
    (G : VertexWeightedMarkedGraph n VertexType EdgeType)
    (hG : G.IsStable) :
    (0 : ℤ) < 2 * (G.genus : ℤ) + (n : ℤ) - 2 :=
  hG.two_mul_genus_add_markings_sub_two_pos

/-- **Remark 6.3.3** (`rem:semistable-prestable-curves`) (numerical equivalence): the
inequality `2g - 2 + n ≤ 0`, written in naturals as `2g + n ≤ 2`, holds exactly for the
four exceptional pairs `(0, 0)`, `(0, 1)`, `(0, 2)`, and `(1, 0)`. -/
theorem two_mul_genus_add_markings_le_two_iff_exceptional (g n : ℕ) :
    2 * g + n ≤ 2 ↔
      (g = 0 ∧ n = 0) ∨ (g = 0 ∧ n = 1) ∨
        (g = 0 ∧ n = 2) ∨ (g = 1 ∧ n = 0) := by
  omega

/-- API lemma used toward Remark 6.3.3 (graph-level reduction): no stable
vertex-weighted `n`-marked graph has one of the four exceptional genus-marking pairs.

The remark is stated for stable curves; transferring this graph-level conclusion to
curves still requires the stability and genus comparison with the dual graph. -/
theorem not_stableMarkedGraph_of_exceptional_pair
    {n : ℕ} {VertexType : Type v} {EdgeType : Type w}
    (G : VertexWeightedMarkedGraph n VertexType EdgeType)
    (h : (G.genus = 0 ∧ n = 0) ∨ (G.genus = 0 ∧ n = 1) ∨
      (G.genus = 0 ∧ n = 2) ∨ (G.genus = 1 ∧ n = 0)) :
    ¬ G.IsStable := by
  apply G.not_isStable_of_two_mul_genus_add_markings_le_two
  exact (two_mul_genus_add_markings_le_two_iff_exceptional G.genus n).mpr h

-- STATUS: remark-complete

end RemSemistablePrestableCurves

end AlgebraicGeometry.Scheme
