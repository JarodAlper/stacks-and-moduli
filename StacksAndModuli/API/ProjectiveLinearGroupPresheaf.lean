module

public import StacksAndModuli.API.BrauerSeveri
public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.6-isom-presheaves»

/-!
# The projective linear group as an automorphism presheaf

The projective linear group over a scheme `S` is first of all the group-valued
presheaf of automorphisms of relative projective space.  This file constructs
that presheaf directly from the automorphism-presheaf API for prestacks.

Representability of this presheaf by the usual smooth affine group scheme is a
separate geometric theorem.  The predicate `IsProjectiveLinearGroupScheme`
isolates exactly that remaining input, so arguments involving actions on
Hilbert schemes need not choose a coordinate construction prematurely.

Main declarations:

* `AlgebraicGeometry.Scheme.projectiveSpaceFamilyFiber`: relative projective
  space regarded as an object of the cartesian-family prestack over its base;
* `AlgebraicGeometry.Scheme.projectiveLinearGroupPresheaf`: the group-valued
  presheaf `Aut_S(ℙⁿ_S)`;
* `AlgebraicGeometry.Scheme.IsProjectiveLinearGroupScheme`: representability
  of this presheaf by a scheme over `S`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Functor

universe u

namespace AlgebraicGeometry.Scheme

/-- Relative projective `n`-space over `S`, regarded as an object over `S` in
the prestack of cartesian families of schemes. -/
noncomputable def projectiveSpaceFamilyFiber (n : ℕ) (S : Scheme.{u}) :
    (CategoryTheory.arrowCartesian Scheme.{u}).p.Fiber S :=
  CategoryTheory.Functor.Fiber.mk
    (p := (CategoryTheory.arrowCartesian Scheme.{u}).p)
    (a := CategoryTheory.ArrowCartesian.mk (projectiveSpaceOverπ n S)) rfl

/-- The projective linear group functor over `S`: on an `S`-scheme `T`, it is
the automorphism group of the base change of `ℙⁿ_S` to `T`.

The chosen pullback object comes from the cleavage of the cartesian-family
prestack; it is canonically isomorphic to `ℙⁿ_T` by
`projectiveSpaceOverPullbackIso`. -/
noncomputable def projectiveLinearGroupPresheaf (n : ℕ) (S : Scheme.{u}) :
    (Over S)ᵒᵖ ⥤ GrpCat.{u} :=
  CategoryTheory.BasedCategory.autPresheaf
    (projectiveSpaceFamilyFiber n S)

/-- A scheme `G → S` is a projective linear group scheme of relative
projective dimension `n` if it represents the automorphism presheaf
`Aut_S(ℙⁿ_S)`.  In the usual notation such a representative is
`PGL_{n+1,S}`.

This definition records only the representing property.  When a concrete
representative is available, its internal group structure is induced from the
group-valued presheaf by `CategoryTheory.GrpObj.ofRepresentableBy`. -/
def IsProjectiveLinearGroupScheme (n : ℕ) (S : Scheme.{u}) (G : Over S) : Prop :=
  Nonempty
    ((projectiveLinearGroupPresheaf n S ⋙
      CategoryTheory.forget GrpCat.{u}).RepresentableBy G)

lemma isProjectiveLinearGroupScheme_iff (n : ℕ) (S : Scheme.{u}) (G : Over S) :
    IsProjectiveLinearGroupScheme n S G ↔
      Nonempty
        ((projectiveLinearGroupPresheaf n S ⋙
          CategoryTheory.forget GrpCat.{u}).RepresentableBy G) :=
  Iff.rfl

/-- A representative of the projective-linear-group presheaf carries the
canonical internal group structure induced by the represented pointwise group
operations. -/
@[instance_reducible]
noncomputable def IsProjectiveLinearGroupScheme.grpObj {n : ℕ} {S : Scheme.{u}}
    {G : Over S} (hG : IsProjectiveLinearGroupScheme n S G) :
    CategoryTheory.GrpObj G :=
  CategoryTheory.GrpObj.ofRepresentableBy G
    (projectiveLinearGroupPresheaf n S) hG.some

end AlgebraicGeometry.Scheme
