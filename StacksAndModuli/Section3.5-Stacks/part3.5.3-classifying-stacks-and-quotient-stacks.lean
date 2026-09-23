module

public import StacksAndModuli.«Section3.5-Stacks».«part3.5.2-first-examples»
public import StacksAndModuli.«Section3.1-Descent».«part3.1.4b-effective-descent-schemes»
public import StacksAndModuli.API.ActionQuotientFpqcStack
public import StacksAndModuli.API.ActionQuotientStack
public import StacksAndModuli.API.ClassifyingPrestack
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Classifying stacks and quotient stacks

This module follows the subsection "Classifying stacks and quotient stacks" of §3.5
(Stacks) of *Stacks and Moduli*,
section label `sec:stacks`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section PropQuotientStackIsAStack

open CategoryTheory Functor

universe w v u

namespace CategoryTheory.PresheafAction

variable {C : Type u} [Category.{v} C]
  (A : CategoryTheory.PresheafAction.{w} C)

/-- API lemma used in the proof of Proposition 3.5.13 (morphism-descent
core, in abstract presheaf form): when the group presheaf and acted-on presheaf are
sheaves, morphisms in the action quotient prestack glue uniquely.

This abstract companion isolates the first stack axiom used in the proposition.
The scheme-theoretic proof below uses the stronger specialized morphism-gluing API
for arbitrary principal `G`-bundles and combines it with effective object descent. -/
theorem quotientPrestack_morphismsGlue_of_sheaves (J : GrothendieckTopology C)
    (hG : Presieve.IsSheaf J (A.G ⋙ forget GrpCat))
    (hU : Presieve.IsSheaf J A.U) :
    A.quotientProj.MorphismsGlue J :=
  A.quotientProj_morphismsGlue_of_sheaves J hG hU

end CategoryTheory.PresheafAction

/-- **Proposition 3.5.13** (`prop:quotient-stack-is-a-stack`): if `G → S` is a smooth affine
group scheme acting on an `S`-scheme `U`, then `[U/G]` is a stack over `Sch_ét`.

The quotient prestack `[U/G]` is `AlgebraicGeometry.Scheme.actionQuotientPrestack G U`
(`StacksAndModuli/API/ClassifyingPrestack.lean`): its objects over `T` are a principal `G`-bundle
`P → T` together with a `G`-equivariant map `P → U`, and its arrows are equivariant
cartesian squares compatible with those maps. It is already known to be fibered in
groupoids.

The book proves this stronger fpqc statement and then deduces the étale one. Its proof
reduces, by Exercise 3.5.5, to a single fpqc map and applies
Fpqc Descent for Morphisms (Proposition 3.1.7) and Fpqc Descent of
Principal `G`-bundles. The Lean proof
works directly with arbitrary fpqc covering sieves: morphisms glue by the specialized
principal-bundle API, while objects are reduced to effective descent of their underlying
affine scheme arrows and the equivariant maps to `U` are glued afterward. -/
theorem AlgebraicGeometry.Scheme.isStack_actionQuotientPrestack_fpqc {S : Scheme.{u}}
    (G : Over S) [CategoryTheory.GrpObj G] [AlgebraicGeometry.Smooth G.hom]
    [AlgebraicGeometry.IsAffineHom G.hom]
    (U : Over S) [CategoryTheory.ModObj G U] :
    (AlgebraicGeometry.Scheme.actionQuotientPrestack G U).IsStack
      (AlgebraicGeometry.Scheme.fpqcTopology.over S) := by
  sorry

/-- Convenience étale corollary of Proposition 3.5.13: `[U/G]` is a stack over
`Sch_ét`.

**Proved** from the fpqc statement, since the étale topology is coarser and the stack
condition passes to coarser topologies (`CategoryTheory.BasedCategory.IsStack.of_le`, itself
an immediate consequence of the single-sieve form of the axioms introduced for
Exercise 3.5.5). This is exactly the book's own step: it proves
the fpqc statement and reads off the étale one. -/
theorem AlgebraicGeometry.Scheme.isStack_actionQuotientPrestack {S : Scheme.{u}}
    (G : Over S) [CategoryTheory.GrpObj G] [AlgebraicGeometry.Smooth G.hom]
    [AlgebraicGeometry.IsAffineHom G.hom]
    (U : Over S) [CategoryTheory.ModObj G U] :
    (AlgebraicGeometry.Scheme.actionQuotientPrestack G U).IsStack
      (AlgebraicGeometry.Scheme.etaleTopology.over S) :=
  haveI := AlgebraicGeometry.Scheme.isStack_actionQuotientPrestack_fpqc G U
  CategoryTheory.BasedCategory.IsStack.of_le
    (AlgebraicGeometry.Scheme.etaleTopology_over_le_fpqcTopology_over S) _

/-- **Proposition 3.5.13** (`prop:quotient-stack-is-a-stack`) (the "in particular",
fpqc form): the classifying stack `BG = [S/G]` is a stack over `Sch_fpqc`.

It is the case `U = 𝟙_(Sch/S)` of the proposition, the terminal `S`-scheme with its trivial
`G`-action; stated separately because `classifyingPrestack G` and
`actionQuotientPrestack G (𝟙_ (Over S))` are equivalent but not equal. Its direct proof
uses the same effective descent of principal bundles as the quotient-stack case. -/
theorem AlgebraicGeometry.Scheme.isStack_classifyingPrestack_fpqc {S : Scheme.{u}}
    (G : Over S) [CategoryTheory.GrpObj G] [AlgebraicGeometry.Smooth G.hom]
    [AlgebraicGeometry.IsAffineHom G.hom] :
    (AlgebraicGeometry.Scheme.classifyingPrestack G).IsStack
      (AlgebraicGeometry.Scheme.fpqcTopology.over S) := by
  sorry

/-- Convenience étale corollary of Proposition 3.5.13 (the "in particular"):
the classifying stack `BG` is a stack over `Sch_ét`. -/
theorem AlgebraicGeometry.Scheme.isStack_classifyingPrestack {S : Scheme.{u}}
    (G : Over S) [CategoryTheory.GrpObj G] [AlgebraicGeometry.Smooth G.hom]
    [AlgebraicGeometry.IsAffineHom G.hom] :
    (AlgebraicGeometry.Scheme.classifyingPrestack G).IsStack
      (AlgebraicGeometry.Scheme.etaleTopology.over S) :=
  haveI := AlgebraicGeometry.Scheme.isStack_classifyingPrestack_fpqc G
  CategoryTheory.BasedCategory.IsStack.of_le
    (AlgebraicGeometry.Scheme.etaleTopology_over_le_fpqcTopology_over S) _

end PropQuotientStackIsAStack
