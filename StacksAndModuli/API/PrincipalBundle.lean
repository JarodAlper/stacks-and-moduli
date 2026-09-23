module

public import StacksAndModuli.API.MonoidalMapMod
public import StacksAndModuli.Util.FpqcCover
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Principal bundles of schemes

Let `X` be a scheme and let `G` be a group object of `Scheme/X`.  A principal
`G`-bundle is an fppf morphism `P ⟶ X` with a `G`-action such that the action
graph `(g,p) ↦ (g⋅p,p)` is an isomorphism.  Expressing the definition inside
the cartesian monoidal category `Over X` makes the action graph exactly
`ModObj.leftSMul G P`.

The group object in this file is already over the bundle base.  Thus, for a group
scheme over `S` and an `S`-scheme `X`, use its image under `Over.pullback X.hom`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open scoped CategoryTheory.Obj CategoryTheory.ModObj

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} (G : Over X) [GrpObj G]

/-- A principal bundle for a group object `G` of `Scheme/X`: an fppf object
`P ⟶ X` with a simply transitive internal `G`-action. -/
structure PrincipalBundle where
  /-- The total space, regarded as a scheme over `X`. -/
  P : Over X
  /-- The action of `G` on the total space. -/
  [action : ModObj G P]
  /-- The projection `P ⟶ X` is flat. -/
  [flat : Flat P.hom]
  /-- The projection `P ⟶ X` is surjective. -/
  [surjective : Surjective P.hom]
  /-- The projection `P ⟶ X` is locally of finite presentation. -/
  [locallyOfFinitePresentation : LocallyOfFinitePresentation P.hom]
  /-- The action graph `G ×_X P ⟶ P ×_X P`, `(g,p) ↦ (g⋅p,p)`,
  is an isomorphism. -/
  [torsor : IsIso (ModObj.leftSMul G P)]

attribute [instance] PrincipalBundle.action PrincipalBundle.flat
  PrincipalBundle.surjective PrincipalBundle.locallyOfFinitePresentation
  PrincipalBundle.torsor

namespace PrincipalBundle

variable {G}

/-- The projection of a principal bundle is an fpqc cover. -/
lemma isFpqcCover (B : PrincipalBundle G) : IsFpqcCover B.P.hom :=
  IsFpqcCover.of_fppf B.P.hom

/-- Pull back a principal bundle along a morphism of base schemes.  Both the group
object and the bundle are mapped by the cartesian monoidal pullback functor. -/
noncomputable def pullback {X' : Scheme.{u}} (f : X' ⟶ X)
    (B : PrincipalBundle G) :
    PrincipalBundle ((Over.pullback f).obj G) where
  P := (Over.pullback f).obj B.P
  action := (Over.pullback f).mapModObj G B.P
  flat := by
    dsimp [Over.pullback]
    infer_instance
  surjective := by
    dsimp [Over.pullback]
    infer_instance
  locallyOfFinitePresentation := by
    dsimp [Over.pullback]
    infer_instance
  torsor := (Over.pullback f).isIso_map_leftSMul G B.P

end PrincipalBundle

end AlgebraicGeometry.Scheme
