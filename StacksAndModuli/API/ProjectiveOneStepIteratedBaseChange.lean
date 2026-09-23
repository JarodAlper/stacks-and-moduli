module

public import StacksAndModuli.API.ProjectiveFlatteningLocusBaseChange
public import StacksAndModuli.API.ProjectiveFlatteningOneStepBaseChange

/-!
# Iterating one-step projective pushforward base change

A base-change comparison for all test schemes over `T` also supplies the two comparison
isomorphisms needed after first restricting the projective family to one fixed test scheme.
Only functoriality of pullback and the canonical iterated-family isomorphism are involved;
no extra multiplication-coherence assertion is needed.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- An isomorphism of projective-space sheaves induces an isomorphism of their twisted
pushforwards in every natural degree. -/
noncomputable def projectiveTwistedPushforwardIso
    {T : Scheme.{u}} {n : ℕ}
    {Q Q' : (Scheme.projectiveSpaceOver n T).Modules}
    (e : Q ≅ Q') (d : ℕ) :
    projectiveTwistedPushforward n Q d ≅
      projectiveTwistedPushforward n Q' d :=
  (pushforward (Scheme.projectiveSpaceOverπ n T)).mapIso
    (tensorLeftIso e (Scheme.projectiveSpaceOverTwist n T (d : ℤ)))

/-- Two compatible stages of pushforward base change give the comparison after first
restricting the family to `A` and then to `B`.  Compatibility here is only by sharing the
same original family; the supplied isomorphisms themselves need no additional coherence. -/
noncomputable def projectiveTwistedPushforwardIteratedBaseChangeIso
    {T : Scheme.{u}} {n d : ℕ}
    (Q : (Scheme.projectiveSpaceOver n T).Modules)
    (A : Over T) (B : Over A.left)
    (eA : (pullback A.hom).obj (projectiveTwistedPushforward n Q d) ≅
      projectiveTwistedPushforward n (projectiveFamilyAt n Q A) d)
    (eAB : (pullback ((Over.map A.hom).obj B).hom).obj
        (projectiveTwistedPushforward n Q d) ≅
      projectiveTwistedPushforward n
        (projectiveFamilyAt n Q ((Over.map A.hom).obj B)) d) :
    (pullback B.hom).obj
        (projectiveTwistedPushforward n (projectiveFamilyAt n Q A) d) ≅
      projectiveTwistedPushforward n
        (projectiveFamilyAt n (projectiveFamilyAt n Q A) B) d :=
  (pullback B.hom).mapIso eA.symm ≪≫
    (pullbackComp B.hom A.hom).app (projectiveTwistedPushforward n Q d) ≪≫
    eAB ≪≫
    projectiveTwistedPushforwardIso
      (projectiveFamilyAtBaseChangeIso n Q A.hom B).symm d

namespace ProjectiveOneStepMultiplicationBaseChangeComparison

/-- Degree-`d` base change for the family obtained after one prior base change. -/
noncomputable def degree_familyAt
    {T : Scheme.{u}} {n d : ℕ}
    {Q : (Scheme.projectiveSpaceOver n T).Modules}
    (C : ProjectiveOneStepMultiplicationBaseChangeComparison n Q d)
    (A : Over T) (B : Over A.left) :
    (pullback B.hom).obj
        (projectiveTwistedPushforward n (projectiveFamilyAt n Q A) d) ≅
      projectiveTwistedPushforward n
        (projectiveFamilyAt n (projectiveFamilyAt n Q A) B) d :=
  projectiveTwistedPushforwardIteratedBaseChangeIso Q A B
    (C.degree A) (C.degree ((Over.map A.hom).obj B))

/-- Degree-`d+1` base change for the family obtained after one prior base change. -/
noncomputable def degreeSucc_familyAt
    {T : Scheme.{u}} {n d : ℕ}
    {Q : (Scheme.projectiveSpaceOver n T).Modules}
    (C : ProjectiveOneStepMultiplicationBaseChangeComparison n Q d)
    (A : Over T) (B : Over A.left) :
    (pullback B.hom).obj
        (projectiveTwistedPushforward n (projectiveFamilyAt n Q A) (d + 1)) ≅
      projectiveTwistedPushforward n
        (projectiveFamilyAt n (projectiveFamilyAt n Q A) B) (d + 1) :=
  projectiveTwistedPushforwardIteratedBaseChangeIso Q A B
    (C.degreeSucc A) (C.degreeSucc ((Over.map A.hom).obj B))

/-- If multiplication is epic for the actual family obtained after two base changes,
then the pullback of multiplication for the once-base-changed family is epic.  This is
the epimorphism-only substitute for a fully coherent iterated multiplication comparison:
the two instances of `C.multiplication_comm` and functoriality of pullback suffice. -/
theorem pullback_multiplication_epi_of_iterated_family
    {T : Scheme.{u}} {n d : ℕ}
    {Q : (Scheme.projectiveSpaceOver n T).Modules}
    (C : ProjectiveOneStepMultiplicationBaseChangeComparison n Q d)
    (A : Over T) (B : Over A.left)
    [Epi (projectiveTwistedPushforwardMul n
      (projectiveFamilyAt n Q ((Over.map A.hom).obj B)) d)] :
    Epi ((pullback B.hom).map
      (projectiveTwistedPushforwardMul n (projectiveFamilyAt n Q A) d)) := by
  let p := projectiveTwistedPushforwardMul n Q d
  haveI hdirectComp : Epi
      ((pullback ((Over.map A.hom).obj B).hom).map p ≫
        (C.degreeSucc ((Over.map A.hom).obj B)).hom) := by
    rw [C.multiplication_comm]
    infer_instance
  haveI hdirect : Epi
      ((pullback ((Over.map A.hom).obj B).hom).map p) :=
    (epi_comp_iff_of_isIso _
      (C.degreeSucc ((Over.map A.hom).obj B)).hom).mp inferInstance
  haveI hdirect' : Epi ((pullback (B.hom ≫ A.hom)).map p) := by
    change Epi ((pullback ((Over.map A.hom).obj B).hom).map p)
    infer_instance
  have hcomp := (pullbackComp B.hom A.hom).hom.naturality p
  haveI hnestedComp : Epi
      ((pullback B.hom).map ((pullback A.hom).map p) ≫
        (pullbackComp B.hom A.hom).hom.app
          (projectiveTwistedPushforward n Q (d + 1))) := by
    change Epi ((pullback A.hom ⋙ pullback B.hom).map p ≫
      (pullbackComp B.hom A.hom).hom.app
        (projectiveTwistedPushforward n Q (d + 1)))
    rw [hcomp]
    infer_instance
  haveI hnested : Epi
      ((pullback B.hom).map ((pullback A.hom).map p)) :=
    (epi_comp_iff_of_isIso _
      ((pullbackComp B.hom A.hom).hom.app
        (projectiveTwistedPushforward n Q (d + 1)))).mp inferInstance
  have hA := congrArg (fun f ↦ (pullback B.hom).map f)
    (C.multiplication_comm A)
  simp only [Functor.map_comp] at hA
  haveI hsourceComp : Epi
      ((pullback B.hom).map
          (projectiveOneStepMultiplicationSourceBaseChangeIso
            n Q d A (C.degree A)).hom ≫
        (pullback B.hom).map
          (projectiveTwistedPushforwardMul n (projectiveFamilyAt n Q A) d)) := by
    rw [← hA]
    infer_instance
  exact epi_of_epi
    ((pullback B.hom).map
      (projectiveOneStepMultiplicationSourceBaseChangeIso
        n Q d A (C.degree A)).hom)
    ((pullback B.hom).map
      (projectiveTwistedPushforwardMul n (projectiveFamilyAt n Q A) d))

end ProjectiveOneStepMultiplicationBaseChangeComparison

end AlgebraicGeometry.Scheme.Modules

end

end
