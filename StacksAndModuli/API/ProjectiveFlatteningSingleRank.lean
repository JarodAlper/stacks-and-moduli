module

public import StacksAndModuli.API.ProjectiveFlatteningFiniteDegree
public import StacksAndModuli.API.ProjectiveFlatteningLocusBaseChange

/-!
# Projective flattening from one algebraic rank condition

The finite sheaf cutting out a projective flattening locus need not be a geometric
pushforward before flatness is known.  This file gives a one-condition interface: any
finitely presented quasicoherent sheaf on the base whose pulled-back projective rank is
equivalent to the flat fixed-Hilbert-polynomial condition represents that condition by an
immersion.

This is the interface used by the graded Grassmann construction.  Its finite sheaf can be
the algebraic fixed-degree cokernel of the universal relation, so its formation commutes
with base change without assuming Cohomology and Base Change for the reconstructed family.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

variable {T : Scheme.{u}} (n : ℕ)
variable (Q : (Scheme.projectiveSpaceOver n T).Modules) [Q.IsQuasicoherent]
variable (P : Polynomial ℚ)

/-- Data identifying projective flattening with one finite projective-rank condition
on a sheaf over the base. -/
structure ProjectiveFlatteningSingleRankData where
  /-- The algebraic finite sheaf whose rank cuts out the flattening locus. -/
  sheaf : T.Modules
  /-- Its prescribed rank. -/
  rank : ℕ
  /-- Quasicoherence of the rank sheaf. -/
  isQuasicoherent : sheaf.IsQuasicoherent
  /-- Finite presentation of the rank sheaf. -/
  isFinitePresentation : sheaf.IsFinitePresentation
  /-- The rank condition is exactly flatness with the fixed fibrewise Hilbert polynomial. -/
  rank_iff (A : Over T) :
    IsProjectiveOfRank rank ((pullback A.hom).obj sheaf) ↔
      (projectiveFamilyAt n Q A).FlatOver
          (Scheme.projectiveSpaceOverπ n A.left) ∧
        Scheme.HasFiberwiseHilbertPolynomial (projectiveFamilyAt n Q A) P

namespace ProjectiveFlatteningSingleRankData

/-- A point of the rank locus gives a point of the projective flattening functor. -/
noncomputable def projectivePointOfFlatRankPoint
    (D : ProjectiveFlatteningSingleRankData n Q P) (A : Over T)
    (x : (flatRankFunctorOver D.sheaf D.rank).obj (op A)) :
    (projectiveFlatteningFunctor n Q (P := P)).obj (op A) := by
  letI : D.sheaf.IsQuasicoherent := D.isQuasicoherent
  have hRank : IsProjectiveOfRank D.rank
      ((pullback A.hom).obj D.sheaf) :=
    (locallyFactors_affineStratum_iff_isProjectiveOfRank
      D.sheaf D.isFinitePresentation D.rank A).mp x.down.down
  exact ULift.up (PLift.up ((D.rank_iff A).mp hRank))

/-- A flat fixed-polynomial projective family satisfies the algebraic rank condition. -/
noncomputable def flatRankPointOfProjectivePoint
    (D : ProjectiveFlatteningSingleRankData n Q P) (A : Over T)
    (x : (projectiveFlatteningFunctor n Q (P := P)).obj (op A)) :
    (flatRankFunctorOver D.sheaf D.rank).obj (op A) := by
  letI : D.sheaf.IsQuasicoherent := D.isQuasicoherent
  have hRank : IsProjectiveOfRank D.rank
      ((pullback A.hom).obj D.sheaf) :=
    (D.rank_iff A).mpr x.down.down
  exact ULift.up (PLift.up
    ((locallyFactors_affineStratum_iff_isProjectiveOfRank
      D.sheaf D.isFinitePresentation D.rank A).mpr hRank))

/-- The one algebraic rank locus is naturally the projective flattening functor. -/
noncomputable def functorIso
    (D : ProjectiveFlatteningSingleRankData n Q P) :
    flatRankFunctorOver D.sheaf D.rank ⋙ uliftFunctor.{u + 1} ≅
      projectiveFlatteningFunctor n Q (P := P) where
  hom :=
    { app := fun A ↦ ↾fun x ↦
        projectivePointOfFlatRankPoint n Q P D A.unop x.down
      naturality := by
        intro A B g
        apply ConcreteCategory.hom_ext
        intro x
        exact (projectiveFlatteningFunctor_subsingleton n Q P B).elim _ _ }
  inv :=
    { app := fun A ↦ ↾fun x ↦ ULift.up
        (flatRankPointOfProjectivePoint n Q P D A.unop x)
      naturality := by
        intro A B g
        apply ConcreteCategory.hom_ext
        intro x
        letI : D.sheaf.IsQuasicoherent := D.isQuasicoherent
        haveI := Scheme.factorsFunctor_subsingleton
          (affineStratum D.sheaf D.rank) B
        haveI : Subsingleton
            ((flatRankFunctorOver D.sheaf D.rank ⋙
              uliftFunctor.{u + 1}).obj B) := by
          change Subsingleton
            (ULift ((flatRankFunctorOver D.sheaf D.rank).obj B))
          infer_instance
        exact Subsingleton.elim _ _ }
  hom_inv_id := by
    ext A x
    letI : D.sheaf.IsQuasicoherent := D.isQuasicoherent
    haveI := Scheme.factorsFunctor_subsingleton
      (affineStratum D.sheaf D.rank) A
    haveI : Subsingleton
        ((flatRankFunctorOver D.sheaf D.rank ⋙
          uliftFunctor.{u + 1}).obj A) := by
      change Subsingleton
        (ULift ((flatRankFunctorOver D.sheaf D.rank).obj A))
      infer_instance
    exact Subsingleton.elim _ _
  inv_hom_id := by
    ext A x
    exact (projectiveFlatteningFunctor_subsingleton n Q P A).elim _ _

/-- A single-rank description gives the general finite-flat-rank presentation. -/
noncomputable def toFiniteFlatRankPresentation
    (D : ProjectiveFlatteningSingleRankData n Q P) :
    FiniteFlatRankPresentation (projectiveFlatteningFunctor n Q (P := P)) where
  count := 1
  sheaf := fun _ ↦ D.sheaf
  rank := fun _ ↦ D.rank
  isQuasicoherent := fun _ ↦ D.isQuasicoherent
  finite := fun _ U ↦ by
    have hfpPull : ((pullback U.1.ι).obj D.sheaf).IsFinitePresentation :=
      isFinitePresentation_pullback_of_isFinitePresentation U.1.ι
        D.isFinitePresentation
    have hfpSec : Module.FinitePresentation Γ(U.1.toScheme, ⊤)
        Γ((pullback U.1.ι).obj D.sheaf, ⊤) :=
      (Scheme.Modules.isFinitePresentation_iff_sections_affineOpens
        ((pullback U.1.ι).obj D.sheaf)).mp
          hfpPull ⟨⊤, isAffineOpen_top _⟩
    letI : Module.FinitePresentation Γ(U.1.toScheme, ⊤)
        Γ((pullback U.1.ι).obj D.sheaf, ⊤) := hfpSec
    infer_instance
  iso := by
    let F := flatRankFunctorOver D.sheaf D.rank ⋙ uliftFunctor.{u + 1}
    have hF : ∀ A, Subsingleton (F.obj A) := by
      intro A
      letI : D.sheaf.IsQuasicoherent := D.isQuasicoherent
      change Subsingleton (ULift ((flatRankFunctorOver D.sheaf D.rank).obj A))
      haveI := Scheme.factorsFunctor_subsingleton
        (affineStratum D.sheaf D.rank) A
      infer_instance
    exact finProdFunctorLargeSingletonIso F hF ≪≫ functorIso n Q P D

/-- A single algebraic rank condition represents the projective flattening locus by
an immersion into the base. -/
theorem projectiveFlatteningHasFiniteRankPresentation
    (D : ProjectiveFlatteningSingleRankData n Q P) :
    ProjectiveFlatteningHasFiniteRankPresentation n Q (P := P) :=
  ⟨toFiniteFlatRankPresentation n Q P D⟩

/-- A single algebraic rank condition gives the represented immersed projective
flattening locus directly. -/
noncomputable def toLocusWitness
    (D : ProjectiveFlatteningSingleRankData n Q P) :
    ProjectiveFlatteningLocusWitness n Q P :=
  ProjectiveFlatteningLocusWitness.ofFiniteRankPresentation n Q P
    (projectiveFlatteningHasFiniteRankPresentation n Q P D)

end ProjectiveFlatteningSingleRankData

end AlgebraicGeometry.Scheme.Modules

end

end
