module

public import StacksAndModuli.«Section2.2-Grassmannian».«part2.2.2-projectivity-of-the-grassmannian»
public import StacksAndModuli.«Section2.2-Grassmannian».«part2.2.4-projective-space-comparison»

/-!
# Immersions into free Grassmannians

This file packages the categorical and projective-geometric endgame for constructing a
quasi-projective moduli space from a natural transformation to a free relative
Grassmannian.  Its principal application is the finite twisted-free case of the Quot
functor in §2.4 of *Stacks and Moduli*.

The only geometric input retained by `HasFreeGrassmannianImmersion` is a natural
transformation to some `Gr(q,m)` which is relatively representable by immersions.  The
numerical condition `q ≤ m` is the nonempty-rank range in which the Plücker target has
positive rank.  The API then:

1. identifies the rank-one Plücker target with relative projective space;
2. proves that the chosen free Grassmannian representative is H-projective;
3. pulls the relatively representable immersion back to obtain a representative immersed
   in relative projective space.

Thus the regularity/flattening construction of the Quot-to-Grassmannian transformation is
the sole remaining input; representability and the projective-space factorization are
automatic.

Main declarations:
- `AlgebraicGeometry.Scheme.grassmannianOverRepresentation_isHProjective_of_le`;
- `AlgebraicGeometry.Scheme.HasFreeGrassmannianImmersion`;
- `AlgebraicGeometry.Scheme.
  exists_representableBy_immersion_projectiveSpace_of_hasFreeGrassmannianImmersion`;
- `AlgebraicGeometry.Scheme.TwistedFreeQuotHasFreeGrassmannianImmersion`;
- `AlgebraicGeometry.Scheme.
  exists_twistedFreeQuot_representableBy_immersion_projectiveSpace`.
-/

@[expose] public section

noncomputable section

-- These options are needed by the projective-space / rank-one-Grassmannian comparison.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Relative projective space is isomorphic over its base to the base-changed glued
rank-one Grassmannian.  This early API form keeps the comparison available to §2.4 without
importing the later discussion of projectivity notions. -/
noncomputable def projectiveSpaceOverIsoFreeRankOneGrassmannian
    (n : ℕ) (S : Scheme.{u}) :
    Over.mk (projectiveSpaceOverπ n S) ≅
      grassmannianOverRepresentation S 1 (n + 1) := by
  refine Over.isoMk (asIso (pullback.map
    (specULiftZIsTerminal.from S)
    (specULiftZIsTerminal.from (projectiveSpace n))
    (specULiftZIsTerminal.from S)
    (specULiftZIsTerminal.from (grassmannianGlueData.{u} 1 (n + 1)).glued)
    (𝟙 S) (ProjectiveSpectrum.Proj.projectiveSpaceToRankOneGrassmannian.{u} n)
    (𝟙 (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (specULiftZIsTerminal.hom_ext _ _)
    (specULiftZIsTerminal.hom_ext _ _))) ?_
  change pullback.map
      (specULiftZIsTerminal.from S)
      (specULiftZIsTerminal.from (projectiveSpace n))
      (specULiftZIsTerminal.from S)
      (specULiftZIsTerminal.from (grassmannianGlueData.{u} 1 (n + 1)).glued)
      (𝟙 S) (ProjectiveSpectrum.Proj.projectiveSpaceToRankOneGrassmannian.{u} n)
      (𝟙 (Spec (CommRingCat.of (ULift.{u} ℤ))))
      (specULiftZIsTerminal.hom_ext _ _)
      (specULiftZIsTerminal.hom_ext _ _) ≫
      pullback.fst (specULiftZIsTerminal.from S)
        (specULiftZIsTerminal.from
          (grassmannianGlueData.{u} 1 (n + 1)).glued) =
    projectiveSpaceOverπ n S
  rw [pullback.lift_fst, Category.comp_id]
  rfl

/-- In the nonempty-rank range, the canonical representative of the free relative
Grassmannian is H-projective.  The closed immersion is the relative Plücker morphism,
followed by the inverse of the rank-one-Grassmannian/projective-space comparison. -/
theorem grassmannianOverRepresentation_isHProjective_of_le
    (S : Scheme.{u}) (q m : ℕ) (hqm : q ≤ m) :
    IsHProjective (grassmannianOverRepresentation S q m).hom := by
  let N := m.choose q - 1
  have hchoose : m.choose q = N + 1 := by
    dsimp [N]
    exact (Nat.sub_add_cancel (Nat.choose_pos hqm)).symm
  let e : Over.mk (projectiveSpaceOverπ N S) ≅
      grassmannianOverRepresentation S 1 (m.choose q) := by
    rw [hchoose]
    exact projectiveSpaceOverIsoFreeRankOneGrassmannian N S
  refine ⟨N, pluckerOverMorphism S q m ≫ e.inv.left, ?_, ?_⟩
  · exact MorphismProperty.IsStableUnderComposition.comp_mem _ _
      (isClosedImmersion_pluckerOverMorphism S q m) inferInstance
  · rw [Category.assoc]
    rw [show e.inv.left ≫ projectiveSpaceOverπ N S =
        (grassmannianOverRepresentation S 1 (m.choose q)).hom from Over.w e.inv]
    exact pluckerOverMorphism_fst S q m

/-- A presheaf on schemes over `S` has a free-Grassmannian immersion if it maps to some
`Gr(q,m)` in the nonempty-rank range by a natural transformation relatively representable
by immersions. -/
def HasFreeGrassmannianImmersion (S : Scheme.{u})
    (F : (Over S)ᵒᵖ ⥤ Type (u + 1)) : Prop :=
  ∃ (q m : ℕ), q ≤ m ∧ ∃ α : F ⟶ Modules.grassmannianFunctorOver S q m,
    MorphismProperty.relative uliftYoneda.{u + 1}
      (MorphismProperty.over
        (@IsImmersion : MorphismProperty Scheme.{u})) α

/-- Construct the free-Grassmannian immersion predicate from an explicit natural
transformation and its relative immersion property. -/
theorem hasFreeGrassmannianImmersion_of_relative
    (S : Scheme.{u}) (F : (Over S)ᵒᵖ ⥤ Type (u + 1))
    (q m : ℕ) (hqm : q ≤ m)
    (α : F ⟶ Modules.grassmannianFunctorOver S q m)
    (hα : MorphismProperty.relative uliftYoneda.{u + 1}
      (MorphismProperty.over
        (@IsImmersion : MorphismProperty Scheme.{u})) α) :
    HasFreeGrassmannianImmersion S F :=
  ⟨q, m, hqm, α, hα⟩

/-- A relatively representable immersion into a free Grassmannian produces a
representative immersed in relative projective space.  This is the complete categorical
endgame after the Grassmannian transformation has been constructed. -/
theorem exists_representableBy_immersion_projectiveSpace_of_hasFreeGrassmannianImmersion
    (S : Scheme.{u}) (F : (Over S)ᵒᵖ ⥤ Type (u + 1))
    (hF : HasFreeGrassmannianImmersion S F) :
    ∃ Q : Over S, Nonempty (F.RepresentableBy Q) ∧
      ∃ (N : ℕ) (ι : Q.left ⟶ projectiveSpaceOver N S),
        IsImmersion ι ∧ ι ≫ projectiveSpaceOverπ N S = Q.hom := by
  obtain ⟨q, m, hqm, α, hα⟩ := hF
  let Q₀ : Over S := grassmannianOverRepresentation S q m
  let eG : (Modules.grassmannianFunctorOver S q m).RepresentableBy Q₀ :=
    grassmannianFunctorOverRepresentableBy S q m
  let eG' : uliftYoneda.{u + 1}.obj Q₀ ≅
      Modules.grassmannianFunctorOver S q m :=
    (Functor.RepresentableBy.equivUliftYonedaIso _ _) eG
  let Q : Over S := hα.rep.pullback eG'.hom
  let j : Q ⟶ Q₀ := hα.rep.snd eG'.hom
  have hj : IsImmersion j.left := hα.property_snd eG'.hom
  have hfst : IsIso (hα.rep.fst eG'.hom) :=
    (hα.rep.isPullback eG'.hom).isIso_fst_of_isIso
  let eF' : uliftYoneda.{u + 1}.obj Q ≅ F :=
    @asIso _ _ _ _ (hα.rep.fst eG'.hom) hfst
  let eF : F.RepresentableBy Q :=
    (Functor.RepresentableBy.equivUliftYonedaIso F Q).symm eF'
  refine ⟨Q, ⟨eF⟩, ?_⟩
  obtain ⟨N, i, hi, hcomp⟩ :=
    grassmannianOverRepresentation_isHProjective_of_le S q m hqm
  refine ⟨N, j.left ≫ i, ?_, ?_⟩
  · have hii : IsImmersion i := by
      obtain ⟨hipre, hclosed⟩ := IsClosedImmersion.iff_isPreimmersion.mp hi
      exact { __ := hipre, isLocallyClosed_range := hclosed.isLocallyClosed }
    exact MorphismProperty.IsStableUnderComposition.comp_mem _ _ hj hii
  · rw [Category.assoc, hcomp, Over.w j]

/-- The precise Grassmannian-immersion input for the finite twisted-free fixed-polynomial
Quot functor.  Constructing this proposition is exactly Steps 1--3 of §2.4: regularity and
cohomology-and-base-change define the natural map, while flattening stratification proves
that it is relatively representable by immersions. -/
def TwistedFreeQuotHasFreeGrassmannianImmersion
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ) : Prop :=
  HasFreeGrassmannianImmersion S
    (quotFunctorP
      (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n S (-l)) P)

/-- Construct the twisted-free Quot Grassmannian-immersion predicate from an explicit
natural transformation. -/
theorem twistedFreeQuotHasFreeGrassmannianImmersion_of_relative
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (q m : ℕ) (hqm : q ≤ m)
    (α : quotFunctorP
      (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n S (-l)) P ⟶
        Modules.grassmannianFunctorOver S q m)
    (hα : MorphismProperty.relative uliftYoneda.{u + 1}
      (MorphismProperty.over
        (@IsImmersion : MorphismProperty Scheme.{u})) α) :
    TwistedFreeQuotHasFreeGrassmannianImmersion n S l r P :=
  hasFreeGrassmannianImmersion_of_relative S _ q m hqm α hα

/-- Once regularity and flattening supply the free-Grassmannian immersion, the finite
twisted-free fixed-polynomial Quot functor has a representative immersed in relative
projective space. -/
theorem exists_twistedFreeQuot_representableBy_immersion_projectiveSpace
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (h : TwistedFreeQuotHasFreeGrassmannianImmersion n S l r P) :
    ∃ Q : Over S,
      Nonempty ((quotFunctorP
        (∐ fun _ : ULift.{u} (Fin r) ↦
          projectiveSpaceOverTwist n S (-l)) P).RepresentableBy Q) ∧
      ∃ (N : ℕ) (ι : Q.left ⟶ projectiveSpaceOver N S),
        IsImmersion ι ∧ ι ≫ projectiveSpaceOverπ N S = Q.hom :=
  exists_representableBy_immersion_projectiveSpace_of_hasFreeGrassmannianImmersion
    S _ h

end AlgebraicGeometry.Scheme

end
