module

public import StacksAndModuli.API.ProjectiveFlatteningUniversalFamily
public import StacksAndModuli.API.SheafFlatteningProjectiveRank
public import StacksAndModuli.API.ProjectiveSpaceZeroGlobalSectionsRank
public import StacksAndModuli.API.ProjectiveSpaceZeroGrassmannianQuot

/-!
# Projective flattening in relative dimension zero

Relative projective zero-space is the base itself.  Accordingly, the fixed constant
Hilbert-polynomial flattening condition for a finitely presented quasicoherent sheaf on
`P^0_T` is one ordinary finite-flat rank condition on `T`.  This file proves that
identification over arbitrary test schemes and packages it as a one-term
`FiniteFlatRankPresentation`.

Main declarations:

* `AlgebraicGeometry.Scheme.Modules.isProjectiveOfRank_projectiveZeroNormalization`;
* `AlgebraicGeometry.Scheme.Modules.projectiveFlatteningFunctorZeroIso`;
* `AlgebraicGeometry.Scheme.Modules.projectiveFlatteningHasFiniteRankPresentation_zero`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

variable {T : Scheme.{u}}

/-- Transport a sheaf on relative projective zero-space to the base. -/
noncomputable def projectiveZeroNormalization
    (Q : (Scheme.projectiveSpaceOver 0 T).Modules) : T.Modules :=
  (pullback (Scheme.projectiveSpaceOverZeroIso T).inv).obj Q

instance projectiveZeroNormalization_isQuasicoherent
    (Q : (Scheme.projectiveSpaceOver 0 T).Modules) [Q.IsQuasicoherent] :
    (projectiveZeroNormalization Q).IsQuasicoherent := by
  dsimp only [projectiveZeroNormalization]
  infer_instance

/-- Normalization of a projective zero-space family commutes with arbitrary base
change. -/
noncomputable def projectiveZeroNormalization_pullbackIso
    {A : Scheme.{u}} (Q : (Scheme.projectiveSpaceOver 0 T).Modules) (f : A ⟶ T) :
    projectiveZeroNormalization
        ((pullback (Scheme.projectiveSpaceOverMap 0 f)).obj Q) ≅
      (pullback f).obj (projectiveZeroNormalization Q) := by
  have hnat : (Scheme.projectiveSpaceOverZeroIso A).inv ≫
        Scheme.projectiveSpaceOverMap 0 f =
      f ≫ (Scheme.projectiveSpaceOverZeroIso T).inv := by
    rw [← cancel_mono (Scheme.projectiveSpaceOverZeroIso T).hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [Scheme.projectiveSpaceOverZeroIso_naturality]
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  exact
    (pullbackComp (Scheme.projectiveSpaceOverZeroIso A).inv
      (Scheme.projectiveSpaceOverMap 0 f)).app Q ≪≫
    (pullbackCongr hnat).app Q ≪≫
    ((pullbackComp f (Scheme.projectiveSpaceOverZeroIso T).inv).app Q).symm

/-- Pulling the normalized sheaf back to projective zero-space recovers the original
family. -/
noncomputable def projectiveZeroNormalization_pullbackProjectiveIso
    (Q : (Scheme.projectiveSpaceOver 0 T).Modules) :
    (pullback (Scheme.projectiveSpaceOverZeroIso T).hom).obj
        (projectiveZeroNormalization Q) ≅ Q :=
  (pullbackComp (Scheme.projectiveSpaceOverZeroIso T).hom
      (Scheme.projectiveSpaceOverZeroIso T).inv).app Q ≪≫
    (pullbackCongr (Scheme.projectiveSpaceOverZeroIso T).hom_inv_id).app Q ≪≫
    (pullbackId _).app Q

/-- A finitely presented flat family on projective zero-space with constant Hilbert
polynomial `q` normalizes to a vector bundle of rank `q` on the base. -/
theorem isProjectiveOfRank_projectiveZeroNormalization
    (Q : (Scheme.projectiveSpaceOver 0 T).Modules) [Q.IsQuasicoherent] (q : ℕ)
    (hfp : Q.IsFinitePresentation)
    (hflat : Q.FlatOver (Scheme.projectiveSpaceOverπ 0 T))
    (hP : Scheme.HasFiberwiseHilbertPolynomial Q (Polynomial.C (q : ℚ))) :
    IsProjectiveOfRank q (projectiveZeroNormalization Q) := by
  let N := projectiveZeroNormalization Q
  intro t
  obtain ⟨_, ⟨U, hU, rfl⟩, htU, -⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ t) isOpen_univ
  let A : T.affineOpens := ⟨U, hU⟩
  let R := Γ(T, A.1)
  let j := A.2.fromSpec
  let QA := (pullback (Scheme.projectiveSpaceOverMap 0 j)).obj Q
  let pT := Scheme.projectiveSpaceOverπ 0 T
  let pA := Scheme.projectiveSpaceOverπ 0 (Spec (.of R))
  let zA := Scheme.projectiveSpaceOverZeroIso (Spec (.of R))
  let MA := projectiveZeroNormalization QA
  letI : QA.IsQuasicoherent := by
    dsimp only [QA]
    infer_instance
  have hfpQA : QA.IsFinitePresentation :=
    isFinitePresentation_pullback_of_isFinitePresentation _ hfp
  have hflatQA : QA.FlatOver pA :=
    FlatOver.pullback_of_isPullback
      (Scheme.projectiveSpaceOverMap 0 j) pA pT j
      (Scheme.isPullback_projectiveSpaceOverMap 0 j).flip Q hflat
  have hPA : Scheme.HasFiberwiseHilbertPolynomial QA (Polynomial.C (q : ℚ)) :=
    Scheme.HasFiberwiseHilbertPolynomial.pullback j hP
  obtain ⟨hfinQA, hprojQA⟩ :=
    Scheme.projectiveSpaceZero_globalSections_finite_projective
      QA hfpQA hflatQA
  have hrankQA := Scheme.projectiveSpaceZero_globalSections_rankAtStalk_eq
    QA q hfinQA hprojQA hPA
  letI : Module R Γ(QA, ⊤) := globalSectionsModule pA QA
  letI : Module.Finite R Γ(QA, ⊤) := hfinQA
  letI : Module.Projective R Γ(QA, ⊤) := hprojQA
  have hcomp : zA.inv ≫ pA = 𝟙 (Spec (.of R)) := by
    simpa only [zA, pA, Scheme.projectiveSpaceOverZeroIso_hom] using zA.inv_hom_id
  letI : Module R Γ(MA, ⊤) := globalSectionsModule (zA.inv ≫ pA) MA
  let eΓ := pullbackGlobalSectionsViaIsoLinearEquiv zA.inv pA QA (Iso.refl MA)
  have hfinMA : Module.Finite R Γ(MA, ⊤) := Module.Finite.equiv eΓ
  have hprojMA : Module.Projective R Γ(MA, ⊤) := Module.Projective.of_equiv' eΓ
  have hrankMA : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk Γ(MA, ⊤) p = q := fun p ↦
    (congrFun (Module.rankAtStalk_eq_of_equiv eΓ) p).symm.trans (hrankQA p)
  have hcoord : Module.Finite R (moduleSpecΓFunctor.obj MA) ∧
      Module.Projective R (moduleSpecΓFunctor.obj MA) ∧
      ∀ p : PrimeSpectrum R,
        Module.rankAtStalk (moduleSpecΓFunctor.obj MA) p = q := by
    let moduleId : Module R Γ(MA, ⊤) := globalSectionsModule (𝟙 (Spec (.of R))) MA
    change @Module.Finite R Γ(MA, ⊤) _ _ moduleId ∧
      @Module.Projective R _ Γ(MA, ⊤) _ moduleId ∧
      ∀ p : PrimeSpectrum R,
        @Module.rankAtStalk R Γ(MA, ⊤) _ _ moduleId p = q
    have hmodule : (globalSectionsModule (zA.inv ≫ pA) MA) = moduleId := by
      dsimp only [moduleId]
      rw [hcomp]
    rw [← hmodule]
    exact ⟨hfinMA, hprojMA, hrankMA⟩
  have htop := moduleSpecΓFunctor_finite_projective_rank_top MA
    hcoord.1 hcoord.2.1 hcoord.2.2
  let e := projectiveZeroNormalization_pullbackIso Q j
  obtain ⟨hfinPull, hprojPull, hrankPull⟩ :=
    sections_finite_projective_rank_of_iso e ⊤
      htop.1 htop.2.1 htop.2.2
  obtain ⟨hfin, hproj, hrank⟩ :=
    sections_finite_projective_rank_of_pullback_openImmersion
      j N ⊤ hfinPull hprojPull hrankPull
  have himage : j ''ᵁ (⊤ : (Spec (.of R)).Opens) = A.1 := by
    rw [Scheme.Hom.image_top_eq_opensRange, A.2.opensRange_fromSpec]
  rw [himage] at hfin hproj hrank
  exact ⟨A, htU, hfin, hproj, hrank⟩

variable (Q : (Scheme.projectiveSpaceOver 0 T).Modules) [Q.IsQuasicoherent]

/-- A point of the ordinary rank-flattening functor of the normalized sheaf gives a
point of the projective flattening functor with constant polynomial. -/
noncomputable def projectiveFlatteningZeroPointOfFlatRankPoint
    (hfp : Q.IsFinitePresentation) (q : ℕ) (A : Over T)
    (x : (flatRankFunctorOver (projectiveZeroNormalization Q) q).obj (op A)) :
    (projectiveFlatteningFunctor 0 Q (P := Polynomial.C (q : ℚ))).obj (op A) := by
  have hloc : Scheme.LocallyFactors
      (affineStratum (projectiveZeroNormalization Q) q) A := x.down.down
  have hRankPull : IsProjectiveOfRank q
      ((pullback A.hom).obj (projectiveZeroNormalization Q)) :=
    (locallyFactors_affineStratum_iff_isProjectiveOfRank
      (projectiveZeroNormalization Q)
      (isFinitePresentation_pullback_of_isFinitePresentation
        (Scheme.projectiveSpaceOverZeroIso T).inv hfp) q A).mp hloc
  let QA := projectiveFamilyAt 0 Q A
  let NA := projectiveZeroNormalization QA
  let eNorm : NA ≅ (pullback A.hom).obj (projectiveZeroNormalization Q) :=
    projectiveZeroNormalization_pullbackIso Q A.hom
  have hRankNA : IsProjectiveOfRank q NA := hRankPull.of_iso eNorm.symm
  let eBack : (pullback (Scheme.projectiveSpaceOverZeroIso A.left).hom).obj NA ≅ QA :=
    projectiveZeroNormalization_pullbackProjectiveIso QA
  have hRankBack : IsProjectiveOfRank q
      ((pullback (Scheme.projectiveSpaceOverZeroIso A.left).hom).obj NA) :=
    hRankNA.pullback (Scheme.projectiveSpaceOverZeroIso A.left).hom
  have hflatBack :
      ((pullback (Scheme.projectiveSpaceOverZeroIso A.left).hom).obj NA).FlatOver
        (Scheme.projectiveSpaceOverπ 0 A.left) := by
    rw [← Scheme.projectiveSpaceOverZeroIso_hom A.left]
    exact hRankBack.isFiniteLocallyFree.flatOver_of_flat
      (Scheme.projectiveSpaceOverZeroIso A.left).hom
  have hflatQA : QA.FlatOver (Scheme.projectiveSpaceOverπ 0 A.left) :=
    FlatOver.of_iso eBack hflatBack
  have hPBack : Scheme.HasFiberwiseHilbertPolynomial
      ((pullback (Scheme.projectiveSpaceOverZeroIso A.left).hom).obj NA)
      (Polynomial.C (q : ℚ)) := by
    rw [Scheme.projectiveSpaceOverZeroIso_hom]
    exact hRankNA.pullback_projectiveSpaceOverZero_hasFiberwise
  have hPQA : Scheme.HasFiberwiseHilbertPolynomial QA (Polynomial.C (q : ℚ)) :=
    Scheme.HasFiberwiseHilbertPolynomial.of_iso eBack hPBack
  exact ULift.up (PLift.up ⟨hflatQA, hPQA⟩)

/-- A point of the constant-polynomial projective flattening functor gives the
ordinary rank-flattening condition for the normalized sheaf. -/
noncomputable def flatRankPointOfProjectiveFlatteningZeroPoint
    (hfp : Q.IsFinitePresentation) (q : ℕ) (A : Over T)
    (x : (projectiveFlatteningFunctor 0 Q
      (P := Polynomial.C (q : ℚ))).obj (op A)) :
    (flatRankFunctorOver (projectiveZeroNormalization Q) q).obj (op A) := by
  let QA := projectiveFamilyAt 0 Q A
  haveI : QA.IsQuasicoherent := inferInstance
  have hfpQA : QA.IsFinitePresentation :=
    isFinitePresentation_pullback_of_isFinitePresentation _ hfp
  have hRankNA : IsProjectiveOfRank q (projectiveZeroNormalization QA) :=
    isProjectiveOfRank_projectiveZeroNormalization QA q hfpQA
      x.down.down.1 x.down.down.2
  let eNorm : projectiveZeroNormalization QA ≅
      (pullback A.hom).obj (projectiveZeroNormalization Q) :=
    projectiveZeroNormalization_pullbackIso Q A.hom
  have hRankPull : IsProjectiveOfRank q
      ((pullback A.hom).obj (projectiveZeroNormalization Q)) :=
    hRankNA.of_iso eNorm
  exact ULift.up (PLift.up
    ((locallyFactors_affineStratum_iff_isProjectiveOfRank
      (projectiveZeroNormalization Q)
      (isFinitePresentation_pullback_of_isFinitePresentation
        (Scheme.projectiveSpaceOverZeroIso T).inv hfp) q A).mpr hRankPull))

/-- The constant-polynomial projective flattening functor on relative projective
zero-space is one ordinary rank-flattening functor on the base. -/
noncomputable def projectiveFlatteningFunctorZeroIso
    (hfp : Q.IsFinitePresentation) (q : ℕ) :
    flatRankFunctorOver (projectiveZeroNormalization Q) q ⋙ uliftFunctor.{u + 1} ≅
      projectiveFlatteningFunctor 0 Q (P := Polynomial.C (q : ℚ)) where
  hom :=
    { app := fun A ↦ ↾fun x ↦
        projectiveFlatteningZeroPointOfFlatRankPoint Q hfp q A.unop x.down
      naturality := by
        intro A B g
        apply ConcreteCategory.hom_ext
        intro x
        exact (projectiveFlatteningFunctor_subsingleton
          0 Q (Polynomial.C (q : ℚ)) B).elim _ _ }
  inv :=
    { app := fun A ↦ ↾fun x ↦ ULift.up
        (flatRankPointOfProjectiveFlatteningZeroPoint Q hfp q A.unop x)
      naturality := by
        intro A B g
        apply ConcreteCategory.hom_ext
        intro x
        haveI := Scheme.factorsFunctor_subsingleton
          (affineStratum (projectiveZeroNormalization Q) q) B
        haveI : Subsingleton
            ((flatRankFunctorOver (projectiveZeroNormalization Q) q ⋙
              uliftFunctor.{u + 1}).obj B) := by
          change Subsingleton
            (ULift ((flatRankFunctorOver (projectiveZeroNormalization Q) q).obj B))
          infer_instance
        exact Subsingleton.elim _ _ }
  hom_inv_id := by
    ext A x
    haveI := Scheme.factorsFunctor_subsingleton
      (affineStratum (projectiveZeroNormalization Q) q) A
    haveI : Subsingleton
        ((flatRankFunctorOver (projectiveZeroNormalization Q) q ⋙
          uliftFunctor.{u + 1}).obj A) := by
      change Subsingleton
        (ULift ((flatRankFunctorOver (projectiveZeroNormalization Q) q).obj A))
      infer_instance
    exact Subsingleton.elim _ _
  inv_hom_id := by
    ext A x
    exact (projectiveFlatteningFunctor_subsingleton
      0 Q (Polynomial.C (q : ℚ)) A).elim _ _

/-- Projective flattening in relative dimension zero has a one-term finite-rank
presentation, over an arbitrary base scheme. -/
theorem projectiveFlatteningHasFiniteRankPresentation_zero
    (hfp : Q.IsFinitePresentation) (q : ℕ) :
    ProjectiveFlatteningHasFiniteRankPresentation
      0 Q (P := Polynomial.C (q : ℚ)) := by
  refine ⟨{
    count := 1
    sheaf := fun _ ↦ projectiveZeroNormalization Q
    rank := fun _ ↦ q
    isQuasicoherent := fun _ ↦ inferInstance
    finite := fun _ U ↦ ?_
    iso := ?_ }⟩
  · have hfpN : (projectiveZeroNormalization Q).IsFinitePresentation :=
      isFinitePresentation_pullback_of_isFinitePresentation
        (Scheme.projectiveSpaceOverZeroIso T).inv hfp
    have hfpPull : ((pullback U.1.ι).obj
        (projectiveZeroNormalization Q)).IsFinitePresentation :=
      isFinitePresentation_pullback_of_isFinitePresentation U.1.ι hfpN
    have hfpSec : Module.FinitePresentation Γ(U.1.toScheme, ⊤)
        Γ((pullback U.1.ι).obj (projectiveZeroNormalization Q), ⊤) :=
      (Scheme.Modules.isFinitePresentation_iff_sections_affineOpens
        ((pullback U.1.ι).obj (projectiveZeroNormalization Q))).mp
          hfpPull ⟨⊤, isAffineOpen_top _⟩
    letI : Module.FinitePresentation Γ(U.1.toScheme, ⊤)
        Γ((pullback U.1.ι).obj (projectiveZeroNormalization Q), ⊤) := hfpSec
    infer_instance
  · let F := flatRankFunctorOver (projectiveZeroNormalization Q) q ⋙
      uliftFunctor.{u + 1}
    have hF : ∀ A, Subsingleton (F.obj A) := by
      intro A
      change Subsingleton
        (ULift ((flatRankFunctorOver (projectiveZeroNormalization Q) q).obj A))
      haveI := Scheme.factorsFunctor_subsingleton
        (affineStratum (projectiveZeroNormalization Q) q) A
      infer_instance
    exact finProdFunctorLargeSingletonIso F hF ≪≫
      projectiveFlatteningFunctorZeroIso Q hfp q

end AlgebraicGeometry.Scheme.Modules

end
