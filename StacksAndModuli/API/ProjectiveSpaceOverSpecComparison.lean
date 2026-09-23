module

public import StacksAndModuli.API.ProjectiveTwistBaseChange
public import StacksAndModuli.API.ProjectiveTwistGlobalSections
public import StacksAndModuli.API.SchemeModulesGlobalSectionsIso
public import StacksAndModuli.«Section2.1-Intro».«part2.1.3-projective-space-and-hilbert-quot-functors»

/-!
# Relative projective space over an affine scheme as polynomial Proj

This file isolates the geometric comparison between relative projective space over
`Spec R` and the intrinsic `Proj` of `R[x₀, …, xₙ]`.  It also identifies the
corresponding twisting sheaves and the two scalar actions on their global sections.

These declarations are independent of the graded-cohomology model.  Keeping them in
this API lets concrete global-section computations use the affine `Proj` comparison
without importing the unfinished relative-cohomology package.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Relative projective space over an affine scheme is canonically the intrinsic `Proj`
of the polynomial ring over its coefficient ring. -/
noncomputable def projectiveSpaceOverSpecIso
    (n : ℕ) (R : Type u) [CommRing R] :
    Scheme.projectiveSpaceOver n (Spec (.of R)) ≅
      Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) := by
  unfold Scheme.projectiveSpaceOver Scheme.projectiveSpace
  exact Proj.polynomialProjOverSpecIso (Fin (n + 1)) R

/-- Pulling a relative twist of the structure sheaf across
`projectiveSpaceOverSpecIso` gives the intrinsic polynomial-`Proj` twist. -/
noncomputable def projectiveSpaceOverUnitTwistPullbackIso
    (n : ℕ) (R : Type u) [CommRing R] (d : ℤ) :
    (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj
        (Scheme.projectiveSpaceOverTwistModule
          (SheafOfModules.unit
            (Scheme.projectiveSpaceOver n (Spec (.of R))).ringCatSheaf) d) ≅
      ProjectiveSpectrum.Twist.twist
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d := by
  unfold Scheme.projectiveSpaceOverTwistModule Scheme.projectiveSpaceOverTwist
  exact
    (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).mapIso
        (Scheme.Modules.tensorLeftUnitIso _) ≪≫
      Proj.polynomialProjOverSpec_pullbackAbsoluteTwistIso
        (Fin (n + 1)) R d ≪≫
      ProjectiveSpectrum.Twist.polynomialPullbackIso
        (Fin (n + 1)) (Proj.uliftIntCastRingHom R) d

private theorem awayToSection_fromZeroRingHom
    {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (G : ℕ → σ) [GradedRing G] (p : G 0) :
    Proj.awayToSection G 1
        (HomogeneousLocalization.fromZeroRingHom G (Submonoid.powers 1) p) =
      ProjectiveSpectrum.Twist.degreeZeroSection G p (Proj.basicOpen G 1) := by
  refine Subtype.ext (funext fun x ↦ ?_)
  apply HomogeneousLocalization.val_injective
  erw [ProjectiveSpectrum.Proj.awayToSection_apply]

private theorem transportSectionToTop
    (X : Scheme.{u}) (U : X.Opens) (e : U = ⊤) (s : Γ(X, U)) :
    ((U.topIso.inv ≫ (X.isoOfEq e).inv.appTop ≫ X.topIso.inv.appTop) s) =
      e ▸ s := by
  subst U
  simp only [Scheme.isoOfEq_rfl, Iso.refl_inv, Scheme.Hom.id_app,
    Category.id_comp, CommRingCat.comp_apply]
  have hmap : (⊤ : X.Opens).topIso.inv = X.topIso.hom.appTop := by
    rw [Scheme.topIso_hom, Scheme.Opens.ι_appTop]
    rfl
  rw [hmap, ← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop]
  simp

private theorem degreeZeroSection_cast
    {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (G : ℕ → σ) [GradedRing G] (p : G 0)
    {U V : Opens (ProjectiveSpectrum.top G)} (e : U = V) :
    e ▸ ProjectiveSpectrum.Twist.degreeZeroSection G p U =
      ProjectiveSpectrum.Twist.degreeZeroSection G p V := by
  subst V
  rfl

/-- The base-ring map induced by the structure morphism `Proj G ⟶ Spec (G 0)` is
the pointwise degree-zero-section map used by the intrinsic twist construction. -/
theorem baseRingHom_toSpecZero
    {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (G : ℕ → σ) [GradedRing G] :
    (Scheme.ΓSpecIso (.of (G 0))).inv ≫ (Proj.toSpecZero G).appTop =
      CommRingCat.ofHom
        (ProjectiveSpectrum.Twist.degreeZeroToSectionsRingHom G ⊤) := by
  ext p
  unfold Proj.toSpecZero
  simp only [Scheme.Hom.comp_appTop, Proj.basicOpenToSpec_app_top]
  simp only [Category.assoc]
  rw [Scheme.ΓSpecIso_naturality_assoc]
  rw [Iso.inv_hom_id_assoc]
  change ((Proj.basicOpen G 1).topIso.inv ≫
      ((Proj G).isoOfEq (Proj.basicOpen_one G)).inv.appTop ≫
        (Proj G).topIso.inv.appTop)
      (Proj.awayToSection G 1
        (HomogeneousLocalization.fromZeroRingHom G (Submonoid.powers 1) p)) =
    ProjectiveSpectrum.Twist.degreeZeroSection G p ⊤
  rw [awayToSection_fromZeroRingHom]
  exact (transportSectionToTop (Proj G) (Proj.basicOpen G 1)
    (Proj.basicOpen_one G) _).trans
      (degreeZeroSection_cast G p (Proj.basicOpen_one G))

/-- The coefficient action used in the polynomial global-sections computation is the
intrinsic action coming from the structure morphism of polynomial projective space. -/
theorem projectiveSpaceScalarRingHom_eq_baseRingHom
    (n : ℕ) (R : Type u) [CommRing R] :
    MvPolynomial.projectiveSpaceScalarRingHom n R =
      (Scheme.Modules.baseRingHom
        (Proj.polynomialToSpec (Fin (n + 1)) R)).hom := by
  ext r
  let G := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
  change ProjectiveSpectrum.Twist.degreeZeroSection G
      (MvPolynomial.coefficientToDegreeZeroRingHom n R r) ⊤ =
    (((Scheme.ΓSpecIso (.of R)).inv ≫
      (Spec.map
        (MvPolynomial.degreeZeroRingEquiv (Fin (n + 1)) R).toCommRingCatIso.hom).appTop ≫
      (Proj.toSpecZero G).appTop).hom r)
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc
    (MvPolynomial.degreeZeroRingEquiv (Fin (n + 1)) R).toCommRingCatIso.hom]
  rw [baseRingHom_toSpecZero]
  rfl

end AlgebraicGeometry.ProjectiveSpace

end
