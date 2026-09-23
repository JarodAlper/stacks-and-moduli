module

public import StacksAndModuli.API.ProjectiveFlatteningFiniteDegree
public import StacksAndModuli.API.ProjectiveGradedCechAugmentationMultiplication
public import StacksAndModuli.API.ProjectiveSpaceTwistProjComparison
public import StacksAndModuli.API.PointSupportCohomology
public import StacksAndModuli.API.TwistedFreeMonomialSpan

/-!
# Degree-one multiplication on relative projective space and polynomial `Proj`

This file compares the concrete degree-one multiplication map used by projective
flattening with multiplication by the standard variables on `Proj.gammaStar`.
The comparison is built from the direct pullback-composition iso, so its action on
global sections is transparent enough for elementwise surjectivity arguments.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- Right-factor naturality of the pullback--tensor comparison along an open
immersion. -/
theorem pullbackTensorIsoOfIsOpenImmersion_naturality_right
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (F : Y.Modules) {G G' : Y.Modules} (ψ : G ⟶ G') :
    (pullback f).map (tensorMapRight F ψ) ≫
        (pullbackTensorIsoOfIsOpenImmersion f F G').hom =
      (pullbackTensorIsoOfIsOpenImmersion f F G).hom ≫
        tensorMapRight ((pullback f).obj F) ((pullback f).map ψ) := by
  dsimp only [pullbackTensorIsoOfIsOpenImmersion, Iso.trans_hom,
    Iso.app_hom, Iso.symm_hom, tensorLeftIso, tensorRightIso]
  have h1 : (pullback f).map (tensorMapRight F ψ) ≫
      (restrictFunctorIsoPullback f).inv.app (tensor F G') =
    (restrictFunctorIsoPullback f).inv.app (tensor F G) ≫
      (restrictFunctor f).map (tensorMapRight F ψ) :=
    (restrictFunctorIsoPullback f).inv.naturality (tensorMapRight F ψ)
  slice_lhs 1 2 => rw [h1]
  have hr := restrictTensorIso_naturality f (𝟙 F) ψ
  simp only [(restrictFunctor f).map_id, tensorMapLeft_id,
    Category.id_comp] at hr
  slice_lhs 2 3 => rw [hr]
  slice_lhs 3 4 => rw [tensorMap_exchange]
  have h2 : tensorMapRight ((pullback f).obj F)
        ((restrictFunctor f).map ψ) ≫
      tensorMapRight ((pullback f).obj F)
        ((restrictFunctorIsoPullback f).hom.app G') =
    tensorMapRight ((pullback f).obj F)
        ((restrictFunctorIsoPullback f).hom.app G) ≫
      tensorMapRight ((pullback f).obj F) ((pullback f).map ψ) := by
    rw [← tensorMapRight_comp, ← tensorMapRight_comp,
      (restrictFunctorIsoPullback f).hom.naturality ψ]
  slice_lhs 4 5 => rw [h2]
  simp only [Category.assoc]

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ} {R : Type u} [CommRing R]

/-- Naturality of the canonical identification between an iterated pullback and a
pullback along an equal composite. -/
theorem pullbackCompCongr_naturality
    {W X Y : Scheme.{u}} (f : W ⟶ X) (ρ : X ⟶ Y) (g : W ⟶ Y)
    (h : f ≫ ρ = g) {M N : Y.Modules} (m : M ⟶ N) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback ρ).map m) ≫
        ((Scheme.Modules.pullbackComp f ρ).hom.app N ≫
          (Scheme.Modules.pullbackCongr h).hom.app N) =
      ((Scheme.Modules.pullbackComp f ρ).hom.app M ≫
          (Scheme.Modules.pullbackCongr h).hom.app M) ≫
        (Scheme.Modules.pullback g).map m := by
  let cM := (Scheme.Modules.pullbackComp f ρ).hom.app M
  let cN := (Scheme.Modules.pullbackComp f ρ).hom.app N
  let kM := (Scheme.Modules.pullbackCongr h).hom.app M
  let kN := (Scheme.Modules.pullbackCongr h).hom.app N
  have hc :
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback ρ).map m) ≫ cN =
        cM ≫ (Scheme.Modules.pullback (f ≫ ρ)).map m :=
    (Scheme.Modules.pullbackComp f ρ).hom.naturality m
  have hk :
      (Scheme.Modules.pullback (f ≫ ρ)).map m ≫ kN =
        kM ≫ (Scheme.Modules.pullback g).map m :=
    (Scheme.Modules.pullbackCongr h).hom.naturality m
  calc
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback ρ).map m) ≫
          (cN ≫ kN) =
        ((Scheme.Modules.pullback f).map
          ((Scheme.Modules.pullback ρ).map m) ≫ cN) ≫ kN :=
      (Category.assoc _ _ _).symm
    _ = (cM ≫ (Scheme.Modules.pullback (f ≫ ρ)).map m) ≫ kN :=
      congrArg (fun q ↦ q ≫ kN) hc
    _ = cM ≫ ((Scheme.Modules.pullback (f ≫ ρ)).map m ≫ kN) :=
      Category.assoc _ _ _
    _ = cM ≫ (kM ≫ (Scheme.Modules.pullback g).map m) :=
      congrArg (fun q ↦ cM ≫ q) hk
    _ = (cM ≫ kM) ≫ (Scheme.Modules.pullback g).map m :=
      (Category.assoc _ _ _).symm

/-- The direct comparison between the pullback of a relative twist and the
intrinsic polynomial-`Proj` twist. -/
noncomputable def projectiveSpaceOverTwistGammaStarIso (n : ℕ)
    (R : Type u) [CommRing R] (d : ℤ) :
    (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj
        (Scheme.projectiveSpaceOverTwist n (Spec (.of R)) d) ≅
      ProjectiveSpectrum.Twist.twist
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d :=
  Proj.polynomialProjOverSpec_pullbackAbsoluteTwistIso (Fin (n + 1)) R d ≪≫
    ProjectiveSpectrum.Twist.polynomialPullbackIso (Fin (n + 1))
      (Proj.uliftIntCastRingHom R) d

/-- The direct twist comparison intertwines a relative monomial multiplication
with multiplication by the coefficient-changed homogeneous form. -/
theorem projectiveSpaceOverTwistGammaStarIso_naturality
    (a b : ℤ) (e : ℕ) (hb : b = a + (e : ℤ))
    (i : Fin ((n + e).choose n)) :
    (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).map
          (Scheme.twistMonomialMulHom n (Spec (.of R)) a b e hb i) ≫
        (projectiveSpaceOverTwistGammaStarIso n R b).hom =
      (projectiveSpaceOverTwistGammaStarIso n R a).hom ≫
        ProjectiveSpectrum.Twist.mulHom
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
          (MvPolynomial.homogeneousSubmoduleFinBasis n R e i) a b hb := by
  let 𝒜ℤ := MvPolynomial.homogeneousSubmodule
    (Fin (n + 1)) (ULift.{u} ℤ)
  let 𝒜R := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
  let f := (projectiveSpaceOverSpecIso n R).inv
  let ρ : Scheme.projectiveSpaceOver n (Spec (.of R)) ⟶ Proj 𝒜ℤ := by
    change Scheme.projectiveSpaceOver n (Spec (.of R)) ⟶ Scheme.projectiveSpace n
    exact Limits.pullback.snd
      (specULiftZIsTerminal.from (Spec (.of R)))
      (specULiftZIsTerminal.from (Scheme.projectiveSpace n))
  let g := Proj.polynomialMap (Fin (n + 1)) (Proj.uliftIntCastRingHom R)
  let p := MvPolynomial.homogeneousSubmoduleFinBasis n (ULift.{u} ℤ) e i
  let m := ProjectiveSpectrum.Twist.mulHom 𝒜ℤ p a b hb
  have habs :
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback ρ).map m) ≫
          (Proj.polynomialProjOverSpec_pullbackAbsoluteTwistIso
            (Fin (n + 1)) R b).hom =
          (Proj.polynomialProjOverSpec_pullbackAbsoluteTwistIso
            (Fin (n + 1)) R a).hom ≫
          (Scheme.Modules.pullback g).map m := by
    exact pullbackCompCongr_naturality f ρ g
      (Proj.polynomialProjOverSpecIso_inv_absoluteProjection
        (Fin (n + 1)) R) m
  have hpoly :=
    ProjectiveSpectrum.Twist.pullback_map_mulHom_comp_pullbackComparison
      (MvPolynomial.mapGradedRingHom (ι := Fin (n + 1))
        (Proj.uliftIntCastRingHom R))
      (MvPolynomial.irrelevant_le_map_mapGradedRingHom
        (Proj.uliftIntCastRingHom R)) p a b hb
  rw [MvPolynomial.gradedImage_homogeneousSubmoduleFinBasis] at hpoly
  have hpoly' :
      (Scheme.Modules.pullback g).map m ≫
          (ProjectiveSpectrum.Twist.polynomialPullbackIso
            (Fin (n + 1)) (Proj.uliftIntCastRingHom R) b).hom =
        (ProjectiveSpectrum.Twist.polynomialPullbackIso
            (Fin (n + 1)) (Proj.uliftIntCastRingHom R) a).hom ≫
          ProjectiveSpectrum.Twist.mulHom 𝒜R
            (MvPolynomial.homogeneousSubmoduleFinBasis n R e i) a b hb := by
    exact hpoly
  have hfinal :
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback ρ).map m) ≫
          ((Proj.polynomialProjOverSpec_pullbackAbsoluteTwistIso
              (Fin (n + 1)) R b).hom ≫
            (ProjectiveSpectrum.Twist.polynomialPullbackIso
              (Fin (n + 1)) (Proj.uliftIntCastRingHom R) b).hom) =
        ((Proj.polynomialProjOverSpec_pullbackAbsoluteTwistIso
              (Fin (n + 1)) R a).hom ≫
            (ProjectiveSpectrum.Twist.polynomialPullbackIso
              (Fin (n + 1)) (Proj.uliftIntCastRingHom R) a).hom) ≫
          ProjectiveSpectrum.Twist.mulHom 𝒜R
            (MvPolynomial.homogeneousSubmoduleFinBasis n R e i) a b hb := by
    calc
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback ρ).map m) ≫
            ((Proj.polynomialProjOverSpec_pullbackAbsoluteTwistIso
                (Fin (n + 1)) R b).hom ≫
              (ProjectiveSpectrum.Twist.polynomialPullbackIso
                (Fin (n + 1)) (Proj.uliftIntCastRingHom R) b).hom) =
          ((Scheme.Modules.pullback f).map
              ((Scheme.Modules.pullback ρ).map m) ≫
            (Proj.polynomialProjOverSpec_pullbackAbsoluteTwistIso
              (Fin (n + 1)) R b).hom) ≫
              (ProjectiveSpectrum.Twist.polynomialPullbackIso
                (Fin (n + 1)) (Proj.uliftIntCastRingHom R) b).hom :=
        (Category.assoc _ _ _).symm
      _ = ((Proj.polynomialProjOverSpec_pullbackAbsoluteTwistIso
              (Fin (n + 1)) R a).hom ≫
            (Scheme.Modules.pullback g).map m) ≫
              (ProjectiveSpectrum.Twist.polynomialPullbackIso
                (Fin (n + 1)) (Proj.uliftIntCastRingHom R) b).hom :=
        congrArg (fun q ↦ q ≫
          (ProjectiveSpectrum.Twist.polynomialPullbackIso
            (Fin (n + 1)) (Proj.uliftIntCastRingHom R) b).hom) habs
      _ = (Proj.polynomialProjOverSpec_pullbackAbsoluteTwistIso
              (Fin (n + 1)) R a).hom ≫
            ((Scheme.Modules.pullback g).map m ≫
              (ProjectiveSpectrum.Twist.polynomialPullbackIso
                (Fin (n + 1)) (Proj.uliftIntCastRingHom R) b).hom) :=
        Category.assoc _ _ _
      _ = (Proj.polynomialProjOverSpec_pullbackAbsoluteTwistIso
              (Fin (n + 1)) R a).hom ≫
            ((ProjectiveSpectrum.Twist.polynomialPullbackIso
                (Fin (n + 1)) (Proj.uliftIntCastRingHom R) a).hom ≫
              ProjectiveSpectrum.Twist.mulHom 𝒜R
                (MvPolynomial.homogeneousSubmoduleFinBasis n R e i) a b hb) :=
        congrArg (fun q ↦
          (Proj.polynomialProjOverSpec_pullbackAbsoluteTwistIso
            (Fin (n + 1)) R a).hom ≫ q) hpoly'
      _ = ((Proj.polynomialProjOverSpec_pullbackAbsoluteTwistIso
              (Fin (n + 1)) R a).hom ≫
            (ProjectiveSpectrum.Twist.polynomialPullbackIso
              (Fin (n + 1)) (Proj.uliftIntCastRingHom R) a).hom) ≫
          ProjectiveSpectrum.Twist.mulHom 𝒜R
            (MvPolynomial.homogeneousSubmoduleFinBasis n R e i) a b hb :=
        (Category.assoc _ _ _).symm
  simpa only [f, ρ, g, m, p, 𝒜ℤ, 𝒜R, Scheme.projectiveSpace,
    Scheme.projectiveSpaceOverTwist, Scheme.twistMonomialMulHom,
    projectiveSpaceOverTwistGammaStarIso, Iso.trans_hom, id_eq] using hfinal

/-- The direct comparison for a twist of an arbitrary module sheaf. -/
noncomputable def projectiveSpaceOverTwistModuleGammaStarIso
    (Q : (Scheme.projectiveSpaceOver n (Spec (.of R))).Modules) (d : ℤ) :
    (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj
        (Scheme.projectiveSpaceOverTwistModule Q d) ≅
      ProjectiveSpectrum.Twist.twistModule
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q) d :=
  Scheme.Modules.pullbackTensorIsoOfIsOpenImmersion
      (projectiveSpaceOverSpecIso n R).inv Q
      (Scheme.projectiveSpaceOverTwist n (Spec (.of R)) d) ≪≫
    Scheme.Modules.tensorRightIso
      ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q)
      (projectiveSpaceOverTwistGammaStarIso n R d)

/-- Pulling back one summand of the concrete degree-one multiplication map and
then applying the direct module-twist comparison gives multiplication by the
corresponding degree-one monomial in `GammaStar`. -/
theorem projectiveSpaceOverTwistModuleGammaStarIso_naturality
    (Q : (Scheme.projectiveSpaceOver n (Spec (.of R))).Modules)
    (d : ℕ) (i : Fin ((n + 1).choose n)) :
    (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).map
          (Scheme.Modules.projectiveTwistMulOne n Q d i) ≫
        (projectiveSpaceOverTwistModuleGammaStarIso Q ((d + 1 : ℕ) : ℤ)).hom =
      (projectiveSpaceOverTwistModuleGammaStarIso Q (d : ℤ)).hom ≫
        ProjectiveSpectrum.Twist.twistModuleMulHom
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
          ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q)
          (MvPolynomial.homogeneousSubmoduleFinBasis n R 1 i)
          (d : ℤ) ((d + 1 : ℕ) : ℤ) (by omega) := by
  let f := (projectiveSpaceOverSpecIso n R).inv
  let F := (Scheme.Modules.pullback f).obj Q
  let Wd := Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (d : ℤ)
  let We := Scheme.projectiveSpaceOverTwist n (Spec (.of R)) ((d + 1 : ℕ) : ℤ)
  let m := Scheme.twistMonomialMulHom n (Spec (.of R))
    (d : ℤ) ((d + 1 : ℕ) : ℤ) 1 (by omega) i
  let p := MvPolynomial.homogeneousSubmoduleFinBasis n R 1 i
  have hpull :=
    Scheme.Modules.pullbackTensorIsoOfIsOpenImmersion_naturality_right f Q m
  have htw := projectiveSpaceOverTwistGammaStarIso_naturality
    (R := R) (n := n) (d : ℤ) ((d + 1 : ℕ) : ℤ) 1 (by omega) i
  change (Scheme.Modules.pullback f).map (Scheme.Modules.tensorMapRight Q m) ≫
      ((Scheme.Modules.pullbackTensorIsoOfIsOpenImmersion f Q We).hom ≫
        Scheme.Modules.tensorMapRight F
          (projectiveSpaceOverTwistGammaStarIso n R ((d + 1 : ℕ) : ℤ)).hom) =
    ((Scheme.Modules.pullbackTensorIsoOfIsOpenImmersion f Q Wd).hom ≫
      Scheme.Modules.tensorMapRight F
        (projectiveSpaceOverTwistGammaStarIso n R (d : ℤ)).hom) ≫
      Scheme.Modules.tensorMapRight F
        (ProjectiveSpectrum.Twist.mulHom
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) p
          (d : ℤ) ((d + 1 : ℕ) : ℤ) (by omega))
  calc
    (Scheme.Modules.pullback f).map (Scheme.Modules.tensorMapRight Q m) ≫
          ((Scheme.Modules.pullbackTensorIsoOfIsOpenImmersion f Q We).hom ≫
            Scheme.Modules.tensorMapRight F
              (projectiveSpaceOverTwistGammaStarIso n R
                ((d + 1 : ℕ) : ℤ)).hom) =
        ((Scheme.Modules.pullback f).map
            (Scheme.Modules.tensorMapRight Q m) ≫
          (Scheme.Modules.pullbackTensorIsoOfIsOpenImmersion f Q We).hom) ≫
            Scheme.Modules.tensorMapRight F
              (projectiveSpaceOverTwistGammaStarIso n R
                ((d + 1 : ℕ) : ℤ)).hom :=
      (Category.assoc _ _ _).symm
    _ = ((Scheme.Modules.pullbackTensorIsoOfIsOpenImmersion f Q Wd).hom ≫
          Scheme.Modules.tensorMapRight F
            ((Scheme.Modules.pullback f).map m)) ≫
        Scheme.Modules.tensorMapRight F
          (projectiveSpaceOverTwistGammaStarIso n R
            ((d + 1 : ℕ) : ℤ)).hom :=
      congrArg (fun q ↦ q ≫ Scheme.Modules.tensorMapRight F
        (projectiveSpaceOverTwistGammaStarIso n R
          ((d + 1 : ℕ) : ℤ)).hom) hpull
    _ = (Scheme.Modules.pullbackTensorIsoOfIsOpenImmersion f Q Wd).hom ≫
        (Scheme.Modules.tensorMapRight F ((Scheme.Modules.pullback f).map m) ≫
          Scheme.Modules.tensorMapRight F
            (projectiveSpaceOverTwistGammaStarIso n R
              ((d + 1 : ℕ) : ℤ)).hom) :=
      Category.assoc _ _ _
    _ = (Scheme.Modules.pullbackTensorIsoOfIsOpenImmersion f Q Wd).hom ≫
        Scheme.Modules.tensorMapRight F
          ((Scheme.Modules.pullback f).map m ≫
            (projectiveSpaceOverTwistGammaStarIso n R
              ((d + 1 : ℕ) : ℤ)).hom) := by
      rw [Scheme.Modules.tensorMapRight_comp]
    _ = (Scheme.Modules.pullbackTensorIsoOfIsOpenImmersion f Q Wd).hom ≫
        Scheme.Modules.tensorMapRight F
          ((projectiveSpaceOverTwistGammaStarIso n R (d : ℤ)).hom ≫
            ProjectiveSpectrum.Twist.mulHom
              (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) p
              (d : ℤ) ((d + 1 : ℕ) : ℤ) (by omega)) :=
      congrArg (fun q ↦
        (Scheme.Modules.pullbackTensorIsoOfIsOpenImmersion f Q Wd).hom ≫
          Scheme.Modules.tensorMapRight F q) htw
    _ = (Scheme.Modules.pullbackTensorIsoOfIsOpenImmersion f Q Wd).hom ≫
        (Scheme.Modules.tensorMapRight F
            (projectiveSpaceOverTwistGammaStarIso n R (d : ℤ)).hom ≫
          Scheme.Modules.tensorMapRight F
            (ProjectiveSpectrum.Twist.mulHom
              (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) p
              (d : ℤ) ((d + 1 : ℕ) : ℤ) (by omega))) := by
      rw [← Scheme.Modules.tensorMapRight_comp]
    _ = ((Scheme.Modules.pullbackTensorIsoOfIsOpenImmersion f Q Wd).hom ≫
          Scheme.Modules.tensorMapRight F
            (projectiveSpaceOverTwistGammaStarIso n R (d : ℤ)).hom) ≫
        Scheme.Modules.tensorMapRight F
          (ProjectiveSpectrum.Twist.mulHom
            (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) p
            (d : ℤ) ((d + 1 : ℕ) : ℤ) (by omega)) :=
      (Category.assoc _ _ _).symm

/-- The additive equivalence from concrete relative twisted global sections to the
corresponding degree of `GammaStar`, using the direct twist comparison. -/
noncomputable def projectiveSpaceTwistedGammaStarAddEquiv
    (Q : (Scheme.projectiveSpaceOver n (Spec (.of R))).Modules) (d : ℤ) :
    Γ(Scheme.projectiveSpaceOverTwistModule Q d, ⊤) ≃+
      (Proj.gammaStar
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (projSpecπ n R)
        ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q)
        (stdVars n R)).obj d :=
  Scheme.Modules.pullbackGlobalSectionsViaIsoAddEquiv
    (projectiveSpaceOverSpecIso n R).inv
    (Scheme.projectiveSpaceOverTwistModule Q d)
    (projectiveSpaceOverTwistModuleGammaStarIso Q d)

/-- The direct global-sections equivalence sends one concrete monomial summand to
multiplication by the corresponding homogeneous basis element on `GammaStar`. -/
theorem projectiveSpaceTwistedGammaStarAddEquiv_mulOne
    (Q : (Scheme.projectiveSpaceOver n (Spec (.of R))).Modules)
    (d : ℕ) (i : Fin ((n + 1).choose n))
    (s : Γ(Scheme.projectiveSpaceOverTwistModule Q (d : ℤ), ⊤)) :
    projectiveSpaceTwistedGammaStarAddEquiv Q ((d + 1 : ℕ) : ℤ)
        (Scheme.Modules.Hom.app
          (Scheme.Modules.projectiveTwistMulOne n Q d i) ⊤ s) =
      Scheme.Modules.Hom.app
        (ProjectiveSpectrum.Twist.twistModuleMulHom
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
          ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q)
          (MvPolynomial.homogeneousSubmoduleFinBasis n R 1 i)
          (d : ℤ) ((d + 1 : ℕ) : ℤ) (by omega)) ⊤
        (projectiveSpaceTwistedGammaStarAddEquiv Q (d : ℤ) s) := by
  let f := (projectiveSpaceOverSpecIso n R).inv
  let Qd := Scheme.projectiveSpaceOverTwistModule Q (d : ℤ)
  let Qe := Scheme.projectiveSpaceOverTwistModule Q ((d + 1 : ℕ) : ℤ)
  let m := Scheme.Modules.projectiveTwistMulOne n Q d i
  let ed := projectiveSpaceOverTwistModuleGammaStarIso Q (d : ℤ)
  let ee := projectiveSpaceOverTwistModuleGammaStarIso Q ((d + 1 : ℕ) : ℤ)
  let p := MvPolynomial.homogeneousSubmoduleFinBasis n R 1 i
  let μ := ProjectiveSpectrum.Twist.twistModuleMulHom
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    ((Scheme.Modules.pullback f).obj Q) p
    (d : ℤ) ((d + 1 : ℕ) : ℤ) (by omega)
  have hpull := Scheme.Modules.pullbackGlobalSections_naturality f m s
  have hnat := projectiveSpaceOverTwistModuleGammaStarIso_naturality Q d i
  have happ := congrArg
    (fun q ↦ Scheme.Modules.Hom.app q ⊤
      (Scheme.Modules.pullbackGlobalSections f Qd s)) hnat
  change Scheme.Modules.Hom.app ee.hom ⊤
      (Scheme.Modules.pullbackGlobalSections f Qe
        (Scheme.Modules.Hom.app m ⊤ s)) =
    Scheme.Modules.Hom.app μ ⊤
      (Scheme.Modules.Hom.app ed.hom ⊤
        (Scheme.Modules.pullbackGlobalSections f Qd s))
  rw [← hpull]
  exact happ

/-- The monomial-basis index of the degree-one monomial `X i`. -/
noncomputable def degreeOneMonomialIndex (n : ℕ) (i : Fin (n + 1)) :
    Fin ((n + 1).choose n) :=
  MvPolynomial.degreeMonomialEquivFin n 1
    ⟨Finsupp.single i 1, by simp⟩

/-- At the preceding index, the noncomputably enumerated monomial basis is the
specified standard variable. -/
theorem homogeneousSubmoduleFinBasis_degreeOneMonomialIndex
    (n : ℕ) (R : Type u) [CommRing R] (i : Fin (n + 1)) :
    MvPolynomial.homogeneousSubmoduleFinBasis n R 1
        (degreeOneMonomialIndex n i) =
      stdVars n R i := by
  apply (MvPolynomial.homogeneousSubmoduleFinFinsuppEquiv n R 1).injective
  have hL : MvPolynomial.homogeneousSubmoduleFinFinsuppEquiv n R 1
      (MvPolynomial.homogeneousSubmoduleFinBasis n R 1
        (degreeOneMonomialIndex n i)) =
      Finsupp.single (degreeOneMonomialIndex n i) 1 :=
    (MvPolynomial.homogeneousSubmoduleFinBasis n R 1).repr_self _
  rw [hL]
  ext j
  rw [MvPolynomial.homogeneousSubmoduleFinFinsuppEquiv_apply']
  simp only [degreeOneMonomialIndex, stdVars_coe, MvPolynomial.coeff_X]
  rcases eq_or_ne j (degreeOneMonomialIndex n i) with rfl | hji
  · simp [degreeOneMonomialIndex]
  · have hne : (MvPolynomial.degreeMonomialEquivFin n 1).symm j ≠
        ⟨Finsupp.single i 1, by simp⟩ := by
      intro h
      apply hji
      calc
        j = MvPolynomial.degreeMonomialEquivFin n 1
            ((MvPolynomial.degreeMonomialEquivFin n 1).symm j) :=
          ((MvPolynomial.degreeMonomialEquivFin n 1).apply_symm_apply j).symm
        _ = MvPolynomial.degreeMonomialEquivFin n 1
            ⟨Finsupp.single i 1, by simp⟩ := congrArg _ h
        _ = degreeOneMonomialIndex n i := rfl
    rw [Finsupp.single_eq_of_ne (by
      simpa [degreeOneMonomialIndex] using hji)]
    have hne_val : Finsupp.single i 1 ≠
        ((MvPolynomial.degreeMonomialEquivFin n 1).symm j).1 := by
      intro h
      apply hne
      exact Subtype.ext h.symm
    simp only [hne_val, ↓reduceIte]

/-- If degree `d+1` of `GammaStar` is generated from degree `d` by the standard
variables, then the concrete pushed-forward degree-one multiplication map is
surjective on the top affine open. -/
theorem surjective_app_top_projectiveTwistedPushforwardMul_of_gammaStar_mulSpan
    (Q : (Scheme.projectiveSpaceOver n (Spec (.of R))).Modules) (d : ℕ)
    (hspan :
      (Proj.gammaStar
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (projSpecπ n R)
        ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q)
        (stdVars n R)).mulSpan (d : ℤ) ((d + 1 : ℕ) : ℤ) = ⊤) :
    Function.Surjective (Scheme.Modules.Hom.app
      (Scheme.Modules.projectiveTwistedPushforwardMul n Q d) ⊤) := by
  let π := Scheme.projectiveSpaceOverπ n (Spec (.of R))
  let Qd := Scheme.projectiveSpaceOverTwistModule Q (d : ℤ)
  let Qe := Scheme.projectiveSpaceOverTwistModule Q ((d + 1 : ℕ) : ℤ)
  let F := (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q
  let M := Proj.gammaStar
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    (projSpecπ n R) F (stdVars n R)
  let Ed := projectiveSpaceTwistedGammaStarAddEquiv Q (d : ℤ)
  let Ee := projectiveSpaceTwistedGammaStarAddEquiv Q ((d + 1 : ℕ) : ℤ)
  let Pd : Γ(Scheme.Modules.projectiveTwistedPushforward n Q d, ⊤) ≃+ Γ(Qd, ⊤) :=
    Scheme.Modules.pushforwardGlobalSectionsAddEquiv
      (Scheme.projectiveSpaceOverπ n (Spec (.of R)))
      (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))
  let Pe : Γ(Scheme.Modules.projectiveTwistedPushforward n Q (d + 1), ⊤) ≃+ Γ(Qe, ⊤) :=
    Scheme.Modules.pushforwardGlobalSectionsAddEquiv
      (Scheme.projectiveSpaceOverπ n (Spec (.of R)))
      (Scheme.projectiveSpaceOverTwistModule Q ((d + 1 : ℕ) : ℤ))
  let S := ∐ (fun _ : Fin ((n + 1).choose n) ↦
    Scheme.Modules.projectiveTwistedPushforward n Q d)
  let μ := Scheme.Modules.projectiveTwistedPushforwardMul n Q d
  intro y
  let y' : Γ(Qe, ⊤) := Pe y
  have hy : Ee y' ∈ M.mulSpan (d : ℤ) ((d + 1 : ℕ) : ℤ) :=
    hspan.symm ▸ Submodule.mem_top
  have hpre : ∃ w : Γ(S, ⊤),
      Ee (Pe (Scheme.Modules.Hom.app μ ⊤ w)) = Ee y' := by
    refine Submodule.iSup_induction
      (fun l : {l : List (Fin (n + 1)) //
          (d : ℤ) + (l.length : ℤ) = ((d + 1 : ℕ) : ℤ)} ↦
        LinearMap.range (M.mulList l.1 (d : ℤ)
          ((d + 1 : ℕ) : ℤ) l.2).hom)
      (motive := fun z ↦ ∃ w : Γ(S, ⊤),
        Ee (Pe (Scheme.Modules.Hom.app μ ⊤ w)) = z)
      hy ?_ ?_ ?_
    · rintro ⟨l, hl⟩ _ ⟨x, rfl⟩
      have hlen : l.length = 1 := by omega
      obtain ⟨j, rfl⟩ := List.length_eq_one_iff.mp hlen
      let k := degreeOneMonomialIndex n j
      let s := Ed.symm x
      let s' : Γ(Scheme.Modules.projectiveTwistedPushforward n Q d, ⊤) := Pd.symm s
      let w := Scheme.Modules.Hom.app
        (Limits.Sigma.ι (fun _ : Fin ((n + 1).choose n) ↦
          Scheme.Modules.projectiveTwistedPushforward n Q d) k) ⊤ s'
      refine ⟨w, ?_⟩
      have hμ : Limits.Sigma.ι
          (fun _ : Fin ((n + 1).choose n) ↦
            Scheme.Modules.projectiveTwistedPushforward n Q d) k ≫ μ =
        (Scheme.Modules.pushforward π).map
          (Scheme.Modules.projectiveTwistMulOne n Q d k) := by
        exact Limits.Sigma.ι_desc _ _
      have hmul := projectiveSpaceTwistedGammaStarAddEquiv_mulOne Q d k s
      rw [homogeneousSubmoduleFinBasis_degreeOneMonomialIndex] at hmul
      have hmulX :
          Scheme.Modules.Hom.app
              (ProjectiveSpectrum.Twist.twistModuleMulHom
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) F
                (stdVars n R j) (d : ℤ) ((d + 1 : ℕ) : ℤ) (by omega)) ⊤
              (Ed s) =
            (M.mulX j (d : ℤ)).hom (Ed s) := rfl
      change Ee (Pe (Scheme.Modules.Hom.app μ ⊤
          (Scheme.Modules.Hom.app (Limits.Sigma.ι
            (fun _ : Fin ((n + 1).choose n) ↦
              Scheme.Modules.projectiveTwistedPushforward n Q d) k) ⊤ s'))) =
        (M.mulList [j] (d : ℤ) ((d + 1 : ℕ) : ℤ) (by omega)).hom x
      have happcomp : Scheme.Modules.Hom.app μ ⊤
          (Scheme.Modules.Hom.app (Limits.Sigma.ι
            (fun _ : Fin ((n + 1).choose n) ↦
              Scheme.Modules.projectiveTwistedPushforward n Q d) k) ⊤ s') =
        Scheme.Modules.Hom.app
          (Limits.Sigma.ι
            (fun _ : Fin ((n + 1).choose n) ↦
              Scheme.Modules.projectiveTwistedPushforward n Q d) k ≫ μ) ⊤ s' := rfl
      rw [happcomp, hμ]
      have hpush : Pe (Scheme.Modules.Hom.app
          ((Scheme.Modules.pushforward π).map
            (Scheme.Modules.projectiveTwistMulOne n Q d k)) ⊤ s') =
        Scheme.Modules.Hom.app
          (Scheme.Modules.projectiveTwistMulOne n Q d k) ⊤ (Pd s') := rfl
      apply Eq.trans (congrArg Ee hpush)
      calc
        Ee (Scheme.Modules.Hom.app
            (Scheme.Modules.projectiveTwistMulOne n Q d k) ⊤ (Pd s')) =
            Ee (Scheme.Modules.Hom.app
              (Scheme.Modules.projectiveTwistMulOne n Q d k) ⊤ s) := by
          exact congrArg
            (fun z ↦ Ee (Scheme.Modules.Hom.app
              (Scheme.Modules.projectiveTwistMulOne n Q d k) ⊤ z))
            (Pd.apply_symm_apply s)
        _ = (M.mulX j (d : ℤ)).hom x := by
          rw [hmul, hmulX, Ed.apply_symm_apply]
        _ = (M.mulList [j] (d : ℤ) ((d + 1 : ℕ) : ℤ) (by omega)).hom x := by
          simp only [ProjectiveSpace.GradedModule.mulList_singleton,
            ProjectiveSpace.GradedModule.mulX', eqToHom_refl, Category.comp_id]
          rfl
    · refine ⟨0, ?_⟩
      simp
    · rintro z₁ z₂ ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩
      refine ⟨w₁ + w₂, ?_⟩
      rw [map_add, map_add, map_add, hw₁, hw₂]
  obtain ⟨w, hw⟩ := hpre
  refine ⟨w, ?_⟩
  exact Pe.injective (Ee.injective hw)

end AlgebraicGeometry.ProjectiveSpace

end

end
