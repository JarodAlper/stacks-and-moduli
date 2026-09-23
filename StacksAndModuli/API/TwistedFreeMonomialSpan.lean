module

public import StacksAndModuli.API.ProjectiveTwistBaseChangeMul
public import StacksAndModuli.API.ProjectiveTwistGlobalSections
public import StacksAndModuli.API.KernelIdealPullback
public import StacksAndModuli.API.CanonicalAffineGlobalSectionsBaseChange
public import StacksAndModuli.API.ProjectiveTwistedFreeGlobalSectionsFinite
public import StacksAndModuli.API.TwistMonomialSections
public import StacksAndModuli.API.QuotGrassmannianSurjectivity
public import StacksAndModuli.API.TwistedFreeGlobalSectionsHomogeneous

/-!
# Coefficient change carries homogeneous sections to homogeneous sections

For a graded ring homomorphism `f : 𝒜 →+*ᵍ ℬ`, the comparison
`ProjectiveSpectrum.Twist.twistToPushforwardComparison` applies `f` to the numerator and
denominator of a local fraction.  A homogeneous element `p` of degree `d` defines the
global section `p/1` of `𝒪(d)`; its image is therefore `f(p)/1` — the homogeneous section
of `gradedImage f p`.  This file records that computation and its adjoint form for the
pullback unit, the elementwise input for identifying the pulled-back monomial basis of a
twist with the intrinsic monomial basis over the new coefficient ring.

Main declarations:

* `ProjectiveSpectrum.Twist.twistToPushforwardComparison_app_homogeneousSection`;
* `ProjectiveSpectrum.Twist.pullbackComparison_app_pullbackGlobalSections_homogeneousSection`;
* `AlgebraicGeometry.ProjectiveSpace.
  projectiveSpaceOverTwistGlobalSectionsBasis_eq_twistMonomialSection`;
* `AlgebraicGeometry.ProjectiveSpace.
  twistedFreeTwistGlobalSectionsHomogeneousEquiv_twistedFreeMonomialSection`;
* `AlgebraicGeometry.ProjectiveSpace.
  surjective_finFreeSectionsMap'_twistedFreeMonomial_top`.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory Graded HomogeneousIdeal HomogeneousLocalization
open TopologicalSpace Opposite TopCat
open ProjectiveSpectrum

universe u

namespace ProjectiveSpectrum.Twist

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- API lemma for the monomial-section base-change calculation: the coefficient-change
comparison carries `p/1` to `f(p)/1`. -/
theorem twistToPushforwardComparison_app_homogeneousSection
    (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f) {d : ℕ} (p : 𝒜 d) (U : (Proj 𝒜).Opens) :
    (twistToPushforwardComparison f hf (d : ℤ)).app U
        (homogeneousSection 𝒜 p U) =
      homogeneousSection ℬ (gradedImage f p) ((Proj.map f hf) ⁻¹ᵁ U) := by
  dsimp only [twistToPushforwardComparison, Scheme.Modules.Hom.app,
    Scheme.Modules.presheaf, PresheafOfModules.homMk]
  refine Subtype.ext (funext fun y ↦ Subtype.ext ?_)
  have hmap := comapTwistAddHom_apply_val f hf (d : ℤ) U ((Proj.map f hf) ⁻¹ᵁ U) (by rfl)
    (homogeneousSection 𝒜 p U) y
  refine hmap.trans ?_
  change Localization.localRingHom
      (ProjectiveSpectrum.comap f hf y.1).asHomogeneousIdeal.toIdeal
      y.1.asHomogeneousIdeal.toIdeal f rfl
        (Localization.mk (p : A) 1) =
    Localization.mk ((gradedImage f p : B)) 1
  rw [Localization.localRingHom_mk]
  congr 1
  exact Subtype.ext (map_one (f : A →+* B))

/-- API lemma giving the adjoint form of the monomial-section base-change calculation:
the pullback unit followed by the pullback comparison carries the homogeneous section
`p/1` to `f(p)/1`. -/
theorem pullbackComparison_app_pullbackGlobalSections_homogeneousSection
    (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f) {d : ℕ} (p : 𝒜 d) (U : (Proj 𝒜).Opens) :
    (pullbackComparison f hf (d : ℤ)).app ((Proj.map f hf) ⁻¹ᵁ U)
        ((((Scheme.Modules.pullbackPushforwardAdjunction (Proj.map f hf)).unit.app
          (twist 𝒜 (d : ℤ))).app U (homogeneousSection 𝒜 p U))) =
      homogeneousSection ℬ (gradedImage f p) ((Proj.map f hf) ⁻¹ᵁ U) := by
  have htr :
      (Scheme.Modules.pullbackPushforwardAdjunction (Proj.map f hf)).homEquiv
        (twist 𝒜 (d : ℤ)) (twist ℬ (d : ℤ)) (pullbackComparison f hf (d : ℤ)) =
          twistToPushforwardComparison f hf (d : ℤ) := by
    rw [pullbackComparison, Equiv.apply_symm_apply]
  rw [(Scheme.Modules.pullbackPushforwardAdjunction
    (Proj.map f hf)).homEquiv_unit] at htr
  have happ := CategoryTheory.congr_fun
    (congrArg (fun (k : twist 𝒜 (d : ℤ) ⟶
        (Scheme.Modules.pushforward (Proj.map f hf)).obj (twist ℬ (d : ℤ))) ↦ k.app U) htr)
    (homogeneousSection 𝒜 p U)
  exact happ.trans (twistToPushforwardComparison_app_homogeneousSection f hf p U)

end ProjectiveSpectrum.Twist

namespace MvPolynomial

open ProjectiveSpectrum.Twist

/-- Helper lemma computing the finite monomial enumeration of forms as a coefficient. -/
theorem homogeneousSubmoduleFinFinsuppEquiv_apply' (n : ℕ) (R : Type u) [CommRing R]
    (e : ℕ) (p : homogeneousSubmodule (Fin (n + 1)) R e) (j : Fin ((n + e).choose n)) :
    homogeneousSubmoduleFinFinsuppEquiv n R e p j
      = coeff ((degreeMonomialEquivFin n e).symm j).1 p.1 := by
  rw [homogeneousSubmoduleFinFinsuppEquiv]
  change ((Finsupp.domLCongr (degreeMonomialEquivFin n e) :
      ({m : Fin (n + 1) →₀ ℕ // m.degree = e} →₀ R) ≃ₗ[R]
        (Fin ((n + e).choose n) →₀ R))
    ((homogeneousSubmoduleFinsuppEquiv (Fin (n + 1)) R e) p)) j = _
  rw [Finsupp.domLCongr_apply, Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply]
  exact homogeneousSubmoduleFinsuppEquiv_apply (Fin (n + 1)) R e p _

/-- API lemma for monomial base change: coefficient change carries the monomial basis of
forms to the monomial basis. The enumeration `degreeMonomialEquivFin` does not involve the
coefficient ring, so the `i`-th basis vector maps to the `i`-th basis vector. -/
theorem gradedImage_homogeneousSubmoduleFinBasis
    {R₁ R₂ : Type u} [CommRing R₁] [CommRing R₂] (g : R₁ →+* R₂) (n e : ℕ)
    (i : Fin ((n + e).choose n)) :
    gradedImage (MvPolynomial.mapGradedRingHom (ι := Fin (n + 1)) g)
        (homogeneousSubmoduleFinBasis n R₁ e i)
      = homogeneousSubmoduleFinBasis n R₂ e i := by
  apply (homogeneousSubmoduleFinFinsuppEquiv n R₂ e).injective
  have hR₂ : homogeneousSubmoduleFinFinsuppEquiv n R₂ e
      (homogeneousSubmoduleFinBasis n R₂ e i) = Finsupp.single i 1 :=
    (homogeneousSubmoduleFinBasis n R₂ e).repr_self i
  have hR₁ : homogeneousSubmoduleFinFinsuppEquiv n R₁ e
      (homogeneousSubmoduleFinBasis n R₁ e i) = Finsupp.single i 1 :=
    (homogeneousSubmoduleFinBasis n R₁ e).repr_self i
  rw [hR₂]
  ext j
  rw [homogeneousSubmoduleFinFinsuppEquiv_apply']
  have hcoe : ((gradedImage (MvPolynomial.mapGradedRingHom (ι := Fin (n + 1)) g)
      (homogeneousSubmoduleFinBasis n R₁ e i)) :
        MvPolynomial (Fin (n + 1)) R₂)
      = MvPolynomial.map g ((homogeneousSubmoduleFinBasis n R₁ e i) :
        MvPolynomial (Fin (n + 1)) R₁) :=
    gradedImage_coe _ _
  rw [hcoe, MvPolynomial.coeff_map]
  have h1 := homogeneousSubmoduleFinFinsuppEquiv_apply' n R₁ e
    (homogeneousSubmoduleFinBasis n R₁ e i) j
  rw [hR₁] at h1
  rw [← h1]
  rcases eq_or_ne j i with rfl | hji
  · simp
  · simp [hji]

end MvPolynomial

namespace AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry

/-- General pullback API used by the affine-open transport: for `p ≫ g = f`, pulling a
global section back along `g` and then `p` agrees, through the composition and congruence
comparisons, with pulling it back along `f`. -/
theorem pullbackGlobalSections_comp_congr {W X Y : Scheme.{u}}
    (p : W ⟶ X) (g : X ⟶ Y) (f : W ⟶ Y) (h : p ≫ g = f)
    (M : Y.Modules) (m : Γ(M, ⊤)) :
    Scheme.Modules.Hom.app ((Modules.pullbackCongr h).hom.app M) ⊤
      (Scheme.Modules.Hom.app ((Modules.pullbackComp p g).hom.app M) ⊤
        (Scheme.Modules.pullbackGlobalSections p ((Modules.pullback g).obj M)
          (Scheme.Modules.pullbackGlobalSections g M m)))
    = Scheme.Modules.pullbackGlobalSections f M m := by
  let phi := homOfGlobalSection M m
  have h1 := Hom.pullbackUnitMap_comp p g phi
  have h2 := Hom.pullbackUnitMap_congr h phi
  have hcomp : Hom.pullbackUnitMap p (Hom.pullbackUnitMap g phi) ≫
      ((Modules.pullbackComp p g).hom.app M ≫ (Modules.pullbackCongr h).hom.app M)
      = Hom.pullbackUnitMap f phi := by
    rw [← Category.assoc, h1, h2]
  have heval := congrArg
    (fun k : SheafOfModules.unit W.ringCatSheaf ⟶ (Modules.pullback f).obj M ↦
      Scheme.Modules.Hom.app k ⊤ (1 : Γ(W, ⊤))) hcomp
  have hL : Scheme.Modules.Hom.app
      (Hom.pullbackUnitMap p (Hom.pullbackUnitMap g phi) ≫
        ((Modules.pullbackComp p g).hom.app M ≫ (Modules.pullbackCongr h).hom.app M)) ⊤
        (1 : Γ(W, ⊤))
      = Scheme.Modules.Hom.app ((Modules.pullbackCongr h).hom.app M) ⊤
        (Scheme.Modules.Hom.app ((Modules.pullbackComp p g).hom.app M) ⊤
          (Scheme.Modules.Hom.app
            (Hom.pullbackUnitMap p (Hom.pullbackUnitMap g phi)) ⊤
            (1 : Γ(W, ⊤)))) := rfl
  rw [hL] at heval
  rw [pullbackUnitMap_app_top_one, pullbackUnitMap_app_top_one,
    homOfGlobalSection_app_top_one_general] at heval
  rw [pullbackUnitMap_app_top_one,
    homOfGlobalSection_app_top_one_general] at heval
  exact heval

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.ProjectiveSpace

open AlgebraicGeometry ProjectiveSpectrum.Twist CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- API identification for the Quot-to-Grassmannian construction in Proposition 2.4.1:
the pulled-back monomial sections are the intrinsic monomial basis. The `i`-th monomial
global section of
`𝒪(e)` on `ℙⁿ_{Spec R}` — the pullback of the `i`-th monomial section over `ℤ` —
corresponds, under the global-sections comparison with polynomial `Proj`, to the `i`-th
vector of the transported binomial basis. -/
theorem projectiveSpaceOverTwistGlobalSectionsLinearEquiv_twistMonomialSection
    (n : ℕ) (R : Type u) [CommRing R] (e : ℕ) (i : Fin ((n + e).choose n)) :
    projectiveSpaceOverTwistGlobalSectionsLinearEquiv n R e
        (Scheme.twistMonomialSection n (Spec (.of R)) e i)
      = MvPolynomial.projectiveTwistGlobalSectionsBasis n R e i := by
  set f := (projectiveSpaceOverSpecIso n R).inv with hf
  set tw := Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (e : ℤ) with htw
  letI := MvPolynomial.projectiveTwistGlobalSectionsModule n (ULift.{u} ℤ) e
  letI := MvPolynomial.projectiveTwistGlobalSectionsModule n R e
  set b : Γ(ProjectiveSpectrum.Twist.twist
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) (e : ℤ), ⊤) :=
    MvPolynomial.projectiveTwistGlobalSectionsBasis n (ULift.{u} ℤ) e i with hb
  -- the equivalence is the twist-pullback comparison after the pullback of sections
  have h0 : projectiveSpaceOverTwistGlobalSectionsLinearEquiv n R e
      (Scheme.twistMonomialSection n (Spec (.of R)) e i)
    = Scheme.Modules.Hom.app (projectiveSpaceOverTwistPullbackIso n R (e : ℤ)).hom ⊤
        (Scheme.Modules.pullbackGlobalSections f tw
          (Scheme.twistMonomialSection n (Spec (.of R)) e i)) := rfl
  rw [h0]
  -- decompose the twist-pullback comparison
  set ρ := Limits.pullback.snd (specULiftZIsTerminal.from (Spec (.of R)))
    (specULiftZIsTerminal.from (Scheme.projectiveSpace n)) with hρ
  have h1 : (projectiveSpaceOverTwistPullbackIso n R (e : ℤ)).hom
      = (Scheme.Modules.pullback f).map
          (Scheme.Modules.tensorLeftUnitIso tw).inv ≫
        ((Scheme.Modules.pullback f).map
          (Scheme.Modules.tensorLeftUnitIso
            ((Scheme.Modules.pullback ρ).obj
              (ProjectiveSpectrum.Twist.twist
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
                (e : ℤ)))).hom ≫
          (Proj.polynomialProjOverSpec_pullbackAbsoluteTwistIso (Fin (n + 1)) R
            (e : ℤ)).hom ≫
          (ProjectiveSpectrum.Twist.polynomialPullbackIso (Fin (n + 1))
            (Proj.uliftIntCastRingHom R) (e : ℤ)).hom) := rfl
  rw [h1]
  -- the unit-tensor pair cancels
  have hcancel : (Scheme.Modules.pullback f).map
        (Scheme.Modules.tensorLeftUnitIso
          ((Scheme.Modules.pullback ρ).obj
            (ProjectiveSpectrum.Twist.twist
              (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
              (e : ℤ)))).inv ≫
      (Scheme.Modules.pullback f).map
        (Scheme.Modules.tensorLeftUnitIso
          ((Scheme.Modules.pullback ρ).obj
            (ProjectiveSpectrum.Twist.twist
              (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
              (e : ℤ)))).hom = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  have h2 : Scheme.Modules.Hom.app ((Scheme.Modules.pullback f).map
        (Scheme.Modules.tensorLeftUnitIso tw).inv ≫
        ((Scheme.Modules.pullback f).map
          (Scheme.Modules.tensorLeftUnitIso
            ((Scheme.Modules.pullback ρ).obj
              (ProjectiveSpectrum.Twist.twist
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
                (e : ℤ)))).hom ≫
          (Proj.polynomialProjOverSpec_pullbackAbsoluteTwistIso (Fin (n + 1)) R
            (e : ℤ)).hom ≫
          (ProjectiveSpectrum.Twist.polynomialPullbackIso (Fin (n + 1))
            (Proj.uliftIntCastRingHom R) (e : ℤ)).hom)) ⊤
        (Scheme.Modules.pullbackGlobalSections f tw
          (Scheme.twistMonomialSection n (Spec (.of R)) e i))
      = Scheme.Modules.Hom.app
          ((Proj.polynomialProjOverSpec_pullbackAbsoluteTwistIso (Fin (n + 1)) R
            (e : ℤ)).hom ≫
          (ProjectiveSpectrum.Twist.polynomialPullbackIso (Fin (n + 1))
            (Proj.uliftIntCastRingHom R) (e : ℤ)).hom) ⊤
        (Scheme.Modules.pullbackGlobalSections f tw
          (Scheme.twistMonomialSection n (Spec (.of R)) e i)) := by
    have hassoc : (Scheme.Modules.pullback f).map
        (Scheme.Modules.tensorLeftUnitIso tw).inv ≫
        ((Scheme.Modules.pullback f).map
          (Scheme.Modules.tensorLeftUnitIso
            ((Scheme.Modules.pullback ρ).obj
              (ProjectiveSpectrum.Twist.twist
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
                (e : ℤ)))).hom ≫
          (Proj.polynomialProjOverSpec_pullbackAbsoluteTwistIso (Fin (n + 1)) R
            (e : ℤ)).hom ≫
          (ProjectiveSpectrum.Twist.polynomialPullbackIso (Fin (n + 1))
            (Proj.uliftIntCastRingHom R) (e : ℤ)).hom)
        = ((Proj.polynomialProjOverSpec_pullbackAbsoluteTwistIso (Fin (n + 1)) R
            (e : ℤ)).hom ≫
          (ProjectiveSpectrum.Twist.polynomialPullbackIso (Fin (n + 1))
            (Proj.uliftIntCastRingHom R) (e : ℤ)).hom) := by
      slice_lhs 1 2 => rw [(show (Scheme.Modules.pullback f).map
        (Scheme.Modules.tensorLeftUnitIso tw).inv ≫
        (Scheme.Modules.pullback f).map
          (Scheme.Modules.tensorLeftUnitIso
            ((Scheme.Modules.pullback ρ).obj
              (ProjectiveSpectrum.Twist.twist
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
                (e : ℤ)))).hom = 𝟙 _ from hcancel)]
      simp only [Category.id_comp]
    rw [hassoc]
    rfl
  rw [h2]
  -- split the composite and collapse the double pullback of sections
  have hsplit : (ConcreteCategory.hom (Scheme.Modules.Hom.app
      ((Proj.polynomialProjOverSpec_pullbackAbsoluteTwistIso (Fin (n + 1)) R
        (e : ℤ)).hom ≫
        (ProjectiveSpectrum.Twist.polynomialPullbackIso (Fin (n + 1))
          (Proj.uliftIntCastRingHom R) (e : ℤ)).hom) ⊤))
      ((Scheme.Modules.pullbackGlobalSections f tw)
        (Scheme.twistMonomialSection n (Spec (CommRingCat.of R)) e i))
    = (ConcreteCategory.hom (Scheme.Modules.Hom.app
        (ProjectiveSpectrum.Twist.polynomialPullbackIso (Fin (n + 1))
          (Proj.uliftIntCastRingHom R) (e : ℤ)).hom ⊤))
      ((ConcreteCategory.hom (Scheme.Modules.Hom.app
        (Proj.polynomialProjOverSpec_pullbackAbsoluteTwistIso (Fin (n + 1)) R
          (e : ℤ)).hom ⊤))
        ((Scheme.Modules.pullbackGlobalSections f tw)
          (Scheme.twistMonomialSection n (Spec (CommRingCat.of R)) e i))) := rfl
  rw [hsplit]
  have h3 : (ConcreteCategory.hom (Scheme.Modules.Hom.app
      (Proj.polynomialProjOverSpec_pullbackAbsoluteTwistIso (Fin (n + 1)) R
        (e : ℤ)).hom ⊤))
      ((Scheme.Modules.pullbackGlobalSections f tw)
        (Scheme.twistMonomialSection n (Spec (CommRingCat.of R)) e i))
    = Scheme.Modules.pullbackGlobalSections
        (Proj.polynomialMap (Fin (n + 1)) (Proj.uliftIntCastRingHom R))
        (ProjectiveSpectrum.Twist.twist
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) (e : ℤ)) b :=
    Scheme.Modules.pullbackGlobalSections_comp_congr f ρ
      (Proj.polynomialMap (Fin (n + 1)) (Proj.uliftIntCastRingHom R))
      (Proj.polynomialProjOverSpecIso_inv_absoluteProjection (Fin (n + 1)) R)
      (ProjectiveSpectrum.Twist.twist
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) (e : ℤ)) b
  rw [h3]
  -- identify the pulled-back basis vector as a homogeneous section
  have hbsec : b = MvPolynomial.homogeneousSubmoduleGlobalSectionsLinearEquiv n
      (ULift.{u} ℤ) e (MvPolynomial.homogeneousSubmoduleFinBasis n (ULift.{u} ℤ) e i) := by
    rw [hb]
    exact Module.Basis.map_apply _ _ _
  rw [hbsec]
  -- the coefficient-change comparison computes the image
  have h4 := ProjectiveSpectrum.Twist.pullbackComparison_app_pullbackGlobalSections_homogeneousSection
    (MvPolynomial.mapGradedRingHom (ι := Fin (n + 1)) (Proj.uliftIntCastRingHom R))
    (MvPolynomial.irrelevant_le_map_mapGradedRingHom (Proj.uliftIntCastRingHom R))
    (MvPolynomial.homogeneousSubmoduleFinBasis n (ULift.{u} ℤ) e i) ⊤
  refine Eq.trans (show _ = ProjectiveSpectrum.Twist.homogeneousSection
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (ProjectiveSpectrum.Twist.gradedImage
        (MvPolynomial.mapGradedRingHom (ι := Fin (n + 1)) (Proj.uliftIntCastRingHom R))
        (MvPolynomial.homogeneousSubmoduleFinBasis n (ULift.{u} ℤ) e i))
      ((Proj.map (MvPolynomial.mapGradedRingHom (ι := Fin (n + 1))
          (Proj.uliftIntCastRingHom R))
        (MvPolynomial.irrelevant_le_map_mapGradedRingHom
          (Proj.uliftIntCastRingHom R))) ⁻¹ᵁ ⊤) from h4) ?_
  rw [MvPolynomial.gradedImage_homogeneousSubmoduleFinBasis]
  have hR : MvPolynomial.projectiveTwistGlobalSectionsBasis n R e i
      = MvPolynomial.homogeneousSubmoduleGlobalSectionsLinearEquiv n R e
        (MvPolynomial.homogeneousSubmoduleFinBasis n R e i) :=
    Module.Basis.map_apply _ _ _
  rw [hR]
  rfl

/-- API identification for the Quot-to-Grassmannian construction in Proposition 2.4.1:
the transported binomial basis is the family of monomial sections. The `i`-th basis vector of
`Γ(ℙⁿ_R, 𝒪(e))` is the pullback of the `i`-th monomial section over `ℤ`. -/
theorem projectiveSpaceOverTwistGlobalSectionsBasis_eq_twistMonomialSection
    (n : ℕ) (R : Type u) [CommRing R] (e : ℕ) (i : Fin ((n + e).choose n)) :
    Scheme.projectiveSpaceOverTwistGlobalSectionsBasis n R e i
      = Scheme.twistMonomialSection n (Spec (.of R)) e i := by
  letI := Scheme.Modules.globalSectionsModule
    (Scheme.projectiveSpaceOverπ n (Spec (.of R)))
    (Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (e : ℤ))
  letI := MvPolynomial.projectiveTwistGlobalSectionsModule n R e
  have h := projectiveSpaceOverTwistGlobalSectionsLinearEquiv_twistMonomialSection n R e i
  have h2 : Scheme.projectiveSpaceOverTwistGlobalSectionsBasis n R e i
      = (projectiveSpaceOverTwistGlobalSectionsLinearEquiv n R e).symm
        (MvPolynomial.projectiveTwistGlobalSectionsBasis n R e i) :=
    Module.Basis.map_apply _ _ _
  rw [h2, ← h]
  exact (projectiveSpaceOverTwistGlobalSectionsLinearEquiv n R e).symm_apply_apply _

/-- Helper lemma: transporting a section along an equality of twists and back is the
identity. -/
theorem hom_app_eqToHom_cast {X : Scheme.{u}} (G : ℤ → X.Modules) {a b : ℤ} (h : a = b)
    (s : Γ(G b, ⊤)) :
    Scheme.Modules.Hom.app (eqToHom (congrArg G h)) ⊤
      (show Γ(G a, ⊤) from h.symm ▸ s) = s := by
  subst h
  rfl

set_option synthInstance.maxHeartbeats 1000000 in
/-- Helper lemma computing the finite-coproduct comparison on a coproduct injection: its
image is the corresponding single-component tuple. -/
theorem globalSectionsFiniteCoproductLinearEquiv_ι
    {X : Scheme.{u}} {R : CommRingCat.{u}} {J : Type u} [Finite J] [DecidableEq J]
    (p : X ⟶ Spec R) (F : J → X.Modules) (j : J) (s : Γ(F j, ⊤)) :
    letI (i : J) := Scheme.Modules.globalSectionsModule p (F i)
    letI := Scheme.Modules.globalSectionsModule p (∐ F)
    Scheme.Modules.globalSectionsFiniteCoproductLinearEquiv p F
        (Scheme.Modules.Hom.app (Limits.Sigma.ι F j) ⊤ s)
      = Pi.single j s := by
  letI (i : J) := Scheme.Modules.globalSectionsModule p (F i)
  letI := Scheme.Modules.globalSectionsModule p (∐ F)
  letI : Limits.HasFiniteBiproducts X.Modules :=
    Limits.HasFiniteBiproducts.of_hasFiniteCoproducts
  funext j'
  have happ := Scheme.Modules.globalSectionsFiniteCoproductLinearEquiv_apply p F
    (Scheme.Modules.Hom.app (Limits.Sigma.ι F j) ⊤ s) j'
  refine happ.trans ?_
  have hcomp : Limits.Sigma.ι F j ≫
      ((Limits.biproduct.isoCoproduct F).inv ≫ Limits.biproduct.π F j')
      = if h : j = j' then eqToHom (congrArg F h) else 0 := by
    rw [Limits.biproduct.isoCoproduct_inv, ← Category.assoc, Limits.colimit.ι_desc]
    exact Limits.biproduct.ι_π F j j'
  have hL : (PresheafOfModules.Hom.app
      ((Limits.biproduct.isoCoproduct F).inv ≫ Limits.biproduct.π F j').val (op ⊤)).hom
      (Scheme.Modules.Hom.app (Limits.Sigma.ι F j) ⊤ s)
      = (PresheafOfModules.Hom.app (Limits.Sigma.ι F j ≫
          ((Limits.biproduct.isoCoproduct F).inv ≫ Limits.biproduct.π F j')).val
        (op ⊤)).hom s := rfl
  rw [hL, hcomp]
  rcases eq_or_ne j j' with rfl | hjj
  · rw [dif_pos rfl]
    rw [Pi.single_eq_same]
    rfl
  · rw [dif_neg hjj]
    rw [Pi.single_eq_of_ne' hjj]
    rfl

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- API computation for the Quot-to-Grassmannian construction in Proposition 2.4.1: the twisted-free
homogeneous comparison carries the monomial sections to the single-monomial tuples. -/
theorem twistedFreeTwistGlobalSectionsHomogeneousEquiv_twistedFreeMonomialSection
    (n : ℕ) (R : Type u) [CommRing R] (l : ℤ) (r : ℕ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) (j : ULift.{u} (Fin r)) (i : Fin ((n + e).choose n)) :
    twistedFreeTwistGlobalSectionsHomogeneousEquiv (J := ULift.{u} (Fin r)) n R l d e
        he.symm
        (Scheme.twistedFreeMonomialSection n (Spec (.of R)) l r d e he j i)
      = Pi.single j (MvPolynomial.homogeneousSubmoduleFinBasis n R e i) := by
  classical
  -- repeat the `let`s of the definition verbatim (see the §2.4 INSIGHTS entry on
  -- computing `letI`-heavy definitions)
  let p := Scheme.projectiveSpaceOverπ n (Spec (.of R))
  let A := Scheme.Modules.tensor
    (∐ fun _ : ULift.{u} (Fin r) => Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l))
    (Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (d : ℤ))
  let F : ULift.{u} (Fin r) → (Scheme.projectiveSpaceOver n (Spec (.of R))).Modules :=
    fun _ => Scheme.projectiveSpaceOverTwist n (Spec (.of R)) ((d : ℤ) - l)
  let eA : A ≅ ∐ F :=
    Scheme.projectiveSpaceOverNegativeTwist_coproduct_twistIso_nat
      (J := ULift.{u} (Fin r)) n (Spec (.of R)) l d
  let eT : Scheme.projectiveSpaceOverTwist n (Spec (.of R)) ((d : ℤ) - l) ≅
      Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (e : ℤ) :=
    eqToIso (congrArg (Scheme.projectiveSpaceOverTwist n (Spec (.of R))) he.symm.symm)
  letI := Scheme.Modules.globalSectionsModule p A
  letI := Scheme.Modules.globalSectionsModule p
    (Scheme.projectiveSpaceOverTwist n (Spec (.of R)) ((d : ℤ) - l))
  letI := Scheme.Modules.globalSectionsModule p (∐ F)
  letI := Scheme.Modules.globalSectionsModule p
    (Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (e : ℤ))
  letI := MvPolynomial.projectiveTwistGlobalSectionsModule n R e
  have hE : twistedFreeTwistGlobalSectionsHomogeneousEquiv (J := ULift.{u} (Fin r)) n R l
      d e he.symm
      = (Scheme.Modules.globalSectionsLinearEquivOfIso p eA).trans
        ((Scheme.Modules.globalSectionsFiniteCoproductLinearEquiv p F).trans
          (LinearEquiv.piCongrRight fun _ : ULift.{u} (Fin r) =>
            (Scheme.Modules.globalSectionsLinearEquivOfIso p eT).trans
              (twistGlobalSectionsHomogeneousEquiv n R e))) := rfl
  rw [hE, LinearEquiv.trans_apply, LinearEquiv.trans_apply]
  -- layer 1: the coproduct-twist identification undoes the one in the definition
  have h1 : (Scheme.Modules.globalSectionsLinearEquivOfIso p eA)
      (Scheme.twistedFreeMonomialSection n (Spec (.of R)) l r d e he j i)
      = Scheme.Modules.Hom.app (Limits.Sigma.ι F j) ⊤
        (show Γ(Scheme.projectiveSpaceOverTwist n (Spec (CommRingCat.of R)) ((d : ℤ) - l), ⊤)
          from he ▸ Scheme.twistMonomialSection n (Spec (.of R)) e i) := by
    have hcancel := congrArg (fun k : (∐ F) ⟶ (∐ F) =>
        (PresheafOfModules.Hom.app k.val (op ⊤)).hom
          (Scheme.Modules.Hom.app (Limits.Sigma.ι F j) ⊤
            (show Γ(Scheme.projectiveSpaceOverTwist n (Spec (CommRingCat.of R)) ((d : ℤ) - l), ⊤)
          from he ▸ Scheme.twistMonomialSection n (Spec (.of R)) e i)))
      eA.inv_hom_id
    exact hcancel
  rw [h1]
  rw [globalSectionsFiniteCoproductLinearEquiv_ι]
  -- layer 3: the twist recast and the keystone identify the component
  have h3 : ((Scheme.Modules.globalSectionsLinearEquivOfIso p eT).trans
        (twistGlobalSectionsHomogeneousEquiv n R e))
      (show Γ(Scheme.projectiveSpaceOverTwist n (Spec (CommRingCat.of R)) ((d : ℤ) - l), ⊤)
          from he ▸ Scheme.twistMonomialSection n (Spec (.of R)) e i)
      = MvPolynomial.homogeneousSubmoduleFinBasis n R e i := by
    have hcast : (Scheme.Modules.globalSectionsLinearEquivOfIso p eT)
        (show Γ(Scheme.projectiveSpaceOverTwist n (Spec (CommRingCat.of R)) ((d : ℤ) - l), ⊤)
          from he ▸ Scheme.twistMonomialSection n (Spec (.of R)) e i)
        = Scheme.twistMonomialSection n (Spec (.of R)) e i :=
      hom_app_eqToHom_cast (Scheme.projectiveSpaceOverTwist n (Spec (.of R))) he
        (Scheme.twistMonomialSection n (Spec (.of R)) e i)
    rw [LinearEquiv.trans_apply, hcast]
    have hkey := projectiveSpaceOverTwistGlobalSectionsLinearEquiv_twistMonomialSection
      n R e i
    have hun : twistGlobalSectionsHomogeneousEquiv n R e
        (Scheme.twistMonomialSection n (Spec (.of R)) e i)
        = (MvPolynomial.homogeneousSubmoduleGlobalSectionsLinearEquiv n R e).symm
          (projectiveSpaceOverTwistGlobalSectionsLinearEquiv n R e
            (Scheme.twistMonomialSection n (Spec (.of R)) e i)) := rfl
    rw [hun, hkey]
    have hbasis : MvPolynomial.projectiveTwistGlobalSectionsBasis n R e i
        = MvPolynomial.homogeneousSubmoduleGlobalSectionsLinearEquiv n R e
          (MvPolynomial.homogeneousSubmoduleFinBasis n R e i) :=
      Module.Basis.map_apply _ _ _
    rw [hbasis, LinearEquiv.symm_apply_apply]
  -- assemble componentwise
  funext j'
  rw [LinearEquiv.piCongrRight_apply]
  rcases eq_or_ne j' j with rfl | hjj
  · rw [Pi.single_eq_same, Pi.single_eq_same]
    exact h3
  · rw [Pi.single_eq_of_ne hjj, Pi.single_eq_of_ne hjj, map_zero]

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- Supporting API for the Quot-to-Grassmannian construction in Proposition 2.4.1: over
an affine base, the monomial evaluation surjects on global sections. Every global section of
`F(d) = 𝒪(-l)^{⊕r}(d)` is a combination of the monomial sections with global-function
coefficients. This is the affine case of the `hmono` hypothesis of
`surjective_finFreeSectionsMap'_quotMonomial`. -/
theorem surjective_finFreeSectionsMap'_twistedFreeMonomial_top
    (n : ℕ) (R : Type u) [CommRing R] (l : ℤ) (r : ℕ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {m : ℕ}
    (σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n)) :
    Function.Surjective (Scheme.Modules.finFreeSectionsMap'
      (Scheme.Modules.freeHomOfSections
        (M := (Scheme.Modules.pushforward
          (Scheme.projectiveSpaceOverπ n (Spec (CommRingCat.of R)))).obj
          (Scheme.projectiveSpaceOverTwistModule
            (∐ fun _ : ULift.{u} (Fin r) =>
              Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l)) (d : ℤ)))
        (fun k : ULift.{u} (Fin m) =>
          Scheme.twistedFreeMonomialSection n (Spec (.of R)) l r d e he (σ k).1 (σ k).2))
      (⊤ : (Spec (CommRingCat.of R)).Opens)) := by
  classical
  let p := Scheme.projectiveSpaceOverπ n (Spec (CommRingCat.of R))
  let A := Scheme.Modules.tensor
    (∐ fun _ : ULift.{u} (Fin r) => Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l))
    (Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (d : ℤ))
  letI := Scheme.Modules.globalSectionsModule p A
  letI : Module R ↥Γ((Scheme.Modules.pushforward
      (Scheme.projectiveSpaceOverπ n (Spec (CommRingCat.of R)))).obj
      (Scheme.projectiveSpaceOverTwistModule
        (∐ fun _ : ULift.{u} (Fin r) =>
          Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l)) (d : ℤ)), ⊤) :=
    Scheme.Modules.globalSectionsModule p A
  let E := twistedFreeTwistGlobalSectionsHomogeneousEquiv (J := ULift.{u} (Fin r)) n R l d e
    he.symm
  rw [Scheme.Modules.surjective_finFreeSectionsMap'_iff, _root_.eq_top_iff]
  rintro x -
  -- the generating sections are the monomial sections
  have hgenmono : ∀ (j : ULift.{u} (Fin r)) (i : Fin ((n + e).choose n)),
      Scheme.Modules.freeGen (Scheme.Modules.freeHomOfSections
        (M := (Scheme.Modules.pushforward
          (Scheme.projectiveSpaceOverπ n (Spec (CommRingCat.of R)))).obj
          (Scheme.projectiveSpaceOverTwistModule
            (∐ fun _ : ULift.{u} (Fin r) =>
              Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l)) (d : ℤ)))
        (fun k : ULift.{u} (Fin m) =>
          Scheme.twistedFreeMonomialSection n (Spec (.of R)) l r d e he (σ k).1 (σ k).2))
        ⊤ ((σ.symm (j, i)).down)
      = Scheme.twistedFreeMonomialSection n (Spec (.of R)) l r d e he j i := by
    intro j i
    rw [Scheme.Modules.freeGen_freeHomOfSections]
    have h1 : ((homOfLE (le_top (a := (⊤ : (Spec (CommRingCat.of R)).Opens)))).op :
        op (⊤ : (Spec (CommRingCat.of R)).Opens) ⟶ op ⊤) = 𝟙 _ := rfl
    rw [h1, PresheafOfModules.map_id]
    have h3 := congrArg (fun z : ULift.{u} (Fin r) × Fin ((n + e).choose n) =>
      Scheme.twistedFreeMonomialSection n (Spec (.of R)) l r d e he z.1 z.2)
      (σ.apply_symm_apply (j, i))
    exact h3
  -- decompose the image of `x` under the global-sections equivalence
  have hEx : E x = ∑ j : ULift.{u} (Fin r), ∑ i : Fin ((n + e).choose n),
      (MvPolynomial.homogeneousSubmoduleFinBasis n R e).repr (E x j) i •
        Pi.single j (MvPolynomial.homogeneousSubmoduleFinBasis n R e i) := by
    conv_lhs => rw [← Finset.univ_sum_single (E x)]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_lhs => rw [← Module.Basis.sum_repr
      (MvPolynomial.homogeneousSubmoduleFinBasis n R e) (E x j)]
    rw [show (Pi.single j (∑ i : Fin ((n + e).choose n),
        (MvPolynomial.homogeneousSubmoduleFinBasis n R e).repr (E x j) i •
          MvPolynomial.homogeneousSubmoduleFinBasis n R e i) : _) =
      LinearMap.single R (fun _ : ULift.{u} (Fin r) =>
        MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R e) j
        (∑ i : Fin ((n + e).choose n),
          (MvPolynomial.homogeneousSubmoduleFinBasis n R e).repr (E x j) i •
            MvPolynomial.homogeneousSubmoduleFinBasis n R e i) from rfl]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    rfl
  -- write `x` as an `R`-combination of the pulled-back single-basis tuples
  have hx : x = ∑ j : ULift.{u} (Fin r), ∑ i : Fin ((n + e).choose n),
      (MvPolynomial.homogeneousSubmoduleFinBasis n R e).repr (E x j) i •
        E.symm (Pi.single j (MvPolynomial.homogeneousSubmoduleFinBasis n R e i)) := by
    conv_lhs => rw [← LinearEquiv.symm_apply_apply E x, hEx]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
  -- the equivalence pulls single-basis tuples back to the monomial sections
  have hmonoEq : ∀ (j : ULift.{u} (Fin r)) (i : Fin ((n + e).choose n)),
      E.symm (Pi.single j (MvPolynomial.homogeneousSubmoduleFinBasis n R e i))
        = Scheme.twistedFreeMonomialSection n (Spec (.of R)) l r d e he j i := by
    intro j i
    rw [← twistedFreeTwistGlobalSectionsHomogeneousEquiv_twistedFreeMonomialSection
      n R l r d e he j i]
    exact LinearEquiv.symm_apply_apply _ _
  rw [hx]
  simp only [hmonoEq]
  refine Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun i _ => ?_
  -- the `R`-action is the restriction of the `Γ(Spec R, ⊤)`-action, definitionally
  exact Submodule.smul_mem _
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      ((MvPolynomial.homogeneousSubmoduleFinBasis n R e).repr (E x j) i))
    (Submodule.subset_span ⟨(σ.symm (j, i)).down, hgenmono j i⟩)

end AlgebraicGeometry.ProjectiveSpace

end
