module

public import StacksAndModuli.API.ProjectiveSpaceTwistSurjectivity
public import StacksAndModuli.API.ProjectiveDVRQuotientPullbackSerre
public import StacksAndModuli.API.FlatOverDescent
public import StacksAndModuli.API.PushforwardProjectiveRank

/-!
# Surjectivity of twisted sections over the affine opens of the base

The scheme-level uniform surjectivity `exists_bound_surjective_twistedGlobalSections`
holds over an affine noetherian base.  The Grassmannian map of §2.4 needs it over each
affine open `U` of a locally noetherian base `T`: the sections of the twisted presentation
over `π⁻¹U` surject.  This file restricts the family to `Spec Γ(U, ⊤)` along
`projectiveSpaceOverMap`, applies the affine statement, and transports the conclusion back
through the open immersion.

Main declarations:

* `AlgebraicGeometry.Scheme.twistedFreeAmbient_isFinitePresentation`;
* `AlgebraicGeometry.Scheme.Modules.surjective_app_of_arrow_iso`;
* `AlgebraicGeometry.ProjectiveSpace.exists_bound_surjective_twist_app_preimage` — the
  per-affine-open uniform surjectivity.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry ProjectiveSpectrum.Twist

universe u

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Background finiteness API for the Quot-to-Grassmannian construction in Proposition 2.4.1: the
finite twisted-free ambient sheaf is finitely presented over any base. -/
theorem twistedFreeAmbient_isFinitePresentation (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) :
    (∐ fun _ : ULift.{u} (Fin r) =>
      Scheme.projectiveSpaceOverTwist n T (-l)).IsFinitePresentation := by
  unfold Scheme.projectiveSpaceOverTwist
  exact ProjectiveSpectrum.Twist.pullbackPolynomialTwistedFree_isFinitePresentation
    (R := ULift.{u} ℤ) (Fin (n + 1))
    (Limits.pullback.snd (specULiftZIsTerminal.from T)
      (specULiftZIsTerminal.from (Scheme.projectiveSpace n))) r (-l)

/-- General transport lemma used by the affine-open API: surjectivity of a section map
transports along a commuting square of sheaf morphisms whose verticals are isomorphisms. -/
theorem Modules.surjective_app_of_arrow_iso {X : Scheme.{u}}
    {A B A' B' : X.Modules} (u : A ⟶ B) (v : A' ⟶ B') (a : A ≅ A') (b : B ≅ B')
    (hsq : u ≫ b.hom = a.hom ≫ v) (V : X.Opens)
    (h : Function.Surjective (Modules.Hom.app v V)) :
    Function.Surjective (Modules.Hom.app u V) := by
  have hbid : ∀ z : Γ(B, V),
      (Modules.Hom.app b.inv V) ((Modules.Hom.app b.hom V) z) = z := by
    intro z
    have h1 := congrArg (fun χ : B ⟶ B =>
      (PresheafOfModules.Hom.app χ.val (op V)).hom) b.hom_inv_id
    exact LinearMap.congr_fun h1 z
  have haid : ∀ z : Γ(A', V),
      (Modules.Hom.app a.hom V) ((Modules.Hom.app a.inv V) z) = z := by
    intro z
    have h1 := congrArg (fun χ : A' ⟶ A' =>
      (PresheafOfModules.Hom.app χ.val (op V)).hom) a.inv_hom_id
    exact LinearMap.congr_fun h1 z
  intro y
  obtain ⟨x', hx'⟩ := h (Modules.Hom.app b.hom V y)
  refine ⟨Modules.Hom.app a.inv V x', ?_⟩
  have hb : Function.Injective (Modules.Hom.app b.hom V) := fun s t hst => by
    have h2 := congrArg (fun z => (Modules.Hom.app b.inv V) z) hst
    rw [hbid s, hbid t] at h2
    exact h2
  refine hb ?_
  have hsq' : (Modules.Hom.app b.hom V) ((Modules.Hom.app u V)
      ((Modules.Hom.app a.inv V) x'))
      = (Modules.Hom.app v V) ((Modules.Hom.app a.hom V)
        ((Modules.Hom.app a.inv V) x')) := by
    have h1 := congrArg (fun χ : A ⟶ B' =>
      (PresheafOfModules.Hom.app χ.val (op V)).hom) hsq
    exact LinearMap.congr_fun h1 ((Modules.Hom.app a.inv V) x')
  rw [hsq', haid, hx']

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProjectiveSpace

open AlgebraicGeometry.Scheme

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
-- Same instance-search and transport burden as the affine-base statement.
/-- Supporting API for the Quot-to-Grassmannian construction in Proposition 2.4.1: uniform
surjectivity of twisted sections over every affine open of the base. For the twisted-free
presentation of a flat family with fibrewise Hilbert polynomial `P` over a locally
noetherian base `T` and `d ≥ d₁(n, l, r, P)`, the map on sections over `π⁻¹U` is
surjective for every affine open `U ⊆ T`. -/
theorem exists_bound_surjective_twist_app_preimage (n r : ℕ) (l : ℤ) (P : Polynomial ℚ) :
    ∃ d₁ : ℤ, 0 ≤ d₁ ∧ ∀ (T : Scheme.{u}) [IsLocallyNoetherian T]
      (Q : (Scheme.projectiveSpaceOver n T).Modules)
      (_ : Q.IsFinitePresentation)
      (ψ : (∐ fun _ : ULift.{u} (Fin r) =>
        Scheme.projectiveSpaceOverTwist n T (-l)) ⟶ Q)
      (_ : Epi ψ)
      (_ : Q.FlatOver (Scheme.projectiveSpaceOverπ n T))
      (_ : Scheme.HasFiberwiseHilbertPolynomial Q P)
      (d : ℤ), d₁ ≤ d → ∀ U : T.affineOpens,
      Function.Surjective (Scheme.Modules.Hom.app
        (Scheme.Modules.tensorMapLeft ψ (Scheme.projectiveSpaceOverTwist n T d))
        (Scheme.projectiveSpaceOverπ n T ⁻¹ᵁ U.1)) := by
  obtain ⟨d₁, hd₁0, hd₁⟩ := exists_bound_surjective_twistedGlobalSections.{u} n r l P
  refine ⟨d₁, hd₁0, ?_⟩
  intro T _ Q hQfp ψ hψ hflat hHP d hd U
  haveI := hQfp
  haveI := hψ
  haveI : Q.IsQuasicoherent := inferInstance
  -- the affine restriction of the base
  set R' : Type u := ↥Γ(T, U.1) with hR'
  haveI : IsNoetherianRing R' := IsLocallyNoetherian.component_noetherian U
  set gU : Spec Γ(T, U.1) ⟶ T := U.2.isoSpec.inv ≫ U.1.ι with hgU
  haveI : IsOpenImmersion gU := inferInstance
  set mU := Scheme.projectiveSpaceOverMap n gU with hmU
  haveI : IsOpenImmersion mU := inferInstance
  -- the restricted datum
  set QU := (Scheme.Modules.pullback mU).obj Q with hQU
  haveI : QU.IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  set ψU := (Scheme.projectiveSpaceOverTwistedFree_pullbackIso n r l gU).inv ≫
    (Scheme.Modules.pullback mU).map ψ with hψU
  haveI : Epi ψU := epi_comp _ _
  have hflatU : QU.FlatOver (Scheme.projectiveSpaceOverπ n (Spec Γ(T, U.1))) :=
    Scheme.Modules.FlatOver.pullback_of_isPullback mU
      (Scheme.projectiveSpaceOverπ n (Spec Γ(T, U.1)))
      (Scheme.projectiveSpaceOverπ n T) gU
      (Scheme.isPullback_projectiveSpaceOverMap n gU).flip Q hflat
  have hHPU : Scheme.HasFiberwiseHilbertPolynomial QU P :=
    Scheme.HasFiberwiseHilbertPolynomial.pullback gU hHP
  -- the affine-base surjectivity
  have hU := hd₁ R' QU inferInstance
    (twistedFreeAmbient_isFinitePresentation n (Spec (CommRingCat.of R')) l r)
    ψU inferInstance hflatU hHPU d hd
  -- peel the ambient identification off the presentation
  have hU2 : Function.Surjective (Scheme.Modules.Hom.app
      (Scheme.Modules.tensorMapLeft ((Scheme.Modules.pullback mU).map ψ)
        (Scheme.projectiveSpaceOverTwist n (Spec Γ(T, U.1)) d)) ⊤) := by
    have hsplit : Scheme.Modules.tensorMapLeft ψU
        (Scheme.projectiveSpaceOverTwist n (Spec Γ(T, U.1)) d)
        = Scheme.Modules.tensorMapLeft
            (Scheme.projectiveSpaceOverTwistedFree_pullbackIso n r l gU).inv
            (Scheme.projectiveSpaceOverTwist n (Spec Γ(T, U.1)) d) ≫
          Scheme.Modules.tensorMapLeft ((Scheme.Modules.pullback mU).map ψ)
            (Scheme.projectiveSpaceOverTwist n (Spec Γ(T, U.1)) d) :=
      Scheme.Modules.tensorMapLeft_comp _ _ _
    have hcomp : (Scheme.Modules.Hom.app (Scheme.Modules.tensorMapLeft ψU
        (Scheme.projectiveSpaceOverTwist n (Spec Γ(T, U.1)) d)) ⊤ :
          _ → _)
        = (Scheme.Modules.Hom.app (Scheme.Modules.tensorMapLeft
            ((Scheme.Modules.pullback mU).map ψ)
            (Scheme.projectiveSpaceOverTwist n (Spec Γ(T, U.1)) d)) ⊤ :
          _ → _) ∘
          (Scheme.Modules.Hom.app (Scheme.Modules.tensorMapLeft
            (Scheme.projectiveSpaceOverTwistedFree_pullbackIso n r l gU).inv
            (Scheme.projectiveSpaceOverTwist n (Spec Γ(T, U.1)) d)) ⊤ :
          _ → _) := by
      rw [hsplit]
      rfl
    rw [hcomp] at hU
    exact hU.of_comp
  -- the pullback of the twisted presentation is conjugate to the twisted pullback
  have hsq := Scheme.Modules.pullbackTensorIsoOfIsOpenImmersion_tensorRight_naturality
    mU ψ (Scheme.projectiveSpaceOverTwist n T d)
    (Scheme.projectiveSpaceOverTwist_pullbackIso n gU d)
  have hpull : Function.Surjective (Scheme.Modules.Hom.app
      ((Scheme.Modules.pullback mU).map
        (Scheme.Modules.tensorMapLeft ψ
          (Scheme.projectiveSpaceOverTwist n T d))) ⊤) :=
    Scheme.Modules.surjective_app_of_arrow_iso _ _ _ _ hsq ⊤ hU2
  -- pass from the pullback functor to the restriction functor
  have hrest : Function.Surjective (Scheme.Modules.Hom.app
      ((Scheme.Modules.restrictFunctor mU).map
        (Scheme.Modules.tensorMapLeft ψ
          (Scheme.projectiveSpaceOverTwist n T d))) ⊤) := by
    refine Scheme.Modules.surjective_app_of_arrow_iso _ _
      ((Scheme.Modules.restrictFunctorIsoPullback mU).app _)
      ((Scheme.Modules.restrictFunctorIsoPullback mU).app _) ?_ ⊤ hpull
    exact (Scheme.Modules.restrictFunctorIsoPullback mU).hom.naturality _
  -- sections of the restriction over `⊤` are sections over the image open
  have himg : Function.Surjective (Scheme.Modules.Hom.app
      (Scheme.Modules.tensorMapLeft ψ (Scheme.projectiveSpaceOverTwist n T d))
      (mU ''ᵁ ⊤)) := hrest
  -- the image open is the preimage of `U`
  have hop : mU ''ᵁ (⊤ : (Scheme.projectiveSpaceOver n (Spec Γ(T, U.1))).Opens)
      = Scheme.projectiveSpaceOverπ n T ⁻¹ᵁ U.1 := by
    rw [Scheme.Hom.image_top_eq_opensRange]
    have hgrange : gU.opensRange = U.1 := by
      apply TopologicalSpace.Opens.ext
      show Set.range gU.base = (U.1 : Set T)
      rw [hgU]
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
      have hsurj : Set.range (U.2.isoSpec.inv).base = Set.univ :=
        Set.range_eq_univ.mpr (fun y => ⟨(U.2.isoSpec.hom).base y, by
          rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]; rfl⟩)
      rw [hsurj, Set.image_univ, Scheme.Opens.range_ι]
    apply TopologicalSpace.Opens.ext
    show Set.range mU.base = _
    rw [hmU, Scheme.range_projectiveSpaceOverMap n gU, hgrange]
  rw [hop] at himg
  exact himg

end AlgebraicGeometry.ProjectiveSpace

end
