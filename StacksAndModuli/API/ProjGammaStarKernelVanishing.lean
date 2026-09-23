module

public import StacksAndModuli.API.ProjGammaStarKernelFibre
public import StacksAndModuli.API.ProjectiveGradedKernelRegularity
public import StacksAndModuli.API.ProjGammaStarQuotientFlat
public import StacksAndModuli.API.ProjectiveSpaceOverMapIso

/-!
# Vanishing of `Hᵍʳ¹(Γ_*(ker p))` in uniformly bounded degrees

Supporting API for Step 1 of Proposition 2.4.1: for the twisted-free presentation of a
Quot datum over a noetherian affine base, the graded Čech cohomology of
`Γ_*(ker p)` vanishes in every positive cohomological degree from a bound `d₁(n, l, r, P)`
onwards, **uniformly** in the base and in the datum.

The proof is Cohomology and Base Change with cochain flatness
(`GradedModule.subsingleton_cechHgr_of_fibrewise'`): the Čech cochains of `Γ_*(ker p)` are
flat because the kernel-route short exact sequence localizes to flat chart sections; and
on each field fibre the cohomology of `Γ_*(ker p) ⊗ κ` is computed by `Γ_*` of the kernel
of the base-changed presentation (`isIso_cechHgrMap_kernelFibreCompare_app`), which is
`m₀`-regular by the uniform bound `exists_boundsRegularity_twistedFree_kernel`.

Main declarations:

* `AlgebraicGeometry.ProjectiveSpace.GradedModule.ShortExact.congr_middle` and
  `…GradedModule.cokerCongrOfSurjectiveComp` — transport helpers;
* `AlgebraicGeometry.ProjectiveSpace.gammaStarFibreTwistedFreeIso` — `Γ_*` of the fibre of
  the twisted-free ambient sheaf is the twisted-free graded module;
* `AlgebraicGeometry.ProjectiveSpace.exists_bound_subsingleton_cechHgr_gammaStar_kernel` —
  uniform higher-cohomology vanishing;
* `AlgebraicGeometry.ProjectiveSpace.exists_bound_surjective_gammaStarMap` — uniform
  surjectivity on twisted global sections.
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

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

variable {k : Type u} [CommRing k] {n : ℕ}

/-- Transport a short exact sequence of graded modules along an isomorphism of the middle
term. -/
lemma ShortExact.congr_middle {A B B' C : GradedModule k n} (e : B ≅ B')
    {f : A ⟶ B} {g : B ⟶ C} (h : ShortExact f g) :
    ShortExact (f ≫ e.hom) (e.inv ≫ g) where
  injective d := by
    intro x y hxy
    refine h.injective d ?_
    have hb := (isoApp e d).toLinearEquiv.injective
    exact hb hxy
  exact d := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      show ((e.inv ≫ g).app d).hom (((f ≫ e.hom).app d).hom w) = 0
      have h1 : ((e.inv ≫ g).app d).hom (((f ≫ e.hom).app d).hom w)
          = (g.app d).hom ((e.inv.app d).hom ((e.hom.app d).hom ((f.app d).hom w))) := rfl
      rw [h1]
      have h2 : (e.inv.app d).hom ((e.hom.app d).hom ((f.app d).hom w))
          = (f.app d).hom w := by
        have := congrArg ModuleCat.Hom.hom (congrArg (fun ψ : B ⟶ B => ψ.app d)
          e.hom_inv_id)
        exact LinearMap.congr_fun this ((f.app d).hom w)
      rw [h2]
      have h3 : (f.app d).hom w ∈ LinearMap.ker (g.app d).hom := by
        rw [← h.exact d]
        exact ⟨w, rfl⟩
      exact h3
    · intro hz
      have hz' : (e.inv.app d).hom z ∈ LinearMap.ker (g.app d).hom := hz
      rw [← h.exact d] at hz'
      obtain ⟨w, hw⟩ := hz'
      refine ⟨w, ?_⟩
      show (e.hom.app d).hom ((f.app d).hom w) = z
      rw [hw]
      have := congrArg ModuleCat.Hom.hom (congrArg (fun ψ : B' ⟶ B' => ψ.app d)
        e.inv_hom_id)
      exact LinearMap.congr_fun this z
  surjective d := by
    have hcomp : (((e.inv ≫ g).app d).hom : B'.obj d → C.obj d)
        = (g.app d).hom ∘ (e.inv.app d).hom := rfl
    rw [hcomp]
    exact (h.surjective d).comp (isoApp e d).symm.toLinearEquiv.surjective

/-- Precomposing with a degreewise surjection does not change the cokernel. -/
noncomputable def cokerCongrOfSurjectiveComp {A' A B : GradedModule k n}
    (u : A' ⟶ A) (hu : ∀ d, Function.Surjective (u.app d).hom) (f : A ⟶ B) :
    coker (u ≫ f) ≅ coker f := by
  have hrange : ∀ d, LinearMap.range ((u ≫ f).app d).hom = LinearMap.range (f.app d).hom := by
    intro d
    have hcomp : (((u ≫ f).app d).hom : A'.obj d → B.obj d)
        = (f.app d).hom ∘ (u.app d).hom := rfl
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨(u.app d).hom w, rfl⟩
    · rintro ⟨w, rfl⟩
      obtain ⟨v, hv⟩ := hu d w
      exact ⟨v, by show (f.app d).hom ((u.app d).hom v) = _; rw [hv]⟩
  refine isoOfBijective (cokerDesc (u ≫ f) (toCoker f) (fun d a => ?_)) (fun d => ⟨?_, ?_⟩)
  · have hmem : ((u ≫ f).app d).hom a ∈ LinearMap.range (f.app d).hom := by
      rw [← hrange d]
      exact ⟨a, rfl⟩
    show Submodule.Quotient.mk (((u ≫ f).app d).hom a) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact hmem
  · intro z w hzw
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    obtain ⟨b', rfl⟩ := Submodule.Quotient.mk_surjective _ w
    have hzw' : Submodule.Quotient.mk (p := LinearMap.range (f.app d).hom) b
        = Submodule.Quotient.mk b' := hzw
    rw [Submodule.Quotient.eq] at hzw' ⊢
    rw [hrange d]
    exact hzw'
  · intro z
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact ⟨Submodule.Quotient.mk b, rfl⟩

/-- An isomorphism of graded modules induces one on Čech cohomology. -/
noncomputable def cechHgrIso {M N : GradedModule k n} (e : M ≅ N) (i : ℕ) :
    M.cechHgr i ≅ N.cechHgr i where
  hom := cechHgrMap e.hom i
  inv := cechHgrMap e.inv i
  hom_inv_id := by rw [← cechHgrMap_comp, e.hom_inv_id, cechHgrMap_id]
  inv_hom_id := by rw [← cechHgrMap_comp, e.inv_hom_id, cechHgrMap_id]

end AlgebraicGeometry.ProjectiveSpace.GradedModule

namespace AlgebraicGeometry.ProjectiveSpace

open AlgebraicGeometry.ProjectiveSpace.GradedModule

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n r : ℕ) (l : ℤ) {R : Type u} [CommRing R] {κ : Type u} [Field κ] (f : R →+* κ)

local notation "𝒜R" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
local notation "𝒜κ" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) κ

/-- The `R`-level ambient sheaf on polynomial `Proj`: the pullback of the twisted-free
sheaf across the comparison with relative projective space. -/
noncomputable abbrev projAmbient : (Proj (MvPolynomial.homogeneousSubmodule
    (Fin (n + 1)) R)).Modules :=
  (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj
    (∐ fun _ : ULift.{u} (Fin r) => Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l))

/-- The fibre of the ambient sheaf is the ambient sheaf: pulling `projAmbient` back along
the coefficient change is the `Proj`-side normalization of the base-changed twisted-free
sheaf. -/
noncomputable def projAmbientFibreIso :
    (Scheme.Modules.pullback (coeffMap n f)).obj (projAmbient n r l (R := R)) ≅
      (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n κ).inv).obj
        (∐ fun _ : ULift.{u} (Fin r) => Scheme.projectiveSpaceOverTwist n (Spec (.of κ)) (-l)) :=
  pullbackPolynomialTransportIso n f _ ≪≫
    (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n κ).inv).mapIso
      (Scheme.projectiveSpaceOverTwistedFree_pullbackIso n r l
        (Spec.map (CommRingCat.ofHom f)))

/-- **`Γ_*` of the fibre of the ambient sheaf is the twisted-free graded module.** -/
noncomputable def gammaStarFibreTwistedFreeIso (hn : 0 < n) :
    Proj.gammaStar 𝒜κ (projSpecπ n κ)
        ((Scheme.Modules.pullback (coeffMap n f)).obj (projAmbient n r l (R := R)))
        (stdVars n κ) ≅
      ((GradedModule.structureModule κ n).twist (-l)).pow r :=
  Proj.gammaStarMapIso _ (projSpecπ n κ) (stdVars n κ) (projAmbientFibreIso n r l f) ≪≫
    gammaStarPullTwistedFreeIso n κ hn (-l) r

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
-- The `IsQuasicoherent` binders over an explicit polynomial `Proj` make instance search
-- slow, and the fibre normalization crosses the semireducible comparison
-- `projectiveSpaceOverSpecIso`.
/-- **Uniform vanishing of the higher graded Čech cohomology of `Γ_*(ker p)`** for the
twisted-free presentation of a flat family with fibrewise Hilbert polynomial `P`: there is
a bound `d₁ = d₁(n, l, r, P)`, independent of the noetherian base and of the datum, beyond
which `Hᵍʳⁱ(Γ_*(ker p))` vanishes for every `i ≥ 1`. -/
theorem exists_bound_subsingleton_cechHgr_gammaStar_kernel (P : Polynomial ℚ) :
    ∃ d₁ : ℤ, 0 ≤ d₁ ∧ ∀ (R' : Type u) [CommRing R'] [IsNoetherianRing R']
      (Q : (Scheme.projectiveSpaceOver n (Spec (CommRingCat.of R'))).Modules)
      (_ : Q.IsFinitePresentation)
      (_ : (∐ fun _ : ULift.{u} (Fin r) =>
        Scheme.projectiveSpaceOverTwist n (Spec (.of R')) (-l)).IsFinitePresentation)
      (p : projAmbient n r l (R := R') ⟶
        (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R').inv).obj Q)
      (_ : Epi p)
      (_ : Q.FlatOver (Scheme.projectiveSpaceOverπ n (Spec (.of R'))))
      (_ : Scheme.HasFiberwiseHilbertPolynomial Q P)
      (i : ℕ), 1 ≤ i → ∀ d : ℤ, d₁ ≤ d →
      Subsingleton (((Proj.gammaStar
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R')
        (projSpecπ n R') (kernel p) (stdVars n R')).cechHgr i).obj d) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · -- on `ℙ⁰` this is Grothendieck vanishing
    subst hn0
    refine ⟨0, le_refl 0, ?_⟩
    intro R' _ _ Q _ _ p _ _ _ i hi d _
    exact GradedModule.subsingleton_cechHgr _ i (by omega) d
  -- the uniform regularity bound
  obtain ⟨m₀, hm₀⟩ := Cohomology.exists_boundsRegularity_twistedFree_kernel.{u} r n l P
  refine ⟨max (m₀ - 1) 0, le_max_right _ _, ?_⟩
  intro R' _ _ Q hQfp hAmbfp p hp hflat hHP i hi d hd
  haveI := hQfp
  haveI := hAmbfp
  haveI := hp
  have hd0 : 0 ≤ d := le_trans (le_max_right _ _) hd
  -- instances on the `Proj` side
  haveI hE : (projAmbient n r l (R := R')).IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  haveI hQ' : ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R').inv).obj
      Q).IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  haveI : ∀ e : ℤ, (twistModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R')
      (projAmbient n r l (R := R')) e).IsQuasicoherent :=
    fun e => twistModule_std_isQuasicoherent _ e
  haveI : ∀ e : ℤ, (twistModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R')
      ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R').inv).obj Q)
      e).IsQuasicoherent :=
    fun e => twistModule_std_isQuasicoherent _ e
  haveI hKfp : (kernel p).IsFinitePresentation :=
    Scheme.Modules.kernel_isFinitePresentation p
  haveI : ∀ e : ℤ, (twistModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R')
      (kernel p) e).IsQuasicoherent :=
    fun e => twistModule_std_isQuasicoherent _ e
  have hflat' : ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R').inv).obj
      Q).FlatOver (projSpecπ n R') :=
    Scheme.Modules.FlatOver.pullback_isIso (projectiveSpaceOverSpecIso n R').inv Q
      (projectiveSpaceOverSpecIso_inv_comp_projectiveSpaceOverπ n R') hflat
  -- graded flatness of the ambient over the base
  have hEflat : GradedModule.IsFlat (Proj.gammaStar
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R') (projSpecπ n R')
      (projAmbient n r l (R := R')) (stdVars n R')) :=
    isFlat_gammaStarPullTwistedFree n R' hn (-l) r
  have hEfg : GradedModule.IsFG (Proj.gammaStar
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R') (projSpecπ n R')
      (projAmbient n r l (R := R')) (stdVars n R')) :=
    isFG_gammaStarPullTwistedFree n R' hn (-l) r
  -- coherence of `Γ_*(ker p)`
  have hKfg : GradedModule.IsFG (Proj.gammaStar
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R') (projSpecπ n R')
      (kernel p) (stdVars n R')) :=
    GradedModule.IsFG.of_injective _
      (fun e => Proj.injective_gammaStarMap_kernel_ι (Fin (n + 1)) (projSpecπ n R')
        (stdVars n R') p e) hEfg
  -- CBC with cochain flatness
  refine GradedModule.subsingleton_cechHgr_of_fibrewise' hKfg (fun q => ?_) ?_ i hi
  · -- cochain flatness of `Γ_*(ker p)`
    refine GradedModule.flat_cechCochain_of_flat_loc _ (fun a => ?_) q d
    refine GradedModule.IsFlat.of_shortExact
      (GradedModule.loc_shortExact _ (l := [a])
        (Proj.shortExact_gammaStar_toCoker_kernel (projSpecπ n R') p))
      (fun e => hEflat.flat_loc [a] e)
      (Proj.isFlat_loc_kernelQuotientModule p a hflat')
  · -- fibrewise vanishing, through the kernel fibre comparison and uniform regularity
    intro κ _ _ i' hi'
    have halg : (algebraMap R' κ).toAlgebra = ‹Algebra R' κ› :=
      Algebra.algebra_ext _ _ (fun r => rfl)
    -- the base-changed presentation and its kernel-route data over `κ`
    set pκ : (Scheme.Modules.pullback (coeffMap n (algebraMap R' κ))).obj
        (projAmbient n r l (R := R')) ⟶
      (Scheme.Modules.pullback (coeffMap n (algebraMap R' κ))).obj
        ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R').inv).obj Q) :=
      (Scheme.Modules.pullback (coeffMap n (algebraMap R' κ))).map p with hpκdef
    haveI hpκepi : Epi pκ := inferInstance
    haveI : ((Scheme.Modules.pullback (coeffMap n (algebraMap R' κ))).obj
        (projAmbient n r l (R := R'))).IsFinitePresentation :=
      Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
    haveI : ((Scheme.Modules.pullback (coeffMap n (algebraMap R' κ))).obj
        ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R').inv).obj
          Q)).IsFinitePresentation :=
      Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
    -- the fibre ambient identification and the transported short exact sequence
    have eE := gammaStarFibreTwistedFreeIso n r l (algebraMap R' κ) hn
    have hSEκ := Proj.shortExact_gammaStar_toCoker_kernel (projSpecπ n κ) pκ
    have hSE' := GradedModule.ShortExact.congr_middle eE hSEκ
    have hEκfg : GradedModule.IsFG (Proj.gammaStar
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) κ) (projSpecπ n κ)
        ((Scheme.Modules.pullback (coeffMap n (algebraMap R' κ))).obj
          (projAmbient n r l (R := R'))) (stdVars n κ)) :=
      GradedModule.IsFG.of_iso eE.symm
        (((GradedModule.isFG_structureModule (k := κ) (n := n)).twist (-l)).pow r)
    have hKκfg : GradedModule.IsFG (Proj.gammaStar
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) κ) (projSpecπ n κ)
        (kernel pκ) (stdVars n κ)) :=
      GradedModule.IsFG.of_injective _
        (fun e => Proj.injective_gammaStarMap_kernel_ι (Fin (n + 1)) (projSpecπ n κ)
          (stdVars n κ) pκ e) hEκfg
    have hNfg : (Cohomology.cech κ).IsCoherent
        (GradedModule.coker (Proj.gammaStarMap
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) κ) (projSpecπ n κ)
          (kernel.ι pκ) (stdVars n κ))) :=
      GradedModule.IsFG.coker _ hEκfg
    -- the fibre Hilbert function of the quotient model
    have hh0 : ∃ dP : ℤ, ∀ d' : ℤ, dP ≤ d' →
        (((Cohomology.cech κ).h (GradedModule.coker (Proj.gammaStarMap
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) κ) (projSpecπ n κ)
          (kernel.ι pκ) (stdVars n κ))) 0 d' : ℚ)) = P.eval (d' : ℚ) := by
      -- normalize the presentation to the standard fibre form
      set tQ := pullbackPolynomialTransportIso n (algebraMap R' κ) Q with htQ
      set pκ' := pκ ≫ tQ.hom with hpκ'
      haveI : Epi pκ' := epi_comp _ _
      set QK := Scheme.Modules.projectiveSpaceBaseChangeOfRingHom Q (algebraMap R' κ)
        with hQK
      haveI : QK.IsFinitePresentation :=
        Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
      haveI : ∀ e : ℤ, (twistModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) κ)
          ((Scheme.Modules.pullback (coeffMap n (algebraMap R' κ))).obj
            (projAmbient n r l (R := R'))) e).IsQuasicoherent :=
        fun e => twistModule_std_isQuasicoherent _ e
      haveI : ∀ e : ℤ, (twistModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) κ)
          ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n κ).inv).obj
            QK) e).IsQuasicoherent :=
        fun e => twistModule_std_isQuasicoherent _ e
      haveI : (kernel pκ').IsFinitePresentation :=
        Scheme.Modules.kernel_isFinitePresentation pκ'
      haveI : ∀ e : ℤ, (twistModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) κ)
          (kernel pκ') e).IsQuasicoherent :=
        fun e => twistModule_std_isQuasicoherent _ e
      -- the two kernel-route models agree
      have hw : (kernelCompMono pκ tQ.hom).hom ≫ kernel.ι pκ = kernel.ι pκ' :=
        kernel.lift_ι _ _ _
      let wIso := Proj.gammaStarMapIso
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) κ) (projSpecπ n κ)
        (stdVars n κ) (kernelCompMono pκ tQ.hom)
      have hfac : Proj.gammaStarMap
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) κ) (projSpecπ n κ)
          (kernel.ι pκ') (stdVars n κ)
          = wIso.hom ≫ Proj.gammaStarMap
            (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) κ) (projSpecπ n κ)
            (kernel.ι pκ) (stdVars n κ) := by
        rw [← hw, Proj.gammaStarMap_comp]
        rfl
      have eN : GradedModule.coker (Proj.gammaStarMap
            (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) κ) (projSpecπ n κ)
            (kernel.ι pκ') (stdVars n κ))
          ≅ GradedModule.coker (Proj.gammaStarMap
            (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) κ) (projSpecπ n κ)
            (kernel.ι pκ) (stdVars n κ)) := by
        rw [hfac]
        exact GradedModule.cokerCongrOfSurjectiveComp wIso.hom
          (fun e => (GradedModule.isoApp wIso e).toLinearEquiv.surjective) _
      -- the scheme-level Hilbert function of the fibre
      have hHPκ := hHP (CommRingCat.of κ) (Field.toIsField κ)
        (Spec.map (CommRingCat.ofHom (algebraMap R' κ)))
      obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hHPκ
      refine ⟨max (N₀ : ℤ) 0, fun d' hd' => ?_⟩
      have hd'0 : 0 ≤ d' := le_trans (le_max_right _ _) hd'
      have hd'N : (N₀ : ℤ) ≤ d' := le_trans (le_max_left _ _) hd'
      -- compare the two graded models and pass to global sections
      have h1 : ((Cohomology.cech κ).h (GradedModule.coker (Proj.gammaStarMap
            (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) κ) (projSpecπ n κ)
            (kernel.ι pκ) (stdVars n κ))) 0 d')
          = Module.finrank κ (((GradedModule.coker (Proj.gammaStarMap
            (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) κ) (projSpecπ n κ)
            (kernel.ι pκ') (stdVars n κ))).cechHgr 0).obj d') :=
        ((GradedModule.isoApp (GradedModule.cechHgrIso eN 0) d').toLinearEquiv.finrank_eq).symm
      rw [h1]
      letI := Scheme.Modules.globalSectionsModule
        (Scheme.projectiveSpaceOverπ n (Spec (CommRingCat.of κ)))
        (Scheme.projectiveSpaceOverTwistModule QK (d' : ℤ))
      have h2 := (cechHgrZeroQuotientModelGlobalSectionsEquiv n κ QK pκ' d').finrank_eq
      rw [h2]
      have h3 := hN₀ d'.toNat (by omega)
      rw [show ((d'.toNat : ℕ) : ℤ) = d' from Int.toNat_of_nonneg hd'0] at h3
      rw [show ((d'.toNat : ℕ) : ℚ) = (d' : ℚ) by
        rw [show ((d'.toNat : ℕ) : ℚ) = ((d'.toNat : ℤ) : ℚ) by push_cast; ring,
          Int.toNat_of_nonneg hd'0]] at h3
      exact h3
    -- the uniform regularity bound applies to the fibre kernel
    have hreg : (Cohomology.cech κ).IsMRegular (Proj.gammaStar
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) κ) (projSpecπ n κ)
        (kernel pκ) (stdVars n κ)) m₀ :=
      hm₀ κ (Cohomology.cech κ) (Cohomology.hasInfiniteBaseChange_cech κ)
        _ _ _ _ hSE' hNfg hh0
    -- vanishing of the fibre cohomology at the degree `d`
    have hreg' := (Cohomology.cech κ).isMRegular_of_le_of_field hKκfg
      (Cohomology.hasInfiniteBaseChange_cech κ) hreg
      (show m₀ ≤ d + (i' : ℤ) by omega)
    have hvan := hreg' i' hi'
    rw [show d + (i' : ℤ) - (i' : ℤ) = d by ring] at hvan
    -- transport through the kernel fibre comparison
    haveI hcomp := isIso_cechHgrMap_kernelFibreCompare_app n (algebraMap R' κ) p
      hflat' i' d.toNat
    rw [← halg]
    rw [show d = (d.toNat : ℤ) from (Int.toNat_of_nonneg hd0).symm]
    haveI : Subsingleton (((Proj.gammaStar
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) κ) (projSpecπ n κ)
        (kernel pκ) (stdVars n κ)).cechHgr i').obj ((d.toNat : ℕ) : ℤ)) := by
      rw [show ((d.toNat : ℕ) : ℤ) = d from Int.toNat_of_nonneg hd0]
      exact hvan
    exact (asIso ((GradedModule.cechHgrMap
      (kernelFibreCompare n (algebraMap R' κ) p) i').app
        ((d.toNat : ℕ) : ℤ))).toLinearEquiv.toEquiv.subsingleton

set_option synthInstance.maxHeartbeats 1000000 in
-- Same instance-search burden as the vanishing theorem above.
/-- Supporting uniform-surjectivity theorem for Step 1 of Proposition 2.4.1: beyond a bound
`d₁ = d₁(n, l, r, P)` independent
of the noetherian base and of the datum, `Γ(E(d)) ⟶ Γ(Q(d))` is surjective for the
twisted-free presentation of every flat family with fibrewise Hilbert polynomial `P`. -/
theorem exists_bound_surjective_gammaStarMap (P : Polynomial ℚ) :
    ∃ d₁ : ℤ, 0 ≤ d₁ ∧ ∀ (R' : Type u) [CommRing R'] [IsNoetherianRing R']
      (Q : (Scheme.projectiveSpaceOver n (Spec (CommRingCat.of R'))).Modules)
      (_ : Q.IsFinitePresentation)
      (_ : (∐ fun _ : ULift.{u} (Fin r) =>
        Scheme.projectiveSpaceOverTwist n (Spec (.of R')) (-l)).IsFinitePresentation)
      (p : projAmbient n r l (R := R') ⟶
        (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R').inv).obj Q)
      (_ : Epi p)
      (_ : Q.FlatOver (Scheme.projectiveSpaceOverπ n (Spec (.of R'))))
      (_ : Scheme.HasFiberwiseHilbertPolynomial Q P)
      (d : ℤ), d₁ ≤ d →
      Function.Surjective ((Proj.gammaStarMap
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R')
        (projSpecπ n R') p (stdVars n R')).app d).hom := by
  obtain ⟨d₁, hd₁0, hd₁⟩ :=
    exists_bound_subsingleton_cechHgr_gammaStar_kernel n r l P
  refine ⟨d₁, hd₁0, ?_⟩
  intro R' _ _ Q hQfp hAmbfp p hp hflat hHP d hd
  haveI := hQfp
  haveI := hAmbfp
  haveI := hp
  haveI : (projAmbient n r l (R := R')).IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  haveI : ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R').inv).obj
      Q).IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  haveI : ∀ e : ℤ, (twistModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R')
      (projAmbient n r l (R := R')) e).IsQuasicoherent :=
    fun e => twistModule_std_isQuasicoherent _ e
  haveI : ∀ e : ℤ, (twistModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R')
      ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R').inv).obj Q)
      e).IsQuasicoherent :=
    fun e => twistModule_std_isQuasicoherent _ e
  haveI : (kernel p).IsFinitePresentation :=
    Scheme.Modules.kernel_isFinitePresentation p
  haveI : ∀ e : ℤ, (twistModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R')
      (kernel p) e).IsQuasicoherent :=
    fun e => twistModule_std_isQuasicoherent _ e
  exact Proj.surjective_app_gammaStarMap_of_subsingleton (projSpecπ n R') p d
    (hd₁ R' Q hQfp hAmbfp p hp hflat hHP 1 le_rfl d hd)

end AlgebraicGeometry.ProjectiveSpace

end
