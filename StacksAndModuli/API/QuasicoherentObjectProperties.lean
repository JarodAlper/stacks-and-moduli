module

public import StacksAndModuli.«Section2.1-Intro».«part2.1.2-the-grassmannian-functor»
public import StacksAndModuli.API.PseudofunctorObjectProperty
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Local properties of quasicoherent sheaves

This file develops reusable descent infrastructure for the full subpseudofunctors of
`Scheme.Modules.quasicoherentPseudofunctor` cut out by finite presentation and finite
local freeness.

For finite presentation it proves the affine module criterion, stability under arbitrary
pullback, and fpqc locality by reducing a covering sieve over each affine open to a finite
affine faithfully flat cover. It also defines the coherent-sheaf and vector-bundle
pseudofunctors as full subpseudofunctors.

The finite-locally-free property is proved invariant under isomorphism and stable under
arbitrary pullback. Its fpqc-locality theorem is supplied once the corresponding affine
projective-module descent bridge is available.
-/

@[expose] public section

set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Bicategory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- Finite presentation transports along a semilinear equivalence over a ring
equivalence. -/
theorem Module.FinitePresentation.of_semilinearEquiv
    {R S M N : Type u} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    [Module.FinitePresentation R M] (e : R ≃+* S)
    [RingHomInvPair (e : R →+* S) (e.symm : S →+* R)]
    [RingHomInvPair (e.symm : S →+* R) (e : R →+* S)]
    (eM : M ≃ₛₗ[(e : R →+* S)] N) : Module.FinitePresentation S N := by
  letI : Algebra R S := (e : R →+* S).toAlgebra
  letI : Module R N := Module.compHom N (e : R →+* S)
  letI : IsScalarTower R S N := ⟨fun r s n ↦ by
    change (e r * s) • n = e r • (s • n)
    exact mul_smul _ _ _⟩
  let l : M →ₗ[R] N :=
    { toFun := eM
      map_add' := map_add eM
      map_smul' := fun r m ↦ eM.map_smulₛₗ r m }
  exact FinitePresentation.of_isBaseChange l
    (Module.isBaseChange_of_semilinearEquiv e rfl eM)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A finite global presentation of a quasicoherent sheaf on an affine spectrum
induces a finite presentation of its global-sections module. -/
lemma moduleSpecΓFunctor_finitePresentation_of_presentation
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    (P : SheafOfModules.Presentation M) [P.IsFinite] :
    Module.FinitePresentation R (moduleSpecΓFunctor.obj M) := by
  let Q := SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
  let d : SheafOfModules.free P.relations.I ⟶
      SheafOfModules.free P.generators.I :=
    (SheafOfModules.freeHomEquiv _).symm P.relations.s ≫
      kernel.ι P.generators.π
  let A : Q.FullSubcategory := ⟨SheafOfModules.free P.relations.I, inferInstance⟩
  let B : Q.FullSubcategory := ⟨SheafOfModules.free P.generators.I, inferInstance⟩
  let C : Q.FullSubcategory := ⟨M, inferInstance⟩
  let dQ : A ⟶ B := ObjectProperty.homMk d
  let gQ : B ⟶ C := ObjectProperty.homMk P.generators.π
  have hdg : dQ ≫ gQ = 0 := by
    apply ObjectProperty.hom_ext
    dsimp [dQ, gQ, d]
    simp
  let cQ : CokernelCofork dQ := CokernelCofork.ofπ gQ hdg
  have hcQ : IsColimit cQ := by
    refine Cofork.IsColimit.mk cQ (fun s ↦ ?_) (fun s ↦ ?_) (fun s m hm ↦ ?_)
    · let s0 : CokernelCofork d := CokernelCofork.ofπ s.π.hom (by
        have h := congrArg InducedCategory.Hom.hom (CokernelCofork.condition s)
        exact h)
      exact ObjectProperty.homMk (P.isColimit.desc s0)
    · apply ObjectProperty.hom_ext
      exact P.isColimit.fac
        (CokernelCofork.ofπ s.π.hom (by
          have h := congrArg InducedCategory.Hom.hom (CokernelCofork.condition s)
          exact h)) WalkingParallelPair.one
    · apply ObjectProperty.hom_ext
      apply Cofork.IsColimit.hom_ext P.isColimit
      let s0 : CokernelCofork d := CokernelCofork.ofπ s.π.hom (by
        have h := congrArg InducedCategory.Hom.hom (CokernelCofork.condition s)
        exact h)
      calc
        P.generators.π ≫ m.hom = s0.π := by
          simpa [cQ, gQ, s0] using congrArg InducedCategory.Hom.hom hm
        _ = P.generators.π ≫ P.isColimit.desc s0 :=
          (P.isColimit.fac s0 WalkingParallelPair.one).symm
  let E := tildeEquiv (R := R)
  have hcMap : IsColimit (cQ.map E.inverse) := cQ.mapIsColimit hcQ E.inverse
  let SC : ShortComplex (ModuleCat R) :=
    ShortComplex.mk (E.inverse.map dQ) (E.inverse.map gQ) (by
      rw [← E.inverse.map_comp, hdg, E.inverse.map_zero])
  have hSC : SC.Exact := ShortComplex.exact_of_g_is_cokernel SC (by
    exact hcMap)
  have hexact : Function.Exact (E.inverse.map dQ).hom (E.inverse.map gQ).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact SC).mp hSC
  have hsurj : Function.Surjective (E.inverse.map gQ).hom :=
    (ModuleCat.epi_iff_surjective _).mp (epi_of_isColimit_cofork hcMap)
  letI : Finite P.generators.I :=
    (inferInstance : P.generators.IsFiniteType).finite
  letI : Finite P.relations.I :=
    (inferInstance : P.relations.IsFiniteType).finite
  have hfpB : Module.FinitePresentation R (E.inverse.obj B) :=
    Module.FinitePresentation.of_equiv
      (freeModuleSpecΓIso (R := R) P.generators.I).toLinearEquiv
  letI : Module.FinitePresentation R (E.inverse.obj B) := hfpB
  have hfiniteA : Module.Finite R (E.inverse.obj A) :=
    Module.Finite.equiv
      (freeModuleSpecΓIso (R := R) P.relations.I).toLinearEquiv
  have hker : (LinearMap.ker (E.inverse.map gQ).hom).FG := by
    rw [LinearMap.exact_iff.mp hexact]
    rw [LinearMap.range_eq_map]
    exact hfiniteA.fg_top.map (E.inverse.map dQ).hom
  exact Module.finitePresentation_of_surjective (E.inverse.map gQ).hom hsurj hker

/-- Finite presentation of sections is invariant under replacing an open by an
equal open. -/
lemma Scheme.Modules.sections_finitePresentation_of_eq
    {X : Scheme.{u}} (M : X.Modules) (U V : X.Opens) (h : U = V)
    (hfp : Module.FinitePresentation Γ(X, U) Γ(M, U)) :
    Module.FinitePresentation Γ(X, V) Γ(M, V) := by
  subst V
  exact hfp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On an affine scheme, a finite global presentation of a quasicoherent module
sheaf induces a finite presentation of its intrinsic top-sections module. -/
lemma Scheme.Modules.finitePresentation_sections_top_of_presentation
    {X : Scheme.{u}} [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (P : SheafOfModules.Presentation M) [P.IsFinite] :
    Module.FinitePresentation Γ(X, ⊤) Γ(M, ⊤) := by
  let A := CommRingCat.of Γ(X, ⊤)
  let f : Spec A ⟶ X := X.isoSpec.inv
  let N := (Scheme.Modules.pullback f).obj M
  let PN := Scheme.Modules.presentationPullback f P
  have hN : Module.FinitePresentation A (moduleSpecΓFunctor.obj N) :=
    moduleSpecΓFunctor_finitePresentation_of_presentation N PN
  letI : Module.FinitePresentation A (moduleSpecΓFunctor.obj N) := hN
  have him : f ''ᵁ (⊤ : (Spec A).Opens) = ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]
  let eR := (f.appIso ⊤).commRingCatIsoToRingEquiv
  let eRestr := M.restrictAppIso f ⊤
  have hres (r : Γ(X, f ''ᵁ (⊤ : (Spec A).Opens)))
      (m : Γ(M, f ''ᵁ (⊤ : (Spec A).Opens))) :
      eRestr.inv (r • m) = eR r • eRestr.inv m := by
    change (M.restrictAppIso f ⊤).inv (r • m) =
      (f.appIso ⊤).hom r • (M.restrictAppIso f ⊤).inv m
    simp
  letI : RingHomInvPair
      (eR : Γ(X, f ''ᵁ (⊤ : (Spec A).Opens)) →+* Γ(Spec A, ⊤))
      (eR.symm : Γ(Spec A, ⊤) →+* Γ(X, f ''ᵁ (⊤ : (Spec A).Opens))) :=
    RingHomInvPair.of_ringEquiv eR
  letI : RingHomInvPair
      (eR.symm : Γ(Spec A, ⊤) →+* Γ(X, f ''ᵁ (⊤ : (Spec A).Opens)))
      (eR : Γ(X, f ''ᵁ (⊤ : (Spec A).Opens)) →+* Γ(Spec A, ⊤)) :=
    ⟨by ext; simp, by ext; simp⟩
  let ePull := Scheme.Modules.restrictSectionsLinearEquivPullback f M ⊤
  let eM : Γ(M, f ''ᵁ (⊤ : (Spec A).Opens))
      ≃ₛₗ[(eR : Γ(X, f ''ᵁ (⊤ : (Spec A).Opens)) →+* Γ(Spec A, ⊤))] Γ(N, ⊤) :=
    { toEquiv :=
        { toFun := fun m ↦ ePull (eRestr.inv m)
          invFun := fun n ↦ eRestr.hom (ePull.symm n)
          left_inv := fun m ↦ by simp
          right_inv := fun n ↦ by simp }
      map_add' := fun a b ↦ by simp
      map_smul' := fun r m ↦ by
        change ePull (eRestr.inv (r • m)) = eR r • ePull (eRestr.inv m)
        rw [hres r m]
        exact ePull.map_smul (eR r) (eRestr.inv m) }
  have hNtop : Module.FinitePresentation Γ(Spec A, ⊤) Γ(N, ⊤) := by
    let eA := (Scheme.ΓSpecIso A).symm.commRingCatIsoToRingEquiv
    letI : RingHomInvPair (eA : A →+* Γ(Spec A, ⊤))
        (eA.symm : Γ(Spec A, ⊤) →+* A) := RingHomInvPair.of_ringEquiv eA
    letI : RingHomInvPair (eA.symm : Γ(Spec A, ⊤) →+* A)
        (eA : A →+* Γ(Spec A, ⊤)) := ⟨by ext; simp, by ext; simp⟩
    let eN : moduleSpecΓFunctor.obj N ≃ₛₗ[(eA : A →+* Γ(Spec A, ⊤))] Γ(N, ⊤) :=
      { toEquiv := Equiv.refl _
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    exact Module.FinitePresentation.of_semilinearEquiv eA eN
  letI : Module.FinitePresentation Γ(Spec A, ⊤) Γ(N, ⊤) := hNtop
  let eBack := eR.symm
  letI : RingHomInvPair
      (eBack : Γ(Spec A, ⊤) →+* Γ(X, f ''ᵁ (⊤ : (Spec A).Opens)))
      (eBack.symm : Γ(X, f ''ᵁ (⊤ : (Spec A).Opens)) →+* Γ(Spec A, ⊤)) :=
    RingHomInvPair.of_ringEquiv eBack
  letI : RingHomInvPair
      (eBack.symm : Γ(X, f ''ᵁ (⊤ : (Spec A).Opens)) →+* Γ(Spec A, ⊤))
      (eBack : Γ(Spec A, ⊤) →+* Γ(X, f ''ᵁ (⊤ : (Spec A).Opens))) :=
    RingHomInvPair.of_ringEquiv eBack.symm
  have hImage : Module.FinitePresentation
      Γ(X, f ''ᵁ (⊤ : (Spec A).Opens)) Γ(M, f ''ᵁ (⊤ : (Spec A).Opens)) :=
    Module.FinitePresentation.of_semilinearEquiv eBack eM.symm
  exact Scheme.Modules.sections_finitePresentation_of_eq M _ _ him hImage

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A finite global presentation after restriction to an affine open yields finite
presentation of the ambient sections over that open. -/
lemma Scheme.Modules.finitePresentation_sections_of_restrict_presentation
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent] (U : X.affineOpens)
    (P : SheafOfModules.Presentation (M.restrict U.1.ι)) [P.IsFinite] :
    Module.FinitePresentation Γ(X, U.1) Γ(M, U.1) := by
  have htop : Module.FinitePresentation Γ(U.1.toScheme, ⊤)
      Γ(M.restrict U.1.ι, ⊤) :=
    Scheme.Modules.finitePresentation_sections_top_of_presentation
      (M.restrict U.1.ι) P
  let eR := (U.1.ι.appIso ⊤).symm.commRingCatIsoToRingEquiv
  letI : RingHomInvPair
      (eR : Γ(U.1.toScheme, ⊤) →+* Γ(X, U.1.ι ''ᵁ ⊤))
      (eR.symm : Γ(X, U.1.ι ''ᵁ ⊤) →+* Γ(U.1.toScheme, ⊤)) :=
    RingHomInvPair.of_ringEquiv eR
  letI : RingHomInvPair
      (eR.symm : Γ(X, U.1.ι ''ᵁ ⊤) →+* Γ(U.1.toScheme, ⊤))
      (eR : Γ(U.1.toScheme, ⊤) →+* Γ(X, U.1.ι ''ᵁ ⊤)) :=
    RingHomInvPair.of_ringEquiv eR.symm
  let eM : Γ(M.restrict U.1.ι, ⊤)
      ≃ₛₗ[(eR : Γ(U.1.toScheme, ⊤) →+* Γ(X, U.1.ι ''ᵁ ⊤))]
        Γ(M, U.1.ι ''ᵁ ⊤) :=
    { toEquiv :=
        { toFun := (M.restrictAppIso U.1.ι ⊤).hom
          invFun := (M.restrictAppIso U.1.ι ⊤).inv
          left_inv := fun m ↦ by simp
          right_inv := fun m ↦ by simp }
      map_add' := fun a b ↦ by simp
      map_smul' := fun r m ↦ by
        change (M.restrictAppIso U.1.ι ⊤).hom (r • m) =
          (U.1.ι.appIso ⊤).inv r • (M.restrictAppIso U.1.ι ⊤).hom m
        simp }
  letI : Module.FinitePresentation Γ(U.1.toScheme, ⊤)
      Γ(M.restrict U.1.ι, ⊤) := htop
  have hImage : Module.FinitePresentation Γ(X, U.1.ι ''ᵁ ⊤)
      Γ(M, U.1.ι ''ᵁ ⊤) :=
    Module.FinitePresentation.of_semilinearEquiv eR eM
  have him : U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens) = U.1 := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
  exact Scheme.Modules.sections_finitePresentation_of_eq M _ _ him hImage

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
/-- Finite presentation of a quasicoherent sheaf on an affine spectrum implies finite
presentation of its coordinate module. -/
lemma moduleSpecΓFunctor_finitePresentation_of_isFinitePresentation
    (M : (Spec R).Modules) [M.IsQuasicoherent] [M.IsFinitePresentation] :
    Module.FinitePresentation R (moduleSpecΓFunctor.obj M) := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  let s : Set R := { r | ∃ P : SheafOfModules.Presentation
      (M.restrict (Scheme.Opens.ι (PrimeSpectrum.basicOpen r))), P.IsFinite }
  have hcover : (⨆ r ∈ s, PrimeSpectrum.basicOpen r) = ⊤ := by
    apply top_unique
    intro x _
    have hxq : x ∈ ⨆ i, q.X i := by
      have hc := q.coversTop
      rw [_root_.Opens.coversTop_iff, TopologicalSpace.IsOpenCover] at hc
      rw [hc]
      trivial
    obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxq
    obtain ⟨V, ⟨_, ⟨r, rfl⟩, rfl⟩, hxr, hrq⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxi (q.X i).2
    let g : Scheme.Opens.toScheme (PrimeSpectrum.basicOpen r) ⟶
        Scheme.Opens.toScheme (q.X i) :=
      (Spec R).homOfLE hrq
    let P₀ : SheafOfModules.Presentation
        (M.restrict (Scheme.Opens.ι (q.X i))) :=
      Scheme.Modules.presentationRestrictOfOver M (q.X i) (q.presentation i)
    let e :=
      (Scheme.Modules.restrictFunctorComp g
        (Scheme.Opens.ι (q.X i))).symm ≪≫
      Scheme.Modules.restrictFunctorCongr
        (Scheme.homOfLE_ι (Spec R) hrq)
    let P :=
      SheafOfModules.Presentation.ofIsIso.{u, u, u} (e.app M).hom
        (Scheme.Modules.presentationRestrict g P₀)
    have hP : P.IsFinite := by
      letI : (q.presentation i).IsFinite := hq.isFinite_presentation i
      letI : P₀.IsFinite := by
        dsimp [P₀]
        infer_instance
      letI : (Scheme.Modules.presentationRestrict g P₀).IsFinite := by
        letI : PreservesColimitsOfSize.{u, u}
            (Scheme.Modules.restrictFunctor g) := inferInstance
        dsimp [Scheme.Modules.presentationRestrict]
        exact SheafOfModules.Presentation.map_isFinite P₀ _ _
      dsimp [P]
      infer_instance
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨r,
      TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨P, hP⟩, hxr⟩⟩
  have hs : Ideal.span s = ⊤ :=
    PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mp hcover
  let Mₚ (g : s) : Type u := Γ(M, PrimeSpectrum.basicOpen g.1)
  let Rₚ (g : s) : Type u := Γ(Spec R, PrimeSpectrum.basicOpen g.1)
  let φ (g : s) : Γ(M, ⊤) →ₗ[R] Mₚ g :=
    Scheme.Modules.sectionsToBasicOpenLinearMap M g.1
  letI (g : s) : IsLocalizedModule (Submonoid.powers g.1) (φ g) :=
    Scheme.Modules.isLocalizedModule_sectionsToBasicOpenLinearMap M g.1
  change Module.FinitePresentation R Γ(M, ⊤)
  refine Module.FinitePresentation.of_localizationSpan'
    (Mₚ := Mₚ) (Rₚ := Rₚ) s hs φ (fun g ↦ ?_)
  let U : (Spec R).affineOpens :=
    ⟨PrimeSpectrum.basicOpen g.1,
      AlgebraicGeometry.IsAffineOpen.Spec_basicOpen g.1⟩
  let P := g.property.choose
  letI : P.IsFinite := g.property.choose_spec
  exact Scheme.Modules.finitePresentation_sections_of_restrict_presentation M U P

/-- Affine pullback preserves finite projectivity of global sections. -/
lemma pullbackQuasicoherentSections_finite_projective
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    (hfin : Module.Finite R (moduleSpecΓFunctor.obj M))
    (hproj : Module.Projective R (moduleSpecΓFunctor.obj M)) :
    Module.Finite S
        (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (Spec.map φ)).obj M)) ∧
      Module.Projective S
        (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (Spec.map φ)).obj M)) := by
  algebraize [φ.hom]
  let e := pullbackQuasicoherentSectionsLinearEquiv φ M
  letI : Module.Finite R (moduleSpecΓFunctor.obj M) := hfin
  letI : Module.Projective R (moduleSpecΓFunctor.obj M) := hproj
  have hfinbase : Module.Finite S
      (TensorProduct R S (moduleSpecΓFunctor.obj M)) :=
    Module.Finite.base_change R S (moduleSpecΓFunctor.obj M)
  have hprojbase : Module.Projective S
      (TensorProduct R S (moduleSpecΓFunctor.obj M)) := inferInstance
  exact ⟨@Module.Finite.equiv S _ _ _ _ _ _ _ hfinbase e.symm,
    @Module.Projective.of_equiv _ _ _ _ _ _ _ _ _ _ _ _ _ _ e.symm hprojbase⟩

/-- Convert finite projectivity in the `R`-module convention to intrinsic top sections. -/
lemma moduleSpecΓFunctor_finite_projective_top (M : (Spec R).Modules)
    (hfin : Module.Finite R (moduleSpecΓFunctor.obj M))
    (hproj : Module.Projective R (moduleSpecΓFunctor.obj M)) :
    Module.Finite Γ(Spec R, ⊤) Γ(M, ⊤) ∧
      Module.Projective Γ(Spec R, ⊤) Γ(M, ⊤) := by
  let eR := (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv
  letI : Algebra R Γ(Spec R, ⊤) := eR.toRingHom.toAlgebra
  letI : RingHomInvPair (eR : R →+* Γ(Spec R, ⊤))
      (eR.symm : Γ(Spec R, ⊤) →+* R) := RingHomInvPair.of_ringEquiv eR
  letI : RingHomInvPair (eR.symm : Γ(Spec R, ⊤) →+* R)
      (eR : R →+* Γ(Spec R, ⊤)) := ⟨by ext; simp, by ext; simp⟩
  let eM : moduleSpecΓFunctor.obj M ≃ₛₗ[(eR : R →+* Γ(Spec R, ⊤))] Γ(M, ⊤) :=
    { toEquiv := Equiv.refl _
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact Module.finite_projective_of_semilinearEquiv eR rfl eM hfin hproj

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

lemma sections_finite_projective_of_pullback_openImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules) (U : X.Opens)
    (hfin : Module.Finite Γ(X, U) Γ((pullback f).obj M, U))
    (hproj : Module.Projective Γ(X, U) Γ((pullback f).obj M, U)) :
    Module.Finite Γ(Y, f ''ᵁ U) Γ(M, f ''ᵁ U) ∧
      Module.Projective Γ(Y, f ''ᵁ U) Γ(M, f ''ᵁ U) := by
  let e := (restrictFunctorIsoPullback f).app M
  let eUCat : ((M.restrict f).val.obj (Opposite.op U)) ≅
      (((pullback f).obj M).val.obj (Opposite.op U)) :=
    { hom := e.hom.val.app (Opposite.op U)
      inv := e.inv.val.app (Opposite.op U)
      hom_inv_id := congrArg (fun k ↦ k.val.app (Opposite.op U)) e.hom_inv_id
      inv_hom_id := congrArg (fun k ↦ k.val.app (Opposite.op U)) e.inv_hom_id }
  let eU : Γ(M.restrict f, U) ≃ₗ[Γ(X, U)] Γ((pullback f).obj M, U) :=
    eUCat.toLinearEquiv
  have hfin' : Module.Finite Γ(X, U) Γ(M.restrict f, U) :=
    @Module.Finite.equiv Γ(X, U) _ _ _ _ _ _ _ hfin eU.symm
  have hproj' : Module.Projective Γ(X, U) Γ(M.restrict f, U) :=
    @Module.Projective.of_equiv _ _ _ _ _ _ _ _ _ _ _ _ _ _ eU.symm hproj
  let eR := (f.appIso U).symm.commRingCatIsoToRingEquiv
  letI : Algebra Γ(X, U) Γ(Y, f ''ᵁ U) := eR.toRingHom.toAlgebra
  letI : RingHomInvPair (eR : Γ(X, U) →+* Γ(Y, f ''ᵁ U))
      (eR.symm : Γ(Y, f ''ᵁ U) →+* Γ(X, U)) := RingHomInvPair.of_ringEquiv eR
  letI : RingHomInvPair (eR.symm : Γ(Y, f ''ᵁ U) →+* Γ(X, U))
      (eR : Γ(X, U) →+* Γ(Y, f ''ᵁ U)) := ⟨by ext; simp, by ext; simp⟩
  let eM : Γ(M.restrict f, U) ≃ₛₗ[(eR : Γ(X, U) →+* Γ(Y, f ''ᵁ U))]
      Γ(M, f ''ᵁ U) :=
    { toEquiv :=
        { toFun := (M.restrictAppIso f U).hom
          invFun := (M.restrictAppIso f U).inv
          left_inv := fun m => by simp
          right_inv := fun m => by simp }
      map_add' := fun _ _ => map_add _ _ _
      map_smul' := fun r m => by
        change (M.restrictAppIso f U).hom (r • m) =
          (f.appIso U).inv r • (M.restrictAppIso f U).hom m
        simp }
  exact Module.finite_projective_of_semilinearEquiv eR rfl eM hfin' hproj'

/-- On an affine scheme, finite projectivity of top sections is finite local freeness. -/
lemma isFiniteLocallyFree_of_top {X : Scheme.{u}} [IsAffine X] {M : X.Modules}
    (hfin : Module.Finite Γ(X, ⊤) Γ(M, ⊤))
    (hproj : Module.Projective Γ(X, ⊤) Γ(M, ⊤)) : IsFiniteLocallyFree M := by
  intro x
  exact ⟨⟨⊤, isAffineOpen_top X⟩, trivial, hfin, hproj⟩

/-- Pullback by an isomorphism preserves finite local freeness. -/
lemma IsFiniteLocallyFree.pullback_of_isIso {X Y : Scheme.{u}} {M : Y.Modules}
    (f : X ⟶ Y) [IsIso f] (hM : IsFiniteLocallyFree M) :
    IsFiniteLocallyFree ((pullback f).obj M) := by
  intro x
  obtain ⟨U, hxU, hfin, hproj⟩ := hM (f x)
  let V : X.affineOpens := ⟨f ⁻¹ᵁ U.1, U.2.preimage_of_isIso f⟩
  have hVU : f ''ᵁ V.1 = U.1 := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Hom.opensRange_of_isIso, top_inf_eq]
  have hfin' : Module.Finite Γ(Y, f ''ᵁ V.1) Γ(M, f ''ᵁ V.1) := by
    rw [hVU]
    exact hfin
  have hproj' : Module.Projective Γ(Y, f ''ᵁ V.1) Γ(M, f ''ᵁ V.1) := by
    rw [hVU]
    exact hproj
  obtain ⟨hfinV, hprojV⟩ :=
    pullback_openImmersion_sections_finite_projective f M V.1 hfin' hproj'
  exact ⟨V, hxU, hfinV, hprojV⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- Pullback preserves finite local freeness of quasicoherent module sheaves. -/
lemma IsFiniteLocallyFree.pullback {X Y : Scheme.{u}} {M : Y.Modules}
    [M.IsQuasicoherent] (f : X ⟶ Y) (hM : IsFiniteLocallyFree M) :
    IsFiniteLocallyFree ((Modules.pullback f).obj M) := by
  intro x
  obtain ⟨U, hxU, hfinU, hprojU⟩ := hM (f x)
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U.1).2
  let VA : X.affineOpens := ⟨V, hV⟩
  let MU := (Modules.pullback U.1.ι).obj M
  have himU : U.1.ι ''ᵁ ⊤ = U.1 := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
  have hMUtop := pullback_openImmersion_sections_finite_projective
    U.1.ι M ⊤ (by rw [himU]; exact hfinU) (by rw [himU]; exact hprojU)
  let Mspec := (Modules.pullback U.2.isoSpec.inv).obj MU
  have himSpec : U.2.isoSpec.inv ''ᵁ ⊤ = ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]
  have hMspecTop := pullback_openImmersion_sections_finite_projective
    U.2.isoSpec.inv MU ⊤ (by rw [himSpec]; exact hMUtop.1)
      (by rw [himSpec]; exact hMUtop.2)
  have hMspecΓ := AlgebraicGeometry.moduleSpecΓFunctor_finite_projective_of_top Mspec
    hMspecTop.1 hMspecTop.2
  let g := f.appLE U.1 VA.1 hVU
  have hAffΓ := AlgebraicGeometry.pullbackQuasicoherentSections_finite_projective g Mspec
    hMspecΓ.1 hMspecΓ.2
  have hAffTop := AlgebraicGeometry.moduleSpecΓFunctor_finite_projective_top
    ((Modules.pullback (Spec.map g)).obj Mspec) hAffΓ.1 hAffΓ.2
  let Aff := (Modules.pullback (Spec.map g)).obj Mspec
  have hAff : IsFiniteLocallyFree Aff :=
    isFiniteLocallyFree_of_top hAffTop.1 hAffTop.2
  have hcomp := IsAffineOpen.SpecMap_appLE_fromSpec f U.2 VA.2 hVU
  let e : Aff ≅
      (Modules.pullback VA.2.isoSpec.inv).obj
        ((Modules.pullback VA.1.ι).obj ((Modules.pullback f).obj M)) :=
    (Modules.pullback (Spec.map g)).mapIso
        ((pullbackComp U.2.isoSpec.inv U.1.ι).app M) ≪≫
      (pullbackComp (Spec.map g) U.2.fromSpec).app M ≪≫
      (pullbackCongr hcomp).app M ≪≫
      ((pullbackComp VA.2.fromSpec f).app M).symm ≪≫
      ((pullbackComp VA.2.isoSpec.inv VA.1.ι).app ((Modules.pullback f).obj M)).symm
  have hSpecV : IsFiniteLocallyFree
      ((Modules.pullback VA.2.isoSpec.inv).obj
        ((Modules.pullback VA.1.ι).obj ((Modules.pullback f).obj M))) :=
    hAff.of_iso e
  have hBack := hSpecV.pullback_of_isIso VA.2.isoSpec.hom
  let NV := (Modules.pullback VA.1.ι).obj ((Modules.pullback f).obj M)
  let eBack : (Modules.pullback VA.2.isoSpec.hom).obj
      ((Modules.pullback VA.2.isoSpec.inv).obj NV) ≅ NV :=
    (pullbackComp VA.2.isoSpec.hom VA.2.isoSpec.inv).app NV ≪≫
      (pullbackCongr VA.2.isoSpec.hom_inv_id).app NV ≪≫ (pullbackId _).app NV
  have hNV : IsFiniteLocallyFree NV := hBack.of_iso eBack
  obtain ⟨W, hxW, hfinW, hprojW⟩ := hNV ⟨x, hxV⟩
  let W' : X.affineOpens := ⟨VA.1.ι ''ᵁ W.1,
    (Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion VA.1.ι).mpr W.2⟩
  have hxW' : x ∈ W'.1 := ⟨⟨x, hxV⟩, hxW, rfl⟩
  have hsec := sections_finite_projective_of_pullback_openImmersion
    VA.1.ι ((Modules.pullback f).obj M) W.1 hfinW hprojW
  have himage : VA.1.ι ''ᵁ W.1 = W'.1 := rfl
  exact ⟨W', hxW', by simpa [himage] using hsec.1,
    by simpa [himage] using hsec.2⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Finite presentation of a quasicoherent sheaf descends along a flat surjective
morphism between affine schemes. -/
lemma isFinitePresentation_of_pullback_of_flat_surjective_affine
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    [Flat f] [Surjective f] (M : Y.Modules) [M.IsQuasicoherent]
    (hM : ((pullback f).obj M).IsFinitePresentation) : M.IsFinitePresentation := by
  let N := (pullback Y.isoSpec.inv).obj M
  let N' := (pullback X.isoSpec.inv).obj ((pullback f).obj M)
  have hN' : N'.IsFinitePresentation := by
    letI : ((pullback f).obj M).IsFinitePresentation := hM
    dsimp [N']
    infer_instance
  let e := AlgebraicGeometry.pullbackAffineIsoSpecIso f M
  have hPull : ((pullback (Spec.map f.appTop)).obj N).IsFinitePresentation :=
    ObjectProperty.prop_of_iso
      (P := SheafOfModules.isFinitePresentation (Spec Γ(X, ⊤)).ringCatSheaf)
      e.symm hN'
  letI : ((pullback (Spec.map f.appTop)).obj N).IsFinitePresentation := hPull
  have hB : Module.FinitePresentation Γ(X, ⊤)
      (moduleSpecΓFunctor.obj ((pullback (Spec.map f.appTop)).obj N)) :=
    AlgebraicGeometry.moduleSpecΓFunctor_finitePresentation_of_isFinitePresentation _
  letI : Module.FinitePresentation Γ(X, ⊤)
      (moduleSpecΓFunctor.obj ((pullback (Spec.map f.appTop)).obj N)) := hB
  let eSec := AlgebraicGeometry.pullbackQuasicoherentSectionsLinearEquiv f.appTop N
  have hTensor : Module.FinitePresentation Γ(X, ⊤)
      ((ModuleCat.extendScalars f.appTop.hom).obj
        (moduleSpecΓFunctor.obj N)) :=
    Module.FinitePresentation.of_equiv eSec
  have hff : f.appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).mp
      ⟨inferInstance, inferInstance⟩
  algebraize [f.appTop.hom]
  letI : Module.FaithfullyFlat Γ(Y, ⊤) Γ(X, ⊤) := hff
  letI : Module.FinitePresentation Γ(X, ⊤)
      ((ModuleCat.extendScalars f.appTop.hom).obj
        (moduleSpecΓFunctor.obj N)) := hTensor
  letI : Module.FinitePresentation Γ(X, ⊤)
      (TensorProduct Γ(Y, ⊤) Γ(X, ⊤) (moduleSpecΓFunctor.obj N)) := by
    change Module.FinitePresentation Γ(X, ⊤)
      ((ModuleCat.extendScalars f.appTop.hom).obj
        (moduleSpecΓFunctor.obj N))
    exact hTensor
  have hNmod : Module.FinitePresentation Γ(Y, ⊤) (moduleSpecΓFunctor.obj N) :=
    Module.FinitePresentation.of_baseChange_faithfullyFlat
      Γ(Y, ⊤) (moduleSpecΓFunctor.obj N) Γ(X, ⊤)
  letI : Module.FinitePresentation Γ(Y, ⊤) (moduleSpecΓFunctor.obj N) := hNmod
  have hN : N.IsFinitePresentation :=
    AlgebraicGeometry.isFinitePresentation_of_moduleSpecΓFunctor N
  letI : N.IsFinitePresentation := hN
  have hBack : ((pullback Y.isoSpec.hom).obj N).IsFinitePresentation := by
    infer_instance
  let eBack : (pullback Y.isoSpec.hom).obj N ≅ M :=
    (pullbackComp Y.isoSpec.hom Y.isoSpec.inv).app M ≪≫
      (pullbackCongr Y.isoSpec.hom_inv_id).app M ≪≫
      (pullbackId _).app M
  exact ObjectProperty.prop_of_iso
    (P := SheafOfModules.isFinitePresentation Y.ringCatSheaf) eBack hBack

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On an affine scheme, a finitely presented quasicoherent sheaf admits a finite
global presentation. -/
lemma exists_finitePresentation_of_isFinitePresentation_affine
    {X : Scheme.{u}} [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    [M.IsFinitePresentation] : ∃ P : SheafOfModules.Presentation M, P.IsFinite := by
  let N := (pullback X.isoSpec.inv).obj M
  have hN : N.IsFinitePresentation := by infer_instance
  letI : N.IsFinitePresentation := hN
  have hNmod : Module.FinitePresentation Γ(X, ⊤) (moduleSpecΓFunctor.obj N) :=
    AlgebraicGeometry.moduleSpecΓFunctor_finitePresentation_of_isFinitePresentation N
  letI : Module.FinitePresentation Γ(X, ⊤) (moduleSpecΓFunctor.obj N) := hNmod
  obtain ⟨P, hP⟩ := AlgebraicGeometry.exists_finitePresentation_of_moduleSpecΓFunctor N
  letI : P.IsFinite := hP
  let Pback := presentationPullback X.isoSpec.hom P
  let eBack : (pullback X.isoSpec.hom).obj N ≅ M :=
    (pullbackComp X.isoSpec.hom X.isoSpec.inv).app M ≪≫
      (pullbackCongr X.isoSpec.hom_inv_id).app M ≪≫
      (pullbackId _).app M
  let Q := SheafOfModules.Presentation.ofIsIso eBack.hom Pback
  have hQ : Q.IsFinite := by
    dsimp [Q, Pback]
    infer_instance
  exact ⟨Q, hQ⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
/-- Finite presentation on a finite disjoint union is detected on its components. -/
lemma isFinitePresentation_of_sigma_pullbacks {n : ℕ} (X : Fin n → Scheme.{u})
    [∀ i, IsAffine (X i)] (M : (∐ X).Modules) [M.IsQuasicoherent]
    (hM : ∀ i, ((pullback (Sigma.ι X i)).obj M).IsFinitePresentation) :
    M.IsFinitePresentation := by
  let 𝒰 := AlgebraicGeometry.sigmaOpenCover X
  let presData (i : Fin n) :
      { P : SheafOfModules.Presentation
          (M.restrict (𝒰.f i).opensRange.ι) // P.IsFinite } := by
    let f := 𝒰.f i
    let K := (pullback f).obj M
    letI : K.IsFinitePresentation := hM i
    let L := (pullback f.isoOpensRange.inv).obj K
    have hL : L.IsFinitePresentation := by infer_instance
    let e : L ≅ M.restrict f.opensRange.ι :=
      (pullbackComp f.isoOpensRange.inv f).app M ≪≫
        (pullbackCongr f.isoOpensRange_inv_comp).app M ≪≫
        ((restrictFunctorIsoPullback f.opensRange.ι).app M).symm
    have hRestrict : (M.restrict f.opensRange.ι).IsFinitePresentation :=
      ObjectProperty.prop_of_iso
        (P := SheafOfModules.isFinitePresentation f.opensRange.toScheme.ringCatSheaf)
        e hL
    letI : (M.restrict f.opensRange.ι).IsFinitePresentation := hRestrict
    letI : IsAffine (𝒰.X i) := by
      change IsAffine (X i)
      infer_instance
    letI : IsAffine f.opensRange.toScheme := IsAffine.of_isIso f.isoOpensRange.inv
    let h := exists_finitePresentation_of_isFinitePresentation_affine
      (M.restrict f.opensRange.ι)
    exact ⟨Classical.choose h, Classical.choose_spec h⟩
  let pres (i : Fin n) : SheafOfModules.Presentation
      (M.restrict (𝒰.f i).opensRange.ι) := (presData i).1
  letI (i : Fin n) : (pres i).IsFinite := (presData i).2
  exact @isFinitePresentation_of_isOpenCover _ M (ULift.{u} (Fin n))
    (fun i ↦ (𝒰.f i.down).opensRange)
    (by
      rw [TopologicalSpace.IsOpenCover, iSup_ulift]
      exact 𝒰.isOpenCover_opensRange)
    (fun i ↦ pres i.down) (fun i ↦ inferInstance)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
/-- Finite presentation descends from an fpqc covering sieve on an affine scheme. -/
lemma isFinitePresentation_of_fpqc_sieve_affine {S : Scheme.{u}} [IsAffine S]
    (R : Sieve S) (hR : R ∈ Scheme.fpqcTopology S)
    (M : S.Modules) [M.IsQuasicoherent]
    (hM : ∀ {X : Scheme.{u}} (f : X ⟶ S), R.arrows f →
      ((pullback f).obj M).IsFinitePresentation) :
    M.IsFinitePresentation := by
  obtain ⟨Q, hQ, hQR⟩ :=
    Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition.mp hR
  obtain ⟨n, X, p, hX, hp, hpQ, hcover⟩ :=
    Scheme.exists_finite_affine_refinement_of_mem_fpqcPrecoverage hQ
  letI (i : Fin n) : IsAffine (X i) := hX i
  have hcoverFlat : Presieve.ofArrows X p ∈ Scheme.precoverage (@Flat) S :=
    (Scheme.propQCPrecoverage_le_precoverage (P := @Flat)) S hcover
  let C : Scheme.Cover.{0, u} (Scheme.precoverage (@Flat)) S :=
    { I₀ := Fin n
      X := X
      f := p
      mem₀ := hcoverFlat }
  let T : Scheme.{u} := ∐ X
  let q : T ⟶ S := Sigma.desc p
  letI : IsAffine T := by
    dsimp [T]
    infer_instance
  letI : Flat q := IsZariskiLocalAtSource.sigmaDesc hp
  letI : Surjective q :=
    Surjective.sigmaDesc_of_union_range_eq_univ (by
      simpa [C, q] using C.iUnion_range)
  have hqM : ((pullback q).obj M).IsFinitePresentation := by
    apply isFinitePresentation_of_sigma_pullbacks X
    intro i
    have hpR : R.arrows (p i) :=
      ((Sieve.generate_le_iff Q R).mpr hQR) _ (hpQ i)
    have hpi : ((pullback (p i)).obj M).IsFinitePresentation := hM (p i) hpR
    let e : (pullback (Sigma.ι X i)).obj ((pullback q).obj M) ≅
        (pullback (p i)).obj M :=
      (pullbackComp (Sigma.ι X i) q).app M ≪≫
        (pullbackCongr (Sigma.ι_desc p i)).app M
    exact ObjectProperty.prop_of_iso
      (P := SheafOfModules.isFinitePresentation (X i).ringCatSheaf) e.symm hpi
  exact isFinitePresentation_of_pullback_of_flat_surjective_affine q M hqM

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
/-- Finite presentation of a quasicoherent sheaf descends from an fpqc covering
sieve. -/
lemma isFinitePresentation_of_fpqc_sieve {S : Scheme.{u}}
    (R : Sieve S) (hR : R ∈ Scheme.fpqcTopology S)
    (M : S.Modules) [M.IsQuasicoherent]
    (hM : ∀ {X : Scheme.{u}} (f : X ⟶ S), R.arrows f →
      ((pullback f).obj M).IsFinitePresentation) :
    M.IsFinitePresentation := by
  let presData (U : S.affineOpens) :
      { P : SheafOfModules.Presentation (M.restrict U.1.ι) // P.IsFinite } := by
    let f := U.1.ι
    let N := (pullback f).obj M
    have hN : N.IsFinitePresentation := by
      apply isFinitePresentation_of_fpqc_sieve_affine
        (R.pullback f) (Scheme.fpqcTopology.pullback_stable f hR) N
      intro X g hg
      have hgf : R.arrows (g ≫ f) := by
        exact hg
      have hcomp : ((pullback (g ≫ f)).obj M).IsFinitePresentation :=
        hM (g ≫ f) hgf
      exact ObjectProperty.prop_of_iso
        (P := SheafOfModules.isFinitePresentation X.ringCatSheaf)
        ((pullbackComp g f).app M).symm hcomp
    let e : N ≅ M.restrict f := ((restrictFunctorIsoPullback f).app M).symm
    have hRestrict : (M.restrict f).IsFinitePresentation :=
      ObjectProperty.prop_of_iso
        (P := SheafOfModules.isFinitePresentation U.1.toScheme.ringCatSheaf) e hN
    letI : (M.restrict f).IsFinitePresentation := hRestrict
    let h := exists_finitePresentation_of_isFinitePresentation_affine (M.restrict f)
    exact ⟨Classical.choose h, Classical.choose_spec h⟩
  let pres (U : S.affineOpens) : SheafOfModules.Presentation
      (M.restrict U.1.ι) := (presData U).1
  letI (U : S.affineOpens) : (pres U).IsFinite := (presData U).2
  exact isFinitePresentation_of_isOpenCover M
    (fun U : S.affineOpens ↦ U.1) (iSup_affineOpens_eq_top S) pres

def finitePresentationProperty : quasicoherentPseudofunctor.{u}.ObjectProperty where
  prop _ M := M.obj.IsFinitePresentation

instance : finitePresentationProperty.{u}.IsClosedUnderMapObj where
  map_obj {X Y M} hM f := by
    change ((pullback f.as.unop).obj M.obj).IsFinitePresentation
    exact @isFinitePresentation_pullback _ _ f.as.unop M.obj hM

instance : finitePresentationProperty.{u}.IsClosedUnderIsomorphisms where
  isClosedUnderIsomorphisms X := by
    constructor
    intro M N e hM
    exact ObjectProperty.prop_of_iso
      (P := SheafOfModules.isFinitePresentation X.as.unop.ringCatSheaf)
      ((SheafOfModules.isQuasicoherent X.as.unop.ringCatSheaf).ι.mapIso e) hM

instance : finitePresentationProperty.{u}.IsLocal Scheme.fpqcTopology where
  of_sieve {S} R hR M hM := by
    change M.obj.IsFinitePresentation
    letI : M.obj.IsQuasicoherent := M.property
    apply isFinitePresentation_of_fpqc_sieve R hR M.obj
    intro X f hf
    let q := Presieve.categoryMk R.arrows f hf
    have hq := hM q
    change ((pullback f).obj M.obj).IsFinitePresentation at hq
    exact hq

noncomputable abbrev coherentPseudofunctor :=
  finitePresentationProperty.{u}.fullsubcategory

def finiteLocallyFreeProperty : quasicoherentPseudofunctor.{u}.ObjectProperty where
  prop _ M := IsFiniteLocallyFree M.obj

instance : finiteLocallyFreeProperty.{u}.IsClosedUnderIsomorphisms where
  isClosedUnderIsomorphisms X := by
    constructor
    intro M N e hM
    exact IsFiniteLocallyFree.of_iso
      ((SheafOfModules.isQuasicoherent X.as.unop.ringCatSheaf).ι.mapIso e) hM

instance : finiteLocallyFreeProperty.{u}.IsClosedUnderMapObj where
  map_obj {X Y M} hM f := by
    change IsFiniteLocallyFree ((Modules.pullback f.as.unop).obj M.obj)
    letI : M.obj.IsQuasicoherent := M.property
    exact hM.pullback f.as.unop

noncomputable abbrev vectorBundlePseudofunctor :=
  finiteLocallyFreeProperty.{u}.fullsubcategory

end AlgebraicGeometry.Scheme.Modules
