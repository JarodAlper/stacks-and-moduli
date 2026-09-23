module

public import StacksAndModuli.API.SchemeModulesGlobalSectionsIso
public import StacksAndModuli.«Section2.1-Intro».«part2.1.0-pullback-quasicoherent»
public import Mathlib.RingTheory.Flat.Equalizer

/-!
# Affine and Čech tools for flat base change of global sections

Supporting API for flat base change of degree-zero cohomology.  Sections of a module
sheaf over an open cover are expressed as the equalizer of the two restriction maps.
Flat tensor product preserves that equalizer.  On an affine cartesian square,
quasicoherent pullback is identified with extension of scalars, first for spectra of a
pushout square of rings and then for arbitrary affine schemes.

These are the local and algebraic ingredients in the standard affine-cover proof that
global sections of a quasicoherent sheaf on projective space commute with extension of
the ground field.

Main declarations:

* `Scheme.Modules.sectionsLinearEquivCompatibleEqLocus`;
* `LinearMap.tensorEqLocusTransportedEquiv`;
* `pullbackQuasicoherentSectionsLinearEquiv_of_ring_isPushout`;
* `affinePullbackSectionsBaseChangeLinearEquiv`.
-/

@[expose] public section

set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory TopologicalSpace Opposite TensorProduct
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {R : Type u} [CommRing R]

/-- The map from a base ring to functions on an open of a scheme over that base. -/
noncomputable def openBaseRingHom (p : X ⟶ Spec (.of R)) (U : X.Opens) :
    R →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE le_top).op).hom.comp (baseRingHom p).hom

/-- Sections on an open of a scheme over `Spec R`, regarded as an `R`-module. -/
@[instance_reducible]
noncomputable def openSectionsModule (p : X ⟶ Spec (.of R))
    (M : X.Modules) (U : X.Opens) : Module R Γ(M, U) :=
  Module.compHom _ (openBaseRingHom p U)

variable {I : Type u}

/-- The first restriction map from a family of local sections to pairwise overlaps. -/
noncomputable def compatibleFamilyLeft (p : X ⟶ Spec (.of R))
    (M : X.Modules) (U : I → X.Opens) :
    letI (i : I) := openSectionsModule p M (U i)
    letI (ij : I × I) := openSectionsModule p M (U ij.1 ⊓ U ij.2)
    (∀ i, Γ(M, U i)) →ₗ[R] (∀ ij : I × I, Γ(M, U ij.1 ⊓ U ij.2)) := by
  letI (i : I) := openSectionsModule p M (U i)
  letI (ij : I × I) := openSectionsModule p M (U ij.1 ⊓ U ij.2)
  refine LinearMap.pi (fun ij ↦ ?_)
  exact
    { toFun := fun s ↦ M.presheaf.map (homOfLE inf_le_left).op (s ij.1)
      map_add' := fun x y ↦ (M.presheaf.map _).hom.map_add _ _
      map_smul' := by
        intro r s
        change M.presheaf.map
            (homOfLE (show U ij.1 ⊓ U ij.2 ≤ U ij.1 from inf_le_left)).op
            ((X.presheaf.map (homOfLE (show U ij.1 ≤ ⊤ from le_top)).op
              ((baseRingHom p).hom r)) • s ij.1) = _
        rw [M.map_smul]
        congr 1
        rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
        rfl }

/-- The second restriction map from a family of local sections to pairwise overlaps. -/
noncomputable def compatibleFamilyRight (p : X ⟶ Spec (.of R))
    (M : X.Modules) (U : I → X.Opens) :
    letI (i : I) := openSectionsModule p M (U i)
    letI (ij : I × I) := openSectionsModule p M (U ij.1 ⊓ U ij.2)
    (∀ i, Γ(M, U i)) →ₗ[R] (∀ ij : I × I, Γ(M, U ij.1 ⊓ U ij.2)) := by
  letI (i : I) := openSectionsModule p M (U i)
  letI (ij : I × I) := openSectionsModule p M (U ij.1 ⊓ U ij.2)
  refine LinearMap.pi (fun ij ↦ ?_)
  exact
    { toFun := fun s ↦ M.presheaf.map (homOfLE inf_le_right).op (s ij.2)
      map_add' := fun x y ↦ (M.presheaf.map _).hom.map_add _ _
      map_smul' := by
        intro r s
        change M.presheaf.map
            (homOfLE (show U ij.1 ⊓ U ij.2 ≤ U ij.2 from inf_le_right)).op
            ((X.presheaf.map (homOfLE (show U ij.2 ≤ ⊤ from le_top)).op
              ((baseRingHom p).hom r)) • s ij.2) = _
        rw [M.map_smul]
        congr 1
        rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
        rfl }

/-- Restriction from global sections to the equalizer of the two overlap maps. -/
noncomputable def restrictTopToCompatibleEqLocus (p : X ⟶ Spec (.of R))
    (M : X.Modules) (U : I → X.Opens) :
    letI := globalSectionsModule p M
    letI (i : I) := openSectionsModule p M (U i)
    letI (ij : I × I) := openSectionsModule p M (U ij.1 ⊓ U ij.2)
    Γ(M, ⊤) →ₗ[R] LinearMap.eqLocus
      (compatibleFamilyLeft p M U) (compatibleFamilyRight p M U) := by
  letI := globalSectionsModule p M
  letI (i : I) := openSectionsModule p M (U i)
  letI (ij : I × I) := openSectionsModule p M (U ij.1 ⊓ U ij.2)
  let res (i : I) : Γ(M, ⊤) →ₗ[R] Γ(M, U i) :=
    { toFun := fun s ↦ M.presheaf.map (homOfLE le_top).op s
      map_add' := fun s t ↦ map_add _ _ _
      map_smul' := by
        intro r s
        change M.presheaf.map (homOfLE (show U i ≤ ⊤ from le_top)).op
            ((baseRingHom p).hom r • s) = _
        rw [M.map_smul]
        change _ = (openBaseRingHom p (U i)) r •
          (M.presheaf.map (homOfLE (show U i ≤ ⊤ from le_top)).op s : Γ(M, U i))
        rfl }
  let resAll : Γ(M, ⊤) →ₗ[R] (∀ i, Γ(M, U i)) := LinearMap.pi res
  refine resAll.codRestrict _ ?_
  intro s
  ext ij
  change M.presheaf.map _ (M.presheaf.map _ s) =
    M.presheaf.map _ (M.presheaf.map _ s)
  rw [← M.presheaf.map_comp_apply, ← M.presheaf.map_comp_apply]
  rfl

/-- Restriction to a covering family is a bijection from global sections to compatible
families. -/
theorem restrictTopToCompatibleEqLocus_bijective (p : X ⟶ Spec (.of R))
    (M : X.Modules) (U : I → X.Opens) (hU : ⨆ i, U i = ⊤) :
    letI := globalSectionsModule p M
    letI (i : I) := openSectionsModule p M (U i)
    letI (ij : I × I) := openSectionsModule p M (U ij.1 ⊓ U ij.2)
    Function.Bijective (restrictTopToCompatibleEqLocus p M U) := by
  let F : TopCat.Sheaf AddCommGrpCat X := ⟨M.presheaf, M.isSheaf⟩
  constructor
  · intro s t hst
    apply F.eq_of_locally_eq' U ⊤ (fun _ ↦ homOfLE le_top) (by rw [hU])
    intro i
    have hi := congrArg (fun z ↦ z.1 i) hst
    change M.presheaf.map (homOfLE (show U i ≤ ⊤ from le_top)).op s =
      M.presheaf.map (homOfLE (show U i ≤ ⊤ from le_top)).op t at hi
    exact hi
  · intro s
    obtain ⟨x, hx, -⟩ := F.existsUnique_gluing' U ⊤ (fun _ ↦ homOfLE le_top)
      (by rw [hU]) s.1 (by
        intro i j
        exact congrFun s.2 (i, j))
    refine ⟨x, ?_⟩
    apply Subtype.ext
    funext i
    change M.presheaf.map (homOfLE (show U i ≤ ⊤ from le_top)).op x = s.1 i
    exact hx i

/-- Sections on a covered scheme form the equalizer of the two restriction maps to
pairwise intersections. -/
noncomputable def sectionsLinearEquivCompatibleEqLocus (p : X ⟶ Spec (.of R))
    (M : X.Modules) (U : I → X.Opens) (hU : ⨆ i, U i = ⊤) :
    letI := globalSectionsModule p M
    letI (i : I) := openSectionsModule p M (U i)
    letI (ij : I × I) := openSectionsModule p M (U ij.1 ⊓ U ij.2)
    Γ(M, ⊤) ≃ₗ[R] LinearMap.eqLocus
      (compatibleFamilyLeft p M U) (compatibleFamilyRight p M U) := by
  letI := globalSectionsModule p M
  letI (i : I) := openSectionsModule p M (U i)
  letI (ij : I × I) := openSectionsModule p M (U ij.1 ⊓ U ij.2)
  exact LinearEquiv.ofBijective (restrictTopToCompatibleEqLocus p M U)
    (restrictTopToCompatibleEqLocus_bijective p M U hU)

end AlgebraicGeometry.Scheme.Modules

namespace LinearMap

variable {S : Type u} [CommRing S]
variable {A B A' B' : Type u}
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup A'] [AddCommGroup B']
variable [Module S A] [Module S B] [Module S A'] [Module S B']

/-- Equivalent source and target modules identify the equalizers of two intertwined
pairs of linear maps. -/
noncomputable def eqLocusLinearEquivOfIntertwining
    (f g : A →ₗ[S] B) (f' g' : A' →ₗ[S] B')
    (eA : A ≃ₗ[S] A') (eB : B ≃ₗ[S] B')
    (hf : eB.toLinearMap.comp f = f'.comp eA.toLinearMap)
    (hg : eB.toLinearMap.comp g = g'.comp eA.toLinearMap) :
    eqLocus f g ≃ₗ[S] eqLocus f' g' where
  toFun x := ⟨eA x, by
    change (f'.comp eA.toLinearMap) x = (g'.comp eA.toLinearMap) x
    rw [← hf, ← hg]
    change eB (f x) = eB (g x)
    exact congrArg eB x.property⟩
  invFun y := ⟨eA.symm y, by
    apply eB.injective
    change (eB.toLinearMap.comp f) (eA.symm y) =
      (eB.toLinearMap.comp g) (eA.symm y)
    rw [hf, hg]
    change f' (eA (eA.symm y)) = g' (eA (eA.symm y))
    rw [eA.apply_symm_apply]
    exact y.property⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_add' x y := by ext; simp
  map_smul' r x := by ext; simp

variable {R : Type u} [CommRing R] [Algebra R S]
variable {N P : Type u} [AddCommGroup N] [AddCommGroup P]
variable [Module R N] [Module R P]

/-- Flat tensor product preserves an equalizer, with the source and target tensor
products subsequently transported through chosen linear equivalences. -/
noncomputable def tensorEqLocusTransportedEquiv [Module.Flat R S]
    (f g : N →ₗ[R] P)
    {N' P' : Type u} [AddCommGroup N'] [AddCommGroup P']
    [Module S N'] [Module S P']
    (eN : (S ⊗[R] N) ≃ₗ[S] N') (eP : (S ⊗[R] P) ≃ₗ[S] P') :
    S ⊗[R] eqLocus f g ≃ₗ[S]
      eqLocus
        (eP.toLinearMap.comp (AlgebraTensorModule.lTensor S S f) |>.comp eN.symm.toLinearMap)
        (eP.toLinearMap.comp (AlgebraTensorModule.lTensor S S g) |>.comp eN.symm.toLinearMap) :=
  tensorEqLocusEquiv S S f g ≪≫ₗ
    eqLocusLinearEquivOfIntertwining
      (AlgebraTensorModule.lTensor S S f)
      (AlgebraTensorModule.lTensor S S g)
      (eP.toLinearMap.comp (AlgebraTensorModule.lTensor S S f) |>.comp eN.symm.toLinearMap)
      (eP.toLinearMap.comp (AlgebraTensorModule.lTensor S S g) |>.comp eN.symm.toLinearMap)
      eN eP (by ext; simp) (by ext; simp)

end LinearMap

namespace AlgebraicGeometry

/-- For a pushout square of rings, global sections of the affine pullback of a
quasicoherent module are extension of scalars across the other side of the square. -/
noncomputable def pullbackQuasicoherentSectionsLinearEquiv_of_ring_isPushout
    {R S A B : CommRingCat.{u}} (f : R ⟶ A) (g : R ⟶ S)
    (fst : A ⟶ B) (snd : S ⟶ B) (h : IsPushout f g fst snd)
    (M : (Spec A).Modules) [M.IsQuasicoherent] :
    let Q := moduleSpecΓFunctor.obj M
    let N := moduleSpecΓFunctor.obj
      ((Scheme.Modules.pullback (Spec.map fst)).obj M)
    letI : Algebra R S := g.hom.toAlgebra
    letI := Module.compHom Q f.hom
    letI := Module.compHom N snd.hom
    N ≃ₗ[S] S ⊗[R] Q := by
  letI : Algebra R A := f.hom.toAlgebra
  letI : Algebra R S := g.hom.toAlgebra
  letI : Algebra A B := fst.hom.toAlgebra
  letI : Algebra S B := snd.hom.toAlgebra
  letI : Algebra R B := (fst.hom.comp f.hom).toAlgebra
  letI : IsScalarTower R A B :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hw : fst.hom.comp f.hom = snd.hom.comp g.hom :=
    congrArg CommRingCat.Hom.hom h.w
  letI : IsScalarTower R S B :=
    IsScalarTower.of_algebraMap_eq fun x ↦ DFunLike.congr_fun hw x
  have hp : IsPushout
      (CommRingCat.ofHom (algebraMap R S)) (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap S B)) (CommRingCat.ofHom (algebraMap A B)) := by
    change IsPushout g f snd fst
    exact h.flip
  letI : Algebra.IsPushout R S A B :=
    CommRingCat.isPushout_iff_isPushout.mp hp
  let Q := moduleSpecΓFunctor.obj M
  letI : Module R Q := Module.compHom Q f.hom
  letI : IsScalarTower R A Q :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let N := moduleSpecΓFunctor.obj
    ((Scheme.Modules.pullback (Spec.map fst)).obj M)
  letI : Module S N := Module.compHom N snd.hom
  let T := (ModuleCat.extendScalars (algebraMap A B)).obj Q
  letI : Module S T := Module.compHom T (algebraMap S B)
  letI : IsScalarTower S B T :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let B' := (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)
  letI : IsScalarTower A B B' :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let eB : B' ≃ₗ[B] B :=
    { toEquiv := Equiv.refl _
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let eB' := TensorProduct.AlgebraTensorModule.congr eB (LinearEquiv.refl A Q)
  letI : Module S (TensorProduct A B' Q) :=
    Module.compHom _ (algebraMap S B)
  letI : IsScalarTower S B (TensorProduct A B' Q) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let eT : T ≃ₗ[S] TensorProduct A B Q := eB'.restrictScalars S
  let ePullB := pullbackQuasicoherentSectionsLinearEquiv fst M
  let ePull : N ≃ₗ[S] T :=
    { toEquiv := ePullB.toEquiv
      map_add' := ePullB.map_add
      map_smul' := fun s x ↦ by
        change ePullB ((algebraMap S B s) • x) =
          (algebraMap S B s) • ePullB x
        exact ePullB.map_smul (algebraMap S B s) x }
  exact ePull.trans eT |>.trans (Algebra.IsPushout.cancelBaseChange R S A B Q)

/-- Pulling a module from an affine scheme to its canonical spectrum preserves its
global sections as modules over any external coefficient ring. -/
noncomputable def pullbackIsoSpecInvSectionsLinearEquiv
    {R₀ : Type u} [CommRing R₀] {X : Scheme.{u}} [IsAffine X]
    (a : R₀ →+* Γ(X, ⊤)) (M : X.Modules) :
    let Mspec := (Scheme.Modules.pullback X.isoSpec.inv).obj M
    letI : Module R₀ Γ(M, ⊤) := Module.compHom _ a
    letI : Module R₀ (moduleSpecΓFunctor.obj Mspec) := Module.compHom _ a
    Γ(M, ⊤) ≃ₗ[R₀] moduleSpecΓFunctor.obj Mspec := by
  let Mspec := (Scheme.Modules.pullback X.isoSpec.inv).obj M
  letI : Module R₀ Γ(M, ⊤) := Module.compHom _ a
  letI : Module R₀ (moduleSpecΓFunctor.obj Mspec) := Module.compHom _ a
  let e := Scheme.Modules.pullbackGlobalSectionsViaIsoAddEquiv
    X.isoSpec.inv M (Iso.refl Mspec)
  exact
    { toEquiv := e.toEquiv
      map_add' := e.map_add
      map_smul' := by
        intro r m
        change e (a r • m) = a r • e m
        change _root_.Scheme.Modules.pullbackGlobalSections X.isoSpec.inv M
            (a r • m) = a r •
              _root_.Scheme.Modules.pullbackGlobalSections X.isoSpec.inv M m
        rw [Scheme.Modules.pullbackGlobalSections_smul]
        have hi : X.isoSpec.inv.appTop =
            (Scheme.ΓSpecIso Γ(X, ⊤)).inv := by
          rw [← cancel_mono X.isoSpec.hom.appTop, ← Scheme.Hom.comp_appTop]
          simp [Scheme.isoSpec]
        rw [hi]
        rfl }

/-- In a cartesian square of affine schemes, global sections of a pulled-back
quasicoherent module are the tensor base change of the original global sections. -/
noncomputable def affinePullbackSectionsBaseChangeLinearEquiv
    {P X Y Z : Scheme.{u}} [IsAffine P] [IsAffine X] [IsAffine Y] [IsAffine Z]
    (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : IsPullback fst snd f g) (M : X.Modules) [M.IsQuasicoherent] :
    let N := (Scheme.Modules.pullback fst).obj M
    letI : Algebra Γ(Z, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
    letI : Module Γ(Z, ⊤) Γ(M, ⊤) := Module.compHom _ f.appTop.hom
    letI : Module Γ(Y, ⊤) Γ(N, ⊤) := Module.compHom _ snd.appTop.hom
    Γ(N, ⊤) ≃ₗ[Γ(Y, ⊤)] Γ(Y, ⊤) ⊗[Γ(Z, ⊤)] Γ(M, ⊤) := by
  let N := (Scheme.Modules.pullback fst).obj M
  letI : Algebra Γ(Z, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
  letI : Module Γ(Z, ⊤) Γ(M, ⊤) := Module.compHom _ f.appTop.hom
  letI : Module Γ(Y, ⊤) Γ(N, ⊤) := Module.compHom _ snd.appTop.hom
  let Mspec := (Scheme.Modules.pullback X.isoSpec.inv).obj M
  letI : Mspec.IsQuasicoherent := by
    letI : IsOpenImmersion X.isoSpec.inv := inferInstance
    let e := (Scheme.Modules.restrictFunctorIsoPullback X.isoSpec.inv).app M
    exact (SheafOfModules.isQuasicoherent (Spec Γ(X, ⊤)).ringCatSheaf).prop_of_iso
      e inferInstance
  let Aff := (Scheme.Modules.pullback (Spec.map fst.appTop)).obj Mspec
  let Nspec := (Scheme.Modules.pullback P.isoSpec.inv).obj N
  letI : Module Γ(Z, ⊤) (moduleSpecΓFunctor.obj Mspec) :=
    Module.compHom _ f.appTop.hom
  letI : Module Γ(Y, ⊤) (moduleSpecΓFunctor.obj Aff) :=
    Module.compHom _ snd.appTop.hom
  letI : Module Γ(Y, ⊤) (moduleSpecΓFunctor.obj Nspec) :=
    Module.compHom _ snd.appTop.hom
  letI : Algebra Γ(Y, ⊤) Γ(P, ⊤) := snd.appTop.hom.toAlgebra
  letI : IsScalarTower Γ(Y, ⊤) Γ(P, ⊤) (moduleSpecΓFunctor.obj Aff) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : IsScalarTower Γ(Y, ⊤) Γ(P, ⊤) (moduleSpecΓFunctor.obj Nspec) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let eSheaf : Aff ≅ (Scheme.Modules.pullback P.isoSpec.inv).obj N :=
    pullbackAffineIsoSpecIso fst M
  let hring : IsPushout f.appTop g.appTop fst.appTop snd.appTop :=
    isPushout_appTop_of_isPullback h
  let eAff := pullbackQuasicoherentSectionsLinearEquiv_of_ring_isPushout
    f.appTop g.appTop fst.appTop snd.appTop hring Mspec
  let eM := pullbackIsoSpecInvSectionsLinearEquiv f.appTop.hom M
  let eNspec := pullbackIsoSpecInvSectionsLinearEquiv snd.appTop.hom N
  let eSheafSections : moduleSpecΓFunctor.obj Nspec ≃ₗ[Γ(Y, ⊤)]
      moduleSpecΓFunctor.obj Aff :=
    (moduleSpecΓFunctor.mapIso eSheaf.symm).toLinearEquiv.restrictScalars Γ(Y, ⊤)
  let eN := eNspec.trans eSheafSections
  exact eN.trans eAff |>.trans
    (TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl Γ(Y, ⊤) Γ(Y, ⊤)) eM.symm)

end AlgebraicGeometry
