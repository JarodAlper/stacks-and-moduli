module

public import StacksAndModuli.API.ProjectiveQuasicoherentSectionsLocalization
public import StacksAndModuli.API.DVRGenericFiber
public import StacksAndModuli.API.FiniteProjectiveFiberRank
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Module

/-!
# Global sections on the generic open of projective space over a DVR

Let `R` be a discrete valuation ring with fraction field `K`, and let `ϖ` be a
uniformizer.  For a quasicoherent module `N` on projective space over `R`, restriction
to the base basic open `D(ϖ)` identifies its sections with localization away from `ϖ`.
Since `K = R[1/ϖ]`, this gives an explicit `K`-linear equivalence

`K ⊗[R] Γ(Pⁿ_R, N) ≃ Γ(D(ϖ), N)`.

This is the module-theoretic generic-fibre comparison used in the DVR argument for
projectivity of Hilbert and Quot.

Main declarations:

* `Scheme.Modules.pullbackSectionsSemilinearEquiv_imageTop`;
* `Scheme.Modules.projectiveSpaceFractionRingToBaseBasicOpen`;
* `Scheme.Modules.fractionRingTensorGlobalSectionsLinearEquiv_baseBasicOpen`;
* `Scheme.Modules.fractionRingTensorGlobalSectionsLinearEquiv_genericFiber`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

open CategoryTheory TopologicalSpace Opposite TensorProduct
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- For an open immersion, sections of a module on its image are semilinearly
equivalent to global sections of the pulled-back module.  The scalar equivalence is the
corresponding isomorphism on functions. -/
noncomputable def pullbackSectionsSemilinearEquiv_imageTop
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules) :
    let eR := (f.appIso ⊤).commRingCatIsoToRingEquiv
    letI : RingHomInvPair (eR : Γ(Y, f ''ᵁ ⊤) →+* Γ(X, ⊤))
        (eR.symm : Γ(X, ⊤) →+* Γ(Y, f ''ᵁ ⊤)) :=
      RingHomInvPair.of_ringEquiv eR
    letI : RingHomInvPair (eR.symm : Γ(X, ⊤) →+* Γ(Y, f ''ᵁ ⊤))
        (eR : Γ(Y, f ''ᵁ ⊤) →+* Γ(X, ⊤)) :=
      RingHomInvPair.symm _ _
    Γ(M, f ''ᵁ ⊤) ≃ₛₗ[(eR : Γ(Y, f ''ᵁ ⊤) →+* Γ(X, ⊤))]
      Γ((pullback f).obj M, ⊤) := by
  dsimp only
  let eR := (f.appIso ⊤).commRingCatIsoToRingEquiv
  letI : RingHomInvPair (eR : Γ(Y, f ''ᵁ ⊤) →+* Γ(X, ⊤))
      (eR.symm : Γ(X, ⊤) →+* Γ(Y, f ''ᵁ ⊤)) :=
    RingHomInvPair.of_ringEquiv eR
  letI : RingHomInvPair (eR.symm : Γ(X, ⊤) →+* Γ(Y, f ''ᵁ ⊤))
      (eR : Γ(Y, f ''ᵁ ⊤) →+* Γ(X, ⊤)) :=
    RingHomInvPair.symm _ _
  let e := (restrictFunctorIsoPullback f).app M
  let eTopCat : ((M.restrict f).val.obj (Opposite.op ⊤)) ≅
      (((pullback f).obj M).val.obj (Opposite.op ⊤)) :=
    { hom := e.hom.val.app (Opposite.op ⊤)
      inv := e.inv.val.app (Opposite.op ⊤)
      hom_inv_id := congrArg (fun k ↦ k.val.app (Opposite.op ⊤)) e.hom_inv_id
      inv_hom_id := congrArg (fun k ↦ k.val.app (Opposite.op ⊤)) e.inv_hom_id }
  let eRestr : Γ(M.restrict f, ⊤) ≃+ Γ(M, f ''ᵁ ⊤) :=
    { toFun := (M.restrictAppIso f ⊤).hom
      invFun := (M.restrictAppIso f ⊤).inv
      left_inv := fun m ↦ by simp
      right_inv := fun m ↦ by simp
      map_add' := fun x y ↦ map_add _ x y }
  let eAdd := eRestr.symm.trans eTopCat.toLinearEquiv.toAddEquiv
  exact
    { toEquiv := eAdd.toEquiv
      map_add' := eAdd.map_add
      map_smul' := fun r m ↦ by
        change e.hom.app ⊤ ((M.restrictAppIso f ⊤).inv (r • m)) =
          (f.appIso ⊤).hom r •
            e.hom.app ⊤ ((M.restrictAppIso f ⊤).inv m)
        rw [show (M.restrictAppIso f ⊤).inv (r • m) =
          (f.appIso ⊤).hom r • (M.restrictAppIso f ⊤).inv m by simp]
        exact eTopCat.toLinearEquiv.map_smul _ _ }

/-- The map from the fraction field of a DVR to functions on the base basic open of
projective space.  It is obtained by inverting a uniformizer, whose pullback is a unit
on its basic open. -/
noncomputable def projectiveSpaceFractionRingToBaseBasicOpen
    (n : ℕ) (R : CommRingCat.{u}) [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : Irreducible ϖ) :
    let X := Scheme.projectiveSpaceOver n (Spec R)
    let p := Scheme.projectiveSpaceOverπ n (Spec R)
    let t : Γ(X, ⊤) := (baseRingHom p).hom ϖ
    FractionRing R →+* Γ(X, X.basicOpen t) := by
  let X := Scheme.projectiveSpaceOver n (Spec R)
  let p := Scheme.projectiveSpaceOverπ n (Spec R)
  let t : Γ(X, ⊤) := (baseRingHom p).hom ϖ
  let U := X.basicOpen t
  let f : R →+* Γ(X, U) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom.comp
      (baseRingHom p).hom
  letI : IsLocalization.Away ϖ (FractionRing R) :=
    IsDiscreteValuationRing.isLocalization_away_of_irreducible hϖ _
  exact IsLocalization.Away.lift ϖ (g := f) (by
    change IsUnit ((X.presheaf.map
      (homOfLE (X.basicOpen_le t)).op).hom t)
    exact X.toRingedSpace.isUnit_res_basicOpen t)

/-- The fraction-field map to the base basic open extends the structural map from
the DVR. -/
theorem projectiveSpaceFractionRingToBaseBasicOpen_comp
    (n : ℕ) (R : CommRingCat.{u}) [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : Irreducible ϖ) :
    let X := Scheme.projectiveSpaceOver n (Spec R)
    let p := Scheme.projectiveSpaceOverπ n (Spec R)
    let t : Γ(X, ⊤) := (baseRingHom p).hom ϖ
    (projectiveSpaceFractionRingToBaseBasicOpen n R ϖ hϖ).comp
        (algebraMap R (FractionRing R)) =
      (X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom.comp
        (baseRingHom p).hom := by
  let X := Scheme.projectiveSpaceOver n (Spec R)
  let p := Scheme.projectiveSpaceOverπ n (Spec R)
  let t : Γ(X, ⊤) := (baseRingHom p).hom ϖ
  let U := X.basicOpen t
  let f : R →+* Γ(X, U) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom.comp
      (baseRingHom p).hom
  letI : IsLocalization.Away ϖ (FractionRing R) :=
    IsDiscreteValuationRing.isLocalization_away_of_irreducible hϖ _
  have hf : IsUnit (f ϖ) := by
    change IsUnit ((X.presheaf.map
      (homOfLE (X.basicOpen_le t)).op).hom t)
    exact X.toRingedSpace.isUnit_res_basicOpen t
  change (IsLocalization.Away.lift ϖ hf).comp
    (algebraMap R (FractionRing R)) = f
  exact IsLocalization.Away.lift_comp ϖ hf

/-- The generic-fibre open immersion into projective space over a DVR has image the
base basic open of any uniformizer. -/
theorem projectiveSpaceGenericFiber_opensRange
    (n : ℕ) (R : CommRingCat.{u}) [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : Irreducible ϖ) :
    let X := Scheme.projectiveSpaceOver n (Spec R)
    let p := Scheme.projectiveSpaceOverπ n (Spec R)
    let j₀ := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    let j := Limits.pullback.fst p j₀
    letI : IsOpenImmersion j₀ :=
      IsDiscreteValuationRing.isOpenImmersion_specMap_fractionRing (FractionRing R)
    letI : IsOpenImmersion j := inferInstance
    let t : Γ(X, ⊤) := (baseRingHom p).hom ϖ
    j.opensRange = X.basicOpen t := by
  dsimp only
  let X := Scheme.projectiveSpaceOver n (Spec R)
  let p := Scheme.projectiveSpaceOverπ n (Spec R)
  let j₀ := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  let j := Limits.pullback.fst p j₀
  let t : Γ(X, ⊤) := (baseRingHom p).hom ϖ
  letI : IsOpenImmersion j₀ :=
    IsDiscreteValuationRing.isOpenImmersion_specMap_fractionRing (FractionRing R)
  rw [Scheme.Hom.opensRange_pullbackFst,
    IsDiscreteValuationRing.opensRange_specMap_fractionRing hϖ (FractionRing R)]
  exact Scheme.preimage_basicOpen_top p
    ((Scheme.ΓSpecIso R).inv.hom ϖ)

/-- The raw scheme-theoretic generic fibre of projective space is canonically
projective space over the fraction field. -/
noncomputable def projectiveSpaceGenericFiberIso
    (n : ℕ) (R : CommRingCat.{u}) [IsDomain R] [IsDiscreteValuationRing R] :
    let p := Scheme.projectiveSpaceOverπ n (Spec R)
    let j₀ := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    Limits.pullback p j₀ ≅
      Scheme.projectiveSpaceOver n (Spec (CommRingCat.of (FractionRing R))) :=
  Limits.pullbackSymmetry _ _ ≪≫
    Scheme.projectiveSpaceOverBaseChangeIso n
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))

@[reassoc (attr := simp)]
theorem projectiveSpaceGenericFiberIso_hom_map
    (n : ℕ) (R : CommRingCat.{u}) [IsDomain R] [IsDiscreteValuationRing R] :
    let p := Scheme.projectiveSpaceOverπ n (Spec R)
    let j₀ := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    (projectiveSpaceGenericFiberIso n R).hom ≫
        Scheme.projectiveSpaceOverMap n j₀ =
      Limits.pullback.fst p j₀ := by
  dsimp only
  unfold projectiveSpaceGenericFiberIso
  rw [Iso.trans_hom, Category.assoc,
    Scheme.projectiveSpaceOverBaseChangeIso_hom_map]
  exact Limits.pullbackSymmetry_hom_comp_snd _ _

@[reassoc (attr := simp)]
theorem projectiveSpaceGenericFiberIso_inv_fst
    (n : ℕ) (R : CommRingCat.{u}) [IsDomain R] [IsDiscreteValuationRing R] :
    let p := Scheme.projectiveSpaceOverπ n (Spec R)
    let j₀ := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    (projectiveSpaceGenericFiberIso n R).inv ≫
        Limits.pullback.fst p j₀ =
      Scheme.projectiveSpaceOverMap n j₀ := by
  dsimp only
  rw [← cancel_epi (projectiveSpaceGenericFiberIso n R).hom]
  simp

/-- Pulling a module from the raw generic fibre across
`projectiveSpaceGenericFiberIso` agrees with the usual projective-space base change. -/
noncomputable def pullbackProjectiveSpaceGenericFiberIso
    (n : ℕ) (R : CommRingCat.{u}) [IsDomain R] [IsDiscreteValuationRing R]
    (N : (Scheme.projectiveSpaceOver n (Spec R)).Modules) :
    let p := Scheme.projectiveSpaceOverπ n (Spec R)
    let j₀ := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    let j := Limits.pullback.fst p j₀
    (pullback (projectiveSpaceGenericFiberIso n R).inv).obj
        ((pullback j).obj N) ≅
      (pullback (Scheme.projectiveSpaceOverMap n j₀)).obj N :=
  (pullbackComp (projectiveSpaceGenericFiberIso n R).inv
      (Limits.pullback.fst
        (Scheme.projectiveSpaceOverπ n (Spec R))
        (Spec.map (CommRingCat.ofHom
          (algebraMap R (FractionRing R)))))).app N ≪≫
    (pullbackCongr (projectiveSpaceGenericFiberIso_inv_fst n R)).app N

/-- For a quasicoherent module on projective space over a DVR, tensoring global
sections with the fraction field is the same as restricting sections to the base
basic open of a uniformizer. -/
noncomputable def fractionRingTensorGlobalSectionsLinearEquiv_baseBasicOpen
    (n : ℕ) (R : CommRingCat.{u}) [IsDomain R] [IsDiscreteValuationRing R]
    (N : (Scheme.projectiveSpaceOver n (Spec R)).Modules) [N.IsQuasicoherent]
    (ϖ : R) (hϖ : Irreducible ϖ) :
    let X := Scheme.projectiveSpaceOver n (Spec R)
    let p := Scheme.projectiveSpaceOverπ n (Spec R)
    let t : Γ(X, ⊤) := (baseRingHom p).hom ϖ
    let U := X.basicOpen t
    letI : Module R Γ(N, ⊤) := globalSectionsModule p N
    letI : Algebra R Γ(X, U) :=
      ((X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom.comp
        (baseRingHom p).hom).toAlgebra
    letI : Algebra (FractionRing R) Γ(X, U) :=
      (projectiveSpaceFractionRingToBaseBasicOpen n R ϖ hϖ).toAlgebra
    letI : Module (FractionRing R) Γ(N, U) :=
      Module.compHom Γ(N, U) (algebraMap (FractionRing R) Γ(X, U))
    (FractionRing R ⊗[R] Γ(N, ⊤)) ≃ₗ[FractionRing R] Γ(N, U) := by
  let X := Scheme.projectiveSpaceOver n (Spec R)
  let p := Scheme.projectiveSpaceOverπ n (Spec R)
  let t : Γ(X, ⊤) := (baseRingHom p).hom ϖ
  let U := X.basicOpen t
  letI : Algebra R Γ(X, ⊤) := globalSectionsAlgebra p
  letI : Module R Γ(N, ⊤) := globalSectionsModule p N
  letI : Algebra R Γ(X, U) :=
    ((X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom.comp
      (baseRingHom p).hom).toAlgebra
  letI : Algebra (FractionRing R) Γ(X, U) :=
    (projectiveSpaceFractionRingToBaseBasicOpen n R ϖ hϖ).toAlgebra
  letI : IsScalarTower R (FractionRing R) Γ(X, U) :=
    IsScalarTower.of_algebraMap_eq'
      (projectiveSpaceFractionRingToBaseBasicOpen_comp n R ϖ hϖ).symm
  letI : Module (FractionRing R) Γ(N, U) :=
    Module.compHom Γ(N, U) (algebraMap (FractionRing R) Γ(X, U))
  letI : Module Γ(X, ⊤) Γ(N, U) := Module.compHom Γ(N, U)
    (X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom
  letI : Module R Γ(N, U) := Module.compHom Γ(N, U) (baseRingHom p).hom
  letI : IsScalarTower R Γ(X, ⊤) Γ(N, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : IsScalarTower R Γ(X, ⊤) Γ(N, U) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : IsScalarTower R (FractionRing R) Γ(N, U) :=
    IsScalarTower.of_algebraMap_smul fun r x ↦ by
      change (algebraMap (FractionRing R) Γ(X, U)
        (algebraMap R (FractionRing R) r)) • x =
          (X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom
            ((baseRingHom p).hom r) • x
      rw [← IsScalarTower.algebraMap_apply R (FractionRing R) Γ(X, U)]
      rfl
  letI : IsLocalization.Away ϖ (FractionRing R) :=
    IsDiscreteValuationRing.isLocalization_away_of_irreducible hϖ _
  haveI : IsLocalizedModule (Submonoid.powers ϖ)
      ((resBasicOpenLinearMap N t).restrictScalars R) :=
    isLocalizedModule_projectiveSpace_resBaseBasicOpen n R N ϖ
  let e := IsLocalizedModule.linearEquiv (Submonoid.powers ϖ)
    (TensorProduct.mk R (FractionRing R) Γ(N, ⊤) 1)
    ((resBasicOpenLinearMap N t).restrictScalars R)
  exact e.extendScalarsOfIsLocalization (Submonoid.powers ϖ) (FractionRing R)

/-- The fraction field acts on the functions of the scheme-theoretic generic fibre of
projective space.  The action is obtained by identifying the generic-fibre image with
the base basic open and then pulling functions back along the open immersion. -/
noncomputable def projectiveSpaceFractionRingToGenericFiber
    (n : ℕ) (R : CommRingCat.{u}) [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : Irreducible ϖ) :
    let p := Scheme.projectiveSpaceOverπ n (Spec R)
    let j₀ := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    let j := Limits.pullback.fst p j₀
    letI : IsOpenImmersion j₀ :=
      IsDiscreteValuationRing.isOpenImmersion_specMap_fractionRing (FractionRing R)
    letI : IsOpenImmersion j := inferInstance
    FractionRing R →+* Γ(Limits.pullback p j₀, ⊤) := by
  dsimp only
  let X := Scheme.projectiveSpaceOver n (Spec R)
  let p := Scheme.projectiveSpaceOverπ n (Spec R)
  let j₀ := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  let j := Limits.pullback.fst p j₀
  letI : IsOpenImmersion j₀ :=
    IsDiscreteValuationRing.isOpenImmersion_specMap_fractionRing (FractionRing R)
  letI : IsOpenImmersion j := inferInstance
  let t : Γ(X, ⊤) := (baseRingHom p).hom ϖ
  let U := X.basicOpen t
  have hU : j ''ᵁ ⊤ = U :=
    j.image_top_eq_opensRange.trans
      (projectiveSpaceGenericFiber_opensRange n R ϖ hϖ)
  letI : Algebra (FractionRing R) Γ(X, U) :=
    (projectiveSpaceFractionRingToBaseBasicOpen n R ϖ hϖ).toAlgebra
  let a : FractionRing R →+* Γ(X, U) :=
    algebraMap (FractionRing R) Γ(X, U)
  let g : FractionRing R →+* Γ(X, j ''ᵁ ⊤) := hU.symm ▸ a
  exact (j.appIso ⊤).hom.hom.comp g

/-- Pulling back a global function along an open immersion can be computed by first
restricting it to the image and then transporting that restriction across an equality
identifying the image with a chosen open. -/
theorem appIso_hom_cast_resTop
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (U : Y.Opens) (hU : f ''ᵁ (⊤ : X.Opens) = U) (s : Γ(Y, ⊤)) :
    (f.appIso ⊤).hom
        (hU.symm ▸ Y.presheaf.map (homOfLE (by rw [← hU]; exact le_top)).op s) =
      f.appTop s := by
  subst U
  rw [f.appIso_hom']
  change f.appLE (f ''ᵁ ⊤) ⊤ _
      (Y.presheaf.map (homOfLE (by exact le_top)).op s) = f.appTop s
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE]
  rw [show f.appLE ⊤ ⊤ _ = f.appTop by
    convert f.appLE_eq_app using 1 <;> simp]

/-- Applying a ring homomorphism after transporting its codomain across an equality of
opens is the same as transporting its value. -/
theorem castRingHom_apply
    {K : Type u} [CommRing K] {X : Scheme.{u}} {U V : X.Opens}
    (h : U = V) (a : K →+* Γ(X, U)) (k : K) :
    (h ▸ a) k = h ▸ a k := by
  subst V
  rfl

/-- The explicitly localized fraction-field action on functions of the generic fibre is
the intrinsic action induced by its structure morphism to the fraction field. -/
theorem projectiveSpaceFractionRingToGenericFiber_eq_baseRingHom
    (n : ℕ) (R : CommRingCat.{u}) [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : Irreducible ϖ) :
    let p := Scheme.projectiveSpaceOverπ n (Spec R)
    let j₀ := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    let j := Limits.pullback.fst p j₀
    letI : IsOpenImmersion j₀ :=
      IsDiscreteValuationRing.isOpenImmersion_specMap_fractionRing (FractionRing R)
    letI : IsOpenImmersion j := inferInstance
    projectiveSpaceFractionRingToGenericFiber n R ϖ hϖ =
      (baseRingHom (Limits.pullback.snd p j₀)).hom := by
  dsimp only
  let X := Scheme.projectiveSpaceOver n (Spec R)
  let p := Scheme.projectiveSpaceOverπ n (Spec R)
  let j₀ := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  let j := Limits.pullback.fst p j₀
  letI : IsOpenImmersion j₀ :=
    IsDiscreteValuationRing.isOpenImmersion_specMap_fractionRing (FractionRing R)
  letI : IsOpenImmersion j := inferInstance
  let t : Γ(X, ⊤) := (baseRingHom p).hom ϖ
  let U := X.basicOpen t
  have hU : j ''ᵁ ⊤ = U :=
    j.image_top_eq_opensRange.trans
      (projectiveSpaceGenericFiber_opensRange n R ϖ hϖ)
  have hrhs :
      (baseRingHom (Limits.pullback.snd p j₀)).hom.comp
          (algebraMap R (FractionRing R)) =
        j.appTop.hom.comp (baseRingHom p).hom := by
    calc
      (baseRingHom (Limits.pullback.snd p j₀)).hom.comp
          (algebraMap R (FractionRing R)) =
          (baseRingHom (Limits.pullback.snd p j₀ ≫ j₀)).hom := by
            exact congrArg CommRingCat.Hom.hom
              (baseRingHom_comp
                (CommRingCat.ofHom (algebraMap R (FractionRing R)))
                (Limits.pullback.snd p j₀))
      _ = (baseRingHom (j ≫ p)).hom := by
        rw [Limits.pullback.condition]
      _ = j.appTop.hom.comp (baseRingHom p).hom := by
        ext r
        rfl
  apply IsLocalization.ringHom_ext (nonZeroDivisors R)
  ext r
  simp only [RingHom.comp_apply]
  dsimp [projectiveSpaceFractionRingToGenericFiber]
  simp only [RingHom.algebraMap_toAlgebra]
  change _ = (baseRingHom (Limits.pullback.snd p j₀)).hom
    ((algebraMap R (FractionRing R)) r)
  have hr := RingHom.congr_fun hrhs r
  change (baseRingHom (Limits.pullback.snd p j₀)).hom
      ((algebraMap R (FractionRing R)) r) =
    j.appTop ((baseRingHom p).hom r) at hr
  rw [hr, castRingHom_apply]
  change (j.appIso ⊤).hom
      (hU.symm ▸ projectiveSpaceFractionRingToBaseBasicOpen n R ϖ hϖ
        ((algebraMap R (FractionRing R)) r)) =
    j.appTop ((baseRingHom p).hom r)
  have hopen := RingHom.congr_fun
    (projectiveSpaceFractionRingToBaseBasicOpen_comp n R ϖ hϖ) r
  change projectiveSpaceFractionRingToBaseBasicOpen n R ϖ hϖ
      ((algebraMap R (FractionRing R)) r) =
    X.presheaf.map (homOfLE (X.basicOpen_le t)).op ((baseRingHom p).hom r) at hopen
  rw [hopen]
  exact appIso_hom_cast_resTop j U hU ((baseRingHom p).hom r)

/-- Transporting sections across an equality of opens commutes with scalar
multiplication when the scalar map is transported across the same equality. -/
theorem castSections_smul
    {K : Type u} [CommRing K] {X : Scheme.{u}} (N : X.Modules)
    {U V : X.Opens} (h : U = V) (a : K →+* Γ(X, U)) (k : K) (m : Γ(N, U)) :
    let b : K →+* Γ(X, V) := h ▸ a
    letI : Module K Γ(N, U) := Module.compHom _ a
    letI : Module K Γ(N, V) := Module.compHom _ b
    AddEquiv.cast (congrArg (fun W : X.Opens ↦ Γ(N, W)) h) (k • m) =
      k • AddEquiv.cast (congrArg (fun W : X.Opens ↦ Γ(N, W)) h) m := by
  subst V
  rfl

/-- Generic-fibre base change for global sections of an arbitrary quasicoherent module
on projective space over a DVR.  The target is the global sections of the genuine
scheme-theoretic pullback to `Spec (FractionRing R)`. -/
noncomputable def fractionRingTensorGlobalSectionsLinearEquiv_genericFiber
    (n : ℕ) (R : CommRingCat.{u}) [IsDomain R] [IsDiscreteValuationRing R]
    (N : (Scheme.projectiveSpaceOver n (Spec R)).Modules) [N.IsQuasicoherent]
    (ϖ : R) (hϖ : Irreducible ϖ) :
    let p := Scheme.projectiveSpaceOverπ n (Spec R)
    let j₀ := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    let XK := Limits.pullback p j₀
    let j := Limits.pullback.fst p j₀
    letI : IsOpenImmersion j₀ :=
      IsDiscreteValuationRing.isOpenImmersion_specMap_fractionRing (FractionRing R)
    letI : IsOpenImmersion j := inferInstance
    letI : Module R Γ(N, ⊤) := globalSectionsModule p N
    letI : Algebra (FractionRing R) Γ(XK, ⊤) :=
      (projectiveSpaceFractionRingToGenericFiber n R ϖ hϖ).toAlgebra
    letI : Module (FractionRing R) Γ((pullback j).obj N, ⊤) :=
      Module.compHom _ (algebraMap (FractionRing R) Γ(XK, ⊤))
    (FractionRing R ⊗[R] Γ(N, ⊤)) ≃ₗ[FractionRing R]
      Γ((pullback j).obj N, ⊤) := by
  dsimp only
  let X := Scheme.projectiveSpaceOver n (Spec R)
  let p := Scheme.projectiveSpaceOverπ n (Spec R)
  let j₀ := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  let XK := Limits.pullback p j₀
  let j := Limits.pullback.fst p j₀
  letI : IsOpenImmersion j₀ :=
    IsDiscreteValuationRing.isOpenImmersion_specMap_fractionRing (FractionRing R)
  letI : IsOpenImmersion j := inferInstance
  letI : Module R Γ(N, ⊤) := globalSectionsModule p N
  letI : Algebra (FractionRing R) Γ(XK, ⊤) :=
    (projectiveSpaceFractionRingToGenericFiber n R ϖ hϖ).toAlgebra
  letI : Module (FractionRing R) Γ((pullback j).obj N, ⊤) :=
    Module.compHom _ (algebraMap (FractionRing R) Γ(XK, ⊤))
  let t : Γ(X, ⊤) := (baseRingHom p).hom ϖ
  let U := X.basicOpen t
  have hU : j ''ᵁ ⊤ = U :=
    j.image_top_eq_opensRange.trans
      (projectiveSpaceGenericFiber_opensRange n R ϖ hϖ)
  letI : Algebra (FractionRing R) Γ(X, U) :=
    (projectiveSpaceFractionRingToBaseBasicOpen n R ϖ hϖ).toAlgebra
  letI : Module (FractionRing R) Γ(N, U) :=
    Module.compHom _ (algebraMap (FractionRing R) Γ(X, U))
  let a : FractionRing R →+* Γ(X, U) :=
    algebraMap (FractionRing R) Γ(X, U)
  let g : FractionRing R →+* Γ(X, j ''ᵁ ⊤) := hU.symm ▸ a
  letI : Algebra (FractionRing R) Γ(X, j ''ᵁ ⊤) := g.toAlgebra
  letI : Module (FractionRing R) Γ(N, j ''ᵁ ⊤) :=
    Module.compHom _ g
  let e₁U := fractionRingTensorGlobalSectionsLinearEquiv_baseBasicOpen
    n R N ϖ hϖ
  let eCast : Γ(N, U) ≃+ Γ(N, j ''ᵁ ⊤) :=
    AddEquiv.cast (congrArg (fun V : X.Opens ↦ Γ(N, V)) hU.symm)
  let e₁Add := e₁U.toAddEquiv.trans eCast
  let e₁ : (FractionRing R ⊗[R] Γ(N, ⊤)) ≃ₗ[FractionRing R]
      Γ(N, j ''ᵁ ⊤) :=
    { toEquiv := e₁Add.toEquiv
      map_add' := e₁Add.map_add
      map_smul' := fun k m ↦ by
        change eCast (e₁U (k • m)) = k • eCast (e₁U m)
        rw [e₁U.map_smul]
        exact castSections_smul N hU.symm a k (e₁U m) }
  let eR := (j.appIso ⊤).commRingCatIsoToRingEquiv
  letI : RingHomInvPair (eR : Γ(X, j ''ᵁ ⊤) →+* Γ(XK, ⊤))
      (eR.symm : Γ(XK, ⊤) →+* Γ(X, j ''ᵁ ⊤)) :=
    RingHomInvPair.of_ringEquiv eR
  letI : RingHomInvPair (eR.symm : Γ(XK, ⊤) →+* Γ(X, j ''ᵁ ⊤))
      (eR : Γ(X, j ''ᵁ ⊤) →+* Γ(XK, ⊤)) :=
    RingHomInvPair.symm _ _
  let e₂semi := pullbackSectionsSemilinearEquiv_imageTop j N
  let e₂ : Γ(N, j ''ᵁ ⊤) ≃ₗ[FractionRing R]
      Γ((pullback j).obj N, ⊤) :=
    { toEquiv := e₂semi.toEquiv
      map_add' := e₂semi.map_add
      map_smul' := fun k m ↦ by
        change e₂semi (g k • m) =
          (j.appIso ⊤).hom (g k) • e₂semi m
        exact e₂semi.map_smulₛₗ (g k) m }
  exact e₁.trans e₂

/-- If the relative global sections are finite projective over the DVR, their rank is
the vector-space dimension of the global sections on the scheme-theoretic generic
fibre. -/
theorem finrank_genericFiber_globalSections_eq
    (n : ℕ) (R : CommRingCat.{u}) [IsDomain R] [IsDiscreteValuationRing R]
    (N : (Scheme.projectiveSpaceOver n (Spec R)).Modules) [N.IsQuasicoherent]
    (ϖ : R) (hϖ : Irreducible ϖ)
    (hfinite :
      letI : Module R Γ(N, ⊤) := globalSectionsModule
        (Scheme.projectiveSpaceOverπ n (Spec R)) N
      Module.Finite R Γ(N, ⊤))
    (hprojective :
      letI : Module R Γ(N, ⊤) := globalSectionsModule
        (Scheme.projectiveSpaceOverπ n (Spec R)) N
      Module.Projective R Γ(N, ⊤)) :
    let p := Scheme.projectiveSpaceOverπ n (Spec R)
    let j₀ := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    let XK := Limits.pullback p j₀
    let j := Limits.pullback.fst p j₀
    letI : IsOpenImmersion j₀ :=
      IsDiscreteValuationRing.isOpenImmersion_specMap_fractionRing (FractionRing R)
    letI : IsOpenImmersion j := inferInstance
    letI : Module R Γ(N, ⊤) := globalSectionsModule p N
    letI : Algebra (FractionRing R) Γ(XK, ⊤) :=
      (projectiveSpaceFractionRingToGenericFiber n R ϖ hϖ).toAlgebra
    letI : Module (FractionRing R) Γ((pullback j).obj N, ⊤) :=
      Module.compHom _ (algebraMap (FractionRing R) Γ(XK, ⊤))
    Module.finrank (FractionRing R) Γ((pullback j).obj N, ⊤) =
      Module.finrank R Γ(N, ⊤) := by
  dsimp only
  let p := Scheme.projectiveSpaceOverπ n (Spec R)
  let j₀ := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  let XK := Limits.pullback p j₀
  let j := Limits.pullback.fst p j₀
  letI : IsOpenImmersion j₀ :=
    IsDiscreteValuationRing.isOpenImmersion_specMap_fractionRing (FractionRing R)
  letI : IsOpenImmersion j := inferInstance
  letI : Module R Γ(N, ⊤) := globalSectionsModule p N
  letI : Module.Finite R Γ(N, ⊤) := hfinite
  letI : Module.Projective R Γ(N, ⊤) := hprojective
  letI : Algebra (FractionRing R) Γ(XK, ⊤) :=
    (projectiveSpaceFractionRingToGenericFiber n R ϖ hϖ).toAlgebra
  letI : Module (FractionRing R) Γ((pullback j).obj N, ⊤) :=
    Module.compHom _ (algebraMap (FractionRing R) Γ(XK, ⊤))
  rw [← (fractionRingTensorGlobalSectionsLinearEquiv_genericFiber
    n R N ϖ hϖ).finrank_eq]
  exact Module.finrank_tensorProduct_eq_of_finite_projective_of_isLocalRing

end AlgebraicGeometry.Scheme.Modules

end
