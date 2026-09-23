module

public import StacksAndModuli.API.AffineCechGlobalSectionsBaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Flat base change of global sections from a finite affine cover

This file packages the canonical scalar-extension maps on sections and a finite
Čech equalizer argument.  If the canonical maps are bijective on every member of
a finite cover and on every pairwise overlap, flatness of the scalar extension
implies that the canonical map on global sections is bijective.

Main declarations:

* `Scheme.Modules.pullbackOpenSectionsBaseChangeLinearMap`;
* `Scheme.Modules.pullbackGlobalSectionsBaseChangeLinearMap`;
* `Scheme.Modules.pullbackGlobalSectionsBaseChangeLinearMap_bijective_of_finiteCover`;
* `Scheme.Modules.pullbackGlobalSectionsBaseChangeLinearEquiv_of_finiteCover`.
-/

@[expose] public section

set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory TopologicalSpace Opposite TensorProduct
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

/-- The canonical scalar-extension map from sections on an open to sections of
the pulled-back module on its inverse image. -/
noncomputable def pullbackOpenSectionsBaseChangeLinearMap
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (pX : X ⟶ Spec R) (pY : Y ⟶ Spec S)
    (h : g ≫ pX = pY ≫ Spec.map φ) (M : X.Modules) (U : X.Opens) :
    let V := g ⁻¹ᵁ U
    let N := (Scheme.Modules.pullback g).obj M
    letI : Algebra R S := φ.hom.toAlgebra
    letI : Module R Γ(M, U) := Scheme.Modules.openSectionsModule pX M U
    letI : Module S Γ(N, V) := Scheme.Modules.openSectionsModule pY N V
    S ⊗[R] Γ(M, U) →ₗ[S] Γ(N, V) := by
  let V := g ⁻¹ᵁ U
  let N := (Scheme.Modules.pullback g).obj M
  letI : Algebra R S := φ.hom.toAlgebra
  letI : Module R Γ(M, U) := Scheme.Modules.openSectionsModule pX M U
  letI : Module S Γ(N, V) := Scheme.Modules.openSectionsModule pY N V
  have hscalar (r : R) : (g.app U).hom
        (Scheme.Modules.openBaseRingHom pX U r) =
      Scheme.Modules.openBaseRingHom pY V (φ.hom r) := by
    have hbase : Scheme.Modules.baseRingHom pX ≫ g.appTop =
        φ ≫ Scheme.Modules.baseRingHom pY := by
      rw [Scheme.Modules.baseRingHom_comp_appTop, h,
        ← Scheme.Modules.baseRingHom_comp]
    have htop := congrArg (fun k ↦ k.hom r) hbase
    have hnat := CategoryTheory.congr_fun
      (g.naturality (homOfLE (show U ≤ ⊤ from le_top)).op)
      ((Scheme.Modules.baseRingHom pX).hom r)
    rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at hnat
    change g.appTop.hom ((Scheme.Modules.baseRingHom pX).hom r) =
      (Scheme.Modules.baseRingHom pY).hom (φ.hom r) at htop
    have hscalar' : g.app U
          (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
            ((Scheme.Modules.baseRingHom pX).hom r)) =
        Y.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
          ((Scheme.Modules.baseRingHom pY).hom (φ.hom r)) := by
      calc
        _ = Y.presheaf.map
            (((Opens.map g.base).map
              (homOfLE (show U ≤ ⊤ from le_top)).op.unop).op)
            (g.appTop.hom ((Scheme.Modules.baseRingHom pX).hom r)) := hnat
        _ = _ := by
          rw [htop]
          congr 1
    exact hscalar'
  let sourceOpenRingHom : R →+* Γ(Y, V) :=
    (g.app U).hom.comp (Scheme.Modules.openBaseRingHom pX U)
  letI : Module R Γ(N, V) := Module.compHom _ sourceOpenRingHom
  letI : IsScalarTower R S Γ(N, V) :=
    IsScalarTower.of_algebraMap_smul fun r m ↦ by
      change Scheme.Modules.openBaseRingHom pY V (φ.hom r) • m =
        (g.app U).hom (Scheme.Modules.openBaseRingHom pX U r) • m
      rw [hscalar]
  let unitSection : Γ(M, U) →ₗ[R] Γ(N, V) :=
    { toFun := fun m ↦
        ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app U m
      map_add' := fun m n ↦ map_add _ m n
      map_smul' := by
        intro r m
        change ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app U
          (Scheme.Modules.openBaseRingHom pX U r • m) =
          (g.app U).hom (Scheme.Modules.openBaseRingHom pX U r) •
            (show Γ(N, V) from
              ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app U m)
        exact Scheme.Modules.Hom.app_smul
          ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M)
          (Scheme.Modules.openBaseRingHom pX U r) m }
  let b : S →ₗ[S] Γ(M, U) →ₗ[R] Γ(N, V) :=
    { toFun := fun s ↦
        { toFun := fun m ↦ s • unitSection m
          map_add' := fun m n ↦ by rw [map_add, smul_add]
          map_smul' := fun r m ↦ by
            rw [unitSection.map_smul]
            exact smul_comm s r (unitSection m) }
      map_add' := fun s t ↦ by ext m; exact add_smul s t _
      map_smul' := fun s t ↦ by ext m; exact mul_smul s t _ }
  exact TensorProduct.AlgebraTensorModule.lift b

@[simp]
lemma pullbackOpenSectionsBaseChangeLinearMap_tmul
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (pX : X ⟶ Spec R) (pY : Y ⟶ Spec S)
    (h : g ≫ pX = pY ≫ Spec.map φ) (M : X.Modules) (U : X.Opens)
    (s : S) (m : Γ(M, U)) :
    let V := g ⁻¹ᵁ U
    let N := (Scheme.Modules.pullback g).obj M
    letI : Algebra R S := φ.hom.toAlgebra
    letI : Module R Γ(M, U) := Scheme.Modules.openSectionsModule pX M U
    letI : Module S Γ(N, V) := Scheme.Modules.openSectionsModule pY N V
    pullbackOpenSectionsBaseChangeLinearMap φ g pX pY h M U (s ⊗ₜ[R] m) =
      s • (show Γ(N, V) from
        ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app U m) := by
  simp [pullbackOpenSectionsBaseChangeLinearMap]

/-- Restriction between two opens, viewed as a linear map over a chosen affine
base. -/
noncomputable def Scheme.Modules.openRestrictionLinearMap
    {R : CommRingCat.{u}} {X : Scheme.{u}} (p : X ⟶ Spec R)
    (M : X.Modules) {V U : X.Opens} (hVU : V ≤ U) :
    letI : Module R Γ(M, U) := Scheme.Modules.openSectionsModule p M U
    letI : Module R Γ(M, V) := Scheme.Modules.openSectionsModule p M V
    Γ(M, U) →ₗ[R] Γ(M, V) := by
  letI : Module R Γ(M, U) := Scheme.Modules.openSectionsModule p M U
  letI : Module R Γ(M, V) := Scheme.Modules.openSectionsModule p M V
  exact
    { toFun := fun m ↦ M.presheaf.map (homOfLE hVU).op m
      map_add' := fun m n ↦ map_add _ m n
      map_smul' := by
        intro r m
        change M.presheaf.map (homOfLE hVU).op
            ((X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
              ((Scheme.Modules.baseRingHom p).hom r)) • m) = _
        rw [M.map_smul]
        change _ = (Scheme.Modules.openBaseRingHom p V r) •
          M.presheaf.map (homOfLE hVU).op m
        congr 1
        rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
        rfl }

@[simp]
lemma Scheme.Modules.openRestrictionLinearMap_apply
    {R : CommRingCat.{u}} {X : Scheme.{u}} (p : X ⟶ Spec R)
    (M : X.Modules) {V U : X.Opens} (hVU : V ≤ U) (m : Γ(M, U)) :
    letI : Module R Γ(M, U) := Scheme.Modules.openSectionsModule p M U
    letI : Module R Γ(M, V) := Scheme.Modules.openSectionsModule p M V
    Scheme.Modules.openRestrictionLinearMap p M hVU m =
      M.presheaf.map (homOfLE hVU).op m := rfl

/-- Canonical base-change maps on open sections commute with restriction. -/
lemma pullbackOpenSectionsBaseChangeLinearMap_restrict
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (pX : X ⟶ Spec R) (pY : Y ⟶ Spec S)
    (h : g ≫ pX = pY ≫ Spec.map φ) (M : X.Modules)
    {W U : X.Opens} (hWU : W ≤ U) :
    let VU := g ⁻¹ᵁ U
    let VW := g ⁻¹ᵁ W
    let N := (Scheme.Modules.pullback g).obj M
    let hVWVU : VW ≤ VU := fun _ hx ↦ hWU hx
    letI : Algebra R S := φ.hom.toAlgebra
    letI : Module R Γ(M, U) := Scheme.Modules.openSectionsModule pX M U
    letI : Module R Γ(M, W) := Scheme.Modules.openSectionsModule pX M W
    letI : Module S Γ(N, VU) := Scheme.Modules.openSectionsModule pY N VU
    letI : Module S Γ(N, VW) := Scheme.Modules.openSectionsModule pY N VW
    (Scheme.Modules.openRestrictionLinearMap pY N hVWVU).comp
        (pullbackOpenSectionsBaseChangeLinearMap φ g pX pY h M U) =
      (pullbackOpenSectionsBaseChangeLinearMap φ g pX pY h M W).comp
        (TensorProduct.AlgebraTensorModule.map LinearMap.id
          (Scheme.Modules.openRestrictionLinearMap pX M hWU)) := by
  dsimp only
  let N := (Scheme.Modules.pullback g).obj M
  letI : Algebra R S := φ.hom.toAlgebra
  letI : Module R Γ(M, U) := Scheme.Modules.openSectionsModule pX M U
  letI : Module R Γ(M, W) := Scheme.Modules.openSectionsModule pX M W
  letI : Module S Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ U) :=
    Scheme.Modules.openSectionsModule pY _ _
  letI : Module S Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ W) :=
    Scheme.Modules.openSectionsModule pY _ _
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s m =>
      simp only [LinearMap.comp_apply,
        TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply,
        pullbackOpenSectionsBaseChangeLinearMap_tmul,
        Scheme.Modules.openRestrictionLinearMap_apply, map_smul]
      have hnat := CategoryTheory.congr_fun
        (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).mapPresheaf.naturality
          (homOfLE hWU).op) m
      rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at hnat
      exact congrArg (s • ·) hnat.symm

/-- The canonical scalar-extension map on global sections for a morphism over a
map of affine bases. -/
noncomputable def Scheme.Modules.pullbackGlobalSectionsBaseChangeLinearMap
    {R S : CommRingCat.{u}} (φ : R ⟶ S) {X Y : Scheme.{u}}
    (g : Y ⟶ X) (pX : X ⟶ Spec R) (pY : Y ⟶ Spec S)
    (h : g ≫ pX = pY ≫ Spec.map φ) (M : X.Modules) :
    let N := (Scheme.Modules.pullback g).obj M
    letI : Algebra R S := φ.hom.toAlgebra
    letI : Module R Γ(M, ⊤) := Scheme.Modules.globalSectionsModule pX M
    letI : Module S Γ(N, ⊤) := Scheme.Modules.globalSectionsModule pY N
    S ⊗[R] Γ(M, ⊤) →ₗ[S] Γ(N, ⊤) := by
  let N := (Scheme.Modules.pullback g).obj M
  letI : Algebra R S := φ.hom.toAlgebra
  letI : Module R Γ(M, ⊤) := Scheme.Modules.globalSectionsModule pX M
  letI : Module S Γ(N, ⊤) := Scheme.Modules.globalSectionsModule pY N
  let sourceRingHom : R →+* Γ(Y, ⊤) :=
    g.appTop.hom.comp (Scheme.Modules.baseRingHom pX).hom
  letI : Module R Γ(N, ⊤) := Module.compHom _ sourceRingHom
  have hbase : Scheme.Modules.baseRingHom pX ≫ g.appTop =
      φ ≫ Scheme.Modules.baseRingHom pY := by
    rw [Scheme.Modules.baseRingHom_comp_appTop, h,
      ← Scheme.Modules.baseRingHom_comp]
  letI : IsScalarTower R S Γ(N, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun r m ↦ by
      change (Scheme.Modules.baseRingHom pY).hom (φ.hom r) • m =
        g.appTop.hom ((Scheme.Modules.baseRingHom pX).hom r) • m
      rw [show g.appTop.hom ((Scheme.Modules.baseRingHom pX).hom r) =
          (Scheme.Modules.baseRingHom pY).hom (φ.hom r) by
        simpa only [← CommRingCat.comp_apply] using
          congrArg (fun k : R ⟶ Γ(Y, ⊤) ↦ k.hom r) hbase]
  let unitSection : Γ(M, ⊤) →ₗ[R] Γ(N, ⊤) :=
    { toFun := Scheme.Modules.pullbackGlobalSections g M
      map_add' := fun m n ↦ map_add _ m n
      map_smul' := by
        intro r m
        change Scheme.Modules.pullbackGlobalSections g M
            ((Scheme.Modules.baseRingHom pX).hom r • m) =
          g.appTop.hom ((Scheme.Modules.baseRingHom pX).hom r) •
            Scheme.Modules.pullbackGlobalSections g M m
        exact Scheme.Modules.pullbackGlobalSections_smul g M _ _ }
  let bilinear : S →ₗ[S] Γ(M, ⊤) →ₗ[R] Γ(N, ⊤) :=
    { toFun := fun s ↦
        { toFun := fun m ↦ s • unitSection m
          map_add' := fun m n ↦ by rw [map_add, smul_add]
          map_smul' := fun r m ↦ by
            rw [unitSection.map_smul]
            exact smul_comm s r (unitSection m) }
      map_add' := fun s t ↦ by ext m; exact add_smul s t _
      map_smul' := fun s t ↦ by ext m; exact mul_smul s t _ }
  exact TensorProduct.AlgebraTensorModule.lift bilinear

@[simp]
lemma Scheme.Modules.pullbackGlobalSectionsBaseChangeLinearMap_tmul
    {R S : CommRingCat.{u}} (φ : R ⟶ S) {X Y : Scheme.{u}}
    (g : Y ⟶ X) (pX : X ⟶ Spec R) (pY : Y ⟶ Spec S)
    (h : g ≫ pX = pY ≫ Spec.map φ) (M : X.Modules)
    (s : S) (m : Γ(M, ⊤)) :
    let N := (Scheme.Modules.pullback g).obj M
    letI : Algebra R S := φ.hom.toAlgebra
    letI : Module R Γ(M, ⊤) := Scheme.Modules.globalSectionsModule pX M
    letI : Module S Γ(N, ⊤) := Scheme.Modules.globalSectionsModule pY N
    Scheme.Modules.pullbackGlobalSectionsBaseChangeLinearMap
        φ g pX pY h M (s ⊗ₜ[R] m) =
      s • Scheme.Modules.pullbackGlobalSections g M m := by
  simp [Scheme.Modules.pullbackGlobalSectionsBaseChangeLinearMap]

/-- Restriction from global sections to one open, as a map over the chosen base
ring. -/
noncomputable def Scheme.Modules.globalToOpenRestrictionLinearMap
    {R : CommRingCat.{u}} {X : Scheme.{u}} (p : X ⟶ Spec R)
    (M : X.Modules) (U : X.Opens) :
    letI : Module R Γ(M, ⊤) := Scheme.Modules.globalSectionsModule p M
    letI : Module R Γ(M, U) := Scheme.Modules.openSectionsModule p M U
    Γ(M, ⊤) →ₗ[R] Γ(M, U) := by
  letI : Module R Γ(M, ⊤) := Scheme.Modules.globalSectionsModule p M
  letI : Module R Γ(M, U) := Scheme.Modules.openSectionsModule p M U
  exact
    { toFun := fun m ↦ M.presheaf.map (homOfLE le_top).op m
      map_add' := fun m n ↦ map_add _ m n
      map_smul' := by
        intro r m
        change M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
            ((Scheme.Modules.baseRingHom p).hom r • m) = _
        rw [M.map_smul]
        rfl }

@[simp]
lemma Scheme.Modules.globalToOpenRestrictionLinearMap_apply
    {R : CommRingCat.{u}} {X : Scheme.{u}} (p : X ⟶ Spec R)
    (M : X.Modules) (U : X.Opens) (m : Γ(M, ⊤)) :
    letI : Module R Γ(M, ⊤) := Scheme.Modules.globalSectionsModule p M
    letI : Module R Γ(M, U) := Scheme.Modules.openSectionsModule p M U
    Scheme.Modules.globalToOpenRestrictionLinearMap p M U m =
      M.presheaf.map (homOfLE le_top).op m := rfl

/-- The canonical global base-change map commutes with restriction to every
open. -/
lemma Scheme.Modules.pullbackGlobalSectionsBaseChangeLinearMap_restrict
    {R S : CommRingCat.{u}} (φ : R ⟶ S) {X Y : Scheme.{u}}
    (g : Y ⟶ X) (pX : X ⟶ Spec R) (pY : Y ⟶ Spec S)
    (h : g ≫ pX = pY ≫ Spec.map φ) (M : X.Modules) (U : X.Opens) :
    let V := g ⁻¹ᵁ U
    let N := (Scheme.Modules.pullback g).obj M
    letI : Algebra R S := φ.hom.toAlgebra
    letI : Module R Γ(M, ⊤) := Scheme.Modules.globalSectionsModule pX M
    letI : Module R Γ(M, U) := Scheme.Modules.openSectionsModule pX M U
    letI : Module S Γ(N, ⊤) := Scheme.Modules.globalSectionsModule pY N
    letI : Module S Γ(N, V) := Scheme.Modules.openSectionsModule pY N V
    (Scheme.Modules.globalToOpenRestrictionLinearMap pY N V).comp
        (Scheme.Modules.pullbackGlobalSectionsBaseChangeLinearMap
          φ g pX pY h M) =
      (pullbackOpenSectionsBaseChangeLinearMap φ g pX pY h M U).comp
        (TensorProduct.AlgebraTensorModule.map LinearMap.id
          (Scheme.Modules.globalToOpenRestrictionLinearMap pX M U)) := by
  dsimp only
  let N := (Scheme.Modules.pullback g).obj M
  letI : Algebra R S := φ.hom.toAlgebra
  letI : Module R Γ(M, ⊤) := Scheme.Modules.globalSectionsModule pX M
  letI : Module R Γ(M, U) := Scheme.Modules.openSectionsModule pX M U
  letI : Module S Γ(N, ⊤) := Scheme.Modules.globalSectionsModule pY N
  letI : Module S Γ(N, g ⁻¹ᵁ U) :=
    Scheme.Modules.openSectionsModule pY N _
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s m =>
      change Scheme.Modules.globalToOpenRestrictionLinearMap pY N (g ⁻¹ᵁ U)
          (Scheme.Modules.pullbackGlobalSectionsBaseChangeLinearMap
            φ g pX pY h M (s ⊗ₜ[R] m)) =
        pullbackOpenSectionsBaseChangeLinearMap φ g pX pY h M U
          (TensorProduct.AlgebraTensorModule.map LinearMap.id
            (Scheme.Modules.globalToOpenRestrictionLinearMap pX M U)
              (s ⊗ₜ[R] m))
      rw [Scheme.Modules.pullbackGlobalSectionsBaseChangeLinearMap_tmul]
      rw [(Scheme.Modules.globalToOpenRestrictionLinearMap
        pY N (g ⁻¹ᵁ U)).map_smul]
      rw [TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply]
      rw [pullbackOpenSectionsBaseChangeLinearMap_tmul]
      rw [Scheme.Modules.globalToOpenRestrictionLinearMap_apply]
      have hnat := CategoryTheory.congr_fun
        (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).mapPresheaf.naturality
          (homOfLE (show U ≤ (⊤ : X.Opens) from le_top)).op) m
      rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at hnat
      exact congrArg (s • ·) hnat.symm

/-- Tensoring a finite family of section modules and then applying the canonical
local base-change maps componentwise. -/
noncomputable def Scheme.Modules.pullbackOpenSectionsBaseChangePiLinearEquiv
    {I : Type u} [Fintype I] [DecidableEq I]
    {R S : CommRingCat.{u}} (φ : R ⟶ S) {X Y : Scheme.{u}}
    (g : Y ⟶ X) (pX : X ⟶ Spec R) (pY : Y ⟶ Spec S)
    (h : g ≫ pX = pY ≫ Spec.map φ) (M : X.Modules) (U : I → X.Opens)
    (hbij : ∀ i, Function.Bijective
      (pullbackOpenSectionsBaseChangeLinearMap φ g pX pY h M (U i))) :
    let N := (Scheme.Modules.pullback g).obj M
    letI : Algebra R S := φ.hom.toAlgebra
    letI (i : I) : Module R Γ(M, U i) :=
      Scheme.Modules.openSectionsModule pX M (U i)
    letI (i : I) : Module S Γ(N, g ⁻¹ᵁ U i) :=
      Scheme.Modules.openSectionsModule pY N (g ⁻¹ᵁ U i)
    S ⊗[R] (∀ i, Γ(M, U i)) ≃ₗ[S]
      (∀ i, Γ(N, g ⁻¹ᵁ U i)) := by
  let N := (Scheme.Modules.pullback g).obj M
  letI : Algebra R S := φ.hom.toAlgebra
  letI (i : I) : Module R Γ(M, U i) :=
    Scheme.Modules.openSectionsModule pX M (U i)
  letI (i : I) : Module S Γ(N, g ⁻¹ᵁ U i) :=
    Scheme.Modules.openSectionsModule pY N (g ⁻¹ᵁ U i)
  exact (TensorProduct.piRight R S S (fun i ↦ Γ(M, U i))).trans
    (LinearEquiv.piCongrRight fun i ↦ LinearEquiv.ofBijective
      (pullbackOpenSectionsBaseChangeLinearMap φ g pX pY h M (U i))
      (hbij i))

@[simp]
lemma Scheme.Modules.pullbackOpenSectionsBaseChangePiLinearEquiv_tmul_apply
    {I : Type u} [Fintype I] [DecidableEq I]
    {R S : CommRingCat.{u}} (φ : R ⟶ S) {X Y : Scheme.{u}}
    (g : Y ⟶ X) (pX : X ⟶ Spec R) (pY : Y ⟶ Spec S)
    (h : g ≫ pX = pY ≫ Spec.map φ) (M : X.Modules) (U : I → X.Opens)
    (hbij : ∀ i, Function.Bijective
      (pullbackOpenSectionsBaseChangeLinearMap φ g pX pY h M (U i)))
    (s : S) (m : ∀ i, Γ(M, U i)) (i : I) :
    let N := (Scheme.Modules.pullback g).obj M
    letI : Algebra R S := φ.hom.toAlgebra
    letI (i : I) : Module R Γ(M, U i) :=
      Scheme.Modules.openSectionsModule pX M (U i)
    letI (i : I) : Module S Γ(N, g ⁻¹ᵁ U i) :=
      Scheme.Modules.openSectionsModule pY N (g ⁻¹ᵁ U i)
    Scheme.Modules.pullbackOpenSectionsBaseChangePiLinearEquiv
        φ g pX pY h M U hbij (s ⊗ₜ[R] m) i =
      pullbackOpenSectionsBaseChangeLinearMap
        φ g pX pY h M (U i) (s ⊗ₜ[R] m i) := by
  simp [Scheme.Modules.pullbackOpenSectionsBaseChangePiLinearEquiv,
    LinearEquiv.piCongrRight]

lemma Scheme.Modules.pullbackOpenSectionsBaseChangePiLinearEquiv_intertwines_left
    {I : Type u} [Fintype I] [DecidableEq I]
    {R S : CommRingCat.{u}} (φ : R ⟶ S) {X Y : Scheme.{u}}
    (g : Y ⟶ X) (pX : X ⟶ Spec R) (pY : Y ⟶ Spec S)
    (h : g ≫ pX = pY ≫ Spec.map φ) (M : X.Modules) (U : I → X.Opens)
    (hbij : ∀ i, Function.Bijective
      (pullbackOpenSectionsBaseChangeLinearMap φ g pX pY h M (U i)))
    (hbij2 : ∀ ij : I × I, Function.Bijective
      (pullbackOpenSectionsBaseChangeLinearMap
        φ g pX pY h M (U ij.1 ⊓ U ij.2))) :
    let N := (Scheme.Modules.pullback g).obj M
    let V := fun i ↦ g ⁻¹ᵁ U i
    let U2 := fun ij : I × I ↦ U ij.1 ⊓ U ij.2
    letI : Algebra R S := φ.hom.toAlgebra
    letI (i : I) : Module R Γ(M, U i) :=
      Scheme.Modules.openSectionsModule pX M (U i)
    letI (ij : I × I) : Module R Γ(M, U2 ij) :=
      Scheme.Modules.openSectionsModule pX M (U2 ij)
    letI (i : I) : Module S Γ(N, V i) :=
      Scheme.Modules.openSectionsModule pY N (V i)
    letI (ij : I × I) : Module S Γ(N, g ⁻¹ᵁ U2 ij) :=
      Scheme.Modules.openSectionsModule pY N (g ⁻¹ᵁ U2 ij)
    letI (ij : I × I) : Module S Γ(N, V ij.1 ⊓ V ij.2) :=
      Scheme.Modules.openSectionsModule pY N (V ij.1 ⊓ V ij.2)
    (Scheme.Modules.pullbackOpenSectionsBaseChangePiLinearEquiv
        φ g pX pY h M U2 hbij2).toLinearMap.comp
      (TensorProduct.AlgebraTensorModule.lTensor S S
        (Scheme.Modules.compatibleFamilyLeft pX M U)) =
      (Scheme.Modules.compatibleFamilyLeft pY N V).comp
        (Scheme.Modules.pullbackOpenSectionsBaseChangePiLinearEquiv
          φ g pX pY h M U hbij).toLinearMap := by
  dsimp only
  let N := (Scheme.Modules.pullback g).obj M
  let V := fun i ↦ g ⁻¹ᵁ U i
  let U2 := fun ij : I × I ↦ U ij.1 ⊓ U ij.2
  letI : Algebra R S := φ.hom.toAlgebra
  letI (i : I) : Module R Γ(M, U i) :=
    Scheme.Modules.openSectionsModule pX M (U i)
  letI (ij : I × I) : Module R Γ(M, U2 ij) :=
    Scheme.Modules.openSectionsModule pX M (U2 ij)
  letI (i : I) : Module S Γ(N, V i) :=
    Scheme.Modules.openSectionsModule pY N (V i)
  letI (ij : I × I) : Module S Γ(N, g ⁻¹ᵁ U2 ij) :=
    Scheme.Modules.openSectionsModule pY N (g ⁻¹ᵁ U2 ij)
  letI (ij : I × I) : Module S Γ(N, V ij.1 ⊓ V ij.2) :=
    Scheme.Modules.openSectionsModule pY N (V ij.1 ⊓ V ij.2)
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s m =>
      change
        Scheme.Modules.pullbackOpenSectionsBaseChangePiLinearEquiv
            φ g pX pY h M U2 hbij2
            (TensorProduct.AlgebraTensorModule.lTensor S S
              (Scheme.Modules.compatibleFamilyLeft pX M U) (s ⊗ₜ[R] m)) =
          Scheme.Modules.compatibleFamilyLeft pY N V
            (Scheme.Modules.pullbackOpenSectionsBaseChangePiLinearEquiv
              φ g pX pY h M U hbij (s ⊗ₜ[R] m))
      ext ij
      change pullbackOpenSectionsBaseChangeLinearMap
          φ g pX pY h M (U ij.1 ⊓ U ij.2)
            (s ⊗ₜ[R] Scheme.Modules.openRestrictionLinearMap pX M
              (show U ij.1 ⊓ U ij.2 ≤ U ij.1 from inf_le_left) (m ij.1)) =
        Scheme.Modules.openRestrictionLinearMap pY N
            (show V ij.1 ⊓ V ij.2 ≤ V ij.1 from inf_le_left)
          (pullbackOpenSectionsBaseChangeLinearMap
            φ g pX pY h M (U ij.1) (s ⊗ₜ[R] m ij.1))
      have hnat := congrArg
        (fun k ↦ k (s ⊗ₜ[R] m ij.1))
        (pullbackOpenSectionsBaseChangeLinearMap_restrict
          φ g pX pY h M (show U ij.1 ⊓ U ij.2 ≤ U ij.1 from inf_le_left))
      convert hnat.symm using 1 <;>
        simp only [LinearMap.comp_apply,
          TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply, N]
      all_goals congr 1

lemma Scheme.Modules.pullbackOpenSectionsBaseChangePiLinearEquiv_intertwines_right
    {I : Type u} [Fintype I] [DecidableEq I]
    {R S : CommRingCat.{u}} (φ : R ⟶ S) {X Y : Scheme.{u}}
    (g : Y ⟶ X) (pX : X ⟶ Spec R) (pY : Y ⟶ Spec S)
    (h : g ≫ pX = pY ≫ Spec.map φ) (M : X.Modules) (U : I → X.Opens)
    (hbij : ∀ i, Function.Bijective
      (pullbackOpenSectionsBaseChangeLinearMap φ g pX pY h M (U i)))
    (hbij2 : ∀ ij : I × I, Function.Bijective
      (pullbackOpenSectionsBaseChangeLinearMap
        φ g pX pY h M (U ij.1 ⊓ U ij.2))) :
    let N := (Scheme.Modules.pullback g).obj M
    let V := fun i ↦ g ⁻¹ᵁ U i
    let U2 := fun ij : I × I ↦ U ij.1 ⊓ U ij.2
    letI : Algebra R S := φ.hom.toAlgebra
    letI (i : I) : Module R Γ(M, U i) :=
      Scheme.Modules.openSectionsModule pX M (U i)
    letI (ij : I × I) : Module R Γ(M, U2 ij) :=
      Scheme.Modules.openSectionsModule pX M (U2 ij)
    letI (i : I) : Module S Γ(N, V i) :=
      Scheme.Modules.openSectionsModule pY N (V i)
    letI (ij : I × I) : Module S Γ(N, g ⁻¹ᵁ U2 ij) :=
      Scheme.Modules.openSectionsModule pY N (g ⁻¹ᵁ U2 ij)
    letI (ij : I × I) : Module S Γ(N, V ij.1 ⊓ V ij.2) :=
      Scheme.Modules.openSectionsModule pY N (V ij.1 ⊓ V ij.2)
    (Scheme.Modules.pullbackOpenSectionsBaseChangePiLinearEquiv
        φ g pX pY h M U2 hbij2).toLinearMap.comp
      (TensorProduct.AlgebraTensorModule.lTensor S S
        (Scheme.Modules.compatibleFamilyRight pX M U)) =
      (Scheme.Modules.compatibleFamilyRight pY N V).comp
        (Scheme.Modules.pullbackOpenSectionsBaseChangePiLinearEquiv
          φ g pX pY h M U hbij).toLinearMap := by
  dsimp only
  let N := (Scheme.Modules.pullback g).obj M
  let V := fun i ↦ g ⁻¹ᵁ U i
  let U2 := fun ij : I × I ↦ U ij.1 ⊓ U ij.2
  letI : Algebra R S := φ.hom.toAlgebra
  letI (i : I) : Module R Γ(M, U i) :=
    Scheme.Modules.openSectionsModule pX M (U i)
  letI (ij : I × I) : Module R Γ(M, U2 ij) :=
    Scheme.Modules.openSectionsModule pX M (U2 ij)
  letI (i : I) : Module S Γ(N, V i) :=
    Scheme.Modules.openSectionsModule pY N (V i)
  letI (ij : I × I) : Module S Γ(N, g ⁻¹ᵁ U2 ij) :=
    Scheme.Modules.openSectionsModule pY N (g ⁻¹ᵁ U2 ij)
  letI (ij : I × I) : Module S Γ(N, V ij.1 ⊓ V ij.2) :=
    Scheme.Modules.openSectionsModule pY N (V ij.1 ⊓ V ij.2)
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s m =>
      change
        Scheme.Modules.pullbackOpenSectionsBaseChangePiLinearEquiv
            φ g pX pY h M U2 hbij2
            (TensorProduct.AlgebraTensorModule.lTensor S S
              (Scheme.Modules.compatibleFamilyRight pX M U) (s ⊗ₜ[R] m)) =
          Scheme.Modules.compatibleFamilyRight pY N V
            (Scheme.Modules.pullbackOpenSectionsBaseChangePiLinearEquiv
              φ g pX pY h M U hbij (s ⊗ₜ[R] m))
      ext ij
      change pullbackOpenSectionsBaseChangeLinearMap
          φ g pX pY h M (U ij.1 ⊓ U ij.2)
            (s ⊗ₜ[R] Scheme.Modules.openRestrictionLinearMap pX M
              (show U ij.1 ⊓ U ij.2 ≤ U ij.2 from inf_le_right) (m ij.2)) =
        Scheme.Modules.openRestrictionLinearMap pY N
            (show V ij.1 ⊓ V ij.2 ≤ V ij.2 from inf_le_right)
          (pullbackOpenSectionsBaseChangeLinearMap
            φ g pX pY h M (U ij.2) (s ⊗ₜ[R] m ij.2))
      have hnat := congrArg
        (fun k ↦ k (s ⊗ₜ[R] m ij.2))
        (pullbackOpenSectionsBaseChangeLinearMap_restrict
          φ g pX pY h M (show U ij.1 ⊓ U ij.2 ≤ U ij.2 from inf_le_right))
      convert hnat.symm using 1 <;>
        simp only [LinearMap.comp_apply,
          TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply, N]
      all_goals congr 1

/-- Flat base change identifies the equalizer of the Čech restriction maps with
the equalizer for the pulled-back sheaf, provided the canonical maps are
bijective on the cover and its pairwise overlaps. -/
noncomputable def Scheme.Modules.pullbackCompatibleEqLocusBaseChangeLinearEquiv
    {I : Type u} [Fintype I] [DecidableEq I]
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (hflat : letI : Algebra R S := φ.hom.toAlgebra; Module.Flat R S)
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (pX : X ⟶ Spec R) (pY : Y ⟶ Spec S)
    (h : g ≫ pX = pY ≫ Spec.map φ) (M : X.Modules) (U : I → X.Opens)
    (hbij : ∀ i, Function.Bijective
      (pullbackOpenSectionsBaseChangeLinearMap φ g pX pY h M (U i)))
    (hbij2 : ∀ ij : I × I, Function.Bijective
      (pullbackOpenSectionsBaseChangeLinearMap
        φ g pX pY h M (U ij.1 ⊓ U ij.2))) :
    let N := (Scheme.Modules.pullback g).obj M
    let V := fun i ↦ g ⁻¹ᵁ U i
    let U2 := fun ij : I × I ↦ U ij.1 ⊓ U ij.2
    letI : Algebra R S := φ.hom.toAlgebra
    letI (i : I) : Module R Γ(M, U i) :=
      Scheme.Modules.openSectionsModule pX M (U i)
    letI (ij : I × I) : Module R Γ(M, U2 ij) :=
      Scheme.Modules.openSectionsModule pX M (U2 ij)
    letI (i : I) : Module S Γ(N, V i) :=
      Scheme.Modules.openSectionsModule pY N (V i)
    letI (ij : I × I) : Module S Γ(N, g ⁻¹ᵁ U2 ij) :=
      Scheme.Modules.openSectionsModule pY N (g ⁻¹ᵁ U2 ij)
    letI (ij : I × I) : Module S Γ(N, V ij.1 ⊓ V ij.2) :=
      Scheme.Modules.openSectionsModule pY N (V ij.1 ⊓ V ij.2)
    S ⊗[R] LinearMap.eqLocus
      (Scheme.Modules.compatibleFamilyLeft pX M U)
      (Scheme.Modules.compatibleFamilyRight pX M U) ≃ₗ[S]
      LinearMap.eqLocus
        (Scheme.Modules.compatibleFamilyLeft pY N V)
        (Scheme.Modules.compatibleFamilyRight pY N V) := by
  let N := (Scheme.Modules.pullback g).obj M
  let V := fun i ↦ g ⁻¹ᵁ U i
  let U2 := fun ij : I × I ↦ U ij.1 ⊓ U ij.2
  letI : Algebra R S := φ.hom.toAlgebra
  letI : Module.Flat R S := hflat
  letI (i : I) : Module R Γ(M, U i) :=
    Scheme.Modules.openSectionsModule pX M (U i)
  letI (ij : I × I) : Module R Γ(M, U2 ij) :=
    Scheme.Modules.openSectionsModule pX M (U2 ij)
  letI (i : I) : Module S Γ(N, V i) :=
    Scheme.Modules.openSectionsModule pY N (V i)
  letI (ij : I × I) : Module S Γ(N, g ⁻¹ᵁ U2 ij) :=
    Scheme.Modules.openSectionsModule pY N (g ⁻¹ᵁ U2 ij)
  letI (ij : I × I) : Module S Γ(N, V ij.1 ⊓ V ij.2) :=
    Scheme.Modules.openSectionsModule pY N (V ij.1 ⊓ V ij.2)
  let fR := Scheme.Modules.compatibleFamilyLeft pX M U
  let gR := Scheme.Modules.compatibleFamilyRight pX M U
  let fS := Scheme.Modules.compatibleFamilyLeft pY N V
  let gS := Scheme.Modules.compatibleFamilyRight pY N V
  let eU := Scheme.Modules.pullbackOpenSectionsBaseChangePiLinearEquiv
    φ g pX pY h M U hbij
  let eU2 := Scheme.Modules.pullbackOpenSectionsBaseChangePiLinearEquiv
    φ g pX pY h M U2 hbij2
  exact (LinearMap.tensorEqLocusEquiv S S fR gR).trans
    (LinearMap.eqLocusLinearEquivOfIntertwining
      (TensorProduct.AlgebraTensorModule.lTensor S S fR)
      (TensorProduct.AlgebraTensorModule.lTensor S S gR)
      fS gS eU eU2
      (Scheme.Modules.pullbackOpenSectionsBaseChangePiLinearEquiv_intertwines_left
        φ g pX pY h M U hbij hbij2)
      (Scheme.Modules.pullbackOpenSectionsBaseChangePiLinearEquiv_intertwines_right
        φ g pX pY h M U hbij hbij2))

@[simp]
lemma Scheme.Modules.pullbackCompatibleEqLocusBaseChangeLinearEquiv_tmul_apply
    {I : Type u} [Fintype I] [DecidableEq I]
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (hflat : letI : Algebra R S := φ.hom.toAlgebra; Module.Flat R S)
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (pX : X ⟶ Spec R) (pY : Y ⟶ Spec S)
    (h : g ≫ pX = pY ≫ Spec.map φ) (M : X.Modules) (U : I → X.Opens)
    (hbij : ∀ i, Function.Bijective
      (pullbackOpenSectionsBaseChangeLinearMap φ g pX pY h M (U i)))
    (hbij2 : ∀ ij : I × I, Function.Bijective
      (pullbackOpenSectionsBaseChangeLinearMap
        φ g pX pY h M (U ij.1 ⊓ U ij.2)))
    (s : S) (m :
      letI (i : I) : Module R Γ(M, U i) :=
        Scheme.Modules.openSectionsModule pX M (U i)
      letI (ij : I × I) : Module R Γ(M, U ij.1 ⊓ U ij.2) :=
        Scheme.Modules.openSectionsModule pX M (U ij.1 ⊓ U ij.2)
      LinearMap.eqLocus
        (Scheme.Modules.compatibleFamilyLeft pX M U)
        (Scheme.Modules.compatibleFamilyRight pX M U)) (i : I) :
    let N := (Scheme.Modules.pullback g).obj M
    let V := fun i ↦ g ⁻¹ᵁ U i
    let U2 := fun ij : I × I ↦ U ij.1 ⊓ U ij.2
    letI : Algebra R S := φ.hom.toAlgebra
    letI (i : I) : Module R Γ(M, U i) :=
      Scheme.Modules.openSectionsModule pX M (U i)
    letI (ij : I × I) : Module R Γ(M, U2 ij) :=
      Scheme.Modules.openSectionsModule pX M (U2 ij)
    letI (i : I) : Module S Γ(N, V i) :=
      Scheme.Modules.openSectionsModule pY N (V i)
    letI (ij : I × I) : Module S Γ(N, g ⁻¹ᵁ U2 ij) :=
      Scheme.Modules.openSectionsModule pY N (g ⁻¹ᵁ U2 ij)
    letI (ij : I × I) : Module S Γ(N, V ij.1 ⊓ V ij.2) :=
      Scheme.Modules.openSectionsModule pY N (V ij.1 ⊓ V ij.2)
    (Scheme.Modules.pullbackCompatibleEqLocusBaseChangeLinearEquiv
      φ hflat g pX pY h M U hbij hbij2 (s ⊗ₜ[R] m) :
        LinearMap.eqLocus
          (Scheme.Modules.compatibleFamilyLeft pY N V)
          (Scheme.Modules.compatibleFamilyRight pY N V)).1 i =
      pullbackOpenSectionsBaseChangeLinearMap
        φ g pX pY h M (U i) (s ⊗ₜ[R] m.1 i) := by
  rfl

@[simp]
lemma Scheme.Modules.sectionsLinearEquivCompatibleEqLocus_apply_apply
    {I : Type u} {R : CommRingCat.{u}} {X : Scheme.{u}}
    (p : X ⟶ Spec R) (M : X.Modules) (U : I → X.Opens)
    (hU : ⨆ i, U i = ⊤) (m : Γ(M, ⊤)) (i : I) :
    letI : Module R Γ(M, ⊤) := Scheme.Modules.globalSectionsModule p M
    letI (i : I) : Module R Γ(M, U i) :=
      Scheme.Modules.openSectionsModule p M (U i)
    letI (ij : I × I) : Module R Γ(M, U ij.1 ⊓ U ij.2) :=
      Scheme.Modules.openSectionsModule p M (U ij.1 ⊓ U ij.2)
    (Scheme.Modules.sectionsLinearEquivCompatibleEqLocus p M U hU m).1 i =
      Scheme.Modules.globalToOpenRestrictionLinearMap p M (U i) m := by
  rfl

/-- The canonical global-sections base-change map is bijective when a finite
cover and all pairwise overlaps have bijective canonical local base-change
maps. -/
lemma Scheme.Modules.pullbackGlobalSectionsBaseChangeLinearMap_bijective_of_finiteCover
    {I : Type u} [Finite I]
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (hflat : letI : Algebra R S := φ.hom.toAlgebra; Module.Flat R S)
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (pX : X ⟶ Spec R) (pY : Y ⟶ Spec S)
    (h : g ≫ pX = pY ≫ Spec.map φ) (M : X.Modules) (U : I → X.Opens)
    (hU : ⨆ i, U i = ⊤)
    (hbij : ∀ i, Function.Bijective
      (pullbackOpenSectionsBaseChangeLinearMap φ g pX pY h M (U i)))
    (hbij2 : ∀ ij : I × I, Function.Bijective
      (pullbackOpenSectionsBaseChangeLinearMap
        φ g pX pY h M (U ij.1 ⊓ U ij.2))) :
    let N := (Scheme.Modules.pullback g).obj M
    letI : Algebra R S := φ.hom.toAlgebra
    letI : Module R Γ(M, ⊤) := Scheme.Modules.globalSectionsModule pX M
    letI : Module S Γ(N, ⊤) := Scheme.Modules.globalSectionsModule pY N
    Function.Bijective
      (Scheme.Modules.pullbackGlobalSectionsBaseChangeLinearMap
        φ g pX pY h M) := by
  letI : Fintype I := Fintype.ofFinite I
  letI : DecidableEq I := Classical.decEq I
  let N := (Scheme.Modules.pullback g).obj M
  let V := fun i ↦ g ⁻¹ᵁ U i
  let U2 := fun ij : I × I ↦ U ij.1 ⊓ U ij.2
  have hV : ⨆ i, V i = ⊤ := g.iSup_preimage_eq_top hU
  letI : Algebra R S := φ.hom.toAlgebra
  letI : Module.Flat R S := hflat
  letI : Module R Γ(M, ⊤) := Scheme.Modules.globalSectionsModule pX M
  letI : Module S Γ(N, ⊤) := Scheme.Modules.globalSectionsModule pY N
  letI (i : I) : Module R Γ(M, U i) :=
    Scheme.Modules.openSectionsModule pX M (U i)
  letI (ij : I × I) : Module R Γ(M, U2 ij) :=
    Scheme.Modules.openSectionsModule pX M (U2 ij)
  letI (i : I) : Module S Γ(N, V i) :=
    Scheme.Modules.openSectionsModule pY N (V i)
  letI (ij : I × I) : Module S Γ(N, g ⁻¹ᵁ U2 ij) :=
    Scheme.Modules.openSectionsModule pY N (g ⁻¹ᵁ U2 ij)
  letI (ij : I × I) : Module S Γ(N, V ij.1 ⊓ V ij.2) :=
    Scheme.Modules.openSectionsModule pY N (V ij.1 ⊓ V ij.2)
  let eR := Scheme.Modules.sectionsLinearEquivCompatibleEqLocus pX M U hU
  let eS := Scheme.Modules.sectionsLinearEquivCompatibleEqLocus pY N V hV
  let eEq := Scheme.Modules.pullbackCompatibleEqLocusBaseChangeLinearEquiv
    φ hflat g pX pY h M U hbij hbij2
  let eSource := TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl S S) eR
  let c := Scheme.Modules.pullbackGlobalSectionsBaseChangeLinearMap
    φ g pX pY h M
  have hc : eS.toLinearMap.comp c =
      eEq.toLinearMap.comp eSource.toLinearMap := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s m =>
        change eS (c (s ⊗ₜ[R] m)) = eEq (eSource (s ⊗ₜ[R] m))
        apply Subtype.ext
        funext i
        rw [show eSource (s ⊗ₜ[R] m) = s ⊗ₜ[R] eR m by
          exact TensorProduct.AlgebraTensorModule.congr_tmul _ _ _ _]
        rw [Scheme.Modules.pullbackCompatibleEqLocusBaseChangeLinearEquiv_tmul_apply]
        rw [Scheme.Modules.sectionsLinearEquivCompatibleEqLocus_apply_apply]
        rw [Scheme.Modules.sectionsLinearEquivCompatibleEqLocus_apply_apply]
        have hnat := congrArg (fun k ↦ k (s ⊗ₜ[R] m))
          (Scheme.Modules.pullbackGlobalSectionsBaseChangeLinearMap_restrict
            φ g pX pY h M (U i))
        convert hnat using 1 <;>
          simp only [LinearMap.comp_apply,
            TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply,
            c, N, V]
  have hcomp : Function.Bijective (eS.toLinearMap.comp c) := by
    rw [hc]
    exact eEq.bijective.comp eSource.bijective
  change Function.Bijective c
  exact (eS.bijective.of_comp_iff' c).mp hcomp

/-- Global sections commute with flat scalar extension whenever the morphism is
affine-cartesian on a finite affine cover and its pairwise overlaps. -/
noncomputable def Scheme.Modules.pullbackGlobalSectionsBaseChangeLinearEquiv_of_finiteCover
    {I : Type u} [Finite I]
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (hflat : letI : Algebra R S := φ.hom.toAlgebra; Module.Flat R S)
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (pX : X ⟶ Spec R) (pY : Y ⟶ Spec S)
    (h : g ≫ pX = pY ≫ Spec.map φ) (M : X.Modules) (U : I → X.Opens)
    (hU : ⨆ i, U i = ⊤)
    (hbij : ∀ i, Function.Bijective
      (pullbackOpenSectionsBaseChangeLinearMap φ g pX pY h M (U i)))
    (hbij2 : ∀ ij : I × I, Function.Bijective
      (pullbackOpenSectionsBaseChangeLinearMap
        φ g pX pY h M (U ij.1 ⊓ U ij.2))) :
    let N := (Scheme.Modules.pullback g).obj M
    letI : Algebra R S := φ.hom.toAlgebra
    letI : Module R Γ(M, ⊤) := Scheme.Modules.globalSectionsModule pX M
    letI : Module S Γ(N, ⊤) := Scheme.Modules.globalSectionsModule pY N
    S ⊗[R] Γ(M, ⊤) ≃ₗ[S] Γ(N, ⊤) := by
  letI : Fintype I := Fintype.ofFinite I
  letI : DecidableEq I := Classical.decEq I
  let N := (Scheme.Modules.pullback g).obj M
  letI : Algebra R S := φ.hom.toAlgebra
  letI : Module R Γ(M, ⊤) := Scheme.Modules.globalSectionsModule pX M
  letI : Module S Γ(N, ⊤) := Scheme.Modules.globalSectionsModule pY N
  exact LinearEquiv.ofBijective
    (Scheme.Modules.pullbackGlobalSectionsBaseChangeLinearMap
      φ g pX pY h M)
    (Scheme.Modules.pullbackGlobalSectionsBaseChangeLinearMap_bijective_of_finiteCover
      φ hflat g pX pY h M U hU hbij hbij2)

end AlgebraicGeometry
