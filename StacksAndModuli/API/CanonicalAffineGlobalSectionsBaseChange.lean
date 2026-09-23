module

public import StacksAndModuli.API.AffineCechGlobalSectionsBaseChange
public import StacksAndModuli.API.KernelIdealPullback

/-!
# Canonical affine base change for global sections

This file identifies the canonical scalar-extension map on global sections of a
quasicoherent module in an affine cartesian square.  The proof compares arbitrary
affine schemes with their canonical spectra and tracks the adjunction-unit map
through the comparison, including the unit-coordinate normalization on spectra.

Main declarations:

* `canonicalAffinePullbackSectionsBaseChangeLinearMap_bijective`;
* `pullbackSectionsBaseChangeLinearMap_bijective_of_isPullback`;
* `pullbackSpecSectionsBaseChangeLinearEquiv_of_ring_isPushout`.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace Opposite TensorProduct
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable def pullbackSectionsBaseChangeLinearMap
    {P X Y Z : Scheme.{u}}
    (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : fst ≫ f = snd ≫ g) (M : X.Modules) :
    let N := (Scheme.Modules.pullback fst).obj M
    letI : Algebra Γ(Z, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
    letI : Module Γ(Z, ⊤) Γ(M, ⊤) := Module.compHom _ f.appTop.hom
    letI : Module Γ(Y, ⊤) Γ(N, ⊤) := Module.compHom _ snd.appTop.hom
    Γ(Y, ⊤) ⊗[Γ(Z, ⊤)] Γ(M, ⊤) →ₗ[Γ(Y, ⊤)] Γ(N, ⊤) := by
  let N := (Scheme.Modules.pullback fst).obj M
  letI : Algebra Γ(Z, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
  letI : Module Γ(Z, ⊤) Γ(M, ⊤) := Module.compHom _ f.appTop.hom
  letI : Module Γ(Y, ⊤) Γ(N, ⊤) := Module.compHom _ snd.appTop.hom
  letI : Algebra Γ(Y, ⊤) Γ(P, ⊤) := snd.appTop.hom.toAlgebra
  letI : IsScalarTower Γ(Y, ⊤) Γ(P, ⊤) Γ(N, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : Module Γ(Z, ⊤) Γ(N, ⊤) :=
    Module.compHom _ (snd.appTop.hom.comp g.appTop.hom)
  letI : IsScalarTower Γ(Z, ⊤) Γ(Y, ⊤) Γ(N, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let b : Γ(Y, ⊤) →ₗ[Γ(Y, ⊤)] Γ(M, ⊤) →ₗ[Γ(Z, ⊤)] Γ(N, ⊤) :=
    { toFun := fun s ↦
        { toFun := fun m ↦ s • Scheme.Modules.pullbackGlobalSections fst M m
          map_add' := by
            intro m n
            rw [(Scheme.Modules.pullbackGlobalSections fst M).map_add, smul_add]
          map_smul' := by
            intro r m
            change s • Scheme.Modules.pullbackGlobalSections fst M
                (f.appTop r • m) = _
            rw [Scheme.Modules.pullbackGlobalSections_smul]
            change s • fst.appTop (f.appTop r) •
                Scheme.Modules.pullbackGlobalSections fst M m =
              g.appTop r • s • Scheme.Modules.pullbackGlobalSections fst M m
            rw [← IsScalarTower.smul_assoc]
            rw [Algebra.smul_def, smul_smul]
            change (snd.appTop s * fst.appTop (f.appTop r)) •
                Scheme.Modules.pullbackGlobalSections fst M m =
              snd.appTop (g.appTop r * s) •
                Scheme.Modules.pullbackGlobalSections fst M m
            congr 1
            have happ := congrArg Scheme.Hom.appTop h
            change f.appTop ≫ fst.appTop = g.appTop ≫ snd.appTop at happ
            have hr := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom happ) r
            rw [← ConcreteCategory.comp_apply, hr, ConcreteCategory.comp_apply,
              map_mul, mul_comm] }
      map_add' := by
        intro s t
        ext m
        exact add_smul s t _
      map_smul' := by
        intro s t
        ext m
        exact mul_smul s t _ }
  exact TensorProduct.AlgebraTensorModule.lift b

@[simp]
lemma pullbackSectionsBaseChangeLinearMap_tmul
    {P X Y Z : Scheme.{u}}
    (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : fst ≫ f = snd ≫ g) (M : X.Modules)
    (s : Γ(Y, ⊤)) (m : Γ(M, ⊤)) :
    let N := (Scheme.Modules.pullback fst).obj M
    letI : Algebra Γ(Z, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
    letI : Module Γ(Z, ⊤) Γ(M, ⊤) := Module.compHom _ f.appTop.hom
    letI : Module Γ(Y, ⊤) Γ(N, ⊤) := Module.compHom _ snd.appTop.hom
    pullbackSectionsBaseChangeLinearMap fst snd f g h M (s ⊗ₜ m) =
      s • Scheme.Modules.pullbackGlobalSections fst M m := by
  simp [pullbackSectionsBaseChangeLinearMap]

noncomputable def specPullbackSectionsBaseChangeLinearMap
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : (Spec R).Modules) :
    let N := (Scheme.Modules.pullback (Spec.map φ)).obj M
    letI : Algebra R S := φ.hom.toAlgebra
    letI : Module R Γ(N, ⊤) := Module.compHom _ φ.hom
    S ⊗[R] Γ(M, ⊤) →ₗ[S] Γ(N, ⊤) := by
  letI : Algebra R S := φ.hom.toAlgebra
  let N := (Scheme.Modules.pullback (Spec.map φ)).obj M
  letI : Module R Γ(N, ⊤) := Module.compHom _ φ.hom
  letI : IsScalarTower R S Γ(N, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let b : S →ₗ[S] Γ(M, ⊤) →ₗ[R] Γ(N, ⊤) :=
    { toFun := fun s ↦
        { toFun := fun m ↦ s • Scheme.Modules.pullbackGlobalSections (Spec.map φ) M m
          map_add' := by
            intro m n
            rw [(Scheme.Modules.pullbackGlobalSections (Spec.map φ) M).map_add,
              smul_add]
          map_smul' := by
            intro r m
            rw [Scheme.Modules.smul_Spec_def]
            change s • Scheme.Modules.pullbackGlobalSections (Spec.map φ) M
                ((Scheme.ΓSpecIso R).inv r • m) = _
            rw [Scheme.Modules.pullbackGlobalSections_smul]
            rw [Scheme.Modules.smul_Spec_def]
            change s • (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r) •
                Scheme.Modules.pullbackGlobalSections (Spec.map φ) M m =
              φ.hom r • s • Scheme.Modules.pullbackGlobalSections (Spec.map φ) M
                m
            have hr : (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r) =
                (Scheme.ΓSpecIso S).inv (φ.hom r) := by
              simpa only [← CommRingCat.comp_apply] using
                congrArg (fun k : R ⟶ Γ(Spec S, ⊤) ↦ k.hom r)
                  (Scheme.ΓSpecIso_inv_naturality φ).symm
            let q := Scheme.Modules.pullbackGlobalSections (Spec.map φ) M m
            have hsmul : φ.hom r • q =
                (Scheme.ΓSpecIso S).inv (φ.hom r) • q := by
              rw [Scheme.Modules.smul_Spec_def]
              have ha : ((⊤ : (Spec S).Opens).leTop).op =
                  𝟙 (Opposite.op (⊤ : (Spec S).Opens)) := Subsingleton.elim _ _
              rw [ha, (Spec S).presheaf.map_id]
              rfl
            rw [hr, ← hsmul]
            rw [smul_smul, smul_smul, mul_comm] }
      map_add' := by
        intro s t
        ext m
        exact add_smul s t _
      map_smul' := by
        intro s t
        ext m
        exact mul_smul s t _ }
  exact TensorProduct.AlgebraTensorModule.lift b

@[simp]
lemma specPullbackSectionsBaseChangeLinearMap_tmul
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : (Spec R).Modules)
    (s : S) (m : Γ(M, ⊤)) :
    let N := (Scheme.Modules.pullback (Spec.map φ)).obj M
    letI : Algebra R S := φ.hom.toAlgebra
    letI : Module R Γ(N, ⊤) := Module.compHom _ φ.hom
    specPullbackSectionsBaseChangeLinearMap φ M (s ⊗ₜ m) =
      s • Scheme.Modules.pullbackGlobalSections (Spec.map φ) M m := by
  simp [specPullbackSectionsBaseChangeLinearMap]

lemma Scheme.Modules.pullbackGlobalSections_naturality
    {X Y : Scheme.{u}} (f : X ⟶ Y) {M N : Y.Modules} (ψ : M ⟶ N)
    (m : Γ(M, ⊤)) :
    ((Scheme.Modules.pullback f).map ψ).app ⊤
        (Scheme.Modules.pullbackGlobalSections f M m) =
      Scheme.Modules.pullbackGlobalSections f N (ψ.app ⊤ m) := by
  change ((Scheme.Modules.pullback f).map ψ).app ⊤
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app ⊤ m) =
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).app ⊤
      (ψ.app ⊤ m)
  have h := congrArg
    (fun k : M ⟶ (Scheme.Modules.pushforward f).obj
        ((Scheme.Modules.pullback f).obj N) ↦ k.app ⊤ m)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality ψ)
  exact h.symm

noncomputable def specPullbackComparisonEnd
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : (Spec R).Modules)
    [M.IsQuasicoherent] :
    let N := (Scheme.Modules.pullback (Spec.map φ)).obj M
    letI : Algebra R S := φ.hom.toAlgebra
    letI : Module R Γ(N, ⊤) := Module.compHom _ φ.hom
    S ⊗[R] Γ(M, ⊤) →ₗ[S] S ⊗[R] Γ(M, ⊤) := by
  letI : Algebra R S := φ.hom.toAlgebra
  let N := (Scheme.Modules.pullback (Spec.map φ)).obj M
  letI : Module R Γ(N, ⊤) := Module.compHom _ φ.hom
  exact (pullbackQuasicoherentSectionsLinearEquiv φ M).toLinearMap.comp
    (specPullbackSectionsBaseChangeLinearMap φ M)

noncomputable def specSectionsLinearMap
    {R : CommRingCat.{u}} {M N : (Spec R).Modules} (ψ : M ⟶ N) :
    Γ(M, ⊤) →ₗ[R] Γ(N, ⊤) where
  toFun := fun m ↦ ψ.app ⊤ m
  map_add' := fun m n ↦ map_add _ _ _
  map_smul' := by
    intro r m
    rw [Scheme.Modules.smul_Spec_def, Scheme.Modules.Hom.app_smul,
      ← Scheme.Modules.smul_Spec_def]
    rfl

lemma specSectionsLinearMap_eq_moduleSpecΓFunctor_map
    {R : CommRingCat.{u}} {M N : (Spec R).Modules} (ψ : M ⟶ N) :
    specSectionsLinearMap ψ = (moduleSpecΓFunctor.map ψ).hom := by
  rfl

lemma specPullbackSectionsBaseChangeLinearMap_naturality
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    {M N : (Spec R).Modules} (ψ : M ⟶ N) :
    let PM := (Scheme.Modules.pullback (Spec.map φ)).obj M
    let PN := (Scheme.Modules.pullback (Spec.map φ)).obj N
    letI : Algebra R S := φ.hom.toAlgebra
    letI : Module R Γ(PM, ⊤) := Module.compHom _ φ.hom
    letI : Module R Γ(PN, ⊤) := Module.compHom _ φ.hom
    (specSectionsLinearMap
        ((Scheme.Modules.pullback (Spec.map φ)).map ψ)).comp
          (specPullbackSectionsBaseChangeLinearMap φ M) =
      (specPullbackSectionsBaseChangeLinearMap φ N).comp
        (TensorProduct.AlgebraTensorModule.lTensor S S
          (specSectionsLinearMap ψ)) := by
  letI : Algebra R S := φ.hom.toAlgebra
  let PM := (Scheme.Modules.pullback (Spec.map φ)).obj M
  let PN := (Scheme.Modules.pullback (Spec.map φ)).obj N
  letI : Module R Γ(PM, ⊤) := Module.compHom _ φ.hom
  letI : Module R Γ(PN, ⊤) := Module.compHom _ φ.hom
  letI : IsScalarTower R S Γ(PM, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : IsScalarTower R S Γ(PN, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>
      rw [LinearMap.comp_apply, specPullbackSectionsBaseChangeLinearMap_tmul,
        map_smul]
      change s • ((Scheme.Modules.pullback (Spec.map φ)).map ψ).app ⊤
          (Scheme.Modules.pullbackGlobalSections (Spec.map φ) M m) = _
      rw [Scheme.Modules.pullbackGlobalSections_naturality]
      rw [LinearMap.comp_apply, TensorProduct.AlgebraTensorModule.lTensor_tmul,
        specPullbackSectionsBaseChangeLinearMap_tmul]
      rfl
  | add x y hx hy => simp only [map_add, hx, hy]

lemma extendScalars_map_eq_lTensor_specSectionsLinearMap
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    {M N : (Spec R).Modules} (ψ : M ⟶ N) :
    letI : Algebra R S := φ.hom.toAlgebra
    ((ModuleCat.extendScalars φ.hom).map
        (moduleSpecΓFunctor.map ψ)).hom =
      TensorProduct.AlgebraTensorModule.lTensor S S
        (specSectionsLinearMap ψ) := by
  letI : Algebra R S := φ.hom.toAlgebra
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>
      rw [ModuleCat.ExtendScalars.map_tmul]
      change (show S from s) ⊗ₜ[R] (ψ.app ⊤ m) =
        (show S from s) ⊗ₜ[R] (specSectionsLinearMap ψ m)
      rfl
  | add x y hx hy => simp only [map_add, hx, hy]

noncomputable def sectionsFromTopAffine
    {X : Scheme.{u}} (M : X.Modules) (m : Γ(M, ⊤)) : M.sections :=
  M.val.sectionsMk
    (fun U ↦ M.presheaf.map (homOfLE (le_top (a := U.unop))).op m)
    (fun {U V} g ↦ by
      let a := (homOfLE (le_top (a := U.unop))).op
      let b := (homOfLE (le_top (a := V.unop))).op
      change M.presheaf.map g (M.presheaf.map a m) = M.presheaf.map b m
      have hab : a ≫ g = b := Subsingleton.elim _ _
      have hm : M.presheaf.map a ≫ M.presheaf.map g = M.presheaf.map b := by
        rw [← M.presheaf.map_comp, hab]
      exact ConcreteCategory.congr_hom hm m)

@[simp]
lemma sectionsFromTopAffine_apply_top
    {X : Scheme.{u}} (M : X.Modules) (m : Γ(M, ⊤)) :
    (sectionsFromTopAffine M m).1 (.op ⊤) = m := by
  change M.presheaf.map (homOfLE (le_top (a := (⊤ : X.Opens)))).op m = m
  have ha : (homOfLE (le_top (a := (⊤ : X.Opens)))).op =
      𝟙 (Opposite.op (⊤ : X.Opens)) := Subsingleton.elim _ _
  rw [ha, M.presheaf.map_id]
  rfl

noncomputable def homOfGlobalSection
    {X : Scheme.{u}} (M : X.Modules) (m : Γ(M, ⊤)) :
    SheafOfModules.unit X.ringCatSheaf ⟶ M :=
  M.unitHomEquiv.symm (sectionsFromTopAffine M m)

lemma homOfGlobalSection_app_top_one
    {R : CommRingCat.{u}} (M : (Spec R).Modules) (m : Γ(M, ⊤)) :
    Scheme.Modules.Hom.app (homOfGlobalSection M m) ⊤
      ((Scheme.ΓSpecIso R).inv 1) = m := by
  rw [map_one]
  change (M.unitHomEquiv (homOfGlobalSection M m)).1 (.op ⊤) = m
  rw [show M.unitHomEquiv (homOfGlobalSection M m) =
      sectionsFromTopAffine M m by exact Equiv.apply_symm_apply _ _]
  exact sectionsFromTopAffine_apply_top M m

lemma homOfGlobalSection_app_top_one_general
    {X : Scheme.{u}} (M : X.Modules) (m : Γ(M, ⊤)) :
    Scheme.Modules.Hom.app (homOfGlobalSection M m) ⊤
      (show Γ(SheafOfModules.unit X.ringCatSheaf, ⊤) from
        (1 : Γ(X, ⊤))) = m := by
  change (M.unitHomEquiv (homOfGlobalSection M m)).1 (.op ⊤) = m
  rw [show M.unitHomEquiv (homOfGlobalSection M m) =
      sectionsFromTopAffine M m by exact Equiv.apply_symm_apply _ _]
  exact sectionsFromTopAffine_apply_top M m

lemma pullbackObjUnitToUnit_unit_one'
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.Modules.Hom.app
        (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
        (⊤ : X.Opens)
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        (SheafOfModules.unit Y.ringCatSheaf)).app (⊤ : Y.Opens)
          (1 : Γ(Y, (⊤ : Y.Opens)))) =
      (1 : Γ(X, (⊤ : X.Opens))) := by
  have htr := (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_unit
    (X := SheafOfModules.unit Y.ringCatSheaf)
    (Y := (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (f := SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
  have hmath : (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv
        (SheafOfModules.unit Y.ringCatSheaf)
        (SheafOfModules.unit X.ringCatSheaf)
        (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  rw [hmath] at htr
  have happ := congrArg
    (fun (k : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶
        (Scheme.Modules.pushforward f).obj
          (SheafOfModules.unit X.ringCatSheaf)) ↦
      Scheme.Modules.Hom.app k (⊤ : Y.Opens)
        (show Γ((SheafOfModules.unit Y.ringCatSheaf : Y.Modules),
          (⊤ : Y.Opens)) from (1 : Γ(Y, (⊤ : Y.Opens))))) htr
  refine Eq.trans happ.symm ?_
  refine Eq.trans (SheafOfModules.unitToPushforwardObjUnit_val_app_apply
    f.toRingCatSheafHom (X := Opposite.op (⊤ : Y.Opens))
      (show Γ(Y, (⊤ : Y.Opens)) from 1)) ?_
  exact map_one ((f.toRingCatSheafHom.hom.app
    (Opposite.op (⊤ : Y.Opens))).hom)

lemma pullbackObjUnitToUnit_inv_one_eq_pullbackGlobalSections
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)] :
    Scheme.Modules.Hom.app
        (inv (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom))
        (⊤ : X.Opens) (1 : Γ(X, (⊤ : X.Opens))) =
      Scheme.Modules.pullbackGlobalSections f
        (SheafOfModules.unit Y.ringCatSheaf)
        (1 : Γ(Y, (⊤ : Y.Opens))) := by
  let a := SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom
  apply (ConcreteCategory.bijective_of_isIso
    (Scheme.Modules.Hom.app a (⊤ : X.Opens))).injective
  change Scheme.Modules.Hom.app a (⊤ : X.Opens)
      (Scheme.Modules.Hom.app (inv a) (⊤ : X.Opens)
        (show Γ(SheafOfModules.unit X.ringCatSheaf, (⊤ : X.Opens)) from
          (1 : Γ(X, (⊤ : X.Opens))))) = _
  rw [← ConcreteCategory.comp_apply]
  change Scheme.Modules.Hom.app (inv a ≫ a) (⊤ : X.Opens)
      (show Γ(SheafOfModules.unit X.ringCatSheaf, (⊤ : X.Opens)) from
        (1 : Γ(X, (⊤ : X.Opens)))) = _
  rw [IsIso.inv_hom_id]
  change (1 : Γ(X, (⊤ : X.Opens))) = Scheme.Modules.Hom.app a (⊤ : X.Opens)
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
      (SheafOfModules.unit Y.ringCatSheaf)).app (⊤ : Y.Opens)
        (show Γ(SheafOfModules.unit Y.ringCatSheaf, (⊤ : Y.Opens)) from
          (1 : Γ(Y, (⊤ : Y.Opens)))))
  exact (pullbackObjUnitToUnit_unit_one' f).symm

lemma pullbackUnitMap_app_top_one
    {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules}
    (phi : SheafOfModules.unit Y.ringCatSheaf ⟶ M) :
    Scheme.Modules.Hom.app
        (Scheme.Modules.Hom.pullbackUnitMap f phi) ⊤
        (1 : Γ(X, ⊤)) =
      Scheme.Modules.pullbackGlobalSections f M
        (Scheme.Modules.Hom.app phi ⊤ (1 : Γ(Y, ⊤))) := by
  let a := SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom
  letI : IsIso a := inferInstance
  change Scheme.Modules.Hom.app
      (inv a ≫ (Scheme.Modules.pullback f).map phi) ⊤
      (1 : Γ(X, ⊤)) = _
  rw [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply]
  rw [show Scheme.Modules.Hom.app (inv a) ⊤ (1 : Γ(X, ⊤)) =
      Scheme.Modules.pullbackGlobalSections f
        (SheafOfModules.unit Y.ringCatSheaf) (1 : Γ(Y, ⊤)) by
      exact pullbackObjUnitToUnit_inv_one_eq_pullbackGlobalSections f]
  exact Scheme.Modules.pullbackGlobalSections_naturality f phi
    (1 : Γ(Y, ⊤))

lemma pullbackUnitMap_homOfGlobalSection_app_top_one
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) (m : Γ(M, ⊤)) :
    Scheme.Modules.Hom.app
        (Scheme.Modules.Hom.pullbackUnitMap f (homOfGlobalSection M m)) ⊤
        (1 : Γ(X, ⊤)) =
      Scheme.Modules.pullbackGlobalSections f M m := by
  rw [pullbackUnitMap_app_top_one,
    homOfGlobalSection_app_top_one_general]

lemma pullbackGlobalSections_compCongrIso
    {W X Y Z : Scheme.{u}} (p : W ⟶ Y) (g : Y ⟶ Z)
    (f : W ⟶ X) (q : X ⟶ Z) (h : p ≫ g = f ≫ q)
    (M : Z.Modules) (m : Γ(M, ⊤)) :
    let e := Scheme.Modules.Hom.pullbackCompCongrIso p g f q h M
    Scheme.Modules.Hom.app e.hom ⊤
        (Scheme.Modules.pullbackGlobalSections p
          ((Scheme.Modules.pullback g).obj M)
          (Scheme.Modules.pullbackGlobalSections g M m)) =
      Scheme.Modules.pullbackGlobalSections f
        ((Scheme.Modules.pullback q).obj M)
        (Scheme.Modules.pullbackGlobalSections q M m) := by
  let phi := homOfGlobalSection M m
  let e := Scheme.Modules.Hom.pullbackCompCongrIso p g f q h M
  have he := Scheme.Modules.Hom.pullbackUnitMap_comp_pullbackCompCongrIso
    p g f q h phi
  have heval := congrArg
    (fun k : SheafOfModules.unit W.ringCatSheaf ⟶
        (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback q).obj M) ↦
      Scheme.Modules.Hom.app k ⊤
        (show Γ(SheafOfModules.unit W.ringCatSheaf, ⊤) from
          (1 : Γ(W, ⊤)))) he
  change Scheme.Modules.Hom.app e.hom ⊤
      (Scheme.Modules.Hom.app
        (Scheme.Modules.Hom.pullbackUnitMap p
          (Scheme.Modules.Hom.pullbackUnitMap g phi)) ⊤
        (1 : Γ(W, ⊤))) =
    Scheme.Modules.Hom.app
      (Scheme.Modules.Hom.pullbackUnitMap f
        (Scheme.Modules.Hom.pullbackUnitMap q phi)) ⊤
      (1 : Γ(W, ⊤)) at heval
  rw [pullbackUnitMap_app_top_one, pullbackUnitMap_app_top_one,
    pullbackUnitMap_app_top_one, pullbackUnitMap_app_top_one,
    homOfGlobalSection_app_top_one_general] at heval
  exact heval

noncomputable def canonicalAffinePullbackSectionsBaseChangeLinearMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    let N := (Scheme.Modules.pullback f).obj M
    letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    Γ(X, ⊤) ⊗[Γ(Y, ⊤)] Γ(M, ⊤) →ₗ[Γ(X, ⊤)] Γ(N, ⊤) := by
  let N := (Scheme.Modules.pullback f).obj M
  letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  letI : Module Γ(Y, ⊤) Γ(N, ⊤) := Module.compHom _ f.appTop.hom
  letI : IsScalarTower Γ(Y, ⊤) Γ(X, ⊤) Γ(N, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let b : Γ(X, ⊤) →ₗ[Γ(X, ⊤)] Γ(M, ⊤) →ₗ[Γ(Y, ⊤)] Γ(N, ⊤) :=
    { toFun := fun s ↦
        { toFun := fun m ↦
            s • Scheme.Modules.pullbackGlobalSections f M m
          map_add' := fun m n ↦ by
            rw [map_add, smul_add]
          map_smul' := fun r m ↦ by
            rw [Scheme.Modules.pullbackGlobalSections_smul]
            change s • f.appTop r •
                Scheme.Modules.pullbackGlobalSections f M m =
              f.appTop r • s •
                Scheme.Modules.pullbackGlobalSections f M m
            simp only [smul_smul]
            rw [mul_comm] }
      map_add' := fun s t ↦ by ext m; exact add_smul s t _
      map_smul' := fun s t ↦ by ext m; exact mul_smul s t _ }
  exact TensorProduct.AlgebraTensorModule.lift b

@[simp]
lemma canonicalAffinePullbackSectionsBaseChangeLinearMap_tmul
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    (s : Γ(X, ⊤)) (m : Γ(M, ⊤)) :
    letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    canonicalAffinePullbackSectionsBaseChangeLinearMap f M (s ⊗ₜ m) =
      s • Scheme.Modules.pullbackGlobalSections f M m := by
  simp [canonicalAffinePullbackSectionsBaseChangeLinearMap]

noncomputable def unitSectionsCoordinateLinearEquiv (R : CommRingCat.{u}) :
    Γ(SheafOfModules.unit (Spec R).ringCatSheaf, ⊤) ≃ₗ[R] R := by
  exact (unitModuleSpecΓIso R).toLinearEquiv.symm

lemma unitSectionsCoordinateLinearEquiv_symm_apply
    (R : CommRingCat.{u}) (r : R) :
    (unitSectionsCoordinateLinearEquiv R).symm r =
      (unitModuleSpecΓIso R).hom r := by
  rfl

noncomputable def unitTensorCoordinateLinearEquiv
    {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    letI : Algebra R S := φ.hom.toAlgebra
    S ⊗[R] Γ(SheafOfModules.unit (Spec R).ringCatSheaf, ⊤) ≃ₗ[S] S := by
  letI : Algebra R S := φ.hom.toAlgebra
  exact (TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl S S)
    (unitSectionsCoordinateLinearEquiv R)).trans
      (TensorProduct.AlgebraTensorModule.rid R S S)

@[simp]
lemma unitTensorCoordinateLinearEquiv_tmul
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (s : S) (r : R) :
    letI : Algebra R S := φ.hom.toAlgebra
    unitTensorCoordinateLinearEquiv φ
        (s ⊗ₜ[R] (unitSectionsCoordinateLinearEquiv R).symm r) =
      s * φ.hom r := by
  letI : Algebra R S := φ.hom.toAlgebra
  rw [show unitTensorCoordinateLinearEquiv φ =
      (TensorProduct.AlgebraTensorModule.congr
        (LinearEquiv.refl S S)
        (unitSectionsCoordinateLinearEquiv R)).trans
          (TensorProduct.AlgebraTensorModule.rid R S S) by rfl]
  rw [LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.congr_tmul]
  simp only [LinearEquiv.refl_apply, LinearEquiv.apply_symm_apply]
  rw [TensorProduct.AlgebraTensorModule.rid_tmul]
  change φ.hom r * s = s * φ.hom r
  exact mul_comm _ _

lemma extendScalars_map_eq_lTensor
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    {M N : ModuleCat.{u} R} (q : M ⟶ N) :
    letI : Algebra R S := φ.hom.toAlgebra
    ((ModuleCat.extendScalars φ.hom).map q).hom =
      TensorProduct.AlgebraTensorModule.lTensor S S q.hom := by
  letI : Algebra R S := φ.hom.toAlgebra
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>
      rw [ModuleCat.ExtendScalars.map_tmul]
      change (show S from s) ⊗ₜ[R] q.hom m =
        TensorProduct.AlgebraTensorModule.lTensor S S q.hom
          ((show S from s) ⊗ₜ[R] m)
      rw [TensorProduct.AlgebraTensorModule.lTensor_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

lemma extendScalars_mapIso_toLinearEquiv_eq_congr
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    {M N : ModuleCat.{u} R} (q : M ≅ N) :
    letI : Algebra R S := φ.hom.toAlgebra
    ((ModuleCat.extendScalars φ.hom).mapIso q).toLinearEquiv =
      TensorProduct.AlgebraTensorModule.congr
        (LinearEquiv.refl S S) q.toLinearEquiv := by
  letI : Algebra R S := φ.hom.toAlgebra
  apply LinearEquiv.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>
      change ((ModuleCat.extendScalars φ.hom).map q.hom).hom
          ((show S from s) ⊗ₜ[R] m) =
        TensorProduct.AlgebraTensorModule.congr
          (LinearEquiv.refl S S) q.toLinearEquiv
            ((show S from s) ⊗ₜ[R] m)
      rw [ModuleCat.ExtendScalars.map_tmul,
        TensorProduct.AlgebraTensorModule.congr_tmul]
      rfl
  | add x y hx hy => simp only [map_add, hx, hy]

lemma unitTensorCoordinateLinearEquiv_eq
    {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    letI : Algebra R S := φ.hom.toAlgebra
    unitTensorCoordinateLinearEquiv φ =
      (((ModuleCat.extendScalars φ.hom).mapIso
        (unitModuleSpecΓIso R).symm).toLinearEquiv).trans
          (TensorProduct.AlgebraTensorModule.rid R S S) := by
  letI : Algebra R S := φ.hom.toAlgebra
  rw [unitTensorCoordinateLinearEquiv,
    extendScalars_mapIso_toLinearEquiv_eq_congr]
  rfl

lemma unitTensorCoordinate_specPullbackComparisonEnd_one
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    [(SheafOfModules.unit (Spec R).ringCatSheaf :
      (Spec R).Modules).IsQuasicoherent] :
    let U := (SheafOfModules.unit (Spec R).ringCatSheaf : (Spec R).Modules)
    let PU := (Scheme.Modules.pullback (Spec.map φ)).obj U
    letI : Algebra R S := φ.hom.toAlgebra
    letI : Module R Γ(PU, ⊤) := Module.compHom _ φ.hom
    unitTensorCoordinateLinearEquiv φ
        (specPullbackComparisonEnd φ U
          (1 ⊗ₜ[R] (unitSectionsCoordinateLinearEquiv R).symm 1)) =
      unitPullbackScalarEquiv φ 1 := by
  let U := (SheafOfModules.unit (Spec R).ringCatSheaf : (Spec R).Modules)
  let PU := (Scheme.Modules.pullback (Spec.map φ)).obj U
  letI : Algebra R S := φ.hom.toAlgebra
  letI : Module R Γ(PU, ⊤) := Module.compHom _ φ.hom
  dsimp only
  let e := (pullbackQuasicoherentSectionsLinearEquiv φ U).toLinearMap
  let c := specPullbackSectionsBaseChangeLinearMap φ U
  change unitTensorCoordinateLinearEquiv φ
      (e (c (1 ⊗ₜ[R] (unitSectionsCoordinateLinearEquiv R).symm 1))) = _
  rw [specPullbackSectionsBaseChangeLinearMap_tmul,
    one_smul, unitSectionsCoordinateLinearEquiv_symm_apply,
    unitModuleSpecΓIso_hom_one, map_one]
  rw [← pullbackObjUnitToUnit_inv_one_eq_pullbackGlobalSections (Spec.map φ)]
  rw [unitTensorCoordinateLinearEquiv_eq]
  simp [unitPullbackScalarEquiv, unitPullbackCoordinateIso,
    unitPullbackSectionsIso, e]
  let a := SheafOfModules.pullbackObjUnitToUnit
    (Spec.map φ).toRingCatSheafHom
  letI : IsIso a := inferInstance
  let q := ((ModuleCat.extendScalars φ.hom).mapIso
    (unitModuleSpecΓIso R).symm).toLinearEquiv
  change q (e ((inv (Scheme.Modules.Hom.app a ⊤))
      (show Γ(SheafOfModules.unit (Spec S).ringCatSheaf, ⊤) from
        (1 : Γ(Spec S, ⊤))))) =
    q (e ((moduleSpecΓFunctor.map (inv a)).hom
      ((unitModuleSpecΓIso S).hom 1)))
  rw [unitModuleSpecΓIso_hom_one]
  have hΓ : (Scheme.ΓSpecIso S).inv 1 = (1 : Γ(Spec S, ⊤)) :=
    (Scheme.ΓSpecIso S).inv.hom.map_one
  rw [hΓ]
  congr 2
  apply (ConcreteCategory.bijective_of_isIso
    (Scheme.Modules.Hom.app a ⊤)).injective
  let oneS : Γ(SheafOfModules.unit (Spec S).ringCatSheaf, ⊤) :=
    show Γ(SheafOfModules.unit (Spec S).ringCatSheaf, ⊤) from
      (1 : Γ(Spec S, ⊤))
  change Scheme.Modules.Hom.app a ⊤
      ((inv (Scheme.Modules.Hom.app a ⊤)) oneS) =
    Scheme.Modules.Hom.app a ⊤
      (Scheme.Modules.Hom.app (inv a) ⊤ oneS)
  rw [← ConcreteCategory.comp_apply, IsIso.inv_hom_id]
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
    IsIso.inv_hom_id]
  rfl

lemma specPullbackComparisonEnd_one_tmul
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (M : (Spec R).Modules) [M.IsQuasicoherent] (m : Γ(M, ⊤)) :
    let N := (Scheme.Modules.pullback (Spec.map φ)).obj M
    letI : Algebra R S := φ.hom.toAlgebra
    letI : Module R Γ(N, ⊤) := Module.compHom _ φ.hom
    specPullbackComparisonEnd φ M (1 ⊗ₜ[R] m) =
      unitPullbackScalarEquiv φ 1 • (1 ⊗ₜ[R] m) := by
  let U := (SheafOfModules.unit (Spec R).ringCatSheaf : (Spec R).Modules)
  letI : U.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
      (tildeSelf (R := R)) inferInstance
  let N := (Scheme.Modules.pullback (Spec.map φ)).obj M
  let PU := (Scheme.Modules.pullback (Spec.map φ)).obj U
  letI : Algebra R S := φ.hom.toAlgebra
  letI : Module R Γ(N, ⊤) := Module.compHom _ φ.hom
  letI : Module R Γ(PU, ⊤) := Module.compHom _ φ.hom
  letI : IsScalarTower R S Γ(N, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : IsScalarTower R S Γ(PU, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  dsimp only
  let uR : Γ(U, ⊤) := (unitSectionsCoordinateLinearEquiv R).symm 1
  let zU : S ⊗[R] Γ(U, ⊤) := 1 ⊗ₜ[R] uR
  let ψ : U ⟶ M := homOfGlobalSection M m
  let cU := specPullbackSectionsBaseChangeLinearMap φ U
  let cM := specPullbackSectionsBaseChangeLinearMap φ M
  let eU := (pullbackQuasicoherentSectionsLinearEquiv φ U).toLinearMap
  let eM := (pullbackQuasicoherentSectionsLinearEquiv φ M).toLinearMap
  let pψ := specSectionsLinearMap
    ((Scheme.Modules.pullback (Spec.map φ)).map ψ)
  let tψ := TensorProduct.AlgebraTensorModule.lTensor S S
    (specSectionsLinearMap ψ)
  have hψ : Scheme.Modules.Hom.app ψ ⊤ uR = m := by
    rw [show uR = (unitSectionsCoordinateLinearEquiv R).symm 1 by rfl,
      unitSectionsCoordinateLinearEquiv_symm_apply,
      unitModuleSpecΓIso_hom_one]
    exact homOfGlobalSection_app_top_one M m
  have hcan : cM (1 ⊗ₜ[R] m) = pψ (cU zU) := by
    have h := DFunLike.congr_fun
      (specPullbackSectionsBaseChangeLinearMap_naturality φ ψ) zU
    change pψ (cU zU) = cM (tψ zU) at h
    have ht : tψ zU = 1 ⊗ₜ[R] m := by
      rw [show zU = 1 ⊗ₜ[R] uR by rfl,
        TensorProduct.AlgebraTensorModule.lTensor_tmul]
      rw [show specSectionsLinearMap ψ uR =
          Scheme.Modules.Hom.app ψ ⊤ uR by rfl, hψ]
    rw [ht] at h
    exact h.symm
  have haff : eM (pψ (cU zU)) =
      ((ModuleCat.extendScalars φ.hom).map
        (moduleSpecΓFunctor.map ψ)).hom (eU (cU zU)) := by
    have h := DFunLike.congr_fun
      (pullbackQuasicoherentSectionsLinearEquiv_naturality φ ψ) (cU zU)
    change eM (pψ (cU zU)) = _ at h
    exact h
  have hzU : eU (cU zU) =
      unitPullbackScalarEquiv φ 1 • zU := by
    apply (unitTensorCoordinateLinearEquiv φ).injective
    rw [show eU (cU zU) = specPullbackComparisonEnd φ U zU by rfl,
      show zU = 1 ⊗ₜ[R] (unitSectionsCoordinateLinearEquiv R).symm 1 by rfl,
      unitTensorCoordinate_specPullbackComparisonEnd_one]
    rw [map_smul, unitTensorCoordinateLinearEquiv_tmul]
    simp
  rw [show specPullbackComparisonEnd φ M (1 ⊗ₜ[R] m) =
      eM (cM (1 ⊗ₜ[R] m)) by rfl, hcan, haff, hzU]
  rw [extendScalars_map_eq_lTensor_specSectionsLinearMap, map_smul]
  change unitPullbackScalarEquiv φ 1 • tψ zU = _
  rw [show zU = 1 ⊗ₜ[R] uR by rfl,
    TensorProduct.AlgebraTensorModule.lTensor_tmul]
  rw [show specSectionsLinearMap ψ uR =
      Scheme.Modules.Hom.app ψ ⊤ uR by rfl, hψ]

lemma specPullbackComparisonEnd_apply
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (M : (Spec R).Modules) [M.IsQuasicoherent] :
    letI : Algebra R S := φ.hom.toAlgebra
    ∀ z : S ⊗[R] Γ(M, ⊤),
    let N := (Scheme.Modules.pullback (Spec.map φ)).obj M
    letI : Module R Γ(N, ⊤) := Module.compHom _ φ.hom
    specPullbackComparisonEnd φ M z = unitPullbackScalarEquiv φ 1 • z := by
  letI : Algebra R S := φ.hom.toAlgebra
  intro z
  let N := (Scheme.Modules.pullback (Spec.map φ)).obj M
  letI : Module R Γ(N, ⊤) := Module.compHom _ φ.hom
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>
      rw [TensorProduct.tmul_eq_smul_one_tmul, map_smul,
        specPullbackComparisonEnd_one_tmul, smul_smul, smul_smul]
      rw [mul_comm s (unitPullbackScalarEquiv φ 1)]
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]

lemma specPullbackSectionsBaseChangeLinearMap_bijective
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (M : (Spec R).Modules) [M.IsQuasicoherent] :
    let N := (Scheme.Modules.pullback (Spec.map φ)).obj M
    letI : Algebra R S := φ.hom.toAlgebra
    letI : Module R Γ(N, ⊤) := Module.compHom _ φ.hom
    Function.Bijective (specPullbackSectionsBaseChangeLinearMap φ M) := by
  let N := (Scheme.Modules.pullback (Spec.map φ)).obj M
  letI : Algebra R S := φ.hom.toAlgebra
  letI : Module R Γ(N, ⊤) := Module.compHom _ φ.hom
  let e := pullbackQuasicoherentSectionsLinearEquiv φ M
  let c := specPullbackSectionsBaseChangeLinearMap φ M
  have hec : Function.Bijective (e ∘ c) := by
    have hfun : (e ∘ c) =
        (fun z ↦ unitPullbackScalarEquiv φ 1 • z) := by
      funext z
      exact specPullbackComparisonEnd_apply φ M z
    rw [hfun]
    exact (isUnit_unitPullbackScalarEquiv_one φ).smul_bijective
  exact (e.bijective.of_comp_iff' c).mp hec

noncomputable def specPullbackSectionsBaseChangeLinearEquiv
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (M : (Spec R).Modules) [M.IsQuasicoherent] :
    let N := (Scheme.Modules.pullback (Spec.map φ)).obj M
    letI : Algebra R S := φ.hom.toAlgebra
    letI : Module R Γ(N, ⊤) := Module.compHom _ φ.hom
    S ⊗[R] Γ(M, ⊤) ≃ₗ[S] Γ(N, ⊤) := by
  let N := (Scheme.Modules.pullback (Spec.map φ)).obj M
  letI : Algebra R S := φ.hom.toAlgebra
  letI : Module R Γ(N, ⊤) := Module.compHom _ φ.hom
  exact LinearEquiv.ofBijective
    (specPullbackSectionsBaseChangeLinearMap φ M)
    (specPullbackSectionsBaseChangeLinearMap_bijective φ M)

@[simp]
lemma specPullbackSectionsBaseChangeLinearEquiv_apply
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    (z : letI : Algebra R S := φ.hom.toAlgebra; S ⊗[R] Γ(M, ⊤)) :
    let N := (Scheme.Modules.pullback (Spec.map φ)).obj M
    letI : Algebra R S := φ.hom.toAlgebra
    letI : Module R Γ(N, ⊤) := Module.compHom _ φ.hom
    specPullbackSectionsBaseChangeLinearEquiv φ M z =
      specPullbackSectionsBaseChangeLinearMap φ M z := by
  rfl

lemma canonicalAffinePullbackSectionsBaseChangeLinearMap_bijective
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (M : Y.Modules) [M.IsQuasicoherent] :
    letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    Function.Bijective
      (canonicalAffinePullbackSectionsBaseChangeLinearMap f M) := by
  letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  let iX := X.isoSpec.inv
  let iY := Y.isoSpec.inv
  let g := Spec.map f.appTop
  let N := (Scheme.Modules.pullback f).obj M
  let Mspec := (Scheme.Modules.pullback iY).obj M
  let Aff := (Scheme.Modules.pullback g).obj Mspec
  let Nspec := (Scheme.Modules.pullback iX).obj N
  letI : Mspec.IsQuasicoherent := by
    letI : IsOpenImmersion iY := inferInstance
    let e := (Scheme.Modules.restrictFunctorIsoPullback iY).app M
    exact (SheafOfModules.isQuasicoherent (Spec Γ(Y, ⊤)).ringCatSheaf).prop_of_iso
      e inferInstance
  let eAffine : Aff ≅ Nspec := pullbackAffineIsoSpecIso f M
  let eM := pullbackIsoSpecInvSectionsLinearEquiv
    (R₀ := Γ(Y, ⊤)) (RingHom.id Γ(Y, ⊤)) M
  let eN := pullbackIsoSpecInvSectionsLinearEquiv
    (R₀ := Γ(X, ⊤)) (RingHom.id Γ(X, ⊤)) N
  let eSheaf : moduleSpecΓFunctor.obj Aff ≃ₗ[Γ(X, ⊤)]
      moduleSpecΓFunctor.obj Nspec :=
    (moduleSpecΓFunctor.mapIso eAffine).toLinearEquiv
  let eTarget := eN.trans eSheaf.symm
  let eSource := TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl Γ(X, ⊤) Γ(X, ⊤)) eM
  let eSpec := specPullbackSectionsBaseChangeLinearEquiv f.appTop Mspec
  let c := canonicalAffinePullbackSectionsBaseChangeLinearMap f M
  have hc (z : Γ(X, ⊤) ⊗[Γ(Y, ⊤)] Γ(M, ⊤)) :
      eTarget (c z) = eSpec (eSource z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s m =>
        rw [show c (s ⊗ₜ[Γ(Y, ⊤)] m) =
            s • Scheme.Modules.pullbackGlobalSections f M m by
          exact canonicalAffinePullbackSectionsBaseChangeLinearMap_tmul f M s m]
        rw [map_smul]
        have heSource : eSource (s ⊗ₜ[Γ(Y, ⊤)] m) =
            s ⊗ₜ[Γ(Y, ⊤)] eM m := by
          exact TensorProduct.AlgebraTensorModule.congr_tmul _ _ _ _
        rw [heSource]
        have heSpec : eSpec (s ⊗ₜ[Γ(Y, ⊤)] eM m) =
            specPullbackSectionsBaseChangeLinearMap f.appTop Mspec
              (s ⊗ₜ[Γ(Y, ⊤)] eM m) := by
          exact specPullbackSectionsBaseChangeLinearEquiv_apply _ _ _
        rw [heSpec, specPullbackSectionsBaseChangeLinearMap_tmul]
        congr 1
        exact pullbackGlobalSections_compCongrIso iX f g iY
          (Scheme.isoSpec_inv_naturality f).symm M m
  have hcomp : Function.Bijective (eTarget ∘ c) := by
    have hfun : (eTarget ∘ c) = (eSpec ∘ eSource) := by
      funext z
      exact hc z
    rw [hfun]
    exact eSpec.bijective.comp eSource.bijective
  change Function.Bijective c
  exact (eTarget.bijective.of_comp_iff' c).mp hcomp

lemma pullbackSectionsBaseChangeLinearMap_bijective_of_isPullback
    {P X Y Z : Scheme.{u}} [IsAffine P] [IsAffine X] [IsAffine Y] [IsAffine Z]
    (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : IsPullback fst snd f g) (M : X.Modules) [M.IsQuasicoherent] :
    let N := (Scheme.Modules.pullback fst).obj M
    letI : Algebra Γ(Z, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
    letI : Module Γ(Z, ⊤) Γ(M, ⊤) := Module.compHom _ f.appTop.hom
    letI : Module Γ(Y, ⊤) Γ(N, ⊤) := Module.compHom _ snd.appTop.hom
    Function.Bijective
      (pullbackSectionsBaseChangeLinearMap fst snd f g h.w M) := by
  let N := (Scheme.Modules.pullback fst).obj M
  letI : Algebra Γ(Z, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  letI : Algebra Γ(Z, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
  letI : Algebra Γ(X, ⊤) Γ(P, ⊤) := fst.appTop.hom.toAlgebra
  letI : Algebra Γ(Y, ⊤) Γ(P, ⊤) := snd.appTop.hom.toAlgebra
  letI : Algebra Γ(Z, ⊤) Γ(P, ⊤) :=
    (fst.appTop.hom.comp f.appTop.hom).toAlgebra
  letI : IsScalarTower Γ(Z, ⊤) Γ(X, ⊤) Γ(P, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hw : fst.appTop.hom.comp f.appTop.hom =
      snd.appTop.hom.comp g.appTop.hom :=
    congrArg CommRingCat.Hom.hom (isPushout_appTop_of_isPullback h).w
  letI : IsScalarTower Γ(Z, ⊤) Γ(Y, ⊤) Γ(P, ⊤) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ DFunLike.congr_fun hw x
  letI : Algebra.IsPushout Γ(Z, ⊤) Γ(Y, ⊤) Γ(X, ⊤) Γ(P, ⊤) :=
    CommRingCat.isPushout_iff_isPushout.mp
      (isPushout_appTop_of_isPullback h).flip
  letI : Module Γ(Z, ⊤) Γ(M, ⊤) := Module.compHom _ f.appTop.hom
  letI : IsScalarTower Γ(Z, ⊤) Γ(X, ⊤) Γ(M, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : Module Γ(Y, ⊤) Γ(N, ⊤) := Module.compHom _ snd.appTop.hom
  let T := Γ(P, ⊤) ⊗[Γ(X, ⊤)] Γ(M, ⊤)
  letI : Module Γ(Y, ⊤) T :=
    Module.compHom _ (algebraMap Γ(Y, ⊤) Γ(P, ⊤))
  letI : IsScalarTower Γ(Y, ⊤) Γ(P, ⊤) T :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let eCancel :=
    (Algebra.IsPushout.cancelBaseChange Γ(Z, ⊤) Γ(Y, ⊤)
      Γ(X, ⊤) Γ(P, ⊤) Γ(M, ⊤)).symm
  let cAff := canonicalAffinePullbackSectionsBaseChangeLinearMap fst M
  let eAff : T ≃ₗ[Γ(P, ⊤)] Γ(N, ⊤) :=
    LinearEquiv.ofBijective cAff
      (canonicalAffinePullbackSectionsBaseChangeLinearMap_bijective fst M)
  let eAff' : T ≃ₗ[Γ(Y, ⊤)] Γ(N, ⊤) :=
    { toEquiv := eAff.toEquiv
      map_add' := eAff.map_add
      map_smul' := fun s x ↦ by
        change eAff ((algebraMap Γ(Y, ⊤) Γ(P, ⊤) s) • x) =
          (algebraMap Γ(Y, ⊤) Γ(P, ⊤) s) • eAff x
        exact eAff.map_smul (algebraMap Γ(Y, ⊤) Γ(P, ⊤) s) x }
  let eTotal := eCancel.trans eAff'
  let c := pullbackSectionsBaseChangeLinearMap fst snd f g h.w M
  have hc : c = eTotal.toLinearMap := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s m =>
        rw [show c (s ⊗ₜ[Γ(Z, ⊤)] m) =
            s • Scheme.Modules.pullbackGlobalSections fst M m by
          exact pullbackSectionsBaseChangeLinearMap_tmul
            fst snd f g h.w M s m]
        change _ = eTotal (s ⊗ₜ[Γ(Z, ⊤)] m)
        rw [show eTotal (s ⊗ₜ[Γ(Z, ⊤)] m) =
            eAff' (eCancel (s ⊗ₜ[Γ(Z, ⊤)] m)) by rfl]
        rw [show eCancel (s ⊗ₜ[Γ(Z, ⊤)] m) =
            (algebraMap Γ(Y, ⊤) Γ(P, ⊤) s) ⊗ₜ[Γ(X, ⊤)] m by
          exact Algebra.IsPushout.cancelBaseChange_symm_tmul _ _ _ _ _ _ _]
        rw [show eAff'
            ((algebraMap Γ(Y, ⊤) Γ(P, ⊤) s) ⊗ₜ[Γ(X, ⊤)] m) =
            algebraMap Γ(Y, ⊤) Γ(P, ⊤) s •
              Scheme.Modules.pullbackGlobalSections fst M m by
          exact canonicalAffinePullbackSectionsBaseChangeLinearMap_tmul
            fst M _ _]
        rfl
  change Function.Bijective c
  rw [hc]
  exact eTotal.bijective

noncomputable def pullbackSpecSectionsBaseChangeLinearEquiv_of_ring_isPushout
    {R S A B : CommRingCat.{u}} (f : R ⟶ A) (g : R ⟶ S)
    (fst : A ⟶ B) (snd : S ⟶ B) (h : IsPushout f g fst snd)
    (M : (Spec A).Modules) [M.IsQuasicoherent] :
    let Q := moduleSpecΓFunctor.obj M
    let N := moduleSpecΓFunctor.obj
      ((Scheme.Modules.pullback (Spec.map fst)).obj M)
    letI : Algebra R S := g.hom.toAlgebra
    letI := Module.compHom Q f.hom
    letI := Module.compHom N snd.hom
    S ⊗[R] Q ≃ₗ[S] N := by
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
      (CommRingCat.ofHom (algebraMap R S))
      (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap S B))
      (CommRingCat.ofHom (algebraMap A B)) := by
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
  let T := (ModuleCat.extendScalars fst.hom).obj Q
  letI : Module S T := Module.compHom T (algebraMap S B)
  letI : IsScalarTower S B T :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let eB := specPullbackSectionsBaseChangeLinearEquiv fst M
  let e : T ≃ₗ[S] N :=
    { toEquiv := eB.toEquiv
      map_add' := eB.map_add
      map_smul' := fun s x ↦ by
        change eB ((algebraMap S B s) • x) =
          (algebraMap S B s) • eB x
        exact eB.map_smul (algebraMap S B s) x }
  exact (Algebra.IsPushout.cancelBaseChange R S A B Q).symm.trans e

@[simp]
lemma pullbackSpecSectionsBaseChangeLinearEquiv_of_ring_isPushout_tmul
    {R S A B : CommRingCat.{u}} (f : R ⟶ A) (g : R ⟶ S)
    (fst : A ⟶ B) (snd : S ⟶ B) (h : IsPushout f g fst snd)
    (M : (Spec A).Modules) [M.IsQuasicoherent]
    (s : S) (m : moduleSpecΓFunctor.obj M) :
    let Q := moduleSpecΓFunctor.obj M
    let N := moduleSpecΓFunctor.obj
      ((Scheme.Modules.pullback (Spec.map fst)).obj M)
    letI : Algebra R S := g.hom.toAlgebra
    letI := Module.compHom Q f.hom
    letI := Module.compHom N snd.hom
    pullbackSpecSectionsBaseChangeLinearEquiv_of_ring_isPushout
        f g fst snd h M (s ⊗ₜ[R] m) =
      s • (show N from
        Scheme.Modules.pullbackGlobalSections (Spec.map fst) M m) := by
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
      (CommRingCat.ofHom (algebraMap R S))
      (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap S B))
      (CommRingCat.ofHom (algebraMap A B)) := by
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
  let T := (ModuleCat.extendScalars fst.hom).obj Q
  letI : Module S T := Module.compHom T (algebraMap S B)
  letI : IsScalarTower S B T :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  change (specPullbackSectionsBaseChangeLinearEquiv fst M)
      ((Algebra.IsPushout.cancelBaseChange R S A B Q).symm
        (s ⊗ₜ[R] m)) = _
  rw [Algebra.IsPushout.cancelBaseChange_symm_tmul,
    specPullbackSectionsBaseChangeLinearEquiv_apply,
    specPullbackSectionsBaseChangeLinearMap_tmul]
  rfl

end AlgebraicGeometry
