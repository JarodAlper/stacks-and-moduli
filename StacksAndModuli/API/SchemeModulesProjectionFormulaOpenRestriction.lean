module

public import StacksAndModuli.API.OpenImmersionPullbackPushforwardCounitBaseChange
public import StacksAndModuli.API.SchemeModulesProjectionFormula

/-!
# Projection formula under restriction to an open cartesian square

This file compares the projection-formula morphism with its restriction through an open
cartesian square. The comparison is reduced to the pullback--tensor coherence square; the
counit compatibility is supplied by the open Beck--Chevalley API.

Main declarations:

* `AlgebraicGeometry.Scheme.Modules.restrictedProjectionFormulaHomOfOpenSquare_eq`;
* `restrictedProjectionFormulaHomOfOpenSquare_eq_of_pullbackTensorCompatibility`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

/-- The source comparison for restricting a projection-formula morphism through
an open cartesian square. -/
noncomputable def projectionFormulaRestrictSourceIsoOfOpenSquare
    {Y Z W P : Scheme.{u}} (i : W ⟶ Z) (g : P ⟶ Y)
    (k : P ⟶ W) (j : Y ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion j]
    (hsq : g ≫ j = k ≫ i)
    (hopen : ∀ U : Y.Opens, k ''ᵁ (g ⁻¹ᵁ U) = i ⁻¹ᵁ (j ''ᵁ U))
    (K : Z.Modules) (F : W.Modules) :
    (restrictFunctor j).obj (tensor K ((pushforward i).obj F)) ≅
      tensor ((restrictFunctor j).obj K)
        ((pushforward g).obj ((restrictFunctor k).obj F)) :=
  restrictTensorIso j K ((pushforward i).obj F) ≪≫
    tensorRightIso ((restrictFunctor j).obj K)
      (restrictPushforwardIsoOfOpenSquare i g k j hsq hopen F)

/-- The target comparison for restricting a projection-formula morphism through
an open cartesian square. -/
noncomputable def projectionFormulaRestrictTargetIsoOfOpenSquare
    {Y Z W P : Scheme.{u}} (i : W ⟶ Z) (g : P ⟶ Y)
    (k : P ⟶ W) (j : Y ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion j]
    (hsq : g ≫ j = k ≫ i)
    (hopen : ∀ U : Y.Opens, k ''ᵁ (g ⁻¹ᵁ U) = i ⁻¹ᵁ (j ''ᵁ U))
    (K : Z.Modules) (F : W.Modules) :
    (restrictFunctor j).obj
        ((pushforward i).obj (tensor ((pullback i).obj K) F)) ≅
      (pushforward g).obj
        (tensor ((pullback g).obj ((restrictFunctor j).obj K))
          ((restrictFunctor k).obj F)) :=
  restrictPushforwardIsoOfOpenSquare i g k j hsq hopen
      (tensor ((pullback i).obj K) F) ≪≫
    (pushforward g).mapIso
      (restrictTensorIso k ((pullback i).obj K) F ≪≫
        tensorLeftIso
          ((restrictPullbackIsoOfOpenSquare i g k j hsq).app K)
          ((restrictFunctor k).obj F))

/-- Restrict the global projection-formula morphism and transport its source
and target through the canonical open-square comparisons. -/
noncomputable def restrictedProjectionFormulaHomOfOpenSquare
    {Y Z W P : Scheme.{u}} (i : W ⟶ Z) (g : P ⟶ Y)
    (k : P ⟶ W) (j : Y ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion j]
    (hsq : g ≫ j = k ≫ i)
    (hopen : ∀ U : Y.Opens, k ''ᵁ (g ⁻¹ᵁ U) = i ⁻¹ᵁ (j ''ᵁ U))
    (K : Z.Modules) (F : W.Modules) :
    tensor ((restrictFunctor j).obj K)
        ((pushforward g).obj ((restrictFunctor k).obj F)) ⟶
      (pushforward g).obj
        (tensor ((pullback g).obj ((restrictFunctor j).obj K))
          ((restrictFunctor k).obj F)) :=
  (projectionFormulaRestrictSourceIsoOfOpenSquare
      i g k j hsq hopen K F).inv ≫
    (restrictFunctor j).map (projectionFormulaHom i K F) ≫
    (projectionFormulaRestrictTargetIsoOfOpenSquare
      i g k j hsq hopen K F).hom

/-- The precise oplax-monoidal coherence needed to compare projection-formula
morphisms through an open square. -/
abbrev PullbackTensorComparisonOpenSquareCompatibility
    {Y Z W P : Scheme.{u}} (i : W ⟶ Z) (g : P ⟶ Y)
    (k : P ⟶ W) (j : Y ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion j]
    (hsq : g ≫ j = k ≫ i) (K G : Z.Modules) : Prop :=
  let α := restrictPullbackIsoOfOpenSquare i g k j hsq
  α.hom.app (tensor K G) ≫
        (pullback g).map (restrictTensorIso j K G).hom ≫
        pullbackTensorComparison g
          ((restrictFunctor j).obj K) ((restrictFunctor j).obj G) =
    (restrictFunctor k).map (pullbackTensorComparison i K G) ≫
      (restrictTensorIso k ((pullback i).obj K) ((pullback i).obj G)).hom ≫
      tensorMapLeft (α.hom.app K) ((restrictFunctor k).obj ((pullback i).obj G)) ≫
      tensorMapRight ((pullback g).obj ((restrictFunctor j).obj K))
        (α.hom.app G)

/-- The counit compatibility used in the projection-formula restriction
calculation. This is the expanded type of the existing open-square counit lemma. -/
abbrev PullbackPushforwardCounitOpenSquareCompatibility
    {Y Z W P : Scheme.{u}} (i : W ⟶ Z) (g : P ⟶ Y)
    (k : P ⟶ W) (j : Y ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion j]
    (hsq : g ≫ j = k ≫ i)
    (hopen : ∀ U : Y.Opens, k ''ᵁ (g ⁻¹ᵁ U) = i ⁻¹ᵁ (j ''ᵁ U))
    (M : W.Modules) : Prop :=
  let α := restrictPullbackIsoOfOpenSquare i g k j hsq
  let bc := restrictPushforwardIsoOfOpenSquare i g k j hsq hopen M
  α.hom.app ((pushforward i).obj M) ≫
        (pullback g).map bc.hom ≫
        (pullbackPushforwardAdjunction g).counit.app
          ((restrictFunctor k).obj M) =
    (restrictFunctor k).map
      ((pullbackPushforwardAdjunction i).counit.app M)

theorem restrictedProjectionFormulaHomOfOpenSquare_eq
    {Y Z W P : Scheme.{u}} (i : W ⟶ Z) (g : P ⟶ Y)
    (k : P ⟶ W) (j : Y ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion j]
    (hsq : g ≫ j = k ≫ i)
    (hopen : ∀ U : Y.Opens, k ''ᵁ (g ⁻¹ᵁ U) = i ⁻¹ᵁ (j ''ᵁ U))
    (K : Z.Modules) (F : W.Modules)
    (hTensor : PullbackTensorComparisonOpenSquareCompatibility
      i g k j hsq K ((pushforward i).obj F))
    (hCounit : ∀ M : W.Modules,
      PullbackPushforwardCounitOpenSquareCompatibility
        i g k j hsq hopen M) :
    restrictedProjectionFormulaHomOfOpenSquare
        i g k j hsq hopen K F =
      projectionFormulaHom g ((restrictFunctor j).obj K)
        ((restrictFunctor k).obj F) := by
  let rK := (restrictFunctor j).obj K
  let rF := (restrictFunctor k).obj F
  let A := tensor K ((pushforward i).obj F)
  let M := tensor ((pullback i).obj K) F
  let q := projectionFormulaHom i K F
  let m := pullbackTensorComparison i K ((pushforward i).obj F) ≫
    tensorMapRight ((pullback i).obj K)
      ((pullbackPushforwardAdjunction i).counit.app F)
  let α := restrictPullbackIsoOfOpenSquare i g k j hsq
  let s := projectionFormulaRestrictSourceIsoOfOpenSquare
    i g k j hsq hopen K F
  let bc := restrictPushforwardIsoOfOpenSquare i g k j hsq hopen M
  let bcF := restrictPushforwardIsoOfOpenSquare i g k j hsq hopen F
  let rt := restrictTensorIso k ((pullback i).obj K) F ≪≫
    tensorLeftIso ((restrictPullbackIsoOfOpenSquare i g k j hsq).app K) rF
  have hOuter :
      (pullback g).map ((restrictFunctor j).map q) ≫
          (pullback g).map bc.hom ≫
          (pullbackPushforwardAdjunction g).counit.app
            ((restrictFunctor k).obj M) =
        α.inv.app A ≫ (restrictFunctor k).map m := by
    have hnat := α.hom.naturality q
    simp only [Functor.comp_map] at hnat
    have hnat' :
        α.inv.app A ≫
            (restrictFunctor k).map ((pullback i).map q) ≫
            α.hom.app ((pushforward i).obj M) =
          (pullback g).map ((restrictFunctor j).map q) := by
      dsimp only [A, M]
      calc
        α.inv.app (tensor K ((pushforward i).obj F)) ≫
              (restrictFunctor k).map ((pullback i).map q) ≫
              α.hom.app ((pushforward i).obj
                (tensor ((pullback i).obj K) F)) =
            α.inv.app (tensor K ((pushforward i).obj F)) ≫
              (α.hom.app (tensor K ((pushforward i).obj F)) ≫
                (pullback g).map ((restrictFunctor j).map q)) := by
          rw [← hnat]
        _ = (pullback g).map ((restrictFunctor j).map q) := by simp
    rw [← hnat']
    simp only [Category.assoc]
    rw [hCounit M]
    rw [← Functor.map_comp]
    have hm := (pullbackPushforwardAdjunction i).homEquiv_counit A M q
    have hmq : ((pullbackPushforwardAdjunction i).homEquiv A M).symm q = m := by
      dsimp only [q, m, A, M, projectionFormulaHom]
      simp only [Functor.id_obj, Equiv.symm_apply_apply]
    rw [← hm, hmq]
  have hTensorInv :
      (pullback g).map
          (restrictTensorIso j K ((pushforward i).obj F)).inv ≫
        α.inv.app (tensor K ((pushforward i).obj F)) ≫
        (restrictFunctor k).map
          (pullbackTensorComparison i K ((pushforward i).obj F)) ≫
        (restrictTensorIso k ((pullback i).obj K)
          ((pullback i).obj ((pushforward i).obj F))).hom ≫
        tensorMapLeft ((α.app K).hom)
          ((restrictFunctor k).obj
            ((pullback i).obj ((pushforward i).obj F))) =
      pullbackTensorComparison g ((restrictFunctor j).obj K)
          ((restrictFunctor j).obj ((pushforward i).obj F)) ≫
        tensorMapRight ((pullback g).obj ((restrictFunctor j).obj K))
          (α.inv.app ((pushforward i).obj F)) := by
    let a := α.app (tensor K ((pushforward i).obj F)) ≪≫
      (pullback g).mapIso
        (restrictTensorIso j K ((pushforward i).obj F))
    let b := tensorRightIso
      ((pullback g).obj ((restrictFunctor j).obj K))
      (α.app ((pushforward i).obj F))
    change a.inv ≫
          (restrictFunctor k).map
            (pullbackTensorComparison i K ((pushforward i).obj F)) ≫
          (restrictTensorIso k ((pullback i).obj K)
            ((pullback i).obj ((pushforward i).obj F))).hom ≫
          tensorMapLeft ((α.app K).hom)
            ((restrictFunctor k).obj
              ((pullback i).obj ((pushforward i).obj F))) =
        pullbackTensorComparison g ((restrictFunctor j).obj K)
            ((restrictFunctor j).obj ((pushforward i).obj F)) ≫ b.inv
    rw [← cancel_epi a.hom]
    simp only [Iso.hom_inv_id_assoc]
    change
      (restrictFunctor k).map
            (pullbackTensorComparison i K ((pushforward i).obj F)) ≫
          (restrictTensorIso k ((pullback i).obj K)
            ((pullback i).obj ((pushforward i).obj F))).hom ≫
          tensorMapLeft ((α.app K).hom)
            ((restrictFunctor k).obj
              ((pullback i).obj ((pushforward i).obj F))) =
        (α.hom.app (tensor K ((pushforward i).obj F)) ≫
          (pullback g).map
            (restrictTensorIso j K ((pushforward i).obj F)).hom ≫
          pullbackTensorComparison g ((restrictFunctor j).obj K)
            ((restrictFunctor j).obj ((pushforward i).obj F))) ≫ b.inv
    simp only [Iso.app_hom]
    rw [hTensor]
    dsimp only [b, tensorRightIso]
    dsimp only [α]
    simp only [Category.assoc]
    rw [← tensorMapRight_comp]
    simp only [Iso.app_inv]
    rw [Iso.hom_inv_id_app,
      tensorMapRight_id
        ((pullback g).obj ((restrictFunctor j).obj K))
        ((pullback i ⋙ restrictFunctor k).obj ((pushforward i).obj F))]
    simp only [Functor.comp_obj, Category.comp_id]
  have hRestrictTensor :
      (restrictFunctor k).map
          (tensorMapRight ((pullback i).obj K)
            ((pullbackPushforwardAdjunction i).counit.app F)) ≫
        (restrictTensorIso k ((pullback i).obj K) F).hom ≫
        tensorMapLeft ((α.app K).hom) ((restrictFunctor k).obj F) =
      (restrictTensorIso k ((pullback i).obj K)
          ((pullback i).obj ((pushforward i).obj F))).hom ≫
        tensorMapLeft ((α.app K).hom)
          ((restrictFunctor k).obj
            ((pullback i).obj ((pushforward i).obj F))) ≫
        tensorMapRight ((pullback g).obj ((restrictFunctor j).obj K))
          ((restrictFunctor k).map
            ((pullbackPushforwardAdjunction i).counit.app F)) := by
    have hn := restrictTensorIso_naturality k
      (φ := 𝟙 ((pullback i).obj K))
      ((pullbackPushforwardAdjunction i).counit.app F)
    simp only [Functor.id_obj, Functor.comp_obj] at hn
    rw [(restrictFunctor k).map_id] at hn
    simp only [tensorMapLeft_id, Category.id_comp] at hn
    have hex := tensorMap_exchange (α.hom.app K)
      ((restrictFunctor k).map
        ((pullbackPushforwardAdjunction i).counit.app F))
    simp only [Functor.id_obj, Functor.comp_obj] at hex
    calc
      (restrictFunctor k).map
            (tensorMapRight ((pullback i).obj K)
              ((pullbackPushforwardAdjunction i).counit.app F)) ≫
          (restrictTensorIso k ((pullback i).obj K) F).hom ≫
          tensorMapLeft ((α.app K).hom) ((restrictFunctor k).obj F) =
        ((restrictTensorIso k ((pullback i).obj K)
            ((pullback i).obj ((pushforward i).obj F))).hom ≫
          tensorMapRight
            ((restrictFunctor k).obj ((pullback i).obj K))
            ((restrictFunctor k).map
              ((pullbackPushforwardAdjunction i).counit.app F))) ≫
          tensorMapLeft ((α.app K).hom) ((restrictFunctor k).obj F) := by
            simpa only [Category.assoc] using congrArg
              (fun z ↦ z ≫ tensorMapLeft ((α.app K).hom)
                ((restrictFunctor k).obj F)) hn
      _ = (restrictTensorIso k ((pullback i).obj K)
              ((pullback i).obj ((pushforward i).obj F))).hom ≫
            (tensorMapLeft ((α.app K).hom)
                ((restrictFunctor k).obj
                  ((pullback i).obj ((pushforward i).obj F))) ≫
              tensorMapRight
                ((pullback g).obj ((restrictFunctor j).obj K))
                ((restrictFunctor k).map
                  ((pullbackPushforwardAdjunction i).counit.app F))) := by
          simpa only [Category.assoc, Iso.app_hom] using congrArg
            (fun z ↦ (restrictTensorIso k ((pullback i).obj K)
              ((pullback i).obj ((pushforward i).obj F))).hom ≫ z) hex
      _ = _ := rfl
  have hCounitInv :
      (pullback g).map
          (restrictPushforwardIsoOfOpenSquare
            i g k j hsq hopen F).inv ≫
        α.inv.app ((pushforward i).obj F) ≫
        (restrictFunctor k).map
          ((pullbackPushforwardAdjunction i).counit.app F) =
      (pullbackPushforwardAdjunction g).counit.app
        ((restrictFunctor k).obj F) := by
    rw [← hCounit F]
    rw [Iso.inv_hom_id_app_assoc]
    rw [← Category.assoc, ← Functor.map_comp]
    simp
  have hPullbackNaturality := pullbackTensorComparison_naturality_right g
    ((restrictFunctor j).obj K) bcF.inv
  have hRightCounit :
      tensorMapRight ((pullback g).obj ((restrictFunctor j).obj K))
          ((pullback g).map bcF.inv) ≫
        tensorMapRight ((pullback g).obj ((restrictFunctor j).obj K))
          (α.inv.app ((pushforward i).obj F)) ≫
        tensorMapRight ((pullback g).obj ((restrictFunctor j).obj K))
          ((restrictFunctor k).map
            ((pullbackPushforwardAdjunction i).counit.app F)) =
      tensorMapRight ((pullback g).obj ((restrictFunctor j).obj K))
        ((pullbackPushforwardAdjunction g).counit.app
          ((restrictFunctor k).obj F)) := by
    rw [← tensorMapRight_comp, ← tensorMapRight_comp, hCounitInv]
  let adj := pullbackPushforwardAdjunction g
  change s.inv ≫
      (((restrictFunctor j).map (projectionFormulaHom i K F) ≫ bc.hom) ≫
        (pushforward g).map rt.hom) =
    projectionFormulaHom g rK rF
  apply (adj.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm]
  rw [Adjunction.homEquiv_naturality_right_symm]
  dsimp only [projectionFormulaHom]
  dsimp only [adj]
  rw [Adjunction.homEquiv_counit]
  rw [Functor.map_comp]
  dsimp only [rK, rF]
  simp only [Functor.comp_obj]
  rw [Equiv.symm_apply_apply]
  change (pullback g).map s.inv ≫
      ((((pullback g).map ((restrictFunctor j).map q) ≫
          (pullback g).map bc.hom) ≫
        (pullbackPushforwardAdjunction g).counit.app
          ((restrictFunctor k).obj M)) ≫ rt.hom) = _
  have hOuterFull := congrArg
    (fun z ↦ (pullback g).map s.inv ≫ z ≫ rt.hom) hOuter
  simp only [Category.assoc] at hOuterFull ⊢
  rw [hOuterFull]
  dsimp only [s, A, m, rt, projectionFormulaRestrictSourceIsoOfOpenSquare,
    tensorRightIso, tensorLeftIso]
  simp only [Functor.map_comp, Functor.comp_obj, Iso.trans_inv, Iso.trans_hom,
    Category.assoc]
  dsimp only [α, rF] at hRestrictTensor hTensorInv hRightCounit
  dsimp only [α, rF]
  rw [hRestrictTensor]
  have hTensorInvFull := congrArg
    (fun z ↦
      (pullback g).map
          (tensorMapRight ((restrictFunctor j).obj K)
            (restrictPushforwardIsoOfOpenSquare
              i g k j hsq hopen F).inv) ≫
        z ≫
        tensorMapRight ((pullback g).obj ((restrictFunctor j).obj K))
          ((restrictFunctor k).map
            ((pullbackPushforwardAdjunction i).counit.app F))) hTensorInv
  simp only [Category.assoc] at hTensorInvFull
  rw [hTensorInvFull]
  dsimp only [bcF] at hPullbackNaturality hRightCounit
  have hPullbackNaturalityFull := congrArg
    (fun z ↦ z ≫
      tensorMapRight ((pullback g).obj ((restrictFunctor j).obj K))
          ((restrictPullbackIsoOfOpenSquare i g k j hsq).inv.app
            ((pushforward i).obj F)) ≫
        tensorMapRight ((pullback g).obj ((restrictFunctor j).obj K))
          ((restrictFunctor k).map
            ((pullbackPushforwardAdjunction i).counit.app F)))
    hPullbackNaturality
  simp only [Category.assoc] at hPullbackNaturalityFull
  rw [hPullbackNaturalityFull]
  have hRightCounitFull := congrArg
    (fun z ↦
      pullbackTensorComparison g ((restrictFunctor j).obj K)
          ((pushforward g).obj ((restrictFunctor k).obj F)) ≫ z)
    hRightCounit
  simpa only [Category.assoc] using hRightCounitFull

/-- Restriction compatibility for the projection-formula map, conditional only
on the pullback--tensor coherence square. The counit square is supplied by the
existing open Beck--Chevalley API. -/
theorem restrictedProjectionFormulaHomOfOpenSquare_eq_of_pullbackTensorCompatibility
    {Y Z W P : Scheme.{u}} (i : W ⟶ Z) (g : P ⟶ Y)
    (k : P ⟶ W) (j : Y ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion j]
    (hsq : g ≫ j = k ≫ i)
    (hopen : ∀ U : Y.Opens, k ''ᵁ (g ⁻¹ᵁ U) = i ⁻¹ᵁ (j ''ᵁ U))
    (K : Z.Modules) (F : W.Modules)
    (hTensor : PullbackTensorComparisonOpenSquareCompatibility
      i g k j hsq K ((pushforward i).obj F)) :
    restrictedProjectionFormulaHomOfOpenSquare
        i g k j hsq hopen K F =
      projectionFormulaHom g ((restrictFunctor j).obj K)
        ((restrictFunctor k).obj F) := by
  apply restrictedProjectionFormulaHomOfOpenSquare_eq
    i g k j hsq hopen K F hTensor
  intro M
  dsimp only [PullbackPushforwardCounitOpenSquareCompatibility]
  simpa only [restrictPullbackPushforwardIsoOfOpenSquare, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom, Category.assoc] using
      restrictPullbackPushforwardIsoOfOpenSquare_hom_counit
        i g k j hsq hopen M

end AlgebraicGeometry.Scheme.Modules
