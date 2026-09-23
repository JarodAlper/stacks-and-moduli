module

public import StacksAndModuli.API.FreeStackCompletionInterpretation.Evaluation

/-!
# Relations and the extension out of the free stack completion

This module evaluates relation derivations, descends the semantic evaluator to the
quotients, and packages the resulting based functor and its comparison with the
canonical inclusion.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Functor

universe v u w z yv yu

namespace CategoryTheory.BasedCategory.FreeStackCompletion.Interpretation

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X : BasedCategory.{w, z} C}
variable {Y : BasedCategory.{yv, yu} C} [BasedCategory.IsStack J Y]

/-- Evaluate a relation derivation in a target stack. -/
noncomputable def evaluateRel (F : X ⥤ᵇ Y) {rho phi psi a b : Pre J X} {S T : C}
    {f g : S ⟶ T} (h : IsRel J X rho phi psi a b f g) : RelResult F h := by
  refine IsRel.rec (C := C) (J := J) (X := X)
    (motive_1 := fun _ _ h ↦ ObjCoreResult F h)
    (motive_2 := fun _ _ _ _ _ _ h ↦ HomResult F h)
    (motive_3 := fun _ _ _ _ _ _ _ _ _ h ↦ RelResult F h)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro a
    exact ⟨⟨inclObj F a, .incl a _ rfl⟩, PUnit.unit⟩
  · intro S T b hb f ihB
    exact ⟨⟨(pullArrow (J := J) ihB.1.1 f).source,
      .pull hb ihB.1.1 ihB.1.2 f _ rfl⟩, PUnit.unit⟩
  · intro S R Dobj Dmap hDobj hDmap idRel compRel hId hComp
      ihObj ihMap ihId ihComp
    have source_eq {q r : R.1.arrows.category} (k : q ⟶ r) :
        (ihMap k).1.source = (ihObj q).1.1 := by
      have hsem := (HomEvaluationStep.endpoints_unique F (ihMap k).2).1
        (ihObj q).1.2 rfl
      exact eq_of_heq (congrArgHEq ObjSemantic.value hsem)
    have target_eq {q r : R.1.arrows.category} (k : q ⟶ r) :
        (ihMap k).1.target = (ihObj r).1.1 := by
      have hsem := (HomEvaluationStep.endpoints_unique F (ihMap k).2).2
        (ihObj r).1.2 rfl
      exact eq_of_heq (congrArgHEq ObjSemantic.value hsem)
    let mapData {q r : R.1.arrows.category} (k : q ⟶ r) :
        HomData Y (ihObj q).1.1 (ihObj r).1.1 k.hom.left :=
      (ihMap k).1.toHomDataOfEndpoints (ihObj q).1.1 (ihObj r).1.1
        (source_eq k) (target_eq k)
    have mapStep {q r : R.1.arrows.category} (k : q ⟶ r) :
        HomEvaluationStep F
          ⟨Dmap k, Dobj q, Dobj r, q.obj.left, r.obj.left, k.hom.left,
            hDmap k, (mapData k).toArrowData⟩ := by
      rw [ArrowData.toHomDataOfEndpoints_toArrowData]
      exact (ihMap k).2
    have map_id (q : R.1.arrows.category) :
        (mapData (𝟙 q)).hom = 𝟙 (ihObj q).1.1.obj := by
      let identityStep : HomEvaluationStep F
          ⟨.homId (Dobj q), Dobj q, Dobj q, q.obj.left, q.obj.left,
            𝟙 q.obj.left, ⟨IsHom.id (hDobj q)⟩, idArrow (ihObj q).1.1⟩ :=
        .id (hDobj q) (ihObj q).1.1 (ihObj q).1.2 _ rfl
      exact eq_of_heq (RelEvaluationStep.hom_heq F (ihId q).2
        (eL := mapStep (𝟙 q)) (eR := identityStep) (hL := rfl) (hR := rfl))
    have map_comp {q r s : R.1.arrows.category} (k : q ⟶ r) (l : r ⟶ s) :
        (mapData (k ≫ l)).hom = (mapData k).hom ≫ (mapData l).hom := by
      let compositeStep : HomEvaluationStep F
          ⟨.homComp (Dmap k) (Dmap l), Dobj q, Dobj s, q.obj.left, s.obj.left,
            k.hom.left ≫ l.hom.left, ⟨IsHom.comp (hDmap k) (hDmap l)⟩,
            compArrow (mapData k) (mapData l)⟩ :=
        .comp (hDmap k) (hDmap l) (ihObj q).1.1 (ihObj r).1.1 (ihObj s).1.1
          (mapData k) (mapData l) (mapStep k) (mapStep l) _ rfl
      have hh := RelEvaluationStep.hom_heq F (ihComp k l).2
        (eL := compositeStep) (eR := mapStep (k ≫ l))
        (hL := rfl) (hR := rfl)
      exact (eq_of_heq hh).symm
    let D : DescentOutput (Y := Y) R :=
      { obj := fun q ↦ (ihObj q).1.1
        map := fun {_ _} k ↦ (mapData k).hom
        mapLift := fun {_ _} k ↦ (mapData k).isLift
        map_id := map_id
        map_comp := map_comp }
    have eObj (q : R.1.arrows.category) : ObjEvaluationStep F
        ⟨Dobj q, q.obj.left, hDobj q, D.obj q⟩ := (ihObj q).1.2
    have eMap {q r : R.1.arrows.category} (k : q ⟶ r) : HomEvaluationStep F
        ⟨Dmap k, Dobj q, Dobj r, q.obj.left, r.obj.left, k.hom.left,
          hDmap k, D.mapArrow k⟩ := mapStep k
    have eId (q : R.1.arrows.category) : RelEvaluationStep F
        ⟨idRel q, Dmap (𝟙 q), .homId (Dobj q), Dobj q, Dobj q,
          q.obj.left, q.obj.left, 𝟙 q.obj.left, 𝟙 q.obj.left, hId q,
          D.idEquation q⟩ := by
      have hleft : HomEvaluationStep F
          ⟨Dmap (𝟙 q), Dobj q, Dobj q, q.obj.left, q.obj.left,
            𝟙 q.obj.left, (hId q).leftHom, (D.idEquation q).leftArrow⟩ := by
        apply HomEvaluationStep.reindex F (eMap (𝟙 q)) (by simp)
        exact ArrowData.heq_of_base_eq _ _ (by simp) rfl rfl (HEq.rfl)
      have hright : HomEvaluationStep F
          ⟨.homId (Dobj q), Dobj q, Dobj q, q.obj.left, q.obj.left,
            𝟙 q.obj.left, (hId q).rightHom, (D.idEquation q).rightArrow⟩ := by
        apply HomEvaluationStep.reindex F
          (.id (hDobj q) (D.obj q) (eObj q) _ rfl) rfl
        exact ArrowData.heq_of_base_eq _ _ rfl rfl rfl (HEq.rfl)
      exact .mk (hId q) (D.idEquation q) hleft hright _ rfl
    have eComp {q r s : R.1.arrows.category} (k : q ⟶ r) (l : r ⟶ s) :
        RelEvaluationStep F
          ⟨compRel k l, .homComp (Dmap k) (Dmap l), Dmap (k ≫ l),
            Dobj q, Dobj s, q.obj.left, s.obj.left,
            k.hom.left ≫ l.hom.left, (k ≫ l).hom.left, hComp k l,
            D.compEquation k l⟩ := by
      have hleft : HomEvaluationStep F
          ⟨.homComp (Dmap k) (Dmap l), Dobj q, Dobj s, q.obj.left, s.obj.left,
            k.hom.left ≫ l.hom.left, (hComp k l).leftHom,
            (D.compEquation k l).leftArrow⟩ := by
        apply HomEvaluationStep.reindex F
          (.comp (hDmap k) (hDmap l) (D.obj q) (D.obj r) (D.obj s)
            (mapData k) (mapData l) (eMap k) (eMap l) _ rfl) rfl
        exact ArrowData.heq_of_base_eq _ _ rfl rfl rfl (HEq.rfl)
      have hright : HomEvaluationStep F
          ⟨Dmap (k ≫ l), Dobj q, Dobj s, q.obj.left, s.obj.left,
            (k ≫ l).hom.left, (hComp k l).rightHom,
            (D.compEquation k l).rightArrow⟩ := by
        apply HomEvaluationStep.reindex F (eMap (k ≫ l)) rfl
        exact ArrowData.heq_of_base_eq _ _ rfl rfl rfl (HEq.rfl)
      exact .mk (hComp k l) (D.compEquation k l) hleft hright _ rfl
    exact ⟨⟨D.gluedObj,
      .glue R Dobj Dmap hDobj hDmap idRel compRel hId hComp D
        eObj eMap eId eComp _ rfl⟩,
      ⟨rfl, hDobj, hDmap, hId, hComp, HEq.rfl,
        D, eObj, eMap, eId, eComp, HEq.rfl⟩⟩
  · intro a b f
    exact ⟨inclArrow F f, .incl f _ rfl⟩
  · intro S a ha ihA
    exact ⟨idArrow ihA.1.1, .id ha ihA.1.1 ihA.1.2 _ rfl⟩
  · intro R S T a b c phi psi p q hphi hpsi ihPhi ihPsi
    have hmid : ihPhi.1.target = ihPsi.1.source := by
      let phiTarget := (HomEvaluationStep.endpointSteps F ihPhi.2).2
      let psiSource := (HomEvaluationStep.endpointSteps F ihPsi.2).1
      have hsem := ObjEvaluationStep.value_unique F phiTarget.2 psiSource.2 rfl
      exact eq_of_heq (congrArgHEq ObjSemantic.value hsem)
    let phiData := ihPhi.1.toHomData
    let psiData := ihPsi.1.toHomDataOfEndpoints ihPhi.1.target ihPsi.1.target
      hmid.symm rfl
    have psiStep : HomEvaluationStep F
        ⟨psi, b, c, S, T, q, hpsi, psiData.toArrowData⟩ := by
      rw [ArrowData.toHomDataOfEndpoints_toArrowData]
      exact ihPsi.2
    exact ⟨compArrow phiData psiData,
      .comp hphi hpsi ihPhi.1.source ihPhi.1.target ihPsi.1.target
        phiData psiData ihPhi.2 psiStep _ rfl⟩
  · intro S T b hb f ihB
    exact ⟨pullArrow (J := J) ihB.1.1 f,
      .pullMap hb ihB.1.1 ihB.1.2 f _ rfl⟩
  · intro R S T a b c cart phi p f g hcart hphi hp ihCart ihPhi
    have htarget : ihCart.1.target = ihPhi.1.target := by
      let cartTarget := (HomEvaluationStep.endpointSteps F ihCart.2).2
      let phiTarget := (HomEvaluationStep.endpointSteps F ihPhi.2).2
      have hsem := ObjEvaluationStep.value_unique F cartTarget.2 phiTarget.2 rfl
      exact eq_of_heq (congrArgHEq ObjSemantic.value hsem)
    let cartData := ihCart.1.toHomData
    let phiData := ihPhi.1.toHomDataOfEndpoints ihPhi.1.source ihCart.1.target
      rfl htarget.symm
    have phiStep : HomEvaluationStep F
        ⟨phi, c, b, R, T, p, hphi, phiData.toArrowData⟩ := by
      rw [ArrowData.toHomDataOfEndpoints_toArrowData]
      exact ihPhi.2
    exact ⟨factorArrow (J := J) cartData phiData hp,
      .factor f g hcart hphi hp ihCart.1.source ihCart.1.target ihPhi.1.source
        cartData phiData ihCart.2 phiStep _ rfl⟩
  · intro S R Dobj Dmap idRel compRel hglue q ihGlue
    rcases ihGlue.2 with ⟨hbase, hDobj, hDmap, hId, hComp, hglue_heq,
      D, eObj, eMap, eId, eComp, hvalue⟩
    cases hbase
    have hglue_eq : hglue =
        .glue R Dobj Dmap hDobj hDmap idRel compRel hId hComp :=
      eq_of_heq hglue_heq
    exact ⟨D.glueArrow q,
      .glueMap R Dobj Dmap idRel compRel hglue hDobj hDmap hId hComp hglue_eq
        D eObj eMap eId eComp q _ rfl⟩
  · intro S R Dobj Dmap a b etaTerm thetaTerm ha hb hDobj hDmap idRel compRel
      hId hComp heta htheta etaNat thetaNat hetaNat hthetaNat
      ihA ihB ihDobj ihDmap ihId ihComp ihEta ihTheta ihEtaNat ihThetaNat
    let DE := buildDescentEvaluation F R Dobj Dmap hDobj hDmap idRel compRel
      hId hComp (fun q ↦ (ihDobj q).1) ihDmap ihId ihComp
    let D := DE.D
    let A := ihA.1.1
    let B := ihB.1.1
    have etaSource (q : R.1.arrows.category) :
        (ihEta q).1.source = D.obj q := by
      have hsem := (HomEvaluationStep.endpoints_unique F (ihEta q).2).1
        (DE.eObj q) rfl
      exact eq_of_heq (congrArgHEq ObjSemantic.value hsem)
    have etaTarget (q : R.1.arrows.category) :
        (ihEta q).1.target = A := by
      have hsem := (HomEvaluationStep.endpoints_unique F (ihEta q).2).2
        ihA.1.2 rfl
      exact eq_of_heq (congrArgHEq ObjSemantic.value hsem)
    let etaData (q : R.1.arrows.category) : HomData Y (D.obj q) A q.obj.hom :=
      (ihEta q).1.toHomDataOfEndpoints (D.obj q) A (etaSource q) (etaTarget q)
    have etaStep (q : R.1.arrows.category) : HomEvaluationStep F
        ⟨etaTerm q, Dobj q, a, q.obj.left, S, q.obj.hom, heta q,
          (etaData q).toArrowData⟩ := by
      rw [ArrowData.toHomDataOfEndpoints_toArrowData]
      exact (ihEta q).2
    have etaNaturality {q r : R.1.arrows.category} (k : q ⟶ r) :
        D.map k ≫ (etaData r).hom = (etaData q).hom := by
      let mapData := (D.mapArrow k).toHomData
      let compositeStep : HomEvaluationStep F
          ⟨.homComp (Dmap k) (etaTerm r), Dobj q, a, q.obj.left, S,
            k.hom.left ≫ r.obj.hom, ⟨IsHom.comp (hDmap k) (heta r)⟩,
            compArrow mapData (etaData r)⟩ :=
        .comp (hDmap k) (heta r) (D.obj q) (D.obj r) A mapData (etaData r)
          (DE.eMap k) (etaStep r) _ rfl
      have hh := RelEvaluationStep.hom_heq F (ihEtaNat k).2
        (eL := compositeStep) (eR := etaStep q) (hL := rfl) (hR := rfl)
      exact eq_of_heq hh
    let eta : CoconeOutput D A :=
      { hom := fun q ↦ (etaData q).hom
        homLift := fun q ↦ (etaData q).isLift
        naturality := fun {_ _} k ↦ etaNaturality k }
    have thetaSource (q : R.1.arrows.category) :
        (ihTheta q).1.source = D.obj q := by
      have hsem := (HomEvaluationStep.endpoints_unique F (ihTheta q).2).1
        (DE.eObj q) rfl
      exact eq_of_heq (congrArgHEq ObjSemantic.value hsem)
    have thetaTarget (q : R.1.arrows.category) :
        (ihTheta q).1.target = B := by
      have hsem := (HomEvaluationStep.endpoints_unique F (ihTheta q).2).2
        ihB.1.2 rfl
      exact eq_of_heq (congrArgHEq ObjSemantic.value hsem)
    let thetaData (q : R.1.arrows.category) : HomData Y (D.obj q) B q.obj.hom :=
      (ihTheta q).1.toHomDataOfEndpoints (D.obj q) B (thetaSource q) (thetaTarget q)
    have thetaStep (q : R.1.arrows.category) : HomEvaluationStep F
        ⟨thetaTerm q, Dobj q, b, q.obj.left, S, q.obj.hom, htheta q,
          (thetaData q).toArrowData⟩ := by
      rw [ArrowData.toHomDataOfEndpoints_toArrowData]
      exact (ihTheta q).2
    have thetaNaturality {q r : R.1.arrows.category} (k : q ⟶ r) :
        D.map k ≫ (thetaData r).hom = (thetaData q).hom := by
      let mapData := (D.mapArrow k).toHomData
      let compositeStep : HomEvaluationStep F
          ⟨.homComp (Dmap k) (thetaTerm r), Dobj q, b, q.obj.left, S,
            k.hom.left ≫ r.obj.hom, ⟨IsHom.comp (hDmap k) (htheta r)⟩,
            compArrow mapData (thetaData r)⟩ :=
        .comp (hDmap k) (htheta r) (D.obj q) (D.obj r) B mapData (thetaData r)
          (DE.eMap k) (thetaStep r) _ rfl
      have hh := RelEvaluationStep.hom_heq F (ihThetaNat k).2
        (eL := compositeStep) (eR := thetaStep q) (hL := rfl) (hR := rfl)
      exact eq_of_heq hh
    let theta : CoconeOutput D B :=
      { hom := fun q ↦ (thetaData q).hom
        homLift := fun q ↦ (thetaData q).isLift
        naturality := fun {_ _} k ↦ thetaNaturality k }
    have eEtaNat {q r : R.1.arrows.category} (k : q ⟶ r) : RelEvaluationStep F
        ⟨etaNat k, .homComp (Dmap k) (etaTerm r), etaTerm q, Dobj q, a,
          q.obj.left, S, k.hom.left ≫ r.obj.hom, q.obj.hom, hetaNat k,
          eta.naturalityEquation k⟩ := by
      let mapData := (D.mapArrow k).toHomData
      have hleft : HomEvaluationStep F
          ⟨.homComp (Dmap k) (etaTerm r), Dobj q, a, q.obj.left, S,
            k.hom.left ≫ r.obj.hom, (hetaNat k).leftHom,
            (eta.naturalityEquation k).leftArrow⟩ := by
        apply HomEvaluationStep.reindex F
          (.comp (hDmap k) (heta r) (D.obj q) (D.obj r) A mapData (etaData r)
            (DE.eMap k) (etaStep r) _ rfl) rfl
        exact ArrowData.heq_of_base_eq _ _ rfl rfl rfl (HEq.rfl)
      have hright : HomEvaluationStep F
          ⟨etaTerm q, Dobj q, a, q.obj.left, S, q.obj.hom,
            (hetaNat k).rightHom, (eta.naturalityEquation k).rightArrow⟩ := by
        apply HomEvaluationStep.reindex F (etaStep q) rfl
        exact ArrowData.heq_of_base_eq _ _ rfl rfl rfl (HEq.rfl)
      exact .mk (hetaNat k) (eta.naturalityEquation k) hleft hright _ rfl
    have eThetaNat {q r : R.1.arrows.category} (k : q ⟶ r) : RelEvaluationStep F
        ⟨thetaNat k, .homComp (Dmap k) (thetaTerm r), thetaTerm q, Dobj q, b,
          q.obj.left, S, k.hom.left ≫ r.obj.hom, q.obj.hom, hthetaNat k,
          theta.naturalityEquation k⟩ := by
      let mapData := (D.mapArrow k).toHomData
      have hleft : HomEvaluationStep F
          ⟨.homComp (Dmap k) (thetaTerm r), Dobj q, b, q.obj.left, S,
            k.hom.left ≫ r.obj.hom, (hthetaNat k).leftHom,
            (theta.naturalityEquation k).leftArrow⟩ := by
        apply HomEvaluationStep.reindex F
          (.comp (hDmap k) (htheta r) (D.obj q) (D.obj r) B mapData (thetaData r)
            (DE.eMap k) (thetaStep r) _ rfl) rfl
        exact ArrowData.heq_of_base_eq _ _ rfl rfl rfl (HEq.rfl)
      have hright : HomEvaluationStep F
          ⟨thetaTerm q, Dobj q, b, q.obj.left, S, q.obj.hom,
            (hthetaNat k).rightHom, (theta.naturalityEquation k).rightArrow⟩ := by
        apply HomEvaluationStep.reindex F (thetaStep q) rfl
        exact ArrowData.heq_of_base_eq _ _ rfl rfl rfl (HEq.rfl)
      exact .mk (hthetaNat k) (theta.naturalityEquation k) hleft hright _ rfl
    let H := homGlueOutput D A B eta theta
    exact ⟨H.arrow,
      .homGlue R Dobj Dmap etaTerm thetaTerm ha hb hDobj hDmap idRel compRel
        hId hComp heta htheta etaNat thetaNat hetaNat hthetaNat D A B eta theta
        ihA.1.2 ihB.1.2 DE.eObj DE.eMap DE.eId DE.eComp etaStep thetaStep
        eEtaNat eThetaNat _ rfl⟩
  · intro S T a b phi f hphi ihPhi
    exact makeRelResult F (.refl hphi) ihPhi.1 ihPhi.2 ihPhi.1 ihPhi.2 HEq.rfl
  · intro S T a b phi f g hphi hfg ihPhi
    let right := (baseChangeEquation ihPhi.1 hfg).rightArrow
    have rightStep : HomEvaluationStep F
        ⟨phi, a, b, S, T, g, ⟨(IsRel.baseChange hphi hfg).rightHom⟩, right⟩ := by
      apply HomEvaluationStep.reindex F ihPhi.2 hfg
      exact ArrowData.heq_of_base_eq _ _ hfg rfl rfl HEq.rfl
    exact makeRelResult F (IsRel.baseChange hphi hfg) ihPhi.1 ihPhi.2 right rightStep HEq.rfl
  · intro S T a b phi psi r f g hr ihR
    exact makeRelResult F (.symm hr) ihR.1.rightArrow
      (RelEvaluationStep.rightStep F ihR.2) ihR.1.leftArrow
      (RelEvaluationStep.leftStep F ihR.2) ihR.1.eq.symm.heq
  · intro S T a b phi psi chi r s f g h hr hs ihR ihS
    have hmidSem := HomEvaluationStep.value_unique F
      (RelEvaluationStep.rightStep F ihR.2)
      (RelEvaluationStep.leftStep F ihS.2) rfl
    have hmid : HEq ihR.1.right ihS.1.left :=
      congrArgHEq (fun x : HomSemantic (Y := Y) ↦ x.value.hom) hmidSem
    have hh : HEq ihR.1.left ihS.1.right :=
      ihR.1.eq.heq.trans (hmid.trans ihS.1.eq.heq)
    exact makeRelResult F (.trans hr hs) ihR.1.leftArrow
      (RelEvaluationStep.leftStep F ihR.2) ihS.1.rightArrow
      (RelEvaluationStep.rightStep F ihS.2) hh
  · intro R S T a b c phi phi' psi psi' r s f f' g g' hr hs ihR ihS
    let rLeftStep := RelEvaluationStep.leftStep F ihR.2
    let sLeftStep := RelEvaluationStep.leftStep F ihS.2
    have hmid : ihR.1.target = ihS.1.source := by
      let rTarget := (HomEvaluationStep.endpointSteps F rLeftStep).2
      let sSource := (HomEvaluationStep.endpointSteps F sLeftStep).1
      have hsem := ObjEvaluationStep.value_unique F rTarget.2 sSource.2 rfl
      exact eq_of_heq (congrArgHEq ObjSemantic.value hsem)
    let sLeftData := ihS.1.leftArrow.toHomDataOfEndpoints ihR.1.target ihS.1.target
      hmid.symm rfl
    let sRightData := ihS.1.rightArrow.toHomDataOfEndpoints ihR.1.target ihS.1.target
      hmid.symm rfl
    have sLeftEval : HomEvaluationStep F
        ⟨psi, b, c, S, T, g, hs.leftHom, sLeftData.toArrowData⟩ := by
      apply HomEvaluationStep.reindex F (RelEvaluationStep.leftStep F ihS.2) rfl
      exact (ArrowData.toHomDataOfEndpoints_toArrowData _ _ _ _ _).symm.heq
    have sRightEval : HomEvaluationStep F
        ⟨psi', b, c, S, T, g', hs.rightHom, sRightData.toArrowData⟩ := by
      apply HomEvaluationStep.reindex F (RelEvaluationStep.rightStep F ihS.2) rfl
      exact (ArrowData.toHomDataOfEndpoints_toArrowData _ _ _ _ _).symm.heq
    let leftData := compArrow ihR.1.leftArrow.toHomData sLeftData
    let rightData := compArrow ihR.1.rightArrow.toHomData sRightData
    have leftEval : HomEvaluationStep F
        ⟨.homComp phi psi, a, c, R, T, f ≫ g, ⟨(IsRel.compCongr hr hs).leftHom⟩,
          leftData⟩ :=
      .comp hr.leftHom hs.leftHom ihR.1.source ihR.1.target ihS.1.target
        ihR.1.leftArrow.toHomData sLeftData
        (RelEvaluationStep.leftStep F ihR.2) sLeftEval _ rfl
    have rightEval : HomEvaluationStep F
        ⟨.homComp phi' psi', a, c, R, T, f' ≫ g', ⟨(IsRel.compCongr hr hs).rightHom⟩,
          rightData⟩ :=
      .comp hr.rightHom hs.rightHom ihR.1.source ihR.1.target ihS.1.target
        ihR.1.rightArrow.toHomData sRightData
        (RelEvaluationStep.rightStep F ihR.2) sRightEval _ rfl
    have hsLeft : HEq sLeftData.hom ihS.1.left :=
      congrArgHEq ArrowData.hom
        (ArrowData.toHomDataOfEndpoints_toArrowData _ _ _ _ _)
    have hsRight : HEq sRightData.hom ihS.1.right :=
      congrArgHEq ArrowData.hom
        (ArrowData.toHomDataOfEndpoints_toArrowData _ _ _ _ _)
    have hsEq : sLeftData.hom = sRightData.hom :=
      eq_of_heq (hsLeft.trans (ihS.1.eq.heq.trans hsRight.symm))
    have hh : leftData.hom = rightData.hom := by
      dsimp [leftData, rightData, compArrow, arrow, HomData.toArrowData]
      change ihR.1.left ≫ sLeftData.hom = ihR.1.right ≫ sRightData.hom
      rw [ihR.1.eq, hsEq]
    exact makeRelResult F (IsRel.compCongr hr hs) leftData leftEval rightData rightEval hh.heq
  · intro S T a b phi f ha hphi ihA ihPhi
    have hsource : ihPhi.1.source = ihA.1.1 := by
      have hsem := (HomEvaluationStep.endpoints_unique F ihPhi.2).1 ihA.1.2 rfl
      exact eq_of_heq (congrArgHEq ObjSemantic.value hsem)
    let phiData := ihPhi.1.toHomDataOfEndpoints ihA.1.1 ihPhi.1.target
      hsource rfl
    have phiStep : HomEvaluationStep F
        ⟨phi, a, b, S, T, f, hphi, phiData.toArrowData⟩ := by
      rw [ArrowData.toHomDataOfEndpoints_toArrowData]
      exact ihPhi.2
    let identity := (idArrow ihA.1.1).toHomData
    let left := compArrow identity phiData
    have leftStep : HomEvaluationStep F
        ⟨.homComp (.homId a) phi, a, b, S, T, 𝟙 S ≫ f,
          ⟨(IsRel.idComp ha hphi).leftHom⟩, left⟩ :=
      .comp (.id ha) hphi ihA.1.1 ihA.1.1 ihPhi.1.target identity phiData
        (.id ha ihA.1.1 ihA.1.2 _ rfl) phiStep _ rfl
    have hh : left.hom = phiData.hom := by
      change (𝟙 _) ≫ phiData.hom = phiData.hom
      simp
    exact makeRelResult F (IsRel.idComp ha hphi) left leftStep phiData.toArrowData
      phiStep hh.heq
  · intro S T a b phi f hb hphi ihB ihPhi
    have htarget : ihPhi.1.target = ihB.1.1 := by
      have hsem := (HomEvaluationStep.endpoints_unique F ihPhi.2).2 ihB.1.2 rfl
      exact eq_of_heq (congrArgHEq ObjSemantic.value hsem)
    let phiData := ihPhi.1.toHomDataOfEndpoints ihPhi.1.source ihB.1.1
      rfl htarget
    have phiStep : HomEvaluationStep F
        ⟨phi, a, b, S, T, f, hphi, phiData.toArrowData⟩ := by
      rw [ArrowData.toHomDataOfEndpoints_toArrowData]
      exact ihPhi.2
    let identity := (idArrow ihB.1.1).toHomData
    let left := compArrow phiData identity
    have leftStep : HomEvaluationStep F
        ⟨.homComp phi (.homId b), a, b, S, T, f ≫ 𝟙 T,
          ⟨(IsRel.compId hb hphi).leftHom⟩, left⟩ :=
      .comp hphi (.id hb) ihPhi.1.source ihB.1.1 ihB.1.1 phiData identity
        phiStep (.id hb ihB.1.1 ihB.1.2 _ rfl) _ rfl
    have hh : left.hom = phiData.hom := by
      change phiData.hom ≫ (𝟙 _) = phiData.hom
      simp
    exact makeRelResult F (IsRel.compId hb hphi) left leftStep phiData.toArrowData
      phiStep hh.heq
  · intro Q R S T a b c d phi psi chi f g h hphi hpsi hchi ihPhi ihPsi ihChi
    have hmid₁ : ihPhi.1.target = ihPsi.1.source := by
      let pTarget := (HomEvaluationStep.endpointSteps F ihPhi.2).2
      let qSource := (HomEvaluationStep.endpointSteps F ihPsi.2).1
      have hsem := ObjEvaluationStep.value_unique F pTarget.2 qSource.2 rfl
      exact eq_of_heq (congrArgHEq ObjSemantic.value hsem)
    let phiData := ihPhi.1.toHomData
    let psiData := ihPsi.1.toHomDataOfEndpoints ihPhi.1.target ihPsi.1.target
      hmid₁.symm rfl
    have psiStep : HomEvaluationStep F
        ⟨psi, b, c, R, S, g, hpsi, psiData.toArrowData⟩ := by
      rw [ArrowData.toHomDataOfEndpoints_toArrowData]
      exact ihPsi.2
    have hmid₂ : ihPsi.1.target = ihChi.1.source := by
      let qTarget := (HomEvaluationStep.endpointSteps F ihPsi.2).2
      let rSource := (HomEvaluationStep.endpointSteps F ihChi.2).1
      have hsem := ObjEvaluationStep.value_unique F qTarget.2 rSource.2 rfl
      exact eq_of_heq (congrArgHEq ObjSemantic.value hsem)
    let chiData := ihChi.1.toHomDataOfEndpoints ihPsi.1.target ihChi.1.target
      hmid₂.symm rfl
    have chiStep : HomEvaluationStep F
        ⟨chi, c, d, S, T, h, hchi, chiData.toArrowData⟩ := by
      rw [ArrowData.toHomDataOfEndpoints_toArrowData]
      exact ihChi.2
    let phiPsi := compArrow phiData psiData
    let psiChi := compArrow psiData chiData
    have phiPsiStep : HomEvaluationStep F
        ⟨.homComp phi psi, a, c, Q, S, f ≫ g, ⟨IsHom.comp hphi hpsi⟩, phiPsi⟩ :=
      .comp hphi hpsi ihPhi.1.source ihPhi.1.target ihPsi.1.target
        phiData psiData ihPhi.2 psiStep _ rfl
    have psiChiStep : HomEvaluationStep F
        ⟨.homComp psi chi, b, d, R, T, g ≫ h, ⟨IsHom.comp hpsi hchi⟩, psiChi⟩ :=
      .comp hpsi hchi ihPhi.1.target ihPsi.1.target ihChi.1.target
        psiData chiData psiStep chiStep _ rfl
    let left := compArrow phiPsi.toHomData chiData
    let right := compArrow phiData psiChi.toHomData
    have leftStep : HomEvaluationStep F
        ⟨.homComp (.homComp phi psi) chi, a, d, Q, T, (f ≫ g) ≫ h,
          ⟨(IsRel.assoc hphi hpsi hchi).leftHom⟩, left⟩ :=
      .comp (.comp hphi hpsi) hchi ihPhi.1.source ihPsi.1.target ihChi.1.target
        phiPsi.toHomData chiData phiPsiStep chiStep _ rfl
    have rightStep : HomEvaluationStep F
        ⟨.homComp phi (.homComp psi chi), a, d, Q, T, f ≫ (g ≫ h),
          ⟨(IsRel.assoc hphi hpsi hchi).rightHom⟩, right⟩ :=
      .comp hphi (.comp hpsi hchi) ihPhi.1.source ihPhi.1.target ihChi.1.target
        phiData psiChi.toHomData ihPhi.2 psiChiStep _ rfl
    have hh : left.hom = right.hom := by
      dsimp [left, right, phiPsi, psiChi, compArrow, arrow,
        HomData.toArrowData, ArrowData.toHomData]
      simp [Category.assoc]
    exact makeRelResult F (IsRel.assoc hphi hpsi hchi) left leftStep right rightStep hh.heq
  · intro a
    let left := inclArrow F (𝟙 a)
    let A := inclObj F a
    let right := idArrow A
    have leftStep : HomEvaluationStep F
        ⟨.homIncl (𝟙 a), .objIncl a, .objIncl a, X.p.obj a, X.p.obj a,
          X.p.map (𝟙 a), ⟨(IsRel.inclId (J := J) (X := X) a).leftHom⟩, left⟩ :=
      .incl (𝟙 a) _ rfl
    have objStep : ObjEvaluationStep F
        ⟨.objIncl a, X.p.obj a, IsObj.incl (J := J) (X := X) a, A⟩ :=
      .incl a _ rfl
    have rightStep : HomEvaluationStep F
        ⟨.homId (.objIncl a), .objIncl a, .objIncl a, X.p.obj a, X.p.obj a,
          𝟙 (X.p.obj a), ⟨(IsRel.inclId (J := J) (X := X) a).rightHom⟩, right⟩ :=
      .id (IsObj.incl (J := J) (X := X) a) A objStep _ rfl
    exact makeRelResult F (IsRel.inclId (J := J) (X := X) a)
      left leftStep right rightStep (F.map_id a).heq
  · intro a b c f g
    let left := inclArrow F (f ≫ g)
    let first := (inclArrow F f).toHomData
    let second := (inclArrow F g).toHomData
    let right := compArrow first second
    have leftStep : HomEvaluationStep F
        ⟨.homIncl (f ≫ g), .objIncl a, .objIncl c, X.p.obj a, X.p.obj c,
          X.p.map (f ≫ g), ⟨(IsRel.inclComp (J := J) (X := X) f g).leftHom⟩, left⟩ :=
      .incl (f ≫ g) _ rfl
    have rightStep : HomEvaluationStep F
        ⟨.homComp (.homIncl f) (.homIncl g), .objIncl a, .objIncl c,
          X.p.obj a, X.p.obj c, X.p.map f ≫ X.p.map g,
          ⟨(IsRel.inclComp (J := J) (X := X) f g).rightHom⟩, right⟩ :=
      .comp (.incl f) (.incl g) (inclObj F a) (inclObj F b) (inclObj F c)
        first second (.incl f _ rfl) (.incl g _ rfl) _ rfl
    exact makeRelResult F (IsRel.inclComp (J := J) (X := X) f g)
      left leftStep right rightStep
      (F.map_comp f g).heq
  · intro R S T a b c cart phi p f g hcart hphi hp ihCart ihPhi
    have htarget : ihCart.1.target = ihPhi.1.target := by
      let cartTarget := (HomEvaluationStep.endpointSteps F ihCart.2).2
      let phiTarget := (HomEvaluationStep.endpointSteps F ihPhi.2).2
      have hsem := ObjEvaluationStep.value_unique F cartTarget.2 phiTarget.2 rfl
      exact eq_of_heq (congrArgHEq ObjSemantic.value hsem)
    let cartData := ihCart.1.toHomData
    let phiData := ihPhi.1.toHomDataOfEndpoints ihPhi.1.source ihCart.1.target
      rfl htarget.symm
    have phiStep : HomEvaluationStep F
        ⟨phi, c, b, R, T, p, hphi, phiData.toArrowData⟩ := by
      rw [ArrowData.toHomDataOfEndpoints_toArrowData]
      exact ihPhi.2
    let factor := factorArrow (J := J) cartData phiData hp
    have factorStep : HomEvaluationStep F
        ⟨.homFactor cart phi f g, c, a, R, S, g, ⟨IsHom.factor f g hcart hphi hp⟩,
          factor⟩ :=
      .factor f g hcart hphi hp ihCart.1.source ihCart.1.target ihPhi.1.source
        cartData phiData ihCart.2 phiStep _ rfl
    let left := compArrow factor.toHomData cartData
    have leftStep : HomEvaluationStep F
        ⟨.homComp (.homFactor cart phi f g) cart, c, b, R, T, g ≫ f,
          ⟨(IsRel.factorFac f g hcart hphi hp).leftHom⟩, left⟩ :=
      .comp (.factor f g hcart hphi hp) hcart ihPhi.1.source ihCart.1.source
        ihCart.1.target factor.toHomData cartData factorStep ihCart.2 _ rfl
    exact makeRelResult F (IsRel.factorFac f g hcart hphi hp) left leftStep
      phiData.toArrowData phiStep (factorArrow_fac (J := J) cartData phiData hp).heq
  · intro R S T a b c cart phi chi fac p q f g hcart hphi hp hchi hq hfac
      ihCart ihPhi ihChi ihFac
    have htarget : ihCart.1.target = ihPhi.1.target := by
      let cartTarget := (HomEvaluationStep.endpointSteps F ihCart.2).2
      let phiTarget := (HomEvaluationStep.endpointSteps F ihPhi.2).2
      have hsem := ObjEvaluationStep.value_unique F cartTarget.2 phiTarget.2 rfl
      exact eq_of_heq (congrArgHEq ObjSemantic.value hsem)
    let cartData := ihCart.1.toHomData
    let phiData := ihPhi.1.toHomDataOfEndpoints ihPhi.1.source ihCart.1.target
      rfl htarget.symm
    have phiStep : HomEvaluationStep F
        ⟨phi, c, b, R, T, p, hphi, phiData.toArrowData⟩ := by
      rw [ArrowData.toHomDataOfEndpoints_toArrowData]
      exact ihPhi.2
    have hchiSource : ihChi.1.source = ihPhi.1.source := by
      let chiSource := (HomEvaluationStep.endpointSteps F ihChi.2).1
      let phiSource := (HomEvaluationStep.endpointSteps F ihPhi.2).1
      have hsem := ObjEvaluationStep.value_unique F chiSource.2 phiSource.2 rfl
      exact eq_of_heq (congrArgHEq ObjSemantic.value hsem)
    have hchiTarget : ihChi.1.target = ihCart.1.source := by
      let chiTarget := (HomEvaluationStep.endpointSteps F ihChi.2).2
      let cartSource := (HomEvaluationStep.endpointSteps F ihCart.2).1
      have hsem := ObjEvaluationStep.value_unique F chiTarget.2 cartSource.2 rfl
      exact eq_of_heq (congrArgHEq ObjSemantic.value hsem)
    let chiData := ihChi.1.toHomDataOfEndpoints ihPhi.1.source ihCart.1.source
      hchiSource hchiTarget
    have chiStep : HomEvaluationStep F
        ⟨chi, c, a, R, S, q, hchi, chiData.toArrowData⟩ := by
      rw [ArrowData.toHomDataOfEndpoints_toArrowData]
      exact ihChi.2
    let composite := compArrow chiData cartData
    have compositeStep : HomEvaluationStep F
        ⟨.homComp chi cart, c, b, R, T, q ≫ f, ⟨IsHom.comp hchi hcart⟩, composite⟩ :=
      .comp hchi hcart ihPhi.1.source ihCart.1.source ihCart.1.target
        chiData cartData chiStep ihCart.2 _ rfl
    have hfacSem := RelEvaluationStep.hom_heq F ihFac.2
      (eL := compositeStep) (eR := phiStep) (hL := rfl) (hR := rfl)
    have hfacEq : chiData.hom ≫ cartData.hom = phiData.hom := eq_of_heq hfacSem
    let factor := factorArrow (J := J) cartData phiData hp
    have factorStep : HomEvaluationStep F
        ⟨.homFactor cart phi f g, c, a, R, S, g,
          ⟨(IsRel.factorUnique f g hcart hphi hp hchi hq hfac).rightHom⟩, factor⟩ :=
      .factor f g hcart hphi hp ihCart.1.source ihCart.1.target ihPhi.1.source
        cartData phiData ihCart.2 phiStep _ rfl
    letI := cartData.isLift
    letI := phiData.isLift
    letI : IsStronglyCartesian Y.p f cartData.hom :=
      IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift Y.p f _
    letI : IsHomLift Y.p g chiData.hom := hq ▸ chiData.isLift
    have huniq : chiData.hom = factor.hom :=
      IsStronglyCartesian.map_uniq Y.p f cartData.hom hp phiData.hom
        chiData.hom hfacEq
    exact makeRelResult F (IsRel.factorUnique f g hcart hphi hp hchi hq hfac)
      chiData.toArrowData chiStep factor factorStep huniq.heq
  · intro S R Dobj Dmap idRel compRel hglue q r k ihGlue
    rcases ihGlue.2 with ⟨hbase, hDobj, hDmap, hId, hComp, hglue_heq,
      D, eObj, eMap, eId, eComp, hvalue⟩
    cases hbase
    have hglue_eq : hglue =
        .glue R Dobj Dmap hDobj hDmap idRel compRel hId hComp :=
      eq_of_heq hglue_heq
    let mapData := (D.mapArrow k).toHomData
    let glueR := (D.glueArrow r).toHomData
    let left := compArrow mapData glueR
    have glueStep (s : R.1.arrows.category) : HomEvaluationStep F
        ⟨.homGlueMap R Dobj Dmap idRel compRel s, Dobj s,
          .objGlue R Dobj Dmap idRel compRel, s.obj.left, S, s.obj.hom,
          ⟨IsHom.glueMap R Dobj Dmap idRel compRel hglue s⟩, D.glueArrow s⟩ :=
      .glueMap R Dobj Dmap idRel compRel hglue hDobj hDmap hId hComp hglue_eq
        D eObj eMap eId eComp s _ rfl
    have leftStep : HomEvaluationStep F
        ⟨.homComp (Dmap k) (.homGlueMap R Dobj Dmap idRel compRel r),
          Dobj q, .objGlue R Dobj Dmap idRel compRel, q.obj.left, S,
          k.hom.left ≫ r.obj.hom,
          ⟨(IsRel.glueMapNatural R Dobj Dmap idRel compRel hglue k).leftHom⟩,
          left⟩ :=
      .comp (hDmap k) (.glueMap R Dobj Dmap idRel compRel hglue r)
        (D.obj q) (D.obj r) D.gluedObj mapData glueR (eMap k) (glueStep r) _ rfl
    exact makeRelResult F (IsRel.glueMapNatural R Dobj Dmap idRel compRel hglue k)
      left leftStep (D.glueArrow q) (glueStep q) (D.glued.cocone_naturality k).heq
  · intro S R Dobj Dmap idRel compRel a b etaTerm thetaTerm etaNat thetaNat
      hglue heta htheta q ihGlue ihEta ihTheta
    let V := HomEvaluationStep.homGlueView F R Dobj Dmap idRel compRel a b
      etaTerm thetaTerm etaNat thetaNat hglue ihGlue.1 ihGlue.2
    let H := homGlueOutput V.D V.A V.B V.eta V.theta
    have glueStep : HomEvaluationStep F
        ⟨.homGlue R Dobj Dmap idRel compRel a b etaTerm thetaTerm etaNat thetaNat,
          a, b, S, S, 𝟙 S, hglue, H.arrow⟩ := by
      rw [← V.value_eq]
      exact ihGlue.2
    have etaStep (s : R.1.arrows.category) : HomEvaluationStep F
        ⟨etaTerm s, Dobj s, a, s.obj.left, S, s.obj.hom, heta s, V.eta.arrow s⟩ := by
      apply HomEvaluationStep.reindex F (V.eEta s) rfl
      exact HEq.rfl
    have thetaStep (s : R.1.arrows.category) : HomEvaluationStep F
        ⟨thetaTerm s, Dobj s, b, s.obj.left, S, s.obj.hom, htheta s,
          V.theta.arrow s⟩ := by
      apply HomEvaluationStep.reindex F (V.eTheta s) rfl
      exact HEq.rfl
    let right := compArrow (V.eta.arrow q).toHomData H.arrow.toHomData
    have rightStep : HomEvaluationStep F
        ⟨.homComp (etaTerm q)
            (.homGlue R Dobj Dmap idRel compRel a b etaTerm thetaTerm etaNat thetaNat),
          Dobj q, b, q.obj.left, S, q.obj.hom ≫ 𝟙 S,
          ⟨(IsRel.homGlueFac R Dobj Dmap idRel compRel etaTerm thetaTerm etaNat
            thetaNat hglue heta htheta q).rightHom⟩, right⟩ :=
      .comp (heta q) hglue (V.D.obj q) V.A V.B (V.eta.arrow q).toHomData
        H.arrow.toHomData (etaStep q) glueStep _ rfl
    exact makeRelResult F
      (IsRel.homGlueFac R Dobj Dmap idRel compRel etaTerm thetaTerm etaNat thetaNat
        hglue heta htheta q)
      (V.theta.arrow q) (thetaStep q) right rightStep (H.fac q).heq
  · intro S R Dobj Dmap idRel compRel a b etaTerm thetaTerm etaNat thetaNat
      phi fac hglue hphi hfac ihGlue ihPhi ihFac
    let V := HomEvaluationStep.homGlueView F R Dobj Dmap idRel compRel a b
      etaTerm thetaTerm etaNat thetaNat hglue ihGlue.1 ihGlue.2
    let H := homGlueOutput V.D V.A V.B V.eta V.theta
    have glueStep : HomEvaluationStep F
        ⟨.homGlue R Dobj Dmap idRel compRel a b etaTerm thetaTerm etaNat thetaNat,
          a, b, S, S, 𝟙 S, hglue, H.arrow⟩ := by
      rw [← V.value_eq]
      exact ihGlue.2
    have hsource : ihPhi.1.source = V.A := by
      let phiSource := (HomEvaluationStep.endpointSteps F ihPhi.2).1
      let glueSource := (HomEvaluationStep.endpointSteps F ihGlue.2).1
      have hsem := ObjEvaluationStep.value_unique F phiSource.2 glueSource.2 rfl
      have hvalue : ihPhi.1.source = ihGlue.1.source :=
        eq_of_heq (congrArgHEq ObjSemantic.value hsem)
      calc
        ihPhi.1.source = ihGlue.1.source := hvalue
        _ = H.arrow.source := congrArg ArrowData.source V.value_eq
        _ = V.A := rfl
    have htarget : ihPhi.1.target = V.B := by
      let phiTarget := (HomEvaluationStep.endpointSteps F ihPhi.2).2
      let glueTarget := (HomEvaluationStep.endpointSteps F ihGlue.2).2
      have hsem := ObjEvaluationStep.value_unique F phiTarget.2 glueTarget.2 rfl
      have hvalue : ihPhi.1.target = ihGlue.1.target :=
        eq_of_heq (congrArgHEq ObjSemantic.value hsem)
      calc
        ihPhi.1.target = ihGlue.1.target := hvalue
        _ = H.arrow.target := congrArg ArrowData.target V.value_eq
        _ = V.B := rfl
    let phiData : HomData Y V.A V.B (𝟙 S) :=
      ihPhi.1.toHomDataOfEndpoints V.A V.B hsource htarget
    have phiStep : HomEvaluationStep F
        ⟨phi, a, b, S, S, 𝟙 S, hphi, phiData.toArrowData⟩ := by
      rw [ArrowData.toHomDataOfEndpoints_toArrowData]
      exact ihPhi.2
    have thetaStep (q : R.1.arrows.category) : HomEvaluationStep F
        ⟨thetaTerm q, Dobj q, b, q.obj.left, S, q.obj.hom,
          (hfac q).leftHom, V.theta.arrow q⟩ := by
      apply HomEvaluationStep.reindex F (V.eTheta q) rfl
      exact HEq.rfl
    let right (q : R.1.arrows.category) :
        ArrowData Y q.obj.left S (q.obj.hom ≫ 𝟙 S) :=
      compArrow (V.eta.arrow q).toHomData phiData
    have rightStep (q : R.1.arrows.category) : HomEvaluationStep F
        ⟨.homComp (etaTerm q) phi, Dobj q, b, q.obj.left, S,
          q.obj.hom ≫ 𝟙 S, (hfac q).rightHom, right q⟩ := by
      exact .comp (V.heta q) hphi (V.D.obj q) V.A V.B
        (V.eta.arrow q).toHomData phiData (V.eEta q) phiStep _ rfl
    have hfac' (q : R.1.arrows.category) :
        V.theta.hom q = V.eta.hom q ≫ phiData.hom := by
      have heq := RelEvaluationStep.hom_heq F (ihFac q).2
        (eL := thetaStep q) (eR := rightStep q) (hL := rfl) (hR := rfl)
      exact eq_of_heq heq
    have huniq : phiData.hom = H.hom :=
      H.unique phiData.hom phiData.isLift hfac'
    exact makeRelResult F
      (IsRel.homGlueUnique R Dobj Dmap idRel compRel etaTerm thetaTerm etaNat
        thetaNat fac hglue hphi hfac)
      phiData.toArrowData phiStep H.arrow glueStep huniq.heq

/-- The chosen semantic object attached to a formal object of the free completion. -/
noncomputable def objectData (F : X ⥤ᵇ Y) (a : Obj J X) : ObjData Y a.base :=
  (evaluateObj F (Classical.choice a.valid)).1

/-- The evaluator graph retained by `objectData`. -/
noncomputable def objectDataStep (F : X ⥤ᵇ Y) (a : Obj J X) :
    ObjEvaluationStep F
      ⟨a.term, a.base, Classical.choice a.valid, objectData F a⟩ :=
  (evaluateObj F (Classical.choice a.valid)).2

/-- The chosen semantic arrow before its endpoint packages are normalized. -/
noncomputable def rawArrow (F : X ⥤ᵇ Y) {a b : Obj J X}
    (phi : RawHom J X a b) : ArrowData Y a.base b.base phi.base :=
  (evaluateHom F (Classical.choice phi.valid)).1

/-- The evaluator graph retained by `rawArrow`. -/
noncomputable def rawArrowStep (F : X ⥤ᵇ Y) {a b : Obj J X}
    (phi : RawHom J X a b) : HomEvaluationStep F
      ⟨phi.term, a.term, b.term, a.base, b.base, phi.base,
        phi.valid, rawArrow F phi⟩ :=
  (evaluateHom F (Classical.choice phi.valid)).2

lemma rawArrow_source (F : X ⥤ᵇ Y) {a b : Obj J X} (phi : RawHom J X a b) :
    (rawArrow F phi).source = objectData F a := by
  have hsem := (HomEvaluationStep.endpoints_unique F (rawArrowStep F phi)).1
    (objectDataStep F a) rfl
  exact eq_of_heq (congrArgHEq ObjSemantic.value hsem)

lemma rawArrow_target (F : X ⥤ᵇ Y) {a b : Obj J X} (phi : RawHom J X a b) :
    (rawArrow F phi).target = objectData F b := by
  have hsem := (HomEvaluationStep.endpoints_unique F (rawArrowStep F phi)).2
    (objectDataStep F b) rfl
  exact eq_of_heq (congrArgHEq ObjSemantic.value hsem)

/-- The semantic arrow normalized to the object packages chosen independently at
its source and target. -/
noncomputable def rawMapData (F : X ⥤ᵇ Y) {a b : Obj J X}
    (phi : RawHom J X a b) : HomData Y (objectData F a) (objectData F b) phi.base :=
  (rawArrow F phi).toHomDataOfEndpoints (objectData F a) (objectData F b)
    (rawArrow_source F phi) (rawArrow_target F phi)

lemma rawMapData_arrow (F : X ⥤ᵇ Y) {a b : Obj J X} (phi : RawHom J X a b) :
    (rawMapData F phi).toArrowData = rawArrow F phi :=
  ArrowData.toHomDataOfEndpoints_toArrowData _ _ _ _ _

lemma rawMapData_rel (F : X ⥤ᵇ Y) {a b : Obj J X}
    {phi psi : RawHom J X a b} (h : RawHom.Rel phi psi) :
    (rawMapData F phi).hom = (rawMapData F psi).hom := by
  let rho := Classical.choose h
  let hrho : IsRel J X rho phi.term psi.term a.term b.term phi.base psi.base :=
    Classical.choice (Classical.choose_spec h)
  let e := evaluateRel F hrho
  have hrel : HEq (rawArrow F phi).hom (rawArrow F psi).hom :=
    RelEvaluationStep.hom_heq F e.2 (rawArrowStep F phi) (rawArrowStep F psi) rfl rfl
  have hphi : HEq (rawMapData F phi).hom (rawArrow F phi).hom :=
    congrArgHEq ArrowData.hom (rawMapData_arrow F phi)
  have hpsi : HEq (rawMapData F psi).hom (rawArrow F psi).hom :=
    congrArgHEq ArrowData.hom (rawMapData_arrow F psi)
  exact eq_of_heq (hphi.trans (hrel.trans hpsi.symm))

/-- Interpret a quotient arrow of the free completion. -/
noncomputable def map (F : X ⥤ᵇ Y) {a b : Obj J X} (phi : a ⟶ b) :
    (objectData F a).obj ⟶ (objectData F b).obj :=
  _root_.Quotient.lift (fun f ↦ (rawMapData F f).hom)
    (fun _ _ h ↦ rawMapData_rel F h) phi

@[simp]
lemma map_mk (F : X ⥤ᵇ Y) {a b : Obj J X} (phi : RawHom J X a b) :
    map F (⟦phi⟧ : a ⟶ b) = (rawMapData F phi).hom := rfl

lemma map_id (F : X ⥤ᵇ Y) (a : Obj J X) : map F (𝟙 a) = 𝟙 (objectData F a).obj := by
  let hobj := Classical.choice a.valid
  let I : HomEvaluationStep F
      ⟨.homId a.term, a.term, a.term, a.base, a.base, 𝟙 a.base,
        ⟨IsHom.id hobj⟩, idArrow (objectData F a)⟩ :=
    .id hobj (objectData F a) (objectDataStep F a) _ rfl
  have hsem := HomEvaluationStep.value_unique F (rawArrowStep F (RawHom.id a)) I rfl
  have hraw : HEq (rawArrow F (RawHom.id a)).hom (𝟙 (objectData F a).obj) :=
    congrArgHEq (fun s : HomSemantic (Y := Y) ↦ s.value.hom) hsem
  have hmap : HEq (rawMapData F (RawHom.id a)).hom
      (rawArrow F (RawHom.id a)).hom :=
    congrArgHEq ArrowData.hom (rawMapData_arrow F (RawHom.id a))
  exact eq_of_heq (hmap.trans hraw)

lemma map_comp (F : X ⥤ᵇ Y) {a b c : Obj J X}
    (phi : a ⟶ b) (psi : b ⟶ c) : map F (phi ≫ psi) = map F phi ≫ map F psi := by
  induction phi using _root_.Quotient.inductionOn with
  | _ phi =>
      induction psi using _root_.Quotient.inductionOn with
      | _ psi =>
          let hphi := Classical.choice phi.valid
          let hpsi := Classical.choice psi.valid
          have ePhi : HomEvaluationStep F
              ⟨phi.term, a.term, b.term, a.base, b.base, phi.base, ⟨hphi⟩,
                (rawMapData F phi).toArrowData⟩ := by
            rw [rawMapData_arrow]
            exact rawArrowStep F phi
          have ePsi : HomEvaluationStep F
              ⟨psi.term, b.term, c.term, b.base, c.base, psi.base, ⟨hpsi⟩,
                (rawMapData F psi).toArrowData⟩ := by
            rw [rawMapData_arrow]
            exact rawArrowStep F psi
          let E : HomEvaluationStep F
              ⟨.homComp phi.term psi.term, a.term, c.term, a.base, c.base,
                phi.base ≫ psi.base, ⟨IsHom.comp hphi hpsi⟩,
                compArrow (rawMapData F phi) (rawMapData F psi)⟩ :=
            .comp hphi hpsi (objectData F a) (objectData F b) (objectData F c)
              (rawMapData F phi) (rawMapData F psi) ePhi ePsi _ rfl
          have hsem := HomEvaluationStep.value_unique F
            (rawArrowStep F (RawHom.comp phi psi)) E rfl
          have hraw : HEq (rawArrow F (RawHom.comp phi psi)).hom
              ((rawMapData F phi).hom ≫ (rawMapData F psi).hom) :=
            congrArgHEq (fun s : HomSemantic (Y := Y) ↦ s.value.hom) hsem
          have hmap : HEq (rawMapData F (RawHom.comp phi psi)).hom
              (rawArrow F (RawHom.comp phi psi)).hom :=
            congrArgHEq ArrowData.hom (rawMapData_arrow F (RawHom.comp phi psi))
          exact eq_of_heq (hmap.trans hraw)

/-- The extension of a based functor from the generators to the free stack completion. -/
noncomputable def extension (F : X ⥤ᵇ Y) : completion J X ⥤ᵇ Y where
  obj a := (objectData F a).obj
  map := map F
  map_id := map_id F
  map_comp := map_comp F
  w := by
    refine Functor.ext_of_iso
      (NatIso.ofComponents (fun a ↦ eqToIso (objectData F a).base_eq) ?_)
      (fun a ↦ (objectData F a).base_eq) (fun _ ↦ rfl)
    intro a b phi
    induction phi using _root_.Quotient.inductionOn with
    | _ phi =>
        letI := (rawMapData F phi).isLift
        change Y.p.map (rawMapData F phi).hom ≫ eqToHom (objectData F b).base_eq =
          eqToHom (objectData F a).base_eq ≫ phi.base
        rw [IsHomLift.fac' Y.p phi.base (rawMapData F phi).hom]
        simp

/-- On an included generator, the chosen semantic object is the original object. -/
lemma objectData_inclusion (F : X ⥤ᵇ Y) (a : X.obj) :
    objectData F ((inclusion J X).obj a) = inclObj F a := by
  let E : ObjEvaluationStep F
      ⟨.objIncl a, X.p.obj a, IsObj.incl (J := J) (X := X) a, inclObj F a⟩ :=
    .incl a _ rfl
  have hsem := ObjEvaluationStep.value_unique F
    (objectDataStep F ((inclusion J X).obj a)) E rfl
  exact eq_of_heq (congrArgHEq ObjSemantic.value hsem)

/-- The raw representative used by the inclusion on an original arrow. -/
def inclusionRaw {a b : X.obj} (f : a ⟶ b) :
    RawHom J X ((inclusion J X).obj a) ((inclusion J X).obj b) :=
  ⟨X.p.map f, .homIncl f, ⟨.incl f⟩⟩

@[simp]
lemma inclusion_map_eq_mk {a b : X.obj} (f : a ⟶ b) :
    (inclusion J X).map f = (⟦inclusionRaw (J := J) (X := X) f⟧ :
      (inclusion J X).obj a ⟶ (inclusion J X).obj b) := rfl

/-- On an included generator, the chosen semantic arrow is the original arrow. -/
lemma rawArrow_inclusion (F : X ⥤ᵇ Y) {a b : X.obj} (f : a ⟶ b) :
    rawArrow F (inclusionRaw (J := J) (X := X) f) = inclArrow F f := by
  let E : HomEvaluationStep F
      ⟨.homIncl f, .objIncl a, .objIncl b, X.p.obj a, X.p.obj b, X.p.map f,
        ⟨IsHom.incl (J := J) (X := X) f⟩, inclArrow F f⟩ :=
    .incl f _ rfl
  have hsem := HomEvaluationStep.value_unique F
    (rawArrowStep F (inclusionRaw (J := J) (X := X) f)) E rfl
  exact eq_of_heq (congrArgHEq HomSemantic.value hsem)

lemma eqToHom_naturality_of_heq {A A' B B' : Y.obj} (hA : A = A') (hB : B = B')
    {f : A ⟶ B} {g : A' ⟶ B'} (h : HEq f g) :
    f ≫ eqToHom hB = eqToHom hA ≫ g := by
  subst A'
  subst B'
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  exact eq_of_heq h

lemma extension_inclusion_naturality (F : X ⥤ᵇ Y) {a b : X.obj} (f : a ⟶ b) :
    (extension (J := J) F).map ((inclusion J X).map f) ≫
        eqToHom (congrArg ObjData.obj (objectData_inclusion (J := J) F b)) =
      eqToHom (congrArg ObjData.obj (objectData_inclusion (J := J) F a)) ≫ F.map f := by
  let r := inclusionRaw (J := J) (X := X) f
  have hraw : (rawMapData F r).toArrowData = inclArrow F f :=
    (rawMapData_arrow F r).trans (rawArrow_inclusion (J := J) F f)
  have hhom : HEq (rawMapData F r).hom (F.map f) :=
    congrArgHEq ArrowData.hom hraw
  exact eqToHom_naturality_of_heq
    (congrArg ObjData.obj (objectData_inclusion (J := J) F a))
    (congrArg ObjData.obj (objectData_inclusion (J := J) F b)) hhom

/-- The extension restricts to the original based functor, up to based natural
isomorphism. -/
noncomputable def extensionInclusionIso (F : X ⥤ᵇ Y) :
    (inclusion J X).comp (extension (J := J) F) ≅ F :=
  BasedNatIso.mkNatIso
    (NatIso.ofComponents
      (fun a ↦ eqToIso (congrArg ObjData.obj (objectData_inclusion (J := J) F a)))
      (fun {_ _} f ↦ extension_inclusion_naturality (J := J) F f))
    (fun a ↦ IsHomLift.eqToHom_domain_lift_id
      (congrArg ObjData.obj (objectData_inclusion (J := J) F a))
      (objectData F ((inclusion J X).obj a)).base_eq)


end CategoryTheory.BasedCategory.FreeStackCompletion.Interpretation

