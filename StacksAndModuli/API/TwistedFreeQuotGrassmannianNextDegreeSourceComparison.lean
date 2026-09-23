module

public import StacksAndModuli.API.ProjectiveGradedGeneratedQuotient
public import StacksAndModuli.API.ProjectivePullbackTwistProjectionFormula
public import StacksAndModuli.API.SchemeModulesTensorMonoidalCoherence
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianNextDegreeSaturationVanishing
public import StacksAndModuli.API.TwistedFreeQuotReconstructedGeneratedNextDegree

/-!
# The next-degree reconstructed relation source

Over an affine base, a finite locally free coefficient `K` satisfies the projection
formula.  Combining it with the degree-one monomial basis and
`O(-d) ⊗ O(d+1) ≅ O(1)` gives the canonical isomorphism

`K^(n+1) ≅ π_*((π^*K ⊗ O(-d)) ⊗ O(d+1))`.

This file constructs that isomorphism explicitly and computes it on every free
generator.  It then proves all monomial, projection-formula, image, and kernel
reductions in the source comparison used by next-degree saturation.  The
monomial-independent right snake identity for the chosen tensor associator follows
from the existing left snake identity, and hence the complete source comparison is
unconditional.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Modules

/-- The projection formula applied after tensoring a coefficient with a global
section is adjoint to tensoring its pullback with the adjoint section. -/
lemma projectionFormulaHom_comp_section
    {X Y : Scheme.{u}} (f : X ⟶ Y) (K : Y.Modules) (F : X.Modules)
    (s : SheafOfModules.unit Y.ringCatSheaf ⟶ (pushforward f).obj F) :
    (tensorUnitIso K).inv ≫ tensorMapRight K s ≫
        projectionFormulaHom f K F =
      (pullbackPushforwardAdjunction f).homEquiv _ _
        ((tensorUnitIso ((pullback f).obj K)).inv ≫
          tensorMapRight ((pullback f).obj K)
            ((asIso (SheafOfModules.pullbackObjUnitToUnit
              f.toRingCatSheafHom)).inv ≫
              (pullback f).map s ≫
              (pullbackPushforwardAdjunction f).counit.app F)) := by
  let p := pullback f
  let q := pushforward f
  let adj := pullbackPushforwardAdjunction f
  let UY := SheafOfModules.unit Y.ringCatSheaf
  let UX := SheafOfModules.unit X.ringCatSheaf
  let unitComparison : p.obj UY ⟶ UX :=
    SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom
  let comparison := pullbackTensorComparison f K (q.obj F)
  let counit := adj.counit.app F
  apply (adj.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm]
  dsimp only [projectionFormulaHom]
  rw [Adjunction.homEquiv_naturality_left_symm]
  dsimp only [adj]
  rw [Equiv.symm_apply_apply]
  change (pullback f).map (tensorUnitIso K).inv ≫
      (pullback f).map (tensorMapRight K s) ≫
      pullbackTensorComparison f K ((pushforward f).obj F) ≫
      tensorMapRight ((pullback f).obj K)
        ((pullbackPushforwardAdjunction f).counit.app F) =
    ((pullbackPushforwardAdjunction f).homEquiv K
      (tensor ((pullback f).obj K) F)).symm
        ((pullbackPushforwardAdjunction f).homEquiv K
          (tensor ((pullback f).obj K) F)
          ((tensorUnitIso ((pullback f).obj K)).inv ≫
            tensorMapRight ((pullback f).obj K)
              ((asIso (SheafOfModules.pullbackObjUnitToUnit
                f.toRingCatSheafHom)).inv ≫
                (pullback f).map s ≫
                (pullbackPushforwardAdjunction f).counit.app F)))
  rw [Equiv.symm_apply_apply]
  have hnat := pullbackTensorComparison_naturality_right f K s
  slice_lhs 2 3 => rw [hnat]
  haveI : IsIso unitComparison := isIso_pullbackObjUnitToUnit f
  haveI : IsIso (tensorMapRight (p.obj K) unitComparison) := by
    change IsIso ((tensorRightIso (p.obj K) (asIso unitComparison)).hom)
    infer_instance
  have hunit := pullbackTensorComparison_comp_unit f K
  change pullbackTensorComparison f K UY ≫
      tensorMapRight (p.obj K) unitComparison ≫
      (tensorUnitIso (p.obj K)).hom =
    p.map (tensorUnitIso K).hom at hunit
  have hunitInv : p.map (tensorUnitIso K).inv ≫
      pullbackTensorComparison f K UY =
    (tensorUnitIso (p.obj K)).inv ≫
      tensorMapRight (p.obj K) (asIso unitComparison).inv := by
    apply (cancel_mono (tensorMapRight (p.obj K) unitComparison ≫
      (tensorUnitIso (p.obj K)).hom)).1
    calc
      (p.map (tensorUnitIso K).inv ≫
            pullbackTensorComparison f K UY) ≫
          (tensorMapRight (p.obj K) unitComparison ≫
            (tensorUnitIso (p.obj K)).hom) =
        p.map (tensorUnitIso K).inv ≫
          (pullbackTensorComparison f K UY ≫
            tensorMapRight (p.obj K) unitComparison ≫
            (tensorUnitIso (p.obj K)).hom) := by
        simp only [Category.assoc]
      _ = p.map (tensorUnitIso K).inv ≫
          p.map (tensorUnitIso K).hom :=
        congrArg (fun z ↦ p.map (tensorUnitIso K).inv ≫ z) hunit
      _ = 𝟙 (p.obj K) := by
        rw [← p.map_comp]
        simp
      _ = ((tensorUnitIso (p.obj K)).inv ≫
            tensorMapRight (p.obj K) (asIso unitComparison).inv) ≫
          (tensorMapRight (p.obj K) unitComparison ≫
            (tensorUnitIso (p.obj K)).hom) := by
        slice_rhs 2 3 => rw [← tensorMapRight_comp]
        simp
  slice_lhs 1 2 => rw [hunitInv]
  change (tensorUnitIso (p.obj K)).inv ≫
      tensorMapRight (p.obj K) (asIso unitComparison).inv ≫
      tensorMapRight (p.obj K) (p.map s) ≫
      tensorMapRight (p.obj K) counit =
    (tensorUnitIso (p.obj K)).inv ≫
      tensorMapRight (p.obj K)
        ((asIso unitComparison).inv ≫ p.map s ≫ counit)
  slice_lhs 2 3 => rw [← tensorMapRight_comp]
  slice_lhs 2 3 => rw [← tensorMapRight_comp]
  rw [Category.assoc]

end Modules

/-- Reindex the chosen degree-one monomial basis by the `n+1` projective
variables, including the unique ambient summand used by the twisted-free monomial
map of rank one. -/
noncomputable def twistedFreeDegreeOneSourceIndexEquiv (n : ℕ) :
    ULift.{u} (Fin (n + 1)) ≃
      ULift.{u} (Fin 1) × Fin ((n + 1).choose n) :=
  (Equiv.ulift.trans
    (ProjectiveSpace.GradedModule.degreeOneMonomialIndexEquiv n)).trans
      (Equiv.uniqueProd (Fin ((n + 1).choose n))
        (ULift.{u} (Fin 1))).symm

/-- The rank-one summand selected by the degree-one source reindexing is the
unique summand. -/
lemma twistedFreeDegreeOneSourceIndexEquiv_fst
    (n : ℕ) (a : ULift.{u} (Fin (n + 1))) :
    (twistedFreeDegreeOneSourceIndexEquiv n a).1 =
      ULift.up (0 : Fin 1) := by
  rfl

/-- The monomial selected by the degree-one source reindexing is the chosen
degree-one monomial corresponding to the same projective variable. -/
lemma twistedFreeDegreeOneSourceIndexEquiv_snd
    (n : ℕ) (a : ULift.{u} (Fin (n + 1))) :
    (twistedFreeDegreeOneSourceIndexEquiv n a).2 =
      twistedFreeDegreeOneMonomialIndex n a.down := by
  rfl

/-- A coproduct of copies of `K` is canonically `K` tensored with the
corresponding free sheaf. -/
noncomputable def Modules.coproductConstantIsoTensorFree
    (T : Scheme.{u}) (I : Type u) (K : T.Modules) :
    (∐ fun _ : I ↦ K) ≅
      Modules.tensor K (SheafOfModules.free (R := T.ringCatSheaf) I) :=
  (Modules.tensorCoproductIso
      (fun _ : I ↦ SheafOfModules.unit T.ringCatSheaf) K ≪≫
    Sigma.mapIso (fun _ : I ↦ Modules.tensorLeftUnitIso K)).symm ≪≫
      Modules.tensorCommIso
        (SheafOfModules.free (R := T.ringCatSheaf) I) K

/-- On a summand inclusion, the coproduct-to-tensor isomorphism is the
inverse right unitor followed by the corresponding free generator. -/
lemma Modules.coproductConstantIsoTensorFree_hom_ι
    (T : Scheme.{u}) (I : Type u) (K : T.Modules) (i : I) :
    Sigma.ι (fun _ : I ↦ K) i ≫
        (Modules.coproductConstantIsoTensorFree T I K).hom =
      (Modules.tensorUnitIso K).inv ≫
        Modules.tensorMapRight K
          (SheafOfModules.ιFree (R := T.ringCatSheaf) i) := by
  dsimp only [Modules.coproductConstantIsoTensorFree, Iso.trans_hom,
    Iso.symm_hom, Iso.trans_inv]
  simp only [Category.assoc]
  rw [Sigma.ι_mapIso_inv_assoc]
  slice_lhs 2 3 => rw [Modules.ι_tensorCoproductIso_inv]
  change (Modules.tensorLeftUnitIso K).inv ≫
      Modules.tensorMapLeft
        (Sigma.ι (fun _ : I ↦
          SheafOfModules.unit T.ringCatSheaf) i) K ≫
      (Modules.tensorCommIso
        (∐ fun _ : I ↦ SheafOfModules.unit T.ringCatSheaf) K).hom =
    (Modules.tensorUnitIso K).inv ≫
      Modules.tensorMapRight K
        (Sigma.ι (fun _ : I ↦
          SheafOfModules.unit T.ringCatSheaf) i)
  slice_lhs 2 3 => rw [Modules.tensorCommIso_hom_naturality_left]
  have hunit := Modules.tensorCommIso_unit_comp_tensorUnitIso K
  have hunitInv : (Modules.tensorLeftUnitIso K).inv ≫
      (Modules.tensorCommIso
        (SheafOfModules.unit T.ringCatSheaf) K).hom =
      (Modules.tensorUnitIso K).inv := by
    apply (cancel_mono (Modules.tensorUnitIso K).hom).1
    simp only [Category.assoc, hunit, Iso.inv_hom_id]
  exact congrArg (fun z ↦ z ≫ Modules.tensorMapRight K
    (Sigma.ι (fun _ : I ↦ SheafOfModules.unit T.ringCatSheaf) i))
      hunitInv

/-- The rank-one twisted-free ambient sheaf with zero source twist, after
twisting once, is `O(1)`. -/
noncomputable def twistedFreeDegreeOneAmbientIso
    (n : ℕ) (T : Scheme.{u}) :
    projectiveSpaceOverTwistModule
        (∐ fun _ : ULift.{u} (Fin 1) ↦
          projectiveSpaceOverTwist n T 0) 1 ≅
      projectiveSpaceOverTwist n T 1 :=
  Modules.tensorLeftIso
      (coproductUniqueIso (fun _ : ULift.{u} (Fin 1) ↦
        projectiveSpaceOverTwist n T 0))
      (projectiveSpaceOverTwist n T 1) ≪≫
    projectiveSpaceOverTwist_addIso_nat n T 0 1 ≪≫
    eqToIso (congrArg (projectiveSpaceOverTwist n T) (by omega))

/-- The chosen degree-one monomial basis identifies the free sheaf on the
projective variables with `π_*O(1)`. -/
noncomputable def twistedFreeDegreeOnePushforwardIso
    (n : ℕ) (T : Scheme.{u}) :
    SheafOfModules.free (R := T.ringCatSheaf)
        (ULift.{u} (Fin (n + 1))) ≅
      (Modules.pushforward (projectiveSpaceOverπ n T)).obj
        (projectiveSpaceOverTwist n T 1) := by
  letI : IsIso (SheafOfModules.freeMap (R := T.ringCatSheaf)
      (twistedFreeDegreeOneSourceIndexEquiv n)) :=
    Modules.freeMap_isIso_of_equiv (twistedFreeDegreeOneSourceIndexEquiv n)
  exact asIso (SheafOfModules.freeMap (R := T.ringCatSheaf)
      (twistedFreeDegreeOneSourceIndexEquiv n)) ≪≫
    asIso (twistedFreeMonomialPushforwardMap n T 0 1 1 1 (by omega)) ≪≫
    (Modules.pushforward (projectiveSpaceOverπ n T)).mapIso
      (twistedFreeDegreeOneAmbientIso n T)

/-- On a free generator, the degree-one pushforward isomorphism is the unit
morphism represented by the corresponding rank-one monomial section, transported
through the rank-one ambient isomorphism. -/
lemma twistedFreeDegreeOnePushforwardIso_hom_ιFree
    (n : ℕ) (T : Scheme.{u})
    (a : ULift.{u} (Fin (n + 1))) :
    SheafOfModules.ιFree (R := T.ringCatSheaf) a ≫
        (twistedFreeDegreeOnePushforwardIso n T).hom =
      ((Modules.pushforward (projectiveSpaceOverπ n T)).obj
        (projectiveSpaceOverTwist n T 1)).unitHomEquiv.symm
          ((Modules.sectionsTopEquiv _).symm
            (Modules.Hom.app
              ((Modules.pushforward (projectiveSpaceOverπ n T)).map
                (twistedFreeDegreeOneAmbientIso n T).hom) ⊤
              (twistedFreeMonomialSection n T 0 1 1 1 (by omega)
                (twistedFreeDegreeOneSourceIndexEquiv n a).1
                (twistedFreeDegreeOneSourceIndexEquiv n a).2))) := by
  dsimp only [twistedFreeDegreeOnePushforwardIso, Iso.trans_hom,
    asIso_hom, Functor.mapIso_hom]
  slice_lhs 1 2 => rw [SheafOfModules.ιFree_freeMap]
  slice_lhs 1 2 =>
    change SheafOfModules.ιFree
      (twistedFreeDegreeOneSourceIndexEquiv n a) ≫
        Modules.freeHomOfSections
          (fun x : ULift.{u} (Fin 1) × Fin ((n + 1).choose n) ↦
            twistedFreeMonomialSection n T 0 1 1 1
              (by omega) x.1 x.2)
    rw [Modules.ιFree_comp_freeHomOfSections]
  rw [Modules.unitHomOfSection_comp]
  rfl

set_option maxHeartbeats 800000 in
-- The proof normalizes nested pullback, free-sheaf, and adjunction equivalences.
/-- The adjoint of the degree-one pushforward isomorphism on a free generator is
the corresponding rank-one monomial map, followed by the ambient isomorphism. -/
lemma twistedFreeDegreeOnePushforwardIso_hom_ιFree_adjunct
    (n : ℕ) (T : Scheme.{u})
    (a : ULift.{u} (Fin (n + 1))) :
    let π := projectiveSpaceOverπ n T
    let unitComparison := SheafOfModules.pullbackObjUnitToUnit
      π.toRingCatSheafHom
    (asIso unitComparison).inv ≫
        (Modules.pullback π).map
          (SheafOfModules.ιFree (R := T.ringCatSheaf) a ≫
            (twistedFreeDegreeOnePushforwardIso n T).hom) ≫
        (Modules.pullbackPushforwardAdjunction π).counit.app
          (projectiveSpaceOverTwist n T 1) =
      SheafOfModules.ιFree
          (R := (projectiveSpaceOver n T).ringCatSheaf)
          (twistedFreeDegreeOneSourceIndexEquiv n a) ≫
        twistedFreeMonomialMap n T 0 1 1 1 (by omega) ≫
        (twistedFreeDegreeOneAmbientIso n T).hom := by
  dsimp only
  let π := projectiveSpaceOverπ n T
  let p := Modules.pullback π
  let adj := Modules.pullbackPushforwardAdjunction π
  let unitComparison := SheafOfModules.pullbackObjUnitToUnit
    π.toRingCatSheafHom
  let b := twistedFreeDegreeOneSourceIndexEquiv n a
  let w := Modules.pullbackFreeIso π
    (ULift.{u} (Fin 1) × Fin ((n + 1).choose n))
  let m := twistedFreeMonomialMap n T 0 1 1 1 (by omega)
  let ambient := twistedFreeDegreeOneAmbientIso n T
  let core := w.hom ≫ m
  let h := (p.map (SheafOfModules.ιFree b) ≫ core) ≫ ambient.hom
  have hs : SheafOfModules.ιFree (R := T.ringCatSheaf) a ≫
      (twistedFreeDegreeOnePushforwardIso n T).hom =
      adj.homEquiv _ _ h := by
    dsimp only [twistedFreeDegreeOnePushforwardIso, Iso.trans_hom,
      asIso_hom, Functor.mapIso_hom]
    slice_lhs 1 2 => rw [SheafOfModules.ιFree_freeMap]
    change SheafOfModules.ιFree b ≫
        twistedFreeMonomialPushforwardMap n T 0 1 1 1 (by omega) ≫
        (Modules.pushforward π).map ambient.hom = adj.homEquiv _ _ h
    have hmon : adj.homEquiv _ _ core =
        twistedFreeMonomialPushforwardMap n T 0 1 1 1 (by omega) :=
      twistedFreeMonomialPushforwardMap_adjunct n T 0 1 1 1 (by omega)
    have hleft := adj.homEquiv_naturality_left
      (SheafOfModules.ιFree b) core
    have hright := adj.homEquiv_naturality_right
      (p.map (SheafOfModules.ιFree b) ≫ core) ambient.hom
    calc
      SheafOfModules.ιFree b ≫
            twistedFreeMonomialPushforwardMap n T 0 1 1 1 (by omega) ≫
            (Modules.pushforward π).map ambient.hom =
          SheafOfModules.ιFree b ≫ adj.homEquiv _ _ core ≫
            (Modules.pushforward π).map ambient.hom := by rw [hmon]
      _ = adj.homEquiv _ _
            (p.map (SheafOfModules.ιFree b) ≫ core) ≫
            (Modules.pushforward π).map ambient.hom := by
        simpa only [Category.assoc] using congrArg
          (fun z ↦ z ≫ (Modules.pushforward π).map ambient.hom) hleft.symm
      _ = adj.homEquiv _ _
            ((p.map (SheafOfModules.ιFree b) ≫ core) ≫ ambient.hom) :=
        hright.symm
      _ = adj.homEquiv _ _ h := rfl
  rw [hs]
  change (asIso unitComparison).inv ≫
      p.map (adj.homEquiv _ _ h) ≫ adj.counit.app _ = _
  have hc : p.map (adj.homEquiv _ _ h) ≫ adj.counit.app _ = h := by
    calc
      p.map (adj.homEquiv _ _ h) ≫ adj.counit.app _ =
          (adj.homEquiv _ _).symm (adj.homEquiv _ _ h) :=
        (adj.homEquiv_counit _ _ _).symm
      _ = h := Equiv.symm_apply_apply _ _
  slice_lhs 2 3 => rw [hc]
  change (asIso unitComparison).inv ≫ p.map (SheafOfModules.ιFree b) ≫
      w.hom ≫ m ≫ ambient.hom =
    SheafOfModules.ιFree b ≫ m ≫ ambient.hom
  have hfree := SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom
    π.toRingCatSheafHom b
  change p.map (SheafOfModules.ιFree b) ≫ w.hom =
    unitComparison ≫ SheafOfModules.ιFree b at hfree
  have hfree' : p.map (SheafOfModules.ιFree b) ≫ w.hom ≫ m ≫
      ambient.hom = unitComparison ≫ SheafOfModules.ιFree b ≫ m ≫
        ambient.hom := by
    simpa only [Category.assoc] using congrArg
      (fun z ↦ z ≫ m ≫ ambient.hom) hfree
  rw [hfree']
  change (asIso unitComparison).inv ≫ (asIso unitComparison).hom ≫
      SheafOfModules.ιFree b ≫ m ≫ ambient.hom = _
  simp only [Iso.inv_hom_id_assoc]

/-- The rank-one degree-one monomial map, after collapsing its unique ambient
summand, is the standard degree-one monomial section. -/
lemma twistedFreeDegreeOneMonomialMap_ι
    (n : ℕ) (T : Scheme.{u})
    (a : ULift.{u} (Fin (n + 1))) :
    SheafOfModules.ιFree
          (R := (projectiveSpaceOver n T).ringCatSheaf)
          (twistedFreeDegreeOneSourceIndexEquiv n a) ≫
        twistedFreeMonomialMap n T 0 1 1 1 (by omega) ≫
        (twistedFreeDegreeOneAmbientIso n T).hom =
      twistMonomialSectionHom n T 1
        (twistedFreeDegreeOneMonomialIndex n a.down) := by
  dsimp only [twistedFreeMonomialMap]
  slice_lhs 1 2 => rw [Modules.ιFree_comp_freeHomOfSections]
  rw [unitHomOf_twistedFreeMonomialSection_eq]
  rw [twistedFreeDegreeOneSourceIndexEquiv_fst,
    twistedFreeDegreeOneSourceIndexEquiv_snd]
  let O1 := projectiveSpaceOverTwist n T ((1 : ℕ) : ℤ)
  let inc := Sigma.ι
    (fun _ : ULift.{u} (Fin 1) ↦ projectiveSpaceOverTwist n T 0)
    (ULift.up (0 : Fin 1))
  let collapse := coproductUniqueIso
    (fun _ : ULift.{u} (Fin 1) ↦ projectiveSpaceOverTwist n T 0)
  dsimp only [twistedFreeDegreeOneAmbientIso, Iso.trans_hom,
    Modules.tensorLeftIso]
  simp only [Category.assoc]
  change _ ≫ Modules.tensorMapLeft inc O1 ≫
      Modules.tensorMapLeft collapse.hom O1 ≫ _ = _
  slice_lhs 2 3 => rw [← Modules.tensorMapLeft_comp]
  rw [Limits.ι_coproductUniqueIso_hom]
  simp only [eqToHom_refl, Modules.tensorMapLeft_id, Category.id_comp]
  have htw := twistMonomialTwistedSectionHom_eq n T 0 1 1 (by omega)
    (twistedFreeDegreeOneMonomialIndex n a.down)
  rw [htw]
  simp only [Category.assoc, eqToHom_refl, Category.id_comp]
  norm_num
  change twistMonomialSectionHom n T 1
      (twistedFreeDegreeOneMonomialIndex n a.down) ≫
        (projectiveSpaceOverTwist_addIso_nat n T 0 1).inv ≫
        (projectiveSpaceOverTwist_addIso_nat n T 0 1).hom = _
  slice_lhs 2 3 => rw [Iso.inv_hom_id]
  simp only [Category.comp_id]

/-- The standard degree-one monomial section, transported to
`O(-d) ⊗ O(d+1)`, is the mate of multiplication by that monomial under the
pairing between `O(-d)` and `O(d)`. -/
lemma twistMonomialSectionHom_degreeOne_pairingMate
    (n : ℕ) (T : Scheme.{u}) (d : ℕ)
    (i : Fin ((n + 1).choose n)) :
    let N := projectiveSpaceOverTwist n T (-(d : ℤ))
    let L := projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ)
    let O1 := projectiveSpaceOverTwist n T 1
    let pair := projectiveSpaceOverTwist_pairingIso_nat n T d
    let s := twistMonomialSectionHom n T 1 i
    let c : O1 ⟶ Modules.tensor N L :=
      (eqToIso (congrArg (projectiveSpaceOverTwist n T)
        (by omega : -(d : ℤ) + ((d + 1 : ℕ) : ℤ) = 1))).inv ≫
        (projectiveSpaceOverTwist_addIso_nat
          n T (-(d : ℤ)) (d + 1)).inv
    let μ := twistMonomialMulHom n T (d : ℤ) ((d + 1 : ℕ) : ℤ)
      1 (by omega) i
    s ≫ c = pair.inv ≫ Modules.tensorMapRight N μ := by
  dsimp only
  rw [twistMonomialSectionHom_eq_zeroIso_inv_comp_mulHom]
  let N := projectiveSpaceOverTwist n T (-(d : ℤ))
  let addD := projectiveSpaceOverTwist_addIso_nat n T (-(d : ℤ)) d
  let addL := projectiveSpaceOverTwist_addIso_nat
    n T (-(d : ℤ)) (d + 1)
  let castD : projectiveSpaceOverTwist n T (-(d : ℤ) + (d : ℤ)) ≅
      projectiveSpaceOverTwist n T 0 :=
    eqToIso (congrArg (projectiveSpaceOverTwist n T) (by omega))
  let castL : projectiveSpaceOverTwist n T
      (-(d : ℤ) + ((d + 1 : ℕ) : ℤ)) ≅
      projectiveSpaceOverTwist n T 1 :=
    eqToIso (congrArg (projectiveSpaceOverTwist n T) (by omega))
  let z := projectiveSpaceOverTwistZeroIso n T
  let m0 := twistMonomialMulHom n T 0 ((1 : ℕ) : ℤ) 1 (by omega) i
  let μ := twistMonomialMulHom n T (d : ℤ) ((d + 1 : ℕ) : ℤ)
    1 (by omega) i
  let mout := twistMonomialMulHom n T
    (-(d : ℤ) + (d : ℤ))
    (-(d : ℤ) + ((d + 1 : ℕ) : ℤ)) 1 (by omega) i
  dsimp only [projectiveSpaceOverTwist_pairingIso_nat, Iso.trans_inv]
  simp only [Category.assoc]
  have hadd := tensorMapRight_twistMonomialMulHom_comp_addIso_nat
    n T (-(d : ℤ)) d (d + 1) 1 (by omega) i
  change Modules.tensorMapRight N μ ≫ addL.hom =
    addD.hom ≫ mout at hadd
  have haddInv : addD.inv ≫ Modules.tensorMapRight N μ =
      mout ≫ addL.inv := by
    apply (cancel_mono addL.hom).1
    calc
      (addD.inv ≫ Modules.tensorMapRight N μ) ≫ addL.hom =
          addD.inv ≫ (Modules.tensorMapRight N μ ≫ addL.hom) :=
        Category.assoc _ _ _
      _ = addD.inv ≫ (addD.hom ≫ mout) :=
        congrArg (fun z ↦ addD.inv ≫ z) hadd
      _ = mout := by simp
      _ = (mout ≫ addL.inv) ≫ addL.hom := by simp
  rw [haddInv]
  have hin := eqToHom_comp_twistMonomialMulHom n T
    0 (-(d : ℤ) + (d : ℤ))
    (-(d : ℤ) + ((d + 1 : ℕ) : ℤ)) 1
    (by omega) (by omega) (by omega) i
  have hout := twistMonomialMulHom_comp_eqToHom n T
    0 1 (-(d : ℤ) + ((d + 1 : ℕ) : ℤ)) 1
    (by omega) (by omega) i
  have hcast : m0 ≫ castL.inv = castD.inv ≫ mout :=
    (hin.trans hout.symm).symm
  simpa only [z, m0, castL, castD, addL, Category.assoc] using
    congrArg (fun k ↦ z.inv ≫ k ≫ addL.inv) hcast

/-- The right snake identity for cancellation of `O(d)` against `O(-d)`,
with an arbitrary module in the untouched tensor factor.  This is the sole
monomial-independent tensor coherence needed by the next-degree source square. -/
def ProjectiveSpaceOverTwistModuleCancellationRightTriangle
    (n : ℕ) (T : Scheme.{u})
    (F : (projectiveSpaceOver n T).Modules) (d : ℕ) : Prop :=
  let N := projectiveSpaceOverTwist n T (-(d : ℤ))
  let D := projectiveSpaceOverTwist n T (d : ℤ)
  let B := projectiveSpaceOverTwistModule F (d : ℤ)
  let pair := projectiveSpaceOverTwist_pairingIso_nat n T d
  let cancel := (projectiveSpaceOverTwistModule_cancelIso_nat n T F d).hom
  (Modules.tensorUnitIso B).inv ≫
      Modules.tensorMapRight B pair.inv ≫
      (Modules.tensorAssocIso B N D).inv ≫
      Modules.tensorMapLeft cancel D =
    𝟙 B

/-- The canonical cancellation of opposite projective twists satisfies the right
snake identity, with an arbitrary module in the untouched tensor factor. -/
lemma projectiveSpaceOverTwistModuleCancellation_rightTriangle
    (n : ℕ) (T : Scheme.{u})
    (F : (projectiveSpaceOver n T).Modules) (d : ℕ) :
    ProjectiveSpaceOverTwistModuleCancellationRightTriangle n T F d := by
  let N := projectiveSpaceOverTwist n T (-(d : ℤ))
  let D := projectiveSpaceOverTwist n T (d : ℤ)
  let coev := projectiveSpaceOverTwist_pairingIso_nat n T d
  let ev := projectiveSpaceOverTwist_cancelIso_nat n T d
  have hleft := projectiveSpaceOverTwist_pairing_left_triangle_nat n T d
  change (Modules.tensorLeftUnitIso N).inv ≫
      Modules.tensorMapLeft coev.inv N ≫
      (Modules.tensorAssocIso N D N).hom ≫
      Modules.tensorMapRight N ev.hom ≫
      (Modules.tensorUnitIso N).hom = 𝟙 N at hleft
  have hright := Modules.tensorPairing_right_triangle_of_left_whiskered
    F N D coev ev hleft
  simpa only [ProjectiveSpaceOverTwistModuleCancellationRightTriangle,
    projectiveSpaceOverTwistModule_cancelIso_nat,
    projectiveSpaceOverTwistModule, N, D, coev, ev,
    Iso.trans_hom, Modules.tensorRightIso, Category.assoc] using hright

/-- The right snake identity turns the pairing mate of `X_i` into ordinary
multiplication by `X_i` after twist cancellation. -/
lemma projectiveTwistDegreeOneCancellation_of_rightTriangle
    (n : ℕ) (T : Scheme.{u})
    (F : (projectiveSpaceOver n T).Modules) (d : ℕ)
    (htriangle : ProjectiveSpaceOverTwistModuleCancellationRightTriangle
      n T F d)
    (i : Fin ((n + 1).choose n)) :
    let Om := projectiveSpaceOverTwist n T (-(d : ℤ))
    let On := projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ)
    let O1 := projectiveSpaceOverTwist n T 1
    let B := projectiveSpaceOverTwistModule F (d : ℤ)
    let s := twistMonomialSectionHom n T 1 i
    let c : O1 ⟶ Modules.tensor Om On :=
      (eqToIso (congrArg (projectiveSpaceOverTwist n T)
        (by omega : -(d : ℤ) + ((d + 1 : ℕ) : ℤ) = 1))).inv ≫
        (projectiveSpaceOverTwist_addIso_nat
          n T (-(d : ℤ)) (d + 1)).inv
    let cancel := (projectiveSpaceOverTwistModule_cancelIso_nat n T F d).hom
    let μ := twistMonomialMulHom n T (d : ℤ) ((d + 1 : ℕ) : ℤ)
      1 (by omega) i
    (Modules.tensorUnitIso B).inv ≫
        Modules.tensorMapRight B s ≫
        Modules.tensorMapRight B c ≫
        (Modules.tensorAssocIso B Om On).inv ≫
        Modules.tensorMapLeft cancel On =
      Modules.tensorMapRight F μ := by
  dsimp only
  let D := projectiveSpaceOverTwist n T (d : ℤ)
  let N := projectiveSpaceOverTwist n T (-(d : ℤ))
  let L := projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ)
  let B := projectiveSpaceOverTwistModule F (d : ℤ)
  let pair := projectiveSpaceOverTwist_pairingIso_nat n T d
  let s := twistMonomialSectionHom n T 1 i
  let c := (eqToIso (congrArg (projectiveSpaceOverTwist n T)
    (by omega : -(d : ℤ) + ((d + 1 : ℕ) : ℤ) = 1))).inv ≫
      (projectiveSpaceOverTwist_addIso_nat n T (-(d : ℤ)) (d + 1)).inv
  let cancel := (projectiveSpaceOverTwistModule_cancelIso_nat n T F d).hom
  let μ := twistMonomialMulHom n T (d : ℤ) ((d + 1 : ℕ) : ℤ)
    1 (by omega) i
  have hmate := twistMonomialSectionHom_degreeOne_pairingMate n T d i
  change s ≫ c = pair.inv ≫ Modules.tensorMapRight N μ at hmate
  have hr := Modules.tensorAssocIso_hom_naturality_right B N μ
  change Modules.tensorMapRight (Modules.tensor B N) μ ≫
      (Modules.tensorAssocIso B N L).hom =
    (Modules.tensorAssocIso B N D).hom ≫
      Modules.tensorMapRight B (Modules.tensorMapRight N μ) at hr
  have hrInv :
      Modules.tensorMapRight B (Modules.tensorMapRight N μ) ≫
          (Modules.tensorAssocIso B N L).inv =
        (Modules.tensorAssocIso B N D).inv ≫
          Modules.tensorMapRight (Modules.tensor B N) μ := by
    apply (cancel_mono (Modules.tensorAssocIso B N L).hom).1
    calc
      (Modules.tensorMapRight B (Modules.tensorMapRight N μ) ≫
            (Modules.tensorAssocIso B N L).inv) ≫
          (Modules.tensorAssocIso B N L).hom =
        Modules.tensorMapRight B (Modules.tensorMapRight N μ) := by simp
      _ = (Modules.tensorAssocIso B N D).inv ≫
          (Modules.tensorMapRight (Modules.tensor B N) μ ≫
            (Modules.tensorAssocIso B N L).hom) := by
        rw [hr]
        simp
      _ = ((Modules.tensorAssocIso B N D).inv ≫
          Modules.tensorMapRight (Modules.tensor B N) μ) ≫
            (Modules.tensorAssocIso B N L).hom := by
        simp only [Category.assoc]
  have hex := Modules.tensorMap_exchange cancel μ
  change Modules.tensorMapRight (Modules.tensor B N) μ ≫
      Modules.tensorMapLeft cancel L =
    Modules.tensorMapLeft cancel D ≫ Modules.tensorMapRight F μ at hex
  change (Modules.tensorUnitIso B).inv ≫
      Modules.tensorMapRight B pair.inv ≫
      (Modules.tensorAssocIso B N D).inv ≫
      Modules.tensorMapLeft cancel D = 𝟙 B at htriangle
  slice_lhs 2 3 => rw [← Modules.tensorMapRight_comp]
  rw [hmate]
  rw [Modules.tensorMapRight_comp]
  simp only [Category.assoc]
  slice_lhs 3 4 => rw [hrInv]
  slice_lhs 4 5 => rw [hex]
  change ((Modules.tensorUnitIso B).inv ≫
      Modules.tensorMapRight B pair.inv ≫
      (Modules.tensorAssocIso B N D).inv ≫
      Modules.tensorMapLeft cancel D) ≫ Modules.tensorMapRight F μ =
    Modules.tensorMapRight F μ
  rw [htriangle]
  simp only [Category.id_comp]

/-- The canonical source isomorphism for the twisted reconstructed relation in
degree `d+1`, over an affine base with finite locally free coefficient. -/
noncomputable def reconstructedNextDegreeRelationSourcePushforwardIso_of_isAffine
    (n : ℕ) (T : Scheme.{u}) [IsAffine T]
    (d : ℕ) {K : T.Modules} [K.IsQuasicoherent]
    (hK : Modules.IsFiniteLocallyFree K) :
    (∐ fun _ : ULift.{u} (Fin (n + 1)) ↦ K) ≅
      (Modules.pushforward (projectiveSpaceOverπ n T)).obj
        (Modules.tensor
          (Modules.tensor
            ((Modules.pullback (projectiveSpaceOverπ n T)).obj K)
            (projectiveSpaceOverTwist n T (-(d : ℤ))))
          (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ))) := by
  letI : IsIso (Modules.projectivePullbackTwistProjectionFormulaHom
      n T K 1) :=
    Modules.projectivePullbackTwistProjectionFormulaHom_isIso_of_isFiniteLocallyFree_of_isAffine
      hK n 1
  exact Modules.coproductConstantIsoTensorFree T
      (ULift.{u} (Fin (n + 1))) K ≪≫
    Modules.tensorRightIso K (twistedFreeDegreeOnePushforwardIso n T) ≪≫
    asIso (Modules.projectivePullbackTwistProjectionFormulaHom n T K 1) ≪≫
    (Modules.pushforward (projectiveSpaceOverπ n T)).mapIso
      (reconstructedNextDegreeRelationSourceTwistIsoPullbackOne n T d K).symm

/-- The canonical relation-source isomorphism on the summand indexed by one
projective variable, expressed using the free generator and projection formula. -/
lemma reconstructedNextDegreeRelationSourcePushforwardIso_hom_ι
    (n : ℕ) (T : Scheme.{u}) [IsAffine T]
    (d : ℕ) {K : T.Modules} [K.IsQuasicoherent]
    (hK : Modules.IsFiniteLocallyFree K)
    (a : ULift.{u} (Fin (n + 1))) :
    Sigma.ι (fun _ : ULift.{u} (Fin (n + 1)) ↦ K) a ≫
        (reconstructedNextDegreeRelationSourcePushforwardIso_of_isAffine
          n T d hK).hom =
      (Modules.tensorUnitIso K).inv ≫
        Modules.tensorMapRight K
          (SheafOfModules.ιFree (R := T.ringCatSheaf) a ≫
            (twistedFreeDegreeOnePushforwardIso n T).hom) ≫
        Modules.projectivePullbackTwistProjectionFormulaHom n T K 1 ≫
        (Modules.pushforward (projectiveSpaceOverπ n T)).map
          (reconstructedNextDegreeRelationSourceTwistIsoPullbackOne
            n T d K).inv := by
  dsimp only [reconstructedNextDegreeRelationSourcePushforwardIso_of_isAffine,
    Iso.trans_hom, Modules.tensorRightIso, asIso_hom,
    Functor.mapIso_hom, Iso.symm_hom]
  slice_lhs 1 2 =>
    rw [Modules.coproductConstantIsoTensorFree_hom_ι]
  simp only [Category.assoc]
  slice_lhs 2 3 => rw [← Modules.tensorMapRight_comp]
  simp only [Category.assoc]

/-- The pushed-forward twisted image identification, followed by its kernel
inclusion and the ambient monomial-basis map, is the pushforward of the twisted
image inclusion. -/
lemma reconstructedNextDegreeRelationImagePushforwardIsoKernel_hom_fac
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E) :
    (reconstructedNextDegreeRelationImagePushforwardIsoKernel
        n T l r d e he u).hom ≫
        kernel.ι (quotGrassmannianFreeMap n T l r
          (reconstructedQuotientMap' n T l r d e he u)
          (d + 1) (e + 1) (by omega)) ≫
        twistedFreeMonomialPushforwardMap n T l r
          (d + 1) (e + 1) (by omega) =
      (Modules.pushforward (projectiveSpaceOverπ n T)).map
        (Modules.tensorMapLeft
          (Abelian.image.ι
            (reconstructedRelation' n T l r d e he u))
          (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ))) := by
  let p := reconstructedQuotientMap' n T l r d e he u
  let O := projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ)
  let kIso := projectiveSpaceOverTwistTensorKernelIso n T p
    ((d + 1 : ℕ) : ℤ)
  let adj := quotGrassmannianTwistedKernelAdjunctIso n T l r p
    (d + 1) (e + 1) (by omega)
  have hadj := quotGrassmannianTwistedKernelAdjunctIso_hom_comp
    n T l r p (d + 1) (e + 1) (by omega)
  change adj.hom ≫
      (Modules.pushforward (projectiveSpaceOverπ n T)).map
        (kernel.ι (Modules.tensorMapLeft p O)) =
    kernel.ι (quotGrassmannianFreeMap n T l r p
      (d + 1) (e + 1) (by omega)) ≫
    twistedFreeMonomialPushforwardMap n T l r
      (d + 1) (e + 1) (by omega) at hadj
  change (Modules.pushforward (projectiveSpaceOverπ n T)).map kIso.hom ≫
      adj.inv ≫ kernel.ι (quotGrassmannianFreeMap n T l r p
        (d + 1) (e + 1) (by omega)) ≫
      twistedFreeMonomialPushforwardMap n T l r
        (d + 1) (e + 1) (by omega) = _
  rw [← hadj]
  change (Modules.pushforward (projectiveSpaceOverπ n T)).map kIso.hom ≫
      adj.inv ≫ adj.hom ≫
      (Modules.pushforward (projectiveSpaceOverπ n T)).map
        (kernel.ι (Modules.tensorMapLeft p O)) = _
  simp only [Iso.inv_hom_id_assoc]
  rw [← Functor.map_comp]
  have hk := PreservesKernel.iso_inv_ι
    (Modules.tensorRightFunctor O) p
  change kIso.inv ≫ Modules.tensorMapLeft (kernel.ι p) O =
    kernel.ι (Modules.tensorMapLeft p O) at hk
  rw [← hk]
  simp only [Iso.hom_inv_id_assoc]
  rfl

/-- The projection-formula source map carries the finite source to the
degree-one-generated reconstructed relation. -/
def TwistedFreeNextDegreeGeneratedRelationSourceCompatibility
    (n : ℕ) (T : Scheme.{u}) [IsAffine T]
    (l : ℤ) (r d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    {E : T.Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (hK : Modules.IsFiniteLocallyFree (kernel u)) : Prop := by
  letI : (kernel u).IsQuasicoherent := Modules.kernel_isQuasicoherent u
  exact (reconstructedNextDegreeRelationSourcePushforwardIso_of_isAffine
      n T d hK).hom ≫
      (Modules.pushforward (projectiveSpaceOverπ n T)).map
        (Modules.tensorMapLeft
          (reconstructedRelation' n T l r d e he u)
          (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ))) =
    reconstructedGeneratedNextDegreeRelation n T l r d e he u

/-- The canonical map from the relation-kernel coefficient corresponding to
one variable into the reconstructed ambient pushforward in degree `d+1`. -/
noncomputable def reconstructedNextDegreeRelationSourceMonomialMap
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (a : ULift.{u} (Fin (n + 1))) :
    kernel u ⟶
      (Modules.pushforward (projectiveSpaceOverπ n T)).obj
        (projectiveSpaceOverTwistModule
          (∐ fun _ : ULift.{u} (Fin r) ↦
            projectiveSpaceOverTwist n T (-l))
          ((d + 1 : ℕ) : ℤ)) :=
  (Modules.tensorUnitIso (kernel u)).inv ≫
    Modules.tensorMapRight (kernel u)
      (SheafOfModules.ιFree (R := T.ringCatSheaf) a ≫
        (twistedFreeDegreeOnePushforwardIso n T).hom) ≫
    Modules.projectivePullbackTwistProjectionFormulaHom
      n T (kernel u) 1 ≫
    (Modules.pushforward (projectiveSpaceOverπ n T)).map
      (reconstructedNextDegreeRelationSourceTwistIsoPullbackOne
        n T d (kernel u)).inv ≫
    (Modules.pushforward (projectiveSpaceOverπ n T)).map
      (Modules.tensorMapLeft
        (reconstructedRelation' n T l r d e he u)
        (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ)))

/-- The degree-`d` reconstructed relation followed by multiplication by one
projective variable, as a map into the degree-`d+1` ambient pushforward. -/
noncomputable def reconstructedNextDegreeGeneratedRelationMonomialMap
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (a : ULift.{u} (Fin (n + 1))) :
    kernel u ⟶
      (Modules.pushforward (projectiveSpaceOverπ n T)).obj
        (projectiveSpaceOverTwistModule
          (∐ fun _ : ULift.{u} (Fin r) ↦
            projectiveSpaceOverTwist n T (-l))
          ((d + 1 : ℕ) : ℤ)) :=
  kernel.ι u ≫
    twistedFreeMonomialPushforwardMap n T l r d e he ≫
    (Modules.pushforward (projectiveSpaceOverπ n T)).map
      (Modules.projectiveTwistMulOne n
        (∐ fun _ : ULift.{u} (Fin r) ↦
          projectiveSpaceOverTwist n T (-l)) d
        (twistedFreeDegreeOneMonomialIndex n a.down))

/-- Restricting the source isomorphism to one summand and then applying the
reconstructed relation gives the corresponding canonical monomial-source map. -/
lemma reconstructedNextDegreeRelationSourcePushforwardIso_hom_ι_comp
    (n : ℕ) (T : Scheme.{u}) [IsAffine T]
    (l : ℤ) (r d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    {E : T.Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    [(kernel u).IsQuasicoherent]
    (hK : Modules.IsFiniteLocallyFree (kernel u))
    (a : ULift.{u} (Fin (n + 1))) :
    (Sigma.ι (fun _ : ULift.{u} (Fin (n + 1)) ↦ kernel u) a ≫
        (reconstructedNextDegreeRelationSourcePushforwardIso_of_isAffine
          n T d hK).hom) ≫
        (Modules.pushforward (projectiveSpaceOverπ n T)).map
          (Modules.tensorMapLeft
            (reconstructedRelation' n T l r d e he u)
            (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ))) =
      reconstructedNextDegreeRelationSourceMonomialMap
        n T l r d e he u a := by
  rw [reconstructedNextDegreeRelationSourcePushforwardIso_hom_ι]
  rfl

/-- The remaining sheaf-level coherence behind the next-degree source square:
tensoring the relation kernel with the standard section `X_i`, undoing twist
cancellation, and applying the reconstructed relation is multiplication by `X_i`
after the degree-`d` monomial relation. -/
def TwistedFreeNextDegreeRelationSheafMonomialCompatibility
    (n : ℕ) (T : Scheme.{u})
    (l : ℤ) (r d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E) : Prop :=
  ∀ a : ULift.{u} (Fin (n + 1)),
    let π := projectiveSpaceOverπ n T
    let K := kernel u
    let F := ∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)
    (Modules.tensorUnitIso ((Modules.pullback π).obj K)).inv ≫
        Modules.tensorMapRight ((Modules.pullback π).obj K)
          (twistMonomialSectionHom n T 1
            (twistedFreeDegreeOneMonomialIndex n a.down)) ≫
        (reconstructedNextDegreeRelationSourceTwistIsoPullbackOne
          n T d K).inv ≫
        Modules.tensorMapLeft
          (reconstructedRelation' n T l r d e he u)
          (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ)) =
      (Modules.pullback π).map (kernel.ι u) ≫
        (Modules.pullbackFreeIso π
          (ULift.{u} (Fin r) × Fin ((n + e).choose n))).hom ≫
        twistedFreeMonomialMap n T l r d e he ≫
        Modules.projectiveTwistMulOne n F d
          (twistedFreeDegreeOneMonomialIndex n a.down)

/-- The right snake identity for the fixed twisted-free ambient sheaf implies
the complete sheaf-level next-degree monomial square. -/
theorem
    twistedFreeNextDegreeRelationSheafMonomialCompatibility_of_rightTriangle
    (n : ℕ) (T : Scheme.{u})
    (l : ℤ) (r d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (htriangle :
      ProjectiveSpaceOverTwistModuleCancellationRightTriangle n T
        (∐ fun _ : ULift.{u} (Fin r) ↦
          projectiveSpaceOverTwist n T (-l)) d) :
    TwistedFreeNextDegreeRelationSheafMonomialCompatibility
      n T l r d e he u := by
  intro a
  let π := projectiveSpaceOverπ n T
  let p := Modules.pullback π
  let f₁ := p.map (kernel.ι u)
  let w := Modules.pullbackFreeIso π
    (ULift.{u} (Fin r) × Fin ((n + e).choose n))
  let m := twistedFreeMonomialMap n T l r d e he
  let f := f₁ ≫ w.hom ≫ m
  let A := p.obj (kernel u)
  let F := ∐ fun _ : ULift.{u} (Fin r) ↦
    projectiveSpaceOverTwist n T (-l)
  let Od := projectiveSpaceOverTwist n T (d : ℤ)
  let Om := projectiveSpaceOverTwist n T (-(d : ℤ))
  let On := projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ)
  let O1 := projectiveSpaceOverTwist n T 1
  let B := projectiveSpaceOverTwistModule F (d : ℤ)
  let s := twistMonomialSectionHom n T 1
    (twistedFreeDegreeOneMonomialIndex n a.down)
  let c : O1 ⟶ Modules.tensor Om On :=
    (eqToIso (congrArg (projectiveSpaceOverTwist n T)
      (by omega : -(d : ℤ) + ((d + 1 : ℕ) : ℤ) = 1))).inv ≫
      (projectiveSpaceOverTwist_addIso_nat
        n T (-(d : ℤ)) (d + 1)).inv
  let cancel := (projectiveSpaceOverTwistModule_cancelIso_nat n T F d).hom
  let μ := twistMonomialMulHom n T (d : ℤ) ((d + 1 : ℕ) : ℤ)
    1 (by omega) (twistedFreeDegreeOneMonomialIndex n a.down)
  dsimp only
  dsimp only [reconstructedNextDegreeRelationSourceTwistIsoPullbackOne,
    reconstructedRelation', Modules.projectiveTwistMulOne,
    Iso.trans_inv, Modules.tensorRightIso, Modules.tensorLeftIso]
  rw [twistedFreeAmbientReconstructionCompatibility n T l r d e he]
  have hrelation :
      Modules.tensorMapLeft f₁ Om ≫
          Modules.tensorMapLeft w.hom Om ≫
          Modules.tensorMapLeft m Om ≫ cancel =
        Modules.tensorMapLeft f Om ≫ cancel := by
    change _ = Modules.tensorMapLeft (f₁ ≫ w.hom ≫ m) Om ≫ cancel
    rw [Modules.tensorMapLeft_comp, Modules.tensorMapLeft_comp]
    simp only [Category.assoc]
  rw [hrelation]
  change (Modules.tensorUnitIso A).inv ≫
      Modules.tensorMapRight A s ≫
      Modules.tensorMapRight A c ≫
      (Modules.tensorAssocIso A Om On).inv ≫
      Modules.tensorMapLeft (Modules.tensorMapLeft f Om ≫ cancel) On =
    f ≫ Modules.tensorMapRight F μ
  rw [Modules.tensorMapLeft_comp]
  have hassoc :
      (Modules.tensorAssocIso A Om On).inv ≫
          Modules.tensorMapLeft (Modules.tensorMapLeft f Om) On =
        Modules.tensorMapLeft f (Modules.tensor Om On) ≫
          (Modules.tensorAssocIso B Om On).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact Modules.tensorAssocIso_hom_naturality_left f Om On
  have hexC := Modules.tensorMap_exchange f c
  have hexS := Modules.tensorMap_exchange f s
  change Modules.tensorMapRight A s ≫ Modules.tensorMapLeft f O1 =
    Modules.tensorMapLeft f
        (SheafOfModules.unit (projectiveSpaceOver n T).ringCatSheaf) ≫
      Modules.tensorMapRight B s at hexS
  have hunit :
      (Modules.tensorUnitIso A).inv ≫
          Modules.tensorMapLeft f
            (SheafOfModules.unit (projectiveSpaceOver n T).ringCatSheaf) =
        f ≫ (Modules.tensorUnitIso B).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact Modules.tensorUnitIso_naturality f
  calc
    (Modules.tensorUnitIso A).inv ≫
          Modules.tensorMapRight A s ≫
          Modules.tensorMapRight A c ≫
          (Modules.tensorAssocIso A Om On).inv ≫
          Modules.tensorMapLeft (Modules.tensorMapLeft f Om) On ≫
          Modules.tensorMapLeft cancel On =
        (Modules.tensorUnitIso A).inv ≫
          Modules.tensorMapRight A s ≫
          Modules.tensorMapRight A c ≫
          Modules.tensorMapLeft f (Modules.tensor Om On) ≫
          (Modules.tensorAssocIso B Om On).inv ≫
          Modules.tensorMapLeft cancel On := by
      simpa only [Category.assoc] using congrArg
        (fun z ↦ (Modules.tensorUnitIso A).inv ≫
          Modules.tensorMapRight A s ≫
          Modules.tensorMapRight A c ≫ z ≫
          Modules.tensorMapLeft cancel On) hassoc
    _ = (Modules.tensorUnitIso A).inv ≫
          Modules.tensorMapRight A s ≫
          Modules.tensorMapLeft f O1 ≫
          Modules.tensorMapRight B c ≫
          (Modules.tensorAssocIso B Om On).inv ≫
          Modules.tensorMapLeft cancel On := by
      simpa only [A, B, O1, Category.assoc] using congrArg
        (fun z ↦ (Modules.tensorUnitIso A).inv ≫
          Modules.tensorMapRight A s ≫ z ≫
          (Modules.tensorAssocIso B Om On).inv ≫
          Modules.tensorMapLeft cancel On) hexC
    _ = (Modules.tensorUnitIso A).inv ≫
          Modules.tensorMapLeft f
            (SheafOfModules.unit (projectiveSpaceOver n T).ringCatSheaf) ≫
          Modules.tensorMapRight B s ≫
          Modules.tensorMapRight B c ≫
          (Modules.tensorAssocIso B Om On).inv ≫
          Modules.tensorMapLeft cancel On := by
      simpa only [A, B, O1, Category.assoc] using congrArg
        (fun z ↦ (Modules.tensorUnitIso A).inv ≫ z ≫
          Modules.tensorMapRight B c ≫
          (Modules.tensorAssocIso B Om On).inv ≫
          Modules.tensorMapLeft cancel On) hexS
    _ = f ≫ (Modules.tensorUnitIso B).inv ≫
          Modules.tensorMapRight B s ≫
          Modules.tensorMapRight B c ≫
          (Modules.tensorAssocIso B Om On).inv ≫
          Modules.tensorMapLeft cancel On := by
      simpa only [A, B, Category.assoc] using congrArg
        (fun z ↦ z ≫ Modules.tensorMapRight B s ≫
          Modules.tensorMapRight B c ≫
          (Modules.tensorAssocIso B Om On).inv ≫
          Modules.tensorMapLeft cancel On) hunit
    _ = f ≫ Modules.tensorMapRight F μ := by
      rw [projectiveTwistDegreeOneCancellation_of_rightTriangle
        n T F d htriangle (twistedFreeDegreeOneMonomialIndex n a.down)]

/-- Pointwise form of the remaining source coherence: on the summand indexed
by `X_i`, the free generator, projection-formula map, twist cancellation, and
reconstructed relation equal the degree-`d` monomial relation followed by
multiplication by `X_i`. -/
def TwistedFreeNextDegreeRelationSourceMonomialCompatibility
    (n : ℕ) (T : Scheme.{u})
    (l : ℤ) (r d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E) : Prop :=
  ∀ a : ULift.{u} (Fin (n + 1)),
    reconstructedNextDegreeRelationSourceMonomialMap
        n T l r d e he u a =
      reconstructedNextDegreeGeneratedRelationMonomialMap
        n T l r d e he u a

/-- The explicit sheaf-level tensor/cancellation square implies the corresponding
source square after projection formula and pushforward. -/
theorem twistedFreeNextDegreeRelationSourceMonomialCompatibility_of_sheaf
    (n : ℕ) (T : Scheme.{u})
    (l : ℤ) (r d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (h : TwistedFreeNextDegreeRelationSheafMonomialCompatibility
      n T l r d e he u) :
    TwistedFreeNextDegreeRelationSourceMonomialCompatibility
      n T l r d e he u := by
  intro a
  let π := projectiveSpaceOverπ n T
  let K := kernel u
  let O1 := projectiveSpaceOverTwist n T 1
  let F := ∐ fun _ : ULift.{u} (Fin r) ↦
    projectiveSpaceOverTwist n T (-l)
  let Fd1 := projectiveSpaceOverTwistModule F ((d + 1 : ℕ) : ℤ)
  let s := SheafOfModules.ιFree (R := T.ringCatSheaf) a ≫
    (twistedFreeDegreeOnePushforwardIso n T).hom
  let μ := Modules.projectiveTwistMulOne n F d
    (twistedFreeDegreeOneMonomialIndex n a.down)
  let adj := Modules.pullbackPushforwardAdjunction π
  dsimp only [reconstructedNextDegreeRelationSourceMonomialMap,
    reconstructedNextDegreeGeneratedRelationMonomialMap]
  change (Modules.tensorUnitIso K).inv ≫
      Modules.tensorMapRight K s ≫
      Modules.projectionFormulaHom π K O1 ≫
      (Modules.pushforward π).map
        (reconstructedNextDegreeRelationSourceTwistIsoPullbackOne
          n T d K).inv ≫
      (Modules.pushforward π).map
        (Modules.tensorMapLeft
          (reconstructedRelation' n T l r d e he u)
          (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ))) =
    kernel.ι u ≫
      twistedFreeMonomialPushforwardMap n T l r d e he ≫
      (Modules.pushforward π).map μ
  slice_lhs 1 3 => rw [Modules.projectionFormulaHom_comp_section]
  rw [← adj.homEquiv_naturality_right]
  rw [← adj.homEquiv_naturality_right]
  rw [← twistedFreeMonomialPushforwardMap_adjunct
    n T l r d e he]
  rw [← adj.homEquiv_naturality_right]
  rw [← adj.homEquiv_naturality_left]
  change adj.homEquiv K Fd1 _ = adj.homEquiv K Fd1 _
  apply_fun (adj.homEquiv K Fd1).symm
  simp only [Equiv.symm_apply_apply]
  have hdegree := twistedFreeDegreeOnePushforwardIso_hom_ιFree_adjunct
    n T a
  change (asIso (SheafOfModules.pullbackObjUnitToUnit
      π.toRingCatSheafHom)).inv ≫
      (Modules.pullback π).map s ≫ adj.counit.app O1 = _ at hdegree
  rw [hdegree]
  rw [twistedFreeDegreeOneMonomialMap_ι]
  exact h a

/-- The right snake identity for twist cancellation supplies the source
monomial compatibility used by the next-degree saturation comparison. -/
theorem
    twistedFreeNextDegreeRelationSourceMonomialCompatibility_of_rightTriangle
    (n : ℕ) (T : Scheme.{u})
    (l : ℤ) (r d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (htriangle :
      ProjectiveSpaceOverTwistModuleCancellationRightTriangle n T
        (∐ fun _ : ULift.{u} (Fin r) ↦
          projectiveSpaceOverTwist n T (-l)) d) :
    TwistedFreeNextDegreeRelationSourceMonomialCompatibility
      n T l r d e he u :=
  twistedFreeNextDegreeRelationSourceMonomialCompatibility_of_sheaf
    n T l r d e he u
      (twistedFreeNextDegreeRelationSheafMonomialCompatibility_of_rightTriangle
        n T l r d e he u htriangle)

/-- The reconstructed next-degree source and the algebraically generated source
agree on every degree-one monomial. -/
theorem twistedFreeNextDegreeRelationSourceMonomialCompatibility
    (n : ℕ) (T : Scheme.{u})
    (l : ℤ) (r d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E) :
    TwistedFreeNextDegreeRelationSourceMonomialCompatibility
      n T l r d e he u :=
  twistedFreeNextDegreeRelationSourceMonomialCompatibility_of_rightTriangle
    n T l r d e he u
      (projectiveSpaceOverTwistModuleCancellation_rightTriangle n T
        (∐ fun _ : ULift.{u} (Fin r) ↦
          projectiveSpaceOverTwist n T (-l)) d)

/-- In relative dimension one, source compatibility is exactly the two
commutative squares associated to the two homogeneous coordinates. -/
theorem twistedFreeNextDegreeRelationSourceMonomialCompatibility_one_iff
    (T : Scheme.{u}) (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E) :
    TwistedFreeNextDegreeRelationSourceMonomialCompatibility
        1 T l r d e he u ↔
      (reconstructedNextDegreeRelationSourceMonomialMap
          1 T l r d e he u (ULift.up (0 : Fin 2)) =
        reconstructedNextDegreeGeneratedRelationMonomialMap
          1 T l r d e he u (ULift.up (0 : Fin 2))) ∧
      (reconstructedNextDegreeRelationSourceMonomialMap
          1 T l r d e he u (ULift.up (1 : Fin 2)) =
        reconstructedNextDegreeGeneratedRelationMonomialMap
          1 T l r d e he u (ULift.up (1 : Fin 2))) := by
  constructor
  · intro h
    exact ⟨h (ULift.up (0 : Fin 2)), h (ULift.up (1 : Fin 2))⟩
  · rintro ⟨h0, h1⟩ a
    obtain ⟨a⟩ := a
    fin_cases a
    · exact h0
    · exact h1

/-- The component of the generated reconstructed relation at one variable is
the degree-`d` relation followed by multiplication by that variable. -/
@[reassoc]
lemma reconstructedGeneratedNextDegreeRelation_ι
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (a : ULift.{u} (Fin (n + 1))) :
    Sigma.ι (fun _ : ULift.{u} (Fin (n + 1)) ↦ kernel u) a ≫
        reconstructedGeneratedNextDegreeRelation n T l r d e he u =
      reconstructedNextDegreeGeneratedRelationMonomialMap
        n T l r d e he u a := by
  dsimp only [reconstructedGeneratedNextDegreeRelation,
    reconstructedNextDegreeGeneratedRelationMonomialMap]
  exact Sigma.ι_desc _ a

/-- The explicit compatibility for every variable supplies compatibility with
the generated reconstructed relation. -/
theorem twistedFreeNextDegreeGeneratedRelationSourceCompatibility_of_monomial
    (n : ℕ) (T : Scheme.{u}) [IsAffine T]
    (l : ℤ) (r d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    {E : T.Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (hK : Modules.IsFiniteLocallyFree (kernel u))
    (h : TwistedFreeNextDegreeRelationSourceMonomialCompatibility
      n T l r d e he u) :
    TwistedFreeNextDegreeGeneratedRelationSourceCompatibility
      n T l r d e he u hK := by
  letI : (kernel u).IsQuasicoherent := Modules.kernel_isQuasicoherent u
  apply Sigma.hom_ext
  intro a
  calc
    Sigma.ι (fun _ : ULift.{u} (Fin (n + 1)) ↦ kernel u) a ≫
          (reconstructedNextDegreeRelationSourcePushforwardIso_of_isAffine
              n T d hK).hom ≫
          (Modules.pushforward (projectiveSpaceOverπ n T)).map
            (Modules.tensorMapLeft
              (reconstructedRelation' n T l r d e he u)
              (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ))) =
        reconstructedNextDegreeRelationSourceMonomialMap
          n T l r d e he u a :=
      reconstructedNextDegreeRelationSourcePushforwardIso_hom_ι_comp
        n T l r d e he u hK a
    _ = reconstructedNextDegreeGeneratedRelationMonomialMap
          n T l r d e he u a := h a
    _ = Sigma.ι
        (fun _ : ULift.{u} (Fin (n + 1)) ↦ kernel u) a ≫
        reconstructedGeneratedNextDegreeRelation n T l r d e he u :=
      (reconstructedGeneratedNextDegreeRelation_ι
        n T l r d e he u a).symm

/-- The single coherence assertion remaining after constructing the canonical
relation-source pushforward isomorphism. -/
def TwistedFreeNextDegreeCanonicalRelationSourceCompatibility
    (n : ℕ) (T : Scheme.{u}) [IsAffine T]
    (l : ℤ) (r d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    {E : T.Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (hK : Modules.IsFiniteLocallyFree (kernel u)) : Prop := by
  letI : (kernel u).IsQuasicoherent := Modules.kernel_isQuasicoherent u
  exact (reconstructedNextDegreeRelationSourcePushforwardIso_of_isAffine
      n T d hK).hom ≫
      (Modules.pushforward (projectiveSpaceOverπ n T)).map
        (Modules.tensorMapLeft
          (Abelian.factorThruImage
            (reconstructedRelation' n T l r d e he u))
          (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ))) ≫
      (reconstructedNextDegreeRelationImagePushforwardIsoKernel
        n T l r d e he u).hom =
    twistedFreeNextDegreeReconstructedKernelLift n T l r d e he u

/-- Compatibility with the generated reconstructed relation implies the
image/kernel source compatibility used by the saturation criterion. -/
theorem twistedFreeNextDegreeCanonicalRelationSourceCompatibility_of_generated
    (n : ℕ) (T : Scheme.{u}) [IsAffine T]
    (l : ℤ) (r d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    {E : T.Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (hK : Modules.IsFiniteLocallyFree (kernel u))
    (h : TwistedFreeNextDegreeGeneratedRelationSourceCompatibility
      n T l r d e he u hK) :
    TwistedFreeNextDegreeCanonicalRelationSourceCompatibility
      n T l r d e he u hK := by
  letI : (kernel u).IsQuasicoherent := Modules.kernel_isQuasicoherent u
  let f := reconstructedRelation' n T l r d e he u
  let p := reconstructedQuotientMap' n T l r d e he u
  let O := projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ)
  let q := quotGrassmannianFreeMap n T l r p
    (d + 1) (e + 1) (by omega)
  let A := twistedFreeMonomialPushforwardMap n T l r
    (d + 1) (e + 1) (by omega)
  let src := reconstructedNextDegreeRelationSourcePushforwardIso_of_isAffine
    n T d hK
  let imageIso := reconstructedNextDegreeRelationImagePushforwardIsoKernel
    n T l r d e he u
  let lift := twistedFreeNextDegreeReconstructedKernelLift
    n T l r d e he u
  change src.hom ≫
      (Modules.pushforward (projectiveSpaceOverπ n T)).map
        (Modules.tensorMapLeft (Abelian.factorThruImage f) O) ≫
      imageIso.hom = lift
  apply (cancel_mono (kernel.ι q ≫ A)).1
  calc
    (src.hom ≫
          (Modules.pushforward (projectiveSpaceOverπ n T)).map
            (Modules.tensorMapLeft (Abelian.factorThruImage f) O) ≫
          imageIso.hom) ≫ (kernel.ι q ≫ A) =
        src.hom ≫
          (Modules.pushforward (projectiveSpaceOverπ n T)).map
            (Modules.tensorMapLeft (Abelian.factorThruImage f) O) ≫
          (imageIso.hom ≫ kernel.ι q ≫ A) := by
      simp only [Category.assoc]
    _ = src.hom ≫
          (Modules.pushforward (projectiveSpaceOverπ n T)).map
            (Modules.tensorMapLeft (Abelian.factorThruImage f) O) ≫
          (Modules.pushforward (projectiveSpaceOverπ n T)).map
            (Modules.tensorMapLeft (Abelian.image.ι f) O) := by
      rw [reconstructedNextDegreeRelationImagePushforwardIsoKernel_hom_fac]
    _ = src.hom ≫
          (Modules.pushforward (projectiveSpaceOverπ n T)).map
            (Modules.tensorMapLeft f O) := by
      rw [← Functor.map_comp, ← Modules.tensorMapLeft_comp,
        Abelian.image.fac]
    _ = reconstructedGeneratedNextDegreeRelation n T l r d e he u := h
    _ = twistedFreeNextDegreeRelation n T r e u ≫ A :=
      (twistedFreeNextDegreeRelation_comp_monomialPushforwardMap
        n T l r d e he u).symm
    _ = (lift ≫ kernel.ι q) ≫ A := by
      rw [twistedFreeNextDegreeReconstructedKernelLift_comp]
    _ = lift ≫ (kernel.ι q ≫ A) := Category.assoc _ _ _

/-- The explicit per-variable monomial coherence supplies the canonical source
compatibility needed by saturation. -/
theorem twistedFreeNextDegreeCanonicalRelationSourceCompatibility_of_monomial
    (n : ℕ) (T : Scheme.{u}) [IsAffine T]
    (l : ℤ) (r d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    {E : T.Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (hK : Modules.IsFiniteLocallyFree (kernel u))
    (h : TwistedFreeNextDegreeRelationSourceMonomialCompatibility
      n T l r d e he u) :
    TwistedFreeNextDegreeCanonicalRelationSourceCompatibility
      n T l r d e he u hK :=
  twistedFreeNextDegreeCanonicalRelationSourceCompatibility_of_generated
    n T l r d e he u hK
      (twistedFreeNextDegreeGeneratedRelationSourceCompatibility_of_monomial
        n T l r d e he u hK h)

/-- The right snake identity for the chosen sheaf tensor coherence supplies the
canonical relation-source compatibility required by next-degree saturation. -/
theorem twistedFreeNextDegreeCanonicalRelationSourceCompatibility_of_rightTriangle
    (n : ℕ) (T : Scheme.{u}) [IsAffine T]
    (l : ℤ) (r d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    {E : T.Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (hK : Modules.IsFiniteLocallyFree (kernel u))
    (htriangle :
      ProjectiveSpaceOverTwistModuleCancellationRightTriangle n T
        (∐ fun _ : ULift.{u} (Fin r) ↦
          projectiveSpaceOverTwist n T (-l)) d) :
    TwistedFreeNextDegreeCanonicalRelationSourceCompatibility
      n T l r d e he u hK :=
  twistedFreeNextDegreeCanonicalRelationSourceCompatibility_of_monomial
    n T l r d e he u hK
      (twistedFreeNextDegreeRelationSourceMonomialCompatibility_of_rightTriangle
        n T l r d e he u htriangle)

/-- The canonical reconstructed and generated relation sources agree over an affine
base when the degree-`d` kernel is finite locally free. -/
theorem twistedFreeNextDegreeCanonicalRelationSourceCompatibility
    (n : ℕ) (T : Scheme.{u}) [IsAffine T]
    (l : ℤ) (r d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    {E : T.Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (hK : Modules.IsFiniteLocallyFree (kernel u)) :
    TwistedFreeNextDegreeCanonicalRelationSourceCompatibility
      n T l r d e he u hK :=
  twistedFreeNextDegreeCanonicalRelationSourceCompatibility_of_rightTriangle
    n T l r d e he u hK
      (projectiveSpaceOverTwistModuleCancellation_rightTriangle n T
        (∐ fun _ : ULift.{u} (Fin r) ↦
          projectiveSpaceOverTwist n T (-l)) d)

/-- The canonical source compatibility supplies the source-comparison structure
used by the cohomological saturation criterion. -/
noncomputable def
    TwistedFreeNextDegreeCanonicalRelationSourceCompatibility.toComparison
    (n : ℕ) (T : Scheme.{u}) [IsAffine T]
    (l : ℤ) (r d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    {E : T.Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (hK : Modules.IsFiniteLocallyFree (kernel u))
    (h : TwistedFreeNextDegreeCanonicalRelationSourceCompatibility
      n T l r d e he u hK) :
    TwistedFreeNextDegreeRelationSourcePushforwardComparison
      n T l r d e he u := by
  letI : (kernel u).IsQuasicoherent := Modules.kernel_isQuasicoherent u
  refine {
  sourceIso :=
    reconstructedNextDegreeRelationSourcePushforwardIso_of_isAffine
      n T d hK
  compatibility := ?_ }
  exact h

/-- Over an affine base, the explicit presentation-cohomology vanishings and
the sole canonical commutative square imply full next-degree saturation. -/
theorem twistedFreeNextDegreeReconstructionSaturation_of_canonical_compatibility
    (n : ℕ) (T : Scheme.{u}) [IsAffine T]
    (l : ℤ) (r d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    {E : T.Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (hK : Modules.IsFiniteLocallyFree (kernel u))
    (hpullback1 : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (projectiveSpaceOverTwistModule
          ((Modules.pullback (projectiveSpaceOverπ n T)).obj (kernel u)) 1)).H 1))
    (hrelationKernel1 : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (kernel (Modules.tensorMapLeft
          (Abelian.factorThruImage
            (reconstructedRelation' n T l r d e he u))
          (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ))))).H 1))
    (hrelationKernel2 : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (kernel (Modules.tensorMapLeft
          (Abelian.factorThruImage
            (reconstructedRelation' n T l r d e he u))
          (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ))))).H 2))
    (hcompat : TwistedFreeNextDegreeCanonicalRelationSourceCompatibility
      n T l r d e he u hK) :
    TwistedFreeNextDegreeReconstructionSaturation n T l r d e he u :=
  twistedFreeNextDegreeReconstructionSaturation_of_pullback_one_vanishing
    n T l r d e he u hpullback1 hrelationKernel1 hrelationKernel2
      (hcompat.toComparison n T l r d e he u hK)

/-- Over an affine base, the three presentation-cohomology vanishings and the
explicit per-variable source coherence imply full next-degree saturation. -/
theorem twistedFreeNextDegreeReconstructionSaturation_of_monomial_compatibility
    (n : ℕ) (T : Scheme.{u}) [IsAffine T]
    (l : ℤ) (r d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    {E : T.Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (hK : Modules.IsFiniteLocallyFree (kernel u))
    (hpullback1 : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (projectiveSpaceOverTwistModule
          ((Modules.pullback (projectiveSpaceOverπ n T)).obj (kernel u)) 1)).H 1))
    (hrelationKernel1 : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (kernel (Modules.tensorMapLeft
          (Abelian.factorThruImage
            (reconstructedRelation' n T l r d e he u))
          (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ))))).H 1))
    (hrelationKernel2 : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (kernel (Modules.tensorMapLeft
          (Abelian.factorThruImage
            (reconstructedRelation' n T l r d e he u))
          (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ))))).H 2))
    (hcompat : TwistedFreeNextDegreeRelationSourceMonomialCompatibility
      n T l r d e he u) :
    TwistedFreeNextDegreeReconstructionSaturation n T l r d e he u :=
  twistedFreeNextDegreeReconstructionSaturation_of_canonical_compatibility
    n T l r d e he u hK hpullback1 hrelationKernel1 hrelationKernel2
      (twistedFreeNextDegreeCanonicalRelationSourceCompatibility_of_monomial
        n T l r d e he u hK hcompat)

/-- Over an affine base, the presentation-cohomology vanishings and the right
snake identity for twist cancellation imply full next-degree saturation. -/
theorem twistedFreeNextDegreeReconstructionSaturation_of_rightTriangle
    (n : ℕ) (T : Scheme.{u}) [IsAffine T]
    (l : ℤ) (r d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    {E : T.Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (hK : Modules.IsFiniteLocallyFree (kernel u))
    (hpullback1 : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (projectiveSpaceOverTwistModule
          ((Modules.pullback (projectiveSpaceOverπ n T)).obj (kernel u)) 1)).H 1))
    (hrelationKernel1 : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (kernel (Modules.tensorMapLeft
          (Abelian.factorThruImage
            (reconstructedRelation' n T l r d e he u))
          (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ))))).H 1))
    (hrelationKernel2 : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (kernel (Modules.tensorMapLeft
          (Abelian.factorThruImage
            (reconstructedRelation' n T l r d e he u))
          (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ))))).H 2))
    (htriangle :
      ProjectiveSpaceOverTwistModuleCancellationRightTriangle n T
        (∐ fun _ : ULift.{u} (Fin r) ↦
          projectiveSpaceOverTwist n T (-l)) d) :
    TwistedFreeNextDegreeReconstructionSaturation n T l r d e he u :=
  twistedFreeNextDegreeReconstructionSaturation_of_canonical_compatibility
    n T l r d e he u hK hpullback1 hrelationKernel1 hrelationKernel2
      (twistedFreeNextDegreeCanonicalRelationSourceCompatibility_of_rightTriangle
        n T l r d e he u hK htriangle)

/-- Over an affine base, the three presentation-cohomology vanishings imply full
next-degree saturation; the relation-source coherence is automatic. -/
theorem twistedFreeNextDegreeReconstructionSaturation
    (n : ℕ) (T : Scheme.{u}) [IsAffine T]
    (l : ℤ) (r d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    {E : T.Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (hK : Modules.IsFiniteLocallyFree (kernel u))
    (hpullback1 : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (projectiveSpaceOverTwistModule
          ((Modules.pullback (projectiveSpaceOverπ n T)).obj (kernel u)) 1)).H 1))
    (hrelationKernel1 : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (kernel (Modules.tensorMapLeft
          (Abelian.factorThruImage
            (reconstructedRelation' n T l r d e he u))
          (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ))))).H 1))
    (hrelationKernel2 : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (kernel (Modules.tensorMapLeft
          (Abelian.factorThruImage
            (reconstructedRelation' n T l r d e he u))
          (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ))))).H 2)) :
    TwistedFreeNextDegreeReconstructionSaturation n T l r d e he u :=
  twistedFreeNextDegreeReconstructionSaturation_of_rightTriangle
    n T l r d e he u hK hpullback1 hrelationKernel1 hrelationKernel2
      (projectiveSpaceOverTwistModuleCancellation_rightTriangle n T
        (∐ fun _ : ULift.{u} (Fin r) ↦
          projectiveSpaceOverTwist n T (-l)) d)

end AlgebraicGeometry.Scheme

end

end
