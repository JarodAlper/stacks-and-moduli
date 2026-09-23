module

public import StacksAndModuli.API.SchemeModulesPullbackFreeMap
public import StacksAndModuli.API.SchemeModulesPullbackKernelVectorBundle
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianReflection

/-!
# Base change for twisted-free Grassmannian reconstruction

The tensor-free reconstruction `reconstructedQuotient'` is convenient for comparing
quotient maps, while the positive-twist reconstruction `reconstructedTwisted` has a
particularly simple base-change relation.  This file connects the two descriptions and
uses the positive-twist model to avoid commuting pullback directly with a negative twist.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Tensoring the positive reconstruction relation by `O(-d)` and cancelling the
opposite twists gives the tensor-free reconstruction relation. -/
lemma reconstructedTwistedRelation_tensor_neg_comp_cancel
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (hambient :
      (freeTensorTwistIso n T
          (ULift.{u} (Fin r) × Fin ((n + e).choose n)) (-(d : ℤ))).hom ≫
          twistedFreeMonomialHom n T l r d e he =
        Modules.tensorMapLeft
            (twistedFreeMonomialMap n T l r d e he)
            (projectiveSpaceOverTwist n T (-(d : ℤ))) ≫
          (projectiveSpaceOverTwistModule_cancelIso_nat n T
            (∐ fun _ : ULift.{u} (Fin r) ↦
              projectiveSpaceOverTwist n T (-l)) d).hom) :
    Modules.tensorMapLeft
          ((Modules.pullback (projectiveSpaceOverπ n T)).map
              (kernel.ι u) ≫
            (Modules.pullbackFreeIso (projectiveSpaceOverπ n T)
              (ULift.{u} (Fin r) × Fin ((n + e).choose n))).hom ≫
            twistedFreeMonomialMap n T l r d e he)
          (projectiveSpaceOverTwist n T (-(d : ℤ))) ≫
        (projectiveSpaceOverTwistModule_cancelIso_nat n T
          (∐ fun _ : ULift.{u} (Fin r) ↦
            projectiveSpaceOverTwist n T (-l)) d).hom =
      reconstructedRelation' n T l r d e he u := by
  rw [reconstructedRelation']
  simp only [Modules.tensorMapLeft_comp, Category.assoc]
  rw [← hambient]
  rfl

/-- The reconstruction obtained by twisting the positive cokernel back by `O(-d)` is
canonically isomorphic to the tensor-free reconstruction. -/
noncomputable def reconstructedQuotientIsoReconstructedQuotient'
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (hambient :
      (freeTensorTwistIso n T
          (ULift.{u} (Fin r) × Fin ((n + e).choose n)) (-(d : ℤ))).hom ≫
          twistedFreeMonomialHom n T l r d e he =
        Modules.tensorMapLeft
            (twistedFreeMonomialMap n T l r d e he)
            (projectiveSpaceOverTwist n T (-(d : ℤ))) ≫
          (projectiveSpaceOverTwistModule_cancelIso_nat n T
            (∐ fun _ : ULift.{u} (Fin r) ↦
              projectiveSpaceOverTwist n T (-l)) d).hom) :
    reconstructedQuotient n T l r d e he u ≅
      reconstructedQuotient' n T l r d e he u := by
  let a :=
    (Modules.pullback (projectiveSpaceOverπ n T)).map (kernel.ι u) ≫
      (Modules.pullbackFreeIso (projectiveSpaceOverπ n T)
        (ULift.{u} (Fin r) × Fin ((n + e).choose n))).hom ≫
      twistedFreeMonomialMap n T l r d e he
  let Dm := projectiveSpaceOverTwist n T (-(d : ℤ))
  let H := Modules.tensorRightFunctor Dm
  let c := projectiveSpaceOverTwistModule_cancelIso_nat n T
    (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) d
  change H.obj (cokernel a) ≅
    cokernel (reconstructedRelation' n T l r d e he u)
  exact PreservesCokernel.iso H a ≪≫
    cokernel.mapIso (H.map a)
      (reconstructedRelation' n T l r d e he u)
      (Iso.refl _) c
      (reconstructedTwistedRelation_tensor_neg_comp_cancel
        n T l r d e he u hambient)

/-- Twisting first by `-d` and then by `d` recovers the original module.  This is the
opposite-order companion to `projectiveSpaceOverTwistModule_cancelIso_nat`. -/
noncomputable def projectiveSpaceOverTwistModule_negCancelIso_nat
    (n : ℕ) (T : Scheme.{u})
    (F : (projectiveSpaceOver n T).Modules) (d : ℕ) :
    Modules.tensor
        (projectiveSpaceOverTwistModule F (-(d : ℤ)))
        (projectiveSpaceOverTwist n T (d : ℤ)) ≅ F :=
  Modules.tensorAssocIso F
      (projectiveSpaceOverTwist n T (-(d : ℤ)))
      (projectiveSpaceOverTwist n T (d : ℤ)) ≪≫
    Modules.tensorRightIso F
      (projectiveSpaceOverTwist_addIso_nat n T (-(d : ℤ)) d ≪≫
        eqToIso (congrArg (projectiveSpaceOverTwist n T) (by omega)) ≪≫
        projectiveSpaceOverTwistZeroIso n T) ≪≫
    Modules.tensorUnitIso F

/-- Cancelling a negative projective twist against its positive inverse is natural in
the module sheaf. -/
@[reassoc]
lemma projectiveSpaceOverTwistModule_negCancelIso_nat_hom_naturality
    (n : ℕ) (T : Scheme.{u}) {F F' : (projectiveSpaceOver n T).Modules}
    (f : F ⟶ F') (d : ℕ) :
    Modules.tensorMapLeft
          (Modules.tensorMapLeft f
            (projectiveSpaceOverTwist n T (-(d : ℤ))))
          (projectiveSpaceOverTwist n T (d : ℤ)) ≫
        (projectiveSpaceOverTwistModule_negCancelIso_nat n T F' d).hom =
      (projectiveSpaceOverTwistModule_negCancelIso_nat n T F d).hom ≫ f := by
  let Dm := projectiveSpaceOverTwist n T (-(d : ℤ))
  let Od := projectiveSpaceOverTwist n T (d : ℤ)
  let c := projectiveSpaceOverTwist_addIso_nat n T (-(d : ℤ)) d ≪≫
    eqToIso (congrArg (projectiveSpaceOverTwist n T) (by omega)) ≪≫
    projectiveSpaceOverTwistZeroIso n T
  change Modules.tensorMapLeft (Modules.tensorMapLeft f Dm) Od ≫
        (Modules.tensorAssocIso F' Dm Od).hom ≫
        Modules.tensorMapRight F' c.hom ≫ (Modules.tensorUnitIso F').hom =
      (Modules.tensorAssocIso F Dm Od).hom ≫
        Modules.tensorMapRight F c.hom ≫ (Modules.tensorUnitIso F).hom ≫ f
  calc
    _ = ((Modules.tensorAssocIso F Dm Od).hom ≫
          Modules.tensorMapLeft f (Modules.tensor Dm Od)) ≫
          Modules.tensorMapRight F' c.hom ≫ (Modules.tensorUnitIso F').hom :=
      congrArg
        (fun k ↦ k ≫ Modules.tensorMapRight F' c.hom ≫
          (Modules.tensorUnitIso F').hom)
        (Modules.tensorAssocIso_hom_naturality_left f Dm Od)
    _ = (Modules.tensorAssocIso F Dm Od).hom ≫
        (Modules.tensorMapLeft f (Modules.tensor Dm Od) ≫
          Modules.tensorMapRight F' c.hom) ≫
          (Modules.tensorUnitIso F').hom := by
      simp only [Category.assoc]
    _ = (Modules.tensorAssocIso F Dm Od).hom ≫
        (Modules.tensorMapRight F c.hom ≫
          Modules.tensorMapLeft f
            (SheafOfModules.unit (projectiveSpaceOver n T).ringCatSheaf)) ≫
          (Modules.tensorUnitIso F').hom :=
      congrArg
        (fun k ↦ (Modules.tensorAssocIso F Dm Od).hom ≫ k ≫
          (Modules.tensorUnitIso F').hom)
        (Modules.tensorMap_exchange f c.hom).symm
    _ = (Modules.tensorAssocIso F Dm Od).hom ≫
        Modules.tensorMapRight F c.hom ≫
        (Modules.tensorMapLeft f
            (SheafOfModules.unit (projectiveSpaceOver n T).ringCatSheaf) ≫
          (Modules.tensorUnitIso F').hom) := by
      simp only [Category.assoc]
    _ = (Modules.tensorAssocIso F Dm Od).hom ≫
        Modules.tensorMapRight F c.hom ≫
        ((Modules.tensorUnitIso F).hom ≫ f) :=
      congrArg
        (fun k ↦ (Modules.tensorAssocIso F Dm Od).hom ≫
          Modules.tensorMapRight F c.hom ≫ k)
        (Modules.tensorUnitIso_naturality f)
    _ = _ := rfl

/-- Tensoring a morphism by `O(-d)` detects whether it is zero. -/
lemma tensorMapLeft_projectiveSpaceOverTwist_neg_eq_zero_iff
    (n : ℕ) (T : Scheme.{u}) {F F' : (projectiveSpaceOver n T).Modules}
    (f : F ⟶ F') (d : ℕ) :
    Modules.tensorMapLeft f
        (projectiveSpaceOverTwist n T (-(d : ℤ))) = 0 ↔ f = 0 := by
  constructor
  · intro h
    change (Modules.tensorRightFunctor
      (projectiveSpaceOverTwist n T (-(d : ℤ)))).map f = 0 at h
    have hnat := projectiveSpaceOverTwistModule_negCancelIso_nat_hom_naturality
      n T f d
    change (Modules.tensorRightFunctor
          (projectiveSpaceOverTwist n T (d : ℤ))).map
            ((Modules.tensorRightFunctor
              (projectiveSpaceOverTwist n T (-(d : ℤ)))).map f) ≫
          (projectiveSpaceOverTwistModule_negCancelIso_nat n T F' d).hom =
        (projectiveSpaceOverTwistModule_negCancelIso_nat n T F d).hom ≫ f at hnat
    rw [h] at hnat
    simp only [Functor.map_zero, zero_comp] at hnat
    apply (cancel_epi
      (projectiveSpaceOverTwistModule_negCancelIso_nat n T F d).hom).1
    exact hnat.symm
  · rintro rfl
    change (Modules.tensorRightFunctor
      (projectiveSpaceOverTwist n T (-(d : ℤ)))).map 0 = 0
    exact Functor.map_zero _ _ _

/-- The positive reconstruction relation is annihilated by the degree-`d` twist of
the tensor-free reconstruction quotient map. -/
lemma reconstructedTwistedRelation_comp_twist_reconstructedQuotientMap'_eq_zero
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (hambient :
      (freeTensorTwistIso n T
          (ULift.{u} (Fin r) × Fin ((n + e).choose n)) (-(d : ℤ))).hom ≫
          twistedFreeMonomialHom n T l r d e he =
        Modules.tensorMapLeft
            (twistedFreeMonomialMap n T l r d e he)
            (projectiveSpaceOverTwist n T (-(d : ℤ))) ≫
          (projectiveSpaceOverTwistModule_cancelIso_nat n T
            (∐ fun _ : ULift.{u} (Fin r) ↦
              projectiveSpaceOverTwist n T (-l)) d).hom) :
    let a :=
      (Modules.pullback (projectiveSpaceOverπ n T)).map (kernel.ι u) ≫
        (Modules.pullbackFreeIso (projectiveSpaceOverπ n T)
          (ULift.{u} (Fin r) × Fin ((n + e).choose n))).hom ≫
        twistedFreeMonomialMap n T l r d e he
    a ≫ Modules.tensorMapLeft
      (reconstructedQuotientMap' n T l r d e he u)
      (projectiveSpaceOverTwist n T (d : ℤ)) = 0 := by
  dsimp only
  let a :=
    (Modules.pullback (projectiveSpaceOverπ n T)).map (kernel.ι u) ≫
      (Modules.pullbackFreeIso (projectiveSpaceOverπ n T)
        (ULift.{u} (Fin r) × Fin ((n + e).choose n))).hom ≫
      twistedFreeMonomialMap n T l r d e he
  let p := reconstructedQuotientMap' n T l r d e he u
  let Od := projectiveSpaceOverTwist n T (d : ℤ)
  let Dm := projectiveSpaceOverTwist n T (-(d : ℤ))
  let cF := projectiveSpaceOverTwistModule_cancelIso_nat n T
    (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) d
  let cQ := projectiveSpaceOverTwistModule_cancelIso_nat n T
    (reconstructedQuotient' n T l r d e he u) d
  apply (tensorMapLeft_projectiveSpaceOverTwist_neg_eq_zero_iff
    n T (a ≫ Modules.tensorMapLeft p Od) d).mp
  have hmap := Modules.tensorMapLeft_comp a
    (Modules.tensorMapLeft p Od) Dm
  have hnat :=
    projectiveSpaceOverTwistModule_cancelIso_nat_hom_naturality n T p d
  have hrel := reconstructedTwistedRelation_tensor_neg_comp_cancel
    n T l r d e he u hambient
  have hrel' :
      Modules.tensorMapLeft a Dm ≫ cF.hom =
        reconstructedRelation' n T l r d e he u := by
    simpa only [a, Dm, cF] using hrel
  have hp : reconstructedRelation' n T l r d e he u ≫ p = 0 := by
    dsimp only [p, reconstructedQuotientMap']
    exact cokernel.condition _
  apply (cancel_mono cQ.hom).1
  calc
    Modules.tensorMapLeft (a ≫ Modules.tensorMapLeft p Od) Dm ≫ cQ.hom =
        (Modules.tensorMapLeft a Dm ≫
          Modules.tensorMapLeft (Modules.tensorMapLeft p Od) Dm) ≫
            cQ.hom := congrArg (fun k ↦ k ≫ cQ.hom) hmap
    _ = Modules.tensorMapLeft a Dm ≫
        (Modules.tensorMapLeft (Modules.tensorMapLeft p Od) Dm ≫
          cQ.hom) := Category.assoc _ _ _
    _ = Modules.tensorMapLeft a Dm ≫ (cF.hom ≫ p) :=
      congrArg (fun k ↦ Modules.tensorMapLeft a Dm ≫ k) hnat
    _ = (Modules.tensorMapLeft a Dm ≫ cF.hom) ≫ p :=
      (Category.assoc _ _ _).symm
    _ = 0 ≫ cQ.hom := by
      exact (congrArg (fun k ↦ k ≫ p) hrel').trans
        (hp.trans zero_comp.symm)

/-- The degree-`d` Grassmannian free map of a tensor-free reconstruction kills the
kernel of the finite free quotient from which the reconstruction was formed. -/
lemma kernel_ι_comp_quotGrassmannianFreeMap_reconstructedQuotientMap'_eq_zero
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (hambient :
      (freeTensorTwistIso n T
          (ULift.{u} (Fin r) × Fin ((n + e).choose n)) (-(d : ℤ))).hom ≫
          twistedFreeMonomialHom n T l r d e he =
        Modules.tensorMapLeft
            (twistedFreeMonomialMap n T l r d e he)
            (projectiveSpaceOverTwist n T (-(d : ℤ))) ≫
          (projectiveSpaceOverTwistModule_cancelIso_nat n T
            (∐ fun _ : ULift.{u} (Fin r) ↦
              projectiveSpaceOverTwist n T (-l)) d).hom) :
    let Qd : T.Modules := (Modules.pushforward (projectiveSpaceOverπ n T)).obj
      (projectiveSpaceOverTwistModule
        (reconstructedQuotient' n T l r d e he u) (d : ℤ))
    let q : SheafOfModules.free (R := T.ringCatSheaf)
        (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ Qd :=
      quotGrassmannianFreeMap n T l r
        (reconstructedQuotientMap' n T l r d e he u) d e he
    kernel.ι u ≫ q =
      @Zero.zero (kernel u ⟶ Qd)
        (Limits.HasZeroMorphisms.zero (C := T.Modules) (kernel u) Qd) := by
  dsimp only
  let π := projectiveSpaceOverπ n T
  let p := reconstructedQuotientMap' n T l r d e he u
  let q := quotGrassmannianFreeMap n T l r p d e he
  let Od := projectiveSpaceOverTwist n T (d : ℤ)
  let w := Modules.pullbackFreeIso π
    (ULift.{u} (Fin r) × Fin ((n + e).choose n))
  let m := twistedFreeMonomialMap n T l r d e he
  have hq : (Modules.pullback π).map q ≫
        (Modules.pullbackPushforwardAdjunction π).counit.app
          (projectiveSpaceOverTwistModule
            (reconstructedQuotient' n T l r d e he u) (d : ℤ)) =
      w.hom ≫ m ≫ Modules.tensorMapLeft p Od := by
    simpa only [π, p, q, Od, w, m] using
      pullback_quotGrassmannianFreeMap_comp_counit_eq_twistedFreeMonomialMap
        n T l r p d e he
  have hz :=
    reconstructedTwistedRelation_comp_twist_reconstructedQuotientMap'_eq_zero
      n T l r d e he u hambient
  let adj := Modules.pullbackPushforwardAdjunction π
  let z : kernel u ⟶ (Modules.pushforward π).obj
      (projectiveSpaceOverTwistModule
        (reconstructedQuotient' n T l r d e he u) (d : ℤ)) :=
    @Zero.zero _ (Limits.HasZeroMorphisms.zero
      (C := T.Modules) (kernel u) _)
  have hleft := adj.homEquiv_naturality_left_symm (kernel.ι u) q
  have hq' := adj.homEquiv_counit (X :=
    SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)))
    (Y := projectiveSpaceOverTwistModule
      (reconstructedQuotient' n T l r d e he u) (d : ℤ)) (g := q)
  have hcomp : (Modules.pullback π).map (kernel.ι u) ≫
      (adj.homEquiv _ _).symm q = 0 := by
    rw [hq']
    have hz' :
        ((Modules.pullback π).map (kernel.ι u) ≫ w.hom ≫ m) ≫
          Modules.tensorMapLeft p Od = 0 := by
      simpa only [π, p, Od, w, m] using hz
    exact (congrArg
      (fun k ↦ (Modules.pullback π).map (kernel.ι u) ≫ k) hq).trans
        ((by rfl :
          (Modules.pullback π).map (kernel.ι u) ≫
              (w.hom ≫ m ≫ Modules.tensorMapLeft p Od) =
            ((Modules.pullback π).map (kernel.ι u) ≫ w.hom ≫ m) ≫
              Modules.tensorMapLeft p Od).trans hz')
  have hz' : (adj.homEquiv _ _).symm z = 0 := by
    have hcounit := adj.homEquiv_counit (X := kernel u)
      (Y := projectiveSpaceOverTwistModule
        (reconstructedQuotient' n T l r d e he u) (d : ℤ)) (g := z)
    have hzmap : (Modules.pullback π).map z = 0 := by
      dsimp only [z]
      exact Functor.map_zero _ _ _
    exact hcounit.trans
      ((congrArg (fun k ↦ k ≫ adj.counit.app
        (projectiveSpaceOverTwistModule
          (reconstructedQuotient' n T l r d e he u) (d : ℤ))) hzmap).trans
        zero_comp)
  apply (adj.homEquiv _ _).symm.injective
  exact hleft.trans (hcomp.trans hz'.symm)

/-- After twisting by `d`, the tensor-free reconstruction becomes the positive
reconstruction. -/
noncomputable def reconstructedQuotient'_twistIso_reconstructedTwisted
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (hambient :
      (freeTensorTwistIso n T
          (ULift.{u} (Fin r) × Fin ((n + e).choose n)) (-(d : ℤ))).hom ≫
          twistedFreeMonomialHom n T l r d e he =
        Modules.tensorMapLeft
            (twistedFreeMonomialMap n T l r d e he)
            (projectiveSpaceOverTwist n T (-(d : ℤ))) ≫
          (projectiveSpaceOverTwistModule_cancelIso_nat n T
            (∐ fun _ : ULift.{u} (Fin r) ↦
              projectiveSpaceOverTwist n T (-l)) d).hom) :
    projectiveSpaceOverTwistModule
        (reconstructedQuotient' n T l r d e he u) (d : ℤ) ≅
      reconstructedTwisted n T l r d e he u :=
  Modules.tensorLeftIso
      (reconstructedQuotientIsoReconstructedQuotient'
        n T l r d e he u hambient).symm
      (projectiveSpaceOverTwist n T (d : ℤ)) ≪≫
    projectiveSpaceOverTwistModule_negCancelIso_nat n T
      (reconstructedTwisted n T l r d e he u) d

/-- The normalized pullback of a map out of a canonical free sheaf. -/
noncomputable def pullbackFreeQuotientMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) {I : Type u} {E : Y.Modules}
    (u : SheafOfModules.free (R := Y.ringCatSheaf) I ⟶ E) :
    SheafOfModules.free (R := X.ringCatSheaf) I ⟶
      (Modules.pullback f).obj E :=
  (Modules.pullbackFreeIso f I).inv ≫ (Modules.pullback f).map u

/-- Normalized pullback commutes with reindexing a canonical free source. -/
lemma pullbackFreeQuotientMap_freeMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) {I J : Type u} {E : Y.Modules}
    (e : I → J)
    (u : SheafOfModules.free (R := Y.ringCatSheaf) J ⟶ E) :
    pullbackFreeQuotientMap f
        (SheafOfModules.freeMap (R := Y.ringCatSheaf) e ≫ u) =
      SheafOfModules.freeMap (R := X.ringCatSheaf) e ≫
        pullbackFreeQuotientMap f u := by
  dsimp only [pullbackFreeQuotientMap]
  rw [Functor.map_comp, ← Category.assoc,
    ← Modules.freeMap_comp_pullbackFreeIso_inv f e, Category.assoc]

/-- Pullback of the kernel of a finite-free quotient, normalized by the canonical
pullback isomorphism on the free source. -/
noncomputable def pullbackKernelIsoPullbackFreeQuotientMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) {I : Type u} {E : Y.Modules}
    [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := Y.ringCatSheaf) I ⟶ E) [Epi u]
    (hE : Modules.IsFiniteLocallyFree E) :
    (Modules.pullback f).obj (kernel u) ≅
      kernel (pullbackFreeQuotientMap f u) := by
  letI : (Modules.pullback f).Additive := inferInstance
  haveI : IsIso (kernelComparison u (Modules.pullback f)) :=
    Modules.pullback_kernelComparison_isIso_of_epi_of_isFiniteLocallyFree
      f u hE
  letI : PreservesLimit (parallelPair u 0) (Modules.pullback f) :=
    PreservesKernel.of_iso_comparison (Modules.pullback f) u
  exact PreservesKernel.iso (Modules.pullback f) u ≪≫
    kernel.mapIso (f := (Modules.pullback f).map u)
      (pullbackFreeQuotientMap f u)
      (Modules.pullbackFreeIso f I) (Iso.refl _) (by
        dsimp only [pullbackFreeQuotientMap]
        simp)

/-- The source of the positive reconstruction relation commutes with base change. -/
noncomputable def reconstructedTwistedRelationSourcePullbackIso
    (n : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    {I : Type u} {E : Y.Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := Y.ringCatSheaf) I ⟶ E) [Epi u]
    (hE : Modules.IsFiniteLocallyFree E) :
    (Modules.pullback (projectiveSpaceOverMap n f)).obj
        ((Modules.pullback (projectiveSpaceOverπ n Y)).obj (kernel u)) ≅
      (Modules.pullback (projectiveSpaceOverπ n X)).obj
        (kernel (pullbackFreeQuotientMap f u)) :=
  (Modules.pullbackComp
      (projectiveSpaceOverMap n f) (projectiveSpaceOverπ n Y)).app (kernel u) ≪≫
    (Modules.pullbackCongr (projectiveSpaceOverMap_π n f)).app (kernel u) ≪≫
    (Modules.pullbackComp (projectiveSpaceOverπ n X) f).symm.app (kernel u) ≪≫
    (Modules.pullback (projectiveSpaceOverπ n X)).mapIso
      (pullbackKernelIsoPullbackFreeQuotientMap f u hE)

/-- The positive twisted-free ambient module commutes with base change. -/
noncomputable def reconstructedTwistedTargetPullbackIso
    (n r : ℕ) (l : ℤ) {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) :
    (Modules.pullback (projectiveSpaceOverMap n f)).obj
        (projectiveSpaceOverTwistModule
          (∐ fun _ : ULift.{u} (Fin r) ↦
            projectiveSpaceOverTwist n Y (-l)) (d : ℤ)) ≅
      projectiveSpaceOverTwistModule
        (∐ fun _ : ULift.{u} (Fin r) ↦
          projectiveSpaceOverTwist n X (-l)) (d : ℤ) :=
  projectiveSpaceOverTwistModule_pullbackIso_nat n f
      (∐ fun _ : ULift.{u} (Fin r) ↦
        projectiveSpaceOverTwist n Y (-l)) d ≪≫
    Modules.tensorLeftIso
      (projectiveSpaceOverTwistedFree_pullbackIso n r l f)
      (projectiveSpaceOverTwist n X (d : ℤ))

/-- The positive ambient monomial map commutes with arbitrary base change. -/
lemma twistedFreeMonomialMap_baseChange
    (n r : ℕ) (l : ℤ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) :
    (Modules.pullbackFreeIso (projectiveSpaceOverMap n f)
          (ULift.{u} (Fin r) × Fin ((n + e).choose n))).inv ≫
        (Modules.pullback (projectiveSpaceOverMap n f)).map
          (twistedFreeMonomialMap n Y l r d e he) ≫
        (reconstructedTwistedTargetPullbackIso n r l f d).hom =
      twistedFreeMonomialMap n X l r d e he := by
  apply Modules.pullback_freeHomOfSections_comp
  intro i
  exact twistedFreeMonomialSection_pullback
    n r l f d e he i.1 i.2

/-- The ambient monomial base-change square, oriented from the pulled ambient module. -/
lemma twistedFreeMonomialMap_baseChange_comp
    (n r : ℕ) (l : ℤ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) :
    (Modules.pullback (projectiveSpaceOverMap n f)).map
          (twistedFreeMonomialMap n Y l r d e he) ≫
        (reconstructedTwistedTargetPullbackIso n r l f d).hom =
      (Modules.pullbackFreeIso (projectiveSpaceOverMap n f)
          (ULift.{u} (Fin r) × Fin ((n + e).choose n))).hom ≫
        twistedFreeMonomialMap n X l r d e he := by
  apply (cancel_epi
    (Modules.pullbackFreeIso (projectiveSpaceOverMap n f)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n))).inv).1
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact twistedFreeMonomialMap_baseChange n r l f d e he

set_option maxHeartbeats 1200000 in
-- The proof normalizes three nested pullback comparison isomorphisms on a free sheaf.
/-- The source comparison for the positive reconstruction carries the pulled kernel
inclusion to the normalized kernel inclusion on the new base. -/
lemma reconstructedTwistedRelationSourcePullbackIso_hom_comp
    (n : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    {I : Type u} {E : Y.Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := Y.ringCatSheaf) I ⟶ E) [Epi u]
    (hE : Modules.IsFiniteLocallyFree E) :
    (reconstructedTwistedRelationSourcePullbackIso n f u hE).hom ≫
        (Modules.pullback (projectiveSpaceOverπ n X)).map
          (kernel.ι (pullbackFreeQuotientMap f u)) ≫
        (Modules.pullbackFreeIso (projectiveSpaceOverπ n X) I).hom =
      (Modules.pullback (projectiveSpaceOverMap n f)).map
          ((Modules.pullback (projectiveSpaceOverπ n Y)).map (kernel.ι u) ≫
            (Modules.pullbackFreeIso (projectiveSpaceOverπ n Y) I).hom) ≫
        (Modules.pullbackFreeIso (projectiveSpaceOverMap n f) I).hom := by
  have hk : (pullbackKernelIsoPullbackFreeQuotientMap f u hE).hom ≫
      kernel.ι (pullbackFreeQuotientMap f u) =
      (Modules.pullback f).map (kernel.ι u) ≫
        (Modules.pullbackFreeIso f I).hom := by
    dsimp only [pullbackKernelIsoPullbackFreeQuotientMap,
      Iso.trans_hom]
    simp only [Category.assoc, PreservesKernel.iso_hom,
      kernel.mapIso, kernel.map, kernel.lift_ι]
    rw [← Category.assoc, kernelComparison_comp_ι]
  dsimp only [reconstructedTwistedRelationSourcePullbackIso,
    Iso.trans_hom, Functor.mapIso_hom]
  simp only [Category.assoc, Functor.map_comp]
  slice_lhs 4 5 => rw [← Functor.map_comp, hk, Functor.map_comp]
  let h := projectiveSpaceOverMap n f
  let pY := projectiveSpaceOverπ n Y
  let pX := projectiveSpaceOverπ n X
  let C : Modules.pullback pY ⋙ Modules.pullback h ≅
      Modules.pullback f ⋙ Modules.pullback pX :=
    Modules.pullbackComp h pY ≪≫
      Modules.pullbackCongr (projectiveSpaceOverMap_π n f) ≪≫
      (Modules.pullbackComp pX f).symm
  have hfree : C.hom.app (SheafOfModules.free I) ≫
        (Modules.pullback pX).map (Modules.pullbackFreeIso f I).hom ≫
        (Modules.pullbackFreeIso pX I).hom =
      (Modules.pullback h).map (Modules.pullbackFreeIso pY I).hom ≫
        (Modules.pullbackFreeIso h I).hom := by
    let pc₁ := Modules.pullbackComp h pY
    let pc₂ := Modules.pullbackComp pX f
    let pg := Modules.pullbackCongr (projectiveSpaceOverMap_π n f)
    let z : SheafOfModules.free
        (R := (projectiveSpaceOver n X).ringCatSheaf) I ⟶
        (Modules.pullback h).obj
          ((Modules.pullback pY).obj (SheafOfModules.free I)) :=
      (Modules.pullbackFreeIso h I).inv ≫
        (Modules.pullback h).map (Modules.pullbackFreeIso pY I).inv
    have hc₁ : z ≫ pc₁.hom.app (SheafOfModules.free I) =
        (Modules.pullbackFreeIso (h ≫ pY) I).inv := by
      exact Modules.pullbackFreeIso_comp h pY I
    have hcg : (Modules.pullbackFreeIso (h ≫ pY) I).inv ≫
          pg.hom.app (SheafOfModules.free I) =
        (Modules.pullbackFreeIso (pX ≫ f) I).inv := by
      have hg := Modules.pullbackFreeIso_congr
        (projectiveSpaceOverMap_π n f) I
      apply (cancel_mono
        (pg.inv.app (SheafOfModules.free I))).1
      simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
      exact hg.symm
    have hc₂ : (Modules.pullbackFreeIso (pX ≫ f) I).inv ≫
          pc₂.inv.app (SheafOfModules.free I) =
        (Modules.pullbackFreeIso pX I).inv ≫
          (Modules.pullback pX).map (Modules.pullbackFreeIso f I).inv := by
      have hh := Modules.pullbackFreeIso_comp pX f I
      apply (cancel_mono
        (pc₂.hom.app (SheafOfModules.free I))).1
      simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
      exact hh.symm
    apply (cancel_epi z).1
    change z ≫ C.hom.app (SheafOfModules.free I) ≫
        (Modules.pullback pX).map (Modules.pullbackFreeIso f I).hom ≫
        (Modules.pullbackFreeIso pX I).hom =
      z ≫ (Modules.pullback h).map
          (Modules.pullbackFreeIso pY I).hom ≫
        (Modules.pullbackFreeIso h I).hom
    calc
      _ = (z ≫ pc₁.hom.app (SheafOfModules.free I)) ≫
          pg.hom.app (SheafOfModules.free I) ≫
          pc₂.inv.app (SheafOfModules.free I) ≫
          (Modules.pullback pX).map (Modules.pullbackFreeIso f I).hom ≫
          (Modules.pullbackFreeIso pX I).hom := by
        rfl
      _ = (Modules.pullbackFreeIso (h ≫ pY) I).inv ≫
          pg.hom.app (SheafOfModules.free I) ≫
          pc₂.inv.app (SheafOfModules.free I) ≫
          (Modules.pullback pX).map (Modules.pullbackFreeIso f I).hom ≫
          (Modules.pullbackFreeIso pX I).hom := by rw [hc₁]
      _ = (Modules.pullbackFreeIso (pX ≫ f) I).inv ≫
          pc₂.inv.app (SheafOfModules.free I) ≫
          (Modules.pullback pX).map (Modules.pullbackFreeIso f I).hom ≫
          (Modules.pullbackFreeIso pX I).hom := by
        rw [← Category.assoc, hcg]
      _ = ((Modules.pullbackFreeIso pX I).inv ≫
            (Modules.pullback pX).map (Modules.pullbackFreeIso f I).inv) ≫
          (Modules.pullback pX).map (Modules.pullbackFreeIso f I).hom ≫
          (Modules.pullbackFreeIso pX I).hom := by
        rw [← Category.assoc, hc₂]
      _ = 𝟙 _ := by simp
      _ = z ≫ (Modules.pullback h).map
          (Modules.pullbackFreeIso pY I).hom ≫
          (Modules.pullbackFreeIso h I).hom := by
        dsimp only [z]
        simp
  let k := kernel.ι u
  have hnat := C.hom.naturality k
  have hnat' :
      (Modules.pullback h).map ((Modules.pullback pY).map k) ≫
          C.hom.app (SheafOfModules.free I) =
        C.hom.app (kernel u) ≫
          (Modules.pullback pX).map ((Modules.pullback f).map k) := hnat
  change C.hom.app (kernel u) ≫
        (Modules.pullback pX).map ((Modules.pullback f).map k) ≫
        (Modules.pullback pX).map (Modules.pullbackFreeIso f I).hom ≫
        (Modules.pullbackFreeIso pX I).hom =
      (Modules.pullback h).map ((Modules.pullback pY).map k) ≫
        (Modules.pullback h).map (Modules.pullbackFreeIso pY I).hom ≫
        (Modules.pullbackFreeIso h I).hom
  rw [← Category.assoc, ← hnat']
  exact congrArg
    (fun a ↦ (Modules.pullback h).map ((Modules.pullback pY).map k) ≫ a)
    hfree

/-- The positive reconstruction relation commutes with arbitrary base change. -/
lemma reconstructedTwistedRelation_baseChange
    (n : ℕ) (l : ℤ) (r : ℕ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ))
    {X Y : Scheme.{u}} (f : X ⟶ Y) {E : Y.Modules}
    [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := Y.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    [Epi u] (hE : Modules.IsFiniteLocallyFree E) :
    (Modules.pullback (projectiveSpaceOverMap n f)).map
          ((Modules.pullback (projectiveSpaceOverπ n Y)).map (kernel.ι u) ≫
            (Modules.pullbackFreeIso (projectiveSpaceOverπ n Y)
              (ULift.{u} (Fin r) × Fin ((n + e).choose n))).hom ≫
            twistedFreeMonomialMap n Y l r d e he) ≫
        (reconstructedTwistedTargetPullbackIso n r l f d).hom =
      (reconstructedTwistedRelationSourcePullbackIso n f u hE).hom ≫
        (Modules.pullback (projectiveSpaceOverπ n X)).map
          (kernel.ι (pullbackFreeQuotientMap f u)) ≫
        (Modules.pullbackFreeIso (projectiveSpaceOverπ n X)
          (ULift.{u} (Fin r) × Fin ((n + e).choose n))).hom ≫
        twistedFreeMonomialMap n X l r d e he := by
  simp only [Functor.map_comp, Category.assoc]
  rw [twistedFreeMonomialMap_baseChange_comp n r l f d e he]
  have hsource := reconstructedTwistedRelationSourcePullbackIso_hom_comp
    n f u hE
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun k ↦ k ≫ twistedFreeMonomialMap n X l r d e he)
      hsource.symm

/-- The positive twisted-free reconstruction commutes with arbitrary base change when
the finite-free quotient target is a vector bundle. -/
noncomputable def reconstructedTwistedPullbackIso
    (n : ℕ) (l : ℤ) (r : ℕ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ))
    {X Y : Scheme.{u}} (f : X ⟶ Y) {E : Y.Modules}
    [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := Y.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    [Epi u] (hE : Modules.IsFiniteLocallyFree E) :
    (Modules.pullback (projectiveSpaceOverMap n f)).obj
        (reconstructedTwisted n Y l r d e he u) ≅
      reconstructedTwisted n X l r d e he
        (pullbackFreeQuotientMap f u) := by
  let a :=
    (Modules.pullback (projectiveSpaceOverπ n Y)).map (kernel.ι u) ≫
      (Modules.pullbackFreeIso (projectiveSpaceOverπ n Y)
        (ULift.{u} (Fin r) × Fin ((n + e).choose n))).hom ≫
      twistedFreeMonomialMap n Y l r d e he
  let b :=
    (Modules.pullback (projectiveSpaceOverπ n X)).map
        (kernel.ι (pullbackFreeQuotientMap f u)) ≫
      (Modules.pullbackFreeIso (projectiveSpaceOverπ n X)
        (ULift.{u} (Fin r) × Fin ((n + e).choose n))).hom ≫
      twistedFreeMonomialMap n X l r d e he
  change (Modules.pullback (projectiveSpaceOverMap n f)).obj
      (cokernel a) ≅ cokernel b
  exact PreservesCokernel.iso
      (Modules.pullback (projectiveSpaceOverMap n f)) a ≪≫
    cokernel.mapIso
      ((Modules.pullback (projectiveSpaceOverMap n f)).map a) b
      (reconstructedTwistedRelationSourcePullbackIso n f u hE)
      (reconstructedTwistedTargetPullbackIso n r l f d)
      (reconstructedTwistedRelation_baseChange
        n l r d e he f u hE)

/-- The tensor-free twisted-free reconstruction commutes with arbitrary base change.
The proof twists positively, applies base change to the positive reconstruction, and
then cancels the positive twist on the new base. -/
noncomputable def reconstructedQuotient'PullbackIso
    (n : ℕ) (l : ℤ) (r : ℕ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ))
    {X Y : Scheme.{u}} (f : X ⟶ Y) {E : Y.Modules}
    [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := Y.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    [Epi u] (hE : Modules.IsFiniteLocallyFree E)
    (hambientY :
      (freeTensorTwistIso n Y
          (ULift.{u} (Fin r) × Fin ((n + e).choose n)) (-(d : ℤ))).hom ≫
          twistedFreeMonomialHom n Y l r d e he =
        Modules.tensorMapLeft
            (twistedFreeMonomialMap n Y l r d e he)
            (projectiveSpaceOverTwist n Y (-(d : ℤ))) ≫
          (projectiveSpaceOverTwistModule_cancelIso_nat n Y
            (∐ fun _ : ULift.{u} (Fin r) ↦
              projectiveSpaceOverTwist n Y (-l)) d).hom)
    (hambientX :
      (freeTensorTwistIso n X
          (ULift.{u} (Fin r) × Fin ((n + e).choose n)) (-(d : ℤ))).hom ≫
          twistedFreeMonomialHom n X l r d e he =
        Modules.tensorMapLeft
            (twistedFreeMonomialMap n X l r d e he)
            (projectiveSpaceOverTwist n X (-(d : ℤ))) ≫
          (projectiveSpaceOverTwistModule_cancelIso_nat n X
            (∐ fun _ : ULift.{u} (Fin r) ↦
              projectiveSpaceOverTwist n X (-l)) d).hom) :
    (Modules.pullback (projectiveSpaceOverMap n f)).obj
        (reconstructedQuotient' n Y l r d e he u) ≅
      reconstructedQuotient' n X l r d e he
        (pullbackFreeQuotientMap f u) := by
  let QY := reconstructedQuotient' n Y l r d e he u
  let uX := pullbackFreeQuotientMap f u
  let QX := reconstructedQuotient' n X l r d e he uX
  let h := projectiveSpaceOverMap n f
  let A := (Modules.pullback h).obj QY
  let Eₑ : projectiveSpaceOverTwistModule A (d : ℤ) ≅
      projectiveSpaceOverTwistModule QX (d : ℤ) :=
    (projectiveSpaceOverTwistModule_pullbackIso_nat n f QY d).symm ≪≫
      (Modules.pullback h).mapIso
        (reconstructedQuotient'_twistIso_reconstructedTwisted
          n Y l r d e he u hambientY) ≪≫
      reconstructedTwistedPullbackIso n l r d e he f u hE ≪≫
      (reconstructedQuotient'_twistIso_reconstructedTwisted
        n X l r d e he uX hambientX).symm
  exact (projectiveSpaceOverTwistModule_cancelIso_nat n X A d).symm ≪≫
    Modules.tensorLeftIso Eₑ
      (projectiveSpaceOverTwist n X (-(d : ℤ))) ≪≫
    projectiveSpaceOverTwistModule_cancelIso_nat n X QX d

end AlgebraicGeometry.Scheme

end

end
