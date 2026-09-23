module

public import StacksAndModuli.API.TwistedFreeQuotGrassmannianFlatteningFibreCanonical

/-!
# Universal fixed-degree comparison for twisted-free reconstruction

The degree-`d` monomial map of a pulled-back reconstruction descends through the
finite-free quotient from which the reconstruction was formed.  The proof works with
the positive reconstruction relation, whose base-change square is canonical, and
therefore avoids a separate quotient-map triangle for the untwisted cokernel model.

An epimorphic map between the resulting equal-rank vector bundles is then an
isomorphism.  These lemmas provide the algebraic core of the universal compatibility
field in the Quot-to-Grassmannian flattening-fibre construction.
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

namespace Modules

/-- Two strict quotients of the same finite free sheaf, with equal-rank vector-bundle
targets, have canonically isomorphic targets as soon as the second map kills the kernel
of the first. -/
noncomputable def freeQuotientTargetIsoOfKernelVanishing
    {X : Scheme.{u}} {I : Type u} {E M : X.Modules}
    [E.IsQuasicoherent] [M.IsQuasicoherent] {q : ℕ}
    (u : SheafOfModules.free (R := X.ringCatSheaf) I ⟶ E) [Epi u]
    (v : SheafOfModules.free (R := X.ringCatSheaf) I ⟶ M) [Epi v]
    (hzero : kernel.ι u ≫ v =
      @Zero.zero (kernel u ⟶ M)
        (Limits.HasZeroMorphisms.zero (C := X.Modules) (kernel u) M))
    (hE : IsProjectiveOfRank q E)
    (hM : IsProjectiveOfRank q M) : E ≅ M := by
  let c := Abelian.epiDesc u v hzero
  have hc : u ≫ c = v := by
    dsimp only [c]
    exact Abelian.comp_epiDesc u v hzero
  let hcEpi : Epi c := epi_of_epi_fac hc
  let hcIso : IsIso c :=
    @isIso_of_epi_of_isProjectiveOfRank X E M _ _ q hE hM c hcEpi
  exact @asIso _ _ _ _ c hcIso

/-- The equal-rank target isomorphism respects the two maps from the common finite
free source. -/
@[reassoc (attr := simp)]
lemma freeQuotientTargetIsoOfKernelVanishing_comp
    {X : Scheme.{u}} {I : Type u} {E M : X.Modules}
    [E.IsQuasicoherent] [M.IsQuasicoherent] {q : ℕ}
    (u : SheafOfModules.free (R := X.ringCatSheaf) I ⟶ E) [Epi u]
    (v : SheafOfModules.free (R := X.ringCatSheaf) I ⟶ M) [Epi v]
    (hzero : kernel.ι u ≫ v =
      @Zero.zero (kernel u ⟶ M)
        (Limits.HasZeroMorphisms.zero (C := X.Modules) (kernel u) M))
    (hE : IsProjectiveOfRank q E)
    (hM : IsProjectiveOfRank q M) :
    u ≫ (freeQuotientTargetIsoOfKernelVanishing
      u v hzero hE hM).hom = v := by
  unfold freeQuotientTargetIsoOfKernelVanishing
  exact Abelian.comp_epiDesc u v hzero

end Modules

/-- Postcomposing a quotient on projective space with an isomorphism postcomposes its
degree-`d` Grassmannian map with the induced isomorphism on twisted pushforwards. -/
lemma quotGrassmannianFreeMap_comp_targetIso
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ)
    {Q Q' : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    (E : Q ≅ Q') (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) :
    quotGrassmannianFreeMap n T l r p d e he ≫
        ((Modules.pushforward (projectiveSpaceOverπ n T)).mapIso
          (Modules.tensorLeftIso E
            (projectiveSpaceOverTwist n T (d : ℤ)))).hom =
      quotGrassmannianFreeMap n T l r (p ≫ E.hom) d e he := by
  dsimp only [quotGrassmannianFreeMap]
  rw [Modules.freeHomOfSections_comp]
  apply congrArg Modules.freeHomOfSections
  funext i
  change Modules.Hom.app
      (Modules.tensorMapLeft E.hom
        (projectiveSpaceOverTwist n T (d : ℤ))) ⊤
      (quotMonomialSection n T l r p d e he i.1 i.2) = _
  dsimp only [quotMonomialSection]
  have htensor : Modules.tensorMapLeft p
        (projectiveSpaceOverTwist n T (d : ℤ)) ≫
      Modules.tensorMapLeft E.hom
        (projectiveSpaceOverTwist n T (d : ℤ)) =
    Modules.tensorMapLeft (p ≫ E.hom)
      (projectiveSpaceOverTwist n T (d : ℤ)) := by
    rw [Modules.tensorMapLeft_comp]
  exact congrArg (fun k ↦ Modules.Hom.app k ⊤
    (twistedFreeMonomialSection n T l r d e he i.1 i.2)) htensor

/-- Reindexing the normalized Quot monomial map from `Fin m` back to the product
monomial basis recovers the unreindexed Grassmannian map. -/
lemma twistedFreeQuotGrassmannianFreeMap_reindex
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) {T : Over S}
    (a : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) {m : ℕ}
    (σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n)) :
    SheafOfModules.freeMap (R := T.left.ringCatSheaf) σ.symm ≫
        twistedFreeQuotGrassmannianFreeMap n S l r a d e he σ =
      quotGrassmannianFreeMap n T.left l r
        (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T a)
        d e he := by
  dsimp only [twistedFreeQuotGrassmannianFreeMap, quotGrassmannianFreeMap]
  rw [Modules.freeMap_comp_freeHomOfSections]
  apply congrArg Modules.freeHomOfSections
  funext i
  simp only [Equiv.apply_symm_apply]

/-- Denormalizing a quotient on the standard relative projective space, applying the
normalized Quot monomial map, and then returning along the normalization isomorphism
recovers the original degree-`d` Grassmannian map. -/
lemma denormalized_twistedFreeQuotGrassmannianFreeMap_reindex
    {S : Scheme.{u}} (n : ℕ) (l : ℤ) (r : ℕ) (T : Over S)
    (Q : (projectiveSpaceOver n T.left).Modules) [Q.IsQuasicoherent]
    (hQfp : Q.IsFinitePresentation)
    (hQflat : Q.FlatOver (projectiveSpaceOverπ n T.left))
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T.left (-l)) ⟶ Q) [Epi p]
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) {m : ℕ}
    (σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n)) :
    let a := Modules.QuotientPullbackData.ofTwistedFreeQuotientOnProjectiveSpace
      (n := n) (r := r) (l := l) T Q hQfp hQflat p
    let E := Modules.QuotientPullbackData.ofTwistedFreeQuotientOnProjectiveSpace_quotDataIso
      (n := n) (r := r) (l := l) T Q hQfp hQflat p
    SheafOfModules.freeMap (R := T.left.ringCatSheaf) σ.symm ≫
        twistedFreeQuotGrassmannianFreeMap n S l r a d e he σ ≫
        ((Modules.pushforward (projectiveSpaceOverπ n T.left)).mapIso
          (Modules.tensorLeftIso E
            (projectiveSpaceOverTwist n T.left (d : ℤ)))).hom =
      quotGrassmannianFreeMap n T.left l r p d e he := by
  dsimp only
  calc
    _ = (SheafOfModules.freeMap (R := T.left.ringCatSheaf) σ.symm ≫
          twistedFreeQuotGrassmannianFreeMap n S l r
            (Modules.QuotientPullbackData.ofTwistedFreeQuotientOnProjectiveSpace
              T Q hQfp hQflat p) d e he σ) ≫
        ((Modules.pushforward (projectiveSpaceOverπ n T.left)).mapIso
          (Modules.tensorLeftIso
            (Modules.QuotientPullbackData.ofTwistedFreeQuotientOnProjectiveSpace_quotDataIso
              T Q hQfp hQflat p)
            (projectiveSpaceOverTwist n T.left (d : ℤ)))).hom := rfl
    _ = quotGrassmannianFreeMap n T.left l r
          (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T
            (Modules.QuotientPullbackData.ofTwistedFreeQuotientOnProjectiveSpace
              T Q hQfp hQflat p)) d e he ≫
        ((Modules.pushforward (projectiveSpaceOverπ n T.left)).mapIso
          (Modules.tensorLeftIso
            (Modules.QuotientPullbackData.ofTwistedFreeQuotientOnProjectiveSpace_quotDataIso
              T Q hQfp hQflat p)
            (projectiveSpaceOverTwist n T.left (d : ℤ)))).hom :=
      congrArg (fun k ↦ k ≫
        ((Modules.pushforward (projectiveSpaceOverπ n T.left)).mapIso
          (Modules.tensorLeftIso
            (Modules.QuotientPullbackData.ofTwistedFreeQuotientOnProjectiveSpace_quotDataIso
              T Q hQfp hQflat p)
            (projectiveSpaceOverTwist n T.left (d : ℤ)))).hom)
        (twistedFreeQuotGrassmannianFreeMap_reindex
          n S l r _ d e he σ)
    _ = quotGrassmannianFreeMap n T.left l r
          (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T
            (Modules.QuotientPullbackData.ofTwistedFreeQuotientOnProjectiveSpace
              T Q hQfp hQflat p) ≫
            (Modules.QuotientPullbackData.ofTwistedFreeQuotientOnProjectiveSpace_quotDataIso
              T Q hQfp hQflat p).hom) d e he :=
      quotGrassmannianFreeMap_comp_targetIso n T.left l r _ _ d e he
    _ = _ := congrArg
      (fun k ↦ quotGrassmannianFreeMap n T.left l r k d e he)
      (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver_ofTwistedFreeQuotient_comp_quotDataIso
        T Q hQfp hQflat p)

/-- If the positive reconstruction relation is killed after twisting a quotient map by
`d`, then the associated degree-`d` Grassmannian free map kills the original finite-free
kernel on the base. -/
lemma kernel_ι_comp_quotGrassmannianFreeMap_eq_zero_of_twistedRelation
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    (hrelation :
      ((Modules.pullback (projectiveSpaceOverπ n T)).map (kernel.ι u) ≫
          (Modules.pullbackFreeIso (projectiveSpaceOverπ n T)
            (ULift.{u} (Fin r) × Fin ((n + e).choose n))).hom ≫
          twistedFreeMonomialMap n T l r d e he) ≫
        Modules.tensorMapLeft p
          (projectiveSpaceOverTwist n T (d : ℤ)) = 0) :
    let Qd : T.Modules := (Modules.pushforward (projectiveSpaceOverπ n T)).obj
      (projectiveSpaceOverTwistModule Q (d : ℤ))
    let q : SheafOfModules.free (R := T.ringCatSheaf)
        (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ Qd :=
      quotGrassmannianFreeMap n T l r p d e he
    kernel.ι u ≫ q =
      @Zero.zero (kernel u ⟶ Qd)
        (Limits.HasZeroMorphisms.zero (C := T.Modules) (kernel u) Qd) := by
  dsimp only
  let π := projectiveSpaceOverπ n T
  let q := quotGrassmannianFreeMap n T l r p d e he
  let Od := projectiveSpaceOverTwist n T (d : ℤ)
  let w := Modules.pullbackFreeIso π
    (ULift.{u} (Fin r) × Fin ((n + e).choose n))
  let m := twistedFreeMonomialMap n T l r d e he
  have hq : (Modules.pullback π).map q ≫
        (Modules.pullbackPushforwardAdjunction π).counit.app
          (projectiveSpaceOverTwistModule Q (d : ℤ)) =
      w.hom ≫ m ≫ Modules.tensorMapLeft p Od := by
    simpa only [π, q, Od, w, m] using
      pullback_quotGrassmannianFreeMap_comp_counit_eq_twistedFreeMonomialMap
        n T l r p d e he
  let adj := Modules.pullbackPushforwardAdjunction π
  let z : kernel u ⟶ (Modules.pushforward π).obj
      (projectiveSpaceOverTwistModule Q (d : ℤ)) :=
    @Zero.zero _ (Limits.HasZeroMorphisms.zero
      (C := T.Modules) (kernel u) _)
  have hleft := adj.homEquiv_naturality_left_symm (kernel.ι u) q
  have hq' := adj.homEquiv_counit (X :=
    SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)))
    (Y := projectiveSpaceOverTwistModule Q (d : ℤ)) (g := q)
  have hcomp : (Modules.pullback π).map (kernel.ι u) ≫
      (adj.homEquiv _ _).symm q = 0 := by
    rw [hq']
    have hz' :
        ((Modules.pullback π).map (kernel.ι u) ≫ w.hom ≫ m) ≫
          Modules.tensorMapLeft p Od = 0 := by
      simpa only [π, Od, w, m] using hrelation
    exact (congrArg
      (fun k ↦ (Modules.pullback π).map (kernel.ι u) ≫ k) hq).trans
        ((by rfl :
          (Modules.pullback π).map (kernel.ι u) ≫
              (w.hom ≫ m ≫ Modules.tensorMapLeft p Od) =
            ((Modules.pullback π).map (kernel.ι u) ≫ w.hom ≫ m) ≫
              Modules.tensorMapLeft p Od).trans hz')
  have hz' : (adj.homEquiv _ _).symm z = 0 := by
    have hcounit := adj.homEquiv_counit (X := kernel u)
      (Y := projectiveSpaceOverTwistModule Q (d : ℤ)) (g := z)
    have hzmap : (Modules.pullback π).map z = 0 := by
      dsimp only [z]
      exact Functor.map_zero _ _ _
    exact hcounit.trans
      ((congrArg (fun k ↦ k ≫ adj.counit.app
        (projectiveSpaceOverTwistModule Q (d : ℤ))) hzmap).trans zero_comp)
  apply (adj.homEquiv _ _).symm.injective
  exact hleft.trans (hcomp.trans hz'.symm)

/-- Pulling the tensor-free reconstruction quotient map to a new base kills the
positive reconstruction relation formed from the normalized pulled finite-free
quotient. -/
lemma reconstructedPullbackRelation_comp_twistQuotientMap_eq_zero
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
              projectiveSpaceOverTwist n Y (-l)) d).hom) :
    let uX := pullbackFreeQuotientMap f u
    let pY := reconstructedQuotientMap' n Y l r d e he u
    let pX := (projectiveSpaceOverTwistedFree_pullbackIso n r l f).inv ≫
      (Modules.pullback (projectiveSpaceOverMap n f)).map pY
    ((Modules.pullback (projectiveSpaceOverπ n X)).map (kernel.ι uX) ≫
        (Modules.pullbackFreeIso (projectiveSpaceOverπ n X)
          (ULift.{u} (Fin r) × Fin ((n + e).choose n))).hom ≫
        twistedFreeMonomialMap n X l r d e he) ≫
      Modules.tensorMapLeft pX
        (projectiveSpaceOverTwist n X (d : ℤ)) = 0 := by
  dsimp only
  let h := projectiveSpaceOverMap n f
  let uX := pullbackFreeQuotientMap f u
  let QY := reconstructedQuotient' n Y l r d e he u
  let pY := reconstructedQuotientMap' n Y l r d e he u
  let QX := (Modules.pullback h).obj QY
  let eF := projectiveSpaceOverTwistedFree_pullbackIso n r l f
  let pX := eF.inv ≫ (Modules.pullback h).map pY
  let OdY := projectiveSpaceOverTwist n Y (d : ℤ)
  let OdX := projectiveSpaceOverTwist n X (d : ℤ)
  let tY := Modules.tensorMapLeft pY OdY
  let tX := Modules.tensorMapLeft pX OdX
  let aY :=
    (Modules.pullback (projectiveSpaceOverπ n Y)).map (kernel.ι u) ≫
      (Modules.pullbackFreeIso (projectiveSpaceOverπ n Y)
        (ULift.{u} (Fin r) × Fin ((n + e).choose n))).hom ≫
      twistedFreeMonomialMap n Y l r d e he
  let aX :=
    (Modules.pullback (projectiveSpaceOverπ n X)).map (kernel.ι uX) ≫
      (Modules.pullbackFreeIso (projectiveSpaceOverπ n X)
        (ULift.{u} (Fin r) × Fin ((n + e).choose n))).hom ≫
      twistedFreeMonomialMap n X l r d e he
  let eT := reconstructedTwistedTargetPullbackIso n r l f d
  let eS := reconstructedTwistedRelationSourcePullbackIso n f u hE
  let eQ := projectiveSpaceOverTwistModule_pullbackIso_nat n f QY d
  let eA := projectiveSpaceOverTwistModule_pullbackIso_nat n f
    (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n Y (-l)) d
  have hnat := projectiveSpaceOverTwistModule_pullbackIso_nat_naturality
    n f pY d
  have hnat' : (Modules.pullback h).map tY ≫ eQ.hom =
      eA.hom ≫ Modules.tensorMapLeft
        ((Modules.pullback h).map pY) OdX := by
    simpa only [h, QY, pY, tY, OdY, OdX, eQ, eA] using hnat
  have hp : (Modules.pullback h).map tY ≫ eQ.hom =
      eT.hom ≫ tX := by
    calc
      _ = eA.hom ≫ Modules.tensorMapLeft
          ((Modules.pullback h).map pY) OdX := hnat'
      _ = eT.hom ≫ tX := by
        dsimp only [eT, reconstructedTwistedTargetPullbackIso, Iso.trans_hom,
          tX, pX, eA]
        rw [Modules.tensorMapLeft_comp]
        symm
        change eA.hom ≫
            (Modules.tensorLeftIso eF OdX).hom ≫
            (Modules.tensorLeftIso eF OdX).inv ≫
            Modules.tensorMapLeft ((Modules.pullback h).map pY) OdX = _
        unfold projectiveSpaceOverTwistModule
        simp only [Iso.hom_inv_id_assoc]
        rfl
  have hrel := reconstructedTwistedRelation_baseChange
    n l r d e he f u hE
  have hrel' : (Modules.pullback h).map aY ≫ eT.hom =
      eS.hom ≫ aX := by
    exact hrel
  have hy :=
    reconstructedTwistedRelation_comp_twist_reconstructedQuotientMap'_eq_zero
      n Y l r d e he u hambientY
  have hy' : aY ≫ tY = 0 := by
    simpa only [aY, tY, pY, OdY] using hy
  have hmap := congrArg (Modules.pullback h).map hy'
  simp only [Functor.map_zero] at hmap
  have hmap' : (Modules.pullback h).map aY ≫
      (Modules.pullback h).map tY = 0 := by
    exact (Functor.map_comp (Modules.pullback h) aY tY).symm.trans hmap
  have hz : (Modules.pullback h).map aY ≫ eT.hom ≫ tX = 0 := by
    have hpre := congrArg
      (fun k ↦ (Modules.pullback h).map aY ≫ k) hp.symm
    have hassoc : (Modules.pullback h).map aY ≫
          ((Modules.pullback h).map tY ≫ eQ.hom) =
        ((Modules.pullback h).map aY ≫
          (Modules.pullback h).map tY) ≫ eQ.hom := rfl
    have hzero := (congrArg (fun k ↦ k ≫ eQ.hom) hmap').trans zero_comp
    exact hpre.trans (hassoc.trans hzero)
  apply (cancel_epi eS.hom).1
  have hpre := congrArg (fun k ↦ k ≫ tX) hrel'.symm
  have hassoc : eS.hom ≫ (aX ≫ tX) =
      (eS.hom ≫ aX) ≫ tX := rfl
  exact hassoc.trans (hpre.trans (hz.trans comp_zero.symm))

/-- The pulled reconstructed quotient's degree-`d` Grassmannian map descends through
the normalized pullback of the original finite-free quotient. -/
lemma kernel_ι_comp_quotGrassmannianFreeMap_reconstructedPullback_eq_zero
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
              projectiveSpaceOverTwist n Y (-l)) d).hom) :
    let uX := pullbackFreeQuotientMap f u
    let pY := reconstructedQuotientMap' n Y l r d e he u
    let QX := (Modules.pullback (projectiveSpaceOverMap n f)).obj
      (reconstructedQuotient' n Y l r d e he u)
    let pX : (∐ fun _ : ULift.{u} (Fin r) ↦
        projectiveSpaceOverTwist n X (-l)) ⟶ QX :=
      (projectiveSpaceOverTwistedFree_pullbackIso n r l f).inv ≫
        (Modules.pullback (projectiveSpaceOverMap n f)).map pY
    let M : X.Modules := (Modules.pushforward (projectiveSpaceOverπ n X)).obj
      (projectiveSpaceOverTwistModule QX (d : ℤ))
    let v : SheafOfModules.free (R := X.ringCatSheaf)
        (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ M :=
      quotGrassmannianFreeMap n X l r pX d e he
    kernel.ι uX ≫ v =
      @Zero.zero (kernel uX ⟶ M)
        (Limits.HasZeroMorphisms.zero (C := X.Modules) (kernel uX) M) := by
  dsimp only
  apply kernel_ι_comp_quotGrassmannianFreeMap_eq_zero_of_twistedRelation
  exact reconstructedPullbackRelation_comp_twistQuotientMap_eq_zero
    n l r d e he f u hE hambientY

set_option maxHeartbeats 400000 in
-- The dependent normalization and representative-transport pasting is elaboration-heavy.
/-- The universal quotient reconstructed from a Grassmannian point has the same strict
degree-`d` finite-free quotient as the pullback of that Grassmannian point.

The rank and epimorphism inputs are taken directly from the intrinsic natural-
transformation datum.  The proof denormalizes the universal projective family, descends
its monomial map through the pulled finite-free quotient, and transports the result back
through the chosen representative of the universal Quot point. -/
noncomputable def grassmannianPointUniversalFreeQuotientComparisonOfAmbient
    {S : Scheme.{u}} {n r m q : ℕ} {l : ℤ} {P : Polynomial ℚ}
    {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)}
    {σ : ULift.{u} (Fin m) ≃
      ULift.{u} (Fin r) × Fin ((n + e).choose n)}
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ)
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m)
    (h : Modules.ProjectiveFlatteningHasFiniteRankPresentation n
      (grassmannianPointReconstructedQuotient
        (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
          (he := he) (σ := σ) T g) (P := P))
    (hambient : TwistedFreeAmbientReconstructionCompatibility
      n T.left l r d e he) :
    GrassmannianPointUniversalFreeQuotientComparison D T g h := by
  let Q := grassmannianPointReconstructedQuotient
    (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
      (he := he) (σ := σ) T g
  let Z := Modules.projectiveFlatteningRepresentative n Q (P := P) h
  let E := Modules.projectiveFlatteningRepresentableBy n Q (P := P) h
  let hz := E.homEquiv (𝟙 Z)
  let QZ := Modules.projectiveFamilyAt n Q Z
  let pZ : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n Z.left (-l)) ⟶ QZ :=
    (projectiveSpaceOverTwistedFree_pullbackIso n r l Z.hom).inv ≫
      (Modules.pullback (projectiveSpaceOverMap n Z.hom)).map
        (grassmannianPointReconstructedQuotientMap
          (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
            (he := he) (σ := σ) T g)
  let b := Modules.QuotientPullbackData.ofTwistedFreeQuotientOnProjectiveSpace
    (n := n) (r := r) (l := l) ((Over.map T.hom).obj Z) QZ
      (by infer_instance) hz.down.down.1 pZ
  let x := grassmannianPointFlatteningUniversalQuotPoint
    (n := n) (r := r) (m := m) (q := q) (l := l) (P := P)
      (d := d) (e := e) (he := he) (σ := σ) T g h
  have hxb : Quotient.mk _ b = x.1 := by
    rfl
  let a := TwistedFreeQuotGrassmannianNatTransData.representative x
  have hab : (Modules.QuotientPullbackData.setoid
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) ((Over.map T.hom).obj Z)).r a b := by
    apply Quotient.exact
    exact (TwistedFreeQuotGrassmannianNatTransData.representative_mk x).trans hxb.symm
  let hPb :=
    Modules.QuotientPullbackData.ofTwistedFreeQuotientOnProjectiveSpace_hasFiberwiseHilbertPolynomial
      ((Over.map T.hom).obj Z) QZ (by infer_instance) hz.down.down.1 pZ P
        hz.down.down.2
  let hMb := D.isProjectiveOfRank ((Over.map T.hom).obj Z) b hPb
  let hsb := D.surjective ((Over.map T.hom).obj Z) b hPb
  let qB := twistedFreeQuotGrassmannianFreeQuotient
    n S l r b d e he σ hMb hsb
  let q₂ := grassmannianPointFreeQuotientPullbackToFlattening
    (n := n) (r := r) (q := q) (l := l) (P := P)
      (d := d) (e := e) (he := he) (σ := σ) T g h
  letI : (grassmannianPointFreeQuotient (q := q) T g).Q.IsQuasicoherent :=
    (grassmannianPointFreeQuotient (q := q) T g).isQuasicoherent
  let u := grassmannianPointMonomialQuotientMap
    (n := n) (r := r) (q := q) (e := e) (σ := σ) T g
  letI : Epi u := by
    letI : IsIso (SheafOfModules.freeMap
        (R := T.left.ringCatSheaf) σ.symm) :=
      Modules.freeMap_isIso_of_equiv σ.symm
    letI : Epi (grassmannianPointFreeQuotient (q := q) T g).π :=
      (grassmannianPointFreeQuotient (q := q) T g).epi
    dsimp only [u, grassmannianPointMonomialQuotientMap]
    infer_instance
  let uZ := pullbackFreeQuotientMap Z.hom u
  let vZ := quotGrassmannianFreeMap n Z.left l r pZ d e he
  let MZ : Z.left.Modules :=
    (Modules.pushforward (projectiveSpaceOverπ n Z.left)).obj
      (projectiveSpaceOverTwistModule QZ (d : ℤ))
  let Eβ :=
    (Modules.pushforward (projectiveSpaceOverπ n Z.left)).mapIso
      (Modules.tensorLeftIso
        (Modules.QuotientPullbackData.ofTwistedFreeQuotientOnProjectiveSpace_quotDataIso
          (n := n) (r := r) (l := l) ((Over.map T.hom).obj Z)
            QZ (by infer_instance) hz.down.down.1 pZ)
        (projectiveSpaceOverTwist n Z.left (d : ℤ)))
  letI : q₂.Q.IsQuasicoherent := q₂.isQuasicoherent
  letI : qB.Q.IsQuasicoherent := qB.isQuasicoherent
  letI : MZ.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent Z.left.ringCatSheaf).prop_of_iso
      Eβ qB.isQuasicoherent
  have hu : uZ = SheafOfModules.freeMap
        (R := Z.left.ringCatSheaf) σ.symm ≫ q₂.π := by
    dsimp only [uZ, u, q₂, grassmannianPointFreeQuotientPullbackToFlattening,
      Modules.FreeQuotient.pullback, grassmannianPointMonomialQuotientMap]
    exact pullbackFreeQuotientMap_freeMap Z.hom σ.symm
      (grassmannianPointFreeQuotient (q := q) T g).π
  have hv : SheafOfModules.freeMap
        (R := Z.left.ringCatSheaf) σ.symm ≫ qB.π ≫ Eβ.hom = vZ := by
    exact denormalized_twistedFreeQuotGrassmannianFreeMap_reindex
      n l r ((Over.map T.hom).obj Z) QZ (by infer_instance)
        hz.down.down.1 pZ d e he σ
  letI : Epi uZ := by
    rw [hu]
    letI : IsIso (SheafOfModules.freeMap
        (R := Z.left.ringCatSheaf) σ.symm) :=
      Modules.freeMap_isIso_of_equiv σ.symm
    letI : Epi q₂.π := q₂.epi
    infer_instance
  letI : Epi vZ := by
    rw [← hv]
    letI : IsIso (SheafOfModules.freeMap
        (R := Z.left.ringCatSheaf) σ.symm) :=
      Modules.freeMap_isIso_of_equiv σ.symm
    letI : Epi qB.π := qB.epi
    infer_instance
  have hzero : kernel.ι uZ ≫ vZ =
      @Zero.zero (kernel uZ ⟶ MZ)
        (Limits.HasZeroMorphisms.zero (C := Z.left.Modules) (kernel uZ) MZ) := by
    exact kernel_ι_comp_quotGrassmannianFreeMap_reconstructedPullback_eq_zero
      n l r d e he Z.hom u
        (grassmannianPointFreeQuotient
          (q := q) T g).isProjectiveOfRank.isFiniteLocallyFree
        hambient
  have huRank : Modules.IsProjectiveOfRank q
      ((Modules.pullback Z.hom).obj
        (grassmannianPointFreeQuotient (q := q) T g).Q) := by
    exact q₂.isProjectiveOfRank
  have hvRank : Modules.IsProjectiveOfRank q MZ := by
    exact hMb.of_iso Eβ
  let C := Modules.freeQuotientTargetIsoOfKernelVanishing
    uZ vZ hzero huRank hvRank
  have hC : uZ ≫ C.hom = vZ :=
    Modules.freeQuotientTargetIsoOfKernelVanishing_comp
      uZ vZ hzero huRank hvRank
  have hq₂B : q₂.π ≫ C.hom = qB.π ≫ Eβ.hom := by
    let w := SheafOfModules.freeMap (R := Z.left.ringCatSheaf) σ.symm
    letI : IsIso w := Modules.freeMap_isIso_of_equiv σ.symm
    apply (cancel_epi w).1
    calc
      w ≫ (q₂.π ≫ C.hom) = uZ ≫ C.hom := by rw [hu]; rfl
      _ = vZ := hC
      _ = w ≫ (qB.π ≫ Eβ.hom) := by rw [hv]
  let EB₂ : qB.Q ≅ q₂.Q := Eβ ≪≫ C.symm
  have hEB₂ : qB.π ≫ EB₂.hom = q₂.π := by
    dsimp only [EB₂, Iso.trans_hom, Iso.symm_hom]
    rw [← Category.assoc, ← hq₂B]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let hPa :=
    TwistedFreeQuotGrassmannianNatTransData.representative_hasFiberwiseHilbertPolynomial x
  let q₁ := grassmannianPointFlatteningUniversalFreeQuotient D T g h
  have hr : (Modules.FreeQuotient.setoid q (ULift.{u} (Fin m)) Z.left).r
      q₁ qB := by
    exact twistedFreeQuotGrassmannianFreeQuotient_r_of_r
      n S l r hab d e he σ
        (D.isProjectiveOfRank ((Over.map T.hom).obj Z) a hPa)
        (D.surjective ((Over.map T.hom).obj Z) a hPa)
        hMb hsb
  let EaB : q₁.Q ≅ qB.Q := Classical.choose hr
  have hEaB : q₁.π ≫ EaB.hom = qB.π := Classical.choose_spec hr
  exact {
    targetIso := EaB ≪≫ EB₂
    π_comp := by
      dsimp only [q₁, q₂, Iso.trans_hom]
      rw [← Category.assoc, hEaB, hEB₂]
  }

/-- Ambient reconstruction coherence supplies the universal strict quotient
comparison required by the projective-flattening fibre package. -/
theorem grassmannianPointUniversalFreeQuotientComparison_nonempty_of_ambient
    {S : Scheme.{u}} {n r m q : ℕ} {l : ℤ} {P : Polynomial ℚ}
    {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)}
    {σ : ULift.{u} (Fin m) ≃
      ULift.{u} (Fin r) × Fin ((n + e).choose n)}
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ)
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m)
    (h : Modules.ProjectiveFlatteningHasFiniteRankPresentation n
      (grassmannianPointReconstructedQuotient
        (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
          (he := he) (σ := σ) T g) (P := P))
    (hambient : TwistedFreeAmbientReconstructionCompatibility
      n T.left l r d e he) :
    Nonempty (GrassmannianPointUniversalFreeQuotientComparison D T g h) :=
  ⟨grassmannianPointUniversalFreeQuotientComparisonOfAmbient
    D T g h hambient⟩

end AlgebraicGeometry.Scheme

end

end
