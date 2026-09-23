module

public import StacksAndModuli.API.ProjectiveSpaceTwistCancellation
public import StacksAndModuli.API.ProjectiveSpaceTwistExact
public import StacksAndModuli.API.ProjHomogeneousSectionMulHom
public import StacksAndModuli.API.PullbackPushforwardEvaluationEpi
public import StacksAndModuli.API.QuasicoherentFiniteCoproduct
public import StacksAndModuli.API.QuotGrassmannianReconstruction
public import StacksAndModuli.API.SchemeModulesTensorRightExact
public import StacksAndModuli.API.TwistedFreeAmbientPushforwardRank
public import StacksAndModuli.API.TwistedFreeMonomialIndexEquiv
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianNatTrans

/-!
# Reflection for the twisted-free Quot-to-Grassmannian map

This file specializes the generic reconstruction comparison to the actual free
Grassmannian map attached to a twisted-free quotient.  There are two geometric inputs:
the untwisted monomial relation must vanish after the quotient map, and its canonical
lift to the quotient kernel must generate that kernel.  The latter is stated on affine
opens, where it directly implies that the lift is an epimorphism.

The resulting `ReconstructedRelationPresentsKernel` gives the canonical isomorphism from
`reconstructedQuotient'` to the original quotient and the commuting triangle with the
twisted-free ambient map.
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

/-- Reindexing a free sheaf before mapping out of it reindexes the defining family of
global sections. -/
lemma Modules.freeMap_comp_freeHomOfSections
    {X : Scheme.{u}} {I J : Type u} {M : X.Modules}
    (f : I → J) (s : J → Γ(M, ⊤)) :
    SheafOfModules.freeMap (R := X.ringCatSheaf) f ≫
        Modules.freeHomOfSections s =
      Modules.freeHomOfSections (fun i ↦ s (f i)) := by
  apply (SheafOfModules.freeHomEquiv M).injective
  funext i
  rw [SheafOfModules.freeHomEquiv_comp_apply,
    SheafOfModules.freeHomEquiv_freeMap]
  simp only [Modules.freeHomOfSections, Equiv.apply_symm_apply]
  change SheafOfModules.sectionsMap
      ((SheafOfModules.freeHomEquiv M).symm
        (fun j ↦ (Modules.sectionsTopEquiv M).symm (s j)))
      (SheafOfModules.freeSection (f i)) =
    (Modules.sectionsTopEquiv M).symm (s (f i))
  exact SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
    (M := M) (fun j ↦ (Modules.sectionsTopEquiv M).symm (s j)) (f i)

/-- A coproduct injection followed by the morphism defined by a family of global
sections is the morphism represented by the corresponding section. -/
lemma Modules.ιFree_comp_freeHomOfSections
    {X : Scheme.{u}} {I : Type u} {M : X.Modules}
    (s : I → Γ(M, ⊤)) (i : I) :
    SheafOfModules.ιFree i ≫ Modules.freeHomOfSections s =
      M.unitHomEquiv.symm ((Modules.sectionsTopEquiv M).symm (s i)) := by
  have h := (SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply
    (Modules.freeHomOfSections s) i).symm
  simpa only [Modules.freeHomOfSections, Equiv.apply_symm_apply] using h

/-- Naturality of the morphism represented by a global section, stated using
`sectionsTopEquiv`. -/
@[reassoc]
lemma Modules.unitHomOfSection_comp
    {X : Scheme.{u}} {M N : X.Modules} (s : Γ(M, ⊤)) (f : M ⟶ N) :
    M.unitHomEquiv.symm ((Modules.sectionsTopEquiv M).symm s) ≫ f =
      N.unitHomEquiv.symm
        ((Modules.sectionsTopEquiv N).symm (Modules.Hom.app f ⊤ s)) := by
  exact (SheafOfModules.unitHomEquiv_symm_comp
    ((Modules.sectionsTopEquiv M).symm s) f).trans
      (congrArg N.unitHomEquiv.symm
        (Modules.sectionsMap_sectionsTopEquiv_symm f s))

/-- A free-sheaf reindexing along an equivalence is an isomorphism. -/
theorem Modules.freeMap_isIso_of_equiv
    {X : Scheme.{u}} {I J : Type u} (e : I ≃ J) :
    IsIso (SheafOfModules.freeMap (R := X.ringCatSheaf) e) := by
  refine ⟨⟨SheafOfModules.freeMap (R := X.ringCatSheaf) e.symm, ?_, ?_⟩⟩
  · apply Cofan.IsColimit.hom_ext
      (SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf) I)
    intro i
    change (SheafOfModules.ιFree (R := X.ringCatSheaf) i ≫
        SheafOfModules.freeMap e) ≫ SheafOfModules.freeMap e.symm =
      SheafOfModules.ιFree i ≫ 𝟙 _
    rw [SheafOfModules.ιFree_freeMap,
      SheafOfModules.ιFree_freeMap, Equiv.symm_apply_apply,
      Category.comp_id]
  · apply Cofan.IsColimit.hom_ext
      (SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf) J)
    intro j
    change (SheafOfModules.ιFree (R := X.ringCatSheaf) j ≫
        SheafOfModules.freeMap e.symm) ≫ SheafOfModules.freeMap e =
      SheafOfModules.ιFree j ≫ 𝟙 _
    rw [SheafOfModules.ιFree_freeMap,
      SheafOfModules.ιFree_freeMap, Equiv.apply_symm_apply,
      Category.comp_id]

/-- The fixed-degree monomial map for the twisted-free ambient sheaf, viewed on
the base through projective pushforward. -/
noncomputable def twistedFreeMonomialPushforwardMap
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) :
    SheafOfModules.free (R := T.ringCatSheaf)
        (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶
      (Modules.pushforward (projectiveSpaceOverπ n T)).obj
        (projectiveSpaceOverTwistModule
          (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l))
          (d : ℤ)) :=
  Modules.freeHomOfSections
    (fun x : ULift.{u} (Fin r) × Fin ((n + e).choose n) ↦
      twistedFreeMonomialSection n T l r d e he x.1 x.2)

/-- The product-indexed ambient monomial pushforward is an epimorphism.  This is the
affine-open monomial spanning theorem, transported through the canonical finite
reindexing. -/
theorem twistedFreeMonomialPushforwardMap_epi
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) :
    Epi (twistedFreeMonomialPushforwardMap n T l r d e he) := by
  let m := r * (n + e).choose n
  let σ : ULift.{u} (Fin m) ≃
      ULift.{u} (Fin r) × Fin ((n + e).choose n) :=
    twistedFreeMonomialIndexEquiv r ((n + e).choose n)
  let A := twistedFreeMonomialPushforwardMap n T l r d e he
  let B : SheafOfModules.free (R := T.ringCatSheaf) (ULift.{u} (Fin m)) ⟶
      (Modules.pushforward (projectiveSpaceOverπ n T)).obj
        (projectiveSpaceOverTwistModule
          (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l))
          (d : ℤ)) :=
    Modules.freeHomOfSections
      (fun k ↦ twistedFreeMonomialSection n T l r d e he (σ k).1 (σ k).2)
  have hsurj : ∀ U : T.affineOpens,
      Function.Surjective (Modules.finFreeSectionsMap' B U.1) := by
    intro U
    exact ProjectiveSpace.surjective_finFreeSectionsMap'_twistedFreeMonomial
      n l r d e he σ U
  have happ : ∀ U : T.affineOpens,
      Function.Surjective (Modules.Hom.app B U.1) :=
    Modules.hom_app_surjective_of_finFreeSectionsMap'_surjective B hsurj
  haveI : Epi B := Modules.epi_of_surjective_on_affineOpens B happ
  let f := SheafOfModules.freeMap (R := T.ringCatSheaf) σ
  haveI : IsIso f := by
    dsimp only [f]
    exact Modules.freeMap_isIso_of_equiv σ
  have hcomp : f ≫ A = B := by
    simpa only [f, A, B, twistedFreeMonomialPushforwardMap,
      Function.comp_apply] using
      Modules.freeMap_comp_freeHomOfSections
        (X := T)
        (M := (Modules.pushforward (projectiveSpaceOverπ n T)).obj
          (projectiveSpaceOverTwistModule
            (∐ fun _ : ULift.{u} (Fin r) ↦
              projectiveSpaceOverTwist n T (-l)) (d : ℤ))) σ
        (fun x : ULift.{u} (Fin r) × Fin ((n + e).choose n) ↦
          (show Γ((Modules.pushforward (projectiveSpaceOverπ n T)).obj
              (projectiveSpaceOverTwistModule
                (∐ fun _ : ULift.{u} (Fin r) ↦
                  projectiveSpaceOverTwist n T (-l)) (d : ℤ)), ⊤) from
            twistedFreeMonomialSection n T l r d e he x.1 x.2))
  exact epi_of_epi_fac hcomp

/-- The fixed-degree monomial map identifies the finite free monomial sheaf with the
pushforward of the twisted-free ambient sheaf. -/
instance twistedFreeMonomialPushforwardMap_isIso
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) :
    IsIso (twistedFreeMonomialPushforwardMap n T l r d e he) := by
  let m := r * (n + e).choose n
  let σ : ULift.{u} (Fin m) ≃
      ULift.{u} (Fin r) × Fin ((n + e).choose n) :=
    twistedFreeMonomialIndexEquiv r ((n + e).choose n)
  let A := twistedFreeMonomialPushforwardMap n T l r d e he
  let B : SheafOfModules.free (R := T.ringCatSheaf) (ULift.{u} (Fin m)) ⟶
      (Modules.pushforward (projectiveSpaceOverπ n T)).obj
        (projectiveSpaceOverTwistModule
          (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l))
          (d : ℤ)) :=
    Modules.freeHomOfSections
      (fun k ↦ twistedFreeMonomialSection n T l r d e he (σ k).1 (σ k).2)
  let f := SheafOfModules.freeMap (R := T.ringCatSheaf) σ
  haveI : IsIso f := by
    dsimp only [f]
    exact Modules.freeMap_isIso_of_equiv σ
  have hcomp : f ≫ A = B := by
    simpa only [f, A, B, twistedFreeMonomialPushforwardMap,
      Function.comp_apply] using
      Modules.freeMap_comp_freeHomOfSections
        (X := T)
        (M := (Modules.pushforward (projectiveSpaceOverπ n T)).obj
          (projectiveSpaceOverTwistModule
            (∐ fun _ : ULift.{u} (Fin r) ↦
              projectiveSpaceOverTwist n T (-l)) (d : ℤ))) σ
        (fun x : ULift.{u} (Fin r) × Fin ((n + e).choose n) ↦
          (show Γ((Modules.pushforward (projectiveSpaceOverπ n T)).obj
              (projectiveSpaceOverTwistModule
                (∐ fun _ : ULift.{u} (Fin r) ↦
                  projectiveSpaceOverTwist n T (-l)) (d : ℤ)), ⊤) from
            twistedFreeMonomialSection n T l r d e he x.1 x.2))
  haveI : Epi A := twistedFreeMonomialPushforwardMap_epi n T l r d e he
  haveI : Epi B := hcomp ▸ epi_comp f A
  let F := ∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)
  let Fd := projectiveSpaceOverTwistModule F (d : ℤ)
  letI : F.IsQuasicoherent := by
    dsimp only [F]
    exact Modules.isQuasicoherent_coproduct _
  letI : Fd.IsQuasicoherent := by dsimp only [Fd]; infer_instance
  letI : ((Modules.pushforward (projectiveSpaceOverπ n T)).obj
      (projectiveSpaceOverTwistModule
        (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l))
        (d : ℤ))).IsQuasicoherent := by
    change ((Modules.pushforward (projectiveSpaceOverπ n T)).obj Fd).IsQuasicoherent
    infer_instance
  have hsource := Modules.free_isProjectiveOfRank T m
  have htarget := twistedFreeTwistPushforward_isProjectiveOfRank
    n T l r d e he
  haveI : IsIso B := Modules.isIso_of_epi_of_isProjectiveOfRank
    hsource htarget B
  exact IsIso.of_isIso_fac_left hcomp

/-- The sheaf-level monomial map is the adjoint of the corresponding fixed-degree
map on the base. -/
lemma twistedFreeMonomialPushforwardMap_adjunct
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) :
    (Modules.pullbackPushforwardAdjunction
      (projectiveSpaceOverπ n T)).homEquiv _ _
        ((Modules.pullbackFreeIso (projectiveSpaceOverπ n T)
          (ULift.{u} (Fin r) × Fin ((n + e).choose n))).hom ≫
            twistedFreeMonomialMap n T l r d e he) =
      twistedFreeMonomialPushforwardMap n T l r d e he := by
  let π := projectiveSpaceOverπ n T
  let F := ∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)
  let Fd := projectiveSpaceOverTwistModule F (d : ℤ)
  let s := fun x : ULift.{u} (Fin r) × Fin ((n + e).choose n) ↦
    twistedFreeMonomialSection n T l r d e he x.1 x.2
  let ε := (Modules.pullbackPushforwardAdjunction π).counit.app Fd
  let w := Modules.pullbackFreeIso π
    (ULift.{u} (Fin r) × Fin ((n + e).choose n))
  have hfree : w.inv ≫
        (Modules.pullback π).map (Modules.freeHomOfSections s) ≫ ε =
      Modules.freeHomOfSections s := by
    apply Modules.pullback_freeHomOfSections_comp_of_sections
    intro x
    exact Modules.counit_app_top_pullbackGlobalSections π Fd (s x)
  apply ((Modules.pullbackPushforwardAdjunction π).homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  change w.hom ≫ Modules.freeHomOfSections s =
    (Modules.pullback π).map (Modules.freeHomOfSections s) ≫ ε
  apply (cancel_epi w.inv).1
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hfree.symm

/-- The morphism from the structure sheaf represented by one monomial section in
`𝒪(-l)(d)`.  This isolates the one-summand input in the comparison between the
multiplication and tensor-cancellation models. -/
noncomputable def twistMonomialTwistedSectionHom
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ))
    (i : Fin ((n + e).choose n)) :
    SheafOfModules.unit (projectiveSpaceOver n T).ringCatSheaf ⟶
      projectiveSpaceOverTwistModule
        (projectiveSpaceOverTwist n T (-l)) (d : ℤ) :=
  let L := projectiveSpaceOverTwist n T (-l)
  let Ld := projectiveSpaceOverTwistModule L (d : ℤ)
  let s : Γ(Ld, ⊤) := Modules.Hom.app
    (projectiveSpaceOverTwist_addIso_nat n T (-l) d).inv ⊤
    (Modules.Hom.app
      (eqToHom (congrArg
        (fun c : ℤ ↦ projectiveSpaceOverTwist n T c)
        (neg_add_eq_sub l (d : ℤ)).symm)) ⊤
      (he ▸ twistMonomialSection n T e i))
  Ld.unitHomEquiv.symm ((Modules.sectionsTopEquiv Ld).symm s)

/-- A summand of the inverse free-tensor comparison is the inverse left unitor
followed by tensoring the corresponding free-sheaf injection. -/
@[reassoc]
lemma ι_freeTensorTwistIso_inv
    (n : ℕ) (T : Scheme.{u}) (I : Type u) (a : ℤ) (i : I) :
    Limits.Sigma.ι (fun _ : I ↦ projectiveSpaceOverTwist n T a) i ≫
        (freeTensorTwistIso n T I a).inv =
      (Modules.tensorLeftUnitIso (projectiveSpaceOverTwist n T a)).inv ≫
        Modules.tensorMapLeft
          (SheafOfModules.ιFree
            (R := (projectiveSpaceOver n T).ringCatSheaf) i)
          (projectiveSpaceOverTwist n T a) := by
  let D := projectiveSpaceOverTwist n T a
  change Limits.Sigma.ι (fun _ : I ↦ D) i ≫
      (Limits.Sigma.mapIso (fun _ : I ↦
        Modules.tensorLeftUnitIso D)).inv ≫
      (Modules.tensorCoproductIso
        (fun _ : I ↦ SheafOfModules.unit
          (projectiveSpaceOver n T).ringCatSheaf) D).inv = _
  rw [Limits.Sigma.ι_mapIso_inv_assoc]
  exact congrArg (fun k ↦ (Modules.tensorLeftUnitIso D).inv ≫ k)
    (Modules.ι_tensorCoproductIso_inv
      (fun _ : I ↦ SheafOfModules.unit
        (projectiveSpaceOver n T).ringCatSheaf) D i)

set_option maxHeartbeats 1200000 in
-- Expanding the tensor-coproduct identifications creates nested sheafification terms.
/-- The ambient multiplication/cancellation comparison reduces to its single-monomial,
single-summand form.  All coproduct, free-sheaf, and cancellation naturality coherence is
discharged here. -/
lemma twistedFreeMonomialHom_eq_tensorMapLeft_cancel_of_single
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    (hsingle : ∀ i : Fin ((n + e).choose n),
      twistMonomialMulHom n T (-(d : ℤ)) (-l) e (by omega) i =
        (Modules.tensorLeftUnitIso
          (projectiveSpaceOverTwist n T (-(d : ℤ)))).inv ≫
          Modules.tensorMapLeft
            (twistMonomialTwistedSectionHom n T l d e he i)
            (projectiveSpaceOverTwist n T (-(d : ℤ))) ≫
          (projectiveSpaceOverTwistModule_cancelIso_nat n T
            (projectiveSpaceOverTwist n T (-l)) d).hom) :
    (freeTensorTwistIso n T
          (ULift.{u} (Fin r) × Fin ((n + e).choose n)) (-(d : ℤ))).hom ≫
        twistedFreeMonomialHom n T l r d e he =
      Modules.tensorMapLeft
          (twistedFreeMonomialMap n T l r d e he)
          (projectiveSpaceOverTwist n T (-(d : ℤ))) ≫
        (projectiveSpaceOverTwistModule_cancelIso_nat n T
          (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) d).hom := by
  let I := ULift.{u} (Fin r) × Fin ((n + e).choose n)
  let Dm := projectiveSpaceOverTwist n T (-(d : ℤ))
  let F := ∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)
  let A := freeTensorTwistIso n T I (-(d : ℤ))
  apply (cancel_epi A.inv).1
  apply Limits.Sigma.hom_ext
  intro x
  change Limits.Sigma.ι (fun _ : I ↦ Dm) x ≫ A.inv ≫ A.hom ≫
      twistedFreeMonomialHom n T l r d e he = _
  simp only [Iso.inv_hom_id_assoc]
  rw [ι_freeTensorTwistIso_inv_assoc]
  rw [twistedFreeMonomialHom, Limits.Sigma.ι_desc]
  change twistMonomialMulHom n T (-(d : ℤ)) (-l) e _ x.2 ≫
      Limits.Sigma.ι (fun _ : ULift.{u} (Fin r) ↦
        projectiveSpaceOverTwist n T (-l)) x.1 = _
  slice_rhs 2 3 =>
    exact (Modules.tensorMapLeft_comp
      (SheafOfModules.ιFree (R := (projectiveSpaceOver n T).ringCatSheaf) x)
      (twistedFreeMonomialMap n T l r d e he) Dm).symm
  let Od := projectiveSpaceOverTwist n T (d : ℤ)
  let L := projectiveSpaceOverTwist n T (-l)
  let Fd := projectiveSpaceOverTwistModule F (d : ℤ)
  let Ld := projectiveSpaceOverTwistModule L (d : ℤ)
  let ι := Modules.tensorMapLeft
    (Limits.Sigma.ι (fun _ : ULift.{u} (Fin r) ↦ L) x.1) Od
  let core : Γ(Ld, ⊤) := Modules.Hom.app
    (projectiveSpaceOverTwist_addIso_nat n T (-l) d).inv ⊤
    (Modules.Hom.app
      (eqToHom (congrArg
        (fun c : ℤ ↦ projectiveSpaceOverTwist n T c)
        (neg_add_eq_sub l (d : ℤ)).symm)) ⊤
      (he ▸ twistMonomialSection n T e x.2))
  have hx := Modules.ιFree_comp_freeHomOfSections
    (fun y : I ↦ twistedFreeMonomialSection n T l r d e he y.1 y.2) x
  have hx' : SheafOfModules.ιFree x ≫
      twistedFreeMonomialMap n T l r d e he =
      Fd.unitHomEquiv.symm
        ((Modules.sectionsTopEquiv Fd).symm
          (twistedFreeMonomialSection n T l r d e he x.1 x.2)) := by
    simpa only [twistedFreeMonomialMap] using hx
  have hdec := twistedFreeMonomialSection_eq_summand
    n T l r d e he x.1 x.2
  have hdecHom : Fd.unitHomEquiv.symm
        ((Modules.sectionsTopEquiv Fd).symm
          (twistedFreeMonomialSection n T l r d e he x.1 x.2)) =
      Fd.unitHomEquiv.symm
        ((Modules.sectionsTopEquiv Fd).symm (Modules.Hom.app ι ⊤ core)) :=
    congrArg (fun s ↦ Fd.unitHomEquiv.symm
      ((Modules.sectionsTopEquiv Fd).symm s)) hdec
  have hsectionNat : Fd.unitHomEquiv.symm
        ((Modules.sectionsTopEquiv Fd).symm (Modules.Hom.app ι ⊤ core)) =
      Ld.unitHomEquiv.symm ((Modules.sectionsTopEquiv Ld).symm core) ≫ ι := by
    exact (Modules.unitHomOfSection_comp core ι).symm
  have hhom : SheafOfModules.ιFree x ≫
      twistedFreeMonomialMap n T l r d e he =
      Ld.unitHomEquiv.symm ((Modules.sectionsTopEquiv Ld).symm core) ≫ ι :=
    hx'.trans (hdecHom.trans hsectionNat)
  have hs : twistMonomialTwistedSectionHom n T l d e he x.2 =
      Ld.unitHomEquiv.symm ((Modules.sectionsTopEquiv Ld).symm core) := rfl
  rw [hsingle x.2, hs]
  calc
    (Modules.tensorLeftUnitIso Dm).inv ≫
          Modules.tensorMapLeft
            (Ld.unitHomEquiv.symm ((Modules.sectionsTopEquiv Ld).symm core)) Dm ≫
          (projectiveSpaceOverTwistModule_cancelIso_nat n T L d).hom ≫
          Limits.Sigma.ι (fun _ : ULift.{u} (Fin r) ↦ L) x.1 =
        (Modules.tensorLeftUnitIso Dm).inv ≫
          Modules.tensorMapLeft
            (Ld.unitHomEquiv.symm ((Modules.sectionsTopEquiv Ld).symm core)) Dm ≫
          Modules.tensorMapLeft ι Dm ≫
          (projectiveSpaceOverTwistModule_cancelIso_nat n T F d).hom := by
      exact congrArg
        (fun k ↦ (Modules.tensorLeftUnitIso Dm).inv ≫
          Modules.tensorMapLeft
            (Ld.unitHomEquiv.symm ((Modules.sectionsTopEquiv Ld).symm core)) Dm ≫ k)
        (projectiveSpaceOverTwistModule_cancelIso_nat_hom_naturality
          n T (Limits.Sigma.ι
            (fun _ : ULift.{u} (Fin r) ↦ L) x.1) d).symm
    _ = (Modules.tensorLeftUnitIso Dm).inv ≫
          Modules.tensorMapLeft
            (Ld.unitHomEquiv.symm ((Modules.sectionsTopEquiv Ld).symm core) ≫ ι) Dm ≫
          (projectiveSpaceOverTwistModule_cancelIso_nat n T F d).hom := by
      rw [Modules.tensorMapLeft_comp]
      simp only [Category.assoc]
    _ = (Modules.tensorLeftUnitIso Dm).inv ≫
          Modules.tensorMapLeft
            (SheafOfModules.ιFree x ≫
              twistedFreeMonomialMap n T l r d e he) Dm ≫
          (projectiveSpaceOverTwistModule_cancelIso_nat n T F d).hom :=
      congrArg
        (fun k ↦ (Modules.tensorLeftUnitIso Dm).inv ≫
          Modules.tensorMapLeft k Dm ≫
            (projectiveSpaceOverTwistModule_cancelIso_nat n T F d).hom)
        hhom.symm

/-- The tensor/coproduct identification occurring immediately before the untwisted
monomial map in the reconstruction relation. -/
noncomputable def quotGrassmannianUntwistedAmbientIso
    (n : ℕ) (T : Scheme.{u}) (r : ℕ) (d e : ℕ) :
    Modules.tensor
        ((Modules.pullback (projectiveSpaceOverπ n T)).obj
          (SheafOfModules.free (R := T.ringCatSheaf)
            (ULift.{u} (Fin r) × Fin ((n + e).choose n))))
        (projectiveSpaceOverTwist n T (-(d : ℤ))) ≅
      ∐ fun _ : ULift.{u} (Fin r) × Fin ((n + e).choose n) ↦
        projectiveSpaceOverTwist n T (-(d : ℤ)) :=
  Modules.tensorLeftIso
      (Modules.pullbackFreeIso (projectiveSpaceOverπ n T)
        (ULift.{u} (Fin r) × Fin ((n + e).choose n)))
      (projectiveSpaceOverTwist n T (-(d : ℤ))) ≪≫
    freeTensorTwistIso n T
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) (-(d : ℤ))

/-- Pulling the fixed-degree monomial map to projective space and applying the adjunction
counit is the free map of the original quotient-monomial sections, after the canonical
free-sheaf comparison. -/
lemma pullback_quotGrassmannianFreeMap_comp_counit
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ)
    {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) :
    (Modules.pullback (projectiveSpaceOverπ n T)).map
          (quotGrassmannianFreeMap n T l r p d e he) ≫
        (Modules.pullbackPushforwardAdjunction
          (projectiveSpaceOverπ n T)).counit.app
            (projectiveSpaceOverTwistModule Q (d : ℤ)) =
      (Modules.pullbackFreeIso (projectiveSpaceOverπ n T)
        (ULift.{u} (Fin r) × Fin ((n + e).choose n))).hom ≫
        Modules.freeHomOfSections
          (fun x : ULift.{u} (Fin r) × Fin ((n + e).choose n) ↦
            quotMonomialSection n T l r p d e he x.1 x.2) := by
  let s := fun x : ULift.{u} (Fin r) × Fin ((n + e).choose n) ↦
    quotMonomialSection n T l r p d e he x.1 x.2
  have h := Modules.pullback_freeHomOfSections_comp
    (projectiveSpaceOverπ n T) s s
    ((Modules.pullbackPushforwardAdjunction
      (projectiveSpaceOverπ n T)).counit.app
        (projectiveSpaceOverTwistModule Q (d : ℤ)))
    (fun x ↦ Modules.counit_app_top_pullbackGlobalSections
      (projectiveSpaceOverπ n T)
      (projectiveSpaceOverTwistModule Q (d : ℤ)) (s x))
  change (Modules.pullbackFreeIso (projectiveSpaceOverπ n T)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n))).inv ≫
      (Modules.pullback (projectiveSpaceOverπ n T)).map
        (quotGrassmannianFreeMap n T l r p d e he) ≫
      (Modules.pullbackPushforwardAdjunction
        (projectiveSpaceOverπ n T)).counit.app
          (projectiveSpaceOverTwistModule Q (d : ℤ)) =
    Modules.freeHomOfSections s at h
  rw [← h]
  simp only [Iso.hom_inv_id_assoc]

/-- The pulled-back Grassmannian free map is the twisted ambient monomial map followed
by the twisted quotient map. -/
lemma pullback_quotGrassmannianFreeMap_comp_counit_eq_twistedFreeMonomialMap
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ)
    {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) :
    (Modules.pullback (projectiveSpaceOverπ n T)).map
          (quotGrassmannianFreeMap n T l r p d e he) ≫
        (Modules.pullbackPushforwardAdjunction
          (projectiveSpaceOverπ n T)).counit.app
            (projectiveSpaceOverTwistModule Q (d : ℤ)) =
      (Modules.pullbackFreeIso (projectiveSpaceOverπ n T)
          (ULift.{u} (Fin r) × Fin ((n + e).choose n))).hom ≫
        twistedFreeMonomialMap n T l r d e he ≫
        Modules.tensorMapLeft p (projectiveSpaceOverTwist n T (d : ℤ)) := by
  rw [pullback_quotGrassmannianFreeMap_comp_counit]
  have hfree : Modules.freeHomOfSections
        (fun x : ULift.{u} (Fin r) × Fin ((n + e).choose n) ↦
          quotMonomialSection n T l r p d e he x.1 x.2) =
      twistedFreeMonomialMap n T l r d e he ≫
        Modules.tensorMapLeft p (projectiveSpaceOverTwist n T (d : ℤ)) := by
    dsimp only [twistedFreeMonomialMap]
    exact (Modules.freeHomOfSections_comp
      (fun x : ULift.{u} (Fin r) × Fin ((n + e).choose n) ↦
        twistedFreeMonomialSection n T l r d e he x.1 x.2)
      (Modules.tensorMapLeft p
        (projectiveSpaceOverTwist n T (d : ℤ)))).symm
  exact congrArg
    (fun k ↦ (Modules.pullbackFreeIso (projectiveSpaceOverπ n T)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n))).hom ≫ k) hfree

/-- The canonical map from the pullback of the Grassmannian kernel to the kernel of
the twisted quotient map.  Its epimorphy is precisely relative global generation of
the original quotient kernel in degree `d`. -/
noncomputable def quotGrassmannianTwistedKernelMap
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ)
    {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) :
    (Modules.pullback (projectiveSpaceOverπ n T)).obj
        (kernel (quotGrassmannianFreeMap n T l r p d e he)) ⟶
      kernel (Modules.tensorMapLeft p
        (projectiveSpaceOverTwist n T (d : ℤ))) :=
  kernel.lift _
    ((Modules.pullback (projectiveSpaceOverπ n T)).map
        (kernel.ι (quotGrassmannianFreeMap n T l r p d e he)) ≫
      (Modules.pullbackFreeIso (projectiveSpaceOverπ n T)
        (ULift.{u} (Fin r) × Fin ((n + e).choose n))).hom ≫
      twistedFreeMonomialMap n T l r d e he) (by
        rw [Category.assoc, Category.assoc,
          ← pullback_quotGrassmannianFreeMap_comp_counit_eq_twistedFreeMonomialMap]
        rw [← Category.assoc, ← Functor.map_comp, kernel.condition,
          Functor.map_zero, zero_comp])

/-- The twisted-kernel comparison recovers the pulled-back monomial relation after
the kernel inclusion. -/
@[reassoc (attr := simp)]
lemma quotGrassmannianTwistedKernelMap_comp
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ)
    {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) :
    quotGrassmannianTwistedKernelMap n T l r p d e he ≫
        kernel.ι (Modules.tensorMapLeft p
          (projectiveSpaceOverTwist n T (d : ℤ))) =
      (Modules.pullback (projectiveSpaceOverπ n T)).map
          (kernel.ι (quotGrassmannianFreeMap n T l r p d e he)) ≫
        (Modules.pullbackFreeIso (projectiveSpaceOverπ n T)
          (ULift.{u} (Fin r) × Fin ((n + e).choose n))).hom ≫
      twistedFreeMonomialMap n T l r d e he :=
  kernel.lift_ι _ _ _

/-- The adjoint on the base of the twisted Grassmannian-kernel comparison.  Showing
this map is an isomorphism identifies the Grassmannian kernel with the pushforward of
the degree-`d` quotient kernel. -/
noncomputable def quotGrassmannianTwistedKernelAdjunct
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ)
    {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) :
    kernel (quotGrassmannianFreeMap n T l r p d e he) ⟶
      (Modules.pushforward (projectiveSpaceOverπ n T)).obj
        (kernel (Modules.tensorMapLeft p
          (projectiveSpaceOverTwist n T (d : ℤ)))) :=
  (Modules.pullbackPushforwardAdjunction
    (projectiveSpaceOverπ n T)).homEquiv _ _
      (quotGrassmannianTwistedKernelMap n T l r p d e he)

/-- If the ambient fixed-degree monomial map is an isomorphism, the kernel of the
Grassmannian quotient map is canonically the pushforward of the twisted quotient
kernel. -/
noncomputable def quotGrassmannianTwistedKernelAdjunctIso
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ)
    {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    [IsIso (twistedFreeMonomialPushforwardMap n T l r d e he)] :
    kernel (quotGrassmannianFreeMap n T l r p d e he) ≅
      (Modules.pushforward (projectiveSpaceOverπ n T)).obj
        (kernel (Modules.tensorMapLeft p
          (projectiveSpaceOverTwist n T (d : ℤ)))) :=
  kernelIsoOfEq (quotGrassmannianFreeMap_eq n T l r p d e he) ≪≫
    kernelIsIsoComp
      (twistedFreeMonomialPushforwardMap n T l r d e he)
      ((Modules.pushforward (projectiveSpaceOverπ n T)).map
        (Modules.tensorMapLeft p
          (projectiveSpaceOverTwist n T (d : ℤ)))) ≪≫
    (PreservesKernel.iso (Modules.pushforward (projectiveSpaceOverπ n T))
      (Modules.tensorMapLeft p
        (projectiveSpaceOverTwist n T (d : ℤ)))).symm

/-- The canonical kernel isomorphism induced by the ambient monomial-basis map has
the expected composite with the pushed-forward kernel inclusion. -/
@[reassoc (attr := simp)]
lemma quotGrassmannianTwistedKernelAdjunctIso_hom_comp
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ)
    {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    [IsIso (twistedFreeMonomialPushforwardMap n T l r d e he)] :
    (quotGrassmannianTwistedKernelAdjunctIso n T l r p d e he).hom ≫
        (Modules.pushforward (projectiveSpaceOverπ n T)).map
          (kernel.ι (Modules.tensorMapLeft p
            (projectiveSpaceOverTwist n T (d : ℤ)))) =
      kernel.ι (quotGrassmannianFreeMap n T l r p d e he) ≫
        twistedFreeMonomialPushforwardMap n T l r d e he := by
  simp only [quotGrassmannianTwistedKernelAdjunctIso, Iso.trans_hom,
    Iso.symm_hom, Category.assoc]
  rw [PreservesKernel.iso_inv_ι]
  have hcomp :
      (kernelIsIsoComp
        (twistedFreeMonomialPushforwardMap n T l r d e he)
        ((Modules.pushforward (projectiveSpaceOverπ n T)).map
          (Modules.tensorMapLeft p
            (projectiveSpaceOverTwist n T (d : ℤ))))).hom ≫
          kernel.ι ((Modules.pushforward (projectiveSpaceOverπ n T)).map
            (Modules.tensorMapLeft p
              (projectiveSpaceOverTwist n T (d : ℤ)))) =
        kernel.ι
            (twistedFreeMonomialPushforwardMap n T l r d e he ≫
              (Modules.pushforward (projectiveSpaceOverπ n T)).map
                (Modules.tensorMapLeft p
                  (projectiveSpaceOverTwist n T (d : ℤ)))) ≫
          twistedFreeMonomialPushforwardMap n T l r d e he := by
    rw [kernelIsIsoComp_hom, kernel.lift_ι]
  rw [hcomp]
  rw [← Category.assoc]
  exact congrArg
    (fun k ↦ k ≫ twistedFreeMonomialPushforwardMap n T l r d e he)
    (kernelIsoOfEq_hom_comp_ι
      (quotGrassmannianFreeMap_eq n T l r p d e he))

/-- The actual adjoint of the twisted-kernel comparison has the same defining
composite as the canonical kernel isomorphism. -/
@[reassoc (attr := simp)]
lemma quotGrassmannianTwistedKernelAdjunct_comp
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ)
    {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) :
    quotGrassmannianTwistedKernelAdjunct n T l r p d e he ≫
        (Modules.pushforward (projectiveSpaceOverπ n T)).map
          (kernel.ι (Modules.tensorMapLeft p
            (projectiveSpaceOverTwist n T (d : ℤ)))) =
      kernel.ι (quotGrassmannianFreeMap n T l r p d e he) ≫
        twistedFreeMonomialPushforwardMap n T l r d e he := by
  let π := projectiveSpaceOverπ n T
  let A := twistedFreeMonomialPushforwardMap n T l r d e he
  let K := kernel (quotGrassmannianFreeMap n T l r p d e he)
  let pd := Modules.tensorMapLeft p (projectiveSpaceOverTwist n T (d : ℤ))
  let t := quotGrassmannianTwistedKernelMap n T l r p d e he
  let w := (Modules.pullbackFreeIso π
    (ULift.{u} (Fin r) × Fin ((n + e).choose n))).hom
  let m := twistedFreeMonomialMap n T l r d e he
  change (Modules.pullbackPushforwardAdjunction π).homEquiv K (kernel pd) t ≫
      (Modules.pushforward π).map (kernel.ι pd) = kernel.ι _ ≫ A
  rw [← (Modules.pullbackPushforwardAdjunction π).homEquiv_naturality_right]
  have ht : t ≫ kernel.ι pd =
      (Modules.pullback π).map (kernel.ι
        (quotGrassmannianFreeMap n T l r p d e he)) ≫ w ≫ m :=
    quotGrassmannianTwistedKernelMap_comp n T l r p d e he
  rw [ht]
  rw [(Modules.pullbackPushforwardAdjunction π).homEquiv_naturality_left]
  exact congrArg (fun k ↦ kernel.ι
      (quotGrassmannianFreeMap n T l r p d e he) ≫ k)
    (twistedFreeMonomialPushforwardMap_adjunct n T l r d e he)

/-- The adjoint of the twisted-kernel comparison is the canonical kernel
isomorphism induced by the ambient monomial-basis map. -/
lemma quotGrassmannianTwistedKernelAdjunct_eq_iso_hom
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ)
    {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    [IsIso (twistedFreeMonomialPushforwardMap n T l r d e he)] :
    quotGrassmannianTwistedKernelAdjunct n T l r p d e he =
      (quotGrassmannianTwistedKernelAdjunctIso n T l r p d e he).hom := by
  apply (cancel_mono
    ((Modules.pushforward (projectiveSpaceOverπ n T)).map
      (kernel.ι (Modules.tensorMapLeft p
        (projectiveSpaceOverTwist n T (d : ℤ)))))).1
  rw [quotGrassmannianTwistedKernelAdjunct_comp,
    quotGrassmannianTwistedKernelAdjunctIso_hom_comp]

/-- The ambient monomial-basis isomorphism makes the twisted-kernel adjunct an
isomorphism. -/
theorem quotGrassmannianTwistedKernelAdjunct_isIso_of_ambient_isIso
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ)
    {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    [IsIso (twistedFreeMonomialPushforwardMap n T l r d e he)] :
    IsIso (quotGrassmannianTwistedKernelAdjunct n T l r p d e he) := by
  rw [quotGrassmannianTwistedKernelAdjunct_eq_iso_hom]
  infer_instance

/-- Once the Grassmannian kernel is identified with the pushforward of the twisted
quotient kernel, epimorphy of the evaluation counit gives epimorphy of the canonical
twisted-kernel comparison. -/
theorem quotGrassmannianTwistedKernelMap_epi_of_adjunct_isIso_of_counit_epi
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ)
    {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    [IsIso (quotGrassmannianTwistedKernelAdjunct n T l r p d e he)]
    [Epi ((Modules.pullbackPushforwardAdjunction
      (projectiveSpaceOverπ n T)).counit.app
        (kernel (Modules.tensorMapLeft p
          (projectiveSpaceOverTwist n T (d : ℤ)))))] :
    Epi (quotGrassmannianTwistedKernelMap n T l r p d e he) := by
  letI : IsIso
      ((Modules.pullbackPushforwardAdjunction
        (projectiveSpaceOverπ n T)).homEquiv _ _
          (quotGrassmannianTwistedKernelMap n T l r p d e he)) := by
    change IsIso (quotGrassmannianTwistedKernelAdjunct n T l r p d e he)
    infer_instance
  exact Modules.epi_of_isIso_pullbackPushforwardAdjunct_of_counit_epi
    (projectiveSpaceOverπ n T)
    (quotGrassmannianTwistedKernelMap n T l r p d e he)

/-- A globally generating family of sections of the twisted quotient kernel supplies
the evaluation-counit hypothesis in the preceding reflection criterion. -/
theorem quotGrassmannianTwistedKernelMap_epi_of_adjunct_isIso_of_freeHomOfSections
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ)
    {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    {I : Type u}
    (s : I → Γ(kernel (Modules.tensorMapLeft p
      (projectiveSpaceOverTwist n T (d : ℤ))), ⊤))
    [IsIso (quotGrassmannianTwistedKernelAdjunct n T l r p d e he)]
    [Epi (Modules.freeHomOfSections s)] :
    Epi (quotGrassmannianTwistedKernelMap n T l r p d e he) := by
  letI : Epi ((Modules.pullbackPushforwardAdjunction
      (projectiveSpaceOverπ n T)).counit.app
        (kernel (Modules.tensorMapLeft p
          (projectiveSpaceOverTwist n T (d : ℤ))))) :=
    Modules.pullbackPushforwardCounit_epi_of_freeHomOfSections
      (projectiveSpaceOverπ n T) _ s
  exact quotGrassmannianTwistedKernelMap_epi_of_adjunct_isIso_of_counit_epi
    n T l r p d e he

/-- The ambient monomial-basis isomorphism and an epimorphic evaluation counit give
the twisted-kernel epimorphism required by reflection. -/
theorem quotGrassmannianTwistedKernelMap_epi_of_ambient_isIso_of_counit_epi
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ)
    {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    [IsIso (twistedFreeMonomialPushforwardMap n T l r d e he)]
    [Epi ((Modules.pullbackPushforwardAdjunction
      (projectiveSpaceOverπ n T)).counit.app
        (kernel (Modules.tensorMapLeft p
          (projectiveSpaceOverTwist n T (d : ℤ)))))] :
    Epi (quotGrassmannianTwistedKernelMap n T l r p d e he) := by
  letI : IsIso (quotGrassmannianTwistedKernelAdjunct n T l r p d e he) :=
    quotGrassmannianTwistedKernelAdjunct_isIso_of_ambient_isIso
      n T l r p d e he
  exact quotGrassmannianTwistedKernelMap_epi_of_adjunct_isIso_of_counit_epi
    n T l r p d e he

/-- A globally generating family for the twisted quotient kernel, together with the
ambient monomial-basis isomorphism, gives the twisted-kernel epimorphism required by
reflection. -/
theorem quotGrassmannianTwistedKernelMap_epi_of_ambient_isIso_of_freeHomOfSections
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ)
    {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    {I : Type u}
    (s : I → Γ(kernel (Modules.tensorMapLeft p
      (projectiveSpaceOverTwist n T (d : ℤ))), ⊤))
    [IsIso (twistedFreeMonomialPushforwardMap n T l r d e he)]
    [Epi (Modules.freeHomOfSections s)] :
    Epi (quotGrassmannianTwistedKernelMap n T l r p d e he) := by
  letI : IsIso (quotGrassmannianTwistedKernelAdjunct n T l r p d e he) :=
    quotGrassmannianTwistedKernelAdjunct_isIso_of_ambient_isIso
      n T l r p d e he
  exact quotGrassmannianTwistedKernelMap_epi_of_adjunct_isIso_of_freeHomOfSections
    n T l r p d e he s

/-- Untwisting the kernel of the degree-`d` quotient map recovers the kernel of the
original quotient map. -/
noncomputable def quotGrassmannianTwistedKernelUntwistIso
    (n : ℕ) (T : Scheme.{u})
    {F Q : (projectiveSpaceOver n T).Modules} (p : F ⟶ Q) (d : ℕ) :
    Modules.tensor
        (kernel (Modules.tensorMapLeft p
          (projectiveSpaceOverTwist n T (d : ℤ))))
        (projectiveSpaceOverTwist n T (-(d : ℤ))) ≅ kernel p :=
  Modules.tensorLeftIso
      (projectiveSpaceOverTwistTensorKernelIso n T p (d : ℤ)).symm
      (projectiveSpaceOverTwist n T (-(d : ℤ))) ≪≫
    projectiveSpaceOverTwistModule_cancelIso_nat n T (kernel p) d

/-- After the kernel inclusions, the twisted-kernel untwisting is the ordinary
opposite-twist cancellation. -/
@[reassoc (attr := simp)]
lemma quotGrassmannianTwistedKernelUntwistIso_hom_comp
    (n : ℕ) (T : Scheme.{u})
    {F Q : (projectiveSpaceOver n T).Modules} (p : F ⟶ Q) (d : ℕ) :
    (quotGrassmannianTwistedKernelUntwistIso n T p d).hom ≫ kernel.ι p =
      Modules.tensorMapLeft
          (kernel.ι (Modules.tensorMapLeft p
            (projectiveSpaceOverTwist n T (d : ℤ))))
          (projectiveSpaceOverTwist n T (-(d : ℤ))) ≫
        (projectiveSpaceOverTwistModule_cancelIso_nat n T F d).hom := by
  let Od := projectiveSpaceOverTwist n T (d : ℤ)
  let Dm := projectiveSpaceOverTwist n T (-(d : ℤ))
  let kIso := projectiveSpaceOverTwistTensorKernelIso n T p (d : ℤ)
  change Modules.tensorMapLeft kIso.inv Dm ≫
        (projectiveSpaceOverTwistModule_cancelIso_nat n T (kernel p) d).hom ≫
        kernel.ι p =
      Modules.tensorMapLeft (kernel.ι (Modules.tensorMapLeft p Od)) Dm ≫
        (projectiveSpaceOverTwistModule_cancelIso_nat n T F d).hom
  rw [← projectiveSpaceOverTwistModule_cancelIso_nat_hom_naturality
    n T (kernel.ι p) d]
  rw [← Category.assoc, ← Modules.tensorMapLeft_comp]
  have hk : kIso.inv ≫ Modules.tensorMapLeft (kernel.ι p) Od =
      kernel.ι (Modules.tensorMapLeft p Od) :=
    PreservesKernel.iso_inv_ι
      (Modules.tensorRightFunctor Od) p
  rw [hk]

/-- The twisted Grassmannian-kernel comparison, followed by inverse twisting. -/
noncomputable def quotGrassmannianTwistedKernelUntwistMap
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ)
    {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) :
    Modules.tensor
        ((Modules.pullback (projectiveSpaceOverπ n T)).obj
          (kernel (quotGrassmannianFreeMap n T l r p d e he)))
        (projectiveSpaceOverTwist n T (-(d : ℤ))) ⟶ kernel p :=
  Modules.tensorMapLeft
      (quotGrassmannianTwistedKernelMap n T l r p d e he)
      (projectiveSpaceOverTwist n T (-(d : ℤ))) ≫
    (quotGrassmannianTwistedKernelUntwistIso n T p d).hom

/-- The inverse-twisted kernel comparison is exactly the reconstruction relation,
provided multiplication by the ambient monomials is compatible with cancellation. -/
@[reassoc (attr := simp)]
lemma quotGrassmannianTwistedKernelUntwistMap_comp
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ)
    {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    (hambient :
      (freeTensorTwistIso n T
          (ULift.{u} (Fin r) × Fin ((n + e).choose n)) (-(d : ℤ))).hom ≫
          twistedFreeMonomialHom n T l r d e he =
        Modules.tensorMapLeft
            (twistedFreeMonomialMap n T l r d e he)
            (projectiveSpaceOverTwist n T (-(d : ℤ))) ≫
          (projectiveSpaceOverTwistModule_cancelIso_nat n T
            (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) d).hom) :
    quotGrassmannianTwistedKernelUntwistMap n T l r p d e he ≫ kernel.ι p =
      reconstructedRelation' n T l r d e he
        (quotGrassmannianFreeMap n T l r p d e he) := by
  let Dm := projectiveSpaceOverTwist n T (-(d : ℤ))
  rw [quotGrassmannianTwistedKernelUntwistMap, Category.assoc,
    quotGrassmannianTwistedKernelUntwistIso_hom_comp]
  rw [← Category.assoc, ← Modules.tensorMapLeft_comp,
    quotGrassmannianTwistedKernelMap_comp]
  simp only [Modules.tensorMapLeft_comp, Category.assoc]
  rw [← hambient]
  rfl

/-- Relative global generation in degree `d` is the epimorphy of the twisted-kernel
comparison.  Together with ambient monomial compatibility it gives the complete kernel
presentation needed for reconstruction. -/
noncomputable def quotGrassmannianReconstructedRelationPresentsKernelOfTwistedKernelEpi
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ)
    {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    (hambient :
      (freeTensorTwistIso n T
          (ULift.{u} (Fin r) × Fin ((n + e).choose n)) (-(d : ℤ))).hom ≫
          twistedFreeMonomialHom n T l r d e he =
        Modules.tensorMapLeft
            (twistedFreeMonomialMap n T l r d e he)
            (projectiveSpaceOverTwist n T (-(d : ℤ))) ≫
          (projectiveSpaceOverTwistModule_cancelIso_nat n T
            (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) d).hom)
    [Epi (quotGrassmannianTwistedKernelMap n T l r p d e he)] :
    ReconstructedRelationPresentsKernel n T l r d e he
      (quotGrassmannianFreeMap n T l r p d e he) p where
  lift := quotGrassmannianTwistedKernelUntwistMap n T l r p d e he
  lift_comp := quotGrassmannianTwistedKernelUntwistMap_comp
    n T l r p d e he hambient
  epi := by
    dsimp only [quotGrassmannianTwistedKernelUntwistMap]
    infer_instance

/-- If the degree-`d` twisted kernel is relatively globally generated, the
Grassmannian reconstruction is canonically isomorphic to the original quotient. -/
noncomputable def reconstructedQuotientIsoOfTwistedKernelEpi
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ)
    {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    [Epi p] (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    (hambient :
      (freeTensorTwistIso n T
          (ULift.{u} (Fin r) × Fin ((n + e).choose n)) (-(d : ℤ))).hom ≫
          twistedFreeMonomialHom n T l r d e he =
        Modules.tensorMapLeft
            (twistedFreeMonomialMap n T l r d e he)
            (projectiveSpaceOverTwist n T (-(d : ℤ))) ≫
          (projectiveSpaceOverTwistModule_cancelIso_nat n T
            (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) d).hom)
    [Epi (quotGrassmannianTwistedKernelMap n T l r p d e he)] :
    reconstructedQuotient' n T l r d e he
        (quotGrassmannianFreeMap n T l r p d e he) ≅ Q :=
  (quotGrassmannianReconstructedRelationPresentsKernelOfTwistedKernelEpi
    n T l r p d e he hambient).quotientIso

/-- The reflection isomorphism obtained from the twisted-kernel comparison commutes
with the original twisted-free quotient map. -/
@[reassoc (attr := simp)]
lemma reconstructedQuotientMap'_comp_reconstructedQuotientIsoOfTwistedKernelEpi_hom
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ)
    {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    [Epi p] (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    (hambient :
      (freeTensorTwistIso n T
          (ULift.{u} (Fin r) × Fin ((n + e).choose n)) (-(d : ℤ))).hom ≫
          twistedFreeMonomialHom n T l r d e he =
        Modules.tensorMapLeft
            (twistedFreeMonomialMap n T l r d e he)
            (projectiveSpaceOverTwist n T (-(d : ℤ))) ≫
          (projectiveSpaceOverTwistModule_cancelIso_nat n T
            (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) d).hom)
    [Epi (quotGrassmannianTwistedKernelMap n T l r p d e he)] :
    reconstructedQuotientMap' n T l r d e he
        (quotGrassmannianFreeMap n T l r p d e he) ≫
      (reconstructedQuotientIsoOfTwistedKernelEpi
        n T l r p d e he hambient).hom = p :=
  ReconstructedRelationPresentsKernel.reconstructedQuotientMap'_comp_quotientIso_hom
    (quotGrassmannianReconstructedRelationPresentsKernelOfTwistedKernelEpi
      n T l r p d e he hambient)

/-- The pointwise free-sheaf untwisting square for every quotient follows from the
single ambient monomial compatibility, using naturality of cancellation. -/
lemma quotGrassmannian_free_untwist_of_ambient
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ)
    {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    (hambient :
      (freeTensorTwistIso n T
          (ULift.{u} (Fin r) × Fin ((n + e).choose n)) (-(d : ℤ))).hom ≫
          twistedFreeMonomialHom n T l r d e he =
        Modules.tensorMapLeft
            (twistedFreeMonomialMap n T l r d e he)
            (projectiveSpaceOverTwist n T (-(d : ℤ))) ≫
          (projectiveSpaceOverTwistModule_cancelIso_nat n T
            (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) d).hom) :
    (freeTensorTwistIso n T
          (ULift.{u} (Fin r) × Fin ((n + e).choose n)) (-(d : ℤ))).hom ≫
          twistedFreeMonomialHom n T l r d e he ≫ p =
        Modules.tensorMapLeft
            (Modules.freeHomOfSections
              (fun x : ULift.{u} (Fin r) × Fin ((n + e).choose n) ↦
                quotMonomialSection n T l r p d e he x.1 x.2))
            (projectiveSpaceOverTwist n T (-(d : ℤ))) ≫
          (projectiveSpaceOverTwistModule_cancelIso_nat n T Q d).hom := by
  let Od := projectiveSpaceOverTwist n T (d : ℤ)
  let Dm := projectiveSpaceOverTwist n T (-(d : ℤ))
  let F := ∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)
  let v := Modules.freeHomOfSections
    (fun x : ULift.{u} (Fin r) × Fin ((n + e).choose n) ↦
      quotMonomialSection n T l r p d e he x.1 x.2)
  have hv : v = twistedFreeMonomialMap n T l r d e he ≫
      Modules.tensorMapLeft p Od := by
    dsimp only [v, twistedFreeMonomialMap]
    exact (Modules.freeHomOfSections_comp
      (fun x : ULift.{u} (Fin r) × Fin ((n + e).choose n) ↦
        twistedFreeMonomialSection n T l r d e he x.1 x.2)
      (Modules.tensorMapLeft p Od)).symm
  change (freeTensorTwistIso n T
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) (-(d : ℤ))).hom ≫
      twistedFreeMonomialHom n T l r d e he ≫ p =
    Modules.tensorMapLeft v Dm ≫
      (projectiveSpaceOverTwistModule_cancelIso_nat n T Q d).hom
  rw [hv, Modules.tensorMapLeft_comp]
  simp only [Category.assoc]
  rw [projectiveSpaceOverTwistModule_cancelIso_nat_hom_naturality n T p d]
  exact congrArg (fun k ↦ k ≫ p) hambient

/-- The full monomial/evaluation square follows from its pointwise untwisting part after
the free-sheaf pullback and adjunction-counit coherence is removed. -/
lemma quotGrassmannian_canonical_monomial_square_of_free_untwist
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ)
    {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    (h : (freeTensorTwistIso n T
          (ULift.{u} (Fin r) × Fin ((n + e).choose n)) (-(d : ℤ))).hom ≫
          twistedFreeMonomialHom n T l r d e he ≫ p =
        Modules.tensorMapLeft
            (Modules.freeHomOfSections
              (fun x : ULift.{u} (Fin r) × Fin ((n + e).choose n) ↦
                quotMonomialSection n T l r p d e he x.1 x.2))
            (projectiveSpaceOverTwist n T (-(d : ℤ))) ≫
          (projectiveSpaceOverTwistModule_cancelIso_nat n T Q d).hom) :
    (quotGrassmannianUntwistedAmbientIso n T r d e).hom ≫
          twistedFreeMonomialHom n T l r d e he ≫ p =
        Modules.tensorMapLeft
            ((Modules.pullback (projectiveSpaceOverπ n T)).map
              (quotGrassmannianFreeMap n T l r p d e he))
            (projectiveSpaceOverTwist n T (-(d : ℤ))) ≫
          projectiveSpaceOverUntwistedEvaluation n T Q d := by
  let Dm := projectiveSpaceOverTwist n T (-(d : ℤ))
  let u := quotGrassmannianFreeMap n T l r p d e he
  let ε := (Modules.pullbackPushforwardAdjunction
    (projectiveSpaceOverπ n T)).counit.app
      (projectiveSpaceOverTwistModule Q (d : ℤ))
  let v := Modules.freeHomOfSections
    (fun x : ULift.{u} (Fin r) × Fin ((n + e).choose n) ↦
      quotMonomialSection n T l r p d e he x.1 x.2)
  let w := (Modules.pullbackFreeIso (projectiveSpaceOverπ n T)
    (ULift.{u} (Fin r) × Fin ((n + e).choose n))).hom
  let c := (projectiveSpaceOverTwistModule_cancelIso_nat n T Q d).hom
  have huv : (Modules.pullback (projectiveSpaceOverπ n T)).map u ≫ ε = w ≫ v :=
    pullback_quotGrassmannianFreeMap_comp_counit n T l r p d e he
  have ht := congrArg (fun k ↦ Modules.tensorMapLeft k Dm) huv
  simp only [Modules.tensorMapLeft_comp] at ht
  dsimp only [quotGrassmannianUntwistedAmbientIso, projectiveSpaceOverUntwistedEvaluation,
    Iso.trans_hom, Modules.tensorLeftIso]
  change Modules.tensorMapLeft w Dm ≫
      (freeTensorTwistIso n T
        (ULift.{u} (Fin r) × Fin ((n + e).choose n)) (-(d : ℤ))).hom ≫
        twistedFreeMonomialHom n T l r d e he ≫ p =
    Modules.tensorMapLeft
        ((Modules.pullback (projectiveSpaceOverπ n T)).map u) Dm ≫
      Modules.tensorMapLeft ε Dm ≫ c
  rw [h]
  calc
    Modules.tensorMapLeft w Dm ≫ Modules.tensorMapLeft v Dm ≫ c =
        (Modules.tensorMapLeft w Dm ≫ Modules.tensorMapLeft v Dm) ≫ c :=
      (Category.assoc _ _ _).symm
    _ = (Modules.tensorMapLeft
          ((Modules.pullback (projectiveSpaceOverπ n T)).map u) Dm ≫
        Modules.tensorMapLeft ε Dm) ≫ c :=
      congrArg (fun k ↦ k ≫ c) ht.symm
    _ = Modules.tensorMapLeft
          ((Modules.pullback (projectiveSpaceOverπ n T)).map u) Dm ≫
        Modules.tensorMapLeft ε Dm ≫ c :=
      Category.assoc _ _ _

/-- The exact untwisted monomial/evaluation square needed for reconstruction.

The lower map is retained as data so that multiplication-based reconstruction is not tied
to a particular chosen tensor associator.  Once this square is available, annihilation of
the reconstructed relation by `p` is formal. -/
structure QuotGrassmannianUntwistedEvaluationData
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) : Type (u + 1) where
  /-- Evaluation after pulling the fixed-degree pushforward back to projective space and
  applying the inverse twist. -/
  evaluation :
    Modules.tensor
        ((Modules.pullback (projectiveSpaceOverπ n T)).obj
          ((Modules.pushforward (projectiveSpaceOverπ n T)).obj
            (projectiveSpaceOverTwistModule Q (d : ℤ))))
        (projectiveSpaceOverTwist n T (-(d : ℤ))) ⟶ Q
  /-- Multiplication by monomials followed by `p` is the evaluation of their images in
  the fixed-degree pushforward. -/
  monomial_comp :
    (quotGrassmannianUntwistedAmbientIso n T r d e).hom ≫
        twistedFreeMonomialHom n T l r d e he ≫ p =
      Modules.tensorMapLeft
          ((Modules.pullback (projectiveSpaceOverπ n T)).map
            (quotGrassmannianFreeMap n T l r p d e he))
          (projectiveSpaceOverTwist n T (-(d : ℤ))) ≫ evaluation

namespace QuotGrassmannianUntwistedEvaluationData

/-- Construct the untwisted evaluation data from the single concrete monomial square
against the pullback--pushforward counit and cancellation of opposite twists. -/
noncomputable def ofCanonical
    {n : ℕ} {T : Scheme.{u}} {l : ℤ} {r : ℕ}
    {Q : (projectiveSpaceOver n T).Modules}
    {p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q}
    {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)}
    (h : (quotGrassmannianUntwistedAmbientIso n T r d e).hom ≫
          twistedFreeMonomialHom n T l r d e he ≫ p =
        Modules.tensorMapLeft
            ((Modules.pullback (projectiveSpaceOverπ n T)).map
              (quotGrassmannianFreeMap n T l r p d e he))
            (projectiveSpaceOverTwist n T (-(d : ℤ))) ≫
          projectiveSpaceOverUntwistedEvaluation n T Q d) :
    QuotGrassmannianUntwistedEvaluationData n T l r p d e he where
  evaluation := projectiveSpaceOverUntwistedEvaluation n T Q d
  monomial_comp := h

/-- Construct the canonical evaluation data from only the pointwise free-sheaf
untwisting equality; pullback of the free map and the adjunction counit are discharged by
`quotGrassmannian_canonical_monomial_square_of_free_untwist`. -/
noncomputable def ofFreeUntwist
    {n : ℕ} {T : Scheme.{u}} {l : ℤ} {r : ℕ}
    {Q : (projectiveSpaceOver n T).Modules}
    {p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q}
    {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)}
    (h : (freeTensorTwistIso n T
          (ULift.{u} (Fin r) × Fin ((n + e).choose n)) (-(d : ℤ))).hom ≫
          twistedFreeMonomialHom n T l r d e he ≫ p =
        Modules.tensorMapLeft
            (Modules.freeHomOfSections
              (fun x : ULift.{u} (Fin r) × Fin ((n + e).choose n) ↦
                quotMonomialSection n T l r p d e he x.1 x.2))
            (projectiveSpaceOverTwist n T (-(d : ℤ))) ≫
          (projectiveSpaceOverTwistModule_cancelIso_nat n T Q d).hom) :
    QuotGrassmannianUntwistedEvaluationData n T l r p d e he :=
  .ofCanonical
    (quotGrassmannian_canonical_monomial_square_of_free_untwist
      n T l r p d e he h)

/-- Construct the canonical evaluation square from the single ambient monomial
untwisting identity.  Naturality of opposite-twist cancellation supplies the quotient
map automatically. -/
noncomputable def ofAmbientUntwist
    {n : ℕ} {T : Scheme.{u}} {l : ℤ} {r : ℕ}
    {Q : (projectiveSpaceOver n T).Modules}
    {p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q}
    {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)}
    (hambient :
      (freeTensorTwistIso n T
          (ULift.{u} (Fin r) × Fin ((n + e).choose n)) (-(d : ℤ))).hom ≫
          twistedFreeMonomialHom n T l r d e he =
        Modules.tensorMapLeft
            (twistedFreeMonomialMap n T l r d e he)
            (projectiveSpaceOverTwist n T (-(d : ℤ))) ≫
          (projectiveSpaceOverTwistModule_cancelIso_nat n T
            (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) d).hom) :
    QuotGrassmannianUntwistedEvaluationData n T l r p d e he :=
  .ofFreeUntwist
    (quotGrassmannian_free_untwist_of_ambient n T l r p d e he hambient)

/-- The untwisted monomial/evaluation square kills the reconstructed relation. -/
lemma reconstructedRelation'_comp_quotient_eq_zero
    {n : ℕ} {T : Scheme.{u}} {l : ℤ} {r : ℕ}
    {Q : (projectiveSpaceOver n T).Modules}
    {p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q}
    {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)}
    (D : QuotGrassmannianUntwistedEvaluationData n T l r p d e he) :
    reconstructedRelation' n T l r d e he
      (quotGrassmannianFreeMap n T l r p d e he) ≫ p = 0 := by
  rw [reconstructedRelation']
  have h := D.monomial_comp
  dsimp only [quotGrassmannianUntwistedAmbientIso, Iso.trans_hom] at h
  simp only [Category.assoc] at h ⊢
  rw [h]
  rw [← Category.assoc, ← Modules.tensorMapLeft_comp, ← Functor.map_comp,
    kernel.condition, Functor.map_zero]
  change (Modules.tensorRightFunctor
    (projectiveSpaceOverTwist n T (-(d : ℤ)))).map 0 ≫ D.evaluation = 0
  rw [Functor.map_zero, zero_comp]

end QuotGrassmannianUntwistedEvaluationData

/-- The canonical lift of the untwisted monomial relation to the kernel of the original
twisted-free quotient. -/
noncomputable def quotGrassmannianReconstructedKernelLift
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    (hzero : reconstructedRelation' n T l r d e he
      (quotGrassmannianFreeMap n T l r p d e he) ≫ p = 0) :
    Modules.tensor
        ((Modules.pullback (projectiveSpaceOverπ n T)).obj
          (kernel (quotGrassmannianFreeMap n T l r p d e he)))
        (projectiveSpaceOverTwist n T (-(d : ℤ))) ⟶ kernel p :=
  kernel.lift p (reconstructedRelation' n T l r d e he
    (quotGrassmannianFreeMap n T l r p d e he)) hzero

/-- The canonical reconstructed-kernel lift recovers the untwisted monomial relation
after the kernel inclusion. -/
@[reassoc (attr := simp)]
lemma quotGrassmannianReconstructedKernelLift_comp
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    (hzero : reconstructedRelation' n T l r d e he
      (quotGrassmannianFreeMap n T l r p d e he) ≫ p = 0) :
    quotGrassmannianReconstructedKernelLift n T l r p d e he hzero ≫ kernel.ι p =
      reconstructedRelation' n T l r d e he
        (quotGrassmannianFreeMap n T l r p d e he) :=
  kernel.lift_ι _ _ _

/-- Vanishing of the monomial relation and affine-local generation of the quotient
kernel construct the presentation needed for reconstruction reflection. -/
noncomputable def quotGrassmannianReconstructedRelationPresentsKernel
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    (hzero : reconstructedRelation' n T l r d e he
      (quotGrassmannianFreeMap n T l r p d e he) ≫ p = 0)
    (hsurj : ∀ U : (projectiveSpaceOver n T).affineOpens,
      Function.Surjective (Modules.Hom.app
        (quotGrassmannianReconstructedKernelLift n T l r p d e he hzero) U.1)) :
    ReconstructedRelationPresentsKernel n T l r d e he
      (quotGrassmannianFreeMap n T l r p d e he) p where
  lift := quotGrassmannianReconstructedKernelLift n T l r p d e he hzero
  lift_comp := quotGrassmannianReconstructedKernelLift_comp n T l r p d e he hzero
  epi := Modules.epi_of_surjective_on_affineOpens _ hsurj

/-- The monomial/evaluation square together with affine-local generation constructs the
kernel presentation without a separately supplied vanishing proof. -/
noncomputable def QuotGrassmannianUntwistedEvaluationData.presentsKernel
    {n : ℕ} {T : Scheme.{u}} {l : ℤ} {r : ℕ}
    {Q : (projectiveSpaceOver n T).Modules}
    {p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q}
    {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)}
    (D : QuotGrassmannianUntwistedEvaluationData n T l r p d e he)
    (hsurj : ∀ U : (projectiveSpaceOver n T).affineOpens,
      Function.Surjective (Modules.Hom.app
        (quotGrassmannianReconstructedKernelLift n T l r p d e he
          D.reconstructedRelation'_comp_quotient_eq_zero) U.1)) :
    ReconstructedRelationPresentsKernel n T l r d e he
      (quotGrassmannianFreeMap n T l r p d e he) p :=
  quotGrassmannianReconstructedRelationPresentsKernel n T l r p d e he
    D.reconstructedRelation'_comp_quotient_eq_zero hsurj

/-- An epimorphic family of relations which factors through the canonical kernel lift
makes that lift epimorphic.  This is the form consumed by a finite twisted-free
presentation of the quotient kernel. -/
noncomputable def QuotGrassmannianUntwistedEvaluationData.presentsKernelOfEpiFactor
    {n : ℕ} {T : Scheme.{u}} {l : ℤ} {r : ℕ}
    {Q : (projectiveSpaceOver n T).Modules}
    {p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q}
    {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)}
    (D : QuotGrassmannianUntwistedEvaluationData n T l r p d e he)
    {A : (projectiveSpaceOver n T).Modules}
    (a : A ⟶ kernel p) [Epi a]
    (s : A ⟶ Modules.tensor
      ((Modules.pullback (projectiveSpaceOverπ n T)).obj
        (kernel (quotGrassmannianFreeMap n T l r p d e he)))
      (projectiveSpaceOverTwist n T (-(d : ℤ))))
    (hs : s ≫ quotGrassmannianReconstructedKernelLift n T l r p d e he
      D.reconstructedRelation'_comp_quotient_eq_zero = a) :
    ReconstructedRelationPresentsKernel n T l r d e he
      (quotGrassmannianFreeMap n T l r p d e he) p where
  lift := quotGrassmannianReconstructedKernelLift n T l r p d e he
    D.reconstructedRelation'_comp_quotient_eq_zero
  lift_comp := quotGrassmannianReconstructedKernelLift_comp n T l r p d e he
    D.reconstructedRelation'_comp_quotient_eq_zero
  epi := epi_of_epi_fac hs

/-- Under the two reflection inputs, the untwisted reconstruction is canonically
isomorphic to the original quotient. -/
noncomputable def reconstructedQuotientIsoOfQuotGrassmannian
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    [Epi p] (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    (hzero : reconstructedRelation' n T l r d e he
      (quotGrassmannianFreeMap n T l r p d e he) ≫ p = 0)
    (hsurj : ∀ U : (projectiveSpaceOver n T).affineOpens,
      Function.Surjective (Modules.Hom.app
        (quotGrassmannianReconstructedKernelLift n T l r p d e he hzero) U.1)) :
    reconstructedQuotient' n T l r d e he
        (quotGrassmannianFreeMap n T l r p d e he) ≅ Q :=
  (quotGrassmannianReconstructedRelationPresentsKernel
    n T l r p d e he hzero hsurj).quotientIso

/-- The canonical reflection isomorphism commutes with the quotient maps from the
twisted-free ambient sheaf. -/
@[reassoc (attr := simp)]
lemma reconstructedQuotientMap'_comp_reconstructedQuotientIsoOfQuotGrassmannian_hom
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    [Epi p] (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    (hzero : reconstructedRelation' n T l r d e he
      (quotGrassmannianFreeMap n T l r p d e he) ≫ p = 0)
    (hsurj : ∀ U : (projectiveSpaceOver n T).affineOpens,
      Function.Surjective (Modules.Hom.app
        (quotGrassmannianReconstructedKernelLift n T l r p d e he hzero) U.1)) :
    reconstructedQuotientMap' n T l r d e he
        (quotGrassmannianFreeMap n T l r p d e he) ≫
      (reconstructedQuotientIsoOfQuotGrassmannian
        n T l r p d e he hzero hsurj).hom = p :=
  ReconstructedRelationPresentsKernel.reconstructedQuotientMap'_comp_quotientIso_hom
      (quotGrassmannianReconstructedRelationPresentsKernel
        n T l r p d e he hzero hsurj)

end AlgebraicGeometry.Scheme

end

end
