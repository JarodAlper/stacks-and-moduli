module

public import StacksAndModuli.API.ProjectiveSpaceBaseChange
public import StacksAndModuli.API.SheafOfModulesLocalIso
public import StacksAndModuli.API.SchemeModulesTensorQuasicoherent
public import StacksAndModuli.API.PullbackAdjoint
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Base change for twisting sheaves on polynomial projective space

This file constructs the canonical comparison from the pullback of a twisting sheaf along
a morphism of projective spectra induced by a graded ring homomorphism.  It then specializes
the construction to coefficient change for multivariate polynomial rings.

The comparison is defined before any polynomial hypotheses: a homogeneous fraction of degree
`d` is sent to the fraction obtained by applying the graded ring homomorphism to its numerator
and denominator.  The polynomial case is locally an isomorphism on the standard opens.

Main declarations:

* `ProjectiveSpectrum.Twist.pullbackComparison`: the canonical pullback comparison for a
  graded ring homomorphism.
* `ProjectiveSpectrum.Twist.polynomialPullbackIso`: coefficient change pulls `𝒪(d)` back to
  `𝒪(d)` on polynomial projective space.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open AlgebraicGeometry CategoryTheory Graded HomogeneousIdeal HomogeneousLocalization
open TopologicalSpace Opposite TopCat
open ProjectiveSpectrum
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- Extend a section over the whole space to the corresponding compatible family. -/
noncomputable def sectionsFromTop (M : X.Modules) (x : Γ(M, ⊤)) : M.sections :=
  M.val.sectionsMk
    (fun U ↦ M.presheaf.map (homOfLE (le_top (a := U.unop))).op x)
    (fun {U V} g ↦ by
      let a := (homOfLE (le_top (a := U.unop))).op
      let b := (homOfLE (le_top (a := V.unop))).op
      change M.presheaf.map g (M.presheaf.map a x) = M.presheaf.map b x
      have hab : a ≫ g = b := Subsingleton.elim _ _
      have hm : M.presheaf.map a ≫ M.presheaf.map g = M.presheaf.map b := by
        rw [← M.presheaf.map_comp, hab]
      exact ConcreteCategory.congr_hom hm x)

@[simp]
theorem sectionsFromTop_apply_top (M : X.Modules) (x : Γ(M, ⊤)) :
    (sectionsFromTop M x).1 (.op ⊤) = x := by
  change M.presheaf.map (homOfLE (le_top (a := (⊤ : X.Opens)))).op x = x
  let a := (homOfLE (le_top (a := (⊤ : X.Opens)))).op
  have ha : a = 𝟙 (Opposite.op (⊤ : X.Opens)) := Subsingleton.elim _ _
  have hm : M.presheaf.map a = 𝟙 _ := by rw [ha, M.presheaf.map_id]
  exact ConcreteCategory.congr_hom hm x

/-- A compatible family of module sections is determined by its component over `⊤`. -/
theorem sections_ext_top_of_eq {M : X.Modules} (s t : M.sections)
    (h : s.1 (.op (⊤ : X.Opens)) = t.1 (.op (⊤ : X.Opens))) : s = t := by
  refine PresheafOfModules.sections_ext s t (fun U ↦ ?_)
  have hs := PresheafOfModules.sections_property s
    (X := .op (⊤ : X.Opens)) (Y := U) (homOfLE le_top).op
  have ht := PresheafOfModules.sections_property t
    (X := .op (⊤ : X.Opens)) (Y := U) (homOfLE le_top).op
  rw [← hs, ← ht, h]

/-- Endomorphisms of the structure sheaf, regarded as a module over itself, commute. -/
theorem unit_endomorphisms_comm
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    a ≫ b = b ≫ a := by
  ext U
  change b.val.app U (a.val.app U (1 : X.presheaf.obj U)) =
    a.val.app U (b.val.app U (1 : X.presheaf.obj U))
  have ha (y : X.presheaf.obj U) :
      a.val.app U y = y • a.val.app U (1 : X.presheaf.obj U) := by
    rw [← (a.val.app U).hom.map_smul]
    simp
  have hb (y : X.presheaf.obj U) :
      b.val.app U y = y • b.val.app U (1 : X.presheaf.obj U) := by
    rw [← (b.val.app U).hom.map_smul]
    simp
  let r : X.presheaf.obj U := a.val.app U (1 : X.presheaf.obj U)
  let s : X.presheaf.obj U := b.val.app U (1 : X.presheaf.obj U)
  calc
    _ = r • s := by simpa only [r, s] using hb r
    _ = s • r := by
      change r * s = s * r
      exact mul_comm r s
    _ = _ := by simpa only [r, s] using (ha s).symm

/-- An endomorphism of the structure sheaf is an isomorphism as soon as `1` has a
preimage on global sections. -/
theorem unit_endomorphism_isIso_of_exists_preimage_one
    (a : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf)
    (s : Γ(X, ⊤))
    (hs : Scheme.Modules.Hom.app a (⊤ : X.Opens) s = (1 : Γ(X, ⊤))) : IsIso a := by
  let b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf :=
    (SheafOfModules.unitHomEquiv _).symm
      (sectionsFromTop (SheafOfModules.unit X.ringCatSheaf) s)
  have hba : b ≫ a = 𝟙 _ := by
    apply (SheafOfModules.unitHomEquiv _).injective
    apply sections_ext_top_of_eq
    change Scheme.Modules.Hom.app a (⊤ : X.Opens)
      (Scheme.Modules.Hom.app b (⊤ : X.Opens) (1 : Γ(X, ⊤))) =
        (1 : Γ(X, ⊤))
    have hb : Scheme.Modules.Hom.app b (⊤ : X.Opens) (1 : Γ(X, ⊤)) = s := by
      change ((SheafOfModules.unitHomEquiv _ b).1 (.op (⊤ : X.Opens))) = s
      rw [show SheafOfModules.unitHomEquiv _ b =
          sectionsFromTop (SheafOfModules.unit X.ringCatSheaf) s by
        exact Equiv.apply_symm_apply _ _]
      exact sectionsFromTop_apply_top _ _
    rw [hb, hs]
  have hab : a ≫ b = 𝟙 _ := (unit_endomorphisms_comm a b).trans hba
  exact ⟨⟨b, hab, hba⟩⟩

/-- A morphism of sheaves of modules which is an isomorphism on every member of an open
cover is an isomorphism. -/
theorem isIso_of_restrict_iSup_eq_top {I : Type*} {M N : X.Modules} (a : M ⟶ N)
    (U : I → X.Opens) (hU : ⨆ i, U i = ⊤)
    (hlocal : ∀ i, IsIso ((restrictFunctor (U i).ι).map a)) : IsIso a := by
  have hstalk (x : X) :
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map a.mapPresheaf) := by
    obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hU.ge (Set.mem_univ x))
    let y : (U i).toScheme := ⟨x, hxi⟩
    let b := (restrictFunctor (U i).ι).map a
    letI : IsIso b := hlocal i
    letI : IsIso ((toPresheaf (U i).toScheme).map b) :=
      Functor.map_isIso (toPresheaf (U i).toScheme) b
    have hbpre : IsIso b.mapPresheaf := by
      change IsIso ((toPresheaf (U i).toScheme).map b)
      infer_instance
    letI : IsIso b.mapPresheaf := hbpre
    haveI : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map b.mapPresheaf) :=
      inferInstance
    let l := (restrictFunctor (U i).ι ⋙ toPresheaf (U i).toScheme ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map a
    have hl : IsIso l := by
      change IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map b.mapPresheaf)
      infer_instance
    letI : IsIso l := hl
    exact IsIso.of_isIso_fac_left
      ((restrictStalkNatIso (U i).ι y).hom.naturality a).symm
  have hsheaf : IsIso ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map a) := by
    letI : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map a).1) := hstalk
    exact TopCat.Presheaf.isIso_of_stalkFunctor_map_iso
      ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map a)
  haveI : IsIso ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map a) := hsheaf
  haveI : (SheafOfModules.toSheaf.{u} X.ringCatSheaf).ReflectsIsomorphisms :=
    inferInstance
  exact isIso_of_reflects_iso a (SheafOfModules.toSheaf.{u} X.ringCatSheaf)

/-- The tautological finite presentation of a finite-rank free sheaf. -/
noncomputable def freePresentation (J : Type u) :
    SheafOfModules.Presentation (SheafOfModules.free (R := X.ringCatSheaf) J) := by
  let G : (SheafOfModules.free (R := X.ringCatSheaf) J).GeneratingSections := {
    I := J
    s := (SheafOfModules.free (R := X.ringCatSheaf) J).freeHomEquiv (𝟙 _)
    epi := by
      change Epi ((SheafOfModules.freeHomEquiv _).symm
        (SheafOfModules.freeHomEquiv _ (𝟙 _)))
      rw [Equiv.symm_apply_apply]
      infer_instance }
  have hG : G.π = 𝟙 _ := by
    change (SheafOfModules.freeHomEquiv _).symm
      (SheafOfModules.freeHomEquiv _ (𝟙 _)) = 𝟙 _
    exact Equiv.symm_apply_apply _ _
  letI : IsIso G.π := hG.symm ▸ inferInstance
  let hzero : IsZero (kernel G.π) := isZero_kernel_of_mono G.π
  exact {
    generators := G
    relations := {
      I := ULift.{u} PUnit
      s := fun _ ↦ sectionsFromTop (kernel G.π) 0
      epi := hzero.epi _ } }

instance freePresentation_isFinite (J : Type u) [Finite J] :
    (freePresentation (X := X) J).IsFinite where
  isFiniteType_generators := {
    finite := by
      change Finite J
      infer_instance }
  isFiniteType_relations := {
    finite := by
      change Finite (ULift.{u} PUnit)
      infer_instance }

/-- A finite global presentation determines a finitely presented sheaf. -/
theorem isFinitePresentation_of_globalPresentation {M : X.Modules}
    (P : SheafOfModules.Presentation M) [P.IsFinite] : M.IsFinitePresentation := by
  apply SheafOfModules.IsFinitePresentation.mk (C := X.Opens)
  refine ⟨P.quasicoherentData, ?_⟩
  constructor
  intro U
  let hP := (inferInstance : P.IsFinite)
  exact {
    isFiniteType_generators := {
      finite := by
        change Finite P.generators.I
        exact hP.isFiniteType_generators.finite }
    isFiniteType_relations := {
      finite := by
        change Finite P.relations.I
        exact hP.isFiniteType_relations.finite } }

/-- The one-generator, no-nontrivial-relations presentation of the structure sheaf. -/
noncomputable def unitPresentation (X : Scheme.{u}) :
    SheafOfModules.Presentation (SheafOfModules.unit X.ringCatSheaf) :=
  let J := ULift.{u} PUnit
  (freePresentation (X := X) J).ofIsIso
    (coproductUniqueIso (fun _ : J ↦ SheafOfModules.unit X.ringCatSheaf)).hom

instance unitPresentation_isFinite (X : Scheme.{u}) :
    (unitPresentation X).IsFinite := by
  dsimp [unitPresentation]
  infer_instance

/-- The structure sheaf, as a module over itself, is finitely presented. -/
theorem unit_isFinitePresentation_of_globalPresentation (X : Scheme.{u}) :
    (SheafOfModules.unit X.ringCatSheaf).IsFinitePresentation :=
  isFinitePresentation_of_globalPresentation (unitPresentation X)

/-- A family of finite presentations on an open cover determines a finite presentation. -/
theorem isFinitePresentation_of_restrictPresentation_iSup_eq_top
    (M : X.Modules) {I : Type u} (U : I → X.Opens) (hU : ⨆ i, U i = ⊤)
    (P : ∀ i, SheafOfModules.Presentation (M.restrict (U i).ι))
    [hP : ∀ i, (P i).IsFinite] : M.IsFinitePresentation := by
  have hcov : (_root_.Opens.grothendieckTopology (X : Type u)).CoversTop U := by
    rw [_root_.Opens.coversTop_iff]
    exact hU
  let overPresentation (i : I) : SheafOfModules.Presentation (M.over (U i)) := by
    let e := overEquiv (U i)
    let oe := overFunctorEquiv (U i)
    let η : SheafOfModules.unit (X.ringCatSheaf.over (U i)) ≅
        e.inverse.obj (SheafOfModules.unit (U i).toScheme.ringCatSheaf) :=
      e.unitIso.app _ ≪≫
        e.inverse.mapIso (oe.app (SheafOfModules.unit X.ringCatSheaf) ≪≫
          restrictUnitIso (U i).ι)
    let iso : e.inverse.obj (M.restrict (U i).ι) ≅ M.over (U i) :=
      e.inverse.mapIso (oe.app M).symm ≪≫ (e.unitIso.app _).symm
    exact SheafOfModules.Presentation.ofIsIso.{u, u, u} iso.hom
      ((P i).map e.inverse η)
  let q : M.QuasicoherentData.{u} := {
    I := I
    X := U
    coversTop := hcov
    presentation := overPresentation }
  apply SheafOfModules.IsFinitePresentation.mk (C := X.Opens)
  refine ⟨q, ?_⟩
  constructor
  intro i
  let hp := hP i
  exact {
    isFiniteType_generators := {
      finite := by
        change Finite (P i).generators.I
        exact hp.isFiniteType_generators.finite }
    isFiniteType_relations := {
      finite := by
        change Finite (P i).relations.I
        exact hp.isFiniteType_relations.finite } }

/-- Restricting a pulled-back module to the inverse image of an open is canonically the
pullback, along the restricted scheme morphism, of the restriction of the original module. -/
noncomputable def restrictPullbackIsoPreimage (f : X ⟶ Y) (U : Y.Opens) (M : Y.Modules) :
    (restrictFunctor (f ⁻¹ᵁ U).ι).obj ((pullback f).obj M) ≅
      (pullback (f.resLE U (f ⁻¹ᵁ U) le_rfl)).obj
        ((restrictFunctor U.ι).obj M) :=
  (restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).app ((pullback f).obj M) ≪≫
    (pullbackComp (f ⁻¹ᵁ U).ι f).app M ≪≫
    (pullbackCongr (by simp)).app M ≪≫
    ((pullbackComp (f.resLE U (f ⁻¹ᵁ U) le_rfl) U.ι).app M).symm ≪≫
    (pullback (f.resLE U (f ⁻¹ᵁ U) le_rfl)).mapIso
      ((restrictFunctorIsoPullback U.ι).symm.app M)

/-- The inverse of the canonical identification between the pullback of the structure
sheaf and the structure sheaf.  This is the orientation required by
`SheafOfModules.Presentation.map`. -/
noncomputable def unitIsoPullbackObjUnit (f : X ⟶ Y) :
    SheafOfModules.unit X.ringCatSheaf ≅
      (pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) := by
  letI : IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) :=
    isIso_pullbackObjUnitToUnit f
  exact (asIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)).symm

/-- Pull a chosen presentation of a module sheaf back along a scheme morphism. -/
noncomputable def pullbackPresentation (f : X ⟶ Y) {M : Y.Modules}
    (P : SheafOfModules.Presentation M) :
    SheafOfModules.Presentation ((pullback f).obj M) := by
  have : PreservesColimitsOfSize.{u, u} (pullback f) := inferInstance
  exact P.map (pullback f) (unitIsoPullbackObjUnit f)

/-- Pullback preserves finiteness of a chosen presentation. -/
instance pullbackPresentation_isFinite (f : X ⟶ Y) {M : Y.Modules}
    (P : SheafOfModules.Presentation M) [P.IsFinite] :
    (pullbackPresentation f P).IsFinite := by
  constructor
  · constructor
    simpa only [pullbackPresentation, SheafOfModules.Presentation.map_generators_I] using
      (inferInstance : Finite P.generators.I)
  · constructor
    simpa only [pullbackPresentation, SheafOfModules.Presentation.map_relations_I] using
      (inferInstance : Finite P.relations.I)

/-- Convert a presentation on the over-site of an open into a presentation of the
restriction to the corresponding open subscheme. -/
noncomputable def restrictPresentationOfOver (M : X.Modules) (U : X.Opens)
    (P : SheafOfModules.Presentation (M.over U)) :
    SheafOfModules.Presentation (M.restrict U.ι) := by
  let e := overEquiv U
  letI : e.functor.IsLeftAdjoint := e.isLeftAdjoint_functor
  let η : SheafOfModules.unit U.toScheme.ringCatSheaf ≅
      e.functor.obj (SheafOfModules.unit (X.ringCatSheaf.over U)) :=
    (restrictUnitIso U.ι).symm ≪≫
      ((overFunctorEquiv U).app (SheafOfModules.unit X.ringCatSheaf)).symm
  let iso : e.functor.obj (M.over U) ≅ M.restrict U.ι :=
    (overFunctorEquiv U).app M
  exact (P.map e.functor η).ofIsIso iso.hom

/-- Passing from an over-site presentation to the corresponding restricted
presentation preserves its finite generator and relation types. -/
instance restrictPresentationOfOver_isFinite (M : X.Modules) (U : X.Opens)
    (P : SheafOfModules.Presentation (M.over U)) [P.IsFinite] :
    (restrictPresentationOfOver M U P).IsFinite := by
  let hP := (inferInstance : P.IsFinite)
  exact {
    isFiniteType_generators := {
      finite := by
        change Finite P.generators.I
        exact hP.isFiniteType_generators.finite }
    isFiniteType_relations := {
      finite := by
        change Finite P.relations.I
        exact hP.isFiniteType_relations.finite } }

/-- Pullback along an arbitrary scheme morphism preserves finite presentation of a
module sheaf.  This API-level result avoids a dependency from Chapter 2 on the later
descent chapter. -/
theorem isFinitePresentation_pullback_of_isFinitePresentation {M : Y.Modules}
    (f : X ⟶ Y) (hM : M.IsFinitePresentation) :
    ((Scheme.Modules.pullback f).obj M).IsFinitePresentation := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  let U (i : q.I) := f ⁻¹ᵁ q.X i
  let P (i : q.I) : SheafOfModules.Presentation
      (((Scheme.Modules.pullback f).obj M).restrict (U i).ι) :=
    (pullbackPresentation (f.resLE (q.X i) (U i) le_rfl)
      (restrictPresentationOfOver M (q.X i) (q.presentation i))).ofIsIso
        (restrictPullbackIsoPreimage f (q.X i) M).inv
  letI (i : q.I) : (P i).IsFinite := by
    dsimp [P]
    letI : (q.presentation i).IsFinite := hq.isFinite_presentation i
    infer_instance
  have hU : ⨆ i, U i = ⊤ := by
    dsimp [U]
    rw [← Scheme.Hom.preimage_iSup]
    have hcov := q.coversTop
    rw [_root_.Opens.coversTop_iff] at hcov
    rw [hcov, Scheme.Hom.preimage_top]
  exact isFinitePresentation_of_restrictPresentation_iSup_eq_top
    ((Scheme.Modules.pullback f).obj M) U hU P

set_option maxHeartbeats 800000 in
-- Refining two quasicoherent covers and transporting both finite presentations is
-- elaboration-heavy under the compatibility transparency settings used by this API.
/-- Tensoring a finitely presented module sheaf with a module sheaf which is trivial on
an open cover preserves finite presentation. -/
theorem tensor_isFinitePresentation_of_iSup_iso_unit
    (F L : X.Modules) [F.IsFinitePresentation]
    {J : Type u} (U : J → X.Opens) (hU : ⨆ j, U j = ⊤)
    (eL : ∀ j, L.restrict (U j).ι ≅
      SheafOfModules.unit (U j).toScheme.ringCatSheaf) :
    (tensor F L).IsFinitePresentation := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData F
  let W (ij : q.I × J) : X.Opens := q.X ij.1 ⊓ U ij.2
  have hW : ⨆ ij, W ij = ⊤ := by
    apply top_unique
    intro x _
    have hxq : x ∈ ⨆ i, q.X i := by
      have hcov := q.coversTop
      rw [_root_.Opens.coversTop_iff] at hcov
      rw [hcov]
      trivial
    have hxU : x ∈ ⨆ j, U j := by
      rw [hU]
      trivial
    rw [Opens.mem_iSup] at hxq hxU ⊢
    obtain ⟨i, hxi⟩ := hxq
    obtain ⟨j, hxj⟩ := hxU
    exact ⟨⟨i, j⟩, hxi, hxj⟩
  let PF (ij : q.I × J) : SheafOfModules.Presentation
      (F.restrict (W ij).ι) := by
    let P₀ := restrictPresentationOfOver F (q.X ij.1) (q.presentation ij.1)
    let g := X.homOfLE (show W ij ≤ q.X ij.1 from inf_le_left)
    let e : (pullback g).obj (F.restrict (Scheme.Opens.ι (q.X ij.1))) ≅
        F.restrict (W ij).ι :=
      (restrictFunctorIsoPullback g).symm.app _ ≪≫
      (((restrictFunctorComp g (Scheme.Opens.ι (q.X ij.1))).symm ≪≫
        restrictFunctorCongr
          (X.homOfLE_ι (show W ij ≤ q.X ij.1 from inf_le_left))).app F)
    exact @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _
      e.hom e.isIso_hom (pullbackPresentation g P₀)
  letI (ij : q.I × J) : (PF ij).IsFinite := by
    letI : (q.presentation ij.1).IsFinite := hq.isFinite_presentation ij.1
    let P₀ := restrictPresentationOfOver F (q.X ij.1) (q.presentation ij.1)
    letI : P₀.IsFinite := by
      dsimp [P₀]
      infer_instance
    let g := X.homOfLE (show W ij ≤ q.X ij.1 from inf_le_left)
    letI : (pullbackPresentation g P₀).IsFinite := by infer_instance
    let hpull := (inferInstance : (pullbackPresentation g P₀).IsFinite)
    exact {
      isFiniteType_generators := {
        finite := by
          change Finite (pullbackPresentation g P₀).generators.I
          exact hpull.isFiniteType_generators.finite }
      isFiniteType_relations := {
        finite := by
          change Finite (pullbackPresentation g P₀).relations.I
          exact hpull.isFiniteType_relations.finite } }
  let eLW (ij : q.I × J) : L.restrict (W ij).ι ≅
      SheafOfModules.unit (W ij).toScheme.ringCatSheaf := by
    let g := X.homOfLE (show W ij ≤ U ij.2 from inf_le_right)
    let e := (restrictFunctorComp g (U ij.2).ι).symm ≪≫
      restrictFunctorCongr
        (X.homOfLE_ι (show W ij ≤ U ij.2 from inf_le_right))
    exact (e.app L).symm ≪≫ (restrictFunctor g).mapIso (eL ij.2) ≪≫
      restrictUnitIso g
  let P (ij : q.I × J) : SheafOfModules.Presentation
      ((tensor F L).restrict (W ij).ι) := by
    let e := restrictTensorIso (W ij).ι F L ≪≫
        tensorRightIso (F.restrict (W ij).ι) (eLW ij) ≪≫
        tensorUnitIso (F.restrict (W ij).ι)
    exact @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _
      e.inv e.isIso_inv (PF ij)
  letI (ij : q.I × J) : (P ij).IsFinite := by
    let hpf := (inferInstance : (PF ij).IsFinite)
    exact {
      isFiniteType_generators := {
        finite := by
          change Finite (PF ij).generators.I
          exact hpf.isFiniteType_generators.finite }
      isFiniteType_relations := {
        finite := by
          change Finite (PF ij).relations.I
          exact hpf.isFiniteType_relations.finite } }
  exact isFinitePresentation_of_restrictPresentation_iSup_eq_top
    (tensor F L) W hW P

end AlgebraicGeometry.Scheme.Modules

namespace HomogeneousLocalization

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- Apply a graded ring homomorphism to a shifted homogeneous fraction at corresponding
prime ideals. -/
def NumDenShift.mapAtPrime (f : 𝒜 →+*ᵍ ℬ) {I : Ideal A} [I.IsPrime]
    {J : Ideal B} [J.IsPrime] (hIJ : I = J.comap f) {d : ℤ}
    (p : NumDenShift 𝒜 I.primeCompl d) : NumDenShift ℬ J.primeCompl d where
  degDen := p.degDen
  degNum := p.degNum
  num := f.gradedAddHom p.degNum p.num
  den := f.gradedAddHom p.degDen p.den
  den_mem := by
    change f p.den ∉ J
    intro h
    exact p.den_mem (hIJ.ge h)
  deg_eq := p.deg_eq

@[simp]
theorem NumDenShift.mapAtPrime_embed (f : 𝒜 →+*ᵍ ℬ) {I : Ideal A} [I.IsPrime]
    {J : Ideal B} [J.IsPrime] (hIJ : I = J.comap f) {d : ℤ}
    (p : NumDenShift 𝒜 I.primeCompl d) :
    Localization.localRingHom I J f hIJ p.embed = (p.mapAtPrime f hIJ).embed := by
  rw [NumDenShift.embed_def, Localization.localRingHom_mk,
    NumDenShift.embed_def]
  rfl

end HomogeneousLocalization

namespace TopCat.PrelocalPredicate

variable {X Y : TopCat.{u}} {T : X → Type u} {T' : Y → Type u}

/-- Pull a dependent function on an open set back along a continuous map, applying a map
between the corresponding fibers. -/
def comapFunction (g : C(Y, X)) (φ : ∀ y : Y, T (g y) → T' y)
    (U : Opens X) (V : Opens Y) (hUV : V.1 ⊆ g ⁻¹' U.1)
    (s : ∀ x : U, T x.1) (y : V) : T' y.1 :=
  φ y.1 (s ⟨g y.1, hUV y.2⟩)

/-- A map of prelocal predicates carries locally admissible functions to locally admissible
functions. -/
theorem sheafify_comapFunction (g : C(Y, X)) (φ : ∀ y : Y, T (g y) → T' y)
    (P : TopCat.PrelocalPredicate T) (P' : TopCat.PrelocalPredicate T')
    (hmap : ∀ (U : Opens X) (V : Opens Y) (hUV : V.1 ⊆ g ⁻¹' U.1)
      (s : ∀ x : U, T x.1), P.pred s → P'.pred (comapFunction g φ U V hUV s))
    (U : Opens X) (V : Opens Y) (hUV : V.1 ⊆ g ⁻¹' U.1)
    (s : ∀ x : U, T x.1) (hs : P.sheafify.pred s) :
    P'.sheafify.pred (comapFunction g φ U V hUV s) := by
  intro y
  obtain ⟨W, hyW, iWU, hW⟩ := hs ⟨g y.1, hUV y.2⟩
  let W' := W.comap g ⊓ V
  have hW'W : W'.1 ⊆ g ⁻¹' W.1 := fun _ hz ↦ hz.1
  have hpred := hmap W W' hW'W (fun x ↦ s (iWU x)) hW
  refine ⟨W', ⟨hyW, y.2⟩, homOfLE (by dsimp [W']; exact inf_le_right), ?_⟩
  exact hpred

end TopCat.PrelocalPredicate

namespace ProjectiveSpectrum.Twist

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- The map on a degree-`d` homogeneous localization induced by a graded ring homomorphism. -/
noncomputable def atDegMap (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f) (d : ℤ)
    (p : ProjectiveSpectrum.top ℬ) :
    atDeg 𝒜 d (ProjectiveSpectrum.comap f hf p) →+
      atDeg ℬ d p where
  toFun z := ⟨Localization.localRingHom
    (ProjectiveSpectrum.comap f hf p).asHomogeneousIdeal.toIdeal
    p.asHomogeneousIdeal.toIdeal f rfl z.1, by
      obtain ⟨q, hq⟩ := z.2
      refine ⟨q.mapAtPrime f rfl, ?_⟩
      rw [← hq]
      exact (HomogeneousLocalization.NumDenShift.mapAtPrime_embed f rfl q).symm⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' z w := Subtype.ext (map_add _ z.1 w.1)

@[simp]
theorem atDegMap_val (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f) (d : ℤ)
    (p : ProjectiveSpectrum.top ℬ)
    (z : atDeg 𝒜 d (ProjectiveSpectrum.comap f hf p)) :
    ((atDegMap f hf d p z : atDeg ℬ d p) : Localization
      p.asHomogeneousIdeal.toIdeal.primeCompl) =
      Localization.localRingHom
        (ProjectiveSpectrum.comap f hf p).asHomogeneousIdeal.toIdeal
        p.asHomogeneousIdeal.toIdeal f rfl z.1 := by
  change Localization.localRingHom
      (ProjectiveSpectrum.comap f hf p).asHomogeneousIdeal.toIdeal
      p.asHomogeneousIdeal.toIdeal f rfl z.1 = _
  rfl

attribute [local irreducible] atDegMap

/-- Apply a graded ring homomorphism pointwise to a degree-`d` section on an open subset
of a projective spectrum. -/
noncomputable def comapTwistFun (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f) (d : ℤ)
    (U : Opens (ProjectiveSpectrum.top 𝒜)) (V : Opens (ProjectiveSpectrum.top ℬ))
    (hUV : V.1 ⊆ ProjectiveSpectrum.comap f hf ⁻¹' U.1)
    (s : ∀ x : U, atDeg 𝒜 d x.1) (y : V) : atDeg ℬ d y.1 :=
  TopCat.PrelocalPredicate.comapFunction (ProjectiveSpectrum.comap f hf)
    (fun p z ↦ (atDegMap f hf d p).toFun z) U V hUV s y

@[simp]
theorem comapTwistFun_val (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f) (d : ℤ)
    (U : Opens (ProjectiveSpectrum.top 𝒜)) (V : Opens (ProjectiveSpectrum.top ℬ))
    (hUV : V.1 ⊆ ProjectiveSpectrum.comap f hf ⁻¹' U.1)
    (s : ∀ x : U, atDeg 𝒜 d x.1) (y : V) :
    ((comapTwistFun f hf d U V hUV s y : atDeg ℬ d y.1) :
      Localization y.1.asHomogeneousIdeal.toIdeal.primeCompl) =
      Localization.localRingHom
        (ProjectiveSpectrum.comap f hf y.1).asHomogeneousIdeal.toIdeal
        y.1.asHomogeneousIdeal.toIdeal f rfl
        ((s ⟨ProjectiveSpectrum.comap f hf y.1, hUV y.2⟩).1) := by
  unfold comapTwistFun
  exact atDegMap_val f hf d y.1 _

/-- Applying a graded ring homomorphism to one homogeneous fraction gives a homogeneous
fraction of the same degree. -/
theorem isFraction_comapTwistFun
    (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f) (d : ℤ)
    (U : Opens (ProjectiveSpectrum.top 𝒜)) (V : Opens (ProjectiveSpectrum.top ℬ))
    (hUV : V.1 ⊆ ProjectiveSpectrum.comap f hf ⁻¹' U.1)
    (s : ∀ x : U, atDeg 𝒜 d x.1)
    (hs : IsFraction (𝒜 := 𝒜) (d := d) s) :
    IsFraction (𝒜 := ℬ) (d := d) (comapTwistFun f hf d U V hUV s) := by
  rcases hs with ⟨i, j, hij, r, t, ht, hfrac⟩
  have ht' : ∀ q : V, (f t : B) ∈ q.1.asHomogeneousIdeal.toIdeal.primeCompl :=
    fun q ↦ ht ⟨ProjectiveSpectrum.comap f hf q.1, hUV q.2⟩
  refine ⟨i, j, hij, f.gradedAddHom j r, f.gradedAddHom i t, ht', fun q ↦ ?_⟩
  specialize hfrac ⟨ProjectiveSpectrum.comap f hf q.1, hUV q.2⟩
  rw [comapTwistFun_val, hfrac, Localization.localRingHom_mk]
  rfl

/-- Applying a graded ring homomorphism to a locally homogeneous fraction again gives a
locally homogeneous fraction of the same degree. -/
theorem isLocallyFraction_comapTwistFun
    (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f) (d : ℤ)
    (U : Opens (ProjectiveSpectrum.top 𝒜)) (V : Opens (ProjectiveSpectrum.top ℬ))
    (hUV : V.1 ⊆ ProjectiveSpectrum.comap f hf ⁻¹' U.1)
    (s : ∀ x : U, atDeg 𝒜 d x.1) (hs : (isLocallyFraction 𝒜 d).pred s) :
    (isLocallyFraction ℬ d).pred (comapTwistFun f hf d U V hUV s) := by
  exact TopCat.PrelocalPredicate.sheafify_comapFunction
    (T := fun p : ProjectiveSpectrum.top 𝒜 ↦ atDeg 𝒜 d p)
    (T' := fun p : ProjectiveSpectrum.top ℬ ↦ atDeg ℬ d p)
    (g := ProjectiveSpectrum.comap f hf)
    (φ := fun p z ↦ (atDegMap f hf d p).toFun z)
    (P := isFractionPrelocal 𝒜 d) (P' := isFractionPrelocal ℬ d)
    (hmap := by
      intro U' V' hUV' s' h
      change IsFraction (𝒜 := ℬ) (d := d) (comapTwistFun f hf d U' V' hUV' s')
      exact isFraction_comapTwistFun f hf d U' V' hUV' s' h)
    U V hUV s hs

/-- The additive map on twist sections induced by a graded ring homomorphism. -/
noncomputable def comapTwistAddHom
    (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f) (d : ℤ)
    (U : Opens (ProjectiveSpectrum.top 𝒜)) (V : Opens (ProjectiveSpectrum.top ℬ))
    (hUV : V.1 ⊆ ProjectiveSpectrum.comap f hf ⁻¹' U.1) :
    (sheafInType 𝒜 d).1.obj (.op U) →+
      (sheafInType ℬ d).1.obj (.op V) where
  toFun s := ⟨comapTwistFun f hf d U V hUV s.1,
    isLocallyFraction_comapTwistFun f hf d U V hUV s.1 s.2⟩
  map_zero' := by
    refine Subtype.ext (funext fun y ↦ Subtype.ext ?_)
    have hval := comapTwistFun_val f hf d U V hUV
      (0 : (sheafInType 𝒜 d).1.obj (.op U)).1 y
    exact hval.trans (map_zero (Localization.localRingHom
      (ProjectiveSpectrum.comap f hf y.1).asHomogeneousIdeal.toIdeal
      y.1.asHomogeneousIdeal.toIdeal f.toRingHom rfl))
  map_add' s t := by
    refine Subtype.ext (funext fun y ↦ Subtype.ext ?_)
    let x : U := ⟨ProjectiveSpectrum.comap f hf y.1, hUV y.2⟩
    let φ : Localization
        (ProjectiveSpectrum.comap f hf y.1).asHomogeneousIdeal.toIdeal.primeCompl →+*
          Localization y.1.asHomogeneousIdeal.toIdeal.primeCompl := Localization.localRingHom
      (ProjectiveSpectrum.comap f hf y.1).asHomogeneousIdeal.toIdeal
      y.1.asHomogeneousIdeal.toIdeal f.toRingHom rfl
    have hst := comapTwistFun_val f hf d U V hUV (s + t).1 y
    have hs := comapTwistFun_val f hf d U V hUV s.1 y
    have ht := comapTwistFun_val f hf d U V hUV t.1 y
    exact hst.trans ((map_add φ (s.1 x).1 (t.1 x).1).trans
      (congrArg₂ (· + ·) hs.symm ht.symm))

@[simp]
theorem comapTwistAddHom_apply_val
    (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f) (d : ℤ)
    (U : Opens (ProjectiveSpectrum.top 𝒜)) (V : Opens (ProjectiveSpectrum.top ℬ))
    (hUV : V.1 ⊆ ProjectiveSpectrum.comap f hf ⁻¹' U.1)
    (s : (sheafInType 𝒜 d).1.obj (.op U)) (y : V) :
    (((comapTwistAddHom f hf d U V hUV) s).1 y :
      Localization y.1.asHomogeneousIdeal.toIdeal.primeCompl) =
      Localization.localRingHom
        (ProjectiveSpectrum.comap f hf y.1).asHomogeneousIdeal.toIdeal
        y.1.asHomogeneousIdeal.toIdeal f rfl
        ((s.1 ⟨ProjectiveSpectrum.comap f hf y.1, hUV y.2⟩).1) := by
  change ((comapTwistFun f hf d U V hUV s.1 y : atDeg ℬ d y.1) :
    Localization y.1.asHomogeneousIdeal.toIdeal.primeCompl) = _
  exact comapTwistFun_val f hf d U V hUV s.1 y

/-- The map from a twist to the pushforward of the corresponding twist induced by a graded
ring homomorphism. -/
noncomputable def twistToPushforwardComparison
    (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f) (d : ℤ) :
    twist 𝒜 d ⟶ (Scheme.Modules.pushforward (Proj.map f hf)).obj (twist ℬ d) where
  val := PresheafOfModules.homMk
    { app := fun U ↦ AddCommGrpCat.ofHom <| comapTwistAddHom f hf d U.unop
        ((Proj.map f hf) ⁻¹ᵁ U.unop) (by rfl)
      naturality := by
        intro U V i
        ext s y
        rfl }
    (by
      intro U r s
      refine Subtype.ext (funext fun y ↦ Subtype.ext ?_)
      let x : U.unop := ⟨ProjectiveSpectrum.comap f hf y.1, y.2⟩
      let φ : Localization
          (ProjectiveSpectrum.comap f hf y.1).asHomogeneousIdeal.toIdeal.primeCompl →+*
            Localization y.1.asHomogeneousIdeal.toIdeal.primeCompl :=
        Localization.localRingHom
          (ProjectiveSpectrum.comap f hf y.1).asHomogeneousIdeal.toIdeal
          y.1.asHomogeneousIdeal.toIdeal f.toRingHom rfl
      have hrs := comapTwistAddHom_apply_val f hf d U.unop
        ((Proj.map f hf) ⁻¹ᵁ U.unop) (by rfl) (r • s) y
      have hs := comapTwistAddHom_apply_val f hf d U.unop
        ((Proj.map f hf) ⁻¹ᵁ U.unop) (by rfl) s y
      have hr := HomogeneousLocalization.val_localRingHom
        (f := f)
        (I := (ProjectiveSpectrum.comap f hf y.1).asHomogeneousIdeal.toIdeal)
        (J := y.1.asHomogeneousIdeal.toIdeal) (hIJ := rfl) (r.1 x)
      exact hrs.trans ((map_mul φ (r.1 x).val (s.1 x).1).trans
        (congrArg₂ (· * ·) hr.symm hs.symm)) )

/-- The adjoint pullback comparison for twists induced by a graded ring homomorphism. -/
noncomputable def pullbackComparison
    (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f) (d : ℤ) :
    (Scheme.Modules.pullback (Proj.map f hf)).obj (twist 𝒜 d) ⟶ twist ℬ d :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (Proj.map f hf)).homEquiv _ _).symm
    (twistToPushforwardComparison f hf d)

/-- The graded-ring comparison carries the standard local basis `f₀ ^ d` of a twist
to the corresponding standard basis after applying the graded ring homomorphism. -/
theorem twistToPushforwardComparison_app_unitSection
    (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f) (d : ℤ) {f₀ : A} (hf₀ : f₀ ∈ 𝒜 1)
    (U : (Proj 𝒜).Opens)
    (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 f₀) :
    (twistToPushforwardComparison f hf d).app U
        (unitSection 𝒜 hf₀ d (.op U) hU) =
      unitSection ℬ
        (show f f₀ ∈ ℬ 1 from (f.gradedAddHom 1 ⟨f₀, hf₀⟩).2) d
        (.op ((Proj.map f hf) ⁻¹ᵁ U))
        (fun _ hy ↦ hU hy) := by
  dsimp only [twistToPushforwardComparison, Scheme.Modules.Hom.app,
    Scheme.Modules.presheaf, PresheafOfModules.homMk]
  refine Subtype.ext (funext fun y ↦ Subtype.ext ?_)
  have hmap := comapTwistAddHom_apply_val f hf d _ _ (by rfl)
    (unitSection 𝒜 hf₀ d (.op U) hU) y
  refine hmap.trans ?_
  change Localization.localRingHom
      (ProjectiveSpectrum.comap f hf y.1).asHomogeneousIdeal.toIdeal
      y.1.asHomogeneousIdeal.toIdeal f rfl
        (unitPow hf₀ (hU y.2) d).embed =
    (unitPow (f.gradedAddHom 1 ⟨f₀, hf₀⟩).2 _ d).embed
  unfold unitPow
  rw [HomogeneousLocalization.NumDenShift.embed_def,
    HomogeneousLocalization.NumDenShift.embed_def,
    Localization.localRingHom_mk]
  simp only [map_pow]
  congr

/-- The adjoint pullback comparison sends the pullback-unit image of a standard local
basis to the corresponding standard basis on the inverse-image basic open. -/
theorem pullbackComparison_app_unitSection
    (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f) (d : ℤ) {f₀ : A} (hf₀ : f₀ ∈ 𝒜 1)
    (U : (Proj 𝒜).Opens)
    (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 f₀) :
    (pullbackComparison f hf d).app ((Proj.map f hf) ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackPushforwardAdjunction
          (Proj.map f hf)).unit.app (twist 𝒜 d)).app U
            (unitSection 𝒜 hf₀ d (.op U) hU)) =
      unitSection ℬ
        (show f f₀ ∈ ℬ 1 from (f.gradedAddHom 1 ⟨f₀, hf₀⟩).2) d
        (.op ((Proj.map f hf) ⁻¹ᵁ U)) (fun _ hy ↦ hU hy) := by
  have htr :
      (Scheme.Modules.pullbackPushforwardAdjunction (Proj.map f hf)).homEquiv
        (twist 𝒜 d) (twist ℬ d) (pullbackComparison f hf d) =
          twistToPushforwardComparison f hf d := by
    rw [pullbackComparison, Equiv.apply_symm_apply]
  rw [(Scheme.Modules.pullbackPushforwardAdjunction
    (Proj.map f hf)).homEquiv_unit] at htr
  have happ := CategoryTheory.congr_fun
    (congrArg (fun (k : twist 𝒜 d ⟶
        (Scheme.Modules.pushforward (Proj.map f hf)).obj (twist ℬ d)) ↦ k.app U) htr)
    (unitSection 𝒜 hf₀ d (.op U) hU)
  exact happ.trans (twistToPushforwardComparison_app_unitSection f hf d hf₀ U hU)

section LocalTrivialization

variable {f₀ : A} (hf₀ : f₀ ∈ 𝒜 1) (d₀ : ℤ)

/-- On a degree-one basic open, the twisting sheaf is canonically trivialized by the
homogeneous section `f₀ ^ d₀`. -/
noncomputable def restrictTwistIsoUnit :
    (Scheme.Modules.restrictFunctor (Proj.basicOpen 𝒜 f₀).ι).obj (twist 𝒜 d₀) ≅
      SheafOfModules.unit (Proj.basicOpen 𝒜 f₀).toScheme.ringCatSheaf := by
  let j := (Proj.basicOpen 𝒜 f₀).ι
  let e : (Scheme.Modules.restrictFunctor j).obj (twist 𝒜 d₀) ≅
      (Scheme.Modules.restrictFunctor j).obj
        (SheafOfModules.unit (Proj 𝒜).ringCatSheaf) :=
    (SheafOfModules.fullyFaithfulForget _).preimageIso <|
      PresheafOfModules.isoMk
        (fun U ↦
          let hU : j ''ᵁ U.unop ≤ Proj.basicOpen 𝒜 f₀ :=
            (Proj.basicOpen 𝒜 f₀).ι_image_le U.unop
          let E := unitSectionEquiv 𝒜 hf₀ d₀ (.op (j ''ᵁ U.unop)) hU
          ModuleCat.isoMk E.symm.toAddEquiv.toAddCommGrpIso (by
            intro r
            ext s
            exact (E.symm.map_smul ((j.appIso U.unop).inv r) s).symm))
        (by
          intro U V i
          ext s
          let hU : j ''ᵁ U.unop ≤ Proj.basicOpen 𝒜 f₀ :=
            (Proj.basicOpen 𝒜 f₀).ι_image_le U.unop
          let hV : j ''ᵁ V.unop ≤ Proj.basicOpen 𝒜 f₀ :=
            (Proj.basicOpen 𝒜 f₀).ι_image_le V.unop
          let hVU : j ''ᵁ V.unop ≤ j ''ᵁ U.unop :=
            Scheme.Hom.image_mono j (leOfHom i.unop)
          let EU := unitSectionEquiv 𝒜 hf₀ d₀ (.op (j ''ᵁ U.unop)) hU
          let EV := unitSectionEquiv 𝒜 hf₀ d₀ (.op (j ''ᵁ V.unop)) hV
          change EV.symm ((sheafInType 𝒜 d₀).1.map (homOfLE hVU).op s) =
            (Proj 𝒜).presheaf.map (homOfLE hVU).op (EU.symm s)
          apply EV.injective
          rw [EV.apply_symm_apply]
          have hs := congrArg (fun t : (sheafInType 𝒜 d₀).1.obj
              (.op (j ''ᵁ U.unop)) ↦
              (sheafInType 𝒜 d₀).1.map (homOfLE hVU).op t)
            (EU.apply_symm_apply s)
          exact hs.symm)
  exact e ≪≫ Scheme.Modules.restrictUnitIso j

end LocalTrivialization

/-- The pullback of a twist along an arbitrary scheme morphism to `Proj`, restricted to
the inverse image of a degree-one basic open, is canonically trivial. -/
noncomputable def restrictPullbackTwistIsoUnitOfHom
    (g : X ⟶ Proj 𝒜) (d : ℤ) {f₀ : A} (hf₀ : f₀ ∈ 𝒜 1) :
    (Scheme.Modules.restrictFunctor
      (g ⁻¹ᵁ Proj.basicOpen 𝒜 f₀).ι).obj
        ((Scheme.Modules.pullback g).obj (twist 𝒜 d)) ≅
      SheafOfModules.unit
        (g ⁻¹ᵁ Proj.basicOpen 𝒜 f₀).toScheme.ringCatSheaf := by
  let g' := g.resLE (Proj.basicOpen 𝒜 f₀)
    (g ⁻¹ᵁ Proj.basicOpen 𝒜 f₀) le_rfl
  letI : IsIso (SheafOfModules.pullbackObjUnitToUnit g'.toRingCatSheafHom) :=
    isIso_pullbackObjUnitToUnit g'
  exact Scheme.Modules.restrictPullbackIsoPreimage g
      (Proj.basicOpen 𝒜 f₀) (twist 𝒜 d) ≪≫
    (Scheme.Modules.pullback g').mapIso
        (restrictTwistIsoUnit hf₀ d) ≪≫
    asIso (SheafOfModules.pullbackObjUnitToUnit g'.toRingCatSheafHom)

/-- The pullback of a twist, restricted to the inverse image of a degree-one basic open,
is canonically trivial. -/
noncomputable def restrictPullbackTwistIsoUnit
    (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f) (d : ℤ) {f₀ : A} (hf₀ : f₀ ∈ 𝒜 1) :
    (Scheme.Modules.restrictFunctor
      ((Proj.map f hf) ⁻¹ᵁ Proj.basicOpen 𝒜 f₀).ι).obj
        ((Scheme.Modules.pullback (Proj.map f hf)).obj (twist 𝒜 d)) ≅
      SheafOfModules.unit
        ((Proj.map f hf) ⁻¹ᵁ Proj.basicOpen 𝒜 f₀).toScheme.ringCatSheaf := by
  let g := (Proj.map f hf).resLE (Proj.basicOpen 𝒜 f₀)
    ((Proj.map f hf) ⁻¹ᵁ Proj.basicOpen 𝒜 f₀) le_rfl
  letI : IsIso (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom) :=
    isIso_pullbackObjUnitToUnit g
  exact Scheme.Modules.restrictPullbackIsoPreimage (Proj.map f hf)
      (Proj.basicOpen 𝒜 f₀) (twist 𝒜 d) ≪≫
    (Scheme.Modules.pullback g).mapIso
        (restrictTwistIsoUnit hf₀ d) ≪≫
    asIso (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom)

/-- The target twist on the inverse image of a degree-one basic open is trivialized by
the image of the same homogeneous element. -/
noncomputable def restrictTargetTwistIsoUnit
    (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f) (d : ℤ) {f₀ : A} (hf₀ : f₀ ∈ 𝒜 1) :
    (Scheme.Modules.restrictFunctor
      ((Proj.map f hf) ⁻¹ᵁ Proj.basicOpen 𝒜 f₀).ι).obj (twist ℬ d) ≅
      SheafOfModules.unit
        ((Proj.map f hf) ⁻¹ᵁ Proj.basicOpen 𝒜 f₀).toScheme.ringCatSheaf :=
  restrictTwistIsoUnit (f.gradedAddHom 1 ⟨f₀, hf₀⟩).2 d

/-- The pullback-unit image of the standard basis, restricted to the inverse-image
degree-one basic open. -/
noncomputable def restrictPullbackUnitSection
    (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f) (d : ℤ) {f₀ : A} (hf₀ : f₀ ∈ 𝒜 1) :
    Γ((Scheme.Modules.restrictFunctor
      ((Proj.map f hf) ⁻¹ᵁ Proj.basicOpen 𝒜 f₀).ι).obj
        ((Scheme.Modules.pullback (Proj.map f hf)).obj (twist 𝒜 d)), ⊤) :=
  let V := (Proj.map f hf) ⁻¹ᵁ Proj.basicOpen 𝒜 f₀
  let M := (Scheme.Modules.pullback (Proj.map f hf)).obj (twist 𝒜 d)
  M.presheaf.map (eqToHom V.ι_image_top).op
    (((Scheme.Modules.pullbackPushforwardAdjunction (Proj.map f hf)).unit.app
      (twist 𝒜 d)).app (Proj.basicOpen 𝒜 f₀)
        (unitSection 𝒜 hf₀ d (.op (Proj.basicOpen 𝒜 f₀)) le_rfl))

/-- The standard basis of the target twist on the inverse-image degree-one basic open. -/
noncomputable def restrictTargetUnitSection
    (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f) (d : ℤ) {f₀ : A} (hf₀ : f₀ ∈ 𝒜 1) :
    Γ((Scheme.Modules.restrictFunctor
      ((Proj.map f hf) ⁻¹ᵁ Proj.basicOpen 𝒜 f₀).ι).obj (twist ℬ d), ⊤) :=
  let V := (Proj.map f hf) ⁻¹ᵁ Proj.basicOpen 𝒜 f₀
  unitSection ℬ (f.gradedAddHom 1 ⟨f₀, hf₀⟩).2 d (.op (V.ι ''ᵁ ⊤)) (by
    rw [V.ι_image_top]
    rfl)

/-- The restricted pullback comparison carries the restricted standard basis to the
standard basis of the target twist. -/
theorem restrictPullbackComparison_app_unitSection
    (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f) (d : ℤ) {f₀ : A} (hf₀ : f₀ ∈ 𝒜 1) :
    ((Scheme.Modules.restrictFunctor
      ((Proj.map f hf) ⁻¹ᵁ Proj.basicOpen 𝒜 f₀).ι).map
        (pullbackComparison f hf d)).app ⊤
          (restrictPullbackUnitSection f hf d hf₀) =
      restrictTargetUnitSection f hf d hf₀ := by
  let V := (Proj.map f hf) ⁻¹ᵁ Proj.basicOpen 𝒜 f₀
  change (pullbackComparison f hf d).app (V.ι ''ᵁ ⊤)
      (((Scheme.Modules.pullback (Proj.map f hf)).obj (twist 𝒜 d)).presheaf.map
        (eqToHom V.ι_image_top).op
        (((Scheme.Modules.pullbackPushforwardAdjunction (Proj.map f hf)).unit.app
          (twist 𝒜 d)).app (Proj.basicOpen 𝒜 f₀)
            (unitSection 𝒜 hf₀ d (.op (Proj.basicOpen 𝒜 f₀)) le_rfl))) = _
  let b := (((Scheme.Modules.pullbackPushforwardAdjunction (Proj.map f hf)).unit.app
    (twist 𝒜 d)).app (Proj.basicOpen 𝒜 f₀)
      (unitSection 𝒜 hf₀ d (.op (Proj.basicOpen 𝒜 f₀)) le_rfl))
  have hnat := ConcreteCategory.congr_hom
    ((pullbackComparison f hf d).val.naturality (eqToHom V.ι_image_top).op) b
  simp only [ConcreteCategory.comp_apply] at hnat
  have hb : (pullbackComparison f hf d).val.app (.op V) b =
      unitSection ℬ (f.gradedAddHom 1 ⟨f₀, hf₀⟩).2 d (.op V) (by rfl) :=
    pullbackComparison_app_unitSection f hf d hf₀
      (Proj.basicOpen 𝒜 f₀) le_rfl
  rw [hb] at hnat
  exact hnat.trans (by rfl)

/-- The target local trivialization sends its standard basis to `1`. -/
@[simp]
theorem restrictTargetTwistIsoUnit_hom_app_top_unitSection
    (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f) (d : ℤ) {f₀ : A} (hf₀ : f₀ ∈ 𝒜 1) :
    (restrictTargetTwistIsoUnit f hf d hf₀).hom.app ⊤
      (restrictTargetUnitSection f hf d hf₀) =
        (show Γ(((Proj.map f hf) ⁻¹ᵁ Proj.basicOpen 𝒜 f₀).toScheme, ⊤) from 1) := by
  let V := Proj.basicOpen ℬ (f f₀)
  let hf₀' : f f₀ ∈ ℬ 1 := (f.gradedAddHom 1 ⟨f₀, hf₀⟩).2
  have hbasis :
      (unitSectionEquiv ℬ hf₀' d (.op (V.ι ''ᵁ ⊤)) (by
        rw [V.ι_image_top]
        exact le_rfl)).symm
          (unitSection ℬ hf₀' d (.op (V.ι ''ᵁ ⊤)) (by
            rw [V.ι_image_top]
            exact le_rfl)) = 1 := by
    rw [LinearEquiv.symm_apply_eq]
    exact (unitSectionEquiv_one ℬ hf₀' d _ _).symm
  change (V.ι.appIso ⊤).hom
      ((unitSectionEquiv ℬ hf₀' d (.op (V.ι ''ᵁ ⊤)) (by
        rw [V.ι_image_top]
        exact le_rfl)).symm
          (unitSection ℬ hf₀' d (.op (V.ι ''ᵁ ⊤)) (by
            rw [V.ι_image_top]
            exact le_rfl))) = 1
  rw [hbasis]
  exact map_one _

/-- The base-change comparison on a degree-one basic open, normalized by the standard
trivializations on source and target. -/
noncomputable def normalizedRestrictPullbackComparison
    (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f) (d : ℤ) {f₀ : A} (hf₀ : f₀ ∈ 𝒜 1) :
    SheafOfModules.unit
        ((Proj.map f hf) ⁻¹ᵁ Proj.basicOpen 𝒜 f₀).toScheme.ringCatSheaf ⟶
      SheafOfModules.unit
        ((Proj.map f hf) ⁻¹ᵁ Proj.basicOpen 𝒜 f₀).toScheme.ringCatSheaf :=
  (restrictPullbackTwistIsoUnit f hf d hf₀).inv ≫
    (Scheme.Modules.restrictFunctor
      ((Proj.map f hf) ⁻¹ᵁ Proj.basicOpen 𝒜 f₀).ι).map
        (pullbackComparison f hf d) ≫
    (restrictTargetTwistIsoUnit f hf d hf₀).hom

/-- A global section which the normalized local comparison sends to `1`. -/
noncomputable def normalizedRestrictPullbackComparisonPreimageOne
    (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f) (d : ℤ) {f₀ : A} (hf₀ : f₀ ∈ 𝒜 1) :
    Γ(((Proj.map f hf) ⁻¹ᵁ Proj.basicOpen 𝒜 f₀).toScheme, ⊤) :=
  (restrictPullbackTwistIsoUnit f hf d hf₀).hom.app ⊤
    (restrictPullbackUnitSection f hf d hf₀)

/-- The normalized local comparison sends its distinguished preimage to `1`. -/
theorem normalizedRestrictPullbackComparison_app_preimageOne
    (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f) (d : ℤ) {f₀ : A} (hf₀ : f₀ ∈ 𝒜 1) :
    Scheme.Modules.Hom.app (normalizedRestrictPullbackComparison f hf d hf₀) ⊤
        (normalizedRestrictPullbackComparisonPreimageOne f hf d hf₀) =
      (show Γ(((Proj.map f hf) ⁻¹ᵁ Proj.basicOpen 𝒜 f₀).toScheme, ⊤) from 1) := by
  change (restrictTargetTwistIsoUnit f hf d hf₀).hom.app ⊤
      (((Scheme.Modules.restrictFunctor
        ((Proj.map f hf) ⁻¹ᵁ Proj.basicOpen 𝒜 f₀).ι).map
          (pullbackComparison f hf d)).app ⊤
        ((restrictPullbackTwistIsoUnit f hf d hf₀).inv.app ⊤
          ((restrictPullbackTwistIsoUnit f hf d hf₀).hom.app ⊤
            (restrictPullbackUnitSection f hf d hf₀)))) = _
  have hcancel :
      (restrictPullbackTwistIsoUnit f hf d hf₀).inv.app ⊤
          ((restrictPullbackTwistIsoUnit f hf d hf₀).hom.app ⊤
            (restrictPullbackUnitSection f hf d hf₀)) =
        restrictPullbackUnitSection f hf d hf₀ := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
      Iso.hom_inv_id, Scheme.Modules.Hom.id_app]
    rfl
  rw [hcancel, restrictPullbackComparison_app_unitSection,
    restrictTargetTwistIsoUnit_hom_app_top_unitSection]

/-- On the inverse image of a degree-one basic open, the pullback comparison is an
isomorphism after normalizing both sides by their standard bases. -/
theorem normalizedRestrictPullbackComparison_isIso
    (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f) (d : ℤ) {f₀ : A} (hf₀ : f₀ ∈ 𝒜 1) :
    IsIso (normalizedRestrictPullbackComparison f hf d hf₀) :=
  Scheme.Modules.unit_endomorphism_isIso_of_exists_preimage_one
    (normalizedRestrictPullbackComparison f hf d hf₀)
    (normalizedRestrictPullbackComparisonPreimageOne f hf d hf₀)
    (normalizedRestrictPullbackComparison_app_preimageOne f hf d hf₀)

/-- The pullback comparison is an isomorphism after restriction to the inverse image of
any degree-one basic open. -/
theorem restrictPullbackComparison_isIso
    (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f) (d : ℤ) {f₀ : A} (hf₀ : f₀ ∈ 𝒜 1) :
    IsIso ((Scheme.Modules.restrictFunctor
      ((Proj.map f hf) ⁻¹ᵁ Proj.basicOpen 𝒜 f₀).ι).map
        (pullbackComparison f hf d)) := by
  let a := (restrictPullbackTwistIsoUnit f hf d hf₀).inv
  let b := (Scheme.Modules.restrictFunctor
    ((Proj.map f hf) ⁻¹ᵁ Proj.basicOpen 𝒜 f₀).ι).map
      (pullbackComparison f hf d)
  let c := (restrictTargetTwistIsoUnit f hf d hf₀).hom
  have hnorm := normalizedRestrictPullbackComparison_isIso f hf d hf₀
  change IsIso (a ≫ b ≫ c) at hnorm
  letI : IsIso (a ≫ b ≫ c) := hnorm
  letI : IsIso c := inferInstance
  letI : IsIso (a ≫ b) := IsIso.of_isIso_comp_right (a ≫ b) c
  letI : IsIso a := inferInstance
  exact IsIso.of_isIso_comp_left a b

section Polynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R S : Type u} [CommRing R] [CommRing S] (i : Type) (g : R →+* S)

/-- The pullback comparison for polynomial twists is an isomorphism. -/
theorem polynomialPullbackComparison_isIso (d : ℤ) :
    IsIso (pullbackComparison (MvPolynomial.mapGradedRingHom (ι := i) g)
      (MvPolynomial.irrelevant_le_map_mapGradedRingHom g) d) := by
  let 𝒜 := MvPolynomial.homogeneousSubmodule i R
  let ℬ := MvPolynomial.homogeneousSubmodule i S
  let α := pullbackComparison (MvPolynomial.mapGradedRingHom (ι := i) g)
    (MvPolynomial.irrelevant_le_map_mapGradedRingHom g) d
  refine Scheme.Modules.isIso_of_restrict_iSup_eq_top α
    (fun j ↦ Proj.basicOpen ℬ (MvPolynomial.X j)) ?_ ?_
  · exact Proj.iSup_basicOpen_eq_top ℬ (MvPolynomial.X : i → MvPolynomial i S)
      (MvPolynomial.irrelevant_toIdeal_le_idealOfVars i S)
  · intro j
    let hj : MvPolynomial.X j ∈ 𝒜 1 :=
      (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
        (MvPolynomial.isHomogeneous_X R j)
    have hlocal := restrictPullbackComparison_isIso
      (MvPolynomial.mapGradedRingHom (ι := i) g)
      (MvPolynomial.irrelevant_le_map_mapGradedRingHom g) d hj
    have hmap : (MvPolynomial.mapGradedRingHom (ι := i) g) (MvPolynomial.X j) =
        MvPolynomial.X j := MvPolynomial.mapGradedRingHom_X g j
    rw [Proj.map_preimage_basicOpen, hmap] at hlocal
    exact hlocal

/-- Coefficient change pulls the polynomial twisting sheaf `𝒪(d)` back to the
corresponding twisting sheaf over the target coefficient ring. -/
noncomputable def polynomialPullbackIso (d : ℤ) :
    (Scheme.Modules.pullback (Proj.polynomialMap i g)).obj
        (twist (MvPolynomial.homogeneousSubmodule i R) d) ≅
      twist (MvPolynomial.homogeneousSubmodule i S) d := by
  letI : IsIso (pullbackComparison (MvPolynomial.mapGradedRingHom (ι := i) g)
      (MvPolynomial.irrelevant_le_map_mapGradedRingHom g) d) :=
    polynomialPullbackComparison_isIso i g d
  exact asIso (pullbackComparison (MvPolynomial.mapGradedRingHom (ι := i) g)
    (MvPolynomial.irrelevant_le_map_mapGradedRingHom g) d)

/-- The standard coordinate basic opens cover polynomial projective spectrum. -/
theorem polynomialCoordinateCover_iSup_eq_top :
    ⨆ j : i, Proj.basicOpen (MvPolynomial.homogeneousSubmodule i R)
      (MvPolynomial.X j) = ⊤ :=
  Proj.iSup_basicOpen_eq_top (MvPolynomial.homogeneousSubmodule i R)
    (MvPolynomial.X : i → MvPolynomial i R)
    (MvPolynomial.irrelevant_toIdeal_le_idealOfVars i R)

/-- A polynomial twisting sheaf is finitely presented. -/
theorem polynomialTwist_isFinitePresentation (d : ℤ) :
    (twist (MvPolynomial.homogeneousSubmodule i R) d).IsFinitePresentation := by
  let 𝒜 := MvPolynomial.homogeneousSubmodule i R
  let U (j : ULift.{u} i) := Proj.basicOpen 𝒜 (MvPolynomial.X j.down)
  let P (j : ULift.{u} i) : SheafOfModules.Presentation
      ((twist 𝒜 d).restrict (U j).ι) :=
    (Scheme.Modules.unitPresentation (U j).toScheme).ofIsIso
      (restrictTwistIsoUnit
        ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr
          (MvPolynomial.isHomogeneous_X R j.down)) d).inv
  letI (j : ULift.{u} i) : (P j).IsFinite := by
    dsimp [P]
    infer_instance
  have hU : ⨆ j, U j = ⊤ := by
    rw [iSup_ulift]
    exact polynomialCoordinateCover_iSup_eq_top (R := R) i
  exact Scheme.Modules.isFinitePresentation_of_restrictPresentation_iSup_eq_top
    (twist 𝒜 d) U hU P

/-- A polynomial twisting sheaf is quasicoherent. -/
theorem polynomialTwist_isQuasicoherent (d : ℤ) :
    (twist (MvPolynomial.homogeneousSubmodule i R) d).IsQuasicoherent := by
  letI : (twist (MvPolynomial.homogeneousSubmodule i R) d).IsFinitePresentation :=
    polynomialTwist_isFinitePresentation (R := R) i d
  infer_instance

/-- A finite coproduct of polynomial twists is finitely presented. -/
theorem polynomialTwistCoproduct_isFinitePresentation
    (J : Type u) [Finite J] (d : J → ℤ) :
    (∐ fun j : J ↦ twist (MvPolynomial.homogeneousSubmodule i R) (d j)).IsFinitePresentation := by
  let 𝒜 := MvPolynomial.homogeneousSubmodule i R
  let M := ∐ fun j : J ↦ twist 𝒜 (d j)
  let U (k : ULift.{u} i) := Proj.basicOpen 𝒜 (MvPolynomial.X k.down)
  let hX (k : ULift.{u} i) : MvPolynomial.X k.down ∈ 𝒜 1 :=
    (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
      (MvPolynomial.isHomogeneous_X R k.down)
  let e (k : ULift.{u} i) : M.restrict (U k).ι ≅
      SheafOfModules.free (R := (U k).toScheme.ringCatSheaf) J :=
    PreservesCoproduct.iso (Scheme.Modules.restrictFunctor (U k).ι)
        (fun j : J ↦ twist 𝒜 (d j)) ≪≫
      Sigma.mapIso (fun j ↦ restrictTwistIsoUnit (hX k) (d j))
  let P (k : ULift.{u} i) : SheafOfModules.Presentation (M.restrict (U k).ι) :=
    (Scheme.Modules.freePresentation (X := (U k).toScheme) J).ofIsIso (e k).inv
  letI (k : ULift.{u} i) : (P k).IsFinite := by
    dsimp [P]
    infer_instance
  have hU : ⨆ k, U k = ⊤ := by
    rw [iSup_ulift]
    exact polynomialCoordinateCover_iSup_eq_top (R := R) i
  exact Scheme.Modules.isFinitePresentation_of_restrictPresentation_iSup_eq_top
    M U hU P

/-- A finite coproduct of polynomial twists is quasicoherent. -/
theorem polynomialTwistCoproduct_isQuasicoherent
    (J : Type u) [Finite J] (d : J → ℤ) :
    (∐ fun j : J ↦ twist (MvPolynomial.homogeneousSubmodule i R) (d j)).IsQuasicoherent := by
  letI : (∐ fun j : J ↦
      twist (MvPolynomial.homogeneousSubmodule i R) (d j)).IsFinitePresentation :=
    polynomialTwistCoproduct_isFinitePresentation (R := R) i J d
  infer_instance

/-- The finite free sum of `r` copies of one polynomial twist is finitely presented. -/
theorem polynomialTwistedFree_isFinitePresentation (r : ℕ) (d : ℤ) :
    (∐ fun _ : ULift.{u} (Fin r) ↦
      twist (MvPolynomial.homogeneousSubmodule i R) d).IsFinitePresentation :=
  polynomialTwistCoproduct_isFinitePresentation (R := R) i (ULift.{u} (Fin r)) (fun _ ↦ d)

/-- The finite free sum of `r` copies of one polynomial twist is quasicoherent. -/
theorem polynomialTwistedFree_isQuasicoherent (r : ℕ) (d : ℤ) :
    (∐ fun _ : ULift.{u} (Fin r) ↦
      twist (MvPolynomial.homogeneousSubmodule i R) d).IsQuasicoherent :=
  polynomialTwistCoproduct_isQuasicoherent (R := R) i (ULift.{u} (Fin r)) (fun _ ↦ d)

/-- The pullback of a polynomial twist along an arbitrary scheme morphism is finitely
presented. -/
theorem pullbackPolynomialTwist_isFinitePresentation {X : Scheme.{u}}
    (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule i R)) (d : ℤ) :
    ((Scheme.Modules.pullback f).obj
      (twist (MvPolynomial.homogeneousSubmodule i R) d)).IsFinitePresentation :=
  Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation f
    (polynomialTwist_isFinitePresentation (R := R) i d)

/-- The pullback of a polynomial twist along an arbitrary scheme morphism is
quasicoherent. -/
theorem pullbackPolynomialTwist_isQuasicoherent {X : Scheme.{u}}
    (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule i R)) (d : ℤ) :
    ((Scheme.Modules.pullback f).obj
      (twist (MvPolynomial.homogeneousSubmodule i R) d)).IsQuasicoherent := by
  letI : ((Scheme.Modules.pullback f).obj
      (twist (MvPolynomial.homogeneousSubmodule i R) d)).IsFinitePresentation :=
    pullbackPolynomialTwist_isFinitePresentation (R := R) i f d
  infer_instance

/-- A finite coproduct of polynomial twists remains finitely presented after pulling
each summand back along an arbitrary scheme morphism. -/
theorem pullbackPolynomialTwistCoproduct_isFinitePresentation {X : Scheme.{u}}
    (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule i R))
    (J : Type u) [Finite J] (d : J → ℤ) :
    (∐ fun j : J ↦ (Scheme.Modules.pullback f).obj
      (twist (MvPolynomial.homogeneousSubmodule i R) (d j))).IsFinitePresentation := by
  have hsource : (∐ fun j : J ↦
      twist (MvPolynomial.homogeneousSubmodule i R) (d j)).IsFinitePresentation :=
    polynomialTwistCoproduct_isFinitePresentation (R := R) i J d
  have hpull : ((Scheme.Modules.pullback f).obj (∐ fun j : J ↦
      twist (MvPolynomial.homogeneousSubmodule i R) (d j))).IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation f hsource
  exact ObjectProperty.prop_of_iso
    (P := SheafOfModules.isFinitePresentation X.ringCatSheaf)
    (PreservesCoproduct.iso (Scheme.Modules.pullback f)
      (fun j : J ↦ twist (MvPolynomial.homogeneousSubmodule i R) (d j))) hpull

/-- A finite coproduct of polynomial twists remains quasicoherent after pulling each
summand back along an arbitrary scheme morphism. -/
theorem pullbackPolynomialTwistCoproduct_isQuasicoherent {X : Scheme.{u}}
    (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule i R))
    (J : Type u) [Finite J] (d : J → ℤ) :
    (∐ fun j : J ↦ (Scheme.Modules.pullback f).obj
      (twist (MvPolynomial.homogeneousSubmodule i R) (d j))).IsQuasicoherent := by
  letI : (∐ fun j : J ↦ (Scheme.Modules.pullback f).obj
      (twist (MvPolynomial.homogeneousSubmodule i R) (d j))).IsFinitePresentation :=
    pullbackPolynomialTwistCoproduct_isFinitePresentation (R := R) i f J d
  infer_instance

/-- The finite free sum of `r` pulled-back copies of one polynomial twist is finitely
presented. -/
theorem pullbackPolynomialTwistedFree_isFinitePresentation {X : Scheme.{u}}
    (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule i R)) (r : ℕ) (d : ℤ) :
    (∐ fun _ : ULift.{u} (Fin r) ↦ (Scheme.Modules.pullback f).obj
      (twist (MvPolynomial.homogeneousSubmodule i R) d)).IsFinitePresentation :=
  pullbackPolynomialTwistCoproduct_isFinitePresentation (R := R) i f
    (ULift.{u} (Fin r)) (fun _ ↦ d)

/-- The finite free sum of `r` pulled-back copies of one polynomial twist is
quasicoherent. -/
theorem pullbackPolynomialTwistedFree_isQuasicoherent {X : Scheme.{u}}
    (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule i R)) (r : ℕ) (d : ℤ) :
    (∐ fun _ : ULift.{u} (Fin r) ↦ (Scheme.Modules.pullback f).obj
      (twist (MvPolynomial.homogeneousSubmodule i R) d)).IsQuasicoherent :=
  pullbackPolynomialTwistCoproduct_isQuasicoherent (R := R) i f
    (ULift.{u} (Fin r)) (fun _ ↦ d)

/-- Coefficient change commutes with an arbitrary coproduct of polynomial twists. -/
noncomputable def polynomialPullbackCoproductIso (J : Type u) (d : J → ℤ) :
    (Scheme.Modules.pullback (Proj.polynomialMap i g)).obj
        (∐ fun j : J ↦ twist (MvPolynomial.homogeneousSubmodule i R) (d j)) ≅
      ∐ fun j : J ↦ twist (MvPolynomial.homogeneousSubmodule i S) (d j) :=
  PreservesCoproduct.iso (Scheme.Modules.pullback (Proj.polynomialMap i g))
      (fun j : J ↦ twist (MvPolynomial.homogeneousSubmodule i R) (d j)) ≪≫
    Sigma.mapIso (fun j ↦ polynomialPullbackIso i g (d j))

/-- Coefficient change commutes with the finite free sum of `r` copies of one
polynomial twist. -/
noncomputable def polynomialPullbackTwistedFreeIso (r : ℕ) (d : ℤ) :
    (Scheme.Modules.pullback (Proj.polynomialMap i g)).obj
        (∐ fun _ : ULift.{u} (Fin r) ↦
          twist (MvPolynomial.homogeneousSubmodule i R) d) ≅
      ∐ fun _ : ULift.{u} (Fin r) ↦
        twist (MvPolynomial.homogeneousSubmodule i S) d :=
  polynomialPullbackCoproductIso i g (ULift.{u} (Fin r)) (fun _ ↦ d)

end Polynomial

end ProjectiveSpectrum.Twist
