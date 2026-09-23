module

public import StacksAndModuli.API.SheafCohomologyModule
public import StacksAndModuli.API.PullbackAdjoint
public import StacksAndModuli.API.SchemeModulesGlobalSectionsIso
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
public import Mathlib.Topology.Sheaves.Functors

/-!
# Sheaf cohomology under isomorphisms of schemes

This file transports abelian sheaves, and in particular the underlying abelian
structure sheaf, across an isomorphism of schemes.  The resulting equivalence
identifies structure-sheaf cohomology and respects the action of a common base
ring.

## Main definitions and results

* `AlgebraicGeometry.Scheme.sheafEquivOfIso`: the induced equivalence of abelian sheaves.
* `AlgebraicGeometry.Scheme.structureCohomologyAddEquivOfIso`: the additive equivalence on
  structure-sheaf cohomology.
* `AlgebraicGeometry.Scheme.structureCohomologyLinearEquivOfOverIso`: its linear form over a
  common field.
* `AlgebraicGeometry.Scheme.Modules.h_structureModule_eq_of_overIso`: invariance of
  cohomology dimensions over that field.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
  TopologicalSpace Opposite

universe u

namespace CategoryTheory.Abelian.Ext

variable {C : Type (u + 1)} [Category.{u} C] [Abelian C]
  [HasExt.{u} C]

/-- Isomorphisms in both variables induce an additive equivalence of `Ext`
groups. -/
noncomputable def isoAddEquiv {X X' Y Y' : C} (eX : X ≅ X')
    (eY : Y ≅ Y') (n : ℕ) : Ext X Y n ≃+ Ext X' Y' n :=
  (((extFunctor (C := C) n).mapIso eX.symm.op).app Y ≪≫
      (extFunctorObj X' n).mapIso eY).addCommGroupIsoToAddEquiv

@[simp]
lemma isoAddEquiv_apply {X X' Y Y' : C} (eX : X ≅ X')
    (eY : Y ≅ Y') (n : ℕ) (x : Ext X Y n) :
    isoAddEquiv eX eY n x =
      ((Ext.mk₀ eX.inv).comp x (zero_add n)).comp
        (Ext.mk₀ eY.hom) (add_zero n) := rfl

end CategoryTheory.Abelian.Ext

namespace AlgebraicGeometry.Scheme

/-- The equivalence between the categories of open subsets induced by an
isomorphism of schemes, oriented from source opens to target opens. -/
noncomputable def opensEquivOfIso {X Y : Scheme.{u}} (e : X ≅ Y) :
    Opens X ≌ Opens Y :=
  (Opens.mapMapIso (forgetToTop.mapIso e)).symm

set_option linter.style.haveILetI false in
/-- The inverse of `opensEquivOfIso` is a dense morphism of the associated
open-set sites. -/
noncomputable instance opensEquivOfIso_inverse_isDenseSubsite
    {X Y : Scheme.{u}} (e : X ≅ Y) :
    (opensEquivOfIso e).inverse.IsDenseSubsite
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) := by
  let E := opensEquivOfIso e
  let H : (X : TopCat.{u}) ≅ (Y : TopCat.{u}) := forgetToTop.mapIso e
  let JX := Opens.grothendieckTopology X
  let JY := Opens.grothendieckTopology Y
  letI : E.functor.IsCocontinuous JX JY :=
    (E.toAdjunction.isCocontinuous_iff_coverPreserving JX JY).mpr
      (coverPreserving_opens_map H.hom)
  letI : E.inverse.IsCocontinuous JY JX :=
    (E.symm.toAdjunction.isCocontinuous_iff_coverPreserving JY JX).mpr
      (coverPreserving_opens_map H.inv)
  exact E.isDenseSubsite_inverse_of_isCocontinuous JX JY

/-- The equivalence between the categories of abelian sheaves induced by an
isomorphism of schemes.  Its forward functor is pushforward along the underlying
homeomorphism. -/
noncomputable def sheafEquivOfIso {X Y : Scheme.{u}} (e : X ≅ Y) :
    TopCat.Sheaf AddCommGrpCat.{u} X ≌ TopCat.Sheaf AddCommGrpCat.{u} Y := by
  exact (opensEquivOfIso e).sheafCongr
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
      AddCommGrpCat.{u}

/-- The forward functor of `sheafEquivOfIso` is the usual pushforward of
abelian sheaves along the underlying continuous map. -/
theorem sheafEquivOfIso_functor_eq {X Y : Scheme.{u}} (e : X ≅ Y) :
    (sheafEquivOfIso e).functor =
      TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom.base := rfl

noncomputable instance sheafEquivOfIso_functor_additive
    {X Y : Scheme.{u}} (e : X ≅ Y) :
    (sheafEquivOfIso e).functor.Additive := ⟨by intros; rfl⟩

/-- Constant abelian sheaves are preserved by the equivalence attached to a
scheme isomorphism. -/
noncomputable def constantAddSheafPushforwardIso {X Y : Scheme.{u}}
    (e : X ≅ Y) (A : AddCommGrpCat.{u}) :
    (constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj A ≅
      (sheafEquivOfIso e).functor.obj
        ((constantSheaf (Opens.grothendieckTopology X)
          AddCommGrpCat.{u}).obj A) := by
  let G := (opensEquivOfIso e).inverse
  exact (equivCommuteConstant'
    (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
    (Opens.grothendieckTopology X) G
    (isTerminalTop : IsTerminal (⊤ : Opens Y))
    (isTerminalTop : IsTerminal (G.obj (⊤ : Opens Y)))).app A

/-- The structure module on the target is canonically the pushforward of the
structure module on the source along a scheme isomorphism. -/
noncomputable def structureModulePushforwardIso {X Y : Scheme.{u}} (e : X ≅ Y) :
    structureModule Y ≅
      (Modules.pushforward e.hom).obj (structureModule X) := by
  letI : IsIso (Modules.pullbackPushforwardAdjunction e.hom).unit :=
    (Modules.pullbackPushforwardAdjunction e.hom).unit_isIso_of_L_fully_faithful
  letI : IsIso
      (SheafOfModules.pullbackObjUnitToUnit e.hom.toRingCatSheafHom) :=
    isIso_pullbackObjUnitToUnit e.hom
  exact asIso ((Modules.pullbackPushforwardAdjunction e.hom).unit.app
      (structureModule Y)) ≪≫
    (Modules.pushforward e.hom).mapIso
      (asIso (SheafOfModules.pullbackObjUnitToUnit e.hom.toRingCatSheafHom))

/-- On underlying abelian sheaves, the structure sheaf on the target is the
image of the structure sheaf on the source under `sheafEquivOfIso`. -/
noncomputable def structureAddSheafPushforwardIso {X Y : Scheme.{u}}
    (e : X ≅ Y) :
    (SheafOfModules.toSheaf Y.ringCatSheaf).obj (structureModule Y) ≅
      (sheafEquivOfIso e).functor.obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj (structureModule X)) :=
  (SheafOfModules.toSheaf Y.ringCatSheaf).mapIso
    (structureModulePushforwardIso e)

/-- Restricting a pulled-back global function agrees with pulling back its
restriction. -/
lemma Hom.app_restrictTop {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Opens Y) (r : Γ(Y, ⊤)) :
    f.app U (Modules.restrictTop Y U r) =
      Modules.restrictTop X (f ⁻¹ᵁ U) (f.appTop r) := by
  exact ConcreteCategory.congr_hom
    (f.naturality (Opens.leTop U).op) r

/-- Pushforward along a scheme isomorphism carries multiplication by the
pullback of a global function to multiplication by that function on the
pushforward module. -/
lemma sheafEquivOfIso_map_smulSheafHom {X Y : Scheme.{u}} (e : X ≅ Y)
    (M : X.Modules) (r : Γ(Y, ⊤)) :
    (sheafEquivOfIso e).functor.map
        (Modules.smulSheafHom M (e.hom.appTop r)) =
      Modules.smulSheafHom ((Modules.pushforward e.hom).obj M) r := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U ↦ ?_))
  refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
  change (M.smul (Modules.restrictTop X (e.hom ⁻¹ᵁ U.unop)
      (e.hom.appTop r))).hom x =
    (M.smul (e.hom.app U.unop (Modules.restrictTop Y U.unop r))).hom x
  rw [e.hom.app_restrictTop]

/-- The structure-sheaf comparison intertwines multiplication by corresponding
global functions. -/
lemma sheafEquivOfIso_map_smul_comp_structureIso {X Y : Scheme.{u}}
    (e : X ≅ Y) (r : Γ(Y, ⊤)) :
    (sheafEquivOfIso e).functor.map
        (Modules.smulSheafHom (structureModule X) (e.hom.appTop r)) ≫
          (structureAddSheafPushforwardIso e).inv =
      (structureAddSheafPushforwardIso e).inv ≫
        Modules.smulSheafHom (structureModule Y) r := by
  rw [sheafEquivOfIso_map_smulSheafHom]
  exact Modules.smulSheafHom_comp
    (structureModulePushforwardIso e).inv r

/-- An isomorphism of schemes induces an additive equivalence on the
cohomology of their structure sheaves, in every degree. -/
noncomputable def structureCohomologyAddEquivOfIso {X Y : Scheme.{u}}
    (e : X ≅ Y) (n : ℕ) :
    Modules.H (structureModule X) n ≃+
      Modules.H (structureModule Y) n := by
  let F := (sheafEquivOfIso e).functor
  let CX := (constantSheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))
  let OX := (SheafOfModules.toSheaf X.ringCatSheaf).obj
    (structureModule X)
  let mapEquiv : Ext CX OX n ≃+ Ext (F.obj CX) (F.obj OX) n :=
    AddEquiv.ofBijective (F.mapExtAddHom CX OX n)
      (F.mapExt_bijective_of_preservesInjectiveObjects CX OX n)
  exact mapEquiv.trans <| Ext.isoAddEquiv
    (constantAddSheafPushforwardIso e
      (AddCommGrpCat.of (ULift ℤ))).symm
    (structureAddSheafPushforwardIso e).symm n

@[simp]
lemma structureCohomologyAddEquivOfIso_apply {X Y : Scheme.{u}}
    (e : X ≅ Y) (n : ℕ) (x : Modules.H (structureModule X) n) :
    structureCohomologyAddEquivOfIso e n x =
      Ext.isoAddEquiv
        (constantAddSheafPushforwardIso e
          (AddCommGrpCat.of (ULift ℤ))).symm
        (structureAddSheafPushforwardIso e).symm n
        (x.mapExactFunctor (sheafEquivOfIso e).functor) := rfl

/-- The cohomology equivalence is semilinear for the isomorphism on global
functions: multiplication by `e.hom.appTop r` on the source corresponds to
multiplication by `r` on the target. -/
lemma structureCohomologyAddEquivOfIso_smul {X Y : Scheme.{u}}
    (e : X ≅ Y) (n : ℕ) (r : Γ(Y, ⊤))
    (x : Modules.H (structureModule X) n) :
    structureCohomologyAddEquivOfIso e n (e.hom.appTop r • x) =
      r • structureCohomologyAddEquivOfIso e n x := by
  simp only [Modules.smul_def, structureCohomologyAddEquivOfIso_apply,
    Ext.isoAddEquiv_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀]
  simp only [Ext.comp_assoc_of_second_deg_zero,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
  exact congrArg
    (fun q ↦
      (Ext.mk₀ (constantAddSheafPushforwardIso e
        (AddCommGrpCat.of (ULift ℤ))).symm.inv).comp
          ((x.mapExactFunctor (sheafEquivOfIso e).functor).comp
            (Ext.mk₀ q) (add_zero n)) (zero_add n))
    (sheafEquivOfIso_map_smul_comp_structureIso e r)

/-- An isomorphism of schemes over a common affine base induces a linear
equivalence on structure-sheaf cohomology over that base ring. -/
noncomputable def structureCohomologyLinearEquivOfOverIso
    (k : Type u) [Field k]
    {X Y : Over (Spec (CommRingCat.of k))} (e : X ≅ Y) (n : ℕ) :
    Modules.H (structureModule X.left) n ≃ₗ[k]
      Modules.H (structureModule Y.left) n := by
  let E : X.left ≅ Y.left :=
    (Over.forget (Spec (CommRingCat.of k))).mapIso e
  exact
    { structureCohomologyAddEquivOfIso E n with
      map_smul' := by
        intro a x
        have hx : a • x =
            X.left.baseRingHom (CommRingCat.of k) a • x :=
          Modules.base_smul_eq_globalSections_smul (structureModule X.left) n a x
        have hy : a • structureCohomologyAddEquivOfIso E n x =
            Y.left.baseRingHom (CommRingCat.of k) a •
              structureCohomologyAddEquivOfIso E n x :=
          Modules.base_smul_eq_globalSections_smul (structureModule Y.left) n a
            (structureCohomologyAddEquivOfIso E n x)
        have hw : E.hom ≫ Y.hom = X.hom := Over.w e.hom
        have hring : Modules.baseRingHom Y.hom ≫ E.hom.appTop =
            Modules.baseRingHom X.hom :=
          (Modules.baseRingHom_comp_appTop E.hom Y.hom).trans
            (congrArg Modules.baseRingHom hw)
        have hbase : E.hom.appTop
              (Y.left.baseRingHom (CommRingCat.of k) a) =
            X.left.baseRingHom (CommRingCat.of k) a :=
          ConcreteCategory.congr_hom hring a
        exact (congrArg (structureCohomologyAddEquivOfIso E n) hx).trans <|
          (congrArg
            (fun r ↦ structureCohomologyAddEquivOfIso E n (r • x))
            hbase).symm.trans <|
          (structureCohomologyAddEquivOfIso_smul E n
            (Y.left.baseRingHom (CommRingCat.of k) a) x).trans hy.symm }

/-- Isomorphic schemes over a field have equal structure-sheaf cohomology
dimensions in every degree. -/
lemma Modules.h_structureModule_eq_of_overIso
    (k : Type u) [Field k]
    {X Y : Over (Spec (CommRingCat.of k))} (e : X ≅ Y) (n : ℕ) :
    Modules.h k (structureModule X.left) n =
      Modules.h k (structureModule Y.left) n :=
  (structureCohomologyLinearEquivOfOverIso k e n).finrank_eq

end AlgebraicGeometry.Scheme
