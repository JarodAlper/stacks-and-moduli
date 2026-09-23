module

public import StacksAndModuli.«Section3.1-Descent».«part3.1.3-descending-morphisms»
public import StacksAndModuli.API.RepresentableInternalHom
public import StacksAndModuli.API.PseudofunctorSheafOverPrestack
public import StacksProject.MoreOnMorphisms.SlicingSmooth.«lemma-etale-nbhd-dominates-smooth»
public import StacksAndModuli.Util.FpqcCover
public import StacksAndModuli.«Section3.3-Presheaves-and-Sheaves».«part3.3.2-single-map-and-schemes-are-sheaves»
public import Mathlib.CategoryTheory.Sites.SheafHom
public import Mathlib.CategoryTheory.Sites.PseudofunctorSheafOver
public import Mathlib.CategoryTheory.Sites.Descent.IsStack

/-!
# Hom sheaves, gluing of sheaves, and covers as epimorphisms

This module formalizes Exercise 3.3.9 (`exer:sheaf-of-morphisms`), Exercise 3.3.10
(`exer:gluing-sheaves`), and Exercise 3.3.11 (`exer:covers-are-epimorphisms`) of §3.3
(Presheaves and sheaves) of *Stacks and Moduli*,
section label `sec:sheaves`, in the order of
the book.

Main results:
- Exercise 3.3.9(a): for sheaves `F` and `G`, the presheaf
  `T ↦ Hom(F|_T, G|_T)` is a sheaf; part (b) specializes this over `Sch/S` to the fpqc
  sheaf `T ↦ Mor_T(X_T, Y_T)` of relative morphisms;
- `CategoryTheory.GrothendieckTopology.isStack_pseudofunctorOver`: sheaves and their
  morphisms glue along coverings — the pseudofunctor `X ↦ Sheaf (J.over X) A` is a stack
  (`CategoryTheory.Pseudofunctor.IsStack`);
- `CategoryTheory.Presheaf.isLocallySurjective_yoneda_map_of_singleton_mem`: if the
  singleton `{f}` is a covering of a precoverage, then `yoneda.map f` is locally surjective
  for the generated topology;
- `CategoryTheory.Presheaf.isLocallySurjective_yoneda_map_of_covering_le`: more generally,
  it suffices that a covering sieve refine the singleton `{f}`;
- `CategoryTheory.Sheaf.epi_yoneda_map_of_singleton_mem`: the corresponding reusable
  epimorphism theorem for representable sheaves on a subcanonical site;
- `AlgebraicGeometry.Scheme.epi_yoneda_map_of_fppf` / `epi_yoneda_map_of_fpqc` /
  `epi_yoneda_map_of_smooth`: a surjective fppf (resp. fpqc, smooth) morphism of schemes is
  an epimorphism of sheaves on `Sch_fppf` (resp. `Sch_fpqc`, `Sch_ét`).
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section ExerSheafOfMorphisms

open CategoryTheory Opposite AlgebraicGeometry

universe w v u

/- **Exercise 3.3.9** (`exer:sheaf-of-morphisms`) (part (a), the presheaf): for presheaves
$F, G$ on a category $\cS$, the assignment $T \mapsto \Mor(F|_{\cS/T}, G|_{\cS/T})$ is a
presheaf on $\cS$. Faithfulness caveat: the book's displayed formula
$S \mapsto \Mor_{\Sets}(F(S), G(S))$ carries no restriction maps; the intended presheaf —
the one used in the proof of the descent criterion of Proposition 3.3.17 — is the internal hom recalled
here (see the Exercise 3.3.9 entry in this folder's COMMENTARY.md). -/
example {𝒮 : Type u} [Category.{v} 𝒮] (F G : 𝒮ᵒᵖ ⥤ Type w) : 𝒮ᵒᵖ ⥤ Type (max u v w) :=
  presheafHom F G

/- **Exercise 3.3.9** (`exer:sheaf-of-morphisms`) (part (a)): if $G$ is a sheaf on a site
$(\cS, J)$, then for any presheaf $F$ the presheaf $\Mor(F, G)$ is a sheaf. -/
example {𝒮 : Type u} [Category.{v} 𝒮] {J : GrothendieckTopology 𝒮} {F G : 𝒮ᵒᵖ ⥤ Type w}
    (hG : Presheaf.IsSheaf J G) :
    Presheaf.IsSheaf J (presheafHom F G) :=
  hG.hom (F := F)

/- Convenience construction derived from Exercise 3.3.9 (part (a), packaged): the hom sheaf of two
sheaves, as a sheaf of types. -/
example {𝒮 : Type u} [Category.{v} 𝒮] {J : GrothendieckTopology 𝒮}
    (F G : Sheaf J (Type w)) : Sheaf J (Type (max u v w)) :=
  sheafHom F G

/-- Supporting identification used in Exercise 3.3.9 (part (b), valuewise form):
let $X$ and $Y$ be schemes
over $S$. The functor $\underline{\Mor}_S(X,Y)$ assigning to an $S$-scheme $T$ the set of
$T$-morphisms $X_T \to Y_T$ — equivalently, morphisms of the restricted presheaves
$X|_{\Sch/T} \to Y|_{\Sch/T}$ — is a sheaf in the fpqc topology on $\Sch/S$. -/
noncomputable def AlgebraicGeometry.Scheme.relativeMorphismPresheafObjEquiv
    (S : Scheme.{u}) (X Y T : Over S) :
    (presheafHom (yoneda.obj X) (yoneda.obj Y)).obj (op T) ≃
      ((Over.pullback T.hom).obj X ⟶ (Over.pullback T.hom).obj Y) :=
  representablePresheafHomObjEquiv X Y T

/- **Exercise 3.3.9** (`exer:sheaf-of-morphisms`) (part (b), sheaf clause): the relative
morphism presheaf identified above is an fpqc sheaf. -/
example (S : Scheme.{u}) (X Y : Over S) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over S)
      (presheafHom (yoneda.obj X) (yoneda.obj Y)) := by
  have hY : Presheaf.IsSheaf (Scheme.fpqcTopology.over S) (yoneda.obj Y) := by
    rw [isSheaf_iff_isSheaf_of_type]
    exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
      (J := Scheme.fpqcTopology.over S) _
  exact hY.hom (F := yoneda.obj X)

end ExerSheafOfMorphisms

section ExerGluingSheaves

open CategoryTheory Opposite

universe v' u' v u

namespace CategoryTheory.GrothendieckTopology

open Bicategory

/-- The full subcategory of arrows in a covering sieve is cover-dense in the slice site.
This is the comparison-lemma input for gluing set-valued sheaves. -/
lemma coveringSieveInclusion_isCoverDense
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {S : C} (R : Sieve S) (hR : R ∈ J S) :
    (ObjectProperty.ι (fun T : Over S ↦ R T.hom)).IsCoverDense (J.over S) where
  is_cover U := by
    refine (J.over S).superset_covering ?_
      (J.overEquiv_symm_mem_over U _ (J.pullback_stable U.hom hR))
    intro V g hg
    have hV : R V.hom := by
      change R (g.left ≫ U.hom) at hg
      simpa only [Over.w g] using hg
    exact ⟨⟨(⟨V, hV⟩ : ObjectProperty.FullSubcategory fun T : Over S ↦ R T.hom),
      𝟙 V, g, by simp⟩⟩

section EffectiveDescent

universe w

set_option backward.defeqAttrib.useBackward true

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {S : C} (R : Sieve S)

lemma restrictedPresheaf_source_arrow {X Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) :
    (Over.homMk (g ≫ f) :
        (Over.map (g ≫ f)).obj (Over.mk (𝟙 Z)) ⟶ Over.mk (𝟙 X)).op ≫
      ((Over.mapComp g f).inv.app (Over.mk (𝟙 Z))).op =
    (Over.homMk f : (Over.map f).obj (Over.mk (𝟙 Y)) ⟶ Over.mk (𝟙 X)).op ≫
      ((Over.map f).map
        (Over.homMk g : (Over.map g).obj (Over.mk (𝟙 Z)) ⟶ Over.mk (𝟙 Y))).op := by
  apply Quiver.Hom.unop_inj
  ext
  simp [Over.mapComp]

lemma restrictedPresheaf_target_naturality {Y Z : C} (g : Z ⟶ Y) :
    (Over.homMk g : (Over.map g).obj (Over.mk (𝟙 Z)) ⟶ Over.mk (𝟙 Y)) ≫
      (Over.mapId Y).inv.app (Over.mk (𝟙 Y)) =
    (Over.mapId Y).inv.app ((Over.map g).obj (Over.mk (𝟙 Z))) ≫
      (Over.map (𝟙 Y)).map
        (Over.homMk g : (Over.map g).obj (Over.mk (𝟙 Z)) ⟶ Over.mk (𝟙 Y)) := by
  simpa only [Functor.id_map] using (Over.mapId Y).inv.naturality
    (Over.homMk g : (Over.map g).obj (Over.mk (𝟙 Z)) ⟶ Over.mk (𝟙 Y))

lemma restrictedPresheaf_target_unit {Y Z : C} (g : Z ⟶ Y) :
    (Over.mapComp g (𝟙 Y)).hom.app (Over.mk (𝟙 Z)) =
      (Over.mapCongr (g ≫ 𝟙 Y) g (by simp)).hom.app (Over.mk (𝟙 Z)) ≫
        (Over.mapId Y).inv.app ((Over.map g).obj (Over.mk (𝟙 Z))) := by
  ext
  simp [Over.mapComp, Over.mapCongr, Over.mapId]

lemma restrictedPresheaf_target_naturality_op {Y Z : C} (g : Z ⟶ Y) :
    ((Over.mapId Y).inv.app (Over.mk (𝟙 Y))).op ≫
      (Over.homMk g : (Over.map g).obj (Over.mk (𝟙 Z)) ⟶ Over.mk (𝟙 Y)).op =
    ((Over.map (𝟙 Y)).map
      (Over.homMk g : (Over.map g).obj (Over.mk (𝟙 Z)) ⟶ Over.mk (𝟙 Y))).op ≫
      ((Over.mapId Y).inv.app ((Over.map g).obj (Over.mk (𝟙 Z)))).op := by
  apply Quiver.Hom.unop_inj
  simpa only [unop_comp, Quiver.Hom.unop_op] using
    restrictedPresheaf_target_naturality g

lemma restrictedPresheaf_source_map
    {X Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) (F : (Over X)ᵒᵖ ⥤ Type w) :
    F.map (Over.homMk (g ≫ f) :
        (Over.map (g ≫ f)).obj (Over.mk (𝟙 Z)) ⟶ Over.mk (𝟙 X)).op ≫
      F.map ((Over.mapComp g f).inv.app (Over.mk (𝟙 Z))).op =
    F.map (Over.homMk f :
        (Over.map f).obj (Over.mk (𝟙 Y)) ⟶ Over.mk (𝟙 X)).op ≫
      F.map ((Over.map f).map
        (Over.homMk g :
          (Over.map g).obj (Over.mk (𝟙 Z)) ⟶ Over.mk (𝟙 Y))).op := by
  rw [← F.map_comp, restrictedPresheaf_source_arrow, F.map_comp]

lemma restrictedPresheaf_target_naturality_map
    {Y Z : C} (g : Z ⟶ Y) (F : (Over Y)ᵒᵖ ⥤ Type w) :
    F.map ((Over.mapId Y).inv.app (Over.mk (𝟙 Y))).op ≫
      F.map (Over.homMk g :
        (Over.map g).obj (Over.mk (𝟙 Z)) ⟶ Over.mk (𝟙 Y)).op =
    F.map ((Over.map (𝟙 Y)).map
      (Over.homMk g :
        (Over.map g).obj (Over.mk (𝟙 Z)) ⟶ Over.mk (𝟙 Y))).op ≫
      F.map ((Over.mapId Y).inv.app
        ((Over.map g).obj (Over.mk (𝟙 Z)))).op := by
  rw [← F.map_comp, restrictedPresheaf_target_naturality_op, F.map_comp]

lemma restrictedPresheaf_mapCongr_cancel
    {X Y : C} {f g : X ⟶ Y} (p : f = g) (Z : Over X)
    (F : (Over Y)ᵒᵖ ⥤ Type w)
    (x : F.obj (op ((Over.map g).obj Z))) :
    (eqToHom (congrArg (fun k ↦ F.obj (op ((Over.map k).obj Z))) p) :
        F.obj (op ((Over.map f).obj Z)) → F.obj (op ((Over.map g).obj Z)))
      (F.map ((Over.mapCongr f g p).hom.app Z).op x) = x := by
  subst g
  simp

/-- The presheaf on a covering sieve extracted from descent data of set-valued sheaves.
Its value at `U ⟶ S` is the value of the local sheaf over `U` at `𝟙 U`.

This is the dense-subsite presheaf used in the proof of
*Stacks and Moduli*, Exercise 3.3.10. -/
noncomputable def Pseudofunctor.DescentData.restrictedPresheaf
    (D : (J.pseudofunctorOver (Type w)).DescentData
      (fun i : R.arrows.category ↦ i.obj.hom)) :
    R.arrows.categoryᵒᵖ ⥤ Type w where
  obj i := (D.obj i.unop).obj.obj (op (Over.mk (𝟙 i.unop.obj.left)))
  map {i j} f :=
    (D.obj i.unop).obj.map
        (Over.homMk f.unop.hom.left :
          (Over.map f.unop.hom.left).obj (Over.mk (𝟙 j.unop.obj.left)) ⟶
            Over.mk (𝟙 i.unop.obj.left)).op ≫
      ((D.iso j.unop.obj.hom (𝟙 _) f.unop.hom.left).inv).hom.app
        (op (Over.mk (𝟙 j.unop.obj.left))) ≫
      (((J.overMapPullbackId (Type w) j.unop.obj.left).hom.app
        (D.obj j.unop)).hom.app (op (Over.mk (𝟙 j.unop.obj.left))))
  map_id i := by
    ext x
    dsimp
    rw [D.hom_self]
    · simp only [overMapPullbackId_hom_app_hom_app,
        pseudofunctorOver_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj_α,
        op_id, Quiver.Hom.id_toLoc, ObjectProperty.FullSubcategory.id_hom,
        NatTrans.id_app,
pseudofunctorOver_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map_toFunctor_obj_obj_obj,
        LocallyDiscrete.id_as, unop_id, id_apply]
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      suffices
          (Over.homMk (𝟙 i.unop.obj.left) :
              (Over.map (𝟙 i.unop.obj.left)).obj (Over.mk (𝟙 i.unop.obj.left)) ⟶
                Over.mk (𝟙 i.unop.obj.left)).op ≫
            ((Over.mapId i.unop.obj.left).inv.app (Over.mk (𝟙 i.unop.obj.left))).op = 𝟙 _ by
        rw [this, Functor.map_id]
        rfl
      apply Quiver.Hom.unop_inj
      ext
      simp
    · cat_disch
  map_comp {X Y Z} f g := by
    dsimp
    simp only [← Category.assoc]
    rw [cancel_mono]
    let hgz := (D.hom (unop Z).obj.hom g.unop.hom.left
      (𝟙 (unop Z).obj.left)).hom.app (op (Over.mk (𝟙 (unop Z).obj.left)))
    let _ : IsIso hgz := by
      dsimp [hgz]
      change IsIso (((D.iso (unop Z).obj.hom g.unop.hom.left
        (𝟙 (unop Z).obj.left)).hom).hom.app (op (Over.mk (𝟙 (unop Z).obj.left))))
      infer_instance
    have hc := congrArg (fun k ↦ k.hom.app (op (Over.mk (𝟙 (unop Z).obj.left))))
      (D.hom_comp (q := (unop Z).obj.hom)
      (f₁ := g.unop.hom.left ≫ f.unop.hom.left) (f₂ := g.unop.hom.left)
      (f₃ := 𝟙 (unop Z).obj.left) (by cat_disch) (by cat_disch) (by simp))
    dsimp at hc
    rw [← hc]
    simp only [← Category.assoc]
    change _ ≫ hgz = _ ≫ hgz
    rw [cancel_mono]
    have hp := congrArg (fun k ↦ k.hom.app (op (Over.mk (𝟙 (unop Z).obj.left))))
      (D.pullHom_hom g.unop.hom.left (unop Y).obj.hom (unop Z).obj.hom
        (by cat_disch) f.unop.hom.left (𝟙 (unop Y).obj.left) (by cat_disch)
        (by cat_disch) (g.unop.hom.left ≫ f.unop.hom.left) g.unop.hom.left
        (by cat_disch) (by simp))
    dsimp at hp
    rw [← hp]
    dsimp [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
    simp only [Pseudofunctor.mapComp', Iso.trans_hom, Iso.trans_inv, Cat.Hom₂.comp_app,
      PrelaxFunctor.map₂Iso_eqToIso,
      pseudofunctorOver_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj_α,
pseudofunctorOver_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map_toFunctor_obj_obj_obj,
      Quiver.Hom.toLoc_as, Quiver.Hom.unop_op,
      LocallyDiscrete.comp_as, unop_comp, Cat.Hom.comp_toFunctor, Functor.comp_obj,
      ObjectProperty.FullSubcategory.comp_hom,
      NatTrans.comp_app, LocallyDiscrete.id_as, unop_id,
      pseudofunctorOver_mapComp_hom_toNatTrans_app_hom_app,
      pseudofunctorOver_mapComp_inv_toNatTrans_app_hom_app,
      eqToIso.hom, eqToIso.inv, Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app,
      ObjectProperty.eqToHom_hom]
    simp only [eqToHom_refl, Category.id_comp]
    rw [← Category.assoc,
      restrictedPresheaf_source_map f.unop.hom.left g.unop.hom.left]
    have hn := (D.hom (unop Y).obj.hom f.unop.hom.left
      (𝟙 (unop Y).obj.left)).hom.naturality
        (Over.homMk g.unop.hom.left :
          (Over.map g.unop.hom.left).obj (Over.mk (𝟙 (unop Z).obj.left)) ⟶
            Over.mk (𝟙 (unop Y).obj.left)).op
    dsimp at hn
    simp only [Category.assoc]
    slice_lhs 2 3 => exact hn
    rw [restrictedPresheaf_target_unit]
    simp only [op_comp, Functor.map_comp, Category.assoc]
    simp only [overMapPullbackId_hom_app_hom_app]
    slice_lhs 3 4 => exact
      (restrictedPresheaf_target_naturality_map g.unop.hom.left _).symm
    let p : g.unop.hom.left ≫ 𝟙 (unop Y).obj.left = g.unop.hom.left :=
      Category.comp_id _
    let q := congrArg (fun k ↦
      (D.obj (unop Y)).obj.obj
        (op ((Over.map k).obj (Over.mk (𝟙 (unop Z).obj.left))))) p
    have ht :
        (D.obj (unop Y)).obj.map
              ((Over.mapCongr
                (g.unop.hom.left ≫ 𝟙 (unop Y).obj.left) g.unop.hom.left
                p).hom.app (Over.mk (𝟙 (unop Z).obj.left))).op ≫
            eqToHom q = 𝟙 _ := by
      apply ConcreteCategory.hom_ext
      intro x
      exact restrictedPresheaf_mapCongr_cancel p _ _ x
    rw [Category.assoc]
    rw [Category.assoc]
    erw [ht]
    simp

/-- For an arrow `U ⟶ S` in a sieve, composition with that arrow sends `Over U` into
the full subcategory of arrows belonging to the sieve. -/
def coveringSieveOverFunctor (i : R.arrows.category) :
    Over i.obj.left ⥤ R.arrows.category :=
  ObjectProperty.lift (fun T : Over S ↦ R T.hom)
    (Over.map i.obj.hom) (fun T ↦ by
    exact R.downward_closed i.property T.hom)

/-- The canonical morphism from a composite arrow in the sieve to its final factor. -/
def coveringSieveStructureHom (i : R.arrows.category) (T : Over i.obj.left) :
    (coveringSieveOverFunctor R i).obj T ⟶ i :=
  ObjectProperty.homMk
    (Over.homMk T.hom (by rfl) : (Over.map i.obj.hom).obj T ⟶ i.obj)

/-- Composition with an arrow in the sieve, regarded as a functor to the slice of the
sieve's arrow category over that arrow. -/
def coveringSieveOverToSliceFunctor (i : R.arrows.category) :
    Over i.obj.left ⥤ Over i where
  obj T := Over.mk (coveringSieveStructureHom R i T)
  map {T U} f := Over.homMk ((coveringSieveOverFunctor R i).map f) (by
    apply ObjectProperty.hom_ext
    ext
    change f.left ≫ U.hom = T.hom
    exact Over.w f)

/-- Forgetting the outer slice recovers an arrow over the source of `i`. -/
def coveringSieveSliceToOverFunctor (i : R.arrows.category) :
    Over i ⥤ Over i.obj.left where
  obj T := Over.mk T.hom.hom.left
  map {T U} f := Over.homMk f.left.hom.left (by
    exact congrArg (fun k ↦ k.hom.left) (Over.w f))

def coveringSieveOverToSliceUnitIso (i : R.arrows.category)
    (T : Over i.obj.left) :
    T ≅ (coveringSieveOverToSliceFunctor R i ⋙
      coveringSieveSliceToOverFunctor R i).obj T :=
  Over.isoMk (Iso.refl _) (by
    simp [coveringSieveOverToSliceFunctor, coveringSieveSliceToOverFunctor,
      coveringSieveStructureHom])

def coveringSieveOverToSliceCounitIso (i : R.arrows.category)
    (T : Over i) :
    (coveringSieveSliceToOverFunctor R i ⋙
      coveringSieveOverToSliceFunctor R i).obj T ≅ T :=
  by
    let e₀ :
        ((coveringSieveSliceToOverFunctor R i ⋙
          coveringSieveOverToSliceFunctor R i).obj T).left.obj ≅ T.left.obj :=
      Over.isoMk (Iso.refl _) (by
        dsimp [coveringSieveOverToSliceFunctor, coveringSieveSliceToOverFunctor,
          coveringSieveStructureHom, coveringSieveOverFunctor]
        simpa only [Category.id_comp] using (Over.w T.hom.hom).symm)
    let e :
        ((coveringSieveSliceToOverFunctor R i ⋙
          coveringSieveOverToSliceFunctor R i).obj T).left ≅ T.left :=
      ObjectProperty.isoMk (fun T : Over S ↦ R T.hom) e₀
    exact Over.isoMk e (by
      apply ObjectProperty.hom_ext
      ext
      simp [e, e₀, coveringSieveOverToSliceFunctor,
        coveringSieveSliceToOverFunctor, coveringSieveStructureHom])

/-- The slice of the category of arrows in the sieve over `i : U ⟶ S` is equivalent
to `Over U`. -/
def coveringSieveOverSliceEquivalence (i : R.arrows.category) :
    Over i.obj.left ≌ Over i where
  functor := coveringSieveOverToSliceFunctor R i
  inverse := coveringSieveSliceToOverFunctor R i
  unitIso := NatIso.ofComponents
    (coveringSieveOverToSliceUnitIso R i) (by
      intro T U f
      ext
      simp [coveringSieveOverToSliceUnitIso, coveringSieveOverToSliceFunctor,
        coveringSieveSliceToOverFunctor, coveringSieveStructureHom,
        coveringSieveOverFunctor])
  counitIso := NatIso.ofComponents
    (coveringSieveOverToSliceCounitIso R i) (by
      intro T U f
      ext
      simp [coveringSieveOverToSliceCounitIso, coveringSieveOverToSliceFunctor,
        coveringSieveSliceToOverFunctor, coveringSieveStructureHom,
        coveringSieveOverFunctor])
  functor_unitIso_comp T := by
    ext
    simp [coveringSieveOverToSliceUnitIso, coveringSieveOverToSliceCounitIso,
      coveringSieveOverToSliceFunctor, coveringSieveSliceToOverFunctor,
      coveringSieveStructureHom, coveringSieveOverFunctor]

/-- Under the slice equivalence, the forgetful functor is composition with `i`. -/
def coveringSieveOverSliceForgetIso (i : R.arrows.category) :
    (coveringSieveOverSliceEquivalence R i).functor ⋙ Over.forget i ≅
      coveringSieveOverFunctor R i :=
  Iso.refl _

/-- On the inverse side of the slice equivalence, composition with `i` recovers the
ordinary slice forgetful functor. -/
def coveringSieveOverSliceInverseForgetIso (i : R.arrows.category) :
    (coveringSieveOverSliceEquivalence R i).inverse ⋙
        coveringSieveOverFunctor R i ≅
      Over.forget i :=
  Functor.isoWhiskerLeft (coveringSieveOverSliceEquivalence R i).inverse
      (coveringSieveOverSliceForgetIso R i).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (coveringSieveOverSliceEquivalence R i).counitIso
      (Over.forget i) ≪≫
    Functor.leftUnitor _

def coveringSieveOverSliceInversePresheafIso
    (i : R.arrows.category) (P : R.arrows.categoryᵒᵖ ⥤ Type w) :
    (coveringSieveOverSliceEquivalence R i).inverse.op ⋙
        ((coveringSieveOverFunctor R i).op ⋙ P) ≅
      (Over.forget i).op ⋙ P :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.opComp _ _).symm P ≪≫
    Functor.isoWhiskerRight
      (NatIso.op (coveringSieveOverSliceInverseForgetIso R i)).symm P

/-- Restricting a presheaf along the arrow represented by `i` is the same as first
restricting to the sieve's arrow category and then composing arrows with `i`. -/
def coveringSieveOverFunctorPresheafIso
    (i : R.arrows.category) (P : (Over S)ᵒᵖ ⥤ Type w) :
    (Over.map i.obj.hom).op ⋙ P ≅
      (coveringSieveOverFunctor R i).op ⋙
        ((ObjectProperty.ι (fun T : Over S ↦ R T.hom)).op ⋙ P) :=
  Iso.refl _

/-- The inverse slice equivalence and the two successive forgetful functors have the
same underlying source object. -/
def coveringSieveOverSliceUnderlyingIso (i : R.arrows.category) :
    (coveringSieveOverSliceEquivalence R i).inverse ⋙
        Over.forget i.obj.left ≅
      Over.forget i ⋙ ObjectProperty.ι (fun T : Over S ↦ R T.hom) ⋙
        Over.forget S :=
  Iso.refl _

lemma coveringSieveOverSlice_sieve (i : R.arrows.category)
    (T : Over i) (Q : Sieve T) :
    (Sieve.overEquiv
      ((coveringSieveOverSliceEquivalence R i).inverse.obj T))
        (Q.functorPushforward
          (coveringSieveOverSliceEquivalence R i).inverse) =
      (Sieve.overEquiv
        ((ObjectProperty.ι (fun T : Over S ↦ R T.hom)).obj T.left))
        ((Sieve.overEquiv T Q).functorPushforward
          (ObjectProperty.ι (fun T : Over S ↦ R T.hom))) := by
  change (Q.functorPushforward
      (coveringSieveOverSliceEquivalence R i).inverse).functorPushforward
        (Over.forget i.obj.left) =
    ((Q.functorPushforward (Over.forget i)).functorPushforward
      (ObjectProperty.ι (fun T : Over S ↦ R T.hom))).functorPushforward
        (Over.forget S)
  rw [← Sieve.functorPushforward_comp, ← Sieve.functorPushforward_comp,
    ← Sieve.functorPushforward_comp]
  rfl

/-- The topology transported to the slice of the sieve's arrow category agrees with
the topology induced from the corresponding slice of the ambient site. -/
lemma coveringSieveOverSlice_inducedTopology (hR : R ∈ J S)
    (i : R.arrows.category) :
    (coveringSieveOverSliceEquivalence R i).inverse.inducedTopology
        (J.over i.obj.left) =
      ((ObjectProperty.ι (fun T : Over S ↦ R T.hom)).inducedTopology
        (J.over S)).over i := by
  let _ : (ObjectProperty.ι
      (fun T : Over S ↦ R T.hom)).IsCoverDense (J.over S) :=
    coveringSieveInclusion_isCoverDense J R hR
  ext T Q
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense,
    GrothendieckTopology.mem_over_iff,
    GrothendieckTopology.mem_over_iff,
    Functor.mem_inducedTopology_iff_of_isCoverDense,
    GrothendieckTopology.mem_over_iff]
  rw [coveringSieveOverSlice_sieve]
  rfl

/-- A type-valued presheaf is a sheaf if all its restrictions to slice categories are
sheaves. It is enough, for a covering sieve on `X`, to use the slice object `𝟙 X`. -/
lemma isSheaf_of_isSheaf_over_restrictions
    {D : Type u} [Category.{v} D] (K : GrothendieckTopology D)
    (P : Dᵒᵖ ⥤ Type w)
    (hP : ∀ X : D, Presheaf.IsSheaf (K.over X)
      ((Over.forget X).op ⋙ P)) :
    Presheaf.IsSheaf K P := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro X Q hQ x hx
  let I : Over X := Over.mk (𝟙 X)
  let Q' : Sieve I := (Sieve.overEquiv I).symm Q
  have hQ' : Q' ∈ K.over X I :=
    K.overEquiv_symm_mem_over I Q hQ
  let y : Q'.arrows.FamilyOfElements ((Over.forget X).op ⋙ P) :=
    fun _ f hf ↦ x f.left ((Sieve.overEquiv_symm_iff Q f).mp hf)
  have hy : y.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ h
    exact hx g₁.left g₂.left
      ((Sieve.overEquiv_symm_iff Q f₁).mp hf₁)
      ((Sieve.overEquiv_symm_iff Q f₂).mp hf₂)
      (congrArg Over.Hom.left h)
  have hPX := (isSheaf_iff_isSheaf_of_type _ _).mp (hP X)
  obtain ⟨t, ht, hut⟩ := hPX Q' hQ' y hy
  refine ⟨t, ?_, ?_⟩
  · intro Y f hf
    let f' : Over.mk f ⟶ I := Over.homMk f
    have hf' : Q' f' :=
      (Sieve.overEquiv_symm_iff Q f').mpr hf
    exact ht f' hf'
  · intro t' ht'
    apply hut t'
    intro Y f hf
    exact ht' f.left ((Sieve.overEquiv_symm_iff Q f).mp hf)

/-- The object obtained by pulling the identity arrow back along `T.hom` is canonically
isomorphic to `T`. -/
def overMapIdentityIso {X : C} (T : Over X) :
    (Over.map T.hom).obj (Over.mk (𝟙 T.left)) ≅ T :=
  Over.isoMk (Iso.refl _) (by simp)

lemma overMapIdentityIso_map {X Y : C} (f : X ⟶ Y) (T : Over X) :
    (Over.mapComp T.hom f).hom.app (Over.mk (𝟙 T.left)) ≫
        (Over.map f).map (overMapIdentityIso T).hom =
      (overMapIdentityIso ((Over.map f).obj T)).hom := by
  ext
  simp [overMapIdentityIso, Over.mapComp]

/-- Objectwise comparison between the presheaf extracted from descent data and the local
sheaf indexed by an arrow of the covering sieve. -/
noncomputable def restrictedPresheafLocalHom
    (D : (J.pseudofunctorOver (Type w)).DescentData
      (fun i : R.arrows.category ↦ i.obj.hom))
    (i : R.arrows.category) (T : Over i.obj.left) :
    (D.obj ((coveringSieveOverFunctor R i).obj T)).obj.obj
        (op (Over.mk (𝟙 T.left))) ⟶
      (D.obj i).obj.obj (op T) :=
  (((J.overMapPullbackId (Type w) T.left).inv.app
          (D.obj ((coveringSieveOverFunctor R i).obj T))).hom.app
      (op (Over.mk (𝟙 T.left)))) ≫
    (D.hom (i₁ := (coveringSieveOverFunctor R i).obj T) (i₂ := i)
      (T.hom ≫ i.obj.hom) (𝟙 T.left) T.hom).hom.app
      (op (Over.mk (𝟙 T.left))) ≫
    (D.obj i).obj.map (overMapIdentityIso T).symm.hom.op

noncomputable def restrictedPresheafLocalObjIso
    (D : (J.pseudofunctorOver (Type w)).DescentData
      (fun i : R.arrows.category ↦ i.obj.hom))
    (i : R.arrows.category) (T : Over i.obj.left) :
    (D.obj ((coveringSieveOverFunctor R i).obj T)).obj.obj
        (op (Over.mk (𝟙 T.left))) ≅
      (D.obj i).obj.obj (op T) :=
  by
    let j := (coveringSieveOverFunctor R i).obj T
    let V := op (Over.mk (𝟙 T.left))
    let e₁ : (D.obj j).obj.obj V ≅
        ((J.overMapPullback (Type w) (𝟙 T.left)).obj (D.obj j)).obj.obj V :=
      { hom := (((J.overMapPullbackId (Type w) T.left).inv.app
            (D.obj j))).hom.app V
        inv := (((J.overMapPullbackId (Type w) T.left).hom.app
            (D.obj j))).hom.app V
        hom_inv_id := by simp [V]
        inv_hom_id := by simp [V] }
    let e₂ :
        ((J.overMapPullback (Type w) (𝟙 T.left)).obj (D.obj j)).obj.obj V ≅
          ((J.overMapPullback (Type w) T.hom).obj (D.obj i)).obj.obj V :=
      { hom := (D.iso (i₁ := j) (i₂ := i) (T.hom ≫ i.obj.hom)
            (𝟙 T.left) T.hom).hom.hom.app V
        inv := (D.iso (i₁ := j) (i₂ := i) (T.hom ≫ i.obj.hom)
            (𝟙 T.left) T.hom).inv.hom.app V
        hom_inv_id := by
          exact congrArg (fun k ↦ k.hom.app V)
            (D.iso (i₁ := j) (i₂ := i) (T.hom ≫ i.obj.hom)
              (𝟙 T.left) T.hom).hom_inv_id
        inv_hom_id := by
          exact congrArg (fun k ↦ k.hom.app V)
            (D.iso (i₁ := j) (i₂ := i) (T.hom ≫ i.obj.hom)
              (𝟙 T.left) T.hom).inv_hom_id }
    exact e₁ ≪≫ e₂ ≪≫
      (D.obj i).obj.mapIso (overMapIdentityIso T).symm.op

lemma restrictedPresheafLocalHom_naturality
    (D : (J.pseudofunctorOver (Type w)).DescentData
      (fun i : R.arrows.category ↦ i.obj.hom))
    (i : R.arrows.category) {T U : Over i.obj.left} (f : T ⟶ U) :
    (Pseudofunctor.DescentData.restrictedPresheaf J R D).map
          ((coveringSieveOverFunctor R i).map f).op ≫
        restrictedPresheafLocalHom J R D i T =
      restrictedPresheafLocalHom J R D i U ≫ (D.obj i).obj.map f.op := by
  dsimp [restrictedPresheafLocalHom,
    Pseudofunctor.DescentData.restrictedPresheaf, coveringSieveOverFunctor]
  simp only [Category.assoc]
  simp only [overMapPullbackId_hom_app_hom_app,
    overMapPullbackId_inv_app_hom_app, cancelIso]
  have hc := congrArg (fun k ↦ k.hom.app (op (Over.mk (𝟙 T.left))))
    (D.hom_comp (i₁ := (coveringSieveOverFunctor R i).obj U)
      (i₂ := (coveringSieveOverFunctor R i).obj T) (i₃ := i)
      (T.hom ≫ i.obj.hom) f.left (𝟙 T.left) T.hom
      (by
        dsimp [coveringSieveOverFunctor]
        rw [← Category.assoc, f.w])
      (by simp [coveringSieveOverFunctor]) (by simp))
  dsimp at hc
  slice_lhs 2 3 => exact hc
  have hp := congrArg (fun k ↦ k.hom.app (op (Over.mk (𝟙 T.left))))
    (D.pullHom_hom (i₁ := (coveringSieveOverFunctor R i).obj U) (i₂ := i)
      f.left (U.hom ≫ i.obj.hom) (T.hom ≫ i.obj.hom)
      (by rw [← Category.assoc, f.w])
      (𝟙 U.left) U.hom (by simp [coveringSieveOverFunctor]) (by simp)
      f.left T.hom (by simp) f.w)
  dsimp [Pseudofunctor.LocallyDiscreteOpToCat.pullHom] at hp
  have hn := (D.hom (i₁ := (coveringSieveOverFunctor R i).obj U) (i₂ := i)
    (U.hom ≫ i.obj.hom) (𝟙 U.left) U.hom).hom.naturality
      (Over.homMk f.left :
        (Over.map f.left).obj (Over.mk (𝟙 T.left)) ⟶ Over.mk (𝟙 U.left)).op
  dsimp at hn
  have hs :
      (D.obj ((coveringSieveOverFunctor R i).obj U)).obj.map
          (Over.homMk f.left :
            (Over.map f.left).obj (Over.mk (𝟙 T.left)) ⟶
              Over.mk (𝟙 U.left)).op ≫
        (((J.pseudofunctorOver (Type w)).mapComp'
          (𝟙 (op U.left)).toLoc f.left.op.toLoc f.left.op.toLoc
          (by simp)).hom.toNatTrans.app
            (D.obj ((coveringSieveOverFunctor R i).obj U))).hom.app
              (op (Over.mk (𝟙 T.left))) =
      (D.obj ((coveringSieveOverFunctor R i).obj U)).obj.map
          ((Over.mapId U.left).hom.app (Over.mk (𝟙 U.left))).op ≫
        (D.obj ((coveringSieveOverFunctor R i).obj U)).obj.map
          ((Over.map (𝟙 U.left)).map
            (Over.homMk f.left :
              (Over.map f.left).obj (Over.mk (𝟙 T.left)) ⟶
                Over.mk (𝟙 U.left))).op := by
    simp only [Pseudofunctor.mapComp', Iso.trans_hom, Cat.Hom₂.comp_app,
      PrelaxFunctor.map₂Iso_eqToIso,
      pseudofunctorOver_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj_α,
pseudofunctorOver_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map_toFunctor_obj_obj_obj,
      Quiver.Hom.toLoc_as, Quiver.Hom.unop_op, LocallyDiscrete.comp_as, unop_comp,
      Cat.Hom.comp_toFunctor, Functor.comp_obj, ObjectProperty.FullSubcategory.comp_hom,
      NatTrans.comp_app, pseudofunctorOver_mapComp_hom_toNatTrans_app_hom_app,
      eqToIso.hom, Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app,
      ObjectProperty.eqToHom_hom]
    rw [← eqToHom_map]
    · rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
      congr 1
      apply Quiver.Hom.unop_inj
      ext
      simp [Over.mapComp]
    · apply congrArg op
      simp
  have ht :
      (D.obj i).obj.map
          ((Over.map U.hom).map
            (Over.homMk f.left :
              (Over.map f.left).obj (Over.mk (𝟙 T.left)) ⟶
                Over.mk (𝟙 U.left))).op ≫
        (((J.pseudofunctorOver (Type w)).mapComp'
          U.hom.op.toLoc f.left.op.toLoc T.hom.op.toLoc
          (by
            change (f.left ≫ U.hom).op.toLoc = _
            rw [f.w])).inv.toNatTrans.app (D.obj i)).hom.app
            (op (Over.mk (𝟙 T.left))) ≫
        (D.obj i).obj.map (overMapIdentityIso T).inv.op =
      (D.obj i).obj.map (overMapIdentityIso U).inv.op ≫
        (D.obj i).obj.map f.op := by
    simp only [Pseudofunctor.mapComp', Iso.trans_inv, Cat.Hom₂.comp_app,
      PrelaxFunctor.map₂Iso_eqToIso,
      pseudofunctorOver_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj_α,
pseudofunctorOver_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map_toFunctor_obj_obj_obj,
      Quiver.Hom.toLoc_as, Quiver.Hom.unop_op, LocallyDiscrete.comp_as, unop_comp,
      Cat.Hom.comp_toFunctor, Functor.comp_obj, ObjectProperty.FullSubcategory.comp_hom,
      NatTrans.comp_app, pseudofunctorOver_mapComp_inv_toNatTrans_app_hom_app,
      eqToIso.inv, Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app,
      ObjectProperty.eqToHom_hom]
    rw [← eqToHom_map]
    · rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
          ← Functor.map_comp]
      congr 1
      apply Quiver.Hom.unop_inj
      ext
      simp [overMapIdentityIso, Over.mapComp]
    · apply congrArg op
      rw [← Over.w f]
  dsimp [coveringSieveOverFunctor] at hs hn
  rw [← hp]
  simp only [← Category.assoc]
  slice_lhs 1 2 => exact hs
  slice_lhs 2 3 => exact hn
  slice_lhs 3 5 => exact ht
  simp

/-- The presheaf extracted from descent data restricts, over every member of the
covering sieve, to the corresponding local sheaf. -/
noncomputable def restrictedPresheafLocalIso
    (D : (J.pseudofunctorOver (Type w)).DescentData
      (fun i : R.arrows.category ↦ i.obj.hom))
    (i : R.arrows.category) :
    (coveringSieveOverFunctor R i).op ⋙
        Pseudofunctor.DescentData.restrictedPresheaf J R D ≅
      (D.obj i).obj :=
  NatIso.ofComponents
    (fun T ↦ restrictedPresheafLocalObjIso J R D i T.unop)
    (by
      intro T U f
      exact restrictedPresheafLocalHom_naturality J R D i f.unop)

/-- Every local restriction of the presheaf extracted from descent data is a sheaf. -/
lemma restrictedPresheafLocal_isSheaf
    (D : (J.pseudofunctorOver (Type w)).DescentData
      (fun i : R.arrows.category ↦ i.obj.hom))
    (i : R.arrows.category) :
    Presheaf.IsSheaf (J.over i.obj.left)
      ((coveringSieveOverFunctor R i).op ⋙
        Pseudofunctor.DescentData.restrictedPresheaf J R D) :=
  (Presheaf.isSheaf_of_iso_iff (restrictedPresheafLocalIso J R D i)).2
    (D.obj i).property

/-- Pulling an object over `Y` toward either side of a descent square and then composing
into the covering sieve produces the same object of the sieve's arrow category. -/
lemma coveringSieveOverFunctor_mapObj_eq
    {Y : C} (q : Y ⟶ S) {i₁ i₂ : R.arrows.category}
    (f₁ : Y ⟶ i₁.obj.left) (f₂ : Y ⟶ i₂.obj.left)
    (hf₁ : f₁ ≫ i₁.obj.hom = q) (hf₂ : f₂ ≫ i₂.obj.hom = q)
    (T : Over Y) :
    (coveringSieveOverFunctor R i₂).obj ((Over.map f₂).obj T) =
      (coveringSieveOverFunctor R i₁).obj ((Over.map f₁).obj T) := by
  apply ObjectProperty.FullSubcategory.ext
  dsimp [coveringSieveOverFunctor]
  apply congrArg (fun h : T.left ⟶ S ↦ Over.mk h)
  change (T.hom ≫ f₂) ≫ i₂.obj.hom =
    (T.hom ≫ f₁) ≫ i₁.obj.hom
  rw [Category.assoc, hf₂, Category.assoc, hf₁]

lemma coveringSieveOverFunctor_eqToHom_left
    {Y : C} (q : Y ⟶ S) {i₁ i₂ : R.arrows.category}
    (f₁ : Y ⟶ i₁.obj.left) (f₂ : Y ⟶ i₂.obj.left)
    (hf₁ : f₁ ≫ i₁.obj.hom = q) (hf₂ : f₂ ≫ i₂.obj.hom = q)
    (T : Over Y) :
    (eqToHom (coveringSieveOverFunctor_mapObj_eq R q f₁ f₂ hf₁ hf₂ T)).hom.left =
      𝟙 T.left := by
  rw [ObjectProperty.eqToHom_hom, Over.eqToHom_left]
  rfl

lemma coveringSieveOverFunctor_eqToHom
    {Y : C} (q : Y ⟶ S) {i₁ i₂ : R.arrows.category}
    (f₁ : Y ⟶ i₁.obj.left) (f₂ : Y ⟶ i₂.obj.left)
    (hf₁ : f₁ ≫ i₁.obj.hom = q) (hf₂ : f₂ ≫ i₂.obj.hom = q)
    (T : Over Y) :
    (eqToHom (coveringSieveOverFunctor_mapObj_eq R q f₁ f₂ hf₁ hf₂ T)).hom =
      (Over.homMk (𝟙 T.left) (by
        dsimp [coveringSieveOverFunctor]
        simp only [Category.id_comp, Category.assoc, hf₁, hf₂]) :
        ((coveringSieveOverFunctor R i₂).obj ((Over.map f₂).obj T)).obj ⟶
          ((coveringSieveOverFunctor R i₁).obj ((Over.map f₁).obj T)).obj) := by
  ext
  exact coveringSieveOverFunctor_eqToHom_left R q f₁ f₂ hf₁ hf₂ T

lemma coveringSieveOverFunctor_eqToHom_full
    {Y : C} (q : Y ⟶ S) {i₁ i₂ : R.arrows.category}
    (f₁ : Y ⟶ i₁.obj.left) (f₂ : Y ⟶ i₂.obj.left)
    (hf₁ : f₁ ≫ i₁.obj.hom = q) (hf₂ : f₂ ≫ i₂.obj.hom = q)
    (T : Over Y) :
    eqToHom (coveringSieveOverFunctor_mapObj_eq R q f₁ f₂ hf₁ hf₂ T) =
      ObjectProperty.homMk (Over.homMk (𝟙 T.left) (by
        dsimp [coveringSieveOverFunctor]
        simp only [Category.id_comp, Category.assoc, hf₁, hf₂])) := by
  apply ObjectProperty.hom_ext
  exact coveringSieveOverFunctor_eqToHom R q f₁ f₂ hf₁ hf₂ T

def coveringSieveOverFunctorComparisonHom
    {Y : C} (q : Y ⟶ S) {i₁ i₂ : R.arrows.category}
    (f₁ : Y ⟶ i₁.obj.left) (f₂ : Y ⟶ i₂.obj.left)
    (hf₁ : f₁ ≫ i₁.obj.hom = q) (hf₂ : f₂ ≫ i₂.obj.hom = q)
    (T : Over Y) :
    (coveringSieveOverFunctor R i₂).obj ((Over.map f₂).obj T) ⟶
      (coveringSieveOverFunctor R i₁).obj ((Over.map f₁).obj T) :=
  ObjectProperty.homMk (Over.homMk (𝟙 T.left) (by
    dsimp [coveringSieveOverFunctor]
    simp only [Category.id_comp, Category.assoc, hf₁, hf₂]))

lemma descentHom_app_eq_pulled
    (D : (J.pseudofunctorOver (Type w)).DescentData
      (fun i : R.arrows.category ↦ i.obj.hom))
    {Y : C} (q : Y ⟶ S) {i₁ i₂ : R.arrows.category}
    (f₁ : Y ⟶ i₁.obj.left) (f₂ : Y ⟶ i₂.obj.left)
    (hf₁ : f₁ ≫ i₁.obj.hom = q) (hf₂ : f₂ ≫ i₂.obj.hom = q)
    (T : Over Y) :
    (D.hom (T.hom ≫ q) (T.hom ≫ f₁) (T.hom ≫ f₂)
          (by simp only [Category.assoc, hf₁])
          (by simp only [Category.assoc, hf₂])).hom.app
            (op (Over.mk (𝟙 T.left))) =
      ((((J.pseudofunctorOver (Type w)).mapComp'
          f₁.op.toLoc T.hom.op.toLoc (T.hom ≫ f₁).op.toLoc
          (by simp)).hom.toNatTrans.app (D.obj i₁))).hom.app
            (op (Over.mk (𝟙 T.left))) ≫
        (D.hom q f₁ f₂ hf₁ hf₂).hom.app
          (op ((Over.map T.hom).obj (Over.mk (𝟙 T.left)))) ≫
        ((((J.pseudofunctorOver (Type w)).mapComp'
          f₂.op.toLoc T.hom.op.toLoc (T.hom ≫ f₂).op.toLoc
          (by simp)).inv.toNatTrans.app (D.obj i₂))).hom.app
            (op (Over.mk (𝟙 T.left))) := by
  have hp := congrArg (fun k ↦ k.hom.app (op (Over.mk (𝟙 T.left))))
    (D.pullHom_hom T.hom q (T.hom ≫ q) rfl
      f₁ f₂ hf₁ hf₂ (T.hom ≫ f₁) (T.hom ≫ f₂) rfl rfl)
  dsimp [Pseudofunctor.LocallyDiscreteOpToCat.pullHom] at hp
  exact hp.symm

lemma descentHom_comp_component
    (D : (J.pseudofunctorOver (Type w)).DescentData
      (fun i : R.arrows.category ↦ i.obj.hom))
    {Y : C} (q : Y ⟶ S) {i₁ i₂ : R.arrows.category}
    (f₁ : Y ⟶ i₁.obj.left) (f₂ : Y ⟶ i₂.obj.left)
    (hf₁ : f₁ ≫ i₁.obj.hom = q) (hf₂ : f₂ ≫ i₂.obj.hom = q)
    (T : Over Y) :
    let U₁ := (Over.map f₁).obj T
    let j := (coveringSieveOverFunctor R i₁).obj U₁
    (D.hom (T.hom ≫ q) (i₁ := j) (i₂ := i₁)
          (𝟙 T.left) (T.hom ≫ f₁)
          (by simp [j, U₁, coveringSieveOverFunctor, hf₁])
          (by simp only [Category.assoc, hf₁])).hom.app
            (op (Over.mk (𝟙 T.left))) ≫
        (D.hom (T.hom ≫ q) (T.hom ≫ f₁) (T.hom ≫ f₂)
          (by simp only [Category.assoc, hf₁])
          (by simp only [Category.assoc, hf₂])).hom.app
            (op (Over.mk (𝟙 T.left))) =
      (D.hom (T.hom ≫ q) (i₁ := j) (i₂ := i₂)
          (𝟙 T.left) (T.hom ≫ f₂)
          (by simp [j, U₁, coveringSieveOverFunctor, hf₁])
          (by simp only [Category.assoc, hf₂])).hom.app
            (op (Over.mk (𝟙 T.left))) := by
  dsimp
  exact congrArg (fun k ↦ k.hom.app (op (Over.mk (𝟙 T.left))))
    (D.hom_comp (i₁ := (coveringSieveOverFunctor R i₁).obj
        ((Over.map f₁).obj T)) (i₂ := i₁) (i₃ := i₂)
      (T.hom ≫ q) (𝟙 T.left) (T.hom ≫ f₁)
      (T.hom ≫ f₂) (by simp [coveringSieveOverFunctor, hf₁])
      (by simp only [Category.assoc, hf₁])
      (by simp only [Category.assoc, hf₂]))

lemma descentHom_app_eq_pulled_identity
    (D : (J.pseudofunctorOver (Type w)).DescentData
      (fun i : R.arrows.category ↦ i.obj.hom))
    {Y : C} (q : Y ⟶ S) {i₁ i₂ : R.arrows.category}
    (f₁ : Y ⟶ i₁.obj.left) (f₂ : Y ⟶ i₂.obj.left)
    (hf₁ : f₁ ≫ i₁.obj.hom = q) (hf₂ : f₂ ≫ i₂.obj.hom = q)
    (T : Over Y) :
    (D.obj i₁).obj.map
          (overMapIdentityIso ((Over.map f₁).obj T)).inv.op ≫
        (D.hom q f₁ f₂ hf₁ hf₂).hom.app (op T) =
      (D.hom (T.hom ≫ q) (T.hom ≫ f₁) (T.hom ≫ f₂)
          (by simp only [Category.assoc, hf₁])
          (by simp only [Category.assoc, hf₂])).hom.app
            (op (Over.mk (𝟙 T.left))) ≫
        (D.obj i₂).obj.map
          (overMapIdentityIso ((Over.map f₂).obj T)).inv.op := by
  rw [descentHom_app_eq_pulled J R D q f₁ f₂ hf₁ hf₂ T]
  have hn := (D.hom q f₁ f₂ hf₁ hf₂).hom.naturality
    (overMapIdentityIso T).hom.op
  dsimp at hn
  rw [← cancel_mono ((D.obj i₂).obj.map
    ((Over.map f₂).map (overMapIdentityIso T).hom).op)]
  simp only [Category.assoc]
  rw [← hn]
  have ho₁ :
      (overMapIdentityIso ((Over.map f₁).obj T)).inv.op ≫
          ((Over.map f₁).map (overMapIdentityIso T).hom).op =
        ((Over.mapComp T.hom f₁).inv.app (Over.mk (𝟙 T.left))).op := by
    apply Quiver.Hom.unop_inj
    ext
    simp [overMapIdentityIso, Over.mapComp]
  have ho₂ :
      (overMapIdentityIso ((Over.map f₂).obj T)).inv.op ≫
          ((Over.map f₂).map (overMapIdentityIso T).hom).op =
        ((Over.mapComp T.hom f₂).inv.app (Over.mk (𝟙 T.left))).op := by
    apply Quiver.Hom.unop_inj
    ext
    simp [overMapIdentityIso, Over.mapComp]
  simp only [Pseudofunctor.mapComp', Iso.trans_hom, Iso.trans_inv,
    Cat.Hom₂.comp_app, PrelaxFunctor.map₂Iso_eqToIso,
    pseudofunctorOver_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj_α,
    pseudofunctorOver_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map_toFunctor_obj_obj_obj,
    Quiver.Hom.toLoc_as, Quiver.Hom.unop_op, LocallyDiscrete.comp_as, unop_comp,
    Cat.Hom.comp_toFunctor, Functor.comp_obj, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app, pseudofunctorOver_mapComp_hom_toNatTrans_app_hom_app,
    pseudofunctorOver_mapComp_inv_toNatTrans_app_hom_app, eqToIso.hom, eqToIso.inv,
    Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app, ObjectProperty.eqToHom_hom]
  simp only [← Functor.map_comp, ho₂, Category.assoc]
  slice_lhs 1 2 => rw [← Functor.map_comp, ho₁]
  simp

lemma restrictedPresheafLocalHom_descent
    (D : (J.pseudofunctorOver (Type w)).DescentData
      (fun i : R.arrows.category ↦ i.obj.hom))
    {Y : C} (q : Y ⟶ S) {i₁ i₂ : R.arrows.category}
    (f₁ : Y ⟶ i₁.obj.left) (f₂ : Y ⟶ i₂.obj.left)
    (hf₁ : f₁ ≫ i₁.obj.hom = q) (hf₂ : f₂ ≫ i₂.obj.hom = q)
    (T : Over Y) :
    let U₁ := (Over.map f₁).obj T
    let U₂ := (Over.map f₂).obj T
    restrictedPresheafLocalHom J R D i₁ U₁ ≫
        (D.hom q f₁ f₂ hf₁ hf₂).hom.app (op T) =
      (Pseudofunctor.DescentData.restrictedPresheaf J R D).map
          (coveringSieveOverFunctorComparisonHom R q f₁ f₂ hf₁ hf₂ T).op ≫
        restrictedPresheafLocalHom J R D i₂ U₂ := by
  dsimp
  simp only [restrictedPresheafLocalHom, Category.assoc]
  dsimp [Over.map]
  simp only [Category.assoc, hf₁, hf₂]
  slice_lhs 3 4 =>
    exact descentHom_app_eq_pulled_identity J R D q f₁ f₂ hf₁ hf₂ T
  have hc := descentHom_comp_component J R D q f₁ f₂ hf₁ hf₂ T
  slice_lhs 2 3 => exact hc
  simp only [Pseudofunctor.DescentData.restrictedPresheaf,
    coveringSieveOverFunctorComparisonHom, coveringSieveOverFunctor]
  simp only [overMapPullbackId_hom_app_hom_app,
    overMapPullbackId_inv_app_hom_app]
  dsimp [coveringSieveOverFunctor]
  slice_rhs 3 4 =>
    rw [← Functor.map_comp]
    simp
  simp only [Category.id_comp]
  simp only [Category.assoc, hf₂]
  let j₁ := (coveringSieveOverFunctor R i₁).obj ((Over.map f₁).obj T)
  let j₂ := (coveringSieveOverFunctor R i₂).obj ((Over.map f₂).obj T)
  have hd := congrArg (fun k ↦ k.hom.app (op (Over.mk (𝟙 T.left))))
    (D.hom_comp (i₁ := j₁) (i₂ := j₂) (i₃ := i₂)
      (T.hom ≫ q) (𝟙 T.left) (𝟙 T.left) (T.hom ≫ f₂)
      (by simp [j₁, coveringSieveOverFunctor, Category.assoc, hf₁])
      (by simp [j₂, coveringSieveOverFunctor, Category.assoc, hf₂])
      (by simp only [Category.assoc, hf₂]))
  dsimp at hd
  slice_rhs 2 3 => exact hd
  congr 2

lemma sheaf_map_coveringSieveComparisonHom
    (M : Sheaf (J.over S) (Type w))
    {Y : C} (q : Y ⟶ S) {i₁ i₂ : R.arrows.category}
    (f₁ : Y ⟶ i₁.obj.left) (f₂ : Y ⟶ i₂.obj.left)
    (hf₁ : f₁ ≫ i₁.obj.hom = q) (hf₂ : f₂ ≫ i₂.obj.hom = q)
    (T : Over Y) :
    M.obj.map
        ((ObjectProperty.ι (fun U : Over S ↦ R U.hom)).map
          (coveringSieveOverFunctorComparisonHom R q f₁ f₂ hf₁ hf₂ T)).op =
      ((((J.pseudofunctorOver (Type w)).mapComp'
          i₁.obj.hom.op.toLoc f₁.op.toLoc q.op.toLoc (by
            change (f₁ ≫ i₁.obj.hom).op.toLoc = q.op.toLoc
            rw [hf₁])).inv.toNatTrans.app M)).hom.app
            (op T) ≫
        ((((J.pseudofunctorOver (Type w)).mapComp'
          i₂.obj.hom.op.toLoc f₂.op.toLoc q.op.toLoc (by
            change (f₂ ≫ i₂.obj.hom).op.toLoc = q.op.toLoc
            rw [hf₂])).hom.toNatTrans.app M)).hom.app
            (op T) := by
  simp only [Pseudofunctor.mapComp', Iso.trans_hom, Iso.trans_inv,
    Cat.Hom₂.comp_app, PrelaxFunctor.map₂Iso_eqToIso,
    ObjectProperty.ι_obj, ObjectProperty.ι_map,
    pseudofunctorOver_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj_α,
    Cat.Hom.comp_toFunctor, Functor.comp_obj,
    pseudofunctorOver_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map_toFunctor_obj_obj_obj,
    Quiver.Hom.toLoc_as, Quiver.Hom.unop_op, LocallyDiscrete.comp_as, unop_comp,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    pseudofunctorOver_mapComp_hom_toNatTrans_app_hom_app,
    pseudofunctorOver_mapComp_inv_toNatTrans_app_hom_app, eqToIso.hom, eqToIso.inv,
    Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app, ObjectProperty.eqToHom_hom]
  rw [← eqToHom_map]
  · rw [← eqToHom_map]
    · simp only [← Functor.map_comp]
      congr 1
      apply Quiver.Hom.unop_inj
      ext
      simp only [unop_comp, Over.comp_left, Quiver.Hom.unop_op]
      rw [eqToHom_unop, Over.eqToHom_left]
      simp only [Over.map_obj_left, Over.mapComp_inv_app_left, eqToHom_refl,
        Category.comp_id, Over.mapComp_hom_app_left]
      rw [eqToHom_unop, Over.eqToHom_left]
      dsimp [coveringSieveOverFunctorComparisonHom]
      simp only [Category.comp_id]
    · rw [hf₂]
  · rw [hf₁]

/-- The presheaf extracted from descent data is a sheaf for the topology induced on
the cover-dense arrow subcategory. -/
lemma restrictedPresheaf_isSheaf_inducedTopology
    (hR : R ∈ J S)
    (D : (J.pseudofunctorOver (Type w)).DescentData
      (fun i : R.arrows.category ↦ i.obj.hom)) :
    Presheaf.IsSheaf
      ((ObjectProperty.ι (fun T : Over S ↦ R T.hom)).inducedTopology
        (J.over S))
      (Pseudofunctor.DescentData.restrictedPresheaf J R D) := by
  apply isSheaf_of_isSheaf_over_restrictions
  intro i
  let e := coveringSieveOverSliceEquivalence R i
  have hlocal := restrictedPresheafLocal_isSheaf J R D i
  have htransport := e.inverse.op_comp_isSheaf_of_isSheaf
    (e.inverse.inducedTopology (J.over i.obj.left))
    (J.over i.obj.left)
    ((coveringSieveOverFunctor R i).op ⋙
      Pseudofunctor.DescentData.restrictedPresheaf J R D) hlocal
  rw [coveringSieveOverSlice_inducedTopology J R hR i] at htransport
  exact (Presheaf.isSheaf_of_iso_iff
    (coveringSieveOverSliceInversePresheafIso R i
      (Pseudofunctor.DescentData.restrictedPresheaf J R D))).mp htransport

noncomputable def restrictedSheaf (hR : R ∈ J S)
    (D : (J.pseudofunctorOver (Type w)).DescentData
      (fun i : R.arrows.category ↦ i.obj.hom)) :
    Sheaf
      ((ObjectProperty.ι (fun T : Over S ↦ R T.hom)).inducedTopology
        (J.over S)) (Type w) :=
  ⟨Pseudofunctor.DescentData.restrictedPresheaf J R D,
    restrictedPresheaf_isSheaf_inducedTopology J R hR D⟩

/-- The sheaf on `Over S` obtained by applying the dense-subsite comparison theorem to
the presheaf extracted from the descent datum. -/
noncomputable def gluedSheaf (hR : R ∈ J S)
    (D : (J.pseudofunctorOver (Type w)).DescentData
      (fun i : R.arrows.category ↦ i.obj.hom))
    [∀ X : (Over S)ᵒᵖ, Limits.HasLimitsOfShape
      (StructuredArrow X
        (ObjectProperty.ι (fun T : Over S ↦ R T.hom)).op) (Type w)] :
    Sheaf (J.over S) (Type w) := by
  let _ : (ObjectProperty.ι
      (fun T : Over S ↦ R T.hom)).IsCoverDense (J.over S) :=
    coveringSieveInclusion_isCoverDense J R hR
  exact ((ObjectProperty.ι
    (fun T : Over S ↦ R T.hom)).sheafInducedTopologyEquivOfIsCoverDense
      (J.over S) (Type w)).functor.obj (restrictedSheaf J R hR D)

/-- The unit of dense-subsite comparison identifies the original restricted sheaf with
the restriction of the glued sheaf. -/
noncomputable def restrictedToGluedIso (hR : R ∈ J S)
    (D : (J.pseudofunctorOver (Type w)).DescentData
      (fun i : R.arrows.category ↦ i.obj.hom))
    [∀ X : (Over S)ᵒᵖ, Limits.HasLimitsOfShape
      (StructuredArrow X
        (ObjectProperty.ι (fun T : Over S ↦ R T.hom)).op) (Type w)] :
    Pseudofunctor.DescentData.restrictedPresheaf J R D ≅
      (ObjectProperty.ι (fun T : Over S ↦ R T.hom)).op ⋙
        (gluedSheaf J R hR D).obj := by
  let _ : (ObjectProperty.ι
      (fun T : Over S ↦ R T.hom)).IsCoverDense (J.over S) :=
    coveringSieveInclusion_isCoverDense J R hR
  let E := (ObjectProperty.ι
    (fun T : Over S ↦ R T.hom)).sheafInducedTopologyEquivOfIsCoverDense
      (J.over S) (Type w)
  exact (sheafToPresheaf _ _).mapIso
    (E.unitIso.app (restrictedSheaf J R hR D))

lemma restrictedToGluedIso_inv_naturality (hR : R ∈ J S)
    (D : (J.pseudofunctorOver (Type w)).DescentData
      (fun i : R.arrows.category ↦ i.obj.hom))
    [∀ X : (Over S)ᵒᵖ, Limits.HasLimitsOfShape
      (StructuredArrow X
        (ObjectProperty.ι (fun T : Over S ↦ R T.hom)).op) (Type w)]
    {i j : R.arrows.category} (f : i ⟶ j) :
    (gluedSheaf J R hR D).obj.map
          ((ObjectProperty.ι (fun T : Over S ↦ R T.hom)).map f).op ≫
        (restrictedToGluedIso J R hR D).inv.app (op i) =
      (restrictedToGluedIso J R hR D).inv.app (op j) ≫
        (Pseudofunctor.DescentData.restrictedPresheaf J R D).map f.op := by
  exact (restrictedToGluedIso J R hR D).inv.naturality f.op

noncomputable def gluedSheafLocalPresheafIso (hR : R ∈ J S)
    (D : (J.pseudofunctorOver (Type w)).DescentData
      (fun i : R.arrows.category ↦ i.obj.hom))
    [∀ X : (Over S)ᵒᵖ, Limits.HasLimitsOfShape
      (StructuredArrow X
        (ObjectProperty.ι (fun T : Over S ↦ R T.hom)).op) (Type w)]
    (i : R.arrows.category) :
    (Over.map i.obj.hom).op ⋙ (gluedSheaf J R hR D).obj ≅
      (D.obj i).obj :=
  coveringSieveOverFunctorPresheafIso R i (gluedSheaf J R hR D).obj ≪≫
    Functor.isoWhiskerLeft (coveringSieveOverFunctor R i).op
      (restrictedToGluedIso J R hR D).symm ≪≫
    restrictedPresheafLocalIso J R D i

lemma gluedSheafLocalPresheafIso_hom_app (hR : R ∈ J S)
    (D : (J.pseudofunctorOver (Type w)).DescentData
      (fun i : R.arrows.category ↦ i.obj.hom))
    [∀ X : (Over S)ᵒᵖ, Limits.HasLimitsOfShape
      (StructuredArrow X
        (ObjectProperty.ι (fun T : Over S ↦ R T.hom)).op) (Type w)]
    (i : R.arrows.category) (T : Over i.obj.left) :
    (gluedSheafLocalPresheafIso J R hR D i).hom.app (op T) =
      (restrictedToGluedIso J R hR D).inv.app
          (op ((coveringSieveOverFunctor R i).obj T)) ≫
        restrictedPresheafLocalHom J R D i T := by
  change (coveringSieveOverFunctorPresheafIso R i
      (gluedSheaf J R hR D).obj).hom.app (op T) ≫
        ((restrictedToGluedIso J R hR D).inv.app
          (op ((coveringSieveOverFunctor R i).obj T)) ≫
            restrictedPresheafLocalHom J R D i T) = _
  rw [show (coveringSieveOverFunctorPresheafIso R i
      (gluedSheaf J R hR D).obj).hom.app (op T) = 𝟙 _ from rfl]
  simp

/-- The glued sheaf pulls back to the prescribed local sheaf at every arrow of the
covering sieve. -/
noncomputable def gluedSheafLocalIso (hR : R ∈ J S)
    (D : (J.pseudofunctorOver (Type w)).DescentData
      (fun i : R.arrows.category ↦ i.obj.hom))
    [∀ X : (Over S)ᵒᵖ, Limits.HasLimitsOfShape
      (StructuredArrow X
        (ObjectProperty.ι (fun T : Over S ↦ R T.hom)).op) (Type w)]
    (i : R.arrows.category) :
    ((J.overMapPullback (Type w) i.obj.hom).obj (gluedSheaf J R hR D)) ≅
      D.obj i :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (gluedSheafLocalPresheafIso J R hR D i)

noncomputable def gluedDescentIso (hR : R ∈ J S)
    (D : (J.pseudofunctorOver (Type w)).DescentData
      (fun i : R.arrows.category ↦ i.obj.hom))
    [∀ X : (Over S)ᵒᵖ, Limits.HasLimitsOfShape
      (StructuredArrow X
        (ObjectProperty.ι (fun T : Over S ↦ R T.hom)).op) (Type w)] :
    ((J.pseudofunctorOver (Type w)).toDescentData
        (fun i : R.arrows.category ↦ i.obj.hom)).obj
          (gluedSheaf J R hR D) ≅ D :=
  Pseudofunctor.DescentData.isoMk (fun i ↦ gluedSheafLocalIso J R hR D i) (by
    intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
    apply (sheafToPresheaf (J.over Y) (Type w)).map_injective
    apply NatTrans.ext
    funext T
    simp only [
      pseudofunctorOver_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj_α,
      Pseudofunctor.toDescentData_obj, Pseudofunctor.DescentData.ofObj_obj,
      ObjectProperty.ι_obj,
pseudofunctorOver_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map_toFunctor_obj_obj_obj,
      Quiver.Hom.toLoc_as, Quiver.Hom.unop_op, gluedSheafLocalIso,
      Functor.FullyFaithful.preimageIso_hom, ObjectProperty.ι_map,
      ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
pseudofunctorOver_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map_toFunctor_map_hom_app,
      ObjectProperty.homMk_hom, Pseudofunctor.DescentData.ofObj_hom,
      Cat.Hom.comp_toFunctor, Category.assoc]
    rw [gluedSheafLocalPresheafIso_hom_app,
      gluedSheafLocalPresheafIso_hom_app]
    let k := coveringSieveOverFunctorComparisonHom R q f₁ f₂ hf₁ hf₂ T.unop
    slice_lhs 2 3 =>
      exact restrictedPresheafLocalHom_descent J R D q f₁ f₂ hf₁ hf₂ T.unop
    slice_lhs 1 2 =>
      exact (restrictedToGluedIso_inv_naturality J R hR D k).symm
    rw [sheaf_map_coveringSieveComparisonHom J R
      (gluedSheaf J R hR D) q f₁ f₂ hf₁ hf₂ T.unop]
    simp)

end EffectiveDescent

end CategoryTheory.GrothendieckTopology

/-- **Exercise 3.3.10** (`exer:gluing-sheaves`) (Gluing sheaves): sheaves on the members of
a covering, together with gluing isomorphisms on the overlaps satisfying the cocycle
condition, glue uniquely to a sheaf on the base: the pseudofunctor
`X ↦ Sheaf (J.over X) A` is a stack for `J`.

The formal proof constructs the glued sheaf by comparison with the cover-dense full
subcategory of arrows belonging to the covering sieve. -/
theorem CategoryTheory.GrothendieckTopology.isStack_pseudofunctorOver
    {𝒮 : Type u} [Category.{v} 𝒮] (J : GrothendieckTopology 𝒮) :
    (J.pseudofunctorOver (Type max u v u')).IsStack J := by
  refine { essSurj_of_sieve := ?_ }
  intro S R hR
  exact ⟨fun D ↦ ⟨J.gluedSheaf R hR D, ⟨J.gluedDescentIso R hR D⟩⟩⟩

end ExerGluingSheaves

section ExerCoversAreEpimorphisms

open CategoryTheory Opposite Limits AlgebraicGeometry

universe v u

/-- If a covering sieve of `Y` consists of arrows factoring through `f : X ⟶ Y`, then
`yoneda.map f` is locally surjective. This isolates the categorical content of the fact
that a cover (or a map refined by a cover) is an epimorphism of sheaves. -/
lemma CategoryTheory.Presheaf.isLocallySurjective_yoneda_map_of_covering_le
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {X Y : C} (f : X ⟶ Y)
    {R : Sieve Y} (hR : R ∈ J Y) (hle : R ≤ Sieve.generate (Presieve.singleton f)) :
    Presheaf.IsLocallySurjective J (yoneda.map f) where
  imageSieve_mem {T} g := by
    refine J.superset_covering ?_ (J.pullback_stable g hR)
    intro Z h hh
    obtain ⟨W, k, j, hj, hk⟩ := hle (h ≫ g) hh
    cases hj
    refine ⟨k, ?_⟩
    simpa using hk

/-- Let `K` be a precoverage on a category `C` with pullbacks, stable under base change, and
let `f : X ⟶ Y` be a morphism such that the singleton family `{f}` is a covering. Then
`yoneda.map f` is locally surjective for the Grothendieck topology generated by `K`: every
morphism `T ⟶ Y` lifts to `X` after base change along the covering `T ×_Y X ⟶ T`. -/
lemma CategoryTheory.Presheaf.isLocallySurjective_yoneda_map_of_singleton_mem
    {C : Type u} [Category.{v} C] [HasPullbacks C] (K : Precoverage C)
    [K.IsStableUnderBaseChange] {X Y : C} (f : X ⟶ Y) (hf : Presieve.singleton f ∈ K Y) :
    Presheaf.IsLocallySurjective K.toGrothendieck (yoneda.map f) where
  imageSieve_mem {T} g := by
    have hpb : Presieve.ofArrows (fun (_ : PUnit.{1}) ↦ pullback g f)
        (fun _ ↦ pullback.fst g f) ∈ K T := by
      refine Precoverage.mem_coverings_of_isPullback (fun (_ : PUnit.{1}) ↦ f) ?_ g _
        (fun _ ↦ pullback.snd g f) (fun _ ↦ IsPullback.of_hasPullback g f)
      rwa [Presieve.ofArrows_pUnit]
    refine K.toGrothendieck.superset_covering ?_
      (Precoverage.generate_mem_toGrothendieck hpb)
    rw [Sieve.generate_le_iff]
    rintro Z h ⟨i⟩
    exact ⟨pullback.snd g f, pullback.condition.symm⟩

/-- A singleton covering in a pullback-stable precoverage induces an epimorphism between
the associated representable sheaves. -/
theorem CategoryTheory.Sheaf.epi_yoneda_map_of_singleton_mem
    {C : Type u} [Category.{v} C] [HasPullbacks C] (K : Precoverage C)
    [K.IsStableUnderBaseChange] [K.toGrothendieck.Subcanonical] {X Y : C} (f : X ⟶ Y)
    (hf : Presieve.singleton f ∈ K Y) : Epi (K.toGrothendieck.yoneda.map f) := by
  have : Presheaf.IsLocallySurjective K.toGrothendieck (yoneda.map f) :=
    Presheaf.isLocallySurjective_yoneda_map_of_singleton_mem K f hf
  have : Sheaf.IsLocallySurjective (K.toGrothendieck.yoneda.map f) := this
  infer_instance

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Exercise 3.3.11** (`exer:covers-are-epimorphisms`) (fppf case): a surjective, flat
morphism of schemes which is locally of finite presentation (i.e. an fppf morphism) is an
epimorphism of sheaves on the big fppf site. -/
theorem epi_yoneda_map_of_fppf [Flat f] [LocallyOfFinitePresentation f] [Surjective f] :
    Epi (Scheme.fppfTopology.yoneda.map f) := by
  exact Sheaf.epi_yoneda_map_of_singleton_mem _ f f.singleton_mem_fppfPrecoverage

/-- **Exercise 3.3.11** (`exer:covers-are-epimorphisms`) (fpqc case, general form): a
singleton fpqc covering in the book's generalized sense is an epimorphism of sheaves on the
big fpqc site. -/
theorem epi_yoneda_map_of_fpqcCover (hf : Scheme.IsFpqcCover f) :
    Epi (Scheme.fpqcTopology.yoneda.map f) := by
  exact Sheaf.epi_yoneda_map_of_singleton_mem _ f hf

/-- Supporting special case of Exercise 3.3.11 (quasi-compact fpqc cover): a surjective, flat,
quasi-compact morphism of schemes is an epimorphism of sheaves on the big fpqc site. This
is the common globally quasi-compact special case of `epi_yoneda_map_of_fpqcCover`. -/
theorem epi_yoneda_map_of_fpqc [Flat f] [QuasiCompact f] [Surjective f] :
    Epi (Scheme.fpqcTopology.yoneda.map f) :=
  epi_yoneda_map_of_fpqcCover f (Scheme.IsFpqcCover.of_flat_of_surjective_of_quasiCompact f)

/-- A scheme morphism refined by an étale covering sieve is an epimorphism of sheaves on
the big étale site. The geometric input needed for a smooth surjection is precisely the
existence of such a refinement (Stacks, Tag 055V). -/
theorem epi_yoneda_map_of_etale_covering_le {R : Sieve Y}
    (hR : R ∈ Scheme.etaleTopology Y)
    (hle : R ≤ Sieve.generate (Presieve.singleton f)) :
    Epi (Scheme.etaleTopology.yoneda.map f) := by
  have : Presheaf.IsLocallySurjective Scheme.etaleTopology (CategoryTheory.yoneda.map f) :=
    Presheaf.isLocallySurjective_yoneda_map_of_covering_le _ f hR hle
  have : Sheaf.IsLocallySurjective (Scheme.etaleTopology.yoneda.map f) := this
  infer_instance

/-- A surjective smooth morphism having étale-local sections is an epimorphism on the big
étale site. This separates the formal covering refinement of Stacks 055V from the
geometric local-section theorem 055U. -/
theorem epi_yoneda_map_of_smooth_of_hasEtaleLocalSections [Smooth f] [Surjective f]
    (hlocal : Scheme.Hom.HasEtaleLocalSections f) :
    Epi (Scheme.etaleTopology.yoneda.map f) := by
  obtain ⟨R, hR, hle⟩ := Scheme.Hom.exists_etale_sieve_le_of_hasEtaleLocalSections f hlocal
  exact epi_yoneda_map_of_etale_covering_le f hR hle

/-- **Exercise 3.3.11** (`exer:covers-are-epimorphisms`) (smooth case): a surjective smooth
morphism of schemes is an epimorphism of sheaves on the big étale site. (The proof requires
that a smooth surjection admits sections étale-locally.) -/
theorem epi_yoneda_map_of_smooth [Smooth f] [Surjective f] :
    Epi (Scheme.etaleTopology.yoneda.map f) := by
  exact epi_yoneda_map_of_smooth_of_hasEtaleLocalSections f
    (Scheme.Hom.hasEtaleLocalSections_of_smooth' f)

end AlgebraicGeometry.Scheme

end ExerCoversAreEpimorphisms
