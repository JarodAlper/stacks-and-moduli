module

public import StacksAndModuli.API.OverPresheafTotal
public import StacksAndModuli.«Section4.1-Definitions».«part4.1.1-representable-morphisms-and-algebraic-spaces»

/-!
# Presheaves relative to a representable base

An arrow from a presheaf `F` to a representable presheaf `yoneda.obj S` determines
a presheaf on the slice category `Over S`: its sections over `T ⟶ S` are the
sections of `F` lying over that morphism.  Conversely, taking the total presheaf of
this relative presheaf recovers `F`, compatibly with the maps to `yoneda.obj S`.

This file also proves that the relative presheaf is a sheaf whenever `F` is a sheaf
for a subcanonical topology.  Thus a representation on the slice site gives an
isomorphism of the original arrow with a Yoneda arrow.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits Opposite ConcreteCategory

universe v u

namespace CategoryTheory.PresheafOver

variable {C : Type u} [Category.{v} C] {S : C}

/-- A natural transformation of presheaves on a slice induces a natural
transformation of their total presheaves. -/
def map {G H : (Over S)ᵒᵖ ⥤ Type v} (α : G ⟶ H) :
    total G ⟶ total H where
  app _ := TypeCat.ofHom fun x ↦ ⟨x.1, α.app _ x.2⟩
  naturality := by
    intro X Y f
    apply ConcreteCategory.hom_ext
    rintro ⟨a, x⟩
    dsimp only [total]
    simp only [types_comp_apply, TypeCat.ofHom_apply]
    let h : Over.mk (f.unop ≫ a) ⟶ Over.mk a := Over.homMk f.unop
    change (⟨f.unop ≫ a,
        α.app (op (Over.mk (f.unop ≫ a))) (G.map h.op x)⟩ :
        Σ b, H.obj (op (Over.mk b))) =
      ⟨f.unop ≫ a, H.map h.op (α.app (op (Over.mk a)) x)⟩
    rw [Sigma.mk.injEq]
    exact ⟨rfl, heq_of_eq (NatTrans.naturality_apply α h.op x)⟩

@[simp]
lemma map_app_fst {G H : (Over S)ᵒᵖ ⥤ Type v} (α : G ⟶ H)
    (X : Cᵒᵖ) (x : (total G).obj X) :
    ((map α).app X x).1 = x.1 := rfl

/-- Taking the total presheaf is functorial. -/
def functor : ((Over S)ᵒᵖ ⥤ Type v) ⥤ (Cᵒᵖ ⥤ Type v) where
  obj := total
  map := map
  map_id G := by
    ext X x
    rfl
  map_comp α β := by
    ext X x
    rfl

/-- The total presheaf of a presheaf on `Over S` maps canonically to the
representable presheaf of `S`. -/
def toBase (G : (Over S)ᵒᵖ ⥤ Type v) : total G ⟶ yoneda.obj S where
  app _ := TypeCat.ofHom Sigma.fst
  naturality := by
    intro X Y f
    apply ConcreteCategory.hom_ext
    intro x
    rfl

/-- The total presheaf, regarded as an object over `yoneda.obj S`. -/
def overObj (G : (Over S)ᵒᵖ ⥤ Type v) : Over (yoneda.obj S) :=
  Over.mk (toBase G)

/-- A natural transformation on a slice induces a morphism between the
corresponding total presheaves over `yoneda.obj S`. -/
def overMap {G H : (Over S)ᵒᵖ ⥤ Type v} (α : G ⟶ H) :
    overObj G ⟶ overObj H :=
  Over.homMk (map α) (by
    apply NatTrans.ext
    funext X
    apply ConcreteCategory.hom_ext
    intro x
    rfl)

/-- Taking total presheaves as a functor into the category over
`yoneda.obj S`. -/
def overFunctor : ((Over S)ᵒᵖ ⥤ Type v) ⥤ Over (yoneda.obj S) where
  obj := overObj
  map := overMap
  map_id G := by
    ext
    rfl
  map_comp α β := by
    ext
    rfl

/-- The total presheaf of the Yoneda presheaf of an object over `S` is the
Yoneda presheaf of its source. -/
def yonedaTotalIso (Z : Over S) :
    total (yoneda.obj Z) ≅ yoneda.obj Z.left where
  hom :=
    { app := fun _ ↦ TypeCat.ofHom fun x ↦ x.2.left
      naturality := by
        intro X Y f
        apply ConcreteCategory.hom_ext
        intro x
        rfl }
  inv :=
    { app := fun _ ↦ TypeCat.ofHom fun f ↦
        ⟨f ≫ Z.hom, Over.homMk f⟩
      naturality := by
        intro X Y f
        apply ConcreteCategory.hom_ext
        intro g
        dsimp only [total]
        simp only [types_comp_apply, TypeCat.ofHom_apply,
          CategoryTheory.yoneda_obj_map]
        rw [Sigma.mk.injEq]
        constructor
        · simp [Category.assoc]
        · let A : Over S := Over.mk ((f.unop ≫ g) ≫ Z.hom)
          let B : Over S := Over.mk (f.unop ≫ (g ≫ Z.hom))
          let e : A = B := congrArg Over.mk (Category.assoc _ _ _)
          change (Over.homMk (f.unop ≫ g) : A ⟶ Z) ≍
            ((Over.homMk f.unop : B ⟶ Over.mk (g ≫ Z.hom)) ≫
              Over.homMk g)
          apply (CategoryTheory.conj_eqToHom_iff_heq _ _ e rfl).1
          apply CategoryTheory.CostructuredArrow.hom_ext
          simp [A, B] }
  hom_inv_id := by
    ext X f
    obtain ⟨a, x⟩ := f
    change (⟨x.left ≫ Z.hom, Over.homMk x.left⟩ :
      Σ b, (yoneda.obj Z).obj (op (Over.mk b))) = ⟨a, x⟩
    rw [Sigma.mk.injEq]
    constructor
    · exact x.w
    · let A : Over S := Over.mk (x.left ≫ Z.hom)
      let B : Over S := Over.mk a
      let e : A = B := congrArg Over.mk x.w
      change (Over.homMk x.left : A ⟶ Z) ≍ (x : B ⟶ Z)
      apply (CategoryTheory.conj_eqToHom_iff_heq _ _ e rfl).1
      apply CategoryTheory.CostructuredArrow.hom_ext
      simp [A, B]
  inv_hom_id := by
    ext X x
    rfl

/-- The total Yoneda isomorphism, compatibly with the arrows to the base. -/
def yonedaTotalOverIso (Z : Over S) :
    overObj (yoneda.obj Z) ≅ Over.mk (yoneda.map Z.hom) :=
  Over.isoMk (yonedaTotalIso Z) (by
    apply NatTrans.ext
    funext X
    apply ConcreteCategory.hom_ext
    intro x
    exact x.2.w)

/-- A presheaf on a slice is a sheaf if its total presheaf is a sheaf. -/
theorem isSheaf_of_isSheaf_total (J : GrothendieckTopology C) [J.Subcanonical]
    (G : (Over S)ᵒᵖ ⥤ Type v) (hG : Presieve.IsSheaf J (total G)) :
    Presieve.IsSheaf (J.over S) G := by
  intro B R hR
  obtain ⟨B, b, rfl⟩ := B.mk_surjective
  let Rbase : Sieve B := Sieve.overEquiv (Over.mk b) R
  have hRbase : Rbase ∈ J B := by
    exact (J.mem_over_iff R).mp hR
  obtain ⟨I, X, f, hf⟩ := Rbase.exists_eq_ofArrows
  have hTotal : Presieve.IsSheafFor (total G) (Presieve.ofArrows X f) := by
    apply hG.isSheafFor
    change Sieve.ofArrows X f ∈ J B
    rw [← hf]
    exact hRbase
  have hRepresentable : Presieve.IsSeparatedFor (yoneda.obj S)
      (Presieve.ofArrows X f) := by
    exact ((GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
      (yoneda.obj S)).isSheafFor _ (by
        change Sieve.ofArrows X f ∈ J B
        rw [← hf]
        exact hRbase)).isSeparatedFor
  have hlift := isSheafFor_lift_of_total G f b hTotal hRepresentable
  have hgen := (Presieve.isSheafFor_iff_generate
    (Presieve.ofArrows (liftObj f b) (liftHom f b))).mp hlift
  rw [generate_lift_eq_overEquiv_symm, ← hf] at hgen
  simpa [Rbase] using hgen

end CategoryTheory.PresheafOver

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C] {S : C}
  {F : Cᵒᵖ ⥤ Type v}

/-- The presheaf on `Over S` obtained from an arrow `F ⟶ yoneda.obj S` by
taking the sections of `F` lying over each morphism to `S`. -/
def relativeOver (η : F ⟶ yoneda.obj S) : (Over S)ᵒᵖ ⥤ Type v :=
  (BasedCategory.overToCostructuredArrowYoneda S).op ⋙
    OverPresheafAux.restrictedYonedaObj η

/-- The pointwise Yoneda comparison for the relative presheaf of a Yoneda
arrow. -/
noncomputable def relativeOverYonedaComponentIso (Z : Over S)
    (A : (Over S)ᵒᵖ) :
    (yoneda.obj Z).obj A ≅
      (relativeOver (yoneda.map Z.hom)).obj A :=
  Equiv.toIso
    { toFun := fun f ↦ OverPresheafAux.OverArrows.yonedaArrow f.left (by
          rw [← yoneda.map_comp, f.w]
          rfl)
      invFun := fun p ↦ Over.homMk p.val (by
        apply yoneda.map_injective
        rw [yoneda.map_comp]
        exact p.map_val)
      left_inv := fun f ↦ by
        apply CategoryTheory.CostructuredArrow.hom_ext
        rfl
      right_inv := fun p ↦ by
        apply OverPresheafAux.OverArrows.ext
        rfl }

/-- The relative presheaf of the Yoneda image of `Z ⟶ S` is represented by
the same object of `Over S`. -/
noncomputable def relativeOverYonedaIso (Z : Over S) :
    yoneda.obj Z ≅ relativeOver (yoneda.map Z.hom) :=
  NatIso.ofComponents (relativeOverYonedaComponentIso Z) (by
    intro A B f
    apply ConcreteCategory.hom_ext
    intro g
    apply OverPresheafAux.OverArrows.ext
    rfl)

/-- An isomorphism of arrows over a representable base induces an isomorphism
of their relative presheaves. -/
def relativeOverMapIso {G : Cᵒᵖ ⥤ Type v}
    {η : F ⟶ yoneda.obj S} {μ : G ⟶ yoneda.obj S}
    (e : Over.mk η ≅ Over.mk μ) :
    relativeOver η ≅ relativeOver μ :=
  Functor.isoWhiskerLeft
    (BasedCategory.overToCostructuredArrowYoneda S).op
    ((OverPresheafAux.restrictedYoneda (yoneda.obj S)).mapIso e)

/-- The pointwise comparison underlying `relativeOverPullbackIso`. -/
noncomputable def relativeOverPullbackComponentIso
    {S' : C} (p : S' ⟶ S) (η : F ⟶ yoneda.obj S) (A : (Over S')ᵒᵖ) :
    (relativeOver (pullback.snd η (yoneda.map p))).obj A ≅
      ((Over.map p).op ⋙ relativeOver η).obj A := by
  dsimp only [relativeOver, Functor.comp_obj,
    BasedCategory.overToCostructuredArrowYoneda,
    OverPresheafAux.restrictedYonedaObj, Over.map]
  change OverPresheafAux.OverArrows
      (pullback.snd η (yoneda.map p)) (yoneda.map A.unop.hom) ≅
    OverPresheafAux.OverArrows η (yoneda.map (A.unop.hom ≫ p))
  exact Equiv.toIso
    { toFun := fun z ↦ ⟨(pullback.fst η (yoneda.map p)).app _ z.val, ⟨by
          have h := congr_hom
            (congr_app (pullback.condition (f := η) (g := yoneda.map p))
              (op A.unop.left)) z.val
          simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h
          rw [z.app_val] at h
          simpa only [yoneda_map_app, ConcreteCategory.hom_ofHom,
            TypeCat.Fun.coe_mk, yonedaEquiv_yoneda_map] using h⟩⟩
      invFun := fun x ↦ by
        have hx : yonedaEquiv.symm x.val ≫ η =
            yoneda.map A.unop.hom ≫ yoneda.map p := by
          apply yonedaEquiv.injective
          simp only [yonedaEquiv_comp, Equiv.apply_symm_apply,
            x.app_val, yonedaEquiv_yoneda_map,
            yoneda_map_app, ConcreteCategory.hom_ofHom,
            TypeCat.Fun.coe_mk]
        let l : yoneda.obj A.unop.left ⟶ pullback η (yoneda.map p) :=
          pullback.lift (yonedaEquiv.symm x.val) (yoneda.map A.unop.hom) hx
        exact ⟨yonedaEquiv l, OverPresheafAux.MakesOverArrow.of_arrow (by
          exact pullback.lift_snd _ _ _)⟩
      left_inv := by
        intro z
        apply OverPresheafAux.OverArrows.ext
        change yonedaEquiv (pullback.lift
          (yonedaEquiv.symm ((pullback.fst η (yoneda.map p)).app _ z.val))
          (yoneda.map A.unop.hom) _) = z.val
        apply yonedaEquiv.symm.injective
        rw [Equiv.symm_apply_apply]
        apply pullback.hom_ext
        · rw [pullback.lift_fst]
          apply yonedaEquiv.injective
          simp only [Equiv.apply_symm_apply, yonedaEquiv_comp]
        · rw [pullback.lift_snd]
          apply yonedaEquiv.injective
          simp only [yonedaEquiv_yoneda_map, yonedaEquiv_comp,
            Equiv.apply_symm_apply, z.app_val]
      right_inv := by
        intro x
        apply OverPresheafAux.OverArrows.ext
        change (pullback.fst η (yoneda.map p)).app _
          (yonedaEquiv (pullback.lift (yonedaEquiv.symm x.val)
            (yoneda.map A.unop.hom) _)) = x.val
        rw [← yonedaEquiv_comp, pullback.lift_fst,
          Equiv.apply_symm_apply] }

/-- Restricting the relative presheaf of an arrow along `p : S' ⟶ S` agrees
with taking the relative presheaf of the absolute presheaf pullback along
`yoneda.map p`. -/
noncomputable def relativeOverPullbackIso
    {S' : C} (p : S' ⟶ S) (η : F ⟶ yoneda.obj S) :
    relativeOver (pullback.snd η (yoneda.map p)) ≅
      (Over.map p).op ⋙ relativeOver η :=
  NatIso.ofComponents (relativeOverPullbackComponentIso p η) (by
    intro A B f
    apply ConcreteCategory.hom_ext
    intro z
    apply OverPresheafAux.OverArrows.ext
    dsimp only [relativeOverPullbackComponentIso,
      Equiv.toFun_as_coe, Equiv.coe_fn_mk, Functor.comp_map,
      relativeOver, BasedCategory.overToCostructuredArrowYoneda,
      OverPresheafAux.restrictedYonedaObj]
    change (pullback.fst η (yoneda.map p)).app (op B.unop.left)
        ((pullback η (yoneda.map p)).map f.unop.left.op z.val) =
      F.map f.unop.left.op
        ((pullback.fst η (yoneda.map p)).app (op A.unop.left) z.val)
    exact NatTrans.naturality_apply
      (pullback.fst η (yoneda.map p)) f.unop.left.op z.val)

/-- Taking the total presheaf of `relativeOver η` recovers the source of
`η`. -/
def relativeOverTotalIso (η : F ⟶ yoneda.obj S) :
    PresheafOver.total (relativeOver η) ≅ F where
  hom :=
    { app := fun _ ↦ TypeCat.ofHom fun x ↦ x.2.val
      naturality := by
        intro X Y f
        apply ConcreteCategory.hom_ext
        intro x
        rfl }
  inv :=
    { app := fun X ↦ TypeCat.ofHom fun x ↦
        ⟨η.app X x, ⟨x, ⟨by
          change η.app X x = yonedaEquiv (yoneda.map (η.app X x))
          exact (yonedaEquiv_yoneda_map _).symm⟩⟩⟩
      naturality := by
        intro X Y f
        apply ConcreteCategory.hom_ext
        intro x
        dsimp only [PresheafOver.total, relativeOver,
          BasedCategory.overToCostructuredArrowYoneda]
        simp only [types_comp_apply, TypeCat.ofHom_apply]
        have hbase := NatTrans.naturality_apply η f x
        have hbase' : η.app Y (F.map f x) = f.unop ≫ η.app X x := by
          simpa only [CategoryTheory.yoneda_obj_map,
            TypeCat.ofHom_apply] using hbase
        rw [Sigma.mk.injEq]
        constructor
        · exact hbase'
        · let A := η.app Y (F.map f x)
          let B := f.unop ≫ η.app X x
          change (⟨F.map f x, _⟩ :
              OverPresheafAux.OverArrows η (yoneda.map A)) ≍
            (OverPresheafAux.OverArrows.map₂ ⟨x, _⟩ f.unop (by
              change yoneda.map f.unop ≫ yoneda.map (η.app X x) =
                yoneda.map B
              rw [← yoneda.map_comp]) :
              OverPresheafAux.OverArrows η (yoneda.map B))
          have hpred : ∀ z : F.obj Y,
              OverPresheafAux.MakesOverArrow η (yoneda.map A) z ↔
                OverPresheafAux.MakesOverArrow η (yoneda.map B) z := by
            intro z
            constructor
            · intro hz
              have hz' : η.app Y z = A := by
                simpa only [yonedaEquiv_yoneda_map] using hz.app
              exact ⟨by
                simpa only [yonedaEquiv_yoneda_map] using hz'.trans hbase'⟩
            · intro hz
              have hz' : η.app Y z = B := by
                simpa only [yonedaEquiv_yoneda_map] using hz.app
              exact ⟨by
                simpa only [yonedaEquiv_yoneda_map] using hz'.trans hbase'.symm⟩
          apply (Subtype.heq_iff_coe_eq hpred).2
          rfl }
  hom_inv_id := by
    ext X x
    obtain ⟨a, x⟩ := x
    change OverPresheafAux.OverArrows η (yoneda.map a) at x
    have hbase : η.app X x.val = a := by
      simpa only [yonedaEquiv_yoneda_map] using x.app_val
    change (⟨η.app X x.val, ⟨x.val, _⟩⟩ :
      Σ b, OverPresheafAux.OverArrows η (yoneda.map b)) = ⟨a, x⟩
    rw [Sigma.mk.injEq]
    constructor
    · exact hbase
    · let A := η.app X x.val
      let B := a
      have hpred : ∀ z : F.obj X,
          OverPresheafAux.MakesOverArrow η (yoneda.map A) z ↔
            OverPresheafAux.MakesOverArrow η (yoneda.map B) z := by
        intro z
        constructor
        · intro hz
          have hz' : η.app X z = A := by
            simpa only [yonedaEquiv_yoneda_map] using hz.app
          exact ⟨by
            simpa only [yonedaEquiv_yoneda_map] using hz'.trans hbase⟩
        · intro hz
          have hz' : η.app X z = B := by
            simpa only [yonedaEquiv_yoneda_map] using hz.app
          exact ⟨by
            simpa only [yonedaEquiv_yoneda_map] using hz'.trans hbase.symm⟩
      apply (Subtype.heq_iff_coe_eq hpred).2
      rfl
  inv_hom_id := by
    ext X x
    rfl

/-- The total-presheaf comparison, compatibly with the maps to
`yoneda.obj S`. -/
def relativeOverTotalOverIso (η : F ⟶ yoneda.obj S) :
    PresheafOver.overObj (relativeOver η) ≅ Over.mk η :=
  Over.isoMk (relativeOverTotalIso η) (by
    apply NatTrans.ext
    funext X
    apply ConcreteCategory.hom_ext
    intro x
    let z : OverPresheafAux.OverArrows η (yoneda.map x.1) := x.2
    change η.app X z.val = x.1
    simpa only [yonedaEquiv_yoneda_map] using z.app_val)

/-- A representation of the relative presheaf gives an isomorphism, over the
representable base, between the original arrow and a Yoneda arrow. -/
def relativeOverRepresentationOverIso (η : F ⟶ yoneda.obj S) (Z : Over S)
    (e : yoneda.obj Z ≅ relativeOver η) :
    Over.mk (yoneda.map Z.hom) ≅ Over.mk η :=
  (PresheafOver.yonedaTotalOverIso Z).symm ≪≫
    (PresheafOver.overFunctor.mapIso e) ≪≫
      relativeOverTotalOverIso η

/-- The arrow-category form of `relativeOverRepresentationOverIso`. -/
def relativeOverRepresentationArrowIso (η : F ⟶ yoneda.obj S) (Z : Over S)
    (e : yoneda.obj Z ≅ relativeOver η) :
    Arrow.mk (yoneda.map Z.hom) ≅ Arrow.mk η := by
  let eOver := relativeOverRepresentationOverIso η Z e
  let eSource : yoneda.obj Z.left ≅ F := (Over.forget _).mapIso eOver
  exact Arrow.isoMk eSource (Iso.refl _) (by
    simpa [eSource, eOver] using eOver.hom.w)

/-- The relative presheaf of a sheaf over a representable base is a sheaf on the
slice site. -/
theorem relativeOver_isSheaf (J : GrothendieckTopology C) [J.Subcanonical]
    (η : F ⟶ yoneda.obj S) (hF : Presieve.IsSheaf J F) :
    Presieve.IsSheaf (J.over S) (relativeOver η) := by
  apply PresheafOver.isSheaf_of_isSheaf_total J
  exact Presieve.isSheaf_iso J (relativeOverTotalIso η).symm hF

end CategoryTheory.Presheaf
