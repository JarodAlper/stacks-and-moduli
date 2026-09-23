module

public import StacksAndModuli.API.PresheafPrestackComparison
public import StacksAndModuli.API.PrestackComponents
public import StacksAndModuli.API.FiberProductEquivalence
public import StacksAndModuli.«Section3.5-Stacks».«part3.5.2-first-examples»

/-!
# Presheaves represented by stacks are sheaves

If the category-of-elements prestack of a presheaf is equivalent, over the base site,
to a stack, then the presheaf is a sheaf.  This is the universe-flexible form of the
forward implication in `CategoryTheory.Functor.isStack_proj_yoneda_iff`: it avoids first
transporting the entire stack structure across an equivalence of total categories.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Opposite

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

namespace BasedFunctor

variable {C : Type u₁} [Category.{v₁} C]

/-- A based functor reflects the base arrow over which a morphism lies. -/
lemma reflects_isHomLift
    {A : BasedCategory.{v₂, u₂} C} {B : BasedCategory.{v₃, u₃} C}
    (E : BasedFunctor A B) {R S : C} {a b : A.obj}
    (f : R ⟶ S) (q : a ⟶ b) (h : IsHomLift B.p f (E.map q)) :
    IsHomLift A.p f q := by
  letI : IsHomLift E.toFunctor (E.map q) q :=
    IsHomLift.map (p := E.toFunctor) q
  letI : IsHomLift B.p f (E.map q) := h
  have h' : IsHomLift (E.toFunctor ⋙ B.p) f q :=
    Functor.IsFiberedInGroupoids.comp_isHomLift
      E.toFunctor B.p (E.map q) f q
  rw [E.w] at h'
  exact h'

end BasedFunctor

namespace BasedCategory

variable {C : Type u₁} [Category.{v₁} C]
  {F : Cᵒᵖ ⥤ Type v₂} {R S : C}

/-- The presheaf element classified by an object in a fiber of the
universe-polymorphic category-of-elements prestack. -/
def elementsFiberElement (a : (elementsPrestack F).p.Fiber S) :
    F.obj (op S) := by
  rw [← a.2]
  exact a.1.unop.2

/-- The canonical fiber object classified by a presheaf element. -/
def elementsFiberObj (x : F.obj (op S)) :
    (elementsPrestack F).p.Fiber S :=
  ⟨op ⟨op S, x⟩, rfl⟩

@[simp]
lemma elementsFiberElement_elementsFiberObj (x : F.obj (op S)) :
    elementsFiberElement (elementsFiberObj x) = x :=
  rfl

/-- A morphism in a category-of-elements prestack expresses restriction of the
classified presheaf elements. -/
lemma elementsFiberElement_map
    (a : (elementsPrestack F).p.Fiber R)
    (b : (elementsPrestack F).p.Fiber S) (f : R ⟶ S)
    (q : a.1 ⟶ b.1) (hq : IsHomLift (elementsPrestack F).p f q) :
    F.map f.op (elementsFiberElement b) = elementsFiberElement a := by
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  subst R
  subst S
  letI : IsHomLift (elementsPrestack F).p f q := hq
  have hbase := IsHomLift.eq_of_isHomLift (elementsPrestack F).p f q
  change F.map f.op b.unop.2 = a.unop.2
  have hvalue := CategoryOfElements.map_snd q.unop
  change F.map q.unop.val b.unop.2 = a.unop.2 at hvalue
  have hop : q.unop.val = f.op := by
    apply Quiver.Hom.unop_inj
    simpa [elementsPrestack] using hbase.symm
  rwa [hop] at hvalue

end BasedCategory

namespace Presieve

variable {C : Type u₁} [Category.{v₁} C]
  {J : GrothendieckTopology C} {F : Cᵒᵖ ⥤ Type v₁}
  {X : BasedCategory.{v₂, u₂} C}

/-- A presheaf is a sheaf if its category-of-elements prestack is equivalent over the
base to a stack. -/
theorem isSheaf_of_isRepresentedByStack
    (E : BasedFunctor (BasedCategory.ofPresheaf F) X)
    [E.toFunctor.IsEquivalence] [BasedCategory.IsStack J X] :
    IsSheaf J F := by
  intro S R hR x hx
  have hxSieve : x.SieveCompatible := hx.to_sieveCompatible
  have hxCongr : ∀ {T : C} {f g : T ⟶ S} (_ : f = g) (hf : R.arrows f)
      (hg : R.arrows g), x f hf = x g hg := by
    intro T f g hfg hf hg
    subst hfg
    rfl
  let D : R.arrows.category ⥤ (BasedCategory.ofPresheaf F).obj :=
    { obj := fun f ↦ CostructuredArrow.mk
        (yonedaEquiv.symm (x f.obj.hom f.property))
      map := fun {f g} q ↦ CostructuredArrow.homMk q.hom.left (by
        simp only [CostructuredArrow.mk_hom_eq_self]
        exact (yonedaEquiv_symm_naturality_left q.hom.left F
          (x g.obj.hom g.property)).trans
            (congrArg yonedaEquiv.symm
              ((hxSieve g.obj.hom q.hom.left g.property).symm.trans
                (hxCongr (Over.w q.hom) _ _))))
      map_id := fun f ↦ by ext; simp
      map_comp := fun q r ↦ by ext; simp }
  have hDobj : ∀ q : R.arrows.category,
      (BasedCategory.ofPresheaf F).p.obj (D.obj q) = q.obj.left :=
    fun _ ↦ rfl
  have hDmap : ∀ {q r : R.arrows.category} (k : q ⟶ r),
      IsHomLift (BasedCategory.ofPresheaf F).p k.hom.left (D.map k) := by
    intro q r k
    apply IsHomLift.of_commSq (ha := rfl) (hb := rfl)
    constructor
    simp [D]
  obtain ⟨b, hb, ε, hεlift, hεnat⟩ :=
    BasedFunctor.exists_gluing_obj_of_isStack E hR D hDobj hDmap
  let d : (BasedCategory.ofPresheaf F).obj :=
    BasedCategory.ofPresheaf.ptObj E b hb.symm
  let α : E.obj d ≅ b := BasedCategory.ofPresheaf.ptObjIso E b hb.symm
  have hαhom : IsHomLift X.p (𝟙 S) α.hom := by
    apply IsHomLift.of_fac' X.p (𝟙 S) α.hom (E.w_obj d) hb
    rw [BasedCategory.ofPresheaf.ptObjIso_base]
    simp
  have hαinv : IsHomLift X.p (𝟙 S) α.inv := by
    letI : IsHomLift X.p (𝟙 S) α.hom := hαhom
    exact IsHomLift.lift_id_inv X.p S α
  let δ : ∀ q : R.arrows.category, D.obj q ⟶ d := fun q ↦
    E.toFunctor.preimage (ε q ≫ α.inv)
  have hEδ : ∀ q : R.arrows.category,
      E.map (δ q) = ε q ≫ α.inv := fun q ↦
    E.toFunctor.map_preimage _
  have hδlift : ∀ q : R.arrows.category,
      IsHomLift (BasedCategory.ofPresheaf F).p q.obj.hom (δ q) := by
    intro q
    have hcomp : IsHomLift X.p q.obj.hom (ε q ≫ α.inv) := by
      exact IsHomLift.comp_lift_id_right' X.p q.obj.hom (ε q) S α.inv
    have hmap : IsHomLift X.p q.obj.hom (E.map (δ q)) := by
      rw [hEδ q]
      exact hcomp
    exact E.reflects_isHomLift q.obj.hom (δ q) hmap
  let t : F.obj (op S) := d.yonedaElement rfl
  have ht : x.IsAmalgamation t := by
    intro T f hf
    let q := R.arrows.categoryMk f hf
    have hmap := CostructuredArrow.map_op_yonedaElement (δ q) (hδlift q) rfl rfl
    change F.map f.op t = x f hf
    simpa [q, t, D] using hmap
  refine ⟨t, ht, ?_⟩
  intro t' ht'
  let d' : (BasedCategory.ofPresheaf F).obj :=
    CostructuredArrow.mk (yonedaEquiv.symm t')
  have hlocal : ∀ q : R.arrows.category,
      F.map q.obj.hom.op t' = (D.obj q).yonedaElement rfl := by
    intro q
    simpa [D] using ht' q.obj.hom q.property
  let η : ∀ q : R.arrows.category, D.obj q ⟶ d' := fun q ↦
    CostructuredArrow.homMkOfElementEq q.obj.hom rfl rfl (by
      simpa [d'] using hlocal q)
  have hηlift : ∀ q : R.arrows.category,
      IsHomLift (BasedCategory.ofPresheaf F).p q.obj.hom (η q) := by
    intro q
    exact CostructuredArrow.homMkOfElementEq_isHomLift
      q.obj.hom rfl rfl (by simpa [d'] using hlocal q)
  have hηnat : ∀ {q r : R.arrows.category} (k : q ⟶ r),
      D.map k ≫ η r = η q := by
    intro q r k
    apply CostructuredArrow.proj_yoneda_hom_ext q.obj.hom
    · have hcomp : IsHomLift (BasedCategory.ofPresheaf F).p
          (k.hom.left ≫ r.obj.hom) (D.map k ≫ η r) :=
        IsHomLift.comp (p := (BasedCategory.ofPresheaf F).p)
          k.hom.left r.obj.hom (D.map k) (η r)
      rw [Over.w k.hom] at hcomp
      exact hcomp
    · exact hηlift q
  have hEDmap : ∀ {q r : R.arrows.category} (k : q ⟶ r),
      IsHomLift X.p k.hom.left ((D ⋙ E.toFunctor).map k) := by
    intro q r k
    change IsHomLift X.p k.hom.left (E.map (D.map k))
    exact E.preserves_isHomLift _ _
  have hEηlift : ∀ q : R.arrows.category,
      IsHomLift X.p q.obj.hom (E.map (η q)) := by
    intro q
    exact E.preserves_isHomLift _ _
  have hEηnat : ∀ {q r : R.arrows.category} (k : q ⟶ r),
      (D ⋙ E.toFunctor).map k ≫ E.map (η r) = E.map (η q) := by
    intro q r k
    simpa only [Functor.comp_map, ← E.map_comp] using congrArg E.map (hηnat k)
  obtain ⟨Φ, hΦ, -⟩ := Functor.IsStack.existsUnique_gluing_hom_of_cocone
    hR (D ⋙ E.toFunctor) (E.w_obj d') hb
      (fun q ↦ E.map (η q)) hEηlift hEDmap hEηnat
      ε hεlift hεnat
  let mY : E.obj d' ⟶ E.obj d := Φ ≫ α.inv
  obtain ⟨m, hm⟩ := E.toFunctor.map_surjective mY
  have hmYlift : IsHomLift X.p (𝟙 S) mY := by
    letI : IsHomLift X.p (𝟙 S) Φ := hΦ.1
    exact IsHomLift.comp_lift_id_right' X.p (𝟙 S) Φ S α.inv
  have hmlift : IsHomLift (BasedCategory.ofPresheaf F).p (𝟙 S) m := by
    have hmap : IsHomLift X.p (𝟙 S) (E.map m) := by
      rw [hm]
      exact hmYlift
    exact E.reflects_isHomLift (𝟙 S) m hmap
  have hfinal := CostructuredArrow.map_op_yonedaElement m hmlift rfl rfl
  simpa [t, d'] using hfinal.symm

/-- Universe-polymorphic variant of `isSheaf_of_isRepresentedByStack`, using the
opposite category of elements instead of a costructured-arrow prestack. -/
theorem isSheaf_of_isRepresentedByStack_elements
    {F : Cᵒᵖ ⥤ Type w} {Y : BasedCategory.{v₂, u₂} C}
    (E : BasedFunctor (BasedCategory.elementsPrestack F) Y)
    [E.toFunctor.IsEquivalence] [BasedCategory.IsStack J Y] :
    IsSheaf J F := by
  intro S R hR x hx
  have hxSieve : x.SieveCompatible := hx.to_sieveCompatible
  have hxCongr : ∀ {T : C} {f g : T ⟶ S} (_ : f = g) (hf : R.arrows f)
      (hg : R.arrows g), x f hf = x g hg := by
    intro T f g hfg hf hg
    subst hfg
    rfl
  let D : R.arrows.category ⥤ (BasedCategory.elementsPrestack F).obj :=
    { obj := fun f ↦ op ⟨op f.obj.left, x f.obj.hom f.property⟩
      map := fun {f g} q ↦
        (CategoryOfElements.homMk _ _ q.hom.left.op (by
          exact (hxSieve g.obj.hom q.hom.left g.property).symm.trans
            (hxCongr (Over.w q.hom) _ _))).op
      map_id := fun f ↦ by
        apply Quiver.Hom.unop_inj
        apply CategoryOfElements.ext
        rfl
      map_comp := fun q r ↦ by
        apply Quiver.Hom.unop_inj
        apply CategoryOfElements.ext
        rfl }
  have hDobj : ∀ q : R.arrows.category,
      (BasedCategory.elementsPrestack F).p.obj (D.obj q) = q.obj.left :=
    fun _ ↦ rfl
  have hDmap : ∀ {q r : R.arrows.category} (k : q ⟶ r),
      IsHomLift (BasedCategory.elementsPrestack F).p k.hom.left (D.map k) := by
    intro q r k
    apply IsHomLift.of_commSq (ha := rfl) (hb := rfl)
    constructor
    simp [D, BasedCategory.elementsPrestack]
  obtain ⟨b, hb, ε, hεlift, hεnat⟩ :=
    BasedFunctor.exists_gluing_obj_of_isStack E hR D hDobj hDmap
  let bFiber : Y.p.Fiber S := ⟨b, hb⟩
  let _ : (E.onFiber S).Full := E.onFiber_full S
  let _ : (E.onFiber S).Faithful := E.onFiber_faithful S
  let _ : (E.onFiber S).EssSurj :=
    BasedCategory.onFiber_essSurj_of_essSurj E S
  let _ : (E.onFiber S).IsEquivalence :=
    { full := inferInstance, faithful := inferInstance, essSurj := inferInstance }
  let a : (BasedCategory.elementsPrestack F).p.Fiber S :=
    (E.onFiber S).objPreimage bFiber
  let e : (E.onFiber S).obj a ≅ bFiber :=
    (E.onFiber S).objObjPreimageIso bFiber
  let δ : ∀ q : R.arrows.category, D.obj q ⟶ a.1 := fun q ↦
    E.toFunctor.preimage (ε q ≫ e.inv.1)
  have hEδ : ∀ q : R.arrows.category,
      E.map (δ q) = ε q ≫ e.inv.1 := fun q ↦
    E.toFunctor.map_preimage _
  have hδlift : ∀ q : R.arrows.category,
      IsHomLift (BasedCategory.elementsPrestack F).p q.obj.hom (δ q) := by
    intro q
    have hcomp : IsHomLift Y.p q.obj.hom (ε q ≫ e.inv.1) := by
      letI : IsHomLift Y.p (𝟙 S) e.inv.1 := e.inv.2
      exact IsHomLift.comp_lift_id_right' Y.p q.obj.hom (ε q) S e.inv.1
    have hmap : IsHomLift Y.p q.obj.hom (E.map (δ q)) := by
      rw [hEδ q]
      exact hcomp
    exact E.reflects_isHomLift q.obj.hom (δ q) hmap
  let t : F.obj (op S) := BasedCategory.elementsFiberElement a
  have ht : x.IsAmalgamation t := by
    intro T f hf
    let q := R.arrows.categoryMk f hf
    let aq : (BasedCategory.elementsPrestack F).p.Fiber T :=
      ⟨D.obj q, rfl⟩
    have hmap := BasedCategory.elementsFiberElement_map
      aq a f (δ q) (hδlift q)
    change F.map f.op t = x f hf
    simpa [q, aq, t, D, BasedCategory.elementsFiberElement] using hmap
  refine ⟨t, ht, ?_⟩
  intro t' ht'
  let a' : (BasedCategory.elementsPrestack F).p.Fiber S :=
    BasedCategory.elementsFiberObj t'
  let η : ∀ q : R.arrows.category, D.obj q ⟶ a'.1 := fun q ↦
    (CategoryOfElements.homMk _ _ q.obj.hom.op (by
      simpa [a', D] using ht' q.obj.hom q.property)).op
  have hηlift : ∀ q : R.arrows.category,
      IsHomLift (BasedCategory.elementsPrestack F).p q.obj.hom (η q) := by
    intro q
    apply IsHomLift.of_commSq (ha := rfl) (hb := rfl)
    constructor
    simp [η, a', BasedCategory.elementsFiberObj,
      BasedCategory.elementsPrestack]
  have hηnat : ∀ {q r : R.arrows.category} (k : q ⟶ r),
      D.map k ≫ η r = η q := by
    intro q r k
    letI hcomp : IsHomLift (BasedCategory.elementsPrestack F).p q.obj.hom
        (D.map k ≫ η r) := by
      have h := IsHomLift.comp (p := (BasedCategory.elementsPrestack F).p)
        k.hom.left r.obj.hom (D.map k) (η r)
      rw [Over.w k.hom] at h
      exact h
    letI hright : IsHomLift (BasedCategory.elementsPrestack F).p q.obj.hom (η q) :=
      hηlift q
    exact BasedCategory.hom_ext_of_faithful_of_isHomLift
      (BasedCategory.elementsPrestack F).p q.obj.hom _ _
  have hEDmap : ∀ {q r : R.arrows.category} (k : q ⟶ r),
      IsHomLift Y.p k.hom.left ((D ⋙ E.toFunctor).map k) := by
    intro q r k
    change IsHomLift Y.p k.hom.left (E.map (D.map k))
    exact E.preserves_isHomLift _ _
  have hEηlift : ∀ q : R.arrows.category,
      IsHomLift Y.p q.obj.hom (E.map (η q)) := by
    intro q
    exact E.preserves_isHomLift _ _
  have hEηnat : ∀ {q r : R.arrows.category} (k : q ⟶ r),
      (D ⋙ E.toFunctor).map k ≫ E.map (η r) = E.map (η q) := by
    intro q r k
    simpa only [Functor.comp_map, ← E.map_comp] using congrArg E.map (hηnat k)
  obtain ⟨Φ, hΦ, -⟩ := Functor.IsStack.existsUnique_gluing_hom_of_cocone
    hR (D ⋙ E.toFunctor) (E.w_obj a'.1) hb
      (fun q ↦ E.map (η q)) hEηlift hEDmap hEηnat
      ε hεlift hεnat
  let mY : E.obj a'.1 ⟶ E.obj a.1 := Φ ≫ e.inv.1
  obtain ⟨m, hm⟩ := E.toFunctor.map_surjective mY
  have hmYlift : IsHomLift Y.p (𝟙 S) mY := by
    letI : IsHomLift Y.p (𝟙 S) Φ := hΦ.1
    letI : IsHomLift Y.p (𝟙 S) e.inv.1 := e.inv.2
    exact IsHomLift.comp_lift_id_right' Y.p (𝟙 S) Φ S e.inv.1
  have hmlift : IsHomLift (BasedCategory.elementsPrestack F).p (𝟙 S) m := by
    have hmap : IsHomLift Y.p (𝟙 S) (E.map m) := by
      rw [hm]
      exact hmYlift
    exact E.reflects_isHomLift (𝟙 S) m hmap
  have hfinal := BasedCategory.elementsFiberElement_map a' a (𝟙 S) m hmlift
  simpa [t, a'] using hfinal.symm

end Presieve

end CategoryTheory
