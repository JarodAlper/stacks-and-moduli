module

public import StacksAndModuli.API.CoreCoGrothendieckPrestack
public import StacksAndModuli.«Section3.5-Stacks».«part3.5.1-the-definition»

/-!
# Stacks from category-valued pseudofunctors

The Grothendieck construction of a groupoid-valued stack is a stack in the
fibered-category sense. In particular, this applies to the pointwise core of a
category-valued stack. The proof normalizes arbitrary descent diagrams against the
canonical cleavage of the Grothendieck construction, then invokes the usual
pseudofunctorial descent equivalence.
-/

@[expose] public section

open CategoryTheory Opposite Bicategory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Pseudofunctor.CoGrothendieck

variable {C : Type u₁} [Category.{v₁} C]
variable (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₂, u₂})
variable (J : GrothendieckTopology C) [F.IsStack J]

section Descent

variable {G : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₂, u₂}}
variable [(forget G).IsFiberedInGroupoids]
variable {S : C} {R : Sieve S}
variable (D : R.arrows.category ⥤ CoGrothendieck G)
variable (hDobj : ∀ q : R.arrows.category, (forget G).obj (D.obj q) = q.obj.left)
variable (hDmap : ∀ {q r : R.arrows.category} (k : q ⟶ r),
  Functor.IsHomLift (forget G) k.hom.left (D.map k))

attribute [local simp] PrelaxFunctor.map₂_eqToHom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma mapComp_hom_comp_cartesianLift
    {X Y Y' : C} (M : G.obj ⟨op X⟩) (f : Y ⟶ X) (g : Y' ⟶ Y)
    (gf : Y' ⟶ X) (hgf : g ≫ f = gf) :
    (CoGrothendieck.ι G Y').map
          ((G.mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc
            (by subst gf; rfl)).hom.toNatTrans.app M) ≫
        cartesianLift ((G.map f.op.toLoc).toFunctor.obj M) g ≫
          cartesianLift M f =
      cartesianLift M gf := by
  subst gf
  refine CoGrothendieck.Hom.ext _ _ (by simp) ?_
  dsimp [Pseudofunctor.mapComp']
  simp [G.mapComp_id_right_inv_app, Bicategory.Strict.rightUnitor_eqToIso,
    ← NatTrans.naturality_assoc, ← Cat.Hom₂.comp_app]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private lemma cartesianLift_comp_cartesianLift
    {X Y Y' : C} (M : G.obj ⟨op X⟩) (f : Y ⟶ X) (g : Y' ⟶ Y)
    (gf : Y' ⟶ X) (hgf : g ≫ f = gf) :
    cartesianLift ((G.map f.op.toLoc).toFunctor.obj M) g ≫
        cartesianLift M f =
      (CoGrothendieck.ι G Y').map
          ((G.mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc
            (by subst gf; rfl)).inv.toNatTrans.app M) ≫
        cartesianLift M gf := by
  subst gf
  refine CoGrothendieck.Hom.ext _ _ (by simp) ?_
  dsimp [Pseudofunctor.mapComp']
  simp [G.mapComp_id_right_inv_app, Bicategory.Strict.rightUnitor_eqToIso,
    ← NatTrans.naturality_assoc, ← Cat.Hom₂.comp_app]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma map_map_comp_cartesianLift
    {Y Y' : C} {M N : G.obj ⟨op Y⟩} (φ : M ⟶ N) (g : Y' ⟶ Y) :
    (CoGrothendieck.ι G Y').map
          ((G.map g.op.toLoc).toFunctor.map φ) ≫ cartesianLift N g =
      cartesianLift M g ≫ (CoGrothendieck.ι G Y).map φ := by
  refine CoGrothendieck.Hom.ext _ _ (by simp) ?_
  simp [G.mapComp_id_left_inv_app, G.mapComp_id_right_inv_app,
    Bicategory.Strict.leftUnitor_eqToIso, Bicategory.Strict.rightUnitor_eqToIso,
    ← Functor.map_comp_assoc, ← Cat.Hom₂.comp_app]

private noncomputable abbrev normalizedFiber (q : R.arrows.category) :
    G.obj ⟨op q.obj.left⟩ :=
  HasFibers.Fib.mk (p := forget G) (hDobj q)

private noncomputable def normalizedIso (q : R.arrows.category) :
    (CoGrothendieck.ι G q.obj.left).obj (normalizedFiber D hDobj q) ≅ D.obj q :=
  HasFibers.Fib.mkIsoSelf (p := forget G) (hDobj q)

private noncomputable abbrev normalizedFiberAt
    {Y : C} (q : Y ⟶ S) (hq : R q) : G.obj ⟨op Y⟩ :=
  normalizedFiber D hDobj (R.arrows.categoryMk q hq)

private noncomputable def normalizedIsoAt
    {Y : C} (q : Y ⟶ S) (hq : R q) :
    (CoGrothendieck.ι G Y).obj (normalizedFiberAt D hDobj q hq) ≅
      D.obj (R.arrows.categoryMk q hq) :=
  normalizedIso D hDobj (R.arrows.categoryMk q hq)

private noncomputable def coconeComparisonIso (A : G.obj ⟨op S⟩)
    (η : ∀ i : R.arrows.category, D.obj i ⟶ ⟨S, A⟩)
    (hηlift : ∀ i, Functor.IsHomLift (forget G) i.obj.hom (η i))
    (i : R.arrows.category) :
    normalizedFiber D hDobj i ≅
      (G.map i.obj.hom.op.toLoc).toFunctor.obj A := by
  let α : (CoGrothendieck.ι G i.obj.left).obj
      (normalizedFiber D hDobj i) ⟶ ⟨S, A⟩ :=
    (normalizedIso D hDobj i).hom ≫ η i
  let β : (CoGrothendieck.ι G i.obj.left).obj
      ((G.map i.obj.hom.op.toLoc).toFunctor.obj A) ⟶ ⟨S, A⟩ :=
    cartesianLift A i.obj.hom
  letI hi : Functor.IsHomLift (forget G) (𝟙 i.obj.left)
      (normalizedIso D hDobj i).hom :=
    HasFibers.Fib.mkIsoSelfIsHomLift (p := forget G) (hDobj i)
  letI hηi : Functor.IsHomLift (forget G) i.obj.hom (η i) := hηlift i
  let hα : Functor.IsCartesian (forget G) i.obj.hom α := by
    dsimp [α]
    exact @Functor.IsCartesian.of_iso_comp C (CoGrothendieck G) _ _
      (forget G) i.obj.left S _ _ i.obj.hom (η i) inferInstance _
      (normalizedIso D hDobj i) hi
  let hβ : Functor.IsCartesian (forget G) i.obj.hom β := by
    letI : Functor.IsStronglyCartesian (forget G) i.obj.hom β := by
      dsimp [β]
      exact CoGrothendieck.isStronglyCartesian_homCartesianLift A i.obj.hom
    exact inferInstance
  let e := @Functor.IsCartesian.domainUniqueUpToIso C (CoGrothendieck G) _ _
    (forget G) i.obj.left S _ _ i.obj.hom β hβ _ α hα
  exact HasFibers.Fib.isoMk e
    (@Functor.IsCartesian.domainUniqueUpToIso_inv_isHomLift C
      (CoGrothendieck G) _ _ (forget G) i.obj.left S _ _
      i.obj.hom β hβ _ α hα)

private lemma coconeComparisonIso_hom_fac (A : G.obj ⟨op S⟩)
    (η : ∀ i : R.arrows.category, D.obj i ⟶ ⟨S, A⟩)
    (hηlift : ∀ i, Functor.IsHomLift (forget G) i.obj.hom (η i))
    (i : R.arrows.category) :
    (CoGrothendieck.ι G i.obj.left).map
          (coconeComparisonIso D hDobj A η hηlift i).hom ≫
        cartesianLift A i.obj.hom =
      (normalizedIso D hDobj i).hom ≫ η i := by
  let α : (CoGrothendieck.ι G i.obj.left).obj
      (normalizedFiber D hDobj i) ⟶ ⟨S, A⟩ :=
    (normalizedIso D hDobj i).hom ≫ η i
  let β : (CoGrothendieck.ι G i.obj.left).obj
      ((G.map i.obj.hom.op.toLoc).toFunctor.obj A) ⟶ ⟨S, A⟩ :=
    cartesianLift A i.obj.hom
  letI hi : Functor.IsHomLift (forget G) (𝟙 i.obj.left)
      (normalizedIso D hDobj i).hom :=
    HasFibers.Fib.mkIsoSelfIsHomLift (p := forget G) (hDobj i)
  letI hηi : Functor.IsHomLift (forget G) i.obj.hom (η i) := hηlift i
  let hα : Functor.IsCartesian (forget G) i.obj.hom α := by
    dsimp [α]
    exact @Functor.IsCartesian.of_iso_comp C (CoGrothendieck G) _ _
      (forget G) i.obj.left S _ _ i.obj.hom (η i) inferInstance _
      (normalizedIso D hDobj i) hi
  let hβ : Functor.IsCartesian (forget G) i.obj.hom β := by
    letI : Functor.IsStronglyCartesian (forget G) i.obj.hom β := by
      dsimp [β]
      exact CoGrothendieck.isStronglyCartesian_homCartesianLift A i.obj.hom
    exact inferInstance
  let e := @Functor.IsCartesian.domainUniqueUpToIso C (CoGrothendieck G) _ _
    (forget G) i.obj.left S _ _ i.obj.hom β hβ _ α hα
  let he : Functor.IsHomLift (forget G) (𝟙 i.obj.left) e.hom :=
    @Functor.IsCartesian.domainUniqueUpToIso_inv_isHomLift C
      (CoGrothendieck G) _ _ (forget G) i.obj.left S _ _
      i.obj.hom β hβ _ α hα
  change (CoGrothendieck.ι G i.obj.left).map
    (@HasFibers.Fib.homMk C (CoGrothendieck G) _ _ (forget G) _
      i.obj.left _ _ e.hom he) ≫ β = α
  have hm : (CoGrothendieck.ι G i.obj.left).map
      (@HasFibers.Fib.homMk C (CoGrothendieck G) _ _ (forget G) _
        i.obj.left _ _ e.hom he) = e.hom := by
    change (HasFibers.ι i.obj.left).map
      (@HasFibers.Fib.homMk C (CoGrothendieck G) _ _ (forget G) _
        i.obj.left _ _ e.hom he) = e.hom
    exact @HasFibers.Fib.map_homMk C (CoGrothendieck G) _ _
      (forget G) _ i.obj.left _ _ e.hom he
  rw [hm]
  letI : Functor.IsCartesian (forget G) i.obj.hom β := hβ
  letI : Functor.IsHomLift (forget G) i.obj.hom α := hα.toIsHomLift
  exact Functor.IsCartesian.fac (forget G) i.obj.hom β α

private noncomputable def pullbackComparisonIso
    {Y : C} (q : Y ⟶ S) (hq : R q) (i : R.arrows.category)
    (f : Y ⟶ i.obj.left) (hf : f ≫ i.obj.hom = q) :
    normalizedFiberAt D hDobj q hq ≅
      (G.map f.op.toLoc).toFunctor.obj (normalizedFiber D hDobj i) := by
  let qi := R.arrows.categoryMk q hq
  let k : qi ⟶ i := ObjectProperty.homMk (Over.homMk f hf)
  let α : (CoGrothendieck.ι G Y).obj (normalizedFiberAt D hDobj q hq) ⟶ D.obj i :=
    (normalizedIsoAt D hDobj q hq).hom ≫ D.map k
  let β : (CoGrothendieck.ι G Y).obj
      ((G.map f.op.toLoc).toFunctor.obj (normalizedFiber D hDobj i)) ⟶ D.obj i :=
    cartesianLift (normalizedFiber D hDobj i) f ≫ (normalizedIso D hDobj i).hom
  letI : Functor.IsHomLift (forget G) f (D.map k) := by
    simpa [k, qi] using hDmap k
  letI hqi : Functor.IsHomLift (forget G) (𝟙 Y) (normalizedIsoAt D hDobj q hq).hom :=
    HasFibers.Fib.mkIsoSelfIsHomLift (p := forget G) (show (forget G).obj
      (D.obj qi) = Y by simpa [qi] using hDobj qi)
  letI hi : Functor.IsHomLift (forget G) (𝟙 i.obj.left)
      (normalizedIso D hDobj i).hom :=
    HasFibers.Fib.mkIsoSelfIsHomLift (p := forget G) (hDobj i)
  letI : Functor.IsStronglyCartesian (forget G) f (D.map k) :=
    Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift
      (forget G) f (D.map k)
  letI : Functor.IsCartesian (forget G) f (D.map k) := inferInstance
  let hα : Functor.IsCartesian (forget G) f α := by
    dsimp [α]
    exact @Functor.IsCartesian.of_iso_comp C (CoGrothendieck G) _ _
      (forget G) Y i.obj.left _ _ f (D.map k) inferInstance _
      (normalizedIsoAt D hDobj q hq) hqi
  let hβ : Functor.IsCartesian (forget G) f β := by
    dsimp [β]
    exact @Functor.IsCartesian.of_comp_iso C (CoGrothendieck G) _ _
      (forget G) Y i.obj.left _ _ f
      (cartesianLift (normalizedFiber D hDobj i) f) inferInstance _
      (normalizedIso D hDobj i) hi
  let e := @Functor.IsCartesian.domainUniqueUpToIso C (CoGrothendieck G) _ _
    (forget G) Y i.obj.left _ _ f β hβ _ α hα
  exact HasFibers.Fib.isoMk e
    (@Functor.IsCartesian.domainUniqueUpToIso_inv_isHomLift C (CoGrothendieck G) _ _
      (forget G) Y i.obj.left _ _ f β hβ _ α hα)

private lemma pullbackComparisonIso_hom_fac
    {Y : C} (q : Y ⟶ S) (hq : R q) (i : R.arrows.category)
    (f : Y ⟶ i.obj.left) (hf : f ≫ i.obj.hom = q) :
    (CoGrothendieck.ι G Y).map
          (pullbackComparisonIso D hDobj hDmap q hq i f hf).hom ≫
        (cartesianLift (normalizedFiber D hDobj i) f ≫
          (normalizedIso D hDobj i).hom) =
      (normalizedIsoAt D hDobj q hq).hom ≫
        D.map (ObjectProperty.homMk (Over.homMk f hf) :
          R.arrows.categoryMk q hq ⟶ i) := by
  let qi := R.arrows.categoryMk q hq
  let k : qi ⟶ i := ObjectProperty.homMk (Over.homMk f hf)
  let α : (CoGrothendieck.ι G Y).obj (normalizedFiberAt D hDobj q hq) ⟶ D.obj i :=
    (normalizedIsoAt D hDobj q hq).hom ≫ D.map k
  let β : (CoGrothendieck.ι G Y).obj
      ((G.map f.op.toLoc).toFunctor.obj (normalizedFiber D hDobj i)) ⟶ D.obj i :=
    cartesianLift (normalizedFiber D hDobj i) f ≫ (normalizedIso D hDobj i).hom
  letI : Functor.IsHomLift (forget G) f (D.map k) := by
    simpa [k, qi] using hDmap k
  letI hqi : Functor.IsHomLift (forget G) (𝟙 Y) (normalizedIsoAt D hDobj q hq).hom :=
    HasFibers.Fib.mkIsoSelfIsHomLift (p := forget G) (show (forget G).obj
      (D.obj qi) = Y by simpa [qi] using hDobj qi)
  letI hi : Functor.IsHomLift (forget G) (𝟙 i.obj.left)
      (normalizedIso D hDobj i).hom :=
    HasFibers.Fib.mkIsoSelfIsHomLift (p := forget G) (hDobj i)
  letI : Functor.IsStronglyCartesian (forget G) f (D.map k) :=
    Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift
      (forget G) f (D.map k)
  letI : Functor.IsCartesian (forget G) f (D.map k) := inferInstance
  let hα : Functor.IsCartesian (forget G) f α := by
    dsimp [α]
    exact @Functor.IsCartesian.of_iso_comp C (CoGrothendieck G) _ _
      (forget G) Y i.obj.left _ _ f (D.map k) inferInstance _
      (normalizedIsoAt D hDobj q hq) hqi
  let hβ : Functor.IsCartesian (forget G) f β := by
    dsimp [β]
    exact @Functor.IsCartesian.of_comp_iso C (CoGrothendieck G) _ _
      (forget G) Y i.obj.left _ _ f
      (cartesianLift (normalizedFiber D hDobj i) f) inferInstance _
      (normalizedIso D hDobj i) hi
  let e := @Functor.IsCartesian.domainUniqueUpToIso C (CoGrothendieck G) _ _
    (forget G) Y i.obj.left _ _ f β hβ _ α hα
  let he : Functor.IsHomLift (forget G) (𝟙 Y) e.hom :=
    @Functor.IsCartesian.domainUniqueUpToIso_inv_isHomLift C (CoGrothendieck G) _ _
      (forget G) Y i.obj.left _ _ f β hβ _ α hα
  change (CoGrothendieck.ι G Y).map
    (@HasFibers.Fib.homMk C (CoGrothendieck G) _ _ (forget G) _ Y _ _ e.hom he) ≫ β = α
  have hm : (CoGrothendieck.ι G Y).map
      (@HasFibers.Fib.homMk C (CoGrothendieck G) _ _ (forget G) _ Y _ _ e.hom he) = e.hom := by
    change (HasFibers.ι Y).map
      (@HasFibers.Fib.homMk C (CoGrothendieck G) _ _ (forget G) _ Y _ _ e.hom he) = e.hom
    exact @HasFibers.Fib.map_homMk C (CoGrothendieck G) _ _ (forget G) _ Y _ _ e.hom he
  rw [hm]
  letI : Functor.IsCartesian (forget G) f β := hβ
  letI : Functor.IsHomLift (forget G) f α := hα.toIsHomLift
  exact Functor.IsCartesian.fac (forget G) f β α

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma coconeComparisonIso_restrict (A : G.obj ⟨op S⟩)
    (η : ∀ i : R.arrows.category, D.obj i ⟶ ⟨S, A⟩)
    (hηlift : ∀ i, Functor.IsHomLift (forget G) i.obj.hom (η i))
    (hηnat : ∀ ⦃i j : R.arrows.category⦄ (h : i ⟶ j),
      D.map h ≫ η j = η i)
    {Y : C} (q : Y ⟶ S) (hq : R q) (i : R.arrows.category)
    (f : Y ⟶ i.obj.left) (hf : f ≫ i.obj.hom = q) :
    (coconeComparisonIso D hDobj A η hηlift
        (R.arrows.categoryMk q hq)).hom ≫
      (G.mapComp' i.obj.hom.op.toLoc f.op.toLoc q.op.toLoc
        (by subst q; rfl)).hom.toNatTrans.app A =
    (pullbackComparisonIso D hDobj hDmap q hq i f hf).hom ≫
      (G.map f.op.toLoc).toFunctor.map
        (coconeComparisonIso D hDobj A η hηlift i).hom := by
  let qi := R.arrows.categoryMk q hq
  let k : qi ⟶ i := ObjectProperty.homMk (Over.homMk f hf)
  let c₀ := coconeComparisonIso D hDobj A η hηlift qi
  let cᵢ := coconeComparisonIso D hDobj A η hηlift i
  let d := pullbackComparisonIso D hDobj hDmap q hq i f hf
  let μ := (G.mapComp' i.obj.hom.op.toLoc f.op.toLoc q.op.toLoc
    (by subst q; rfl)).hom.toNatTrans.app A
  let τ := cartesianLift
      ((G.map i.obj.hom.op.toLoc).toFunctor.obj A) f ≫
    cartesianLift A i.obj.hom
  have hτ : Functor.IsCartesian (forget G) (f ≫ i.obj.hom) τ := by
    letI : Functor.IsStronglyCartesian (forget G) f
        (cartesianLift ((G.map i.obj.hom.op.toLoc).toFunctor.obj A) f) :=
      inferInstance
    letI : Functor.IsStronglyCartesian (forget G) i.obj.hom
        (cartesianLift A i.obj.hom) := inferInstance
    letI : Functor.IsStronglyCartesian (forget G) (f ≫ i.obj.hom) τ :=
      inferInstance
    infer_instance
  letI : Functor.IsCartesian (forget G) (f ≫ i.obj.hom) τ := hτ
  apply HasFibers.Fib.hom_ext
  change (CoGrothendieck.ι G Y).map _ = (CoGrothendieck.ι G Y).map _
  have hleft : Functor.IsHomLift (forget G) (𝟙 Y)
      ((CoGrothendieck.ι G Y).map (c₀.hom ≫ μ)) := by
    change Functor.IsHomLift (forget G) (𝟙 Y)
      ((HasFibers.ι Y).map (c₀.hom ≫ μ))
    infer_instance
  have hright : Functor.IsHomLift (forget G) (𝟙 Y)
      ((CoGrothendieck.ι G Y).map
        (d.hom ≫ (G.map f.op.toLoc).toFunctor.map cᵢ.hom)) := by
    change Functor.IsHomLift (forget G) (𝟙 Y)
      ((HasFibers.ι Y).map
        (d.hom ≫ (G.map f.op.toLoc).toFunctor.map cᵢ.hom))
    infer_instance
  refine @Functor.IsCartesian.ext C (CoGrothendieck G) _ _ (forget G)
    Y S _ _ (f ≫ i.obj.hom) τ hτ _
    ((CoGrothendieck.ι G Y).map (c₀.hom ≫ μ))
    ((CoGrothendieck.ι G Y).map
      (d.hom ≫ (G.map f.op.toLoc).toFunctor.map cᵢ.hom)) hleft hright ?_
  change (CoGrothendieck.ι G Y).map (c₀.hom ≫ μ) ≫ τ =
    (CoGrothendieck.ι G Y).map
      (d.hom ≫ (G.map f.op.toLoc).toFunctor.map cᵢ.hom) ≫ τ
  calc
    (CoGrothendieck.ι G Y).map (c₀.hom ≫ μ) ≫ τ =
        (CoGrothendieck.ι G Y).map c₀.hom ≫
          cartesianLift A q := by
      simpa [τ, μ, Category.assoc] using congrArg
        (fun z ↦ (CoGrothendieck.ι G Y).map c₀.hom ≫ z)
        (mapComp_hom_comp_cartesianLift A i.obj.hom f q hf)
    _ = (normalizedIso D hDobj qi).hom ≫ η qi := by
      simpa [c₀, qi] using coconeComparisonIso_hom_fac
        D hDobj A η hηlift qi
    _ = (normalizedIso D hDobj qi).hom ≫ D.map k ≫ η i := by
      simpa [Category.assoc] using
        (congrArg (fun z ↦ (normalizedIso D hDobj qi).hom ≫ z)
          (hηnat k)).symm
    _ = (CoGrothendieck.ι G Y).map d.hom ≫
          cartesianLift (normalizedFiber D hDobj i) f ≫
            (normalizedIso D hDobj i).hom ≫ η i := by
      simpa [d, qi, k, normalizedIsoAt, Category.assoc] using
        congrArg (fun z ↦ z ≫ η i)
        (pullbackComparisonIso_hom_fac D hDobj hDmap q hq i f hf).symm
    _ = (CoGrothendieck.ι G Y).map d.hom ≫
          cartesianLift (normalizedFiber D hDobj i) f ≫
            (CoGrothendieck.ι G i.obj.left).map cᵢ.hom ≫
              cartesianLift A i.obj.hom := by
      simpa [cᵢ, Category.assoc] using congrArg
        (fun z ↦ (CoGrothendieck.ι G Y).map d.hom ≫
          cartesianLift (normalizedFiber D hDobj i) f ≫ z)
        (coconeComparisonIso_hom_fac D hDobj A η hηlift i).symm
    _ = (CoGrothendieck.ι G Y).map d.hom ≫
          (CoGrothendieck.ι G Y).map
            ((G.map f.op.toLoc).toFunctor.map cᵢ.hom) ≫
          cartesianLift ((G.map i.obj.hom.op.toLoc).toFunctor.obj A) f ≫
            cartesianLift A i.obj.hom := by
      simpa [Category.assoc] using congrArg
        (fun z ↦ (CoGrothendieck.ι G Y).map d.hom ≫ z ≫
          cartesianLift A i.obj.hom)
        (map_map_comp_cartesianLift cᵢ.hom f).symm
    _ = (CoGrothendieck.ι G Y).map
          (d.hom ≫ (G.map f.op.toLoc).toFunctor.map cᵢ.hom) ≫ τ := by
      simp [τ, Category.assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma pullbackComparisonIso_restrict
    {Y' Y : C} (g : Y' ⟶ Y) (q : Y ⟶ S) (q' : Y' ⟶ S)
    (hq : R q) (hq' : R q') (hqg : g ≫ q = q')
    (i : R.arrows.category) (f : Y ⟶ i.obj.left)
    (gf : Y' ⟶ i.obj.left) (hf : f ≫ i.obj.hom = q)
    (hgf : g ≫ f = gf) :
    (pullbackComparisonIso D hDobj hDmap q' hq' i gf
        (by rw [← hgf, Category.assoc, hf, hqg])).hom ≫
      (G.mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc
        (by subst gf; rfl)).hom.toNatTrans.app (normalizedFiber D hDobj i) =
    (pullbackComparisonIso D hDobj hDmap q' hq'
        (R.arrows.categoryMk q hq) g hqg).hom ≫
      (G.map g.op.toLoc).toFunctor.map
        (pullbackComparisonIso D hDobj hDmap q hq i f hf).hom := by
  let kf : R.arrows.categoryMk q hq ⟶ i :=
    ObjectProperty.homMk (Over.homMk f hf)
  let kg : R.arrows.categoryMk q' hq' ⟶ R.arrows.categoryMk q hq :=
    ObjectProperty.homMk (Over.homMk g hqg)
  let kgf : R.arrows.categoryMk q' hq' ⟶ i := ObjectProperty.homMk
    (Over.homMk gf (by rw [← hgf, Category.assoc, hf, hqg]; rfl))
  have hkgf : kg ≫ kf = kgf := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact hgf
  let cf := pullbackComparisonIso D hDobj hDmap q hq i f hf
  let cg := pullbackComparisonIso D hDobj hDmap q' hq'
    (R.arrows.categoryMk q hq) g hqg
  let cgf := pullbackComparisonIso D hDobj hDmap q' hq' i gf
    (by rw [← hgf, Category.assoc, hf, hqg])
  let μ := (G.mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc
    (by subst gf; rfl)).hom.toNatTrans.app (normalizedFiber D hDobj i)
  let τ := (cartesianLift
      ((G.map f.op.toLoc).toFunctor.obj (normalizedFiber D hDobj i)) g ≫
    cartesianLift (normalizedFiber D hDobj i) f) ≫
      (normalizedIso D hDobj i).hom
  letI hi : Functor.IsHomLift (forget G) (𝟙 i.obj.left)
      (normalizedIso D hDobj i).hom :=
    HasFibers.Fib.mkIsoSelfIsHomLift (p := forget G) (hDobj i)
  let first := cartesianLift
    ((G.map f.op.toLoc).toFunctor.obj (normalizedFiber D hDobj i)) g
  let second := cartesianLift (normalizedFiber D hDobj i) f
  have hbase : Functor.IsCartesian (forget G) (g ≫ f) (first ≫ second) := by
    letI : Functor.IsStronglyCartesian (forget G) g first := inferInstance
    letI : Functor.IsStronglyCartesian (forget G) f second := inferInstance
    letI : Functor.IsStronglyCartesian (forget G) (g ≫ f) (first ≫ second) :=
      inferInstance
    infer_instance
  have hτ : Functor.IsCartesian (forget G) (g ≫ f) τ := by
    dsimp [τ, first, second]
    exact @Functor.IsCartesian.of_comp_iso C (CoGrothendieck G) _ _
      (forget G) Y' i.obj.left _ _ (g ≫ f)
      (first ≫ second) hbase _ (normalizedIso D hDobj i) hi
  letI : Functor.IsCartesian (forget G) (g ≫ f) τ := hτ
  apply HasFibers.Fib.hom_ext
  change (CoGrothendieck.ι G Y').map _ = (CoGrothendieck.ι G Y').map _
  have hleft : Functor.IsHomLift (forget G) (𝟙 Y')
      ((CoGrothendieck.ι G Y').map (cgf.hom ≫ μ)) := by
    change Functor.IsHomLift (forget G) (𝟙 Y')
      ((HasFibers.ι Y').map (cgf.hom ≫ μ))
    infer_instance
  have hright : Functor.IsHomLift (forget G) (𝟙 Y')
      ((CoGrothendieck.ι G Y').map
        (cg.hom ≫ (G.map g.op.toLoc).toFunctor.map cf.hom)) := by
    change Functor.IsHomLift (forget G) (𝟙 Y')
      ((HasFibers.ι Y').map
        (cg.hom ≫ (G.map g.op.toLoc).toFunctor.map cf.hom))
    infer_instance
  refine @Functor.IsCartesian.ext C (CoGrothendieck G) _ _ (forget G)
    Y' i.obj.left _ _ (g ≫ f) τ hτ _
    ((CoGrothendieck.ι G Y').map (cgf.hom ≫ μ))
    ((CoGrothendieck.ι G Y').map
      (cg.hom ≫ (G.map g.op.toLoc).toFunctor.map cf.hom)) hleft hright ?_
  change (CoGrothendieck.ι G Y').map (cgf.hom ≫ μ) ≫ τ =
    (CoGrothendieck.ι G Y').map
      (cg.hom ≫ (G.map g.op.toLoc).toFunctor.map cf.hom) ≫ τ
  calc
    (CoGrothendieck.ι G Y').map (cgf.hom ≫ μ) ≫ τ =
        (CoGrothendieck.ι G Y').map cgf.hom ≫
          ((CoGrothendieck.ι G Y').map μ ≫
            cartesianLift ((G.map f.op.toLoc).toFunctor.obj
              (normalizedFiber D hDobj i)) g ≫
            cartesianLift (normalizedFiber D hDobj i) f) ≫
          (normalizedIso D hDobj i).hom := by simp [τ, Category.assoc]
    _ = (CoGrothendieck.ι G Y').map cgf.hom ≫
          cartesianLift (normalizedFiber D hDobj i) gf ≫
          (normalizedIso D hDobj i).hom := by
      simpa [μ, Category.assoc] using congrArg
        (fun z ↦ (CoGrothendieck.ι G Y').map cgf.hom ≫ z ≫
          (normalizedIso D hDobj i).hom)
        (mapComp_hom_comp_cartesianLift (normalizedFiber D hDobj i)
          f g gf hgf)
    _ = (normalizedIsoAt D hDobj q' hq').hom ≫ D.map kgf := by
      simpa [cgf, kgf, Category.assoc] using
        pullbackComparisonIso_hom_fac D hDobj hDmap q' hq' i gf
          (by rw [← hgf, Category.assoc, hf, hqg])
    _ = (normalizedIsoAt D hDobj q' hq').hom ≫ D.map kg ≫ D.map kf := by
      rw [← D.map_comp, hkgf]
    _ = (CoGrothendieck.ι G Y').map cg.hom ≫
          cartesianLift (normalizedFiber D hDobj
            (R.arrows.categoryMk q hq)) g ≫
          (normalizedIso D hDobj (R.arrows.categoryMk q hq)).hom ≫ D.map kf := by
      simpa [cg, kg, Category.assoc] using congrArg (fun z ↦ z ≫ D.map kf)
        (pullbackComparisonIso_hom_fac D hDobj hDmap q' hq'
          (R.arrows.categoryMk q hq) g hqg).symm
    _ = (CoGrothendieck.ι G Y').map cg.hom ≫
          cartesianLift (normalizedFiber D hDobj
            (R.arrows.categoryMk q hq)) g ≫
          (CoGrothendieck.ι G Y).map cf.hom ≫
          cartesianLift (normalizedFiber D hDobj i) f ≫
          (normalizedIso D hDobj i).hom := by
      simpa [cf, kf, normalizedIsoAt, Category.assoc] using congrArg
        (fun z ↦ (CoGrothendieck.ι G Y').map cg.hom ≫
          cartesianLift (normalizedFiberAt D hDobj q hq) g ≫ z)
        (pullbackComparisonIso_hom_fac D hDobj hDmap q hq i f hf).symm
    _ = (CoGrothendieck.ι G Y').map cg.hom ≫
          (CoGrothendieck.ι G Y').map
            ((G.map g.op.toLoc).toFunctor.map cf.hom) ≫
          cartesianLift ((G.map f.op.toLoc).toFunctor.obj
            (normalizedFiber D hDobj i)) g ≫
          cartesianLift (normalizedFiber D hDobj i) f ≫
          (normalizedIso D hDobj i).hom := by
      simpa [Category.assoc] using congrArg
        (fun z ↦ (CoGrothendieck.ι G Y').map cg.hom ≫ z ≫
          cartesianLift (normalizedFiber D hDobj i) f ≫
          (normalizedIso D hDobj i).hom)
        (map_map_comp_cartesianLift cf.hom g).symm
    _ = (CoGrothendieck.ι G Y').map
          (cg.hom ≫ (G.map g.op.toLoc).toFunctor.map cf.hom) ≫ τ := by
      simp [τ, Category.assoc]

private lemma overlapMem {Y : C} (q : Y ⟶ S) (i : R.arrows.category)
    (f : Y ⟶ i.obj.left) (hf : f ≫ i.obj.hom = q) : R q := by
  rw [← hf]
  exact R.downward_closed i.property f

private noncomputable def normalizedDescentData :
    G.DescentData (fun i : R.arrows.category ↦ i.obj.hom) where
  obj i := normalizedFiber D hDobj i
  hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ :=
    (pullbackComparisonIso D hDobj hDmap q
      (overlapMem q i₁ f₁ hf₁) i₁ f₁ hf₁).inv ≫
    (pullbackComparisonIso D hDobj hDmap q
      (overlapMem q i₁ f₁ hf₁) i₂ f₂ hf₂).hom
  pullHom_hom := by
    intros Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
    let hRq : R q := overlapMem q i₁ f₁ hf₁
    have hgf₁S : gf₁ ≫ i₁.obj.hom = q' := by
      rw [← hgf₁, Category.assoc, hf₁, hq]
    have hgf₂S : gf₂ ≫ i₂.obj.hom = q' := by
      rw [← hgf₂, Category.assoc, hf₂, hq]
    let hRq' : R q' := overlapMem q' i₁ gf₁ hgf₁S
    let c₀ := pullbackComparisonIso D hDobj hDmap q' hRq'
      (R.arrows.categoryMk q hRq) g hq
    let c₁ := pullbackComparisonIso D hDobj hDmap q hRq i₁ f₁ hf₁
    let c₂ := pullbackComparisonIso D hDobj hDmap q hRq i₂ f₂ hf₂
    let c₁' := pullbackComparisonIso D hDobj hDmap q' hRq' i₁ gf₁ hgf₁S
    let c₂' := pullbackComparisonIso D hDobj hDmap q' hRq' i₂ gf₂ hgf₂S
    let μ₁ := (Cat.Hom.toNatIso (G.mapComp' f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
      (by subst gf₁; rfl))).app (normalizedFiber D hDobj i₁)
    let μ₂ := (Cat.Hom.toNatIso (G.mapComp' f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
      (by subst gf₂; rfl))).app (normalizedFiber D hDobj i₂)
    have h₁ : c₁'.hom ≫ μ₁.hom = c₀.hom ≫
        (G.map g.op.toLoc).toFunctor.map c₁.hom := by
      simpa [c₀, c₁, c₁', μ₁, hRq, hRq'] using
        pullbackComparisonIso_restrict D hDobj hDmap g q q' hRq hRq' hq
          i₁ f₁ gf₁ hf₁ hgf₁
    have h₂ : c₂'.hom ≫ μ₂.hom = c₀.hom ≫
        (G.map g.op.toLoc).toFunctor.map c₂.hom := by
      simpa [c₀, c₂, c₂', μ₂, hRq, hRq'] using
        pullbackComparisonIso_restrict D hDobj hDmap g q q' hRq hRq' hq
          i₂ f₂ gf₂ hf₂ hgf₂
    have he₁ : c₁'.trans μ₁ = c₀.trans
        ((G.map g.op.toLoc).toFunctor.mapIso c₁) := Iso.ext h₁
    have hi₁ : μ₁.inv ≫ c₁'.inv =
        ((G.map g.op.toLoc).toFunctor.mapIso c₁).inv ≫ c₀.inv := by
      simpa using congrArg Iso.inv he₁
    change LocallyDiscreteOpToCat.pullHom (c₁.inv ≫ c₂.hom) g gf₁ gf₂ =
      c₁'.inv ≫ c₂'.hom
    rw [← cancel_epi μ₁.inv, ← cancel_mono μ₂.hom]
    calc
      (μ₁.inv ≫ LocallyDiscreteOpToCat.pullHom
          (c₁.inv ≫ c₂.hom) g gf₁ gf₂) ≫ μ₂.hom =
          (G.map g.op.toLoc).toFunctor.map (c₁.inv ≫ c₂.hom) := by
        simpa [μ₁, μ₂, Category.assoc] using
          (LocallyDiscreteOpToCat.map_eq_pullHom
            (c₁.inv ≫ c₂.hom) g gf₁ gf₂ hgf₁ hgf₂).symm
      _ = (μ₁.inv ≫ (c₁'.inv ≫ c₂'.hom)) ≫ μ₂.hom := by
        simp only [Functor.map_comp, Category.assoc]
        slice_rhs 1 2 => rw [hi₁]
        slice_rhs 3 4 => rw [h₂]
        simp
  hom_self Y q i g hg := by
    simp
  hom_comp Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
    simp

private noncomputable def coconeDescentIso (A : G.obj ⟨op S⟩)
    (η : ∀ i : R.arrows.category, D.obj i ⟶ ⟨S, A⟩)
    (hηlift : ∀ i, Functor.IsHomLift (forget G) i.obj.hom (η i))
    (hηnat : ∀ ⦃i j : R.arrows.category⦄ (h : i ⟶ j),
      D.map h ≫ η j = η i) :
    (G.toDescentData (fun i : R.arrows.category ↦ i.obj.hom)).obj A ≅
      normalizedDescentData D hDobj hDmap :=
  Pseudofunctor.DescentData.isoMk
    (fun i ↦ (coconeComparisonIso D hDobj A η hηlift i).symm)
    (fun Y q i₁ i₂ f₁ f₂ hf₁ hf₂ ↦ by
      let hRq : R q := overlapMem q i₁ f₁ hf₁
      let qi := R.arrows.categoryMk q hRq
      let c₀ := coconeComparisonIso D hDobj A η hηlift qi
      let c₁ := coconeComparisonIso D hDobj A η hηlift i₁
      let c₂ := coconeComparisonIso D hDobj A η hηlift i₂
      let d₁ := pullbackComparisonIso D hDobj hDmap q hRq i₁ f₁ hf₁
      let d₂ := pullbackComparisonIso D hDobj hDmap q hRq i₂ f₂ hf₂
      let μ₁ := (Cat.Hom.toNatIso (G.mapComp' i₁.obj.hom.op.toLoc
        f₁.op.toLoc q.op.toLoc (by
          change (f₁ ≫ i₁.obj.hom).op.toLoc = q.op.toLoc
          simpa using congrArg (fun z ↦ z.op.toLoc) hf₁))).app A
      let μ₂ := (Cat.Hom.toNatIso (G.mapComp' i₂.obj.hom.op.toLoc
        f₂.op.toLoc q.op.toLoc (by
          change (f₂ ≫ i₂.obj.hom).op.toLoc = q.op.toLoc
          simpa using congrArg (fun z ↦ z.op.toLoc) hf₂))).app A
      have h₁ : c₀.hom ≫ μ₁.hom = d₁.hom ≫
          (G.map f₁.op.toLoc).toFunctor.map c₁.hom := by
        simpa [c₀, c₁, d₁, μ₁, qi, hRq] using
          coconeComparisonIso_restrict D hDobj hDmap A η hηlift hηnat
            q hRq i₁ f₁ hf₁
      have h₂ : c₀.hom ≫ μ₂.hom = d₂.hom ≫
          (G.map f₂.op.toLoc).toFunctor.map c₂.hom := by
        simpa [c₀, c₂, d₂, μ₂, qi, hRq] using
          coconeComparisonIso_restrict D hDobj hDmap A η hηlift hηnat
            q hRq i₂ f₂ hf₂
      have he₁ : c₀.trans μ₁ = d₁.trans
          ((G.map f₁.op.toLoc).toFunctor.mapIso c₁) := Iso.ext h₁
      have hi₁ : (G.map f₁.op.toLoc).toFunctor.map c₁.inv ≫ d₁.inv =
          μ₁.inv ≫ c₀.inv := by
        simpa using (congrArg Iso.inv he₁).symm
      have hi₂ : c₀.inv ≫ d₂.hom = μ₂.hom ≫
          (G.map f₂.op.toLoc).toFunctor.map c₂.inv := by
        simpa [Category.assoc] using
          (congrArg (fun z ↦ c₀.inv ≫ z ≫
            (G.map f₂.op.toLoc).toFunctor.map c₂.inv) h₂).symm
      change (G.map f₁.op.toLoc).toFunctor.map c₁.inv ≫
          (d₁.inv ≫ d₂.hom) =
        (μ₁.inv ≫ μ₂.hom) ≫
          (G.map f₂.op.toLoc).toFunctor.map c₂.inv
      rw [← Category.assoc, hi₁, Category.assoc, hi₂]
      simp [Category.assoc])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem existsUnique_gluing_hom_of_cocone_of_isStack
    {J : GrothendieckTopology C} [G.IsStack J] (hR : R ∈ J S)
    (hDobj : ∀ q : R.arrows.category, (forget G).obj (D.obj q) = q.obj.left)
    (hDmap : ∀ ⦃q r : R.arrows.category⦄ (k : q ⟶ r),
      Functor.IsHomLift (forget G) k.hom.left (D.map k))
    (A B : G.obj ⟨op S⟩)
    (η : ∀ i : R.arrows.category, D.obj i ⟶ ⟨S, A⟩)
    (hηlift : ∀ i, Functor.IsHomLift (forget G) i.obj.hom (η i))
    (hηnat : ∀ ⦃i j : R.arrows.category⦄ (h : i ⟶ j),
      D.map h ≫ η j = η i)
    (θ : ∀ i : R.arrows.category, D.obj i ⟶ ⟨S, B⟩)
    (hθlift : ∀ i, Functor.IsHomLift (forget G) i.obj.hom (θ i))
    (hθnat : ∀ ⦃i j : R.arrows.category⦄ (h : i ⟶ j),
      D.map h ≫ θ j = θ i) :
    ∃! Φ : (⟨S, A⟩ : CoGrothendieck G) ⟶ ⟨S, B⟩,
      Functor.IsHomLift (forget G) (𝟙 S) Φ ∧
        ∀ i : R.arrows.category, θ i = η i ≫ Φ := by
  let p : R.arrows.category → C := fun i ↦ i.obj.left
  let f : ∀ i, p i ⟶ S := fun i ↦ i.obj.hom
  let E := G.toDescentData f
  have hf : Sieve.ofArrows p f = R := by
    rw [Sieve.ofArrows_category']
    simp [p, f]
  let hE : E.FullyFaithful := G.fullyFaithfulToDescentData f (by rwa [hf])
  let eA := coconeDescentIso D hDobj
    (fun {q r} k ↦ hDmap (q := q) (r := r) k) A η hηlift hηnat
  let eB := coconeDescentIso D hDobj
    (fun {q r} k ↦ hDmap (q := q) (r := r) k) B θ hθlift hθnat
  let ψ : E.obj A ⟶ E.obj B := eA.hom ≫ eB.inv
  let u : A ⟶ B := hE.preimage ψ
  let Φ : (⟨S, A⟩ : CoGrothendieck G) ⟶ ⟨S, B⟩ :=
    (CoGrothendieck.ι G S).map u
  have hΦlift : Functor.IsHomLift (forget G) (𝟙 S) Φ := by
    dsimp only [Φ]
    exact IsHomLift.map (forget G) ((CoGrothendieck.ι G S).map u)
  have hu (i : R.arrows.category) :
      (G.map i.obj.hom.op.toLoc).toFunctor.map u =
          (coconeComparisonIso D hDobj A η hηlift i).inv ≫
          (coconeComparisonIso D hDobj B θ hθlift i).hom := by
    have hmap : E.map u = ψ := hE.map_preimage ψ
    have h := congrArg
      (fun z : E.obj A ⟶ E.obj B ↦ Pseudofunctor.DescentData.Hom.hom z i) hmap
    change (G.map i.obj.hom.op.toLoc).toFunctor.map u =
      (coconeComparisonIso D hDobj A η hηlift i).inv ≫
        (coconeComparisonIso D hDobj B θ hθlift i).hom at h
    exact h
  have hΦ (i : R.arrows.category) : θ i = η i ≫ Φ := by
    rw [← cancel_epi (normalizedIso D hDobj i).hom]
    calc
      (normalizedIso D hDobj i).hom ≫ θ i =
          (CoGrothendieck.ι G i.obj.left).map
              (coconeComparisonIso D hDobj B θ hθlift i).hom ≫
            cartesianLift B i.obj.hom := by
        simpa using (coconeComparisonIso_hom_fac
          D hDobj B θ hθlift i).symm
      _ = (CoGrothendieck.ι G i.obj.left).map
              ((coconeComparisonIso D hDobj A η hηlift i).hom ≫
                (G.map i.obj.hom.op.toLoc).toFunctor.map u) ≫
            cartesianLift B i.obj.hom := by
        rw [hu i]
        simp
      _ = (CoGrothendieck.ι G i.obj.left).map
              (coconeComparisonIso D hDobj A η hηlift i).hom ≫
            cartesianLift A i.obj.hom ≫
              (CoGrothendieck.ι G S).map u := by
        rw [Functor.map_comp, Category.assoc,
          map_map_comp_cartesianLift u i.obj.hom]
      _ = (normalizedIso D hDobj i).hom ≫ η i ≫ Φ := by
        simpa [Φ, Category.assoc] using congrArg
          (fun z ↦ z ≫ (CoGrothendieck.ι G S).map u)
          (coconeComparisonIso_hom_fac D hDobj A η hηlift i)
  refine ⟨Φ, ⟨hΦlift, hΦ⟩, ?_⟩
  intro Ψ hΨ
  letI hΨlift : Functor.IsHomLift (forget G) (𝟙 S) Ψ := hΨ.1
  have hΨbase : Ψ.base = 𝟙 S := by
    simpa using (IsHomLift.fac (forget G) (𝟙 S) Ψ).symm
  let v : A ⟶ B := Ψ.fiber ≫ eqToHom (by simp [hΨbase]) ≫
    (G.mapId ⟨op S⟩).hom.toNatTrans.app B
  have hvmap : (CoGrothendieck.ι G S).map v = Ψ := by
    apply CoGrothendieck.Hom.ext _ _ (by simp [hΨbase])
    simp [v, hΨbase, ← Cat.Hom₂.comp_app]
  have hv (i : R.arrows.category) :
      (G.map i.obj.hom.op.toLoc).toFunctor.map v =
        (coconeComparisonIso D hDobj A η hηlift i).inv ≫
          (coconeComparisonIso D hDobj B θ hθlift i).hom := by
    rw [← cancel_epi (coconeComparisonIso D hDobj A η hηlift i).hom]
    simp only [Iso.hom_inv_id_assoc]
    apply HasFibers.Fib.hom_ext
    change (CoGrothendieck.ι G i.obj.left).map _ =
      (CoGrothendieck.ι G i.obj.left).map _
    let β := cartesianLift B i.obj.hom
    have hl : Functor.IsHomLift (forget G) (𝟙 i.obj.left)
        ((CoGrothendieck.ι G i.obj.left).map
          ((coconeComparisonIso D hDobj A η hηlift i).hom ≫
            (G.map i.obj.hom.op.toLoc).toFunctor.map v)) := by
      simpa using IsHomLift.map (forget G)
        ((CoGrothendieck.ι G i.obj.left).map
          ((coconeComparisonIso D hDobj A η hηlift i).hom ≫
            (G.map i.obj.hom.op.toLoc).toFunctor.map v))
    have hr : Functor.IsHomLift (forget G) (𝟙 i.obj.left)
        ((CoGrothendieck.ι G i.obj.left).map
          (coconeComparisonIso D hDobj B θ hθlift i).hom) := by
      simpa using IsHomLift.map (forget G)
        ((CoGrothendieck.ι G i.obj.left).map
          (coconeComparisonIso D hDobj B θ hθlift i).hom)
    refine @Functor.IsCartesian.ext C (CoGrothendieck G) _ _ (forget G)
      i.obj.left S _ _ i.obj.hom β inferInstance _ _ _ hl hr ?_
    calc
      (CoGrothendieck.ι G i.obj.left).map
            ((coconeComparisonIso D hDobj A η hηlift i).hom ≫
              (G.map i.obj.hom.op.toLoc).toFunctor.map v) ≫ β =
          (CoGrothendieck.ι G i.obj.left).map
              (coconeComparisonIso D hDobj A η hηlift i).hom ≫
            cartesianLift A i.obj.hom ≫
              (CoGrothendieck.ι G S).map v := by
        dsimp only [β]
        rw [Functor.map_comp, Category.assoc,
          map_map_comp_cartesianLift v i.obj.hom]
      _ = (normalizedIso D hDobj i).hom ≫ η i ≫ Ψ := by
        simpa [Category.assoc, hvmap] using congrArg
          (fun z ↦ z ≫ (CoGrothendieck.ι G S).map v)
          (coconeComparisonIso_hom_fac D hDobj A η hηlift i)
      _ = (normalizedIso D hDobj i).hom ≫ θ i := by
        simpa [Category.assoc] using congrArg
          (fun z ↦ (normalizedIso D hDobj i).hom ≫ z) (hΨ.2 i).symm
      _ = (CoGrothendieck.ι G i.obj.left).map
            (coconeComparisonIso D hDobj B θ hθlift i).hom ≫ β := by
        simpa [β] using (coconeComparisonIso_hom_fac
          D hDobj B θ hθlift i).symm
  have hvE : E.map v = ψ := by
    apply Pseudofunctor.DescentData.hom_ext
    intro i
    change (G.map i.obj.hom.op.toLoc).toFunctor.map v =
      (coconeComparisonIso D hDobj A η hηlift i).inv ≫
        (coconeComparisonIso D hDobj B θ hθlift i).hom
    exact hv i
  have hvu : v = u := by
    apply hE.map_injective
    rw [hE.map_preimage]
    exact hvE
  dsimp [Φ]
  rw [← hvmap, hvu]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem morphismsGlue_of_isStack {J : GrothendieckTopology C} [G.IsStack J] :
    (forget G).MorphismsGlue J := by
  intro S R hR a b ha hb φ hφlift hφnat
  rcases a with ⟨Sa, A⟩
  rcases b with ⟨Sb, B⟩
  change Sa = S at ha
  change Sb = S at hb
  subst Sa
  subst Sb
  obtain ⟨D, η, hηlift, hDmap, hηnat⟩ :=
    Functor.IsStack.exists_lift_cocone (p := forget G)
      (a := (⟨S, A⟩ : CoGrothendieck G)) R
  let θ : ∀ i : R.arrows.category, D.obj i ⟶ ⟨S, B⟩ :=
    fun i ↦ φ i.property (η i) (hηlift i)
  have hDobj : ∀ i : R.arrows.category,
      (forget G).obj (D.obj i) = i.obj.left := fun i ↦
    IsHomLift.domain_eq (forget G) i.obj.hom (η i)
  have hθlift : ∀ i, Functor.IsHomLift (forget G) i.obj.hom (θ i) := by
    intro i
    exact hφlift i.property (η i) (hηlift i)
  have hθnat : ∀ ⦃i j : R.arrows.category⦄ (h : i ⟶ j),
      D.map h ≫ θ j = θ i := by
    intro i j h
    simpa [θ, hηnat h] using
      (hφnat j.property (D.map h) (η j) (hηlift j) (hDmap h)).symm
  obtain ⟨Φ, hΦ, huniq⟩ :=
    existsUnique_gluing_hom_of_cocone_of_isStack
      (G := G) (D := D) hR hDobj
        (fun {q r} k ↦ hDmap (q := q) (r := r) k) A B
        η hηlift (fun {i j} h ↦ hηnat (q := i) (r := j) h)
        θ hθlift hθnat
  refine ⟨Φ, ⟨hΦ.1, ?_⟩, ?_⟩
  · intro T q hq x ξ hξ
    let qi := R.arrows.categoryMk q hq
    letI : Functor.IsHomLift (forget G) q (η qi) := by
      simpa [qi] using hηlift qi
    letI : Functor.IsStronglyCartesian (forget G) q (η qi) :=
      Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift
        (forget G) q (η qi)
    let κ : x ⟶ D.obj qi :=
      Functor.IsStronglyCartesian.map
        (forget G) q (η qi) (Category.id_comp q).symm ξ
    have hκlift : Functor.IsHomLift (forget G) (𝟙 T) κ := by
      simpa [κ] using Functor.IsStronglyCartesian.map_isHomLift
        (forget G) q (η qi) (Category.id_comp q).symm ξ
    have hκfac : κ ≫ η qi = ξ := by
      exact Functor.IsStronglyCartesian.fac
        (forget G) q (η qi) (Category.id_comp q).symm ξ
    calc
      φ hq ξ hξ = κ ≫ θ qi := by
        simpa [θ, qi, hκfac] using
          hφnat (hg := hq) κ (η qi) (hηlift qi) hκlift
      _ = κ ≫ η qi ≫ Φ := by rw [hΦ.2 qi]
      _ = ξ ≫ Φ := by rw [← Category.assoc, hκfac]
  · intro Ψ hΨ
    apply huniq Ψ
    refine ⟨hΨ.1, ?_⟩
    intro i
    exact hΨ.2 i.property (η i) (hηlift i)

private noncomputable def gluingHom (M : G.obj ⟨op S⟩)
    (e : (G.toDescentData (fun i : R.arrows.category ↦ i.obj.hom)).obj M ≅
      normalizedDescentData D hDobj hDmap) (i : R.arrows.category) :
    D.obj i ⟶ ⟨S, M⟩ :=
  ((normalizedIso D hDobj i).inv ≫
    (CoGrothendieck.ι G i.obj.left).map (e.inv.hom i)) ≫
      cartesianLift M i.obj.hom

private lemma gluingHom_isHomLift (M : G.obj ⟨op S⟩)
    (e : (G.toDescentData (fun i : R.arrows.category ↦ i.obj.hom)).obj M ≅
      normalizedDescentData D hDobj hDmap) (i : R.arrows.category) :
    Functor.IsHomLift (forget G) i.obj.hom (gluingHom D hDobj hDmap M e i) := by
  letI : Functor.IsHomLift (forget G) (𝟙 i.obj.left)
      (normalizedIso D hDobj i).hom :=
    HasFibers.Fib.mkIsoSelfIsHomLift (p := forget G) (hDobj i)
  letI : Functor.IsHomLift (forget G) (𝟙 i.obj.left)
      (normalizedIso D hDobj i).inv := inferInstance
  have he : Functor.IsHomLift (forget G) (𝟙 i.obj.left)
      ((CoGrothendieck.ι G i.obj.left).map (e.inv.hom i)) := by
    change Functor.IsHomLift (forget G) (𝟙 i.obj.left)
      ((HasFibers.ι i.obj.left).map (e.inv.hom i))
    exact HasFibers.homLift (p := forget G) (e.inv.hom i)
  have hl : Functor.IsHomLift (forget G) i.obj.hom
      (cartesianLift M i.obj.hom) :=
    CoGrothendieck.isHomLift_cartesianLift M i.obj.hom
  have hne : Functor.IsHomLift (forget G)
      ((𝟙 i.obj.left) ≫ 𝟙 i.obj.left)
      ((normalizedIso D hDobj i).inv ≫
        (CoGrothendieck.ι G i.obj.left).map (e.inv.hom i)) := by
    exact @IsHomLift.comp C (CoGrothendieck G) _ _ (forget G)
      _ _ _ _ _ _ (𝟙 i.obj.left) (𝟙 i.obj.left)
      (normalizedIso D hDobj i).inv
      ((CoGrothendieck.ι G i.obj.left).map (e.inv.hom i)) inferInstance he
  have hall : Functor.IsHomLift (forget G)
      (((𝟙 i.obj.left) ≫ 𝟙 i.obj.left) ≫ i.obj.hom)
      (((normalizedIso D hDobj i).inv ≫
        (CoGrothendieck.ι G i.obj.left).map (e.inv.hom i)) ≫
          cartesianLift M i.obj.hom) := by
    exact @IsHomLift.comp C (CoGrothendieck G) _ _ (forget G)
      _ _ _ _ _ _ ((𝟙 i.obj.left) ≫ 𝟙 i.obj.left) i.obj.hom
      ((normalizedIso D hDobj i).inv ≫
        (CoGrothendieck.ι G i.obj.left).map (e.inv.hom i))
      (cartesianLift M i.obj.hom) hne hl
  simpa only [gluingHom, Category.id_comp] using hall

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma gluingHom_naturality (M : G.obj ⟨op S⟩)
    (e : (G.toDescentData (fun i : R.arrows.category ↦ i.obj.hom)).obj M ≅
      normalizedDescentData D hDobj hDmap) {i j : R.arrows.category} (h : i ⟶ j) :
    D.map h ≫ gluingHom D hDobj hDmap M e j =
      gluingHom D hDobj hDmap M e i := by
  let q := i.obj.hom
  let hq : R q := i.property
  let qi := R.arrows.categoryMk q hq
  let ki : qi ⟶ i := ObjectProperty.homMk
    (Over.homMk (𝟙 i.obj.left) (by
      change 𝟙 i.obj.left ≫ i.obj.hom = q
      simp [q]))
  let kj : qi ⟶ j := ObjectProperty.homMk
    (Over.homMk h.hom.left (by
      change h.hom.left ≫ j.obj.hom = q
      simpa [q] using h.hom.w))
  have hk : ki ≫ h = kj := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact Category.id_comp _
  let ci := pullbackComparisonIso D hDobj hDmap q hq i
    (𝟙 i.obj.left) (by simp [q])
  let cj := pullbackComparisonIso D hDobj hDmap q hq j h.hom.left
    (by simpa [q] using h.hom.w)
  have hci := pullbackComparisonIso_hom_fac D hDobj hDmap q hq i
    (𝟙 i.obj.left) (by simp [q])
  have hcj := pullbackComparisonIso_hom_fac D hDobj hDmap q hq j h.hom.left
    (by simpa [q] using h.hom.w)
  have hDh :
      ((CoGrothendieck.ι G i.obj.left).map ci.hom ≫
        cartesianLift (normalizedFiber D hDobj i) (𝟙 i.obj.left) ≫
          (normalizedIso D hDobj i).hom) ≫ D.map h =
        (CoGrothendieck.ι G i.obj.left).map cj.hom ≫
          cartesianLift (normalizedFiber D hDobj j) h.hom.left ≫
            (normalizedIso D hDobj j).hom := by
    calc
      ((CoGrothendieck.ι G i.obj.left).map ci.hom ≫
          cartesianLift (normalizedFiber D hDobj i) (𝟙 i.obj.left) ≫
            (normalizedIso D hDobj i).hom) ≫ D.map h =
        (normalizedIsoAt D hDobj q hq).hom ≫ D.map ki ≫ D.map h := by
          simpa [ci, ki, Category.assoc] using congrArg (fun z ↦ z ≫ D.map h) hci
      _ = (normalizedIsoAt D hDobj q hq).hom ≫ D.map kj := by
        rw [← D.map_comp, hk]
      _ = (CoGrothendieck.ι G i.obj.left).map cj.hom ≫
          cartesianLift (normalizedFiber D hDobj j) h.hom.left ≫
            (normalizedIso D hDobj j).hom := by
        simpa [cj, kj, Category.assoc] using hcj.symm
  let P := ((CoGrothendieck.ι G i.obj.left).map ci.hom ≫
    cartesianLift (normalizedFiber D hDobj i) (𝟙 i.obj.left)) ≫
      (normalizedIso D hDobj i).hom
  letI : IsIso (cartesianLift (normalizedFiber D hDobj i) (𝟙 i.obj.left)) :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso (forget G)
      (𝟙 i.obj.left) (cartesianLift (normalizedFiber D hDobj i) (𝟙 i.obj.left))
  haveI : IsIso P := by dsimp [P]; infer_instance
  rw [← cancel_epi P]
  have hPD : P ≫ D.map h =
      (CoGrothendieck.ι G i.obj.left).map cj.hom ≫
        cartesianLift (normalizedFiber D hDobj j) h.hom.left ≫
          (normalizedIso D hDobj j).hom := by
    simpa [P] using hDh
  rw [← Category.assoc, hPD]
  dsimp only [P]
  simp only [gluingHom, Category.assoc, Iso.hom_inv_id_assoc]
  let μi := (Cat.Hom.toNatIso (G.mapComp' i.obj.hom.op.toLoc
    (𝟙 i.obj.left).op.toLoc q.op.toLoc (by simp [q]))).app M
  let μj := (Cat.Hom.toNatIso (G.mapComp' j.obj.hom.op.toLoc
    h.hom.left.op.toLoc q.op.toLoc (by
      change (h.hom.left ≫ j.obj.hom).op.toLoc = q.op.toLoc
      simpa [q] using congrArg (fun z ↦ z.op.toLoc) h.hom.w))).app M
  have hecomm := e.inv.comm q (𝟙 i.obj.left) h.hom.left
    (by simp [q]) (by simpa [q] using h.hom.w)
  have hecomm' :
      (G.map (𝟙 i.obj.left).op.toLoc).toFunctor.map (e.inv.hom i) ≫
          μi.inv ≫ μj.hom =
        (ci.inv ≫ cj.hom) ≫
          (G.map h.hom.left.op.toLoc).toFunctor.map (e.inv.hom j) := by
    simpa [Pseudofunctor.toDescentData, Pseudofunctor.DescentData.ofObj,
      normalizedDescentData, ci, cj, μi, μj, q, hq] using hecomm
  have hfiber :
      ci.hom ≫
          (G.map (𝟙 i.obj.left).op.toLoc).toFunctor.map (e.inv.hom i) ≫ μi.inv =
        cj.hom ≫
          (G.map h.hom.left.op.toLoc).toFunctor.map (e.inv.hom j) ≫ μj.inv := by
    simpa [Category.assoc] using congrArg (fun z ↦ ci.hom ≫ z ≫ μj.inv) hecomm'
  have hpathj :
      cartesianLift (normalizedFiber D hDobj j) h.hom.left ≫
          (CoGrothendieck.ι G j.obj.left).map (e.inv.hom j) ≫
            cartesianLift M j.obj.hom =
        (CoGrothendieck.ι G i.obj.left).map
            ((G.map h.hom.left.op.toLoc).toFunctor.map (e.inv.hom j) ≫ μj.inv) ≫
          cartesianLift M q := by
    calc
      cartesianLift (normalizedFiber D hDobj j) h.hom.left ≫
          (CoGrothendieck.ι G j.obj.left).map (e.inv.hom j) ≫
            cartesianLift M j.obj.hom =
        (CoGrothendieck.ι G i.obj.left).map
            ((G.map h.hom.left.op.toLoc).toFunctor.map (e.inv.hom j)) ≫
          cartesianLift ((G.map j.obj.hom.op.toLoc).toFunctor.obj M) h.hom.left ≫
            cartesianLift M j.obj.hom := by
              simpa [normalizedDescentData, Category.assoc] using congrArg
                (fun z ↦ z ≫ cartesianLift M j.obj.hom)
                (map_map_comp_cartesianLift (G := G)
                  (e.inv.hom j) h.hom.left).symm
      _ = (CoGrothendieck.ι G i.obj.left).map
            ((G.map h.hom.left.op.toLoc).toFunctor.map (e.inv.hom j) ≫ μj.inv) ≫
          cartesianLift M q := by
        rw [cartesianLift_comp_cartesianLift M j.obj.hom h.hom.left q
          (by
            change h.hom.left ≫ j.obj.hom = q
            simpa [q] using h.hom.w)]
        simp [μj, Category.assoc]
  have hpathi :
      cartesianLift (normalizedFiber D hDobj i) (𝟙 i.obj.left) ≫
          (CoGrothendieck.ι G i.obj.left).map (e.inv.hom i) ≫
            cartesianLift M i.obj.hom =
        (CoGrothendieck.ι G i.obj.left).map
            ((G.map (𝟙 i.obj.left).op.toLoc).toFunctor.map (e.inv.hom i) ≫ μi.inv) ≫
          cartesianLift M q := by
    calc
      cartesianLift (normalizedFiber D hDobj i) (𝟙 i.obj.left) ≫
          (CoGrothendieck.ι G i.obj.left).map (e.inv.hom i) ≫
            cartesianLift M i.obj.hom =
        (CoGrothendieck.ι G i.obj.left).map
            ((G.map (𝟙 i.obj.left).op.toLoc).toFunctor.map (e.inv.hom i)) ≫
          cartesianLift ((G.map i.obj.hom.op.toLoc).toFunctor.obj M)
              (𝟙 i.obj.left) ≫
            cartesianLift M i.obj.hom := by
              simpa [normalizedDescentData, Category.assoc] using congrArg
                (fun z ↦ z ≫ cartesianLift M i.obj.hom)
                (map_map_comp_cartesianLift (G := G)
                  (e.inv.hom i) (𝟙 i.obj.left)).symm
      _ = (CoGrothendieck.ι G i.obj.left).map
            ((G.map (𝟙 i.obj.left).op.toLoc).toFunctor.map (e.inv.hom i) ≫
              μi.inv) ≫
          cartesianLift M q := by
        rw [cartesianLift_comp_cartesianLift M i.obj.hom (𝟙 i.obj.left) q
          (by simp [q])]
        simp [μi, Category.assoc]
  calc
    (CoGrothendieck.ι G i.obj.left).map cj.hom ≫
        cartesianLift (normalizedFiber D hDobj j) h.hom.left ≫
          (CoGrothendieck.ι G j.obj.left).map (e.inv.hom j) ≫
            cartesianLift M j.obj.hom =
      (CoGrothendieck.ι G i.obj.left).map
          (cj.hom ≫ (G.map h.hom.left.op.toLoc).toFunctor.map (e.inv.hom j) ≫ μj.inv) ≫
        cartesianLift M q := by
      simpa [Functor.map_comp, Category.assoc] using congrArg
        (fun z ↦ (CoGrothendieck.ι G i.obj.left).map cj.hom ≫ z) hpathj
    _ = (CoGrothendieck.ι G i.obj.left).map
          (ci.hom ≫ (G.map (𝟙 i.obj.left).op.toLoc).toFunctor.map (e.inv.hom i) ≫ μi.inv) ≫
        cartesianLift M q := by rw [hfiber]
    _ = (CoGrothendieck.ι G i.obj.left).map ci.hom ≫
        cartesianLift (normalizedFiber D hDobj i) (𝟙 i.obj.left) ≫
          (CoGrothendieck.ι G i.obj.left).map (e.inv.hom i) ≫
            cartesianLift M i.obj.hom := by
      simpa [Functor.map_comp, Category.assoc] using congrArg
        (fun z ↦ (CoGrothendieck.ι G i.obj.left).map ci.hom ≫ z) hpathi.symm

private theorem exists_gluing_obj_of_isStack
    {J : GrothendieckTopology C} [G.IsStack J] (hR : R ∈ J S)
    (hDobj : ∀ q : R.arrows.category, (forget G).obj (D.obj q) = q.obj.left)
    (hDmap : ∀ ⦃q r : R.arrows.category⦄ (k : q ⟶ r),
      Functor.IsHomLift (forget G) k.hom.left (D.map k)) :
    ∃ (a : CoGrothendieck G) (_ : (forget G).obj a = S)
      (ε : ∀ i : R.arrows.category, D.obj i ⟶ a),
      (∀ i, Functor.IsHomLift (forget G) i.obj.hom (ε i)) ∧
        ∀ ⦃i j : R.arrows.category⦄ (h : i ⟶ j), D.map h ≫ ε j = ε i := by
  let E := G.toDescentData (fun i : R.arrows.category ↦ i.obj.hom)
  let N := normalizedDescentData D hDobj (fun {_ _} k ↦ hDmap k)
  let hE : E.EssSurj := Pseudofunctor.IsStack.essSurj_of_sieve G R hR
  let M := E.objPreimage N
  let e : E.obj M ≅ N := E.objObjPreimageIso N
  exact ⟨⟨S, M⟩, rfl,
    gluingHom D hDobj (fun {_ _} k ↦ hDmap k) M e,
    gluingHom_isHomLift D hDobj (fun {_ _} k ↦ hDmap k) M e,
    (fun {i j} h ↦ gluingHom_naturality D hDobj
      (fun {_ _} k ↦ hDmap k) M e (i := i) (j := j) h)⟩

end Descent

/-- The Grothendieck construction of a groupoid-valued pseudofunctor which is a stack
is a stack as a category fibered in groupoids. -/
noncomputable instance forgetBasedCategoryIsStack
    {G : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₂, u₂}}
    {J : GrothendieckTopology C} [G.IsStack J]
    [(forget G).IsFiberedInGroupoids] :
    BasedCategory.IsStack J (BasedCategory.ofFunctor (forget G)) := by
  letI : (BasedCategory.ofFunctor (forget G)).p.IsFiberedInGroupoids := by
    change (forget G).IsFiberedInGroupoids
    infer_instance
  exact
    { isFiberedInGroupoids := inferInstance
      isStack :=
        { existsUnique_gluing_hom := morphismsGlue_of_isStack (G := G)
          exists_gluing_obj := fun {S R} hR D hDobj hDmap ↦
            exists_gluing_obj_of_isStack
              (G := G) (D := D) hR hDobj
                (fun {_ _} k ↦ hDmap k) } }

/-- If a category-valued pseudofunctor is a stack, then the Grothendieck construction
of its pointwise core is a stack as a category fibered in groupoids. -/
noncomputable instance coreForgetBasedCategoryIsStack :
    BasedCategory.IsStack J
      (BasedCategory.ofFunctor (forget F.core)) := by
  let _ : F.core.IsStack J := Pseudofunctor.core_isStack F
  exact forgetBasedCategoryIsStack (G := F.core) (J := J)

end CategoryTheory.Pseudofunctor.CoGrothendieck
