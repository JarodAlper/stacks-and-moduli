module

public import StacksAndModuli.API.OverPresheafTotal
public import StacksAndModuli.API.PresheafPrestack
public import Mathlib.CategoryTheory.ShrinkYoneda

/-!
# Prestacks of total presheaves on slice categories

For a presheaf on a slice category, its category of elements may either be formed over
the slice and then projected to the base, or formed after passing to the total presheaf.
This file gives the canonical equivalence between those two prestacks.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Opposite

universe w v u

namespace CategoryTheory.PresheafOver

variable {C : Type u} [Category.{v} C] {S : C}

/-- Applying an equality transport to an element does not change that element, as a
heterogeneous equality. -/
lemma eqToHom_apply_heq {A B : Type w} (h : A = B) (x : A) :
    (eqToHom h : A ⟶ B) x ≍ x := by
  subst h
  rfl

/-- Replacing an object of a slice category by the canonical `Over.mk` with the same
structure morphism does not change presheaf restriction, up to the required transport. -/
lemma map_homMk_heq (G : Functor (Over S)ᵒᵖ (Type w))
    {A Z : Over S} (g : Z ⟶ A) (x : G.obj (op A)) :
    G.map g.op x ≍
      G.map ((Over.homMk g.left : Over.mk (g.left ≫ A.hom) ⟶ A)).op x := by
  obtain ⟨Z, z, rfl⟩ := Z.mk_surjective
  let m : Over.mk (g.left ≫ A.hom) ⟶ A := Over.homMk g.left
  have e : Over.mk (g.left ≫ A.hom) = Over.mk z :=
    congrArg Over.mk (Over.w g)
  have hm : m = eqToHom e ≫ g := by
    ext
    simp [m]
  change G.map g.op x ≍ G.map m.op x
  rw [hm]
  simp only [op_comp, Functor.map_comp, types_comp_apply]
  rw [eqToHom_op, eqToHom_map]
  exact (eqToHom_apply_heq _ _).symm

/-- The category of elements of a presheaf on `Over S`, regarded as a prestack over the
original base category by composing its projection with `Over.forget S`. -/
abbrev elementsPrestack (G : Functor (Over S)ᵒᵖ (Type w)) :
    BasedCategory.{v, max u v w} C where
  obj := G.Elementsᵒᵖ
  p := (CategoryOfElements.π G).leftOp ⋙ Over.forget S

/-- The canonical functor from elements of the total presheaf to elements over the slice. -/
noncomputable def totalElementsComparison (G : Functor (Over S)ᵒᵖ (Type w)) :
    BasedFunctor (BasedCategory.elementsPrestack (total G)) (elementsPrestack G) where
  obj x := op ⟨op (Over.mk x.unop.2.1), x.unop.2.2⟩
  map {x y} q := by
    let hpair := CategoryOfElements.map_snd q.unop
    let hbase : q.unop.val.unop ≫ y.unop.2.1 = x.unop.2.1 :=
      congrArg Sigma.fst hpair
    let k : Over.mk x.unop.2.1 ⟶ Over.mk y.unop.2.1 :=
      Over.homMk q.unop.val.unop hbase
    refine (CategoryOfElements.homMk _ _ k.op ?_).op
    have hsecond := (Sigma.ext_iff.mp hpair).2
    change G.map k.op y.unop.2.2 = x.unop.2.2
    exact eq_of_heq ((map_homMk_heq G k y.unop.2.2).trans hsecond)
  map_id x := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    rfl
  map_comp q r := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    rfl
  w := rfl

/-- The comparison from the prestack of the total presheaf is faithful. -/
lemma totalElementsComparison_faithful (G : Functor (Over S)ᵒᵖ (Type w)) :
    (totalElementsComparison G).toFunctor.Faithful := by
  constructor
  intro x y q r h
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext
  apply Quiver.Hom.unop_inj
  have hleft := congrArg (fun z ↦ z.unop.val.unop.left) h
  simpa [totalElementsComparison] using hleft

/-- The comparison from the prestack of the total presheaf is full. -/
lemma totalElementsComparison_full (G : Functor (Over S)ᵒᵖ (Type w)) :
    (totalElementsComparison G).toFunctor.Full := by
  constructor
  intro x y q
  let k : Over.mk x.unop.2.1 ⟶ Over.mk y.unop.2.1 := q.unop.val.unop
  let f : x.unop.1.unop ⟶ y.unop.1.unop := k.left
  have hbase : f ≫ y.unop.2.1 = x.unop.2.1 := Over.w k
  have hpair : (total G).map f.op y.unop.2 = x.unop.2 := by
    apply Sigma.ext hbase
    have hq := CategoryOfElements.map_snd q.unop
    exact (map_homMk_heq G k y.unop.2.2).symm.trans (heq_of_eq hq)
  let r : x ⟶ y :=
    (CategoryOfElements.homMk y.unop x.unop f.op hpair).op
  refine ⟨r, ?_⟩
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext
  apply Quiver.Hom.unop_inj
  exact Over.OverMorphism.ext rfl

/-- The comparison from the prestack of the total presheaf is essentially surjective. -/
lemma totalElementsComparison_essSurj (G : Functor (Over S)ᵒᵖ (Type w)) :
    (totalElementsComparison G).toFunctor.EssSurj := by
  constructor
  intro z
  induction z with
  | op z =>
      rcases z with ⟨A, x⟩
      induction A with
      | op A =>
          obtain ⟨T, a, rfl⟩ := Over.mk_surjective A
          let z : (BasedCategory.elementsPrestack (total G)).obj :=
            op ⟨op T, ⟨a, x⟩⟩
          exact ⟨z, ⟨Iso.refl _⟩⟩

/-- The category of elements of a total presheaf is equivalent, over the base category,
to the category of elements on the slice followed by the slice projection. -/
theorem isEquivalence_totalElementsComparison (G : Functor (Over S)ᵒᵖ (Type w)) :
    (totalElementsComparison G).toFunctor.IsEquivalence := by
  let _ := totalElementsComparison_faithful G
  let _ := totalElementsComparison_full G
  let _ := totalElementsComparison_essSurj G
  exact { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }

/-- The canonical comparison from the usual prestack associated to the total presheaf to
the slice category-of-elements prestack. -/
noncomputable def totalPrestackComparison (G : Functor (Over S)ᵒᵖ (Type v)) :
    BasedFunctor (BasedCategory.ofPresheaf (total G)) (elementsPrestack G) where
  toFunctor :=
    (CategoryOfElements.costructuredArrowYonedaEquivalence (total G)).inverse ⋙
      (totalElementsComparison G).toFunctor
  w := rfl

/-- The usual prestack associated to a total presheaf is equivalent over the base to the
slice category of elements followed by the slice projection. -/
theorem isEquivalence_totalPrestackComparison
    (G : Functor (Over S)ᵒᵖ (Type v)) :
    (totalPrestackComparison G).toFunctor.IsEquivalence := by
  have h₁ :=
    (CategoryOfElements.costructuredArrowYonedaEquivalence (total G)).isEquivalence_inverse
  have h₂ := isEquivalence_totalElementsComparison G
  exact Functor.isEquivalence_trans _ _

end CategoryTheory.PresheafOver

namespace CategoryTheory.BasedCategory

variable {C : Type u} [Category.{v} C]

/-- Decoding the shrunken values of a presheaf induces a functor between the two
category-of-elements prestacks. -/
noncomputable def shrinkElementsComparison (F : Cᵒᵖ ⥤ Type w)
    [FunctorToTypes.Small.{v} F] :
    BasedFunctor (elementsPrestack (FunctorToTypes.shrink.{v} F))
      (elementsPrestack F) where
  obj x := op ⟨x.unop.1, (equivShrink _).symm x.unop.2⟩
  map {x y} f :=
    (CategoryOfElements.homMk (F := F) _ _ f.unop.val (by
      have h := CategoryOfElements.map_snd f.unop
      simpa [FunctorToTypes.shrink] using congrArg (equivShrink _).symm h)).op
  map_id x := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    rfl
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    rfl
  w := rfl

/-- Decoding shrunken presheaf values is faithful on categories of elements. -/
lemma shrinkElementsComparison_faithful (F : Cᵒᵖ ⥤ Type w)
    [FunctorToTypes.Small.{v} F] :
    (shrinkElementsComparison F).toFunctor.Faithful := by
  constructor
  intro x y f g h
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext
  have hval := congrArg (fun k ↦ k.unop.val) h
  simpa [shrinkElementsComparison] using hval

/-- Decoding shrunken presheaf values is full on categories of elements. -/
lemma shrinkElementsComparison_full (F : Cᵒᵖ ⥤ Type w)
    [FunctorToTypes.Small.{v} F] :
    (shrinkElementsComparison F).toFunctor.Full := by
  constructor
  intro x y f
  let g : x ⟶ y :=
    (CategoryOfElements.homMk
      (F := FunctorToTypes.shrink.{v} F) _ _ f.unop.val (by
      apply (equivShrink _).symm.injective
      simpa [FunctorToTypes.shrink, shrinkElementsComparison] using
        CategoryOfElements.map_snd f.unop)).op
  refine ⟨g, ?_⟩
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext
  rfl

/-- Decoding shrunken presheaf values is essentially surjective on categories of
elements. -/
lemma shrinkElementsComparison_essSurj (F : Cᵒᵖ ⥤ Type w)
    [FunctorToTypes.Small.{v} F] :
    (shrinkElementsComparison F).toFunctor.EssSurj := by
  constructor
  rintro ⟨x⟩
  let y : (elementsPrestack (FunctorToTypes.shrink.{v} F)).obj :=
    op ⟨x.1, equivShrink _ x.2⟩
  refine ⟨y, ⟨Iso.op (CategoryOfElements.isoMk x
    ((shrinkElementsComparison F).obj y).unop (Iso.refl x.1) ?_)⟩⟩
  simp [shrinkElementsComparison, y]

/-- Shrinking the values of a pointwise-small presheaf does not change its
category-of-elements prestack up to equivalence. -/
theorem isEquivalence_shrinkElementsComparison (F : Cᵒᵖ ⥤ Type w)
    [FunctorToTypes.Small.{v} F] :
    (shrinkElementsComparison F).toFunctor.IsEquivalence := by
  let _ := shrinkElementsComparison_faithful F
  let _ := shrinkElementsComparison_full F
  let _ := shrinkElementsComparison_essSurj F
  exact { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }

end CategoryTheory.BasedCategory

namespace CategoryTheory.PresheafOver

variable {C : Type u} [Category.{v} C] {S : C}

/-- Pointwise `v`-small values on the slice make the total presheaf `v`-small. -/
lemma small_total_of_small (G : (Over S)ᵒᵖ ⥤ Type w)
    [∀ A, Small.{v} (G.obj A)] : FunctorToTypes.Small.{v} (total G) := by
  intro T
  rw [total_obj]
  infer_instance

/-- A universe-safe comparison from the prestack of the shrunken total presheaf to
the original slice category-of-elements prestack. -/
noncomputable def smallTotalPrestackComparison (G : (Over S)ᵒᵖ ⥤ Type w)
    [FunctorToTypes.Small.{v} (total G)] :
    BasedFunctor
      (BasedCategory.ofPresheaf (FunctorToTypes.shrink.{v} (total G)))
      (elementsPrestack G) where
  toFunctor :=
    (CategoryOfElements.costructuredArrowYonedaEquivalence
      (FunctorToTypes.shrink.{v} (total G))).inverse ⋙
      (BasedCategory.shrinkElementsComparison (total G)).toFunctor ⋙
      (totalElementsComparison G).toFunctor
  w := by
    rw [Functor.assoc, Functor.assoc, (totalElementsComparison G).w,
      (BasedCategory.shrinkElementsComparison (total G)).w]
    rfl

/-- The prestack of the shrunken total presheaf is equivalent over the base to the
slice category-of-elements prestack. -/
theorem isEquivalence_smallTotalPrestackComparison
    (G : (Over S)ᵒᵖ ⥤ Type w) [FunctorToTypes.Small.{v} (total G)] :
    (smallTotalPrestackComparison G).toFunctor.IsEquivalence := by
  have h₁ :=
    (CategoryOfElements.costructuredArrowYonedaEquivalence
      (FunctorToTypes.shrink.{v} (total G))).isEquivalence_inverse
  have h₂ := BasedCategory.isEquivalence_shrinkElementsComparison (total G)
  have h₃ := isEquivalence_totalElementsComparison G
  have h₁₂ : ((CategoryOfElements.costructuredArrowYonedaEquivalence
      (FunctorToTypes.shrink.{v} (total G))).inverse ⋙
        (BasedCategory.shrinkElementsComparison (total G)).toFunctor).IsEquivalence :=
    Functor.isEquivalence_trans _ _
  exact Functor.isEquivalence_trans _ _

/-- Pointwise smallness of the original slice presheaf is enough to apply the
universe-safe total-prestack comparison. -/
theorem isEquivalence_smallTotalPrestackComparison_of_small
    (G : (Over S)ᵒᵖ ⥤ Type w) [∀ A, Small.{v} (G.obj A)] :
    let _ : FunctorToTypes.Small.{v} (total G) := small_total_of_small G
    (smallTotalPrestackComparison G).toFunctor.IsEquivalence := by
  let _ : FunctorToTypes.Small.{v} (total G) := small_total_of_small G
  exact isEquivalence_smallTotalPrestackComparison G

end CategoryTheory.PresheafOver
