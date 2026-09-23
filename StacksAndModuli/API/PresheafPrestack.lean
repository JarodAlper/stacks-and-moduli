module

public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.2-examples»
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory

/-!
# Prestacks associated to presheaves

Reusable packaging of the category of elements of a presheaf as a based category.
The construction first occurs in Example 3.4.7 of *Stacks and Moduli* and is used
by Exercise 3.4.39 and the representability theory of Chapter 4.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Opposite

universe w v u v' u'

namespace CategoryTheory.Functor.IsFiberedInGroupoids

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]

/-- A lift through two successive functors is a lift through their composite. -/
lemma comp_isHomLift (p : E ⥤ D) (q : D ⥤ C) {R S : D} {P Q : C} {a b : E}
    (f : R ⟶ S) (g : P ⟶ Q) (φ : a ⟶ b) [IsHomLift p f φ]
    [IsHomLift q g f] : IsHomLift (p ⋙ q) g φ := by
  subst_hom_lift p f φ
  subst_hom_lift q g (p.map φ)
  exact IsHomLift.map (p := p ⋙ q) φ

/-- The composite of two categories fibered in groupoids is fibered in groupoids.
The proof successively applies the two cartesian universal properties. -/
instance comp (p : E ⥤ D) (q : D ⥤ C) [p.IsFiberedInGroupoids]
    [q.IsFiberedInGroupoids] : (p ⋙ q).IsFiberedInGroupoids where
  exists_isHomLift {a R} f := by
    obtain ⟨d, ψ, hψ⟩ := IsFiberedInGroupoids.exists_isHomLift (p := q) f
    obtain ⟨b, φ, hφ⟩ := IsFiberedInGroupoids.exists_isHomLift (p := p) ψ
    refine ⟨b, φ, ?_⟩
    exact comp_isHomLift p q ψ f φ
  isStronglyCartesian {a b} φ := by
    constructor
    intro a' g ψ hψ
    have hbaseψ : g ≫ q.map (p.map φ) = q.map (p.map ψ) := by
      have h := IsHomLift.eq_of_isHomLift (p ⋙ q) (g ≫ (p ⋙ q).map φ) ψ
      simpa using h
    letI hqψ : IsHomLift q (g ≫ q.map (p.map φ)) (p.map ψ) := by
      exact hbaseψ.symm ▸ IsHomLift.map (p := q) (p.map ψ)
    obtain ⟨h, ⟨hhq, hhfac⟩, hhuniq⟩ :=
      IsStronglyCartesian.universal_property q (q.map (p.map φ)) (p.map φ)
        g (g ≫ q.map (p.map φ)) rfl (p.map ψ)
    letI hpψ : IsHomLift p (h ≫ p.map φ) ψ :=
      hhfac.symm ▸ IsHomLift.map (p := p) ψ
    obtain ⟨χ, ⟨hχp, hχfac⟩, hχuniq⟩ :=
      IsStronglyCartesian.universal_property p (p.map φ) φ
        h (h ≫ p.map φ) rfl ψ
    refine ⟨χ, ⟨?_, hχfac⟩, ?_⟩
    · exact comp_isHomLift p q h g χ
    · intro χ' hχ'
      letI : IsHomLift (p ⋙ q) g χ' := hχ'.1
      have hbaseχ' : g = q.map (p.map χ') := by
        have h := IsHomLift.eq_of_isHomLift (p ⋙ q) g χ'
        simpa using h
      have hqχ' : IsHomLift q g (p.map χ') :=
        hbaseχ'.symm ▸ IsHomLift.map (p := q) (p.map χ')
      have hbasefac : p.map χ' ≫ p.map φ = p.map ψ := by
        rw [← p.map_comp, hχ'.2]
      have hbase : p.map χ' = h := hhuniq (p.map χ') ⟨hqχ', hbasefac⟩
      have hpχ' : IsHomLift p h χ' := hbase ▸ IsHomLift.map (p := p) χ'
      exact hχuniq χ' ⟨hpχ', hχ'.2⟩

end CategoryTheory.Functor.IsFiberedInGroupoids

namespace CategoryTheory.BasedCategory

variable {𝒮 : Type u} [Category.{v} 𝒮]

/-- The prestack associated to a presheaf `F`: its objects are pairs `(S, a)` with
`S : 𝒮` and `a ∈ F(S)`, and its projection remembers `S`. -/
abbrev ofPresheaf (F : 𝒮ᵒᵖ ⥤ Type v) : BasedCategory 𝒮 where
  obj := CostructuredArrow yoneda F
  p := CostructuredArrow.proj yoneda F

/-- The category of elements of a presheaf is fibered in groupoids over its base. -/
instance (F : 𝒮ᵒᵖ ⥤ Type v) : (ofPresheaf F).p.IsFiberedInGroupoids :=
  inferInstanceAs (CostructuredArrow.proj yoneda F).IsFiberedInGroupoids

/-- A natural transformation of presheaves induces a morphism of the associated
prestacks. -/
def ofPresheaf.map {F G : 𝒮ᵒᵖ ⥤ Type v} (φ : F ⟶ G) : ofPresheaf F ⥤ᵇ ofPresheaf G where
  toFunctor := CostructuredArrow.map φ
  w := rfl

/-- The universe-polymorphic category-of-elements prestack of a presheaf. Unlike
`ofPresheaf`, this construction also accepts presheaves whose values live in a universe
different from the hom universe of the base category. -/
abbrev elementsPrestack (F : 𝒮ᵒᵖ ⥤ Type w) : BasedCategory.{v, max u w} 𝒮 where
  obj := F.Elementsᵒᵖ
  p := (CategoryOfElements.π F).leftOp

/-- The opposite category of elements of any universe-valued presheaf is fibered in
groupoids over its base. -/
instance (F : 𝒮ᵒᵖ ⥤ Type w) : (elementsPrestack F).p.IsFiberedInGroupoids where
  exists_isHomLift {a R} f := by
    let b : F.Elementsᵒᵖ := op ⟨op R, F.map f.op a.unop.2⟩
    let φ : b ⟶ a := (CategoryOfElements.homMk _ _ f.op rfl).op
    refine ⟨b, φ, ?_⟩
    have h := IsHomLift.map (p := (elementsPrestack F).p) φ
    simpa [elementsPrestack, b, φ] using h
  isStronglyCartesian {a b} φ := by
    constructor
    intro a' g ψ hψ
    have hg : g ≫ (elementsPrestack F).p.map φ = (elementsPrestack F).p.map ψ :=
      IsHomLift.eq_of_isHomLift _ _ _
    let χ : a' ⟶ a :=
      (CategoryOfElements.homMk _ _ g.op (by
        rw [← CategoryOfElements.map_snd φ.unop, ← Functor.map_comp_apply]
        have hop : φ.unop.val ≫ g.op = ψ.unop.val := by
          simpa [elementsPrestack] using congrArg Quiver.Hom.op hg
        rw [hop, CategoryOfElements.map_snd ψ.unop])).op
    refine ⟨χ, ⟨?_, ?_⟩, ?_⟩
    · have h := IsHomLift.map (p := (elementsPrestack F).p) χ
      simpa [elementsPrestack, χ] using h
    · apply Quiver.Hom.unop_inj
      apply CategoryOfElements.ext
      simpa [χ, elementsPrestack] using congrArg Quiver.Hom.op hg
    · rintro χ' ⟨hχ₁, hχ₂⟩
      apply Quiver.Hom.unop_inj
      apply CategoryOfElements.ext
      have h := IsHomLift.eq_of_isHomLift (elementsPrestack F).p g χ'
      simpa [χ, elementsPrestack] using congrArg Quiver.Hom.op h.symm

/-- A natural transformation induces a morphism of universe-polymorphic
category-of-elements prestacks. -/
def elementsPrestack.map {F G : 𝒮ᵒᵖ ⥤ Type w} (φ : F ⟶ G) :
    elementsPrestack F ⥤ᵇ elementsPrestack G where
  toFunctor := (CategoryOfElements.map φ).op
  w := show (CategoryOfElements.map φ).op ⋙ (CategoryOfElements.π G).leftOp =
      (CategoryOfElements.π F).leftOp from by
    change (CategoryOfElements.map φ ⋙ CategoryOfElements.π G).leftOp =
      (CategoryOfElements.π F).leftOp
    rw [CategoryOfElements.map_π]

/-- A based category is equivalent to a presheaf if it is equivalent over its base
to the category-of-elements prestack of some set-valued presheaf. -/
def IsEquivalentToPresheaf {𝒳 : BasedCategory.{v', u'} 𝒮} : Prop :=
  ∃ (F : 𝒮ᵒᵖ ⥤ Type u')
    (E : elementsPrestack F ⥤ᵇ 𝒳), E.toFunctor.IsEquivalence

section OfPresheafFullyFaithful

variable {F G : 𝒮ᵒᵖ ⥤ Type v}

lemma surjective_app_of_essSurj (φ : F ⟶ G)
    [(ofPresheaf.map φ).toFunctor.EssSurj] (S : 𝒮) :
    Function.Surjective (φ.app (op S)) := by
  intro c
  obtain ⟨x, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := (ofPresheaf.map φ).toFunctor)
    (CostructuredArrow.mk (yonedaEquiv.symm c))
  have hf : yoneda.map e.hom.left ≫ yonedaEquiv.symm c = x.hom ≫ φ :=
    CostructuredArrow.w e.hom
  have hiso : IsIso e.hom.left := by
    refine ⟨e.inv.left, ?_, ?_⟩
    · have := e.hom_inv_id
      exact congrArg CommaMorphism.left this
    · have := e.inv_hom_id
      exact congrArg CommaMorphism.left this
  refine ⟨yonedaEquiv (yoneda.map (inv e.hom.left) ≫ x.hom), ?_⟩
  rw [← yonedaEquiv_comp, Category.assoc, ← hf, ← Category.assoc,
    ← yoneda.map_comp, IsIso.inv_hom_id, yoneda.map_id, Category.id_comp]
  simp

lemma injective_app_of_full (φ : F ⟶ G)
    [(ofPresheaf.map φ).toFunctor.Full] (S : 𝒮) :
    Function.Injective (φ.app (op S)) := by
  intro a b hab
  have huv : (yonedaEquiv.symm a : yoneda.obj S ⟶ F) ≫ φ = yonedaEquiv.symm b ≫ φ := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_comp]
    simpa using hab
  let k : (ofPresheaf.map φ).obj (CostructuredArrow.mk (yonedaEquiv.symm a)) ⟶
      (ofPresheaf.map φ).obj (CostructuredArrow.mk (yonedaEquiv.symm b)) :=
    CostructuredArrow.homMk (𝟙 S) (by
      show yoneda.map (𝟙 S) ≫ (yonedaEquiv.symm b ≫ φ) = yonedaEquiv.symm a ≫ φ
      simp only [CategoryTheory.Functor.map_id, Category.id_comp]
      exact huv.symm)
  obtain ⟨ψ, hψ⟩ := (ofPresheaf.map φ).toFunctor.map_surjective k
  have hleft : ψ.left = 𝟙 S := congrArg CommaMorphism.left hψ
  have hw := CostructuredArrow.w ψ
  rw [hleft] at hw
  have hb : (yonedaEquiv.symm b : yoneda.obj S ⟶ F) = yonedaEquiv.symm a := by
    simpa using hw
  simpa using congrArg yonedaEquiv hb.symm

/-- If the morphism of prestacks induced by a morphism of presheaves is an equivalence,
the morphism of presheaves is an isomorphism. -/
theorem isIso_of_isEquivalence_ofPresheaf_map (φ : F ⟶ G)
    [h : (ofPresheaf.map φ).toFunctor.IsEquivalence] : IsIso φ := by
  have : ∀ S : 𝒮ᵒᵖ, IsIso (φ.app S) := by
    intro S
    induction S with
    | op S =>
      rw [isIso_iff_bijective]
      exact ⟨injective_app_of_full φ S, surjective_app_of_essSurj φ S⟩
  exact NatIso.isIso_of_isIso_app φ

end OfPresheafFullyFaithful

end CategoryTheory.BasedCategory
