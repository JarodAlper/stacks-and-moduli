module

public import StacksAndModuli.«Section4.1-Definitions».«part4.1.1-representable-morphisms-and-algebraic-spaces»
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Open substacks as full sub-based-categories

This file supplies the machinery that `def:topology-of-stacks` (§4.3 of *Stacks and
Moduli*) needs in order to be a topology: a dictionary between *open substack inclusions*
`𝒰 ⥤ᵇ 𝒳` and *object properties* of `𝒳`.

The point of the dictionary is a universe bound. `AlgebraicGeometry.BasedCategory.pointTopology`
declares a subset of `|𝒳|` open when it is the point-image of an open substack inclusion
`i : 𝒰 ⥤ᵇ 𝒳` with `𝒰` in the *same* universes as `𝒳`. The fiber product of two such lands in
`BasedCategory.{v₂, max u₂ v₂}` (Construction 3.4.33), which is not `BasedCategory.{v₂, u₂}`;
so the fiber product cannot itself serve as the witness for the intersection of two open
subsets. A *full sub-based-category* `𝒳.restrict Q` of `𝒳`, on the other hand, stays in
`BasedCategory.{v₂, u₂}`, and every open substack is equivalent to one — so the intersection
and the union of open subsets can be realized there. See the `def:topology-of-stacks` entries
in `StacksAndModuli/Section4.3-Properties/COMMENTARY.md`.

## Main results

Passing from a property to a substack:

* `CategoryTheory.BasedCategory.restrict` and `restrictι`: the full sub-based-category on
  the objects satisfying `Q`, and its (fully faithful) inclusion.
* `CategoryTheory.BasedCategory.isRepresentedBy_fiberProduct_restrictι`: if the objects of
  `𝒮/T` whose image under `g : 𝒮/T ⥤ᵇ 𝒵` satisfies `Q` are exactly those whose structure
  morphism factors through a monomorphism `j : W ⟶ T`, then `𝒵|_Q ×_𝒵 (𝒮/T)` is
  represented by `W`, and the classified morphism is `j`
  (`restrictFiberProductLift_comp_snd`).

Passing from a substack to a property:

* `CategoryTheory.BasedFunctor.fiberEssImage`: the objects isomorphic to one in the image of
  `F` *by an isomorphism lying over an identity* — the closure property that objects of a
  fiber product actually provide (`BasedCategory.FiberClosed`), weaker than
  `ObjectProperty.IsClosedUnderIsomorphisms`.
* `CategoryTheory.BasedCategory.fiberEssImage_obj_iff_factors`: if `E` realizes
  `𝒜 ×_𝒵 (𝒮/T)` as `𝒮/T'`, then `g(X)` lies in the fiber-essential image of `F` exactly when
  the structure morphism of `X` factors through the morphism `T' ⟶ T` classified by `E`.
  This is the converse of the previous item, and it is what extracts the open subscheme from
  a representability datum.

Supporting lemmas of independent interest:

* `CategoryTheory.BasedCategory.fiberProductSnd_faithful` / `fiberProductSnd_full`: the second
  projection of a fiber product inherits full faithfulness from the first factor.
* `CategoryTheory.BasedCategory.overBased_map_full`: `𝒮/W ⥤ᵇ 𝒮/T` is full when `W ⟶ T` is a
  monomorphism.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

open CategoryTheory Functor BasedCategory

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]

namespace BasedFunctor

variable {𝒜 : BasedCategory.{v₂, u₂} 𝒮} {𝒵 : BasedCategory.{v₃, u₃} 𝒮}

/-- The *fiber-essential image* of a morphism of based categories: the objects of `𝒵`
isomorphic to an object in the image of `F` by an isomorphism lying over an identity. -/
def fiberEssImage (F : 𝒜 ⥤ᵇ 𝒵) : ObjectProperty 𝒵.obj := fun x =>
  ∃ (u : 𝒜.obj) (e : F.obj u ≅ x), IsHomLift 𝒵.p (𝟙 (𝒵.p.obj x)) e.hom

lemma fiberEssImage_of_iso {F : 𝒜 ⥤ᵇ 𝒵} {x y : 𝒵.obj} (hx : F.fiberEssImage x)
    (e : x ≅ y) (he : IsHomLift 𝒵.p (𝟙 (𝒵.p.obj y)) e.hom) : F.fiberEssImage y := by
  obtain ⟨u, e', he'⟩ := hx
  haveI := he'
  haveI := he
  refine ⟨u, e'.trans e, ?_⟩
  have h1 := IsHomLift.fac' 𝒵.p (𝟙 (𝒵.p.obj x)) e'.hom
  have h2 := IsHomLift.fac' 𝒵.p (𝟙 (𝒵.p.obj y)) e.hom
  refine IsHomLift.of_fac' 𝒵.p _ _
    ((IsHomLift.domain_eq 𝒵.p (𝟙 (𝒵.p.obj x)) e'.hom).trans
      (IsHomLift.domain_eq 𝒵.p (𝟙 (𝒵.p.obj y)) e.hom)) rfl ?_
  simp [Iso.trans, h1, h2]

end BasedFunctor

namespace BasedCategory

/-- An object property of a based category is *fiber-closed* if it is stable under
isomorphisms lying over an identity. This is the closure property that the objects of a
fiber product actually provide, and it is weaker than
`CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms`. -/
def FiberClosed {𝒵 : BasedCategory.{v₃, u₃} 𝒮} (Q : ObjectProperty 𝒵.obj) : Prop :=
  ∀ ⦃x y : 𝒵.obj⦄ (e : x ≅ y), IsHomLift 𝒵.p (𝟙 (𝒵.p.obj x)) e.hom → Q x → Q y

/-- An isomorphism lying over the identity of the target also lies over the identity of
the source. -/
lemma isHomLift_id_domain {𝒵 : BasedCategory.{v₃, u₃} 𝒮} {x y : 𝒵.obj} (e : x ≅ y)
    (h : IsHomLift 𝒵.p (𝟙 (𝒵.p.obj y)) e.hom) :
    IsHomLift 𝒵.p (𝟙 (𝒵.p.obj x)) e.hom := by
  haveI := h
  have hd : 𝒵.p.obj x = 𝒵.p.obj y := IsHomLift.domain_eq 𝒵.p (𝟙 (𝒵.p.obj y)) e.hom
  rw [hd]
  exact h

/-- An isomorphism lying over the identity of the source also lies over the identity of
the target. -/
lemma isHomLift_id_codomain {𝒵 : BasedCategory.{v₃, u₃} 𝒮} {x y : 𝒵.obj} (e : x ≅ y)
    (h : IsHomLift 𝒵.p (𝟙 (𝒵.p.obj x)) e.hom) :
    IsHomLift 𝒵.p (𝟙 (𝒵.p.obj y)) e.hom := by
  haveI := h
  have hc : 𝒵.p.obj y = 𝒵.p.obj x := IsHomLift.codomain_eq 𝒵.p (𝟙 (𝒵.p.obj x)) e.hom
  rw [hc]
  exact h

lemma FiberClosed.inf {𝒵 : BasedCategory.{v₃, u₃} 𝒮} {Q Q' : ObjectProperty 𝒵.obj}
    (hQ : FiberClosed Q) (hQ' : FiberClosed Q') : FiberClosed (Q ⊓ Q') :=
  fun _ _ e he h => ⟨hQ e he h.1, hQ' e he h.2⟩

end BasedCategory

namespace BasedCategory

variable (𝒳 : BasedCategory.{v₂, u₂} 𝒮)

/-- The full sub-based-category on the objects satisfying `P`. -/
def restrict (P : ObjectProperty 𝒳.obj) : BasedCategory.{v₂, u₂} 𝒮 where
  obj := P.FullSubcategory
  category := inferInstance
  p := P.ι ⋙ 𝒳.p

/-- The inclusion of a full sub-based-category. -/
def restrictι (P : ObjectProperty 𝒳.obj) : 𝒳.restrict P ⥤ᵇ 𝒳 where
  toFunctor := P.ι
  w := rfl

instance (P : ObjectProperty 𝒳.obj) : (𝒳.restrictι P).toFunctor.Full :=
  inferInstanceAs P.ι.Full

instance (P : ObjectProperty 𝒳.obj) : (𝒳.restrictι P).toFunctor.Faithful :=
  inferInstanceAs P.ι.Faithful

@[simp]
lemma restrictι_obj (P : ObjectProperty 𝒳.obj) (u : (𝒳.restrict P).obj) :
    (𝒳.restrictι P).obj u = u.obj := rfl

variable {𝒳}

/-- For a fiber-closed object property, the fiber-essential image of the inclusion of the
corresponding full sub-based-category is the property itself. -/
lemma fiberEssImage_restrictι (P : ObjectProperty 𝒳.obj) (hP : FiberClosed P) :
    (𝒳.restrictι P).fiberEssImage = P := by
  ext x
  constructor
  · rintro ⟨u, e, he⟩
    exact hP e (isHomLift_id_domain e he) u.property
  · intro hx
    exact ⟨⟨x, hx⟩, Iso.refl x, by simp⟩

section EssImageLemmas

variable {𝒜 : BasedCategory.{v₂, u₂} 𝒮} {𝒵 : BasedCategory.{v₃, u₃} 𝒮}

open BasedFunctor

/-- An object of `𝒮/T` is in the fiber-essential image of `𝒮/W → 𝒮/T` exactly when its
structure morphism factors through `f`. -/
lemma fiberEssImage_overBased_map {W T : 𝒮} (f : W ⟶ T) (X : Over T) :
    (overBased.map f).fiberEssImage X ↔ ∃ k : X.left ⟶ W, k ≫ f = X.hom := by
  constructor
  · rintro ⟨u, e, he⟩
    haveI := he
    have h : (overBased T).p.obj ((overBased.map f).obj u) = (overBased T).p.obj X :=
      IsHomLift.domain_eq (overBased T).p (𝟙 ((overBased T).p.obj X)) e.hom
    have hfac := IsHomLift.fac' (overBased T).p (𝟙 ((overBased T).p.obj X)) e.hom
    have hel : e.hom.left = eqToHom h := by simpa using hfac
    have hw := Over.w e.hom
    rw [hel] at hw
    refine ⟨eqToHom h.symm ≫ u.hom, ?_⟩
    have h2 : u.hom ≫ f = ((overBased.map f).obj u).hom := rfl
    rw [Category.assoc, h2, ← hw, ← Category.assoc, eqToHom_trans, eqToHom_refl,
      Category.id_comp]
  · rintro ⟨k, hk⟩
    refine ⟨Over.mk k, Over.isoMk (Iso.refl _) ?_, ?_⟩
    · simp only [Iso.refl_hom, Category.id_comp]
      exact hk.symm
    refine IsHomLift.of_fac' (overBased T).p _ _ rfl rfl ?_
    simp

end EssImageLemmas

section FiberProductEssImage

variable {𝒜 : BasedCategory.{v₂, u₂} 𝒮} {𝒵 : BasedCategory.{v₃, u₃} 𝒮} {T : 𝒮}

open BasedFunctor

/-- An object `X` of `𝒮/T` is in the fiber-essential image of the second projection of
`𝒜 ×_𝒵 (𝒮/T)` exactly when `g(X)` is in the fiber-essential image of `F`. -/
lemma fiberEssImage_fiberProductSnd (F : 𝒜 ⥤ᵇ 𝒵) (g : overBased T ⥤ᵇ 𝒵) (X : Over T) :
    (fiberProductSnd F g).fiberEssImage X ↔ F.fiberEssImage (g.obj X) := by
  constructor
  · rintro ⟨z, e, he⟩
    haveI := he
    haveI := z.isHomLift
    have hdom : (overBased T).p.obj z.snd = (overBased T).p.obj X :=
      IsHomLift.domain_eq (overBased T).p (𝟙 ((overBased T).p.obj X)) e.hom
    haveI hge : IsHomLift 𝒵.p (𝟙 ((overBased T).p.obj X)) (g.map e.hom) :=
      BasedFunctor.preserves_isHomLift g _ e.hom
    have ha : 𝒵.p.obj (F.obj z.fst) = 𝒵.p.obj (g.obj X) := by
      rw [F.w_obj z.fst, ← z.over_eq, hdom, g.w_obj X]
    refine ⟨z.fst, z.iso ≪≫ g.mapIso e, IsHomLift.of_fac' 𝒵.p _ _ ha rfl ?_⟩
    simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp,
      IsHomLift.fac' 𝒵.p (𝟙 (𝒜.p.obj z.fst)) z.iso.hom,
      IsHomLift.fac' 𝒵.p (𝟙 ((overBased T).p.obj X)) (g.map e.hom)]
    simp
  · rintro ⟨u, e, he⟩
    haveI := he
    have hu : 𝒵.p.obj (F.obj u) = 𝒵.p.obj (g.obj X) :=
      IsHomLift.domain_eq 𝒵.p (𝟙 (𝒵.p.obj (g.obj X))) e.hom
    have hu' : (overBased T).p.obj X = 𝒜.p.obj u := by
      rw [← F.w_obj u, hu, g.w_obj X]
    have hiso : IsHomLift 𝒵.p (𝟙 (𝒜.p.obj u)) e.hom := by
      refine IsHomLift.of_fac' 𝒵.p _ _ (F.w_obj u) ?_ ?_
      · rw [← hu', g.w_obj X]
      · simp [IsHomLift.fac' 𝒵.p (𝟙 (𝒵.p.obj (g.obj X))) e.hom]
    refine ⟨⟨u, X, hu', e, hiso⟩, Iso.refl X, ?_⟩
    refine IsHomLift.of_fac' (overBased T).p _ _ rfl rfl ?_
    simp

end FiberProductEssImage

section FullyFaithfulSnd

variable {𝒜 : BasedCategory.{v₂, u₂} 𝒮} {𝒵 : BasedCategory.{v₃, u₃} 𝒮}
  {𝒲 : BasedCategory.{v₄, u₄} 𝒮} {F : 𝒜 ⥤ᵇ 𝒵} {G : 𝒲 ⥤ᵇ 𝒵}

/-- If `F` is faithful, so is the second projection of the fiber product along `F`. -/
instance fiberProductSnd_faithful [F.toFunctor.Faithful] :
    (fiberProductSnd F G).toFunctor.Faithful where
  map_injective {a b} φ ψ h := by
    have hs : FiberProductHom.snd φ = FiberProductHom.snd ψ := h
    have hw : F.map (FiberProductHom.fst φ) ≫ b.iso.hom
        = F.map (FiberProductHom.fst ψ) ≫ b.iso.hom := by
      rw [FiberProductHom.w, FiberProductHom.w, hs]
    have : F.map (FiberProductHom.fst φ) = F.map (FiberProductHom.fst ψ) := by
      exact (cancel_mono b.iso.hom).mp hw
    exact FiberProductHom.ext (F.toFunctor.map_injective this) hs

/-- If `F` is full and faithful, so is the second projection of the fiber product
along `F`. -/
instance fiberProductSnd_full [F.toFunctor.Full] [F.toFunctor.Faithful] :
    (fiberProductSnd F G).toFunctor.Full where
  map_surjective {a b} s := by
    obtain ⟨t, ht⟩ := F.toFunctor.map_surjective (a.iso.hom ≫ G.map s ≫ b.iso.inv)
    have hGs : G.map s = a.iso.inv ≫ F.map t ≫ b.iso.hom := by
      rw [ht]; simp
    haveI h1 : IsHomLift 𝒵.p (𝟙 (𝒜.p.obj a.fst)) a.iso.inv :=
      IsHomLift.lift_id_inv 𝒵.p (𝒜.p.obj a.fst) a.iso
    haveI h2 : IsHomLift 𝒵.p (𝒜.p.map t) (F.map t) :=
      BasedFunctor.preserves_isHomLift F (𝒜.p.map t) t
    haveI h3 : IsHomLift 𝒵.p (𝟙 (𝒜.p.obj b.fst)) b.iso.hom := b.isHomLift
    haveI h4 : IsHomLift 𝒵.p (𝒜.p.map t) (a.iso.inv ≫ F.map t ≫ b.iso.hom) :=
      inferInstance
    haveI h5 : IsHomLift 𝒵.p (𝒜.p.map t) (G.map s) := by rw [hGs]; exact h4
    haveI h6 : IsHomLift 𝒲.p (𝒜.p.map t) s := BasedFunctor.isHomLift_map (F := G) (𝒜.p.map t) s
    exact ⟨⟨t, s, h6, by rw [ht]; simp⟩, rfl⟩

end FullyFaithfulSnd

/-- Every value of a morphism factoring through `i` lies in the fiber-essential image
of `i`. -/
lemma fiberEssImage_comp_obj {𝒲 : BasedCategory.{v₄, u₄} 𝒮} (i : 𝒜 ⥤ᵇ 𝒵)
    (G : 𝒲 ⥤ᵇ 𝒜) (X : 𝒲.obj) : i.fiberEssImage ((G.comp i).obj X) :=
  ⟨G.obj X, Iso.refl _, IsHomLift.id rfl⟩

/-- The fiber-essential image of the values of a morphism only depends on its
2-isomorphism class. -/
lemma fiberEssImage_obj_of_iso {𝒲 : BasedCategory.{v₄, u₄} 𝒮} (i : 𝒜 ⥤ᵇ 𝒵)
    {g g' : 𝒲 ⥤ᵇ 𝒵} (e : g ≅ g') (X : 𝒲.obj) (h : i.fiberEssImage (g.obj X)) :
    i.fiberEssImage (g'.obj X) := by
  refine BasedFunctor.fiberEssImage_of_iso h (asIso (e.hom.toNatTrans.app X)) ?_
  have hl := BasedNatTrans.app_isHomLift (α := e.hom) X
  have h2 : 𝒵.p.obj (g'.obj X) = 𝒲.p.obj X := g'.w_obj X
  rw [h2]
  exact hl

section StepC

variable {𝒜 : BasedCategory.{v₂, u₂} 𝒮} {𝒵 : BasedCategory.{v₃, u₃} 𝒮}
  {𝒲 : BasedCategory.{v₄, u₄} 𝒮} {T : 𝒮}

open BasedFunctor

/-- The fiber-essential image only depends on the 2-isomorphism class of the morphism. -/
lemma fiberEssImage_congr {F F' : 𝒜 ⥤ᵇ 𝒵} (α : F ≅ F') :
    F.fiberEssImage = F'.fiberEssImage := by
  have key : ∀ (G G' : 𝒜 ⥤ᵇ 𝒵) (_ : G ≅ G') (x : 𝒵.obj), G.fiberEssImage x →
      G'.fiberEssImage x := by
    rintro G G' β x ⟨u, e, he⟩
    haveI := he
    haveI hb : IsHomLift 𝒵.p (𝟙 (𝒵.p.obj (G'.obj u))) (β.inv.toNatTrans.app u) := by
      have h := BasedNatTrans.app_isHomLift (α := β.inv) u
      have h2 : 𝒵.p.obj (G'.obj u) = 𝒜.p.obj u := G'.w_obj u
      rw [h2]
      exact h
    refine ⟨u, asIso (β.inv.toNatTrans.app u) ≪≫ e, ?_⟩
    have ha : 𝒵.p.obj (G'.obj u) = 𝒵.p.obj x := by
      rw [G'.w_obj u, ← G.w_obj u]
      exact IsHomLift.domain_eq 𝒵.p (𝟙 (𝒵.p.obj x)) e.hom
    refine IsHomLift.of_fac' 𝒵.p _ _ ha rfl ?_
    simp only [Iso.trans_hom, asIso_hom, Functor.map_comp,
      IsHomLift.fac' 𝒵.p (𝟙 (𝒵.p.obj (G'.obj u))) (β.inv.toNatTrans.app u),
      IsHomLift.fac' 𝒵.p (𝟙 (𝒵.p.obj x)) e.hom]
    simp
  ext x
  exact ⟨key F F' α x, key F' F α.symm x⟩

/-- The fiber-essential image is fiber-closed. -/
lemma fiberClosed_fiberEssImage (F : 𝒜 ⥤ᵇ 𝒵) : FiberClosed F.fiberEssImage :=
  fun _ _ e he h => fiberEssImage_of_iso h e (isHomLift_id_codomain e he)

/-- Precomposing shrinks the fiber-essential image. -/
lemma fiberEssImage_comp_le (E : 𝒲 ⥤ᵇ 𝒜) (F : 𝒜 ⥤ᵇ 𝒵) :
    (E.comp F).fiberEssImage ≤ F.fiberEssImage := by
  rintro x ⟨u, e, he⟩
  exact ⟨E.obj u, e, he⟩

/-- The ordinary essential image of a morphism into `𝒮/T` detects factorizations. -/
lemma essImage_overBased_map_iff {W : 𝒮} (f : W ⟶ T) (X : Over T) :
    (overBased.map f).toFunctor.essImage X ↔ ∃ k : X.left ⟶ W, k ≫ f = X.hom := by
  constructor
  · rintro ⟨y, ⟨e⟩⟩
    refine ⟨e.inv.left ≫ y.hom, ?_⟩
    have hw := Over.w e.inv
    have h2 : y.hom ≫ f = ((overBased.map f).obj y).hom := rfl
    rw [Category.assoc, h2, hw]
  · rintro ⟨k, hk⟩
    refine ⟨Over.mk k, ⟨Over.isoMk (Iso.refl _) ?_⟩⟩
    simp only [Iso.refl_hom, Category.id_comp]
    exact hk.symm

/-- **Extraction of the open from a representation.** Let `F : 𝒜 ⥤ᵇ 𝒵` be a morphism of
prestacks, `g : 𝒮/T ⥤ᵇ 𝒵`, and let `E` realize the fiber product `𝒜 ×_𝒵 (𝒮/T)` as `𝒮/T'`.
Then an object `X` of `𝒮/T` has `g(X)` in the fiber-essential image of `F` exactly when the
structure morphism of `X` factors through the morphism `T' ⟶ T` classified by `E`. -/
lemma fiberEssImage_obj_iff_factors (F : 𝒜 ⥤ᵇ 𝒵) (g : overBased T ⥤ᵇ 𝒵) {T' : 𝒮}
    (E : overBased T' ⥤ᵇ fiberProduct F g) (hE : E.toFunctor.IsEquivalence) (X : Over T) :
    F.fiberEssImage (g.obj X) ↔
      ∃ k : X.left ⟶ T', k ≫ (E.comp (fiberProductSnd F g)).overHom = X.hom := by
  rw [← fiberEssImage_fiberProductSnd]
  obtain ⟨α⟩ := BasedFunctor.nonempty_iso_overBased_map (E.comp (fiberProductSnd F g))
  set f := (E.comp (fiberProductSnd F g)).overHom with hf
  have β := (BasedNatTrans.forgetful (overBased T') (overBased T)).mapIso α
  constructor
  · rintro ⟨z, e, -⟩
    haveI := hE
    obtain ⟨y, ⟨ε⟩⟩ := Functor.EssSurj.mem_essImage (F := E.toFunctor) z
    have e2 : (E.comp (fiberProductSnd F g)).obj y ≅ X :=
      ((fiberProductSnd F g).mapIso ε).trans e
    have e3 : (overBased.map f).obj y ≅ X := (β.app y).symm.trans e2
    exact (essImage_overBased_map_iff f X).mp ⟨y, ⟨e3⟩⟩
  · intro hk
    have h1 : (overBased.map f).fiberEssImage X :=
      (fiberEssImage_overBased_map f X).mpr hk
    rw [← fiberEssImage_congr α] at h1
    exact fiberEssImage_comp_le E (fiberProductSnd F g) X h1

end StepC

section StepB

variable {𝒜 : BasedCategory.{v₂, u₂} 𝒮} {𝒵 : BasedCategory.{v₃, u₃} 𝒮} {T W : 𝒮}

open BasedFunctor

/-- `𝒮/W → 𝒮/T` is faithful. -/
instance overBased_map_faithful (j : W ⟶ T) : (overBased.map j).toFunctor.Faithful where
  map_injective {x y} φ ψ h := by
    ext
    exact congrArg (fun (t : ((overBased.map j).obj x) ⟶ ((overBased.map j).obj y)) =>
      t.left) h

/-- `𝒮/W → 𝒮/T` is full when `j` is a monomorphism. -/
instance overBased_map_full (j : W ⟶ T) [Mono j] : (overBased.map j).toFunctor.Full where
  map_surjective {x y} φ := by
    have h2 : φ.left ≫ (y.hom ≫ j) = x.hom ≫ j := Over.w φ
    have h3 : (φ.left ≫ y.hom) ≫ j = x.hom ≫ j := by rw [Category.assoc]; exact h2
    exact ⟨Over.homMk φ.left ((cancel_mono j).mp h3), by ext; rfl⟩

/-- Corestriction of a morphism of based categories to a full sub-based-category. -/
def corestrict {𝒯 : BasedCategory.{v₄, u₄} 𝒮} (H : 𝒯 ⥤ᵇ 𝒵) (Q : ObjectProperty 𝒵.obj)
    (hH : ∀ t, Q (H.obj t)) : 𝒯 ⥤ᵇ 𝒵.restrict Q where
  toFunctor := Q.lift H.toFunctor hH
  w := H.w

lemma corestrict_comp_restrictι {𝒯 : BasedCategory.{v₄, u₄} 𝒮} (H : 𝒯 ⥤ᵇ 𝒵)
    (Q : ObjectProperty 𝒵.obj) (hH : ∀ t, Q (H.obj t)) :
    (corestrict H Q hH).comp (𝒵.restrictι Q) = H :=
  BasedFunctor.ext_of_toFunctor_eq rfl

variable (g : overBased T ⥤ᵇ 𝒵) (Q : ObjectProperty 𝒵.obj) (j : W ⟶ T) [Mono j]
  (hQ : ∀ X : Over T, Q (g.obj X) ↔ ∃ k : X.left ⟶ W, k ≫ j = X.hom)

/-- The lift `𝒮/W ⥤ᵇ 𝒵|_Q ×_𝒵 (𝒮/T)` attached to an open condition realized by `j`. -/
def restrictFiberProductLift : overBased W ⥤ᵇ fiberProduct (𝒵.restrictι Q) g :=
  fiberProductLift
    (corestrict ((overBased.map j).comp g) Q
      (fun x => (hQ ((overBased.map j).obj x)).mpr ⟨x.hom, rfl⟩))
    (overBased.map j) (Iso.refl _)

lemma restrictFiberProductLift_comp_snd :
    (restrictFiberProductLift g Q j hQ).comp (fiberProductSnd (𝒵.restrictι Q) g)
      = overBased.map j :=
  fiberProductLift_comp_snd _ _ _

/-- The lift is an equivalence: the fiber product `𝒵|_Q ×_𝒵 (𝒮/T)` is represented by `W`. -/
lemma isEquivalence_restrictFiberProductLift (hQc : FiberClosed Q) :
    (restrictFiberProductLift g Q j hQ).toFunctor.IsEquivalence := by
  haveI hri : (𝒵.restrictι Q).toFunctor.Faithful := inferInstanceAs Q.ι.Faithful
  haveI hri' : (𝒵.restrictι Q).toFunctor.Full := inferInstanceAs Q.ι.Full
  haveI hsndf : (fiberProductSnd (𝒵.restrictι Q) g).toFunctor.Faithful :=
    fiberProductSnd_faithful (F := 𝒵.restrictι Q) (G := g)
  haveI hsndF : (fiberProductSnd (𝒵.restrictι Q) g).toFunctor.Full :=
    fiberProductSnd_full (F := 𝒵.restrictι Q) (G := g)
  have hF : (restrictFiberProductLift g Q j hQ).toFunctor ⋙
      (fiberProductSnd (𝒵.restrictι Q) g).toFunctor = (overBased.map j).toFunctor :=
    congrArg BasedFunctor.toFunctor (restrictFiberProductLift_comp_snd g Q j hQ)
  haveI hfa : ((restrictFiberProductLift g Q j hQ).toFunctor ⋙
      (fiberProductSnd (𝒵.restrictι Q) g).toFunctor).Faithful := by
    rw [hF]; exact overBased_map_faithful j
  haveI hE1 : (restrictFiberProductLift g Q j hQ).toFunctor.Faithful :=
    Functor.Faithful.of_comp _ (fiberProductSnd (𝒵.restrictι Q) g).toFunctor
  haveI hfu : ((restrictFiberProductLift g Q j hQ).toFunctor ⋙
      (fiberProductSnd (𝒵.restrictι Q) g).toFunctor).Full := by
    rw [hF]; exact overBased_map_full j
  haveI hE2 : (restrictFiberProductLift g Q j hQ).toFunctor.Full :=
    Functor.Full.of_comp_faithful _ (fiberProductSnd (𝒵.restrictι Q) g).toFunctor
  haveI hE3 : (restrictFiberProductLift g Q j hQ).toFunctor.EssSurj := by
    constructor
    intro z
    have hz : Q (g.obj z.snd) := hQc z.iso z.isHomLift z.fst.property
    obtain ⟨k, hk⟩ := (hQ z.snd).mp hz
    refine ⟨Over.mk k, ⟨?_⟩⟩
    have e : (fiberProductSnd (𝒵.restrictι Q) g).obj
          ((restrictFiberProductLift g Q j hQ).obj (Over.mk k))
        ≅ (fiberProductSnd (𝒵.restrictι Q) g).obj z := by
      refine Over.isoMk (Iso.refl _) ?_
      simp only [Iso.refl_hom, Category.id_comp]
      exact hk.symm
    exact Functor.preimageIso (fiberProductSnd (𝒵.restrictι Q) g).toFunctor e
  exact ⟨hE1, hE2, hE3⟩

/-- **Step B.** If the objects of `𝒮/T` whose image under `g` satisfies `Q` are exactly
those whose structure morphism factors through the monomorphism `j : W ⟶ T`, then the
fiber product of the full sub-based-category `𝒵|_Q` with `𝒮/T` over `𝒵` is represented
by `W`. -/
lemma isRepresentedBy_fiberProduct_restrictι (hQc : FiberClosed Q)
    (j' : W ⟶ T) [Mono j']
    (hQ' : ∀ X : Over T, Q (g.obj X) ↔ ∃ k : X.left ⟶ W, k ≫ j' = X.hom) :
    (fiberProduct (𝒵.restrictι Q) g).IsRepresentedBy W :=
  ⟨restrictFiberProductLift g Q j' hQ',
    isEquivalence_restrictFiberProductLift g Q j' hQ' hQc⟩

end StepB

end BasedCategory

end CategoryTheory
