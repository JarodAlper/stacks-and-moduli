module

public import StacksAndModuli.API.BasedCategoryOpenSubstack
public import StacksAndModuli.«Section4.1-Definitions».«part4.1.2-deligne-mumford-and-algebraic-stacks»

/-!
# The intersection of two open substacks

The intersection of two open substack inclusions `i₁ : 𝒰₁ ⥤ᵇ 𝒳` and `i₂ : 𝒰₂ ⥤ᵇ 𝒳` is
realized by the full sub-based-category of `𝒳` on the objects lying in both fiber-essential
images — *not* by the fiber product `𝒰₁ ×_𝒳 𝒰₂`, which leaves the universes of `𝒳`
(Construction 3.4.33 puts it in `BasedCategory.{v₂, max u₂ v₂}`). This is what
`AlgebraicGeometry.BasedCategory.pointTopology` needs for `isOpen_inter`, since
`def:topology-of-stacks` quantifies over open substacks in the universes of `𝒳`; see the
`def:topology-of-stacks` entries in `StacksAndModuli/Section4.3-Properties/COMMENTARY.md`.

The proof runs the dictionary of `StacksAndModuli/API/BasedCategoryOpenSubstack.lean` in both
directions. Each `iₖ` cuts out an open subscheme `Wₖ ⊆ T` for every `g : Sch/T ⥤ᵇ 𝒳`
(`exists_opens_fiberEssImage`, from the representability datum); the intersection property
is then cut out by `W₁ ⊓ W₂`, so the fiber product of the full subcategory with `Sch/T` is
represented by `W₁ ⊓ W₂` (`isRepresentedBy_fiberProduct_restrictι`). That the projection is
an open immersion *for every* representation, not just the constructed one, follows because
any two morphisms into `T` defining the same factorization sieve differ by an isomorphism
when both are monomorphisms — and the projection is a monomorphism because
`Sch/S' ⥤ᵇ Sch/T` is full, being 2-isomorphic to a fully faithful composite.

## Main results

* `AlgebraicGeometry.isOpenSubstackInclusion_restrictι_inf`
* `AlgebraicGeometry.exists_opens_fiberEssImage`: the open subscheme an open substack cuts
  out of a scheme mapping to `𝒳`.
* `AlgebraicGeometry.exists_comp_eq_iff_range_subset`: factorization through an open
  immersion is detected by ranges.
* `CategoryTheory.BasedCategory.mono_of_overBased_map_full`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe v₂ u₂ v₃ u₃ u

namespace CategoryTheory.BasedCategory

variable {𝒮 : Type*} [Category 𝒮]

/-- If `𝒮/W ⥤ᵇ 𝒮/T` is full then `W ⟶ T` is a monomorphism. -/
lemma mono_of_overBased_map_full {W T : 𝒮} (f : W ⟶ T)
    [h : (overBased.map f).toFunctor.Full] : Mono f := by
  constructor
  intro V a b hab
  obtain ⟨ψ, hψ⟩ := h.map_surjective (X := Over.mk a) (Y := Over.mk (𝟙 W))
    (Over.homMk b (by
      show b ≫ ((𝟙 W) ≫ f) = a ≫ f
      simpa using hab.symm))
  have h1 : ψ.left ≫ (𝟙 W) = a := Over.w ψ
  have h2 : ψ.left = b := by
    have hc := congrArg Over.Hom.left hψ
    simpa [overBased.map] using hc
  rw [h2] at h1
  simpa using h1.symm

end CategoryTheory.BasedCategory

namespace AlgebraicGeometry

open CategoryTheory Limits CategoryTheory.BasedCategory CategoryTheory.BasedFunctor

/-- A morphism factors through an open immersion exactly when its range is contained in
the range of that open immersion. -/
lemma exists_comp_eq_iff_range_subset {T' T V : Scheme.{u}} (f : T' ⟶ T) [IsOpenImmersion f]
    (h : V ⟶ T) : (∃ k : V ⟶ T', k ≫ f = h) ↔ Set.range h.base ⊆ Set.range f.base := by
  constructor
  · rintro ⟨k, rfl⟩
    rintro y ⟨v, rfl⟩
    exact ⟨k.base v, by simp⟩
  · intro H
    exact ⟨IsOpenImmersion.lift f h H, IsOpenImmersion.lift_fac f h H⟩

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} {𝒰 : BasedCategory.{v₃, u₃} Scheme.{u}}

/-- **The open subscheme cut out by an open substack.** For an open substack inclusion
`i : 𝒰 ⥤ᵇ 𝒳` and a morphism `g : Sch/T ⥤ᵇ 𝒳` there is an open `W ⊆ T` such that an object
`X` of `Sch/T` has `g(X)` in the fiber-essential image of `i` exactly when the image of `X`
lies in `W`. -/
lemma exists_opens_fiberEssImage (i : 𝒰 ⥤ᵇ 𝒳) [hi : BasedFunctor.IsOpenSubstackInclusion i]
    (T : Scheme.{u}) (g : overBased T ⥤ᵇ 𝒳) :
    ∃ W : T.Opens, ∀ X : Over T,
      i.fiberEssImage (g.obj X) ↔ Set.range X.hom.base ⊆ (W : Set T) := by
  obtain ⟨T', E, hE⟩ := hi.relativelyRepresentableWith.1 T g
  haveI hoi : IsOpenImmersion ((E.comp (fiberProductSnd i g)).overHom) :=
    hi.relativelyRepresentableWith.2 T g T' E hE
  refine ⟨((E.comp (fiberProductSnd i g)).overHom).opensRange, fun X => ?_⟩
  rw [fiberEssImage_obj_iff_factors i g E hE X, exists_comp_eq_iff_range_subset _ X.hom]
  rfl

/-- Two morphisms into `T` that define the same factorization sieve and are both
monomorphisms differ by an isomorphism; so if one is an open immersion, so is the
other. -/
lemma isOpenImmersion_of_forall_exists_comp_eq_iff {S' T W : Scheme.{u}} (f' : S' ⟶ T)
    (j : W ⟶ T) [IsOpenImmersion j] [Mono f']
    (hsieve : ∀ (V : Scheme.{u}) (h' : V ⟶ T),
      (∃ k : V ⟶ S', k ≫ f' = h') ↔ ∃ k : V ⟶ W, k ≫ j = h') :
    IsOpenImmersion f' := by
  obtain ⟨k, hk⟩ := (hsieve W j).mpr ⟨𝟙 W, by simp⟩
  obtain ⟨k', hk'⟩ := (hsieve S' f').mp ⟨𝟙 S', by simp⟩
  have h1 : (k' ≫ k) ≫ f' = 𝟙 S' ≫ f' := by rw [Category.assoc, hk, hk']; simp
  have h2 : (k ≫ k') ≫ j = 𝟙 W ≫ j := by rw [Category.assoc, hk', hk]; simp
  have e1 : k' ≫ k = 𝟙 S' := (cancel_mono f').mp h1
  have e2 : k ≫ k' = 𝟙 W := (cancel_mono j).mp h2
  haveI : IsIso k' := ⟨k, e1, e2⟩
  rw [← hk']
  infer_instance

/-- **Criterion for a full sub-based-category to be an open substack.** If the object
property `Q` is fiber-closed and, for every morphism `g : Sch/T ⥤ᵇ 𝒳` from a scheme, the
objects of `Sch/T` whose image under `g` satisfies `Q` are exactly those whose structure
morphism factors through an open `W ⊆ T`, then `𝒳|_Q ⥤ᵇ 𝒳` is an open substack
inclusion. -/
theorem isOpenSubstackInclusion_restrictι (Q : ObjectProperty 𝒳.obj) (hQc : FiberClosed Q)
    (key : ∀ (T : Scheme.{u}) (g : overBased T ⥤ᵇ 𝒳), ∃ W : T.Opens, ∀ X : Over T,
      Q (g.obj X) ↔ Set.range X.hom.base ⊆ (W : Set T)) :
    BasedFunctor.IsOpenSubstackInclusion (𝒳.restrictι Q) where
  full := inferInstanceAs Q.ι.Full
  faithful := inferInstanceAs Q.ι.Faithful
  relativelyRepresentableWith := by
    have key' : ∀ (T : Scheme.{u}) (g : overBased T ⥤ᵇ 𝒳), ∃ W : T.Opens, ∀ X : Over T,
        Q (g.obj X) ↔ ∃ k : X.left ⟶ W.toScheme, k ≫ W.ι = X.hom := by
      intro T g
      obtain ⟨W, hW⟩ := key T g
      refine ⟨W, fun X => ?_⟩
      rw [exists_comp_eq_iff_range_subset _ X.hom, Scheme.Opens.range_ι]
      exact hW X
    refine ⟨fun T g => ?_, ?_⟩
    · obtain ⟨W, hW⟩ := key' T g
      exact ⟨W.toScheme, isRepresentedBy_fiberProduct_restrictι g Q hQc W.ι hW⟩
    · intro T g S' E hE
      obtain ⟨W, hW⟩ := key' T g
      haveI hri : (𝒳.restrictι Q).toFunctor.Faithful := inferInstanceAs Q.ι.Faithful
      haveI hri' : (𝒳.restrictι Q).toFunctor.Full := inferInstanceAs Q.ι.Full
      haveI hsf : (fiberProductSnd (𝒳.restrictι Q) g).toFunctor.Faithful :=
        fiberProductSnd_faithful (F := 𝒳.restrictι Q) (G := g)
      haveI hsF : (fiberProductSnd (𝒳.restrictι Q) g).toFunctor.Full :=
        fiberProductSnd_full (F := 𝒳.restrictι Q) (G := g)
      haveI := hE
      haveI hEfull : E.toFunctor.Full := inferInstance
      haveI hEfaith : E.toFunctor.Faithful := inferInstance
      haveI hcf : (E.toFunctor ⋙ (fiberProductSnd (𝒳.restrictι Q) g).toFunctor).Full :=
        Functor.Full.comp _ _
      obtain ⟨α⟩ := BasedFunctor.nonempty_iso_overBased_map
        (E.comp (fiberProductSnd (𝒳.restrictι Q) g))
      haveI hcf' : (E.comp (fiberProductSnd (𝒳.restrictι Q) g)).toFunctor.Full := hcf
      have β : (E.comp (fiberProductSnd (𝒳.restrictι Q) g)).toFunctor ≅
          (overBased.map
            (E.comp (fiberProductSnd (𝒳.restrictι Q) g)).overHom).toFunctor :=
        (BasedNatTrans.forgetful (overBased S') (overBased T)).mapIso α
      haveI hfull :
          (overBased.map (E.comp (fiberProductSnd (𝒳.restrictι Q) g)).overHom).toFunctor.Full :=
        Functor.Full.of_iso β
      haveI : Mono (E.comp (fiberProductSnd (𝒳.restrictι Q) g)).overHom :=
        mono_of_overBased_map_full _
      refine isOpenImmersion_of_forall_exists_comp_eq_iff _ W.ι (fun V h' => ?_)
      have hC := fiberEssImage_obj_iff_factors (𝒳.restrictι Q) g E hE (Over.mk h')
      rw [fiberEssImage_restrictι Q hQc] at hC
      exact hC.symm.trans (hW (Over.mk h'))

variable {𝒰₁ : BasedCategory.{v₃, u₃} Scheme.{u}} {𝒰₂ : BasedCategory.{v₃, u₃} Scheme.{u}}

/-- **The intersection of two open substacks is an open substack.** The witness is the
full sub-based-category of `𝒳` on the objects lying in both fiber-essential images, which
— unlike the fiber product `𝒰₁ ×_𝒳 𝒰₂` — stays in the universes of `𝒳`. -/
theorem isOpenSubstackInclusion_restrictι_inf (i₁ : 𝒰₁ ⥤ᵇ 𝒳) (i₂ : 𝒰₂ ⥤ᵇ 𝒳)
    [BasedFunctor.IsOpenSubstackInclusion i₁]
    [BasedFunctor.IsOpenSubstackInclusion i₂] :
    BasedFunctor.IsOpenSubstackInclusion
      (𝒳.restrictι (i₁.fiberEssImage ⊓ i₂.fiberEssImage)) :=
  isOpenSubstackInclusion_restrictι _
    ((fiberClosed_fiberEssImage i₁).inf (fiberClosed_fiberEssImage i₂))
    (fun T g => by
      obtain ⟨W₁, hW₁⟩ := exists_opens_fiberEssImage i₁ T g
      obtain ⟨W₂, hW₂⟩ := exists_opens_fiberEssImage i₂ T g
      refine ⟨W₁ ⊓ W₂, fun X => ⟨fun h => Set.subset_inter ((hW₁ X).mp h.1) ((hW₂ X).mp h.2),
        fun h => ⟨(hW₁ X).mpr (h.trans Set.inter_subset_left),
          (hW₂ X).mpr (h.trans Set.inter_subset_right)⟩⟩⟩)

variable {𝒴 : BasedCategory.{v₃, u₃} Scheme.{u}} {𝒱 : BasedCategory.{v₄, u₄} Scheme.{u}}

/-- **The preimage of an open substack is an open substack.** For a morphism of prestacks
`F : 𝒳 ⥤ᵇ 𝒴` and an open substack inclusion `j : 𝒱 ⥤ᵇ 𝒴`, the full sub-based-category of
`𝒳` on the objects whose image under `F` lies in the fiber-essential image of `j` is an open
substack of `𝒳`. -/
theorem isOpenSubstackInclusion_restrictι_comap (F : 𝒳 ⥤ᵇ 𝒴) (j : 𝒱 ⥤ᵇ 𝒴)
    [BasedFunctor.IsOpenSubstackInclusion j] :
    BasedFunctor.IsOpenSubstackInclusion
      (𝒳.restrictι (fun a => j.fiberEssImage (F.obj a))) := by
  refine isOpenSubstackInclusion_restrictι _ ?_
    (fun T g => exists_opens_fiberEssImage j T (g.comp F))
  intro a a' e he h
  refine BasedFunctor.fiberEssImage_of_iso h (F.mapIso e) ?_
  refine BasedCategory.isHomLift_id_codomain (F.mapIso e) ?_
  have h2 : Functor.IsHomLift 𝒴.p (𝟙 (𝒳.p.obj a)) (F.map e.hom) :=
    BasedFunctor.preserves_isHomLift F (𝟙 (𝒳.p.obj a)) e.hom
  have h3 : 𝒴.p.obj (F.obj a) = 𝒳.p.obj a := F.w_obj a
  rw [h3]
  exact h2

end AlgebraicGeometry
