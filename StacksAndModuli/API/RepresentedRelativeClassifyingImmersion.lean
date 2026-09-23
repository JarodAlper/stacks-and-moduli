module

public import StacksAndModuli.API.RepresentableByTransport
public import StacksAndModuli.API.FreeGrassmannianImmersion

/-!
# The morphism between representatives induced by a relative transformation

A relatively representable immersion `F ⟶ G` induces an immersion between any chosen
representatives of `F` and `G`.  This file records the construction together with the
identity saying that the induced morphism classifies the image of the universal point.

Main declarations:

* `AlgebraicGeometry.representedRelativeClassifyingHom`;
* `AlgebraicGeometry.representedRelativeClassifyingHom_isImmersion`;
* `AlgebraicGeometry.representedRelativeClassifyingHom_homEquiv`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace AlgebraicGeometry

variable {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type (u + 1)}

/-- Postcomposing a relatively representable immersion with the inverse of a natural
isomorphism preserves relative representability by immersions. -/
theorem relative_over_isImmersion_comp_iso_inv
    {G' : (Over S)ᵒᵖ ⥤ Type (u + 1)} (α : F ⟶ G) (e : G' ≅ G)
    (hα : MorphismProperty.relative uliftYoneda.{u + 1}
      (MorphismProperty.over (@IsImmersion : MorphismProperty Scheme.{u})) α) :
    MorphismProperty.relative uliftYoneda.{u + 1}
      (MorphismProperty.over (@IsImmersion : MorphismProperty Scheme.{u}))
      (α ≫ e.inv) := by
  let a : Arrow ((Over S)ᵒᵖ ⥤ Type (u + 1)) := Arrow.mk α
  let b : Arrow ((Over S)ᵒᵖ ⥤ Type (u + 1)) := Arrow.mk (α ≫ e.inv)
  let i : a ≅ b := Arrow.isoMk (Iso.refl F) e.symm (by simp [a, b])
  exact (MorphismProperty.arrow_mk_iso_iff _ i).mp hα

/-- The morphism between chosen representatives induced by a relatively representable
natural transformation.  We first use the canonical pullback representative supplied by
relative representability, and then transport from the caller's representative by the
canonical classifying isomorphism. -/
noncomputable def representedRelativeClassifyingHom
    (hα : MorphismProperty.relative uliftYoneda.{u + 1}
      (MorphismProperty.over (@IsImmersion : MorphismProperty Scheme.{u}))
      (α : F ⟶ G)) {Q P : Over S} (eF : F.RepresentableBy Q)
    (eG : G.RepresentableBy P) : Q ⟶ P := by
  let eG' : uliftYoneda.{u + 1}.obj P ≅ G :=
    (Functor.RepresentableBy.equivUliftYonedaIso G P) eG
  let Q₀ : Over S := hα.rep.pullback eG'.hom
  let j : Q₀ ⟶ P := hα.rep.snd eG'.hom
  have hfst : IsIso (hα.rep.fst eG'.hom) :=
    (hα.rep.isPullback eG'.hom).isIso_fst_of_isIso
  let eF' : uliftYoneda.{u + 1}.obj Q₀ ≅ F :=
    @asIso _ _ _ _ (hα.rep.fst eG'.hom) hfst
  let eF₀ : F.RepresentableBy Q₀ :=
    (Functor.RepresentableBy.equivUliftYonedaIso F Q₀).symm eF'
  exact (eF.classifyingIso eF₀).hom ≫ j

/-- The morphism induced between representatives by a relatively representable
immersion is an immersion. -/
theorem representedRelativeClassifyingHom_isImmersion
    (α : F ⟶ G)
    (hα : MorphismProperty.relative uliftYoneda.{u + 1}
      (MorphismProperty.over (@IsImmersion : MorphismProperty Scheme.{u})) α)
    {Q P : Over S} (eF : F.RepresentableBy Q) (eG : G.RepresentableBy P) :
    IsImmersion (representedRelativeClassifyingHom hα eF eG).left := by
  let eG' : uliftYoneda.{u + 1}.obj P ≅ G :=
    (Functor.RepresentableBy.equivUliftYonedaIso G P) eG
  let Q₀ : Over S := hα.rep.pullback eG'.hom
  let j : Q₀ ⟶ P := hα.rep.snd eG'.hom
  have hfst : IsIso (hα.rep.fst eG'.hom) :=
    (hα.rep.isPullback eG'.hom).isIso_fst_of_isIso
  let eF' : uliftYoneda.{u + 1}.obj Q₀ ≅ F :=
    @asIso _ _ _ _ (hα.rep.fst eG'.hom) hfst
  let eF₀ : F.RepresentableBy Q₀ :=
    (Functor.RepresentableBy.equivUliftYonedaIso F Q₀).symm eF'
  let i : Q ≅ Q₀ := eF.classifyingIso eF₀
  have hi : IsImmersion i.hom.left := by infer_instance
  have hj : IsImmersion j.left := hα.property_snd eG'.hom
  change IsImmersion (i.hom.left ≫ j.left)
  exact MorphismProperty.IsStableUnderComposition.comp_mem _ _ hi hj

/-- The induced morphism classifies the image under `α` of the universal `F`-point. -/
theorem representedRelativeClassifyingHom_homEquiv
    (α : F ⟶ G)
    (hα : MorphismProperty.relative uliftYoneda.{u + 1}
      (MorphismProperty.over (@IsImmersion : MorphismProperty Scheme.{u})) α)
    {Q P : Over S} (eF : F.RepresentableBy Q) (eG : G.RepresentableBy P) :
    eG.homEquiv (representedRelativeClassifyingHom hα eF eG) =
      α.app (op Q) (eF.homEquiv (𝟙 Q)) := by
  let eG' : uliftYoneda.{u + 1}.obj P ≅ G :=
    (Functor.RepresentableBy.equivUliftYonedaIso G P) eG
  let Q₀ : Over S := hα.rep.pullback eG'.hom
  let j : Q₀ ⟶ P := hα.rep.snd eG'.hom
  have hfst : IsIso (hα.rep.fst eG'.hom) :=
    (hα.rep.isPullback eG'.hom).isIso_fst_of_isIso
  let eF' : uliftYoneda.{u + 1}.obj Q₀ ≅ F :=
    @asIso _ _ _ _ (hα.rep.fst eG'.hom) hfst
  let eF₀ : F.RepresentableBy Q₀ :=
    (Functor.RepresentableBy.equivUliftYonedaIso F Q₀).symm eF'
  let i : Q ≅ Q₀ := eF.classifyingIso eF₀
  have hi : eF₀.homEquiv i.hom = eF.homEquiv (𝟙 Q) := by
    simpa only [i, Functor.RepresentableBy.classifyingIso_hom,
      Category.id_comp] using eF.homEquiv_comp_classifyingHom eF₀ (𝟙 Q)
  have hsq := hα.rep.w eG'.hom
  let zi : (uliftYoneda.{u + 1}.obj Q₀).obj (op Q) :=
    Equiv.ulift.symm i.hom
  have happ := congrArg (fun k ↦ k.app (op Q) zi) hsq
  change eG.homEquiv (i.hom ≫ j) = α.app (op Q) (eF.homEquiv (𝟙 Q))
  rw [← hi]
  have hulift : Equiv.ulift (ULift.up (i.hom ≫ j)) = i.hom ≫ j := by
    rfl
  have h := happ.symm
  simp only [Functor.RepresentableBy.equivUliftYonedaIso_apply, yoneda_obj_obj,
    equivEquivIso_hom, NatTrans.comp_app, uliftYoneda_map_app,
    NatIso.ofComponents_hom_app, comp_apply, TypeCat.hom_ofHom,
    Equiv.ulift_symm_apply, TypeCat.Fun.coe_mk, Equiv.toIso_hom_hom_apply,
    Equiv.trans_apply, eG', zi] at h
  rw [hulift] at h
  exact h

end AlgebraicGeometry

end

end
