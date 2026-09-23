module

public import StacksAndModuli.API.RepresentableSheafProperty
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Overlap isomorphisms for represented sheaves

This file records the categorical part of singleton descent for sheaves on over-sites.
An isomorphism between a locally represented sheaf and the pullback of a global sheaf
induces the canonical isomorphism between the two pullbacks of its representative to
the kernel pair.  It also records that a sheaf represented by a monomorphism is
subterminal.  The geometric descent arguments for open and closed subschemes use these
facts without unfolding the pseudofunctor of sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable (J : GrothendieckTopology C) [J.Subcanonical]

/-- Pullback commutes with the Yoneda embedding on an over-site. -/
noncomputable def overMapPullbackYonedaIso {X Y : C} (f : X ⟶ Y)
    (Z : Over Y) :
    (J.over X).yoneda.obj ((Over.pullback f).obj Z) ≅
      (J.overMapPullback (Type v) f).obj ((J.over Y).yoneda.obj Z) :=
  (fullyFaithfulSheafToPresheaf (J.over X) (Type v)).preimageIso
    ((Over.mapPullbackAdj f).compYonedaIso.app Z)

/-- The two iterated pullbacks of a sheaf along the kernel pair of a morphism are
canonically isomorphic. -/
noncomputable def overMapPullbackKernelPairIso {X S : C} (f : X ⟶ S)
    (F : Sheaf (J.over S) (Type v)) :
    (J.overMapPullback (Type v) (pullback.fst f f)).obj
        ((J.overMapPullback (Type v) f).obj F) ≅
      (J.overMapPullback (Type v) (pullback.snd f f)).obj
        ((J.overMapPullback (Type v) f).obj F) :=
  (J.overMapPullbackComp (Type v) (pullback.fst f f) f).app F ≪≫
    (J.overMapPullbackCongr (Type v) (pullback.condition :
      pullback.fst f f ≫ f = pullback.snd f f ≫ f)).app F ≪≫
    (J.overMapPullbackComp (Type v) (pullback.snd f f) f).symm.app F

/-- If a pullback of a sheaf is represented by `Z`, the canonical comparison of the
two iterated pullbacks gives an isomorphism between the two pullbacks of `Z` to the
kernel pair. -/
noncomputable def representedKernelPairIso {X S : C} (f : X ⟶ S)
    (F : Sheaf (J.over S) (Type v)) (Z : Over X)
    (e : CategoryTheory.yoneda.obj Z ≅
      ((J.overMapPullback (Type v) f).obj F).obj) :
    (Over.pullback (pullback.fst f f)).obj Z ≅
      (Over.pullback (pullback.snd f f)).obj Z := by
  let eS : (J.over X).yoneda.obj Z ≅
      (J.overMapPullback (Type v) f).obj F :=
    (fullyFaithfulSheafToPresheaf (J.over X) (Type v)).preimageIso e
  let ePB :
      (J.over (Limits.pullback f f)).yoneda.obj
          ((Over.pullback (pullback.fst f f)).obj Z) ≅
        (J.over (Limits.pullback f f)).yoneda.obj
          ((Over.pullback (pullback.snd f f)).obj Z) :=
    J.overMapPullbackYonedaIso (pullback.fst f f) Z ≪≫
      (J.overMapPullback (Type v) (pullback.fst f f)).mapIso eS ≪≫
      J.overMapPullbackKernelPairIso f F ≪≫
      (J.overMapPullback (Type v) (pullback.snd f f)).mapIso eS.symm ≪≫
      (J.overMapPullbackYonedaIso (pullback.snd f f) Z).symm
  exact Yoneda.fullyFaithful.preimageIso
    ((sheafToPresheaf (J.over (Limits.pullback f f)) (Type v)).mapIso ePB)

/-- A sheaf represented by a monomorphism in an over-category is subterminal. -/
lemma subsingleton_hom_of_representedBy_mono {X : C}
    (M G : Sheaf (J.over X) (Type v)) (Z : Over X) [Mono Z.hom]
    (e : CategoryTheory.yoneda.obj Z ≅ G.obj) :
    Subsingleton (M ⟶ G) := by
  constructor
  intro a b
  apply (sheafToPresheaf (J.over X) (Type v)).map_injective
  apply NatTrans.ext
  funext T
  apply ConcreteCategory.hom_ext
  intro x
  apply (show Function.Injective (e.inv.app T) from
    (CategoryTheory.bijective_iff_isIso_ofHom (e.inv.app T)).mpr inferInstance |>.1)
  apply Over.OverMorphism.ext
  apply (cancel_mono Z.hom).mp
  rw [Over.w, Over.w]

/-- Every further pullback of a sheaf represented by a monomorphism is subterminal. -/
lemma subsingleton_hom_to_pullback_of_representedBy_mono
    {X S Y : C} (f : X ⟶ S) (g : Y ⟶ X)
    (F : Sheaf (J.over S) (Type v)) (Z : Over X) [Mono Z.hom]
    (e : CategoryTheory.yoneda.obj Z ≅
      ((J.overMapPullback (Type v) f).obj F).obj)
    (M : Sheaf (J.over Y) (Type v)) :
    Subsingleton
      (M ⟶ (J.overMapPullback (Type v) g).obj
        ((J.overMapPullback (Type v) f).obj F)) := by
  let eS : (J.over X).yoneda.obj Z ≅
      (J.overMapPullback (Type v) f).obj F :=
    (fullyFaithfulSheafToPresheaf (J.over X) (Type v)).preimageIso e
  let eTargetS : (J.over Y).yoneda.obj ((Over.pullback g).obj Z) ≅
      (J.overMapPullback (Type v) g).obj
        ((J.overMapPullback (Type v) f).obj F) :=
    J.overMapPullbackYonedaIso g Z ≪≫
      (J.overMapPullback (Type v) g).mapIso eS
  let eTarget : CategoryTheory.yoneda.obj ((Over.pullback g).obj Z) ≅
      ((J.overMapPullback (Type v) g).obj
        ((J.overMapPullback (Type v) f).obj F)).obj :=
    (sheafToPresheaf (J.over Y) (Type v)).mapIso eTargetS
  letI : Mono ((Over.pullback g).obj Z).hom := by
    change Mono (pullback.snd Z.hom g)
    infer_instance
  exact J.subsingleton_hom_of_representedBy_mono M _
    ((Over.pullback g).obj Z) eTarget

end CategoryTheory.GrothendieckTopology

namespace AlgebraicGeometry.Scheme

open CategoryTheory CategoryTheory.Limits

/-- Two open immersions into the same scheme with the same image are isomorphic in the
over-category. -/
noncomputable def openOverIsoOfOpensRangeEq {X : Scheme.{u}} {Z W : Over X}
    [IsOpenImmersion Z.hom] [IsOpenImmersion W.hom]
    (h : Z.hom.opensRange = W.hom.opensRange) : Z ≅ W :=
  Over.isoMk
    (Z.hom.isoOpensRange ≪≫ X.isoOfEq h ≪≫ W.hom.isoOpensRange.symm) (by
      simp)

/-- If a sheaf pulled back along `f` is represented by an open subscheme, the open is
saturated for the kernel pair of `f`. -/
lemma representedOpenKernelPairEq
    (J : GrothendieckTopology Scheme.{u}) [J.Subcanonical]
    {X S : Scheme.{u}} (f : X ⟶ S)
    (F : Sheaf (J.over S) (Type u)) (Z : Over X)
    (e : CategoryTheory.yoneda.obj Z ≅
      ((J.overMapPullback (Type u) f).obj F).obj)
    [IsOpenImmersion Z.hom] :
    pullback.fst f f ⁻¹ᵁ Z.hom.opensRange =
      pullback.snd f f ⁻¹ᵁ Z.hom.opensRange := by
  rw [← Scheme.Hom.opensRange_pullbackSnd,
    ← Scheme.Hom.opensRange_pullbackSnd]
  let α := J.representedKernelPairIso f F Z e
  letI : IsIso α.hom.left := by
    change IsIso ((Over.forget (pullback f f)).map α.hom)
    infer_instance
  letI : IsOpenImmersion α.hom.left := by infer_instance
  have hw := α.hom.w
  change α.hom.left ≫ pullback.snd Z.hom (pullback.snd f f) =
    pullback.snd Z.hom (pullback.fst f f) at hw
  apply TopologicalSpace.Opens.ext
  change Set.range (pullback.snd Z.hom (pullback.fst f f)).base =
    Set.range (pullback.snd Z.hom (pullback.snd f f)).base
  have hs : Set.range α.hom.left.base = Set.univ :=
    Set.range_eq_univ.mpr α.hom.left.homeomorph.surjective
  rw [← hw, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hs,
    Set.image_univ]

end AlgebraicGeometry.Scheme
