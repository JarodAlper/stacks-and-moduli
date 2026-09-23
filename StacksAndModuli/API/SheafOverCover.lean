module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.PseudofunctorSheafOver
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# Pullback along a cover detects isomorphisms of sheaves on an over-site

For a morphism `f : X ⟶ S` which generates a covering sieve, the counit maps
`T ×_S X ⟶ T` generate covering sieves on the over-site.  Consequently, pullback along
`f` detects isomorphisms between sheaves of types on that over-site.

This is reusable infrastructure for descent arguments which first construct a comparison
morphism globally and then verify that it is an isomorphism after pulling back to a cover.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe w v u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable (J : GrothendieckTopology C) {X S : C} (f : X ⟶ S)

set_option backward.defeqAttrib.useBackward true in
/-- If `f : X ⟶ S` generates a covering sieve, then for every `T ⟶ S` the counit
`T ×_S X ⟶ T` of the pullback/postcomposition adjunction generates a covering sieve on
the over-site of `S`. -/
theorem cover_generate_singleton_mapPullbackAdj_counit
    (hf : Sieve.generate (Presieve.singleton f) ∈ J S) (T : Over S) :
    Sieve.generate (Presieve.singleton ((Over.mapPullbackAdj f).counit.app T)) ∈
      (J.over S) T := by
  rw [J.mem_over_iff, Sieve.overEquiv_generate]
  apply J.superset_covering _ (J.pullback_stable T.hom hf)
  intro Z g hg
  rw [Sieve.pullback_apply] at hg
  obtain ⟨W, h, _, ⟨⟩, eq⟩ := hg
  refine ⟨Limits.pullback T.hom f, pullback.lift g h eq.symm,
    ((Over.mapPullbackAdj f).counit.app T).left, ?_, ?_⟩
  · change Presieve.functorPushforward (Over.forget S)
      (Presieve.singleton ((Over.mapPullbackAdj f).counit.app T))
        ((Over.forget S).map ((Over.mapPullbackAdj f).counit.app T))
    apply Presieve.image_mem_functorPushforward (Over.forget S)
    exact Presieve.singleton.mk
  · simpa using pullback.lift_fst g h eq.symm

/-- Pullback along `f` detects isomorphisms of sheaves of types on the over-site, provided
the base-changed counit morphism generates a covering sieve over every object. -/
theorem isIso_of_isIso_overMapPullback
    (hcover : ∀ T : Over S,
      Sieve.generate (Presieve.singleton ((Over.mapPullbackAdj f).counit.app T)) ∈
        (J.over S) T)
    {F G : Sheaf (J.over S) (Type w)} (a : F ⟶ G)
    [IsIso ((J.overMapPullback (Type w) f).map a)] : IsIso a := by
  apply (Sheaf.isLocallyBijective_iff_isIso (J := J.over S) (A := Type w) a).mp
  constructor
  · constructor
    intro T x y hxy
    apply (J.over S).superset_covering _ (hcover T.unop)
    rw [Sieve.generate_le_iff]
    rintro U _ ⟨⟩
    let q := (Over.mapPullbackAdj f).counit.app T.unop
    change F.obj.map q.op x = F.obj.map q.op y
    let a' := ((J.overMapPullback (Type w) f).map a).hom.app
      (op ((Over.pullback f).obj T.unop))
    have ha' : Function.Bijective a' :=
      (CategoryTheory.bijective_iff_isIso_ofHom a').mpr inferInstance
    apply ha'.injective
    change a.hom.app _ (F.obj.map q.op x) = a.hom.app _ (F.obj.map q.op y)
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
    simpa using congrArg (G.obj.map q.op) hxy
  · constructor
    intro T y
    apply (J.over S).superset_covering _ (hcover T)
    rw [Sieve.generate_le_iff]
    rintro U _ ⟨⟩
    let q := (Over.mapPullbackAdj f).counit.app T
    let a' := ((J.overMapPullback (Type w) f).map a).hom.app
      (op ((Over.pullback f).obj T))
    have ha' : Function.Bijective a' :=
      (CategoryTheory.bijective_iff_isIso_ofHom a').mpr inferInstance
    obtain ⟨x', hx'⟩ := ha'.surjective (G.obj.map q.op y)
    exact ⟨x', hx'⟩

/-- If `f` generates a covering sieve, pullback along `f` detects isomorphisms between
sheaves of types on the over-site of its target. -/
theorem isIso_of_isIso_overMapPullback_of_generate_singleton_mem
    (hf : Sieve.generate (Presieve.singleton f) ∈ J S)
    {F G : Sheaf (J.over S) (Type w)} (a : F ⟶ G)
    [IsIso ((J.overMapPullback (Type w) f).map a)] : IsIso a := by
  apply J.isIso_of_isIso_overMapPullback f
  exact J.cover_generate_singleton_mapPullbackAdj_counit f hf

end CategoryTheory.GrothendieckTopology
