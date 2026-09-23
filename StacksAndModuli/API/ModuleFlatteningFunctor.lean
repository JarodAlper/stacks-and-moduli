module

public import StacksAndModuli.API.ModuleFlatteningStratum

/-!
# The flattening stratum as a functor

`API/ModuleFlatteningStratum.lean` builds, for a finite module `M` over `R` and a rank `r`, the
affine stratum `Module.freeRankStratum g f` with its immersion into `Spec R` and the
factorization property `Module.flat_and_rankAtStalk_iff_exists_freeRankStratumLift` on affine
test objects.  Assembling those into a single stratification means representing a *functor*, and
this file introduces it.

`Module.LocallyFlatRank R M r T` says that through every point of `T : Over (Spec R)` there is
an **open immersion** `V ⟶ T` over `Spec R` whose structure morphism factors through one of the
affine strata.  Two design points, both load-bearing:

* the condition is stated *locally* — the naive "factors through some stratum" is not a Zariski
  sheaf, because different opens of `T` may need different `f`;
* locality is expressed with open immersions `V ⟶ T` rather than opens `U ⊆ T`.  With opens,
  descent along a cover needs the `''ᵁ` image bookkeeping; with open immersions it is
  *composition* of open immersions, and `LocallyFlatRank.of_cover` is four lines.  The price is
  that base change (`LocallyFlatRank.comp`) goes through
  `AlgebraicGeometry.IsOpenImmersion.lift` instead of `Scheme.Hom.resLE`, which is no worse.

The intended continuation, recorded in `PLAN-hilbert-quot.md`, is: upgrade `flatRankFunctor` to
a `Sheaf` for `Scheme.zariskiTopology.over (Spec R)` (`of_cover` is the content), prove the
chart maps jointly locally surjective and relatively representable by **open** immersions — over
`flatRankFunctor` the flatness and rank conditions are automatic and only `IsUnit (φ f)` is
left — and glue with `AlgebraicGeometry.OverLocalRepresentability.representableBy`.

Main declarations:

* `Module.LocallyFlatRank`, with `of_factors`, `of_openImmersion`, `comp` and `of_cover`;
* `Module.flatRankFunctor` and `Module.flatRankChart`.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u v

open CategoryTheory AlgebraicGeometry

namespace Module

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (r : ℕ)

/-- `T` lies in the rank-`r` flattening stratum: through every point of `T` there is an open
immersion `V ⟶ T` over `Spec R` whose structure morphism factors through one of the affine
strata `Module.freeRankStratum`. -/
def LocallyFlatRank (T : Over (Spec (CommRingCat.of R))) : Prop :=
  ∀ x : T.left, ∃ (V : Over (Spec (CommRingCat.of R))) (k : V ⟶ T),
    IsOpenImmersion k.left ∧ x ∈ Set.range k.left.base ∧
    ∃ (f : R) (g : Fin r → M)
      (_hg : ∀ m : M, f • m ∈ Submodule.span R (Set.range g))
      (h : V.left ⟶ Module.freeRankStratum g f),
      h ≫ Module.freeRankStratumι g f = V.hom

variable {R M r}

/-- A global factorization gives the local one. -/
lemma LocallyFlatRank.of_factors {T : Over (Spec (CommRingCat.of R))} (f : R) (g : Fin r → M)
    (hg : ∀ m : M, f • m ∈ Submodule.span R (Set.range g))
    (h : T.left ⟶ Module.freeRankStratum g f)
    (hh : h ≫ Module.freeRankStratumι g f = T.hom) : LocallyFlatRank R M r T := by
  intro x
  refine ⟨T, 𝟙 T, ?_, ?_, f, g, hg, h, hh⟩
  · change IsOpenImmersion (𝟙 T.left); infer_instance
  · exact ⟨x, rfl⟩

/-- The condition is stable under composition with an open immersion into a larger object. -/
lemma LocallyFlatRank.of_openImmersion {T V : Over (Spec (CommRingCat.of R))} (k : V ⟶ T)
    [IsOpenImmersion k.left] (hV : LocallyFlatRank R M r V)
    {x : T.left} (hx : x ∈ Set.range k.left.base) :
    ∃ (W : Over (Spec (CommRingCat.of R))) (j : W ⟶ T),
      IsOpenImmersion j.left ∧ x ∈ Set.range j.left.base ∧
      ∃ (f : R) (g : Fin r → M)
        (_hg : ∀ m : M, f • m ∈ Submodule.span R (Set.range g))
        (h : W.left ⟶ Module.freeRankStratum g f),
        h ≫ Module.freeRankStratumι g f = W.hom := by
  obtain ⟨v, rfl⟩ := hx
  obtain ⟨W, j, hj, hxW, f, g, hg, h, hh⟩ := hV v
  refine ⟨W, j ≫ k, ?_, ?_, f, g, hg, h, hh⟩
  · change IsOpenImmersion (j.left ≫ k.left)
    haveI := hj
    infer_instance
  · obtain ⟨w, hw⟩ := hxW
    refine ⟨w, ?_⟩
    show ((j ≫ k).left).base w = k.left.base v
    simp only [Over.comp_left, Scheme.Hom.comp_base]
    exact congrArg k.left.base hw

/-- The flattening-stratum condition is stable under base change. -/
lemma LocallyFlatRank.comp {T T' : Over (Spec (CommRingCat.of R))} (φ : T' ⟶ T)
    (hT : LocallyFlatRank R M r T) : LocallyFlatRank R M r T' := by
  intro x'
  obtain ⟨V, k, hk, hx, f, g, hg, h, hh⟩ := hT (φ.left.base x')
  haveI := hk
  set U : T'.left.Opens := φ.left ⁻¹ᵁ k.left.opensRange with hU
  have hx'U : x' ∈ U := hx
  have hrange : Set.range (U.ι ≫ φ.left).base ⊆ Set.range k.left.base := by
    rintro _ ⟨y, rfl⟩
    exact y.2
  have hl : IsOpenImmersion.lift k.left (U.ι ≫ φ.left) hrange ≫ k.left = U.ι ≫ φ.left :=
    IsOpenImmersion.lift_fac _ _ _
  refine ⟨Over.mk (U.ι ≫ T'.hom), Over.homMk U.ι rfl, ?_, ⟨⟨x', hx'U⟩, rfl⟩, f, g, hg,
    IsOpenImmersion.lift k.left (U.ι ≫ φ.left) hrange ≫ h, ?_⟩
  · change IsOpenImmersion U.ι
    infer_instance
  · change (IsOpenImmersion.lift k.left (U.ι ≫ φ.left) hrange ≫ h) ≫
      Module.freeRankStratumι g f = U.ι ≫ T'.hom
    rw [Category.assoc, hh, ← Over.w k, ← Category.assoc, hl, Category.assoc, Over.w φ]

/-- **Descent along an open cover.**  The flattening-stratum condition is local. -/
lemma LocallyFlatRank.of_cover {T : Over (Spec (CommRingCat.of R))} {ι : Type*}
    (V : ι → Over (Spec (CommRingCat.of R))) (k : ∀ i, V i ⟶ T)
    (hk : ∀ i, IsOpenImmersion (k i).left)
    (hcov : ∀ x : T.left, ∃ i, x ∈ Set.range (k i).left.base)
    (hV : ∀ i, LocallyFlatRank R M r (V i)) : LocallyFlatRank R M r T := by
  intro x
  obtain ⟨i, hi⟩ := hcov x
  haveI := hk i
  exact LocallyFlatRank.of_openImmersion (k i) (hV i) hi

variable (R M r)

/-- The rank-`r` flattening stratum, as a subsingleton-valued presheaf on schemes over
`Spec R`. -/
def flatRankFunctor : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type u where
  obj T := ULift.{u} (PLift (LocallyFlatRank R M r T.unop))
  map φ := ↾fun h => ⟨⟨LocallyFlatRank.comp φ.unop h.down.down⟩⟩
  map_id _ := rfl
  map_comp _ _ := rfl

variable {R M r}

/-- The chart map from an affine stratum into the flattening-stratum functor. -/
def flatRankChart (g : Fin r → M) (f : R)
    (hg : ∀ m : M, f • m ∈ Submodule.span R (Set.range g)) :
    uliftYoneda.{0}.obj (Over.mk (Module.freeRankStratumι g f)) ⟶ flatRankFunctor R M r where
  app _W := ↾fun φ => ⟨⟨LocallyFlatRank.of_factors f g hg φ.down.left (Over.w φ.down)⟩⟩
  naturality _ _ _ := rfl

end Module
