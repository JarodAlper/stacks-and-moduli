module

public import StacksAndModuli.API.ModuleFlatteningFunctor
public import StacksAndModuli.«Section2.2-Grassmannian».«part2.2.3-relative-grassmannians»
public import StacksAndModuli.API.ZariskiSieveBasis
public import StacksAndModuli.API.QuotFunctorZariskiDescent
public import StacksAndModuli.API.ChartAtlasFunctor

/-!
# The affine flattening charts, indexed

`API/ModuleFlatteningFunctor.lean` introduces the flattening-stratum functor
`Module.flatRankFunctor` and the chart map out of one affine stratum.  This file indexes the
charts so that they can be fed to `AlgebraicGeometry.OverLocalRepresentability`, whose input is
a family `g : (i : I) → uliftYoneda.{w}.obj (X i) ⟶ G.1` over a *type* `I`.

`Module.FlatRankIndex R M r` is that type: a base element `f : R` together with `r` generators
of `M` after inverting `f`.  Note it lives in `Type u` only because `M` is taken in `Type u`
here — the affine stratification of `API/ModuleFlatteningStratum.lean` allows `M : Type v`, but
the gluing machinery does not.

`AlgebraicGeometry.Scheme.openCoverOfOpens` and `…openCoverOfMaps` (in
`API/ChartAtlasFunctor.lean`) are the missing constructors of a `Scheme.OpenCover`; they are
what turn `Module.LocallyFlatRank`'s pointwise data into a cover.

Main declarations:

* `Module.FlatRankIndex`, `Module.flatRankChartObj`, `Module.flatRankChartMap`;
* `Module.flatRankFunctor_subsingleton`;
* `Module.isSheaf_flatRankFunctor` and `Module.flatRankSheaf`;
* `Module.flatRankChartMap_isLocallySurjective`.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Module

variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (r : ℕ)

/-- Index type of the affine flattening charts: a base element `f` together with `r`
generators of `M` after inverting it. -/
def FlatRankIndex : Type u :=
  Σ _f : R, Σ _g : Fin r → M, PLift (∀ m : M, _f • m ∈ Submodule.span R (Set.range _g))

variable {R M r}

/-- The chart family indexed by `FlatRankIndex`. -/
noncomputable def flatRankChartObj (i : FlatRankIndex R M r) :
    Over (Spec (CommRingCat.of R)) :=
  Over.mk (Module.freeRankStratumι i.2.1 i.1)

/-- The chart maps into the flattening functor. -/
noncomputable def flatRankChartMap (i : FlatRankIndex R M r) :
    uliftYoneda.{0}.obj (flatRankChartObj i) ⟶ flatRankFunctor R M r :=
  flatRankChart i.2.1 i.1 i.2.2.down

/-- The flattening functor is subsingleton-valued. -/
lemma flatRankFunctor_subsingleton (T : (Over (Spec (CommRingCat.of R)))ᵒᵖ) :
    Subsingleton ((flatRankFunctor R M r).obj T) := by
  refine ⟨fun a b => ?_⟩
  have ha : a = (⟨⟨a.down.down⟩⟩ :
    ULift.{u} (PLift (LocallyFlatRank R M r T.unop))) := rfl
  have hb : b = (⟨⟨b.down.down⟩⟩ :
    ULift.{u} (PLift (LocallyFlatRank R M r T.unop))) := rfl
  rw [ha, hb]

/-- **The flattening-stratum presheaf is a Zariski sheaf.** -/
lemma isSheaf_flatRankFunctor :
    Presheaf.IsSheaf (Scheme.zariskiTopology.over (Spec (CommRingCat.of R)))
      (flatRankFunctor R M r) := by
  rw [CategoryTheory.isSheaf_iff_isSheaf_of_type]
  intro T Sv hSv x _hx
  rw [GrothendieckTopology.mem_over_iff] at hSv
  set 𝒰 := Scheme.zariskiOpenCoverOfSieve _ hSv with h𝒰
  have hmem : ∀ i, Sv (Scheme.openCoverMapOver T 𝒰 i) := by
    intro i
    have h1 : (Sieve.overEquiv T Sv).arrows (𝒰.f i) :=
      Scheme.zariskiOpenCoverOfSieve_le _ hSv (𝒰.X i) (𝒰.f i) (Presieve.ofArrows.mk i)
    exact (Sieve.overEquiv_iff Sv (𝒰.f i)).mp h1
  have hloc : LocallyFlatRank R M r T := by
    refine LocallyFlatRank.of_cover
      (fun i => Scheme.openCoverObjectOver T 𝒰 i)
      (fun i => Scheme.openCoverMapOver T 𝒰 i)
      (fun i => Scheme.openCoverMapOver_isOpenImmersion T 𝒰 i)
      (fun y => ⟨𝒰.idx y, 𝒰.covers y⟩) (fun i => ?_)
    exact (x _ (hmem i)).down.down
  haveI : ∀ (Y : (Over (Spec (CommRingCat.of R)))ᵒᵖ),
      Subsingleton ((flatRankFunctor R M r).obj Y) := flatRankFunctor_subsingleton
  exact ⟨⟨⟨hloc⟩⟩, fun Y f hf => Subsingleton.elim _ _, fun y _ => Subsingleton.elim _ _⟩

/-- The flattening stratum as a Zariski sheaf on schemes over `Spec R`. -/
def flatRankSheaf (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
    (r : ℕ) : Sheaf (Scheme.zariskiTopology.over (Spec (CommRingCat.of R))) (Type u) :=
  ⟨flatRankFunctor R M r, isSheaf_flatRankFunctor⟩

/-- **The affine flattening charts are jointly locally surjective.**

A point of `flatRankFunctor R M r` over `T` is, by definition, a pointwise factorization of
`T` through affine flattening strata; the open immersions witnessing it *are* a Zariski cover
of `T`, and over each member the factorization is exactly a point of the corresponding chart.
Since the functor is subsingleton-valued, no compatibility has to be checked. -/
instance flatRankChartMap_isLocallySurjective :
    Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over (Spec (CommRingCat.of R)))
      (Sigma.desc (f := fun i : FlatRankIndex R M r =>
        uliftYoneda.{0}.obj (flatRankChartObj i)) flatRankChartMap) where
  imageSieve_mem {T} s := by
    have hT : LocallyFlatRank R M r T := s.down.down
    choose V k hk hx f g hg h hh using hT
    let 𝒰 : Scheme.OpenCover.{u} T.left :=
      Scheme.openCoverOfMaps (fun x => (V x).left) (fun x => (k x).left) hk
        (fun y => ⟨y, (hx y).choose, (hx y).choose_spec⟩)
    refine (Scheme.zariskiTopology.over (Spec (CommRingCat.of R))).superset_covering ?_
      (Scheme.Modules.QuotientOpenDescent.openCoverMapOver_mem_zariskiTopology T 𝒰)
    rw [Sieve.generate_le_iff]
    rintro W j ⟨x⟩
    haveI := flatRankFunctor_subsingleton (R := R) (M := M) (r := r)
      (op (Scheme.openCoverObjectOver T 𝒰 x))
    refine ⟨(Sigma.ι (fun i : FlatRankIndex R M r =>
      uliftYoneda.{0}.obj (flatRankChartObj i)) ⟨f x, g x, PLift.up (hg x)⟩).app
        (op (Scheme.openCoverObjectOver T 𝒰 x))
        (ULift.up (Over.homMk (h x) ?_)), Subsingleton.elim _ _⟩
    change h x ≫ Module.freeRankStratumι (g x) (f x) = (k x).left ≫ T.hom
    rw [hh x, Over.w (k x)]

end Module
