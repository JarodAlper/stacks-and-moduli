module

public import StacksAndModuli.«Section2.2-Grassmannian».«part2.2.3-relative-grassmannians»
public import StacksAndModuli.API.ZariskiSieveBasis
public import StacksAndModuli.API.QuotFunctorZariskiDescent

/-!
# The subfunctor of objects that locally factor through a chart family

Let `X` be a scheme and `C : I → Over X` a family of objects over it — the *charts*.  This
file builds, once and for all, the subsingleton-valued presheaf

`AlgebraicGeometry.Scheme.factorsFunctor C`

whose value on `T : Over X` is the proposition that `T` factors through some chart Zariski
locally, and supplies two of the three inputs of
`AlgebraicGeometry.OverLocalRepresentability`: it is a Zariski sheaf, and the chart maps are
jointly locally surjective onto it.  Both are trivial once the functor is known to be
subsingleton-valued, so neither depends on anything about the charts.

This is the machinery behind the flattening stratification (`API/ModuleFlatteningCharts.lean`
for an affine base), factored out so that the general-base version costs only the third input
— the relative-open-immersion clause, which is the only place the geometry of the charts
enters.

Main declarations:

* `AlgebraicGeometry.Scheme.openCoverOfOpens`, `AlgebraicGeometry.Scheme.openCoverOfMaps` —
  the two `Scheme.OpenCover` constructors Mathlib does not provide;
* `AlgebraicGeometry.Scheme.LocallyFactors` and its stability lemmas;
* `AlgebraicGeometry.Scheme.factorsFunctor`, `…factorsFunctor_subsingleton`,
  `…isSheaf_factorsFunctor`, `…factorsSheaf`;
* `AlgebraicGeometry.Scheme.factorsChart` and `…factorsChart_isLocallySurjective`.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- The open cover of a scheme given by a family of opens covering every point. -/
def openCoverOfOpens {Y : Scheme.{u}} {ι : Type u} (U : ι → Y.Opens)
    (h : ∀ y : Y, ∃ i, y ∈ U i) : Y.OpenCover where
  I₀ := ι
  X i := (U i).toScheme
  f i := (U i).ι
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun y => ?_, inferInstance⟩
    obtain ⟨i, hi⟩ := h y
    exact ⟨i, ⟨y, hi⟩, rfl⟩

/-- The open cover of a scheme given by a jointly surjective family of open immersions. -/
def openCoverOfMaps {Y : Scheme.{u}} {ι : Type u} (X : ι → Scheme.{u}) (f : ∀ i, X i ⟶ Y)
    (hf : ∀ i, IsOpenImmersion (f i)) (h : ∀ y : Y, ∃ i z, (f i).base z = y) : Y.OpenCover where
  I₀ := ι
  X := X
  f := f
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    exact ⟨h, hf⟩

section ChartAtlas

variable {X : Scheme.{u}} {I : Type u} (C : I → Over X)

/-- `T` factors through the chart family Zariski locally: through every point of `T` there is
an open immersion `V ⟶ T` over `X` whose structure morphism factors through some chart. -/
def LocallyFactors (T : Over X) : Prop :=
  ∀ x : T.left, ∃ (V : Over X) (k : V ⟶ T),
    IsOpenImmersion k.left ∧ x ∈ Set.range k.left.base ∧
    ∃ (i : I) (h : V.left ⟶ (C i).left), h ≫ (C i).hom = V.hom

variable {C}

/-- A global factorization gives the local one. -/
lemma LocallyFactors.of_factors {T : Over X} (i : I) (h : T.left ⟶ (C i).left)
    (hh : h ≫ (C i).hom = T.hom) : LocallyFactors C T := by
  intro x
  refine ⟨T, 𝟙 T, ?_, ?_, i, h, hh⟩
  · change IsOpenImmersion (𝟙 T.left); infer_instance
  · exact ⟨x, rfl⟩

/-- The condition is stable under composition with an open immersion into a larger object. -/
lemma LocallyFactors.of_openImmersion {T V : Over X} (k : V ⟶ T)
    [IsOpenImmersion k.left] (hV : LocallyFactors C V)
    {x : T.left} (hx : x ∈ Set.range k.left.base) :
    ∃ (W : Over X) (j : W ⟶ T),
      IsOpenImmersion j.left ∧ x ∈ Set.range j.left.base ∧
      ∃ (i : I) (h : W.left ⟶ (C i).left), h ≫ (C i).hom = W.hom := by
  obtain ⟨v, rfl⟩ := hx
  obtain ⟨W, j, hj, hxW, i, h, hh⟩ := hV v
  refine ⟨W, j ≫ k, ?_, ?_, i, h, hh⟩
  · change IsOpenImmersion (j.left ≫ k.left)
    haveI := hj
    infer_instance
  · obtain ⟨w, hw⟩ := hxW
    refine ⟨w, ?_⟩
    show ((j ≫ k).left).base w = k.left.base v
    simp only [Over.comp_left, Scheme.Hom.comp_base]
    exact congrArg k.left.base hw

/-- The condition is stable under base change. -/
lemma LocallyFactors.comp {T T' : Over X} (φ : T' ⟶ T)
    (hT : LocallyFactors C T) : LocallyFactors C T' := by
  intro x'
  obtain ⟨V, k, hk, hx, i, h, hh⟩ := hT (φ.left.base x')
  haveI := hk
  set U : T'.left.Opens := φ.left ⁻¹ᵁ k.left.opensRange with hU
  have hx'U : x' ∈ U := hx
  have hrange : Set.range (U.ι ≫ φ.left).base ⊆ Set.range k.left.base := by
    rintro _ ⟨y, rfl⟩
    exact y.2
  have hl : IsOpenImmersion.lift k.left (U.ι ≫ φ.left) hrange ≫ k.left = U.ι ≫ φ.left :=
    IsOpenImmersion.lift_fac _ _ _
  refine ⟨Over.mk (U.ι ≫ T'.hom), Over.homMk U.ι rfl, ?_, ⟨⟨x', hx'U⟩, rfl⟩, i,
    IsOpenImmersion.lift k.left (U.ι ≫ φ.left) hrange ≫ h, ?_⟩
  · change IsOpenImmersion U.ι
    infer_instance
  · change (IsOpenImmersion.lift k.left (U.ι ≫ φ.left) hrange ≫ h) ≫ (C i).hom =
      U.ι ≫ T'.hom
    rw [Category.assoc, hh, ← Over.w k, ← Category.assoc, hl, Category.assoc, Over.w φ]

/-- **Descent along an open cover.**  The condition is local. -/
lemma LocallyFactors.of_cover {T : Over X} {ι : Type*}
    (V : ι → Over X) (k : ∀ i, V i ⟶ T)
    (hk : ∀ i, IsOpenImmersion (k i).left)
    (hcov : ∀ x : T.left, ∃ i, x ∈ Set.range (k i).left.base)
    (hV : ∀ i, LocallyFactors C (V i)) : LocallyFactors C T := by
  intro x
  obtain ⟨i, hi⟩ := hcov x
  haveI := hk i
  exact LocallyFactors.of_openImmersion (k i) (hV i) hi

variable (C)

/-- The subfunctor of objects factoring locally through the chart family. -/
def factorsFunctor : (Over X)ᵒᵖ ⥤ Type u where
  obj T := ULift.{u} (PLift (LocallyFactors C T.unop))
  map φ := ↾fun h => ⟨⟨LocallyFactors.comp φ.unop h.down.down⟩⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The chart map into the subfunctor. -/
def factorsChart (i : I) : uliftYoneda.{0}.obj (C i) ⟶ factorsFunctor C where
  app _W := ↾fun φ => ⟨⟨LocallyFactors.of_factors i φ.down.left (Over.w φ.down)⟩⟩
  naturality _ _ _ := rfl

/-- The subfunctor is subsingleton-valued. -/
lemma factorsFunctor_subsingleton (T : (Over X)ᵒᵖ) :
    Subsingleton ((factorsFunctor C).obj T) := by
  refine ⟨fun a b => ?_⟩
  have ha : a = (⟨⟨a.down.down⟩⟩ : ULift.{u} (PLift (LocallyFactors C T.unop))) := rfl
  have hb : b = (⟨⟨b.down.down⟩⟩ : ULift.{u} (PLift (LocallyFactors C T.unop))) := rfl
  rw [ha, hb]

/-- **The subfunctor is a Zariski sheaf.** -/
lemma isSheaf_factorsFunctor :
    Presheaf.IsSheaf (Scheme.zariskiTopology.over X) (factorsFunctor C) := by
  rw [CategoryTheory.isSheaf_iff_isSheaf_of_type]
  intro T Sv hSv x _hx
  rw [GrothendieckTopology.mem_over_iff] at hSv
  set 𝒰 := Scheme.zariskiOpenCoverOfSieve _ hSv with h𝒰
  have hmem : ∀ i, Sv (Scheme.openCoverMapOver T 𝒰 i) := by
    intro i
    have h1 : (Sieve.overEquiv T Sv).arrows (𝒰.f i) :=
      Scheme.zariskiOpenCoverOfSieve_le _ hSv (𝒰.X i) (𝒰.f i) (Presieve.ofArrows.mk i)
    exact (Sieve.overEquiv_iff Sv (𝒰.f i)).mp h1
  have hloc : LocallyFactors C T := by
    refine LocallyFactors.of_cover
      (fun i => Scheme.openCoverObjectOver T 𝒰 i)
      (fun i => Scheme.openCoverMapOver T 𝒰 i)
      (fun i => Scheme.openCoverMapOver_isOpenImmersion T 𝒰 i)
      (fun y => ⟨𝒰.idx y, 𝒰.covers y⟩) (fun i => ?_)
    exact (x _ (hmem i)).down.down
  haveI : ∀ (Y : (Over X)ᵒᵖ), Subsingleton ((factorsFunctor C).obj Y) :=
    factorsFunctor_subsingleton C
  exact ⟨⟨⟨hloc⟩⟩, fun Y f hf => Subsingleton.elim _ _, fun y _ => Subsingleton.elim _ _⟩

/-- The subfunctor as a Zariski sheaf on schemes over `X`. -/
def factorsSheaf : Sheaf (Scheme.zariskiTopology.over X) (Type u) :=
  ⟨factorsFunctor C, isSheaf_factorsFunctor C⟩

/-- **The charts are jointly locally surjective.**

A point of `factorsFunctor C` over `T` is, by definition, a pointwise factorization of `T`
through charts; the open immersions witnessing it *are* a Zariski cover of `T`, and over each
member the factorization is a point of the corresponding chart.  Since the functor is
subsingleton-valued, no compatibility has to be checked. -/
instance factorsChart_isLocallySurjective :
    Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over X)
      (Sigma.desc (f := fun i : I => uliftYoneda.{0}.obj (C i)) (factorsChart C)) where
  imageSieve_mem {T} s := by
    have hT : LocallyFactors C T := s.down.down
    choose V k hk hx i h hh using hT
    let 𝒰 : Scheme.OpenCover.{u} T.left :=
      Scheme.openCoverOfMaps (fun x => (V x).left) (fun x => (k x).left) hk
        (fun y => ⟨y, (hx y).choose, (hx y).choose_spec⟩)
    refine (Scheme.zariskiTopology.over X).superset_covering ?_
      (Scheme.Modules.QuotientOpenDescent.openCoverMapOver_mem_zariskiTopology T 𝒰)
    rw [Sieve.generate_le_iff]
    rintro W j ⟨x⟩
    haveI := factorsFunctor_subsingleton C (op (Scheme.openCoverObjectOver T 𝒰 x))
    refine ⟨(Sigma.ι (fun i : I => uliftYoneda.{0}.obj (C i)) (i x)).app
        (op (Scheme.openCoverObjectOver T 𝒰 x))
        (ULift.up (Over.homMk (h x) ?_)), Subsingleton.elim _ _⟩
    change h x ≫ (C (i x)).hom = (k x).left ≫ T.hom
    rw [hh x, Over.w (k x)]

end ChartAtlas

end AlgebraicGeometry.Scheme
