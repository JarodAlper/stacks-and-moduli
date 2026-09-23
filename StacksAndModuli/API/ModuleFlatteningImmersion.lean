module

public import StacksAndModuli.API.ModuleFlatteningOpenChart

/-!
# The flattening stratum is an immersion

`API/ModuleFlatteningOpenChart.lean` represents the flattening functor by a scheme
`Module.flatRankRepresentative R M r` over `Spec R` whose structure morphism is a
monomorphism.  This file upgrades that to an **immersion**, which is the form in which the
flattening stratification enters the Grassmannian step of §2.4: a natural transformation
whose fibres are flattening strata is then relatively representable by immersions.

Being an immersion is *not* local on the source, so it does not follow from the charts
`Module.freeRankStratumι` being immersions — glue the closed point of `Spec k[x]` to `D(x)`
for a monomorphism that is locally an immersion and is not one.  The argument instead
factors the structure morphism through the open locus

`Module.flatRankOpen = ⋃_f D(f)`

covered by the charts, and shows that `S_r ⟶ flatRankOpen` is a **closed** immersion, a
property that *is* local at the target.  The local input is
`Module.isPullback_chartOverMap`: over `D(f)` the stratum *is* the chart, which is the
universal property of `Module.exists_chartRestrictLift` read as a pullback square.

Main declarations:

* `CategoryTheory.IsPullback.of_comp_mono` — cancelling a monomorphism out of the cospan;
* `Module.chartOverMap` and `Module.isPullback_chartOverMap`;
* `Module.flatRankOpen`, `Module.flatRankLift` and its `IsClosedImmersion` instance;
* `Module.flatRankRepresentative_hom_isImmersion`;
* `AlgebraicGeometry.relative_over_isImmersion_map` and
  `AlgebraicGeometry.relative_over_isImmersion_of_iso` — the interface in which §2.4 consumes
  such a result: a morphism of presheaves over `S` induced by an immersion of representing
  objects is relatively representable by immersions.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

/-- A square whose cospan is postcomposed with a monomorphism is a pullback square as soon as
the postcomposed square is. -/
theorem CategoryTheory.IsPullback.of_comp_mono {C : Type u} [Category.{v} C] {P X Y Z W : C}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (m : Z ⟶ W) [Mono m]
    (h : IsPullback fst snd (f ≫ m) (g ≫ m)) : IsPullback fst snd f g := by
  have hw : fst ≫ f = snd ≫ g := by
    rw [← cancel_mono m, Category.assoc, Category.assoc]; exact h.w
  refine IsPullback.of_isLimit (PullbackCone.isLimitAux (PullbackCone.mk _ _ hw)
    (fun s => h.lift s.fst s.snd (by
      rw [← Category.assoc, ← Category.assoc, s.condition]))
    (fun s => h.lift_fst _ _ _) (fun s => h.lift_snd _ _ _) (fun s m' hm => ?_))
  have h1 := hm WalkingCospan.left
  have h2 := hm WalkingCospan.right
  change m' ≫ fst = s.fst at h1
  change m' ≫ snd = s.snd at h2
  exact h.hom_ext (by rw [h.lift_fst, h1]) (by rw [h.lift_snd, h2])

namespace AlgebraicGeometry

/-- An immersion in `Over S` is stable under base change. -/
instance overIsImmersion_isStableUnderBaseChange (S : Scheme.{u}) :
    (MorphismProperty.over (@IsImmersion : MorphismProperty Scheme.{u})
      (X := S)).IsStableUnderBaseChange := by
  constructor
  intro A B A' B' f g f' g' h hg
  have h' : IsPullback ((Over.forget S).map f') ((Over.forget S).map g')
      ((Over.forget S).map g) ((Over.forget S).map f) := h.map (Over.forget S)
  exact (IsImmersion.isStableUnderBaseChange).of_isPullback h' hg

/-- **A morphism of representable presheaves over `S` induced by an immersion is relatively
representable by immersions.** -/
theorem relative_over_isImmersion_map {S : Scheme.{u}} {Z T : Over S} (j : Z ⟶ T)
    (hj : IsImmersion j.left) :
    MorphismProperty.relative uliftYoneda.{v}
      (MorphismProperty.over (@IsImmersion : MorphismProperty Scheme.{u}))
      (uliftYoneda.map j) :=
  MorphismProperty.relative_map hj

/-- The previous statement transported along isomorphisms of presheaves: this is the shape in
which §2.4 consumes a relatively representable immersion (see
`AlgebraicGeometry.Scheme.exists_representableBy_isHQuasiProjective_of_relative_immersion`). -/
theorem relative_over_isImmersion_of_iso {S : Scheme.{u}}
    {F G : (Over S)ᵒᵖ ⥤ Type (max u v)} (α : F ⟶ G)
    {Z T : Over S} (eF : uliftYoneda.{v}.obj Z ≅ F) (eG : uliftYoneda.{v}.obj T ≅ G)
    (j : Z ⟶ T) (hj : IsImmersion j.left)
    (hcomm : eF.hom ≫ α = uliftYoneda.map j ≫ eG.hom) :
    MorphismProperty.relative uliftYoneda.{v}
      (MorphismProperty.over (@IsImmersion : MorphismProperty Scheme.{u})) α :=
  (MorphismProperty.arrow_mk_iso_iff _ (Arrow.isoMk eF eG hcomm)).mp
    (relative_over_isImmersion_map j hj)

end AlgebraicGeometry

namespace Module

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M] {r : ℕ}

section Chart

/-- The chart carries the tautological point of the flattening functor. -/
lemma chartLocallyFlatRank (i : FlatRankIndex R M r) :
    LocallyFlatRank R M r (flatRankChartObj i) :=
  LocallyFlatRank.of_factors i.1 i.2.1 i.2.2.down (𝟙 _) (Category.id_comp _)

/-- The chart, as an object over the flattening stratum. -/
def chartOverMap (i : FlatRankIndex R M r) :
    flatRankChartObj i ⟶ flatRankRepresentative R M r :=
  (flatRankRepresentableBy R M r).homEquiv.symm ⟨⟨chartLocallyFlatRank i⟩⟩

lemma chartOverMap_w (i : FlatRankIndex R M r) :
    (chartOverMap i).left ≫ (flatRankRepresentative R M r).hom =
      freeRankStratumι i.2.1 i.1 :=
  Over.w (chartOverMap i)

/-- A test scheme over the stratum whose structure map factors through `D(f)` factors through
the chart of `f`. -/
lemma exists_chartLift (i : FlatRankIndex R M r) {Z : Scheme.{u}}
    (a : Z ⟶ (flatRankRepresentative R M r).left)
    (b : Z ⟶ Spec (CommRingCat.of (Localization.Away i.1)))
    (hab : a ≫ (flatRankRepresentative R M r).hom = b ≫ awayIncl i.1) :
    ∃ c : Z ⟶ freeRankStratum i.2.1 i.1,
      c ≫ freeRankStratumι i.2.1 i.1 = a ≫ (flatRankRepresentative R M r).hom := by
  let T : Over (Spec (CommRingCat.of R)) :=
    Over.mk (a ≫ (flatRankRepresentative R M r).hom)
  have hT : LocallyFlatRank R M r T :=
    ((flatRankRepresentableBy R M r).homEquiv
      (Over.homMk a rfl : T ⟶ flatRankRepresentative R M r)).down.down
  obtain ⟨kk, hkk⟩ := exists_chartRestrictLift (g := i.2.1) (f := i.1) i.2.2.down hT
  refine ⟨(pullback.lift (𝟙 Z) b (by rw [Category.id_comp]; exact hab) :
    Z ⟶ chartRestrict i.1 T) ≫ kk, ?_⟩
  rw [Category.assoc, hkk, ← Category.assoc]
  change (pullback.lift (𝟙 Z) b _ ≫ pullback.fst _ _) ≫ T.hom = _
  rw [pullback.lift_fst, Category.id_comp]
  rfl

/-- **The chart is exactly the part of the flattening stratum lying over `D(f)`.** -/
theorem isPullback_chartOverMap (i : FlatRankIndex R M r) :
    IsPullback ((chartOverMap i).left) (freeRankLocusι (awayPresentation i.2.1 i.1))
      (flatRankRepresentative R M r).hom (awayIncl i.1) := by
  haveI : Mono (flatRankRepresentative R M r).hom := inferInstance
  haveI : Mono (awayIncl i.1) := inferInstance
  haveI : Mono (freeRankStratumι i.2.1 i.1) := inferInstance
  have hw : (chartOverMap i).left ≫ (flatRankRepresentative R M r).hom =
      freeRankLocusι (awayPresentation i.2.1 i.1) ≫ awayIncl i.1 := by
    rw [chartOverMap_w, freeRankStratumι_eq]
  have key : ∀ s : PullbackCone (flatRankRepresentative R M r).hom (awayIncl i.1),
      ∃ c : s.pt ⟶ freeRankStratum i.2.1 i.1,
        c ≫ freeRankStratumι i.2.1 i.1 = s.fst ≫ (flatRankRepresentative R M r).hom :=
    fun s => exists_chartLift i s.fst s.snd s.condition
  refine IsPullback.of_isLimit (PullbackCone.isLimitAux (PullbackCone.mk _ _ hw)
    (fun s => (key s).choose) (fun s => ?_) (fun s => ?_) (fun s m hm => ?_))
  · rw [← cancel_mono (flatRankRepresentative R M r).hom]
    change (key s).choose ≫ (chartOverMap i).left ≫
      (flatRankRepresentative R M r).hom = _
    rw [chartOverMap_w, (key s).choose_spec]
  · rw [← cancel_mono (awayIncl i.1)]
    change ((key s).choose ≫ freeRankLocusι (awayPresentation i.2.1 i.1)) ≫ awayIncl i.1 = _
    rw [Category.assoc, ← freeRankStratumι_eq, (key s).choose_spec, s.condition]
  · rw [← cancel_mono (freeRankStratumι i.2.1 i.1), (key s).choose_spec,
      freeRankStratumι_eq, ← Category.assoc]
    have h2 := hm WalkingCospan.right
    change m ≫ freeRankLocusι (awayPresentation i.2.1 i.1) = s.snd at h2
    rw [h2, ← s.condition]

end Chart

section Immersion

variable (R M r)

/-- The relative-open-immersion witness of the flattening charts, named for reuse. -/
theorem flatRankChartsOpen (i : FlatRankIndex R M r) :
    (AlgebraicGeometry.Scheme.isOpenImmersionOver (Spec (CommRingCat.of R))).relative
      uliftYoneda.{0} (flatRankChartMap i) :=
  flatRankChartMap_relative_isOpenImmersion i

/-- **The open locus of `Spec R` covered by the flattening charts** — the locus where `M`
needs at most `r` generators. -/
def flatRankOpen : (Spec (CommRingCat.of R)).Opens :=
  ⨆ i : FlatRankIndex R M r, (awayIncl i.1).opensRange

variable {R M r}

lemma awayIncl_range_subset (i : FlatRankIndex R M r) :
    Set.range (awayIncl i.1).base ⊆ (flatRankOpen R M r : Set (Spec (CommRingCat.of R))) :=
  le_iSup (fun j : FlatRankIndex R M r => (awayIncl j.1).opensRange) i

lemma range_flatRankRepresentative_hom_subset :
    Set.range (flatRankRepresentative R M r).hom.base ⊆
      (flatRankOpen R M r : Set (Spec (CommRingCat.of R))) := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨i, y, hy⟩ :=
    (Scheme.OverLocalRepresentability.glueData (flatRankChartsOpen R M r)).openCover.exists_eq x
  have hcomp := Scheme.OverLocalRepresentability.toGlued_comp_gluedHom
    (flatRankChartsOpen R M r) i
  refine awayIncl_range_subset i ⟨(freeRankLocusι (awayPresentation i.2.1 i.1)).base y, ?_⟩
  change ((freeRankLocusι (awayPresentation i.2.1 i.1)) ≫ awayIncl i.1).base y = _
  rw [← freeRankStratumι_eq]
  change (((flatRankChartObj i).hom)).base y = _
  rw [← hcomp, ← hy]
  rfl

variable (R M r)

/-- The flattening stratum, as a scheme over the open locus it maps into. -/
def flatRankLift : (flatRankRepresentative R M r).left ⟶ (flatRankOpen R M r).toScheme :=
  IsOpenImmersion.lift (flatRankOpen R M r).ι (flatRankRepresentative R M r).hom
    (by rw [Scheme.Opens.range_ι]; exact range_flatRankRepresentative_hom_subset)

lemma flatRankLift_ι : flatRankLift R M r ≫ (flatRankOpen R M r).ι =
    (flatRankRepresentative R M r).hom := IsOpenImmersion.lift_fac _ _ _

/-- The chart `D(f)`, as a scheme over the open locus. -/
def flatRankChartToOpen (i : FlatRankIndex R M r) :
    Spec (CommRingCat.of (Localization.Away i.1)) ⟶ (flatRankOpen R M r).toScheme :=
  IsOpenImmersion.lift (flatRankOpen R M r).ι (awayIncl i.1)
    (by rw [Scheme.Opens.range_ι]; exact awayIncl_range_subset i)

lemma flatRankChartToOpen_ι (i : FlatRankIndex R M r) :
    flatRankChartToOpen R M r i ≫ (flatRankOpen R M r).ι = awayIncl i.1 :=
  IsOpenImmersion.lift_fac _ _ _

instance flatRankChartToOpen_isOpenImmersion (i : FlatRankIndex R M r) :
    IsOpenImmersion (flatRankChartToOpen R M r i) := by
  haveI : IsOpenImmersion (flatRankChartToOpen R M r i ≫ (flatRankOpen R M r).ι) := by
    rw [flatRankChartToOpen_ι]; infer_instance
  exact IsOpenImmersion.of_comp _ (flatRankOpen R M r).ι

/-- The charts cover the open locus. -/
def flatRankOpenCover : Scheme.OpenCover.{u} (flatRankOpen R M r).toScheme :=
  Scheme.openCoverOfMaps
    (fun i : FlatRankIndex R M r => Spec (CommRingCat.of (Localization.Away i.1)))
    (flatRankChartToOpen R M r) (fun i => inferInstance) (by
      intro y
      have hy : ∃ i : FlatRankIndex R M r,
          ((flatRankOpen R M r).ι).base y ∈ (awayIncl i.1).opensRange := by
        rw [← TopologicalSpace.Opens.mem_iSup]; exact y.2
      obtain ⟨i, z, hz⟩ := hy
      refine ⟨i, z, ?_⟩
      apply ((flatRankOpen R M r).ι.isOpenEmbedding).injective
      rw [← Scheme.Hom.comp_apply, flatRankChartToOpen_ι]
      exact hz)

/-- **The flattening stratum is a closed subscheme of the open locus.**  Closedness is local
at the target, and over each chart `D(f)` the stratum is the chart. -/
instance flatRankLift_isClosedImmersion : IsClosedImmersion (flatRankLift R M r) := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion)
    (flatRankOpenCover R M r)]
  intro i
  have hsq : IsPullback ((chartOverMap i).left) (freeRankLocusι (awayPresentation i.2.1 i.1))
      (flatRankLift R M r) (flatRankChartToOpen R M r i) := by
    refine IsPullback.of_comp_mono (flatRankOpen R M r).ι ?_
    rw [flatRankLift_ι, flatRankChartToOpen_ι]
    exact isPullback_chartOverMap i
  have hcan := IsPullback.of_hasPullback (flatRankLift R M r) (flatRankChartToOpen R M r i)
  have e : Arrow.mk (pullback.snd (flatRankLift R M r) (flatRankChartToOpen R M r i)) ≅
      Arrow.mk (freeRankLocusι (awayPresentation i.2.1 i.1)) :=
    Arrow.isoMk (hcan.isoIsPullback _ _ hsq) (Iso.refl _) (by simp)
  change IsClosedImmersion (pullback.snd (flatRankLift R M r) (flatRankChartToOpen R M r i))
  exact (MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion) e).mpr inferInstance

/-- **The flattening stratum is an immersion into the base.**  This is the form the
flattening stratification takes in the Grassmannian step of §2.4. -/
theorem flatRankRepresentative_hom_isImmersion :
    IsImmersion (flatRankRepresentative R M r).hom := by
  rw [IsImmersion.isImmersion_iff_exists]
  exact ⟨_, flatRankLift R M r, (flatRankOpen R M r).ι, inferInstance, inferInstance,
    flatRankLift_ι R M r⟩

end Immersion

end Module
