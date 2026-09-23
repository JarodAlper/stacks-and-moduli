module

public import StacksAndModuli.API.ModuleFlatteningCharts
public import StacksAndModuli.API.OpenCoverMonoLift

/-!
# The flattening charts are relatively representable open immersions

`API/ModuleFlatteningCharts.lean` produces the affine flattening charts
`Module.flatRankChartMap` and shows they are jointly Zariski-locally surjective onto the
flattening functor `Module.flatRankFunctor`.  This file supplies the other input of
`AlgebraicGeometry.OverLocalRepresentability`: each chart map is *relatively representable
by open immersions*.

The stratum `Module.freeRankStratum g f` is only an immersion into `Spec R` — a closed
subscheme of the basic open `D(f)` — so the chart is not an open subscheme of the base.  But
relative representability is measured **over `flatRankFunctor`**, and a test object `T`
mapping to `flatRankFunctor` already carries the flatness and rank conditions, Zariski
locally.  Over such a `T` the only remaining condition is that `f` be invertible, which is
the *open* subscheme `T ×_{Spec R} D(f)`.  Concretely, the fibre product of a chart with `T`
over the functor is the open part `Module.chartRestrict`, and the projection to the chart is
the canonical lift `Module.exists_chartRestrictLift`, glued from the affine universal
property `Module.flat_and_rankAtStalk_iff_exists_freeRankStratumLift`.

Main declarations:

* `AlgebraicGeometry.Scheme.exists_lift_of_openCover` — lifting along a monomorphism is local
  on the source;
* `Module.chartRestrict`, `Module.exists_chartRestrictLift` and the converse
  `Module.locallyFlatRank_of_flat_of_rankAtStalk`;
* `Module.flatRankChartMap_relative_isOpenImmersion`;
* `Module.flatRankRepresentative`, `Module.flatRankRepresentableBy` and
  `Module.flatRankRepresentative_mono` — the flattening stratum `S_r` as a subscheme of
  `Spec R`.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TensorProduct

namespace Module

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M] {r : ℕ}

/-- **Changing chart on an affine test object.**  Over an affine scheme mapping to *some*
flattening stratum, the module is flat of rank `r`, so the test object factors through any
other stratum whose base element has become invertible. -/
theorem exists_freeRankStratumLift_of_lift
    {g g' : Fin r → M} {f f' : R}
    (hg : ∀ m : M, f • m ∈ Submodule.span R (Set.range g))
    (hg' : ∀ m : M, f' • m ∈ Submodule.span R (Set.range g'))
    (B : Type u) [CommRing B] (φ : R →+* B) (hunit : IsUnit (φ f))
    (hx : ∃ k : Spec (.of B) ⟶ freeRankStratum g' f',
      k ≫ freeRankStratumι g' f' = Spec.map (CommRingCat.ofHom φ)) :
    ∃ k : Spec (.of B) ⟶ freeRankStratum g f,
      k ≫ freeRankStratumι g f = Spec.map (CommRingCat.ofHom φ) := by
  obtain ⟨-, hflat, hrank⟩ :=
    (flat_and_rankAtStalk_iff_exists_freeRankStratumLift hg' B φ).mpr hx
  exact (flat_and_rankAtStalk_iff_exists_freeRankStratumLift hg B φ).mp ⟨hunit, hflat, hrank⟩

section ChartRestrict

variable (g : Fin r → M) (f : R)

/-- The open immersion `D(f) ↪ Spec R`. -/
def awayIncl : Spec (CommRingCat.of (Localization.Away f)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))

instance : IsOpenImmersion (awayIncl f) := by
  unfold awayIncl; infer_instance

/-- The stratum immersion factors through `D(f)` by construction. -/
lemma freeRankStratumι_eq :
    freeRankStratumι g f = freeRankLocusι (awayPresentation g f) ≫ awayIncl f := rfl

variable (T : Over (Spec (CommRingCat.of R)))

/-- **The part of `T` lying over the chart `D(f)`.**  This is the fibre product of a chart
with `T` over the flattening functor. -/
def chartRestrict : Scheme.{u} := pullback T.hom (awayIncl f)

/-- The open immersion of the restricted part into `T`. -/
def chartRestrictι : chartRestrict f T ⟶ T.left := pullback.fst _ _

instance : IsOpenImmersion (chartRestrictι f T) := by
  unfold chartRestrictι; infer_instance

/-- The restricted part maps to `D(f)`. -/
def chartRestrictAway :
    chartRestrict f T ⟶ Spec (CommRingCat.of (Localization.Away f)) := pullback.snd _ _

lemma chartRestrict_condition :
    chartRestrictι f T ≫ T.hom = chartRestrictAway f T ≫ awayIncl f :=
  pullback.condition

variable {g f T}

/-- **The affine-local lift into a chart stratum.**  Every point of the restricted part has an
affine open neighbourhood which factors through the stratum of the chart `(g, f)`: it factors
through *some* stratum by `Module.LocallyFlatRank`, hence is flat of rank `r`, and `f` is
invertible on it because it lies over `D(f)`. -/
theorem exists_affine_freeRankStratumLift
    (hg : ∀ m : M, f • m ∈ Submodule.span R (Set.range g))
    (hT : LocallyFlatRank R M r T) (w : chartRestrict f T) :
    ∃ (B : CommRingCat.{u}) (b : Spec B ⟶ chartRestrict f T), IsOpenImmersion b ∧
      w ∈ Set.range b.base ∧
      ∃ kk : Spec B ⟶ freeRankStratum g f,
        kk ≫ freeRankStratumι g f = b ≫ chartRestrictι f T ≫ T.hom := by
  choose V k hk hx f' g' hg' h hh using hT
  set p₁ := chartRestrictι f T with hp₁
  set x := p₁.base w with hxdef
  have hmem : w ∈ p₁ ⁻¹ᵁ ((k x).left).opensRange := hx x
  obtain ⟨B, b, hb, hwmem, hsub⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset hmem
  letI := hb
  have hsub' : Set.range (b ≫ p₁).base ⊆ Set.range ((k x).left).base := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    rintro _ ⟨y, ⟨z, rfl⟩, rfl⟩
    exact hsub ⟨z, rfl⟩
  let q : Spec B ⟶ (V x).left := IsOpenImmersion.lift ((k x).left) (b ≫ p₁) hsub'
  have hq : q ≫ (k x).left = b ≫ p₁ := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨χ, hχ⟩ := Spec.map_surjective (b ≫ p₁ ≫ T.hom)
  obtain ⟨α, hα⟩ := Spec.map_surjective (b ≫ chartRestrictAway f T)
  have hχα : χ = CommRingCat.ofHom (algebraMap R (Localization.Away f)) ≫ α := by
    apply Spec.map_injective
    rw [hχ, Spec.map_comp, hα]
    simp only [Category.assoc, hp₁, chartRestrict_condition f T, awayIncl]
  have hunit : IsUnit (χ.hom f) := by
    rw [hχα]
    change IsUnit (α.hom (algebraMap R (Localization.Away f) f))
    exact (IsLocalization.Away.algebraMap_isUnit f).map α.hom
  refine ⟨B, b, hb, hwmem, ?_⟩
  have hlift : ∃ kk : Spec (.of ↥B) ⟶ freeRankStratum (g' x) (f' x),
      kk ≫ freeRankStratumι (g' x) (f' x) = Spec.map (CommRingCat.ofHom χ.hom) := by
    refine ⟨q ≫ h x, ?_⟩
    rw [Category.assoc, hh x, ← Over.w (k x), ← Category.assoc, hq, Category.assoc]
    rw [show CommRingCat.ofHom χ.hom = χ from rfl, hχ]
  obtain ⟨kk, hkk⟩ :=
    exists_freeRankStratumLift_of_lift hg (hg' x) ↥B χ.hom hunit hlift
  exact ⟨kk, by rw [hkk, show CommRingCat.ofHom χ.hom = χ from rfl, hχ]⟩

/-- **The canonical lift of the restricted part into the chart stratum.**  Glued from the
affine lifts of `Module.exists_affine_freeRankStratumLift`; the local lifts agree because the
stratum immersion is a monomorphism. -/
theorem exists_chartRestrictLift
    (hg : ∀ m : M, f • m ∈ Submodule.span R (Set.range g))
    (hT : LocallyFlatRank R M r T) :
    ∃ kk : chartRestrict f T ⟶ freeRankStratum g f,
      kk ≫ freeRankStratumι g f = chartRestrictι f T ≫ T.hom := by
  choose B b hb hwmem kk hkk using exists_affine_freeRankStratumLift hg hT
  let 𝒰 : Scheme.OpenCover.{u} (chartRestrict f T) :=
    Scheme.openCoverOfMaps (fun w => Spec (B w)) b hb
      (fun w => ⟨w, (hwmem w).choose, (hwmem w).choose_spec⟩)
  exact Scheme.exists_lift_of_openCover _ _ 𝒰 (fun w => ⟨kk w, hkk w⟩)

/-- **Flat of rank `r` implies locally in the flattening stratum.**  The converse direction of
the affine universal property, in the form the *general-base* flattening stratification needs:
a test ring on which `M` becomes flat of constant rank `r` factors, Zariski locally, through
the strata.

The locus is reached through `Module.map_genByIdeal_eq_top_of_flat_of_rankAtStalk`: flatness
already forces the test object into the open where `M` needs at most `r` generators, so some
`f ∈ Module.genBySet R M r` is invertible at each point. -/
theorem locallyFlatRank_of_flat_of_rankAtStalk [Module.Finite R M]
    (B : Type u) [CommRing B] [Algebra R B] [Module.Flat B (B ⊗[R] M)]
    (hrank : ∀ q : PrimeSpectrum B, Module.rankAtStalk (B ⊗[R] M) q = r) :
    LocallyFlatRank R M r (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B)))) := by
  intro x
  have htop : (genByIdeal R M r).map (algebraMap R B) = ⊤ :=
    map_genByIdeal_eq_top_of_flat_of_rankAtStalk B hrank
  obtain ⟨f, hf, hfx⟩ : ∃ f ∈ genBySet R M r, algebraMap R B f ∉ x.asIdeal := by
    by_contra hcon
    push Not at hcon
    have hle : (genByIdeal R M r).map (algebraMap R B) ≤ x.asIdeal := by
      rw [genByIdeal, Ideal.map_span]
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨y, hy, rfl⟩
      exact hcon y hy
    rw [htop] at hle
    exact x.2.1 (Ideal.eq_top_iff_one _ |>.mpr (hle Submodule.mem_top))
  obtain ⟨g, hg⟩ := (mem_genBySet_iff (R := R) (M := M) (r := r)).mp hf
  set b : B := algebraMap R B f with hb
  have htower : (algebraMap R (Localization.Away b)) =
      (algebraMap B (Localization.Away b)).comp (algebraMap R B) :=
    IsScalarTower.algebraMap_eq R B (Localization.Away b)
  have hlift : ∃ k : Spec (.of (Localization.Away b)) ⟶ freeRankStratum g f,
      k ≫ freeRankStratumι g f =
        Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away b))) := by
    refine (flat_and_rankAtStalk_iff_exists_freeRankStratumLift' hg
      (Localization.Away b)).mp ⟨?_, ?_, ?_⟩
    · rw [htower]
      exact IsLocalization.Away.algebraMap_isUnit b
    · exact Module.Flat.of_linearEquiv
        (AlgebraTensorModule.cancelBaseChange R B (Localization.Away b)
          (Localization.Away b) M).symm
    · intro q
      rw [← Module.rankAtStalk_eq_of_equiv
        (AlgebraTensorModule.cancelBaseChange R B (Localization.Away b)
          (Localization.Away b) M), Module.rankAtStalk_baseChange]
      exact hrank _
  obtain ⟨k, hk⟩ := hlift
  refine ⟨Over.mk (awayIncl b ≫ Spec.map (CommRingCat.ofHom (algebraMap R B))),
    Over.homMk (awayIncl b) rfl, inferInstanceAs (IsOpenImmersion (awayIncl b)),
    ?_, f, g, hg, k, ?_⟩
  · have hbase : ⇑(awayIncl b).base =
      (PrimeSpectrum.comap (algebraMap B (Localization.Away b))) := rfl
    change x ∈ Set.range ⇑(awayIncl b).base
    rw [hbase, PrimeSpectrum.localization_away_comap_range (Localization.Away b) b]
    exact hfx
  · rw [hk, htower, awayIncl]
    change Spec.map (CommRingCat.ofHom (algebraMap R B) ≫
      CommRingCat.ofHom (algebraMap B (Localization.Away b))) = _
    rw [Spec.map_comp]
    rfl

end ChartRestrict

section Representable

/-- **Each flattening chart is a relatively representable open subfunctor.**

Over a test object carrying a point of `Module.flatRankFunctor`, the fibre product with the
chart of index `i` is the open part `Module.chartRestrict` lying over `D(f)`: the projection
to the chart is `Module.exists_chartRestrictLift`, and no compatibility has to be checked
because the flattening functor is subsingleton-valued. -/
theorem flatRankChartMap_relative_isOpenImmersion {R : Type u} [CommRing R] {M : Type u}
    [AddCommGroup M] [Module R M] {r : ℕ} (i : FlatRankIndex R M r) :
    (AlgebraicGeometry.Scheme.isOpenImmersionOver (Spec (CommRingCat.of R))).relative
      uliftYoneda.{0} (flatRankChartMap i) := by
  haveI hss : ∀ (Y : (Over (Spec (CommRingCat.of R)))ᵒᵖ),
      Subsingleton ((flatRankFunctor R M r).obj Y) := flatRankFunctor_subsingleton
  apply MorphismProperty.relative.of_exists
  intro T z
  have hT : LocallyFlatRank R M r T := (uliftYonedaEquiv z).down.down
  obtain ⟨kk, hkk⟩ := exists_chartRestrictLift (g := i.2.1) (f := i.1) i.2.2.down hT
  haveI : Mono (chartRestrictι i.1 T) := inferInstance
  refine ⟨Over.mk (chartRestrictι i.1 T ≫ T.hom),
    uliftYoneda.map (Over.homMk kk hkk), Over.homMk (chartRestrictι i.1 T) rfl, ?_,
    (inferInstance : IsOpenImmersion (chartRestrictι i.1 T))⟩
  have hsq : uliftYoneda.map (Over.homMk kk hkk) ≫ flatRankChartMap i =
      uliftYoneda.map (Over.homMk (chartRestrictι i.1 T) rfl :
        Over.mk (chartRestrictι i.1 T ≫ T.hom) ⟶ T) ≫ z := by
    ext Y a
    exact Subsingleton.elim _ _
  apply IsPullback.of_forall_isPullback_app
  intro Y
  rw [Types.isPullback_iff]
  refine ⟨congrArg (·.app Y) hsq, ?_, ?_⟩
  · rintro ⟨u⟩ ⟨v⟩ ⟨-, h2⟩
    apply ULift.ext
    haveI : Mono (Over.homMk (chartRestrictι i.1 T) rfl :
        Over.mk (chartRestrictι i.1 T ≫ T.hom) ⟶ T) := Over.mono_of_mono_left _
    rw [← cancel_mono (Over.homMk (chartRestrictι i.1 T) rfl :
      Over.mk (chartRestrictι i.1 T ≫ T.hom) ⟶ T)]
    exact congrArg ULift.down h2
  · rintro ⟨L⟩ ⟨a⟩ -
    have hLw : L.left ≫ freeRankStratumι i.2.1 i.1 = (unop Y).hom := Over.w L
    have haw : a.left ≫ T.hom = (unop Y).hom := Over.w a
    have hcond : a.left ≫ T.hom =
        (L.left ≫ freeRankLocusι (awayPresentation i.2.1 i.1)) ≫ awayIncl i.1 := by
      rw [Category.assoc, ← freeRankStratumι_eq, hLw, haw]
    let c : (unop Y).left ⟶ chartRestrict i.1 T := pullback.lift _ _ hcond
    have hc : c ≫ chartRestrictι i.1 T = a.left := pullback.lift_fst _ _ _
    refine ⟨⟨Over.homMk c (by rw [show (Over.mk (chartRestrictι i.1 T ≫ T.hom)).hom =
      chartRestrictι i.1 T ≫ T.hom from rfl, ← Category.assoc, hc, haw])⟩, ?_, ?_⟩
    · apply ULift.ext
      apply Over.OverMorphism.ext
      rw [← cancel_mono (freeRankStratumι i.2.1 i.1)]
      change (c ≫ kk) ≫ freeRankStratumι i.2.1 i.1 = L.left ≫ freeRankStratumι i.2.1 i.1
      rw [Category.assoc, hkk, hLw, ← Category.assoc, hc, haw]
    · apply ULift.ext
      apply Over.OverMorphism.ext
      exact hc

/-- **The flattening stratum `S_r`,** obtained by gluing the affine strata along the
flattening functor. -/
def flatRankRepresentative (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M]
    [Module R M] (r : ℕ) : Over (Spec (CommRingCat.of R)) :=
  Scheme.OverLocalRepresentability.gluedOver
    (fun i : FlatRankIndex R M r => flatRankChartMap_relative_isOpenImmersion i)

/-- **The flattening stratification, for one rank, over an affine base.**  The functor of
those schemes over `Spec R` on which `M` becomes Zariski-locally flat of rank `r` is
represented by a scheme over `Spec R`. -/
def flatRankRepresentableBy (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M]
    [Module R M] (r : ℕ) :
    (flatRankFunctor R M r).RepresentableBy (flatRankRepresentative R M r) := by
  let G := flatRankSheaf R M r
  let g : (i : FlatRankIndex R M r) → uliftYoneda.{0}.obj (flatRankChartObj i) ⟶ G.1 :=
    flatRankChartMap
  letI : Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over (Spec (CommRingCat.of R)))
      (Limits.Sigma.desc g) := by exact flatRankChartMap_isLocallySurjective
  exact Scheme.OverLocalRepresentability.representableBy G g
    (fun i : FlatRankIndex R M r => flatRankChartMap_relative_isOpenImmersion i)

/-- **The flattening stratum is a subscheme of the base**: its structure morphism is a
monomorphism, because the functor it represents is subsingleton-valued. -/
instance flatRankRepresentative_mono (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M]
    [Module R M] (r : ℕ) : Mono (flatRankRepresentative R M r).hom := by
  haveI hss : ∀ (Y : (Over (Spec (CommRingCat.of R)))ᵒᵖ),
      Subsingleton ((flatRankFunctor R M r).obj Y) := flatRankFunctor_subsingleton
  constructor
  intro Z a b hab
  let T : Over (Spec (CommRingCat.of R)) :=
    Over.mk (a ≫ (flatRankRepresentative R M r).hom)
  let A : T ⟶ flatRankRepresentative R M r := Over.homMk a rfl
  let B : T ⟶ flatRankRepresentative R M r := Over.homMk b hab.symm
  have hAB : A = B :=
    (flatRankRepresentableBy R M r).homEquiv.injective (Subsingleton.elim _ _)
  exact congrArg (fun q => q.left) hAB

/-- The flattening stratum is representable. -/
theorem flatRankFunctor_isRepresentable (R : Type u) [CommRing R] (M : Type u)
    [AddCommGroup M] [Module R M] (r : ℕ) : (flatRankFunctor R M r).IsRepresentable :=
  ⟨flatRankRepresentative R M r, ⟨flatRankRepresentableBy R M r⟩⟩

end Representable

end Module
