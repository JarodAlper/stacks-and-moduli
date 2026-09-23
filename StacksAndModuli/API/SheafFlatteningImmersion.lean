module

public import StacksAndModuli.API.SheafFlattening
public import StacksAndModuli.API.ModuleFlatteningImmersion

/-!
# The general-base flattening stratum is an immersion

`API/SheafFlattening.lean` represents the rank-`r` flattening functor of a quasi-coherent sheaf
`E` on an arbitrary scheme `X`.  This file upgrades its structure morphism to an **immersion**,
which is the form in which §2.4 consumes the flattening stratification: a natural
transformation whose fibres are flattening strata is then relatively representable by
immersions (`AlgebraicGeometry.relative_over_isImmersion_of_iso`).

The argument is the one of `API/ModuleFlatteningImmersion.lean`, transported chart by chart.
Being an immersion is not local on the source, so the structure morphism is factored through
the open locus `⨆ U (chart open of U)` and shown to be a **closed** immersion into it — a
property that *is* local at the target, and over each chart open the stratum *is* the chart
(`Modules.isPullback_chartOverMapGen`).

Main declarations:

* `AlgebraicGeometry.Scheme.Modules.chartOpenScheme`, `…chartOpenIncl`, `…chartClosedIncl`;
* `…chartOverMapGen` and `…isPullback_chartOverMapGen`;
* `…flatRankOpenOver`, `…flatRankLiftOver` and its `IsClosedImmersion` instance;
* `…flatRankRepresentativeOver_hom_isImmersion` and the unconditional
  `…flatRankRepresentativeOfFinite_hom_isImmersion`.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (E : X.Modules) (r : ℕ)

/-- The scheme over which the chart of `U` is a closed subscheme. -/
def chartOpenScheme (U : X.affineOpens) : Scheme.{u} :=
  (Module.flatRankOpen ↥Γ(U.1.toScheme, ⊤) ↥Γ((Modules.pullback U.1.ι).obj E, ⊤) r).toScheme

/-- Its open immersion into `X`. -/
def chartOpenIncl (U : X.affineOpens) : chartOpenScheme E r U ⟶ X :=
  haveI : IsAffine U.1.toScheme := U.2
  (Module.flatRankOpen ↥Γ(U.1.toScheme, ⊤)
      ↥Γ((Modules.pullback U.1.ι).obj E, ⊤) r).ι ≫
    U.1.toScheme.isoSpec.inv ≫ U.1.ι

instance chartOpenIncl_isOpenImmersion (U : X.affineOpens) :
    IsOpenImmersion (chartOpenIncl E r U) := by
  haveI : IsAffine U.1.toScheme := U.2
  change IsOpenImmersion ((Module.flatRankOpen ↥Γ(U.1.toScheme, ⊤)
      ↥Γ((Modules.pullback U.1.ι).obj E, ⊤) r).ι ≫
    U.1.toScheme.isoSpec.inv ≫ U.1.ι)
  infer_instance

/-- The affine stratum, as a closed subscheme of its open. -/
def chartClosedIncl (U : X.affineOpens) :
    (affineStratum E r U).left ⟶ chartOpenScheme E r U :=
  haveI : IsAffine U.1.toScheme := U.2
  Module.flatRankLift ↥Γ(U.1.toScheme, ⊤) ↥Γ((Modules.pullback U.1.ι).obj E, ⊤) r

instance chartClosedIncl_isClosedImmersion (U : X.affineOpens) :
    IsClosedImmersion (chartClosedIncl E r U) := by
  haveI : IsAffine U.1.toScheme := U.2
  change IsClosedImmersion (Module.flatRankLift ↥Γ(U.1.toScheme, ⊤)
    ↥Γ((Modules.pullback U.1.ι).obj E, ⊤) r)
  infer_instance

lemma chartClosedIncl_chartOpenIncl (U : X.affineOpens) :
    chartClosedIncl E r U ≫ chartOpenIncl E r U = (affineStratum E r U).hom := by
  haveI : IsAffine U.1.toScheme := U.2
  change Module.flatRankLift ↥Γ(U.1.toScheme, ⊤)
      ↥Γ((Modules.pullback U.1.ι).obj E, ⊤) r ≫
    (Module.flatRankOpen ↥Γ(U.1.toScheme, ⊤)
      ↥Γ((Modules.pullback U.1.ι).obj E, ⊤) r).ι ≫
    U.1.toScheme.isoSpec.inv ≫ U.1.ι = _
  rw [← Category.assoc, Module.flatRankLift_ι]
  rfl

variable {E r}

/-- The chart, as an object over the general-base flattening stratum. -/
def chartOverMapGen (hcmp : HasChartComparison E r) (U : X.affineOpens) :
    affineStratum E r U ⟶ flatRankRepresentativeOver E r hcmp :=
  (flatRankRepresentableByOver E r hcmp).homEquiv.symm
    ⟨⟨Scheme.LocallyFactors.of_factors U (𝟙 _) (Category.id_comp _)⟩⟩

lemma chartOverMapGen_w (hcmp : HasChartComparison E r) (U : X.affineOpens) :
    (chartOverMapGen hcmp U).left ≫ (flatRankRepresentativeOver E r hcmp).hom =
      (affineStratum E r U).hom :=
  Over.w (chartOverMapGen hcmp U)

/-- A test scheme over the stratum whose structure map factors through the chart's open
factors through the chart. -/
lemma exists_chartLiftGen (hcmp : HasChartComparison E r) (U : X.affineOpens)
    {Z : Scheme.{u}} (a : Z ⟶ (flatRankRepresentativeOver E r hcmp).left)
    (b : Z ⟶ chartOpenScheme E r U)
    (hab : a ≫ (flatRankRepresentativeOver E r hcmp).hom = b ≫ chartOpenIncl E r U) :
    ∃ c : Z ⟶ (affineStratum E r U).left,
      c ≫ (affineStratum E r U).hom = a ≫ (flatRankRepresentativeOver E r hcmp).hom := by
  haveI : IsAffine U.1.toScheme := U.2
  set T : Over X := Over.mk (a ≫ (flatRankRepresentativeOver E r hcmp).hom) with hT
  have hTloc : Scheme.LocallyFactors (affineStratum E r) T :=
    ((flatRankRepresentableByOver E r hcmp).homEquiv
      (Over.homMk a rfl : T ⟶ flatRankRepresentativeOver E r hcmp)).down.down
  set ψ : Z ⟶ U.1.toScheme :=
    b ≫ (Module.flatRankOpen ↥Γ(U.1.toScheme, ⊤)
      ↥Γ((Modules.pullback U.1.ι).obj E, ⊤) r).ι ≫ U.1.toScheme.isoSpec.inv with hψdef
  have hψ : ψ ≫ U.1.ι = T.hom := by
    rw [hψdef]
    simp only [Category.assoc]
    change b ≫ chartOpenIncl E r U = _
    rw [← hab]
    rfl
  have hloc := hcmp U T ψ hψ hTloc
  set cA := (Module.flatRankRepresentableBy ↥Γ(U.1.toScheme, ⊤)
    ↥Γ((Modules.pullback U.1.ι).obj E, ⊤) r).homEquiv.symm ⟨⟨hloc⟩⟩ with hcA
  have hcAw : cA.left ≫ (Module.flatRankRepresentative ↥Γ(U.1.toScheme, ⊤)
      ↥Γ((Modules.pullback U.1.ι).obj E, ⊤) r).hom = ψ ≫ U.1.toScheme.isoSpec.hom := Over.w cA
  refine ⟨cA.left, ?_⟩
  change cA.left ≫ (Module.flatRankRepresentative ↥Γ(U.1.toScheme, ⊤)
    ↥Γ((Modules.pullback U.1.ι).obj E, ⊤) r).hom ≫
    U.1.toScheme.isoSpec.inv ≫ U.1.ι = _
  rw [← Category.assoc, hcAw]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact hψ

/-- **The chart is exactly the part of the flattening stratum over the chart's open.** -/
theorem isPullback_chartOverMapGen (hcmp : HasChartComparison E r) (U : X.affineOpens) :
    IsPullback ((chartOverMapGen hcmp U).left) (chartClosedIncl E r U)
      (flatRankRepresentativeOver E r hcmp).hom (chartOpenIncl E r U) := by
  haveI : Mono (flatRankRepresentativeOver E r hcmp).hom := inferInstance
  haveI : Mono (chartOpenIncl E r U) := inferInstance
  haveI : Mono (affineStratum E r U).hom := inferInstance
  have hw : (chartOverMapGen hcmp U).left ≫ (flatRankRepresentativeOver E r hcmp).hom =
      chartClosedIncl E r U ≫ chartOpenIncl E r U := by
    rw [chartOverMapGen_w, chartClosedIncl_chartOpenIncl]
  have key : ∀ s : PullbackCone (flatRankRepresentativeOver E r hcmp).hom (chartOpenIncl E r U),
      ∃ c : s.pt ⟶ (affineStratum E r U).left,
        c ≫ (affineStratum E r U).hom =
          s.fst ≫ (flatRankRepresentativeOver E r hcmp).hom :=
    fun s => exists_chartLiftGen hcmp U s.fst s.snd s.condition
  refine IsPullback.of_isLimit (PullbackCone.isLimitAux (PullbackCone.mk _ _ hw)
    (fun s => (key s).choose) (fun s => ?_) (fun s => ?_) (fun s m hm => ?_))
  · rw [← cancel_mono (flatRankRepresentativeOver E r hcmp).hom]
    change (key s).choose ≫ (chartOverMapGen hcmp U).left ≫
      (flatRankRepresentativeOver E r hcmp).hom = _
    rw [chartOverMapGen_w, (key s).choose_spec]
  · rw [← cancel_mono (chartOpenIncl E r U)]
    change ((key s).choose ≫ chartClosedIncl E r U) ≫ chartOpenIncl E r U = _
    rw [Category.assoc, chartClosedIncl_chartOpenIncl, (key s).choose_spec, s.condition]
  · rw [← cancel_mono (affineStratum E r U).hom, (key s).choose_spec,
      ← chartClosedIncl_chartOpenIncl, ← Category.assoc]
    have h2 := hm WalkingCospan.right
    change m ≫ chartClosedIncl E r U = s.snd at h2
    rw [h2, ← s.condition]

variable (E r)

/-- The open locus of `X` covered by the chart opens. -/
def flatRankOpenOver : X.Opens := ⨆ U : X.affineOpens, (chartOpenIncl E r U).opensRange

variable {E r}

lemma chartOpenIncl_range_subset (U : X.affineOpens) :
    Set.range (chartOpenIncl E r U).base ⊆ (flatRankOpenOver E r : Set X) :=
  le_iSup (fun V : X.affineOpens => (chartOpenIncl E r V).opensRange) U

lemma range_flatRankRepresentativeOver_hom_subset (hcmp : HasChartComparison E r) :
    Set.range (flatRankRepresentativeOver E r hcmp).hom.base ⊆
      (flatRankOpenOver E r : Set X) := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨U, y, hy⟩ :=
    (Scheme.OverLocalRepresentability.glueData
      (fun U : X.affineOpens =>
        flatRankChartOver_relative_isOpenImmersion hcmp U)).openCover.exists_eq x
  have hcomp := Scheme.OverLocalRepresentability.toGlued_comp_gluedHom
    (fun U : X.affineOpens => flatRankChartOver_relative_isOpenImmersion hcmp U) U
  refine chartOpenIncl_range_subset U ⟨(chartClosedIncl E r U).base y, ?_⟩
  change ((chartClosedIncl E r U) ≫ chartOpenIncl E r U).base y = _
  rw [chartClosedIncl_chartOpenIncl]
  rw [← hcomp, ← hy]
  rfl

variable (E r)

/-- The stratum, as a scheme over the open locus. -/
def flatRankLiftOver (hcmp : HasChartComparison E r) :
    (flatRankRepresentativeOver E r hcmp).left ⟶ (flatRankOpenOver E r).toScheme :=
  IsOpenImmersion.lift (flatRankOpenOver E r).ι (flatRankRepresentativeOver E r hcmp).hom
    (by rw [Scheme.Opens.range_ι]; exact range_flatRankRepresentativeOver_hom_subset hcmp)

lemma flatRankLiftOver_ι (hcmp : HasChartComparison E r) :
    flatRankLiftOver E r hcmp ≫ (flatRankOpenOver E r).ι =
      (flatRankRepresentativeOver E r hcmp).hom := IsOpenImmersion.lift_fac _ _ _

/-- A chart open, as a scheme over the open locus. -/
def chartOpenToOpen (U : X.affineOpens) :
    chartOpenScheme E r U ⟶ (flatRankOpenOver E r).toScheme :=
  IsOpenImmersion.lift (flatRankOpenOver E r).ι (chartOpenIncl E r U)
    (by rw [Scheme.Opens.range_ι]; exact chartOpenIncl_range_subset U)

lemma chartOpenToOpen_ι (U : X.affineOpens) :
    chartOpenToOpen E r U ≫ (flatRankOpenOver E r).ι = chartOpenIncl E r U :=
  IsOpenImmersion.lift_fac _ _ _

instance chartOpenToOpen_isOpenImmersion (U : X.affineOpens) :
    IsOpenImmersion (chartOpenToOpen E r U) := by
  haveI : IsOpenImmersion (chartOpenToOpen E r U ≫ (flatRankOpenOver E r).ι) := by
    rw [chartOpenToOpen_ι]; infer_instance
  exact IsOpenImmersion.of_comp _ (flatRankOpenOver E r).ι

/-- The chart opens cover the open locus. -/
def flatRankOpenOverCover : Scheme.OpenCover.{u} (flatRankOpenOver E r).toScheme :=
  Scheme.openCoverOfMaps (fun U : X.affineOpens => chartOpenScheme E r U)
    (chartOpenToOpen E r) (fun U => inferInstance) (by
      intro y
      have hy : ∃ U : X.affineOpens,
          ((flatRankOpenOver E r).ι).base y ∈ (chartOpenIncl E r U).opensRange := by
        rw [← TopologicalSpace.Opens.mem_iSup]; exact y.2
      obtain ⟨U, z, hz⟩ := hy
      refine ⟨U, z, ?_⟩
      apply ((flatRankOpenOver E r).ι.isOpenEmbedding).injective
      rw [← Scheme.Hom.comp_apply, chartOpenToOpen_ι]
      exact hz)

instance flatRankLiftOver_isClosedImmersion (hcmp : HasChartComparison E r) :
    IsClosedImmersion (flatRankLiftOver E r hcmp) := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion)
    (flatRankOpenOverCover E r)]
  intro U
  have hsq : IsPullback ((chartOverMapGen hcmp U).left) (chartClosedIncl E r U)
      (flatRankLiftOver E r hcmp) (chartOpenToOpen E r U) := by
    refine IsPullback.of_comp_mono (flatRankOpenOver E r).ι ?_
    rw [flatRankLiftOver_ι, chartOpenToOpen_ι]
    exact isPullback_chartOverMapGen hcmp U
  have hcan := IsPullback.of_hasPullback (flatRankLiftOver E r hcmp) (chartOpenToOpen E r U)
  have e : Arrow.mk (pullback.snd (flatRankLiftOver E r hcmp) (chartOpenToOpen E r U)) ≅
      Arrow.mk (chartClosedIncl E r U) :=
    Arrow.isoMk (hcan.isoIsPullback _ _ hsq) (Iso.refl _) (by simp)
  change IsClosedImmersion (pullback.snd (flatRankLiftOver E r hcmp) (chartOpenToOpen E r U))
  exact (MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion) e).mpr inferInstance

/-- **The general-base flattening stratum is an immersion into the base.** -/
theorem flatRankRepresentativeOver_hom_isImmersion (hcmp : HasChartComparison E r) :
    IsImmersion (flatRankRepresentativeOver E r hcmp).hom := by
  rw [IsImmersion.isImmersion_iff_exists]
  exact ⟨_, flatRankLiftOver E r hcmp, (flatRankOpenOver E r).ι, inferInstance, inferInstance,
    flatRankLiftOver_ι E r hcmp⟩

/-- **The flattening stratum of a quasi-coherent sheaf on an arbitrary scheme is an
immersion into the base.** -/
theorem flatRankRepresentativeOfFinite_hom_isImmersion (E : X.Modules) [E.IsQuasicoherent]
    (r : ℕ) (hfin : ∀ U : X.affineOpens, haveI : IsAffine U.1.toScheme := U.2;
      Module.Finite ↥Γ(U.1.toScheme, ⊤) ↥Γ((Modules.pullback U.1.ι).obj E, ⊤)) :
    IsImmersion (flatRankRepresentativeOfFinite E r hfin).hom :=
  flatRankRepresentativeOver_hom_isImmersion E r (hasChartComparison E r hfin)

end AlgebraicGeometry.Scheme.Modules
