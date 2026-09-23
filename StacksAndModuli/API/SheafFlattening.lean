module

public import StacksAndModuli.API.ChartAtlasFunctor
public import StacksAndModuli.API.ModuleFlatteningImmersion
public import StacksAndModuli.«Section2.1-Intro».«part2.1.2-the-grassmannian-functor»
public import StacksAndModuli.API.CanonicalAffineGlobalSectionsBaseChange

/-!
# The flattening stratification over a general base

`API/ModuleFlatteningOpenChart.lean` represents the rank-`r` flattening functor of a *module*
over a ring, and `API/ModuleFlatteningImmersion.lean` shows its representative is an immersion
into `Spec R`.  §2.4 needs the same for a quasi-coherent sheaf `E` on an arbitrary scheme `X`
— the Grassmannian, over which the Quot-to-Grassmannian map is to be shown relatively
representable by immersions, is not affine.

The charts are the affine strata: for an affine open `U ⊆ X`,

`Module.flatRankRepresentative Γ(U,⊤) Γ(E|_U,⊤) r ⟶ Spec Γ(U,⊤) ≅ U ↪ X`,

an immersion by `Module.flatRankRepresentative_hom_isImmersion`.  Two of the three inputs of
`AlgebraicGeometry.OverLocalRepresentability` are then immediate from
`API/ChartAtlasFunctor.lean`, because the functor is subsingleton-valued: it is a Zariski sheaf
and the charts are jointly locally surjective.

Main declarations:

* `AlgebraicGeometry.Scheme.Modules.affineStratum` and its `IsImmersion` instance;
* `AlgebraicGeometry.Scheme.Modules.flatRankFunctorOver`,
  `…flatRankSheafOver`, `…flatRankChartOver`;
* `AlgebraicGeometry.Scheme.Modules.HasChartComparison` — the single remaining input — and
  `…flatRankChartOver_relative_isOpenImmersion`, the third input of the gluing, derived
  from it;
* `…flatRankRepresentativeOver`, `…flatRankRepresentableByOver`,
  `…flatRankFunctorOver_isRepresentable` and `…flatRankRepresentativeOver_mono`;
* `…affineOpenTensorEquiv` and `…chartTensorComparison` — the algebraic content of
  `HasChartComparison`;
* `…AffineFlatRank`, `…affineFlatRank_congr`, `…locallyFlatRank_of_affineFlatRank`,
  `…exists_affineFlatRank_of_toAffineStratum` and `…hasChartComparison` — the proof of that
  input, hence `…flatRankRepresentableByOfFinite`, the flattening stratification of a
  quasi-coherent sheaf on an arbitrary scheme.
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

/-- **The flattening stratum of `E` over an affine open of `X`**, regarded over `X`: the
rank-`r` stratum of the `Γ(U,⊤)`-module `Γ(E|_U,⊤)`, mapped into `X` through `U`.

Phrasing the module side as the *global sections of the restricted sheaf on the affine scheme
`U.toScheme`*, rather than as `Γ(E,U)` over `Γ(X,U)`, is what makes
`Modules.HasChartComparison` a direct application of
`canonicalAffinePullbackSectionsBaseChangeLinearMap_bijective`: no `Γ(U.toScheme,⊤) ≅ Γ(X,U)`
or `Γ((pullback U.ι).obj E, ⊤) ≅ Γ(E,U)` transport is needed anywhere. -/
def affineStratum (U : X.affineOpens) : Over X :=
  haveI : IsAffine U.1.toScheme := U.2
  Over.mk ((Module.flatRankRepresentative ↥Γ(U.1.toScheme, ⊤)
      ↥Γ((Modules.pullback U.1.ι).obj E, ⊤) r).hom ≫
    (U.1.toScheme.isoSpec).inv ≫ U.1.ι)

/-- The structure map of an affine flattening stratum is an immersion: a closed immersion into
an open part of `Spec Γ(X,U)`, followed by the open immersion `U ↪ X`. -/
instance affineStratum_hom_isImmersion (U : X.affineOpens) :
    IsImmersion (affineStratum E r U).hom := by
  haveI : IsAffine U.1.toScheme := U.2
  have h := Module.flatRankRepresentative_hom_isImmersion
    (R := ↥Γ(U.1.toScheme, ⊤)) (M := ↥Γ((Modules.pullback U.1.ι).obj E, ⊤)) (r := r)
  change IsImmersion ((Module.flatRankRepresentative ↥Γ(U.1.toScheme, ⊤)
      ↥Γ((Modules.pullback U.1.ι).obj E, ⊤) r).hom ≫
    (U.1.toScheme.isoSpec).inv ≫ U.1.ι)
  infer_instance

/-- Structure maps of the affine strata are monomorphisms. -/
instance affineStratum_hom_mono (U : X.affineOpens) : Mono (affineStratum E r U).hom :=
  inferInstance

/-- **The rank-`r` flattening functor of a sheaf on a general base**: those `T` over `X` that
Zariski locally factor through an affine flattening stratum. -/
abbrev flatRankFunctorOver : (Over X)ᵒᵖ ⥤ Type u :=
  Scheme.factorsFunctor (affineStratum E r)

/-- The flattening functor of a sheaf is a Zariski sheaf on schemes over `X`. -/
abbrev flatRankSheafOver : Sheaf (Scheme.zariskiTopology.over X) (Type u) :=
  Scheme.factorsSheaf (affineStratum E r)

/-- The chart map of an affine open into the flattening functor. -/
abbrev flatRankChartOver (U : X.affineOpens) :
    uliftYoneda.{0}.obj (affineStratum E r U) ⟶ flatRankFunctorOver E r :=
  Scheme.factorsChart (affineStratum E r) U

/-- The charts are jointly locally surjective onto the flattening functor. -/
example : Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over X)
    (Sigma.desc (f := fun U : X.affineOpens => uliftYoneda.{0}.obj (affineStratum E r U))
      (Scheme.factorsChart (affineStratum E r))) := inferInstance

/-- **The one remaining geometric input for a general base.**  If `V` over `X` factors locally
through the affine strata, and its structure map factors through the affine open `U`, then it
factors locally through the strata *of `U`*.

Everything else in the general-base flattening stratification is already proved: this is the
statement that the flattening conditions read off from two different affine opens agree, i.e.
that `Γ(Z,⊤) ⊗_{Γ(U,⊤)} Γ(E|_U,⊤)` and `Γ(Z,⊤) ⊗_{Γ(U',⊤)} Γ(E|_{U'},⊤)` agree for an affine `Z`
mapping into `U ⊓ U'` — both being `Γ(E|_Z, ⊤)`, by
`canonicalAffinePullbackSectionsBaseChangeLinearMap_bijective` and `Modules.pullbackComp`. -/
def HasChartComparison : Prop :=
  ∀ (U : X.affineOpens) (V : Over X) (ψ : V.left ⟶ U.1.toScheme),
    ψ ≫ U.1.ι = V.hom → Scheme.LocallyFactors (affineStratum E r) V →
      haveI : IsAffine U.1.toScheme := U.2
      Module.LocallyFlatRank ↥Γ(U.1.toScheme, ⊤) ↥Γ((Modules.pullback U.1.ι).obj E, ⊤) r
        (Over.mk (ψ ≫ U.1.toScheme.isoSpec.hom))

variable {E r}

/-- **Each chart of the general-base flattening functor is a relatively representable open
subfunctor.**  Over a test object carrying a point of the functor, the fibre product with the
chart of `U` is the open part `T ×_X U`; the projection to the chart is the affine
representability theorem, applied through `Modules.HasChartComparison`. -/
theorem flatRankChartOver_relative_isOpenImmersion (hcmp : HasChartComparison E r)
    (U : X.affineOpens) :
    (isOpenImmersionOver X).relative uliftYoneda.{0} (flatRankChartOver E r U) := by
  haveI hss : ∀ (Y : (Over X)ᵒᵖ), Subsingleton ((flatRankFunctorOver E r).obj Y) :=
    Scheme.factorsFunctor_subsingleton (affineStratum E r)
  apply MorphismProperty.relative.of_exists
  intro T z
  have hT : Scheme.LocallyFactors (affineStratum E r) T := (uliftYonedaEquiv z).down.down
  set p₁ := Limits.pullback.fst T.hom U.1.ι with hp₁
  set p₂ := Limits.pullback.snd T.hom U.1.ι with hp₂
  haveI : IsOpenImmersion p₁ := inferInstance
  set W : Over X := Over.mk (p₁ ≫ T.hom) with hW
  set w : W ⟶ T := Over.homMk p₁ rfl with hw
  have hψ : p₂ ≫ U.1.ι = W.hom := Limits.pullback.condition.symm
  have hWloc : Scheme.LocallyFactors (affineStratum E r) W :=
    Scheme.LocallyFactors.comp w hT
  haveI : IsAffine U.1.toScheme := U.2
  have hloc := hcmp U W p₂ hψ hWloc
  set cA := (Module.flatRankRepresentableBy ↥Γ(U.1.toScheme, ⊤)
    ↥Γ((Modules.pullback U.1.ι).obj E, ⊤) r).homEquiv.symm ⟨⟨hloc⟩⟩ with hcA
  have hcAw : cA.left ≫ (Module.flatRankRepresentative ↥Γ(U.1.toScheme, ⊤)
      ↥Γ((Modules.pullback U.1.ι).obj E, ⊤) r).hom =
      p₂ ≫ U.1.toScheme.isoSpec.hom := Over.w cA
  have hcw : cA.left ≫ (affineStratum E r U).hom = W.hom := by
    change cA.left ≫ (Module.flatRankRepresentative ↥Γ(U.1.toScheme, ⊤)
      ↥Γ((Modules.pullback U.1.ι).obj E, ⊤) r).hom ≫
      U.1.toScheme.isoSpec.inv ≫ U.1.ι = W.hom
    rw [← Category.assoc, hcAw, Category.assoc, Iso.hom_inv_id_assoc, hψ]
  haveI : Mono (affineStratum E r U).hom := inferInstance
  refine ⟨W, uliftYoneda.map (Over.homMk cA.left hcw), w, ?_,
    (inferInstance : IsOpenImmersion p₁)⟩
  have hsq : uliftYoneda.map (Over.homMk cA.left hcw : W ⟶ affineStratum E r U) ≫
      flatRankChartOver E r U = uliftYoneda.map w ≫ z := by
    ext Y a
    exact Subsingleton.elim _ _
  apply IsPullback.of_forall_isPullback_app
  intro Y
  rw [Types.isPullback_iff]
  refine ⟨congrArg (·.app Y) hsq, ?_, ?_⟩
  · rintro ⟨u⟩ ⟨v⟩ ⟨-, h2⟩
    apply ULift.ext
    haveI : Mono w := Over.mono_of_mono_left _
    rw [← cancel_mono w]
    exact congrArg ULift.down h2
  · rintro ⟨L⟩ ⟨a⟩ -
    have hLw : L.left ≫ (affineStratum E r U).hom = (unop Y).hom := Over.w L
    have haw : a.left ≫ T.hom = (unop Y).hom := Over.w a
    have hcond : a.left ≫ T.hom =
        (L.left ≫ (Module.flatRankRepresentative ↥Γ(U.1.toScheme, ⊤)
          ↥Γ((Modules.pullback U.1.ι).obj E, ⊤) r).hom ≫
          U.1.toScheme.isoSpec.inv) ≫ U.1.ι := by
      rw [Category.assoc, Category.assoc]
      change _ = L.left ≫ (affineStratum E r U).hom
      rw [hLw, haw]
    set c : (unop Y).left ⟶ Limits.pullback T.hom U.1.ι := Limits.pullback.lift _ _ hcond with hc
    have hcfst : c ≫ p₁ = a.left := Limits.pullback.lift_fst _ _ _
    refine ⟨⟨Over.homMk c (by
      change c ≫ p₁ ≫ T.hom = (unop Y).hom
      rw [← Category.assoc, hcfst, haw])⟩, ?_, ?_⟩
    · apply ULift.ext
      apply Over.OverMorphism.ext
      rw [← cancel_mono (affineStratum E r U).hom]
      change (c ≫ cA.left) ≫ (affineStratum E r U).hom =
        L.left ≫ (affineStratum E r U).hom
      rw [Category.assoc, hcw, hLw]
      change c ≫ p₁ ≫ T.hom = _
      rw [← Category.assoc, hcfst, haw]
    · apply ULift.ext
      apply Over.OverMorphism.ext
      exact hcfst

variable (E r)

/-- **The flattening stratum of a sheaf on a general base**, obtained by gluing the affine
strata along the flattening functor. -/
def flatRankRepresentativeOver (hcmp : HasChartComparison E r) : Over X :=
  Scheme.OverLocalRepresentability.gluedOver
    (fun U : X.affineOpens => flatRankChartOver_relative_isOpenImmersion hcmp U)

/-- **The flattening stratification over a general base.**  The functor of those schemes over
`X` on which `E` becomes Zariski-locally flat of rank `r` is represented by a scheme over
`X`. -/
def flatRankRepresentableByOver (hcmp : HasChartComparison E r) :
    (flatRankFunctorOver E r).RepresentableBy (flatRankRepresentativeOver E r hcmp) := by
  let G := flatRankSheafOver E r
  let g : (U : X.affineOpens) → uliftYoneda.{0}.obj (affineStratum E r U) ⟶ G.1 :=
    flatRankChartOver E r
  letI : Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over X)
      (Limits.Sigma.desc g) := by
    exact Scheme.factorsChart_isLocallySurjective (affineStratum E r)
  exact Scheme.OverLocalRepresentability.representableBy G g
    (fun U : X.affineOpens => flatRankChartOver_relative_isOpenImmersion hcmp U)

/-- The general-base flattening stratum is representable. -/
theorem flatRankFunctorOver_isRepresentable (hcmp : HasChartComparison E r) :
    (flatRankFunctorOver E r).IsRepresentable :=
  ⟨flatRankRepresentativeOver E r hcmp, ⟨flatRankRepresentableByOver E r hcmp⟩⟩

/-- **The general-base flattening stratum is a subscheme of the base**: its structure morphism
is a monomorphism, because the functor it represents is subsingleton-valued. -/
instance flatRankRepresentativeOver_mono (hcmp : HasChartComparison E r) :
    Mono (flatRankRepresentativeOver E r hcmp).hom := by
  haveI hss : ∀ (Y : (Over X)ᵒᵖ), Subsingleton ((flatRankFunctorOver E r).obj Y) :=
    Scheme.factorsFunctor_subsingleton (affineStratum E r)
  constructor
  intro Z a b hab
  let T : Over X := Over.mk (a ≫ (flatRankRepresentativeOver E r hcmp).hom)
  let A : T ⟶ flatRankRepresentativeOver E r hcmp := Over.homMk a rfl
  let B : T ⟶ flatRankRepresentativeOver E r hcmp := Over.homMk b hab.symm
  have hAB : A = B :=
    (flatRankRepresentableByOver E r hcmp).homEquiv.injective (Subsingleton.elim _ _)
  exact congrArg (fun q => q.left) hAB

section Comparison

/-- The sections at `⊤` of isomorphic modules are isomorphic. -/
def topSectionsIso {Z : Scheme.{u}} {M N : Z.Modules} (e : M ≅ N) :
    M.val.obj (op ⊤) ≅ N.val.obj (op ⊤) where
  hom := e.hom.val.app (op ⊤)
  inv := e.inv.val.app (op ⊤)
  hom_inv_id := congrArg (fun k => k.val.app (op ⊤)) e.hom_inv_id
  inv_hom_id := congrArg (fun k => k.val.app (op ⊤)) e.inv_hom_id

/-- **Sections of the pullback of `E` to an affine `Z` mapping into an affine open `U`.**
This is `canonicalAffinePullbackSectionsBaseChangeLinearMap_bijective` for the affine scheme
`U.toScheme`, followed by `Modules.pullbackComp`. -/
def affineOpenTensorEquiv (E : X.Modules) [E.IsQuasicoherent] (U : X.affineOpens)
    {Z : Scheme.{u}} [IsAffine Z] (ψ : Z ⟶ U.1.toScheme) :
    letI : IsAffine U.1.toScheme := U.2
    letI : Algebra ↥Γ(U.1.toScheme, ⊤) ↥Γ(Z, ⊤) := ψ.appTop.hom.toAlgebra
    Γ(Z, ⊤) ⊗[↥Γ(U.1.toScheme, ⊤)] Γ((Modules.pullback U.1.ι).obj E, ⊤) ≃ₗ[↥Γ(Z, ⊤)]
      Γ((Modules.pullback (ψ ≫ U.1.ι)).obj E, ⊤) := by
  haveI : IsAffine U.1.toScheme := U.2
  letI : Algebra ↥Γ(U.1.toScheme, ⊤) ↥Γ(Z, ⊤) := ψ.appTop.hom.toAlgebra
  exact (LinearEquiv.ofBijective
    (canonicalAffinePullbackSectionsBaseChangeLinearMap ψ ((Modules.pullback U.1.ι).obj E))
    (canonicalAffinePullbackSectionsBaseChangeLinearMap_bijective ψ _)).trans
    (topSectionsIso ((Scheme.Modules.pullbackComp ψ U.1.ι).app E)).toLinearEquiv

/-- The same, with the composite structure map to `X` named. -/
def affineOpenTensorEquiv' (E : X.Modules) [E.IsQuasicoherent] (U : X.affineOpens)
    {Z : Scheme.{u}} [IsAffine Z] (ψ : Z ⟶ U.1.toScheme) (φ : Z ⟶ X)
    (hφ : ψ ≫ U.1.ι = φ) :
    letI : IsAffine U.1.toScheme := U.2
    letI : Algebra ↥Γ(U.1.toScheme, ⊤) ↥Γ(Z, ⊤) := ψ.appTop.hom.toAlgebra
    Γ(Z, ⊤) ⊗[↥Γ(U.1.toScheme, ⊤)] Γ((Modules.pullback U.1.ι).obj E, ⊤) ≃ₗ[↥Γ(Z, ⊤)]
      Γ((Modules.pullback φ).obj E, ⊤) := by
  subst hφ
  exact affineOpenTensorEquiv E U ψ

/-- **The chart comparison.**  For an affine `Z` mapping into two affine opens of `X`, the two
base changes of the sections of `E` agree — both are the sections of `E` pulled back to `Z`.
This is the whole content of `Modules.HasChartComparison`. -/
def chartTensorComparison (E : X.Modules) [E.IsQuasicoherent] (U U' : X.affineOpens)
    {Z : Scheme.{u}} [IsAffine Z] (ψ : Z ⟶ U.1.toScheme) (ψ' : Z ⟶ U'.1.toScheme)
    (φ : Z ⟶ X) (hφ : ψ ≫ U.1.ι = φ) (hφ' : ψ' ≫ U'.1.ι = φ) :
    letI : IsAffine U.1.toScheme := U.2
    letI : IsAffine U'.1.toScheme := U'.2
    letI : Algebra ↥Γ(U.1.toScheme, ⊤) ↥Γ(Z, ⊤) := ψ.appTop.hom.toAlgebra
    letI : Algebra ↥Γ(U'.1.toScheme, ⊤) ↥Γ(Z, ⊤) := ψ'.appTop.hom.toAlgebra
    Γ(Z, ⊤) ⊗[↥Γ(U.1.toScheme, ⊤)] Γ((Modules.pullback U.1.ι).obj E, ⊤) ≃ₗ[↥Γ(Z, ⊤)]
      Γ(Z, ⊤) ⊗[↥Γ(U'.1.toScheme, ⊤)] Γ((Modules.pullback U'.1.ι).obj E, ⊤) :=
  (affineOpenTensorEquiv' E U ψ φ hφ).trans (affineOpenTensorEquiv' E U' ψ' φ hφ').symm

/-- The flatness-and-rank condition on an affine scheme mapping into an affine open. -/
def AffineFlatRank (E : X.Modules) (r : ℕ) {Z : Scheme.{u}} [IsAffine Z]
    (U : X.affineOpens) (ψ : Z ⟶ U.1.toScheme) : Prop :=
  letI : IsAffine U.1.toScheme := U.2
  letI : Algebra ↥Γ(U.1.toScheme, ⊤) ↥Γ(Z, ⊤) := ψ.appTop.hom.toAlgebra
  Module.Flat ↥Γ(Z, ⊤)
      (↥Γ(Z, ⊤) ⊗[↥Γ(U.1.toScheme, ⊤)] ↥Γ((Modules.pullback U.1.ι).obj E, ⊤)) ∧
    ∀ q : PrimeSpectrum ↥Γ(Z, ⊤),
      Module.rankAtStalk
        (↥Γ(Z, ⊤) ⊗[↥Γ(U.1.toScheme, ⊤)] ↥Γ((Modules.pullback U.1.ι).obj E, ⊤)) q = r

/-- (C3) From the affine condition to the local factorization through the strata of `U`. -/
theorem locallyFlatRank_of_affineFlatRank (E : X.Modules) (r : ℕ) (U : X.affineOpens)
    [haffU : IsAffine U.1.toScheme]
    [Module.Finite ↥Γ(U.1.toScheme, ⊤) ↥Γ((Modules.pullback U.1.ι).obj E, ⊤)]
    {Z : Scheme.{u}} [IsAffine Z] (ψ : Z ⟶ U.1.toScheme) (h : AffineFlatRank E r U ψ) :
    Module.LocallyFlatRank ↥Γ(U.1.toScheme, ⊤) ↥Γ((Modules.pullback U.1.ι).obj E, ⊤) r
      (Over.mk (ψ ≫ U.1.toScheme.isoSpec.hom)) := by
  letI : Algebra ↥Γ(U.1.toScheme, ⊤) ↥Γ(Z, ⊤) := ψ.appTop.hom.toAlgebra
  obtain ⟨hflat, hrank⟩ := h
  haveI := hflat
  have hP1 := Module.locallyFlatRank_of_flat_of_rankAtStalk
    (R := ↥Γ(U.1.toScheme, ⊤)) (M := ↥Γ((Modules.pullback U.1.ι).obj E, ⊤)) (r := r)
    ↥Γ(Z, ⊤) hrank
  have hcomm : Z.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap ↥Γ(U.1.toScheme, ⊤) ↥Γ(Z, ⊤))) =
      ψ ≫ U.1.toScheme.isoSpec.hom := by
    change Z.toSpecΓ ≫ Spec.map ψ.appTop = ψ ≫ U.1.toScheme.toSpecΓ
    exact (Scheme.toSpecΓ_naturality ψ).symm
  exact Module.LocallyFlatRank.comp
    (Over.homMk Z.isoSpec.hom hcomm :
      Over.mk (ψ ≫ U.1.toScheme.isoSpec.hom) ⟶
        Over.mk (Spec.map (CommRingCat.ofHom
          (algebraMap ↥Γ(U.1.toScheme, ⊤) ↥Γ(Z, ⊤))))) hP1

/-- (C1) The affine condition does not depend on the affine open used to compute it. -/
theorem affineFlatRank_congr (E : X.Modules) [E.IsQuasicoherent] (r : ℕ)
    (U U' : X.affineOpens) {Z : Scheme.{u}} [IsAffine Z]
    (ψ : Z ⟶ U.1.toScheme) (ψ' : Z ⟶ U'.1.toScheme)
    (φ : Z ⟶ X) (hφ : ψ ≫ U.1.ι = φ) (hφ' : ψ' ≫ U'.1.ι = φ)
    (h : AffineFlatRank E r U' ψ') : AffineFlatRank E r U ψ := by
  haveI : IsAffine U.1.toScheme := U.2
  haveI : IsAffine U'.1.toScheme := U'.2
  letI : Algebra ↥Γ(U.1.toScheme, ⊤) ↥Γ(Z, ⊤) := ψ.appTop.hom.toAlgebra
  letI : Algebra ↥Γ(U'.1.toScheme, ⊤) ↥Γ(Z, ⊤) := ψ'.appTop.hom.toAlgebra
  obtain ⟨hflat, hrank⟩ := h
  haveI := hflat
  set e := chartTensorComparison E U U' ψ ψ' φ hφ hφ' with he
  exact ⟨Module.Flat.of_linearEquiv e,
    fun q => by rw [Module.rankAtStalk_eq_of_equiv e]; exact hrank q⟩

/-- (C2) A map from an affine scheme to an affine stratum gives the affine condition, locally. -/
theorem exists_affineFlatRank_of_toAffineStratum (E : X.Modules) [E.IsQuasicoherent] (r : ℕ)
    (U' : X.affineOpens) {Z : Scheme.{u}} [IsAffine Z]
    (α : Z ⟶ (affineStratum E r U').left) (z : Z) :
    ∃ (R₂ : CommRingCat.{u}) (b : Spec R₂ ⟶ Z), IsOpenImmersion b ∧ z ∈ Set.range b.base ∧
      haveI : IsAffine U'.1.toScheme := U'.2
      AffineFlatRank E r U' (b ≫ α ≫
        (Module.flatRankRepresentative ↥Γ(U'.1.toScheme, ⊤)
          ↥Γ((Modules.pullback U'.1.ι).obj E, ⊤) r).hom ≫ U'.1.toScheme.isoSpec.inv) := by
  haveI : IsAffine U'.1.toScheme := U'.2
  set A' := ↥Γ(U'.1.toScheme, ⊤) with hA'
  set M' := ↥Γ((Modules.pullback U'.1.ι).obj E, ⊤) with hM'
  set S' := Module.flatRankRepresentative A' M' r with hS'
  set T : Over (Spec (CommRingCat.of A')) := Over.mk (α ≫ S'.hom) with hT
  have hTloc : Module.LocallyFlatRank A' M' r T :=
    ((Module.flatRankRepresentableBy A' M' r).homEquiv
      (Over.homMk α rfl : T ⟶ S')).down.down
  obtain ⟨V₁, k₁, hk₁, hz, f', g', hg', h₁, hh₁⟩ := hTloc z
  haveI := hk₁
  obtain ⟨R₂, b, hb, hzb, hsub⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (X := Z) (x := z)
      (U := k₁.left.opensRange) hz
  letI := hb
  set θ := IsOpenImmersion.lift k₁.left b hsub with hθ
  have hθb : θ ≫ k₁.left = b := IsOpenImmersion.lift_fac _ _ _
  refine ⟨R₂, b, hb, hzb, ?_⟩
  set ψ'' : Spec R₂ ⟶ U'.1.toScheme :=
    b ≫ α ≫ S'.hom ≫ U'.1.toScheme.isoSpec.inv with hψ''
  letI : Algebra A' ↥Γ(Spec R₂, ⊤) := ψ''.appTop.hom.toAlgebra
  have hmap : Spec.map (CommRingCat.ofHom (algebraMap A' ↥Γ(Spec R₂, ⊤))) =
      (Spec R₂).isoSpec.inv ≫ b ≫ α ≫ S'.hom := by
    have hnat := Scheme.toSpecΓ_naturality ψ''
    change ψ'' ≫ U'.1.toScheme.isoSpec.hom =
      (Spec R₂).isoSpec.hom ≫ Spec.map ψ''.appTop at hnat
    change Spec.map ψ''.appTop = _
    rw [← Iso.inv_hom_id_assoc (Spec R₂).isoSpec (Spec.map ψ''.appTop), ← hnat, hψ'']
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hlift : ∃ k : Spec (CommRingCat.of ↥Γ(Spec R₂, ⊤)) ⟶ Module.freeRankStratum g' f',
      k ≫ Module.freeRankStratumι g' f' =
        Spec.map (CommRingCat.ofHom (algebraMap A' ↥Γ(Spec R₂, ⊤))) := by
    refine ⟨(Spec R₂).isoSpec.inv ≫ θ ≫ h₁, ?_⟩
    have key : θ ≫ Over.Hom.left k₁ ≫ T.hom = b ≫ α ≫ S'.hom := by
      rw [← Category.assoc, hθb]
      rfl
    rw [hmap, Category.assoc, Category.assoc, hh₁, ← Over.w k₁, key]
  obtain ⟨-, hflat, hrank⟩ :=
    (Module.flat_and_rankAtStalk_iff_exists_freeRankStratumLift' hg' ↥Γ(Spec R₂, ⊤)).mpr hlift
  exact ⟨hflat, hrank⟩

/-- **The chart comparison holds.** -/
theorem hasChartComparison (E : X.Modules) [E.IsQuasicoherent] (r : ℕ)
    (hfin : ∀ U : X.affineOpens, haveI : IsAffine U.1.toScheme := U.2;
      Module.Finite ↥Γ(U.1.toScheme, ⊤) ↥Γ((Modules.pullback U.1.ι).obj E, ⊤)) :
    HasChartComparison E r := by
  intro U V ψ hψ hV
  haveI : IsAffine U.1.toScheme := U.2
  haveI := hfin U
  have main : ∀ x : V.left,
      ∃ (W : Over (Spec (CommRingCat.of ↥Γ(U.1.toScheme, ⊤))))
        (k : W ⟶ Over.mk (ψ ≫ U.1.toScheme.isoSpec.hom)),
        IsOpenImmersion k.left ∧ x ∈ Set.range k.left.base ∧
        Module.LocallyFlatRank ↥Γ(U.1.toScheme, ⊤)
          ↥Γ((Modules.pullback U.1.ι).obj E, ⊤) r W := by
    intro x
    obtain ⟨V₀, k₀, hk₀, hx₀, U', d, hd⟩ := hV x
    haveI := hk₀
    obtain ⟨R₁, b₁, hb₁, hxb₁, hsub₁⟩ :=
      Scheme.exists_affine_mem_range_and_range_subset (X := V.left) (x := x)
        (U := (Over.Hom.left k₀).opensRange) hx₀
    letI := hb₁
    set θ₀ := IsOpenImmersion.lift (Over.Hom.left k₀) b₁ hsub₁ with hθ₀
    have hθ₀b : θ₀ ≫ Over.Hom.left k₀ = b₁ := IsOpenImmersion.lift_fac _ _ _
    obtain ⟨y, hy⟩ := hxb₁
    obtain ⟨R₂, b, hb, hyb, hafr'⟩ :=
      exists_affineFlatRank_of_toAffineStratum E r U' (θ₀ ≫ d) y
    letI := hb
    haveI : IsAffine U'.1.toScheme := U'.2
    set ψ₂ : Spec R₂ ⟶ U.1.toScheme := (b ≫ b₁) ≫ ψ with hψ₂
    have heq : ψ₂ ≫ U.1.ι =
        (b ≫ (θ₀ ≫ d) ≫ (Module.flatRankRepresentative ↥Γ(U'.1.toScheme, ⊤)
          ↥Γ((Modules.pullback U'.1.ι).obj E, ⊤) r).hom ≫ U'.1.toScheme.isoSpec.inv) ≫
          U'.1.ι := by
      have h1' : d ≫ (Module.flatRankRepresentative ↥Γ(U'.1.toScheme, ⊤)
          ↥Γ((Modules.pullback U'.1.ι).obj E, ⊤) r).hom ≫ U'.1.toScheme.isoSpec.inv ≫ U'.1.ι =
          V₀.hom := hd
      have key : θ₀ ≫ Over.Hom.left k₀ ≫ V.hom = b₁ ≫ V.hom := by
        rw [← Category.assoc, hθ₀b]
      simp only [hψ₂, Category.assoc]
      rw [h1', hψ, ← Over.w k₀, key]
    have hafr : AffineFlatRank E r U ψ₂ :=
      affineFlatRank_congr E r U U' ψ₂ _ (ψ₂ ≫ U.1.ι) rfl heq.symm hafr'
    refine ⟨Over.mk (ψ₂ ≫ U.1.toScheme.isoSpec.hom), Over.homMk (b ≫ b₁) ?_, ?_, ?_,
      locallyFlatRank_of_affineFlatRank E r U ψ₂ hafr⟩
    · change b ≫ b₁ ≫ ψ ≫ U.1.toScheme.isoSpec.hom = ψ₂ ≫ U.1.toScheme.isoSpec.hom
      simp only [hψ₂, Category.assoc]
    · exact inferInstanceAs (IsOpenImmersion (b ≫ b₁))
    · obtain ⟨w, hw⟩ := hyb
      exact ⟨w, by
        change (b ≫ b₁).base w = x
        rw [Scheme.Hom.comp_base]
        change b₁.base (b.base w) = x
        rw [hw]
        exact hy⟩
  choose W k hk hx hW using main
  exact Module.LocallyFlatRank.of_cover W k hk (fun x => ⟨x, hx x⟩) hW

/-- **The general-base flattening stratum, unconditionally.** -/
def flatRankRepresentativeOfFinite (E : X.Modules) [E.IsQuasicoherent] (r : ℕ)
    (hfin : ∀ U : X.affineOpens, haveI : IsAffine U.1.toScheme := U.2;
      Module.Finite ↥Γ(U.1.toScheme, ⊤) ↥Γ((Modules.pullback U.1.ι).obj E, ⊤)) : Over X :=
  flatRankRepresentativeOver E r (hasChartComparison E r hfin)

/-- **The flattening stratification of a quasi-coherent sheaf on an arbitrary scheme.**  The
functor of those `T` over `X` on which `E` becomes Zariski-locally flat of constant rank `r` is
represented by a scheme over `X`. -/
def flatRankRepresentableByOfFinite (E : X.Modules) [E.IsQuasicoherent] (r : ℕ)
    (hfin : ∀ U : X.affineOpens, haveI : IsAffine U.1.toScheme := U.2;
      Module.Finite ↥Γ(U.1.toScheme, ⊤) ↥Γ((Modules.pullback U.1.ι).obj E, ⊤)) :
    (flatRankFunctorOver E r).RepresentableBy (flatRankRepresentativeOfFinite E r hfin) :=
  flatRankRepresentableByOver E r (hasChartComparison E r hfin)

/-- The general-base flattening stratum is representable. -/
theorem flatRankFunctorOver_isRepresentable_of_finite (E : X.Modules) [E.IsQuasicoherent]
    (r : ℕ) (hfin : ∀ U : X.affineOpens, haveI : IsAffine U.1.toScheme := U.2;
      Module.Finite ↥Γ(U.1.toScheme, ⊤) ↥Γ((Modules.pullback U.1.ι).obj E, ⊤)) :
    (flatRankFunctorOver E r).IsRepresentable :=
  flatRankFunctorOver_isRepresentable E r (hasChartComparison E r hfin)

end Comparison

end AlgebraicGeometry.Scheme.Modules
