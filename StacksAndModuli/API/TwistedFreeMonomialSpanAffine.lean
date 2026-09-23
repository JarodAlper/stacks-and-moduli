module

public import StacksAndModuli.API.TwistedFreeMonomialSpan
public import StacksAndModuli.API.ProjectiveSpaceTwistSurjectivityAffine

/-!
# Monomial spanning over the affine opens of the base

`API/TwistedFreeMonomialSpan.lean` proves the monomial spanning of `Γ(F(d))` over an
affine base (`surjective_finFreeSectionsMap'_twistedFreeMonomial_top`).  The Grassmannian
map of §2.4 needs it over each affine open `U` of an arbitrary base `T`.  This file
transports the affine statement along the open immersion
`mU := projectiveSpaceOverMap n (U.isoSpec.inv ≫ U.ι)`.

The transport never touches the coproduct-twist identification `ν : F(d) ≅ 𝒪(d-l)^{⊕r}`
of the ambient sheaf under base change: the span statement is conjugated by `ν` *on the
base `T` itself* (an app of an isomorphism over the same scheme, hence linear), split by
the finite-coproduct sections equivalence, and only the resulting *single-twist*
statement is transported.  For a single twist, the pullback comparison is definitionally
the `pullbackComp ≫ pullbackCongr` chain, so the monomial compatibility is exactly
`Scheme.Modules.pullbackGlobalSections_comp_congr`.

Main declarations:

* `AlgebraicGeometry.ProjectiveSpace.twistMonomialSection_pullback` — the monomial
  sections form a compatible family under any base change;
* `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback_app_top_res` — the
  restriction of a global section, read through the restriction/pullback comparison, is
  its canonical pullback;
* `AlgebraicGeometry.ProjectiveSpace.span_twistMonomialSection_res` — the single-twist
  spanning over every affine open of any base;
* `AlgebraicGeometry.ProjectiveSpace.
  surjective_finFreeSectionsMap'_twistedFreeMonomial` — monomial spanning of the
  twisted-free ambient sheaf;
* `AlgebraicGeometry.ProjectiveSpace.
  exists_bound_surjective_finFreeSectionsMap_quotGrassmannian` — the resulting uniform
  affine-section surjectivity for the Quot-to-Grassmannian map.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Helper lemma for the affine-open transport: the affine chart `Spec Γ(T, U) ⟶ T` of
an affine open has image `U`. -/
lemma isoSpec_inv_ι_image_top {T : Scheme.{u}} (U : T.affineOpens) :
    (U.2.isoSpec.inv ≫ U.1.ι) ''ᵁ (⊤ : (Spec Γ(T, U.1)).Opens) = U.1 := by
  rw [Scheme.Hom.image_top_eq_opensRange]
  apply TopologicalSpace.Opens.ext
  show Set.range (U.2.isoSpec.inv ≫ U.1.ι).base = (U.1 : Set T)
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  have hsurj : Set.range (U.2.isoSpec.inv).base = Set.univ :=
    Set.range_eq_univ.mpr (fun y => ⟨(U.2.isoSpec.hom).base y, by
      rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]; rfl⟩)
  rw [hsurj, Set.image_univ, Scheme.Opens.range_ι]

/-- Helper lemma for the affine-open transport: relative projective space over the affine
chart of an affine open maps onto the preimage of the open. -/
lemma projectiveSpaceOverMap_image_top (n : ℕ) {T : Scheme.{u}} (U : T.affineOpens) :
    Scheme.projectiveSpaceOverMap n (U.2.isoSpec.inv ≫ U.1.ι) ''ᵁ
        (⊤ : (Scheme.projectiveSpaceOver n (Spec Γ(T, U.1))).Opens)
      = Scheme.projectiveSpaceOverπ n T ⁻¹ᵁ U.1 := by
  haveI : IsOpenImmersion (U.2.isoSpec.inv ≫ U.1.ι) := inferInstance
  rw [Scheme.Hom.image_top_eq_opensRange]
  have hgrange : (U.2.isoSpec.inv ≫ U.1.ι).opensRange = U.1 := by
    rw [← Scheme.Hom.image_top_eq_opensRange]
    exact isoSpec_inv_ι_image_top U
  apply TopologicalSpace.Opens.ext
  show Set.range (Scheme.projectiveSpaceOverMap n (U.2.isoSpec.inv ≫ U.1.ι)).base = _
  rw [Scheme.range_projectiveSpaceOverMap n (U.2.isoSpec.inv ≫ U.1.ι), hgrange]

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Modules

/-- API lemma for the affine-open transport: `pullbackGlobalSections` is the raw unit of
the pullback--pushforward adjunction on global sections. -/
lemma pullbackGlobalSections_eq_unit_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (t : Γ(M, ⊤)) :
    Scheme.Modules.pullbackGlobalSections f M t
      = ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app ⊤ t := rfl

-- The adjunction-uniqueness component calculation needs additional elaboration time.
set_option maxHeartbeats 800000 in
/-- API lemma for the affine-open transport: the restriction of a global section, through
the restriction/pullback comparison, is its canonical pullback. This is
`Adjunction.unit_leftAdjointUniq_hom_app` for the two left adjoints of the pushforward
along an open immersion. -/
lemma restrictFunctorIsoPullback_app_top_res {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (M : Y.Modules) (t : Γ(M, ⊤)) :
    Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app M) ⊤
        (show Γ((Scheme.Modules.restrictFunctor f).obj M, ⊤) from
          M.val.map ((homOfLE (le_top (a := f ''ᵁ (⊤ : X.Opens)))).op :
            op (⊤ : Y.Opens) ⟶ op (f ''ᵁ (⊤ : X.Opens))) t)
      = Scheme.Modules.pullbackGlobalSections f M t := by
  have huniq := CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app
    (Scheme.Modules.restrictAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction f) M
  have happ := congrArg
    (fun k : M ⟶ (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj M) =>
      Scheme.Modules.Hom.app k ⊤ t) huniq
  -- the composite app splits, the pushforward app is the app on the preimage, and the
  -- restriction-adjunction unit is a presheaf restriction, all definitionally
  have hL : Scheme.Modules.Hom.app
      ((Scheme.Modules.restrictAdjunction f).unit.app M ≫
        (Scheme.Modules.pushforward f).map
          ((CategoryTheory.Adjunction.leftAdjointUniq
            (Scheme.Modules.restrictAdjunction f)
            (Scheme.Modules.pullbackPushforwardAdjunction f)).hom.app M)) ⊤ t
      = Scheme.Modules.Hom.app
          ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app M) ⊤
          (show Γ((Scheme.Modules.restrictFunctor f).obj M, ⊤) from
            M.val.map ((homOfLE (le_top (a := f ''ᵁ (⊤ : X.Opens)))).op :
              op (⊤ : Y.Opens) ⟶ op (f ''ᵁ (⊤ : X.Opens))) t) := rfl
  exact hL.symm.trans happ

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.ProjectiveSpace

open AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Supporting API for the Quot-to-Grassmannian construction in Proposition 2.4.1: the monomial
sections form a compatible family. Pulling the `i`-th monomial section back along the
relative projective-space map of any base morphism gives the `i`-th monomial section,
through the twist base-change comparison. -/
theorem twistMonomialSection_pullback (n : ℕ) {S T : Scheme.{u}} (g : T ⟶ S) (e : ℕ)
    (i : Fin ((n + e).choose n)) :
    Scheme.Modules.Hom.app (Scheme.projectiveSpaceOverTwist_pullbackIso n g (e : ℤ)).hom ⊤
        (Scheme.Modules.pullbackGlobalSections (Scheme.projectiveSpaceOverMap n g)
          (Scheme.projectiveSpaceOverTwist n S (e : ℤ))
          (Scheme.twistMonomialSection n S e i))
      = Scheme.twistMonomialSection n T e i := by
  have hcol := Scheme.Modules.pullbackGlobalSections_comp_congr
    (Scheme.projectiveSpaceOverMap n g)
    (Limits.pullback.snd (specULiftZIsTerminal.from S)
      (specULiftZIsTerminal.from (Scheme.projectiveSpace n)))
    (Limits.pullback.snd (specULiftZIsTerminal.from T)
      (specULiftZIsTerminal.from (Scheme.projectiveSpace n)))
    (Scheme.projectiveSpaceOverMap_absolute_snd n g)
    (ProjectiveSpectrum.Twist.twist
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) (e : ℤ))
    (MvPolynomial.projectiveTwistGlobalSectionsBasis n (ULift.{u} ℤ) e i)
  exact hcol

-- Instance search under the section-module `letI`s needs additional time.
set_option synthInstance.maxHeartbeats 1000000 in
/-- Supporting API for the Quot-to-Grassmannian construction in Proposition 2.4.1: the monomial
sections of a single twist span over an affine base, over the global functions of the
base. -/
theorem span_twistMonomialSection_top (n : ℕ) (R : Type u) [CommRing R] (e : ℕ) :
    letI : Module ↥Γ(Spec (CommRingCat.of R), ⊤)
        ↥Γ(Scheme.projectiveSpaceOverTwist n (Spec (CommRingCat.of R)) (e : ℤ), ⊤) :=
      Scheme.Modules.preimageSectionsModule
        (Scheme.projectiveSpaceOverπ n (Spec (CommRingCat.of R)))
        (Scheme.projectiveSpaceOverTwist n (Spec (CommRingCat.of R)) (e : ℤ)) ⊤
    Submodule.span ↥Γ(Spec (CommRingCat.of R), ⊤)
        (Set.range fun i : Fin ((n + e).choose n) =>
          Scheme.twistMonomialSection n (Spec (CommRingCat.of R)) e i) = ⊤ := by
  letI : Module ↥Γ(Spec (CommRingCat.of R), ⊤)
      ↥Γ(Scheme.projectiveSpaceOverTwist n (Spec (CommRingCat.of R)) (e : ℤ), ⊤) :=
    Scheme.Modules.preimageSectionsModule
      (Scheme.projectiveSpaceOverπ n (Spec (CommRingCat.of R)))
      (Scheme.projectiveSpaceOverTwist n (Spec (CommRingCat.of R)) (e : ℤ)) ⊤
  letI := Scheme.Modules.globalSectionsModule
    (Scheme.projectiveSpaceOverπ n (Spec (CommRingCat.of R)))
    (Scheme.projectiveSpaceOverTwist n (Spec (CommRingCat.of R)) (e : ℤ))
  rw [_root_.eq_top_iff]
  rintro x -
  have hx : x = ∑ i : Fin ((n + e).choose n),
      (Scheme.projectiveSpaceOverTwistGlobalSectionsBasis n R e).repr x i •
        Scheme.projectiveSpaceOverTwistGlobalSectionsBasis n R e i :=
    (Module.Basis.sum_repr _ x).symm
  rw [hx]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [projectiveSpaceOverTwistGlobalSectionsBasis_eq_twistMonomialSection n R e i]
  exact Submodule.smul_mem _
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      ((Scheme.projectiveSpaceOverTwistGlobalSectionsBasis n R e).repr x i))
    (Submodule.subset_span ⟨i, rfl⟩)

/-- Helper lemma for the affine-open transport: equal morphisms have equal `appLE`s. -/
lemma _root_.AlgebraicGeometry.Scheme.Hom.appLE_congr_hom {X Y : Scheme.{u}}
    {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) :
    f.appLE U V e = g.appLE U V (h ▸ e) := by subst h; rfl

-- The transport carries the same instance-search and elaboration burden as the (C) chain.
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- Supporting API for the Quot-to-Grassmannian construction in Proposition 2.4.1: the restricted
monomial sections of a single twist span over every affine open of any base. The statement
over the affine chart `Spec Γ(T, U)`
(`span_twistMonomialSection_top`) transports along the open immersion
`ℙⁿ_{Spec Γ(T, U)} ⟶ ℙⁿ_T`. -/
theorem span_twistMonomialSection_res (n : ℕ) {T : Scheme.{u}} (U : T.affineOpens)
    (e : ℕ) :
    letI : Module ↥Γ(T, U.1)
        ↥Γ(Scheme.projectiveSpaceOverTwist n T (e : ℤ),
          Scheme.projectiveSpaceOverπ n T ⁻¹ᵁ U.1) :=
      Scheme.Modules.preimageSectionsModule (Scheme.projectiveSpaceOverπ n T)
        (Scheme.projectiveSpaceOverTwist n T (e : ℤ)) U.1
    Submodule.span ↥Γ(T, U.1)
        (Set.range fun i : Fin ((n + e).choose n) =>
          (show ↥Γ(Scheme.projectiveSpaceOverTwist n T (e : ℤ),
              Scheme.projectiveSpaceOverπ n T ⁻¹ᵁ U.1) from
            (Scheme.projectiveSpaceOverTwist n T (e : ℤ)).val.map
              ((homOfLE (le_top (a := Scheme.projectiveSpaceOverπ n T ⁻¹ᵁ U.1))).op :
                op (⊤ : (Scheme.projectiveSpaceOver n T).Opens) ⟶
                  op (Scheme.projectiveSpaceOverπ n T ⁻¹ᵁ U.1))
              (Scheme.twistMonomialSection n T e i))) = ⊤ := by
  set gU : Spec Γ(T, U.1) ⟶ T := U.2.isoSpec.inv ≫ U.1.ι with hgU
  haveI : IsOpenImmersion gU := inferInstance
  set mU := Scheme.projectiveSpaceOverMap n gU with hmU
  haveI : IsOpenImmersion mU := inferInstance
  set Mtw := Scheme.projectiveSpaceOverTwist n T (e : ℤ) with hMtw
  letI : Module ↥Γ(T, U.1)
      ↥Γ(Mtw, Scheme.projectiveSpaceOverπ n T ⁻¹ᵁ U.1) :=
    Scheme.Modules.preimageSectionsModule (Scheme.projectiveSpaceOverπ n T) Mtw U.1
  set Mtw' := Scheme.projectiveSpaceOverTwist n (Spec Γ(T, U.1)) (e : ℤ) with hMtw'
  letI : Module ↥Γ(Spec Γ(T, U.1), ⊤) ↥Γ(Mtw', ⊤) :=
    Scheme.Modules.preimageSectionsModule
      (Scheme.projectiveSpaceOverπ n (Spec Γ(T, U.1))) Mtw' ⊤
  have hW : Scheme.projectiveSpaceOverπ n T ⁻¹ᵁ U.1
      = mU ''ᵁ (⊤ : (Scheme.projectiveSpaceOver n (Spec Γ(T, U.1))).Opens) :=
    (projectiveSpaceOverMap_image_top n U).symm
  have hU : U.1 = gU ''ᵁ (⊤ : (Spec Γ(T, U.1)).Opens) :=
    (isoSpec_inv_ι_image_top U).symm
  -- the single-twist comparison isomorphism on the chart
  set θ : (Scheme.Modules.restrictFunctor mU).obj Mtw ≅ Mtw' :=
    (Scheme.Modules.restrictFunctorIsoPullback mU).app Mtw ≪≫
      Scheme.projectiveSpaceOverTwist_pullbackIso n gU (e : ℤ) with hθ
  -- the section comparison
  set Ψ : ↥Γ(Mtw, Scheme.projectiveSpaceOverπ n T ⁻¹ᵁ U.1) → ↥Γ(Mtw', ⊤) :=
    fun v => Scheme.Modules.Hom.app θ.hom ⊤
      (show Γ((Scheme.Modules.restrictFunctor mU).obj Mtw, ⊤) from
        Mtw.val.map ((eqToHom hW.symm).op) v) with hΨ
  -- the ring comparisons
  set χ : Γ(Scheme.projectiveSpaceOver n T, Scheme.projectiveSpaceOverπ n T ⁻¹ᵁ U.1) ⟶
      Γ(Scheme.projectiveSpaceOver n (Spec Γ(T, U.1)), ⊤) :=
    (Scheme.projectiveSpaceOver n T).presheaf.map ((eqToHom hW.symm).op) ≫
      (mU.appIso ⊤).hom with hχ
  set ρ : Γ(T, U.1) ⟶ Γ(Spec Γ(T, U.1), ⊤) :=
    T.presheaf.map ((eqToHom hU.symm).op) ≫ (gU.appIso ⊤).hom with hρ
  haveI : IsIso ρ := by rw [hρ]; infer_instance
  have hρbij : Function.Bijective ρ.hom :=
    (ConcreteCategory.isIso_iff_bijective ρ).mp inferInstance
  let ρe := RingEquiv.ofBijective ρ.hom hρbij
  have hρe : ∀ z : ↥Γ(Spec Γ(T, U.1), ⊤), ρ.hom (ρe.symm z) = z := fun z =>
    ρe.apply_symm_apply z
  -- the ring square
  have hcomm : mU ≫ Scheme.projectiveSpaceOverπ n T
      = Scheme.projectiveSpaceOverπ n (Spec Γ(T, U.1)) ≫ gU :=
    Scheme.projectiveSpaceOverMap_π n gU
  have hpre : (mU ≫ Scheme.projectiveSpaceOverπ n T) ⁻¹ᵁ U.1 = ⊤ := by
    show mU ⁻¹ᵁ (Scheme.projectiveSpaceOverπ n T ⁻¹ᵁ U.1) = ⊤
    rw [hW]
    exact mU.preimage_image_eq ⊤
  have he₁ : (⊤ : (Scheme.projectiveSpaceOver n (Spec Γ(T, U.1))).Opens)
      ≤ (mU ≫ Scheme.projectiveSpaceOverπ n T) ⁻¹ᵁ U.1 := le_of_eq hpre.symm
  have hgUpre : gU ⁻¹ᵁ U.1 = ⊤ := by
    have h := congrArg (fun V : T.Opens => gU ⁻¹ᵁ V) hU
    rw [gU.preimage_image_eq ⊤] at h
    exact h
  have hpre' : (Scheme.projectiveSpaceOverπ n (Spec Γ(T, U.1)) ≫ gU) ⁻¹ᵁ U.1 = ⊤ := by
    show Scheme.projectiveSpaceOverπ n (Spec Γ(T, U.1)) ⁻¹ᵁ (gU ⁻¹ᵁ U.1) = ⊤
    rw [hgUpre]
    rfl
  have he₂ : Scheme.projectiveSpaceOverπ n (Spec Γ(T, U.1)) ⁻¹ᵁ
        (⊤ : (Spec Γ(T, U.1)).Opens)
      ≤ (Scheme.projectiveSpaceOverπ n (Spec Γ(T, U.1)) ≫ gU) ⁻¹ᵁ U.1 :=
    le_of_eq (by rw [hpre']; rfl)
  have h1 : (Scheme.projectiveSpaceOverπ n T).app U.1 ≫ χ
      = (mU ≫ Scheme.projectiveSpaceOverπ n T).appLE U.1 ⊤ he₁ := by
    rw [hχ, Scheme.Hom.appIso_hom' mU ⊤, Scheme.Hom.map_appLE, Scheme.Hom.comp_appLE]
  have h2 : ρ ≫ (Scheme.projectiveSpaceOverπ n (Spec Γ(T, U.1))).app ⊤
      = (Scheme.projectiveSpaceOverπ n (Spec Γ(T, U.1)) ≫ gU).appLE U.1
          (Scheme.projectiveSpaceOverπ n (Spec Γ(T, U.1)) ⁻¹ᵁ ⊤) he₂ := by
    rw [hρ, Scheme.Hom.appIso_hom' gU ⊤, Scheme.Hom.map_appLE,
      Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  have h3 : (mU ≫ Scheme.projectiveSpaceOverπ n T).appLE U.1 ⊤ he₁
      = (Scheme.projectiveSpaceOverπ n (Spec Γ(T, U.1)) ≫ gU).appLE U.1
          (Scheme.projectiveSpaceOverπ n (Spec Γ(T, U.1)) ⁻¹ᵁ ⊤) he₂ :=
    (Scheme.Hom.appLE_congr_hom hcomm U.1 ⊤ he₁).trans rfl
  have hcat : (Scheme.projectiveSpaceOverπ n T).app U.1 ≫ χ
      = ρ ≫ (Scheme.projectiveSpaceOverπ n (Spec Γ(T, U.1))).app ⊤ :=
    h1.trans (h3.trans h2.symm)
  have hsq : ∀ a : ↥Γ(T, U.1),
      χ.hom (((Scheme.projectiveSpaceOverπ n T).app U.1).hom a)
        = ((Scheme.projectiveSpaceOverπ n (Spec Γ(T, U.1))).app ⊤).hom (ρ.hom a) :=
    fun a => ConcreteCategory.congr_hom hcat a
  -- elementwise inverse of the appIso ring comparison
  have hIsoCancel : ∀ z : ↥Γ(Scheme.projectiveSpaceOver n T,
      mU ''ᵁ (⊤ : (Scheme.projectiveSpaceOver n (Spec Γ(T, U.1))).Opens)),
      (mU.appIso ⊤).inv.hom ((mU.appIso ⊤).hom.hom z) = z := fun z =>
    ConcreteCategory.congr_hom (mU.appIso ⊤).hom_inv_id z
  -- semilinearity of the section comparison
  have hsmul : ∀ (a : ↥Γ(Scheme.projectiveSpaceOver n T,
        Scheme.projectiveSpaceOverπ n T ⁻¹ᵁ U.1))
      (v : ↥Γ(Mtw, Scheme.projectiveSpaceOverπ n T ⁻¹ᵁ U.1)),
      Ψ (a • v) = χ.hom a • Ψ v := by
    intro a v
    have hmap : Mtw.val.map ((eqToHom hW.symm).op) (a • v)
        = ((Scheme.projectiveSpaceOver n T).presheaf.map ((eqToHom hW.symm).op) a)
          • Mtw.val.map ((eqToHom hW.symm).op) v := Mtw.val.map_smul _ a v
    have hcancel : (mU.appIso ⊤).inv.hom (χ.hom a)
        = (Scheme.projectiveSpaceOver n T).presheaf.map ((eqToHom hW.symm).op) a := by
      have hval : χ.hom a = (mU.appIso ⊤).hom.hom
          ((Scheme.projectiveSpaceOver n T).presheaf.map ((eqToHom hW.symm).op) a) := rfl
      rw [hval, hIsoCancel]
    have hres : (show Γ((Scheme.Modules.restrictFunctor mU).obj Mtw, ⊤) from
        Mtw.val.map ((eqToHom hW.symm).op) (a • v))
        = (χ.hom a) • (show Γ((Scheme.Modules.restrictFunctor mU).obj Mtw, ⊤) from
            Mtw.val.map ((eqToHom hW.symm).op) v) := by
      rw [hmap, ← hcancel]
      rfl
    show Scheme.Modules.Hom.app θ.hom ⊤ _ = _
    rw [hres]
    exact Scheme.Modules.Hom.app_smul θ.hom (χ.hom a) _
  -- additivity of the section comparison
  have hadd : ∀ v w, Ψ (v + w) = Ψ v + Ψ w := by
    intro v w
    show Scheme.Modules.Hom.app θ.hom ⊤ _ = _
    rw [show (show Γ((Scheme.Modules.restrictFunctor mU).obj Mtw, ⊤) from
        Mtw.val.map ((eqToHom hW.symm).op) (v + w))
      = (show Γ((Scheme.Modules.restrictFunctor mU).obj Mtw, ⊤) from
          Mtw.val.map ((eqToHom hW.symm).op) v)
        + (show Γ((Scheme.Modules.restrictFunctor mU).obj Mtw, ⊤) from
            Mtw.val.map ((eqToHom hW.symm).op) w) from map_add _ v w]
    exact map_add _ _ _
  have hzero : Ψ 0 = 0 := by
    show Scheme.Modules.Hom.app θ.hom ⊤ _ = _
    rw [show (show Γ((Scheme.Modules.restrictFunctor mU).obj Mtw, ⊤) from
        Mtw.val.map ((eqToHom hW.symm).op) 0)
      = 0 from map_zero _]
    exact map_zero _
  let Ψ' : ↥Γ(Mtw, Scheme.projectiveSpaceOverπ n T ⁻¹ᵁ U.1) →+ ↥Γ(Mtw', ⊤) :=
    { toFun := Ψ, map_zero' := hzero, map_add' := hadd }
  -- injectivity of the section comparison
  have hinj : Function.Injective Ψ := by
    intro v w hvw
    have hstep : Mtw.val.map ((eqToHom hW.symm).op) v
        = Mtw.val.map ((eqToHom hW.symm).op) w := by
      have hivo := congrArg (fun k :
          (Scheme.Modules.restrictFunctor mU).obj Mtw ⟶
            (Scheme.Modules.restrictFunctor mU).obj Mtw =>
        (PresheafOfModules.Hom.app k.val (op ⊤)).hom
          (show Γ((Scheme.Modules.restrictFunctor mU).obj Mtw, ⊤) from
            Mtw.val.map ((eqToHom hW.symm).op) v)) θ.hom_inv_id
      have hivw := congrArg (fun k :
          (Scheme.Modules.restrictFunctor mU).obj Mtw ⟶
            (Scheme.Modules.restrictFunctor mU).obj Mtw =>
        (PresheafOfModules.Hom.app k.val (op ⊤)).hom
          (show Γ((Scheme.Modules.restrictFunctor mU).obj Mtw, ⊤) from
            Mtw.val.map ((eqToHom hW.symm).op) w)) θ.hom_inv_id
      have hmid := congrArg
        (fun z : ↥Γ(Mtw', ⊤) => Scheme.Modules.Hom.app θ.inv ⊤ z) hvw
      exact hivo.symm.trans (hmid.trans hivw)
    have hback := congrArg
      (fun z => Mtw.val.map ((eqToHom hW).op) z) hstep
    have hvv : ∀ u : ↥Γ(Mtw, Scheme.projectiveSpaceOverπ n T ⁻¹ᵁ U.1),
        Mtw.val.map ((eqToHom hW).op) (Mtw.val.map ((eqToHom hW.symm).op) u) = u := by
      intro u
      have hcompmap := (Mtw.val.map_comp_apply
        ((eqToHom hW.symm).op) ((eqToHom hW).op) u).symm
      have hid : ((eqToHom hW.symm).op ≫ (eqToHom hW).op :
          op (Scheme.projectiveSpaceOverπ n T ⁻¹ᵁ U.1) ⟶
            op (Scheme.projectiveSpaceOverπ n T ⁻¹ᵁ U.1))
          = 𝟙 _ := Subsingleton.elim _ _
      rw [hid, PresheafOfModules.map_id] at hcompmap
      exact hcompmap
    exact (hvv v).symm.trans (hback.trans (hvv w))
  -- the restricted monomial family
  set mres : Fin ((n + e).choose n) →
      ↥Γ(Mtw, Scheme.projectiveSpaceOverπ n T ⁻¹ᵁ U.1) := fun i =>
    Mtw.val.map
      ((homOfLE (le_top (a := Scheme.projectiveSpaceOverπ n T ⁻¹ᵁ U.1))).op)
      (Scheme.twistMonomialSection n T e i) with hmres
  -- the monomial compatibility
  have hmono : ∀ i : Fin ((n + e).choose n),
      Ψ (mres i)
        = Scheme.twistMonomialSection n (Spec Γ(T, U.1)) e i := by
    intro i
    have hmerge : Mtw.val.map ((eqToHom hW.symm).op)
        (Mtw.val.map
          ((homOfLE (le_top (a := Scheme.projectiveSpaceOverπ n T ⁻¹ᵁ U.1))).op)
          (Scheme.twistMonomialSection n T e i))
        = Mtw.val.map ((homOfLE (le_top (a := mU ''ᵁ
            (⊤ : (Scheme.projectiveSpaceOver n (Spec Γ(T, U.1))).Opens)))).op)
          (Scheme.twistMonomialSection n T e i) := by
      have hcompmap := (Mtw.val.map_comp_apply
        ((homOfLE (le_top (a := Scheme.projectiveSpaceOverπ n T ⁻¹ᵁ U.1))).op)
        ((eqToHom hW.symm).op) (Scheme.twistMonomialSection n T e i)).symm
      have hid : ((homOfLE (le_top (a := Scheme.projectiveSpaceOverπ n T ⁻¹ᵁ U.1))).op ≫
          (eqToHom hW.symm).op :
            op (⊤ : (Scheme.projectiveSpaceOver n T).Opens) ⟶
              op (mU ''ᵁ (⊤ : (Scheme.projectiveSpaceOver n
                (Spec Γ(T, U.1))).Opens)))
          = (homOfLE (le_top (a := mU ''ᵁ (⊤ : (Scheme.projectiveSpaceOver n
              (Spec Γ(T, U.1))).Opens)))).op := Subsingleton.elim _ _
      rw [hid] at hcompmap
      exact hcompmap
    show Scheme.Modules.Hom.app θ.hom ⊤ _ = _
    refine Eq.trans (congrArg
      (fun z : ↥Γ((Scheme.Modules.restrictFunctor mU).obj Mtw, ⊤) =>
        Scheme.Modules.Hom.app θ.hom ⊤ z) hmerge) ?_
    refine Eq.trans (congrArg
      (fun z : ↥Γ((Scheme.Modules.pullback mU).obj Mtw, ⊤) =>
        Scheme.Modules.Hom.app
          (Scheme.projectiveSpaceOverTwist_pullbackIso n gU (e : ℤ)).hom ⊤ z)
      (Scheme.Modules.restrictFunctorIsoPullback_app_top_res mU Mtw
        (Scheme.twistMonomialSection n T e i))) ?_
    exact twistMonomialSection_pullback n gU e i
  -- the span transport
  rw [_root_.eq_top_iff]
  rintro y -
  have htop := span_twistMonomialSection_top n (↥Γ(T, U.1)) e
  have hmem : Ψ y ∈ Submodule.span ↥Γ(Spec (CommRingCat.of ↥Γ(T, U.1)), ⊤)
      (Set.range fun i : Fin ((n + e).choose n) =>
        Scheme.twistMonomialSection n (Spec (CommRingCat.of ↥Γ(T, U.1))) e i) :=
    Submodule.eq_top_iff'.mp htop (Ψ y)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hmem
  -- the preimage combination
  have hterm : ∀ i : Fin ((n + e).choose n),
      Ψ (ρe.symm (c i) • mres i)
        = c i • Scheme.twistMonomialSection n (Spec Γ(T, U.1)) e i := by
    intro i
    have hact : ρe.symm (c i) • mres i
        = (((Scheme.projectiveSpaceOverπ n T).app U.1).hom (ρe.symm (c i)))
          • mres i := rfl
    rw [hact, hsmul, hsq (ρe.symm (c i)), hρe (c i), hmono i]
    rfl
  have hΨsum : Ψ (∑ i : Fin ((n + e).choose n), ρe.symm (c i) • mres i) = Ψ y := by
    have hmapsum : Ψ (∑ i : Fin ((n + e).choose n), ρe.symm (c i) • mres i)
        = ∑ i : Fin ((n + e).choose n), Ψ (ρe.symm (c i) • mres i) :=
      map_sum Ψ' (fun i : Fin ((n + e).choose n) => ρe.symm (c i) • mres i)
        Finset.univ
    rw [hmapsum]
    have hsum2 : ∑ i : Fin ((n + e).choose n), Ψ (ρe.symm (c i) • mres i)
        = ∑ i : Fin ((n + e).choose n),
            c i • Scheme.twistMonomialSection n (Spec Γ(T, U.1)) e i :=
      Finset.sum_congr rfl fun i _ => hterm i
    rw [hsum2]
    exact hc
  have hyeq : y = ∑ i : Fin ((n + e).choose n), ρe.symm (c i) • mres i :=
    (hinj hΨsum).symm
  rw [hyeq]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hmm : mres i ∈ Set.range (fun i : Fin ((n + e).choose n) =>
      (show ↥Γ(Scheme.projectiveSpaceOverTwist n T (e : ℤ),
          Scheme.projectiveSpaceOverπ n T ⁻¹ᵁ U.1) from
        (Scheme.projectiveSpaceOverTwist n T (e : ℤ)).val.map
          ((homOfLE (le_top (a := Scheme.projectiveSpaceOverπ n T ⁻¹ᵁ U.1))).op :
            op (⊤ : (Scheme.projectiveSpaceOver n T).Opens) ⟶
              op (Scheme.projectiveSpaceOverπ n T ⁻¹ᵁ U.1))
          (Scheme.twistMonomialSection n T e i))) := ⟨i, rfl⟩
  exact Submodule.smul_mem _ (ρe.symm (c i)) (Submodule.subset_span hmm)

end AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme.Modules

section OpenSectionsFiniteCoproduct

attribute [local instance] Limits.HasFiniteBiproducts.of_hasFiniteCoproducts

-- Biproduct instance search needs additional time.
set_option synthInstance.maxHeartbeats 400000 in
/-- Helper lemma computing the finite-coproduct sections comparison over an open through
the biproduct projections. The `letI`s repeat those of `openSectionsFiniteCoproductLinearEquiv`
verbatim so that the `show` step is `rfl`. -/
theorem openSectionsFiniteCoproductLinearEquiv_apply {X : Scheme.{u}} {J : Type u}
    [Finite J] (U : X.Opens) (F : J → X.Modules) (s : Γ(∐ F, U)) (j : J) :
    openSectionsFiniteCoproductLinearEquiv U F s j
      = (PresheafOfModules.Hom.app
          ((Limits.biproduct.isoCoproduct F).inv ≫ Limits.biproduct.π F j).val
          (op U)).hom s := by
  letI : Limits.HasFiniteBiproducts X.Modules :=
    Limits.HasFiniteBiproducts.of_hasFiniteCoproducts
  let G := openSectionsFunctor U
  letI : G.Additive := by dsimp only [G]; infer_instance
  letI : Limits.PreservesBiproduct F G :=
    let ⟨_⟩ := nonempty_fintype J
    { preserves := fun hb ↦
        ⟨Limits.isBilimitOfTotal _ (by
          simp_rw [G.mapBicone_π, G.mapBicone_ι, ← G.map_comp]
          erw [← G.map_sum, ← G.map_id, Limits.IsBilimit.total hb])⟩ }
  show ((moduleCatBiproductIsoPi (G.obj ∘ F)).hom.hom
      ((Functor.mapBiproduct G F).hom.hom
        ((G.map (Limits.biproduct.isoCoproduct F).symm.hom).hom s))) j = _
  have hA : ∀ (H : J → ModuleCat.{u} ↥Γ(X, U)) (w : (⨁ H : ModuleCat.{u} ↥Γ(X, U)))
      (i : J),
      ((moduleCatBiproductIsoPi H).hom.hom w) i = (Limits.biproduct.π H i).hom w := by
    intro H w i
    exact congrArg (fun f : (⨁ H : ModuleCat.{u} ↥Γ(X, U)) ⟶ H i ↦ f.hom w)
      (Limits.IsLimit.conePointUniqueUpToIso_hom_comp (Limits.biproduct.isLimit H)
        (ModuleCat.HasLimit.productLimitCone H).isLimit ⟨i⟩)
  have hB : (Functor.mapBiproduct G F).hom ≫ Limits.biproduct.π (G.obj ∘ F) j
      = G.map (Limits.biproduct.π F j) := by
    rw [Functor.mapBiproduct_hom]
    exact Limits.biproduct.lift_π _ j
  rw [hA]
  have hB' := congrArg (fun f : G.obj (⨁ F) ⟶ (G.obj ∘ F) j ↦
    f.hom ((G.map (Limits.biproduct.isoCoproduct F).symm.hom).hom s)) hB
  refine hB'.trans ?_
  rfl

-- Biproduct instance search needs additional time.
set_option synthInstance.maxHeartbeats 400000 in
/-- Helper lemma computing the finite-coproduct sections comparison over an open on a
coproduct injection: its image is the corresponding single-component tuple. -/
theorem openSectionsFiniteCoproductLinearEquiv_ι {X : Scheme.{u}} {J : Type u}
    [Finite J] [DecidableEq J] (U : X.Opens) (F : J → X.Modules) (j : J)
    (s : Γ(F j, U)) :
    openSectionsFiniteCoproductLinearEquiv U F
        (Scheme.Modules.Hom.app (Limits.Sigma.ι F j) U s)
      = Pi.single j s := by
  letI : Limits.HasFiniteBiproducts X.Modules :=
    Limits.HasFiniteBiproducts.of_hasFiniteCoproducts
  funext j'
  have happ := openSectionsFiniteCoproductLinearEquiv_apply U F
    (Scheme.Modules.Hom.app (Limits.Sigma.ι F j) U s) j'
  refine happ.trans ?_
  have hcomp : Limits.Sigma.ι F j ≫
      ((Limits.biproduct.isoCoproduct F).inv ≫ Limits.biproduct.π F j')
      = if h : j = j' then eqToHom (congrArg F h) else 0 := by
    rw [Limits.biproduct.isoCoproduct_inv, ← Category.assoc, Limits.colimit.ι_desc]
    exact Limits.biproduct.ι_π F j j'
  have hL : (PresheafOfModules.Hom.app
      ((Limits.biproduct.isoCoproduct F).inv ≫ Limits.biproduct.π F j').val (op U)).hom
      (Scheme.Modules.Hom.app (Limits.Sigma.ι F j) U s)
      = (PresheafOfModules.Hom.app (Limits.Sigma.ι F j ≫
          ((Limits.biproduct.isoCoproduct F).inv ≫ Limits.biproduct.π F j')).val
        (op U)).hom s := rfl
  rw [hL, hcomp]
  rcases eq_or_ne j j' with rfl | hjj
  · rw [dif_pos rfl]
    rw [Pi.single_eq_same]
    rfl
  · rw [dif_neg hjj]
    rw [Pi.single_eq_of_ne' hjj]
    rfl

end OpenSectionsFiniteCoproduct

/-- Helper lemma for the affine-open transport: restricting the image of a global section
under a sheaf morphism is the image of the restriction. -/
lemma app_top_restrict {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) (V : X.Opens)
    (t : Γ(M, ⊤)) :
    N.val.map ((homOfLE (le_top (a := V))).op : op (⊤ : X.Opens) ⟶ op V)
        (Scheme.Modules.Hom.app φ ⊤ t)
      = Scheme.Modules.Hom.app φ V
        (M.val.map ((homOfLE (le_top (a := V))).op : op (⊤ : X.Opens) ⟶ op V) t) := by
  have hnat := ConcreteCategory.congr_hom
    (φ.val.naturality ((homOfLE (le_top (a := V))).op : op (⊤ : X.Opens) ⟶ op V)) t
  have hnat' : Scheme.Modules.Hom.app φ V
      (M.val.map ((homOfLE (le_top (a := V))).op : op (⊤ : X.Opens) ⟶ op V) t)
      = N.val.map ((homOfLE (le_top (a := V))).op : op (⊤ : X.Opens) ⟶ op V)
        (Scheme.Modules.Hom.app φ ⊤ t) := hnat
  exact hnat'.symm

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.ProjectiveSpace

open AlgebraicGeometry.Scheme

-- Instance search under the section-module `letI`s needs additional time.
set_option synthInstance.maxHeartbeats 1000000 in
/-- API variant of `span_twistMonomialSection_res`, with the twist written as an arbitrary
integer equal to a natural number and the monomial sections transported along the
equality. -/
theorem span_twistMonomialSection_res_cast (n : ℕ) {T : Scheme.{u}} (U : T.affineOpens)
    (a : ℤ) (e : ℕ) (ha : a = (e : ℤ)) :
    letI : Module ↥Γ(T, U.1)
        ↥Γ(Scheme.projectiveSpaceOverTwist n T a,
          Scheme.projectiveSpaceOverπ n T ⁻¹ᵁ U.1) :=
      Scheme.Modules.preimageSectionsModule (Scheme.projectiveSpaceOverπ n T)
        (Scheme.projectiveSpaceOverTwist n T a) U.1
    Submodule.span ↥Γ(T, U.1)
        (Set.range fun i : Fin ((n + e).choose n) =>
          (show ↥Γ(Scheme.projectiveSpaceOverTwist n T a,
              Scheme.projectiveSpaceOverπ n T ⁻¹ᵁ U.1) from
            (Scheme.projectiveSpaceOverTwist n T a).val.map
              ((homOfLE (le_top (a := Scheme.projectiveSpaceOverπ n T ⁻¹ᵁ U.1))).op :
                op (⊤ : (Scheme.projectiveSpaceOver n T).Opens) ⟶
                  op (Scheme.projectiveSpaceOverπ n T ⁻¹ᵁ U.1))
              (show Γ(Scheme.projectiveSpaceOverTwist n T a, ⊤) from
                ha ▸ Scheme.twistMonomialSection n T e i))) = ⊤ := by
  subst ha
  exact span_twistMonomialSection_res n U e

-- Instance search under the section-module `letI`s needs additional time.
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- Supporting API for the Quot-to-Grassmannian construction in Proposition 2.4.1: the restricted
monomial sections of the coproduct of twists span over every affine open of any base.
This is the componentwise assembly of `span_twistMonomialSection_res_cast`
through the finite-coproduct sections comparison. -/
theorem span_twistedFreeCoproduct_res (n : ℕ) {T : Scheme.{u}} (U : T.affineOpens)
    (l : ℤ) (r : ℕ) (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) :
    letI : Module ↥Γ(T, U.1)
        ↥Γ(∐ (fun _ : ULift.{u} (Fin r) =>
            Scheme.projectiveSpaceOverTwist n T ((d : ℤ) - l)),
          Scheme.projectiveSpaceOverπ n T ⁻¹ᵁ U.1) :=
      Scheme.Modules.preimageSectionsModule (Scheme.projectiveSpaceOverπ n T)
        (∐ (fun _ : ULift.{u} (Fin r) =>
          Scheme.projectiveSpaceOverTwist n T ((d : ℤ) - l))) U.1
    Submodule.span ↥Γ(T, U.1)
        (Set.range fun q : ULift.{u} (Fin r) × Fin ((n + e).choose n) =>
          (show ↥Γ(∐ (fun _ : ULift.{u} (Fin r) =>
              Scheme.projectiveSpaceOverTwist n T ((d : ℤ) - l)),
              Scheme.projectiveSpaceOverπ n T ⁻¹ᵁ U.1) from
            (∐ (fun _ : ULift.{u} (Fin r) =>
              Scheme.projectiveSpaceOverTwist n T ((d : ℤ) - l))).val.map
              ((homOfLE (le_top (a := Scheme.projectiveSpaceOverπ n T ⁻¹ᵁ U.1))).op :
                op (⊤ : (Scheme.projectiveSpaceOver n T).Opens) ⟶
                  op (Scheme.projectiveSpaceOverπ n T ⁻¹ᵁ U.1))
              (Scheme.Modules.Hom.app (Limits.Sigma.ι (fun _ : ULift.{u} (Fin r) =>
                  Scheme.projectiveSpaceOverTwist n T ((d : ℤ) - l)) q.1) ⊤
                (show Γ(Scheme.projectiveSpaceOverTwist n T ((d : ℤ) - l), ⊤) from
                  he ▸ Scheme.twistMonomialSection n T e q.2)))) = ⊤ := by
  classical
  set W := Scheme.projectiveSpaceOverπ n T ⁻¹ᵁ U.1 with hW0
  letI : Module ↥Γ(T, U.1) ↥Γ(∐ (fun _ : ULift.{u} (Fin r) =>
      Scheme.projectiveSpaceOverTwist n T ((d : ℤ) - l)), W) :=
    Scheme.Modules.preimageSectionsModule (Scheme.projectiveSpaceOverπ n T)
      (∐ (fun _ : ULift.{u} (Fin r) =>
        Scheme.projectiveSpaceOverTwist n T ((d : ℤ) - l))) U.1
  letI : Module ↥Γ(T, U.1)
      ↥Γ(Scheme.projectiveSpaceOverTwist n T ((d : ℤ) - l), W) :=
    Scheme.Modules.preimageSectionsModule (Scheme.projectiveSpaceOverπ n T)
      (Scheme.projectiveSpaceOverTwist n T ((d : ℤ) - l)) U.1
  -- the restricted single-twist monomial family
  set rct : Fin ((n + e).choose n) →
      ↥Γ(Scheme.projectiveSpaceOverTwist n T ((d : ℤ) - l), W) := fun i =>
    (Scheme.projectiveSpaceOverTwist n T ((d : ℤ) - l)).val.map
      ((homOfLE (le_top (a := W))).op : op (⊤ : (Scheme.projectiveSpaceOver n T).Opens)
        ⟶ op W)
      (show Γ(Scheme.projectiveSpaceOverTwist n T ((d : ℤ) - l), ⊤) from
        he ▸ Scheme.twistMonomialSection n T e i) with hrct
  set E2 := Scheme.Modules.openSectionsFiniteCoproductLinearEquiv W
    (fun _ : ULift.{u} (Fin r) =>
      Scheme.projectiveSpaceOverTwist n T ((d : ℤ) - l)) with hE2
  rw [_root_.eq_top_iff]
  rintro y -
  -- each component lies in the single-twist span
  have hcomp : ∀ j : ULift.{u} (Fin r),
      E2 y j ∈ Submodule.span ↥Γ(T, U.1) (Set.range rct) := by
    intro j
    have h := span_twistMonomialSection_res_cast n U ((d : ℤ) - l) e he
    exact Submodule.eq_top_iff'.mp h (E2 y j)
  have hcoef : ∀ j : ULift.{u} (Fin r),
      ∃ c : Fin ((n + e).choose n) → ↥Γ(T, U.1),
        ∑ i : Fin ((n + e).choose n), c i • rct i = E2 y j := fun j =>
    (Submodule.mem_span_range_iff_exists_fun _).mp (hcomp j)
  choose c hc using hcoef
  -- decompose `y` accordingly
  have hEy : E2 y = ∑ j : ULift.{u} (Fin r),
      ∑ i : Fin ((n + e).choose n), c j i • Pi.single j (rct i) := by
    conv_lhs => rw [← Finset.univ_sum_single (E2 y)]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_lhs => rw [← hc j]
    rw [show (Pi.single j (∑ i : Fin ((n + e).choose n), c j i • rct i) :
        ∀ _ : ULift.{u} (Fin r),
          ↥Γ(Scheme.projectiveSpaceOverTwist n T ((d : ℤ) - l), W))
      = ∑ i : Fin ((n + e).choose n), Pi.single j (c j i • rct i) from
        map_sum (LinearMap.single ↥Γ(T, U.1) (fun _ : ULift.{u} (Fin r) =>
          ↥Γ(Scheme.projectiveSpaceOverTwist n T ((d : ℤ) - l), W)) j) _ Finset.univ]
    exact Finset.sum_congr rfl fun i _ =>
      map_smul (LinearMap.single ↥Γ(T, U.1) (fun _ : ULift.{u} (Fin r) =>
        ↥Γ(Scheme.projectiveSpaceOverTwist n T ((d : ℤ) - l), W)) j) (c j i) (rct i)
  -- pull the decomposition back through the comparison
  have hyeq : y = ∑ j : ULift.{u} (Fin r), ∑ i : Fin ((n + e).choose n),
      c j i • E2.symm (Pi.single j (rct i)) := by
    conv_lhs => rw [← LinearEquiv.symm_apply_apply E2 y, hEy]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    show E2.symm ((((Scheme.projectiveSpaceOverπ n T).app U.1).hom (c j i)) •
      Pi.single j (rct i)) = _
    rw [map_smul]
    rfl
  -- the pulled-back single tuples are the coproduct monomial sections
  have hsingle : ∀ (j : ULift.{u} (Fin r)) (i : Fin ((n + e).choose n)),
      E2.symm (Pi.single j (rct i))
        = (∐ (fun _ : ULift.{u} (Fin r) =>
            Scheme.projectiveSpaceOverTwist n T ((d : ℤ) - l))).val.map
            ((homOfLE (le_top (a := W))).op :
              op (⊤ : (Scheme.projectiveSpaceOver n T).Opens) ⟶ op W)
            (Scheme.Modules.Hom.app (Limits.Sigma.ι
                (fun _ : ULift.{u} (Fin r) =>
                  Scheme.projectiveSpaceOverTwist n T ((d : ℤ) - l)) j) ⊤
              (show Γ(Scheme.projectiveSpaceOverTwist n T ((d : ℤ) - l), ⊤) from
                he ▸ Scheme.twistMonomialSection n T e i)) := by
    intro j i
    have hnat := Scheme.Modules.app_top_restrict
      (Limits.Sigma.ι (fun _ : ULift.{u} (Fin r) =>
        Scheme.projectiveSpaceOverTwist n T ((d : ℤ) - l)) j) W
      (show Γ(Scheme.projectiveSpaceOverTwist n T ((d : ℤ) - l), ⊤) from
        he ▸ Scheme.twistMonomialSection n T e i)
    rw [hnat]
    have hι := Scheme.Modules.openSectionsFiniteCoproductLinearEquiv_ι W
      (fun _ : ULift.{u} (Fin r) =>
        Scheme.projectiveSpaceOverTwist n T ((d : ℤ) - l)) j (rct i)
    rw [← hι, LinearEquiv.symm_apply_apply]
  rw [hyeq]
  refine Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun i _ => ?_
  refine Submodule.smul_mem _ (c j i) (Submodule.subset_span ?_)
  refine ⟨(j, i), ?_⟩
  exact (hsingle j i).symm

-- Instance search under the section-module `letI`s needs additional time.
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- Supporting API for the Quot-to-Grassmannian construction in Proposition 2.4.1: monomial spanning
of the ambient twisted-free sheaf over every affine open of any base, namely the `hmono`
hypothesis of `surjective_finFreeSectionsMap'_quotMonomial`. The
coproduct-of-twists statement `span_twistedFreeCoproduct_res` is conjugated by the
coproduct-twist identification `F(d) ≅ 𝒪(d-l)^{⊕r}` on the base `T` itself. -/
theorem surjective_finFreeSectionsMap'_twistedFreeMonomial
    (n : ℕ) {T : Scheme.{u}} (l : ℤ) (r : ℕ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {m : ℕ}
    (σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n))
    (U : T.affineOpens) :
    Function.Surjective (Scheme.Modules.finFreeSectionsMap'
      (Scheme.Modules.freeHomOfSections
        (M := (Scheme.Modules.pushforward (Scheme.projectiveSpaceOverπ n T)).obj
          (Scheme.projectiveSpaceOverTwistModule
            (∐ fun _ : ULift.{u} (Fin r) =>
              Scheme.projectiveSpaceOverTwist n T (-l)) (d : ℤ)))
        (fun k : ULift.{u} (Fin m) =>
          Scheme.twistedFreeMonomialSection n T l r d e he (σ k).1 (σ k).2))
      U.1) := by
  classical
  rw [Scheme.Modules.surjective_finFreeSectionsMap'_iff, _root_.eq_top_iff]
  rintro y -
  set W := Scheme.projectiveSpaceOverπ n T ⁻¹ᵁ U.1 with hW0
  set ν := Scheme.projectiveSpaceOverNegativeTwist_coproduct_twistIso_nat
    (J := ULift.{u} (Fin r)) n T l d with hν
  letI : Module ↥Γ(T, U.1)
      ↥Γ(Scheme.projectiveSpaceOverTwistModule
        (∐ fun _ : ULift.{u} (Fin r) =>
          Scheme.projectiveSpaceOverTwist n T (-l)) (d : ℤ), W) :=
    Scheme.Modules.preimageSectionsModule (Scheme.projectiveSpaceOverπ n T)
      (Scheme.projectiveSpaceOverTwistModule
        (∐ fun _ : ULift.{u} (Fin r) =>
          Scheme.projectiveSpaceOverTwist n T (-l)) (d : ℤ)) U.1
  letI : Module ↥Γ(T, U.1) ↥Γ(∐ (fun _ : ULift.{u} (Fin r) =>
      Scheme.projectiveSpaceOverTwist n T ((d : ℤ) - l)), W) :=
    Scheme.Modules.preimageSectionsModule (Scheme.projectiveSpaceOverπ n T)
      (∐ (fun _ : ULift.{u} (Fin r) =>
        Scheme.projectiveSpaceOverTwist n T ((d : ℤ) - l))) U.1
  letI : Module ↥Γ(T, U.1)
      ↥Γ(Scheme.Modules.tensor
        (∐ fun _ : ULift.{u} (Fin r) => Scheme.projectiveSpaceOverTwist n T (-l))
        (Scheme.projectiveSpaceOverTwist n T (d : ℤ)), W) :=
    Scheme.Modules.preimageSectionsModule (Scheme.projectiveSpaceOverπ n T)
      (Scheme.Modules.tensor
        (∐ fun _ : ULift.{u} (Fin r) => Scheme.projectiveSpaceOverTwist n T (-l))
        (Scheme.projectiveSpaceOverTwist n T (d : ℤ))) U.1
  -- the restricted coproduct monomial family of `span_twistedFreeCoproduct_res`
  set fam2 : ULift.{u} (Fin r) × Fin ((n + e).choose n) →
      ↥Γ(∐ (fun _ : ULift.{u} (Fin r) =>
        Scheme.projectiveSpaceOverTwist n T ((d : ℤ) - l)), W) := fun q =>
    (∐ (fun _ : ULift.{u} (Fin r) =>
      Scheme.projectiveSpaceOverTwist n T ((d : ℤ) - l))).val.map
      ((homOfLE (le_top (a := W))).op :
        op (⊤ : (Scheme.projectiveSpaceOver n T).Opens) ⟶ op W)
      (Scheme.Modules.Hom.app (Limits.Sigma.ι (fun _ : ULift.{u} (Fin r) =>
          Scheme.projectiveSpaceOverTwist n T ((d : ℤ) - l)) q.1) ⊤
        (show Γ(Scheme.projectiveSpaceOverTwist n T ((d : ℤ) - l), ⊤) from
          he ▸ Scheme.twistMonomialSection n T e q.2)) with hfam2
  -- the restricted ambient monomial family
  set mres : ULift.{u} (Fin r) × Fin ((n + e).choose n) →
      ↥Γ(Scheme.projectiveSpaceOverTwistModule
        (∐ fun _ : ULift.{u} (Fin r) =>
          Scheme.projectiveSpaceOverTwist n T (-l)) (d : ℤ), W) := fun q =>
    (Scheme.projectiveSpaceOverTwistModule
      (∐ fun _ : ULift.{u} (Fin r) =>
        Scheme.projectiveSpaceOverTwist n T (-l)) (d : ℤ)).val.map
      ((homOfLE (le_top (a := W))).op :
        op (⊤ : (Scheme.projectiveSpaceOver n T).Opens) ⟶ op W)
      (Scheme.twistedFreeMonomialSection n T l r d e he q.1 q.2) with hmres
  -- the coproduct-twist conjugation carries one family to the other
  have hβfam : ∀ q : ULift.{u} (Fin r) × Fin ((n + e).choose n),
      Scheme.Modules.Hom.app ν.hom W (mres q) = fam2 q := by
    intro q
    have hres := (Scheme.Modules.app_top_restrict ν.hom W
      (Scheme.twistedFreeMonomialSection n T l r d e he q.1 q.2)).symm
    refine hres.trans ?_
    have hcancel := congrArg (fun k :
        (∐ (fun _ : ULift.{u} (Fin r) =>
          Scheme.projectiveSpaceOverTwist n T ((d : ℤ) - l))) ⟶
        (∐ (fun _ : ULift.{u} (Fin r) =>
          Scheme.projectiveSpaceOverTwist n T ((d : ℤ) - l))) =>
      (PresheafOfModules.Hom.app k.val (op (⊤ :
          (Scheme.projectiveSpaceOver n T).Opens))).hom
        (Scheme.Modules.Hom.app (Limits.Sigma.ι (fun _ : ULift.{u} (Fin r) =>
            Scheme.projectiveSpaceOverTwist n T ((d : ℤ) - l)) q.1) ⊤
          (show Γ(Scheme.projectiveSpaceOverTwist n T ((d : ℤ) - l), ⊤) from
            he ▸ Scheme.twistMonomialSection n T e q.2))) ν.inv_hom_id
    exact congrArg ((∐ (fun _ : ULift.{u} (Fin r) =>
      Scheme.projectiveSpaceOverTwist n T ((d : ℤ) - l))).val.map
      ((homOfLE (le_top (a := W))).op :
        op (⊤ : (Scheme.projectiveSpaceOver n T).Opens) ⟶ op W)) hcancel
  -- the coproduct span applied to the conjugated section
  have h2span := span_twistedFreeCoproduct_res n U l r d e he
  have hmemz : Scheme.Modules.Hom.app ν.hom W y
      ∈ Submodule.span ↥Γ(T, U.1) (Set.range fam2) :=
    Submodule.eq_top_iff'.mp h2span (Scheme.Modules.Hom.app ν.hom W y)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hmemz
  -- the packaged linear conjugation
  let βlin := Scheme.Modules.hom_app_preimage_linearMap
    (Scheme.projectiveSpaceOverπ n T) ν.hom U.1
  have hβsum : βlin (∑ q : ULift.{u} (Fin r) × Fin ((n + e).choose n),
      c q • mres q) = Scheme.Modules.Hom.app ν.hom W y := by
    rw [map_sum]
    refine Eq.trans (Finset.sum_congr rfl fun q _ => ?_) hc
    rw [map_smul]
    exact congrArg (fun z => c q • z) (hβfam q)
  -- injectivity of the conjugation
  have hβinj : Function.Injective
      (fun z : ↥Γ(Scheme.projectiveSpaceOverTwistModule
        (∐ fun _ : ULift.{u} (Fin r) =>
          Scheme.projectiveSpaceOverTwist n T (-l)) (d : ℤ), W) =>
        Scheme.Modules.Hom.app ν.hom W z) := by
    intro v w hvw
    have hv := congrArg (fun k :
        Scheme.projectiveSpaceOverTwistModule
          (∐ fun _ : ULift.{u} (Fin r) =>
            Scheme.projectiveSpaceOverTwist n T (-l)) (d : ℤ) ⟶
        Scheme.projectiveSpaceOverTwistModule
          (∐ fun _ : ULift.{u} (Fin r) =>
            Scheme.projectiveSpaceOverTwist n T (-l)) (d : ℤ) =>
      (PresheafOfModules.Hom.app k.val (op W)).hom v) ν.hom_inv_id
    have hw := congrArg (fun k :
        Scheme.projectiveSpaceOverTwistModule
          (∐ fun _ : ULift.{u} (Fin r) =>
            Scheme.projectiveSpaceOverTwist n T (-l)) (d : ℤ) ⟶
        Scheme.projectiveSpaceOverTwistModule
          (∐ fun _ : ULift.{u} (Fin r) =>
            Scheme.projectiveSpaceOverTwist n T (-l)) (d : ℤ) =>
      (PresheafOfModules.Hom.app k.val (op W)).hom w) ν.hom_inv_id
    have hmid := congrArg (fun z => Scheme.Modules.Hom.app ν.inv W z) hvw
    exact hv.symm.trans (hmid.trans hw)
  -- recover the combination for `y`
  have hyeq : y = ∑ q : ULift.{u} (Fin r) × Fin ((n + e).choose n),
      c q • mres q := by
    refine (hβinj ?_).symm
    exact hβsum
  -- generators
  have hgen : ∀ q : ULift.{u} (Fin r) × Fin ((n + e).choose n),
      Scheme.Modules.freeGen (Scheme.Modules.freeHomOfSections
        (M := (Scheme.Modules.pushforward (Scheme.projectiveSpaceOverπ n T)).obj
          (Scheme.projectiveSpaceOverTwistModule
            (∐ fun _ : ULift.{u} (Fin r) =>
              Scheme.projectiveSpaceOverTwist n T (-l)) (d : ℤ)))
        (fun k : ULift.{u} (Fin m) =>
          Scheme.twistedFreeMonomialSection n T l r d e he (σ k).1 (σ k).2))
        U.1 ((σ.symm q).down)
      = mres q := by
    intro q
    rw [Scheme.Modules.freeGen_freeHomOfSections]
    have h3 := congrArg (fun z : ULift.{u} (Fin r) × Fin ((n + e).choose n) =>
      mres z) (σ.apply_symm_apply q)
    exact h3
  rw [hyeq]
  refine Submodule.sum_mem _ fun q _ => ?_
  exact Submodule.smul_mem _ (c q)
    (Submodule.subset_span ⟨(σ.symm q).down, hgen q⟩)

-- Instance search under the section-module `letI`s needs additional time.
set_option synthInstance.maxHeartbeats 1000000 in
/-- Supporting API for the Quot-to-Grassmannian construction in Proposition 2.4.1: uniform
surjectivity of its free map on affine sections. For a twisted-free presentation of a flat
family with fibrewise Hilbert polynomial `P`
over a locally noetherian base `T` and any natural twist `d ≥ d₁(n, l, r, P)`, the free
map cut out by the monomial sections of `Q(d)` is surjective on sections over every
affine open of the base.  This is the `hsurj` input of the Grassmannian point of the
Quot functor. -/
theorem exists_bound_surjective_finFreeSectionsMap_quotGrassmannian
    (n r : ℕ) (l : ℤ) (P : Polynomial ℚ) :
    ∃ d₁ : ℤ, 0 ≤ d₁ ∧ ∀ (T : Scheme.{u}) [IsLocallyNoetherian T]
      (Q : (Scheme.projectiveSpaceOver n T).Modules)
      (_ : Q.IsFinitePresentation)
      (ψ : (∐ fun _ : ULift.{u} (Fin r) =>
        Scheme.projectiveSpaceOverTwist n T (-l)) ⟶ Q)
      (_ : Epi ψ)
      (_ : Q.FlatOver (Scheme.projectiveSpaceOverπ n T))
      (_ : Scheme.HasFiberwiseHilbertPolynomial Q P)
      (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)), d₁ ≤ (d : ℤ) →
      ∀ {m : ℕ} (σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n))
        (U : T.affineOpens),
      Function.Surjective (Scheme.Modules.finFreeSectionsMap'
        (Scheme.Modules.freeHomOfSections
          (M := (Scheme.Modules.pushforward (Scheme.projectiveSpaceOverπ n T)).obj
            (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ)))
          (fun i : ULift.{u} (Fin m) =>
            Scheme.quotMonomialSection n T l r ψ d e he (σ i).1 (σ i).2)) U.1) := by
  obtain ⟨d₁, hd₁0, hd₁⟩ := exists_bound_surjective_twist_app_preimage.{u} n r l P
  refine ⟨d₁, hd₁0, ?_⟩
  intro T _ Q hQfp ψ hψ hflat hHP d e he hd m σ U
  refine Scheme.surjective_finFreeSectionsMap'_quotMonomial l r ψ d e he σ U ?_ ?_
  · exact surjective_finFreeSectionsMap'_twistedFreeMonomial n l r d e he σ U
  · exact hd₁ T Q hQfp ψ hψ hflat hHP (d : ℤ) hd U

end AlgebraicGeometry.ProjectiveSpace

end
