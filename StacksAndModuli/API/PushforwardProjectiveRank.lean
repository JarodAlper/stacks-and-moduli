module

public import StacksAndModuli.API.SheafFlatteningImmersion
public import StacksAndModuli.API.OpenImmersionModuleBaseChange

/-!
# Local freeness of a pushforward, checked on preimages of affine opens

For the Grassmannian step of §2.4 one needs `π_*(Q(d))` to be locally free of rank `P(d)` on
the base, where `π : ℙⁿ_T → T`.  `AlgebraicGeometry.Scheme.IsProjectiveOfRank` is *by
definition* a condition on the sections over affine opens of the base, and the sections of a
pushforward over `U` are, definitionally, the sections of the sheaf over `π ⁻¹ᵁ U`.  This file
records that reduction.

The `Γ(T,U)`-module structure has to be taken through the pushforward — there is no
`Module Γ(T,U) Γ(G, π ⁻¹ᵁ U)` instance — which is what
`AlgebraicGeometry.Scheme.Modules.preimageSectionsModule` supplies; it is definitionally the
structure carried by `Γ(π_*G, U)`, which is why the reduction is an `exact`.

**What is still missing** for the Grassmannian step, and is *not* in this file: the
identification, for an affine open `U` of `T`,

```
Γ(G, π ⁻¹ᵁ U)  ≅  Γ((Modules.pullback (projectiveSpaceOverMap n U.ι)).obj G, ⊤)
```

as `Γ(T,U)`-modules — the same manoeuvre as
`Scheme.Modules.pullbackOpenImageTopSectionsLinearEquiv` in
`API/AffineOpenGlobalSectionsBaseChange.lean` — which turns the affine input
`Scheme.Modules.HasEventualFiniteProjectiveGlobalSectionsBaseChange` into the hypothesis of
`isProjectiveOfRank_pushforward`.  `projectiveSpaceOverMap n U.ι` is an open immersion
(instance) onto `π ⁻¹ᵁ U`, and
`Scheme.projectiveSpaceOverTwistModule_pullbackIso_of_isOpenImmersion` already commutes the
twist past it.

Main declarations:

* `AlgebraicGeometry.Scheme.Modules.preimageSectionsModule`;
* `AlgebraicGeometry.Scheme.Modules.isProjectiveOfRank_pushforward`;
* `AlgebraicGeometry.Scheme.isPullback_projectiveSpaceOverMap` and
  `AlgebraicGeometry.Scheme.projectiveSpaceOverOpenIso` — `ℙⁿ_{U} ≅ π ⁻¹ᵁ U`;
* `AlgebraicGeometry.Scheme.projectiveSpaceOverAffineOpenIso` — the same with the base
  `Spec Γ(T, U)`, so that the ring is the one `IsProjectiveOfRank` and the affine
  base-change theory both speak about;
* `AlgebraicGeometry.Scheme.range_projectiveSpaceOverMap_ι` and
  `…projectiveSpaceOverMap_image_preimage` — the opens-level cartesianity of the
  base-change square;
* `AlgebraicGeometry.Scheme.projectiveSpacePushforwardRestrictIso` — pushforward along
  `ℙⁿ → base` commutes with restriction to an open of the base;
* `AlgebraicGeometry.Scheme.isProjectiveOfRank_pushforward_projectiveSpace` — **local
  freeness of `π_*G` reduces to affine opens of the base**, which is where
  `Modules.HasEventualFiniteProjectiveGlobalSectionsBaseChange` lives;
* `AlgebraicGeometry.Scheme.isProjectiveOfRank_pushforward_projectiveSpace_of_top` — the same
  reduction stated directly in terms of **global sections over each affine open of the base**.

* `AlgebraicGeometry.Scheme.isProjectiveOfRank_pushforward_spec` — the affine-base case, in
  exactly the `Modules.globalSectionsModule` convention of
  `Modules.HasEventualFiniteProjectiveGlobalSectionsBaseChange`;
* `AlgebraicGeometry.Scheme.range_projectiveSpaceOverMap`,
  `…projectiveSpaceOverMap_image_preimage'` and `…projectiveSpacePushforwardRestrictIso'` — the
  same for an arbitrary open immersion of bases;
* `AlgebraicGeometry.Scheme.isProjectiveOfRank_pushforward_of_isAffine`;
* **`AlgebraicGeometry.Scheme.isProjectiveOfRank_pushforward_of_globalSections`** — the full
  bridge: `π_*G` is locally free of rank `q` on an *arbitrary* base as soon as, for every
  affine open `U` of the base, the global sections of `G` restricted to `ℙⁿ_{Spec Γ(U,⊤)}` are
  finite projective of rank `q`.

No comparison of section modules is needed anywhere: the base change is
`Modules.restrictPushforwardIsoOfOpenSquare` (already in
`API/OpenImmersionModuleBaseChange.lean`), the descent is
`Modules.IsProjectiveOfRank.of_affineOpen_pullbacks`, and the affine case is
`Modules.isProjectiveOfRank_of_top`.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- The `Γ(T,U)`-module structure on the sections of `G` over `π ⁻¹ᵁ U`, taken through
`π.app U`.  This is definitionally the structure that `Γ((pushforward π).obj G, U)` carries. -/
abbrev preimageSectionsModule {Y T : Scheme.{u}} (π : Y ⟶ T) (G : Y.Modules) (U : T.Opens) :
    Module ↥Γ(T, U) ↥Γ(G, π ⁻¹ᵁ U) :=
  Module.compHom _ (π.app U).hom

/-- **`IsProjectiveOfRank` for a pushforward** is a condition on the sections of `G` over the
preimages of affine opens of the base. -/
theorem isProjectiveOfRank_pushforward {Y T : Scheme.{u}} (π : Y ⟶ T) (G : Y.Modules) (q : ℕ)
    (h : ∀ x : T, ∃ U : T.affineOpens, x ∈ U.1 ∧
      (letI := preimageSectionsModule π G U.1
       Module.Finite ↥Γ(T, U.1) ↥Γ(G, π ⁻¹ᵁ U.1) ∧
       Module.Projective ↥Γ(T, U.1) ↥Γ(G, π ⁻¹ᵁ U.1) ∧
       ∀ p : PrimeSpectrum ↥Γ(T, U.1),
         Module.rankAtStalk (R := ↥Γ(T, U.1)) ↥Γ(G, π ⁻¹ᵁ U.1) p = q)) :
    IsProjectiveOfRank q ((Modules.pushforward π).obj G) := by
  intro x
  obtain ⟨U, hxU, hfin, hproj, hrank⟩ := h x
  exact ⟨U, hxU, hfin, hproj, hrank⟩

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

/-- **Relative projective space is a base change**: the square

```
ℙⁿ_T --projectiveSpaceOverMap n g--> ℙⁿ_S
 |                                    |
 π_T                                  π_S
 v                                    v
 T ------------ g ----------------->  S
```

is cartesian.  This is `Scheme.projectiveSpaceOverBaseChangeIso` read as an `IsPullback`. -/
theorem isPullback_projectiveSpaceOverMap (n : ℕ) {S T : Scheme.{u}} (g : T ⟶ S) :
    IsPullback (Scheme.projectiveSpaceOverπ n T) (Scheme.projectiveSpaceOverMap n g)
      g (Scheme.projectiveSpaceOverπ n S) := by
  refine IsPullback.of_iso_pullback ⟨?_⟩ (Scheme.projectiveSpaceOverBaseChangeIso n g).symm ?_ ?_
  · exact (Scheme.projectiveSpaceOverMap_π n g).symm
  · change (Scheme.projectiveSpaceOverBaseChangeIso n g).inv ≫ Limits.pullback.fst _ _ = _
    rw [← Scheme.projectiveSpaceOverBaseChangeIso_hom_π, Iso.inv_hom_id_assoc]
  · change (Scheme.projectiveSpaceOverBaseChangeIso n g).inv ≫ Limits.pullback.snd _ _ = _
    rw [← Scheme.projectiveSpaceOverBaseChangeIso_hom_map, Iso.inv_hom_id_assoc]

/-- **The projective space over an open subscheme of the base is the preimage open.**  Both
sides are the base change of `π : ℙⁿ_T → T` along `U.ι`, so they agree by uniqueness of
pullbacks; `isPullback_morphismRestrict` supplies the second square. -/
def projectiveSpaceOverOpenIso (n : ℕ) {T : Scheme.{u}} (U : T.Opens) :
    Scheme.projectiveSpaceOver n U.toScheme ≅
      ((Scheme.projectiveSpaceOverπ n T) ⁻¹ᵁ U).toScheme :=
  (isPullback_projectiveSpaceOverMap n U.ι).isoIsPullback _ _
    (isPullback_morphismRestrict (Scheme.projectiveSpaceOverπ n T) U)

@[reassoc]
lemma projectiveSpaceOverOpenIso_hom_ι (n : ℕ) {T : Scheme.{u}} (U : T.Opens) :
    (projectiveSpaceOverOpenIso n U).hom ≫ ((Scheme.projectiveSpaceOverπ n T) ⁻¹ᵁ U).ι =
      Scheme.projectiveSpaceOverMap n U.ι :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

instance projectiveSpaceOverMap_isIso (n : ℕ) {S T : Scheme.{u}} (g : T ⟶ S) [IsIso g] :
    IsIso (Scheme.projectiveSpaceOverMap n g) :=
  (isPullback_projectiveSpaceOverMap n g).isIso_snd_of_isIso

/-- **`ℙⁿ` over the spectrum of the sections of an affine open, compared with the preimage
open.**  This is the comparison in which the *ring* is `Γ(T, U)` on the nose — the module
structures of `Modules.HasEventualFiniteProjectiveGlobalSectionsBaseChange` are over exactly
that ring, so no transport along `Scheme.Opens.topIso` is needed anywhere. -/
def projectiveSpaceOverAffineOpenIso (n : ℕ) {T : Scheme.{u}} (U : T.affineOpens) :
    Scheme.projectiveSpaceOver n (Spec Γ(T, U.1)) ≅
      ((Scheme.projectiveSpaceOverπ n T) ⁻¹ᵁ U.1).toScheme :=
  asIso (Scheme.projectiveSpaceOverMap n U.2.isoSpec.inv) ≪≫
    projectiveSpaceOverOpenIso n U.1

@[reassoc]
lemma projectiveSpaceOverAffineOpenIso_hom_ι (n : ℕ) {T : Scheme.{u}} (U : T.affineOpens) :
    (projectiveSpaceOverAffineOpenIso n U).hom ≫
        ((Scheme.projectiveSpaceOverπ n T) ⁻¹ᵁ U.1).ι =
      Scheme.projectiveSpaceOverMap n (U.2.isoSpec.inv ≫ U.1.ι) := by
  change (Scheme.projectiveSpaceOverMap n U.2.isoSpec.inv ≫
    (projectiveSpaceOverOpenIso n U.1).hom) ≫ _ = _
  rw [Category.assoc, projectiveSpaceOverOpenIso_hom_ι,
    ← Scheme.projectiveSpaceOverMap_comp]

/-- The range of the projective-space base-change map along an open immersion. -/
lemma range_projectiveSpaceOverMap_ι (n : ℕ) {T : Scheme.{u}} (U : T.Opens) :
    Set.range (Scheme.projectiveSpaceOverMap n U.ι).base =
      ((Scheme.projectiveSpaceOverπ n T) ⁻¹ᵁ U : Set _) := by
  rw [← projectiveSpaceOverOpenIso_hom_ι n U, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp]
  rw [Set.range_eq_univ.mpr (fun y => ?_), Set.image_univ, Scheme.Opens.range_ι]
  exact ⟨(projectiveSpaceOverOpenIso n U).inv.base y, by
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl⟩

/-- Opens-level cartesianity of the projective-space base-change square. -/
lemma projectiveSpaceOverMap_image_preimage (n : ℕ) {T : Scheme.{u}} (U : T.Opens)
    (W : U.toScheme.Opens) :
    (Scheme.projectiveSpaceOverMap n U.ι) ''ᵁ
        ((Scheme.projectiveSpaceOverπ n U.toScheme) ⁻¹ᵁ W) =
      (Scheme.projectiveSpaceOverπ n T) ⁻¹ᵁ (U.ι ''ᵁ W) := by
  have hsq := Scheme.projectiveSpaceOverMap_π n U.ι
  apply TopologicalSpace.Opens.ext
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(Scheme.projectiveSpaceOverπ n U.toScheme).base y, hy, ?_⟩
    change (Scheme.projectiveSpaceOverπ n U.toScheme ≫ U.ι).base y = _
    rw [← hsq, Scheme.Hom.comp_base]
    rfl
  · rintro ⟨u, hu, hux⟩
    have hxU : x ∈ ((Scheme.projectiveSpaceOverπ n T) ⁻¹ᵁ U : Set _) := by
      change (Scheme.projectiveSpaceOverπ n T).base x ∈ U
      rw [← hux]
      exact u.2
    rw [← range_projectiveSpaceOverMap_ι n U] at hxU
    obtain ⟨y, rfl⟩ := hxU
    refine ⟨y, ?_, rfl⟩
    change (Scheme.projectiveSpaceOverπ n U.toScheme).base y ∈ W
    have : U.ι.base ((Scheme.projectiveSpaceOverπ n U.toScheme).base y) = U.ι.base u := by
      change (Scheme.projectiveSpaceOverπ n U.toScheme ≫ U.ι).base y = _
      rw [← hsq]
      exact hux.symm
    have hinj : Function.Injective U.ι.base := (U.ι.isOpenEmbedding).injective
    rw [hinj this]
    exact hu

/-- **Pushforward along `ℙⁿ → base` commutes with restriction to an open of the base.** -/
def projectiveSpacePushforwardRestrictIso (n : ℕ) {T : Scheme.{u}} (U : T.Opens)
    (G : (Scheme.projectiveSpaceOver n T).Modules) :
    (Modules.restrictFunctor U.ι).obj
        ((Modules.pushforward (Scheme.projectiveSpaceOverπ n T)).obj G) ≅
      (Modules.pushforward (Scheme.projectiveSpaceOverπ n U.toScheme)).obj
        ((Modules.restrictFunctor (Scheme.projectiveSpaceOverMap n U.ι)).obj G) :=
  Modules.restrictPushforwardIsoOfOpenSquare
    (Scheme.projectiveSpaceOverπ n T) (Scheme.projectiveSpaceOverπ n U.toScheme)
    (Scheme.projectiveSpaceOverMap n U.ι) U.ι
    (Scheme.projectiveSpaceOverMap_π n U.ι).symm
    (projectiveSpaceOverMap_image_preimage n U) G

/-- **Local freeness of `π_*G` reduces to the affine opens of the base.** -/
theorem isProjectiveOfRank_pushforward_projectiveSpace (n : ℕ) {T : Scheme.{u}}
    (G : (Scheme.projectiveSpaceOver n T).Modules) (q : ℕ)
    (h : ∀ U : T.affineOpens, Modules.IsProjectiveOfRank q
      ((Modules.pushforward (Scheme.projectiveSpaceOverπ n U.1.toScheme)).obj
        ((Modules.restrictFunctor (Scheme.projectiveSpaceOverMap n U.1.ι)).obj G))) :
    Modules.IsProjectiveOfRank q
      ((Modules.pushforward (Scheme.projectiveSpaceOverπ n T)).obj G) := by
  apply Modules.IsProjectiveOfRank.of_affineOpen_pullbacks
  intro U
  refine Modules.IsProjectiveOfRank.of_iso ?_ (h U)
  exact ((projectiveSpacePushforwardRestrictIso n U.1 G).symm.trans
    ((Modules.restrictFunctorIsoPullback U.1.ι).app _))

/-- The restriction of `G` to `ℙⁿ` over an affine open of the base. -/
abbrev projectiveSpaceRestrictOverAffine (n : ℕ) {T : Scheme.{u}} (U : T.affineOpens)
    (G : (Scheme.projectiveSpaceOver n T).Modules) :
    (Scheme.projectiveSpaceOver n U.1.toScheme).Modules :=
  (Modules.restrictFunctor (Scheme.projectiveSpaceOverMap n U.1.ι)).obj G

/-- **Local freeness of `π_*G` from global sections over each affine open of the base.** -/
theorem isProjectiveOfRank_pushforward_projectiveSpace_of_top (n : ℕ) {T : Scheme.{u}}
    (G : (Scheme.projectiveSpaceOver n T).Modules) (q : ℕ)
    (hfin : ∀ U : T.affineOpens, Module.Finite ↥Γ(U.1.toScheme, ⊤)
      ↥Γ((Modules.pushforward (Scheme.projectiveSpaceOverπ n U.1.toScheme)).obj
        (projectiveSpaceRestrictOverAffine n U G), ⊤))
    (hproj : ∀ U : T.affineOpens, Module.Projective ↥Γ(U.1.toScheme, ⊤)
      ↥Γ((Modules.pushforward (Scheme.projectiveSpaceOverπ n U.1.toScheme)).obj
        (projectiveSpaceRestrictOverAffine n U G), ⊤))
    (hrank : ∀ (U : T.affineOpens) (p : PrimeSpectrum ↥Γ(U.1.toScheme, ⊤)),
      Module.rankAtStalk (R := ↥Γ(U.1.toScheme, ⊤))
        ↥Γ((Modules.pushforward (Scheme.projectiveSpaceOverπ n U.1.toScheme)).obj
          (projectiveSpaceRestrictOverAffine n U G), ⊤) p = q) :
    Modules.IsProjectiveOfRank q
      ((Modules.pushforward (Scheme.projectiveSpaceOverπ n T)).obj G) := by
  refine isProjectiveOfRank_pushforward_projectiveSpace n G q (fun U => ?_)
  haveI : IsAffine U.1.toScheme := U.2
  exact Modules.isProjectiveOfRank_of_top (hfin U) (hproj U) (hrank U)

/-- Over an affine base, local freeness of `π_*Q` is finite projectivity of the module of
global sections in the `Modules.globalSectionsModule` convention. -/
theorem isProjectiveOfRank_pushforward_spec (n : ℕ) (R : CommRingCat.{u})
    (Q : (Scheme.projectiveSpaceOver n (Spec R)).Modules) (q : ℕ)
    (hfin : letI := Modules.globalSectionsModule (Scheme.projectiveSpaceOverπ n (Spec R)) Q
      Module.Finite R ↥Γ(Q, ⊤))
    (hproj : letI := Modules.globalSectionsModule (Scheme.projectiveSpaceOverπ n (Spec R)) Q
      Module.Projective R ↥Γ(Q, ⊤))
    (hrank : letI := Modules.globalSectionsModule (Scheme.projectiveSpaceOverπ n (Spec R)) Q
      ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) ↥Γ(Q, ⊤) p = q) :
    Modules.IsProjectiveOfRank q
      ((Modules.pushforward (Scheme.projectiveSpaceOverπ n (Spec R))).obj Q) := by
  obtain ⟨hfin', hproj', hrank'⟩ :=
    moduleSpecΓFunctor_finite_projective_rank_top
      ((Modules.pushforward (Scheme.projectiveSpaceOverπ n (Spec R))).obj Q)
      hfin hproj hrank
  exact Modules.isProjectiveOfRank_of_top hfin' hproj' hrank'

lemma range_projectiveSpaceOverMap (n : ℕ) {T T' : Scheme.{u}} (j : T' ⟶ T)
    [IsOpenImmersion j] :
    Set.range (Scheme.projectiveSpaceOverMap n j).base =
      ((Scheme.projectiveSpaceOverπ n T) ⁻¹ᵁ j.opensRange : Set _) := by
  have hrange : Set.range j.base = Set.range (j.opensRange).ι.base := by
    rw [Scheme.Opens.range_ι]; rfl
  let e : T' ≅ (j.opensRange).toScheme :=
    IsOpenImmersion.isoOfRangeEq j (j.opensRange).ι hrange
  have hj : e.hom ≫ (j.opensRange).ι = j := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hmap : Scheme.projectiveSpaceOverMap n j =
      Scheme.projectiveSpaceOverMap n e.hom ≫
        Scheme.projectiveSpaceOverMap n (j.opensRange).ι := by
    rw [Scheme.projectiveSpaceOverMap_comp, hj]
  have hsurj : Set.range ⇑(Scheme.projectiveSpaceOverMap n e.hom).base = Set.univ := by
    refine Set.range_eq_univ.mpr (fun y => ?_)
    exact ⟨(inv (Scheme.projectiveSpaceOverMap n e.hom)).base y, by
      rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
  rw [hmap, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hsurj, Set.image_univ,
    range_projectiveSpaceOverMap_ι n j.opensRange]

lemma projectiveSpaceOverMap_image_preimage' (n : ℕ) {T T' : Scheme.{u}} (j : T' ⟶ T)
    [IsOpenImmersion j] (W : T'.Opens) :
    (Scheme.projectiveSpaceOverMap n j) ''ᵁ
        ((Scheme.projectiveSpaceOverπ n T') ⁻¹ᵁ W) =
      (Scheme.projectiveSpaceOverπ n T) ⁻¹ᵁ (j ''ᵁ W) := by
  have hsq := Scheme.projectiveSpaceOverMap_π n j
  apply TopologicalSpace.Opens.ext
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(Scheme.projectiveSpaceOverπ n T').base y, hy, ?_⟩
    change (Scheme.projectiveSpaceOverπ n T' ≫ j).base y = _
    rw [← hsq, Scheme.Hom.comp_base]
    rfl
  · rintro ⟨u, hu, hux⟩
    have hxU : x ∈ ((Scheme.projectiveSpaceOverπ n T) ⁻¹ᵁ j.opensRange : Set _) := by
      change (Scheme.projectiveSpaceOverπ n T).base x ∈ j.opensRange
      rw [← hux]
      exact ⟨u, rfl⟩
    rw [← range_projectiveSpaceOverMap n j] at hxU
    obtain ⟨y, rfl⟩ := hxU
    refine ⟨y, ?_, rfl⟩
    change (Scheme.projectiveSpaceOverπ n T').base y ∈ W
    have hkey : j.base ((Scheme.projectiveSpaceOverπ n T').base y) = j.base u := by
      change (Scheme.projectiveSpaceOverπ n T' ≫ j).base y = _
      rw [← hsq]
      exact hux.symm
    have hinj : Function.Injective j.base := (j.isOpenEmbedding).injective
    rw [hinj hkey]
    exact hu

/-- Pushforward along `ℙⁿ → base` commutes with restriction along any open immersion of
bases. -/
def projectiveSpacePushforwardRestrictIso' (n : ℕ) {T T' : Scheme.{u}} (j : T' ⟶ T)
    [IsOpenImmersion j] (G : (Scheme.projectiveSpaceOver n T).Modules) :
    (Modules.restrictFunctor j).obj
        ((Modules.pushforward (Scheme.projectiveSpaceOverπ n T)).obj G) ≅
      (Modules.pushforward (Scheme.projectiveSpaceOverπ n T')).obj
        ((Modules.restrictFunctor (Scheme.projectiveSpaceOverMap n j)).obj G) :=
  Modules.restrictPushforwardIsoOfOpenSquare
    (Scheme.projectiveSpaceOverπ n T) (Scheme.projectiveSpaceOverπ n T')
    (Scheme.projectiveSpaceOverMap n j) j
    (Scheme.projectiveSpaceOverMap_π n j).symm
    (projectiveSpaceOverMap_image_preimage' n j) G

/-- **Local freeness of `π_*G` over an affine base**, transported to `Spec Γ(B,⊤)`. -/
theorem isProjectiveOfRank_pushforward_of_isAffine (n : ℕ) {B : Scheme.{u}} [IsAffine B]
    (G : (Scheme.projectiveSpaceOver n B).Modules) (q : ℕ)
    (h : Modules.IsProjectiveOfRank q
      ((Modules.pushforward (Scheme.projectiveSpaceOverπ n (Spec Γ(B, ⊤)))).obj
        ((Modules.restrictFunctor
          (Scheme.projectiveSpaceOverMap n B.isoSpec.inv)).obj G))) :
    Modules.IsProjectiveOfRank q
      ((Modules.pushforward (Scheme.projectiveSpaceOverπ n B)).obj G) := by
  have h1 : Modules.IsProjectiveOfRank q
      ((Modules.restrictFunctor B.isoSpec.inv).obj
        ((Modules.pushforward (Scheme.projectiveSpaceOverπ n B)).obj G)) :=
    Modules.IsProjectiveOfRank.of_iso
      (projectiveSpacePushforwardRestrictIso' n B.isoSpec.inv G).symm h
  have h2 : Modules.IsProjectiveOfRank q
      ((Modules.pullback B.isoSpec.inv).obj
        ((Modules.pushforward (Scheme.projectiveSpaceOverπ n B)).obj G)) :=
    Modules.IsProjectiveOfRank.of_iso
      ((Modules.restrictFunctorIsoPullback B.isoSpec.inv).app _) h1
  have h3 := Modules.IsProjectiveOfRank.pullback_of_isIso B.isoSpec.hom h2
  refine Modules.IsProjectiveOfRank.of_iso ?_ h3
  exact ((Modules.pullbackComp B.isoSpec.hom B.isoSpec.inv).app _).trans
    (((Modules.pullbackCongr B.isoSpec.hom_inv_id).app _).trans
      ((Modules.pullbackId B).app _))

/-- The restriction of `G` to `ℙⁿ` over the spectrum of the sections of an affine open. -/
abbrev projectiveSpaceRestrictSpec (n : ℕ) {T : Scheme.{u}} (U : T.affineOpens)
    (G : (Scheme.projectiveSpaceOver n T).Modules) :
    (Scheme.projectiveSpaceOver n (Spec Γ(U.1.toScheme, ⊤))).Modules :=
  haveI : IsAffine U.1.toScheme := U.2
  (Modules.restrictFunctor
      (Scheme.projectiveSpaceOverMap n U.1.toScheme.isoSpec.inv)).obj
    ((Modules.restrictFunctor (Scheme.projectiveSpaceOverMap n U.1.ι)).obj G)

/-- **The full bridge**: `π_*G` is locally free of rank `q` on an arbitrary base as soon as,
for every affine open `U` of the base, the global sections of `G` restricted to
`ℙⁿ_{Spec Γ(U,⊤)}` are finite projective of rank `q` — which is exactly the conclusion of
`Modules.HasEventualFiniteProjectiveGlobalSectionsBaseChange`. -/
theorem isProjectiveOfRank_pushforward_of_globalSections (n : ℕ) {T : Scheme.{u}}
    (G : (Scheme.projectiveSpaceOver n T).Modules) (q : ℕ)
    (hfin : ∀ U : T.affineOpens,
      letI := Modules.globalSectionsModule
        (Scheme.projectiveSpaceOverπ n (Spec Γ(U.1.toScheme, ⊤)))
        (projectiveSpaceRestrictSpec n U G)
      Module.Finite ↥Γ(U.1.toScheme, ⊤) ↥Γ(projectiveSpaceRestrictSpec n U G, ⊤))
    (hproj : ∀ U : T.affineOpens,
      letI := Modules.globalSectionsModule
        (Scheme.projectiveSpaceOverπ n (Spec Γ(U.1.toScheme, ⊤)))
        (projectiveSpaceRestrictSpec n U G)
      Module.Projective ↥Γ(U.1.toScheme, ⊤) ↥Γ(projectiveSpaceRestrictSpec n U G, ⊤))
    (hrank : ∀ U : T.affineOpens,
      letI := Modules.globalSectionsModule
        (Scheme.projectiveSpaceOverπ n (Spec Γ(U.1.toScheme, ⊤)))
        (projectiveSpaceRestrictSpec n U G)
      ∀ p : PrimeSpectrum ↥Γ(U.1.toScheme, ⊤),
        Module.rankAtStalk (R := ↥Γ(U.1.toScheme, ⊤))
          ↥Γ(projectiveSpaceRestrictSpec n U G, ⊤) p = q) :
    Modules.IsProjectiveOfRank q
      ((Modules.pushforward (Scheme.projectiveSpaceOverπ n T)).obj G) := by
  refine isProjectiveOfRank_pushforward_projectiveSpace n G q (fun U => ?_)
  haveI : IsAffine U.1.toScheme := U.2
  exact isProjectiveOfRank_pushforward_of_isAffine n _ q
    (isProjectiveOfRank_pushforward_spec n Γ(U.1.toScheme, ⊤)
      (projectiveSpaceRestrictSpec n U G) q (hfin U) (hproj U) (hrank U))

end AlgebraicGeometry.Scheme
