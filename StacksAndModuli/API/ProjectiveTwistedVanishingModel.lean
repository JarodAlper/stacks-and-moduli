module

public import StacksAndModuli.API.FiniteFreePresentationVanishingModel
public import StacksAndModuli.API.ProjectiveFiniteTwistedFreePresentation
public import StacksAndModuli.API.ProjectiveTwistModuleFaithful
public import StacksAndModuli.API.ProjectiveTwistModuleBaseChange
public import StacksAndModuli.API.SchemeModulesGlobalSectionsIso

/-!
# Finite vanishing models from positive twists on projective space

A positive twist turns a finitely presented source into a quotient of a finite free
sheaf.  If the corresponding twist of the target has finite-projective global sections
and canonical arbitrary-base Cohomology and Base Change, its global sections provide a
finite-projective model for the twisted morphism.  Twisting is faithful after every base
change, so the same coordinates detect vanishing of the original morphism.

This file packages that argument independently of Quot.  The remaining geometric input
is an eventual fixed-degree package for the target sheaf, recorded by
`HasEventualFiniteProjectiveCanonicalGlobalSectionsBaseChange`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry ProjectiveSpectrum.Twist

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Pulling a module morphism successively along two maps detects the same zero
condition as pulling it along their composite. -/
lemma pullback_map_map_eq_zero_iff
    {W X Y : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y)
    {M N : Y.Modules} (p : M ⟶ N) :
    (pullback f).map ((pullback g).map p) = 0 ↔
      (pullback (f ≫ g)).map p = 0 := by
  let α := pullbackComp f g
  have hnat := α.hom.naturality p
  constructor
  · intro h
    apply zero_of_epi_comp (α.hom.app M)
    calc
      α.hom.app M ≫ (pullback (f ≫ g)).map p =
          (pullback f).map ((pullback g).map p) ≫ α.hom.app N := hnat.symm
      _ = 0 := by rw [h, zero_comp]
  · intro h
    apply zero_of_comp_mono (α.hom.app N)
    calc
      (pullback f).map ((pullback g).map p) ≫ α.hom.app N =
          α.hom.app M ≫ (pullback (f ≫ g)).map p := hnat
      _ = 0 := by rw [h, comp_zero]

/-- Pulling a module morphism first along a map and then along an isomorphism detects the
same zero condition as pulling it along the composite. -/
lemma pullback_map_eq_zero_iff_pullback_comp_of_isIso
    {X Y Z : Scheme.{u}} (e : X ⟶ Y) [IsIso e] (g : Y ⟶ Z)
    {M N : Z.Modules} (p : M ⟶ N) :
    (pullback g).map p = 0 ↔ (pullback (e ≫ g)).map p = 0 := by
  let α := pullbackComp e g
  have hnat := α.hom.naturality p
  have hiter_iff :
      (pullback e).map ((pullback g).map p) = 0 ↔
        (pullback (e ≫ g)).map p = 0 := by
    constructor
    · intro h
      apply zero_of_epi_comp (α.hom.app M)
      calc
        α.hom.app M ≫ (pullback (e ≫ g)).map p =
            (pullback e).map ((pullback g).map p) ≫ α.hom.app N := hnat.symm
        _ = 0 := by rw [h, zero_comp]
    · intro h
      apply zero_of_comp_mono (α.hom.app N)
      calc
        (pullback e).map ((pullback g).map p) ≫ α.hom.app N =
            α.hom.app M ≫ (pullback (e ≫ g)).map p := hnat
        _ = 0 := by rw [h, comp_zero]
  constructor
  · intro h
    apply hiter_iff.mp
    rw [h, Functor.map_zero]
  · intro h
    apply (Functor.map_eq_zero_iff (pullback e)).mp
    exact hiter_iff.mpr h

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ} {R A : Type u} [CommRing R] [CommRing A]

local notation "𝒜ᴿ" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
local notation "𝒜ᴬ" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A

/-- Pullback along the raw cartesian base change of polynomial projective space
detects the same zero condition as pullback along the intrinsic coefficient-change
map. -/
lemma pullback_map_eq_zero_iff_polynomialMap
    {E F : (Proj 𝒜ᴿ).Modules} (p : E ⟶ F) (f : R →+* A) :
    let π := Proj.polynomialToSpec (Fin (n + 1)) R
    let Y := Limits.pullback (Spec.map (CommRingCat.ofHom f)) π
    let g : Y ⟶ Proj 𝒜ᴿ := Limits.pullback.snd _ _
    (Scheme.Modules.pullback g).map p = 0 ↔
      (Scheme.Modules.pullback
        (Proj.polynomialMap (Fin (n + 1)) f)).map p = 0 := by
  let π := Proj.polynomialToSpec (Fin (n + 1)) R
  let Y := Limits.pullback (Spec.map (CommRingCat.ofHom f)) π
  let g : Y ⟶ Proj 𝒜ᴿ := Limits.pullback.snd _ _
  let H := (Proj.polynomialMap_isPullback (Fin (n + 1)) R f).flip
  let e := H.isoPullback
  have he : e.hom ≫ g = Proj.polynomialMap (Fin (n + 1)) f :=
    H.isoPullback_hom_snd
  exact he ▸
    (Scheme.Modules.pullback_map_eq_zero_iff_pullback_comp_of_isIso e.hom g p)

/-- After coefficient change, the pullback of a morphism vanishes exactly when the
pullback of any nonnegative twist of that morphism vanishes. -/
lemma polynomialMap_pullback_twistModuleMap_eq_zero_iff
    (p : E ⟶ F) (d : ℕ) (f : R →+* A) :
    (Scheme.Modules.pullback (Proj.polynomialMap (Fin (n + 1)) f)).map p = 0 ↔
      (Scheme.Modules.pullback (Proj.polynomialMap (Fin (n + 1)) f)).map
        (twistModuleMap 𝒜ᴿ p (d : ℤ)) = 0 := by
  let q := (Scheme.Modules.pullback
    (Proj.polynomialMap (Fin (n + 1)) f)).map p
  let αE := twistModulePolynomialPullbackHom (Fin (n + 1)) f E (d : ℤ)
  let αF := twistModulePolynomialPullbackHom (Fin (n + 1)) f F (d : ℤ)
  have hnat := pullback_map_twistModuleMap_comp_twistModulePolynomialPullbackHom
    (Fin (n + 1)) f p (d : ℤ)
  have hpull_iff :
      (Scheme.Modules.pullback (Proj.polynomialMap (Fin (n + 1)) f)).map
          (twistModuleMap 𝒜ᴿ p (d : ℤ)) = 0 ↔
        twistModuleMap 𝒜ᴬ q (d : ℤ) = 0 := by
    constructor
    · intro h
      apply zero_of_epi_comp αE
      calc
        αE ≫ twistModuleMap 𝒜ᴬ q (d : ℤ) =
            (Scheme.Modules.pullback (Proj.polynomialMap (Fin (n + 1)) f)).map
              (twistModuleMap 𝒜ᴿ p (d : ℤ)) ≫ αF := hnat.symm
        _ = 0 := by rw [h, zero_comp]
    · intro h
      apply zero_of_comp_mono αF
      calc
        (Scheme.Modules.pullback (Proj.polynomialMap (Fin (n + 1)) f)).map
              (twistModuleMap 𝒜ᴿ p (d : ℤ)) ≫ αF =
            αE ≫ twistModuleMap 𝒜ᴬ q (d : ℤ) := hnat
        _ = 0 := by rw [h, comp_zero]
  exact (twistModuleMap_nat_eq_zero_iff q d).symm.trans hpull_iff.symm

/-- On the raw cartesian base-change model used by the affine zero-locus API, a
nonnegative twist of a morphism detects the original morphism. -/
lemma pullback_twistModuleMap_eq_zero_iff
    (p : E ⟶ F) (d : ℕ) (f : R →+* A) :
    let π := Proj.polynomialToSpec (Fin (n + 1)) R
    let Y := Limits.pullback (Spec.map (CommRingCat.ofHom f)) π
    let g : Y ⟶ Proj 𝒜ᴿ := Limits.pullback.snd _ _
    (Scheme.Modules.pullback g).map p = 0 ↔
      (Scheme.Modules.pullback g).map (twistModuleMap 𝒜ᴿ p (d : ℤ)) = 0 := by
  let π := Proj.polynomialToSpec (Fin (n + 1)) R
  let Y := Limits.pullback (Spec.map (CommRingCat.ofHom f)) π
  let g : Y ⟶ Proj 𝒜ᴿ := Limits.pullback.snd _ _
  let H := (Proj.polynomialMap_isPullback (Fin (n + 1)) R f).flip
  let e := H.isoPullback
  have he : e.hom ≫ g = Proj.polynomialMap (Fin (n + 1)) f :=
    H.isoPullback_hom_snd
  have hp :
      (Scheme.Modules.pullback g).map p = 0 ↔
        (Scheme.Modules.pullback (Proj.polynomialMap (Fin (n + 1)) f)).map p = 0 := by
    exact he ▸
      (Scheme.Modules.pullback_map_eq_zero_iff_pullback_comp_of_isIso e.hom g p)
  have htwist :
      (Scheme.Modules.pullback g).map (twistModuleMap 𝒜ᴿ p (d : ℤ)) = 0 ↔
        (Scheme.Modules.pullback (Proj.polynomialMap (Fin (n + 1)) f)).map
          (twistModuleMap 𝒜ᴿ p (d : ℤ)) = 0 := by
    exact he ▸
      (Scheme.Modules.pullback_map_eq_zero_iff_pullback_comp_of_isIso e.hom g
        (twistModuleMap 𝒜ᴿ p (d : ℤ)))
  exact hp.trans ((polynomialMap_pullback_twistModuleMap_eq_zero_iff p d f).trans htwist.symm)

/-- Eventual finite projectivity and canonical arbitrary-base compatibility for the
global sections of positive twists on polynomial projective space. -/
structure HasEventualFiniteProjectiveCanonicalGlobalSectionsBaseChange
    (F : (Proj 𝒜ᴿ).Modules) : Type (u + 1) where
  /-- A twist from which the fixed-degree package is available. -/
  bound : ℕ
  /-- The fixed-degree finite-projective and arbitrary-base package. -/
  fixedDegree : ∀ (d : ℕ), bound ≤ d →
    Scheme.Modules.HasFiniteProjectiveGlobalSectionsBaseChange
      (Proj.polynomialToSpec (Fin (n + 1)) R)
      (twistModule 𝒜ᴿ F (d : ℤ))

namespace HasEventualFiniteProjectiveCanonicalGlobalSectionsBaseChange

/-- A finitely presented source and eventual canonical Cohomology and Base Change for
the target produce a finite-free universal vanishing model for every morphism between
them. -/
theorem nonempty_finiteFreeVanishingModel
    {E F : (Proj 𝒜ᴿ).Modules} (p : E ⟶ F)
    [E.IsFinitePresentation]
    (H : HasEventualFiniteProjectiveCanonicalGlobalSectionsBaseChange F) :
    Nonempty (Scheme.Modules.HasFiniteFreeVanishingModel
      (Proj.polynomialToSpec (Fin (n + 1)) R) p) := by
  classical
  obtain ⟨m, d, s, hd, hs⟩ :=
    exists_epi_freeHomOfSections_to_twistModule_ge E H.bound
  let s' : ULift.{u} (Σ i, Fin (m i)) →
      Γ(twistModule 𝒜ᴿ E (d : ℤ), ⊤) := fun a ↦ s a.down
  letI : Epi (Scheme.Modules.freeHomOfSections s') := hs
  let HT := (H.fixedDegree d hd).toFiniteProjectiveVanishingModel
    (p := twistModuleMap 𝒜ᴿ p (d : ℤ)) s'
  let H0 : Scheme.Modules.HasFiniteProjectiveVanishingModel
      (Proj.polynomialToSpec (Fin (n + 1)) R) p :=
    Scheme.Modules.HasFiniteProjectiveVanishingModel.of_pullback_zero_iff
      (pX := Proj.polynomialToSpec (Fin (n + 1)) R) (p := p) HT
        (fun A _ f ↦ pullback_twistModuleMap_eq_zero_iff p d f)
  exact ⟨H0.toFiniteFreeVanishingModel⟩

end HasEventualFiniteProjectiveCanonicalGlobalSectionsBaseChange

end AlgebraicGeometry.Proj

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Transporting a morphism from a relative-projective fibre product to polynomial
`Proj` intertwines arbitrary affine coefficient change with the original cartesian
base-change map, as far as vanishing is concerned. -/
lemma polynomialProjectiveTransport_pullback_eq_zero_iff
    {S : Scheme.{u}} {n : ℕ} {R A : Type u} [CommRing R] [CommRing A]
    (sigma : Spec (.of R) ⟶ S) (f : R →+* A)
    {E Q : ((Over.pullback (projectiveSpaceOverπ n S)).obj
      (Over.mk sigma)).left.Modules}
    (q : E ⟶ Q) :
    let g : Over.mk (Spec.map (CommRingCat.ofHom f) ≫ sigma) ⟶
        Over.mk sigma := Over.homMk (Spec.map (CommRingCat.ofHom f)) rfl
    let eR := projectiveSpaceOverBaseChangeIso n sigma
    let eSpecR := ProjectiveSpace.projectiveSpaceOverSpecIso n R
    let qR := (Modules.pullback eSpecR.inv).map
      ((Modules.pullback eR.inv).map q)
    (Modules.pullback (Proj.polynomialMap (Fin (n + 1)) f)).map qR = 0 ↔
      (Modules.pullback
        (((Over.pullback (projectiveSpaceOverπ n S)).map g).left)).map q = 0 := by
  let TR : Over S := Over.mk sigma
  let TA : Over S := Over.mk (Spec.map (CommRingCat.ofHom f) ≫ sigma)
  let g : TA ⟶ TR := Over.homMk (Spec.map (CommRingCat.ofHom f)) rfl
  let eR := projectiveSpaceOverBaseChangeIso n sigma
  let eA := projectiveSpaceOverBaseChangeIso n TA.hom
  let eSpecR := ProjectiveSpace.projectiveSpaceOverSpecIso n R
  let eSpecA := ProjectiveSpace.projectiveSpaceOverSpecIso n A
  let rawMap := ((Over.pullback (projectiveSpaceOverπ n S)).map g).left
  let polyMap := Proj.polynomialMap (Fin (n + 1)) f
  have hpoly : polyMap ≫ eSpecR.inv =
      eSpecA.inv ≫ projectiveSpaceOverMap n g.left := by
    exact ProjectiveSpace.polynomialMap_comp_polynomialProjOverSpecIso_inv n f
  have hbc : eA.inv ≫ rawMap =
      projectiveSpaceOverMap n g.left ≫ eR.inv := by
    exact projectiveSpaceOverBaseChangeIso_inv_naturality n g
  have hcomp : (polyMap ≫ eSpecR.inv) ≫ eR.inv =
      (eSpecA.inv ≫ eA.inv) ≫ rawMap := by
    calc
      (polyMap ≫ eSpecR.inv) ≫ eR.inv =
          (eSpecA.inv ≫ projectiveSpaceOverMap n g.left) ≫ eR.inv :=
        congrArg (fun k ↦ k ≫ eR.inv) hpoly
      _ = eSpecA.inv ≫
          (projectiveSpaceOverMap n g.left ≫ eR.inv) := Category.assoc _ _ _
      _ = eSpecA.inv ≫ (eA.inv ≫ rawMap) :=
        congrArg (fun k ↦ eSpecA.inv ≫ k) hbc.symm
      _ = (eSpecA.inv ≫ eA.inv) ≫ rawMap := (Category.assoc _ _ _).symm
  change (Modules.pullback polyMap).map
      ((Modules.pullback eSpecR.inv).map
        ((Modules.pullback eR.inv).map q)) = 0 ↔
    (Modules.pullback rawMap).map q = 0
  rw [Modules.pullback_map_map_eq_zero_iff]
  rw [Modules.pullback_map_map_eq_zero_iff]
  have hz : (Modules.pullback ((polyMap ≫ eSpecR.inv) ≫ eR.inv)).map q = 0 ↔
      (Modules.pullback ((eSpecA.inv ≫ eA.inv) ≫ rawMap)).map q = 0 := by
    rw [hcomp]
  rw [hz]
  exact (Modules.pullback_map_eq_zero_iff_pullback_comp_of_isIso
    (eSpecA.inv ≫ eA.inv) rawMap q).symm

end AlgebraicGeometry.Scheme

end

end
