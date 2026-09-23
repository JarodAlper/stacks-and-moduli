module

public import StacksAndModuli.API.ProjectiveSpaceTwistMultiplication
public import StacksAndModuli.API.ProjectiveSpaceOverSpecComparison
public import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# Finite global sections of twisted-free sheaves on projective space

The polynomial-`Proj` computation of `H⁰(O(d))` transports across the canonical
identification of relative projective space over `Spec R` with polynomial `Proj`.
Consequently, natural-degree twists have finite free global sections, and every
nonnegative integer twist has finite global sections.

The global-sections functor over an affine base is additive, so finite coproducts of
such twists also have finite global sections.  Combined with multiplication of twists
and its compatibility with arbitrary small coproducts, this proves the corresponding
finiteness result for a finite twisted-free ambient sheaf after a sufficiently positive
twist.

* `Scheme.projectiveSpaceOverTwistGlobalSectionsBasis`: the transported binomial basis.
* `Scheme.projectiveSpaceOverTwist_globalSections_finite_projective`: finite projective
  `H⁰(O(d))` for natural `d`.
* `Scheme.projectiveSpaceOverNegativeTwist_coproduct_twist_globalSections_finite`:
  finite global sections of a normalized finite twisted-free ambient sheaf.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open ProjectiveSpectrum
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The biproduct of an arbitrary small finite family of modules is its dependent
function module.  This is the universe-polymorphic form needed for `ULift (Fin r)`.
-/
noncomputable def moduleCatBiproductIsoPi
    {R : Type u} [Ring R] {J : Type u} [Finite J]
    (F : J → ModuleCat.{u} R) :
    ((⨁ F) : ModuleCat.{u} R) ≅ ModuleCat.of R (∀ j, F j) :=
  IsLimit.conePointUniqueUpToIso (biproduct.isLimit F)
    (ModuleCat.HasLimit.productLimitCone F).isLimit

/-- Global sections of module sheaves on a scheme over an affine base, regarded as
modules over the base ring. -/
noncomputable def globalSectionsOverBaseFunctor
    {X : Scheme.{u}} {R : CommRingCat.{u}} (p : X ⟶ Spec R) :
    X.Modules ⥤ ModuleCat.{u} R where
  obj M := letI := globalSectionsModule p M; ModuleCat.of R Γ(M, ⊤)
  map {M N} f := by
    letI := globalSectionsModule p M
    letI := globalSectionsModule p N
    exact ModuleCat.ofHom (globalSectionsLinearMap p f)
  map_id M := by
    ext
    rfl
  map_comp f g := by
    ext
    rfl

/-- The global-sections-over-an-affine-base functor is additive. -/
noncomputable instance {X : Scheme.{u}} {R : CommRingCat.{u}}
    (p : X ⟶ Spec R) : (globalSectionsOverBaseFunctor p).Additive where
  map_add := by
    intro X Y f g
    ext x
    change (f + g).val.app (op ⊤) x =
      f.val.app (op ⊤) x + g.val.app (op ⊤) x
    rfl

/-- Global sections over an affine base identify the global sections of a finite
coproduct with the dependent product of the component global sections. -/
noncomputable def globalSectionsFiniteCoproductLinearEquiv
    {X : Scheme.{u}} {R : CommRingCat.{u}} {J : Type u} [Finite J]
    (p : X ⟶ Spec R) (F : J → X.Modules) :
    letI (j : J) := globalSectionsModule p (F j)
    letI := globalSectionsModule p (∐ F)
    Γ(∐ F, ⊤) ≃ₗ[R] (∀ j, Γ(F j, ⊤)) := by
  letI (j : J) := globalSectionsModule p (F j)
  letI := globalSectionsModule p (∐ F)
  letI : HasFiniteBiproducts X.Modules :=
    HasFiniteBiproducts.of_hasFiniteCoproducts
  let G := globalSectionsOverBaseFunctor p
  letI : G.Additive := by
    dsimp only [G]
    infer_instance
  letI : PreservesBiproduct F G :=
    let ⟨_⟩ := nonempty_fintype J
    { preserves := fun hb ↦
        ⟨isBilimitOfTotal _ (by
          simp_rw [G.mapBicone_π, G.mapBicone_ι, ← G.map_comp]
          erw [← G.map_sum, ← G.map_id, IsBilimit.total hb])⟩ }
  exact (G.mapIso (biproduct.isoCoproduct F).symm ≪≫
    G.mapBiproduct F ≪≫
    moduleCatBiproductIsoPi (G.obj ∘ F)).toLinearEquiv

section GlobalSectionsFiniteCoproduct

attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

/-- **The `j`-th component of the finite-coproduct comparison is restriction along the `j`-th
biproduct projection.**  Together with bijectivity of the comparison this says that a global
section of `∐ F` is determined by, and can be prescribed by, its components — the form in
which `Γ_*` of a twisted-free sheaf is identified with a `GradedModule.pow`.

Both characterizing identities are `Functor.mapBiproduct_hom` (`= biproduct.lift fun j ↦
F.map (biproduct.π f j)`, by `rfl`) and `IsLimit.conePointUniqueUpToIso_hom_comp` for
`moduleCatBiproductIsoPi`; the `letI`s below must repeat those of
`globalSectionsFiniteCoproductLinearEquiv` verbatim so that the `show` step is `rfl`. -/
theorem globalSectionsFiniteCoproductLinearEquiv_apply
    {X : Scheme.{u}} {R : CommRingCat.{u}} {J : Type u} [Finite J]
    (p : X ⟶ Spec R) (F : J → X.Modules) (s : Γ(∐ F, ⊤)) (j : J) :
    letI (i : J) := globalSectionsModule p (F i)
    letI := globalSectionsModule p (∐ F)
    globalSectionsFiniteCoproductLinearEquiv p F s j
      = (PresheafOfModules.Hom.app
          ((biproduct.isoCoproduct F).inv ≫ biproduct.π F j).val (op ⊤)).hom s := by
  letI (i : J) := globalSectionsModule p (F i)
  letI := globalSectionsModule p (∐ F)
  letI : HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteCoproducts
  let G := globalSectionsOverBaseFunctor p
  letI : G.Additive := by dsimp only [G]; infer_instance
  letI : PreservesBiproduct F G :=
    let ⟨_⟩ := nonempty_fintype J
    { preserves := fun hb ↦
        ⟨isBilimitOfTotal _ (by
          simp_rw [G.mapBicone_π, G.mapBicone_ι, ← G.map_comp]
          erw [← G.map_sum, ← G.map_id, IsBilimit.total hb])⟩ }
  show ((moduleCatBiproductIsoPi (G.obj ∘ F)).hom.hom
      ((Functor.mapBiproduct G F).hom.hom
        ((G.map (biproduct.isoCoproduct F).symm.hom).hom s))) j = _
  have hA : ∀ (H : J → ModuleCat.{u} R) (w : (⨁ H : ModuleCat.{u} R)) (i : J),
      ((moduleCatBiproductIsoPi H).hom.hom w) i = (biproduct.π H i).hom w := by
    intro H w i
    exact congrArg (fun f : (⨁ H : ModuleCat.{u} R) ⟶ H i ↦ f.hom w)
      (IsLimit.conePointUniqueUpToIso_hom_comp (biproduct.isLimit H)
        (ModuleCat.HasLimit.productLimitCone H).isLimit ⟨i⟩)
  have hB : (Functor.mapBiproduct G F).hom ≫ biproduct.π (G.obj ∘ F) j
      = G.map (biproduct.π F j) := by
    rw [Functor.mapBiproduct_hom]
    exact biproduct.lift_π _ j
  rw [hA]
  have hB' := congrArg (fun f : G.obj (⨁ F) ⟶ (G.obj ∘ F) j ↦
    f.hom ((G.map (biproduct.isoCoproduct F).symm.hom).hom s)) hB
  refine hB'.trans ?_
  rfl

end GlobalSectionsFiniteCoproduct

/-- A finite coproduct of module sheaves with finite global sections again has
finite global sections over the affine base. -/
theorem finite_globalSections_finiteCoproduct
    {X : Scheme.{u}} {R : CommRingCat.{u}} {J : Type u} [Finite J]
    (p : X ⟶ Spec R) (F : J → X.Modules)
    (hF : ∀ j, letI := globalSectionsModule p (F j)
      Module.Finite R Γ(F j, ⊤)) :
    letI := globalSectionsModule p (∐ F)
    Module.Finite R Γ(∐ F, ⊤) := by
  letI (j : J) := globalSectionsModule p (F j)
  letI := globalSectionsModule p (∐ F)
  letI (j : J) : Module.Finite R Γ(F j, ⊤) := hF j
  letI : Module.Finite R (∀ j, Γ(F j, ⊤)) := Module.Finite.pi
  exact Module.Finite.equiv (globalSectionsFiniteCoproductLinearEquiv p F).symm

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Under the affine polynomial-`Proj` comparison, the relative structure map
becomes the intrinsic polynomial-`Proj` structure map. -/
theorem projectiveSpaceOverSpecIso_inv_comp_projectiveSpaceOverπ
    (n : ℕ) (R : Type u) [CommRing R] :
    (projectiveSpaceOverSpecIso n R).inv ≫
        Scheme.projectiveSpaceOverπ n (Spec (.of R)) =
      Proj.polynomialToSpec (Fin (n + 1)) R := by
  apply (cancel_epi (projectiveSpaceOverSpecIso n R).hom).1
  rw [Iso.hom_inv_id_assoc]
  exact Proj.polynomialProjOverSpecIso_hom_toSpec (Fin (n + 1)) R |>.symm

/-- Pulling the relative twisting sheaf across the affine polynomial-`Proj`
comparison gives the intrinsic polynomial twisting sheaf. -/
noncomputable def projectiveSpaceOverTwistPullbackIso
    (n : ℕ) (R : Type u) [CommRing R] (d : ℤ) :
    (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj
        (Scheme.projectiveSpaceOverTwist n (Spec (.of R)) d) ≅
      ProjectiveSpectrum.Twist.twist
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d :=
  (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).mapIso
      (Scheme.Modules.tensorLeftUnitIso _).symm ≪≫
    projectiveSpaceOverUnitTwistPullbackIso n R d

/-- The intrinsic polynomial computation of `H⁰(O(d))` transported to relative
projective space over an affine base. -/
noncomputable def projectiveSpaceOverTwistGlobalSectionsLinearEquiv
    (n : ℕ) (R : Type u) [CommRing R] (d : ℕ) :
    letI := Scheme.Modules.globalSectionsModule
      (Scheme.projectiveSpaceOverπ n (Spec (.of R)))
      (Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (d : ℤ))
    letI := MvPolynomial.projectiveTwistGlobalSectionsModule n R d
    Γ(Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (d : ℤ), ⊤) ≃ₗ[R]
      Γ(ProjectiveSpectrum.Twist.twist
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (d : ℤ), ⊤) := by
  letI := Scheme.Modules.globalSectionsModule
    (Scheme.projectiveSpaceOverπ n (Spec (.of R)))
    (Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (d : ℤ))
  letI := MvPolynomial.projectiveTwistGlobalSectionsModule n R d
  let f := (projectiveSpaceOverSpecIso n R).inv
  let p := Scheme.projectiveSpaceOverπ n (Spec (.of R))
  let M := Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (d : ℤ)
  let e := projectiveSpaceOverTwistPullbackIso n R (d : ℤ)
  let a := Scheme.Modules.pullbackGlobalSectionsViaIsoAddEquiv f M e
  exact
    { a with
      map_smul' := by
        intro r m
        change e.hom.app ⊤
            (_root_.Scheme.Modules.pullbackGlobalSections f M
              ((Scheme.Modules.baseRingHom p).hom r • m)) =
          MvPolynomial.projectiveSpaceScalarRingHom n R r •
            e.hom.app ⊤
              (_root_.Scheme.Modules.pullbackGlobalSections f M m)
        rw [Scheme.Modules.pullbackGlobalSections_smul]
        change e.hom.val.app (op ⊤)
            (f.appTop ((Scheme.Modules.baseRingHom p).hom r) •
              _root_.Scheme.Modules.pullbackGlobalSections f M m) = _
        rw [(e.hom.val.app (op ⊤)).hom.map_smul]
        congr 1
        change ((Scheme.Modules.baseRingHom p ≫ f.appTop).hom) r =
          MvPolynomial.projectiveSpaceScalarRingHom n R r
        rw [Scheme.Modules.baseRingHom_comp_appTop]
        rw [projectiveSpaceOverSpecIso_inv_comp_projectiveSpaceOverπ]
        rw [projectiveSpaceScalarRingHom_eq_baseRingHom] }

end AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme

/-- A finite basis of global sections of a natural-degree twist on relative
projective space over an affine base. -/
noncomputable def projectiveSpaceOverTwistGlobalSectionsBasis
    (n : ℕ) (R : Type u) [CommRing R] (d : ℕ) :
    letI := Modules.globalSectionsModule
      (projectiveSpaceOverπ n (Spec (.of R)))
      (projectiveSpaceOverTwist n (Spec (.of R)) (d : ℤ))
    Module.Basis (Fin ((n + d).choose n)) R
      Γ(projectiveSpaceOverTwist n (Spec (.of R)) (d : ℤ), ⊤) := by
  letI := Modules.globalSectionsModule
    (projectiveSpaceOverπ n (Spec (.of R)))
    (projectiveSpaceOverTwist n (Spec (.of R)) (d : ℤ))
  letI := MvPolynomial.projectiveTwistGlobalSectionsModule n R d
  exact (MvPolynomial.projectiveTwistGlobalSectionsBasis n R d).map
    (ProjectiveSpace.projectiveSpaceOverTwistGlobalSectionsLinearEquiv n R d).symm

/-- Global sections of a natural-degree twist on relative projective space over
an affine base are finite projective over the base ring. -/
theorem projectiveSpaceOverTwist_globalSections_finite_projective
    (n : ℕ) (R : Type u) [CommRing R] (d : ℕ) :
    letI := Modules.globalSectionsModule
      (projectiveSpaceOverπ n (Spec (.of R)))
      (projectiveSpaceOverTwist n (Spec (.of R)) (d : ℤ))
    Module.Finite R
        Γ(projectiveSpaceOverTwist n (Spec (.of R)) (d : ℤ), ⊤) ∧
      Module.Projective R
        Γ(projectiveSpaceOverTwist n (Spec (.of R)) (d : ℤ), ⊤) := by
  letI := Modules.globalSectionsModule
    (projectiveSpaceOverπ n (Spec (.of R)))
    (projectiveSpaceOverTwist n (Spec (.of R)) (d : ℤ))
  exact
    ⟨Module.Finite.of_basis (projectiveSpaceOverTwistGlobalSectionsBasis n R d),
      Module.Projective.of_basis (projectiveSpaceOverTwistGlobalSectionsBasis n R d)⟩

/-- Global sections of a nonnegative integer twist on relative projective space
over an affine base are finite over the base ring. -/
theorem projectiveSpaceOverTwist_globalSections_finite_of_nonneg
    (n : ℕ) (R : Type u) [CommRing R] (e : ℤ) (he : 0 ≤ e) :
    letI := Modules.globalSectionsModule
      (projectiveSpaceOverπ n (Spec (.of R)))
      (projectiveSpaceOverTwist n (Spec (.of R)) e)
    Module.Finite R Γ(projectiveSpaceOverTwist n (Spec (.of R)) e, ⊤) := by
  let k := e.toNat
  have hk : (k : ℤ) = e := Int.toNat_of_nonneg he
  let E := projectiveSpaceOverTwist n (Spec (.of R)) e
  let F := projectiveSpaceOverTwist n (Spec (.of R)) (k : ℤ)
  let p := projectiveSpaceOverπ n (Spec (.of R))
  let eSheaf : E ≅ F := eqToIso (by simp only [E, F, hk])
  letI := Modules.globalSectionsModule p E
  letI := Modules.globalSectionsModule p F
  let _ : Module.Finite R Γ(F, ⊤) :=
    (projectiveSpaceOverTwist_globalSections_finite_projective n R k).1
  exact Module.Finite.equiv (Modules.globalSectionsLinearEquivOfIso p eSheaf).symm

/-- A finite coproduct of nonnegative twists on relative projective space over an
affine base has finite global sections. -/
theorem projectiveSpaceOverTwist_coproduct_globalSections_finite
    {J : Type u} [Finite J] (n : ℕ) (R : Type u) [CommRing R]
    (degree : J → ℕ) :
    let F := fun j : J ↦
      projectiveSpaceOverTwist n (Spec (.of R)) (degree j : ℤ)
    letI := Modules.globalSectionsModule
      (projectiveSpaceOverπ n (Spec (.of R))) (∐ F)
    Module.Finite R Γ(∐ F, ⊤) := by
  let F := fun j : J ↦
    projectiveSpaceOverTwist n (Spec (.of R)) (degree j : ℤ)
  let p := projectiveSpaceOverπ n (Spec (.of R))
  exact Modules.finite_globalSections_finiteCoproduct p F fun j ↦
    (projectiveSpaceOverTwist_globalSections_finite_projective
      n R (degree j)).1

/-- After twisting a finite coproduct of copies of `O(-l)` by a natural-degree
twist, its global sections are finite whenever the normalized degree `d-l` is
nonnegative. -/
theorem projectiveSpaceOverNegativeTwist_coproduct_twist_globalSections_finite
    {J : Type u} [Finite J] (n : ℕ) (R : Type u) [CommRing R]
    (l : ℤ) (d : ℕ) (h : 0 ≤ (d : ℤ) - l) :
    let A := Modules.tensor
      (∐ fun _ : J ↦ projectiveSpaceOverTwist n (Spec (.of R)) (-l))
      (projectiveSpaceOverTwist n (Spec (.of R)) (d : ℤ))
    letI := Modules.globalSectionsModule
      (projectiveSpaceOverπ n (Spec (.of R))) A
    Module.Finite R Γ(A, ⊤) := by
  let A := Modules.tensor
    (∐ fun _ : J ↦ projectiveSpaceOverTwist n (Spec (.of R)) (-l))
    (projectiveSpaceOverTwist n (Spec (.of R)) (d : ℤ))
  let F := fun _ : J ↦
    projectiveSpaceOverTwist n (Spec (.of R)) ((d : ℤ) - l)
  let B := ∐ F
  let p := projectiveSpaceOverπ n (Spec (.of R))
  let eSheaf : A ≅ B :=
    projectiveSpaceOverNegativeTwist_coproduct_twistIso_nat
      (J := J) n (Spec (.of R)) l d
  letI := Modules.globalSectionsModule p A
  letI := Modules.globalSectionsModule p B
  let _ : Module.Finite R Γ(B, ⊤) :=
    Modules.finite_globalSections_finiteCoproduct p F fun _ ↦
      projectiveSpaceOverTwist_globalSections_finite_of_nonneg n R _ h
  exact Module.Finite.equiv (Modules.globalSectionsLinearEquivOfIso p eSheaf).symm

/-- For a fixed finite twisted-free ambient sheaf, sufficiently positive natural
twists have finite global sections over the affine base. -/
theorem eventually_projectiveSpaceOverNegativeTwist_coproduct_twist_globalSections_finite
    {J : Type u} [Finite J] (n : ℕ) (R : Type u) [CommRing R] (l : ℤ) :
    ∀ᶠ d : ℕ in Filter.atTop,
      let A := Modules.tensor
        (∐ fun _ : J ↦ projectiveSpaceOverTwist n (Spec (.of R)) (-l))
        (projectiveSpaceOverTwist n (Spec (.of R)) (d : ℤ))
      letI := Modules.globalSectionsModule
        (projectiveSpaceOverπ n (Spec (.of R))) A
      Module.Finite R Γ(A, ⊤) := by
  rw [Filter.eventually_atTop]
  refine ⟨l.toNat, fun d hd ↦
    projectiveSpaceOverNegativeTwist_coproduct_twist_globalSections_finite
      (J := J) n R l d ?_⟩
  exact Int.sub_nonneg.mpr
    ((Int.self_le_toNat l).trans (Int.ofNat_le.mpr hd))

end AlgebraicGeometry.Scheme
