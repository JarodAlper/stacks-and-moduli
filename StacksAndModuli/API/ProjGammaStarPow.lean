module

public import StacksAndModuli.API.ProjectiveTwistedFreeGlobalSectionsFinite
public import StacksAndModuli.API.SchemeModulesTensorFiniteCoproduct
public import StacksAndModuli.API.SchemeModulesTensorUnitNaturality
public import StacksAndModuli.API.ProjGammaStarTwist
public import StacksAndModuli.API.ProjectiveGradedFreeBaseChange

/-!
# `Γ_*` of a finite direct sum, and `Γ_*(𝒪(a)^{⊕r}) ≅ S(a)^{⊕r}`

This completes the identification of the twisted-free ambient sheaf of a Quot presentation
with a finitely generated, flat graded module:

`Γ_*(𝒪(a)^{⊕r}) ≅ ((structureModule k n).twist a).pow r`  (`twistedFreeIsoGammaStar`, `n ≥ 1`),

so that `GradedModule.isFG_structureModule`, `IsFG.twist`, `IsFG.pow` give `IsFG`, and
`isFlat_structureModule`, `isFlat_twist`, `isFlat_pow` give `IsFlat`.

The construction is in three layers.

1. **Sheaf level.**  `bijective_tensorBiproductProjections`: a section of `(∐ F) ⊗ G` over `⊤`
   is exactly its family of components along the biproduct projections.  This is
   `globalSectionsFiniteCoproductLinearEquiv` together with its component formula
   (`globalSectionsFiniteCoproductLinearEquiv_apply`) and the fact that the distributivity
   isomorphism intertwines the projections (`tensorFiniteCoproductIso'_hom_comp`), which is
   `Functor.mapBiproduct_hom` plus `biproduct.lift_π`.
2. **Graded level.**  `gammaStarCopiesToPow` is built from the *projections*, not from the
   injections, so no finite sums appear and the `comm` field is componentwise
   `Proj.gammaStarMap.comm`.  `gammaStarCopiesIsoPow` is then `isoOfBijective`.
3. **Specialization.**  `twistedFreeIsoGammaStar` composes it with
   `GradedModule.powMapIso (twistIsoGammaStar …).symm`.

Two ambient facts are supplied here because Mathlib's are shaped for `Type 0` index types
while the schemes here live in `Type u`: the `PreservesBiproduct` instance for
`tensorRightFunctor`, and `tensorFiniteCoproductIso'` (the universe-polymorphic form of
`Scheme.Modules.tensorFiniteCoproductIso`).  Functoriality of `GradedModule.pow` is `GradedModule.powMap` / `GradedModule.powMapIso`,
already in `API/ProjectiveGradedFreeBaseChange.lean`.

Main declarations:

* `AlgebraicGeometry.Scheme.Modules.tensorFiniteCoproductIso'` and
  `tensorFiniteCoproductIso'_hom_comp`;
* `AlgebraicGeometry.Scheme.Modules.bijective_tensorBiproductProjections`;
* `AlgebraicGeometry.ProjectiveSpace.GradedModule.bijective_hom_app`;
* `AlgebraicGeometry.ProjectiveSpace.gammaStarCopiesIsoPow`;
* `AlgebraicGeometry.ProjectiveSpace.twistedFreeIsoGammaStar`.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

/-- An additive functor preserves any finite biproduct; the Mathlib instance is stated for
shapes in `Type 0`, and the index types here live in the scheme's universe. -/
noncomputable instance preservesBiproduct_tensorRightFunctor {J : Type u} [Finite J]
    (F : J → X.Modules) (G : X.Modules) :
    PreservesBiproduct F (tensorRightFunctor G) :=
  let ⟨_⟩ := nonempty_fintype J
  { preserves := fun hb ↦
      ⟨isBilimitOfTotal _ (by
        simp_rw [(tensorRightFunctor G).mapBicone_π, (tensorRightFunctor G).mapBicone_ι,
          ← (tensorRightFunctor G).map_comp]
        erw [← (tensorRightFunctor G).map_sum, ← (tensorRightFunctor G).map_id,
          IsBilimit.total hb])⟩ }

/-- Tensoring in the right factor distributes over a finite coproduct whose index type lives
in the scheme's universe. -/
noncomputable def tensorFiniteCoproductIso' {J : Type u} [Finite J]
    (F : J → X.Modules) (G : X.Modules) :
    (tensorRightFunctor G).obj (∐ F) ≅ ∐ ((tensorRightFunctor G).obj ∘ F) :=
  (tensorRightFunctor G).mapIso (biproduct.isoCoproduct F).symm
    ≪≫ (tensorRightFunctor G).mapBiproduct F
    ≪≫ biproduct.isoCoproduct ((tensorRightFunctor G).obj ∘ F)

/-- The comparison intertwines the biproduct projections. -/
theorem tensorFiniteCoproductIso'_hom_comp {J : Type u} [Finite J]
    (F : J → X.Modules) (G : X.Modules) (j : J) :
    (tensorFiniteCoproductIso' F G).hom ≫
        (biproduct.isoCoproduct ((tensorRightFunctor G).obj ∘ F)).inv ≫
          biproduct.π ((tensorRightFunctor G).obj ∘ F) j
      = (tensorRightFunctor G).map ((biproduct.isoCoproduct F).inv ≫ biproduct.π F j) := by
  rw [tensorFiniteCoproductIso']
  simp only [Iso.trans_hom, Category.assoc, Iso.hom_inv_id_assoc, Functor.mapIso_hom,
    Iso.symm_hom, Functor.mapBiproduct_hom]
  rw [Functor.map_comp]
  congr 1
  exact biproduct.lift_π _ j

/-- **Sections of a tensored finite coproduct are their components.**  The map sending a
section of `(∐ F) ⊗ G` to its family of components along the biproduct projections is
bijective. -/
theorem bijective_tensorBiproductProjections {R : CommRingCat.{u}} (p : X ⟶ Spec R)
    {J : Type u} [Finite J] (F : J → X.Modules) (G : X.Modules) :
    Function.Bijective (fun s : Γ((tensorRightFunctor G).obj (∐ F), ⊤) ↦ fun j : J ↦
      (PresheafOfModules.Hom.app
        ((tensorRightFunctor G).map
          ((biproduct.isoCoproduct F).inv ≫ biproduct.π F j)).val (op ⊤)).hom s) := by
  letI (i : J) := globalSectionsModule p ((tensorRightFunctor G).obj (F i))
  letI := globalSectionsModule p (∐ ((tensorRightFunctor G).obj ∘ F))
  have hfun : (fun s : Γ((tensorRightFunctor G).obj (∐ F), ⊤) ↦ fun j : J ↦
        (PresheafOfModules.Hom.app
          ((tensorRightFunctor G).map
            ((biproduct.isoCoproduct F).inv ≫ biproduct.π F j)).val (op ⊤)).hom s)
      = (fun t ↦ globalSectionsFiniteCoproductLinearEquiv p
            ((tensorRightFunctor G).obj ∘ F) t) ∘
        (fun s ↦ (PresheafOfModules.Hom.app
          (tensorFiniteCoproductIso' F G).hom.val (op ⊤)).hom s) := by
    funext s j
    rw [Function.comp_apply,
      globalSectionsFiniteCoproductLinearEquiv_apply p ((tensorRightFunctor G).obj ∘ F) _ j]
    exact (congrArg (fun ψ : (tensorRightFunctor G).obj (∐ F) ⟶
        ((tensorRightFunctor G).obj ∘ F) j ↦
      (PresheafOfModules.Hom.app ψ.val (op ⊤)).hom s)
        (tensorFiniteCoproductIso'_hom_comp F G j)).symm
  rw [hfun]
  exact (globalSectionsFiniteCoproductLinearEquiv p
    ((tensorRightFunctor G).obj ∘ F)).bijective.comp
      (bijective_app_of_iso (tensorFiniteCoproductIso' F G) (op ⊤))

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.ProjectiveSpace

open ProjectiveSpectrum.Twist

attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

/-- **An isomorphism of graded modules is degreewise bijective.**  For the inverse, apply this
to `e.symm`. -/
theorem GradedModule.bijective_hom_app {k : Type u} [CommRing k] {n : ℕ}
    {M N : GradedModule k n} (e : M ≅ N) (d : ℤ) :
    Function.Bijective ((e.hom.app d).hom) := by
  have h1 : ∀ z, (e.inv.app d).hom ((e.hom.app d).hom z) = z :=
    fun z ↦ congrArg (fun ψ : M ⟶ M ↦ (ψ.app d).hom z) e.hom_inv_id
  have h2 : ∀ z, (e.hom.app d).hom ((e.inv.app d).hom z) = z :=
    fun z ↦ congrArg (fun ψ : N ⟶ N ↦ (ψ.app d).hom z) e.inv_hom_id
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

section GammaStarCopies

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {m : ℕ} {R : CommRingCat.{u}} (π : Proj 𝒜 ⟶ Spec R)
variable (F : (Proj 𝒜).Modules) (x : Fin (m + 1) → 𝒜 1) (r : ℕ)

/-- The `j`-th biproduct projection of `r` copies of `F`. -/
noncomputable abbrev copyProj (j : Fin r) :
    (∐ fun _ : ULift.{u} (Fin r) => F) ⟶ F :=
  (biproduct.isoCoproduct (fun _ : ULift.{u} (Fin r) => F)).inv ≫
    biproduct.π (fun _ : ULift.{u} (Fin r) => F) (ULift.up j)

/-- **`Γ_*` of a finite direct sum maps to the direct sum of the `Γ_*`.** -/
noncomputable def gammaStarCopiesToPow :
    Proj.gammaStar 𝒜 π (∐ fun _ : ULift.{u} (Fin r) => F) x ⟶
      (Proj.gammaStar 𝒜 π F x).pow r :=
  letI (d : ℤ) : Module R
      Γ(twistModule 𝒜 (∐ fun _ : ULift.{u} (Fin r) => F) d, ⊤) :=
    Scheme.Modules.globalSectionsModule π
      (twistModule 𝒜 (∐ fun _ : ULift.{u} (Fin r) => F) d)
  letI (d : ℤ) : Module R Γ(twistModule 𝒜 F d, ⊤) :=
    Scheme.Modules.globalSectionsModule π (twistModule 𝒜 F d)
  { app := fun d ↦ ModuleCat.ofHom
      { toFun := fun s j ↦ ((Proj.gammaStarMap 𝒜 π (copyProj 𝒜 F r j) x).app d).hom s
        map_add' := fun s t ↦ funext fun j ↦ map_add _ _ _
        map_smul' := fun c s ↦ funext fun j ↦ map_smul _ _ _ }
    comm := fun i d ↦ by
      refine ModuleCat.hom_ext (LinearMap.ext fun s ↦ funext fun j ↦ ?_)
      exact congrArg
        (fun ψ : (Proj.gammaStar 𝒜 π (∐ fun _ : ULift.{u} (Fin r) => F) x).obj d ⟶
            (Proj.gammaStar 𝒜 π F x).obj (d + 1) ↦ ψ.hom s)
        ((Proj.gammaStarMap 𝒜 π (copyProj 𝒜 F r j) x).comm i d) }

/-- **Bijectivity**: a section of `Γ_*(F^{⊕r})` is exactly a family of `r` sections of
`Γ_*(F)`. -/
theorem bijective_gammaStarCopiesToPow_app (d : ℤ) :
    Function.Bijective (((gammaStarCopiesToPow 𝒜 π F x r).app d).hom) := by
  have h := Scheme.Modules.bijective_tensorBiproductProjections π
    (fun _ : ULift.{u} (Fin r) => F) (twist 𝒜 d)
  letI := Scheme.Modules.globalSectionsModule π (twistModule 𝒜 F d)
  have he : Function.Bijective (fun g : ULift.{u} (Fin r) → Γ(twistModule 𝒜 F d, ⊤) ↦
      fun j : Fin r ↦ g (ULift.up j)) :=
    (Equiv.arrowCongr Equiv.ulift (Equiv.refl Γ(twistModule 𝒜 F d, ⊤))).bijective
  exact he.comp h

/-- **`Γ_*(F^{⊕r}) ≅ (Γ_*F)^r`.** -/
noncomputable def gammaStarCopiesIsoPow :
    Proj.gammaStar 𝒜 π (∐ fun _ : ULift.{u} (Fin r) => F) x ≅
      (Proj.gammaStar 𝒜 π F x).pow r :=
  GradedModule.isoOfBijective (gammaStarCopiesToPow 𝒜 π F x r)
    (bijective_gammaStarCopiesToPow_app 𝒜 π F x r)

end GammaStarCopies

section TwistedFreeGammaStar

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **`Γ_*(𝒪(a)^{⊕r}) ≅ S(a)^{⊕r}` on `ℙⁿ_k` for `n ≥ 1`.**  This is the identification that
makes the twisted-free ambient sheaf of a Quot presentation finitely generated and flat as a
graded module: `GradedModule.isFG_structureModule`, `IsFG.twist` and `IsFG.pow` apply to the
right-hand side. -/
noncomputable def twistedFreeIsoGammaStar (k : Type u) [CommRing k] (n : ℕ) (hn : 0 < n)
    (a : ℤ) (r : ℕ) :
    Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (projπ k n)
        (∐ fun _ : ULift.{u} (Fin r) =>
          twist (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) a) (stdVars n k)
      ≅ ((GradedModule.structureModule k n).twist a).pow r :=
  gammaStarCopiesIsoPow (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (projπ k n)
      (twist (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) a) (stdVars n k) r ≪≫
    GradedModule.powMapIso (twistIsoGammaStar k n hn a).symm r

end TwistedFreeGammaStar

end AlgebraicGeometry.ProjectiveSpace

end

end
