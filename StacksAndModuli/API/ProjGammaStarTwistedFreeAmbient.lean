module

public import StacksAndModuli.API.ProjGammaStarPow
public import StacksAndModuli.API.ProjGammaStarTwistedFreeBaseChange
public import StacksAndModuli.API.ProjectiveGradedCoherent
public import StacksAndModuli.API.ProjectiveGradedFlat
public import StacksAndModuli.API.ProjectiveDVRQuotientPullbackSerre

/-!
# `Γ_*` of the twisted-free ambient sheaf on `ℙⁿ_{Spec R}`

The ambient sheaf of a Quot presentation is `F = 𝒪(-l)^{⊕r}`.  This file identifies its `Γ_*`
with the free graded module, **in every degree**:

`Γ_*(F) ≅ ((structureModule R n).twist (-l)).pow r`  (`gammaStarPullTwistedFreeIso`, `n ≥ 1`),

and deduces the two hypotheses that `RelativeCohomology` asks of the graded module attached to
the ambient sheaf:

* `isFG_gammaStarPullTwistedFree` — `Crel.IsCoherent`, i.e. `GradedModule.IsFG`;
* `isFlat_gammaStarPullTwistedFree` — `Crel.IsFlat`.

Note the difference from `twistedFreeGradedGlobalSectionsEquiv`
(`API/TwistedFreeGlobalSectionsHomogeneous.lean`), which compares the degree-zero *Čech*
cohomology with global sections only in degrees `d ≥ l`.  What is proved here is an
isomorphism of graded modules in all degrees, which is what the coherence and flatness
clauses need.

Three pieces of ambient functoriality are supplied on the way, none of which existed:

* `AlgebraicGeometry.Proj.gammaStarMap_id`, `gammaStarMap_comp`, `gammaStarMapIso` — `Γ_*`
  transports along an isomorphism of sheaves;
* `GradedModule.IsFG.of_iso` and `GradedModule.IsFlat.of_iso` — the two clauses transport
  along an isomorphism of graded modules (`mulSpan_eq_top_of_iso` handles the generation
  clause);
* `pullTwistedFreeIso` — pulling `𝒪(a)^{⊕r}` across the comparison `ℙⁿ_{Spec R} ≅ Proj R[x]`
  gives `∐_r 𝒪(a)`, since `Scheme.Modules.pullback` preserves coproducts and
  `projectiveSpaceOverTwistPullbackIso` handles one summand.

`projSpecπ n R` and `projπ R n` are the same abbreviation for
`Proj.polynomialToSpec (Fin (n+1)) R`, so no transport of the structure morphism is needed.

Main declarations:

* `AlgebraicGeometry.Proj.gammaStarMapIso`;
* `AlgebraicGeometry.ProjectiveSpace.GradedModule.IsFG.of_iso`, `IsFlat.of_iso`;
* `AlgebraicGeometry.ProjectiveSpace.pullTwistedFreeIso`;
* `AlgebraicGeometry.ProjectiveSpace.gammaStarPullTwistedFreeIso`;
* `AlgebraicGeometry.ProjectiveSpace.isFG_gammaStarPullTwistedFree` and
  `isFlat_gammaStarPullTwistedFree`.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Proj

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {n : ℕ} {R : CommRingCat.{u}} (f : Proj 𝒜 ⟶ Spec R) (x : Fin (n + 1) → 𝒜 1)

@[simp] theorem gammaStarMap_id (F : (Proj 𝒜).Modules) :
    gammaStarMap 𝒜 f (𝟙 F) x = 𝟙 (gammaStar 𝒜 f F x) := by
  refine ProjectiveSpace.GradedModule.hom_ext fun d ↦ ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun s ↦ ?_)
  exact congrArg (fun ψ : ProjectiveSpectrum.Twist.twistModule 𝒜 F d ⟶
      ProjectiveSpectrum.Twist.twistModule 𝒜 F d ↦
    (PresheafOfModules.Hom.app ψ.val (op ⊤)).hom s)
    (ProjectiveSpectrum.Twist.twistModuleMap_id 𝒜 F d)

@[simp] theorem gammaStarMap_comp {F F' F'' : (Proj 𝒜).Modules} (φ : F ⟶ F') (φ' : F' ⟶ F'') :
    gammaStarMap 𝒜 f (φ ≫ φ') x = gammaStarMap 𝒜 f φ x ≫ gammaStarMap 𝒜 f φ' x := by
  refine ProjectiveSpace.GradedModule.hom_ext fun d ↦ ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun s ↦ ?_)
  exact congrArg (fun ψ : ProjectiveSpectrum.Twist.twistModule 𝒜 F d ⟶
      ProjectiveSpectrum.Twist.twistModule 𝒜 F'' d ↦
    (PresheafOfModules.Hom.app ψ.val (op ⊤)).hom s)
    (ProjectiveSpectrum.Twist.twistModuleMap_comp 𝒜 φ φ' d)

/-- `Γ_*` transports along an isomorphism of sheaves. -/
noncomputable def gammaStarMapIso {F F' : (Proj 𝒜).Modules} (e : F ≅ F') :
    gammaStar 𝒜 f F x ≅ gammaStar 𝒜 f F' x where
  hom := gammaStarMap 𝒜 f e.hom x
  inv := gammaStarMap 𝒜 f e.inv x
  hom_inv_id := by rw [← gammaStarMap_comp, e.hom_inv_id, gammaStarMap_id]
  inv_hom_id := by rw [← gammaStarMap_comp, e.inv_hom_id, gammaStarMap_id]

end AlgebraicGeometry.Proj
namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

variable {k : Type u} [CommRing k] {n : ℕ}

/-- Finite generation of a graded module transports along an isomorphism. -/
theorem IsFG.of_iso {M N : GradedModule k n} (e : M ≅ N) (hM : IsFG M) :
    IsFG N := by
  obtain ⟨hfin, ⟨a, ha⟩, ⟨b, hb⟩⟩ := hM
  refine ⟨fun d ↦ Module.Finite.equiv (appIso e d).toLinearEquiv, ⟨a, fun d hd ↦ ?_⟩,
    ⟨b, fun d hd ↦ ?_⟩⟩
  · haveI := ha d hd
    exact (appIso e d).symm.toLinearEquiv.injective.subsingleton
  · exact mulSpan_eq_top_of_iso e d (d + 1) (hb d hd)

/-- Degreewise flatness transports along an isomorphism. -/
theorem IsFlat.of_iso {M N : GradedModule k n} (e : M ≅ N) (hM : IsFlat M) : IsFlat N :=
  fun d ↦ by
    haveI := hM d
    exact Module.Flat.of_linearEquiv (appIso e d).symm.toLinearEquiv

end AlgebraicGeometry.ProjectiveSpace.GradedModule

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Pulling the twisted-free sheaf across the affine comparison gives the direct sum of the
intrinsic twists on polynomial `Proj`. -/
noncomputable def pullTwistedFreeIso (n : ℕ) (R : Type u) [CommRing R] (a : ℤ) (r : ℕ) :
    (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj
        (∐ fun _ : ULift.{u} (Fin r) => Scheme.projectiveSpaceOverTwist n (Spec (.of R)) a)
      ≅ ∐ fun _ : ULift.{u} (Fin r) =>
          ProjectiveSpectrum.Twist.twist
            (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) a :=
  PreservesCoproduct.iso (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv) _ ≪≫
    Sigma.mapIso (fun _ ↦ projectiveSpaceOverTwistPullbackIso n R a)

/-- **`Γ_*` of the twisted-free ambient sheaf on `ℙⁿ_{Spec R}` is `S(a)^{⊕r}`.** -/
noncomputable def gammaStarPullTwistedFreeIso (n : ℕ) (R : Type u) [CommRing R] (hn : 0 < n)
    (a : ℤ) (r : ℕ) :
    Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (projSpecπ n R)
        ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj
          (∐ fun _ : ULift.{u} (Fin r) => Scheme.projectiveSpaceOverTwist n (Spec (.of R)) a))
        (stdVars n R)
      ≅ ((GradedModule.structureModule R n).twist a).pow r :=
  Proj.gammaStarMapIso _ (projSpecπ n R) (stdVars n R) (pullTwistedFreeIso n R a r) ≪≫
    twistedFreeIsoGammaStar R n hn a r

/-- **`Crel.IsCoherent` for the twisted-free ambient sheaf.**  `Γ_*` of `𝒪(a)^{⊕r}` is a
finitely generated graded module. -/
theorem isFG_gammaStarPullTwistedFree (n : ℕ) (R : Type u) [CommRing R]
    (hn : 0 < n) (a : ℤ) (r : ℕ) :
    GradedModule.IsFG
      (Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (projSpecπ n R)
        ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj
          (∐ fun _ : ULift.{u} (Fin r) => Scheme.projectiveSpaceOverTwist n (Spec (.of R)) a))
        (stdVars n R)) :=
  GradedModule.IsFG.of_iso (gammaStarPullTwistedFreeIso n R hn a r).symm
    (((GradedModule.isFG_structureModule (k := R) (n := n)).twist a).pow r)

/-- **`Crel.IsFlat` for the twisted-free ambient sheaf.** -/
theorem isFlat_gammaStarPullTwistedFree (n : ℕ) (R : Type u) [CommRing R]
    (hn : 0 < n) (a : ℤ) (r : ℕ) :
    GradedModule.IsFlat
      (Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (projSpecπ n R)
        ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj
          (∐ fun _ : ULift.{u} (Fin r) => Scheme.projectiveSpaceOverTwist n (Spec (.of R)) a))
        (stdVars n R)) :=
  GradedModule.IsFlat.of_iso (gammaStarPullTwistedFreeIso n R hn a r).symm
    (((GradedModule.isFlat_structureModule (R := R) (n := n)).twist a).pow r)

/-- **The base-change obligation holds for the twisted-free ambient sheaf.**  Both `Γ_*` of
`𝒪(-l)^{⊕r}` and `Γ_*` of each of its field fibres are the free graded module, so
`hasGammaStarBaseChangeCechHgrZero_of_freeIso` applies. -/
theorem hasGammaStarBaseChangeCechHgrZero_twistedFree (n : ℕ) (R : Type u) [CommRing R]
    (hn : 0 < n) (l : ℤ) (r : ℕ) :
    HasGammaStarBaseChangeCechHgrZero n R
      (∐ fun _ : ULift.{u} (Fin r) =>
        Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l)) :=
  hasGammaStarBaseChangeCechHgrZero_of_freeIso n R _ l r
    (gammaStarPullTwistedFreeIso n R hn (-l) r)
    (fun K _ f ↦
      Proj.gammaStarMapIso _ (projSpecπ n K) (stdVars n K)
          ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n K).inv).mapIso
            (Scheme.projectiveSpaceOverTwistedFree_pullbackIso n r l
              (Spec.map (CommRingCat.ofHom f)))) ≪≫
        gammaStarPullTwistedFreeIso n K hn (-l) r)

/-- **W4 for the twisted-free ambient sheaf, with no bound.**  The graded Čech model computes
`Γ(ℙⁿ_R, 𝒪(-l)^{⊕r}(d))` in every degree `d ≥ 0` and on every field fibre.

This is the same package as
`AlgebraicGeometry.ProjectiveSpace.twistedFreeSchemeGlobalSectionsComparison`
(`API/TwistedFreeSchemeComparison.lean`), but for the graded module `Γ_*(F)` rather than for
the free model, and with `bound = 0` rather than `l.toNat`. -/
noncomputable def gammaStarTwistedFreeSchemeGlobalSectionsComparison (n : ℕ) (R : Type u)
    [CommRing R] [IsNoetherianRing R] (hn : 0 < n) (l : ℤ) (r : ℕ)
    [(∐ fun _ : ULift.{u} (Fin r) =>
      Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l)).IsFinitePresentation] :
    (RelativeCohomology.cech R).SchemeGlobalSectionsComparison
      (Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (projSpecπ n R)
        ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj
          (∐ fun _ : ULift.{u} (Fin r) =>
            Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l))) (stdVars n R))
      (∐ fun _ : ULift.{u} (Fin r) =>
        Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l)) :=
  schemeGlobalSectionsComparison _ (hasGammaStarBaseChangeCechHgrZero_twistedFree n R hn l r)

end AlgebraicGeometry.ProjectiveSpace

end

end
