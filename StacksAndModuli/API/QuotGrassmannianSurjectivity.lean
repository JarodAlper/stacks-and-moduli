module

public import StacksAndModuli.API.QuotGrassmannianMap
public import StacksAndModuli.API.ProjectiveSpaceTwistSurjectivityAffine
public import StacksAndModuli.API.QcqsPushforwardQuasicoherent
public import StacksAndModuli.API.FreeSheafSections
public import StacksAndModuli.API.KernelGrassmannianPoint

/-!
# Surjectivity of the Quot-to-Grassmannian free map on affine sections

The `hsurj` input of `Modules.kernelGrassmannianPoint` for the map
`𝒪_T^m ⟶ π_*(Q(d))` of `API/QuotGrassmannianMap.lean`: over every affine open of the
base, the sections map is surjective.

By `quotGrassmannianFreeMap_eq` the map factors through `π_*(F(d))`, so the statement
splits into the twisted-presentation surjectivity on `π⁻¹U`
(`exists_bound_surjective_twist_app_preimage`, proved) and the spanning of
`Γ(F(d), π⁻¹U)` by the restricted monomial sections, which this file takes as the
hypothesis `hmono`. The later module `TwistedFreeMonomialSpanAffine.lean` supplies this
hypothesis uniformly in sufficiently large degree and assembles the eventual surjectivity
statement.

Main declarations:

* `AlgebraicGeometry.Scheme.Modules.freeGen_freeHomOfSections`;
* `AlgebraicGeometry.Scheme.Modules.hom_app_preimage_linearMap`;
* `AlgebraicGeometry.Scheme.Modules.finFreeSectionsMap'_comp`;
* `AlgebraicGeometry.Scheme.surjective_finFreeSectionsMap'_quotMonomial`.
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

namespace AlgebraicGeometry.Scheme.Modules

/-- The generating sections of a map built from global sections are the restrictions of
those sections. -/
lemma freeGen_freeHomOfSections {X : Scheme.{u}} {m : ℕ} {M : X.Modules}
    (s : ULift.{u} (Fin m) → ↥Γ(M, ⊤)) (U : X.Opens) (i : Fin m) :
    freeGen (freeHomOfSections s) U i
      = M.val.map ((homOfLE (le_top (a := U))).op : (op (⊤ : X.Opens)) ⟶ op U)
        (s (ULift.up i)) := by
  have hkey : (SheafOfModules.freeHomEquiv M) (freeHomOfSections s) (ULift.up i) =
      (sectionsTopEquiv M).symm (s (ULift.up i)) := by
    simp only [freeHomOfSections, Equiv.apply_symm_apply]
  exact congrArg (fun t : M.sections => t.1 (op U)) hkey

/-- The sections of a morphism over the preimage of an open of the base are linear over
the sections of the base, for the restriction-of-scalars module structures. -/
def hom_app_preimage_linearMap {X T : Scheme.{u}} (π : X ⟶ T) {M N : X.Modules}
    (φ : M ⟶ N) (U : T.Opens) :
    letI := preimageSectionsModule π M U
    letI := preimageSectionsModule π N U
    Γ(M, π ⁻¹ᵁ U) →ₗ[↥Γ(T, U)] Γ(N, π ⁻¹ᵁ U) := by
  letI := preimageSectionsModule π M U
  letI := preimageSectionsModule π N U
  exact
    { toFun := Scheme.Modules.Hom.app φ (π ⁻¹ᵁ U)
      map_add' := fun a b => map_add _ a b
      map_smul' := fun r s => Scheme.Modules.Hom.app_smul φ ((π.app U).hom r) s }

/-- The module map of a composite splits through the section map of the second factor. -/
lemma finFreeSectionsMap'_comp {X : Scheme.{u}} {m : ℕ} {M N : X.Modules}
    (ψ : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m)) ⟶ M)
    (f : M ⟶ N) (U : X.Opens) (x : Fin m → ↥Γ(X, U)) :
    finFreeSectionsMap' (ψ ≫ f) U x
      = Scheme.Modules.Hom.app f U (finFreeSectionsMap' ψ U x) := by
  have hgen : ∀ i : Fin m, freeGen (ψ ≫ f) U i
      = Scheme.Modules.Hom.app f U (freeGen ψ U i) := fun i => rfl
  change ∑ i : Fin m, x i • freeGen (ψ ≫ f) U i
    = (Scheme.Modules.Hom.app f U) (∑ i : Fin m, x i • freeGen ψ U i)
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hgen i]
  exact (Scheme.Modules.Hom.app_smul f (x i) (freeGen ψ U i)).symm

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ} {T : Scheme.{u}}

/-- **Surjectivity of the Quot-to-Grassmannian free map on affine sections**, given the
monomial spanning of the ambient sheaf (`hmono`) and the twisted-presentation surjectivity
over the preimage (`hpush`, supplied by `exists_bound_surjective_twist_app_preimage`). -/
theorem surjective_finFreeSectionsMap'_quotMonomial
    (l : ℤ) (r : ℕ) {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) => projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) {m : ℕ}
    (σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n))
    (U : T.affineOpens)
    (hmono : Function.Surjective (Modules.finFreeSectionsMap'
      (Modules.freeHomOfSections
        (M := (Modules.pushforward (projectiveSpaceOverπ n T)).obj
          (projectiveSpaceOverTwistModule
            (∐ fun _ : ULift.{u} (Fin r) => projectiveSpaceOverTwist n T (-l)) (d : ℤ)))
        (fun i : ULift.{u} (Fin m) =>
          twistedFreeMonomialSection n T l r d e he (σ i).1 (σ i).2)) U.1))
    (hpush : Function.Surjective (Scheme.Modules.Hom.app
      (Scheme.Modules.tensorMapLeft p (projectiveSpaceOverTwist n T (d : ℤ)))
      (projectiveSpaceOverπ n T ⁻¹ᵁ U.1))) :
    Function.Surjective (Modules.finFreeSectionsMap'
      (Modules.freeHomOfSections
        (M := (Modules.pushforward (projectiveSpaceOverπ n T)).obj
          (projectiveSpaceOverTwistModule Q (d : ℤ)))
        (fun i : ULift.{u} (Fin m) =>
          quotMonomialSection n T l r p d e he (σ i).1 (σ i).2)) U.1) := by
  have hfac : Modules.freeHomOfSections
      (M := (Modules.pushforward (projectiveSpaceOverπ n T)).obj
        (projectiveSpaceOverTwistModule Q (d : ℤ)))
      (fun i : ULift.{u} (Fin m) =>
        quotMonomialSection n T l r p d e he (σ i).1 (σ i).2)
      = Modules.freeHomOfSections
        (M := (Modules.pushforward (projectiveSpaceOverπ n T)).obj
          (projectiveSpaceOverTwistModule
            (∐ fun _ : ULift.{u} (Fin r) => projectiveSpaceOverTwist n T (-l)) (d : ℤ)))
        (fun i : ULift.{u} (Fin m) =>
          twistedFreeMonomialSection n T l r d e he (σ i).1 (σ i).2) ≫
        (Modules.pushforward (projectiveSpaceOverπ n T)).map
          (Scheme.Modules.tensorMapLeft p (projectiveSpaceOverTwist n T (d : ℤ))) := by
    rw [Modules.freeHomOfSections_comp]
    rfl
  rw [hfac]
  intro y
  have hpush' : Function.Surjective (Scheme.Modules.Hom.app
      ((Modules.pushforward (projectiveSpaceOverπ n T)).map
        (Scheme.Modules.tensorMapLeft p (projectiveSpaceOverTwist n T (d : ℤ)))) U.1) :=
    hpush
  obtain ⟨z, hz⟩ := hpush' y
  obtain ⟨x, hx⟩ := hmono z
  refine ⟨x, ?_⟩
  rw [Modules.finFreeSectionsMap'_comp, hx]
  exact hz

end AlgebraicGeometry.Scheme

end
