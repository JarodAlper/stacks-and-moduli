module

public import StacksAndModuli.API.GlobalSectionsTorsionFreeLocal
public import StacksAndModuli.API.SchemeModulesTensorQuasicoherent

/-!
# Sections of a twist on a chart are as flat as the sheaf

`Scheme.Modules.FlatOver` is a condition on *affine* opens, while
`GradedModule.IsFlat (Γ_*(F))` is about sections over `⊤` of every twist `F(d)`.  This file
supplies the chart half of the passage between them: on `D₊(xᵢ)` every twist is trivial, so

`Γ(D₊(xᵢ), F(d))` is flat over the base as soon as `Γ(D₊(xᵢ), F)` is.

Two trivializations are combined: `ProjectiveSpectrum.Twist.zeroIso` (the degree-zero twist is
the structure sheaf) and `AlgebraicGeometry.Proj.chartTwistLinearEquiv` (multiplication by
`xᵢ^k` is bijective on chart sections), the latter used in whichever direction the sign of `d`
allows.

Combined with `Scheme.Modules.isTorsionFree_globalSections_of_cover` this gives degreewise
flatness of `Γ_*(F)` over a Dedekind base.

Main declarations:

* `AlgebraicGeometry.Scheme.Modules.openSectionsLinearEquivOfIso`;
* `AlgebraicGeometry.Proj.chartTwistZeroLinearEquiv`;
* `AlgebraicGeometry.Proj.flat_openSections_twistModule_basicOpen`.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {R : CommRingCat.{u}}

/-- An isomorphism of module sheaves induces an `R`-linear equivalence on the sections over
any open, for the `R`-module structures determined by `f : X ⟶ Spec R`. -/
noncomputable def openSectionsLinearEquivOfIso {M N : X.Modules}
    (f : X ⟶ Spec R) (e : M ≅ N) (U : X.Opens) :
    letI := openSectionsModuleOver f M U
    letI := openSectionsModuleOver f N U
    Γ(M, U) ≃ₗ[R] Γ(N, U) := by
  letI := openSectionsModuleOver f M U
  letI := openSectionsModuleOver f N U
  let eU : M.val.obj (op U) ≅ N.val.obj (op U) :=
    { hom := e.hom.val.app (op U)
      inv := e.inv.val.app (op U)
      hom_inv_id := congrArg (fun k ↦ k.val.app (op U)) e.hom_inv_id
      inv_hom_id := congrArg (fun k ↦ k.val.app (op U)) e.inv_hom_id }
  exact
    { toEquiv := eU.toLinearEquiv.toEquiv
      map_add' := eU.toLinearEquiv.map_add
      map_smul' := fun r m ↦
        (openSectionsLinearMap f e.hom U).map_smul r m }

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

open ProjectiveSpectrum.Twist AlgebraicGeometry.ProjectiveSpace

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {n : ℕ} {R : CommRingCat.{u}} (π : Proj 𝒜 ⟶ Spec R)
variable (G : (Proj 𝒜).Modules) (x : Fin (n + 1) → 𝒜 1) (i : Fin (n + 1))

/-- On a chart, the degree-zero twist is the sheaf itself. -/
noncomputable def chartTwistZeroLinearEquiv :
    letI := Scheme.Modules.openSectionsModuleOver π (twistModule 𝒜 G 0)
      (basicOpen 𝒜 ((x i : A)))
    letI := Scheme.Modules.openSectionsModuleOver π G (basicOpen 𝒜 ((x i : A)))
    Γ(twistModule 𝒜 G 0, basicOpen 𝒜 ((x i : A))) ≃ₗ[R] Γ(G, basicOpen 𝒜 ((x i : A))) :=
  Scheme.Modules.openSectionsLinearEquivOfIso π
    (Scheme.Modules.tensorRightIso G (ProjectiveSpectrum.Twist.zeroIso 𝒜) ≪≫
      Scheme.Modules.tensorUnitIso G) (basicOpen 𝒜 ((x i : A)))

/-- **Flatness of the sections of a twist on a chart.**  On `D₊(xᵢ)` every twist is trivial, so
the sections of `F(d)` there are flat over the base as soon as those of `F` are. -/
theorem flat_openSections_twistModule_basicOpen (d : ℤ)
    (h : letI := Scheme.Modules.openSectionsModuleOver π G (basicOpen 𝒜 ((x i : A)))
      Module.Flat R Γ(G, basicOpen 𝒜 ((x i : A)))) :
    letI := Scheme.Modules.openSectionsModuleOver π (twistModule 𝒜 G d)
      (basicOpen 𝒜 ((x i : A)))
    Module.Flat R Γ(twistModule 𝒜 G d, basicOpen 𝒜 ((x i : A))) := by
  letI := Scheme.Modules.openSectionsModuleOver π G (basicOpen 𝒜 ((x i : A)))
  letI := Scheme.Modules.openSectionsModuleOver π (twistModule 𝒜 G 0)
    (basicOpen 𝒜 ((x i : A)))
  letI := Scheme.Modules.openSectionsModuleOver π (twistModule 𝒜 G d)
    (basicOpen 𝒜 ((x i : A)))
  haveI : Module.Flat R Γ(G, basicOpen 𝒜 ((x i : A))) := h
  haveI : Module.Flat R Γ(twistModule 𝒜 G 0, basicOpen 𝒜 ((x i : A))) :=
    Module.Flat.of_linearEquiv (chartTwistZeroLinearEquiv 𝒜 π G x i)
  rcases le_or_gt 0 d with hd | hd
  · exact Module.Flat.of_linearEquiv
      (chartTwistLinearEquiv 𝒜 π G x i 0 d.toNat d (by omega)).symm
  · exact Module.Flat.of_linearEquiv
      (chartTwistLinearEquiv 𝒜 π G x i d (-d).toNat 0 (by omega))

end AlgebraicGeometry.Proj

end

end
