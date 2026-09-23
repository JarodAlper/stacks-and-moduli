module

public import StacksAndModuli.API.ProjChartFlatSections
public import StacksAndModuli.API.ProjectiveGradedFlatTorsionFree
public import StacksAndModuli.API.ProjGammaStar
public import StacksAndModuli.«Section2.1-Intro».«part2.1.3-projective-space-and-hilbert-quot-functors»
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# `Γ_*` of a sheaf flat over the base is degreewise flat

`RelativeCohomology.cech`'s `IsFlat` is degreewise flatness of a graded module, and for
`Γ_*(F)` that is flatness of `Γ(F(d), ⊤)` over the base ring — sections over a *non-affine*
open, of a twist that is not globally trivial.  The hypothesis available in §2.4 is
`Scheme.Modules.FlatOver`, a condition on affine opens.  This file bridges the two:

* `Scheme.Modules.isTorsionFree_openSections_of_flatOver` — on an affine open, `FlatOver` gives
  torsion-freeness over the base ring.  The only content is that the two module structures
  agree: `FlatOver` uses `Γ(Spec R, ⊤)` acting through `π.app ⊤`, while
  `Scheme.Modules.openSectionsModuleOver` uses `R` acting through
  `baseRingHom π = (ΓSpecIso R).inv ≫ π.appTop`; the composites are definitionally equal, and
  `(ΓSpecIso R).inv` carries nonzerodivisors to nonzerodivisors.
* `AlgebraicGeometry.Proj.isFlat_gammaStar_of_flatOver` — the assembly, over a Dedekind base:
  charts are affine, every twist is trivial on a chart
  (`Proj.flat_openSections_twistModule_basicOpen`), and torsion-freeness descends from a cover
  to `⊤` (`Scheme.Modules.isTorsionFree_globalSections_of_cover`).

Main declarations:

* `AlgebraicGeometry.Scheme.Modules.isTorsionFree_openSections_of_flatOver`;
* `AlgebraicGeometry.Scheme.Modules.flat_openSections_of_flatOver`;
* `AlgebraicGeometry.Proj.isFlat_gammaStar_of_flatOver`.
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
open scoped nonZeroDivisors

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {R : CommRingCat.{u}}

/-- The sections of a sheaf flat over an affine base are torsion-free on every affine open. -/
theorem isTorsionFree_openSections_of_flatOver
    (π : X ⟶ Spec R) (M : X.Modules) (hflat : M.FlatOver π) (U : X.affineOpens) :
    letI := openSectionsModuleOver π M U.1
    Module.IsTorsionFree R Γ(M, U.1) := by
  letI := openSectionsModuleOver π M U.1
  have hT : IsAffineOpen (⊤ : (Spec R).Opens) := isAffineOpen_top _
  have hle : U.1 ≤ π ⁻¹ᵁ (⊤ : (Spec R).Opens) := le_top
  letI := Module.compHom Γ(M, U.1)
    ((X.presheaf.map (homOfLE hle).op).hom.comp ((π.app ⊤).hom))
  haveI : Module.Flat Γ(Spec R, ⊤) Γ(M, U.1) := hflat U ⟨⊤, hT⟩ hle
  refine ⟨fun r hr => ?_⟩
  have hrR : r ∈ nonZeroDivisors ((R : Type u)) := hr.mem_nonZeroDivisors
  have hw : (Scheme.ΓSpecIso R).inv.hom r ∈ nonZeroDivisors ((Γ(Spec R, ⊤) : Type u)) := by
    have key : ∀ y : Γ(Spec R, ⊤), (Scheme.ΓSpecIso R).inv.hom r * y = 0 → y = 0 := by
      intro y hy
      have h1 : (Scheme.ΓSpecIso R).hom.hom ((Scheme.ΓSpecIso R).inv.hom r * y) = 0 := by
        rw [hy, map_zero]
      rw [map_mul] at h1
      have h2 : (Scheme.ΓSpecIso R).hom.hom ((Scheme.ΓSpecIso R).inv.hom r) = r := by
        rw [← CommRingCat.comp_apply, (Scheme.ΓSpecIso R).inv_hom_id]
        rfl
      rw [h2] at h1
      have h3 : (Scheme.ΓSpecIso R).hom.hom y = 0 :=
        (mem_nonZeroDivisors_iff.mp hrR).1 _ h1
      have h4 : (Scheme.ΓSpecIso R).inv.hom ((Scheme.ΓSpecIso R).hom.hom y) = y := by
        rw [← CommRingCat.comp_apply, (Scheme.ΓSpecIso R).hom_inv_id]
        rfl
      rw [← h4, h3, map_zero]
    exact mem_nonZeroDivisors_iff.mpr ⟨key, fun y hy => key y (by rw [mul_comm]; exact hy)⟩
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Γ(M, U.1)) hw
  intro a b hab
  exact hreg hab

/-- The sections of a sheaf flat over an affine base are flat over the base ring on every
affine open.  `FlatOver` states flatness over `Γ(Spec R, ⊤)`; the passage to `R` is
`Module.Flat.trans` along the ring isomorphism `Scheme.ΓSpecIso`. -/
theorem flat_openSections_of_flatOver
    (π : X ⟶ Spec R) (M : X.Modules) (hflat : M.FlatOver π) (U : X.affineOpens) :
    letI := openSectionsModuleOver π M U.1
    Module.Flat R Γ(M, U.1) := by
  letI := openSectionsModuleOver π M U.1
  have hT : IsAffineOpen (⊤ : (Spec R).Opens) := isAffineOpen_top _
  have hle : U.1 ≤ π ⁻¹ᵁ (⊤ : (Spec R).Opens) := le_top
  letI := Module.compHom Γ(M, U.1)
    ((X.presheaf.map (homOfLE hle).op).hom.comp ((π.app ⊤).hom))
  haveI hS : Module.Flat Γ(Spec R, ⊤) Γ(M, U.1) := hflat U ⟨⊤, hT⟩ hle
  letI : Algebra R Γ(Spec R, ⊤) := ((Scheme.ΓSpecIso R).inv.hom).toAlgebra
  haveI : Module.Flat R Γ(Spec R, ⊤) := by
    refine Module.Flat.of_linearEquiv (M := (R : Type u)) (N := Γ(Spec R, ⊤)) ?_
    refine
      { toFun := (Scheme.ΓSpecIso R).hom.hom
        map_add' := map_add _
        map_smul' := ?_
        invFun := (Scheme.ΓSpecIso R).inv.hom
        left_inv := ?_
        right_inv := ?_ }
    · intro r s
      change (Scheme.ΓSpecIso R).hom.hom ((Scheme.ΓSpecIso R).inv.hom r * s)
        = r * (Scheme.ΓSpecIso R).hom.hom s
      rw [map_mul, ← CommRingCat.comp_apply, (Scheme.ΓSpecIso R).inv_hom_id]
      rfl
    · intro s
      rw [← CommRingCat.comp_apply, (Scheme.ΓSpecIso R).hom_inv_id]; rfl
    · intro s
      rw [← CommRingCat.comp_apply, (Scheme.ΓSpecIso R).inv_hom_id]; rfl
  haveI : IsScalarTower R Γ(Spec R, ⊤) Γ(M, U.1) := by
    refine ⟨fun r s x => ?_⟩
    change ((X.presheaf.map (homOfLE hle).op).hom ((π.app ⊤).hom
        ((Scheme.ΓSpecIso R).inv.hom r * s))) • x
      = (openRingHom π U.1).hom r • ((X.presheaf.map (homOfLE hle).op).hom
        ((π.app ⊤).hom s) • x)
    rw [map_mul, map_mul, mul_smul]
    rfl
  exact Module.Flat.trans R Γ(Spec R, ⊤) Γ(M, U.1)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

open ProjectiveSpectrum.Twist AlgebraicGeometry.ProjectiveSpace

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {n : ℕ} {R : CommRingCat.{u}} [IsDedekindDomain (R : Type u)]
variable (π : Proj 𝒜 ⟶ Spec R) (G : (Proj 𝒜).Modules) (x : Fin (n + 1) → 𝒜 1)

/-- **`Γ_*` of a sheaf flat over the base is degreewise flat.**  The charts `D₊(xᵢ)` are affine,
so `FlatOver` applies there; every twist is trivial on a chart, so the twisted chart sections
are flat too; and torsion-freeness of the global sections follows from the sheaf axiom. -/
theorem isFlat_gammaStar_of_flatOver
    (hcover : (⊤ : (Proj 𝒜).Opens) ≤ ⨆ k : Fin (n + 1), basicOpen 𝒜 ((x k : A)))
    (hflat : G.FlatOver π) :
    (gammaStar 𝒜 π G x).IsFlat := by
  refine GradedModule.isFlat_of_isTorsionFree _ fun d => ?_
  have hchart : ∀ k : Fin (n + 1),
      letI := Scheme.Modules.openSectionsModuleOver π (twistModule 𝒜 G d)
        (basicOpen 𝒜 ((x k : A)))
      Module.IsTorsionFree (R : Type u) Γ(twistModule 𝒜 G d, basicOpen 𝒜 ((x k : A))) := by
    intro k
    letI := Scheme.Modules.openSectionsModuleOver π G (basicOpen 𝒜 ((x k : A)))
    letI := Scheme.Modules.openSectionsModuleOver π (twistModule 𝒜 G d)
      (basicOpen 𝒜 ((x k : A)))
    haveI : Module.IsTorsionFree (R : Type u) Γ(G, basicOpen 𝒜 ((x k : A))) :=
      Scheme.Modules.isTorsionFree_openSections_of_flatOver π G hflat
        ⟨basicOpen 𝒜 ((x k : A)), isAffineOpen_basicOpen 𝒜 _ (x k).2 Nat.one_pos⟩
    haveI : Module.Flat (R : Type u) Γ(twistModule 𝒜 G d, basicOpen 𝒜 ((x k : A))) :=
      flat_openSections_twistModule_basicOpen 𝒜 π G x k d inferInstance
    infer_instance
  exact Scheme.Modules.isTorsionFree_globalSections_of_cover π (twistModule 𝒜 G d)
    (fun k => basicOpen 𝒜 ((x k : A))) hcover hchart

end AlgebraicGeometry.Proj

end

end
