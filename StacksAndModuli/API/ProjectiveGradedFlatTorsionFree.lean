module

public import StacksAndModuli.API.ProjectiveGradedFlat
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Flatness of graded modules over a Dedekind domain

`GradedModule.IsFlat M` asks that every graded piece be a flat module over the base ring.  Over a
Dedekind domain — in particular over the DVRs of the valuative criterion of §2.4 — flatness is
torsion-freeness, so it is inherited by submodules.  That is what makes the "kernel" route to
`Crel.IsFlat` work: `Γ_*(K) ⊆ Γ_*(𝒪(-l)^{⊕r})` is flat because the ambient twisted-free module is.

Main declarations:
- `GradedModule.isFlat_of_isTorsionFree`;
- `GradedModule.IsFlat.of_injective`;
- `GradedModule.IsFlat.coker_of_exact`.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

variable {R : Type u} [CommRing R] [IsDedekindDomain R] {n : ℕ}

/-- Over a Dedekind domain, a graded module whose pieces are torsion-free is flat. -/
theorem isFlat_of_isTorsionFree (M : GradedModule R n)
    (h : ∀ d : ℤ, Module.IsTorsionFree R (M.obj d)) : M.IsFlat := by
  intro d
  haveI := h d
  infer_instance

/-- Over a Dedekind domain, a graded submodule of a flat graded module is flat. -/
theorem IsFlat.of_injective {M N : GradedModule R n} (f : M ⟶ N)
    (hf : ∀ d : ℤ, Function.Injective (f.app d).hom) (hN : N.IsFlat) : M.IsFlat := by
  refine isFlat_of_isTorsionFree M fun d ↦ ?_
  haveI : Module.Flat R (N.obj d) := hN d
  haveI : Module.IsTorsionFree R (N.obj d) := inferInstance
  exact Function.Injective.moduleIsTorsionFree ((f.app d).hom) (hf d)
    (fun r m ↦ map_smul ((f.app d).hom) r m)

/-- **Flatness of a cokernel that embeds in a flat module.**  If `f ⟶ g` is degreewise exact
and the target is flat, the cokernel of `f` is flat.

This is the form §2.4 needs over the DVRs of the valuative criterion: for a twisted-free
presentation `E ↠ Q` with kernel `K`, the graded module `E ⧸ Γ_*(K)` embeds in `Γ_*(Q)`,
which is torsion-free because `Q` is flat over the DVR, so the cokernel is flat even though
the flatness of a quotient is not formal. -/
theorem IsFlat.coker_of_exact {M N P : GradedModule R n} (f : M ⟶ N) (g : N ⟶ P)
    (hex : ∀ d : ℤ, Function.Exact (f.app d).hom (g.app d).hom) (hP : P.IsFlat) :
    (coker f).IsFlat := by
  refine isFlat_of_isTorsionFree (coker f) fun d ↦ ?_
  haveI : Module.Flat R (P.obj d) := hP d
  haveI : Module.IsTorsionFree R (P.obj d) := inferInstance
  let q : (coker f).obj d →ₗ[R] P.obj d :=
    Submodule.liftQ _ (g.app d).hom (by
      rintro x ⟨y, rfl⟩
      exact (hex d).apply_apply_eq_zero y)
  have hq : Function.Injective q := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨x⟩ hx
    have hx0 : (g.app d).hom x = 0 := hx
    obtain ⟨y, hy⟩ := (hex d) x |>.mp hx0
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨y, hy⟩
  exact Function.Injective.moduleIsTorsionFree q hq (fun r m ↦ map_smul q r m)

end AlgebraicGeometry.ProjectiveSpace.GradedModule

end

end
