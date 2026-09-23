module

public import StacksAndModuli.API.OpenCoverQuotient

/-!
# A section killed by a morphism locally is killed globally

If a morphism of sheaves of modules sends the restriction of a global section to zero on every
member of an open cover, it sends the section itself to zero.  This is the sheaf axiom plus the
naturality of `Scheme.Modules.Hom.app`, packaged for the finite-cover step of Hartshorne II.5.14.

## Main results

* `AlgebraicGeometry.Scheme.Modules.app_top_eq_zero_of_app_restrict`
* `AlgebraicGeometry.Scheme.Modules.app_restrict`
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M N : X.Modules}

/-- Applying a morphism of sheaves of modules commutes with restriction. -/
theorem app_restrict (Φ : M ⟶ N) {U V : X.Opens} (hUV : U ≤ V) (t : Γ(M, V)) :
    Φ.app U ((M.presheaf.map (homOfLE hUV).op) t)
      = (N.presheaf.map (homOfLE hUV).op) (Φ.app V t) := by
  have hnat := ConcreteCategory.congr_hom (Φ.mapPresheaf.naturality (homOfLE hUV).op) t
  simpa using hnat

/-- A global section that a morphism kills on every member of an open cover is killed
outright. -/
theorem app_top_eq_zero_of_app_restrict (Φ : M ⟶ N)
    {ι : Type*} (U : ι → X.Opens) (hU : (⊤ : X.Opens) ≤ ⨆ i, U i) (t : Γ(M, ⊤))
    (h : ∀ i, Φ.app (U i) ((M.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op) t) = 0) :
    Φ.app ⊤ t = 0 := by
  refine (abSheaf N).eq_of_locally_eq' U ⊤ (fun i ↦ homOfLE le_top) hU _ 0 ?_
  intro i
  rw [map_zero, ← app_restrict Φ (le_top : U i ≤ ⊤) t]
  exact h i

end AlgebraicGeometry.Scheme.Modules
