module

public import StacksAndModuli.API.NoetherianExactnessLocus

/-!
# Homology modules and localization support

For composable linear maps with zero composite, the middle homology is the quotient of
the kernel of the second map by the image of the first.  This file gives that concrete
module a small API: ordinary exactness is its vanishing, and exactness after localization
at a prime is equivalent to the prime lying outside its support.

These statements isolate the homology-support input in the acyclicity lemma used by the
Buchsbaum--Eisenbud criterion.

Main declarations:

* `LinearMap.Homology`;
* `LinearMap.exact_iff_subsingleton_homology`;
* `LinearMap.notMem_support_homology_iff_exact_localizedMap`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v

variable {R : Type u} [CommRing R]
variable {M N P : Type v}
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable [AddCommGroup P] [Module R P]

namespace LinearMap

/-- A map into the kernel of the next differential, obtained from a zero composite. -/
def homologyBoundary (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hgf : g.comp f = 0) : M →ₗ[R] LinearMap.ker g :=
  f.codRestrict (LinearMap.ker g) fun x ↦ by
    rw [LinearMap.mem_ker]
    exact LinearMap.congr_fun hgf x

@[simp]
theorem ker_subtype_comp_homologyBoundary
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hgf : g.comp f = 0) :
    (LinearMap.ker g).subtype.comp (homologyBoundary f g hgf) = f := by
  ext x
  rfl

/-- The middle homology of a pair of linear maps with zero composite. -/
def Homology (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hgf : g.comp f = 0) : Type v :=
  LinearMap.ker g ⧸ LinearMap.range (homologyBoundary f g hgf)

instance (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hgf : g.comp f = 0) :
    AddCommGroup (Homology f g hgf) := by
  change AddCommGroup
    (LinearMap.ker g ⧸ LinearMap.range (homologyBoundary f g hgf))
  infer_instance

instance (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hgf : g.comp f = 0) :
    Module R (Homology f g hgf) := by
  change Module R
    (LinearMap.ker g ⧸ LinearMap.range (homologyBoundary f g hgf))
  infer_instance

/-- Middle homology of finite-module maps over a Noetherian ring is finite. -/
instance [IsNoetherianRing R] [Module.Finite R N]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hgf : g.comp f = 0) :
    Module.Finite R (Homology f g hgf) := by
  change Module.Finite R
    (LinearMap.ker g ⧸ LinearMap.range (homologyBoundary f g hgf))
  exact Module.Finite.of_surjective
    (hM := Module.Finite.of_fg (IsNoetherian.noetherian (LinearMap.ker g)))
    (LinearMap.range (homologyBoundary f g hgf)).mkQ
    (Submodule.mkQ_surjective
      (LinearMap.range (homologyBoundary f g hgf)))

/-- Exactness is equivalent to surjectivity of the induced map into the kernel. -/
theorem exact_iff_range_homologyBoundary_eq_top
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hgf : g.comp f = 0) :
    Function.Exact f g ↔
      LinearMap.range (homologyBoundary f g hgf) = ⊤ := by
  constructor
  · intro h
    rw [eq_top_iff]
    intro y hy
    obtain ⟨x, hx⟩ := (h y.1).mp y.2
    exact ⟨x, Subtype.ext hx⟩
  · intro h y
    constructor
    · intro hy
      have hmem : (⟨y, hy⟩ : LinearMap.ker g) ∈
          LinearMap.range (homologyBoundary f g hgf) := by
        rw [h]
        exact Submodule.mem_top
      obtain ⟨x, hx⟩ := hmem
      exact ⟨x, congrArg Subtype.val hx⟩
    · rintro ⟨x, rfl⟩
      exact LinearMap.congr_fun hgf x

/-- A pair of maps is exact precisely when its middle homology is trivial. -/
theorem exact_iff_subsingleton_homology
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hgf : g.comp f = 0) :
    Function.Exact f g ↔ Subsingleton (Homology f g hgf) := by
  rw [exact_iff_range_homologyBoundary_eq_top f g hgf, Homology,
    Submodule.Quotient.subsingleton_iff]

/-- Localized exactness is equivalent to surjectivity of the localized map into the
original kernel. -/
theorem exact_localizedMap_iff_surjective_homologyBoundary
    (S : Submonoid R) (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hgf : g.comp f = 0) :
    Function.Exact (LocalizedModule.map S f) (LocalizedModule.map S g) ↔
      Function.Surjective
        (LocalizedModule.map S (homologyBoundary f g hgf)) := by
  let b := homologyBoundary f g hgf
  have hb : (LinearMap.ker g).subtype.comp b = f :=
    ker_subtype_comp_homologyBoundary f g hgf
  constructor
  · intro h
    exact surjective_localizedMap_codRestrict_of_exact f g b hb S h
  · intro h
    apply exact_localizedMap_of_codRestrict_range_eq_top f g b hb S
    change (LinearMap.range b).localized'
      (Localization S) S
      (LocalizedModule.mkLinearMap S (LinearMap.ker g)) = ⊤
    rw [LinearMap.localized'_range_eq_range_localizedMap
      (Localization S) S (LocalizedModule.mkLinearMap S M)
      (LocalizedModule.mkLinearMap S (LinearMap.ker g)) b]
    exact LinearMap.range_eq_top.mpr h

/-- A prime lies outside the support of middle homology exactly when the two maps become
exact after localization at that prime. -/
theorem notMem_support_homology_iff_exact_localizedMap
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hgf : g.comp f = 0)
    (p : PrimeSpectrum R) :
    p ∉ Module.support R (Homology f g hgf) ↔
      Function.Exact
        (LocalizedModule.map p.asIdeal.primeCompl f)
        (LocalizedModule.map p.asIdeal.primeCompl g) := by
  rw [Module.notMem_support_iff]
  change Subsingleton
      (LocalizedModule p.asIdeal.primeCompl
        (LinearMap.ker g ⧸ LinearMap.range (homologyBoundary f g hgf))) ↔ _
  rw [← LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker]
  exact (exact_localizedMap_iff_surjective_homologyBoundary
    p.asIdeal.primeCompl f g hgf).symm

end LinearMap

end

end
