module

public import StacksAndModuli.API.GlobalSectionsModElement
public import StacksAndModuli.«Section2.1-Intro».«part2.1.3-projective-space-and-hilbert-quot-functors»
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Global sections of flat module sheaves over a DVR

Supporting API for the DVR step in the projectivity proof for Quot.  A base
non-zero-divisor acts injectively on a module sheaf flat over an affine base.  Over a
discrete valuation ring this makes finite global sections free and projective.  If the
first sheaf cohomology vanishes, the global sections of the canonical cokernel are the
reduction of the original global sections modulo the base element.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TensorProduct
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A sheaf of modules flat over an affine base is torsion-free with respect to the
pullback of any non-zero-divisor on the base. -/
lemma Modules.FlatOver.smul_regular_sections
    {P T : Scheme.{u}} {Q : P.Modules} {p : P ⟶ T} (hflat : Q.FlatOver p)
    (hT : IsAffineOpen (⊤ : T.Opens)) (w : Γ(T, ⊤))
    (hw : w ∈ nonZeroDivisors Γ(T, ⊤)) (V : P.affineOpens) (q : Γ(Q, V.1))
    (h : (P.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom
      ((p.app ⊤).hom w) • q = 0) :
    q = 0 := by
  have hVle : V.1 ≤ p ⁻¹ᵁ (⊤ : T.Opens) := le_top
  letI := Module.compHom Γ(Q, V.1)
    ((P.presheaf.map (homOfLE hVle).op).hom.comp (p.app ⊤).hom)
  haveI : Module.Flat Γ(T, ⊤) Γ(Q, V.1) := hflat V ⟨⊤, hT⟩ hVle
  have hreg : IsSMulRegular Γ(Q, V.1) w :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors hw
  have hsm : w • q = w • (0 : Γ(Q, V.1)) := by
    rw [smul_zero]
    exact h
  exact hreg hsm

/-- Multiplication by the pullback of a non-zero-divisor on an affine base is a
monomorphism on every module sheaf flat over that base. -/
lemma Modules.FlatOver.mulByGlobalSection_mono
    {P T : Scheme.{u}} {Q : P.Modules} {p : P ⟶ T} (hflat : Q.FlatOver p)
    (hT : IsAffineOpen (⊤ : T.Opens)) (w : Γ(T, ⊤))
    (hw : w ∈ nonZeroDivisors Γ(T, ⊤)) :
    Mono (Q.mulByGlobalSection ((p.app ⊤).hom w)) := by
  apply Modules.mulByGlobalSection_mono_of_smul_eq_zero_affine
  intro V q hq
  exact hflat.smul_regular_sections hT w hw V q hq

/-- For a flat module sheaf over an affine base, the cokernel of multiplication by a
base non-zero-divisor has global sections obtained by reducing modulo that element once
`H¹` of the sheaf vanishes. -/
noncomputable def Modules.FlatOver.quotientTensorGlobalSectionsCokernelLinearEquiv
    {R : CommRingCat.{u}} {P : Scheme.{u}} {Q : P.Modules}
    {p : P ⟶ Spec R} (hflat : Q.FlatOver p) (r : R)
    (hr : (Scheme.ΓSpecIso R).inv.hom r ∈ nonZeroDivisors Γ(Spec R, ⊤))
    (hH1 : Subsingleton (((SheafOfModules.toSheaf _).obj Q).H 1)) :
    letI := Modules.globalSectionsModule p Q
    letI := Modules.globalSectionsModule p
      (cokernel (Q.mulByGlobalSection ((Modules.baseRingHom p).hom r)))
    ((R ⧸ Ideal.span {r}) ⊗[R] Γ(Q, ⊤)) ≃ₗ[R]
      Γ(cokernel (Q.mulByGlobalSection ((Modules.baseRingHom p).hom r)), ⊤) := by
  let w : Γ(Spec R, ⊤) := (Scheme.ΓSpecIso R).inv.hom r
  have ht : (Modules.baseRingHom p).hom r = (p.app ⊤).hom w := rfl
  letI : Mono (Q.mulByGlobalSection ((Modules.baseRingHom p).hom r)) := by
    rw [ht]
    exact hflat.mulByGlobalSection_mono (isAffineOpen_top (Spec R)) w hr
  exact Modules.quotientTensorGlobalSectionsCokernelLinearEquiv p r Q hH1

/-- Non-zero-divisors transfer backwards along ring isomorphisms. -/
lemma mem_nonZeroDivisors_of_commRingCatIso {A B : CommRingCat.{u}} (e : A ≅ B)
    (b : B) (hb : b ∈ nonZeroDivisors B) : e.inv.hom b ∈ nonZeroDivisors A := by
  have key : ∀ x : A, x * e.inv.hom b = 0 → x = 0 := by
    intro x hx
    have h1 : e.hom.hom (x * e.inv.hom b) = 0 := by rw [hx, map_zero]
    rw [map_mul] at h1
    have h2 : e.hom.hom (e.inv.hom b) = b := by
      rw [← CommRingCat.comp_apply, e.inv_hom_id]
      rfl
    rw [h2] at h1
    have h3 : e.hom.hom x = 0 := hb.2 _ h1
    have h4 : x = e.inv.hom (e.hom.hom x) := by
      rw [← CommRingCat.comp_apply, e.hom_inv_id]
      rfl
    rw [h4, h3, map_zero]
  rw [mem_nonZeroDivisors_iff]
  exact ⟨fun x hx ↦ key x (by rwa [mul_comm] at hx), key⟩

/-- Finite global sections of a module sheaf flat over the spectrum of a DVR are
projective. -/
theorem Modules.FlatOver.projective_globalSections_of_finite
    {R : CommRingCat.{u}} [IsDomain R] [IsDiscreteValuationRing R]
    {P : Scheme.{u}} {Q : P.Modules} {p : P ⟶ Spec R}
    (hflat : Q.FlatOver p) (ϖ : R) (hϖ : Irreducible ϖ)
    (hfinite : letI := Modules.globalSectionsModule p Q
      Module.Finite R Γ(Q, ⊤)) :
    letI := Modules.globalSectionsModule p Q
    Module.Projective R Γ(Q, ⊤) := by
  let w : Γ(Spec R, ⊤) := (Scheme.ΓSpecIso R).inv.hom ϖ
  have hw : w ∈ nonZeroDivisors Γ(Spec R, ⊤) :=
    mem_nonZeroDivisors_of_commRingCatIso (Scheme.ΓSpecIso R) ϖ
      (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero)
  have ht : (Modules.baseRingHom p).hom ϖ = (p.app ⊤).hom w := rfl
  letI : Mono (Q.mulByGlobalSection ((Modules.baseRingHom p).hom ϖ)) := by
    rw [ht]
    exact hflat.mulByGlobalSection_mono (isAffineOpen_top (Spec R)) w hw
  exact Modules.projective_globalSections_of_finite_of_mulByGlobalSection_mono
    p ϖ hϖ Q hfinite

end AlgebraicGeometry.Scheme
