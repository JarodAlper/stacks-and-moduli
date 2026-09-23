module

public import StacksAndModuli.API.PrincipalClosedFiberGlobalSections
public import StacksAndModuli.API.FlatOverGlobalSectionsDVR

/-!
# Global-section rank on the closed fibre of a DVR

This file turns the principal closed-fibre base-change equivalence into a
dimension formula.  For finite projective global sections over a DVR, the
dimension after reduction by a uniformizer equals the relative rank.  For a
flat sheaf, projectivity follows automatically from finiteness.

Main declarations:

* `Scheme.Modules.finrank_principalClosedFiber_globalSections_eq`;
* `Scheme.Modules.FlatOver.finrank_principalClosedFiber_globalSections_eq_of_finite`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TensorProduct
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- If the uniformizer cokernel is the pushforward of the closed-fibre
pullback and `H¹` vanishes, finite projective global sections have the same
rank as global sections on that closed fibre. -/
theorem finrank_principalClosedFiber_globalSections_eq
    (R : CommRingCat.{u}) [IsDomain R] [IsDiscreteValuationRing R]
    {X Z : Scheme.{u}} (p : X ⟶ Spec R)
    (ϖ : R) (hϖ : Irreducible ϖ)
    (i : Z ⟶ X)
    (pZ : Z ⟶ Spec (principalClosedFiberRing ϖ))
    (hbase : i ≫ p =
      pZ ≫ Spec.map (principalClosedFiberRingHom ϖ))
    (M : X.Modules)
    [Mono (M.mulByGlobalSection ((baseRingHom p).hom ϖ))]
    (hH1 : Subsingleton (((SheafOfModules.toSheaf _).obj M).H 1))
    (eC : cokernel
        (M.mulByGlobalSection ((baseRingHom p).hom ϖ)) ≅
      (pushforward i).obj ((pullback i).obj M))
    (hfinite : letI := globalSectionsModule p M
      Module.Finite R Γ(M, ⊤))
    (hprojective : letI := globalSectionsModule p M
      Module.Projective R Γ(M, ⊤)) :
    let S := principalClosedFiberRing ϖ
    let F := (pullback i).obj M
    letI := globalSectionsModule p M
    letI := globalSectionsModule pZ F
    Module.finrank S Γ(F, ⊤) = Module.finrank R Γ(M, ⊤) := by
  dsimp only
  let S := principalClosedFiberRing ϖ
  let F := (pullback i).obj M
  let _ : (Ideal.span {ϖ} : Ideal R).IsMaximal := by
    rw [← hϖ.maximalIdeal_eq]
    infer_instance
  letI : Field S := Ideal.Quotient.field (Ideal.span {ϖ})
  letI : Module R Γ(M, ⊤) := globalSectionsModule p M
  letI : Module.Finite R Γ(M, ⊤) := hfinite
  letI : Module.Projective R Γ(M, ⊤) := hprojective
  letI : Module S Γ(F, ⊤) := globalSectionsModule pZ F
  rw [←
    (quotientTensorGlobalSectionsPullbackLinearEquiv_of_cokernelIso
      p ϖ i pZ hbase M hH1 eC).finrank_eq]
  exact Module.finrank_tensorProduct_eq_of_finite_projective_of_isLocalRing

/-- For a flat module sheaf over a DVR, finiteness of `H⁰`, vanishing of
`H¹`, and the geometric uniformizer-cokernel identification imply the
closed-fibre dimension formula.  Flatness supplies both monicity of
multiplication by the uniformizer and projectivity of `H⁰`. -/
theorem FlatOver.finrank_principalClosedFiber_globalSections_eq_of_finite
    (R : CommRingCat.{u}) [IsDomain R] [IsDiscreteValuationRing R]
    {X Z : Scheme.{u}} (p : X ⟶ Spec R)
    (ϖ : R) (hϖ : Irreducible ϖ)
    (i : Z ⟶ X)
    (pZ : Z ⟶ Spec (principalClosedFiberRing ϖ))
    (hbase : i ≫ p =
      pZ ≫ Spec.map (principalClosedFiberRingHom ϖ))
    (M : X.Modules) (hflat : M.FlatOver p)
    (hH1 : Subsingleton (((SheafOfModules.toSheaf _).obj M).H 1))
    (eC : cokernel
        (M.mulByGlobalSection ((baseRingHom p).hom ϖ)) ≅
      (pushforward i).obj ((pullback i).obj M))
    (hfinite : letI := globalSectionsModule p M
      Module.Finite R Γ(M, ⊤)) :
    let S := principalClosedFiberRing ϖ
    let F := (pullback i).obj M
    letI := globalSectionsModule p M
    letI := globalSectionsModule pZ F
    Module.finrank S Γ(F, ⊤) = Module.finrank R Γ(M, ⊤) := by
  let w : Γ(Spec R, ⊤) := (Scheme.ΓSpecIso R).inv.hom ϖ
  have hw : w ∈ nonZeroDivisors Γ(Spec R, ⊤) :=
    mem_nonZeroDivisors_of_commRingCatIso (Scheme.ΓSpecIso R) ϖ
      (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero)
  have ht : (baseRingHom p).hom ϖ = (p.app ⊤).hom w := rfl
  letI : Mono
      (M.mulByGlobalSection ((baseRingHom p).hom ϖ)) := by
    rw [ht]
    exact hflat.mulByGlobalSection_mono
      (isAffineOpen_top (Spec R)) w hw
  have hprojective := hflat.projective_globalSections_of_finite
    ϖ hϖ hfinite
  exact finrank_principalClosedFiber_globalSections_eq
    R p ϖ hϖ i pZ hbase M hH1 eC hfinite hprojective

end AlgebraicGeometry.Scheme.Modules

end
