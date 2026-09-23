module

public import StacksAndModuli.API.AffineOpenAcyclic
public import StacksAndModuli.API.QuasicoherentCokernel

/-!
# Sections of a quasicoherent short exact sequence are exact on an affine open

The affine tilde equivalence identifies a quasicoherent cokernel with the tilde of the
cokernel of global sections.  Consequently `Γ(U, -)` is **exact** on short exact sequences
of quasicoherent module sheaves over every affine open, with no noetherian hypothesis:

`0 → Γ(U, F₁) → Γ(U, F₂) → Γ(U, F₃) → 0`.

Left exactness is formal (`Scheme.Modules.exact_app_of_shortExact` and the mono clause); the
content is the surjectivity on the right.  The older cohomological criterion through affine
acyclicity is retained separately below.

This is the input a graded model of a *quotient* sheaf needs: `Γ_*` is only left exact, so
`Γ_*(E)/Γ_*(K)` is a proper submodule of `Γ_*(Q)` in general, but on each chart `D₊(xᵢ)` of
`Proj` — an affine open — the quotient is computed exactly, which is all that the Čech
criterion `GradedModule.isIso_cechHgrMap_app_zero_of_injective` inspects.

Main declarations:

* `AlgebraicGeometry.Scheme.Modules.surjective_app_of_shortExact_of_subsingleton_HPrime_one`;
* `AlgebraicGeometry.Scheme.Modules.cokernel_π_app_surjective_of_isAffineOpen`;
* `AlgebraicGeometry.Scheme.Modules.surjective_app_of_shortExact_of_isAffineOpen`.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Sections over an open surject when `H'¹` of the kernel vanishes there.  The module-sheaf
form of `CategoryTheory.Sheaf.surjective_app_of_shortExact_of_subsingleton_HPrime_one`. -/
theorem surjective_app_of_shortExact_of_subsingleton_HPrime_one
    {S : ShortComplex X.Modules} (hS : S.ShortExact) (U : X.Opens)
    (h₁ : Subsingleton (((SheafOfModules.toSheaf X.ringCatSheaf).obj S.X₁).H' 1 U)) :
    Function.Surjective (S.g.val.app (op U)).hom :=
  CategoryTheory.Sheaf.surjective_app_of_shortExact_of_subsingleton_HPrime_one
    (shortExact_map_toSheaf hS) U h₁

/-- The projection to the cokernel of a morphism between quasicoherent module sheaves is
surjective on sections over every affine open. -/
theorem cokernel_π_app_surjective_of_isAffineOpen {N M : X.Modules}
    (ι : N ⟶ M) [N.IsQuasicoherent] [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Surjective ((cokernel.π ι).app U).hom := by
  classical
  set j : Spec Γ(X, U) ⟶ X := hU.fromSpec with hj
  have him : j ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]
  let e : (restrictFunctor j).obj (cokernel ι) ≅
      cokernel ((restrictFunctor j).map ι) :=
    PreservesCokernel.iso (restrictFunctor j) ι
  have hcomp : (restrictFunctor j).map (cokernel.π ι) ≫ e.hom =
      cokernel.π ((restrictFunctor j).map ι) :=
    PreservesCokernel.π_iso_hom _ _
  haveI : (cokernel ((restrictFunctor j).map ι)).IsQuasicoherent :=
    isQuasicoherent_cokernel_spec _
  have hsurj : Function.Surjective
      (moduleSpecΓFunctor.map (cokernel.π ((restrictFunctor j).map ι))) :=
    moduleSpecΓFunctor_map_surjective_of_epi _
  intro s
  obtain ⟨m, hm⟩ := hsurj ((e.hom.app ⊤).hom
    (((cokernel ι).presheaf.map (eqToHom him).op).hom s))
  refine ⟨(M.presheaf.map (eqToHom him.symm).op).hom m, ?_⟩
  have hinj : Function.Injective
      (((cokernel ι).presheaf.map (eqToHom him).op).hom) :=
    (ConcreteCategory.bijective_of_isIso
      ((cokernel ι).presheaf.map (eqToHom him).op)).injective
  apply hinj
  have hnat := CategoryTheory.congr_fun
    ((cokernel.π ι).mapPresheaf.naturality (eqToHom him).op)
    ((M.presheaf.map (eqToHom him.symm).op).hom m)
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at hnat
  have hmm : (M.presheaf.map (eqToHom him).op).hom
      ((M.presheaf.map (eqToHom him.symm).op).hom m) = m := by
    rw [← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp,
      eqToHom_trans, eqToHom_refl, op_id]
    exact ConcreteCategory.congr_hom (M.presheaf.map_id _) m
  refine hnat.symm.trans ?_
  rw [hmm]
  apply (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).1
  have happ := CategoryTheory.congr_fun (congrArg
    (fun k : (restrictFunctor j).obj M ⟶
      cokernel ((restrictFunctor j).map ι) => k.app ⊤) hcomp) m
  exact happ.trans hm

/-- **Sections of a short exact sequence of quasicoherent module sheaves surject on every
affine open.**  This is affine exactness of the quasicoherent tilde equivalence and does not
require the affine coordinate ring to be noetherian. -/
theorem surjective_app_of_shortExact_of_isAffineOpen {U : X.Opens} (hU : IsAffineOpen U)
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] :
    Function.Surjective (S.g.val.app (op U)).hom := by
  let e : cokernel S.f ≅ S.X₃ :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel S.f) hS.gIsCokernel
  have he : cokernel.π S.f ≫ e.hom = S.g :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (cokernelIsCokernel S.f) hS.gIsCokernel WalkingParallelPair.one
  change Function.Surjective ((S.g.app U).hom)
  intro y
  obtain ⟨x, hx⟩ := cokernel_π_app_surjective_of_isAffineOpen S.f hU
    ((e.inv.app U).hom y)
  refine ⟨x, ?_⟩
  have happ := CategoryTheory.congr_fun
    (congrArg (fun k : S.X₂ ⟶ S.X₃ => k.app U) he) x
  change (e.hom.app U).hom (((cokernel.π S.f).app U).hom x) =
    (S.g.app U).hom x at happ
  rw [hx] at happ
  have hei : e.inv ≫ e.hom = 𝟙 S.X₃ := e.inv_hom_id
  have hy' := CategoryTheory.congr_fun
    (congrArg (fun k : S.X₃ ⟶ S.X₃ => k.app U) hei) y
  change (e.hom.app U).hom ((e.inv.app U).hom y) =
    (Scheme.Modules.Hom.app (𝟙 S.X₃) U).hom y at hy'
  have hy : (e.hom.app U).hom ((e.inv.app U).hom y) = y := by
    simpa using hy'
  exact happ.symm.trans hy

end AlgebraicGeometry.Scheme.Modules

end

end
