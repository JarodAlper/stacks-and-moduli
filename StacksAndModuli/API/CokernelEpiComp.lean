module

public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Cokernels are unchanged by epimorphic precomposition

If `g : W ⟶ X` is an epimorphism, then `f : X ⟶ Y` and `g ≫ f` have the same
cokernel.  Mathlib already proves that every chosen cokernel cocone of `f` is a cokernel
cocone of `g ≫ f`; this file packages the resulting canonical isomorphism between the
chosen cokernel objects and records its compatibility with the two cokernel projections.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- Precomposing a morphism by an epimorphism does not change its chosen cokernel. -/
noncomputable def cokernelEpiCompIso
    {W X Y : C} (g : W ⟶ X) [Epi g] (f : X ⟶ Y)
    [HasCokernel f] [HasCokernel (g ≫ f)] :
    cokernel (g ≫ f) ≅ cokernel f :=
  IsColimit.coconePointUniqueUpToIso
    (colimit.isColimit (parallelPair (g ≫ f) 0))
    (isCokernelEpiComp
      (colimit.isColimit (parallelPair f 0)) g rfl)

/-- The canonical comparison from `cokernel (g ≫ f)` to `cokernel f` carries the
cokernel projection of the composite to the cokernel projection of `f`. -/
@[reassoc (attr := simp)]
lemma cokernel_π_comp_cokernelEpiCompIso_hom
    {W X Y : C} (g : W ⟶ X) [Epi g] (f : X ⟶ Y)
    [HasCokernel f] [HasCokernel (g ≫ f)] :
    cokernel.π (g ≫ f) ≫ (cokernelEpiCompIso g f).hom = cokernel.π f :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit (parallelPair (g ≫ f) 0))
    (isCokernelEpiComp
      (colimit.isColimit (parallelPair f 0)) g rfl)
    WalkingParallelPair.one

/-- In an abelian category, an epimorphism is the cokernel of its kernel inclusion. -/
noncomputable def cokernelKernelIsoOfEpi
    {C : Type*} [Category C] [Abelian C]
    {X Y : C} (f : X ⟶ Y) [Epi f] : cokernel (kernel.ι f) ≅ Y :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel f))

/-- The canonical cokernel-of-kernel comparison carries its cokernel projection to the
original epimorphism. -/
@[reassoc (attr := simp)]
lemma cokernel_π_comp_cokernelKernelIsoOfEpi_hom
    {C : Type*} [Category C] [Abelian C]
    {X Y : C} (f : X ⟶ Y) [Epi f] :
    cokernel.π (kernel.ι f) ≫ (cokernelKernelIsoOfEpi f).hom = f :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _)
    (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel f)) WalkingParallelPair.one

/-- If an epimorphism onto the kernel supplies a family of relations for an epimorphism
`f`, then the cokernel of those relations is canonically the target of `f`. -/
noncomputable def cokernelEpiCompKernelIsoOfEpi
    {C : Type*} [Category C] [Abelian C]
    {W X Y : C} (f : X ⟶ Y) [Epi f] (g : W ⟶ kernel f) [Epi g] :
    cokernel (g ≫ kernel.ι f) ≅ Y :=
  cokernelEpiCompIso g (kernel.ι f) ≪≫ cokernelKernelIsoOfEpi f

/-- The preceding reconstruction isomorphism identifies its cokernel projection with the
original epimorphism. -/
@[reassoc (attr := simp)]
lemma cokernel_π_comp_cokernelEpiCompKernelIsoOfEpi_hom
    {C : Type*} [Category C] [Abelian C]
    {W X Y : C} (f : X ⟶ Y) [Epi f] (g : W ⟶ kernel f) [Epi g] :
    cokernel.π (g ≫ kernel.ι f) ≫
        (cokernelEpiCompKernelIsoOfEpi f g).hom = f := by
  simp [cokernelEpiCompKernelIsoOfEpi]

end CategoryTheory.Limits

end
