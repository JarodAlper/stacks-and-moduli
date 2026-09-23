module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Kernel vanishing under right-exact functors

A left-adjoint functor between abelian categories need not preserve kernels.  It does,
however, preserve the presentation of an epimorphism as the cokernel of its kernel.
Consequently, after applying the functor, vanishing on the mapped original kernel is
equivalent to vanishing on the kernel of the mapped epimorphism.
-/

@[expose] public section

noncomputable section

open CategoryTheory.Limits

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u} [Category.{w} D] [Abelian D]

/-- The canonical retraction onto the kernel of a split epimorphism.  Together
with the chosen section of the epimorphism, this is the standard direct-sum
decomposition of its source. -/
noncomputable def kernelRetractionOfSplitEpi
    {X Y : C} (p : X ⟶ Y) [IsSplitEpi p] : X ⟶ kernel p :=
  kernel.lift p (𝟙 X - p ≫ section_ p) (by simp)

@[reassoc (attr := simp)]
lemma kernelRetractionOfSplitEpi_comp_ι
    {X Y : C} (p : X ⟶ Y) [IsSplitEpi p] :
    kernelRetractionOfSplitEpi p ≫ kernel.ι p = 𝟙 X - p ≫ section_ p := by
  exact kernel.lift_ι _ _ _

@[reassoc (attr := simp)]
lemma kernel_ι_comp_kernelRetractionOfSplitEpi
    {X Y : C} (p : X ⟶ Y) [IsSplitEpi p] :
    kernel.ι p ≫ kernelRetractionOfSplitEpi p = 𝟙 (kernel p) := by
  rw [← cancel_mono (kernel.ι p)]
  simp [kernelRetractionOfSplitEpi]

/-- An additive functor preserves the kernel of a split epimorphism.  This
local form is useful for right-exact geometric functors: a vector-bundle
quotient of a finite free object splits locally even when it need not split
globally. -/
lemma kernelComparison_isIso_of_isSplitEpi
    (F : C ⥤ D) [Functor.Additive F]
    {X Y : C} (p : X ⟶ Y) [IsSplitEpi p] :
    IsIso (kernelComparison p F) := by
  let r : X ⟶ kernel p := kernelRetractionOfSplitEpi p
  have hir : kernel.ι p ≫ r = 𝟙 (kernel p) :=
    kernel_ι_comp_kernelRetractionOfSplitEpi p
  letI : IsSplitMono (F.map (kernel.ι p)) :=
    IsSplitMono.mk' {
      retraction := F.map r
      id := by rw [← F.map_comp, hir, F.map_id] }
  let g : kernel (F.map p) ⟶ F.obj (kernel p) :=
    kernel.ι (F.map p) ≫ F.map r
  refine ⟨⟨g, ?_, ?_⟩⟩
  · apply (cancel_mono (F.map (kernel.ι p))).mp
    simp only [g, Category.assoc]
    rw [kernelComparison_comp_ι_assoc, ← Category.assoc,
      ← F.map_comp, hir, F.map_id, Category.id_comp]
  · apply (cancel_mono (kernel.ι (F.map p))).mp
    simp only [g, Category.assoc, kernelComparison_comp_ι,
      Category.id_comp]
    rw [← F.map_comp, kernelRetractionOfSplitEpi_comp_ι]
    simp

/-- A left adjoint between abelian categories maps the kernel of an epimorphism
epimorphically onto the kernel of its image.  This is the kernel-comparison form of right
exactness. -/
lemma kernelComparison_epi_of_isLeftAdjoint
    (F : C ⥤ D) [Functor.Additive F] [Functor.IsLeftAdjoint F]
    {X Y : C} (p : X ⟶ Y) [Epi p] :
    Epi (kernelComparison p F) := by
  let S := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
  have hS : S.Exact := ShortComplex.exact_kernel p
  have hpres : PreservesFiniteColimits F := inferInstance
  have hright := ((Functor.preservesFiniteColimits_tfae F).out 3 1).mp hpres
  have hmap : (S.map F).Exact ∧ Epi (F.map S.g) :=
    hright S ⟨hS, inferInstance⟩
  have h := (S.map F).exact_iff_epi_kernel_lift.mp hmap.1
  simpa only [S, ShortComplex.map, kernelComparison] using h

/-- A left adjoint detects the same vanishing condition using the image of the
original kernel or the kernel of the image epimorphism. -/
lemma map_kernel_ι_comp_eq_zero_iff_of_isLeftAdjoint
    (F : C ⥤ D) [F.IsLeftAdjoint]
    {X Y Z : C} (p : X ⟶ Y) [Epi p] (q : X ⟶ Z) :
    F.map (kernel.ι p ≫ q) = 0 ↔
      kernel.ι (F.map p) ≫ F.map q = 0 := by
  constructor
  · intro h
    have hmap : F.map (kernel.ι p) ≫ F.map q = 0 := by
      simpa only [F.map_comp] using h
    let hp : IsColimit (CokernelCofork.ofπ p (kernel.condition p)) :=
      Abelian.epiIsCokernelOfKernel _ (limit.isLimit _)
    let hpF := (CokernelCofork.ofπ p (kernel.condition p)).mapIsColimit hp F
    obtain ⟨d, hd⟩ := CokernelCofork.IsColimit.desc' hpF (F.map q) hmap
    let d' : F.obj Y ⟶ F.obj Z := d
    have hd' : F.map p ≫ d' = F.map q := by
      exact hd
    rw [← hd', ← Category.assoc, kernel.condition, zero_comp]
  · intro h
    rw [F.map_comp, ← kernelComparison_comp_ι_assoc, h, comp_zero]

end CategoryTheory

end

end
