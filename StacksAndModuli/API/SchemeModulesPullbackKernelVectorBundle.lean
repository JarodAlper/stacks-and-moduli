module

public import StacksAndModuli.API.RightExactFunctorKernelVanishing
public import StacksAndModuli.API.AffineQuasicoherentSplit
public import StacksAndModuli.API.SchemeModulesOpenCover
public import StacksAndModuli.API.SchemeModulesPullbackTensorComp
public import StacksAndModuli.API.QuasicoherentVectorBundles
public import StacksAndModuli.API.FlatOverDescent
public import StacksAndModuli.API.OpenImmersionModuleBaseChange

/-!
# Pullback of a kernel with vector-bundle quotient

Pullback of module sheaves is right exact but does not preserve arbitrary kernels.  It
does preserve the kernel of an epimorphism whose target is finite locally free.  Indeed,
after restriction to an affine open of the target the epimorphism splits, and every
further pullback preserves the kernel of a split epimorphism.  Pullback-composition
coherence then transports the local statement to the pulled affine cover of the source.

The main declaration is
`AlgebraicGeometry.Scheme.Modules.pullback_kernelComparison_isIso_of_epi_of_isFiniteLocallyFree`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u u₁ u₂ u₃ v₁ v₂ v₃

namespace CategoryTheory.Limits

/-- The kernel comparison for a composite of additive functors is the composite of
the two successive kernel comparisons. -/
lemma kernelComparison_comp_functors
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    {E : Type u₃} [Category.{v₃} E] [Abelian E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    {X Y : C} (p : X ⟶ Y) :
    G.map (kernelComparison p F) ≫ kernelComparison (F.map p) G =
      kernelComparison p (F ⋙ G) := by
  apply (cancel_mono (kernel.ι ((F ⋙ G).map p))).1
  rw [kernelComparison_comp_ι]
  simp only [Functor.comp_map, Category.assoc,
    kernelComparison_comp_ι, ← G.map_comp]

end CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Sections of a finite locally free quasicoherent sheaf over an affine open
are a finite projective module.  Kept here at low dependency so kernel
preservation does not depend on the projective-zero Quot construction. -/
lemma finiteLocallyFree_sections_finite_projective_affine
    {X : Scheme.{u}} {M : X.Modules} [M.IsQuasicoherent]
    (hM : IsFiniteLocallyFree M) (U : X.affineOpens) :
    Module.Finite Γ(X, U.1) Γ(M, U.1) ∧
      Module.Projective Γ(X, U.1) Γ(M, U.1) := by
  let j := U.2.fromSpec
  let N := (pullback j).obj M
  have hN : IsFiniteLocallyFree N := hM.pullback j
  have hcoord := moduleSpecΓFunctor_finite_projective_of_isFiniteLocallyFree N hN
  have htop := AlgebraicGeometry.moduleSpecΓFunctor_finite_projective_top N
    hcoord.1 hcoord.2
  have hsections := sections_finite_projective_of_pullback_openImmersion
    j M (⊤ : (Spec (.of Γ(X, U.1))).Opens) htop.1 htop.2
  have himage : j ''ᵁ (⊤ : (Spec (.of Γ(X, U.1))).Opens) = U.1 := by
    rw [Scheme.Hom.image_top_eq_opensRange, U.2.opensRange_fromSpec]
  rw [himage] at hsections
  exact hsections

set_option maxHeartbeats 2000000 in
-- The proof transports kernel preservation through four pullback functors on each chart.
/-- Pullback along an arbitrary scheme morphism preserves the kernel of an epimorphism
of quasicoherent modules when the quotient is finite locally free. -/
lemma pullback_kernelComparison_isIso_of_epi_of_isFiniteLocallyFree
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (p : M ⟶ N) [Epi p] (hN : IsFiniteLocallyFree N) :
    IsIso (kernelComparison p (pullback f)) := by
  let U := Y.affineOpenCover.openCover
  let V : X.OpenCover := U.pullback₁ f
  apply isIso_of_restrict_openCover _ V
  intro i
  let j : U.X i ⟶ Y := U.f i
  let k : V.X i ⟶ X := V.f i
  let g : V.X i ⟶ U.X i := U.pullbackHom f i
  let F := pullback f
  let G := pullback k
  let R := pullback j
  let H := pullback g
  let pU : R.obj M ⟶ R.obj N := R.map p
  letI : (R.obj M).IsQuasicoherent := inferInstance
  letI : (R.obj N).IsQuasicoherent := inferInstance
  letI : Epi pU := inferInstance
  have hNU : IsFiniteLocallyFree (R.obj N) := hN.pullback j
  let W : (U.X i).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  have hs := finiteLocallyFree_sections_finite_projective_affine hNU W
  letI : IsSplitEpi pU :=
    isSplitEpi_of_epi_of_projective_sections_of_isAffine pU hs.1 hs.2
  letI : IsIso (kernelComparison pU H) :=
    kernelComparison_isIso_of_isSplitEpi H pU
  letI : PreservesLimit (parallelPair pU 0) H :=
    PreservesKernel.of_iso_comparison H pU
  letI : PreservesLimit (parallelPair p 0) (restrictFunctor j) := inferInstance
  letI : PreservesLimit (parallelPair p 0) R :=
    preservesLimit_of_natIso _ (restrictFunctorIsoPullback j)
  let dR : parallelPair p 0 ⋙ R ≅ parallelPair (R.map p) 0 :=
    diagramIsoParallelPair _ ≪≫ parallelPair.eqOfHomEq rfl (by simp)
  letI : PreservesLimit (parallelPair p 0 ⋙ R) H :=
    preservesLimit_of_iso_diagram H dR.symm
  letI : PreservesLimit (parallelPair p 0) (R ⋙ H) := inferInstance
  let c : R ⋙ H ≅ F ⋙ G :=
    pullbackComp g j ≪≫
      pullbackCongr (U.pullbackHom_map f i) ≪≫
      (pullbackComp k f).symm
  letI : PreservesLimit (parallelPair p 0) (F ⋙ G) :=
    preservesLimit_of_natIso _ c
  letI : IsIso (kernelComparison p (F ⋙ G)) := by
    rw [← PreservesKernel.iso_hom (F ⋙ G) p]
    infer_instance
  letI : PreservesLimit (parallelPair (F.map p) 0) (restrictFunctor k) :=
    inferInstance
  letI : PreservesLimit (parallelPair (F.map p) 0) G :=
    preservesLimit_of_natIso _ (restrictFunctorIsoPullback k)
  letI : IsIso (kernelComparison (F.map p) G) := by
    rw [← PreservesKernel.iso_hom G (F.map p)]
    infer_instance
  let a := kernelComparison p F
  have ha := kernelComparison_comp_functors F G p
  haveI : IsIso (G.map a ≫ kernelComparison (F.map p) G) := by
    rw [ha]
    infer_instance
  haveI : IsIso (G.map a) :=
    IsIso.of_isIso_comp_right (G.map a) (kernelComparison (F.map p) G)
  let η := restrictFunctorIsoPullback k
  have hn := η.hom.naturality a
  haveI : IsIso ((restrictFunctor k).map a ≫ η.hom.app _) := by
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_right ((restrictFunctor k).map a) (η.hom.app _)

end AlgebraicGeometry.Scheme.Modules

end

end
