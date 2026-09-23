module

public import StacksAndModuli.API.FlatOverKernel
public import StacksAndModuli.API.ProjectiveSpaceZeroGrassmannianQuot
public import StacksAndModuli.API.SchemeModulesKernelFinitePresentationVectorBundle

/-!
# Finite locally free kernels of vector-bundle quotients

An epimorphism between finite locally free quasicoherent module sheaves has finite locally
free kernel.  The finite-presentation input is affine-local, while flatness follows from the
kernel criterion for a short exact sequence of sheaves flat over the identity.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- The kernel of an epimorphism between finite locally free quasicoherent sheaves is
finite locally free. -/
theorem kernel_isFiniteLocallyFree_of_epi_of_isFiniteLocallyFree
    {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hM : IsFiniteLocallyFree M) (hN : IsFiniteLocallyFree N)
    (f : M ⟶ N) [Epi f] : IsFiniteLocallyFree (kernel f) := by
  letI : (kernel f).IsQuasicoherent := kernel_isQuasicoherent f
  have hfp : (kernel f).IsFinitePresentation :=
    kernel_isFinitePresentation_of_epi_of_isFiniteLocallyFree hM hN f
  have hMflat : M.FlatOver (𝟙 X) := hM.flatOver_of_flat (𝟙 X)
  have hNflat : N.FlatOver (𝟙 X) := hN.flatOver_of_flat (𝟙 X)
  have hKflat : (kernel f).FlatOver (𝟙 X) :=
    hMflat.kernel_of_epi (𝟙 X) f hNflat
  exact isFiniteLocallyFree_of_isFinitePresentation_flatOver_id
    (kernel f) hfp hKflat

end AlgebraicGeometry.Scheme.Modules

end

end
