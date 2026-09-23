module

public import StacksAndModuli.API.PresentationTensorKernelBaseChange
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Reflecting exactness through a two-stage base change

Exactness after the composite scalar extension `R → k → A` can be transported to the
iterated base change and then reflected from `A` to `k` when `A` is faithfully flat over
`k`.

Main declaration:

* `LinearMap.lTensor_exact_of_baseChange_exact_of_faithfullyFlat`.
-/

@[expose] public section

open TensorProduct

universe u

noncomputable section

namespace LinearMap

/-- If a pair becomes exact after a composite base change `R → A`, and `A` is faithfully
flat over an intermediate ring `k`, then it is already exact after base change to `k`. -/
theorem lTensor_exact_of_baseChange_exact_of_faithfullyFlat
    {R k A L K F : Type u}
    [CommRing R] [CommRing k] [CommRing A]
    [Algebra R k] [Algebra R A] [Algebra k A] [IsScalarTower R k A]
    [Module.FaithfullyFlat k A]
    [AddCommGroup L] [Module R L]
    [AddCommGroup K] [Module R K]
    [AddCommGroup F] [Module R F]
    (f : L →ₗ[R] K) (g : K →ₗ[R] F)
    (hA : Function.Exact (f.baseChange A) (g.baseChange A)) :
    Function.Exact (f.lTensor k) (g.lTensor k) := by
  let eL := AlgebraTensorModule.cancelBaseChange R k A A L
  let eK := AlgebraTensorModule.cancelBaseChange R k A A K
  let eF := AlgebraTensorModule.cancelBaseChange R k A A F
  have hnested : Function.Exact
      ((f.baseChange k).baseChange A) ((g.baseChange k).baseChange A) := by
    apply (Function.Exact.iff_of_ladder_linearEquiv
      (e₁ := eL) (e₂ := eK) (e₃ := eF) ?_ ?_).mp hA
    · exact (cancelBaseChange_naturality (R := R) (A := k) (B := A) f).symm
    · exact (cancelBaseChange_naturality (R := R) (A := k) (B := A) g).symm
  change Function.Exact (f.baseChange k) (g.baseChange k)
  apply Module.FaithfullyFlat.lTensor_reflects_exact k A
    (f.baseChange k) (g.baseChange k)
  simpa only [LinearMap.baseChange_eq_ltensor] using hnested

end LinearMap

end
