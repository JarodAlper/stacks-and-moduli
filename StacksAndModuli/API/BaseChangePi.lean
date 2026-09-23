module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Basic
public import StacksAndModuli.API.SemilinearTransport

/-!
# Base change of a linear map out of a finite free module

Supporting API with no Stacks Project counterpart.

The Grassmannian material of §2.1–§2.2 presents a rank-`q` locally free quotient of `O_X^{⊕n}`
by the kernel of a map out of `Fin n → Γ(X, U)`, and repeatedly base-changes that presentation
along a ring map. Because the source is free, the base change can be taken to land again in a
`Pi` type rather than in a tensor product, which is what `baseChangePi` records.

Mathlib supplies the identification `S ⊗[R] (ι → R) ≃ₗ[S] (ι → S)` as
`TensorProduct.piScalarRight`, so the definition itself is immediate; what is missing are the
two facts about it that the Grassmannian charts use — that it is surjective when `f` is, and
that its kernel is the span of the image of `ker f`.

Main declarations:
- `LinearMap.baseChangePi`: base change of a map out of `Fin n → R`, landing in `Fin n → S`;
- `LinearMap.baseChangePi_surjective`;
- `LinearMap.ker_baseChangePi_eq_span`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open TensorProduct

universe u v w

namespace LinearMap

variable {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
variable {n : ℕ} {M : Type w} [AddCommGroup M] [Module R M]

/-- Base change of a linear map out of a finite free module, with the source rewritten as a
`Pi` type via `TensorProduct.piScalarRight`. -/
noncomputable def baseChangePi (f : (Fin n → R) →ₗ[R] M) :
    (Fin n → S) →ₗ[S] S ⊗[R] M :=
  (LinearMap.baseChange S f).comp
    ((TensorProduct.piScalarRight R S S (Fin n)).symm : (Fin n → S) →ₗ[S] S ⊗[R] (Fin n → R))

/-- Base change of a surjection out of a finite free module is surjective.

Proof route: `piScalarRight` is an equivalence, and `LinearMap.baseChange` of a surjection is
surjective because `S ⊗[R] -` is right exact. -/
theorem baseChangePi_surjective {f : (Fin n → R) →ₗ[R] M} (hf : Function.Surjective f) :
    Function.Surjective (baseChangePi S f) := by
  have h : ⇑(baseChangePi S f) =
      ⇑(LinearMap.baseChange S f) ∘ ⇑((TensorProduct.piScalarRight R S S (Fin n)).symm) := rfl
  rw [h]
  exact (LinearMap.baseChange_surjective S hf).comp
    (TensorProduct.piScalarRight R S S (Fin n)).symm.surjective

/-- `baseChangePi` on a vector of scalars coming from the base ring. -/
@[simp]
theorem baseChangePi_comp_algebraMap (f : (Fin n → R) →ₗ[R] M) (w : Fin n → R) :
    baseChangePi S f (fun i ↦ (algebraMap R S) (w i)) = 1 ⊗ₜ[R] f w := by
  have h : (TensorProduct.piScalarRight R S S (Fin n)).symm
      (fun i ↦ (algebraMap R S) (w i)) = 1 ⊗ₜ[R] w := by
    apply (TensorProduct.piScalarRight R S S (Fin n)).injective
    simp [Algebra.smul_def]
  simp [baseChangePi, h]

/-- The kernel of the base change of a surjection out of a finite free module is the `S`-span
of the image of the original kernel.

Proof route: right exactness of `S ⊗[R] -` identifies `ker (S ⊗ f)` with the image of
`S ⊗[R] ker f`, and transporting along `piScalarRight` turns that image into the span of the
coordinatewise image of `ker f`. This is the affine-local form of "the kernel presentation of a
locally free quotient is stable under base change". -/
theorem ker_baseChangePi_eq_span {f : (Fin n → R) →ₗ[R] M} (hf : Function.Surjective f) :
    LinearMap.ker (baseChangePi S f) =
      Submodule.span S ((fun w : Fin n → R ↦ fun i ↦ algebraMap R S (w i)) ''
        (LinearMap.ker f : Set (Fin n → R))) := by
  classical
  have hexact : Function.Exact ((LinearMap.ker f).subtype.lTensor S) (f.lTensor S) :=
    lTensor_exact S (LinearMap.exact_subtype_ker_map f) hf
  apply le_antisymm
  · intro x hx
    have hx' : (f.lTensor S) ((TensorProduct.piScalarRight R S S (Fin n)).symm x) = 0 := by
      have hb : LinearMap.baseChange S f
          ((TensorProduct.piScalarRight R S S (Fin n)).symm x) = 0 := hx
      calc (f.lTensor S) ((TensorProduct.piScalarRight R S S (Fin n)).symm x)
          = LinearMap.baseChange S f
              ((TensorProduct.piScalarRight R S S (Fin n)).symm x) :=
            (congrFun (LinearMap.baseChange_eq_ltensor f) _).symm
        _ = 0 := hb
    obtain ⟨y, hy⟩ := (hexact _).mp hx'
    have hxy : (TensorProduct.piScalarRight R S S (Fin n))
        (((LinearMap.ker f).subtype.lTensor S) y) = x := by
      rw [hy]
      exact (TensorProduct.piScalarRight R S S (Fin n)).apply_symm_apply x
    rw [← hxy]
    clear hxy hy hx hx'
    induction y using TensorProduct.induction_on with
    | zero => simpa using Submodule.zero_mem _
    | tmul s w =>
      have hval : (TensorProduct.piScalarRight R S S (Fin n))
          (((LinearMap.ker f).subtype.lTensor S) (s ⊗ₜ w)) =
          s • fun i ↦ algebraMap R S (w.1 i) := by
        funext i
        simp [Algebra.smul_def, mul_comm]
      rw [hval]
      exact Submodule.smul_mem _ s (Submodule.subset_span ⟨w.1, w.2, rfl⟩)
    | add a b ha hb =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ ha hb
  · rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    have hb : baseChangePi S f (fun i ↦ algebraMap R S (w i)) = 1 ⊗ₜ[R] f w :=
      baseChangePi_comp_algebraMap S f w
    have hw0 : f w = 0 := hw
    simp only [SetLike.mem_coe, LinearMap.mem_ker, hb, hw0, TensorProduct.tmul_zero]

/-- One inclusion of `ker_baseChangePi_eq_span`, which is the direction the chart arguments of
§2.1 actually use. -/
theorem ker_baseChangePi_le_span {f : (Fin n → R) →ₗ[R] M} (hf : Function.Surjective f) :
    LinearMap.ker (baseChangePi S f) ≤
      Submodule.span S ((fun w : Fin n → R ↦ fun i ↦ (algebraMap R S) (w i)) ''
        (LinearMap.ker f : Set (Fin n → R))) :=
  (ker_baseChangePi_eq_span S hf).le

/-- Finiteness, projectivity and constant stalk rank of the quotient by the kernel are all
inherited by the base change.

Proof route: for surjective `f`, `(Fin n → R) ⧸ ker f ≃ₗ M`, and likewise after base change, so
this is `Module.finite_projective_rankAtStalk_baseChange` transported along those quotient
equivalences. -/
theorem quotKer_baseChangePi_finite_projective_rank {q : ℕ} (f : (Fin n → R) →ₗ[R] M)
    (hf : Function.Surjective f)
    (hrank : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = q)
    [Module.Finite R M] [Module.Projective R M] :
    Module.Finite S ((Fin n → S) ⧸ LinearMap.ker (baseChangePi S f)) ∧
      Module.Projective S ((Fin n → S) ⧸ LinearMap.ker (baseChangePi S f)) ∧
      ∀ p : PrimeSpectrum S,
        Module.rankAtStalk ((Fin n → S) ⧸ LinearMap.ker (baseChangePi S f)) p = q := by
  have hsurj : Function.Surjective (baseChangePi S f) := baseChangePi_surjective S hf
  let e : ((Fin n → S) ⧸ LinearMap.ker (baseChangePi S f)) ≃ₗ[S] S ⊗[R] M :=
    LinearMap.quotKerEquivOfSurjective _ hsurj
  obtain ⟨hfin, hproj, hrk⟩ := Module.finite_projective_rankAtStalk_baseChange R S M
    inferInstance inferInstance q hrank
  refine ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm, fun p ↦ ?_⟩
  rw [Module.rankAtStalk_eq_of_equiv e]
  exact hrk p

end LinearMap
