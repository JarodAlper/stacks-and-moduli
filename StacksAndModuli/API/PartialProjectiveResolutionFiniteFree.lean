module

public import StacksProject.Algebra.RegularFiniteGlDim.ProjectiveDimension
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Finite-free certificates for partial projective resolutions

`Module.IsPartialProjectiveResolution` records each intermediate term only as projective.
This file supplies a proof-indexed certificate that the hidden terms are finite free, and a
strengthened finite-module existence theorem which retains that certificate.  It also records
the canonical first two finite-free covers of a matrix cokernel: the standard target surjects
onto the cokernel, and the standard source surjects onto the matrix image.

The certificate is intentionally a proposition indexed by the existing resolution proof.  A
consumer which only needs to prove the existence of matrices may eliminate the resolution and
certificate together, choose bases using `Module.finBasis`, and avoid introducing a second
resolution structure.

Main declarations:

* `Module.IsPartialProjectiveResolution.HasFiniteFreeTerms`;
* `Module.exists_isPartialProjectiveResolution_finiteFree`;
* `Module.IsPartialProjectiveResolution.matrixCokernel_firstTwoSteps`.
-/

@[expose] public section

noncomputable section

universe u v

namespace Module.IsPartialProjectiveResolution

/-- A certificate that every projective cover hidden in a partial projective resolution is
finite free.  The final syzygy is not one of the certified terms. -/
inductive HasFiniteFreeTerms {R : Type u} [CommRing R] :
    {e : ℕ} → {M : Type v} → [AddCommGroup M] → [Module R M] →
      {K : Type v} → [AddCommGroup K] → [Module R K] →
      Module.IsPartialProjectiveResolution R e M K → Prop
  | zero {M : Type v} [AddCommGroup M] [Module R M]
      {K : Type v} [AddCommGroup K] [Module R K]
      {F : Type v} [AddCommGroup F] [Module R F]
      [Module.Free R F] [Module.Finite R F]
      (f : F →ₗ[R] M) (hf : Function.Surjective f)
      (i : K →ₗ[R] F) (hi : Function.Injective i)
      (hexact : LinearMap.range i = LinearMap.ker f) :
      HasFiniteFreeTerms
        (Module.IsPartialProjectiveResolution.zero f hf i hi hexact)
  | succ {e : ℕ} {M : Type v} [AddCommGroup M] [Module R M]
      {K' : Type v} [AddCommGroup K'] [Module R K']
      {K : Type v} [AddCommGroup K] [Module R K]
      {h : Module.IsPartialProjectiveResolution R e M K'}
      (hh : HasFiniteFreeTerms h)
      {F : Type v} [AddCommGroup F] [Module R F]
      [Module.Free R F] [Module.Finite R F]
      (f : F →ₗ[R] K') (hf : Function.Surjective f)
      (i : K →ₗ[R] F) (hi : Function.Injective i)
      (hexact : LinearMap.range i = LinearMap.ker f) :
      HasFiniteFreeTerms
        (Module.IsPartialProjectiveResolution.succ h f hf i hi hexact)

end Module.IsPartialProjectiveResolution

namespace Module

/-- Every finite module over a Noetherian ring admits a partial projective resolution whose
hidden projective covers are certified to be finite free. -/
theorem exists_isPartialProjectiveResolution_finiteFree
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] (d : ℕ) :
    ∃ (K : Type u) (_ : AddCommGroup K) (_ : Module R K) (_ : Module.Finite R K)
      (h : Module.IsPartialProjectiveResolution R d M K),
      h.HasFiniteFreeTerms := by
  induction d with
  | zero =>
      obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
      let h : Module.IsPartialProjectiveResolution R 0 M (LinearMap.ker f) :=
        Module.IsPartialProjectiveResolution.zero f hf (LinearMap.ker f).subtype
          (Submodule.injective_subtype _) (Submodule.range_subtype _)
      refine ⟨LinearMap.ker f, inferInstance, inferInstance, ?_, h, ?_⟩
      · exact Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
      · exact IsPartialProjectiveResolution.HasFiniteFreeTerms.zero f hf
          (LinearMap.ker f).subtype (Submodule.injective_subtype _)
          (Submodule.range_subtype _)
  | succ d ih =>
      obtain ⟨K', _, _, _, h, hh⟩ := ih
      obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R K'
      let h' : Module.IsPartialProjectiveResolution R (d + 1) M (LinearMap.ker f) :=
        Module.IsPartialProjectiveResolution.succ h f hf (LinearMap.ker f).subtype
          (Submodule.injective_subtype _) (Submodule.range_subtype _)
      refine ⟨LinearMap.ker f, inferInstance, inferInstance, ?_, h', ?_⟩
      · exact Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
      · exact IsPartialProjectiveResolution.HasFiniteFreeTerms.succ hh f hf
          (LinearMap.ker f).subtype (Submodule.injective_subtype _)
          (Submodule.range_subtype _)

end Module

namespace Module.IsPartialProjectiveResolution

/-- The canonical first two finite-free covers of a matrix cokernel.  The second cover has
terminal syzygy equal to the kernel of the original matrix map. -/
theorem matrixCokernel_firstTwoSteps
    {R : Type u} [CommRing R] {m n : ℕ}
    (G : Matrix (Fin n) (Fin m) R) :
    ∃ h : Module.IsPartialProjectiveResolution R 1
        ((Fin n → R) ⧸ LinearMap.range (Matrix.toLin' G))
        (LinearMap.ker (Matrix.toLin' G)),
      h.HasFiniteFreeTerms := by
  let g : (Fin m → R) →ₗ[R] (Fin n → R) := Matrix.toLin' G
  change ∃ h : Module.IsPartialProjectiveResolution R 1
      ((Fin n → R) ⧸ LinearMap.range g) (LinearMap.ker g),
    h.HasFiniteFreeTerms
  let q : (Fin n → R) →ₗ[R] ((Fin n → R) ⧸ LinearMap.range g) :=
    (LinearMap.range g).mkQ
  let h0 : Module.IsPartialProjectiveResolution R 0
      ((Fin n → R) ⧸ LinearMap.range g) (LinearMap.range g) :=
    Module.IsPartialProjectiveResolution.zero q (Submodule.mkQ_surjective _)
      (LinearMap.range g).subtype (Submodule.injective_subtype _) (by
        rw [Submodule.range_subtype, Submodule.ker_mkQ])
  let h1 : Module.IsPartialProjectiveResolution R 1
      ((Fin n → R) ⧸ LinearMap.range g) (LinearMap.ker g) :=
    Module.IsPartialProjectiveResolution.succ h0 g.rangeRestrict
      g.surjective_rangeRestrict (LinearMap.ker g).subtype
      (Submodule.injective_subtype _) (by
        rw [Submodule.range_subtype, LinearMap.ker_rangeRestrict])
  refine ⟨h1, ?_⟩
  exact HasFiniteFreeTerms.succ
    (HasFiniteFreeTerms.zero q (Submodule.mkQ_surjective _)
      (LinearMap.range g).subtype (Submodule.injective_subtype _) (by
        rw [Submodule.range_subtype, Submodule.ker_mkQ]))
    g.rangeRestrict g.surjective_rangeRestrict (LinearMap.ker g).subtype
    (Submodule.injective_subtype _) (by
      rw [Submodule.range_subtype, LinearMap.ker_rangeRestrict])

end Module.IsPartialProjectiveResolution

end
