module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.NoetherNormalization

/-!
# Lifting Noether-normalization parameters from a residue fibre

An element of the residue fibre `κ(p) ⊗[R] S` need not be the image of an element of
`S`.  It becomes such an image after multiplication by a nonzero residue-field scalar.
For a finite family of fibre elements, scaling each polynomial variable by the
corresponding scalar is an automorphism of the polynomial ring.  Thus a finite injective
polynomial normalization of the fibre can be replaced by one whose parameters all come
from `S`.

This is the parameter-lifting step needed in relative Noether normalization.  The last
equality in `Ideal.Fiber.exists_lifted_finite_injective_mvPolynomial` says that the new
normalization is the coefficient base change of the polynomial map defined by the lifted
parameters.

Main declarations:

* `MvPolynomial.scaleVariablesAlgEquiv`;
* `Ideal.Fiber.exists_lifted_finite_injective_mvPolynomial`.
-/

@[expose] public section

noncomputable section

universe u v

namespace MvPolynomial

/-- Independently scaling polynomial variables by units is an algebra automorphism. -/
noncomputable def scaleVariablesAlgEquiv
    {K : Type u} {sigma : Type v} [CommRing K] (c : sigma → Kˣ) :
    MvPolynomial sigma K ≃ₐ[K] MvPolynomial sigma K :=
  AlgEquiv.ofAlgHom
    (aeval fun i ↦ C (c i : K) * X i)
    (aeval fun i ↦ C (↑((c i)⁻¹) : K) * X i)
    (by
      rw [comp_aeval, ← aeval_X_left]
      ext i
      simp)
    (by
      rw [comp_aeval, ← aeval_X_left]
      ext i
      simp)

@[simp]
theorem scaleVariablesAlgEquiv_X
    {K : Type u} {sigma : Type v} [CommRing K] (c : sigma → Kˣ) (i : sigma) :
    scaleVariablesAlgEquiv c (X i) = C (c i : K) * X i := by
  simp [scaleVariablesAlgEquiv]

end MvPolynomial

namespace Ideal.Fiber

/-- A finite injective polynomial normalization of a residue fibre can be changed by a
diagonal automorphism of its source so that all normalization parameters lift from the
original algebra.  The final equality records compatibility with coefficient base change. -/
theorem exists_lifted_finite_injective_mvPolynomial
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (n : ℕ)
    (g : MvPolynomial (Fin n) p.ResidueField →ₐ[p.ResidueField] p.Fiber S)
    (hg_injective : Function.Injective g) (hg_finite : g.Finite) :
    ∃ (s : Fin n → S) (c : Fin n → p.ResidueFieldˣ)
      (g' : MvPolynomial (Fin n) p.ResidueField →ₐ[p.ResidueField] p.Fiber S),
      Function.Injective g' ∧
        g'.Finite ∧
        g' = g.comp (MvPolynomial.scaleVariablesAlgEquiv c).toAlgHom ∧
        (∀ i, g' (MvPolynomial.X i) = 1 ⊗ₜ[R] s i) ∧
        (g'.restrictScalars R).comp
            (MvPolynomial.mapAlgHom
              (R := R) (σ := Fin n) (S₁ := R) (S₂ := p.ResidueField)
              (Algebra.ofId R p.ResidueField)) =
          (Algebra.TensorProduct.includeRight : S →ₐ[R] p.Fiber S).comp
            (MvPolynomial.aeval s) := by
  classical
  choose r hr s hs using fun i ↦
    Ideal.Fiber.exists_smul_eq_one_tmul p (g (MvPolynomial.X i))
  have hr_ne (i : Fin n) : algebraMap R p.ResidueField (r i) ≠ 0 := by
    intro hzero
    exact hr i (Ideal.algebraMap_residueField_eq_zero.mp hzero)
  let c : Fin n → p.ResidueFieldˣ := fun i ↦
    Units.mk0 (algebraMap R p.ResidueField (r i)) (hr_ne i)
  let e := MvPolynomial.scaleVariablesAlgEquiv c
  let g' := g.comp e.toAlgHom
  have hg'_X (i : Fin n) :
      g' (MvPolynomial.X i) = 1 ⊗ₜ[R] s i := by
    change g (MvPolynomial.scaleVariablesAlgEquiv c (MvPolynomial.X i)) = _
    rw [MvPolynomial.scaleVariablesAlgEquiv_X, map_mul,
      MvPolynomial.C_eq_algebraMap, g.commutes]
    simpa only [c, Units.val_mk0, Algebra.smul_def,
      IsScalarTower.algebraMap_apply R p.ResidueField (p.Fiber S)] using hs i
  refine ⟨s, c, g', hg_injective.comp e.injective, ?_, rfl, hg'_X, ?_⟩
  · exact hg_finite.comp e.toRingEquiv.finite
  · ext i
    simpa only [AlgHom.comp_apply, MvPolynomial.mapAlgHom_apply,
      MvPolynomial.map_X, MvPolynomial.aeval_X, AlgHom.restrictScalars_apply,
      Algebra.TensorProduct.includeRight_apply] using hg'_X i

end Ideal.Fiber

end

end
