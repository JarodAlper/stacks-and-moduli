module

public import Mathlib.Algebra.Ring.Fin
public import Mathlib.RingTheory.Etale.Field

/-!
# Finite étale algebras of rank two

An étale algebra over a field is a finite product of finite separable field
extensions.  If its vector-space rank is two, this decomposition has only two
possibilities: one quadratic field factor, or two copies of the base field.

This file also supplies algebra-equivalence versions of the standard descriptions
of a product over a unique index type and over `Fin 2`.

## Main results

* `AlgEquiv.piUnique`: a dependent product over a unique type is algebra-equivalent
  to its unique factor.
* `AlgEquiv.piFinTwo`: a dependent product over `Fin 2` is algebra-equivalent to a
  binary product.
* `Algebra.Etale.exists_quadratic_algEquiv_or_prod_of_finrank_eq_two`: an étale
  algebra of rank two is either a separable quadratic field extension or the split
  algebra `K × K`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

universe u v

namespace AlgEquiv

variable (R : Type u) [CommSemiring R]

/-- A dependent product of `R`-algebras over a unique index type is
`R`-algebra-equivalent to its unique factor. -/
def piUnique {I : Type v} [Unique I] (A : I → Type*)
    [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)] :
    (∀ i, A i) ≃ₐ[R] A default :=
  .ofRingEquiv (f := RingEquiv.piUnique A) (by intro; rfl)

/-- A dependent product of two `R`-algebras is their binary product. -/
def piFinTwo (A : Fin 2 → Type*) [∀ i, Semiring (A i)]
    [∀ i, Algebra R (A i)] :
    (∀ i, A i) ≃ₐ[R] A 0 × A 1 :=
  .ofRingEquiv (f := RingEquiv.piFinTwo A) (by intro; rfl)

end AlgEquiv

namespace Algebra.Etale

variable {K : Type u} {A : Type v} [Field K] [CommRing A] [Algebra K A]

/-- An étale algebra of vector-space rank two over a field is either a finite
separable quadratic field extension or the split algebra `K × K`.

The field extension in the first alternative is returned together with its field,
algebra, separability, and quadratic-extension instances. -/
theorem exists_quadratic_algEquiv_or_prod_of_finrank_eq_two
    [Algebra.Etale K A] (hA : Module.finrank K A = 2) :
    (∃ (L : Type v) (_ : Field L) (_ : Algebra K L)
        (_ : Algebra.IsSeparable K L) (_ : Algebra.IsQuadraticExtension K L),
        Nonempty (A ≃ₐ[K] L)) ∨
      Nonempty (A ≃ₐ[K] K × K) := by
  classical
  obtain ⟨I, hI, L, hLfield, hLalgebra, e, hL⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod (K := K) (A := A)).mp inferInstance
  let _ : Finite I := hI
  let _ : Fintype I := Fintype.ofFinite I
  let _ (i : I) : Field (L i) := hLfield i
  let _ (i : I) : Algebra K (L i) := hLalgebra i
  let _ (i : I) : Module.Finite K (L i) := (hL i).1
  have hsum : ∑ i, Module.finrank K (L i) = 2 := by
    calc
      ∑ i, Module.finrank K (L i) = Module.finrank K (∀ i, L i) :=
        (Module.finrank_pi_fintype K).symm
      _ = Module.finrank K A := e.toLinearEquiv.finrank_eq.symm
      _ = 2 := hA
  have hpos (i : I) : 0 < Module.finrank K (L i) :=
    Module.finrank_pos
  have hcard_le : Fintype.card I ≤ 2 := by
    calc
      Fintype.card I = ∑ _ : I, 1 := by simp
      _ ≤ ∑ i, Module.finrank K (L i) := by
        exact Finset.sum_le_sum fun i _ ↦ hpos i
      _ = 2 := hsum
  have hnonempty : Nonempty I := by
    by_contra h
    let _ : IsEmpty I := not_nonempty_iff.mp h
    simp at hsum
  have hcard_pos : 0 < Fintype.card I :=
    Fintype.card_pos_iff.mpr hnonempty
  have hcard : Fintype.card I = 1 ∨ Fintype.card I = 2 := by
    omega
  rcases hcard with hcard_one | hcard_two
  · left
    let _ : Unique I :=
      (Fintype.card_eq_one_iff_nonempty_unique.mp hcard_one).some
    let eL : A ≃ₐ[K] L default :=
      e.trans (AlgEquiv.piUnique K L)
    have hLrank : Module.finrank K (L default) = 2 :=
      eL.toLinearEquiv.finrank_eq.symm.trans hA
    let hquadratic : Algebra.IsQuadraticExtension K (L default) :=
      { finrank_eq_two' := hLrank }
    exact ⟨L default, inferInstance, inferInstance, (hL default).2,
      hquadratic, ⟨eL⟩⟩
  · right
    let ι : I ≃ Fin 2 := Fintype.equivFinOfCardEq hcard_two
    let eι : (∀ i, L i) ≃ₐ[K] ∀ j : Fin 2, L (ι.symm j) :=
      AlgEquiv.piCongrLeft' K L ι
    let eFin : A ≃ₐ[K] ∀ j : Fin 2, L (ι.symm j) :=
      e.trans eι
    have hsumFin :
        Module.finrank K (L (ι.symm 0)) +
            Module.finrank K (L (ι.symm 1)) = 2 := by
      have hproduct :
          Module.finrank K (∀ j : Fin 2, L (ι.symm j)) = 2 :=
        eFin.toLinearEquiv.finrank_eq.symm.trans hA
      simpa [Module.finrank_pi_fintype, Fin.sum_univ_two] using hproduct
    have hzero_pos : 0 < Module.finrank K (L (ι.symm 0)) := hpos _
    have hone_pos : 0 < Module.finrank K (L (ι.symm 1)) := hpos _
    have hzero : Module.finrank K (L (ι.symm 0)) = 1 := by omega
    have hone : Module.finrank K (L (ι.symm 1)) = 1 := by omega
    have hrank (j : Fin 2) : Module.finrank K (L (ι.symm j)) = 1 := by
      fin_cases j
      · exact hzero
      · exact hone
    let factorEquiv (j : Fin 2) : L (ι.symm j) ≃ₐ[K] K :=
      (Module.nonempty_algEquiv_iff_finrank_eq_one.mpr (hrank j)).some.symm
    exact ⟨eFin |>.trans (AlgEquiv.piCongrRight factorEquiv) |>.trans
      (AlgEquiv.piFinTwo K fun _ ↦ K)⟩

end Algebra.Etale

end
