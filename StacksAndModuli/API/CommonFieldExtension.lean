module

public import Mathlib.RingTheory.TensorProduct.Nontrivial
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Maximal

/-!
# A common extension of two field extensions

Two extensions `K → L` and `K → L'` of a field always admit a common extension: the
tensor product `L ⊗[K] L'` is a nonzero commutative ring (both factors are domains into
which `K` injects), so it has a maximal ideal, and the quotient by one is a field
receiving `L` and `L'` compatibly over `K`.

This is the standard "amalgamation" step. It is what makes the identification of
field-valued points of a prestack (Definition 4.3.17, `def:topology-of-stacks`) a
transitive relation, and thereby makes the topological space `|𝒳|` of a prestack a
quotient by an equivalence relation rather than by a mere relation.

## Main results

* `Field.exists_common_extension`: two extensions of a field admit a common extension.
-/

@[expose] public section

open TensorProduct

universe u

namespace Field

/-- **Two extensions of a field admit a common extension.** Given ring homomorphisms
`i : K → L` and `i' : K → L'` out of a field, there are a field `M` and homomorphisms
`j : L → M`, `j' : L' → M` with `j ∘ i = j' ∘ i'`.

The witness is a quotient of `L ⊗[K] L'` by a maximal ideal. The tensor product is nonzero
by `Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain`: `L` and `L'` are
domains and a ring homomorphism out of a field is injective. -/
theorem exists_common_extension {K L L' : Type u} [Field K] [Field L] [Field L']
    (i : K →+* L) (i' : K →+* L') :
    ∃ (M : Type u) (_ : Field M) (j : L →+* M) (j' : L' →+* M), j.comp i = j'.comp i' := by
  let _ : Algebra K L := i.toAlgebra
  let _ : Algebra K L' := i'.toAlgebra
  have : Nontrivial (L ⊗[K] L') :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain K L L'
      i.injective i'.injective
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (L ⊗[K] L')
  let _ : m.IsMaximal := hm
  let _ : Field ((L ⊗[K] L') ⧸ m) := Ideal.Quotient.field m
  refine ⟨(L ⊗[K] L') ⧸ m, inferInstance,
    (Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeLeftRingHom,
    (Ideal.Quotient.mk m).comp
      (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := L')).toRingHom, ?_⟩
  ext a
  have h : i a ⊗ₜ[K] (1 : L') = (1 : L) ⊗ₜ[K] i' a := by
    simp [show i a = algebraMap K L a from rfl, show i' a = algebraMap K L' a from rfl,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  simpa only [RingHom.coe_comp, Function.comp_apply,
    Algebra.TensorProduct.includeLeftRingHom_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply] using congrArg (Ideal.Quotient.mk m) h

end Field
