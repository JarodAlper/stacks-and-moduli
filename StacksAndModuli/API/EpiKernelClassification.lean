module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Quotients in an abelian category are classified by their kernels

Supporting API with no Stacks Project counterpart of its own, used by the formalization of
`prop:quot-proper` in §2.4: two epimorphisms out of the same object are isomorphic under it if
and only if they have the same kernel subobject.  This converts the equivalence classes of the
Quot functor (`Scheme.Modules.QuotientPullbackData`, whose setoid identifies quotients through
compatible isomorphisms) into kernel data, which is what the valuative criterion manipulates:
the flat extension of a quotient over a discrete valuation ring is constructed and compared
through its kernel (the saturation of the generic-fibre kernel).

Main declarations:
- `CategoryTheory.Abelian.exists_iso_comp_eq_of_kernelSubobject_eq`: equal kernels give a
  compatible isomorphism of quotients;
- `CategoryTheory.Abelian.exists_iso_comp_eq_iff_kernelSubobject_eq`: the classification.
-/

@[expose] public section

namespace CategoryTheory.Abelian

open CategoryTheory Limits

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {F Q Q' : C} (π : F ⟶ Q) (π' : F ⟶ Q') [Epi π] [Epi π']

/-- If two epimorphisms out of `F` have the same kernel subobject, the composite with the
kernel inclusion of the other vanishes. -/
theorem kernel_ι_comp_eq_zero_of_kernelSubobject_eq
    (h : kernelSubobject π = kernelSubobject π') :
    kernel.ι π ≫ π' = 0 := by
  have h2 := kernelSubobject_arrow_comp π'
  rw [← h] at h2
  rw [← kernelSubobject_arrow', Category.assoc, h2, comp_zero]

/-- **Quotients with equal kernels are isomorphic**: two epimorphisms out of `F` with the
same kernel subobject differ by a unique compatible isomorphism of their targets. -/
theorem exists_iso_comp_eq_of_kernelSubobject_eq
    (h : kernelSubobject π = kernelSubobject π') :
    ∃ e : Q ≅ Q', π ≫ e.hom = π' := by
  have h1 : kernel.ι π ≫ π' = 0 :=
    kernel_ι_comp_eq_zero_of_kernelSubobject_eq π π' h
  have h1' : kernel.ι π' ≫ π = 0 :=
    kernel_ι_comp_eq_zero_of_kernelSubobject_eq π' π h.symm
  refine ⟨⟨Abelian.epiDesc π π' h1, Abelian.epiDesc π' π h1', ?_, ?_⟩,
    Abelian.comp_epiDesc π π' h1⟩
  · rw [← cancel_epi π, ← Category.assoc, Abelian.comp_epiDesc,
      Abelian.comp_epiDesc, Category.comp_id]
  · rw [← cancel_epi π', ← Category.assoc, Abelian.comp_epiDesc,
      Abelian.comp_epiDesc, Category.comp_id]

/-- **Classification of quotients by kernels**: two epimorphisms out of `F` are isomorphic
under `F` if and only if they have the same kernel subobject. -/
theorem exists_iso_comp_eq_iff_kernelSubobject_eq :
    (∃ e : Q ≅ Q', π ≫ e.hom = π') ↔ kernelSubobject π = kernelSubobject π' := by
  constructor
  · rintro ⟨e, he⟩
    rw [← he, kernelSubobject_comp_mono]
  · exact exists_iso_comp_eq_of_kernelSubobject_eq π π'

end CategoryTheory.Abelian

end
