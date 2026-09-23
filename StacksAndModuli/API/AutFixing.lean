module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.CategoryTheory.Endomorphism

/-!
# Automorphisms fixing a family of morphisms

For morphisms `p i : A ⟶ X`, this file defines the subgroup of
`CategoryTheory.Aut X` fixing every `p i` under postcomposition.  The construction is
categorical and is intended in particular for automorphism groups of marked objects.

## Main declarations

* `CategoryTheory.Aut.fixingSubgroup`: automorphisms satisfying
  `p i ≫ Aut.toEnd X φ = p i` for every `i`;
* `CategoryTheory.Aut.Fixing`: the underlying group type of that subgroup;
* `CategoryTheory.Aut.fixingSubgroup_comp_equiv`: reindexing a family by an equivalence
  does not change its fixing subgroup.
* `CategoryTheory.Aut.fixingMonoidHomOfSubfamily`: fixing a larger family embeds into
  the group fixing any subfamily.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe v u w w'

namespace CategoryTheory.Aut

variable {C : Type u} [Category.{v} C] {A X : C} {I : Type w}

/-- The subgroup of automorphisms of `X` that fix every morphism in the indexed family
`p : I → (A ⟶ X)` under postcomposition. -/
def fixingSubgroup (p : I → (A ⟶ X)) : Subgroup (Aut X) where
  carrier := { φ | ∀ i, p i ≫ (toEnd X) φ = p i }
  one_mem' := by
    intro i
    rw [map_one, End.one_def, Category.comp_id]
  mul_mem' := by
    intro φ ψ hφ hψ i
    rw [map_mul, End.mul_def, ← Category.assoc]
    rw [hψ i, hφ i]
  inv_mem' := by
    intro φ hφ i
    have hinv : (toEnd X) φ ≫ (toEnd X) φ⁻¹ = 𝟙 X := by
      have h := congrArg (toEnd X) (inv_mul_cancel φ)
      simpa only [map_mul, map_one, End.mul_def, End.one_def] using h
    have h := congrArg (fun q ↦ q ≫ (toEnd X) φ⁻¹) (hφ i)
    simpa only [Category.assoc, hinv, Category.comp_id] using h.symm

/-- Membership in `fixingSubgroup p` is exactly pointwise preservation of the family
`p`. -/
lemma mem_fixingSubgroup_iff (p : I → (A ⟶ X)) (φ : Aut X) :
    φ ∈ fixingSubgroup p ↔ ∀ i, p i ≫ (toEnd X) φ = p i :=
  Iff.rfl

/-- The group of automorphisms of `X` fixing every member of `p`. -/
abbrev Fixing (p : I → (A ⟶ X)) : Type v :=
  fixingSubgroup p

/-- Precomposing a family with an equivalence of index types does not change the subgroup
of automorphisms fixing it. -/
lemma fixingSubgroup_comp_equiv {J : Type w'} (p : I → (A ⟶ X)) (e : J ≃ I) :
    fixingSubgroup (p ∘ e) = fixingSubgroup p := by
  ext φ
  rw [mem_fixingSubgroup_iff, mem_fixingSubgroup_iff]
  constructor
  · intro h i
    simpa only [Function.comp_apply, e.apply_symm_apply] using h (e.symm i)
  · intro h j
    exact h (e j)

/-- Reindexing a family by an equivalence gives the canonical multiplicative equivalence
between its fixing groups. -/
def fixingMulEquivOfEquiv {J : Type w'} (p : I → (A ⟶ X)) (e : J ≃ I) :
    Fixing (p ∘ e) ≃* Fixing p :=
  MulEquiv.subgroupCongr (fixingSubgroup_comp_equiv p e)

/-- An automorphism fixing `q` also fixes every subfamily `p` obtained by selecting
members of `q`. -/
def fixingMonoidHomOfSubfamily {J : Type w'} (p : I → (A ⟶ X))
    (q : J → (A ⟶ X)) (f : I → J) (h : ∀ i, p i = q (f i)) :
    Fixing q →* Fixing p where
  toFun φ := ⟨φ.1, fun i ↦ by simpa only [h i] using φ.2 (f i)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The homomorphism from automorphisms fixing a family to those fixing a selected
subfamily is injective. -/
theorem fixingMonoidHomOfSubfamily_injective {J : Type w'}
    (p : I → (A ⟶ X)) (q : J → (A ⟶ X)) (f : I → J)
    (h : ∀ i, p i = q (f i)) :
    Function.Injective (fixingMonoidHomOfSubfamily p q f h) := by
  intro φ ψ hφψ
  apply Subtype.ext
  exact congrArg (fun z : Fixing p ↦ z.1) hφψ

/-- If the automorphisms fixing a selected subfamily are finite, then the
automorphisms fixing the whole family are finite. -/
theorem finite_fixing_of_finite_subfamily {J : Type w'}
    (p : I → (A ⟶ X)) (q : J → (A ⟶ X)) (f : I → J)
    (h : ∀ i, p i = q (f i)) (hfinite : Finite (Fixing p)) :
    Finite (Fixing q) := by
  let _ : Finite (Fixing p) := hfinite
  exact Finite.of_injective (fixingMonoidHomOfSubfamily p q f h)
    (fixingMonoidHomOfSubfamily_injective p q f h)

/-- Forgetting an empty family imposes no condition on automorphisms. -/
lemma fixingSubgroup_eq_top_of_isEmpty (p : I → (A ⟶ X)) [IsEmpty I] :
    fixingSubgroup p = ⊤ := by
  ext φ
  simp only [mem_fixingSubgroup_iff, Subgroup.mem_top, iff_true]
  exact fun i ↦ isEmptyElim i

/-- Conjugation by `e : X ≅ Y`, read on the underlying endomorphisms. -/
lemma toEnd_autMulEquivOfIso_apply {Y : C} (e : X ≅ Y) (φ : Aut X) :
    (toEnd Y) (autMulEquivOfIso e φ) =
      e.inv ≫ (toEnd X) φ ≫ e.hom :=
  rfl

/-- Conjugation by an isomorphism identifies the automorphisms fixing two corresponding
families of morphisms. -/
def fixingMulEquivOfIso {Y : C} (e : X ≅ Y) (p : I → (A ⟶ X))
    (q : I → (A ⟶ Y)) (hpq : ∀ i, p i ≫ e.hom = q i) :
    Fixing p ≃* Fixing q := by
  let E : Aut X ≃* Aut Y := autMulEquivOfIso e
  have hqp : ∀ i, q i ≫ e.inv = p i := by
    intro i
    rw [← hpq i, Category.assoc, e.hom_inv_id, Category.comp_id]
  exact
    { toFun := fun φ ↦ ⟨E φ, by
        intro i
        rw [toEnd_autMulEquivOfIso_apply, ← Category.assoc, hqp i,
          ← Category.assoc, φ.property i, hpq i]⟩
      invFun := fun ψ ↦ ⟨E.symm ψ, by
        intro i
        rw [show E.symm = autMulEquivOfIso e.symm from rfl,
          toEnd_autMulEquivOfIso_apply, Iso.symm_inv, Iso.symm_hom,
          ← Category.assoc, hpq i,
          ← Category.assoc, ψ.property i, hqp i]⟩
      left_inv := fun φ ↦ Subtype.ext (E.left_inv φ)
      right_inv := fun ψ ↦ Subtype.ext (E.right_inv ψ)
      map_mul' := fun φ ψ ↦ Subtype.ext (E.map_mul φ ψ) }

end CategoryTheory.Aut
