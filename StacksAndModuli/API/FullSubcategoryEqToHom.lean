module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.EqToHom

/-!
# `eqToHom` in a full subcategory

Mathlib records how the underlying morphism of a morphism in `P.FullSubcategory` behaves for
identities and composites (`ObjectProperty.FullSubcategory.id_hom`, `…comp_hom`) but not for
`eqToHom`.  That case is what turns up whenever a pseudofunctor's `map₂` of an `eqToHom` has
to be pushed down to the ambient category — for instance in the Beck–Chevalley mate
identities of §3.1, where the transport coming from `Functor.toPseudofunctor`'s functoriality
proof must be compared with a concrete `eqToIso`.

Both sides are `eqToHom`s between the same pair of objects, so downstream the comparison is
settled by proof irrelevance; the only thing missing was this projection lemma.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory.ObjectProperty

universe v u

variable {C : Type u} [Category.{v} C] {P : ObjectProperty C}

/-- The underlying morphism of `eqToHom` in a full subcategory is `eqToHom` of the
corresponding equality of underlying objects. -/
@[simp]
lemma FullSubcategory.eqToHom_hom {X Y : P.FullSubcategory} (h : X = Y) :
    (eqToHom h).hom = eqToHom (congrArg ObjectProperty.FullSubcategory.obj h) := by
  subst h
  rfl

end CategoryTheory.ObjectProperty
