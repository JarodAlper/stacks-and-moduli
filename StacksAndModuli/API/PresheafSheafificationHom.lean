module

public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Sheafification morphisms on large sites

On a site whose presheaf category is too large for the available sheafification functor,
one can still say that a map exhibits its target as a sheafification: the target is a
sheaf and the map is locally injective and locally surjective. This file packages that
standard characterization and its invariance under replacing the source by an isomorphic
presheaf.
-/

@[expose] public section

open CategoryTheory

universe w v u

namespace CategoryTheory.Presheaf

/-- A morphism of presheaves exhibits its target as a sheafification if the target is a
sheaf and the morphism is locally injective and locally surjective. -/
def IsSheafificationHom {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {F G : Cᵒᵖ ⥤ Type w} (η : F ⟶ G) : Prop :=
  Presieve.IsSheaf J G ∧ IsLocallyInjective J η ∧ IsLocallySurjective J η

/-- Precomposing a sheafification morphism by an isomorphism gives another
sheafification morphism. -/
lemma IsSheafificationHom.iso_hom_comp {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {F F' G : Cᵒᵖ ⥤ Type w} (e : F' ≅ F)
    {η : F ⟶ G} (hη : IsSheafificationHom J η) :
    IsSheafificationHom J (e.hom ≫ η) := by
  letI : IsLocallyInjective J η := hη.2.1
  letI : IsLocallySurjective J η := hη.2.2
  exact ⟨hη.1, inferInstance, inferInstance⟩

end CategoryTheory.Presheaf
