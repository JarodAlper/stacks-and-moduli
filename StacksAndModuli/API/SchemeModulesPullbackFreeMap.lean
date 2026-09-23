module

public import StacksAndModuli.«Section2.1-Intro».«part2.1.0-pullback-quasicoherent»

/-!
# Pullback and reindexing of free module sheaves

The canonical identification of a pulled-back free module sheaf with the free sheaf on
the source is natural in maps of indexing types.  This is the source-side coherence
needed when a finite-free quotient is first reindexed and then pulled back.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Reindexing a canonical free sheaf commutes with its normalized pullback
identification. -/
lemma freeMap_comp_pullbackFreeIso_inv
    {X Y : Scheme.{u}} (f : X ⟶ Y) {I J : Type u} (e : I → J) :
    SheafOfModules.freeMap (R := X.ringCatSheaf) e ≫
        (pullbackFreeIso f J).inv =
      (pullbackFreeIso f I).inv ≫
        (pullback f).map
          (SheafOfModules.freeMap (R := Y.ringCatSheaf) e) := by
  apply Cofan.IsColimit.hom_ext
      (SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf) I)
  intro i
  change (SheafOfModules.ιFree (R := X.ringCatSheaf) i ≫
        SheafOfModules.freeMap e) ≫ (pullbackFreeIso f J).inv =
    SheafOfModules.ιFree i ≫ (pullbackFreeIso f I).inv ≫
      (pullback f).map (SheafOfModules.freeMap e)
  rw [← Category.assoc, SheafOfModules.ιFree_freeMap]
  rw [ιFree_comp_pullbackFreeIso_inv]
  rw [ιFree_comp_pullbackFreeIso_inv]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [SheafOfModules.ιFree_freeMap]

end AlgebraicGeometry.Scheme.Modules

end

end
