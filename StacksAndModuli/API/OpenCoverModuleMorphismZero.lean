module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Detecting zero morphisms of module sheaves on open covers

A morphism of sheaves of modules is zero if its restrictions to the members of an
open cover are zero.  This small lemma is useful independently of the Quot-functor
application in which it first arose.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The underlying `Ab`-sheaf of a sheaf of modules, as a `TopCat.Sheaf`. -/
noncomputable abbrev abSheaf {Y : Scheme.{u}} (A : Y.Modules) :
    TopCat.Sheaf AddCommGrpCat.{u} Y :=
  ⟨A.presheaf, A.isSheaf⟩

/-- A morphism of sheaves of modules which is zero on every member of an open cover
is zero. -/
lemma eq_zero_of_openCover_restrict {X : Scheme.{u}} (U : X.OpenCover)
    {M N : X.Modules} (a : M ⟶ N)
    (h : ∀ i, (restrictFunctor (U.f i)).map a = 0) :
    a = 0 := by
  apply hom_ext a 0
  intro W
  ext s
  apply (abSheaf N).eq_of_locally_eq'
    (fun i ↦ (U.f i) ''ᵁ ((U.f i) ⁻¹ᵁ W)) W
    (fun i ↦ homOfLE (Scheme.Hom.image_preimage_le (U.f i) W))
  · intro x hx
    obtain ⟨i, ⟨y, hy⟩⟩ := U.exists_eq x
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨i, ⟨y, ?_, hy⟩⟩
    change (U.f i) y ∈ W
    rw [hy]
    exact hx
  · intro i
    have hi := congrArg (fun q ↦ q.app ((U.f i) ⁻¹ᵁ W)) (h i)
    rw [show ((0 : M ⟶ N).app W).hom s = 0 from rfl, map_zero]
    change ((N.presheaf.map
      (homOfLE (Scheme.Hom.image_preimage_le (U.f i) W)).op).hom)
        ((a.app W).hom s) = 0
    rw [show ((N.presheaf.map
      (homOfLE (Scheme.Hom.image_preimage_le (U.f i) W)).op).hom)
        ((a.app W).hom s) =
      (((restrictFunctor (U.f i)).map a).app ((U.f i) ⁻¹ᵁ W)).hom
        (((M.presheaf.map
          (homOfLE (Scheme.Hom.image_preimage_le (U.f i) W)).op).hom) s) from
      (CategoryTheory.congr_fun (a.mapPresheaf.naturality
        (homOfLE (Scheme.Hom.image_preimage_le (U.f i) W)).op) s).symm]
    rw [hi]
    rfl

end AlgebraicGeometry.Scheme.Modules

end
