module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Residue fields under morphisms surjective on stalks

A morphism of schemes which is surjective on stalks induces an isomorphism on residue
fields at every point of its source. In particular, this applies to closed immersions.

## Main result

* `AlgebraicGeometry.Scheme.Hom.residueFieldMap_bijective_of_surjectiveOnStalks`.
* `AlgebraicGeometry.Scheme.Hom.residueFieldRingEquiv_of_surjectiveOnStalks`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- A morphism surjective on stalks induces a bijection from the residue field of the
image point to the residue field of the source point. -/
theorem Hom.residueFieldMap_bijective_of_surjectiveOnStalks
    {X Y : Scheme.{u}} (f : X ⟶ Y) [SurjectiveOnStalks f] (x : X) :
    Function.Bijective (f.residueFieldMap x) := by
  constructor
  · exact RingHom.injective _
  · intro y
    obtain ⟨z, rfl⟩ := X.residue_surjective x y
    obtain ⟨w, hw⟩ := f.stalkMap_surjective x z
    refine ⟨Y.residue (f x) w, ?_⟩
    have h := DFunLike.congr_fun
      (CommRingCat.hom_ext_iff.mp (residue_residueFieldMap f x)) w
    simpa only [CommRingCat.comp_apply, hw] using h

/-- A closed immersion induces a bijection on residue fields at every point of its
source. -/
theorem Hom.residueFieldMap_bijective_of_isClosedImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] (x : X) :
    Function.Bijective (f.residueFieldMap x) :=
  f.residueFieldMap_bijective_of_surjectiveOnStalks x

/-- The residue-field map of a morphism surjective on stalks, bundled as a ring
equivalence. -/
noncomputable def Hom.residueFieldRingEquiv_of_surjectiveOnStalks
    {X Y : Scheme.{u}} (f : X ⟶ Y) [SurjectiveOnStalks f] (x : X) :
    Y.residueField (f x) ≃+* X.residueField x :=
  RingEquiv.ofBijective (f.residueFieldMap x).hom
    (f.residueFieldMap_bijective_of_surjectiveOnStalks x)

/-- The residue-field map of a closed immersion, bundled as a ring equivalence. -/
noncomputable def Hom.residueFieldRingEquiv_of_isClosedImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] (x : X) :
    Y.residueField (f x) ≃+* X.residueField x :=
  f.residueFieldRingEquiv_of_surjectiveOnStalks x

end AlgebraicGeometry.Scheme
