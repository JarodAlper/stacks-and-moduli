module

public import StacksAndModuli.«Section3.1-Descent».«part3.1.4b-effective-descent-schemes»
public import StacksAndModuli.API.SchemeRepresentableSheafDescent
public import StacksAndModuli.API.QuasiAffineMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# The descent criterion for a sheaf to be a scheme

This module formalizes Proposition 3.3.17
(`prop:descent-criterion-for-an-fppf-sheaf-to-be-a-scheme`) of §3.3 (Presheaves and
sheaves) of *Stacks and Moduli*,
section label `sec:sheaves`.

The book works directly on the over-sites: `F` is a sheaf on `(Sch/Y)_ét` (respectively
`(Sch/Y)_fppf`), and its pullback to `X` is represented by a scheme over `X`. We use the
same formulation. For a morphism property `P`, the assertion that a sheaf on `Sch/Y` is
represented by a `P`-morphism is
`Scheme.etaleTopology.representableByProperty P` (or its fppf analogue).

All five properties and both variants in the book are included: open immersion, closed
immersion, affine, quasi-affine, and locally quasi-finite separated. In the last case an
explicit `LocallyOfFiniteType` factor records the finite-type clause in the book's standard
meaning of locally quasi-finite; Mathlib's bare `LocallyQuasiFinite` only records the
fibrewise-discreteness clause.

Main results:
- `MorphismProperty.presheaf_isOpenImmersion_of_pullback` and its `_fppf` variant;
- `MorphismProperty.presheaf_isClosedImmersion_of_pullback` and its `_fppf` variant;
- `MorphismProperty.presheaf_isAffineHom_of_pullback` and its `_fppf` variant;
- `MorphismProperty.presheaf_isQuasiAffineHom_of_pullback` and its `_fppf` variant;
- `MorphismProperty.presheaf_locallyQuasiFinite_isSeparated_of_pullback` and its `_fppf`
  variant.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section PropDescentCriterionForAnFppfSheafToBeAScheme

open CategoryTheory CategoryTheory.Bicategory AlgebraicGeometry Opposite

universe u

variable {X Y : Scheme.{u}} (π : X ⟶ Y)

/-- **Proposition 3.3.17**
(`prop:descent-criterion-for-an-fppf-sheaf-to-be-a-scheme`) (open immersion,
smooth/étale variant): if a sheaf on `(Sch/Y)_ét` becomes represented by an open
subscheme after pullback along a surjective smooth morphism `X ⟶ Y`, then it is represented
by an open subscheme of `Y`. -/
theorem MorphismProperty.presheaf_isOpenImmersion_of_pullback
    [Surjective π] [Smooth π]
    (F : Sheaf (Scheme.etaleTopology.over Y) (Type u))
    (hF : (Scheme.etaleTopology.representableByProperty
      (@IsOpenImmersion : MorphismProperty Scheme.{u})).prop (.mk (op X))
        ((Scheme.etaleTopology.overMapPullback (Type u) π).obj F)) :
    (Scheme.etaleTopology.representableByProperty
      (@IsOpenImmersion : MorphismProperty Scheme.{u})).prop (.mk (op Y)) F := by
  exact Scheme.open_representableByProperty_of_fpqcCover π Scheme.etaleTopology
    (Scheme.IsFpqcCover.of_fppf π)
    (Scheme.generate_singleton_mem_etaleTopology_of_smooth π) F hF

/-- **Proposition 3.3.17**
(`prop:descent-criterion-for-an-fppf-sheaf-to-be-a-scheme`) (closed immersion,
smooth/étale variant). -/
theorem MorphismProperty.presheaf_isClosedImmersion_of_pullback
    [Surjective π] [Smooth π]
    (F : Sheaf (Scheme.etaleTopology.over Y) (Type u))
    (hF : (Scheme.etaleTopology.representableByProperty
      (@IsClosedImmersion : MorphismProperty Scheme.{u})).prop (.mk (op X))
        ((Scheme.etaleTopology.overMapPullback (Type u) π).obj F)) :
    (Scheme.etaleTopology.representableByProperty
      (@IsClosedImmersion : MorphismProperty Scheme.{u})).prop (.mk (op Y)) F := by
  exact Scheme.closed_representableByProperty_of_fpqcCover π Scheme.etaleTopology
    (Scheme.IsFpqcCover.of_fppf π)
    (Scheme.generate_singleton_mem_etaleTopology_of_smooth π) F hF

/-- **Proposition 3.3.17**
(`prop:descent-criterion-for-an-fppf-sheaf-to-be-a-scheme`) (affine,
smooth/étale variant). -/
theorem MorphismProperty.presheaf_isAffineHom_of_pullback
    [Surjective π] [Smooth π]
    (F : Sheaf (Scheme.etaleTopology.over Y) (Type u))
    (hF : (Scheme.etaleTopology.representableByProperty
      (@IsAffineHom : MorphismProperty Scheme.{u})).prop (.mk (op X))
        ((Scheme.etaleTopology.overMapPullback (Type u) π).obj F)) :
    (Scheme.etaleTopology.representableByProperty
      (@IsAffineHom : MorphismProperty Scheme.{u})).prop (.mk (op Y)) F := by
  let _ := Scheme.isLocal_representableByProperty_isAffineHom Scheme.etaleTopology
    (Scheme.etaleTopology_le_fppfTopology.trans Scheme.fppfTopology_le_fpqcTopology)
  exact Scheme.etale_representableByProperty_of_smooth π _ F hF

/-- **Proposition 3.3.17**
(`prop:descent-criterion-for-an-fppf-sheaf-to-be-a-scheme`) (quasi-affine,
smooth/étale variant). -/
theorem MorphismProperty.presheaf_isQuasiAffineHom_of_pullback
    [Surjective π] [Smooth π]
    (F : Sheaf (Scheme.etaleTopology.over Y) (Type u))
    (hF : (Scheme.etaleTopology.representableByProperty
      (IsQuasiAffineHom : MorphismProperty Scheme.{u})).prop (.mk (op X))
        ((Scheme.etaleTopology.overMapPullback (Type u) π).obj F)) :
    (Scheme.etaleTopology.representableByProperty
      (IsQuasiAffineHom : MorphismProperty Scheme.{u})).prop (.mk (op Y)) F := by
  let _ := Scheme.isLocal_representableByProperty_isQuasiAffineHom Scheme.etaleTopology
    (Scheme.etaleTopology_le_fppfTopology.trans Scheme.fppfTopology_le_fpqcTopology)
  exact Scheme.etale_representableByProperty_of_smooth π _ F hF

/-- **Proposition 3.3.17**
(`prop:descent-criterion-for-an-fppf-sheaf-to-be-a-scheme`) (locally quasi-finite and
separated, smooth/étale variant). `LocallyOfFiniteType` supplies the finite-type clause
of the standard notion used by the book. -/
theorem MorphismProperty.presheaf_locallyQuasiFinite_isSeparated_of_pullback
    [Surjective π] [Smooth π]
    (F : Sheaf (Scheme.etaleTopology.over Y) (Type u))
    (hF : (Scheme.etaleTopology.representableByProperty
      (@LocallyOfFiniteType ⊓ @LocallyQuasiFinite ⊓ @IsSeparated :
        MorphismProperty Scheme.{u})).prop (.mk (op X))
          ((Scheme.etaleTopology.overMapPullback (Type u) π).obj F)) :
    (Scheme.etaleTopology.representableByProperty
      (@LocallyOfFiniteType ⊓ @LocallyQuasiFinite ⊓ @IsSeparated :
        MorphismProperty Scheme.{u})).prop (.mk (op Y)) F := by
  let _ := Scheme.isLocal_representableByProperty_locallyQuasiFinite_isSeparated
    Scheme.etaleTopology Scheme.etaleTopology_le_fppfTopology
  exact Scheme.etale_representableByProperty_of_smooth π _ F hF

/-- **Proposition 3.3.17**
(`prop:descent-criterion-for-an-fppf-sheaf-to-be-a-scheme`) (open immersion, fppf
variant): if a sheaf on `(Sch/Y)_fppf` becomes represented by an open subscheme after
pullback along an fppf morphism `X ⟶ Y`, then it is represented by an open subscheme of
`Y`. -/
theorem MorphismProperty.presheaf_isOpenImmersion_of_pullback_fppf
    [Surjective π] [Flat π] [LocallyOfFinitePresentation π]
    (F : Sheaf (Scheme.fppfTopology.over Y) (Type u))
    (hF : (Scheme.fppfTopology.representableByProperty
      (@IsOpenImmersion : MorphismProperty Scheme.{u})).prop (.mk (op X))
        ((Scheme.fppfTopology.overMapPullback (Type u) π).obj F)) :
    (Scheme.fppfTopology.representableByProperty
      (@IsOpenImmersion : MorphismProperty Scheme.{u})).prop (.mk (op Y)) F := by
  exact Scheme.open_representableByProperty_of_fpqcCover π Scheme.fppfTopology
    (Scheme.IsFpqcCover.of_fppf π)
    (Scheme.generate_singleton_mem_fppfTopology_of_fppf π) F hF

/-- **Proposition 3.3.17**
(`prop:descent-criterion-for-an-fppf-sheaf-to-be-a-scheme`) (closed immersion, fppf
variant). -/
theorem MorphismProperty.presheaf_isClosedImmersion_of_pullback_fppf
    [Surjective π] [Flat π] [LocallyOfFinitePresentation π]
    (F : Sheaf (Scheme.fppfTopology.over Y) (Type u))
    (hF : (Scheme.fppfTopology.representableByProperty
      (@IsClosedImmersion : MorphismProperty Scheme.{u})).prop (.mk (op X))
        ((Scheme.fppfTopology.overMapPullback (Type u) π).obj F)) :
    (Scheme.fppfTopology.representableByProperty
      (@IsClosedImmersion : MorphismProperty Scheme.{u})).prop (.mk (op Y)) F := by
  exact Scheme.closed_representableByProperty_of_fpqcCover π Scheme.fppfTopology
    (Scheme.IsFpqcCover.of_fppf π)
    (Scheme.generate_singleton_mem_fppfTopology_of_fppf π) F hF

/-- **Proposition 3.3.17**
(`prop:descent-criterion-for-an-fppf-sheaf-to-be-a-scheme`) (affine, fppf variant). -/
theorem MorphismProperty.presheaf_isAffineHom_of_pullback_fppf
    [Surjective π] [Flat π] [LocallyOfFinitePresentation π]
    (F : Sheaf (Scheme.fppfTopology.over Y) (Type u))
    (hF : (Scheme.fppfTopology.representableByProperty
      (@IsAffineHom : MorphismProperty Scheme.{u})).prop (.mk (op X))
        ((Scheme.fppfTopology.overMapPullback (Type u) π).obj F)) :
    (Scheme.fppfTopology.representableByProperty
      (@IsAffineHom : MorphismProperty Scheme.{u})).prop (.mk (op Y)) F := by
  let _ := Scheme.isLocal_representableByProperty_isAffineHom Scheme.fppfTopology
    Scheme.fppfTopology_le_fpqcTopology
  exact Scheme.fppf_representableByProperty_of_fppf π _ F hF

/-- **Proposition 3.3.17**
(`prop:descent-criterion-for-an-fppf-sheaf-to-be-a-scheme`) (quasi-affine, fppf
variant). -/
theorem MorphismProperty.presheaf_isQuasiAffineHom_of_pullback_fppf
    [Surjective π] [Flat π] [LocallyOfFinitePresentation π]
    (F : Sheaf (Scheme.fppfTopology.over Y) (Type u))
    (hF : (Scheme.fppfTopology.representableByProperty
      (IsQuasiAffineHom : MorphismProperty Scheme.{u})).prop (.mk (op X))
        ((Scheme.fppfTopology.overMapPullback (Type u) π).obj F)) :
    (Scheme.fppfTopology.representableByProperty
      (IsQuasiAffineHom : MorphismProperty Scheme.{u})).prop (.mk (op Y)) F := by
  let _ := Scheme.isLocal_representableByProperty_isQuasiAffineHom Scheme.fppfTopology
    Scheme.fppfTopology_le_fpqcTopology
  exact Scheme.fppf_representableByProperty_of_fppf π _ F hF

/-- **Proposition 3.3.17**
(`prop:descent-criterion-for-an-fppf-sheaf-to-be-a-scheme`) (locally quasi-finite and
separated, fppf variant). `LocallyOfFiniteType` supplies the finite-type clause of the
standard notion used by the book. -/
theorem MorphismProperty.presheaf_locallyQuasiFinite_isSeparated_of_pullback_fppf
    [Surjective π] [Flat π] [LocallyOfFinitePresentation π]
    (F : Sheaf (Scheme.fppfTopology.over Y) (Type u))
    (hF : (Scheme.fppfTopology.representableByProperty
      (@LocallyOfFiniteType ⊓ @LocallyQuasiFinite ⊓ @IsSeparated :
        MorphismProperty Scheme.{u})).prop (.mk (op X))
          ((Scheme.fppfTopology.overMapPullback (Type u) π).obj F)) :
    (Scheme.fppfTopology.representableByProperty
      (@LocallyOfFiniteType ⊓ @LocallyQuasiFinite ⊓ @IsSeparated :
        MorphismProperty Scheme.{u})).prop (.mk (op Y)) F := by
  let _ := Scheme.isLocal_representableByProperty_locallyQuasiFinite_isSeparated
    Scheme.fppfTopology (le_refl _)
  exact Scheme.fppf_representableByProperty_of_fppf π _ F hF

end PropDescentCriterionForAnFppfSheafToBeAScheme
