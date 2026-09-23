module

public import StacksAndModuli.«Section3.1-Descent».«part3.1.4-descending-schemes»
public import StacksAndModuli.API.AffineSchemeDescent
public import StacksAndModuli.API.RepresentableSheafProperty
public import StacksAndModuli.API.QuasiAffineMorphism
public import StacksAndModuli.API.SchemeRelationSaturation
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Sites.Etale

/-!
# Effective descent for special classes of schemes

This module formalizes Proposition 3.1.12
(`prop:fpqc-descent-for-affine-quasi-affine-schemes`), Theorem 3.1.14
(`thm:fppf-descent-for-separated-locally-quasi-finite-schemes`), Example 3.1.16
(`ex:non-effective-descent`), and Proposition 3.1.17
(`prop:fpqc-descent-for-principal-G-bundles`) of §3.1 of *Stacks and Moduli*.

Effective descent is exposed in the form needed downstream: for a topology `J`
contained in the fpqc (respectively fppf) topology, being a sheaf on an over-site
represented by a morphism with the indicated property is a `J`-local object property.
Together with `GrothendieckTopology.representableByProperty_of_map_obj`, this produces
the descended representing scheme and its comparison isomorphism.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- The big étale topology is contained in the fppf topology. -/
lemma etaleTopology_le_fppfTopology :
    etaleTopology.{u} ≤ fppfTopology := by
  apply Precoverage.toGrothendieck_mono
  apply precoverage_mono
  intro X Y f hf
  letI : Etale f := hf
  exact ⟨inferInstance, inferInstance⟩

section PropFpqcDescentForAffineQuasiAffineSchemes

/-- Reduction step used in the proof of Proposition 3.1.12 (affine coordinate form):
a multiplicative affine descent coaction along a faithfully flat ring map is effective.
The descended scheme is the spectrum of the equalizer algebra, and the displayed
isomorphism identifies its pullback with the original affine scheme over `Spec B`.

This is the algebraic core of the book's affine case after restricting to an affine
base and a faithfully flat affine refinement. -/
theorem exists_affine_of_commAlgebraDescentData
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B]
    (D : Algebra.CommAlgebraDescentData A B) :
    ∃ (X : Scheme.{u}) (i : X ⟶ Spec (.of A)) (_ : IsAffineHom i)
      (e : D.originalScheme ≅ pullback i D.coverHom),
      D.originalHom = e.hom ≫ pullback.snd i D.coverHom := by
  refine ⟨D.descendedScheme, D.descendedHom, ?_, D.comparisonIso, ?_⟩
  · dsimp [Algebra.CommAlgebraDescentData.descendedScheme,
      Algebra.CommAlgebraDescentData.descendedHom]
    infer_instance
  · exact D.comparisonIso_hom_snd.symm

/-- Reduction step used in the proof of Proposition 3.1.12 (quasi-affine open-locus
coordinate form): a compact open in an affine descent datum which is saturated for the
kernel pair descends to a quasi-affine open in the invariant affine scheme. -/
theorem exists_quasiAffineOpen_of_commAlgebraDescentData
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B]
    (D : Algebra.CommAlgebraDescentData A B)
    (U' : D.originalScheme.Opens) (hcompactU' : IsCompact (U' : Set D.originalScheme))
    (hU' : (pullback.fst D.descentCoverHom D.descentCoverHom) ⁻¹ᵁ U' =
      (pullback.snd D.descentCoverHom D.descentCoverHom) ⁻¹ᵁ U') :
    ∃ U : D.descendedScheme.Opens,
      D.descentCoverHom ⁻¹ᵁ U = U' ∧ U.toScheme.IsQuasiAffine := by
  have hff : (algebraMap A B).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  obtain ⟨U, hU⟩ := exists_opens_preimage_eq_of_fpqcCover
    (D.descentCoverHom_isFpqcCover hff) U' hU'
  refine ⟨U, hU, ?_⟩
  have hcompact : IsCompact (U : Set D.descendedScheme) := by
    have himage : D.descentCoverHom.base '' (U' : Set D.originalScheme) =
        (U : Set D.descendedScheme) := by
      rw [← congrArg SetLike.coe hU]
      exact Set.image_preimage_eq _ (D.descentCoverHom_surjective hff).surj
    rw [← himage]
    exact hcompactU'.image D.descentCoverHom.continuous
  letI : CompactSpace U := isCompact_iff_compactSpace.mp hcompact
  letI : IsAffine D.descendedScheme := by
    dsimp [Algebra.CommAlgebraDescentData.descendedScheme]
    infer_instance
  exact Scheme.IsQuasiAffine.of_isImmersion U.ι

/-- **Proposition 3.1.12**
(`prop:fpqc-descent-for-affine-quasi-affine-schemes`) (affine case):
representability by an affine morphism is local for every topology contained in the
fpqc topology.  Equivalently, affine schemes with descent datum along an fpqc cover
descend effectively. -/
theorem isLocal_representableByProperty_isAffineHom
    (J : GrothendieckTopology Scheme.{u}) (hJ : J ≤ fpqcTopology) :
    Pseudofunctor.ObjectProperty.IsLocal
      (J.representableByProperty
        (@IsAffineHom : MorphismProperty Scheme.{u})) J := by
  sorry

/-- **Proposition 3.1.12**
(`prop:fpqc-descent-for-affine-quasi-affine-schemes`) (quasi-affine case):
representability by a quasi-affine morphism is local for every topology contained in
the fpqc topology. -/
theorem isLocal_representableByProperty_isQuasiAffineHom
    (J : GrothendieckTopology Scheme.{u}) (hJ : J ≤ fpqcTopology) :
    Pseudofunctor.ObjectProperty.IsLocal
      (J.representableByProperty
        (IsQuasiAffineHom : MorphismProperty Scheme.{u})) J := by
  sorry

end PropFpqcDescentForAffineQuasiAffineSchemes

section ThmFppfDescentForSeparatedLocallyQuasiFiniteSchemes

/-- **Theorem 3.1.14**
(`thm:fppf-descent-for-separated-locally-quasi-finite-schemes`):
representability by a locally finite-type, locally quasi-finite, separated morphism is
local for every topology contained in the fppf topology.

The explicit `LocallyOfFiniteType` factor is necessary because Mathlib's
`LocallyQuasiFinite` records only the fibrewise-discreteness clause, whereas the book
uses the standard Stacks-project notion which includes finite type. -/
theorem isLocal_representableByProperty_locallyQuasiFinite_isSeparated
    (J : GrothendieckTopology Scheme.{u}) (hJ : J ≤ fppfTopology) :
    Pseudofunctor.ObjectProperty.IsLocal
      (J.representableByProperty
        (@LocallyOfFiniteType ⊓ @LocallyQuasiFinite ⊓ @IsSeparated :
          MorphismProperty Scheme.{u})) J := by
  sorry

end ThmFppfDescentForSeparatedLocallyQuasiFiniteSchemes

section ExNonEffectiveDescent

/- Prose record of Example 3.1.16: arbitrary descent data for
schemes need not be effective, even for an étale cover.  The book cites Hironaka,
Raynaud, and further literature examples; these examples require substantial geometry
not currently present in Mathlib, so this block records the claim as prose rather than
introducing an unfaithful abstract counterexample. -/

-- STATUS: remark-complete

end ExNonEffectiveDescent

end AlgebraicGeometry.Scheme
