module

public import StacksAndModuli.API.SmoothOfRelativeDimension
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.RingTheory.Etale.Descent

/-!
# Faithfully flat descent of smooth relative dimension

Supporting material for §4.3 of *Stacks and Moduli*, corresponding to no labelled result
of the book and to no Stacks Project tag.

A smooth algebra has a well-defined relative dimension on each standard-smooth chart.
After a faithfully flat base change, that dimension can be read on the base-changed chart;
faithful flatness ensures that a nonempty chart remains nonempty.  This gives descent for
ring maps which are locally standard smooth of a fixed relative dimension.

## Main declarations

- `RingHom.IsStandardSmooth.exists_isStandardSmoothOfRelativeDimension`: a standard-smooth
  ring map has some relative dimension.
- `RingHom.locally_isStandardSmoothOfRelativeDimension_codescendsAlong_faithfullyFlat`:
  being locally standard smooth of relative dimension `n` descends along faithfully flat
  base change.
- `AlgebraicGeometry.smoothOfRelativeDimension_descendsAlong`: the corresponding scheme
  morphism property descends along surjective flat quasi-compact base change.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open TensorProduct

universe u

namespace Ideal

/-- Removing nilpotent elements from a set which spans the unit ideal still leaves a set
spanning the unit ideal. -/
lemma span_nonNilpotent_eq_top {R : Type u} [CommRing R] [Nontrivial R] (s : Set R)
    (hs : span s = ⊤) : span {x | x ∈ s ∧ ¬ IsNilpotent x} = ⊤ := by
  by_contra hne
  obtain ⟨M, hM, hle⟩ := ne_top_iff_exists_maximal.mp hne
  have hspan : span s ≤ M := by
    rw [span_le]
    intro x hx
    by_cases hnil : IsNilpotent x
    · exact nilpotent_iff_mem_prime.mp hnil M hM.isPrime
    · exact hle (subset_span ⟨hx, hnil⟩)
  rw [hs] at hspan
  exact hM.ne_top (top_unique hspan)

end Ideal

namespace RingHom

/-- A standard-smooth ring homomorphism is standard smooth of some relative dimension. -/
lemma IsStandardSmooth.exists_isStandardSmoothOfRelativeDimension
    {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : IsStandardSmooth f) : ∃ n, IsStandardSmoothOfRelativeDimension n f := by
  algebraize [f]
  obtain ⟨ι, σ, hσ, hι, ⟨P⟩⟩ := hf.toAlgebra.out
  letI : _root_.Finite σ := hσ
  letI : _root_.Finite ι := hι
  refine ⟨P.dimension, ?_⟩
  exact P.isStandardSmoothOfRelativeDimension rfl

/-- Ring maps which are locally standard smooth of relative dimension `n` descend along
faithfully flat base change. -/
lemma locally_isStandardSmoothOfRelativeDimension_codescendsAlong_faithfullyFlat (n : ℕ) :
    CodescendsAlong (Locally (IsStandardSmoothOfRelativeDimension n)) FaithfullyFlat := by
  refine CodescendsAlong.mk FaithfullyFlat
    (locally_respectsIso (@isStandardSmoothOfRelativeDimension_respectsIso n)) ?_
  intro R S T _ _ _ _ _ hff hdim
  have hffRing : FaithfullyFlat (algebraMap R S) := hff
  rw [faithfullyFlat_algebraMap_iff] at hff
  have hsmoothST : Smooth (algebraMap S (S ⊗[R] T)) := by
    rw [smooth_iff_locally_isStandardSmooth]
    exact locally_of_locally
      (fun h ↦ IsStandardSmoothOfRelativeDimension.isStandardSmooth n _ h) hdim
  have hsmoothRT : Smooth (algebraMap R T) :=
    Smooth.codescendsAlong_faithfullyFlat.algebraMap_tensorProduct
      FaithfullyFlat R S T hffRing hsmoothST
  by_cases hT : Nontrivial T
  · letI : Nontrivial T := hT
    obtain ⟨s, hs, hstandard⟩ := hsmoothRT.locally_isStandardSmooth
    refine ⟨{x | x ∈ s ∧ ¬ IsNilpotent x}, Ideal.span_nonNilpotent_eq_top s hs,
      fun t ht ↦ ?_⟩
    have ht_not_nilpotent : ¬ IsNilpotent t := ht.2
    have ht_mem : t ∈ s := ht.1
    let Tₜ := Localization.Away t
    let fₜ : R →+* Tₜ := (algebraMap T Tₜ).comp (algebraMap R T)
    have hstandardₜ : IsStandardSmooth fₜ := hstandard t ht_mem
    obtain ⟨m, hm⟩ := hstandardₜ.exists_isStandardSmoothOfRelativeDimension
    have hTₜ : ¬ Subsingleton Tₜ := by
      intro hsub
      apply ht_not_nilpotent
      rw [isNilpotent_iff_zero_mem_powers]
      exact (IsLocalization.subsingleton_iff (M := Submonoid.powers t) (S := Tₜ)).mp hsub
    letI : Nontrivial Tₜ := not_subsingleton_iff_nontrivial.mp hTₜ
    letI : Module.FaithfullyFlat R S := hff
    have hm' : IsStandardSmoothOfRelativeDimension m (algebraMap R Tₜ) := by
      have hmap : fₜ = algebraMap R Tₜ := by
        ext x
        exact (IsScalarTower.algebraMap_apply R T Tₜ x).symm
      exact hmap ▸ hm
    have hmBase : IsStandardSmoothOfRelativeDimension m
        (algebraMap S (S ⊗[R] Tₜ)) :=
      (isStandardSmoothOfRelativeDimension_isStableUnderBaseChange m).tensorProduct S hm'
    letI : Algebra T (S ⊗[R] T) := Algebra.TensorProduct.rightAlgebra
    let Bₜ := Localization.Away (1 ⊗ₜ[R] t : S ⊗[R] T)
    let e : S ⊗[R] Tₜ ≃ₐ[S] Bₜ :=
      IsLocalization.Away.tensorProductEquivTMulRight R S t Tₜ
    have hdimBₜ : Locally (IsStandardSmoothOfRelativeDimension n)
        (algebraMap S Bₜ) := by
      have h := locally_stableUnderCompositionWithLocalizationAwayTarget
        (isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).2
        Bₜ (1 ⊗ₜ[R] t : S ⊗[R] T) (algebraMap S (S ⊗[R] T)) hdim
      have hmap : (algebraMap (S ⊗[R] T) Bₜ).comp (algebraMap S (S ⊗[R] T)) =
          algebraMap S Bₜ := by
        ext x
        exact (IsScalarTower.algebraMap_apply S (S ⊗[R] T) Bₜ x).symm
      exact hmap ▸ h
    have hmBₜ : IsStandardSmoothOfRelativeDimension m (algebraMap S Bₜ) := by
      have h := (@isStandardSmoothOfRelativeDimension_respectsIso m).1
        (algebraMap S (S ⊗[R] Tₜ)) e.toRingEquiv hmBase
      have hmap : e.toRingEquiv.toRingHom.comp (algebraMap S (S ⊗[R] Tₜ)) =
          algebraMap S Bₜ := by
        ext x
        exact e.commutes x
      exact hmap ▸ h
    haveI : Nontrivial (S ⊗[R] Tₜ) :=
      (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right R S).2 inferInstance
    letI : Nontrivial Bₜ := e.symm.toEquiv.nontrivial
    letI : Algebra.IsStandardSmoothOfRelativeDimension m S Bₜ :=
      (isStandardSmoothOfRelativeDimension_algebraMap m).mp hmBₜ
    have hnm : n = m :=
      Algebra.IsStandardSmoothOfRelativeDimension.eq_of_locally hdimBₜ
    simpa [hnm] using hm
  · haveI : Subsingleton T := not_nontrivial_iff_subsingleton.mp hT
    exact ⟨∅, Subsingleton.elim _ _, by simp⟩

end RingHom

namespace AlgebraicGeometry

/-- Smooth morphisms of fixed relative dimension descend along surjective, flat,
quasi-compact base change. -/
instance smoothOfRelativeDimension_descendsAlong (n : ℕ) :
    CategoryTheory.MorphismProperty.DescendsAlong
      (@SmoothOfRelativeDimension n : CategoryTheory.MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact :
        CategoryTheory.MorphismProperty Scheme.{u}) := by
  let _ : CategoryTheory.MorphismProperty.IsStableUnderBaseChange
      (@SmoothOfRelativeDimension n : CategoryTheory.MorphismProperty Scheme.{u}) :=
    smoothOfRelativeDimension_isStableUnderBaseChange n
  exact HasRingHomProperty.descendsAlong_flat
    (RingHom.locally_isStandardSmoothOfRelativeDimension_codescendsAlong_faithfullyFlat n)

end AlgebraicGeometry
