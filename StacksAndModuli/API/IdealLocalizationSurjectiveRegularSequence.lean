module

public import StacksAndModuli.API.DeterminantalGradeLocus

/-!
# Regular-sequence witnesses after a localization and a quotient

An element of the extension of an ideal to a localization is a unit multiple of the
image of an element of the original ideal.  The same remains true after a further
surjective coefficient change: lift through the surjection, clear the localization
denominator, and then map the resulting unit relation forward.

The finite-family form applies this observation termwise.  Since regularity is invariant
under multiplying the terms by units, a regular sequence contained in the extended ideal
can be replaced by images of elements of the original ideal.  This is the denominator-
clearing shape needed for localized relative fibres, which are quotients of localizations.

Main declarations:

* `RingTheory.Sequence.IsUnitMultiple.map`;
* `Ideal.exists_mem_and_isUnitMultiple_algebraMap_of_mem_map_of_localization_surjective`;
* `Ideal.exists_family_mem_and_isRegular_map_of_isRegular_of_localization_surjective`.
-/

@[expose] public section

noncomputable section

universe u v w x

namespace RingTheory.Sequence

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A ring homomorphism preserves the relation of being a unit multiple. -/
theorem IsUnitMultiple.map {a b : R} (h : IsUnitMultiple a b) (f : R →+* S) :
    IsUnitMultiple (f a) (f b) := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨f c, hc.map f, by rw [map_mul]⟩

end RingTheory.Sequence

namespace Ideal

variable {R : Type u} {L : Type v} {S : Type w}
variable [CommRing R] [CommRing L] [CommRing S]
variable [Algebra R L] [Algebra L S] [Algebra R S] [IsScalarTower R L S]

/-- After a localization followed by a surjective coefficient change, an element of an
extended ideal is a unit multiple of the image of an element of the original ideal. -/
theorem exists_mem_and_isUnitMultiple_algebraMap_of_mem_map_of_localization_surjective
    (W : Submonoid R) [IsLocalization W L]
    (hsurj : Function.Surjective (algebraMap L S))
    (I : Ideal R) {z : S} (hz : z ∈ I.map (algebraMap R S)) :
    ∃ x : R, x ∈ I ∧
      RingTheory.Sequence.IsUnitMultiple z (algebraMap R S x) := by
  have hz' : z ∈ (I.map (algebraMap R L)).map (algebraMap L S) := by
    simpa only [Ideal.map_map, IsScalarTower.algebraMap_eq R L S] using hz
  obtain ⟨y, hy, hyz⟩ :=
    (Ideal.mem_map_iff_of_surjective (algebraMap L S) hsurj).mp hz'
  obtain ⟨x, hx, hunit⟩ :=
    exists_mem_and_isUnitMultiple_algebraMap_of_mem_map W I hy
  refine ⟨x, hx, ?_⟩
  rw [← hyz]
  simpa only [IsScalarTower.algebraMap_apply R L S] using
    hunit.map (algebraMap L S)

/-- A finite regular sequence contained in the extension of an ideal through a localization
and a surjective coefficient change can be replaced by images of elements of the original
ideal without losing regularity. -/
theorem exists_family_mem_and_isRegular_map_of_isRegular_of_localization_surjective
    (W : Submonoid R) [IsLocalization W L]
    (hsurj : Function.Surjective (algebraMap L S))
    {M : Type x} [AddCommGroup M] [Module S M]
    (I : Ideal R) (d : ℕ) (g : Fin d → S)
    (hgI : ∀ i, g i ∈ I.map (algebraMap R S))
    (hreg : RingTheory.Sequence.IsRegular M (List.ofFn g)) :
    ∃ f : Fin d → R, (∀ i, f i ∈ I) ∧
      RingTheory.Sequence.IsRegular M
        (List.ofFn fun i ↦ algebraMap R S (f i)) := by
  let hw (i : Fin d) :=
    exists_mem_and_isUnitMultiple_algebraMap_of_mem_map_of_localization_surjective
      W hsurj I (hgI i)
  let f : Fin d → R := fun i ↦ (hw i).choose
  have hfI (i : Fin d) : f i ∈ I := (hw i).choose_spec.1
  have hunit (i : Fin d) : RingTheory.Sequence.IsUnitMultiple
      (g i) (algebraMap R S (f i)) := (hw i).choose_spec.2
  refine ⟨f, hfI, ?_⟩
  exact (RingTheory.Sequence.isRegular_iff_of_forall₂_isUnitMultiple
    (RingTheory.Sequence.forall₂_isUnitMultiple_ofFn hunit)).mp hreg

end Ideal

end
