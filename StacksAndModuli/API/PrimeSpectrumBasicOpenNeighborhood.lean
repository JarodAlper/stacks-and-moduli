module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksProject.Topology.KrullDimension.«definition-Krull»

/-!
# Principal-open neighbourhoods in affine spectra

Principal opens form a basis for the Zariski topology on an affine spectrum.  This file packages
the pointwise form of that fact using `TopologicalSpace.Opens`, and combines it with pointwise
topological Krull dimension: the minimum dimension at a point is already attained on a principal
open neighbourhood.

Main declarations:

* `PrimeSpectrum.exists_basicOpen_le_of_mem`;
* `PrimeSpectrum.exists_basicOpen_topologicalKrullDim_eq_atPoint`;
* `PrimeSpectrum.localizationAwayHomeomorphBasicOpen`;
* `PrimeSpectrum.topologicalKrullDim_basicOpen_eq_ringKrullDim_of_isLocalizationAway`.
-/

@[expose] public section

open TopologicalSpace

universe u v

namespace PrimeSpectrum

/-- The spectrum of a localization away from one element is homeomorphic to the
corresponding principal open in the original spectrum. -/
noncomputable def localizationAwayHomeomorphBasicOpen
    {R : Type u} [CommSemiring R] (S : Type v) [CommSemiring S]
    [Algebra R S] (f : R) [IsLocalization.Away f S] :
    PrimeSpectrum S ≃ₜ (basicOpen f : Set (PrimeSpectrum R)) :=
  (localization_away_isOpenEmbedding S f).isEmbedding.toHomeomorph |>.trans
    (Homeomorph.setCongr (localization_away_comap_range S f))

/-- The topological Krull dimension of a principal open is the ring Krull dimension
of any chosen localization away from its defining element. -/
theorem topologicalKrullDim_basicOpen_eq_ringKrullDim_of_isLocalizationAway
    {R : Type u} [CommSemiring R] (S : Type v) [CommSemiring S]
    [Algebra R S] (f : R) [IsLocalization.Away f S] :
    topologicalKrullDim (basicOpen f) = ringKrullDim S := by
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  let e := localizationAwayHomeomorphBasicOpen S f
  exact (IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph).symm

/-- The topological Krull dimension of a principal open is the ring Krull dimension
of the canonical localization away from its defining element. -/
theorem topologicalKrullDim_basicOpen_eq_ringKrullDim_away
    {R : Type u} [CommSemiring R] (f : R) :
    topologicalKrullDim (basicOpen f) =
      ringKrullDim (Localization.Away f) :=
  topologicalKrullDim_basicOpen_eq_ringKrullDim_of_isLocalizationAway
    (Localization.Away f) f

/-- Multiplying the defining function of a principal open by a unit does not change
the principal open. -/
theorem basicOpen_mul_eq_right_of_isUnit
    {R : Type u} [CommSemiring R] (c f : R) (hc : IsUnit c) :
    basicOpen (c * f) = basicOpen f := by
  rw [basicOpen_mul]
  have hc_top : basicOpen c = ⊤ := by
    apply top_unique
    intro p _
    change c ∉ p.asIdeal
    exact Ideal.notMem_of_isUnit p.asIdeal hc
  simp [hc_top]

/-- Scaling the defining function of a principal open by a unit scalar does not change
the principal open. -/
theorem basicOpen_smul_eq_of_isUnit
    {K : Type u} {R : Type v} [CommSemiring K] [CommSemiring R] [Algebra K R]
    (c : K) (f : R) (hc : IsUnit c) :
    basicOpen (c • f) = basicOpen f := by
  rw [Algebra.smul_def]
  exact basicOpen_mul_eq_right_of_isUnit _ _ (hc.map (algebraMap K R))

/-- The action of a coefficient-ring unit does not change the principal open defined by
an element of an algebra. -/
theorem basicOpen_units_smul_eq
    {K : Type u} {R : Type v} [CommSemiring K] [CommSemiring R] [Algebra K R]
    (c : Kˣ) (f : R) :
    basicOpen (c • f) = basicOpen f := by
  rw [Units.smul_def]
  exact basicOpen_smul_eq_of_isUnit (c : K) f c.isUnit

/-- Every open neighbourhood of a point of an affine spectrum contains a principal-open
neighbourhood of that point. -/
theorem exists_basicOpen_le_of_mem
    {R : Type u} [CommRing R] (x : PrimeSpectrum R) (U : Opens (PrimeSpectrum R))
    (hxU : x ∈ U) :
    ∃ f : R, x ∈ basicOpen f ∧ basicOpen f ≤ U := by
  obtain ⟨V, ⟨f, rfl⟩, hxV, hVU⟩ :=
    isTopologicalBasis_basic_opens.exists_subset_of_mem_open hxU U.isOpen
  exact ⟨f, hxV, hVU⟩

/-- Pointwise topological Krull dimension on an affine spectrum is attained on a principal-open
neighbourhood. -/
theorem exists_basicOpen_topologicalKrullDim_eq_atPoint
    {R : Type u} [CommRing R] (x : PrimeSpectrum R) :
    ∃ f : R, x ∈ basicOpen f ∧
      topologicalKrullDim (basicOpen f) =
        topologicalKrullDimAtPoint (PrimeSpectrum R) x := by
  obtain ⟨U, hxU, hU⟩ := exists_open_topologicalKrullDim_eq_atPoint x
  obtain ⟨f, hxf, hfU⟩ := exists_basicOpen_le_of_mem x U hxU
  refine ⟨f, hxf, le_antisymm ?_ ?_⟩
  · exact (topologicalKrullDim_opens_mono hfU).trans_eq hU
  · exact topologicalKrullDimAtPoint_le (basicOpen f) hxf

/-- If the pointwise dimension of an affine spectrum is the finite value `n`, a principal-open
neighbourhood has dimension `n`. -/
theorem exists_basicOpen_topologicalKrullDim_eq_nat
    {R : Type u} [CommRing R] {x : PrimeSpectrum R} {n : ℕ}
    (h : topologicalKrullDimAtPoint (PrimeSpectrum R) x = (n : WithBot ℕ∞)) :
    ∃ f : R, x ∈ basicOpen f ∧
      topologicalKrullDim (basicOpen f) = (n : WithBot ℕ∞) := by
  obtain ⟨f, hxf, hf⟩ := exists_basicOpen_topologicalKrullDim_eq_atPoint x
  exact ⟨f, hxf, hf.trans h⟩

end PrimeSpectrum

end
