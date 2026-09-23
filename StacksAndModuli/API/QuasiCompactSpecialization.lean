module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Specializations in the image of a quasi-compact scheme morphism

This file supplies the scheme-theoretic specialization lemma used when studying the
topological image of a quasi-compact morphism of algebraic stacks.  The affine core is
the prime-ideal fact that a point of the closure of the image of `Spec.map φ` is a
specialization of an actual image point.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Topology

universe u

namespace PrimeSpectrum

/-- A point in the closure of the image of a map of prime spectra is a specialization
of a point in the image. -/
theorem exists_specializes_of_mem_closure_range_comap
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    {p : PrimeSpectrum R} (hp : p ∈ closure (Set.range (PrimeSpectrum.comap f))) :
    ∃ q : PrimeSpectrum S, PrimeSpectrum.comap f q ⤳ p := by
  rw [PrimeSpectrum.closure_range_comap] at hp
  change RingHom.ker f ≤ p.asIdeal at hp
  have hbot : (⊥ : Ideal S).comap f ≤ p.asIdeal := by
    simpa only [RingHom.ker_eq_comap_bot] using hp
  obtain ⟨q, -, hq, hqle⟩ := p.asIdeal.exists_ideal_comap_le_prime (⊥ : Ideal S) hbot
  exact ⟨⟨q, hq⟩, (PrimeSpectrum.le_iff_specializes _ _).mp hqle⟩

end PrimeSpectrum

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- For a morphism between affine schemes, every point in the closure of the image is
a specialization of an actual image point. -/
theorem Scheme.Hom.exists_specializes_of_mem_closure_range_of_isAffine
    (f : X ⟶ Y) [IsAffine X] [IsAffine Y] {y : Y}
    (hy : y ∈ closure (Set.range f)) : ∃ x : X, f x ⤳ y := by
  let g : Spec Γ(X, ⊤) ⟶ Spec Γ(Y, ⊤) := X.isoSpec.inv ≫ f ≫ Y.isoSpec.hom
  have hy' : Y.isoSpec.hom.base y ∈ closure (Set.range g) := by
    have h := image_closure_subset_closure_image Y.isoSpec.hom.continuous
      (Set.mem_image_of_mem Y.isoSpec.hom.base hy)
    simpa only [g, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.image_image, Set.image_univ, Set.range_eq_univ.mpr
        (ConcreteCategory.bijective_of_isIso X.isoSpec.inv.base).2] using h
  obtain ⟨φ, hφ⟩ := Spec.map_surjective g
  rw [← hφ] at hy'
  change (Y.isoSpec.hom.base y : PrimeSpectrum Γ(Y, ⊤)) ∈
    closure (Set.range (PrimeSpectrum.comap φ.hom)) at hy'
  obtain ⟨q, hq⟩ :=
    PrimeSpectrum.exists_specializes_of_mem_closure_range_comap φ.hom hy'
  refine ⟨X.isoSpec.inv.base q, ?_⟩
  have hq' := hq.map Y.isoSpec.inv.continuous
  change Y.isoSpec.inv.base ((Spec.map φ).base q) ⤳
    Y.isoSpec.inv.base (Y.isoSpec.hom.base y) at hq'
  rw [hφ] at hq'
  simpa only [← Scheme.Hom.comp_apply, Category.assoc, Iso.hom_inv_id,
    Category.comp_id, Scheme.Hom.id_base, TopCat.id_app, g] using hq'

/-- If the target of a quasi-compact scheme morphism is affine, every point in the
closure of its image is a specialization of an actual image point. -/
theorem Scheme.Hom.exists_specializes_of_mem_closure_range_of_quasiCompact_of_isAffine
    (f : X ⟶ Y) [QuasiCompact f] [IsAffine Y] {y : Y}
    (hy : y ∈ closure (Set.range f)) : ∃ x : X, f x ⤳ y := by
  let _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let U := X.affineCover.finiteSubcover
  have hrange : Set.range f = ⋃ i, Set.range (U.f i ≫ f) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨i, x, rfl⟩ := U.exists_eq x
      exact Set.mem_iUnion.mpr ⟨i, ⟨x, by simp only [Scheme.Hom.comp_apply]⟩⟩
    · simp only [Set.mem_iUnion, Set.mem_range]
      rintro ⟨i, x, rfl⟩
      exact ⟨U.f i x, by simp only [Scheme.Hom.comp_apply]⟩
  rw [hrange, closure_iUnion_of_finite] at hy
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
  let _ : IsAffine (U.X i) := by
    dsimp only [U, Scheme.OpenCover.finiteSubcover_X]
    infer_instance
  obtain ⟨x, hx⟩ :=
    Scheme.Hom.exists_specializes_of_mem_closure_range_of_isAffine (U.f i ≫ f) hi
  exact ⟨U.f i x, by simpa only [Scheme.Hom.comp_apply] using hx⟩

end AlgebraicGeometry
