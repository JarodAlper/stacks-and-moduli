module

public import StacksAndModuli.API.RelativeFibreRegularSequenceLocusOver

/-!
# Relative regular-sequence loci over an open fibre

If a point `p` is open in the prime spectrum of the base, then its set-theoretic fibre is
open in the source spectrum.  The fixed-fibre regular-sequence theorem can therefore be
promoted from openness inside that fibre to openness in the ambient zero locus of the
sequence.  This gives a genuine ambient, though isolated-base-point, case of the
varying-fibre openness problem.

Main declarations:

* `Matrix.FiniteFreeComplex.fixedFibreZeroLocusHomeomorph_zeroLocusInFibre`;
* `Matrix.FiniteFreeComplex.isOpen_relativeFibreRegularSequenceLocusInZeroLocusOver`;
* `Matrix.FiniteFreeComplex.isOpen_relativeFibreRegularSequenceOnZeroLocus_of_isOpen_singleton`;
* `Matrix.FiniteFreeComplex.isOpen_relativeFibreBuchsbaumEisenbudLocusOver_of_isOpen_singleton`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

namespace Matrix.FiniteFreeComplex

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The part of a sequence's zero locus lying in the set-theoretic fibre over `p`. -/
def zeroLocusInFibre (p : PrimeSpectrum R) (rs : List S) :
    Set (PrimeSpectrum.zeroLocus (Ideal.ofList rs : Set S)) :=
  {q | q.1.comap (algebraMap R S) = p}

/-- Reordering the two subtype conditions identifies the fixed-fibre zero locus with the
part of the ambient zero locus lying over the same base point. -/
noncomputable def fixedFibreZeroLocusHomeomorph_zeroLocusInFibre
    (p : PrimeSpectrum R) (rs : List S) :
    Ideal.Fiber.fixedFibreZeroLocus p rs ≃ₜ zeroLocusInFibre p rs where
  toFun q := ⟨⟨q.1.1, q.2⟩, q.1.2⟩
  invFun q := ⟨⟨q.1.1, q.2⟩, q.1.2⟩
  left_inv q := rfl
  right_inv q := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val

/-- The relative regular-sequence locus in the ambient zero locus, restricted to the fibre
over `p`. -/
def relativeFibreRegularSequenceLocusInZeroLocusOver
    {d : ℕ} (p : PrimeSpectrum R) (f : Fin d → S) :
    Set (PrimeSpectrum.zeroLocus
      (Ideal.ofList (List.ofFn f) : Set S)) :=
  {q | q.1.comap (algebraMap R S) = p ∧
    IsRelativeFibreRegularSequenceAt (R := R) q.1 f}

/-- If `p` is open in the base spectrum, relative regularity of a fixed sequence is open in
the ambient zero locus, after restricting to the fibre over `p`. -/
theorem isOpen_relativeFibreRegularSequenceLocusInZeroLocusOver
    [Algebra.FiniteType R S]
    {d : ℕ} (p : PrimeSpectrum R) (hp : IsOpen ({p} : Set (PrimeSpectrum R)))
    (f : Fin d → S) :
    IsOpen (relativeFibreRegularSequenceLocusInZeroLocusOver
      (R := R) p f) := by
  let Z := PrimeSpectrum.zeroLocus
    (Ideal.ofList (List.ofFn f) : Set S)
  let F : Set Z := zeroLocusInFibre (R := R) p (List.ofFn f)
  let e := fixedFibreZeroLocusHomeomorph_zeroLocusInFibre
    (R := R) p (List.ofFn f)
  let L := relativeFibreRegularSequenceLocusOver (R := R) p f
  have hF : IsOpen F := by
    exact hp.preimage
      ((PrimeSpectrum.continuous_comap (algebraMap R S)).comp
        continuous_subtype_val)
  have hL : IsOpen L :=
    isOpen_relativeFibreRegularSequenceLocusOver p f
  have himage : IsOpen
      ((Subtype.val : F → Z) '' (e '' L)) :=
    hF.isOpenMap_subtype_val _ (e.isOpenMap _ hL)
  have hset :
      relativeFibreRegularSequenceLocusInZeroLocusOver
        (R := R) p f =
        (Subtype.val : F → Z) '' (e '' L) := by
    ext q
    constructor
    · intro hq
      let qF : F := ⟨q, hq.1⟩
      let qL := e.symm qF
      have hqL : qL ∈ L := by
        exact hq.2
      exact ⟨qF, ⟨qL, hqL, e.apply_symm_apply qF⟩, rfl⟩
    · rintro ⟨qF, ⟨qL, hqL, hqFL⟩, rfl⟩
      subst qF
      exact ⟨(e qL).2, hqL⟩
  rw [hset]
  exact himage

/-- If `p` is open in the base spectrum, the relative regular-sequence predicate over `p`
is open in the standard zero locus of a finite family. -/
theorem isOpen_relativeFibreRegularSequenceOnZeroLocus_of_isOpen_singleton
    [Algebra.FiniteType R S]
    {d : ℕ} (p : PrimeSpectrum R) (hp : IsOpen ({p} : Set (PrimeSpectrum R)))
    (f : Fin d → S) :
    IsOpen {q : PrimeSpectrum.zeroLocus (Set.range f) |
      q.1.comap (algebraMap R S) = p ∧
        IsRelativeFibreRegularSequenceAt (R := R) q.1 f} := by
  have hrange : Set.range f = {x | x ∈ List.ofFn f} := by
    ext x
    simp
  have hzero :
      PrimeSpectrum.zeroLocus (Set.range f) =
        PrimeSpectrum.zeroLocus
          (Ideal.ofList (List.ofFn f) : Set S) := by
    rw [hrange]
    exact (PrimeSpectrum.zeroLocus_span (R := S) _).symm
  let e : PrimeSpectrum.zeroLocus (Set.range f) ≃ₜ
      PrimeSpectrum.zeroLocus
        (Ideal.ofList (List.ofFn f) : Set S) :=
    Homeomorph.setCongr hzero
  have hopen :=
    isOpen_relativeFibreRegularSequenceLocusInZeroLocusOver
      (R := R) p hp f
  have hset :
      {q : PrimeSpectrum.zeroLocus (Set.range f) |
        q.1.comap (algebraMap R S) = p ∧
          IsRelativeFibreRegularSequenceAt (R := R) q.1 f} =
        e ⁻¹' relativeFibreRegularSequenceLocusInZeroLocusOver
          (R := R) p f := by
    ext q
    rfl
  rw [hset]
  exact hopen.preimage e.continuous

/-- The part of the relative Buchsbaum--Eisenbud locus lying in the set-theoretic fibre
over `p`. -/
def relativeFibreBuchsbaumEisenbudLocusOver
    (p : PrimeSpectrum R) (C : FiniteFreeComplex S)
    {N : ℕ} (r : C.ExpectedRanks N) : Set (PrimeSpectrum S) :=
  (PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p}) ∩
    relativeFibreBuchsbaumEisenbudLocus (R := R) C r

/-- If `p` is open in the base spectrum, the part of the relative
Buchsbaum--Eisenbud locus over `p` is open in the source spectrum. -/
theorem isOpen_relativeFibreBuchsbaumEisenbudLocusOver_of_isOpen_singleton
    [Algebra.FiniteType R S]
    (p : PrimeSpectrum R) (hp : IsOpen ({p} : Set (PrimeSpectrum R)))
    (C : FiniteFreeComplex S) {N : ℕ} (r : C.ExpectedRanks N) :
    IsOpen (relativeFibreBuchsbaumEisenbudLocusOver
      (R := R) p C r) := by
  let F : Set (PrimeSpectrum S) :=
    PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p}
  let L : Set (PrimeSpectrum S) :=
    ⋂ i ∈ Finset.range N,
      Matrix.determinantalGradeLocus
        (C.differential i) (r.rank i) (i + 1)
        (fun q f ↦ q ∈ F ∧
          IsRelativeFibreRegularSequenceAt (R := R) q f)
  have hF : IsOpen F :=
    hp.preimage (PrimeSpectrum.continuous_comap (algebraMap R S))
  have hdet (i : ℕ) (hi : i < N) :
      IsOpen (Matrix.determinantalGradeLocus
        (C.differential i) (r.rank i) (i + 1)
        (fun q f ↦ q ∈ F ∧
          IsRelativeFibreRegularSequenceAt (R := R) q f)) := by
    apply Matrix.isOpen_determinantalGradeLocus_of_isOpen_subtype
    intro f hf
    simpa only [F, Set.mem_preimage, Set.mem_singleton_iff] using
      (isOpen_relativeFibreRegularSequenceOnZeroLocus_of_isOpen_singleton
        (R := R) p hp f)
  have hL : IsOpen L := by
    apply isOpen_biInter_finset
    intro i hi
    exact hdet i (Finset.mem_range.mp hi)
  have hpoint (q : PrimeSpectrum S) (hqF : q ∈ F) (i : ℕ) :
      q ∈ Matrix.determinantalGradeLocus
          (C.differential i) (r.rank i) (i + 1)
          (fun q f ↦ IsRelativeFibreRegularSequenceAt (R := R) q f) ↔
        q ∈ Matrix.determinantalGradeLocus
          (C.differential i) (r.rank i) (i + 1)
          (fun q f ↦ q ∈ F ∧
            IsRelativeFibreRegularSequenceAt (R := R) q f) := by
    constructor
    · rintro (hunit | ⟨f, hf, hreg⟩)
      · exact Or.inl hunit
      · exact Or.inr ⟨f, hf, hqF, hreg⟩
    · rintro (hunit | ⟨f, hf, _, hreg⟩)
      · exact Or.inl hunit
      · exact Or.inr ⟨f, hf, hreg⟩
  have hset :
      relativeFibreBuchsbaumEisenbudLocusOver
          (R := R) p C r = F ∩ L := by
    ext q
    simp only [relativeFibreBuchsbaumEisenbudLocusOver,
      relativeFibreBuchsbaumEisenbudLocus, L, F,
      Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      Set.mem_iInter]
    constructor
    · rintro ⟨hqF, hq⟩
      refine ⟨hqF, ?_⟩
      intro i hi
      exact (hpoint q hqF i).mp (hq i hi)
    · rintro ⟨hqF, hq⟩
      refine ⟨hqF, ?_⟩
      intro i hi
      exact (hpoint q hqF i).mpr (hq i hi)
  rw [hset]
  exact hF.inter hL

end Matrix.FiniteFreeComplex

end

end
