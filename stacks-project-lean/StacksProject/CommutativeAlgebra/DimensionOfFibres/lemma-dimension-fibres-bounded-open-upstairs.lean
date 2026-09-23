module

public import StacksAndModuli.API.FibreAwayBaseChange
public import StacksAndModuli.API.FibreBasicOpenLift
public import StacksProject.CommutativeAlgebra.DimensionOfFibres.«lemma-dimension-quasi-finite-over-polynomial-algebra»
public import StacksProject.CommutativeAlgebra.DimensionOfFibres.«lemma-quasi-finite-over-polynomial-algebra»

/-!
# Upper semicontinuity of fibre dimension at a point

Stacks Project tag **00QH**, label `lemma-dimension-fibres-bounded-open-upstairs`, in
`algebra.tex`, §`00QC` (Dimension of fibres).

The proof follows the Stacks Project reduction.  Tag 00QE supplies a principal target
neighbourhood quasi-finite over relative affine `n`-space.  On every residue fibre this
map is the base change of the original quasi-finite map, and tag 00QG bounds the Krull
dimension by `n`.  Pointwise dimension is bounded by the dimension of the corresponding
principal open in that fibre.

Main declarations:

* `Algebra.QuasiFinite.ringKrullDim_fibre_le_of_mvPolynomial`;
* `Algebra.exists_notMem_forall_relativeKrullDimAt_le_of_eq_nat`;
* `Algebra.exists_open_forall_relativeKrullDimAt_le_of_eq_nat`.
-/

@[expose] public section

noncomputable section

set_option linter.style.haveILetI false

universe u v

open TensorProduct

namespace Algebra.QuasiFinite

/-- Every coefficient residue fibre of a quasi-finite map from a polynomial algebra in
`n` variables has Krull dimension at most `n`. -/
theorem ringKrullDim_fibre_le_of_mvPolynomial
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (n : ℕ)
    (f : MvPolynomial (Fin n) R →ₐ[R] S) (hf : f.toRingHom.QuasiFinite)
    (p : Ideal R) [p.IsPrime] :
    ringKrullDim (p.Fiber S) ≤ (n : WithBot ℕ∞) := by
  let A := MvPolynomial (Fin n) R
  let K := p.ResidueField
  let B := MvPolynomial (Fin n) K
  let T := p.Fiber S
  letI : Algebra A S := f.toAlgebra
  letI : IsScalarTower R A S :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  haveI hqfAS : Algebra.QuasiFinite A S := by
    rw [← RingHom.quasiFinite_algebraMap]
    simpa only [RingHom.algebraMap_toAlgebra] using hf
  letI : Algebra A B := MvPolynomial.algebraMvPolynomial
  haveI : Algebra.IsPushout R K A B := inferInstance
  let U := B ⊗[A] S
  haveI hqfBU : Algebra.QuasiFinite B U := inferInstance
  let e : U ≃ₐ[K] T :=
    Algebra.IsPushout.cancelBaseChangeAlg R K A B S
  let φ : B →ₐ[K] T :=
    e.toAlgHom.comp (IsScalarTower.toAlgHom K B U)
  letI : Algebra B T := φ.toAlgebra
  letI : IsScalarTower K B T :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let eB : U ≃ₐ[B] T :=
    { __ := e.toRingEquiv
      commutes' := fun x ↦ rfl }
  haveI hqfBT : Algebra.QuasiFinite B T :=
    (Algebra.QuasiFinite.iff_of_algEquiv eB).mp hqfBU
  letI : Algebra.FiniteType K T := inferInstance
  exact ringKrullDim_le_nat_of_mvPolynomial K T n

end Algebra.QuasiFinite

namespace Algebra

/-- Principal-open form of upper semicontinuity at a point of finite relative dimension. -/
theorem exists_notMem_forall_relativeKrullDimAt_le_of_eq_nat
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (q : PrimeSpectrum S) (n : ℕ)
    (hdim : Algebra.relativeKrullDimAt R S q = (n : WithBot ℕ∞)) :
    ∃ g : S, g ∉ q.asIdeal ∧
      ∀ q' : PrimeSpectrum S, g ∉ q'.asIdeal →
        Algebra.relativeKrullDimAt R S q' ≤ (n : WithBot ℕ∞) := by
  obtain ⟨g, hgq, f, hf⟩ :=
    exists_notMem_quasiFinite_away_mvPolynomial_of_relativeKrullDimAt_eq
      R S q n hdim
  refine ⟨g, hgq, fun q' hgq' ↦ ?_⟩
  let p : Ideal R := (q'.comap (algebraMap R S)).asIdeal
  let T := p.Fiber S
  let qF : PrimeSpectrum T := PrimeSpectrum.relativeFibrePrime (R := R) q'
  have hqF : qF ∈ PrimeSpectrum.basicOpen (1 ⊗ₜ[R] g : T) := by
    change 1 ⊗ₜ[R] g ∉ qF.asIdeal
    intro hmem
    apply hgq'
    rw [← PrimeSpectrum.relativeFibrePrime_comap_includeRight (R := R) q']
    exact hmem
  change topologicalKrullDimAtPoint (PrimeSpectrum T) qF ≤ (n : WithBot ℕ∞)
  calc
    topologicalKrullDimAtPoint (PrimeSpectrum T) qF ≤
        topologicalKrullDim
          (PrimeSpectrum.basicOpen (1 ⊗ₜ[R] g : T)) :=
      topologicalKrullDimAtPoint_le _ hqF
    _ = ringKrullDim (p.Fiber (Localization.Away g)) :=
      (Ideal.Fiber.ringKrullDim_away_eq_topologicalKrullDim_basicOpen p g).symm
    _ ≤ (n : WithBot ℕ∞) :=
      Algebra.QuasiFinite.ringKrullDim_fibre_le_of_mvPolynomial n f hf p

/-- **Lemma 10.125.6** (`00QH`,
`lemma-dimension-fibres-bounded-open-upstairs`): if a finite-type algebra has relative
dimension `n` at a prime `q`, then `q` has an open neighbourhood on which every relative
dimension is at most `n`. -/
@[stacks 00QH]
theorem exists_open_forall_relativeKrullDimAt_le_of_eq_nat
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (q : PrimeSpectrum S) (n : ℕ)
    (hdim : Algebra.relativeKrullDimAt R S q = (n : WithBot ℕ∞)) :
    ∃ V : TopologicalSpace.Opens (PrimeSpectrum S), q ∈ V ∧
      ∀ q' : PrimeSpectrum S, q' ∈ V →
        Algebra.relativeKrullDimAt R S q' ≤ (n : WithBot ℕ∞) := by
  obtain ⟨g, hgq, hdim⟩ :=
    exists_notMem_forall_relativeKrullDimAt_le_of_eq_nat R S q n hdim
  exact ⟨PrimeSpectrum.basicOpen g, hgq, hdim⟩

end Algebra

end

end
