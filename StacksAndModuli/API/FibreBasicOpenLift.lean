module

public import StacksAndModuli.API.PrimeSpectrumBasicOpenNeighborhood
public import StacksAndModuli.API.RelativeFibreExactnessInterface

/-!
# Lifting principal opens from residue fibres

Every element of a residue fibre `κ(p) ⊗[R] S` becomes the image of an element of `S`
after multiplication by a nonzero residue-field scalar.  Since that scalar is a unit, the two
elements define the same principal open in the spectrum of the fibre.  At the fibre prime
induced by a prime `q` of `S`, membership in this principal open also shows that the lifted
element does not belong to `q`.

Main declarations:

* `Ideal.Fiber.exists_basicOpen_eq_one_tmul`;
* `PrimeSpectrum.relativeFibrePrime_exists_notMem_basicOpen_eq_one_tmul`;
* `PrimeSpectrum.relativeFibrePrime_exists_notMem_basicOpen_topologicalKrullDim_eq_atPoint`.
-/

@[expose] public section

noncomputable section

universe u v

namespace Ideal.Fiber

/-- Every principal open in a residue fibre is defined by an element lifted from the original
algebra. -/
theorem exists_basicOpen_eq_one_tmul
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (x : p.Fiber S) :
    ∃ s : S, PrimeSpectrum.basicOpen (1 ⊗ₜ[R] s) = PrimeSpectrum.basicOpen x := by
  obtain ⟨r, hrp, s, hrs⟩ := Ideal.Fiber.exists_smul_eq_one_tmul p x
  refine ⟨s, ?_⟩
  rw [← hrs, Algebra.smul_def]
  have hr_ne : algebraMap R p.ResidueField r ≠ 0 := by
    intro hr
    exact hrp (Ideal.algebraMap_residueField_eq_zero.mp hr)
  have hr_unit : IsUnit (algebraMap R (p.Fiber S) r) := by
    rw [IsScalarTower.algebraMap_apply R p.ResidueField (p.Fiber S)]
    exact (Ne.isUnit hr_ne).map (algebraMap p.ResidueField (p.Fiber S))
  exact PrimeSpectrum.basicOpen_mul_eq_right_of_isUnit _ _ hr_unit

end Ideal.Fiber

namespace PrimeSpectrum

/-- If the fibre prime induced by `q` belongs to a principal open, that open can be defined by
an element lifted from `S` which does not belong to `q`. -/
theorem relativeFibrePrime_exists_notMem_basicOpen_eq_one_tmul
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S)
    (x : (q.comap (algebraMap R S)).asIdeal.Fiber S)
    (hx : relativeFibrePrime (R := R) q ∈ basicOpen x) :
    ∃ s : S, s ∉ q.asIdeal ∧ basicOpen (1 ⊗ₜ[R] s) = basicOpen x := by
  obtain ⟨s, hs⟩ :=
    Ideal.Fiber.exists_basicOpen_eq_one_tmul
      (q.comap (algebraMap R S)).asIdeal x
  have hmem : relativeFibrePrime (R := R) q ∈ basicOpen (1 ⊗ₜ[R] s) := by
    rw [hs]
    exact hx
  have htensor : 1 ⊗ₜ[R] s ∉ (relativeFibrePrime (R := R) q).asIdeal :=
    (PrimeSpectrum.mem_basicOpen _ _).mp hmem
  have hs_notMem : s ∉ q.asIdeal := by
    intro hs_mem
    apply htensor
    rw [← Algebra.TensorProduct.includeRight_apply]
    change s ∈ (relativeFibrePrime (R := R) q).asIdeal.comap
      Algebra.TensorProduct.includeRight.toRingHom
    rw [relativeFibrePrime_comap_includeRight (R := R) q]
    exact hs_mem
  exact ⟨s, hs_notMem, hs⟩

/-- Pointwise topological Krull dimension at an induced fibre prime is attained on a
principal open defined by an element lifted from the original algebra and avoiding the
original prime. -/
theorem relativeFibrePrime_exists_notMem_basicOpen_topologicalKrullDim_eq_atPoint
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) :
    ∃ s : S, s ∉ q.asIdeal ∧
      topologicalKrullDim
          (basicOpen
            (1 ⊗ₜ[R] s : (q.comap (algebraMap R S)).asIdeal.Fiber S)) =
        topologicalKrullDimAtPoint
          (PrimeSpectrum ((q.comap (algebraMap R S)).asIdeal.Fiber S))
          (relativeFibrePrime (R := R) q) := by
  obtain ⟨x, hqx, hx⟩ :=
    PrimeSpectrum.exists_basicOpen_topologicalKrullDim_eq_atPoint
      (relativeFibrePrime (R := R) q)
  obtain ⟨s, hs, hsOpen⟩ :=
    relativeFibrePrime_exists_notMem_basicOpen_eq_one_tmul q x hqx
  refine ⟨s, hs, ?_⟩
  exact
    (congrArg
      (fun U : TopologicalSpace.Opens
          (PrimeSpectrum ((q.comap (algebraMap R S)).asIdeal.Fiber S)) ↦
        topologicalKrullDim U)
      hsOpen).trans hx

end PrimeSpectrum

end

end
