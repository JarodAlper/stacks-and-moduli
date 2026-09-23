module

public import Mathlib.RingTheory.Etale.Field

/-!
# Reduced finite-dimensional algebras over perfect fields

A finite-dimensional commutative algebra over a field is Artinian.  If it is also
reduced, the Artinian product decomposition identifies it with a finite product of
fields.  Over a perfect base field those factors are separable, so the algebra is
finite étale.

## Main result

* `Algebra.Etale.of_finiteDimensional_of_isReduced_of_perfectField`: a reduced
  finite-dimensional algebra over a perfect field is étale.
-/

@[expose] public section

universe u v

namespace Algebra.Etale

variable {K : Type u} {A : Type v} [Field K] [CommRing A] [Algebra K A]

/-- A reduced finite-dimensional commutative algebra over a perfect field is étale.

The Artinian product decomposition writes the algebra as the product of its residue
fields at maximal ideals.  These fields are finite over the perfect base field and
hence separable. -/
theorem of_finiteDimensional_of_isReduced_of_perfectField
    [PerfectField K] [FiniteDimensional K A] [IsReduced A] :
    Algebra.Etale K A := by
  classical
  let _ : IsArtinianRing A := isArtinian_of_tower K inferInstance
  let L (m : MaximalSpectrum A) := A ⧸ m.asIdeal
  let _ (m : MaximalSpectrum A) : Field (L m) :=
    Ideal.Quotient.field m.asIdeal
  let _ (m : MaximalSpectrum A) : Algebra K (L m) := inferInstance
  apply (Algebra.Etale.iff_exists_algEquiv_prod (K := K) (A := A)).mpr
  refine ⟨MaximalSpectrum A, inferInstance, L, (fun _ ↦ inferInstance),
    (fun _ ↦ inferInstance),
    (IsArtinianRing.equivPi A).restrictScalars K, fun m ↦ ⟨?_, ?_⟩⟩
  · exact Module.Finite.of_surjective
      (Ideal.Quotient.mkₐ K m.asIdeal).toLinearMap
      Ideal.Quotient.mk_surjective
  · infer_instance

end Algebra.Etale

end
