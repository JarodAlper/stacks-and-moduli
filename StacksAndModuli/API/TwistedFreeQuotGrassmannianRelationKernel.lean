module

public import StacksAndModuli.API.SchemeModulesFiniteLocallyFreeKernel
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianUniversalFlatteningLocus

/-!
# Relation kernels for twisted-free Grassmannian reconstruction

The finite-free quotient underlying a point of the free Grassmannian has finite locally
free kernel.  In particular, this applies to the quotient underlying the universal point.
These are the coefficient sheaves whose pullbacks and low twists occur in the two-term
presentation of the reconstructed quotient.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {n r m q e : ℕ}
  {σ : ULift.{u} (Fin m) ≃
    ULift.{u} (Fin r) × Fin ((n + e).choose n)}

/-- The relation kernel of the monomial quotient associated to a Grassmannian point is
finite locally free. -/
lemma grassmannianPointMonomialQuotientMap_kernel_isFiniteLocallyFree
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶
      Modules.grassmannianFunctorOver S q m) :
    Modules.IsFiniteLocallyFree
      (kernel (grassmannianPointMonomialQuotientMap
        (n := n) (r := r) (q := q) (e := e) (σ := σ) T g)) := by
  let x := grassmannianPointFreeQuotient (q := q) T g
  letI : x.Q.IsQuasicoherent := x.isQuasicoherent
  let f := SheafOfModules.freeMap (R := T.left.ringCatSheaf) σ.symm
  letI : IsIso f := Modules.freeMap_isIso_of_equiv σ.symm
  have hSource : Modules.IsFiniteLocallyFree
      (SheafOfModules.free (R := T.left.ringCatSheaf)
        (ULift.{u} (Fin r) × Fin ((n + e).choose n))) :=
    (Modules.free_isFiniteLocallyFree T.left m).of_iso (asIso f).symm
  have hTarget : Modules.IsFiniteLocallyFree x.Q :=
    x.isProjectiveOfRank.isFiniteLocallyFree
  letI : Epi x.π := x.epi
  let p := grassmannianPointMonomialQuotientMap
    (n := n) (r := r) (q := q) (e := e) (σ := σ) T g
  letI : Epi p := by
    dsimp only [p, grassmannianPointMonomialQuotientMap, x, f]
    infer_instance
  exact Modules.kernel_isFiniteLocallyFree_of_epi_of_isFiniteLocallyFree
    hSource hTarget p

/-- The relation kernel used by the universal twisted-free Grassmannian reconstruction is
finite locally free. -/
lemma freeGrassmannianUniversalMonomialQuotientMap_kernel_isFiniteLocallyFree
    (S : Scheme.{u}) (n r m q e : ℕ)
    (σ : ULift.{u} (Fin m) ≃
      ULift.{u} (Fin r) × Fin ((n + e).choose n)) :
    Modules.IsFiniteLocallyFree
      (kernel (grassmannianPointMonomialQuotientMap
        (n := n) (r := r) (q := q) (e := e) (σ := σ)
        (grassmannianOverRepresentation S q m)
        (freeGrassmannianUniversalPoint S q m))) :=
  grassmannianPointMonomialQuotientMap_kernel_isFiniteLocallyFree
    (n := n) (r := r) (q := q) (e := e) (σ := σ)
    (grassmannianOverRepresentation S q m)
    (freeGrassmannianUniversalPoint S q m)

end AlgebraicGeometry.Scheme

end

end
