module

public import StacksAndModuli.API.FiniteFreeComplexExactExpectedRanks
public import StacksAndModuli.API.LinearMapHomologySupport

/-!
# Homology of matrix finite free complexes

This file specializes the concrete linear-map homology module to the differentials of a
matrix finite free complex.  It exposes exactness through a bound as the vanishing of the
individual homology modules and identifies their localized support pointwise.

Main declarations:

* `Matrix.FiniteFreeComplex.homology`;
* `Matrix.FiniteFreeComplex.isExactAt_iff_subsingleton_homology`;
* `Matrix.FiniteFreeComplex.isExactInPositiveDegreesUpTo_iff_subsingleton_homology`;
* `Matrix.FiniteFreeComplex.notMem_support_homology_iff_exact_localizedMap`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

namespace Matrix.FiniteFreeComplex

variable {R : Type u} [CommRing R]

/-- Consecutive linear maps of a matrix finite free complex have zero composite. -/
theorem differential_comp (C : FiniteFreeComplex R) (i : ℕ) :
    (Matrix.toLin' (C.differential i)).comp
      (Matrix.toLin' (C.differential (i + 1))) = 0 := by
  rw [← Matrix.toLin'_mul, C.differential_sq]
  simp

/-- Homology at the term in degree `i + 1` of a matrix finite free complex. -/
def homology (C : FiniteFreeComplex R) (i : ℕ) : Type u :=
  LinearMap.Homology
    (Matrix.toLin' (C.differential (i + 1)))
    (Matrix.toLin' (C.differential i))
    (C.differential_comp i)

instance (C : FiniteFreeComplex R) (i : ℕ) : AddCommGroup (C.homology i) := by
  change AddCommGroup (LinearMap.Homology
    (Matrix.toLin' (C.differential (i + 1)))
    (Matrix.toLin' (C.differential i)) (C.differential_comp i))
  infer_instance

instance (C : FiniteFreeComplex R) (i : ℕ) : Module R (C.homology i) := by
  change Module R (LinearMap.Homology
    (Matrix.toLin' (C.differential (i + 1)))
    (Matrix.toLin' (C.differential i)) (C.differential_comp i))
  infer_instance

instance [IsNoetherianRing R] (C : FiniteFreeComplex R) (i : ℕ) :
    Module.Finite R (C.homology i) := by
  change Module.Finite R (LinearMap.Homology
    (Matrix.toLin' (C.differential (i + 1)))
    (Matrix.toLin' (C.differential i)) (C.differential_comp i))
  infer_instance

/-- Exactness at one positive degree is equivalent to vanishing of its homology module. -/
theorem isExactAt_iff_subsingleton_homology
    (C : FiniteFreeComplex R) (i : ℕ) :
    Function.Exact
        (Matrix.toLin' (C.differential (i + 1)))
        (Matrix.toLin' (C.differential i)) ↔
      Subsingleton (C.homology i) :=
  LinearMap.exact_iff_subsingleton_homology
    (Matrix.toLin' (C.differential (i + 1)))
    (Matrix.toLin' (C.differential i))
    (C.differential_comp i)

/-- Exactness through a bound is equivalent to vanishing of every displayed homology
module. -/
theorem isExactInPositiveDegreesUpTo_iff_subsingleton_homology
    (C : FiniteFreeComplex R) (N : ℕ) :
    C.IsExactInPositiveDegreesUpTo N ↔
      ∀ i : ℕ, i < N → Subsingleton (C.homology i) := by
  constructor
  · intro h i hi
    exact (C.isExactAt_iff_subsingleton_homology i).mp (h i hi)
  · intro h i hi
    exact (C.isExactAt_iff_subsingleton_homology i).mpr (h i hi)

/-- A prime is outside the support of homology at degree `i + 1` exactly when the two
localized adjacent differentials are exact there. -/
theorem notMem_support_homology_iff_exact_localizedMap
    (C : FiniteFreeComplex R) (i : ℕ) (p : PrimeSpectrum R) :
    p ∉ Module.support R (C.homology i) ↔
      Function.Exact
        (LocalizedModule.map p.asIdeal.primeCompl
          (Matrix.toLin' (C.differential (i + 1))))
        (LocalizedModule.map p.asIdeal.primeCompl
          (Matrix.toLin' (C.differential i))) :=
  by
    change p ∉ Module.support R (LinearMap.Homology
        (Matrix.toLin' (C.differential (i + 1)))
        (Matrix.toLin' (C.differential i)) (C.differential_comp i)) ↔ _
    exact LinearMap.notMem_support_homology_iff_exact_localizedMap
      (Matrix.toLin' (C.differential (i + 1)))
      (Matrix.toLin' (C.differential i))
      (C.differential_comp i) p

end Matrix.FiniteFreeComplex

end

end
