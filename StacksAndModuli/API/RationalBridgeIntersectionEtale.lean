module

public import StacksAndModuli.API.FiniteDimensionalReducedEtale
public import StacksAndModuli.API.RationalBridgeIntersectionSupport
public import StacksAndModuli.API.RationalTailBridgeFieldReduction

/-!
# Étaleness reduction for rational-bridge intersections

For a smooth genus-zero subcurve in a proper curve over an algebraically closed
field, its field of global constants is the ground field up to ring equivalence.
Consequently, a reduced scheme-theoretic intersection of degree two is a reduced
two-dimensional algebra over a perfect field and hence is finite étale.

Combining this with the rational-bridge degree calculation and the rank-two finite
étale classification proves the quadratic-field-or-split conclusion under one
explicit remaining geometric hypothesis: reducedness of the scheme-theoretic
intersection.

The ambient nodal hypotheses prove that the intersection is supported at distinct
split nodes; see `RationalBridgeIntersectionSupport`.  They do not yet prove that
the pullback has no nilpotent thickening.  Thus the `IsReduced E.intersection`
assumption below records exactly the missing branch-transversality theorem rather
than hiding it in an étaleness assumption.

## Main results

* `SmoothGenusZeroSubcurveOver.intersection_etale_of_degree_two_of_isReduced`:
  reducedness and degree two imply étaleness after identifying the constants with
  a field.
* `SmoothGenusZeroSubcurveOver.IsRationalBridge.
  intersection_isQuadraticOrSplit_of_prestable_of_isReduced`: the corresponding
  quadratic-or-split classification for an unmarked rational bridge on a prestable
  curve.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Scheme

namespace SmoothGenusZeroSubcurveOver

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
  [C.Over (Spec (CommRingCat.of k))]

/-- A reduced degree-two intersection is étale over any field identified with the
global constants of the smooth genus-zero subcurve.

Properness and integrality identify the global constants with the algebraically
closed ground field, so the chosen target field is perfect.  The degree hypothesis
then supplies finite-dimensionality and reducedness supplies étaleness.

The scheme-level hypothesis `IsReduced E.intersection` is intentionally explicit:
it is precisely the branch-transversality input not supplied by the current nodal
curve API. -/
theorem intersection_etale_of_degree_two_of_isReduced
    (E : SmoothGenusZeroSubcurveOver k C)
    [IsProper (C ↘ Spec (CommRingCat.of k))]
    {K : Type u} [Field K] (e : Γ(E.curve.left, ⊤) ≃+* K)
    [IsReduced E.intersection] (hdegree : E.intersectionDegree = 2) :
    letI : Algebra K Γ(E.intersection, ⊤) :=
      ((E.intersectionGlobalSectionsMap.comp e.symm.toRingHom)).toAlgebra
    Algebra.Etale K Γ(E.intersection, ⊤) := by
  let _ : Algebra K Γ(E.intersection, ⊤) :=
    ((E.intersectionGlobalSectionsMap.comp e.symm.toRingHom)).toAlgebra
  let _ : IsIntegral E.curve.left := E.curve_isIntegral
  let _ : UniversallyClosed (E.curve.left ↘ Spec (CommRingCat.of k)) :=
    E.curve_isProper.toUniversallyClosed
  let ek : k ≃+* K :=
    (RingEquiv.ofBijective (E.curve.left.baseRingHom (CommRingCat.of k))
      (bijective_baseRingHom_of_isAlgClosed k E.curve.left)).trans e
  let _ : PerfectField K := PerfectField.of_ringEquiv ek
  have hfinrank : Module.finrank K Γ(E.intersection, ⊤) = 2 := by
    let _ : Algebra Γ(E.curve.left, ⊤) Γ(E.intersection, ⊤) :=
      E.intersectionGlobalSectionsMap.toAlgebra
    have hfinrank' :
        Module.finrank Γ(E.curve.left, ⊤) Γ(E.intersection, ⊤) = 2 :=
      hdegree
    rw [← hfinrank']
    symm
    apply Algebra.finrank_eq_of_equiv_equiv e (RingEquiv.refl _)
    ext a
    simp [RingHom.algebraMap_toAlgebra]
  let _ : FiniteDimensional K Γ(E.intersection, ⊤) :=
    FiniteDimensional.of_finrank_eq_succ (n := 1) hfinrank
  let _ : _root_.IsReduced Γ(E.intersection, ⊤) :=
    AlgebraicGeometry.IsReduced.component_reduced ⊤
  exact Algebra.Etale.of_finiteDimensional_of_isReduced_of_perfectField

/-- The intersection algebra of an unmarked rational bridge on a prestable curve is
either a separable quadratic field or the split algebra, provided the
scheme-theoretic intersection is reduced.

All ambient hypotheses come from prestability: nodality identifies the supported
points as nodes and projectivity gives properness.  The only additional geometric
hypothesis is the explicitly displayed `IsReduced E.intersection`. -/
theorem IsRationalBridge.intersection_isQuadraticOrSplit_of_prestable_of_isReduced
    {I : Type v} {g : ℕ} (E : SmoothGenusZeroSubcurveOver k C)
    (p : I → C.SectionOver (Spec (CommRingCat.of k)))
    (hpre : IsPrestableMarkedCurveOfGenusOver k g C p)
    (hbridge : E.IsRationalBridge p) (hmarks : E.ContainsNoMarkedPoints p)
    {K : Type u} [Field K] (e : Γ(E.curve.left, ⊤) ≃+* K)
    [IsReduced E.intersection] :
    letI : Algebra K Γ(E.intersection, ⊤) :=
      ((E.intersectionGlobalSectionsMap.comp e.symm.toRingHom)).toAlgebra
    (∃ (L : Type u) (_ : Field L) (_ : Algebra K L)
        (_ : Algebra.IsSeparable K L)
        (_ : Algebra.IsQuadraticExtension K L),
        Nonempty (Γ(E.intersection, ⊤) ≃ₐ[K] L)) ∨
      Nonempty (Γ(E.intersection, ⊤) ≃ₐ[K] K × K) := by
  let _ : IsNodalCurveOver k C := hpre.nodal
  let _ : IsProper (C ↘ Spec (CommRingCat.of k)) := hpre.proper
  let _ : Algebra K Γ(E.intersection, ⊤) :=
    ((E.intersectionGlobalSectionsMap.comp e.symm.toRingHom)).toAlgebra
  have hdegree : E.intersectionDegree = 2 :=
    hbridge.intersectionDegree_eq_two_of_containsNoMarkedPoints hmarks
  have hEtale : Algebra.Etale K Γ(E.intersection, ⊤) :=
    E.intersection_etale_of_degree_two_of_isReduced e hdegree
  exact E.intersection_isQuadraticOrSplit_of_degree_two e hEtale hdegree

end SmoothGenusZeroSubcurveOver

end AlgebraicGeometry.Scheme

end
