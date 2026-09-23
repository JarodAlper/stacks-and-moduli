module

public import StacksAndModuli.API.TwistedFreeQuotGrassmannianCanonicalPackage
public import StacksAndModuli.API.PolynomialHilbertNatValue
public import StacksAndModuli.API.RelativeVeryAmpleEmpty
public import StacksAndModuli.API.TwistedFreeMonomialIndexEquiv

/-!
# Eventual determinant very ampleness for twisted-free Quot functors

The fixed-degree canonical Grassmannian package already identifies the pullback of the
Plucker line bundle with the determinant of the corresponding twisted pushforward.  This
file packages the quantifier change needed in the Quot-scheme application: canonical
packages in every sufficiently large natural degree give relative very ampleness of the
determinant in every such degree.

The remaining geometric work is concentrated in
`HasEventualTwistedFreeQuotGrassmannianCanonicalPackages`; this interface deliberately
allows the monomial rank, the twist difference, and the chosen reindexing equivalence to
depend on the degree.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Above a numerical bound, subtracting the fixed ambient twist from a natural degree is
again a natural number. -/
theorem exists_bound_twistedFree_twistDifference (l : ℤ) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∃ e : ℕ, (d : ℤ) - l = (e : ℤ) := by
  refine ⟨l.natAbs, fun d hd ↦ ?_⟩
  have hd' : (l.natAbs : ℤ) ≤ (d : ℤ) := by
    exact_mod_cast hd
  have hld : l ≤ (d : ℤ) := le_trans Int.le_natAbs hd'
  refine ⟨((d : ℤ) - l).toNat, ?_⟩
  exact (Int.toNat_of_nonneg (sub_nonneg.mpr hld)).symm

/-- Eventual availability of the complete canonical Quot-to-Grassmannian package.  The
rank is the natural value of the fixed Hilbert polynomial; all auxiliary presentation
choices may vary with the twist degree. -/
def HasEventualTwistedFreeQuotGrassmannianCanonicalPackages
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ) : Prop :=
  ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
    ∃ e : ℕ, ∃ he : (d : ℤ) - l = (e : ℤ), ∃ m : ℕ,
      ∃ σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n),
        Nonempty (TwistedFreeQuotGrassmannianCanonicalPackage
          n S l r P d e he m (P.hilbertNatValue d) σ)

/-- An eventual family of canonical packages supplies the free-Grassmannian immersion
needed for representability; one degree at the stated bound is enough. -/
theorem HasEventualTwistedFreeQuotGrassmannianCanonicalPackages.w6
    {n : ℕ} {S : Scheme.{u}} {l : ℤ} {r : ℕ} {P : Polynomial ℚ}
    (H : HasEventualTwistedFreeQuotGrassmannianCanonicalPackages n S l r P) :
    TwistedFreeQuotHasFreeGrassmannianImmersion n S l r P := by
  obtain ⟨D, hD⟩ := H
  obtain ⟨e, he, m, σ, ⟨C⟩⟩ := hD D le_rfl
  exact C.w6

/-- Eventual canonical Grassmannian packages make the determinant of the normalized
universal twisted pushforward relatively very ample in every sufficiently large natural
degree. -/
theorem exists_eventually_isRelativelyVeryAmple_exteriorPower_twistedFreeUniversalPushforward
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (H : HasEventualTwistedFreeQuotGrassmannianCanonicalPackages n S l r P)
    (Q : Over S)
    (h : (quotFunctorP
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l)) P).RepresentableBy Q) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      IsRelativelyVeryAmple Q.hom
        (Modules.exteriorPower
          (twistedFreeQuotientTwistPushforward n S l r
            (h.homEquiv (CategoryStruct.id Q)).1.out d)
          (P.hilbertNatValue d)) := by
  obtain ⟨D, hD⟩ := H
  refine ⟨D, fun d hd ↦ ?_⟩
  obtain ⟨e, he, m, σ, ⟨C⟩⟩ := hD d hd
  exact C.determinant_isRelativelyVeryAmple h

/-- Integer-indexed form of eventual determinant very ampleness.  This is the exact
quantifier shape used for twists `d ≫ 0`: a natural rank `N` is accepted whenever its
rational cast is the value `P(d)`. -/
theorem exists_eventually_isRelativelyVeryAmple_exteriorPower_universalQuot_int
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (H : HasEventualTwistedFreeQuotGrassmannianCanonicalPackages n S l r P)
    (Q : Over S)
    (h : (quotFunctorP
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l)) P).RepresentableBy Q) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ N : ℕ, (N : ℚ) = P.eval (d : ℚ) →
      IsRelativelyVeryAmple Q.hom
        (Modules.exteriorPower
          ((Modules.pushforward (projectiveSpaceOverπ n Q.left)).obj
            (projectiveSpaceOverTwistModule
              (quotDataOnProjectiveSpace
                (Modules.QuotientPullbackData.twistedFreeAmbient
                  (n := n) (r := r) (l := l))
                (h.homEquiv (CategoryStruct.id Q)).1.out) d)) N) := by
  obtain ⟨D, hD⟩ :=
    exists_eventually_isRelativelyVeryAmple_exteriorPower_twistedFreeUniversalPushforward
      n S l r P H Q h
  refine ⟨(D : ℤ), fun d hd N hN ↦ ?_⟩
  have hd0 : 0 ≤ d := le_trans (Int.natCast_nonneg D) hd
  have hdn : ((d.toNat : ℕ) : ℤ) = d := Int.toNat_of_nonneg hd0
  have hDdn : D ≤ d.toNat := by
    exact_mod_cast (show (D : ℤ) ≤ (d.toNat : ℤ) by simpa [hdn] using hd)
  have hv := hD d.toNat hDdn
  have hq : P.hilbertNatValue d.toNat = N := by
    apply Polynomial.hilbertNatValue_eq
    rw [show ((d.toNat : ℕ) : ℚ) = ((d.toNat : ℤ) : ℚ) by push_cast; ring, hdn]
    exact hN
  rw [hq] at hv
  simpa [twistedFreeQuotientTwistPushforward, twistedFreeQuotientSheaf, hdn] using hv

/-- Empty Quot functors need no numerical Grassmannian package: every sheaf on their empty
representative is relatively very ample.  Thus it is enough to construct eventual canonical
packages under the assumption that the chosen representative has a point.  This is the
correct interface for arbitrary rational polynomials, whose fixed-polynomial Quot functor may
be empty when the requested Hilbert function is inadmissible. -/
theorem
    exists_eventually_isRelativelyVeryAmple_exteriorPower_universalQuot_int_of_nonempty
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (Q : Over S)
    (h : (quotFunctorP
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l)) P).RepresentableBy Q)
    (H : Nonempty Q.left →
      HasEventualTwistedFreeQuotGrassmannianCanonicalPackages n S l r P) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ N : ℕ, (N : ℚ) = P.eval (d : ℚ) →
      IsRelativelyVeryAmple Q.hom
        (Modules.exteriorPower
          ((Modules.pushforward (projectiveSpaceOverπ n Q.left)).obj
            (projectiveSpaceOverTwistModule
              (quotDataOnProjectiveSpace
                (Modules.QuotientPullbackData.twistedFreeAmbient
                  (n := n) (r := r) (l := l))
                (h.homEquiv (CategoryStruct.id Q)).1.out) d)) N) := by
  by_cases hQ : Nonempty Q.left
  · exact exists_eventually_isRelativelyVeryAmple_exteriorPower_universalQuot_int
      n S l r P (H hQ) Q h
  · letI : IsEmpty Q.left := not_nonempty_iff.mp hQ
    exact ⟨0, fun d _ N _ ↦ isRelativelyVeryAmple_of_isEmpty Q.hom _⟩

end AlgebraicGeometry.Scheme

end

end
