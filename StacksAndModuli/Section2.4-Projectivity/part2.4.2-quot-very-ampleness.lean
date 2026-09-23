module

public import StacksAndModuli.«Section2.4-Projectivity».«part2.4.1-valuative-criteria»
public import StacksAndModuli.API.ProjectiveSpaceZeroDeterminantVeryAmple

/-!
# Very ampleness of the universal Quot determinant

This module corresponds to the end of §2.4 (Projectivity of Hilb and Quot) of Chapter 2
of *Stacks and Moduli*, section label
`sec:representability-of-hilb-quot`.

It proves Corollary 2.4.6. In relative dimension zero the universal Quot determinant is
the Plücker line bundle under the Quot--Grassmannian isomorphism. In positive relative
dimension the proof uses the eventual canonical Quot-to-Grassmannian immersion package.

Main result:
- `AlgebraicGeometry.Scheme.exists_isRelativelyVeryAmple_det_pushforward_universalQuot`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section CorQuotVeryAmple

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Limits

universe u

/-- The universal quotient on `ℙ^n_Q` attached to a scheme `Q` representing `Quot^P`: the
family classified by the identity map, transported to `ℙ^n_Q`. -/
noncomputable def AlgebraicGeometry.Scheme.universalQuot {n : ℕ} {S : Scheme.{u}}
    (F : (Scheme.projectiveSpaceOver n S).Modules) (P : Polynomial ℚ) {Q : Over S}
    (h : (Scheme.quotFunctorP F P).RepresentableBy Q) :
    (Scheme.projectiveSpaceOver n Q.left).Modules :=
  Scheme.quotDataOnProjectiveSpace F (h.homEquiv (𝟙 Q)).1.out

/-- **Corollary 2.4.6** (`cor:quot-very-ample`): for `d ≫ 0`, the line bundle
`det(p_{2,*}(𝒬_univ(d)))` on `Quot^P(F/ℙ^n_S)` is relatively very ample over `S`. -/
theorem AlgebraicGeometry.Scheme.exists_isRelativelyVeryAmple_det_pushforward_universalQuot
    (n : ℕ) (S : Scheme.{u}) [IsLocallyNoetherian S] (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (Q : Over S)
    (h : (Scheme.quotFunctorP
      (Scheme.projectiveSpaceOverTwistedFree n S l r) P).RepresentableBy Q) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ N : ℕ, (N : ℚ) = P.eval (d : ℚ) →
      Scheme.IsRelativelyVeryAmple Q.hom
        (Scheme.Modules.exteriorPower
          ((Scheme.Modules.pushforward (Scheme.projectiveSpaceOverπ n Q.left)).obj
            (Scheme.projectiveSpaceOverTwistModule
              (Scheme.universalQuot _ P h) d)) N) := by
  cases n with
  | zero =>
      simpa only [Scheme.universalQuot, Scheme.projectiveSpaceOverTwistedFree,
        Scheme.Modules.QuotientPullbackData.twistedFreeAmbient] using
          Scheme.exists_eventually_isRelativelyVeryAmple_universalQuot_int_zero
            S l r P Q h
  | succ n =>
      let H : Nonempty Q.left →
          Scheme.HasEventualTwistedFreeQuotGrassmannianImmersionPackages
            (n + 1) S l r P := by
        intro hQ
        exact
          Scheme.hasEventualTwistedFreeQuotGrassmannianImmersionPackages_of_isLocallyNoetherian
            (n + 1) (Nat.zero_lt_succ n) S l r P Q hQ (h.homEquiv (𝟙 Q))
      let h' : (Scheme.quotFunctorP
          (Scheme.Modules.QuotientPullbackData.twistedFreeAmbient
            (n := n + 1) (r := r) (l := l)) P).RepresentableBy Q := h
      simpa only [h', Scheme.universalQuot, Scheme.projectiveSpaceOverTwistedFree,
        Scheme.Modules.QuotientPullbackData.twistedFreeAmbient] using
          exists_eventually_isRelativelyVeryAmple_universalQuot_int_of_nonempty_immersionPackages
            (n + 1) S l r P Q h' H

end CorQuotVeryAmple
