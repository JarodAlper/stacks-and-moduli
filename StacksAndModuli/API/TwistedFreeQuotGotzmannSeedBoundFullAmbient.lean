module

public import StacksAndModuli.API.ProjectiveGradedKernelRegularity
public import StacksAndModuli.API.TwistedFreeQuotGotzmannSeedBoundZeroAmbient

/-!
# The full-ambient projective-line Gotzmann seed bound

For the Hilbert polynomial of the full twisted-free ambient sheaf
`O(-l)^{⊕r}`, an epimorphic coefficient quotient with the prescribed rank is an
isomorphism.  Its kernel is therefore zero, so Grassmannian reconstruction recovers
the ambient sheaf itself.  The affine Gotzmann seed comparison consequently holds
in every degree in which the normalized degree is a natural number.

Main declarations:

* `Polynomial.twistedFreeHilbertPolynomial_hilbertNatValue_one`;
* `AlgebraicGeometry.Scheme.Modules.
  twistedFreeQuotProjectiveLineAffineGotzmannSeedBound_fullAmbient`;
* `AlgebraicGeometry.Scheme.Modules.
  twistedFreeQuotProjectiveLineGotzmannSeedBound_fullAmbient`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Polynomial

/-- On the projective line, the natural value of the twisted-free ambient Hilbert
polynomial is the number of degree-`e` monomial coefficients. -/
lemma twistedFreeHilbertPolynomial_hilbertNatValue_one
    (r : ℕ) (l : ℤ) (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) :
    (twistedFreeHilbertPolynomial 1 r l).hilbertNatValue d =
      r * (1 + e).choose 1 := by
  apply hilbertNatValue_eq
  rw [show (d : ℚ) = ((d : ℤ) : ℚ) by push_cast; ring]
  rw [twistedFreeHilbertPolynomial_eval 1 r l (d : ℤ) (by omega)]
  rw [he]
  rw [show (((1 : ℕ) : ℤ) + (e : ℤ)).toNat = 1 + e by omega]
  norm_num

end Polynomial

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A finite free sheaf on the product indexing the twisted-free monomials has
the expected product rank. -/
lemma twistedFreeMonomialFree_isProjectiveOfRank
    (T : Scheme.{u}) (r m : ℕ) :
    IsProjectiveOfRank (r * m)
      (SheafOfModules.free (R := T.ringCatSheaf)
        (ULift.{u} (Fin r) × Fin m)) := by
  let σ : ULift.{u} (Fin (r * m)) ≃ ULift.{u} (Fin r) × Fin m :=
    Scheme.twistedFreeMonomialIndexEquiv r m
  let w := SheafOfModules.freeMap (R := T.ringCatSheaf) σ
  haveI : IsIso w := Scheme.Modules.freeMap_isIso_of_equiv σ
  exact (free_isProjectiveOfRank T (r * m)).of_iso (asIso w)

/-- If the coefficient quotient is an isomorphism, its tensor-free
Grassmannian reconstruction is canonically the full twisted-free ambient sheaf. -/
noncomputable def twistedFreeAmbientIsoReconstructedQuotient'_of_isIso
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E) [IsIso u] :
    (∐ fun _ : ULift.{u} (Fin r) ↦
        Scheme.projectiveSpaceOverTwist n T (-l)) ≅
      Scheme.reconstructedQuotient' n T l r d e he u := by
  let f := Scheme.reconstructedRelation' n T l r d e he u
  let p := Scheme.reconstructedQuotientMap' n T l r d e he u
  have hkernel : IsZero (kernel u) := isZero_kernel_of_mono u
  have hpullback : IsZero
      ((pullback (Scheme.projectiveSpaceOverπ n T)).obj (kernel u)) :=
    Functor.map_isZero (pullback (Scheme.projectiveSpaceOverπ n T)) hkernel
  have hsource : IsZero
      (tensor
        ((pullback (Scheme.projectiveSpaceOverπ n T)).obj (kernel u))
        (Scheme.projectiveSpaceOverTwist n T (-(d : ℤ)))) :=
    tensor_isZero_of_left_isZero _ _ hpullback
  have hf : f = 0 := hsource.eq_zero_of_src f
  haveI : IsIso p := by
    dsimp only [p, Scheme.reconstructedQuotientMap']
    exact cokernel.π_of_zero hf
  exact asIso p

/-- For the Hilbert polynomial of the full ambient sheaf, the affine
projective-line Gotzmann seed bound is `0`. -/
noncomputable def
    twistedFreeQuotProjectiveLineAffineGotzmannSeedBound_fullAmbient
    (r : ℕ) (l : ℤ) :
    TwistedFreeQuotProjectiveLineAffineGotzmannSeedBound.{u}
      r l (Polynomial.twistedFreeHilbertPolynomial 1 r l) where
  bound := 0
  affineSeedRanks T _ d e he E _ u _ _ hE _ := by
    let m := r * (1 + e).choose 1
    have hsource : IsProjectiveOfRank m
        (SheafOfModules.free (R := T.ringCatSheaf)
          (ULift.{u} (Fin r) × Fin ((1 + e).choose 1))) :=
      twistedFreeMonomialFree_isProjectiveOfRank T r ((1 + e).choose 1)
    have hE' : IsProjectiveOfRank m E := by
      simpa only [m,
        Polynomial.twistedFreeHilbertPolynomial_hilbertNatValue_one r l d e he]
        using hE
    letI : IsIso u := isIso_of_epi_of_isProjectiveOfRank hsource hE' u
    let F := ∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist 1 T (-l)
    let Q := Scheme.reconstructedQuotient' 1 T l r d e he u
    let eQ : F ≅ Q :=
      twistedFreeAmbientIsoReconstructedQuotient'_of_isIso
        1 T l r d e he u
    have hFd : IsProjectiveOfRank (r * (1 + e).choose 1)
        (projectiveTwistedPushforward 1 F d) :=
      Scheme.twistedFreeTwistPushforward_isProjectiveOfRank
        1 T l r d e he
    have hQd : IsProjectiveOfRank (r * (1 + e).choose 1)
        (projectiveTwistedPushforward 1 Q d) :=
      hFd.of_iso (projectiveTwistedPushforwardIso eQ d)
    have heSucc : ((d + 1 : ℕ) : ℤ) - l = ((e + 1 : ℕ) : ℤ) := by
      omega
    have hFnext : IsProjectiveOfRank (r * (1 + (e + 1)).choose 1)
        (projectiveTwistedPushforward 1 F (d + 1)) :=
      Scheme.twistedFreeTwistPushforward_isProjectiveOfRank
        1 T l r (d + 1) (e + 1) heSucc
    have hQnext : IsProjectiveOfRank (r * (1 + (e + 1)).choose 1)
        (projectiveTwistedPushforward 1 Q (d + 1)) :=
      hFnext.of_iso (projectiveTwistedPushforwardIso eQ (d + 1))
    constructor
    · intro _
      simpa only [Q,
        Polynomial.twistedFreeHilbertPolynomial_hilbertNatValue_one r l d e he]
        using hQd
    · intro _
      simpa only [Q,
        Polynomial.twistedFreeHilbertPolynomial_hilbertNatValue_one
          r l (d + 1) (e + 1) heSucc]
        using hQnext

/-- The full-ambient affine seed-bound endpoint is inhabited for every ambient
rank and generating twist. -/
theorem
    nonempty_twistedFreeQuotProjectiveLineAffineGotzmannSeedBound_fullAmbient
    (r : ℕ) (l : ℤ) :
    Nonempty (TwistedFreeQuotProjectiveLineAffineGotzmannSeedBound.{u}
      r l (Polynomial.twistedFreeHilbertPolynomial 1 r l)) :=
  ⟨twistedFreeQuotProjectiveLineAffineGotzmannSeedBound_fullAmbient r l⟩

/-- The full-ambient affine comparison upgrades formally to the seed comparison
after arbitrary base change.  This is only the full-ambient boundary case: it does
not prove Gotzmann persistence for proper quotients or for an arbitrary admissible
Hilbert polynomial. -/
noncomputable def
    twistedFreeQuotProjectiveLineGotzmannSeedBound_fullAmbient
    (r : ℕ) (l : ℤ) :
    TwistedFreeQuotProjectiveLineGotzmannSeedBound.{u}
      r l (Polynomial.twistedFreeHilbertPolynomial 1 r l) :=
  (twistedFreeQuotProjectiveLineAffineGotzmannSeedBound_fullAmbient r l
    ).toGotzmannSeedBound

/-- The arbitrary-base-change seed-bound endpoint is inhabited for the Hilbert
polynomial of the full twisted-free ambient sheaf.  No general Gotzmann persistence
claim is involved. -/
theorem
    nonempty_twistedFreeQuotProjectiveLineGotzmannSeedBound_fullAmbient
    (r : ℕ) (l : ℤ) :
    Nonempty (TwistedFreeQuotProjectiveLineGotzmannSeedBound.{u}
      r l (Polynomial.twistedFreeHilbertPolynomial 1 r l)) :=
  ⟨twistedFreeQuotProjectiveLineGotzmannSeedBound_fullAmbient r l⟩

end AlgebraicGeometry.Scheme.Modules

end

end
