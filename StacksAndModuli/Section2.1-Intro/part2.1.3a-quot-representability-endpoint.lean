module

public import StacksAndModuli.«Section2.4-Projectivity».«part2.4.1-valuative-criteria»
public import StacksAndModuli.API.QuotientKernelProjectiveTwistedModels

/-!
# Projective representability of the fixed-polynomial Quot functor

This supplemental part closes the dependency loop in Theorem 2.1.3.  The definitions of
relative projective space and `Quot^P` occur in the preceding part.  The projectivity
theorem for a finite twisted-free ambient sheaf is proved in §2.4, and the canonical
kernel zero-locus construction then descends projectivity along the printed epimorphic
presentation `O(-l)^⊕r ⟶ F`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry

universe u

section ThmQuotSchemeRepresentable

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

/-- **Theorem 2.1.3** (`thm:quot-scheme-representable`): let `S` be a locally noetherian
scheme and `F` a quasi-coherent, finitely presented quotient of `O(-l)^{⊕r}` on
`ℙ^n_S`. For `P ∈ ℚ[z]`, `Quot^P(F/ℙ^n_S)` is representable by a scheme projective
over `S`.

The finite twisted-free Quot functor is projective by Theorem 2.4.5.  The epimorphism in
the printed presentation induces a closed subfunctor: on the universal twisted-free
Quot representative, its ambient-kernel condition is cut out by canonical finite-free
positive-twist equations.  In dimension zero the corresponding Cohomology and Base
Change package has bound zero; in positive dimension it is supplied by the graded
Čech construction. -/
theorem exists_quotFunctorP_representableBy (n : ℕ) (S : Scheme.{u})
    [IsLocallyNoetherian S] (F : (projectiveSpaceOver n S).Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation]
    (hF : F.IsQuotientOfTwistedFree) (P : Polynomial ℚ) :
    ∃ Q : Over S,
      Nonempty ((quotFunctorP F P).RepresentableBy Q) ∧ IsHProjective Q.hom := by
  obtain ⟨l, r, p, hp⟩ := hF
  letI : Epi p := hp
  obtain ⟨Q₀, ⟨eG⟩, hQ₀⟩ :=
    exists_quotFunctorP_representableBy_isHProjective n S l r P
  have hp' : Epi p := inferInstance
  change Modules.QuotientPullbackData.twistedFreeAmbient
    (S := S) (n := n) (r := r) (l := l) ⟶ F at p
  letI : Epi p := hp'
  change (quotFunctorP
    (Modules.QuotientPullbackData.twistedFreeAmbient
      (S := S) (n := n) (r := r) (l := l)) P).RepresentableBy Q₀ at eG
  letI : LocallyOfFiniteType Q₀.hom :=
    hQ₀.isHQuasiProjective.locallyOfFiniteType
  letI : IsLocallyNoetherian Q₀.left :=
    LocallyOfFiniteType.isLocallyNoetherian Q₀.hom
  cases n with
  | zero =>
      exact
        exists_quotFunctorP_representableBy_isHProjective_of_universal_twistedFree_zero
          r l p P Q₀ eG hQ₀
  | succ n =>
      exact
        exists_quotFunctorP_representableBy_isHProjective_of_universal_twistedFree
          (n + 1) r (Nat.zero_lt_succ n) l p P Q₀ eG hQ₀

end AlgebraicGeometry.Scheme

end ThmQuotSchemeRepresentable

end
