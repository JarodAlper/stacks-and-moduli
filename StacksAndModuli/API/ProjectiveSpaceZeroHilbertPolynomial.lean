module

public import StacksAndModuli.API.ProjectiveSpaceZeroGrassmannian

/-!
# Hilbert-polynomial classification on projective zero-space

A polynomial agreeing eventually with a Hilbert function is unique.  Since the
Hilbert function on relative projective zero-space is constant, every Hilbert
polynomial occurring over a nonempty base is therefore a constant polynomial
`Polynomial.C q` for a natural number `q`.

The final declaration applies this observation directly to points of the
fixed-polynomial Quot functor.  It separates the dimension-zero problem into
constant-polynomial Grassmannian strata and the case of a functor supported only on
empty test schemes.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme

/-- A Hilbert polynomial on relative projective space is unique when it exists. -/
theorem HasHilbertPolynomialOver.unique
    {n : ℕ} {R : CommRingCat.{u}}
    {Q : (projectiveSpaceOver n (Spec R)).Modules}
    {P P' : Polynomial ℚ}
    (hP : HasHilbertPolynomialOver Q P)
    (hP' : HasHilbertPolynomialOver Q P') : P = P' := by
  have hPP' : ∀ᶠ d : ℕ in Filter.atTop,
      P.eval (d : ℚ) = P'.eval (d : ℚ) := by
    filter_upwards [hP, hP'] with d hd hd' using hd ▸ hd'
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hPP'
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.Infinite.mono
    (s := (fun d : ℕ ↦ (d : ℚ)) '' {d | N ≤ d})
  · rintro _ ⟨d, hd, rfl⟩
    exact hN d hd
  · refine Set.Infinite.image ?_ (Set.Ici_infinite N)
    exact Set.injOn_of_injective (fun _ _ h ↦ by exact_mod_cast h)

/-- Every Hilbert polynomial on projective zero-space is the constant polynomial
whose value is the dimension of untwisted global sections. -/
theorem hasHilbertPolynomialOver_zero_eq_C
    {R : CommRingCat.{u}}
    (Q : (projectiveSpaceOver 0 (Spec R)).Modules)
    (P : Polynomial ℚ) (hP : HasHilbertPolynomialOver Q P) :
    letI := Modules.globalSectionsModule
      (projectiveSpaceOverπ 0 (Spec R)) Q
    P = Polynomial.C (Module.finrank R Γ(Q, ⊤) : ℚ) := by
  letI := Modules.globalSectionsModule
    (projectiveSpaceOverπ 0 (Spec R)) Q
  apply hP.unique
  exact (hasHilbertPolynomialOver_zero_C_iff Q
    (Module.finrank R Γ(Q, ⊤))).mpr rfl

/-- Over a nonempty base, every fiberwise Hilbert polynomial on projective
zero-space is a constant polynomial with a natural value. -/
theorem HasFiberwiseHilbertPolynomial.zero_eq_C_of_nonempty
    {S : Scheme.{u}} [Nonempty S]
    (Q : (projectiveSpaceOver 0 S).Modules) (P : Polynomial ℚ)
    (hP : HasFiberwiseHilbertPolynomial Q P) :
    ∃ q : ℕ, P = Polynomial.C (q : ℚ) := by
  let x : S := Classical.arbitrary S
  let s : Spec (S.residueField x) ⟶ S := S.fromSpecResidueField x
  let Qx := (Modules.pullback (projectiveSpaceOverMap 0 s)).obj Q
  letI := Modules.globalSectionsModule
    (projectiveSpaceOverπ 0 (Spec (S.residueField x))) Qx
  refine ⟨Module.finrank (S.residueField x) Γ(Qx, ⊤), ?_⟩
  exact hasHilbertPolynomialOver_zero_eq_C Qx P
    (hP (S.residueField x) (Field.toIsField _) s)

/-- A dimension-zero Quot datum over a nonempty test scheme can have only a
constant natural-valued fiberwise Hilbert polynomial. -/
theorem Modules.QuotientPullbackData.zero_polynomial_eq_C_of_nonempty
    {S : Scheme.{u}} {F : (projectiveSpaceOver 0 S).Modules}
    {T : Over S} [Nonempty T.left]
    (a : Modules.QuotientPullbackData F (projectiveSpaceOverπ 0 S) T)
    (P : Polynomial ℚ) (hP : a.HasFiberwiseHilbertPolynomial P) :
    ∃ q : ℕ, P = Polynomial.C (q : ℚ) :=
  HasFiberwiseHilbertPolynomial.zero_eq_C_of_nonempty
    (quotDataOnProjectiveSpace F a) P hP

/-- Every point of dimension-zero fixed-polynomial Quot over a nonempty test
scheme forces the chosen polynomial to be constant and natural-valued. -/
theorem quotFunctorP_zero_polynomial_eq_C_of_nonempty
    {S : Scheme.{u}} (F : (projectiveSpaceOver 0 S).Modules)
    (P : Polynomial ℚ) (T : Over S) [Nonempty T.left]
    (z : (quotFunctorP F P).obj (op T)) :
    ∃ q : ℕ, P = Polynomial.C (q : ℚ) := by
  obtain ⟨a, -, hP⟩ := z.2
  exact a.zero_polynomial_eq_C_of_nonempty P hP

end AlgebraicGeometry.Scheme

end
