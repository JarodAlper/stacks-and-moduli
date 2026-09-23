module

public import StacksAndModuli.«Section2.1-Intro».«part2.1.3a-quot-representability-endpoint»
public import StacksAndModuli.API.HilbertQuotientBridge
public import StacksAndModuli.API.ProjectiveSpaceTwistZero
public import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# Hilbert representability via Quot

This supplemental module completes the polynomial-free representability assertion of
§2.1 (Intro), Chapter 2 of *Stacks and Moduli*
(the section heading carries no `sec:` label).

The quotient theorem occurs after the Hilbert theorem in the book and in the preceding
part file. Keeping its corollary here preserves acyclic imports while making the proof the
formal counterpart of Remark 2.1.5(4): the Hilbert functor is the Quot functor of the
structure sheaf.

Main book result:
- `AlgebraicGeometry.Scheme.exists_hilbFunctorP_representableBy`.

The polynomial-free Hilbert functor and its representability statement are supporting
forms used to connect this result to Remark 2.1.5.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

section ThmHilbertSchemeRepresentable

namespace AlgebraicGeometry.Scheme

/-- Background definition for Theorem 2.1.2 (fixed-polynomial
functor): the subfunctor `Hilb^P(ℙ^n_S/S)` of flat, finitely presented closed
families whose structure-sheaf quotient has fibrewise Hilbert polynomial `P`.

The condition is deliberately phrased using the corresponding quotient of the
structure sheaf. This makes the comparison with `Quot^P(𝒪_{ℙ^n_S})` exact and
uses the same all-field-valued-points formulation that makes `quotFunctorP` stable
under arbitrary base change. -/
noncomputable def hilbFunctorP (n : ℕ) (S : Scheme.{u}) (P : Polynomial ℚ) :
    CategoryTheory.Functor (Over S)ᵒᵖ (Type u) :=
  ({ obj T := { I | ∃ a : Modules.QuotientPullbackData
          (SheafOfModules.unit (projectiveSpaceOver n S).ringCatSheaf)
          (projectiveSpaceOverπ n S) T.unop,
        Quotient.mk _ a =
          hilbertToStructureSheafQuotientAt (projectiveSpaceOverπ n S) T.unop I ∧
        a.HasFiberwiseHilbertPolynomial P }
     map := by
      intro T T' g I hI
      obtain ⟨a, ha, hP⟩ := hI
      refine ⟨a.pullback g.unop, ?_,
        Modules.QuotientPullbackData.hasFiberwiseHilbertPolynomial_pullback g.unop hP⟩
      change (quotFunctor
          (SheafOfModules.unit (projectiveSpaceOver n S).ringCatSheaf)
          (projectiveSpaceOverπ n S)).map g (Quotient.mk _ a) = _
      rw [ha]
      exact (hilbertToStructureSheafQuotientAt_naturality
        (projectiveSpaceOverπ n S) g.unop I).symm } :
    Subfunctor (hilbFunctor (projectiveSpaceOverπ n S))).toFunctor

/-- Fixed-polynomial Hilbert families are pointwise equivalent to fixed-polynomial
quotients of the structure sheaf. -/
noncomputable def hilbStructureSheafQuotientPEquiv
    (n : ℕ) (S : Scheme.{u}) (P : Polynomial ℚ) (T : Over S) :
    (hilbFunctorP n S P).obj (op T) ≃
      (quotFunctorP
        (SheafOfModules.unit (projectiveSpaceOver n S).ringCatSheaf) P).obj (op T) where
  toFun I := ⟨hilbertToStructureSheafQuotientAt
    (projectiveSpaceOverπ n S) T I.1, I.2⟩
  invFun q := ⟨structureSheafQuotientToHilbertAt
    (projectiveSpaceOverπ n S) T q.1, by
      obtain ⟨a, ha, hP⟩ := q.2
      refine ⟨a, ?_, hP⟩
      rw [← ha]
      exact (hilbertStructureSheafQuotientEquiv
        (projectiveSpaceOverπ n S) T).apply_symm_apply (Quotient.mk _ a) |>.symm⟩
  left_inv I := by
    apply Subtype.ext
    exact (hilbertStructureSheafQuotientEquiv
      (projectiveSpaceOverπ n S) T).symm_apply_apply I.1
  right_inv q := by
    apply Subtype.ext
    exact (hilbertStructureSheafQuotientEquiv
      (projectiveSpaceOverπ n S) T).apply_symm_apply q.1

/-- After lifting the smaller value universe, `Hilb^P(ℙ^n_S/S)` is naturally
isomorphic to `Quot^P(𝒪_{ℙ^n_S}/ℙ^n_S/S)`. -/
noncomputable def hilbStructureSheafQuotientPNatIso
    (n : ℕ) (S : Scheme.{u}) (P : Polynomial ℚ) :
    hilbFunctorP n S P ⋙ uliftFunctor.{u + 1, u} ≅
      quotFunctorP
        (SheafOfModules.unit (projectiveSpaceOver n S).ringCatSheaf) P :=
  NatIso.ofComponents
    (fun T ↦ ((Equiv.ulift.{u + 1, u}).trans
      (hilbStructureSheafQuotientPEquiv n S P T.unop)).toIso)
    (fun {T T'} g ↦ by
      ext z
      apply Subtype.ext
      change hilbertToStructureSheafQuotientAt (projectiveSpaceOverπ n S) T'.unop
          ((hilbFunctor (projectiveSpaceOverπ n S)).map g z.down.1) =
        (quotFunctor
          (SheafOfModules.unit (projectiveSpaceOver n S).ringCatSheaf)
          (projectiveSpaceOverπ n S)).map g
            (hilbertToStructureSheafQuotientAt
              (projectiveSpaceOverπ n S) T.unop z.down.1)
      exact hilbertToStructureSheafQuotientAt_naturality
        (projectiveSpaceOverπ n S) g.unop z.down.1)

/-- API lemma for Theorem 2.1.2 (projective
Hilbert-from-Quot reduction): a projective representing scheme for the fixed-polynomial
Quot functor of the structure sheaf represents the corresponding fixed-polynomial
Hilbert functor as well. -/
theorem exists_hilbFunctorP_representableBy_of_quotFunctorP
    (n : ℕ) (S : Scheme.{u}) (P : Polynomial ℚ)
    (hQ : ∃ Q : Over S,
      Nonempty ((quotFunctorP
        (SheafOfModules.unit (projectiveSpaceOver n S).ringCatSheaf) P).RepresentableBy Q) ∧
      IsHProjective Q.hom) :
    ∃ H : Over S,
      Nonempty ((hilbFunctorP n S P).RepresentableBy H) ∧ IsHProjective H.hom := by
  obtain ⟨Q, ⟨hQ⟩, hQproj⟩ := hQ
  refine ⟨Q, ⟨?_⟩, hQproj⟩
  exact Functor.representableByUliftFunctorEquiv.toFun
    (hQ.ofIso (hilbStructureSheafQuotientPNatIso n S P).symm)

/-- **Theorem 2.1.2** (`thm:hilbert-scheme-representable`): for every noetherian
scheme `S` and every polynomial `P ∈ ℚ[z]`, the functor
`Hilb^P(ℙⁿ_S/S)` is representable by a projective scheme over `S`.

The formal statement proves the same conclusion under the weaker locally noetherian
hypothesis used by the formal Quot theorem. -/
theorem exists_hilbFunctorP_representableBy
    (n : ℕ) (S : Scheme.{u}) [IsLocallyNoetherian S] (P : Polynomial ℚ) :
    ∃ H : Over S,
      Nonempty ((hilbFunctorP n S P).RepresentableBy H) ∧ IsHProjective H.hom := by
  apply exists_hilbFunctorP_representableBy_of_quotFunctorP n S P
  let _ : (SheafOfModules.unit
      (projectiveSpaceOver n S).ringCatSheaf).IsQuasicoherent :=
    Modules.unit_isQuasicoherent (projectiveSpaceOver n S)
  let _ : (SheafOfModules.unit
      (projectiveSpaceOver n S).ringCatSheaf).IsFinitePresentation :=
    Modules.unit_isFinitePresentation (projectiveSpaceOver n S)
  exact exists_quotFunctorP_representableBy n S
    (SheafOfModules.unit (projectiveSpaceOver n S).ringCatSheaf)
    (Modules.unit_isQuotientOfTwistedFree_projectiveSpaceOver n S) P

/-- API lemma for Theorem 2.1.2 (polynomial-free part, via
Remark 2.1.5(4)): representability of the Hilbert functor. Let `S` be
a locally noetherian scheme and `n` a natural number. The Hilbert functor `Hilb(ℙ^n_S/S)`
of flat, finitely presented families of closed subschemes of `ℙ^n_S` is representable by a
scheme locally of finite type over `S`.

The book's theorem asserts more: each subfunctor `Hilb^P` with fixed fiberwise Hilbert
polynomial `P` is representable by a *projective* scheme over `S`, and `Hilb = ⊔_P
Hilb^P`. This declaration records the polynomial-free content, obtained by identifying
Hilbert families with quotients of the structure sheaf. -/
theorem exists_hilbFunctor_representableBy (n : ℕ) (S : Scheme.{u})
    [IsLocallyNoetherian S] :
    ∃ H : Over S,
      Nonempty ((hilbFunctor (Scheme.projectiveSpaceOverπ n S)).RepresentableBy H) ∧
      LocallyOfFiniteType H.hom := by
  let _ : (SheafOfModules.unit
      (Scheme.projectiveSpaceOver n S).ringCatSheaf).IsQuasicoherent :=
    Modules.unit_isQuasicoherent (Scheme.projectiveSpaceOver n S)
  let _ : (SheafOfModules.unit
      (Scheme.projectiveSpaceOver n S).ringCatSheaf).IsFinitePresentation :=
    Modules.unit_isFinitePresentation (Scheme.projectiveSpaceOver n S)
  obtain ⟨Q, ⟨hQ⟩, hQlfp⟩ := exists_quotFunctor_representableBy n S
    (SheafOfModules.unit (Scheme.projectiveSpaceOver n S).ringCatSheaf)
  refine ⟨Q, ⟨?_⟩, hQlfp⟩
  exact Functor.representableByUliftFunctorEquiv.toFun
    (hQ.ofIso (hilbertStructureSheafQuotientNatIso
      (Scheme.projectiveSpaceOverπ n S)).symm)

end AlgebraicGeometry.Scheme

end ThmHilbertSchemeRepresentable
