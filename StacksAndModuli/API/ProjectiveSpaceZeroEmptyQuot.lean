module

public import StacksAndModuli.API.ProjectiveSpaceZeroHilbertPolynomial
public import StacksAndModuli.API.SchemeModulesEmptyOpen

/-!
# Empty fixed-polynomial Quot functors on projective zero-space

If a polynomial is not `Polynomial.C q` for any natural number `q`, the
fixed-polynomial Quot functor on relative projective zero-space has points only
over empty test schemes.  This file identifies that functor with the functor
represented by the empty scheme over the base and proves that the resulting
representing morphism is H-projective.

The construction also records the underlying empty-scheme module facts: every
module sheaf on an empty scheme is a zero object and is flat over every base.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme

/-- Every sheaf of modules on an empty scheme is a zero object. -/
lemma Modules.isZero_of_isEmpty {X : Scheme.{u}} [IsEmpty X]
    (M : X.Modules) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  apply Modules.hom_ext _ _ fun U ↦ ?_
  have hU : U = ⊥ := Subsingleton.elim _ _
  subst U
  letI : Subsingleton Γ(M, ⊥) := Modules.subsingleton_sections_bot M
  ext x
  exact Subsingleton.elim _ _

/-- A sheaf of modules on an empty scheme is flat over every target scheme. -/
lemma Modules.flatOver_of_isEmpty {X Y : Scheme.{u}} [IsEmpty X]
    (M : X.Modules) (f : X ⟶ Y) : M.FlatOver f := by
  intro U V h
  letI := Module.compHom Γ(M, U.1)
    ((X.presheaf.map (homOfLE h).op).hom.comp (f.app V.1).hom)
  have hU : U.1 = ⊥ := Subsingleton.elim _ _
  letI : Subsingleton Γ(M, U.1) :=
    hU.symm ▸ Modules.subsingleton_sections_bot M
  exact Module.Flat.of_free

/-- The canonical quotient datum over an empty test scheme.  Its target is the
structure sheaf of the empty fibre product, which is a zero object. -/
noncomputable def emptyQuotientPullbackData
    {n : ℕ} {S : Scheme.{u}}
    (F : (projectiveSpaceOver n S).Modules) (T : Over S)
    [IsEmpty T.left] :
    Modules.QuotientPullbackData F (projectiveSpaceOverπ n S) T := by
  let W := ((Over.pullback (projectiveSpaceOverπ n S)).obj T).left
  letI : IsEmpty W :=
    (pullback.fst T.hom (projectiveSpaceOverπ n S)).base.hom.1.isEmpty
  let Q : W.Modules := SheafOfModules.unit W.ringCatSheaf
  exact
    { Q := Q
      isQuasicoherent := Modules.unit_isQuasicoherent W
      isFinitePresentation :=
        Modules.unit_isFinitePresentation_of_globalPresentation W
      flatOver := Modules.flatOver_of_isEmpty Q _
      π := 0
      epi := (Modules.isZero_of_isEmpty Q).epi 0 }

/-- The canonical quotient over an empty test scheme satisfies every fiberwise
Hilbert-polynomial condition, since there are no field-valued points. -/
lemma emptyQuotientPullbackData_hasFiberwiseHilbertPolynomial
    {n : ℕ} {S : Scheme.{u}}
    (F : (projectiveSpaceOver n S).Modules) (P : Polynomial ℚ)
    (T : Over S) [IsEmpty T.left] :
    (emptyQuotientPullbackData F T).HasFiberwiseHilbertPolynomial P := by
  intro K hK s
  letI : Field K := hK.toField
  letI : IsEmpty (Spec K) := s.base.hom.1.isEmpty
  exact isEmptyElim (Classical.arbitrary (Spec K))

/-- The canonical point of fixed-polynomial Quot over an empty test scheme. -/
noncomputable def emptyQuotFunctorPPoint
    {n : ℕ} {S : Scheme.{u}}
    (F : (projectiveSpaceOver n S).Modules) (P : Polynomial ℚ)
    (T : Over S) [IsEmpty T.left] :
    (quotFunctorP F P).obj (op T) :=
  ⟨Quotient.mk _ (emptyQuotientPullbackData F T),
    emptyQuotientPullbackData F T,
    rfl, emptyQuotientPullbackData_hasFiberwiseHilbertPolynomial F P T⟩

/-- Any two quotient presentations over an empty test scheme are equivalent. -/
lemma quotientPullbackData_r_of_isEmpty
    {X S : Scheme.{u}} {F : X.Modules} {f : X ⟶ S}
    (T : Over S) [IsEmpty T.left]
    (x y : Modules.QuotientPullbackData F f T) :
    (Modules.QuotientPullbackData.setoid F f T).r x y := by
  let W := ((Over.pullback f).obj T).left
  letI : IsEmpty W := (pullback.fst T.hom f).base.hom.1.isEmpty
  let hx : IsZero x.Q := Modules.isZero_of_isEmpty x.Q
  let hy : IsZero y.Q := Modules.isZero_of_isEmpty y.Q
  refine ⟨hx.isoZero ≪≫ hy.isoZero.symm, ?_⟩
  exact hy.eq_of_tgt _ _

/-- Fixed-polynomial Quot has at most one point over an empty test scheme. -/
lemma quotFunctorP_subsingleton_of_isEmpty
    {n : ℕ} {S : Scheme.{u}}
    (F : (projectiveSpaceOver n S).Modules) (P : Polynomial ℚ)
    (T : Over S) [IsEmpty T.left] :
    Subsingleton ((quotFunctorP F P).obj (op T)) := by
  constructor
  intro x y
  apply Subtype.ext
  obtain ⟨a, ha⟩ := Quotient.exists_rep x.1
  obtain ⟨b, hb⟩ := Quotient.exists_rep y.1
  rw [← ha, ← hb]
  exact Quotient.sound (quotientPullbackData_r_of_isEmpty T a b)

/-- The empty scheme equipped with its unique morphism to `S`. -/
noncomputable def emptyOver (S : Scheme.{u}) : Over S :=
  Over.mk (Scheme.emptyTo S)

instance emptyOver_isEmpty (S : Scheme.{u}) : IsEmpty (emptyOver S).left := by
  dsimp [emptyOver]
  infer_instance

/-- A morphism to the empty `S`-scheme yields the unique fixed-polynomial Quot
point over its necessarily empty source. -/
noncomputable def emptyOverToQuotFunctorP
    {n : ℕ} {S : Scheme.{u}}
    (F : (projectiveSpaceOver n S).Modules) (P : Polynomial ℚ)
    {T : Over S} (g : T ⟶ emptyOver S) :
    (quotFunctorP F P).obj (op T) := by
  letI : IsEmpty T.left := g.left.base.hom.1.isEmpty
  exact emptyQuotFunctorPPoint F P T

/-- A fixed-polynomial Quot functor is empty on nonempty test schemes if every
such test scheme has an empty type of functor points. -/
def QuotFunctorPEmptyOnNonempty
    {n : ℕ} {S : Scheme.{u}}
    (F : (projectiveSpaceOver n S).Modules) (P : Polynomial ℚ) : Prop :=
  ∀ T : Over S, Nonempty T.left → IsEmpty ((quotFunctorP F P).obj (op T))

/-- If fixed-polynomial Quot is empty on every nonempty test scheme, a functor
point forces the parameter scheme to be empty and hence gives a map to the
empty `S`-scheme. -/
noncomputable def quotFunctorPToEmptyOver_of_isEmptyOnNonempty
    {n : ℕ} {S : Scheme.{u}}
    (F : (projectiveSpaceOver n S).Modules) (P : Polynomial ℚ)
    (hempty : QuotFunctorPEmptyOnNonempty F P)
    {T : Over S} (z : (quotFunctorP F P).obj (op T)) :
    T ⟶ emptyOver S := by
  have hne : ¬ Nonempty T.left := by
    intro hT
    letI : IsEmpty ((quotFunctorP F P).obj (op T)) := hempty T hT
    exact isEmptyElim z
  letI : IsEmpty T.left := not_nonempty_iff.mp hne
  let hT : IsInitial T.left := isInitialOfIsEmpty
  exact Over.homMk (hT.to (emptyOver S).left) (hT.hom_ext _ _)

/-- Maps to the empty `S`-scheme are naturally equivalent to fixed-polynomial
Quot points whenever the latter are empty on all nonempty test schemes. -/
noncomputable def emptyOverQuotFunctorPEquiv_of_isEmptyOnNonempty
    {n : ℕ} {S : Scheme.{u}}
    (F : (projectiveSpaceOver n S).Modules) (P : Polynomial ℚ)
    (hempty : QuotFunctorPEmptyOnNonempty F P) (T : Over S) :
    (T ⟶ emptyOver S) ≃ (quotFunctorP F P).obj (op T) where
  toFun := emptyOverToQuotFunctorP F P
  invFun := quotFunctorPToEmptyOver_of_isEmptyOnNonempty F P hempty
  left_inv g := by
    letI : IsEmpty T.left := g.left.base.hom.1.isEmpty
    apply Over.OverMorphism.ext
    exact isInitialOfIsEmpty.hom_ext _ _
  right_inv z := by
    let g := quotFunctorPToEmptyOver_of_isEmptyOnNonempty F P hempty z
    letI : IsEmpty T.left := g.left.base.hom.1.isEmpty
    exact (quotFunctorP_subsingleton_of_isEmpty F P T).elim _ _

/-- A fixed-polynomial Quot functor empty on every nonempty test scheme is
represented by the empty scheme. -/
noncomputable def quotFunctorPRepresentableByEmpty_of_isEmptyOnNonempty
    {n : ℕ} {S : Scheme.{u}}
    (F : (projectiveSpaceOver n S).Modules) (P : Polynomial ℚ)
    (hempty : QuotFunctorPEmptyOnNonempty F P) :
    (quotFunctorP F P).RepresentableBy (emptyOver S) where
  homEquiv := emptyOverQuotFunctorPEquiv_of_isEmptyOnNonempty F P hempty _
  homEquiv_comp {X X'} f g := by
    letI : IsEmpty X.left := (f ≫ g).left.base.hom.1.isEmpty
    exact (quotFunctorP_subsingleton_of_isEmpty F P X).elim _ _

/-- If `P` is not a natural-valued constant, every `P⁰` fixed-polynomial Quot
point has empty parameter scheme and hence induces a morphism to `emptyOver S`. -/
noncomputable def quotFunctorPToEmptyOver
    {S : Scheme.{u}}
    (F : (projectiveSpaceOver 0 S).Modules) (P : Polynomial ℚ)
    (hP : ¬ ∃ q : ℕ, P = Polynomial.C (q : ℚ))
    {T : Over S} (z : (quotFunctorP F P).obj (op T)) :
    T ⟶ emptyOver S := by
  have hne : ¬ Nonempty T.left := by
    intro hT
    letI : Nonempty T.left := hT
    exact hP (quotFunctorP_zero_polynomial_eq_C_of_nonempty F P T z)
  letI : IsEmpty T.left := not_nonempty_iff.mp hne
  let hT : IsInitial T.left := isInitialOfIsEmpty
  exact Over.homMk (hT.to (emptyOver S).left) (hT.hom_ext _ _)

/-- The pointwise equivalence between maps to the empty `S`-scheme and points of
a non-natural-constant fixed-polynomial Quot functor on `P⁰`. -/
noncomputable def emptyOverQuotFunctorPEquiv
    {S : Scheme.{u}}
    (F : (projectiveSpaceOver 0 S).Modules) (P : Polynomial ℚ)
    (hP : ¬ ∃ q : ℕ, P = Polynomial.C (q : ℚ))
    (T : Over S) :
    (T ⟶ emptyOver S) ≃ (quotFunctorP F P).obj (op T) where
  toFun := emptyOverToQuotFunctorP F P
  invFun := quotFunctorPToEmptyOver F P hP
  left_inv g := by
    letI : IsEmpty T.left := g.left.base.hom.1.isEmpty
    apply Over.OverMorphism.ext
    exact isInitialOfIsEmpty.hom_ext _ _
  right_inv z := by
    let g := quotFunctorPToEmptyOver F P hP z
    letI : IsEmpty T.left := g.left.base.hom.1.isEmpty
    exact (quotFunctorP_subsingleton_of_isEmpty F P T).elim _ _

/-- If `P` is not `C(q)` for a natural number `q`, fixed-polynomial Quot on
relative `P⁰` is represented by the empty `S`-scheme. -/
noncomputable def quotFunctorPRepresentableByEmpty_zero
    {S : Scheme.{u}}
    (F : (projectiveSpaceOver 0 S).Modules) (P : Polynomial ℚ)
    (hP : ¬ ∃ q : ℕ, P = Polynomial.C (q : ℚ)) :
    (quotFunctorP F P).RepresentableBy (emptyOver S) where
  homEquiv := emptyOverQuotFunctorPEquiv F P hP _
  homEquiv_comp {X X'} f g := by
    letI : IsEmpty X.left := (f ≫ g).left.base.hom.1.isEmpty
    exact (quotFunctorP_subsingleton_of_isEmpty F P X).elim _ _

/-- The empty scheme over any base is H-projective. -/
theorem emptyOver_isHProjective (S : Scheme.{u}) :
    IsHProjective (emptyOver S).hom := by
  refine ⟨0, Scheme.emptyTo (projectiveSpaceOver 0 S), inferInstance, ?_⟩
  exact Scheme.empty_ext _ _

/-- A fixed-polynomial Quot functor empty on every nonempty test scheme has an
H-projective representative, namely the empty scheme. -/
theorem exists_quotFunctorP_representableBy_isHProjective_empty_of_isEmptyOnNonempty
    {n : ℕ} {S : Scheme.{u}}
    (F : (projectiveSpaceOver n S).Modules) (P : Polynomial ℚ)
    (hempty : QuotFunctorPEmptyOnNonempty F P) :
    ∃ Q : Over S, Nonempty ((quotFunctorP F P).RepresentableBy Q) ∧
      IsHProjective Q.hom :=
  ⟨emptyOver S,
    ⟨quotFunctorPRepresentableByEmpty_of_isEmptyOnNonempty F P hempty⟩,
    emptyOver_isHProjective S⟩

/-- The non-natural-constant fixed-polynomial Quot functor on relative `P⁰` has
an H-projective representative, namely the empty scheme. -/
theorem exists_quotFunctorP_zero_representableBy_isHProjective_empty
    {S : Scheme.{u}}
    (F : (projectiveSpaceOver 0 S).Modules) (P : Polynomial ℚ)
    (hP : ¬ ∃ q : ℕ, P = Polynomial.C (q : ℚ)) :
    ∃ Q : Over S, Nonempty ((quotFunctorP F P).RepresentableBy Q) ∧
      IsHProjective Q.hom :=
  ⟨emptyOver S, ⟨quotFunctorPRepresentableByEmpty_zero F P hP⟩,
    emptyOver_isHProjective S⟩

end AlgebraicGeometry.Scheme

end
