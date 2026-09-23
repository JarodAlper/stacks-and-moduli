module

public import StacksAndModuli.API.TwistedFreeMonomialSpanAffine
public import StacksAndModuli.API.PushforwardProjectiveRank
public import StacksAndModuli.API.FreeQuotientRankBound
public import StacksAndModuli.API.ProjectiveSpaceZeroGlobalSectionsRank
public import StacksAndModuli.API.ProjectiveSpaceZeroHilbertPolynomial
public import StacksAndModuli.API.TwistedFreeQuotArbitraryBase
public import StacksAndModuli.API.FiniteFlatConstantRank
public import StacksAndModuli.API.PolynomialHilbertNatValue

/-!
# Fixed-degree ranks of pushforwards in the twisted-free Quot problem

For the Quot-to-Grassmannian construction in Proposition 2.4.1, one degree `d` must work
simultaneously for every twisted-free quotient with fixed Hilbert polynomial `P`.  The
eventual cohomology-and-base-change package is not enough by itself: its bound is chosen
separately for each family.  This file instead feeds the uniform kernel-regularity bound
directly into fixed-degree cohomology and base change.

Over a locally noetherian base the result is that, in every sufficiently large fixed degree,
`pi_* Q(d)` is finite locally free of the natural-number value of `P(d)`.  Over an arbitrary
base this file isolates the precise remaining proper-finiteness input: finite positive Cech
cohomology and finitely presented `H^0` imply the same fixed-degree conclusion and arbitrary
base change.  Projective zero-space is handled over an arbitrary base without this extra
input.  The numerical rank bound forced by the monomial presentation is also recorded.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open AlgebraicGeometry ProjectiveSpectrum.Twist

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

namespace CochainComplex

variable {R : Type u} [CommRing R]
  (C : CochainComplex (ModuleCat.{u} R) ℕ)

/-- If a bounded flat complex is already exact above degree `j + 1`, then exactness at
degree `j + 1` after scalar extension makes the scalar extension of the differential
onto the scalar-extended cocycles. -/
theorem surjective_baseChange_dToCocycles_of_exactAtSucc
    (hflat : ∀ p : ℕ, Module.Flat R (C.X p)) {N : ℕ}
    (hvan : ∀ p : ℕ, N < p → Subsingleton (C.X p))
    (j : ℕ) (habove : ∀ i : ℕ, j + 1 ≤ i → ExactAtSucc C i)
    (A : Type u) [CommRing A] [Algebra R A]
    (hA : ExactAtSucc (GradedModule.cochainBaseChange A C) j) :
    Function.Surjective (LinearMap.baseChange A (dToCocycles C j)) := by
  have hAe : LinearMap.range (LinearMap.baseChange A (C.d j (j + 1)).hom) =
      LinearMap.ker (LinearMap.baseChange A (C.d (j + 1) (j + 2)).hom) := by
    have h := hA
    rw [ExactAtSucc, cocyclesSub, cochainBaseChange_d_hom,
      cochainBaseChange_d_hom] at h
    exact h
  have hker : LinearMap.ker (LinearMap.baseChange A (C.d (j + 1) (j + 2)).hom) =
      Submodule.map (LinearMap.baseChange A (cocyclesSub C (j + 1)).subtype) ⊤ := by
    rw [Submodule.map_top]
    exact ker_baseChange_d A hflat hvan habove (i := j + 1) le_rfl
  have hrange : LinearMap.range (LinearMap.baseChange A (C.d j (j + 1)).hom) =
      Submodule.map (LinearMap.baseChange A (cocyclesSub C (j + 1)).subtype)
        (LinearMap.range (LinearMap.baseChange A (dToCocycles C j))) := by
    have hfac : (C.d j (j + 1)).hom =
        (cocyclesSub C (j + 1)).subtype ∘ₗ dToCocycles C j := rfl
    rw [hfac, LinearMap.baseChange_comp, LinearMap.range_comp]
  have hinj := injective_baseChange_cocyclesSub_subtype A hflat hvan habove
    (i := j + 1) le_rfl
  rw [← LinearMap.range_eq_top]
  refine Submodule.map_injective_of_injective hinj ?_
  rw [← hrange, hAe, hker]

/-- Exactness at the successor of `j` is equivalent to surjectivity of the differential
corestricted to the cocycles. -/
lemma exactAtSucc_iff_surjective_dToCocycles (j : ℕ) :
    ExactAtSucc C j ↔ Function.Surjective (dToCocycles C j) := by
  constructor
  · exact surjective_dToCocycles C
  · intro h
    rw [← subsingleton_cohomologySucc_iff C j,
      Submodule.Quotient.subsingleton_iff]
    exact LinearMap.range_eq_top.mpr h

set_option maxHeartbeats 1000000 in
-- The descending induction repeatedly elaborates base-change exactness and Nakayama.
/-- A bounded complex of finitely presented flat modules which is exact on every field
fibre is exact in positive degrees, and all its cocycle modules are finitely presented.

The proof descends from the top of the complex.  At each stage, the next cocycle module
is finite projective, so fibrewise surjectivity of the corestricted differential is
detected by Nakayama and the resulting split exact sequence makes the current cocycles
finitely presented. -/
theorem exactAtSucc_and_finitePresentation_cocycles_of_fibrewise
    (hfp : ∀ p : ℕ, Module.FinitePresentation R (C.X p))
    (hflat : ∀ p : ℕ, Module.Flat R (C.X p)) {N : ℕ}
    (hvan : ∀ p : ℕ, N < p → Subsingleton (C.X p))
    (hfib : ∀ (K : Type u) [Field K] [Algebra R K] (j : ℕ),
      ExactAtSucc (GradedModule.cochainBaseChange K C) j) :
    (∀ j : ℕ, ExactAtSucc C j) ∧
      ∀ i : ℕ, Module.FinitePresentation R (cocyclesSub C i) := by
  have key : ∀ (m j : ℕ), N ≤ j + m →
      ExactAtSucc C j ∧ Module.FinitePresentation R (cocyclesSub C j) := by
    intro m
    induction m with
    | zero =>
        intro j hj
        have hXnext : Subsingleton (C.X (j + 1)) := hvan (j + 1) (by omega)
        have hexj : ExactAtSucc C j := exactAtSucc_of_subsingleton_X hXnext
        haveI hfpj : Module.FinitePresentation R (C.X j) := hfp j
        haveI hZnext : Subsingleton (cocyclesSub C (j + 1)) :=
          ⟨fun x y ↦ Subtype.ext (Subsingleton.elim x.1 y.1)⟩
        haveI hflatZnext : Module.Flat R (cocyclesSub C (j + 1)) :=
          Module.Flat.of_shrink.{u, u, u}
        haveI hfpZnext : Module.FinitePresentation R (cocyclesSub C (j + 1)) :=
          inferInstance
        haveI hprojZnext : Module.Projective R (cocyclesSub C (j + 1)) :=
          Module.Flat.projective_of_finitePresentation
        refine ⟨hexj, ?_⟩
        exact Module.finitePresentation_of_projective_of_exact
          (cocyclesSub C j).subtype (dToCocycles C j)
          Subtype.val_injective (surjective_dToCocycles C hexj)
          (exact_subtype_dToCocycles C j)
    | succ m ih =>
        intro j hj
        by_cases hjm : N ≤ j + m
        · exact ih j hjm
        · have hNjm : N = j + m + 1 := by omega
          have habove : ∀ i : ℕ, j + 1 ≤ i → ExactAtSucc C i := by
            intro i hi
            exact (ih i (by omega)).1
          haveI hfpj : Module.FinitePresentation R (C.X j) := hfp j
          haveI hfpZnext : Module.FinitePresentation R (cocyclesSub C (j + 1)) :=
            (ih (j + 1) (by omega)).2
          haveI hflatZnext : Module.Flat R (cocyclesSub C (j + 1)) :=
            flat_cocyclesSub hflat hvan habove le_rfl
          haveI hprojZnext : Module.Projective R (cocyclesSub C (j + 1)) :=
            Module.Flat.projective_of_finitePresentation
          have hsurj : Function.Surjective (dToCocycles C j) :=
            Module.surjective_of_forall_quotient_maximal (dToCocycles C j) (fun I hI ↦ by
              letI : Field (R ⧸ I) := @Ideal.Quotient.field _ _ I hI
              exact surjective_baseChange_dToCocycles_of_exactAtSucc
                C hflat hvan j habove (R ⧸ I) (hfib (R ⧸ I) j))
          have hexj : ExactAtSucc C j :=
            (exactAtSucc_iff_surjective_dToCocycles C j).mpr hsurj
          refine ⟨hexj, ?_⟩
          exact Module.finitePresentation_of_projective_of_exact
            (cocyclesSub C j).subtype (dToCocycles C j)
            Subtype.val_injective hsurj (exact_subtype_dToCocycles C j)
  refine ⟨fun j ↦ (key (N + 1) j (by omega)).1, fun i ↦ ?_⟩
  exact (key (N + 1) i (by omega)).2

/-- Arbitrary-base Cohomology and Base Change for a bounded complex of finitely presented
flat modules: field-fibre exactness in positive degrees makes `H⁰` finite projective and
its formation commute with every scalar extension. -/
theorem finite_projective_homologyZero_and_baseChange_of_fibrewise
    (hfp : ∀ p : ℕ, Module.FinitePresentation R (C.X p))
    (hflat : ∀ p : ℕ, Module.Flat R (C.X p)) {N : ℕ}
    (hvan : ∀ p : ℕ, N < p → Subsingleton (C.X p))
    (hfib : ∀ (K : Type u) [Field K] [Algebra R K] (j : ℕ),
      ExactAtSucc (GradedModule.cochainBaseChange K C) j) :
    Module.Finite R (C.homology 0) ∧ Module.Projective R (C.homology 0) ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Nonempty ((A ⊗[R] (C.homology 0)) ≃ₗ[A]
          ((GradedModule.cochainBaseChange A C).homology 0)) := by
  obtain ⟨hex, hfpZ⟩ :=
    exactAtSucc_and_finitePresentation_cocycles_of_fibrewise C hfp hflat hvan hfib
  haveI hfpZ0 : Module.FinitePresentation R (cocyclesSub C 0) := hfpZ 0
  haveI hflatZ0 : Module.Flat R (cocyclesSub C 0) :=
    flat_cocyclesSub hflat hvan (fun i _ ↦ hex i) le_rfl
  haveI hprojZ0 : Module.Projective R (cocyclesSub C 0) :=
    Module.Flat.projective_of_finitePresentation
  haveI hfpH0 : Module.FinitePresentation R (C.homology 0) :=
    Module.FinitePresentation.of_equiv (homologyZeroEquiv C).symm
  have hfinH0 : Module.Finite R (C.homology 0) := inferInstance
  have hprojH0 : Module.Projective R (C.homology 0) :=
    Module.Projective.of_equiv' (homologyZeroEquiv C).symm
  refine ⟨hfinH0, hprojH0, ?_⟩
  intro A _ _
  exact ⟨((homologyZeroEquiv C).baseChange R A).trans
    ((cocyclesBaseChangeEquiv C hflat hvan (fun i ↦ hex i) A 0).trans
      (homologyZeroEquiv (GradedModule.cochainBaseChange A C)).symm)⟩

/-- Arbitrary-base Cohomology and Base Change for a bounded flat complex with finite
positive cohomology and finitely presented `H⁰`.  Unlike the finite-cochain version,
this applies in principle to complexes such as Cech complexes whose terms themselves are
not finite over the base ring. -/
theorem finite_projective_homologyZero_and_baseChange_of_finiteHomology
    (hflat : ∀ p : ℕ, Module.Flat R (C.X p)) {N : ℕ}
    (hvan : ∀ p : ℕ, N < p → Subsingleton (C.X p))
    (hfin : ∀ j : ℕ, Module.Finite R (C.homology (j + 1)))
    (hfp0 : Module.FinitePresentation R (C.homology 0))
    (hfib : ∀ (K : Type u) [Field K] [Algebra R K] (j : ℕ),
      ExactAtSucc (GradedModule.cochainBaseChange K C) j) :
    Module.Finite R (C.homology 0) ∧ Module.Projective R (C.homology 0) ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Nonempty ((A ⊗[R] (C.homology 0)) ≃ₗ[A]
          ((GradedModule.cochainBaseChange A C).homology 0)) := by
  have hex : ∀ j : ℕ, ExactAtSucc C j :=
    exactAtSucc_of_fibrewise C hflat hvan
      (fun j ↦ @finite_cohomologySucc R _ C j (hfin j)) hfib
  haveI hfpH0 : Module.FinitePresentation R (C.homology 0) := hfp0
  haveI hfpZ0 : Module.FinitePresentation R (cocyclesSub C 0) :=
    Module.FinitePresentation.of_equiv (homologyZeroEquiv C)
  haveI hflatZ0 : Module.Flat R (cocyclesSub C 0) :=
    flat_cocyclesSub hflat hvan (fun i _ ↦ hex i) le_rfl
  haveI hprojZ0 : Module.Projective R (cocyclesSub C 0) :=
    Module.Flat.projective_of_finitePresentation
  have hfinH0 : Module.Finite R (C.homology 0) := inferInstance
  have hprojH0 : Module.Projective R (C.homology 0) :=
    Module.Projective.of_equiv (homologyZeroEquiv C).symm
  refine ⟨hfinH0, hprojH0, ?_⟩
  intro A _ _
  exact ⟨((homologyZeroEquiv C).baseChange R A).trans
    ((cocyclesBaseChangeEquiv C hflat hvan (fun i ↦ hex i) A 0).trans
      (homologyZeroEquiv (GradedModule.cochainBaseChange A C)).symm)⟩

/-- Arbitrary-base cohomology and base change for a bounded flat complex with finite
positive homology, without any finiteness assumption on `H⁰`.  Field-fibre exactness
makes the complex exact in positive degrees; consequently `H⁰` is flat and commutes with
every scalar extension. -/
theorem flat_homologyZero_and_baseChange_of_finiteHomology
    (hflat : ∀ p : ℕ, Module.Flat R (C.X p)) {N : ℕ}
    (hvan : ∀ p : ℕ, N < p → Subsingleton (C.X p))
    (hfin : ∀ j : ℕ, Module.Finite R (C.homology (j + 1)))
    (hfib : ∀ (K : Type u) [Field K] [Algebra R K] (j : ℕ),
      ExactAtSucc (GradedModule.cochainBaseChange K C) j) :
    Module.Flat R (C.homology 0) ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Nonempty ((A ⊗[R] (C.homology 0)) ≃ₗ[A]
          ((GradedModule.cochainBaseChange A C).homology 0)) := by
  have hex : ∀ j : ℕ, ExactAtSucc C j :=
    exactAtSucc_of_fibrewise C hflat hvan
      (fun j ↦ @finite_cohomologySucc R _ C j (hfin j)) hfib
  have hflatZ0 : Module.Flat R (cocyclesSub C 0) :=
    flat_cocyclesSub hflat hvan (fun i _ ↦ hex i) le_rfl
  letI : Module.Flat R (cocyclesSub C 0) := hflatZ0
  refine ⟨Module.Flat.of_linearEquiv (homologyZeroEquiv C), ?_⟩
  intro A _ _
  exact ⟨((homologyZeroEquiv C).baseChange R A).trans
    ((cocyclesBaseChangeEquiv C hflat hvan (fun i ↦ hex i) A 0).trans
      (homologyZeroEquiv (GradedModule.cochainBaseChange A C)).symm)⟩

/-- A bounded finite-projective complex which computes `C` and continues to compute it after
every coefficient change.  This is the precise strictly-perfect output needed from
relative perfectness; it does not require the ordinary Cech cochains of `C` to be finite. -/
structure StrictlyPerfectReplacement where
  /-- The bounded finite-projective replacement complex. -/
  complex : CochainComplex (ModuleCat.{u} R) ℕ
  /-- An upper bound for its nonzero cochain degrees. -/
  bound : ℕ
  /-- The replacement is bounded above. -/
  bounded : ∀ p : ℕ, bound < p → Subsingleton (complex.X p)
  /-- Every cochain module of the replacement is finite. -/
  finite : ∀ p : ℕ, Module.Finite R (complex.X p)
  /-- Every cochain module of the replacement is projective. -/
  projective : ∀ p : ℕ, Module.Projective R (complex.X p)
  /-- The replacement computes the homology of the original complex over the base. -/
  homologyEquiv : ∀ i : ℕ,
    ((complex.homology i : ModuleCat.{u} R) : Type u) ≃ₗ[R]
      ((C.homology i : ModuleCat.{u} R) : Type u)
  /-- The homology comparison remains an equivalence after every coefficient change. -/
  baseChangeHomologyEquiv : ∀ (A : Type u) [CommRing A] [Algebra R A] (i : ℕ),
    ((((GradedModule.cochainBaseChange A complex).homology i : ModuleCat.{u} A) : Type u)
      ≃ₗ[A]
    (((GradedModule.cochainBaseChange A C).homology i : ModuleCat.{u} A) : Type u))

/-- A universally strictly-perfect replacement turns field-fibre exactness into the
proper-finiteness hypotheses needed for arbitrary-base Cohomology and Base Change. -/
theorem finiteHomology_and_finitePresentation_homologyZero_of_strictlyPerfectReplacement
    (E : StrictlyPerfectReplacement C)
    (hfib : ∀ (K : Type u) [Field K] [Algebra R K] (j : ℕ),
      ExactAtSucc (GradedModule.cochainBaseChange K C) j) :
    (∀ j : ℕ, Module.Finite R (C.homology (j + 1))) ∧
      Module.FinitePresentation R (C.homology 0) := by
  let D := E.complex
  have hfpD : ∀ p : ℕ, Module.FinitePresentation R (D.X p) := by
    intro p
    letI : Module.Finite R (D.X p) := E.finite p
    letI : Module.Projective R (D.X p) := E.projective p
    exact Module.finitePresentation_of_projective R _
  have hflatD : ∀ p : ℕ, Module.Flat R (D.X p) := by
    intro p
    letI : Module.Projective R (D.X p) := E.projective p
    exact Module.Flat.of_projective
  have hfibD : ∀ (K : Type u) [Field K] [Algebra R K] (j : ℕ),
      ExactAtSucc (GradedModule.cochainBaseChange K D) j := by
    intro K _ _ j
    rw [← subsingleton_homology_succ_iff]
    haveI : Subsingleton
        ((GradedModule.cochainBaseChange K C).homology (j + 1)) := by
      rw [subsingleton_homology_succ_iff]
      exact hfib K j
    exact (E.baseChangeHomologyEquiv K (j + 1)).toEquiv.subsingleton
  obtain ⟨hexD, hfpZD⟩ :=
    exactAtSucc_and_finitePresentation_cocycles_of_fibrewise
      D hfpD hflatD E.bounded hfibD
  constructor
  · intro j
    haveI hsubD : Subsingleton (D.homology (j + 1)) := by
      rw [subsingleton_homology_succ_iff]
      exact hexD j
    haveI hfinD : Module.Finite R (D.homology (j + 1)) := inferInstance
    exact Module.Finite.equiv (E.homologyEquiv (j + 1))
  · haveI hfpZD0 : Module.FinitePresentation R (cocyclesSub D 0) := hfpZD 0
    haveI hfpD0 : Module.FinitePresentation R (D.homology 0) :=
      Module.FinitePresentation.of_equiv (homologyZeroEquiv D).symm
    exact Module.FinitePresentation.of_equiv (E.homologyEquiv 0)

/-- Arbitrary-base Cohomology and Base Change for a bounded flat complex admitting a
universally strictly-perfect replacement. -/
theorem finite_projective_homologyZero_and_baseChange_of_strictlyPerfectReplacement
    (E : StrictlyPerfectReplacement C)
    (hflat : ∀ p : ℕ, Module.Flat R (C.X p)) {N : ℕ}
    (hvan : ∀ p : ℕ, N < p → Subsingleton (C.X p))
    (hfib : ∀ (K : Type u) [Field K] [Algebra R K] (j : ℕ),
      ExactAtSucc (GradedModule.cochainBaseChange K C) j) :
    Module.Finite R (C.homology 0) ∧ Module.Projective R (C.homology 0) ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Nonempty ((A ⊗[R] (C.homology 0)) ≃ₗ[A]
          ((GradedModule.cochainBaseChange A C).homology 0)) := by
  obtain ⟨hfin, hfp0⟩ :=
    finiteHomology_and_finitePresentation_homologyZero_of_strictlyPerfectReplacement
      C E hfib
  exact finite_projective_homologyZero_and_baseChange_of_finiteHomology
    C hflat hvan hfin hfp0 hfib

end CochainComplex

namespace GradedModule

variable {R : Type u} [CommRing R] {n : ℕ} (M : GradedModule R n) (d : ℤ)

/-- The homology comparison induced by coefficient change of the Cech complex, without
any noetherian hypothesis on the source ring. -/
noncomputable def cechHgrBaseChangeHomologyIso_arbitrary
    (A : Type u) [CommRing A] [Algebra R A] (q : ℕ) :
    ((M.baseChange A).cechComplex d).homology q ≅
      (cochainBaseChange A (M.cechComplex d)).homology q :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.up ℕ) q).mapIso
    (cechComplexBaseChangeIso A M d)

/-- Fibrewise vanishing translated into exactness of the coefficient-changed Cech
complex, over an arbitrary source ring. -/
lemma exactAtSucc_cochainBaseChange_of_subsingleton_arbitrary
    (A : Type u) [CommRing A] [Algebra R A] (j : ℕ)
    (h : Subsingleton (((M.baseChange A).cechHgr (j + 1)).obj d)) :
    CochainComplex.ExactAtSucc (cochainBaseChange A (M.cechComplex d)) j := by
  rw [← CochainComplex.subsingleton_homology_succ_iff]
  haveI : Subsingleton (((M.baseChange A).cechComplex d).homology (j + 1)) := h
  exact (cechHgrBaseChangeHomologyIso_arbitrary M d A (j + 1)
    ).toLinearEquiv.toEquiv.symm.subsingleton

/-- Arbitrary-base Cohomology and Base Change for a graded Cech complex with finite
positive cohomology and finitely presented `H⁰`.  This is the coherent-enough form:
the Cech cochains themselves are allowed to be infinite over the base. -/
theorem finite_projective_cechHgr_zero_and_baseChange_of_finiteHomology
    (hflat : ∀ p : ℕ, Module.Flat R ((M.cechComplex d).X p))
    (hfin : ∀ i : ℕ, 1 ≤ i → Module.Finite R ((M.cechHgr i).obj d))
    (hfp0 : Module.FinitePresentation R ((M.cechHgr 0).obj d))
    (hfib : ∀ (K : Type u) [Field K] [Algebra R K] (i : ℕ), 1 ≤ i →
      Subsingleton (((M.baseChange K).cechHgr i).obj d)) :
    Module.Finite R ((M.cechHgr 0).obj d) ∧
      Module.Projective R ((M.cechHgr 0).obj d) ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Nonempty ((A ⊗[R] ((M.cechHgr 0).obj d)) ≃ₗ[A]
          (((M.baseChange A).cechHgr 0).obj d)) := by
  have hbound : ∀ p : ℕ, n < p → Subsingleton ((M.cechComplex d).X p) := by
    intro p hp
    have h := isZero_cechCochain M hp d
    rw [ModuleCat.isZero_iff_subsingleton] at h
    exact h
  have hfin' : ∀ j : ℕ, Module.Finite R ((M.cechComplex d).homology (j + 1)) :=
    fun j ↦ hfin (j + 1) (by omega)
  have hfp0' : Module.FinitePresentation R ((M.cechComplex d).homology 0) := hfp0
  have hexK : ∀ (K : Type u) [Field K] [Algebra R K] (j : ℕ),
      CochainComplex.ExactAtSucc (cochainBaseChange K (M.cechComplex d)) j := by
    intro K _ _ j
    exact exactAtSucc_cochainBaseChange_of_subsingleton_arbitrary M d K j
      (hfib K (j + 1) (by omega))
  obtain ⟨hfinite, hprojective, hbc⟩ :=
    CochainComplex.finite_projective_homologyZero_and_baseChange_of_finiteHomology
      (M.cechComplex d) hflat hbound hfin' hfp0' hexK
  refine ⟨hfinite, hprojective, ?_⟩
  intro A _ _
  obtain ⟨e⟩ := hbc A
  exact ⟨e.trans
    (cechHgrBaseChangeHomologyIso_arbitrary M d A 0).symm.toLinearEquiv⟩

/-- Arbitrary-base cohomology and base change for a graded Cech complex with finite
positive cohomology, without a finite-presentation assumption on `H⁰`.  The conclusion
is precisely the flatness and universal base-change part; finiteness and constant rank can
then be supplied by the geometric presentation. -/
theorem flat_cechHgr_zero_and_baseChange_of_finiteHomology
    (hflat : ∀ p : ℕ, Module.Flat R ((M.cechComplex d).X p))
    (hfin : ∀ i : ℕ, 1 ≤ i → Module.Finite R ((M.cechHgr i).obj d))
    (hfib : ∀ (K : Type u) [Field K] [Algebra R K] (i : ℕ), 1 ≤ i →
      Subsingleton (((M.baseChange K).cechHgr i).obj d)) :
    Module.Flat R ((M.cechHgr 0).obj d) ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Nonempty ((A ⊗[R] ((M.cechHgr 0).obj d)) ≃ₗ[A]
          (((M.baseChange A).cechHgr 0).obj d)) := by
  have hbound : ∀ p : ℕ, n < p → Subsingleton ((M.cechComplex d).X p) := by
    intro p hp
    have h := isZero_cechCochain M hp d
    rw [ModuleCat.isZero_iff_subsingleton] at h
    exact h
  have hfin' : ∀ j : ℕ, Module.Finite R ((M.cechComplex d).homology (j + 1)) :=
    fun j ↦ hfin (j + 1) (by omega)
  have hexK : ∀ (K : Type u) [Field K] [Algebra R K] (j : ℕ),
      CochainComplex.ExactAtSucc (cochainBaseChange K (M.cechComplex d)) j := by
    intro K _ _ j
    exact exactAtSucc_cochainBaseChange_of_subsingleton_arbitrary M d K j
      (hfib K (j + 1) (by omega))
  obtain ⟨hflat0, hbc⟩ :=
    CochainComplex.flat_homologyZero_and_baseChange_of_finiteHomology
      (M.cechComplex d) hflat hbound hfin' hexK
  refine ⟨hflat0, ?_⟩
  intro A _ _
  obtain ⟨e⟩ := hbc A
  exact ⟨e.trans
    (cechHgrBaseChangeHomologyIso_arbitrary M d A 0).symm.toLinearEquiv⟩

/-- Arbitrary-base Cohomology and Base Change for a graded Cech complex whose cochain
modules are finitely presented and flat.  The finite-presentation assumption is explicit:
ordinary projective-space Cech cochains need not satisfy it, so applying this theorem to
geometry requires a separate finite-complex replacement. -/
theorem finite_projective_cechHgr_zero_and_baseChange_of_finitePresentationCochains
    (hfp : ∀ p : ℕ, Module.FinitePresentation R ((M.cechComplex d).X p))
    (hflat : ∀ p : ℕ, Module.Flat R ((M.cechComplex d).X p))
    (hfib : ∀ (K : Type u) [Field K] [Algebra R K] (i : ℕ), 1 ≤ i →
      Subsingleton (((M.baseChange K).cechHgr i).obj d)) :
    Module.Finite R ((M.cechHgr 0).obj d) ∧
      Module.Projective R ((M.cechHgr 0).obj d) ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Nonempty ((A ⊗[R] ((M.cechHgr 0).obj d)) ≃ₗ[A]
          (((M.baseChange A).cechHgr 0).obj d)) := by
  have hbound : ∀ p : ℕ, n < p → Subsingleton ((M.cechComplex d).X p) := by
    intro p hp
    have h := isZero_cechCochain M hp d
    rw [ModuleCat.isZero_iff_subsingleton] at h
    exact h
  have hexK : ∀ (K : Type u) [Field K] [Algebra R K] (j : ℕ),
      CochainComplex.ExactAtSucc (cochainBaseChange K (M.cechComplex d)) j := by
    intro K _ _ j
    exact exactAtSucc_cochainBaseChange_of_subsingleton_arbitrary M d K j
      (hfib K (j + 1) (by omega))
  obtain ⟨hfin, hproj, hbc⟩ :=
    CochainComplex.finite_projective_homologyZero_and_baseChange_of_fibrewise
      (M.cechComplex d) hfp hflat hbound hexK
  refine ⟨hfin, hproj, ?_⟩
  intro A _ _
  obtain ⟨e⟩ := hbc A
  exact ⟨e.trans
    (cechHgrBaseChangeHomologyIso_arbitrary M d A 0).symm.toLinearEquiv⟩

end GradedModule

-- The explicit chart comparison and twist trivialization are elaboration-heavy.
set_option synthInstance.maxHeartbeats 1000000 in
-- The explicit polynomial `Proj` twist instances make typeclass search expensive.
/-- The single-variable localization of the kernel-route model is degreewise flat over an
arbitrary base ring when the quotient sheaf is flat.  This removes the noetherian binder
from `Proj.isFlat_loc_kernelQuotientModule`; its proof only uses the affine chart
comparison, which is now available over arbitrary rings. -/
theorem _root_.AlgebraicGeometry.Proj.isFlat_loc_kernelQuotientModule_arbitrary
    {R : Type u} [CommRing R] {n : ℕ}
    {F F' : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules}
    (p : F ⟶ F') [Epi p] (i : Fin (n + 1))
    [∀ e : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) F e).IsQuasicoherent]
    [∀ e : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) F' e).IsQuasicoherent]
    [∀ e : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (kernel p) e).IsQuasicoherent]
    (hflat : F'.FlatOver (projSpecπ n R)) :
    GradedModule.IsFlat
      ((Proj.kernelQuotientModule
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (projSpecπ n R) (stdVars n R) p).loc [i]) := by
  intro e
  have hcover := top_le_iSup_basicOpen_stdVars n R
  letI := Scheme.Modules.openSectionsModuleOver (projSpecπ n R)
    (twistModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) F' e)
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      ((stdVars n R i : MvPolynomial (Fin (n + 1)) R)))
  letI := Scheme.Modules.openSectionsModuleOver (projSpecπ n R) F'
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      ((stdVars n R i : MvPolynomial (Fin (n + 1)) R)))
  haveI hF : Module.Flat R
      Γ(F', Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        ((stdVars n R i : MvPolynomial (Fin (n + 1)) R))) :=
    Scheme.Modules.flat_openSections_of_flatOver (projSpecπ n R) F' hflat
      ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) _,
        Proj.isAffineOpen_basicOpen _ _ (stdVars n R i).2 Nat.one_pos⟩
  haveI hT : Module.Flat R
      Γ(twistModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) F' e,
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
          ((stdVars n R i : MvPolynomial (Fin (n + 1)) R))) :=
    Proj.flat_openSections_twistModule_basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (projSpecπ n R) F' (stdVars n R) i e hF
  refine Module.Flat.of_linearEquiv
    ((LinearEquiv.ofBijective _
      (Proj.bijective_locMap_kernelQuotientToGammaStar (projSpecπ n R) p i e)).trans
      (LinearEquiv.ofBijective
        (Proj.chartColimitMap (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
          (projSpecπ n R) F' (stdVars n R) i e)
        (Proj.bijective_chartColimitMap
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
          (projSpecπ n R) F' (stdVars n R) i hcover e)))

/-- The kernel-route model computes all graded Cech cohomology groups of the quotient
sheaf, not only `H^0`. -/
theorem _root_.AlgebraicGeometry.Proj.isIso_cechHgrMap_kernelQuotientToGammaStar_all
    {R : Type u} [CommRing R] {n : ℕ}
    (pi : Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) ⟶
      Spec (CommRingCat.of R))
    {F F' : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules}
    (p : F ⟶ F') [Epi p]
    [∀ e : ℤ, (twistModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      F e).IsQuasicoherent]
    [∀ e : ℤ, (twistModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      F' e).IsQuasicoherent]
    [∀ e : ℤ, (twistModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (kernel p) e).IsQuasicoherent]
    (q : ℕ) (d : ℤ) :
    IsIso ((GradedModule.cechHgrMap
      (Proj.kernelQuotientToGammaStar
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) pi (stdVars n R) p) q).app d) := by
  refine GradedModule.isIso_cechHgrMap_app_of_singleton_bijective _ q d (fun a t => ?_)
  exact Proj.bijective_locMap_kernelQuotientToGammaStar pi p a (d + (t : ℤ))

/-- Base change of the kernel-route comparison computes all graded Cech cohomology groups,
not only `H^0`. -/
theorem isIso_cechHgrMap_baseChangeMap_kernelQuotientToGammaStar_all
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {n : ℕ}
    {E G : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules}
    (p : E ⟶ G) [Epi p]
    [∀ e : ℤ, (twistModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      E e).IsQuasicoherent]
    [∀ e : ℤ, (twistModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      G e).IsQuasicoherent]
    [∀ e : ℤ, (twistModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (kernel p) e).IsQuasicoherent]
    (q : ℕ) (d : ℤ) :
    IsIso ((GradedModule.cechHgrMap (GradedModule.baseChangeMap
      (Proj.kernelQuotientToGammaStar _ (projSpecπ n R) (stdVars n R) p) A) q).app d) := by
  refine GradedModule.isIso_cechHgrMap_app_of_singleton_bijective _ q d (fun a t => ?_)
  exact GradedModule.bijective_locMap_baseChangeMap_app A _ [a] (d + (t : ℤ))
    (Proj.bijective_locMap_kernelQuotientToGammaStar
      (projSpecπ n R) p a (d + (t : ℤ)))

set_option synthInstance.maxHeartbeats 1000000 in
-- The comparison simultaneously elaborates localization, base change, and Cech homology.
/-- The `Gamma_*` base-change comparison is an isomorphism on all graded Cech cohomology
groups in nonnegative degrees. -/
theorem isIso_cechHgrMap_gammaStarBaseChangeHom_app_all
    {R A : Type u} [CommRing R] [CommRing A] (n : ℕ) (f : R →+* A)
    (F : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules)
    [F.IsFinitePresentation] (q d : ℕ) :
    letI : Algebra R A := f.toAlgebra
    IsIso ((GradedModule.cechHgrMap (gammaStarBaseChangeHom n f F) q).app (d : ℤ)) := by
  letI : Algebra R A := f.toAlgebra
  refine GradedModule.isIso_cechHgrMap_app_of_singleton_bijective _ q (d : ℤ)
    (fun a t => ?_)
  refine GradedModule.bijective_locMap_app_of_eq _ [a] ?_
    (bijective_locMap_gammaStarBaseChangeHom_app n f F a (d + t))
  push_cast
  ring

set_option synthInstance.maxHeartbeats 1000000 in
-- The uniform kernel construction creates many explicit twist instances.
set_option maxHeartbeats 2000000 in
-- The fibrewise comparison combines two long Cech-homology isomorphisms.
/-- A single degree, depending only on `(n,r,l,P)`, kills the higher cohomology of every
field base change of the kernel-route quotient model of a twisted-free Quot family. -/
theorem exists_bound_subsingleton_cechHgr_kernelQuotientModule_baseChange
    (n r : ℕ) (hn : 0 < n) (l : ℤ) (P : Polynomial ℚ) :
    ∃ d₀ : ℤ, 0 ≤ d₀ ∧ ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
      (Q : (Scheme.projectiveSpaceOver n (Spec (.of R))).Modules)
      (_ : Q.IsFinitePresentation)
      (q : (∐ fun _ : ULift.{u} (Fin r) ↦
        Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l)) ⟶ Q)
      (_ : Epi q)
      (_ : Q.FlatOver (Scheme.projectiveSpaceOverπ n (Spec (.of R))))
      (_ : Scheme.HasFiberwiseHilbertPolynomial Q P)
      (d : ℕ), d₀ ≤ (d : ℤ) →
      let p := (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).map q
      let M := Proj.kernelQuotientModule
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (projSpecπ n R) (stdVars n R) p
      ∀ (κ : Type u) [Field κ] [Algebra R κ] (i : ℕ), 1 ≤ i →
        Subsingleton (((M.baseChange κ).cechHgr i).obj (d : ℤ)) := by
  obtain ⟨dK, hdK0, hK⟩ :=
    exists_bound_subsingleton_cechHgr_gammaStar_kernel n r l P
  refine ⟨max dK (max (l - (n : ℤ)) 0), by omega, ?_⟩
  intro R _ _ Q hQfp q hq hflat hHP d hd
  haveI := hQfp
  haveI := hq
  haveI hAmb : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l)).IsFinitePresentation :=
    Scheme.twistedFreeAmbient_isFinitePresentation n (Spec (.of R)) l r
  let E := projAmbient n r l (R := R)
  let G := (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q
  let p := (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).map q
  haveI hp : Epi p := inferInstance
  haveI hEfp : E.IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  haveI hGfp : G.IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  haveI hKfp : (kernel p).IsFinitePresentation :=
    Scheme.Modules.kernel_isFinitePresentation p
  haveI hEqc : ∀ e : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) E e).IsQuasicoherent :=
    fun e ↦ twistModule_std_isQuasicoherent _ e
  haveI hGqc : ∀ e : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) G e).IsQuasicoherent :=
    fun e ↦ twistModule_std_isQuasicoherent _ e
  haveI hKqc : ∀ e : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (kernel p) e).IsQuasicoherent :=
    fun e ↦ twistModule_std_isQuasicoherent _ e
  let Kγ := Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    (projSpecπ n R) (kernel p) (stdVars n R)
  let M := Proj.kernelQuotientModule
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    (projSpecπ n R) (stdVars n R) p
  have hGflat : G.FlatOver (projSpecπ n R) :=
    Scheme.Modules.FlatOver.pullback_isIso (projectiveSpaceOverSpecIso n R).inv Q
      (projectiveSpaceOverSpecIso_inv_comp_projectiveSpaceOverπ n R) hflat
  have hEflat : GradedModule.IsFlat (Proj.gammaStar
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (projSpecπ n R)
      E (stdVars n R)) :=
    isFlat_gammaStarPullTwistedFree n R hn (-l) r
  have hKflatC : ∀ s : ℕ, Module.Flat R ((Kγ.cechComplex (d : ℤ)).X s) := by
    intro s
    refine GradedModule.flat_cechCochain_of_flat_loc _ (fun a ↦ ?_) s (d : ℤ)
    refine GradedModule.IsFlat.of_shortExact
      (GradedModule.loc_shortExact _ (l := [a])
        (Proj.shortExact_gammaStar_toCoker_kernel (projSpecπ n R) p))
      (fun e ↦ hEflat.flat_loc [a] e)
      (Proj.isFlat_loc_kernelQuotientModule p a hGflat)
  have hKvan : ∀ i : ℕ, 1 ≤ i →
      Subsingleton ((Kγ.cechHgr i).obj (d : ℤ)) := by
    intro i hi
    exact hK R Q hQfp hAmb p hp hflat hHP i hi (d : ℤ)
      (le_trans (le_max_left _ _) hd)
  dsimp only
  intro κ _ hAlg i hi
  letI : Algebra R κ := hAlg
  have halg : (algebraMap R κ).toAlgebra = hAlg :=
    Algebra.algebra_ext _ _ (fun x ↦ rfl)
  let pκ := (Scheme.Modules.pullback (coeffMap n (algebraMap R κ))).map p
  haveI hpκ : Epi pκ := inferInstance
  haveI hEκfp : ((Scheme.Modules.pullback (coeffMap n (algebraMap R κ))).obj E
      ).IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  haveI hGκfp : ((Scheme.Modules.pullback (coeffMap n (algebraMap R κ))).obj G
      ).IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  haveI hEκqc : ∀ e : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) κ)
      ((Scheme.Modules.pullback (coeffMap n (algebraMap R κ))).obj E)
      e).IsQuasicoherent := fun e ↦ twistModule_std_isQuasicoherent _ e
  haveI hGκqc : ∀ e : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) κ)
      ((Scheme.Modules.pullback (coeffMap n (algebraMap R κ))).obj G)
      e).IsQuasicoherent := fun e ↦ twistModule_std_isQuasicoherent _ e
  haveI hKκfp : (kernel pκ).IsFinitePresentation :=
    Scheme.Modules.kernel_isFinitePresentation pκ
  haveI hKκqc : ∀ e : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) κ) (kernel pκ)
      e).IsQuasicoherent := fun e ↦ twistModule_std_isQuasicoherent _ e
  haveI hKbc : Subsingleton (((Kγ.baseChange κ).cechHgr (i + 1)).obj (d : ℤ)) :=
    GradedModule.subsingleton_cechHgr_baseChange_of_flatCochain
      Kγ (d : ℤ) κ hKflatC hKvan (i + 1) (by omega)
  haveI hKκ : Subsingleton (((Proj.gammaStar
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) κ) (projSpecπ n κ)
      (kernel pκ) (stdVars n κ)).cechHgr (i + 1)).obj (d : ℤ)) := by
    haveI := isIso_cechHgrMap_kernelFibreCompare_app n (algebraMap R κ) p
      hGflat (i + 1) d
    let eK := (asIso ((GradedModule.cechHgrMap
      (kernelFibreCompare n (algebraMap R κ) p) (i + 1)).app (d : ℤ))).toLinearEquiv
    rw [halg] at eK
    exact eK.symm.toEquiv.subsingleton
  haveI hEκ : Subsingleton (((Proj.gammaStar
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) κ) (projSpecπ n κ)
      ((Scheme.Modules.pullback (coeffMap n (algebraMap R κ))).obj E)
      (stdVars n κ)).cechHgr i).obj (d : ℤ)) := by
    haveI : Subsingleton (((((GradedModule.structureModule κ n).twist (-l)).pow r
      ).cechHgr i).obj (d : ℤ)) :=
      GradedModule.subsingleton_cechHgr_free (-l) r i hi (d : ℤ)
        (by omega)
    let eE := GradedModule.isoApp (GradedModule.cechHgrIso
      (gammaStarFibreTwistedFreeIso n r l (algebraMap R κ) hn) i) (d : ℤ)
    exact eE.toLinearEquiv.toEquiv.subsingleton
  haveI hQκ : Subsingleton (((Proj.gammaStar
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) κ) (projSpecπ n κ)
      ((Scheme.Modules.pullback (coeffMap n (algebraMap R κ))).obj G)
      (stdVars n κ)).cechHgr i).obj (d : ℤ)) := by
    let Mκ := Proj.kernelQuotientModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) κ)
      (projSpecπ n κ) (stdVars n κ) pκ
    haveI hMκ : Subsingleton ((Mκ.cechHgr i).obj (d : ℤ)) := by
      exact GradedModule.subsingleton_of_exact _ _
        (GradedModule.cech_exact_map_δ
          (Proj.shortExact_gammaStar_toCoker_kernel (projSpecπ n κ) pκ)
          i (d : ℤ))
    haveI := Proj.isIso_cechHgrMap_kernelQuotientToGammaStar_all
      (projSpecπ n κ) pκ i (d : ℤ)
    exact (asIso ((GradedModule.cechHgrMap
      (Proj.kernelQuotientToGammaStar _ (projSpecπ n κ) (stdVars n κ) pκ)
      i).app (d : ℤ))).symm.toLinearEquiv.toEquiv.subsingleton
  haveI hGbc : Subsingleton ((((Proj.gammaStar
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (projSpecπ n R)
      G (stdVars n R)).baseChange κ).cechHgr i).obj (d : ℤ)) := by
    haveI := isIso_cechHgrMap_gammaStarBaseChangeHom_app_all
      n (algebraMap R κ) G i d
    let eG := (asIso ((GradedModule.cechHgrMap
      (gammaStarBaseChangeHom n (algebraMap R κ) G) i).app (d : ℤ))).toLinearEquiv
    rw [halg] at eG
    exact eG.toEquiv.subsingleton
  haveI := isIso_cechHgrMap_baseChangeMap_kernelQuotientToGammaStar_all
    (A := κ) p i (d : ℤ)
  exact (asIso ((GradedModule.cechHgrMap (GradedModule.baseChangeMap
    (Proj.kernelQuotientToGammaStar _ (projSpecπ n R) (stdVars n R) p) κ) i
    ).app (d : ℤ))).toLinearEquiv.toEquiv.subsingleton

namespace Cohomology

variable {K : Type u} [Field K] (C : Cohomology K) {n : ℕ}

/-- Eventual agreement of `h^0` with `P` identifies the Cech Euler-characteristic
polynomial with `P` in every degree. -/
theorem hasHilbertPolynomial_of_eventually_h_zero_eq
    (hC : C.HasInfiniteBaseChange) (M : GradedModule K n)
    (hM : C.IsCoherent M) (P : Polynomial ℚ)
    (h : ∀ᶠ d : ℕ in Filter.atTop,
      (C.h M 0 (d : ℤ) : ℚ) = P.eval (d : ℚ)) :
    C.HasHilbertPolynomial M P := by
  obtain ⟨P', hP'⟩ := C.exists_hasHilbertPolynomial hC M hM
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
  obtain ⟨D, hD⟩ := C.eventually_chi_eq_h_zero hM
  have hPP : P' = P := Polynomial.eq_of_eventually_intCast_eval_eq
      (max (max D (N : ℤ)) 0) (fun d hd => by
        have hdD : D ≤ d := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hd)
        have hdN : (N : ℤ) ≤ d :=
          le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hd)
        have hd0 : 0 ≤ d := le_trans (le_max_right _ _) hd
        rw [← hP' d, hD d hdD]
        have hn := hN d.toNat (by omega)
        rw [show ((d.toNat : ℕ) : ℤ) = d from Int.toNat_of_nonneg hd0] at hn
        rw [show ((d.toNat : ℕ) : ℚ) = (d : ℚ) by
          rw [show ((d.toNat : ℕ) : ℚ) = ((d.toNat : ℤ) : ℚ) by push_cast; ring,
            Int.toNat_of_nonneg hd0]] at hn
        exact_mod_cast hn)
  simpa [hPP] using hP'

/-- If every positive cohomology group in one degree vanishes, the Euler characteristic
in that degree is the dimension of `H^0`. -/
lemma chi_eq_h_zero_of_subsingleton (M : GradedModule K n) (d : ℤ)
    (hvan : ∀ i : ℕ, 1 ≤ i → Subsingleton ((C.Hgr M i).obj d)) :
    C.chi M d = (C.h M 0 d : ℤ) := by
  rw [Cohomology.chi, Finset.sum_eq_single 0]
  · simp
  · intro i _ hi
    rw [C.h_eq_zero_of_subsingleton (hvan i (by omega))]
    ring
  · intro h0
    exact absurd (Finset.mem_range.mpr (by omega)) h0

end Cohomology

/-- Degreewise comparison between graded Cech `H⁰` and actual twisted global sections,
including all field-valued coefficient changes.  Unlike
`RelativeCohomology.SchemeGlobalSectionsComparison`, this small interface is available over
an arbitrary commutative base ring. -/
structure GradedModule.CechSchemeGlobalSectionsComparison
    {R : Type u} [CommRing R] {n : ℕ} (M : GradedModule R n)
    (Q : (Scheme.projectiveSpaceOver n (Spec (.of R))).Modules) : Type (u + 1) where
  /-- Degree from which the comparisons are supplied. -/
  bound : ℕ
  /-- Graded Cech `H⁰` computes twisted global sections over the base. -/
  globalSectionsIso : ∀ d : ℕ, bound ≤ d →
    letI := Scheme.Modules.globalSectionsModule
      (Scheme.projectiveSpaceOverπ n (Spec (.of R)))
      (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))
    ((M.cechHgr 0).obj (d : ℤ)) ≃ₗ[R]
      Scheme.Modules.projectiveSpaceTwistedGlobalSections Q (d : ℤ)
  /-- The same comparison after every field-valued coefficient change. -/
  fibreGlobalSectionsIso : ∀ (K : Type u) [Field K] (f : R →+* K) (d : ℕ), bound ≤ d →
    letI : Algebra R K := f.toAlgebra
    let QK := Scheme.Modules.projectiveSpaceBaseChangeOfRingHom Q f
    letI := Scheme.Modules.globalSectionsModule
      (Scheme.projectiveSpaceOverπ n (Spec (.of K)))
      (Scheme.projectiveSpaceOverTwistModule QK (d : ℤ))
    (((M.baseChange K).cechHgr 0).obj (d : ℤ)) ≃ₗ[K]
      Scheme.Modules.projectiveSpaceTwistedGlobalSections QK (d : ℤ)

set_option synthInstance.maxHeartbeats 1000000 in
-- The arbitrary-base comparison elaborates the full polynomial `Proj` normalization.
/-- The kernel-quotient graded model carries the Cech/global-sections comparison over an
arbitrary commutative base ring. -/
noncomputable def cechSchemeGlobalSectionsComparisonQuotientModel_arbitrary
    (n : ℕ) (R : Type u) [CommRing R]
    (Q : (Scheme.projectiveSpaceOver n (Spec (.of R))).Modules)
    [Q.IsFinitePresentation]
    {E : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules}
    (p : E ⟶ (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q)
    [Epi p]
    [∀ e : ℤ, (twistModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      E e).IsQuasicoherent]
    [∀ e : ℤ, (twistModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q)
      e).IsQuasicoherent]
    [∀ e : ℤ, (twistModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (kernel p) e).IsQuasicoherent] :
    GradedModule.CechSchemeGlobalSectionsComparison
      (Proj.kernelQuotientModule
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (projSpecπ n R) (stdVars n R) p) Q where
  bound := 0
  globalSectionsIso d _ :=
    cechHgrZeroQuotientModelGlobalSectionsEquiv n R Q p (d : ℤ)
  fibreGlobalSectionsIso K _ f d _ := by
    letI : Algebra R K := f.toAlgebra
    haveI := isIso_cechHgrMap_baseChangeMap_kernelQuotientToGammaStar_all_arbitrary
      (A := K) p 0 (d : ℤ)
    haveI : (Scheme.Modules.projectiveSpaceBaseChangeOfRingHom Q f).IsFinitePresentation :=
      Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
    exact (asIso ((GradedModule.cechHgrMap (GradedModule.baseChangeMap
        (Proj.kernelQuotientToGammaStar _ (projSpecπ n R) (stdVars n R) p) K)
        0).app (d : ℤ))).toLinearEquiv.trans
      ((hasGammaStarBaseChangeCechHgrZero_of_isFinitePresentation n R Q K f d).some.trans
        (cechHgrZeroGlobalSectionsEquiv
          (Scheme.Modules.projectiveSpaceBaseChangeOfRingHom Q f) (d : ℤ)))

namespace RelativeCohomology.SchemeGlobalSectionsComparison

variable {R : Type u} [CommRing R] {n : ℕ}
variable {M : GradedModule R n}
variable {Q : (Scheme.projectiveSpaceOver n (Spec (.of R))).Modules}

/-- Once fixed-degree `H⁰` is finite, flat, and compatible with arbitrary coefficient
change, the fibrewise Hilbert polynomial computes its constant stalkwise rank. -/
theorem cechHgr_zero_rankAtStalk_of_finite_flat_baseChange
    (E : GradedModule.CechSchemeGlobalSectionsComparison M Q)
    (hM : GradedModule.IsFG M) (P : Polynomial ℚ)
    (hP : Scheme.HasFiberwiseHilbertPolynomial Q P) (d : ℕ)
    (hfinite0 : Module.Finite R ((M.cechHgr 0).obj (d : ℤ)))
    (hflat0 : Module.Flat R ((M.cechHgr 0).obj (d : ℤ)))
    (hbaseChange0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      Nonempty ((A ⊗[R] ((M.cechHgr 0).obj (d : ℤ))) ≃ₗ[A]
        (((M.baseChange A).cechHgr 0).obj (d : ℤ))))
    (hfib : ∀ (κ : Type u) [Field κ] [Algebra R κ] (i : ℕ), 1 ≤ i →
      Subsingleton (((M.baseChange κ).cechHgr i).obj (d : ℤ))) :
    ∀ p : PrimeSpectrum R,
      Module.rankAtStalk ((M.cechHgr 0).obj (d : ℤ)) p = P.hilbertNatValue d := by
  letI : Module.Finite R ((M.cechHgr 0).obj (d : ℤ)) := hfinite0
  letI : Module.Flat R ((M.cechHgr 0).obj (d : ℤ)) := hflat0
  intro p
  let κ := p.asIdeal.ResidueField
  letI : Field κ := inferInstance
  letI : Algebra R κ := inferInstance
  let f : R →+* κ := algebraMap R κ
  have halg : f.toAlgebra = (‹Algebra R κ›) :=
    Algebra.algebra_ext _ _ (fun x ↦ rfl)
  let Qκ := Scheme.Modules.projectiveSpaceBaseChangeOfRingHom Q f
  letI := Scheme.Modules.globalSectionsModule
    (Scheme.projectiveSpaceOverπ n (Spec (.of κ)))
    (Scheme.projectiveSpaceOverTwistModule Qκ (d : ℤ))
  have hPκ : Scheme.HasHilbertPolynomialOver Qκ P := by
    simpa [Qκ, Scheme.Modules.projectiveSpaceBaseChangeOfRingHom] using
      hP (CommRingCat.of κ) (Field.toIsField κ)
        (Spec.map (CommRingCat.ofHom f))
  have heventual : ∀ᶠ e : ℕ in Filter.atTop,
      (((Cohomology.cech κ).h (M.baseChange κ) 0 (e : ℤ) : ℕ) : ℚ) =
        P.eval (e : ℚ) := by
    filter_upwards [hPκ, Filter.eventually_ge_atTop E.bound] with e he heE
    letI := Scheme.Modules.globalSectionsModule
      (Scheme.projectiveSpaceOverπ n (Spec (.of κ)))
      (Scheme.projectiveSpaceOverTwistModule Qκ (e : ℤ))
    have heiso := E.fibreGlobalSectionsIso κ f e heE
    rw [halg] at heiso
    have heq : (Cohomology.cech κ).h (M.baseChange κ) 0 (e : ℤ) =
        Scheme.hilbertFunctionOver Qκ (e : ℤ) := by
      change Module.finrank κ (((M.baseChange κ).cechHgr 0).obj (e : ℤ)) =
        Module.finrank κ
          (Scheme.Modules.projectiveSpaceTwistedGlobalSections Qκ (e : ℤ))
      simpa only [Qκ] using heiso.finrank_eq
    rw [heq]
    exact he
  have hpoly : (Cohomology.cech κ).HasHilbertPolynomial (M.baseChange κ) P :=
    (Cohomology.cech κ).hasHilbertPolynomial_of_eventually_h_zero_eq
      (Cohomology.hasInfiniteBaseChange_cech κ) (M.baseChange κ)
      (hM.baseChange κ) P heventual
  have hdimQ : (Module.finrank κ
      (((M.baseChange κ).cechHgr 0).obj (d : ℤ)) : ℚ) = P.eval (d : ℚ) := by
    have hp := hpoly (d : ℤ)
    rw [(Cohomology.cech κ).chi_eq_h_zero_of_subsingleton
      (M.baseChange κ) (d : ℤ) (hfib κ)] at hp
    change (Module.finrank κ
      (((M.baseChange κ).cechHgr 0).obj (d : ℤ)) : ℚ) = P.eval (d : ℚ) at hp
    exact hp
  have hnat : P.hilbertNatValue d = Module.finrank κ
      (((M.baseChange κ).cechHgr 0).obj (d : ℤ)) :=
    Polynomial.hilbertNatValue_eq hdimQ
  rw [Module.rankAtStalk_eq p]
  let ebc := Classical.choice (hbaseChange0 κ)
  calc
    Module.finrank κ (p.asIdeal.Fiber ((M.cechHgr 0).obj (d : ℤ))) =
        Module.finrank κ (κ ⊗[R] ((M.cechHgr 0).obj (d : ℤ))) := rfl
    _ = Module.finrank κ (((M.baseChange κ).cechHgr 0).obj (d : ℤ)) :=
      ebc.finrank_eq
    _ = P.hilbertNatValue d := hnat.symm

/-- Fixed-degree Cohomology and Base Change, including the rank dictated by the
fibrewise Hilbert polynomial, over an arbitrary base ring.  Proper finiteness is exposed
as the two hypotheses that the positive Cech cohomology is finite and `H⁰` is finitely
presented; the Cech cochains themselves may be infinite over the base. -/
theorem finite_projective_rank_at_fixed_degree_of_finiteHomology
    (E : GradedModule.CechSchemeGlobalSectionsComparison M Q)
    (hM : GradedModule.IsFG M) (P : Polynomial ℚ)
    (hP : Scheme.HasFiberwiseHilbertPolynomial Q P) (d : ℕ) (hdE : E.bound ≤ d)
    (hflatC : ∀ p : ℕ, Module.Flat R ((M.cechComplex (d : ℤ)).X p))
    (hfin : ∀ i : ℕ, 1 ≤ i →
      Module.Finite R ((M.cechHgr i).obj (d : ℤ)))
    (hfp0 : Module.FinitePresentation R ((M.cechHgr 0).obj (d : ℤ)))
    (hfib : ∀ (κ : Type u) [Field κ] [Algebra R κ] (i : ℕ), 1 ≤ i →
      Subsingleton (((M.baseChange κ).cechHgr i).obj (d : ℤ))) :
    letI := Scheme.Modules.globalSectionsModule
      (Scheme.projectiveSpaceOverπ n (Spec (.of R)))
      (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))
    Module.Finite R (Scheme.Modules.projectiveSpaceTwistedGlobalSections Q (d : ℤ)) ∧
      Module.Projective R (Scheme.Modules.projectiveSpaceTwistedGlobalSections Q (d : ℤ)) ∧
      ∀ p : PrimeSpectrum R,
        Module.rankAtStalk (Scheme.Modules.projectiveSpaceTwistedGlobalSections Q (d : ℤ)) p =
          P.hilbertNatValue d := by
  letI := Scheme.Modules.globalSectionsModule
    (Scheme.projectiveSpaceOverπ n (Spec (.of R)))
    (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))
  let eΓ := E.globalSectionsIso d hdE
  obtain ⟨hfiniteM, hprojectiveM, hbaseChangeM⟩ :=
    GradedModule.finite_projective_cechHgr_zero_and_baseChange_of_finiteHomology
      M (d : ℤ) hflatC hfin hfp0 hfib
  have hfinite : Module.Finite R
      (Scheme.Modules.projectiveSpaceTwistedGlobalSections Q (d : ℤ)) := by
    letI := hfiniteM
    exact Module.Finite.equiv eΓ
  have hprojective : Module.Projective R
      (Scheme.Modules.projectiveSpaceTwistedGlobalSections Q (d : ℤ)) := by
    letI := hprojectiveM
    exact Module.Projective.of_equiv eΓ
  refine ⟨hfinite, hprojective, ?_⟩
  letI := hfinite
  letI := hprojective
  intro p
  let κ := p.asIdeal.ResidueField
  letI : Field κ := inferInstance
  letI : Algebra R κ := inferInstance
  let f : R →+* κ := algebraMap R κ
  have halg : f.toAlgebra = (‹Algebra R κ›) :=
    Algebra.algebra_ext _ _ (fun x ↦ rfl)
  let Qκ := Scheme.Modules.projectiveSpaceBaseChangeOfRingHom Q f
  letI := Scheme.Modules.globalSectionsModule
    (Scheme.projectiveSpaceOverπ n (Spec (.of κ)))
    (Scheme.projectiveSpaceOverTwistModule Qκ (d : ℤ))
  have hPκ : Scheme.HasHilbertPolynomialOver Qκ P := by
    simpa [Qκ, Scheme.Modules.projectiveSpaceBaseChangeOfRingHom] using
      hP (CommRingCat.of κ) (Field.toIsField κ)
        (Spec.map (CommRingCat.ofHom f))
  have heventual : ∀ᶠ e : ℕ in Filter.atTop,
      (((Cohomology.cech κ).h (M.baseChange κ) 0 (e : ℤ) : ℕ) : ℚ) =
        P.eval (e : ℚ) := by
    filter_upwards [hPκ, Filter.eventually_ge_atTop E.bound] with e he heE
    letI := Scheme.Modules.globalSectionsModule
      (Scheme.projectiveSpaceOverπ n (Spec (.of κ)))
      (Scheme.projectiveSpaceOverTwistModule Qκ (e : ℤ))
    have heiso := E.fibreGlobalSectionsIso κ f e heE
    rw [halg] at heiso
    have heq : (Cohomology.cech κ).h (M.baseChange κ) 0 (e : ℤ) =
        Scheme.hilbertFunctionOver Qκ (e : ℤ) := by
      change Module.finrank κ (((M.baseChange κ).cechHgr 0).obj (e : ℤ)) =
        Module.finrank κ
          (Scheme.Modules.projectiveSpaceTwistedGlobalSections Qκ (e : ℤ))
      simpa only [Qκ] using heiso.finrank_eq
    rw [heq]
    exact he
  have hpoly : (Cohomology.cech κ).HasHilbertPolynomial (M.baseChange κ) P :=
    (Cohomology.cech κ).hasHilbertPolynomial_of_eventually_h_zero_eq
      (Cohomology.hasInfiniteBaseChange_cech κ) (M.baseChange κ)
      (hM.baseChange κ) P heventual
  have hdimQ : (Module.finrank κ
      (((M.baseChange κ).cechHgr 0).obj (d : ℤ)) : ℚ) = P.eval (d : ℚ) := by
    have hp := hpoly (d : ℤ)
    rw [(Cohomology.cech κ).chi_eq_h_zero_of_subsingleton
      (M.baseChange κ) (d : ℤ) (hfib κ)] at hp
    change (Module.finrank κ
      (((M.baseChange κ).cechHgr 0).obj (d : ℤ)) : ℚ) = P.eval (d : ℚ) at hp
    exact hp
  have hnat : P.hilbertNatValue d = Module.finrank κ
      (((M.baseChange κ).cechHgr 0).obj (d : ℤ)) :=
    Polynomial.hilbertNatValue_eq hdimQ
  rw [Module.rankAtStalk_eq p]
  let ebc := Classical.choice (hbaseChangeM κ)
  calc
    Module.finrank κ (p.asIdeal.Fiber
        (Scheme.Modules.projectiveSpaceTwistedGlobalSections Q (d : ℤ))) =
        Module.finrank κ (κ ⊗[R]
          (Scheme.Modules.projectiveSpaceTwistedGlobalSections Q (d : ℤ))) := rfl
    _ = Module.finrank κ (κ ⊗[R] ((M.cechHgr 0).obj (d : ℤ))) :=
      (eΓ.symm.baseChange R κ).finrank_eq
    _ = Module.finrank κ (((M.baseChange κ).cechHgr 0).obj (d : ℤ)) :=
      ebc.finrank_eq
    _ = P.hilbertNatValue d := hnat.symm

/-- Fixed-degree cohomology and base change when positive Cech cohomology and `H⁰` are
finite.  Finite presentation of `H⁰` is a conclusion: flatness and base change come from
positive exactness, while constant fibre rank upgrades the finite flat module to a finite
projective module. -/
theorem finite_projective_rank_at_fixed_degree_of_finiteHomology_and_finiteZero
    (E : GradedModule.CechSchemeGlobalSectionsComparison M Q)
    (hM : GradedModule.IsFG M) (P : Polynomial ℚ)
    (hP : Scheme.HasFiberwiseHilbertPolynomial Q P) (d : ℕ) (hdE : E.bound ≤ d)
    (hflatC : ∀ p : ℕ, Module.Flat R ((M.cechComplex (d : ℤ)).X p))
    (hfin : ∀ i : ℕ, 1 ≤ i →
      Module.Finite R ((M.cechHgr i).obj (d : ℤ)))
    (hfinite0 : Module.Finite R ((M.cechHgr 0).obj (d : ℤ)))
    (hfib : ∀ (κ : Type u) [Field κ] [Algebra R κ] (i : ℕ), 1 ≤ i →
      Subsingleton (((M.baseChange κ).cechHgr i).obj (d : ℤ))) :
    letI := Scheme.Modules.globalSectionsModule
      (Scheme.projectiveSpaceOverπ n (Spec (.of R)))
      (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))
    Module.Finite R (Scheme.Modules.projectiveSpaceTwistedGlobalSections Q (d : ℤ)) ∧
      Module.Projective R (Scheme.Modules.projectiveSpaceTwistedGlobalSections Q (d : ℤ)) ∧
      ∀ p : PrimeSpectrum R,
        Module.rankAtStalk (Scheme.Modules.projectiveSpaceTwistedGlobalSections Q (d : ℤ)) p =
          P.hilbertNatValue d := by
  obtain ⟨hflat0, hbaseChange0⟩ :=
    GradedModule.flat_cechHgr_zero_and_baseChange_of_finiteHomology
      M (d : ℤ) hflatC hfin hfib
  have hrank0 := cechHgr_zero_rankAtStalk_of_finite_flat_baseChange
    E hM P hP d hfinite0 hflat0 hbaseChange0 hfib
  have hfp0 : Module.FinitePresentation R ((M.cechHgr 0).obj (d : ℤ)) := by
    letI : Module.Finite R ((M.cechHgr 0).obj (d : ℤ)) := hfinite0
    letI : Module.Flat R ((M.cechHgr 0).obj (d : ℤ)) := hflat0
    exact Module.FinitePresentation.of_finite_of_flat_of_rankAtStalk_eq
      (P.hilbertNatValue d) hrank0
  exact finite_projective_rank_at_fixed_degree_of_finiteHomology
    E hM P hP d hdE hflatC hfin hfp0 hfib

/-- Fixed-degree Cohomology and Base Change, with proper finiteness supplied by a
universally strictly-perfect replacement of the Cech complex.  This is the direct
interface expected from a relative-perfectness or noetherian-approximation theorem. -/
theorem finite_projective_rank_at_fixed_degree_of_strictlyPerfectReplacement
    (E : GradedModule.CechSchemeGlobalSectionsComparison M Q)
    (hM : GradedModule.IsFG M) (P : Polynomial ℚ)
    (hP : Scheme.HasFiberwiseHilbertPolynomial Q P) (d : ℕ) (hdE : E.bound ≤ d)
    (D : CochainComplex.StrictlyPerfectReplacement (M.cechComplex (d : ℤ)))
    (hflatC : ∀ p : ℕ, Module.Flat R ((M.cechComplex (d : ℤ)).X p))
    (hfib : ∀ (κ : Type u) [Field κ] [Algebra R κ] (i : ℕ), 1 ≤ i →
      Subsingleton (((M.baseChange κ).cechHgr i).obj (d : ℤ))) :
    letI := Scheme.Modules.globalSectionsModule
      (Scheme.projectiveSpaceOverπ n (Spec (.of R)))
      (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))
    Module.Finite R (Scheme.Modules.projectiveSpaceTwistedGlobalSections Q (d : ℤ)) ∧
      Module.Projective R (Scheme.Modules.projectiveSpaceTwistedGlobalSections Q (d : ℤ)) ∧
      ∀ p : PrimeSpectrum R,
        Module.rankAtStalk (Scheme.Modules.projectiveSpaceTwistedGlobalSections Q (d : ℤ)) p =
          P.hilbertNatValue d := by
  have hfibC : ∀ (κ : Type u) [Field κ] [Algebra R κ] (j : ℕ),
      CochainComplex.ExactAtSucc
        (GradedModule.cochainBaseChange κ (M.cechComplex (d : ℤ))) j := by
    intro κ _ _ j
    exact GradedModule.exactAtSucc_cochainBaseChange_of_subsingleton_arbitrary
      M (d : ℤ) κ j (hfib κ (j + 1) (by omega))
  obtain ⟨hfinC, hfpC0⟩ :=
    CochainComplex.finiteHomology_and_finitePresentation_homologyZero_of_strictlyPerfectReplacement
      (M.cechComplex (d : ℤ)) D hfibC
  have hfin : ∀ i : ℕ, 1 ≤ i →
      Module.Finite R ((M.cechHgr i).obj (d : ℤ)) := by
    intro i hi
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = j + 1 := ⟨i - 1, by omega⟩
    exact hfinC j
  have hfp0 : Module.FinitePresentation R ((M.cechHgr 0).obj (d : ℤ)) := hfpC0
  exact finite_projective_rank_at_fixed_degree_of_finiteHomology
    E hM P hP d hdE hflatC hfin hfp0 hfib

variable [IsNoetherianRing R]

/-- Fixed-degree Cohomology and Base Change, including the rank dictated by a fibrewise
Hilbert polynomial.  Unlike the eventual package, this theorem takes a uniform
fibre-vanishing hypothesis in the chosen degree. -/
theorem finite_projective_rank_at_fixed_degree
    (E : (RelativeCohomology.cech R).SchemeGlobalSectionsComparison M Q)
    (hM : GradedModule.IsFG M) (P : Polynomial ℚ)
    (hP : Scheme.HasFiberwiseHilbertPolynomial Q P) (d : ℕ) (hdE : E.bound ≤ d)
    (hflatC : ∀ p : ℕ, Module.Flat R ((M.cechComplex (d : ℤ)).X p))
    (hfib : ∀ (κ : Type u) [Field κ] [Algebra R κ] (i : ℕ), 1 ≤ i →
      Subsingleton (((M.baseChange κ).cechHgr i).obj (d : ℤ))) :
    letI := Scheme.Modules.globalSectionsModule
      (Scheme.projectiveSpaceOverπ n (Spec (.of R)))
      (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))
    Module.Finite R (Scheme.Modules.projectiveSpaceTwistedGlobalSections Q (d : ℤ)) ∧
      Module.Projective R (Scheme.Modules.projectiveSpaceTwistedGlobalSections Q (d : ℤ)) ∧
      ∀ p : PrimeSpectrum R,
        Module.rankAtStalk (Scheme.Modules.projectiveSpaceTwistedGlobalSections Q (d : ℤ)) p =
          P.hilbertNatValue d := by
  letI := Scheme.Modules.globalSectionsModule
    (Scheme.projectiveSpaceOverπ n (Spec (.of R)))
    (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))
  let eΓ := E.globalSectionsIso d hdE
  have hfiniteM : Module.Finite R
      (((RelativeCohomology.cech R).Hgr M 0).obj (d : ℤ)) :=
    GradedModule.finiteDimensional_cechHgr_of_isFG M hM 0 (d : ℤ)
  have hprojectiveM : Module.Projective R
      (((RelativeCohomology.cech R).Hgr M 0).obj (d : ℤ)) :=
    GradedModule.projective_cechHgr_zero' hM hflatC hfib
  have hfinite : Module.Finite R
      (Scheme.Modules.projectiveSpaceTwistedGlobalSections Q (d : ℤ)) := by
    letI := hfiniteM
    exact Module.Finite.equiv eΓ
  have hprojective : Module.Projective R
      (Scheme.Modules.projectiveSpaceTwistedGlobalSections Q (d : ℤ)) := by
    letI := hprojectiveM
    exact Module.Projective.of_equiv eΓ
  refine ⟨hfinite, hprojective, ?_⟩
  letI := hfinite
  letI := hprojective
  intro p
  let κ := p.asIdeal.ResidueField
  letI : Field κ := inferInstance
  letI : Algebra R κ := inferInstance
  let f : R →+* κ := algebraMap R κ
  have halg : f.toAlgebra = (‹Algebra R κ›) :=
    Algebra.algebra_ext _ _ (fun x ↦ rfl)
  let Qκ := Scheme.Modules.projectiveSpaceBaseChangeOfRingHom Q f
  letI := Scheme.Modules.globalSectionsModule
    (Scheme.projectiveSpaceOverπ n (Spec (.of κ)))
    (Scheme.projectiveSpaceOverTwistModule Qκ (d : ℤ))
  have hPκ : Scheme.HasHilbertPolynomialOver Qκ P := by
    simpa [Qκ, Scheme.Modules.projectiveSpaceBaseChangeOfRingHom] using
      hP (CommRingCat.of κ) (Field.toIsField κ)
        (Spec.map (CommRingCat.ofHom f))
  have heventual : ∀ᶠ e : ℕ in Filter.atTop,
      (((Cohomology.cech κ).h (M.baseChange κ) 0 (e : ℤ) : ℕ) : ℚ) =
        P.eval (e : ℚ) := by
    filter_upwards [hPκ, Filter.eventually_ge_atTop E.bound] with e he heE
    letI := Scheme.Modules.globalSectionsModule
      (Scheme.projectiveSpaceOverπ n (Spec (.of κ)))
      (Scheme.projectiveSpaceOverTwistModule Qκ (e : ℤ))
    have heiso := E.fibreGlobalSectionsIso κ f e
      heE
    rw [halg] at heiso
    have heq : (Cohomology.cech κ).h (M.baseChange κ) 0 (e : ℤ) =
        Scheme.hilbertFunctionOver Qκ (e : ℤ) := by
      change Module.finrank κ (((M.baseChange κ).cechHgr 0).obj (e : ℤ)) =
        Module.finrank κ
          (Scheme.Modules.projectiveSpaceTwistedGlobalSections Qκ (e : ℤ))
      simpa only [RelativeCohomology.cech, Cohomology.cech_Hgr, Qκ] using
        heiso.finrank_eq
    rw [heq]
    exact he
  have hpoly : (Cohomology.cech κ).HasHilbertPolynomial (M.baseChange κ) P :=
    (Cohomology.cech κ).hasHilbertPolynomial_of_eventually_h_zero_eq
      (Cohomology.hasInfiniteBaseChange_cech κ) (M.baseChange κ)
      (hM.baseChange κ) P heventual
  have hdimQ : (Module.finrank κ
      (((M.baseChange κ).cechHgr 0).obj (d : ℤ)) : ℚ) = P.eval (d : ℚ) := by
    have hp := hpoly (d : ℤ)
    rw [(Cohomology.cech κ).chi_eq_h_zero_of_subsingleton
      (M.baseChange κ) (d : ℤ) (hfib κ)] at hp
    change (Module.finrank κ
      (((M.baseChange κ).cechHgr 0).obj (d : ℤ)) : ℚ) = P.eval (d : ℚ) at hp
    exact hp
  have hnat : P.hilbertNatValue d = Module.finrank κ
      (((M.baseChange κ).cechHgr 0).obj (d : ℤ)) :=
    Polynomial.hilbertNatValue_eq hdimQ
  rw [Module.rankAtStalk_eq p]
  let ebc := GradedModule.cechHgrZeroBaseChangeEquiv' hM hflatC hfib κ
  calc
    Module.finrank κ (p.asIdeal.Fiber
        (Scheme.Modules.projectiveSpaceTwistedGlobalSections Q (d : ℤ))) =
        Module.finrank κ (κ ⊗[R]
          (Scheme.Modules.projectiveSpaceTwistedGlobalSections Q (d : ℤ))) := rfl
    _ = Module.finrank κ (κ ⊗[R] ((M.cechHgr 0).obj (d : ℤ))) :=
      (eΓ.symm.baseChange R κ).finrank_eq
    _ = Module.finrank κ (((M.baseChange κ).cechHgr 0).obj (d : ℤ)) :=
      ebc.finrank_eq
    _ = P.hilbertNatValue d := hnat.symm

end RelativeCohomology.SchemeGlobalSectionsComparison

/-- Restricting a twist to the spectrum of an affine base open agrees with twisting the
single pullback along the composite map from that spectrum. -/
noncomputable def _root_.AlgebraicGeometry.Scheme.projectiveSpaceRestrictSpecTwistIso
    (n : ℕ) {T : Scheme.{u}} (U : T.affineOpens)
    (Q : (Scheme.projectiveSpaceOver n T).Modules) (d : ℤ) :
    Scheme.projectiveSpaceRestrictSpec n U (Scheme.projectiveSpaceOverTwistModule Q d) ≅
      Scheme.projectiveSpaceOverTwistModule
        ((Scheme.Modules.pullback (Scheme.projectiveSpaceOverMap n
          (U.1.toScheme.isoSpec.inv ≫ U.1.ι))).obj Q) d := by
  letI : IsAffine U.1.toScheme := U.2
  let j := Scheme.projectiveSpaceOverMap n U.1.ι
  let e := Scheme.projectiveSpaceOverMap n U.1.toScheme.isoSpec.inv
  let g := U.1.toScheme.isoSpec.inv ≫ U.1.ι
  haveI : IsOpenImmersion j := inferInstance
  haveI : IsOpenImmersion e := inferInstance
  haveI : IsOpenImmersion g := inferInstance
  exact (Scheme.Modules.restrictFunctorIsoPullback e).app
      ((Scheme.Modules.restrictFunctor j).obj (Scheme.projectiveSpaceOverTwistModule Q d)) ≪≫
    (Scheme.Modules.pullback e).mapIso ((Scheme.Modules.restrictFunctorIsoPullback j).app _) ≪≫
    (Scheme.Modules.pullbackComp e j).app _ ≪≫
    (Scheme.Modules.pullbackCongr
      (Scheme.projectiveSpaceOverMap_comp n U.1.toScheme.isoSpec.inv U.1.ι)).app _ ≪≫
    Scheme.projectiveSpaceOverTwistModule_pullbackIso_of_isOpenImmersion n g Q d

set_option synthInstance.maxHeartbeats 1000000 in
-- The zero-dimensional twist and global-sections equivalences are instance-heavy.
/-- On projective zero-space the twisted global sections of any finitely presented flat
family are finite projective, and their rank is the value prescribed by its fibrewise
Hilbert polynomial.  No noetherian hypothesis is needed. -/
theorem projectiveSpaceZero_twistedGlobalSections_finite_projective_rank
    (R : Type u) [CommRing R]
    (Q : (Scheme.projectiveSpaceOver 0 (Spec (.of R))).Modules)
    (P : Polynomial ℚ)
    (hQfp : Q.IsFinitePresentation)
    (hflat : Q.FlatOver (Scheme.projectiveSpaceOverπ 0 (Spec (.of R))))
    (hP : Scheme.HasFiberwiseHilbertPolynomial Q P) (d : ℕ) :
    letI := Scheme.Modules.globalSectionsModule
      (Scheme.projectiveSpaceOverπ 0 (Spec (.of R)))
      (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))
    Module.Finite R (Scheme.Modules.projectiveSpaceTwistedGlobalSections Q (d : ℤ)) ∧
      Module.Projective R (Scheme.Modules.projectiveSpaceTwistedGlobalSections Q (d : ℤ)) ∧
      ∀ p : PrimeSpectrum R,
        Module.rankAtStalk
          (Scheme.Modules.projectiveSpaceTwistedGlobalSections Q (d : ℤ)) p =
            P.hilbertNatValue d := by
  let pR := Scheme.projectiveSpaceOverπ 0 (Spec (.of R))
  let Qd := Scheme.projectiveSpaceOverTwistModule Q (d : ℤ)
  letI := Scheme.Modules.globalSectionsModule pR Q
  letI := Scheme.Modules.globalSectionsModule pR Qd
  obtain ⟨hfiniteQ, hprojectiveQ⟩ :=
    Scheme.projectiveSpaceZero_globalSections_finite_projective Q hQfp hflat
  let eΓ := Scheme.Modules.globalSectionsLinearEquivOfIso pR
    (Scheme.projectiveSpaceOverZeroTwistModuleIso Q (d : ℤ))
  have hfiniteQd : Module.Finite R Γ(Qd, ⊤) := by
    letI : Module.Finite R Γ(Q, ⊤) := hfiniteQ
    exact Module.Finite.equiv eΓ.symm
  have hprojectiveQd : Module.Projective R Γ(Qd, ⊤) := by
    letI : Module.Projective R Γ(Q, ⊤) := hprojectiveQ
    exact Module.Projective.of_equiv' eΓ.symm
  refine ⟨hfiniteQd, hprojectiveQd, ?_⟩
  letI : Module.Finite R Γ(Q, ⊤) := hfiniteQ
  letI : Module.Projective R Γ(Q, ⊤) := hprojectiveQ
  intro p
  let κ := p.asIdeal.ResidueField
  letI : Field κ := inferInstance
  letI : Algebra R κ := inferInstance
  let f : R →+* κ := algebraMap R κ
  let Qκ := Scheme.Modules.projectiveSpaceBaseChangeOfRingHom Q f
  letI := Scheme.Modules.globalSectionsModule
    (Scheme.projectiveSpaceOverπ 0 (Spec (.of κ))) Qκ
  have hPκ : Scheme.HasHilbertPolynomialOver Qκ P := by
    simpa [Qκ, Scheme.Modules.projectiveSpaceBaseChangeOfRingHom] using
      hP
        (CommRingCat.of κ) (Field.toIsField κ) (Spec.map (CommRingCat.ofHom f))
  let q := Module.finrank κ Γ(Qκ, ⊤)
  have hPconst : P = Polynomial.C (q : ℚ) :=
    Scheme.hasHilbertPolynomialOver_zero_eq_C Qκ P hPκ
  have hPq : Scheme.HasFiberwiseHilbertPolynomial Q (Polynomial.C (q : ℚ)) := by
    simpa only [← hPconst] using hP
  have hrankQ : Module.rankAtStalk Γ(Q, ⊤) p = q :=
    Scheme.projectiveSpaceZero_globalSections_rankAtStalk_eq
      Q q hfiniteQ hprojectiveQ hPq p
  have hnat : P.hilbertNatValue d = q := by
    rw [hPconst, Polynomial.hilbertNatValue]
    simp [q]
  exact (congrFun (Module.rankAtStalk_eq_of_equiv eΓ) p).trans
    (hrankQ.trans hnat.symm)

set_option synthInstance.maxHeartbeats 1000000 in
-- Local restriction of the zero-dimensional comparison creates nested pullback instances.
set_option maxHeartbeats 3000000 in
-- The affine-cover assembly elaborates rank transport on every chart.
/-- On relative projective zero-space, the pushforward of every twist of a finitely
presented flat family is a vector bundle whose rank is prescribed by the fibrewise
Hilbert polynomial.  This holds over an arbitrary base scheme. -/
theorem projectiveSpaceZero_pushforward_isProjectiveOfRank
    (T : Scheme.{u})
    (Q : (Scheme.projectiveSpaceOver 0 T).Modules)
    (hQfp : Q.IsFinitePresentation)
    (hflat : Q.FlatOver (Scheme.projectiveSpaceOverπ 0 T))
    (hP : Scheme.HasFiberwiseHilbertPolynomial Q P) (d : ℕ) :
    Scheme.Modules.IsProjectiveOfRank (P.hilbertNatValue d)
      ((Scheme.Modules.pushforward (Scheme.projectiveSpaceOverπ 0 T)).obj
        (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))) := by
  haveI := hQfp
  let Qd := Scheme.projectiveSpaceOverTwistModule Q (d : ℤ)
  have hlocal : ∀ U : T.affineOpens,
      letI := Scheme.Modules.globalSectionsModule
        (Scheme.projectiveSpaceOverπ 0 (Spec Γ(U.1.toScheme, ⊤)))
        (Scheme.projectiveSpaceRestrictSpec 0 U Qd)
      Module.Finite Γ(U.1.toScheme, ⊤) Γ(Scheme.projectiveSpaceRestrictSpec 0 U Qd, ⊤) ∧
        Module.Projective Γ(U.1.toScheme, ⊤)
          Γ(Scheme.projectiveSpaceRestrictSpec 0 U Qd, ⊤) ∧
        ∀ p : PrimeSpectrum Γ(U.1.toScheme, ⊤),
          Module.rankAtStalk Γ(Scheme.projectiveSpaceRestrictSpec 0 U Qd, ⊤) p =
            P.hilbertNatValue d := by
    intro U
    haveI hUaff : IsAffine U.1.toScheme := U.2
    let R := Γ(U.1.toScheme, ⊤)
    let gU : Spec (CommRingCat.of R) ⟶ T := U.1.toScheme.isoSpec.inv ≫ U.1.ι
    let mU := Scheme.projectiveSpaceOverMap 0 gU
    haveI : IsOpenImmersion gU := inferInstance
    haveI : IsOpenImmersion mU := inferInstance
    let QU := (Scheme.Modules.pullback mU).obj Q
    have hQUfp : QU.IsFinitePresentation :=
      Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ hQfp
    have hflatU : QU.FlatOver
        (Scheme.projectiveSpaceOverπ 0 (Spec (CommRingCat.of R))) :=
      Scheme.Modules.FlatOver.pullback_of_isPullback mU
        (Scheme.projectiveSpaceOverπ 0 (Spec (CommRingCat.of R)))
        (Scheme.projectiveSpaceOverπ 0 T) gU
        (Scheme.isPullback_projectiveSpaceOverMap 0 gU).flip Q hflat
    have hPU : Scheme.HasFiberwiseHilbertPolynomial QU P :=
      Scheme.HasFiberwiseHilbertPolynomial.pullback gU hP
    obtain ⟨hfinU, hprojU, hrankU⟩ :=
      projectiveSpaceZero_twistedGlobalSections_finite_projective_rank
        R QU P hQUfp hflatU hPU d
    let QUd := Scheme.projectiveSpaceOverTwistModule QU (d : ℤ)
    letI := Scheme.Modules.globalSectionsModule
      (Scheme.projectiveSpaceOverπ 0 (Spec (CommRingCat.of R)))
      (Scheme.projectiveSpaceRestrictSpec 0 U Qd)
    letI := Scheme.Modules.globalSectionsModule
      (Scheme.projectiveSpaceOverπ 0 (Spec (CommRingCat.of R))) QUd
    let eQ := Scheme.projectiveSpaceRestrictSpecTwistIso 0 U Q (d : ℤ)
    let eΓ := Scheme.Modules.globalSectionsLinearEquivOfIso
      (Scheme.projectiveSpaceOverπ 0 (Spec (CommRingCat.of R))) eQ
    letI : Module.Finite R Γ(QUd, ⊤) := hfinU
    letI : Module.Projective R Γ(QUd, ⊤) := hprojU
    exact ⟨Module.Finite.equiv eΓ.symm, Module.Projective.of_equiv' eΓ.symm,
      fun p ↦ (congrFun (Module.rankAtStalk_eq_of_equiv eΓ) p).trans (hrankU p)⟩
  exact Scheme.isProjectiveOfRank_pushforward_of_globalSections 0 Qd
    (P.hilbertNatValue d) (fun U ↦ (hlocal U).1)
      (fun U ↦ (hlocal U).2.1) (fun U ↦ (hlocal U).2.2)

open RelativeCohomology.SchemeGlobalSectionsComparison

-- The polynomial `Proj` comparison and its fibrewise rank calculation are elaboration-heavy.
set_option synthInstance.maxHeartbeats 1000000 in
-- The kernel-route model carries several quantified twist instances.
set_option maxHeartbeats 2000000 in
-- The rank calculation compares Cech and geometric fibres through multiple equivalences.
/-- Uniform fixed-degree finite projectivity and rank over an arbitrary affine base,
conditional only on the proper-finiteness input not supplied by the ordinary Cech complex.
All Cech cohomology groups, including `H⁰`, need only be finite; finite presentation of
`H⁰` follows from flatness, base change, and its constant fibre rank.

The degree bound itself is unconditional and uniform in the quotient: it comes from
fibrewise kernel regularity over fields. -/
theorem exists_bound_twistedFreeQuot_globalSections_finite_projective_rank_of_finiteHomology
    (n r : ℕ) (hn : 0 < n) (l : ℤ) (P : Polynomial ℚ) :
    ∃ d₀ : ℤ, 0 ≤ d₀ ∧ ∀ (R : Type u) [CommRing R]
      (Q : (Scheme.projectiveSpaceOver n (Spec (.of R))).Modules)
      (_ : Q.IsFinitePresentation)
      (q : (∐ fun _ : ULift.{u} (Fin r) ↦
        Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l)) ⟶ Q)
      (_ : Epi q)
      (_ : Q.FlatOver (Scheme.projectiveSpaceOverπ n (Spec (.of R))))
      (_ : Scheme.HasFiberwiseHilbertPolynomial Q P)
      (d : ℕ), d₀ ≤ (d : ℤ) →
      let p := (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).map q
      let M := Proj.kernelQuotientModule
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (projSpecπ n R) (stdVars n R) p
      (∀ i : ℕ, 1 ≤ i → Module.Finite R ((M.cechHgr i).obj (d : ℤ))) →
        Module.Finite R ((M.cechHgr 0).obj (d : ℤ)) →
          letI := Scheme.Modules.globalSectionsModule
            (Scheme.projectiveSpaceOverπ n (Spec (.of R)))
            (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))
          Module.Finite R
              (Scheme.Modules.projectiveSpaceTwistedGlobalSections Q (d : ℤ)) ∧
            Module.Projective R
              (Scheme.Modules.projectiveSpaceTwistedGlobalSections Q (d : ℤ)) ∧
            ∀ x : PrimeSpectrum R,
              Module.rankAtStalk
                (Scheme.Modules.projectiveSpaceTwistedGlobalSections Q (d : ℤ)) x =
                  P.hilbertNatValue d := by
  obtain ⟨d₀, hd₀0, hd₀⟩ :=
    exists_bound_subsingleton_cechHgr_kernelQuotientModule_baseChange_arbitrary
      n r hn l P
  refine ⟨d₀, hd₀0, ?_⟩
  intro R _ Q hQfp q hq hflat hHP d hd
  dsimp only
  intro hfin hfinite0
  haveI := hQfp
  haveI := hq
  haveI hAmb : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l)).IsFinitePresentation :=
    Scheme.twistedFreeAmbient_isFinitePresentation n (Spec (.of R)) l r
  let E := projAmbient n r l (R := R)
  let G := (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q
  let p := (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).map q
  haveI hp : Epi p := inferInstance
  haveI hEfp : E.IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  haveI hGfp : G.IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  haveI hEqc : ∀ e : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) E e).IsQuasicoherent :=
    fun e ↦ twistModule_std_isQuasicoherent _ e
  haveI hGqc : ∀ e : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) G e).IsQuasicoherent :=
    fun e ↦ twistModule_std_isQuasicoherent _ e
  have hKqc0 : (kernel p).IsQuasicoherent := Scheme.Modules.kernel_isQuasicoherent p
  letI hKqc0' : (kernel p).IsQuasicoherent := hKqc0
  haveI hKqc : ∀ e : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (kernel p) e).IsQuasicoherent :=
    fun e ↦ twistModule_std_isQuasicoherent_of_isQuasicoherent n _ e
  let M := Proj.kernelQuotientModule
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    (projSpecπ n R) (stdVars n R) p
  have hGflat : G.FlatOver (projSpecπ n R) :=
    Scheme.Modules.FlatOver.pullback_isIso (projectiveSpaceOverSpecIso n R).inv Q
      (projectiveSpaceOverSpecIso_inv_comp_projectiveSpaceOverπ n R) hflat
  have hMfg : GradedModule.IsFG M :=
    isFG_kernelQuotientModule_twistedFree_arbitrary n r hn l R Q q
  have hMflatC : ∀ s : ℕ, Module.Flat R ((M.cechComplex (d : ℤ)).X s) := by
    intro s
    exact GradedModule.flat_cechCochain_of_flat_loc _
      (fun a ↦ Proj.isFlat_loc_kernelQuotientModule_arbitrary p a hGflat) s (d : ℤ)
  let C := cechSchemeGlobalSectionsComparisonQuotientModel_arbitrary n R Q p
  have hdC : C.bound ≤ d := by
    change 0 ≤ d
    omega
  exact finite_projective_rank_at_fixed_degree_of_finiteHomology_and_finiteZero
      C hMfg P hHP d hdC hMflatC hfin hfinite0
        (hd₀ R Q hQfp q hq hflat hHP d hd)

-- The polynomial `Proj` comparison and its fibrewise rank calculation are elaboration-heavy.
set_option synthInstance.maxHeartbeats 1000000 in
-- The kernel-route model carries several quantified twist instances.
set_option maxHeartbeats 2000000 in
-- The rank calculation compares Cech and geometric fibres through multiple equivalences.
/-- Uniform fixed-degree finite projectivity and rank over an arbitrary affine base, assuming a
universally strictly-perfect replacement of the fixed-degree Cech complex.  This packages the
single relative-perfectness input needed by the arbitrary-base Quot construction. -/
theorem
    exists_bound_twistedFreeQuot_globalSections_finite_projective_rank_of_strictlyPerfectReplacement
    (n r : ℕ) (hn : 0 < n) (l : ℤ) (P : Polynomial ℚ) :
    ∃ d₀ : ℤ, 0 ≤ d₀ ∧ ∀ (R : Type u) [CommRing R]
      (Q : (Scheme.projectiveSpaceOver n (Spec (.of R))).Modules)
      (_ : Q.IsFinitePresentation)
      (q : (∐ fun _ : ULift.{u} (Fin r) ↦
        Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l)) ⟶ Q)
      (_ : Epi q)
      (_ : Q.FlatOver (Scheme.projectiveSpaceOverπ n (Spec (.of R))))
      (_ : Scheme.HasFiberwiseHilbertPolynomial Q P)
      (d : ℕ), d₀ ≤ (d : ℤ) →
      let p := (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).map q
      let M := Proj.kernelQuotientModule
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (projSpecπ n R) (stdVars n R) p
      CochainComplex.StrictlyPerfectReplacement (M.cechComplex (d : ℤ)) →
        letI := Scheme.Modules.globalSectionsModule
          (Scheme.projectiveSpaceOverπ n (Spec (.of R)))
          (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))
        Module.Finite R
            (Scheme.Modules.projectiveSpaceTwistedGlobalSections Q (d : ℤ)) ∧
          Module.Projective R
            (Scheme.Modules.projectiveSpaceTwistedGlobalSections Q (d : ℤ)) ∧
          ∀ x : PrimeSpectrum R,
            Module.rankAtStalk
              (Scheme.Modules.projectiveSpaceTwistedGlobalSections Q (d : ℤ)) x =
                P.hilbertNatValue d := by
  obtain ⟨d₀, hd₀0, hd₀⟩ :=
    exists_bound_subsingleton_cechHgr_kernelQuotientModule_baseChange_arbitrary
      n r hn l P
  refine ⟨d₀, hd₀0, ?_⟩
  intro R _ Q hQfp q hq hflat hHP d hd
  dsimp only
  intro D
  haveI := hQfp
  haveI := hq
  haveI hAmb : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l)).IsFinitePresentation :=
    Scheme.twistedFreeAmbient_isFinitePresentation n (Spec (.of R)) l r
  let E := projAmbient n r l (R := R)
  let G := (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q
  let p := (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).map q
  haveI hp : Epi p := inferInstance
  haveI hEfp : E.IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  haveI hGfp : G.IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  haveI hEqc : ∀ e : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) E e).IsQuasicoherent :=
    fun e ↦ twistModule_std_isQuasicoherent _ e
  haveI hGqc : ∀ e : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) G e).IsQuasicoherent :=
    fun e ↦ twistModule_std_isQuasicoherent _ e
  have hKqc0 : (kernel p).IsQuasicoherent := Scheme.Modules.kernel_isQuasicoherent p
  letI hKqc0' : (kernel p).IsQuasicoherent := hKqc0
  haveI hKqc : ∀ e : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (kernel p) e).IsQuasicoherent :=
    fun e ↦ twistModule_std_isQuasicoherent_of_isQuasicoherent n _ e
  let M := Proj.kernelQuotientModule
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    (projSpecπ n R) (stdVars n R) p
  have hGflat : G.FlatOver (projSpecπ n R) :=
    Scheme.Modules.FlatOver.pullback_isIso (projectiveSpaceOverSpecIso n R).inv Q
      (projectiveSpaceOverSpecIso_inv_comp_projectiveSpaceOverπ n R) hflat
  have hMfg : GradedModule.IsFG M :=
    isFG_kernelQuotientModule_twistedFree_arbitrary n r hn l R Q q
  have hMflatC : ∀ s : ℕ, Module.Flat R ((M.cechComplex (d : ℤ)).X s) := by
    intro s
    exact GradedModule.flat_cechCochain_of_flat_loc _
      (fun a ↦ Proj.isFlat_loc_kernelQuotientModule_arbitrary p a hGflat) s (d : ℤ)
  let C := cechSchemeGlobalSectionsComparisonQuotientModel_arbitrary n R Q p
  have hdC : C.bound ≤ d := by
    change 0 ≤ d
    omega
  exact finite_projective_rank_at_fixed_degree_of_strictlyPerfectReplacement
    C hMfg P hHP d hdC D hMflatC
      (hd₀ R Q hQfp q hq hflat hHP d hd)

-- The noetherian proof uses Serre finiteness for the graded Cech complex.
set_option synthInstance.maxHeartbeats 1000000 in
-- The kernel-route model carries several quantified twist instances.
set_option maxHeartbeats 2000000 in
-- Serre finiteness and the fibre-rank calculation are elaboration-heavy together.
/-- Uniform fixed-degree finite projectivity and rank on an affine noetherian base.
The rank is the natural-number value of the prescribed Hilbert polynomial in that degree. -/
theorem exists_bound_twistedFreeQuot_globalSections_finite_projective_rank
    (n r : ℕ) (hn : 0 < n) (l : ℤ) (P : Polynomial ℚ) :
    ∃ d₀ : ℤ, 0 ≤ d₀ ∧ ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
      (Q : (Scheme.projectiveSpaceOver n (Spec (.of R))).Modules)
      (_ : Q.IsFinitePresentation)
      (q : (∐ fun _ : ULift.{u} (Fin r) ↦
        Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l)) ⟶ Q)
      (_ : Epi q)
      (_ : Q.FlatOver (Scheme.projectiveSpaceOverπ n (Spec (.of R))))
      (_ : Scheme.HasFiberwiseHilbertPolynomial Q P)
      (d : ℕ), d₀ ≤ (d : ℤ) →
      letI := Scheme.Modules.globalSectionsModule
        (Scheme.projectiveSpaceOverπ n (Spec (.of R)))
        (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))
      Module.Finite R (Scheme.Modules.projectiveSpaceTwistedGlobalSections Q (d : ℤ)) ∧
        Module.Projective R (Scheme.Modules.projectiveSpaceTwistedGlobalSections Q (d : ℤ)) ∧
        ∀ p : PrimeSpectrum R,
          Module.rankAtStalk
            (Scheme.Modules.projectiveSpaceTwistedGlobalSections Q (d : ℤ)) p =
              P.hilbertNatValue d := by
  obtain ⟨d₀, hd₀0, hd₀⟩ :=
    exists_bound_subsingleton_cechHgr_kernelQuotientModule_baseChange n r hn l P
  refine ⟨d₀, hd₀0, ?_⟩
  intro R _ _ Q hQfp q hq hflat hHP d hd
  haveI := hQfp
  haveI := hq
  haveI hAmb : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l)).IsFinitePresentation :=
    Scheme.twistedFreeAmbient_isFinitePresentation n (Spec (.of R)) l r
  let E := projAmbient n r l (R := R)
  let G := (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q
  let p := (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).map q
  haveI hp : Epi p := inferInstance
  haveI hEfp : E.IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  haveI hGfp : G.IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  haveI hKfp : (kernel p).IsFinitePresentation :=
    Scheme.Modules.kernel_isFinitePresentation p
  haveI hEqc : ∀ e : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) E e).IsQuasicoherent :=
    fun e ↦ twistModule_std_isQuasicoherent _ e
  haveI hGqc : ∀ e : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) G e).IsQuasicoherent :=
    fun e ↦ twistModule_std_isQuasicoherent _ e
  haveI hKqc : ∀ e : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (kernel p) e).IsQuasicoherent :=
    fun e ↦ twistModule_std_isQuasicoherent _ e
  let M := Proj.kernelQuotientModule
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    (projSpecπ n R) (stdVars n R) p
  have hGflat : G.FlatOver (projSpecπ n R) :=
    Scheme.Modules.FlatOver.pullback_isIso (projectiveSpaceOverSpecIso n R).inv Q
      (projectiveSpaceOverSpecIso_inv_comp_projectiveSpaceOverπ n R) hflat
  have hMfg : GradedModule.IsFG M :=
    GradedModule.IsFG.coker _ (isFG_gammaStarPullTwistedFree n R hn (-l) r)
  have hMflatC : ∀ s : ℕ, Module.Flat R ((M.cechComplex (d : ℤ)).X s) := by
    intro s
    exact GradedModule.flat_cechCochain_of_flat_loc _
      (fun a ↦ Proj.isFlat_loc_kernelQuotientModule p a hGflat) s (d : ℤ)
  let C := schemeGlobalSectionsComparisonQuotientModel n R Q p
  have hdC : C.bound ≤ d := by
    change 0 ≤ d
    omega
  exact C.finite_projective_rank_at_fixed_degree hMfg P hHP d hdC
    hMflatC (hd₀ R Q hQfp q hq hflat hHP d hd)

set_option synthInstance.maxHeartbeats 1000000 in
-- Restricting the family to every affine base chart creates nested pullback instances.
set_option maxHeartbeats 3000000 in
-- The local-to-global pushforward assembly transports three module properties per chart.
/-- Uniform fixed-degree local freeness of the twisted quotient pushforward over every
locally noetherian base. -/
theorem exists_bound_twistedFreeQuot_pushforward_isProjectiveOfRank
    (n r : ℕ) (hn : 0 < n) (l : ℤ) (P : Polynomial ℚ) :
    ∃ d₀ : ℤ, 0 ≤ d₀ ∧ ∀ (T : Scheme.{u}) [IsLocallyNoetherian T]
      (Q : (Scheme.projectiveSpaceOver n T).Modules)
      (_ : Q.IsFinitePresentation)
      (q : (∐ fun _ : ULift.{u} (Fin r) ↦
        Scheme.projectiveSpaceOverTwist n T (-l)) ⟶ Q)
      (_ : Epi q)
      (_ : Q.FlatOver (Scheme.projectiveSpaceOverπ n T))
      (_ : Scheme.HasFiberwiseHilbertPolynomial Q P)
      (d : ℕ), d₀ ≤ (d : ℤ) →
      Scheme.Modules.IsProjectiveOfRank (P.hilbertNatValue d)
        ((Scheme.Modules.pushforward (Scheme.projectiveSpaceOverπ n T)).obj
          (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))) := by
  obtain ⟨d₀, hd₀0, hd₀⟩ :=
    exists_bound_twistedFreeQuot_globalSections_finite_projective_rank n r hn l P
  refine ⟨d₀, hd₀0, ?_⟩
  intro T _ Q hQfp q hq hflat hHP d hd
  haveI := hQfp
  haveI := hq
  let Qd := Scheme.projectiveSpaceOverTwistModule Q (d : ℤ)
  have hlocal : ∀ U : T.affineOpens,
      letI := Scheme.Modules.globalSectionsModule
        (Scheme.projectiveSpaceOverπ n (Spec Γ(U.1.toScheme, ⊤)))
        (Scheme.projectiveSpaceRestrictSpec n U Qd)
      Module.Finite Γ(U.1.toScheme, ⊤) Γ(Scheme.projectiveSpaceRestrictSpec n U Qd, ⊤) ∧
        Module.Projective Γ(U.1.toScheme, ⊤)
          Γ(Scheme.projectiveSpaceRestrictSpec n U Qd, ⊤) ∧
        ∀ p : PrimeSpectrum Γ(U.1.toScheme, ⊤),
          Module.rankAtStalk Γ(Scheme.projectiveSpaceRestrictSpec n U Qd, ⊤) p =
            P.hilbertNatValue d := by
    intro U
    haveI hUaff : IsAffine U.1.toScheme := U.2
    let R := Γ(U.1.toScheme, ⊤)
    letI : IsNoetherianRing Γ(T, U.1) :=
      IsLocallyNoetherian.component_noetherian U
    haveI hR : IsNoetherianRing R :=
      isNoetherianRing_of_ringEquiv Γ(T, U.1)
        U.1.topIso.symm.commRingCatIsoToRingEquiv
    let gU : Spec (CommRingCat.of R) ⟶ T := U.1.toScheme.isoSpec.inv ≫ U.1.ι
    let mU := Scheme.projectiveSpaceOverMap n gU
    haveI : IsOpenImmersion gU := inferInstance
    haveI : IsOpenImmersion mU := inferInstance
    let QU := (Scheme.Modules.pullback mU).obj Q
    haveI hQUfp : QU.IsFinitePresentation :=
      Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
    let qU := (Scheme.projectiveSpaceOverTwistedFree_pullbackIso n r l gU).inv ≫
      (Scheme.Modules.pullback mU).map q
    haveI hqU : Epi qU := epi_comp _ _
    have hflatU : QU.FlatOver
        (Scheme.projectiveSpaceOverπ n (Spec (CommRingCat.of R))) :=
      Scheme.Modules.FlatOver.pullback_of_isPullback mU
        (Scheme.projectiveSpaceOverπ n (Spec (CommRingCat.of R)))
        (Scheme.projectiveSpaceOverπ n T) gU
        (Scheme.isPullback_projectiveSpaceOverMap n gU).flip Q hflat
    have hHPU : Scheme.HasFiberwiseHilbertPolynomial QU P :=
      Scheme.HasFiberwiseHilbertPolynomial.pullback gU hHP
    obtain ⟨hfinU, hprojU, hrankU⟩ :=
      hd₀ R QU hQUfp qU hqU hflatU hHPU d hd
    let QUd := Scheme.projectiveSpaceOverTwistModule QU (d : ℤ)
    letI := Scheme.Modules.globalSectionsModule
      (Scheme.projectiveSpaceOverπ n (Spec (CommRingCat.of R)))
      (Scheme.projectiveSpaceRestrictSpec n U Qd)
    letI := Scheme.Modules.globalSectionsModule
      (Scheme.projectiveSpaceOverπ n (Spec (CommRingCat.of R))) QUd
    let eQ := Scheme.projectiveSpaceRestrictSpecTwistIso n U Q (d : ℤ)
    let eΓ := Scheme.Modules.globalSectionsLinearEquivOfIso
      (Scheme.projectiveSpaceOverπ n (Spec (CommRingCat.of R))) eQ
    letI : Module.Finite R Γ(QUd, ⊤) := hfinU
    letI : Module.Projective R Γ(QUd, ⊤) := hprojU
    exact ⟨Module.Finite.equiv eΓ.symm, Module.Projective.of_equiv' eΓ.symm,
      fun p ↦ (congrFun (Module.rankAtStalk_eq_of_equiv eΓ) p).trans (hrankU p)⟩
  exact Scheme.isProjectiveOfRank_pushforward_of_globalSections n Qd
    (P.hilbertNatValue d) (fun U ↦ (hlocal U).1)
      (fun U ↦ (hlocal U).2.1) (fun U ↦ (hlocal U).2.2)

/-- Affine-local relative-perfectness data for the fixed-degree Cech complexes attached to a
twisted-free quotient.  This is the single missing input in the arbitrary-base pushforward-rank
theorem below. -/
def HasAffineStrictlyPerfectTwistedFreeQuotCechReplacement
    (n r : ℕ) (l : ℤ) {T : Scheme.{u}}
    (Q : (Scheme.projectiveSpaceOver n T).Modules)
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n T (-l)) ⟶ Q) (d : ℕ) : Prop :=
  ∀ U : T.affineOpens,
    let R := Γ(U.1.toScheme, ⊤)
    let gU : Spec (CommRingCat.of R) ⟶ T := U.1.toScheme.isoSpec.inv ≫ U.1.ι
    let mU := Scheme.projectiveSpaceOverMap n gU
    let QU := (Scheme.Modules.pullback mU).obj Q
    let qU := (Scheme.projectiveSpaceOverTwistedFree_pullbackIso n r l gU).inv ≫
      (Scheme.Modules.pullback mU).map q
    let pU := (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).map qU
    let M := Proj.kernelQuotientModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (projSpecπ n R) (stdVars n R) pU
    Nonempty (CochainComplex.StrictlyPerfectReplacement (M.cechComplex (d : ℤ)))

set_option synthInstance.maxHeartbeats 1000000 in
-- Restricting the family and its replacement to affine charts nests pullback instances.
set_option maxHeartbeats 3000000 in
-- The local-to-global assembly transports finite projectivity and rank on every chart.
/-- Uniform fixed-degree local freeness of the twisted quotient pushforward over an arbitrary
base, conditional on affine-local strictly-perfect replacements of the fixed-degree Cech
complexes. -/
theorem exists_bound_twistedFreeQuot_pushforward_isProjectiveOfRank_of_strictlyPerfectReplacement
    (n r : ℕ) (hn : 0 < n) (l : ℤ) (P : Polynomial ℚ) :
    ∃ d₀ : ℤ, 0 ≤ d₀ ∧ ∀ (T : Scheme.{u})
      (Q : (Scheme.projectiveSpaceOver n T).Modules)
      (_ : Q.IsFinitePresentation)
      (q : (∐ fun _ : ULift.{u} (Fin r) ↦
        Scheme.projectiveSpaceOverTwist n T (-l)) ⟶ Q)
      (_ : Epi q)
      (_ : Q.FlatOver (Scheme.projectiveSpaceOverπ n T))
      (_ : Scheme.HasFiberwiseHilbertPolynomial Q P)
      (d : ℕ), d₀ ≤ (d : ℤ) →
      HasAffineStrictlyPerfectTwistedFreeQuotCechReplacement n r l Q q d →
      Scheme.Modules.IsProjectiveOfRank (P.hilbertNatValue d)
        ((Scheme.Modules.pushforward (Scheme.projectiveSpaceOverπ n T)).obj
          (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))) := by
  obtain ⟨d₀, hd₀0, hd₀⟩ :=
    exists_bound_twistedFreeQuot_globalSections_finite_projective_rank_of_strictlyPerfectReplacement
      n r hn l P
  refine ⟨d₀, hd₀0, ?_⟩
  intro T Q hQfp q hq hflat hHP d hd hperfect
  haveI := hQfp
  haveI := hq
  let Qd := Scheme.projectiveSpaceOverTwistModule Q (d : ℤ)
  have hlocal : ∀ U : T.affineOpens,
      letI := Scheme.Modules.globalSectionsModule
        (Scheme.projectiveSpaceOverπ n (Spec Γ(U.1.toScheme, ⊤)))
        (Scheme.projectiveSpaceRestrictSpec n U Qd)
      Module.Finite Γ(U.1.toScheme, ⊤) Γ(Scheme.projectiveSpaceRestrictSpec n U Qd, ⊤) ∧
        Module.Projective Γ(U.1.toScheme, ⊤)
          Γ(Scheme.projectiveSpaceRestrictSpec n U Qd, ⊤) ∧
        ∀ p : PrimeSpectrum Γ(U.1.toScheme, ⊤),
          Module.rankAtStalk Γ(Scheme.projectiveSpaceRestrictSpec n U Qd, ⊤) p =
            P.hilbertNatValue d := by
    intro U
    haveI hUaff : IsAffine U.1.toScheme := U.2
    let R := Γ(U.1.toScheme, ⊤)
    let gU : Spec (CommRingCat.of R) ⟶ T := U.1.toScheme.isoSpec.inv ≫ U.1.ι
    let mU := Scheme.projectiveSpaceOverMap n gU
    haveI : IsOpenImmersion gU := inferInstance
    haveI : IsOpenImmersion mU := inferInstance
    let QU := (Scheme.Modules.pullback mU).obj Q
    haveI hQUfp : QU.IsFinitePresentation :=
      Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
    let qU := (Scheme.projectiveSpaceOverTwistedFree_pullbackIso n r l gU).inv ≫
      (Scheme.Modules.pullback mU).map q
    haveI hqU : Epi qU := epi_comp _ _
    have hflatU : QU.FlatOver
        (Scheme.projectiveSpaceOverπ n (Spec (CommRingCat.of R))) :=
      Scheme.Modules.FlatOver.pullback_of_isPullback mU
        (Scheme.projectiveSpaceOverπ n (Spec (CommRingCat.of R)))
        (Scheme.projectiveSpaceOverπ n T) gU
        (Scheme.isPullback_projectiveSpaceOverMap n gU).flip Q hflat
    have hHPU : Scheme.HasFiberwiseHilbertPolynomial QU P :=
      Scheme.HasFiberwiseHilbertPolynomial.pullback gU hHP
    obtain ⟨hfinU, hprojU, hrankU⟩ :=
      hd₀ R QU hQUfp qU hqU hflatU hHPU d hd (Classical.choice (hperfect U))
    let QUd := Scheme.projectiveSpaceOverTwistModule QU (d : ℤ)
    letI := Scheme.Modules.globalSectionsModule
      (Scheme.projectiveSpaceOverπ n (Spec (CommRingCat.of R)))
      (Scheme.projectiveSpaceRestrictSpec n U Qd)
    letI := Scheme.Modules.globalSectionsModule
      (Scheme.projectiveSpaceOverπ n (Spec (CommRingCat.of R))) QUd
    let eQ := Scheme.projectiveSpaceRestrictSpecTwistIso n U Q (d : ℤ)
    let eΓ := Scheme.Modules.globalSectionsLinearEquivOfIso
      (Scheme.projectiveSpaceOverπ n (Spec (CommRingCat.of R))) eQ
    letI : Module.Finite R Γ(QUd, ⊤) := hfinU
    letI : Module.Projective R Γ(QUd, ⊤) := hprojU
    exact ⟨Module.Finite.equiv eΓ.symm, Module.Projective.of_equiv' eΓ.symm,
      fun p ↦ (congrFun (Module.rankAtStalk_eq_of_equiv eΓ) p).trans (hrankU p)⟩
  exact Scheme.isProjectiveOfRank_pushforward_of_globalSections n Qd
    (P.hilbertNatValue d) (fun U ↦ (hlocal U).1)
      (fun U ↦ (hlocal U).2.1) (fun U ↦ (hlocal U).2.2)

/-- Uniform fixed-degree local freeness of twisted quotient pushforwards for every
projective-space dimension over a locally noetherian base.  The zero-dimensional case
uses the direct arbitrary-base identification `P⁰_T ≅ T`; positive dimensions use the
uniform kernel-regularity bound. -/
theorem exists_bound_twistedFreeQuot_pushforward_isProjectiveOfRank_all_n
    (n r : ℕ) (l : ℤ) (P : Polynomial ℚ) :
    ∃ d₀ : ℤ, 0 ≤ d₀ ∧ ∀ (T : Scheme.{u}) [IsLocallyNoetherian T]
      (Q : (Scheme.projectiveSpaceOver n T).Modules)
      (_ : Q.IsFinitePresentation)
      (q : (∐ fun _ : ULift.{u} (Fin r) ↦
        Scheme.projectiveSpaceOverTwist n T (-l)) ⟶ Q)
      (_ : Epi q)
      (_ : Q.FlatOver (Scheme.projectiveSpaceOverπ n T))
      (_ : Scheme.HasFiberwiseHilbertPolynomial Q P)
      (d : ℕ), d₀ ≤ (d : ℤ) →
      Scheme.Modules.IsProjectiveOfRank (P.hilbertNatValue d)
        ((Scheme.Modules.pushforward (Scheme.projectiveSpaceOverπ n T)).obj
          (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))) := by
  cases n with
  | zero =>
      refine ⟨0, le_rfl, ?_⟩
      intro T _ Q hQfp q hq hflat hP d hd
      exact projectiveSpaceZero_pushforward_isProjectiveOfRank
        T Q hQfp hflat hP d
  | succ n =>
      exact exists_bound_twistedFreeQuot_pushforward_isProjectiveOfRank
        (n + 1) r (by omega) l P

end AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- A strict rank-`q` quotient of a finite free sheaf of rank `m` on a nonempty scheme
forces `q ≤ m`.  Pulling the quotient to the residue field of one point reduces this to
the finite-dimensional vector-space rank inequality. -/
lemma FreeQuotient.rank_le_of_nonempty {X : Scheme.{u}} {q m : ℕ}
    (x : FreeQuotient q (ULift.{u} (Fin m)) X) (hX : Nonempty X) : q ≤ m := by
  let t : X := Classical.choice hX
  exact (x.pullback (X.fromSpecResidueField t)).rank_le_of_field

/-- An epimorphism from the canonical free sheaf of rank `m` to a rank-`q` vector bundle
on a nonempty scheme forces `q ≤ m`. -/
lemma IsProjectiveOfRank.rank_le_of_epi_finFree {X : Scheme.{u}} {q m : ℕ}
    {M : X.Modules} [M.IsQuasicoherent] (hM : IsProjectiveOfRank q M)
    (f : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m)) ⟶ M)
    [Epi f] (hX : Nonempty X) : q ≤ m := by
  let x : FreeQuotient q (ULift.{u} (Fin m)) X := {
    Q := M
    isQuasicoherent := inferInstance
    isProjectiveOfRank := hM
    π := f
    epi := inferInstance }
  exact x.rank_le_of_nonempty hX

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.ProjectiveSpace

set_option synthInstance.maxHeartbeats 1000000 in
-- The monomial map and the pushforward rank calculation each carry many sheaf instances.
set_option maxHeartbeats 2000000 in
-- Combining the two uniform bounds elaborates both constructions simultaneously.
/-- In every sufficiently large twist, the rank prescribed by the Hilbert polynomial is
at most the number of monomial generators.  The statement accepts an arbitrary finite
reindexing `σ`, matching the free map used by the Quot-to-Grassmannian construction. -/
theorem exists_bound_twistedFreeQuot_pushforward_rank_le_monomial_count
    (n r : ℕ) (l : ℤ) (P : Polynomial ℚ) :
    ∃ d₀ : ℤ, 0 ≤ d₀ ∧ ∀ (T : Scheme.{u}) [IsLocallyNoetherian T]
      (_hT : Nonempty T)
      (Q : (Scheme.projectiveSpaceOver n T).Modules)
      (_ : Q.IsFinitePresentation)
      (q : (∐ fun _ : ULift.{u} (Fin r) ↦
        Scheme.projectiveSpaceOverTwist n T (-l)) ⟶ Q)
      (_ : Epi q)
      (_ : Q.FlatOver (Scheme.projectiveSpaceOverπ n T))
      (_ : Scheme.HasFiberwiseHilbertPolynomial Q P)
      (d e : ℕ) (_he : (d : ℤ) - l = (e : ℤ)), d₀ ≤ (d : ℤ) →
      ∀ {m : ℕ}
        (_σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n)),
          P.hilbertNatValue d ≤ m := by
  obtain ⟨dRank, hdRank0, hRank⟩ :=
    exists_bound_twistedFreeQuot_pushforward_isProjectiveOfRank_all_n n r l P
  obtain ⟨dSpan, hdSpan0, hSpan⟩ :=
    exists_bound_surjective_finFreeSectionsMap_quotGrassmannian n r l P
  refine ⟨max dRank dSpan, by omega, ?_⟩
  intro T _ hT Q hQfp q hq hflat hP d e he hd m σ
  have hRankQ := hRank T Q hQfp q hq hflat hP d
    (le_trans (le_max_left dRank dSpan) hd)
  let M := (Scheme.Modules.pushforward (Scheme.projectiveSpaceOverπ n T)).obj
    (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))
  let s : ULift.{u} (Fin m) → ↥Γ(M, ⊤) := fun i ↦
    Scheme.quotMonomialSection n T l r q d e he (σ i).1 (σ i).2
  let φ : SheafOfModules.free (R := T.ringCatSheaf) (ULift.{u} (Fin m)) ⟶ M :=
    Scheme.Modules.freeHomOfSections s
  have hsurj : ∀ U : T.affineOpens,
      Function.Surjective (Scheme.Modules.finFreeSectionsMap' φ U.1) := by
    intro U
    simpa only [M, s, φ] using
      hSpan T Q hQfp q hq hflat hP d e he
        (le_trans (le_max_right dRank dSpan) hd) σ U
  haveI hφ : Epi φ := by
    apply Scheme.Modules.epi_freeHomOfSections_of_span
    intro U
    have hspan :=
      (Scheme.Modules.surjective_finFreeSectionsMap'_iff φ U.1).mp (hsurj U)
    refine hspan.ge.trans (Submodule.span_mono ?_)
    rintro _ ⟨i, rfl⟩
    refine ⟨ULift.up i, ?_⟩
    simpa only [φ] using (Scheme.Modules.freeGen_freeHomOfSections s U.1 i).symm
  exact hRankQ.rank_le_of_epi_finFree φ hT

end AlgebraicGeometry.ProjectiveSpace

end

end
