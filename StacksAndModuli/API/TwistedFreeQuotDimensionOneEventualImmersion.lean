module

public import StacksAndModuli.API.ProjectiveDimensionOneMultiplicationEpi
public import StacksAndModuli.API.TwistedFreeQuotEventualCanonicalInputsAndKernelGeneration
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianEventualPackageFromOneStepGeometry

/-!
# Eventual Quot-to-Grassmannian immersion in projective dimension one

This file assembles the parts of the eventual immersion argument which are specific to
projective dimension one.  In that dimension, one nonempty fixed-polynomial Quot family
supplies the polynomial numerics, and the two adjacent rank conditions determine the whole
field-valued Hilbert function.  Multiplication surjectivity on actual Quot families is then
derived from the adjacent base-change comparison, so the remaining universal geometry has
only two fields: that comparison and relative flatness persistence.

The arbitrary-base noetherian model and kernel-generation hypotheses remain explicit.  They
are precisely the hypotheses supplied by the spreading-out step, independently of the
dimension-one field calculation.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The universal one-step assertions which remain in projective dimension one after the
field-growth theorem and multiplication-surjectivity theorem have been extracted from the
twisted-free presentation. -/
structure TwistedFreeQuotUniversalDimensionOneGeometry
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) : Type (u + 1) where
  /-- Base change for the two adjacent pushforwards and their multiplication. -/
  multiplicationBaseChange :
    Modules.ProjectiveOneStepMultiplicationBaseChangeComparison n
      (twistedFreeQuotUniversalReconstructedQuotient n S l r P d e he) d
  /-- Relative flatness persistence from the one-step rank conditions. -/
  flatnessPersistence : Modules.ProjectiveOneStepFlatnessPersistenceEpi n
    (twistedFreeQuotUniversalReconstructedQuotient n S l r P d e he) P d

/-- In projective dimension one, the field-growth theorem fills the only omitted field of
`TwistedFreeQuotUniversalDimensionOneGeometry`. -/
noncomputable def TwistedFreeQuotUniversalDimensionOneGeometry.toReducedGeometry
    {n : ℕ} (hn : 0 < n) (hn₁ : n ≤ 1)
    {S : Scheme.{u}} {l : ℤ} {r : ℕ} {P : Polynomial ℚ}
    {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)}
    (G : TwistedFreeQuotUniversalDimensionOneGeometry n S l r P d e he)
    (hPdeg : P.natDegree ≤ n)
    (hPd : ((P.eval (d : ℚ)).num.natAbs : ℚ) = P.eval (d : ℚ))
    (hPsucc : ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs : ℚ) =
      P.eval ((d + 1 : ℕ) : ℚ))
    (I₁ : TwistedFreeQuotGrassmannianCanonicalInputs n S l r P
      (d + 1) (e + 1) (by omega)
      (r * (n + (e + 1)).choose n) (P.hilbertNatValue (d + 1))
      (twistedFreeMonomialIndexEquiv r ((n + (e + 1)).choose n))) :
    TwistedFreeQuotUniversalReducedOneStepFlatteningGeometry n S l r P d e he where
  multiplicationBaseChange := G.multiplicationBaseChange
  multiplicationEpi :=
    twistedFreeQuotUniversal_multiplicationEpi_of_dimension_le_one
      n hn hn₁ S l r P d e he G.multiplicationBaseChange I₁
  fieldGrowth :=
    twistedFreeQuotUniversal_fieldGrowth_of_dimension_le_one
      n hn hn₁ S l r P d e he hPdeg hPd hPsucc G.multiplicationBaseChange
  flatnessPersistence := G.flatnessPersistence

/-- In positive projective dimension at most one, eventual arbitrary-base noetherian models,
kernel generation, and the two genuinely relative one-step assertions give the complete
eventual Quot-to-Grassmannian immersion package.

The chosen Quot point is used only for the numerical rank inequality and for the eventual
natural-value and degree bounds of its Hilbert polynomial. -/
theorem
    hasEventualTwistedFreeQuotGrassmannianImmersionPackages_of_dimension_le_one
    (n : ℕ) (hn : 0 < n) (hn₁ : n ≤ 1)
    (S : Scheme.{u}) [IsLocallyNoetherian S]
    (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (T : Over S) (hT : Nonempty T.left)
    (z : (quotFunctorP (projectiveSpaceOverTwistedFree n S l r) P).obj (op T))
    (hmodel : ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ProjectiveSpace.HasUniversallyAffineNoetherianTwistedFreeQuotCechModel
        n r l P S d)
    (hkernel : ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (A : Over S)
        (a : Modules.QuotientPullbackData
          (Modules.QuotientPullbackData.twistedFreeAmbient
            (n := n) (r := r) (l := l))
          (projectiveSpaceOverπ n S) A),
        a.HasFiberwiseHilbertPolynomial P →
          TwistedFreeQuotKernelIsGloballyGenerated n A.left l r
            (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver
              A a) d)
    (hgeometry : ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (e : ℕ) (he : (d : ℤ) - l = (e : ℤ)),
        Nonempty (TwistedFreeQuotUniversalDimensionOneGeometry
          n S l r P d e he)) :
    HasEventualTwistedFreeQuotGrassmannianImmersionPackages n S l r P := by
  obtain ⟨a, _ha, hP⟩ := z.2
  obtain ⟨DI, hinputs⟩ :=
    exists_eventual_twistedFreeQuotGrassmannianCanonicalInputs_of_quotPoint_of_noetherianCechModel
      n S l r P hn hmodel T hT z
  let Q := twistedFreeQuotientSheaf n S l r a
  haveI hQfp : Q.IsFinitePresentation :=
    Modules.QuotientPullbackData.quotDataOnProjectiveSpace_isFinitePresentation_over T a
  let q :=
    Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T a
  haveI hqepi : Epi q :=
    Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver_epi T a
  obtain ⟨DP, hDP⟩ :=
    Modules.exists_eventual_hilbertPolynomial_numerics_of_dimension_le_one
      n r hn hn₁ T.left hT l Q q P hP
  obtain ⟨DG, hDG⟩ := hgeometry
  apply
    hasEventualTwistedFreeQuotGrassmannianImmersionPackages_of_universalReducedOneStepGeometry
      n S hn l r P ⟨DI, hinputs⟩ hkernel
  refine ⟨max DP (max DG DI), ?_⟩
  intro d hd e he
  obtain ⟨G⟩ := hDG d (by omega) e he
  obtain ⟨I₁⟩ := hinputs (d + 1) (by omega) (e + 1) (by omega)
  obtain ⟨_, hPdeg, hPd, hPsucc⟩ := hDP d (by omega)
  exact ⟨G.toReducedGeometry hn hn₁ hPdeg hPd hPsucc I₁⟩

end AlgebraicGeometry.Scheme

end

end
