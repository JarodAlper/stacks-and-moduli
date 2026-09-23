module

public import StacksAndModuli.API.TwistedFreeMonomialIndexEquiv
public import StacksAndModuli.API.TwistedFreeQuotNoetherianCechModel
public import StacksAndModuli.API.TwistedFreeQuotKernelGlobalGeneration
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianCanonicalPackageFromGeometry

/-!
# Eventual canonical inputs and kernel generation for twisted-free Quot

This file puts the two uniform regularity outputs used by the eventual
Quot-to-Grassmannian package into their exact canonical-index forms.

Universal affine noetherian Čech models give the full canonical fixed-degree
input package in every sufficiently large degree.  Separately, the uniform
relative-Serre theorem gives the required kernel evaluation epimorphism for every
normalized Quot family over a noetherian affine test scheme.  The latter statement
is deliberately kept affine: extending it to arbitrary test schemes requires
compatibility of the pullback--pushforward counit with restriction, followed by
noetherian approximation.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Eventual universal affine noetherian Čech models, together with one
nonempty fixed-polynomial Quot family, give the canonical monomial-indexed
Grassmannian inputs in every sufficiently large degree.  The family is used only
to obtain the necessary numerical inequality between the Hilbert rank and the
rank of the ambient finite free module. -/
theorem
    exists_eventual_twistedFreeQuotGrassmannianCanonicalInputs_of_noetherianCechModel
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (hn : 0 < n)
    (hmodel : ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      HasUniversallyAffineNoetherianTwistedFreeQuotCechModel n r l P S d)
    (T : Over S)
    (a : Scheme.Modules.QuotientPullbackData
      (Scheme.Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (Scheme.projectiveSpaceOverπ n S) T)
    (hP : a.HasFiberwiseHilbertPolynomial P) (hT : Nonempty T.left) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (e : ℕ) (he : (d : ℤ) - l = (e : ℤ)),
        Nonempty (Scheme.TwistedFreeQuotGrassmannianCanonicalInputs
          n S l r P d e he (r * (n + e).choose n)
            (P.hilbertNatValue d)
            (Scheme.twistedFreeMonomialIndexEquiv r ((n + e).choose n))) := by
  obtain ⟨d₀, hd₀0, hinputs⟩ :=
    exists_bound_twistedFreeQuotGrassmannianCanonicalInputs_of_noetherianCechModel
      n r hn l P
  obtain ⟨Dmodel, hmodel⟩ := hmodel
  refine ⟨max d₀.toNat Dmodel, ?_⟩
  intro d hd e he
  have hd₀d : d₀ ≤ (d : ℤ) := by
    rw [← Int.toNat_of_nonneg hd₀0]
    exact_mod_cast (show d₀.toNat ≤ d by omega)
  exact hinputs S d e he hd₀d
    (Scheme.twistedFreeMonomialIndexEquiv r ((n + e).choose n))
    (hmodel d (by omega)) T a hP hT

/-- Quot-functor form of
`exists_eventual_twistedFreeQuotGrassmannianCanonicalInputs_of_noetherianCechModel`.
It extracts the fixed-polynomial representative carried by a Quot point, so its
conclusion is the `hinputs` argument used verbatim by the eventual immersion
constructor. -/
theorem
    exists_eventual_twistedFreeQuotGrassmannianCanonicalInputs_of_quotPoint_of_noetherianCechModel
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (hn : 0 < n)
    (hmodel : ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      HasUniversallyAffineNoetherianTwistedFreeQuotCechModel n r l P S d)
    (T : Over S) (hT : Nonempty T.left)
    (z : (Scheme.quotFunctorP
      (Scheme.Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l)) P).obj (op T)) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (e : ℕ) (he : (d : ℤ) - l = (e : ℤ)),
        Nonempty (Scheme.TwistedFreeQuotGrassmannianCanonicalInputs
          n S l r P d e he (r * (n + e).choose n)
            (P.hilbertNatValue d)
            (Scheme.twistedFreeMonomialIndexEquiv r ((n + e).choose n))) := by
  obtain ⟨a, _ha, hP⟩ := z.2
  exact
    exists_eventual_twistedFreeQuotGrassmannianCanonicalInputs_of_noetherianCechModel
      n S l r P hn hmodel T a hP hT

/-- The uniform relative-Serre bound, specialized to the normalized quotient
attached to a Quot datum over a noetherian affine test scheme.  This is precisely
the kernel-generation hypothesis of the eventual Grassmannian construction on
that test subcategory. -/
theorem
    exists_eventual_twistedFreeQuotKernelIsGloballyGenerated_noetherianAffine
    (n r : ℕ) (hn : 0 < n) (l : ℤ) (P : Polynomial ℚ) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
        (S : Scheme.{u}) (f : Spec (.of R) ⟶ S)
        (a : Scheme.Modules.QuotientPullbackData
          (Scheme.Modules.QuotientPullbackData.twistedFreeAmbient
            (n := n) (r := r) (l := l))
          (Scheme.projectiveSpaceOverπ n S) (Over.mk f)),
        a.HasFiberwiseHilbertPolynomial P →
          Scheme.TwistedFreeQuotKernelIsGloballyGenerated
            n (Spec (.of R)) l r
              (Scheme.Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver
                (Over.mk f) a) d := by
  obtain ⟨D, hD⟩ :=
    exists_bound_pullbackPushforwardCounit_epi_twistedFreeQuotKernel_noetherian_affine
      n r hn l P
  refine ⟨D, ?_⟩
  intro d hd R _ _ S f a hP
  let T : Over S := Over.mk f
  let Q := Scheme.twistedFreeQuotientSheaf n S l r a
  let q := Scheme.Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver
    T a
  haveI hQfp : Q.IsFinitePresentation :=
    Scheme.Modules.QuotientPullbackData.quotDataOnProjectiveSpace_isFinitePresentation_over
      T a
  haveI hq : Epi q :=
    Scheme.Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver_epi T a
  have hflat : Q.FlatOver (Scheme.projectiveSpaceOverπ n (Spec (.of R))) :=
    Scheme.Modules.QuotientPullbackData.quotDataOnProjectiveSpace_flatOver_over T a
  exact hD d hd R Q hQfp q hq hflat hP

end AlgebraicGeometry.ProjectiveSpace

end

end
