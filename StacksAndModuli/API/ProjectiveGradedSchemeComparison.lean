module

public import StacksAndModuli.API.ProjectiveGradedFamilies
public import StacksAndModuli.API.ProjectiveSheafGlobalSectionsBaseChange
public import StacksAndModuli.API.ProjectiveSpaceOverSpecComparison

/-!
# Comparing graded and scheme-theoretic projective cohomology

`ProjectiveGradedFamilies` packages relative cohomology in the graded-module model, while
`ProjectiveSheafGlobalSectionsBaseChange` records the scheme-level conclusion needed by the
Hilbert and Quot arguments.  This file isolates the comparison between those two models.

The structure `RelativeCohomology.SchemeGlobalSectionsComparison` records only the two
degreewise `H⁰` identifications: over the base ring and over every field-valued base change.
From these identifications, relative Serre vanishing and Cohomology and Base Change transport
formally to eventual finite-projective scheme global sections and their base-change
equivalences.

Constructing the comparison for a general finitely presented quasicoherent sheaf still needs
the missing graded-module/sheafification equivalence and its compatibility with pullback and
global sections.  The transfer theorem here is independent of that construction and contains
no additional cohomological assumptions.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory TensorProduct TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- Degreewise comparison between the relative graded `H⁰` model of a projective-space
sheaf and its actual scheme-theoretic global sections, including every field-valued base
change.

No compatibility square is required as data: the eventual scheme-level base-change
equivalence is obtained by conjugating the graded comparison with these equivalences. -/
structure RelativeCohomology.SchemeGlobalSectionsComparison
    {R : Type u} [CommRing R] (Crel : RelativeCohomology R) {n : ℕ}
    (M : GradedModule R n)
    (Q : (Scheme.projectiveSpaceOver n (Spec (.of R))).Modules) : Type (u + 1) where
  /-- The degree from which the comparison is asserted.  The transfer below only ever uses
  the comparison in large degrees, so a bound costs nothing and lets the comparison be
  constructed in the range where both sides are computed. -/
  bound : ℕ
  /-- Relative graded `H⁰` agrees with actual global sections over the base. -/
  globalSectionsIso : ∀ d : ℕ, bound ≤ d →
    letI := Scheme.Modules.globalSectionsModule
      (Scheme.projectiveSpaceOverπ n (Spec (.of R)))
      (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))
    ((Crel.Hgr M 0).obj (d : ℤ)) ≃ₗ[R]
      Scheme.Modules.projectiveSpaceTwistedGlobalSections Q (d : ℤ)
  /-- Fibrewise graded `H⁰` agrees with actual global sections after coefficient change. -/
  fibreGlobalSectionsIso : ∀ (K : Type u) [Field K] (f : R →+* K) (d : ℕ), bound ≤ d →
    letI : Algebra R K := f.toAlgebra
    let QK := Scheme.Modules.projectiveSpaceBaseChangeOfRingHom Q f
    letI := Scheme.Modules.globalSectionsModule
      (Scheme.projectiveSpaceOverπ n (Spec (.of K)))
      (Scheme.projectiveSpaceOverTwistModule QK (d : ℤ))
    ((Crel.fibre K).Hgr (M.baseChange K) 0).obj (d : ℤ) ≃ₗ[K]
      Scheme.Modules.projectiveSpaceTwistedGlobalSections QK (d : ℤ)

namespace RelativeCohomology.SchemeGlobalSectionsComparison

variable {R : Type u} [CommRing R] {Crel : RelativeCohomology R} {n : ℕ}
variable {M : GradedModule R n}
variable {Q : (Scheme.projectiveSpaceOver n (Spec (.of R))).Modules}

/-- A coherent flat graded family with a scheme-level `H⁰` comparison has eventual
finite-projective global sections on projective space, and their formation commutes with
every field-valued coefficient change.

This is the formal transfer from `RelativeCohomology.cbc` to the scheme-level interface used
by the Hilbert and Quot projectivity arguments. -/
noncomputable def toHasEventualFiniteProjectiveGlobalSectionsBaseChange
    (E : Crel.SchemeGlobalSectionsComparison M Q)
    (hM : Crel.IsCoherent M) (hflat : Crel.IsFlat M) :
    Scheme.Modules.HasEventualFiniteProjectiveGlobalSectionsBaseChange Q := by
  let d₀ := Classical.choose (Crel.uniform_serre_vanishing M hM hflat)
  have hd₀ := Classical.choose_spec (Crel.uniform_serre_vanishing M hM hflat)
  refine
    { bound := max d₀.toNat E.bound
      finite := ?_
      projective := ?_
      baseChangeIso := ?_ }
  · intro d hd
    have hd1 : d₀.toNat ≤ d := le_trans (le_max_left _ _) hd
    have hdE : E.bound ≤ d := le_trans (le_max_right _ _) hd
    letI := Scheme.Modules.globalSectionsModule
      (Scheme.projectiveSpaceOverπ n (Spec (.of R)))
      (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))
    have hd' : d₀ ≤ (d : ℤ) := by omega
    obtain ⟨-, hfinite, -, -⟩ := Crel.cbc M (d : ℤ) hM hflat
      (fun K _ _ i hi ↦ hd₀ K i hi (d : ℤ) hd')
    letI : Module.Finite R ((Crel.Hgr M 0).obj (d : ℤ)) := hfinite
    exact Module.Finite.equiv (E.globalSectionsIso d hdE)
  · intro d hd
    have hd1 : d₀.toNat ≤ d := le_trans (le_max_left _ _) hd
    have hdE : E.bound ≤ d := le_trans (le_max_right _ _) hd
    letI := Scheme.Modules.globalSectionsModule
      (Scheme.projectiveSpaceOverπ n (Spec (.of R)))
      (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))
    have hd' : d₀ ≤ (d : ℤ) := by omega
    obtain ⟨-, -, hprojective, -⟩ := Crel.cbc M (d : ℤ) hM hflat
      (fun K _ _ i hi ↦ hd₀ K i hi (d : ℤ) hd')
    letI : Module.Projective R ((Crel.Hgr M 0).obj (d : ℤ)) := hprojective
    exact Module.Projective.of_equiv (E.globalSectionsIso d hdE)
  · intro K _ f d hd
    have hd1 : d₀.toNat ≤ d := le_trans (le_max_left _ _) hd
    have hdE : E.bound ≤ d := le_trans (le_max_right _ _) hd
    letI : Algebra R K := f.toAlgebra
    let QK := Scheme.Modules.projectiveSpaceBaseChangeOfRingHom Q f
    letI := Scheme.Modules.globalSectionsModule
      (Scheme.projectiveSpaceOverπ n (Spec (.of R)))
      (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))
    letI := Scheme.Modules.globalSectionsModule
      (Scheme.projectiveSpaceOverπ n (Spec (.of K)))
      (Scheme.projectiveSpaceOverTwistModule QK (d : ℤ))
    have hd' : d₀ ≤ (d : ℤ) := by omega
    obtain ⟨-, -, -, hbc⟩ := Crel.cbc M (d : ℤ) hM hflat
      (fun L _ _ i hi ↦ hd₀ L i hi (d : ℤ) hd')
    exact
      ((E.globalSectionsIso d hdE).symm.baseChange R K).trans
        ((Crel.baseChangeIso M (d : ℤ) hbc K).toLinearEquiv.trans
          (E.fibreGlobalSectionsIso K f d hdE))

end RelativeCohomology.SchemeGlobalSectionsComparison

end AlgebraicGeometry.ProjectiveSpace
