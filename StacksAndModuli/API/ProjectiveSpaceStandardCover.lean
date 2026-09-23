module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.Topology.Sheaves.AddCommGrpCat

/-!
# The standard affine cover of `ℙⁿ`

`Proj` of the standard graded polynomial ring `R[x₀, …, xₙ]` is covered by the `n + 1` basic
opens `D₊(xᵢ)`.  This is the cover on which the graded model computes: the Čech complex of
`StacksAndModuli/API/ProjectiveGradedCech.lean` is the Čech complex of exactly this cover, so the
comparison `Γ(ℙⁿ, Q(d)) ≅ (Hgr M 0)_d` demanded by
`RelativeCohomology.SchemeGlobalSectionsComparison` is the sheaf axiom for it.

Mathlib supplies `AlgebraicGeometry.Proj.iSup_basicOpen_eq_top'` — a homogeneous family
generating `A` as an `A₀`-algebra gives a cover — and what is added here is the verification
for the variables of a polynomial ring: they are homogeneous of degree one and generate.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The variables are homogeneous of degree one for the total-degree grading. -/
lemma X_mem_homogeneousSubmodule (i : Fin (n + 1)) :
    (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) ∈
      MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 1 :=
  MvPolynomial.isHomogeneous_X R i

/-- The variables generate `R[x₀, …, xₙ]` as an algebra over the degree-zero part. -/
lemma adjoin_range_X_eq_top :
    Algebra.adjoin (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 0)
      (Set.range (fun i : Fin (n + 1) => (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R)))
      = ⊤ := by
  rw [eq_top_iff]
  rintro p -
  induction p using MvPolynomial.induction_on with
  | C r =>
      exact Subalgebra.algebraMap_mem _
        (⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C _ r⟩ :
          MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 0)
  | add p q hp hq => exact Subalgebra.add_mem _ hp hq
  | mul_X p i hp => exact Subalgebra.mul_mem _ hp (Algebra.subset_adjoin ⟨i, rfl⟩)

/-- **The standard affine cover of `ℙⁿ`.**  The `n + 1` basic opens `D₊(xᵢ)` cover
`Proj R[x₀, …, xₙ]`. -/
lemma iSup_basicOpen_X_eq_top :
    ⨆ i : Fin (n + 1),
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
          (MvPolynomial.X i) = ⊤ :=
  Proj.iSup_basicOpen_eq_top' _ _
    (fun i => ⟨1, X_mem_homogeneousSubmodule R n i⟩) (adjoin_range_X_eq_top R n)

/-! ## The sheaf axiom on the standard cover

These are the two halves of the equaliser description of `Γ(ℙⁿ, F)`: sections agreeing on all
the charts are equal, and a compatible family on the charts glues.  Together they say that
`Γ(ℙⁿ, F)` is the kernel of `∏ᵢ F(D₊(xᵢ)) ⇉ ∏_{i,j} F(D₊(xᵢ) ⊓ D₊(xⱼ))`, which is precisely
the degree-zero Čech group of the graded model. -/

variable {R n}

/-- Two global sections agreeing on every standard chart are equal. -/
theorem eq_of_locally_eq_standard
    (F : TopCat.Sheaf AddCommGrpCat.{u} (ProjectiveSpectrum.top
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)))
    (s t : F.obj.obj (Opposite.op ⊤))
    (h : ∀ i : Fin (n + 1),
      F.obj.map (homOfLE (le_top (a := Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)))).op s
        = F.obj.map (homOfLE (le_top (a := Proj.basicOpen
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)))).op t) :
    s = t :=
  F.eq_of_locally_eq'
    (fun i : Fin (n + 1) => Proj.basicOpen _ (MvPolynomial.X i)) ⊤
    (fun _ => homOfLE le_top) (le_of_eq (iSup_basicOpen_X_eq_top R n).symm) s t h

/-- A compatible family of sections on the standard charts glues uniquely. -/
theorem existsUnique_gluing_standard
    (F : TopCat.Sheaf AddCommGrpCat.{u} (ProjectiveSpectrum.top
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)))
    (s : ∀ i : Fin (n + 1),
      F.obj.obj (Opposite.op (Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i))))
    (hs : TopCat.Presheaf.IsCompatible F.obj
      (fun i : Fin (n + 1) => Proj.basicOpen _ (MvPolynomial.X i)) s) :
    ∃! g : F.obj.obj (Opposite.op ⊤), ∀ i : Fin (n + 1),
      F.obj.map (homOfLE (le_top (a := Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)))).op g
        = s i :=
  F.existsUnique_gluing'
    (fun i : Fin (n + 1) => Proj.basicOpen _ (MvPolynomial.X i)) ⊤
    (fun _ => homOfLE le_top) (le_of_eq (iSup_basicOpen_X_eq_top R n).symm) s hs

end AlgebraicGeometry.ProjectiveSpace
