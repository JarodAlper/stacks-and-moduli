module

public import StacksAndModuli.API.ProjectiveGradedStrictlyPerfectExact

/-!
# Exactness from one local residue fibre

For a finite module over a local ring, Nakayama's lemma says that vanishing after tensoring
with the residue field implies vanishing.  Applying this observation in the descending
argument for a bounded complex of flat modules shows that exactness on the single closed
fibre already implies exactness over the local ring.

This is the local form of the homological step in Stacks Project tag 00MI.  It complements
`CochainComplex.exactAtSucc_of_fibrewise`, which assumes exactness after every field-valued
base change over a not-necessarily-local ring.

Main declarations:

* `Module.subsingleton_of_residueField_tensor`;
* `CochainComplex.exactAtSucc_of_residueField`;
* `CochainComplex.flat_cocyclesSub_of_residueField`.
* `CochainComplex.exactAtSucc_baseChange_of_residueField`.
* `CochainComplex.strictlyPerfectReplacementOfResidueFieldExact`.
* `CochainComplex.strictlyPerfectReplacementOfResidueFieldExact_of_finite_terms`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open TensorProduct

namespace Module

/-- Nakayama in tensor form: a finite module over a local ring vanishes if its residue-field
base change vanishes. -/
theorem subsingleton_of_residueField_tensor
    {R N : Type u} [CommRing R] [IsLocalRing R]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    (h : Subsingleton (IsLocalRing.ResidueField R ⊗[R] N)) :
    Subsingleton N := by
  let m := IsLocalRing.maximalIdeal R
  have htensor : Subsingleton ((R ⧸ m) ⊗[R] N) := by
    simpa only [m, IsLocalRing.ResidueField] using h
  letI : Subsingleton ((R ⧸ m) ⊗[R] N) := htensor
  have hquot : Subsingleton (N ⧸ m • (⊤ : Submodule R N)) := by
    simpa only [m, IsLocalRing.ResidueField] using
      (TensorProduct.quotTensorEquivQuotSMul N m).symm.injective.subsingleton
  have htop : (⊤ : Submodule R N) = m • (⊤ : Submodule R N) := by
    apply le_antisymm
    · intro x _hx
      rw [← Submodule.Quotient.mk_eq_zero]
      exact Subsingleton.elim _ 0
    · exact le_top
  have hbot : (⊤ : Submodule R N) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot m ⊤ Module.Finite.fg_top
      htop.le (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  constructor
  intro x y
  have hxy : x - y ∈ (⊤ : Submodule R N) := Submodule.mem_top
  rw [hbot] at hxy
  exact sub_eq_zero.mp (by simpa using hxy)

end Module

namespace AlgebraicGeometry.ProjectiveSpace.CochainComplex

open CategoryTheory

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Exactness on the residue-field fibre of a bounded complex of flat modules with finite
cohomology implies exactness over the local ring.

The proof is the same descending argument as `exactAtSucc_of_fibrewise`, but at each step
local Nakayama needs only the unique closed fibre. -/
theorem exactAtSucc_of_residueField
    (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (hflat : ∀ p : ℕ, Module.Flat R (C.X p)) {N : ℕ}
    (hvan : ∀ p : ℕ, N < p → Subsingleton (C.X p))
    (hfin : ∀ j : ℕ, Module.Finite R (cohomologySucc C j))
    (hfib : ∀ j : ℕ,
      ExactAtSucc
        (GradedModule.cochainBaseChange (IsLocalRing.ResidueField R) C) j) :
    ∀ j : ℕ, ExactAtSucc C j := by
  have key : ∀ (m j : ℕ), N ≤ j + m → ExactAtSucc C j := by
    intro m
    induction m with
    | zero =>
        intro j hj
        exact exactAtSucc_of_subsingleton_X (hvan (j + 1) (by omega))
    | succ m ih =>
        intro j hj
        rcases le_or_gt N j with hNj | hNj
        · exact exactAtSucc_of_subsingleton_X (hvan (j + 1) (by omega))
        · have habove : ∀ i : ℕ, j + 1 ≤ i → ExactAtSucc C i :=
            fun i hi ↦ ih i (by omega)
          rw [← subsingleton_cohomologySucc_iff]
          letI : Module.Finite R (cohomologySucc C j) := hfin j
          apply Module.subsingleton_of_residueField_tensor
            (R := R) (N := cohomologySucc C j)
          exact subsingleton_baseChange_cohomologySucc C hflat hvan j habove
            (IsLocalRing.ResidueField R) (hfib j)
  exact fun j ↦ key N j (by omega)

/-- Under the hypotheses of `exactAtSucc_of_residueField`, every cocycle module of the
bounded complex is flat over the local base ring. -/
theorem flat_cocyclesSub_of_residueField
    (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (hflat : ∀ p : ℕ, Module.Flat R (C.X p)) {N : ℕ}
    (hvan : ∀ p : ℕ, N < p → Subsingleton (C.X p))
    (hfin : ∀ j : ℕ, Module.Finite R (cohomologySucc C j))
    (hfib : ∀ j : ℕ,
      ExactAtSucc
        (GradedModule.cochainBaseChange (IsLocalRing.ResidueField R) C) j)
    (i : ℕ) :
    Module.Flat R (cocyclesSub C i) := by
  exact flat_cocyclesSub hflat hvan (t := 0)
    (fun j _hj ↦ exactAtSucc_of_residueField C hflat hvan hfin hfib j)
    (Nat.zero_le i)

omit [IsLocalRing R] in
/-- Over a noetherian ring, finite terms make the concrete positive cohomology modules of
 a cochain complex finite.  This is the finiteness input needed by the local Nakayama
 argument below. -/
theorem finite_cohomologySucc_of_finite_terms [IsNoetherianRing R]
    (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (hfinite : ∀ p : ℕ, Module.Finite R (C.X p)) (j : ℕ) :
    Module.Finite R (cohomologySucc C j) := by
  letI : Module.Finite R (C.X (j + 1)) := hfinite (j + 1)
  letI : Module.Finite R (cocyclesSub C (j + 1)) :=
    Module.Finite.of_fg (IsNoetherian.noetherian _)
  exact Module.Finite.of_surjective _ (Submodule.mkQ_surjective _)

/-- Once the residue-field fibre of the local bounded complex is exact, every ring base
change of the complex remains exact. -/
theorem exactAtSucc_baseChange_of_residueField
    (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (hflat : ∀ p : ℕ, Module.Flat R (C.X p)) {N : ℕ}
    (hvan : ∀ p : ℕ, N < p → Subsingleton (C.X p))
    (hfin : ∀ j : ℕ, Module.Finite R (cohomologySucc C j))
    (hfib : ∀ j : ℕ,
      ExactAtSucc
        (GradedModule.cochainBaseChange (IsLocalRing.ResidueField R) C) j)
    (A : Type u) [CommRing A] [Algebra R A] (j : ℕ) :
    ExactAtSucc (GradedModule.cochainBaseChange A C) j := by
  rw [ExactAtSucc, cocyclesSub, cochainBaseChange_d_hom,
    cochainBaseChange_d_hom]
  apply range_baseChange_d_eq_ker A hflat hvan (t := 0)
  · intro i _hi
    exact exactAtSucc_of_residueField C hflat hvan hfin hfib i
  · exact Nat.zero_le j

/-- The cocycles of any base change are canonically the base change of the original
cocycles once the local residue fibre is exact. -/
noncomputable def cocyclesBaseChangeEquiv_of_residueField
    (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (hflat : ∀ p : ℕ, Module.Flat R (C.X p)) {N : ℕ}
    (hvan : ∀ p : ℕ, N < p → Subsingleton (C.X p))
    (hfin : ∀ j : ℕ, Module.Finite R (cohomologySucc C j))
    (hfib : ∀ j : ℕ,
      ExactAtSucc
        (GradedModule.cochainBaseChange (IsLocalRing.ResidueField R) C) j)
    (A : Type u) [CommRing A] [Algebra R A] (i : ℕ) :
    (A ⊗[R] cocyclesSub C i) ≃ₗ[A]
      cocyclesSub (GradedModule.cochainBaseChange A C) i :=
  cocyclesBaseChangeEquiv C hflat hvan
    (fun j ↦ exactAtSucc_of_residueField C hflat hvan hfin hfib j) A i

/-- A bounded flat complex whose residue-field fibre is exact and whose zeroth homology is
finite projective admits a universal strictly perfect replacement concentrated in degree
zero.  This is the local-residue-field entry point to
`strictlyPerfectReplacementOfExact`. -/
noncomputable def strictlyPerfectReplacementOfResidueFieldExact
    (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (hflat : ∀ p : ℕ, Module.Flat R (C.X p)) {N : ℕ}
    (hvan : ∀ p : ℕ, N < p → Subsingleton (C.X p))
    (hfin : ∀ j : ℕ, Module.Finite R (cohomologySucc C j))
    (hfib : ∀ j : ℕ,
      ExactAtSucc
        (GradedModule.cochainBaseChange (IsLocalRing.ResidueField R) C) j)
    (hfinite : Module.Finite R (C.homology 0))
    (hprojective : Module.Projective R (C.homology 0)) :
    StrictlyPerfectReplacement C :=
  strictlyPerfectReplacementOfExact C hflat hvan
    (exactAtSucc_of_residueField C hflat hvan hfin hfib) hfinite hprojective

/-- A bounded complex of finite flat modules over a noetherian local ring admits a universal
strictly perfect replacement as soon as its residue-field fibre is exact in positive
degrees.  Finiteness of the terms makes the cocycles finite, while residue-fibre exactness
makes them flat; finite flat modules over a noetherian ring are projective. -/
noncomputable def strictlyPerfectReplacementOfResidueFieldExact_of_finite_terms
    [IsNoetherianRing R]
    (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (hfinite : ∀ p : ℕ, Module.Finite R (C.X p))
    (hflat : ∀ p : ℕ, Module.Flat R (C.X p)) {N : ℕ}
    (hvan : ∀ p : ℕ, N < p → Subsingleton (C.X p))
    (hfib : ∀ j : ℕ,
      ExactAtSucc
        (GradedModule.cochainBaseChange (IsLocalRing.ResidueField R) C) j) :
    StrictlyPerfectReplacement C := by
  have hfin : ∀ j : ℕ, Module.Finite R (cohomologySucc C j) :=
    finite_cohomologySucc_of_finite_terms C hfinite
  haveI hfiniteZ : Module.Finite R (cocyclesSub C 0) := by
    letI : Module.Finite R (C.X 0) := hfinite 0
    exact Module.Finite.of_fg (IsNoetherian.noetherian _)
  haveI hflatZ : Module.Flat R (cocyclesSub C 0) :=
    flat_cocyclesSub_of_residueField C hflat hvan hfin hfib 0
  haveI hfpZ : Module.FinitePresentation R (cocyclesSub C 0) :=
    Module.finitePresentation_of_finite R _
  haveI hprojZ : Module.Projective R (cocyclesSub C 0) :=
    Module.Flat.projective_of_finitePresentation
  have hfiniteH : Module.Finite R (C.homology 0) :=
    Module.Finite.equiv (homologyZeroEquiv C).symm
  have hprojectiveH : Module.Projective R (C.homology 0) :=
    Module.Projective.of_equiv' (homologyZeroEquiv C).symm
  exact strictlyPerfectReplacementOfResidueFieldExact C hflat hvan hfin hfib
    hfiniteH hprojectiveH

end AlgebraicGeometry.ProjectiveSpace.CochainComplex

end

end
