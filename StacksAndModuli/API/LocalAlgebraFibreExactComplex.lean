module

public import StacksAndModuli.API.LocalResidueFibreExactComplex

/-!
# Exactness detected by a local algebra fibre

Let `R → A` be a local homomorphism of local rings.  Tensoring a finite `R`-module with
`A` detects whether the module is zero: after passing to residue fields this is faithful
flat descent along the field extension `κ(R) → κ(A)`, followed by Nakayama over `R`.

Consequently, the bounded-complex argument of `CochainComplex.exactAtSucc_of_residueField`
does not require the detecting fibre to be literally `κ(R)`.  Exactness after base change
to any local `R`-algebra whose structure map is local already implies ordinary exactness,
flatness of all cocycle modules, and exactness after every further base change.  This form is
useful when a geometric fibre is presented as a localization of a tensor-product ring rather
than as the residue field in a syntactically canonical way.

Main declarations:

* `Module.subsingleton_of_localAlgebra_tensor`;
* `CochainComplex.exactAtSucc_of_localAlgebra`;
* `CochainComplex.flat_cocyclesSub_of_localAlgebra`;
* `CochainComplex.exactAtSucc_baseChange_of_localAlgebra`;
* `CochainComplex.strictlyPerfectReplacementOfLocalAlgebraExact_of_finite_terms`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open TensorProduct

namespace Module

/-- A local algebra detects vanishing of finite modules.  The proof passes to the two
residue fields, reflects vanishing along their faithfully flat field extension, and then
applies Nakayama over the source local ring. -/
theorem subsingleton_of_localAlgebra_tensor
    {R A N : Type u} [CommRing R] [IsLocalRing R]
    [CommRing A] [IsLocalRing A] [Algebra R A]
    [IsLocalHom (algebraMap R A)]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    (h : Subsingleton (A ⊗[R] N)) :
    Subsingleton N := by
  let kR := IsLocalRing.ResidueField R
  let kA := IsLocalRing.ResidueField A
  letI : Subsingleton (A ⊗[R] N) := h
  have hkA : Subsingleton (kA ⊗[R] N) := by
    let e := AlgebraTensorModule.cancelBaseChange R A kA kA N
    exact e.toEquiv.subsingleton_congr.mp inferInstance
  have hfield : Subsingleton (kA ⊗[kR] (kR ⊗[R] N)) := by
    let e := AlgebraTensorModule.cancelBaseChange R kR kA kA N
    exact e.toEquiv.subsingleton_congr.mpr hkA
  haveI : Module.FaithfullyFlat kR kA :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hkR : Subsingleton (kR ⊗[R] N) :=
    (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right kR kA).mp hfield
  exact IsLocalRing.subsingleton_tensorProduct.mp hkR

end Module

namespace AlgebraicGeometry.ProjectiveSpace.CochainComplex

open CategoryTheory

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Exactness after base change to a local `R`-algebra detects exactness of a bounded
complex of flat modules with finite cohomology. -/
theorem exactAtSucc_of_localAlgebra
    (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (hflat : ∀ p : ℕ, Module.Flat R (C.X p)) {N : ℕ}
    (hvan : ∀ p : ℕ, N < p → Subsingleton (C.X p))
    (hfin : ∀ j : ℕ, Module.Finite R (cohomologySucc C j))
    (A : Type u) [CommRing A] [IsLocalRing A] [Algebra R A]
    [IsLocalHom (algebraMap R A)]
    (hfib : ∀ j : ℕ,
      ExactAtSucc (GradedModule.cochainBaseChange A C) j) :
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
          apply Module.subsingleton_of_localAlgebra_tensor
            (R := R) (A := A) (N := cohomologySucc C j)
          exact subsingleton_baseChange_cohomologySucc C hflat hvan j habove A (hfib j)
  exact fun j ↦ key N j (by omega)

/-- Under the hypotheses of `exactAtSucc_of_localAlgebra`, every cocycle module is flat
over the source local ring. -/
theorem flat_cocyclesSub_of_localAlgebra
    (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (hflat : ∀ p : ℕ, Module.Flat R (C.X p)) {N : ℕ}
    (hvan : ∀ p : ℕ, N < p → Subsingleton (C.X p))
    (hfin : ∀ j : ℕ, Module.Finite R (cohomologySucc C j))
    (A : Type u) [CommRing A] [IsLocalRing A] [Algebra R A]
    [IsLocalHom (algebraMap R A)]
    (hfib : ∀ j : ℕ,
      ExactAtSucc (GradedModule.cochainBaseChange A C) j)
    (i : ℕ) :
    Module.Flat R (cocyclesSub C i) := by
  exact flat_cocyclesSub hflat hvan (t := 0)
    (fun j _hj ↦ exactAtSucc_of_localAlgebra C hflat hvan hfin A hfib j)
    (Nat.zero_le i)

/-- Once one local algebra fibre is exact, every ring base change of the bounded complex
is exact. -/
theorem exactAtSucc_baseChange_of_localAlgebra
    (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (hflat : ∀ p : ℕ, Module.Flat R (C.X p)) {N : ℕ}
    (hvan : ∀ p : ℕ, N < p → Subsingleton (C.X p))
    (hfin : ∀ j : ℕ, Module.Finite R (cohomologySucc C j))
    (A : Type u) [CommRing A] [IsLocalRing A] [Algebra R A]
    [IsLocalHom (algebraMap R A)]
    (hfib : ∀ j : ℕ,
      ExactAtSucc (GradedModule.cochainBaseChange A C) j)
    (B : Type u) [CommRing B] [Algebra R B] (j : ℕ) :
    ExactAtSucc (GradedModule.cochainBaseChange B C) j := by
  rw [ExactAtSucc, cocyclesSub, cochainBaseChange_d_hom,
    cochainBaseChange_d_hom]
  apply range_baseChange_d_eq_ker B hflat hvan (t := 0)
  · intro i _hi
    exact exactAtSucc_of_localAlgebra C hflat hvan hfin A hfib i
  · exact Nat.zero_le j

/-- The cocycles after an arbitrary base change are canonically the base change of the
original cocycles once one local algebra fibre is exact. -/
noncomputable def cocyclesBaseChangeEquiv_of_localAlgebra
    (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (hflat : ∀ p : ℕ, Module.Flat R (C.X p)) {N : ℕ}
    (hvan : ∀ p : ℕ, N < p → Subsingleton (C.X p))
    (hfin : ∀ j : ℕ, Module.Finite R (cohomologySucc C j))
    (A : Type u) [CommRing A] [IsLocalRing A] [Algebra R A]
    [IsLocalHom (algebraMap R A)]
    (hfib : ∀ j : ℕ,
      ExactAtSucc (GradedModule.cochainBaseChange A C) j)
    (B : Type u) [CommRing B] [Algebra R B] (i : ℕ) :
    (B ⊗[R] cocyclesSub C i) ≃ₗ[B]
      cocyclesSub (GradedModule.cochainBaseChange B C) i :=
  cocyclesBaseChangeEquiv C hflat hvan
    (fun j ↦ exactAtSucc_of_localAlgebra C hflat hvan hfin A hfib j) B i

/-- A bounded flat complex whose local-algebra fibre is exact and whose zeroth homology is
finite projective admits a universal strictly perfect replacement concentrated in degree
zero. -/
noncomputable def strictlyPerfectReplacementOfLocalAlgebraExact
    (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (hflat : ∀ p : ℕ, Module.Flat R (C.X p)) {N : ℕ}
    (hvan : ∀ p : ℕ, N < p → Subsingleton (C.X p))
    (hfin : ∀ j : ℕ, Module.Finite R (cohomologySucc C j))
    (A : Type u) [CommRing A] [IsLocalRing A] [Algebra R A]
    [IsLocalHom (algebraMap R A)]
    (hfib : ∀ j : ℕ,
      ExactAtSucc (GradedModule.cochainBaseChange A C) j)
    (hfinite : Module.Finite R (C.homology 0))
    (hprojective : Module.Projective R (C.homology 0)) :
    StrictlyPerfectReplacement C :=
  strictlyPerfectReplacementOfExact C hflat hvan
    (exactAtSucc_of_localAlgebra C hflat hvan hfin A hfib) hfinite hprojective

/-- Over a noetherian local ring, finite flat terms and exactness after extension to one
local algebra produce a universal strictly perfect replacement.  Finiteness of the terms
supplies finite cohomology, while local-algebra exactness supplies flat cocycles. -/
noncomputable def strictlyPerfectReplacementOfLocalAlgebraExact_of_finite_terms
    [IsNoetherianRing R]
    (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (hfinite : ∀ p : ℕ, Module.Finite R (C.X p))
    (hflat : ∀ p : ℕ, Module.Flat R (C.X p)) {N : ℕ}
    (hvan : ∀ p : ℕ, N < p → Subsingleton (C.X p))
    (A : Type u) [CommRing A] [IsLocalRing A] [Algebra R A]
    [IsLocalHom (algebraMap R A)]
    (hfib : ∀ j : ℕ,
      ExactAtSucc (GradedModule.cochainBaseChange A C) j) :
    StrictlyPerfectReplacement C := by
  have hfin : ∀ j : ℕ, Module.Finite R (cohomologySucc C j) :=
    finite_cohomologySucc_of_finite_terms C hfinite
  haveI hfiniteZ : Module.Finite R (cocyclesSub C 0) := by
    letI : Module.Finite R (C.X 0) := hfinite 0
    exact Module.Finite.of_fg (IsNoetherian.noetherian _)
  haveI hflatZ : Module.Flat R (cocyclesSub C 0) :=
    flat_cocyclesSub_of_localAlgebra C hflat hvan hfin A hfib 0
  haveI hfpZ : Module.FinitePresentation R (cocyclesSub C 0) :=
    Module.finitePresentation_of_finite R _
  haveI hprojZ : Module.Projective R (cocyclesSub C 0) :=
    Module.Flat.projective_of_finitePresentation
  have hfiniteH : Module.Finite R (C.homology 0) :=
    Module.Finite.equiv (homologyZeroEquiv C).symm
  have hprojectiveH : Module.Projective R (C.homology 0) :=
    Module.Projective.of_equiv' (homologyZeroEquiv C).symm
  exact strictlyPerfectReplacementOfLocalAlgebraExact C hflat hvan hfin A hfib
    hfiniteH hprojectiveH

end AlgebraicGeometry.ProjectiveSpace.CochainComplex

end

end
