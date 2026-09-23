module

public import StacksAndModuli.API.QuotFunctorPrecomposition

/-!
# Quot functors under an isomorphism of ambient sheaves

Precomposition by an isomorphism of ambient sheaves is a natural isomorphism on
both the ordinary and fixed-Hilbert-polynomial Quot functors.  This file derives
the fixed-polynomial comparison from the image characterization in
`QuotFunctorPrecomposition`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules.QuotientPullbackData

variable {X S : Scheme.{u}} {F G : X.Modules} {f : X ⟶ S}

/-- Pulling back an isomorphism of ambient sheaves gives an isomorphism on every
Quot parameter space. -/
instance ambientMap_isIso (p : G ⟶ F) [IsIso p] (T : Over S) :
    IsIso (ambientMap (f := f) p T) := by
  dsimp [ambientMap]
  infer_instance

end AlgebraicGeometry.Scheme.Modules.QuotientPullbackData

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

/-- Precomposition by an isomorphism of ambient sheaves is surjective on every
fixed-polynomial Quot set. -/
theorem quotFunctorPPrecomp_app_surjective_of_isIso {n : ℕ}
    {F G : (projectiveSpaceOver n S).Modules} (p : G ⟶ F) [IsIso p]
    (P : Polynomial ℚ) (T : (Over S)ᵒᵖ) :
    Function.Surjective ((quotFunctorPPrecomp p P).app T) := by
  intro z
  obtain ⟨y, hy⟩ := Quotient.exists_rep z.1
  have hz : QuotientClassKillsAmbientKernel p T.unop z.1 := by
    refine ⟨y, hy, ?_⟩
    rw [kernel.ι_of_mono, zero_comp]
  simpa using
    (mem_range_quotFunctorPPrecomp_app_iff p P T.unop z).2 hz

/-- Precomposition by an isomorphism of ambient sheaves is bijective on every
fixed-polynomial Quot set. -/
theorem quotFunctorPPrecomp_app_bijective_of_isIso {n : ℕ}
    {F G : (projectiveSpaceOver n S).Modules} (p : G ⟶ F) [IsIso p]
    (P : Polynomial ℚ) (T : (Over S)ᵒᵖ) :
    Function.Bijective ((quotFunctorPPrecomp p P).app T) :=
  ⟨quotFunctorPPrecomp_app_injective p P T,
    quotFunctorPPrecomp_app_surjective_of_isIso p P T⟩

/-- Isomorphic ambient sheaves define naturally isomorphic fixed-polynomial
Quot functors.  The forward map precomposes quotient presentations with the
given ambient isomorphism. -/
noncomputable def quotFunctorPIsoOfIso {n : ℕ}
    {F G : (projectiveSpaceOver n S).Modules} (p : G ⟶ F) [IsIso p]
    (P : Polynomial ℚ) :
    quotFunctorP F P ≅ quotFunctorP G P :=
  NatIso.ofComponents
    (fun T ↦ (Equiv.ofBijective ((quotFunctorPPrecomp p P).app T)
      (quotFunctorPPrecomp_app_bijective_of_isIso p P T)).toIso)
    (fun {_ _} g ↦ (quotFunctorPPrecomp p P).naturality g)

@[simp]
theorem quotFunctorPIsoOfIso_hom_app {n : ℕ}
    {F G : (projectiveSpaceOver n S).Modules} (p : G ⟶ F) [IsIso p]
    (P : Polynomial ℚ) (T : (Over S)ᵒᵖ) :
    (quotFunctorPIsoOfIso p P).hom.app T = (quotFunctorPPrecomp p P).app T :=
  rfl

/-- Representability transports across an isomorphism of the ambient sheaf. -/
noncomputable def quotFunctorP_representableBy_of_iso {n : ℕ}
    {F G : (projectiveSpaceOver n S).Modules} (p : G ⟶ F) [IsIso p]
    (P : Polynomial ℚ) (Q : Over S)
    (h : (quotFunctorP F P).RepresentableBy Q) :
    (quotFunctorP G P).RepresentableBy Q :=
  h.ofIso (quotFunctorPIsoOfIso p P)

end AlgebraicGeometry.Scheme

end
