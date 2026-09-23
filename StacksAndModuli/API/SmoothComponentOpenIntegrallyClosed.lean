module

public import StacksAndModuli.API.IrreducibleComponentNeighborhood
public import StacksAndModuli.API.SmoothAffineIntegrallyClosed

/-!
# Normal affine opens inside smooth curve components

An open contained in one irreducible component of a reduced scheme is integral once it
is nonempty.  If that open is affine, lies in the smooth locus over a field, and the
ambient scheme has dimension at most one, its ring of sections is integrally closed.

## Main results

* `AlgebraicGeometry.Scheme.Hom.smooth_comp_openImmersion_of_le_smoothLocus`:
  restricting a morphism to an open inside its smooth locus is smooth.
* `AlgebraicGeometry.Scheme.Opens.isIntegral_toScheme_of_nonempty_of_le_component`:
  a nonempty open inside an irreducible component of a reduced scheme is integral.
* `IsAffineOpen.isIntegrallyClosed_sections_of_le_component_of_le_smoothLocus`:
  an affine open inside a smooth component of a reduced curve has a normal ring of
  sections.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- Restricting a morphism to an open contained in its smooth locus gives a smooth
morphism. -/
theorem Hom.smooth_comp_openImmersion_of_le_smoothLocus
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (U : X.Opens) (hU : (U : Set X) ⊆ f.smoothLocus) : Smooth (U.ι ≫ f) := by
  rw [← Scheme.Hom.smoothLocus_eq_top_iff]
  rw [← Scheme.Hom.preimage_smoothLocus_eq]
  apply top_unique
  intro x hx
  exact hU x.property

/-- A nonempty open contained in an irreducible component of a reduced scheme is an
integral scheme. -/
theorem Opens.isIntegral_toScheme_of_nonempty_of_le_component
    {X : Scheme.{u}} [IsReduced X] (U : X.Opens)
    (hUnonempty : (U : Set X).Nonempty)
    (Z : irreducibleComponents X) (hUZ : (U : Set X) ⊆ Z.1) :
    IsIntegral U.toScheme := by
  let _ : Nonempty U := by simpa using hUnonempty
  let _ : IrreducibleSpace U.toScheme :=
    { toPreirreducibleSpace :=
        Subtype.preirreducibleSpace (Z.property.1.2.open_subset U.2 hUZ)
      toNonempty := inferInstance }
  let _ : IsReduced U.toScheme := isReduced_of_isOpenImmersion U.ι
  exact isIntegral_of_irreducibleSpace_of_isReduced U.toScheme

/-- The ring of sections on an affine open inside one smooth component of a reduced
curve is integrally closed. -/
theorem IsAffineOpen.isIntegrallyClosed_sections_of_le_component_of_le_smoothLocus
    {K : Type u} [Field K] {X : Scheme.{u}} [IsReduced X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f]
    {U : X.Opens} (hUaffine : IsAffineOpen U)
    (hUnonempty : (U : Set X).Nonempty)
    (Z : irreducibleComponents X) (hUZ : (U : Set X) ⊆ Z.1)
    (hUsmooth : (U : Set X) ⊆ f.smoothLocus)
    (hdim : topologicalKrullDim X ≤ 1) : IsIntegrallyClosed Γ(X, U) := by
  let _ : IsAffine U.toScheme := hUaffine
  let _ : IsIntegral U.toScheme :=
    U.isIntegral_toScheme_of_nonempty_of_le_component hUnonempty Z hUZ
  let _ : Smooth (U.ι ≫ f) :=
    f.smooth_comp_openImmersion_of_le_smoothLocus U hUsmooth
  have hdimU : topologicalKrullDim U.toScheme ≤ 1 :=
    (topologicalKrullDim_subspace_le X U).trans hdim
  let _ : IsIntegrallyClosed Γ(U.toScheme, ⊤) :=
    isIntegrallyClosed_globalSections_of_smooth_toSpec_field_of_dim_le_one
      U.toScheme (U.ι ≫ f) hdimU
  let e : Γ(U.toScheme, ⊤) ≃+* Γ(X, Scheme.Hom.opensRange U.ι) :=
    (IsOpenImmersion.ΓIsoTop U.ι).commRingCatIsoToRingEquiv
  have hnormal : IsIntegrallyClosed Γ(X, Scheme.Hom.opensRange U.ι) :=
    IsIntegrallyClosed.of_equiv e
  rw [Scheme.Opens.opensRange_ι U] at hnormal
  exact hnormal

end AlgebraicGeometry.Scheme

end
