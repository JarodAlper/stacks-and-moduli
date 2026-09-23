module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksProject.Algebra.SmoothOverField.«lemma-characterize-smooth-over-field»
public import StacksAndModuli.API.ReducedClosedStalks

/-!
# Reduced stalks at smooth points over a field

This file connects Mathlib's formally smooth stalk criterion with the regular-local-ring
results for smooth algebras over fields.  A formally smooth point of a locally finitely
presented scheme over a field has a smooth affine neighbourhood.  Its local ring is therefore
regular, hence a domain and in particular reduced.

## Main results

* `AlgebraicGeometry.Scheme.isRegularLocalRing_stalk_of_formallySmooth_toSpec_field`:
  a formally smooth stalk of a locally finitely presented scheme over a field is regular.
* `AlgebraicGeometry.Scheme.isReduced_stalk_of_formallySmooth_toSpec_field`:
  the corresponding stalk is reduced.
* `AlgebraicGeometry.Scheme.isReduced_of_smooth_toSpec_field`:
  a scheme smooth over a field is reduced.
* `AlgebraicGeometry.Scheme.isIntegral_of_smooth_toSpec_field_of_irreducible`:
  an irreducible scheme smooth over a field is integral.
* `AlgebraicGeometry.Scheme.isReduced_of_formallySmooth_or_isReduced_closed_stalk`:
  a Jacobson scheme over a field is reduced if every closed point is formally smooth or
  already has a reduced stalk.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- A formally smooth stalk of a locally finitely presented scheme over a field is a regular
local ring. -/
theorem isRegularLocalRing_stalk_of_formallySmooth_toSpec_field
    {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation p]
    (x : X) (h : (p.stalkMap x).hom.FormallySmooth) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨U, hU, V, hV, hVU, hxV, hSmooth⟩ :=
    exists_smooth_of_formallySmooth_stalk p x h
  have hUtop : U = ⊤ := by
    ext y
    constructor
    · intro _
      trivial
    · intro _
      have hpx : p x ∈ U := hVU hxV
      change y ∈ (U : Set (Spec (.of K)))
      rw [Subsingleton.elim y (p x)]
      change p x ∈ U
      exact hpx
  subst U
  let e : K ≃+* Γ(Spec (.of K), ⊤) :=
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  let _ : Field Γ(Spec (.of K), ⊤) := (e.symm.isField (Field.toIsField K)).toField
  let φ := p.appLE (⊤ : (Spec (.of K)).Opens) V hVU
  have hφ : φ.hom.Smooth := hSmooth
  algebraize [φ.hom]
  let _ : Algebra.Smooth Γ(Spec (.of K), ⊤) Γ(X, V) := by
    rw [← RingHom.smooth_algebraMap]
    exact hφ
  let _ : IsNoetherianRing Γ(X, V) :=
    Algebra.FiniteType.isNoetherianRing Γ(Spec (.of K), ⊤) Γ(X, V)
  let _ : Algebra Γ(X, V) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxV⟩
  let q := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  let _ : q.IsPrime := (hV.primeIdealOf ⟨x, hxV⟩).isPrime
  let _ : IsLocalization.AtPrime (X.presheaf.stalk x) q :=
    hV.isLocalization_stalk ⟨x, hxV⟩
  exact isRegularLocalRing_of_smooth_of_isLocalization_atPrime
    Γ(Spec (.of K), ⊤) Γ(X, V) q (X.presheaf.stalk x)

/-- A formally smooth stalk of a locally finitely presented scheme over a field is reduced. -/
theorem isReduced_stalk_of_formallySmooth_toSpec_field
    {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation p]
    (x : X) (h : (p.stalkMap x).hom.FormallySmooth) :
    _root_.IsReduced (X.presheaf.stalk x) := by
  let _ : IsRegularLocalRing (X.presheaf.stalk x) :=
    isRegularLocalRing_stalk_of_formallySmooth_toSpec_field p x h
  let _ : IsDomain (X.presheaf.stalk x) := IsRegularLocalRing.isDomain
  infer_instance

/-- A scheme smooth over a field is reduced. -/
theorem isReduced_of_smooth_toSpec_field
    {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) [Smooth p] : IsReduced X := by
  let _ (x : X) : _root_.IsReduced (X.presheaf.stalk x) :=
    isReduced_stalk_of_formallySmooth_toSpec_field p x <| by
      rw [← Scheme.Hom.mem_smoothLocus, p.smoothLocus_eq_top]
      exact Set.mem_univ x
  exact isReduced_of_isReduced_stalk X

/-- An irreducible scheme smooth over a field is integral. -/
theorem isIntegral_of_smooth_toSpec_field_of_irreducible
    {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) [Smooth p] [IrreducibleSpace X] : IsIntegral X := by
  let _ : IsReduced X := isReduced_of_smooth_toSpec_field p
  exact isIntegral_of_irreducibleSpace_of_isReduced X

/-- A Jacobson scheme locally finitely presented over a field is reduced if, at every closed
point, either its structure morphism is formally smooth or its local ring is already known to
be reduced. -/
theorem isReduced_of_formallySmooth_or_isReduced_closed_stalk
    {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation p] [JacobsonSpace X]
    (h : ∀ x : X, IsClosed ({x} : Set X) →
      (p.stalkMap x).hom.FormallySmooth ∨ _root_.IsReduced (X.presheaf.stalk x)) :
    IsReduced X := by
  apply isReduced_of_isReduced_closed_stalk X
  intro x hx
  rcases h x hx with hsmooth | hreduced
  · exact isReduced_stalk_of_formallySmooth_toSpec_field p x hsmooth
  · exact hreduced

end AlgebraicGeometry.Scheme
