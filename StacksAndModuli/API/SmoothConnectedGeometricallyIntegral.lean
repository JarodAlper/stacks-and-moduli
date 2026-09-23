module

public import StacksAndModuli.API.GlobalConstantsSmooth
public import StacksAndModuli.API.IrreducibleComponentNeighborhood
public import StacksAndModuli.API.SmoothGeometricallyReduced
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Geometric integrality from smoothness and connectedness

A connected Noetherian scheme whose local rings are domains is irreducible: its
irreducible components are pairwise disjoint, hence open as well as closed.  Applied
after every field extension, this turns a smooth, quasi-compact, geometrically
connected scheme over a field into a geometrically integral scheme.

The final theorem applies this bridge to the canonical morphism to the spectrum of
global constants.  It isolates geometric connectedness as the exact remaining
Stein-factorization input; smoothness and properness over the constants are discharged
from the finite-separable hypotheses and the original proper structure morphism.

## Main results

* `irreducibleSpace_of_connectedSpace_of_finiteComponents_of_isDomain_stalk`;
* `geometricallyIntegral_of_smooth_of_quasiCompact_of_geometricallyConnected`;
* `geometricallyIntegral_toSpecGlobalSections_of_finiteSeparable_of_geometricallyConnected`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace Scheme

/-- A connected scheme with finitely many irreducible components and domain local
rings is irreducible.

Every point then belongs to a unique irreducible component.  Consequently, each
component equals the open complement of all the other components, so connectedness
forces any component to be the whole space. -/
theorem irreducibleSpace_of_connectedSpace_of_finiteComponents_of_isDomain_stalk
    (X : Scheme.{u}) [ConnectedSpace X]
    [Finite (irreducibleComponents X)]
    (hstalk : ∀ x : X, IsDomain (X.presheaf.stalk x)) :
    IrreducibleSpace X := by
  let _ (x : X) : IsDomain (X.presheaf.stalk x) := hstalk x
  let x : X := Classical.choice (inferInstance : Nonempty X)
  let Z : irreducibleComponents X := X.componentAtOfIsDomainStalk x
  have hZopen : IsOpen Z.1 := by
    have heq : (X.exclusiveComponentOpen Z : Set X) = Z.1 := by
      apply Set.Subset.antisymm (X.exclusiveComponentOpen_le Z)
      intro y hy
      apply X.mem_exclusiveComponentOpen_of_unique Z y
      intro W hyW
      exact X.eq_of_mem_irreducibleComponents_of_isDomain_stalk y W Z hyW hy
    rw [← heq]
    exact (X.exclusiveComponentOpen Z).2
  have hZclopen : IsClopen Z.1 :=
    ⟨isClosed_of_mem_irreducibleComponents Z.1 Z.2, hZopen⟩
  have hZeq : Z.1 = Set.univ := by
    rcases (connectedSpace_iff_clopen.mp (inferInstance : ConnectedSpace X)).2
        Z.1 hZclopen with h | h
    · exact False.elim (by
        have hx : x ∈ Z.1 := X.mem_componentAtOfIsDomainStalk x
        rw [h] at hx
        exact hx)
    · exact h
  refine { toNonempty := inferInstance, toPreirreducibleSpace := ⟨?_⟩ }
  rw [← hZeq]
  exact Z.2.1.2

end Scheme

/-- A smooth, quasi-compact, geometrically connected scheme over a field is
geometrically integral. -/
theorem geometricallyIntegral_of_smooth_of_quasiCompact_of_geometricallyConnected
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [Smooth f] [QuasiCompact f]
    [GeometricallyConnected f] : GeometricallyIntegral f := by
  let _ : GeometricallyReduced f :=
    geometricallyReduced_of_smooth_toSpec_field f
  let _ : GeometricallyIrreducible f := by
    constructor
    intro L _ y Z fst snd h
    let _ : Smooth snd := MorphismProperty.of_isPullback h inferInstance
    let _ : QuasiCompact snd := MorphismProperty.of_isPullback h inferInstance
    let _ : ConnectedSpace Z :=
      GeometricallyConnected.geometrically_connectedSpace y fst snd h
    let _ : IsLocallyNoetherian Z :=
      LocallyOfFiniteType.isLocallyNoetherian snd
    let _ : CompactSpace Z :=
      (quasiCompact_iff_compactSpace snd).mp inferInstance
    let _ : IsNoetherian Z := by
      convert IsNoetherian.mk
      · infer_instance
      · infer_instance
    let _ : Finite (irreducibleComponents Z) :=
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.to_subtype
    apply Scheme.irreducibleSpace_of_connectedSpace_of_finiteComponents_of_isDomain_stalk
    intro z
    let _ : IsRegularLocalRing (Z.presheaf.stalk z) :=
      Scheme.isRegularLocalRing_stalk_of_formallySmooth_toSpec_field snd z (by
        rw [← Scheme.Hom.mem_smoothLocus, snd.smoothLocus_eq_top]
        exact Set.mem_univ z)
    exact IsRegularLocalRing.isDomain
  exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible f

/-- A smooth, proper, geometrically connected scheme over a field is geometrically
integral. -/
theorem geometricallyIntegral_of_smooth_of_isProper_of_geometricallyConnected
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [Smooth f] [IsProper f]
    [GeometricallyConnected f] : GeometricallyIntegral f :=
  geometricallyIntegral_of_smooth_of_quasiCompact_of_geometricallyConnected f

namespace Scheme

/-- The canonical morphism from a proper smooth scheme to the spectrum of its
finite separable field of global constants is geometrically integral, provided it
is geometrically connected.

Thus the remaining premise is precisely the connected-fibres conclusion supplied
classically by Stein factorization; no geometric irreducibility premise is needed. -/
theorem geometricallyIntegral_toSpecGlobalSections_of_finiteSeparable_of_geometricallyConnected
    {k : Type u} [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))]
    [IsProper (X ↘ Spec (CommRingCat.of k))]
    (hfield : IsField Γ(X, ⊤))
    (hfinite : Module.Finite k Γ(X, ⊤))
    (hsep :
      letI : Field Γ(X, ⊤) := hfield.toField
      Algebra.IsSeparable k Γ(X, ⊤))
    (hsmooth : Smooth (X ↘ Spec (CommRingCat.of k)))
    (hconnected : GeometricallyConnected X.toSpecGlobalSections) :
    GeometricallyIntegral X.toSpecGlobalSections := by
  let _ : Field Γ(X, ⊤) := hfield.toField
  let _ : Smooth X.toSpecGlobalSections :=
    smooth_toSpecGlobalSections_of_finiteSeparable X hfield hfinite hsep hsmooth
  let _ : IsProper X.toSpecGlobalSections :=
    isProper_toSpecGlobalSections (k := k) X
  let _ : GeometricallyConnected X.toSpecGlobalSections := hconnected
  exact geometricallyIntegral_of_smooth_of_isProper_of_geometricallyConnected
    X.toSpecGlobalSections

end Scheme

end AlgebraicGeometry

end
