module

public import StacksAndModuli.API.GlobalSectionsRationalPoint
public import StacksAndModuli.API.SmoothCancellationEtale

/-!
# Smoothness over a finite separable field of global constants

Let a scheme over a field `k` have field-valued global sections `K`.  Its original
structure morphism factors through the canonical map to `Spec K`.  If `K / k` is
finite separable, then `Spec K ⟶ Spec k` is etale, so smoothness over `k` cancels
to smoothness over `K`.

## Main results

* `AlgebraicGeometry.Scheme.toSpecGlobalSections_comp_specMap_algebraMap`;
* `AlgebraicGeometry.Scheme.smooth_toSpecGlobalSections_of_finiteSeparable`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- The original structure morphism factors through the canonical map to the
spectrum of global sections. -/
theorem toSpecGlobalSections_comp_specMap_algebraMap
    {k : Type u} [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] :
    X.toSpecGlobalSections ≫
        Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, ⊤))) =
      X ↘ Spec (CommRingCat.of k) := by
  rw [show CommRingCat.ofHom (algebraMap k Γ(X, ⊤)) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (X ↘ Spec (CommRingCat.of k)).appTop from rfl]
  rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]
  simp

/-- A smooth scheme remains smooth over its field of global constants when that
field is finite separable over the original ground field. -/
theorem smooth_toSpecGlobalSections_of_finiteSeparable
    {k : Type u} [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))]
    (hfield : IsField Γ(X, ⊤))
    (hfinite : Module.Finite k Γ(X, ⊤))
    (hsep :
      letI : Field Γ(X, ⊤) := hfield.toField
      Algebra.IsSeparable k Γ(X, ⊤))
    (hsmooth : Smooth (X ↘ Spec (CommRingCat.of k))) :
    Smooth X.toSpecGlobalSections := by
  let _ : Field Γ(X, ⊤) := hfield.toField
  let _ : Module.Finite k Γ(X, ⊤) := hfinite
  let _ : Algebra.IsSeparable k Γ(X, ⊤) := hsep
  let _ : Algebra.FormallyEtale k Γ(X, ⊤) :=
    Algebra.FormallyEtale.of_isSeparable k Γ(X, ⊤)
  let _ : Algebra.FinitePresentation k Γ(X, ⊤) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let _ : Algebra.Etale k Γ(X, ⊤) :=
    ⟨inferInstance, inferInstance⟩
  let g : Spec (CommRingCat.of Γ(X, ⊤)) ⟶
      Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, ⊤)))
  have hg : Etale g := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    change (algebraMap k Γ(X, ⊤)).Etale
    rw [RingHom.etale_algebraMap]
    infer_instance
  apply AlgebraicGeometry.Smooth.of_comp_of_etale X.toSpecGlobalSections g
  · rw [toSpecGlobalSections_comp_specMap_algebraMap X]
    exact hsmooth
  · exact hg

end AlgebraicGeometry.Scheme

end
