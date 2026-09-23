module

public import StacksAndModuli.API.SheafCohomologyModule
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Rational points over the field of global constants

For any scheme `X`, the adjunction unit `X.toSpecΓ` equips `X` with its canonical
structure over the spectrum of its global-sections ring.  If evaluation at a point
`x` identifies the global-sections ring with `κ(x)`, the inverse identification
constructs a section of this structure map.  This is the rational-point input used
when a rational tail is viewed over its field of global constants.

The file also records that properness over any original base descends to the
canonical global-sections structure map.

## Main results

* `AlgebraicGeometry.Scheme.sectionToSpecGlobalSectionsOfBijectiveEvaluation`;
* `AlgebraicGeometry.Scheme.
    sectionToSpecGlobalSectionsOfBijectiveEvaluation_comp`;
* `AlgebraicGeometry.Scheme.bijective_baseRingHom_toSpecGlobalSections`;
* `AlgebraicGeometry.Scheme.isProper_toSpecGlobalSections`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- The canonical structure map to the spectrum of the underlying type of the
global-sections ring.  This is `Scheme.toSpecΓ`, with its target written in the
field-valued form used by `Scheme.Over`. -/
abbrev toSpecGlobalSections (X : Scheme.{u}) :
    X ⟶ Spec (CommRingCat.of Γ(X, ⊤)) :=
  X.toSpecΓ

/-- The residue-field point followed by the canonical map to global constants is
the spectrum map induced by evaluation at that point. -/
theorem fromSpecResidueField_toSpecΓ (X : Scheme.{u}) (x : X) :
    X.fromSpecResidueField x ≫ X.toSpecΓ =
      Spec.map (X.Γevaluation x) := by
  rw [fromSpecResidueField, Category.assoc,
    Scheme.fromSpecStalk_toSpecΓ, ← Spec.map_comp]
  rfl

/-- A point at which global evaluation is bijective determines a rational point
over the global-sections ring. -/
def sectionToSpecGlobalSectionsOfBijectiveEvaluation
    (X : Scheme.{u}) (x : X)
    (h : Function.Bijective (X.Γevaluation x)) :
    Spec (CommRingCat.of Γ(X, ⊤)) ⟶ X :=
  let e : Γ(X, ⊤) ≃+* X.residueField x :=
    RingEquiv.ofBijective (X.Γevaluation x).hom h
  Spec.map e.symm.toCommRingCatIso.hom ≫ X.fromSpecResidueField x

/-- The point constructed from bijective evaluation is a section of the canonical
global-sections structure map. -/
theorem sectionToSpecGlobalSectionsOfBijectiveEvaluation_comp
    (X : Scheme.{u}) (x : X)
    (h : Function.Bijective (X.Γevaluation x)) :
    sectionToSpecGlobalSectionsOfBijectiveEvaluation X x h ≫
      X.toSpecGlobalSections = 𝟙 _ := by
  rw [sectionToSpecGlobalSectionsOfBijectiveEvaluation, Category.assoc,
    X.fromSpecResidueField_toSpecΓ x]
  let e : Γ(X, ⊤) ≃+* X.residueField x :=
    RingEquiv.ofBijective (X.Γevaluation x).hom h
  change Spec.map e.symm.toCommRingCatIso.hom ≫
    Spec.map (X.Γevaluation x) = 𝟙 _
  rw [← Spec.map_comp]
  have heq : X.Γevaluation x ≫ e.symm.toCommRingCatIso.hom = 𝟙 _ := by
    ext a
    exact e.symm_apply_apply a
  rw [heq]
  simpa only [CommRingCat.of_carrier] using
    Spec.map_id (X.presheaf.obj (.op ⊤))

/-- For the canonical structure over its global-sections ring, the induced map on
global sections is bijective. -/
theorem bijective_baseRingHom_toSpecGlobalSections (X : Scheme.{u}) :
    letI : X.Over (Spec (CommRingCat.of Γ(X, ⊤))) :=
      ⟨X.toSpecGlobalSections⟩
    Function.Bijective
      (X.baseRingHom (CommRingCat.of Γ(X, ⊤))) := by
  let _ : X.Over (Spec (CommRingCat.of Γ(X, ⊤))) :=
    ⟨X.toSpecGlobalSections⟩
  rw [baseRingHom_eq]
  change Function.Bijective
    (((Scheme.ΓSpecIso (CommRingCat.of Γ(X, ⊤))).inv ≫
      X.toSpecΓ.appTop).hom)
  rw [Scheme.toSpecΓ_appTop]
  exact ConcreteCategory.bijective_of_isIso _

/-- If a scheme is proper over an original field, it is proper over the spectrum
of its global-sections ring via the canonical structure map. -/
theorem isProper_toSpecGlobalSections
    {k : Type u} [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))]
    [IsProper (X ↘ Spec (CommRingCat.of k))] :
    IsProper X.toSpecGlobalSections := by
  have hcomp : IsProper
      (X.toSpecΓ ≫ Spec.map (X ↘ Spec (CommRingCat.of k)).appTop) := by
    rw [← Scheme.toSpecΓ_naturality]
    infer_instance
  let _ : IsProper
      (X.toSpecΓ ≫ Spec.map (X ↘ Spec (CommRingCat.of k)).appTop) := hcomp
  exact IsProper.of_comp X.toSpecΓ
    (Spec.map (X ↘ Spec (CommRingCat.of k)).appTop)

end AlgebraicGeometry.Scheme

end
