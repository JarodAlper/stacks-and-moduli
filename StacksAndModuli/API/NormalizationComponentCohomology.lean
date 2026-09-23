module

public import StacksAndModuli.API.FiniteCoproductGlobalSections
public import StacksAndModuli.API.NormalizationComponents
public import StacksAndModuli.API.SheafCohomologySchemeIso

/-!
# Degree-zero cohomology of normalized irreducible components

Let `X` be a reduced scheme over an algebraically closed field and suppose that its
structure morphism is universally closed.  The relative normalization of `X` in the
function field of any irreducible component is integral and universally closed over the
field.  It therefore has only constant global functions, so its degree-zero
structure-sheaf cohomology is one-dimensional.

## Main results

* `AlgebraicGeometry.Scheme.relativeComponentNormalization_bijective_baseRingHom`:
  the ground field is the ring of global functions on a normalized component.
* `AlgebraicGeometry.Scheme.relativeComponentNormalization_finrank_globalSections_eq_one`:
  those global functions have dimension one.
* `AlgebraicGeometry.Scheme.relativeComponentNormalization_h_zero_eq_one`:
  the corresponding degree-zero cohomology dimension is one.
* `AlgebraicGeometry.Scheme.normalizationPushforward_h_zero_eq_componentCount`:
  degree-zero cohomology of the normalization pushforward counts irreducible components.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- A normalized irreducible component of a universally closed reduced scheme over an
algebraically closed field has no nonconstant global functions. -/
theorem relativeComponentNormalization_bijective_baseRingHom
    (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [IsReduced X]
    [UniversallyClosed (X ↘ Spec (CommRingCat.of k))]
    (Z : irreducibleComponents X) :
    Function.Bijective
      ((X.relativeComponentNormalization Z).baseRingHom
        (CommRingCat.of k)) :=
  bijective_baseRingHom_of_isAlgClosed k
    (X.relativeComponentNormalization Z)

/-- The global functions on a normalized irreducible component are one-dimensional over
the algebraically closed ground field. -/
theorem relativeComponentNormalization_finrank_globalSections_eq_one
    (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [IsReduced X]
    [UniversallyClosed (X ↘ Spec (CommRingCat.of k))]
    (Z : irreducibleComponents X) :
    Module.finrank k Γ(X.relativeComponentNormalization Z, ⊤) = 1 :=
  finrank_globalSections_eq_one k (X.relativeComponentNormalization Z)
    (relativeComponentNormalization_bijective_baseRingHom k X Z)

/-- Degree-zero structure-sheaf cohomology of a normalized irreducible component has
dimension one. -/
theorem relativeComponentNormalization_h_zero_eq_one
    (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [IsReduced X]
    [UniversallyClosed (X ↘ Spec (CommRingCat.of k))]
    (Z : irreducibleComponents X) :
    Modules.h k
      (structureModule (X.relativeComponentNormalization Z)) 0 = 1 :=
  h_structureModule_zero_eq_one k (X.relativeComponentNormalization Z)

/-- Degree-zero cohomology of the normalization pushforward of a reduced universally
closed scheme over an algebraically closed field counts its irreducible components.

The normalization is first decomposed as the finite coproduct of the relative
normalizations in the component function fields.  Each summand has only constant global
functions, and degree-zero cohomology is unchanged by pushforward. -/
theorem normalizationPushforward_h_zero_eq_componentCount
    (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [IsReduced X]
    [Finite (irreducibleComponents X)]
    [UniversallyClosed (X ↘ Spec (CommRingCat.of k))] :
    letI : X.normalization.Over (Spec (CommRingCat.of k)) :=
      ⟨X.normalizationMap ≫ (X ↘ Spec (CommRingCat.of k))⟩
    Modules.h k
      ((Modules.pushforward X.normalizationMap).obj
        (structureModule X.normalization)) 0 =
      Nat.card (irreducibleComponents X) := by
  let N := fun Z : irreducibleComponents X ↦
    X.relativeComponentNormalization Z
  let _ : X.normalization.Over (Spec (CommRingCat.of k)) :=
    ⟨X.normalizationMap ≫ (X ↘ Spec (CommRingCat.of k))⟩
  let _ : (∐ N : Scheme.{u}).Over (Spec (CommRingCat.of k)) :=
    sigmaOver N k
  let _ := Fintype.ofFinite (irreducibleComponents X)
  let eOver :
      Over.mk (Sigma.desc fun Z : irreducibleComponents X ↦
        X.relativeComponentNormalizationMap Z ≫
          (X ↘ Spec (CommRingCat.of k))) ≅
        Over.mk (X.normalizationMap ≫
          (X ↘ Spec (CommRingCat.of k))) :=
    X.relativeComponentNormalizationSigmaOverIso
  calc
    Modules.h k
        ((Modules.pushforward X.normalizationMap).obj
          (structureModule X.normalization)) 0 =
        Modules.h k (structureModule X.normalization) 0 :=
      Modules.h_zero_pushforward_eq k X.normalizationMap rfl _
    _ = Modules.h k (structureModule (∐ N)) 0 :=
      (Modules.h_structureModule_eq_of_overIso k eOver 0).symm
    _ = Fintype.card (irreducibleComponents X) :=
      Modules.h_structureModule_sigma_zero_eq_card_of_isIntegral N k
    _ = Nat.card (irreducibleComponents X) := by
      rw [Nat.card_eq_fintype_card]

end AlgebraicGeometry.Scheme
