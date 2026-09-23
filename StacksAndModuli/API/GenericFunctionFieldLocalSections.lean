module

public import StacksAndModuli.API.GenericFunctionFieldResolution

/-!
# Local sections of the generic function-field module

On every open containing the generic point of an integral scheme, the pushed-forward
function-field module has exactly the same sections as it has globally.  In particular,
those local sections are canonically additively equivalent to the function field.

This is the local ingredient in principal-parts arguments: a local lift near the generic
point can be replaced by one global rational function.

## Main results

* `AlgebraicGeometry.Scheme.genericPointMap_preimage_eq_top`: an open containing the
  generic point pulls back to the whole function-field point.
* `AlgebraicGeometry.Scheme.genericFunctionFieldRestrictTopAddEquiv`: restriction from
  global sections to such an open is an additive equivalence.
* `AlgebraicGeometry.Scheme.genericFunctionFieldSectionsAddEquiv`: sections on such an
  open are canonically identified with the function field.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme

/-- An open containing the generic point pulls back to the whole spectrum of the
function field. -/
theorem genericPointMap_preimage_eq_top
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens)
    (hU : genericPoint X ∈ U) : X.genericPointMap ⁻¹ᵁ U = ⊤ := by
  apply top_unique
  intro y _
  change X.genericPointMap y ∈ U
  rw [Subsingleton.elim y (IsLocalRing.closedPoint X.functionField)]
  simpa using hU

/-- Restriction of the generic function-field module from the whole scheme to an open
containing the generic point is bijective. -/
theorem genericFunctionField_restrictTop_bijective
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens)
    (hU : genericPoint X ∈ U) :
    Function.Bijective
      (X.genericFunctionFieldModule.presheaf.map
        (homOfLE (show U ≤ ⊤ from le_top)).op).hom := by
  change Function.Bijective
    ((structureModule X.genericPointScheme).presheaf.map
      (homOfLE (show X.genericPointMap ⁻¹ᵁ U ≤
        X.genericPointMap ⁻¹ᵁ (⊤ : X.Opens) from
          Scheme.Hom.preimage_mono _ le_top)).op).hom
  have hopen : X.genericPointMap ⁻¹ᵁ U =
      X.genericPointMap ⁻¹ᵁ (⊤ : X.Opens) := by
    rw [genericPointMap_preimage_eq_top X U hU]
    simp
  let _ : IsIso (homOfLE (show X.genericPointMap ⁻¹ᵁ U ≤
      X.genericPointMap ⁻¹ᵁ (⊤ : X.Opens) from
        Scheme.Hom.preimage_mono _ le_top)) := by
    rw [show homOfLE (show X.genericPointMap ⁻¹ᵁ U ≤
      X.genericPointMap ⁻¹ᵁ (⊤ : X.Opens) from
        Scheme.Hom.preimage_mono _ le_top) = eqToHom hopen from
          Subsingleton.elim _ _]
    infer_instance
  exact ConcreteCategory.bijective_of_isIso _

/-- Restriction from global sections of the generic function-field module to an open
containing the generic point, as an additive equivalence. -/
noncomputable def genericFunctionFieldRestrictTopAddEquiv
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens)
    (hU : genericPoint X ∈ U) :
    Γ(X.genericFunctionFieldModule, ⊤) ≃+
      Γ(X.genericFunctionFieldModule, U) :=
  AddEquiv.ofBijective
    (X.genericFunctionFieldModule.presheaf.map
      (homOfLE (show U ≤ ⊤ from le_top)).op).hom
    (genericFunctionField_restrictTop_bijective X U hU)

/-- Sections of the generic function-field module on an open containing the generic
point are canonically equivalent to the function field. -/
noncomputable def genericFunctionFieldSectionsAddEquiv
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens)
    (hU : genericPoint X ∈ U) :
    Γ(X.genericFunctionFieldModule, U) ≃+ X.functionField :=
  (genericFunctionFieldRestrictTopAddEquiv X U hU).symm.trans
    X.genericFunctionFieldGlobalSectionsAddEquiv

/-- The local function-field identification sends the restriction of a global section
to its global function-field value. -/
@[simp]
theorem genericFunctionFieldSectionsAddEquiv_restrictTop
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens)
    (hU : genericPoint X ∈ U)
    (s : Γ(X.genericFunctionFieldModule, ⊤)) :
    genericFunctionFieldSectionsAddEquiv X U hU
        (X.genericFunctionFieldModule.presheaf.map
          (homOfLE (show U ≤ ⊤ from le_top)).op s) =
      X.genericFunctionFieldGlobalSectionsAddEquiv s := by
  exact congrArg X.genericFunctionFieldGlobalSectionsAddEquiv
    ((genericFunctionFieldRestrictTopAddEquiv X U hU).symm_apply_apply s)

end AlgebraicGeometry.Scheme
