module

public import StacksAndModuli.API.PointSupportCohomology
public import StacksAndModuli.API.SheafCohomologyModuleLES
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# The generic-point function-field resolution

For an integral scheme `X`, the canonical map from the spectrum of its function field
to `X` is dominant and hence scheme-theoretically dominant.  Consequently, the
structure module embeds into the pushforward of the structure module from the generic
point.  The latter is flasque because its source has only one point.

This file packages the resulting short exact sequence

`0 ⟶ 𝒪_X ⟶ η_* K(X) ⟶ 𝒱_X ⟶ 0`,

where `𝒱_X` is defined as the cokernel and plays the role of the sheaf of principal
parts.  It also isolates the precise approximation input needed to deduce
`H¹(X, 𝒪_X) = 0`: every global principal part must be represented by a single
element of `K(X)`.

For the affine line this last assertion is the algebraic partial-fractions theorem,
together with an identification of the sheaf cokernel with finite local principal-part
data.  That identification is not presently available in Mathlib, so this file does not
assert the affine-line specialization without the explicit surjectivity input.

## Main definitions

* `AlgebraicGeometry.Scheme.genericPointMap`: the canonical function-field point.
* `AlgebraicGeometry.Scheme.genericFunctionFieldModule`: the pushforward `η_* K(X)`.
* `AlgebraicGeometry.Scheme.genericPrincipalPartsModule`: its quotient by `𝒪_X`.
* `AlgebraicGeometry.Scheme.functionFieldToGenericPrincipalPartsGlobalSections`: the
  global principal-parts map from `K(X)`.

## Main results

* `AlgebraicGeometry.Scheme.genericFunctionFieldComplex_shortExact`: the generic-point
  sequence is short exact.
* `AlgebraicGeometry.Scheme.subsingleton_H_genericFunctionFieldModule`: the middle term
  has vanishing positive cohomology.
* `AlgebraicGeometry.Scheme.subsingleton_H_one_structureModule_of_surjective_genericPrincipalParts`:
  weak approximation for global principal parts implies `H¹(X, 𝒪_X) = 0`.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The spectrum of the function field of an integral scheme. -/
abbrev genericPointScheme (X : Scheme.{u}) [IsIntegral X] : Scheme.{u} :=
  Spec X.functionField

/-- The canonical function-field point of an integral scheme. -/
abbrev genericPointMap (X : Scheme.{u}) [IsIntegral X] :
    X.genericPointScheme ⟶ X :=
  X.fromSpecStalk (genericPoint X)

/-- The spectrum of the function field has at most one point. -/
instance genericPointScheme_subsingleton (X : Scheme.{u}) [IsIntegral X] :
    Subsingleton X.genericPointScheme :=
  PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mpr
    (Field.toIsField X.functionField)

/-- The canonical function-field point is quasicompact. -/
instance genericPointMap_quasiCompact (X : Scheme.{u}) [IsIntegral X] :
    QuasiCompact X.genericPointMap := by
  exact ⟨fun _ _ _ ↦ (Set.toFinite _).isCompact⟩

/-- The canonical function-field point has dense image. -/
instance genericPointMap_isDominant (X : Scheme.{u}) [IsIntegral X] :
    IsDominant X.genericPointMap := by
  rw [isDominant_iff, denseRange_iff_closure_range]
  apply Set.eq_univ_of_forall
  intro x
  have hgeneric : genericPoint X ∈ Set.range X.genericPointMap := by
    exact ⟨IsLocalRing.closedPoint X.functionField,
      Scheme.fromSpecStalk_closedPoint⟩
  have hclosure : closure ({genericPoint X} : Set X) = Set.univ :=
    genericPoint_spec X
  have hx : x ∈ closure ({genericPoint X} : Set X) := by
    rw [hclosure]
    trivial
  exact closure_mono (Set.singleton_subset_iff.mpr hgeneric) hx

/-- The canonical function-field point is scheme-theoretically dominant. -/
instance genericPointMap_isSchemeTheoreticallyDominant
    (X : Scheme.{u}) [IsIntegral X] :
    IsSchemeTheoreticallyDominant X.genericPointMap :=
  IsSchemeTheoreticallyDominant.of_isDominant X.genericPointMap

/-- The function-field sheaf of an integral scheme, realized as pushforward from its
generic point. -/
abbrev genericFunctionFieldModule (X : Scheme.{u}) [IsIntegral X] : X.Modules :=
  (Modules.pushforward X.genericPointMap).obj
    (structureModule X.genericPointScheme)

/-- The underlying additive sheaf of the generic function-field module. -/
abbrev genericFunctionFieldAddSheaf
    (X : Scheme.{u}) [IsIntegral X] : TopCat.Sheaf AddCommGrpCat.{u} X :=
  (SheafOfModules.toSheaf X.ringCatSheaf).obj
    X.genericFunctionFieldModule

/-- Global sections of the generic function-field module are the function field. -/
def genericFunctionFieldGlobalSectionsAddEquiv
    (X : Scheme.{u}) [IsIntegral X] :
    Γ(X.genericFunctionFieldModule, ⊤) ≃+ X.functionField :=
  (Modules.pushforwardGlobalSectionsAddEquiv X.genericPointMap
    (structureModule X.genericPointScheme)).trans <|
      (Modules.structureModuleSectionsEquiv X.genericPointScheme ⊤).toAddEquiv |>.trans <|
        (Scheme.ΓSpecIso X.functionField).commRingCatIsoToRingEquiv.toAddEquiv

/-- The generic function-field module is flasque. -/
instance genericFunctionFieldModule_isFlasque
    (X : Scheme.{u}) [IsIntegral X] :
    TopCat.Presheaf.IsFlasque
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj
        X.genericFunctionFieldModule).obj := by
  let F : TopCat.Sheaf AddCommGrpCat.{u} X.genericPointScheme :=
    (SheafOfModules.toSheaf X.genericPointScheme.ringCatSheaf).obj
      (structureModule X.genericPointScheme)
  let _ : F.IsFlasque := TopCat.Sheaf.isFlasque_of_subsingleton F
  exact TopCat.Sheaf.IsFlasque.pushforward_isFlasque F X.genericPointMap.base

/-- The structure sheaf embeds canonically into the function-field sheaf. -/
def structureToGenericFunctionField
    (X : Scheme.{u}) [IsIntegral X] :
    structureModule X ⟶ X.genericFunctionFieldModule :=
  SheafOfModules.unitToPushforwardObjUnit
    X.genericPointMap.toRingCatSheafHom

/-- The canonical map from the structure sheaf to the function-field sheaf is a
monomorphism. -/
instance structureToGenericFunctionField_mono
    (X : Scheme.{u}) [IsIntegral X] :
    Mono X.structureToGenericFunctionField := by
  apply Functor.mono_of_mono_map (SheafOfModules.forget X.ringCatSheaf)
  change Mono X.structureToGenericFunctionField.val
  apply PresheafOfModules.mono_of_injective
  intro U a b hab
  apply X.genericPointMap.app_injective U.unop
  exact hab

/-- The principal-parts cokernel of the structure sheaf inside the function-field
sheaf. -/
abbrev genericPrincipalPartsModule (X : Scheme.{u}) [IsIntegral X] : X.Modules :=
  cokernel X.structureToGenericFunctionField

/-- The quotient map from generic rational functions to principal parts. -/
def genericPrincipalPartsProjection (X : Scheme.{u}) [IsIntegral X] :
    X.genericFunctionFieldModule ⟶ X.genericPrincipalPartsModule :=
  cokernel.π X.structureToGenericFunctionField

/-- The underlying additive sheaf of the generic principal-parts module. -/
abbrev genericPrincipalPartsAddSheaf
    (X : Scheme.{u}) [IsIntegral X] : TopCat.Sheaf AddCommGrpCat.{u} X :=
  (SheafOfModules.toSheaf X.ringCatSheaf).obj
    X.genericPrincipalPartsModule

/-- The principal-parts projection regarded as a morphism of additive sheaves. -/
abbrev genericPrincipalPartsProjectionAdd
    (X : Scheme.{u}) [IsIntegral X] :
    X.genericFunctionFieldAddSheaf ⟶ X.genericPrincipalPartsAddSheaf :=
  (SheafOfModules.toSheaf X.ringCatSheaf).map
    X.genericPrincipalPartsProjection

/-- The principal-parts projection evaluated on global sections. -/
def genericPrincipalPartsProjectionOnGlobalSections
    (X : Scheme.{u}) [IsIntegral X] :
    Γ(X.genericFunctionFieldModule, ⊤) →+
      Γ(X.genericPrincipalPartsModule, ⊤) :=
  (X.genericPrincipalPartsProjection.val.app
    (op (⊤ : Opens X))).hom.toAddMonoidHom

/-- The principal-parts map on global sections, with its source identified with the
function field. -/
def functionFieldToGenericPrincipalPartsGlobalSections
    (X : Scheme.{u}) [IsIntegral X] :
    X.functionField →+ Γ(X.genericPrincipalPartsModule, ⊤) :=
  X.genericPrincipalPartsProjectionOnGlobalSections.comp
    X.genericFunctionFieldGlobalSectionsAddEquiv.symm.toAddMonoidHom

/-- Surjectivity of the function-field principal-parts map is equivalent to
surjectivity of the original quotient map on global sections. -/
theorem surjective_functionFieldToGenericPrincipalPartsGlobalSections_iff
    (X : Scheme.{u}) [IsIntegral X] :
    Function.Surjective X.functionFieldToGenericPrincipalPartsGlobalSections ↔
      Function.Surjective X.genericPrincipalPartsProjectionOnGlobalSections := by
  constructor
  · intro h y
    obtain ⟨x, hx⟩ := h y
    exact ⟨X.genericFunctionFieldGlobalSectionsAddEquiv.symm x, hx⟩
  · intro h y
    obtain ⟨x, hx⟩ := h y
    exact ⟨X.genericFunctionFieldGlobalSectionsAddEquiv x, by
      change X.genericPrincipalPartsProjectionOnGlobalSections
        (X.genericFunctionFieldGlobalSectionsAddEquiv.symm
          (X.genericFunctionFieldGlobalSectionsAddEquiv x)) = y
      rw [AddEquiv.symm_apply_apply]
      exact hx⟩

/-- The generic-point rational-function sequence. -/
abbrev genericFunctionFieldComplex (X : Scheme.{u}) [IsIntegral X] :
    ShortComplex X.Modules :=
  ShortComplex.mk X.structureToGenericFunctionField
    X.genericPrincipalPartsProjection (by
      simp [genericPrincipalPartsProjection])

/-- The generic-point rational-function sequence is short exact. -/
theorem genericFunctionFieldComplex_shortExact
    (X : Scheme.{u}) [IsIntegral X] :
    X.genericFunctionFieldComplex.ShortExact := by
  exact
    { exact := by
        simpa [genericFunctionFieldComplex, genericPrincipalPartsProjection] using
          ShortComplex.exact_cokernel X.structureToGenericFunctionField
      mono_f := inferInstance
      epi_g := by
        dsimp [genericFunctionFieldComplex, genericPrincipalPartsProjection]
        infer_instance }

/-- The generic function-field module has vanishing positive cohomology. -/
theorem subsingleton_H_genericFunctionFieldModule
    (X : Scheme.{u}) [IsIntegral X] (n : ℕ) :
    Subsingleton (Modules.H X.genericFunctionFieldModule (n + 1)) :=
  Modules.subsingleton_H_of_isFlasque X.genericFunctionFieldModule inferInstance n

/-- The first cohomology of the generic function-field module vanishes. -/
theorem subsingleton_H_genericFunctionFieldModule_one
    (X : Scheme.{u}) [IsIntegral X] :
    Subsingleton (Modules.H X.genericFunctionFieldModule 1) := by
  simpa using X.subsingleton_H_genericFunctionFieldModule 0

namespace Modules

/-- In a short exact sequence, surjectivity on `H⁰` and vanishing of the middle
term's `H¹` imply vanishing of the first term's `H¹`. -/
theorem subsingleton_H_one_of_shortExact_of_surjective_HMap_zero
    {X : Scheme.{u}} {S : ShortComplex X.Modules}
    (hS : S.ShortExact) (hsurj : Function.Surjective (HMap S.g 0))
    (h₂ : Subsingleton (H S.X₂ 1)) : Subsingleton (H S.X₁ 1) := by
  have hex₁ := exact_HDelta_HMap S hS 0 1 rfl
  have hex₃ := exact_HMap_HDelta S hS 0 1 rfl
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨y, rfl⟩ := (hex₁ x).mp (h₂.elim _ _)
  exact (hex₃ y).mpr (hsurj y)

/-- Surjectivity on top-open sections implies surjectivity on degree-zero
cohomology. -/
theorem surjective_HMap_zero_of_surjective_appTop
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (hsurj : Function.Surjective (f.val.app (op (⊤ : Opens X))).hom) :
    Function.Surjective (HMap f 0) := by
  intro y
  obtain ⟨a, ha⟩ := hsurj
    (CategoryTheory.Sheaf.H.equiv₀
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj N)
      isTerminalTop y)
  let x := (CategoryTheory.Sheaf.H.equiv₀
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)
    isTerminalTop).symm a
  refine ⟨x, (CategoryTheory.Sheaf.H.equiv₀
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj N)
    isTerminalTop).injective ?_⟩
  have hn := CategoryTheory.Sheaf.H.equiv₀_naturality
    (f := (SheafOfModules.toSheaf X.ringCatSheaf).map f)
    (hT := isTerminalTop) x
  exact hn.symm.trans ((congrArg (fun z ↦ f.val.app (op (⊤ : Opens X)) z)
    (AddEquiv.apply_symm_apply _ a)).trans ha)

-- `subsingleton_H_one_of_shortExact_of_surjective_appTop` — surjectivity on top-open
-- sections plus vanishing of the middle term's `H¹` gives vanishing of the first term's
-- `H¹` — lives with the rest of the long-exact-sequence API, in
-- `StacksAndModuli/API/SheafCohomologyLES.lean`; it is in scope here through the imports.

end Modules

set_option maxHeartbeats 300000 in
-- Elaborating the nested sheaf-cokernel maps exceeds the default heartbeat budget.
/-- If every global principal part on an integral scheme is represented by a single
element of its function field, then the structure sheaf has vanishing `H¹`. -/
theorem subsingleton_H_one_structureModule_of_surjective_genericPrincipalParts
    (X : Scheme.{u}) [IsIntegral X]
    (hsurj : Function.Surjective
      X.functionFieldToGenericPrincipalPartsGlobalSections) :
    Subsingleton (Modules.H (structureModule X) 1) := by
  have hsections : Function.Surjective
      X.genericPrincipalPartsProjectionOnGlobalSections :=
    X.surjective_functionFieldToGenericPrincipalPartsGlobalSections_iff.mp hsurj
  change Function.Surjective
    (X.genericPrincipalPartsProjection.val.app
      (op (⊤ : Opens X))).hom at hsections
  have hHMap : Function.Surjective
      (Modules.HMap X.genericPrincipalPartsProjection 0) :=
    Modules.surjective_HMap_zero_of_surjective_appTop _ hsections
  exact Modules.subsingleton_H_one_of_shortExact_of_surjective_HMap_zero
    X.genericFunctionFieldComplex_shortExact hHMap
    X.subsingleton_H_genericFunctionFieldModule_one

end AlgebraicGeometry.Scheme
