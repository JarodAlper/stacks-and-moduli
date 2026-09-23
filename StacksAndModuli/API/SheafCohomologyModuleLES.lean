module

public import StacksAndModuli.API.SheafCohomologyModule
public import StacksAndModuli.API.SheafCohomologyLES
public import StacksAndModuli.API.ExactSequenceFinrank

/-!
# The cohomology long exact sequence of `𝒪_X`-modules is linear

`StacksAndModuli/API/SheafCohomologyLES.lean` transports the covariant `Ext` long exact sequence to
sheaves of modules on a scheme, but only as a sequence of abelian groups, and only in the
"two of three terms vanish" shape. `StacksAndModuli/API/SheafCohomologyModule.lean` makes each
`Hⁿ(X, F)` a `Γ(X, 𝒪_X)`-module. This file joins the two: for a short exact sequence of
`𝒪_X`-modules, *all three* maps of the long exact sequence — the two induced maps and the
connecting map — are `Γ(X, 𝒪_X)`-linear, and the sequence is exact as a sequence of
modules.

The only non-formal point is the connecting map. Multiplication by a global section `r` of
`𝒪_X` is an endomorphism of the whole short exact sequence (`smulShortComplexHom`), and the
naturality of the extension class (`ShortComplex.ShortExact.extClass_naturality`) then says
that the class commutes with `r` — which is exactly the linearity of `δ`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.smulShortComplexHom`: multiplication by a global section
  of `𝒪_X`, as an endomorphism of a short complex of abelian sheaves underlying a short
  complex of `𝒪_X`-modules.
* `AlgebraicGeometry.Scheme.Modules.HDelta`: the connecting map `Hⁿ(X₃) → Hⁿ⁺¹(X₁)`, as a
  `Γ(X, 𝒪_X)`-linear map.

## Main results

* `AlgebraicGeometry.Scheme.Modules.extClass_smul_comm`: the extension class commutes with
  multiplication by a global section.
* `AlgebraicGeometry.Scheme.Modules.exact_HMap_HMap`,
  `…exact_HMap_HDelta`, `…exact_HDelta_HMap`: exactness at the three positions.
* `AlgebraicGeometry.Scheme.Modules.injective_HMap_zero`: `H⁰` of a monomorphism is
  injective (`H⁰ = Hom`, and `Hom(A, -)` is left exact).
* `AlgebraicGeometry.Scheme.Modules.eulerChar_add_of_shortExact`: **additivity of the Euler
  characteristic**, `χ(F₂) = χ(F₁) + χ(F₃)`, for a short exact sequence of `𝒪_X`-modules
  whose cohomology is finite dimensional and vanishes in degree `2` on the sub. This is the
  induction step of Riemann–Roch.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open CategoryTheory Abelian Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf))

/-- Multiplication by a global section `r` of `𝒪_X` is an endomorphism of the short complex
of abelian sheaves underlying a short complex of `𝒪_X`-modules: the maps of the complex are
`𝒪_X`-linear. -/
@[simps]
noncomputable def smulShortComplexHom (r : Γ(X, ⊤)) :
    (S.map (SheafOfModules.toSheaf X.ringCatSheaf)) ⟶
      (S.map (SheafOfModules.toSheaf X.ringCatSheaf)) where
  τ₁ := smulSheafHom S.X₁ r
  τ₂ := smulSheafHom S.X₂ r
  τ₃ := smulSheafHom S.X₃ r
  comm₁₂ := smulSheafHom_comp S.f r
  comm₂₃ := smulSheafHom_comp S.g r

/-- **The extension class of a short exact sequence of `𝒪_X`-modules is `𝒪_X`-linear.**
This is the naturality of `ShortComplex.ShortExact.extClass` applied to multiplication by a
global section, and it is what makes the connecting map of the long exact sequence
linear. -/
lemma extClass_smul_comm (hS : S.ShortExact) (r : Γ(X, ⊤)) :
    (shortExact_map_toSheaf hS).extClass.comp (Ext.mk₀ (smulSheafHom S.X₁ r)) (add_zero 1) =
      (Ext.mk₀ (smulSheafHom S.X₃ r)).comp (shortExact_map_toSheaf hS).extClass
        (zero_add 1) :=
  ShortComplex.ShortExact.extClass_naturality _ _ (smulShortComplexHom S r)

/-- **The connecting map of the cohomology long exact sequence, as a linear map.**
`δ : Hⁿ⁰(X, F₃) → Hⁿ¹(X, F₁)` for `n₀ + 1 = n₁`, given by composition with the extension
class of the short exact sequence. -/
noncomputable def HDelta (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    H S.X₃ n₀ →ₗ[Γ(X, ⊤)] H S.X₁ n₁ where
  toFun x := x.comp (shortExact_map_toSheaf hS).extClass h
  map_add' x y := Ext.add_comp x y _ h
  map_smul' r x := by
    simp only [RingHom.id_apply, smul_def, Ext.comp_assoc_of_second_deg_zero,
      Ext.comp_assoc_of_third_deg_zero]
    rw [extClass_smul_comm S hS r]

@[simp]
lemma HDelta_apply (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (x : H S.X₃ n₀) :
    HDelta S hS n₀ n₁ h x = x.comp (shortExact_map_toSheaf hS).extClass h := rfl

/-- Exactness of the cohomology sequence at `Hⁿ(X, F₂)`. -/
theorem exact_HMap_HMap (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (HMap S.f n) (HMap S.g n) := by
  have hex := Abelian.Ext.covariant_sequence_exact₂' (constantIntSheaf X)
    (shortExact_map_toSheaf hS) n
  rw [ShortComplex.ab_exact_iff_function_exact] at hex
  exact hex

/-- Exactness of the cohomology sequence at `Hⁿ⁰(X, F₃)`. -/
theorem exact_HMap_HDelta (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (HMap S.g n₀) (HDelta S hS n₀ n₁ h) := by
  have hex := Abelian.Ext.covariant_sequence_exact₃' (constantIntSheaf X)
    (shortExact_map_toSheaf hS) n₀ n₁ h
  rw [ShortComplex.ab_exact_iff_function_exact] at hex
  exact hex

/-- Exactness of the cohomology sequence at `Hⁿ¹(X, F₁)`. -/
theorem exact_HDelta_HMap (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (HDelta S hS n₀ n₁ h) (HMap S.f n₁) := by
  have hex := Abelian.Ext.covariant_sequence_exact₁' (constantIntSheaf X)
    (shortExact_map_toSheaf hS) n₀ n₁ h
  rw [ShortComplex.ab_exact_iff_function_exact] at hex
  exact hex

section EulerCharacteristic

variable {k : Type u} [Field k] [X.Over (Spec (CommRingCat.of k))]

/-- `H⁰` of a monomorphism of `𝒪_X`-modules is injective: `H⁰(X, F) = Hom(ℤ_X, F)` and
`Hom(A, -)` is left exact. -/
lemma injective_HMap_zero {F G : X.Modules} (φ : F ⟶ G)
    [Mono ((SheafOfModules.toSheaf X.ringCatSheaf).map φ)] :
    Function.Injective (HMap φ 0) := by
  intro x y hxy
  refine Ext.addEquiv₀.injective ((cancel_mono
    ((SheafOfModules.toSheaf X.ringCatSheaf).map φ)).mp ?_)
  rw [← Sheaf.H.addEquiv₀_map, ← Sheaf.H.addEquiv₀_map]
  exact congrArg Ext.addEquiv₀ hxy

/-- If `H²` of the sub vanishes, `H¹` of the quotient map is surjective. -/
lemma surjective_HMap_one (hS : S.ShortExact) (h2 : Subsingleton (H S.X₁ 2)) :
    Function.Surjective (HMap S.g 1) := by
  intro y
  have hex := exact_HMap_HDelta S hS 1 2 rfl
  exact (hex y).mp (Subsingleton.elim _ _)

/-- **Additivity of the Euler characteristic.** For a short exact sequence
`0 → F₁ → F₂ → F₃ → 0` of `𝒪_X`-modules on a `k`-scheme whose cohomology is finite
dimensional in degrees `0, 1` and vanishes in degree `2` on `F₁`,

`χ(F₂) = χ(F₁) + χ(F₃)`.

The hypothesis `Subsingleton (H¹ F₁ 2)` is Grothendieck vanishing on a curve; on a curve it
is automatic, but Mathlib has no Grothendieck vanishing, so it is carried explicitly. This
is the step that makes Riemann–Roch an induction on divisors: adding a point to `D` changes
`χ(𝒪_C(D))` by `1` because the skyscraper quotient has `χ = 1`. -/
theorem eulerChar_add_of_shortExact (hS : S.ShortExact) (h2 : Subsingleton (H S.X₁ 2))
    [FiniteDimensional k (H S.X₂ 0)] [FiniteDimensional k (H S.X₃ 0)]
    [FiniteDimensional k (H S.X₁ 1)] [FiniteDimensional k (H S.X₂ 1)] :
    eulerChar k S.X₂ = eulerChar k S.X₁ + eulerChar k S.X₃ := by
  haveI : Mono ((SheafOfModules.toSheaf X.ringCatSheaf).map S.f) :=
    (shortExact_map_toSheaf hS).mono_f
  have key := Module.finrank_alternating_eq_zero_of_exact₆ (k := k)
    (a := LinearMap.restrictScalars k (HMap S.f 0))
    (b := LinearMap.restrictScalars k (HMap S.g 0))
    (c := LinearMap.restrictScalars k (HDelta S hS 0 1 rfl))
    (d := LinearMap.restrictScalars k (HMap S.f 1))
    (e := LinearMap.restrictScalars k (HMap S.g 1))
    (injective_HMap_zero S.f) (exact_HMap_HMap S hS 0) (exact_HMap_HDelta S hS 0 1 rfl)
    (exact_HDelta_HMap S hS 0 1 rfl) (exact_HMap_HMap S hS 1) (surjective_HMap_one S hS h2)
  simp only [eulerChar_def, h_def]
  omega

end EulerCharacteristic

end AlgebraicGeometry.Scheme.Modules
