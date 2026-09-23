module

public import StacksAndModuli.API.SchemeModulesTensor

/-!
# Multiplication by a global function as a morphism of sheaves of modules

Mathlib's `AlgebraicGeometry.Scheme.Modules.smul` gives multiplication by a section as an
endomorphism of `Γ(M, U)` for a single open `U`.  This file bundles multiplication by a *global*
function into a morphism `M ⟶ M`, and proves the one compatibility the `Γ_*` comparison needs:
it commutes with tensoring, `F ⊗ (r • 𝟙_G) = r • 𝟙_{F ⊗ G}`.

That compatibility is what lets the identity "`x_i^N = (x_i/x_j)^N · x_j^N` on `D₊(x_j)`" — proved
for the twisting sheaves in `StacksAndModuli/API/ProjRatioSectionMul.lean` — be transported to `F(d)` for
an arbitrary sheaf of modules `F`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.smulPresheafHom`, `smulHom`.
* `AlgebraicGeometry.Scheme.Modules.tensorMapRight_smulHom`.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The restriction of a global function to an open, as a scalar for presheaves of modules. -/
noncomputable def resTop (r : Γ(X, ⊤)) (U : (X.Opens)ᵒᵖ) : X.ringCatSheaf.obj.obj U :=
  (X.presheaf.map (homOfLE (le_top (a := U.unop))).op).hom r

theorem map_resTop (r : Γ(X, ⊤)) {U V : (X.Opens)ᵒᵖ} (f : U ⟶ V) :
    (X.ringCatSheaf.obj.map f).hom (resTop r U) = resTop r V := by
  change (X.presheaf.map f).hom ((X.presheaf.map _).hom r) = _
  rw [← CategoryTheory.comp_apply, ← X.presheaf.map_comp]
  congr 1

/-- Multiplication by a global function, as an endomorphism of a presheaf of modules. -/
noncomputable def smulPresheafHom (r : Γ(X, ⊤)) (P : X.PresheafOfModules) : P ⟶ P where
  app U := ModuleCat.ofHom
    { toFun := fun m ↦ resTop r U • m
      map_add' := fun a b ↦ smul_add _ _ _
      map_smul' := fun c m ↦ by
        let _ : CommRing (X.ringCatSheaf.obj.obj U) :=
          inferInstanceAs (CommRing (X.presheaf.obj U))
        change resTop r U • (c • m) = c • (resTop r U • m)
        rw [smul_smul, smul_smul, mul_comm] }
  naturality {U V} f := by
    ext m
    have h1 := P.map_smul f (resTop r U) m
    rw [map_resTop] at h1
    exact h1.symm

@[simp]
theorem smulPresheafHom_app_apply (r : Γ(X, ⊤)) (P : X.PresheafOfModules)
    (U : (X.Opens)ᵒᵖ) (m : P.obj U) :
    (smulPresheafHom r P).app U m = resTop r U • m := rfl

/-- Multiplication by a global function commutes with every morphism of presheaves of
modules. -/
theorem smulPresheafHom_naturality (r : Γ(X, ⊤)) {P Q : X.PresheafOfModules} (φ : P ⟶ Q) :
    φ ≫ smulPresheafHom r Q = smulPresheafHom r P ≫ φ := by
  refine PresheafOfModules.hom_ext fun U ↦ ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun m ↦ ?_)
  exact ((φ.app U).hom.map_smul (resTop r U) m).symm

/-- Multiplication by a global function, as an endomorphism of a sheaf of modules. -/
noncomputable def smulHom (r : Γ(X, ⊤)) (M : X.Modules) : M ⟶ M :=
  ⟨smulPresheafHom r M.val⟩

/-- Sheafification carries multiplication by a global function to multiplication by the same
function.  Both sides have the same image under the sheafification adjunction, namely
`smulPresheafHom r P ≫ unit`. -/
theorem sheafification_map_smulPresheafHom (r : Γ(X, ⊤)) (P : X.PresheafOfModules) :
    (sheafification X).map (smulPresheafHom r P) = smulHom r ((sheafification X).obj P) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  refine (adj.homEquiv P ((sheafification X).obj P)).injective ?_
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have h1 : smulPresheafHom r P ≫ adj.unit.app P
      = adj.unit.app P ≫ (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
          ((SheafOfModules.forget X.ringCatSheaf).map
            ((sheafification X).map (smulPresheafHom r P))) :=
    adj.unit.naturality (smulPresheafHom r P)
  simp only [Functor.comp_map]
  rw [← h1]
  refine PresheafOfModules.hom_ext fun U ↦ ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun m ↦ ?_)
  exact ((adj.unit.app P).app U).hom.map_smul (resTop r U) m

/-- `x ⊗ (r • y) = r • (x ⊗ y)` over the base ring, with no `SMulCommClass` side condition. -/
theorem tmul_smul_base {R : Type*} [CommSemiring R] {M N : Type*} [AddCommMonoid M]
    [Module R M] [AddCommMonoid N] [Module R N] (r : R) (x : M) (y : N) :
    x ⊗ₜ[R] (r • y) = r • (x ⊗ₜ[R] y) := by
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']

/-- Whiskering by `F` on the left sends multiplication by `r` to multiplication by `r`. -/
theorem whiskerLeft_smulPresheafHom (r : Γ(X, ⊤)) (F G : X.Modules) :
    MonoidalCategoryStruct.whiskerLeft (C := X.PresheafOfModules) F.val (smulHom r G).val
      = smulPresheafHom r
          (MonoidalCategoryStruct.tensorObj (C := X.PresheafOfModules) F.val G.val) := by
  refine PresheafOfModules.hom_ext fun U ↦ ?_
  refine ModuleCat.MonoidalCategory.tensor_ext fun x y ↦ ?_
  exact tmul_smul_base _ x y

/-- Multiplication by a global function commutes with every morphism of sheaves of modules. -/
theorem smulHom_naturality (r : Γ(X, ⊤)) {M N : X.Modules} (φ : M ⟶ N) :
    φ ≫ smulHom r N = smulHom r M ≫ φ :=
  SheafOfModules.hom_ext (smulPresheafHom_naturality r φ.val)

/-- **Multiplication by a global function commutes with tensoring.** -/
theorem tensorMapRight_smulHom (r : Γ(X, ⊤)) (F G : X.Modules) :
    tensorMapRight F (smulHom r G) = smulHom r (tensor F G) := by
  change (sheafification X).map (MonoidalCategoryStruct.whiskerLeft
    (C := X.PresheafOfModules) F.val ((SheafOfModules.forget _).map (smulHom r G))) = _
  rw [show (SheafOfModules.forget _).map (smulHom r G) = (smulHom r G).val from rfl,
    whiskerLeft_smulPresheafHom]
  exact sheafification_map_smulPresheafHom r _

end AlgebraicGeometry.Scheme.Modules
