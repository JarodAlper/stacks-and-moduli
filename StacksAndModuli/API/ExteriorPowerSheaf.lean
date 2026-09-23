module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import StacksAndModuli.API.ExteriorPowerBaseChange

/-!
# The exterior power of a presheaf of modules

Supporting API with no Stacks Project counterpart of its own, consumed by the relative
Plücker embedding `Gr(q, V) ↪ Gr(1, ⋀^q V)` of **Theorem 2.1.1**: for a presheaf of
modules `M` over a presheaf of commutative rings `R`, the presheaf of modules
`U ↦ ⋀[R(U)]^n M(U)`, whose restriction maps are the semilinear functoriality
`exteriorPower.mapSemilinear` of exterior powers.

Sheafification (for a sheaf of modules on a scheme) and quasi-coherence are developed
downstream of this file.

Main declarations:
- `PresheafOfModules.exteriorPower`: the presheaf `U ↦ ⋀[R(U)]^n M(U)`;
- `PresheafOfModules.exteriorPowerMap`: its functoriality in `M`.
-/

@[expose] public section

universe u u₁ v₁

open CategoryTheory

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
variable (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) (n : ℕ)

/-- The restriction map of the exterior-power presheaf: the semilinear extension of the
restriction map of `M` to `n`-th exterior powers. -/
noncomputable def exteriorPowerObjMap {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ModuleCat.of (R.obj X)
        (⋀[R.obj X]^n (M.obj X) : Submodule (R.obj X) (ExteriorAlgebra (R.obj X) (M.obj X))) ⟶
      (ModuleCat.restrictScalars ((R ⋙ forget₂ CommRingCat RingCat).map f).hom).obj
        (ModuleCat.of (R.obj Y)
          (⋀[R.obj Y]^n (M.obj Y) :
            Submodule (R.obj Y) (ExteriorAlgebra (R.obj Y) (M.obj Y)))) :=
  letI : Algebra (R.obj X) (R.obj Y) := (R.map f).hom.toAlgebra
  letI : Module (R.obj X) (M.obj Y) := Module.compHom _ (R.map f).hom
  haveI : IsScalarTower (R.obj X) (R.obj Y) (M.obj Y) :=
    ⟨fun r s m ↦ by
      show ((R.map f).hom r * s) • m = (R.map f).hom r • s • m
      rw [mul_smul]⟩
  let f' : M.obj X →ₗ[R.obj X] M.obj Y := (M.map f).hom
  ModuleCat.ofHom
    (exteriorPower.mapSemilinear (R.obj X) (R.obj Y) n (M.obj X) f')

set_option maxHeartbeats 800000 in
lemma exteriorPowerObjMap_ιMulti {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : Fin n → M.obj X) :
    (exteriorPowerObjMap M n f).hom
        (exteriorPower.ιMulti (R.obj X) n m) =
      exteriorPower.ιMulti (R.obj Y) n (fun i ↦ show M.obj Y from M.map f (m i)) := by
  letI : Algebra (R.obj X) (R.obj Y) := (R.map f).hom.toAlgebra
  letI : Module (R.obj X) (M.obj Y) := Module.compHom _ (R.map f).hom
  haveI : IsScalarTower (R.obj X) (R.obj Y) (M.obj Y) :=
    ⟨fun r s m ↦ by
      show ((R.map f).hom r * s) • m = (R.map f).hom r • s • m
      rw [mul_smul]⟩
  let f' : M.obj X →ₗ[R.obj X] M.obj Y := (M.map f).hom
  exact exteriorPower.mapSemilinear_ιMulti (R.obj X) (R.obj Y) n (M.obj X) f' m

/-- **The exterior power of a presheaf of modules**: the presheaf
`U ↦ ⋀[R(U)]^n M(U)`, with restriction maps the semilinear functoriality of exterior
powers. -/
noncomputable def exteriorPower :
    PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat) where
  obj X := ModuleCat.of (R.obj X)
    (⋀[R.obj X]^n (M.obj X) : Submodule (R.obj X) (ExteriorAlgebra (R.obj X) (M.obj X)))
  map f := exteriorPowerObjMap M n f
  map_id X := by
    ext m
    simp only [LinearMap.compAlternatingMap_apply]
    rw [exteriorPowerObjMap_ιMulti]
    exact congrArg (exteriorPower.ιMulti (R.obj X) n)
      (funext fun i ↦ by rw [M.map_id]; rfl)
  map_comp {X Y Z} f g := by
    ext m
    change (exteriorPowerObjMap M n (f ≫ g)).hom (exteriorPower.ιMulti (R.obj X) n m) =
      (exteriorPowerObjMap M n g).hom
        ((exteriorPowerObjMap M n f).hom (exteriorPower.ιMulti (R.obj X) n m))
    rw [exteriorPowerObjMap_ιMulti]
    rw [exteriorPowerObjMap_ιMulti]
    rw [exteriorPowerObjMap_ιMulti]
    exact congrArg (exteriorPower.ιMulti (R.obj Z) n)
      (funext fun i ↦ M.map_comp_apply f g (m i))

variable {M₁ M₂ : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}

/-- The component of the exterior-power functoriality: the `R(X)`-linear map on
sections induced by `φ.app X`. -/
noncomputable def exteriorPowerMapApp (φ : M₁ ⟶ M₂) (X : Cᵒᵖ) :
    (⋀[R.obj X]^n (M₁.obj X) : Submodule (R.obj X) (ExteriorAlgebra (R.obj X) (M₁.obj X)))
      →ₗ[R.obj X]
    (⋀[R.obj X]^n (M₂.obj X) : Submodule (R.obj X) (ExteriorAlgebra (R.obj X) (M₂.obj X))) :=
  _root_.exteriorPower.map n
    (show M₁.obj X →ₗ[R.obj X] M₂.obj X from (φ.app X).hom)

@[simp]
lemma exteriorPowerMapApp_ιMulti (φ : M₁ ⟶ M₂) (X : Cᵒᵖ) (m : Fin n → M₁.obj X) :
    exteriorPowerMapApp n φ X (_root_.exteriorPower.ιMulti (R.obj X) n m) =
      _root_.exteriorPower.ιMulti (R.obj X) n (fun i ↦ show M₂.obj X from φ.app X (m i)) := by
  rw [exteriorPowerMapApp, _root_.exteriorPower.map_apply_ιMulti]
  rfl

/-- Functoriality of the exterior-power presheaf in the presheaf of modules. -/
noncomputable def exteriorPowerMap (φ : M₁ ⟶ M₂) :
    exteriorPower M₁ n ⟶ exteriorPower M₂ n where
  app X := ModuleCat.ofHom (exteriorPowerMapApp n φ X)
  naturality {X Y} f := by
    change exteriorPowerObjMap M₁ n f ≫
        (ModuleCat.restrictScalars ((R ⋙ forget₂ CommRingCat RingCat).map f).hom).map
          (ModuleCat.ofHom (exteriorPowerMapApp n φ Y)) =
      ModuleCat.ofHom (exteriorPowerMapApp n φ X) ≫ exteriorPowerObjMap M₂ n f
    ext m
    change (exteriorPowerMapApp n φ Y)
        ((exteriorPowerObjMap M₁ n f).hom (_root_.exteriorPower.ιMulti (R.obj X) n m)) =
      (exteriorPowerObjMap M₂ n f).hom
        ((exteriorPowerMapApp n φ X) (_root_.exteriorPower.ιMulti (R.obj X) n m))
    rw [exteriorPowerObjMap_ιMulti]
    rw [exteriorPowerMapApp_ιMulti]
    rw [exteriorPowerMapApp_ιMulti]
    rw [exteriorPowerObjMap_ιMulti]
    exact congrArg (_root_.exteriorPower.ιMulti (R.obj Y) n)
      (funext fun i ↦ naturality_apply φ f (m i))

/-- The exterior-power presheaf map of the identity. -/
lemma exteriorPowerMap_id {M₁ : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)} :
    exteriorPowerMap n (𝟙 M₁) = 𝟙 (exteriorPower M₁ n) := by
  ext X : 2
  change exteriorPowerMapApp n (𝟙 M₁) X = LinearMap.id
  ext m
  simp only [LinearMap.compAlternatingMap_apply]
  rw [exteriorPowerMapApp_ιMulti]
  rfl

/-- The exterior-power presheaf map of a composition. -/
lemma exteriorPowerMap_comp {M₁ M₂ M₃ : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
    (φ : M₁ ⟶ M₂) (ψ : M₂ ⟶ M₃) :
    exteriorPowerMap n (φ ≫ ψ) = exteriorPowerMap n φ ≫ exteriorPowerMap n ψ := by
  ext X : 2
  change exteriorPowerMapApp n (φ ≫ ψ) X =
    (exteriorPowerMapApp n ψ X) ∘ₗ (exteriorPowerMapApp n φ X)
  ext m
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply]
  rw [exteriorPowerMapApp_ιMulti, exteriorPowerMapApp_ιMulti, exteriorPowerMapApp_ιMulti]
  rfl

/-- The exterior-power presheaf of an isomorphism of presheaves of modules. -/
noncomputable def exteriorPowerMapIso
    {M₁ M₂ : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)} (e : M₁ ≅ M₂) :
    exteriorPower M₁ n ≅ exteriorPower M₂ n where
  hom := exteriorPowerMap n e.hom
  inv := exteriorPowerMap n e.inv
  hom_inv_id := by
    rw [← exteriorPowerMap_comp, e.hom_inv_id, exteriorPowerMap_id]
  inv_hom_id := by
    rw [← exteriorPowerMap_comp, e.inv_hom_id, exteriorPowerMap_id]

end PresheafOfModules

end
