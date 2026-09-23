module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Spec

/-!
# Global sections of a sheaf of modules on a scheme over a base ring

For a scheme `X` equipped with a morphism `f : X ⟶ Spec R`, the global functions `Γ(X, ⊤)`
are an `R`-algebra, and hence the global sections `Γ(M, ⊤)` of any sheaf of modules `M` on
`X` are an `R`-module. This is what gives `H⁰(X, M)` a dimension over the base, and so what
makes Hilbert functions and Hilbert polynomials expressible.

Both structures are provided as `def`s rather than instances: a scheme carries no
distinguished morphism to an affine scheme, so the `R`-module structure on `Γ(M, ⊤)` depends
on the choice of `f` and must not be found by typeclass search. Install it locally with
`letI := Scheme.Modules.globalSectionsModule f M`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.baseRingHom`: the ring map `R ⟶ Γ(X, ⊤)` attached to a
  morphism `X ⟶ Spec R`.
* `AlgebraicGeometry.Scheme.Modules.globalSectionsAlgebra`: the induced `R`-algebra
  structure on `Γ(X, ⊤)`.
* `AlgebraicGeometry.Scheme.Modules.globalSectionsModule`: the induced `R`-module structure
  on `Γ(M, ⊤)`.
* `AlgebraicGeometry.Scheme.Modules.globalSectionsLinearMap`: a morphism of module sheaves
  induces an `R`-linear map on global sections.
* `AlgebraicGeometry.Scheme.Modules.globalSectionsLinearEquivOfIso`: an isomorphism of
  module sheaves induces an `R`-linear equivalence on global sections.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {R : CommRingCat.{u}}

/-- The ring map from the base ring to the global functions of a scheme over `Spec R`,
obtained from `f` on global sections together with `Γ(Spec R, ⊤) ≅ R`. -/
noncomputable def baseRingHom (f : X ⟶ Spec R) : R ⟶ Γ(X, ⊤) :=
  (Scheme.ΓSpecIso R).inv ≫ f.appTop

/-- The map from the base ring to global functions is compatible with changing the
affine base. -/
@[reassoc]
theorem baseRingHom_comp {S : CommRingCat.{u}} (φ : R ⟶ S)
    (f : X ⟶ Spec S) :
    φ ≫ baseRingHom f = baseRingHom (f ≫ Spec.map φ) := by
  unfold baseRingHom
  rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality,
    Category.assoc, ← Scheme.Hom.comp_appTop]

/-- The map from the base ring to global functions is compatible with
precomposition on the source scheme. -/
@[reassoc]
theorem baseRingHom_comp_appTop {Y : Scheme.{u}} (f : X ⟶ Y)
    (p : Y ⟶ Spec R) :
    baseRingHom p ≫ f.appTop = baseRingHom (f ≫ p) := by
  unfold baseRingHom
  rw [Category.assoc, Scheme.Hom.comp_appTop]

/-- The global functions of a scheme over `Spec R` form an `R`-algebra.

Not an instance: it depends on the chosen morphism `f`. -/
@[instance_reducible]
noncomputable def globalSectionsAlgebra (f : X ⟶ Spec R) : Algebra R Γ(X, ⊤) :=
  (baseRingHom f).hom.toAlgebra

/-- The global sections of a sheaf of modules on a scheme over `Spec R` form an
`R`-module.

Not an instance: it depends on the chosen morphism `f`. Install it with
`letI := globalSectionsModule f M`. -/
@[instance_reducible]
noncomputable def globalSectionsModule (f : X ⟶ Spec R) (M : X.Modules) :
    Module R Γ(M, ⊤) :=
  Module.compHom _ (baseRingHom f).hom

/-- A morphism of module sheaves induces a linear map on global sections over the base
ring. -/
noncomputable def globalSectionsLinearMap (f : X ⟶ Spec R) {M N : X.Modules}
    (φ : M ⟶ N) :
    letI := globalSectionsModule f M
    letI := globalSectionsModule f N
    Γ(M, ⊤) →ₗ[R] Γ(N, ⊤) := by
  letI := globalSectionsModule f M
  letI := globalSectionsModule f N
  exact
    { toFun := φ.val.app (op ⊤)
      map_add' := map_add _
      map_smul' := fun r m ↦ by
        change φ.val.app (op ⊤) ((baseRingHom f).hom r • m) =
          (baseRingHom f).hom r • φ.val.app (op ⊤) m
        exact _root_.map_smul _ _ _ }

@[simp]
theorem globalSectionsLinearMap_apply (f : X ⟶ Spec R) {M N : X.Modules}
    (φ : M ⟶ N) (x : Γ(M, ⊤)) :
    globalSectionsLinearMap f φ x = φ.val.app (op ⊤) x := rfl

/-- An isomorphism of module sheaves induces an `R`-linear equivalence on global
sections, for the `R`-module structures determined by `f : X ⟶ Spec R`. -/
noncomputable def globalSectionsLinearEquivOfIso {M N : X.Modules}
    (f : X ⟶ Spec R) (e : M ≅ N) :
    letI := globalSectionsModule f M
    letI := globalSectionsModule f N
    Γ(M, ⊤) ≃ₗ[R] Γ(N, ⊤) := by
  letI := globalSectionsModule f M
  letI := globalSectionsModule f N
  let eTop : M.val.obj (op ⊤) ≅ N.val.obj (op ⊤) :=
    { hom := e.hom.val.app (op ⊤)
      inv := e.inv.val.app (op ⊤)
      hom_inv_id := congrArg (fun k ↦ k.val.app (op ⊤)) e.hom_inv_id
      inv_hom_id := congrArg (fun k ↦ k.val.app (op ⊤)) e.inv_hom_id }
  exact
    { toEquiv := eTop.toLinearEquiv.toEquiv
      map_add' := eTop.toLinearEquiv.map_add
      map_smul' := fun r m ↦ by
        change e.hom.val.app (op ⊤) ((baseRingHom f).hom r • m) =
          (baseRingHom f).hom r • e.hom.val.app (op ⊤) m
        exact _root_.map_smul _ _ _ }

end AlgebraicGeometry.Scheme.Modules
