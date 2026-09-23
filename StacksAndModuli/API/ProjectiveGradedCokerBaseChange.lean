module

public import StacksAndModuli.API.ProjectiveGradedFreeBaseChange
public import StacksAndModuli.API.LinearMapCokernelBaseChange

/-!
# Base change of cokernels of graded-module morphisms

Scalar extension is right exact degree by degree, so it commutes with the cokernel of every
morphism of diagrammatic graded modules.  This file packages the degreewise linear
comparison as a morphism of graded modules and proves it is an isomorphism.  It also gives
the change-of-presentation isomorphism on cokernels induced by a commutative square whose
vertical maps are graded isomorphisms.

Main declarations:

* `GradedModule.cokerBaseChangeIso`;
* `GradedModule.cokerMapIso`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

open CategoryTheory TensorProduct

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable {n : ℕ} {M N : GradedModule R n}

/-- Evaluation of a base-changed graded morphism on a pure tensor. -/
@[simp] lemma baseChangeMap_app_tmul (f : M ⟶ N) (d : ℤ) (a : A) (x : M.obj d) :
    ((baseChangeMap f A).app d).hom (a ⊗ₜ[R] x) = a ⊗ₜ[R] (f.app d).hom x :=
  LinearMap.baseChange_tmul (f := (f.app d).hom) a x

/-- The canonical comparison from the cokernel of a base-changed graded morphism to the
base change of its degreewise cokernel. -/
noncomputable def cokerBaseChangeHom (f : M ⟶ N) :
    coker (baseChangeMap f A) ⟶ (coker f).baseChange A where
  app d := by
    let q : N.obj d →ₗ[R] (N.obj d ⧸ LinearMap.range (f.app d).hom) :=
      (LinearMap.range (f.app d).hom).mkQ
    have hq : Function.Surjective q := Submodule.mkQ_surjective _
    have hex : Function.Exact
        (LinearMap.baseChange A (f.app d).hom) (LinearMap.baseChange A q) := by
      simpa only [LinearMap.baseChange_eq_ltensor] using
        lTensor_exact A (LinearMap.exact_map_mkQ_range (f.app d).hom) hq
    exact ModuleCat.ofHom <|
      (LinearMap.range (LinearMap.baseChange A (f.app d).hom)).liftQ
        (LinearMap.baseChange A q) hex.linearMap_ker_eq.symm.le
  comm i d := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨x⟩
    exact congrArg
      (fun ψ : (N.baseChange A).obj d ⟶ ((coker f).baseChange A).obj (d + 1) ↦ ψ.hom x)
      ((baseChangeMap (toCoker f) A).comm i d)

/-- Right exactness makes every degree of `cokerBaseChangeHom` bijective. -/
lemma bijective_cokerBaseChangeHom_app (f : M ⟶ N) (d : ℤ) :
    Function.Bijective ((cokerBaseChangeHom (A := A) f).app d).hom := by
  let q : N.obj d →ₗ[R] (N.obj d ⧸ LinearMap.range (f.app d).hom) :=
    (LinearMap.range (f.app d).hom).mkQ
  have hq : Function.Surjective q := Submodule.mkQ_surjective _
  have hex : Function.Exact
      (LinearMap.baseChange A (f.app d).hom) (LinearMap.baseChange A q) := by
    simpa only [LinearMap.baseChange_eq_ltensor] using
      lTensor_exact A (LinearMap.exact_map_mkQ_range (f.app d).hom) hq
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    change LinearMap.baseChange A q x = 0 at hz
    rw [← LinearMap.mem_ker, hex.linearMap_ker_eq] at hz
    rw [Submodule.Quotient.mk_eq_zero]
    exact hz
  · intro z
    obtain ⟨x, rfl⟩ := LinearMap.baseChange_surjective A hq z
    exact ⟨Submodule.Quotient.mk x, rfl⟩

/-- Scalar extension commutes with degreewise cokernels of graded-module morphisms. -/
noncomputable def cokerBaseChangeIso (f : M ⟶ N) :
    (coker f).baseChange A ≅ coker (baseChangeMap f A) :=
  (isoOfBijective (cokerBaseChangeHom (A := A) f)
    (bijective_cokerBaseChangeHom_app (A := A) f)).symm

variable {k : Type u} [CommRing k] {m : ℕ}
variable {M₁ N₁ M₂ N₂ : GradedModule k m}

/-- A commutative square with isomorphic vertical maps carries the range of the upper map
onto the range of the lower map in every degree. -/
lemma cokerMap_range_app (f : M₁ ⟶ N₁) (g : M₂ ⟶ N₂)
    (eM : M₁ ≅ M₂) (eN : N₁ ≅ N₂)
    (h : f ≫ eN.hom = eM.hom ≫ g) (d : ℤ) :
    (LinearMap.range (f.app d).hom).map (eN.hom.app d).hom =
      LinearMap.range (g.app d).hom := by
  rw [← LinearMap.range_comp]
  have hd := congrArg ModuleCat.Hom.hom
    (congrArg (fun ψ : M₁ ⟶ N₂ ↦ ψ.app d) h)
  simp only [comp_app, ModuleCat.hom_comp] at hd
  rw [hd]
  apply LinearMap.range_comp_of_range_eq_top
  exact LinearEquiv.range (isoApp eM d).toLinearEquiv

/-- The degreewise quotient equivalence induced by a commutative square with isomorphic
vertical maps. -/
noncomputable def cokerMapAppEquiv (f : M₁ ⟶ N₁) (g : M₂ ⟶ N₂)
    (eM : M₁ ≅ M₂) (eN : N₁ ≅ N₂)
    (h : f ≫ eN.hom = eM.hom ≫ g) (d : ℤ) :
    (coker f).obj d ≃ₗ[k] (coker g).obj d := by
  change (N₁.obj d ⧸ LinearMap.range (f.app d).hom) ≃ₗ[k]
    (N₂.obj d ⧸ LinearMap.range (g.app d).hom)
  exact Submodule.Quotient.equiv _ _ (isoApp eN d).toLinearEquiv
    (cokerMap_range_app f g eM eN h d)

/-- A commutative square of graded morphisms whose vertical maps are isomorphisms induces
an isomorphism of degreewise cokernels. -/
noncomputable def cokerMapIso (f : M₁ ⟶ N₁) (g : M₂ ⟶ N₂)
    (eM : M₁ ≅ M₂) (eN : N₁ ≅ N₂)
    (h : f ≫ eN.hom = eM.hom ≫ g) : coker f ≅ coker g :=
  isoOfAppEquiv (fun d ↦ cokerMapAppEquiv f g eM eN h d) (fun i d x ↦ by
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      exact congrArg
        (fun ψ : N₁.obj d ⟶ N₂.obj (d + 1) ↦
          Submodule.Quotient.mk (ψ.hom x))
        (eN.hom.comm i d))

end AlgebraicGeometry.ProjectiveSpace.GradedModule

end

end
