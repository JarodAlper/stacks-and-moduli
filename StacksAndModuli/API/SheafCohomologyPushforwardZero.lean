module

public import StacksAndModuli.API.SheafCohomologyModule

/-!
# Degree-zero cohomology of a pushforward

For a morphism of schemes `f : X ⟶ Y`, global sections of a pushed-forward module
sheaf are the global sections of the original module sheaf.  When both schemes are over
the same ring and `f` respects their structure morphisms, this identification is linear
over the base.  Consequently, the dimension of degree-zero cohomology of `f_* M` can be
computed directly from the global sections of `M`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.pushforwardGlobalSectionsLinearEquiv`: the
  base-linear identification `Γ(Y, f_* M) ≃ Γ(X, M)`.
* `AlgebraicGeometry.Scheme.Modules.h_zero_pushforward_eq_finrank_globalSections`:
  `h⁰(Y, f_* M) = dim_k Γ(X, M)` for a morphism of `k`-schemes.
* `AlgebraicGeometry.Scheme.Modules.h_zero_pushforward_eq`: pushforward preserves
  degree-zero cohomology dimensions.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Global sections commute with pushforward, as a linear equivalence over any base
respected by the morphism. -/
noncomputable def pushforwardGlobalSectionsLinearEquiv
    {R : CommRingCat.{u}} {X Y : Scheme.{u}}
    (f : X ⟶ Y) (pX : X ⟶ Spec R) (pY : Y ⟶ Spec R)
    (hf : f ≫ pY = pX) (M : X.Modules) :
    letI := globalSectionsModule pY ((pushforward f).obj M)
    letI := globalSectionsModule pX M
    Γ((pushforward f).obj M, ⊤) ≃ₗ[R] Γ(M, ⊤) := by
  letI := globalSectionsModule pY ((pushforward f).obj M)
  letI := globalSectionsModule pX M
  refine
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r x ↦ ?_ }
  change (M.smul (f.appTop.hom ((baseRingHom pY).hom r))).hom x =
    (M.smul ((baseRingHom pX).hom r)).hom x
  rw [← ConcreteCategory.comp_apply, baseRingHom_comp_appTop, hf]

/-- Degree-zero cohomology of a pushforward is the dimension of the original global
sections. -/
lemma h_zero_pushforward_eq_finrank_globalSections
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))]
    [Y.Over (Spec (CommRingCat.of k))]
    (f : X ⟶ Y) (hf : f ≫ (Y ↘ Spec (CommRingCat.of k)) =
      X ↘ Spec (CommRingCat.of k)) (M : X.Modules) :
    letI := globalSectionsModule (X ↘ Spec (CommRingCat.of k)) M
    h k ((pushforward f).obj M) 0 = Module.finrank k Γ(M, ⊤) := by
  let _ := globalSectionsModule (Y ↘ Spec (CommRingCat.of k))
    ((pushforward f).obj M)
  let _ := globalSectionsModule (X ↘ Spec (CommRingCat.of k)) M
  rw [h_zero_eq_finrank_globalSections]
  exact (pushforwardGlobalSectionsLinearEquiv f _ _ hf M).finrank_eq

/-- Pushforward along a morphism of `k`-schemes preserves the dimension of degree-zero
cohomology. -/
lemma h_zero_pushforward_eq
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))]
    [Y.Over (Spec (CommRingCat.of k))]
    (f : X ⟶ Y) (hf : f ≫ (Y ↘ Spec (CommRingCat.of k)) =
      X ↘ Spec (CommRingCat.of k)) (M : X.Modules) :
    h k ((pushforward f).obj M) 0 = h k M 0 := by
  let _ := globalSectionsModule (X ↘ Spec (CommRingCat.of k)) M
  rw [h_zero_pushforward_eq_finrank_globalSections k f hf M,
    h_zero_eq_finrank_globalSections]

end AlgebraicGeometry.Scheme.Modules
