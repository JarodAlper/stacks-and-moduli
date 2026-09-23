module

public import StacksAndModuli.API.GlobalSectionsModElement
public import StacksAndModuli.API.PrincipalClosedFiberCokernel

/-!
# Global sections on a principal closed fibre

Suppose `X → Spec R`, an element `r : R`, and a morphism
`i : Z → X` over `Spec (R/(r))` are given.  If the cokernel of multiplication
by `r` on a module sheaf `M` is identified with `i_*i^*M`, then vanishing of
`H¹(X, M)` gives the expected base-change equivalence

`(R/(r)) ⊗[R] H⁰(X, M) ≃ H⁰(Z, i^*M)`.

The equivalence is linear over `R/(r)`.  This strengthens the `R`-linear
cokernel calculation in `GlobalSectionsModElement` and is the numerical
closed-fibre input in the DVR argument for Quot projectivity.

Main declaration:

* `Scheme.Modules.quotientTensorGlobalSectionsPullbackLinearEquiv_of_cokernelIso`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TensorProduct
open AlgebraicGeometry

universe u

namespace LinearEquiv

/-- If `R → S` is surjective, an `R`-linear equivalence between `S`-modules
whose `R`-actions come from scalar restriction is automatically `S`-linear. -/
noncomputable def ofRestrictScalarsOfSurjective
    {R S M N : Type u}
    [CommSemiring R] [Semiring S] [Algebra R S]
    [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] [Module S M] [Module S N]
    [IsScalarTower R S M] [IsScalarTower R S N]
    (e : M ≃ₗ[R] N) (hsur : Function.Surjective (algebraMap R S)) :
    M ≃ₗ[S] N :=
  { e.toEquiv with
    map_add' := e.map_add
    map_smul' := by
      intro s m
      obtain ⟨r, rfl⟩ := hsur s
      change e ((algebraMap R S r) • m) =
        (algebraMap R S r) • e m
      rw [IsScalarTower.algebraMap_smul,
        IsScalarTower.algebraMap_smul]
      exact e.map_smul r m }

end LinearEquiv

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}} {X : Scheme.{u}}

/-- If the cokernel of multiplication by `r` is `i_*i^*M`, then `H¹(M) = 0`
identifies global sections on the closed fibre with the reduction of global
sections modulo `r`.

The hypothesis `hbase` says that `Z → X → Spec R` is obtained from the
displayed `Z → Spec (R/(r))` using the quotient map.  It is used to upgrade
the underlying `R`-linear cokernel calculation to an `R/(r)`-linear
equivalence. -/
noncomputable def
    quotientTensorGlobalSectionsPullbackLinearEquiv_of_cokernelIso
    {Z : Scheme.{u}} (p : X ⟶ Spec R) (r : R)
    (i : Z ⟶ X)
    (pZ : Z ⟶ Spec (principalClosedFiberRing r))
    (hbase : i ≫ p =
      pZ ≫ Spec.map (principalClosedFiberRingHom r))
    (M : X.Modules)
    [Mono (M.mulByGlobalSection ((baseRingHom p).hom r))]
    (hH1 : Subsingleton (((SheafOfModules.toSheaf _).obj M).H 1))
    (eC : cokernel (M.mulByGlobalSection ((baseRingHom p).hom r)) ≅
      (pushforward i).obj ((pullback i).obj M)) :
    let S := principalClosedFiberRing r
    let F := (pullback i).obj M
    letI := globalSectionsModule p M
    letI := globalSectionsModule pZ F
    (S ⊗[R] Γ(M, ⊤)) ≃ₗ[S] Γ(F, ⊤) := by
  dsimp only
  let S := principalClosedFiberRing r
  let q := principalClosedFiberRingHom r
  let F := (pullback i).obj M
  let C := cokernel
    (M.mulByGlobalSection ((baseRingHom p).hom r))
  letI : Module R Γ(M, ⊤) := globalSectionsModule p M
  letI : Module R Γ(C, ⊤) := globalSectionsModule p C
  letI : Module R Γ(F, ⊤) := globalSectionsModule (i ≫ p) F
  letI : Module S Γ(F, ⊤) := globalSectionsModule pZ F
  have hbaseRing : q ≫ baseRingHom pZ = baseRingHom (i ≫ p) := by
    rw [baseRingHom_comp q pZ, ← hbase]
  letI : IsScalarTower R S Γ(F, ⊤) := by
    apply IsScalarTower.of_algebraMap_smul
    intro a x
    change (baseRingHom pZ).hom (q.hom a) • x =
      (baseRingHom (i ≫ p)).hom a • x
    exact congrArg (fun t : Γ(Z, ⊤) ↦ t • x)
      (congrArg (fun f : R ⟶ Γ(Z, ⊤) ↦ f.hom a) hbaseRing)
  let e₀ := quotientTensorGlobalSectionsCokernelLinearEquiv
    p r M hH1
  let eTop : C.val.obj (op ⊤) ≅
      ((pushforward i).obj F).val.obj (op ⊤) :=
    { hom := eC.hom.val.app (op ⊤)
      inv := eC.inv.val.app (op ⊤)
      hom_inv_id := congrArg
        (fun k ↦ k.val.app (op ⊤)) eC.hom_inv_id
      inv_hom_id := congrArg
        (fun k ↦ k.val.app (op ⊤)) eC.inv_hom_id }
  let e₁ : Γ(C, ⊤) ≃ₗ[R] Γ(F, ⊤) :=
    { toEquiv := eTop.toLinearEquiv.toEquiv
      map_add' := eTop.toLinearEquiv.map_add
      map_smul' := fun a m ↦ by
        let y : Γ(F, ⊤) := eC.hom.val.app (op ⊤) m
        have hm := _root_.map_smul
          (eC.hom.val.app (op ⊤)).hom
            ((baseRingHom p).hom a) m
        change (show Γ(F, ⊤) from
            eC.hom.val.app (op ⊤)
              ((baseRingHom p).hom a • m)) =
          i.appTop ((baseRingHom p).hom a) • y at hm
        change (show Γ(F, ⊤) from
            eC.hom.val.app (op ⊤)
              ((baseRingHom p).hom a • m)) =
          (baseRingHom (i ≫ p)).hom a • y
        rw [← baseRingHom_comp_appTop i p]
        exact hm }
  exact LinearEquiv.ofRestrictScalarsOfSurjective (e₀.trans e₁)
    Ideal.Quotient.mk_surjective

end AlgebraicGeometry.Scheme.Modules

end
