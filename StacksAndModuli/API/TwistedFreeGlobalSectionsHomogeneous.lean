module

public import StacksAndModuli.API.ProjectiveTwistedFreeGlobalSectionsFinite
public import StacksAndModuli.API.ProjectiveGradedFreeH0Homogeneous
public import StacksAndModuli.API.ProjectiveGradedFreeBaseChange
public import StacksAndModuli.API.ProjectiveDVRQuotientPullbackSerre

/-!
# Global sections of a twisted-free sheaf as homogeneous forms

The scheme half of the `H⁰` bridge of `PLAN-hilbert-quot.md` for the twisted-free ambient
sheaf `F = 𝒪(-l)^{⊕J}`.  For a natural twist `d` with `d - l = e ≥ 0`,

`Γ(ℙⁿ_R, F(d)) ≃ₗ[R] (J → R[x₀, …, xₙ]_e)`.

Every ingredient is already proved:

* `Scheme.projectiveSpaceOverNegativeTwist_coproduct_twistIso_nat` — `F(d) ≅ 𝒪(d-l)^{⊕J}`;
* `Scheme.Modules.globalSectionsLinearEquivOfIso` — transport along a sheaf isomorphism;
* `Scheme.Modules.globalSectionsFiniteCoproductLinearEquiv` — `Γ(∐ F) ≅ ∀ j, Γ(F j)`;
* `AlgebraicGeometry.ProjectiveSpace.projectiveSpaceOverTwistGlobalSectionsLinearEquiv` and
  `MvPolynomial.homogeneousSubmoduleGlobalSectionsLinearEquiv` — the chartwise computation
  `Γ(ℙⁿ_R, 𝒪(e)) ≅ R[x]_e`.

The graded side of the same comparison is `GradedModule.bijective_cechAug_free`, so this is
the last missing half of `RelativeCohomology.SchemeGlobalSectionsComparison` for a
twisted-free ambient sheaf.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- `Γ(ℙⁿ_R, 𝒪(e)) ≅ R[x₀, …, xₙ]_e` for a natural twist, on the relative model. -/
noncomputable def twistGlobalSectionsHomogeneousEquiv
    (n : ℕ) (R : Type u) [CommRing R] (e : ℕ) :
    letI := Scheme.Modules.globalSectionsModule
      (Scheme.projectiveSpaceOverπ n (Spec (.of R)))
      (Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (e : ℤ))
    Γ(Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (e : ℤ), ⊤) ≃ₗ[R]
      MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R e := by
  letI := Scheme.Modules.globalSectionsModule
    (Scheme.projectiveSpaceOverπ n (Spec (.of R)))
    (Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (e : ℤ))
  letI := MvPolynomial.projectiveTwistGlobalSectionsModule n R e
  exact (projectiveSpaceOverTwistGlobalSectionsLinearEquiv n R e).trans
    (MvPolynomial.homogeneousSubmoduleGlobalSectionsLinearEquiv n R e).symm

/-- **The scheme half of the twisted-free `H⁰` comparison.**  For `F = 𝒪(-l)^{⊕J}` and a
natural twist `d` with `d - l = e ≥ 0`,
`Γ(ℙⁿ_R, F(d)) ≃ₗ[R] (J → R[x₀, …, xₙ]_e)`. -/
noncomputable def twistedFreeTwistGlobalSectionsHomogeneousEquiv
    {J : Type u} [Finite J] (n : ℕ) (R : Type u) [CommRing R] (l : ℤ) (d e : ℕ)
    (he : (e : ℤ) = (d : ℤ) - l) :
    letI := Scheme.Modules.globalSectionsModule
      (Scheme.projectiveSpaceOverπ n (Spec (.of R)))
      (Scheme.Modules.tensor
        (∐ fun _ : J => Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l))
        (Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (d : ℤ)))
    Γ(Scheme.Modules.tensor
        (∐ fun _ : J => Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l))
        (Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (d : ℤ)), ⊤) ≃ₗ[R]
      (J → MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R e) := by
  let p := Scheme.projectiveSpaceOverπ n (Spec (.of R))
  let A := Scheme.Modules.tensor
    (∐ fun _ : J => Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l))
    (Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (d : ℤ))
  let F : J → (Scheme.projectiveSpaceOver n (Spec (.of R))).Modules :=
    fun _ => Scheme.projectiveSpaceOverTwist n (Spec (.of R)) ((d : ℤ) - l)
  let eA : A ≅ ∐ F :=
    Scheme.projectiveSpaceOverNegativeTwist_coproduct_twistIso_nat
      (J := J) n (Spec (.of R)) l d
  let eT : Scheme.projectiveSpaceOverTwist n (Spec (.of R)) ((d : ℤ) - l) ≅
      Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (e : ℤ) :=
    eqToIso (congrArg (Scheme.projectiveSpaceOverTwist n (Spec (.of R))) he.symm)
  letI := Scheme.Modules.globalSectionsModule p A
  letI := Scheme.Modules.globalSectionsModule p
    (Scheme.projectiveSpaceOverTwist n (Spec (.of R)) ((d : ℤ) - l))
  letI := Scheme.Modules.globalSectionsModule p (∐ F)
  letI := Scheme.Modules.globalSectionsModule p
    (Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (e : ℤ))
  exact (Scheme.Modules.globalSectionsLinearEquivOfIso p eA).trans
    ((Scheme.Modules.globalSectionsFiniteCoproductLinearEquiv p F).trans
      (LinearEquiv.piCongrRight fun _ : J =>
        (Scheme.Modules.globalSectionsLinearEquivOfIso p eT).trans
          (twistGlobalSectionsHomogeneousEquiv n R e)))

/-- **The twisted-free `H⁰` comparison.**  For `F = 𝒪(-l)^{⊕ULift (Fin r)}` on `ℙⁿ_R` and a
natural twist `d` with `d - l = e ≥ 0`, the graded `H⁰` of `⨁_r S(-l)` in degree `d` agrees
with the global sections of `F(d)`.

This is `RelativeCohomology.SchemeGlobalSectionsComparison.globalSectionsIso` for the
twisted-free ambient sheaf, in the degree range that the structure's `bound` field allows. -/
noncomputable def twistedFreeGradedGlobalSectionsEquiv
    (n : ℕ) (R : Type u) [CommRing R] (l : ℤ) (r : ℕ) (d e : ℕ)
    (he : (e : ℤ) = (d : ℤ) - l) :
    letI := Scheme.Modules.globalSectionsModule
      (Scheme.projectiveSpaceOverπ n (Spec (.of R)))
      (Scheme.Modules.tensor
        (∐ fun _ : ULift.{u} (Fin r) =>
          Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l))
        (Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (d : ℤ)))
    ((((((GradedModule.structureModule R n).twist (-l)).pow r).cechHgr 0).obj (d : ℤ))) ≃ₗ[R]
      Γ(Scheme.Modules.tensor
        (∐ fun _ : ULift.{u} (Fin r) =>
          Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l))
        (Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (d : ℤ)), ⊤) := by
  letI := Scheme.Modules.globalSectionsModule
    (Scheme.projectiveSpaceOverπ n (Spec (.of R)))
    (Scheme.Modules.tensor
      (∐ fun _ : ULift.{u} (Fin r) =>
        Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l))
      (Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (d : ℤ)))
  exact (GradedModule.cechHgrFreeHomogeneousEquiv R n l r (d : ℤ) e he).trans
    (((LinearEquiv.funCongrLeft R
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R e)
        (Equiv.ulift.{u, 0} (α := Fin r)))).trans
      (twistedFreeTwistGlobalSectionsHomogeneousEquiv
        (J := ULift.{u} (Fin r)) n R l d e he).symm)

/-- **The fibre form of the twisted-free `H⁰` comparison.**  The base change of
`𝒪(-l)^{⊕r}` along `R → A` is `𝒪(-l)^{⊕r}` over `A`, so its global sections after a natural
twist `d` with `d - l = e ≥ 0` are again `Fin r → A[x]_e`. -/
noncomputable def twistedFreeBaseChangeGlobalSectionsEquiv
    (n : ℕ) (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (l : ℤ) (r : ℕ) (d e : ℕ) (he : (e : ℤ) = (d : ℤ) - l) :
    letI := Scheme.Modules.globalSectionsModule
      (Scheme.projectiveSpaceOverπ n (Spec (.of A)))
      (Scheme.projectiveSpaceOverTwistModule
        (Scheme.Modules.projectiveSpaceBaseChangeOfRingHom
          (∐ fun _ : ULift.{u} (Fin r) =>
            Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l))
          (algebraMap R A)) (d : ℤ))
    ((((((GradedModule.structureModule R n).twist (-l)).pow r).baseChange A).cechHgr 0).obj
        (d : ℤ)) ≃ₗ[A]
      Scheme.Modules.projectiveSpaceTwistedGlobalSections
        (Scheme.Modules.projectiveSpaceBaseChangeOfRingHom
          (∐ fun _ : ULift.{u} (Fin r) =>
            Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l))
          (algebraMap R A)) (d : ℤ) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let eQ : Scheme.Modules.projectiveSpaceBaseChangeOfRingHom
      (∐ fun _ : ULift.{u} (Fin r) =>
        Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l)) (algebraMap R A) ≅
      ∐ fun _ : ULift.{u} (Fin r) =>
        Scheme.projectiveSpaceOverTwist n (Spec (.of A)) (-l) :=
    Scheme.projectiveSpaceOverTwistedFree_pullbackIso n r l g
  let eTw := Scheme.Modules.tensorLeftIso eQ
    (Scheme.projectiveSpaceOverTwist n (Spec (.of A)) (d : ℤ))
  exact (GradedModule.cechHgrFreeBaseChangeHomogeneousEquiv
      (R := R) (A := A) (n := n) r l (d : ℤ) e he).trans
    (((LinearEquiv.funCongrLeft A
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A e)
        (Equiv.ulift.{u, 0} (α := Fin r)))).trans
      ((twistedFreeTwistGlobalSectionsHomogeneousEquiv
          (J := ULift.{u} (Fin r)) n A l d e he).symm.trans
        (Scheme.Modules.globalSectionsLinearEquivOfIso
          (Scheme.projectiveSpaceOverπ n (Spec (.of A))) eTw).symm))

end AlgebraicGeometry.ProjectiveSpace
