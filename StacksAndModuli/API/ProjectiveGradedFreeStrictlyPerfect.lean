module

public import StacksAndModuli.API.TwistedFreeQuotPushforwardRank
public import StacksAndModuli.API.ProjectiveGradedFreeBaseChange
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# Strictly perfect Cech complexes for twisted-free graded modules

The Cech complex of a finite sum of twists of the polynomial structure module has a
universally strictly-perfect replacement in every degree in which the twist is
nonnegative.  The replacement is the degree piece itself, concentrated in cochain degree
zero.  The Cech augmentation computes its degree-zero homology, while the explicit
cohomology of projective space kills all positive homology, over the base ring and after
every coefficient change.

This is the base case needed to turn a finite twisted-free resolution of a flat finitely
presented sheaf into the strictly-perfect replacement used by arbitrary-base Cohomology
and Base Change.  The construction of that finite resolution is a separate relative
perfectness problem.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits TensorProduct
open AlgebraicGeometry ProjectiveSpectrum.Twist

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] {n : ℕ}

/-! ## Elementary single-complex comparisons -/

private lemma subsingleton_tensor_right {A : Type u} [CommRing A] [Algebra R A]
    {M : Type u} [AddCommGroup M] [Module R M] [Subsingleton M] :
    Subsingleton (A ⊗[R] M) := by
  refine ⟨fun x y ↦ ?_⟩
  have hz : ∀ z : A ⊗[R] M, z = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul a m => rw [Subsingleton.elim m 0, tmul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  rw [hz x, hz y]

/-- If the outgoing differential in cochain degree zero vanishes, the zero-cocycles are
the whole degree-zero cochain module. -/
noncomputable def CochainComplex.cocyclesZeroEquivOfDZero
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (h : C.d 0 1 = 0) :
    CochainComplex.cocyclesSub C 0 ≃ₗ[R] C.X 0 :=
  (LinearEquiv.ofEq _ _ (by
    rw [CochainComplex.cocyclesSub, h, ModuleCat.hom_zero, LinearMap.ker_zero])).trans
      Submodule.topEquiv

/-- The degree-zero homology of the coefficient change of a complex concentrated in
degree zero is the coefficient change of its only term. -/
noncomputable def CochainComplex.baseChangeSingleZeroHomologyEquiv
    (X : ModuleCat.{u} R) (A : Type u) [CommRing A] [Algebra R A] :
    (((cochainBaseChange A
      ((CochainComplex.single₀ (ModuleCat.{u} R)).obj X)).homology 0 :
        ModuleCat.{u} A) : Type u) ≃ₗ[A] (A ⊗[R] X) :=
  (CochainComplex.homologyZeroEquiv _).trans
    (CochainComplex.cocyclesZeroEquivOfDZero _ (by
      rw [cochainBaseChange_d, HomologicalComplex.single_obj_d]
      apply ModuleCat.hom_ext
      simp))

/-! ## Twisted-free degree pieces -/

/-- A nonnegative degree piece of a finite sum of twists of the polynomial structure
module is finite projective (in fact finite free). -/
theorem finite_projective_free_obj (a : ℤ) (r : ℕ) (d : ℤ) (hd : 0 ≤ d + a) :
    Module.Finite R (((((structureModule R n).twist a).pow r).obj d)) ∧
      Module.Projective R (((((structureModule R n).twist a).pow r).obj d)) := by
  let e : (((((structureModule R n).twist a).pow r).obj d)) ≃ₗ[R]
      (Fin r → MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R (d + a).toNat) := by
    have hpoly : polySubmodule R n (d + a) =
        MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R (d + a).toNat :=
      polySubmodule_of_nonneg (k := R) (n := n) hd
    exact LinearEquiv.piCongrRight fun _ : Fin r => LinearEquiv.ofEq _ _ hpoly
  let b := MvPolynomial.homogeneousSubmoduleFinSumBasis r n R (d + a).toNat
  let b' := b.map e.symm
  exact ⟨Module.Finite.of_basis b', Module.Projective.of_basis b'⟩

/-! ## The universal strictly-perfect replacement -/

/-- In a degree in which the twist is nonnegative, the Cech complex of a twisted-free
graded module has a universal strictly-perfect replacement concentrated in degree zero. -/
noncomputable def strictlyPerfectReplacement_cechComplex_free
    (a : ℤ) (r : ℕ) (d : ℤ) (hd : 0 ≤ d + a) :
    CochainComplex.StrictlyPerfectReplacement
      (((((structureModule R n).twist a).pow r).cechComplex d)) := by
  let F := ((structureModule R n).twist a).pow r
  let D := (CochainComplex.single₀ (ModuleCat.{u} R)).obj (F.obj d)
  have hfree : Module.Finite R (F.obj d) ∧ Module.Projective R (F.obj d) :=
    finite_projective_free_obj a r d hd
  refine
    { complex := D
      bound := 0
      bounded := ?_
      finite := ?_
      projective := ?_
      homologyEquiv := ?_
      baseChangeHomologyEquiv := ?_ }
  · intro p hp
    exact ModuleCat.subsingleton_of_isZero
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 (F.obj d) p (by omega))
  · intro p
    by_cases hp : p = 0
    · subst p
      simpa [D] using hfree.1
    · letI : Subsingleton (D.X p) := ModuleCat.subsingleton_of_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 (F.obj d) p hp)
      letI : Module.FinitePresentation R (D.X p) := inferInstance
      exact inferInstance
  · intro p
    by_cases hp : p = 0
    · subst p
      simpa [D] using hfree.2
    · letI : Subsingleton (D.X p) := ModuleCat.subsingleton_of_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 (F.obj d) p hp)
      haveI : Module.Projective R (Fin 0 → R) := inferInstance
      exact Module.Projective.of_equiv'
        (default : (Fin 0 → R) ≃ₗ[R] (D.X p : Type u))
  · intro i
    rcases i with _ | j
    · exact
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0 (F.obj d)
          ).toLinearEquiv.trans
        (LinearEquiv.ofBijective (F.cechAug d).hom
          (bijective_cechAug_free a r d hd))
    · haveI hD : Subsingleton (D.homology (j + 1)) := by
        rw [CochainComplex.subsingleton_homology_succ_iff]
        apply CochainComplex.exactAtSucc_of_subsingleton_X
        exact ModuleCat.subsingleton_of_isZero
          (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0
            (F.obj d) (j + 1) (by omega))
      haveI hC : Subsingleton ((F.cechComplex d).homology (j + 1)) := by
        exact subsingleton_cechHgr_free a r (j + 1) (by omega) d (by omega)
      exact LinearEquiv.ofSubsingleton _ _
  · intro A _ _ i
    rcases i with _ | j
    · let e := freeBaseChangeIso (R := R) (A := A) (n := n) r a
      exact (CochainComplex.baseChangeSingleZeroHomologyEquiv (F.obj d) A).trans
        ((appIso e d).toLinearEquiv.trans
          ((LinearEquiv.ofBijective
            (((((structureModule A n).twist a).pow r).cechAug d).hom)
            (bijective_cechAug_free a r d hd)).trans
          (((appIso (cechHgrMapIso e 0) d).toLinearEquiv.symm).trans
            (cechHgrBaseChangeHomologyIso_arbitrary F d A 0).toLinearEquiv)))
    · haveI hD : Subsingleton
          ((cochainBaseChange A D).homology (j + 1)) := by
        rw [CochainComplex.subsingleton_homology_succ_iff]
        apply CochainComplex.exactAtSucc_of_subsingleton_X
        change Subsingleton (A ⊗[R] (D.X (j + 1)))
        letI : Subsingleton (D.X (j + 1)) := ModuleCat.subsingleton_of_isZero
          (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0
            (F.obj d) (j + 1) (by omega))
        exact subsingleton_tensor_right
      let e := freeBaseChangeIso (R := R) (A := A) (n := n) r a
      haveI hFA : Subsingleton
          ((((((structureModule A n).twist a).pow r).cechHgr (j + 1)).obj d)) :=
        subsingleton_cechHgr_free a r (j + 1) (by omega) d (by omega)
      haveI hFB : Subsingleton
          (((F.baseChange A).cechComplex d).homology (j + 1)) := by
        change Subsingleton ((((F.baseChange A).cechHgr (j + 1)).obj d))
        exact subsingleton_of_iso (appIso (cechHgrMapIso e (j + 1)) d).symm
      haveI hC : Subsingleton
          ((cochainBaseChange A (F.cechComplex d)).homology (j + 1)) :=
        subsingleton_of_iso
          (cechHgrBaseChangeHomologyIso_arbitrary F d A (j + 1))
      exact LinearEquiv.ofSubsingleton _ _

end AlgebraicGeometry.ProjectiveSpace.GradedModule

end

end
