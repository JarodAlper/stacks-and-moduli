module

public import StacksAndModuli.API.ProjectiveGradedFlatComplex
public import StacksAndModuli.API.ProjectiveGradedCechBaseChange

/-!
# Canonical base change on zeroth graded Čech cohomology

Supporting API with no Stacks Project counterpart.  Scalar extension carries
cocycles canonically to cocycles even when it does not preserve kernels.  In
degree zero, where cohomology is canonically the cocycles, this gives an
unconditional base-change morphism

`A ⊗[R] H⁰(M(d)) → H⁰((M ⊗[R] A)(d))`.

The construction is natural in the cochain complex.  Applied degreewise to the
projective Čech complexes, it is compatible with multiplication by every
homogeneous coordinate and therefore assembles into a graded-module morphism.

Main declarations:
- `CochainComplex.homologyZeroBaseChangeHom`;
- `GradedModule.cechHgrZeroCanonicalBaseChangeHom`;
- `GradedModule.cechHgrZeroCanonicalBaseChangeMap`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.ProjectiveSpace.CochainComplex

open CategoryTheory TensorProduct

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- The canonical map from scalar-extended cocycles to the cocycles of the
scalar-extended complex. -/
noncomputable def cocyclesBaseChangeHom
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (i : ℕ) :
    (A ⊗[R] cocyclesSub C i) →ₗ[A]
      cocyclesSub (GradedModule.cochainBaseChange A C) i :=
  (LinearMap.baseChange A (cocyclesSub C i).subtype).codRestrict _ (by
    intro x
    rw [cocyclesSub_cochainBaseChange, LinearMap.mem_ker]
    change (LinearMap.baseChange A (C.d i (i + 1)).hom)
      ((LinearMap.baseChange A (cocyclesSub C i).subtype) x) = 0
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
    have hz : (C.d i (i + 1)).hom.comp (cocyclesSub C i).subtype = 0 := by
      apply LinearMap.ext
      intro z
      exact LinearMap.mem_ker.mp z.2
    rw [hz, LinearMap.baseChange_zero]
    rfl)

@[simp] lemma cocyclesBaseChangeHom_val
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (i : ℕ)
    (x : A ⊗[R] cocyclesSub C i) :
    ((cocyclesBaseChangeHom (A := A) C i x :
        cocyclesSub (GradedModule.cochainBaseChange A C) i) :
      (GradedModule.cochainBaseChange A C).X i) =
      LinearMap.baseChange A (cocyclesSub C i).subtype x := rfl

/-- If the differential leaving a degree is surjective, right exactness of tensor
product makes the canonical map onto the cocycles after arbitrary coefficient change. -/
theorem cocyclesBaseChangeHom_surjective_of_surjective
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (i : ℕ)
    (hsurj : Function.Surjective (C.d i (i + 1)).hom) :
    Function.Surjective (cocyclesBaseChangeHom (A := A) C i) := by
  intro z
  have hz : (LinearMap.baseChange A (C.d i (i + 1)).hom) (z :
      (GradedModule.cochainBaseChange A C).X i) = 0 := by
    rw [← LinearMap.mem_ker]
    simpa only [cocyclesSub_cochainBaseChange] using z.2
  have hex := lTensor_exact A
    (LinearMap.exact_subtype_ker_map (C.d i (i + 1)).hom) hsurj
  obtain ⟨x, hx⟩ := (hex (z :
    (GradedModule.cochainBaseChange A C).X i)).mp hz
  refine ⟨x, Subtype.ext ?_⟩
  exact hx

/-- The canonical map on zeroth homology under arbitrary coefficient change. -/
noncomputable def homologyZeroBaseChangeHom
    (C : CochainComplex (ModuleCat.{u} R) ℕ) :
    (A ⊗[R] (C.homology 0 : ModuleCat.{u} R)) →ₗ[A]
      ((GradedModule.cochainBaseChange A C).homology 0 : ModuleCat.{u} A) :=
  (homologyZeroEquiv
      (GradedModule.cochainBaseChange A C)).symm.toLinearMap.comp
    ((cocyclesBaseChangeHom (A := A) C 0).comp
      ((homologyZeroEquiv C).toLinearMap.baseChange A))

/-- Surjectivity of the first differential makes the canonical zeroth-homology
coefficient-change map surjective. -/
theorem homologyZeroBaseChangeHom_surjective_of_surjective
    (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (hsurj : Function.Surjective (C.d 0 1).hom) :
    Function.Surjective (homologyZeroBaseChangeHom (A := A) C) := by
  let eSource := LinearEquiv.baseChange R A _ _ (homologyZeroEquiv C)
  let eTarget := homologyZeroEquiv (GradedModule.cochainBaseChange A C)
  have hcyc := cocyclesBaseChangeHom_surjective_of_surjective
    (A := A) C 0 hsurj
  have hsource : Function.Surjective
      (LinearMap.baseChange A (homologyZeroEquiv C).toLinearMap) := by
    change Function.Surjective eSource.toLinearMap
    exact eSource.surjective
  intro z
  obtain ⟨y, hy⟩ := hcyc (eTarget z)
  obtain ⟨x, hx⟩ := hsource y
  refine ⟨x, eTarget.injective ?_⟩
  change eTarget (eTarget.symm
      (cocyclesBaseChangeHom (A := A) C 0
        ((LinearMap.baseChange A (homologyZeroEquiv C).toLinearMap) x))) =
    eTarget z
  rw [eTarget.apply_symm_apply, hx, hy]

/-- The canonical zeroth-homology coefficient-change map is natural in the complex. -/
lemma homologyZeroBaseChangeHom_naturality
    {C D : CochainComplex (ModuleCat.{u} R) ℕ} (f : C ⟶ D) :
    (homologyZeroBaseChangeHom (A := A) D).comp
        (LinearMap.baseChange A (HomologicalComplex.homologyMap f 0).hom) =
      (HomologicalComplex.homologyMap
          (GradedModule.cochainBaseChangeMap A f) 0).hom.comp
        (homologyZeroBaseChangeHom (A := A) C) := by
  apply LinearMap.ext
  intro x
  let eC := homologyZeroEquiv (GradedModule.cochainBaseChange A C)
  let eD := homologyZeroEquiv (GradedModule.cochainBaseChange A D)
  let zC := cocyclesBaseChangeHom (A := A) C 0
    ((LinearMap.baseChange A (homologyZeroEquiv C).toLinearMap) x)
  let zD := cocyclesBaseChangeHom (A := A) D 0
    ((LinearMap.baseChange A (homologyZeroEquiv D).toLinearMap)
      ((LinearMap.baseChange A (HomologicalComplex.homologyMap f 0).hom) x))
  apply eD.injective
  have hleft : eD
      ((homologyZeroBaseChangeHom (A := A) D)
        ((LinearMap.baseChange A (HomologicalComplex.homologyMap f 0).hom) x)) = zD := by
    exact eD.apply_symm_apply zD
  have hright : eD
      ((HomologicalComplex.homologyMap
          (GradedModule.cochainBaseChangeMap A f) 0).hom
        (homologyZeroBaseChangeHom (A := A) C x)) =
      cocyclesMap (GradedModule.cochainBaseChangeMap A f) 0 zC := by
    rw [homologyZeroEquiv_naturality]
    exact congrArg (cocyclesMap (GradedModule.cochainBaseChangeMap A f) 0)
      (eC.apply_symm_apply zC)
  simp only [LinearMap.comp_apply]
  rw [hleft, hright]
  dsimp only [zD, zC]
  have hnat :
      (homologyZeroEquiv D).toLinearMap.comp
          (HomologicalComplex.homologyMap f 0).hom =
        (cocyclesMap f 0).comp (homologyZeroEquiv C).toLinearMap := by
    apply LinearMap.ext
    intro y
    exact homologyZeroEquiv_naturality f y
  have hinner :
      (LinearMap.baseChange A (homologyZeroEquiv D).toLinearMap)
          ((LinearMap.baseChange A
            (HomologicalComplex.homologyMap f 0).hom) x) =
        (LinearMap.baseChange A (cocyclesMap f 0))
          ((LinearMap.baseChange A
            (homologyZeroEquiv C).toLinearMap) x) := by
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hnat,
      LinearMap.baseChange_comp, LinearMap.comp_apply]
  rw [hinner]
  apply Subtype.ext
  change LinearMap.baseChange A (cocyclesSub D 0).subtype
      ((LinearMap.baseChange A (cocyclesMap f 0))
        ((LinearMap.baseChange A (homologyZeroEquiv C).toLinearMap) x)) =
    (LinearMap.baseChange A (f.f 0).hom)
      ((LinearMap.baseChange A (cocyclesSub C 0).subtype)
        ((LinearMap.baseChange A (homologyZeroEquiv C).toLinearMap) x))
  have key : (LinearMap.baseChange A (cocyclesSub D 0).subtype) ∘ₗ
        (LinearMap.baseChange A (cocyclesMap f 0)) =
      (LinearMap.baseChange A (f.f 0).hom) ∘ₗ
        (LinearMap.baseChange A (cocyclesSub C 0).subtype) := by
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
    rfl
  exact LinearMap.congr_fun key _

end AlgebraicGeometry.ProjectiveSpace.CochainComplex

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

open CategoryTheory TensorProduct
open AlgebraicGeometry.ProjectiveSpace.CochainComplex

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable {n : ℕ}

/-- The canonical map from scalar extension of zeroth graded Čech cohomology to
zeroth graded Čech cohomology after scalar extension. -/
noncomputable def cechHgrZeroCanonicalBaseChangeHom
    (M : GradedModule R n) (d : ℤ) :
    (A ⊗[R] ((M.cechHgr 0).obj d)) →ₗ[A]
      (((M.baseChange A).cechHgr 0).obj d) :=
  ((HomologicalComplex.homologyFunctor
      (ModuleCat.{u} A) (ComplexShape.up ℕ) 0).mapIso
      (cechComplexBaseChangeIso A M d)).inv.hom.comp
    (homologyZeroBaseChangeHom (A := A) (M.cechComplex d))

/-- On the projective line, vanishing of first Čech cohomology makes the
degree-zero Čech differential surjective. -/
theorem cechD_zero_surjective_of_subsingleton_cechHgr_one
    (M : GradedModule R 1) (d : ℤ)
    [Subsingleton ((M.cechHgr 1).obj d)] :
    Function.Surjective ((M.cechComplex d).d 0 1).hom := by
  have hex : CochainComplex.ExactAtSucc (M.cechComplex d) 0 := by
    rw [← CochainComplex.subsingleton_homology_succ_iff]
    change Subsingleton ((M.cechHgr 1).obj d)
    infer_instance
  intro y
  haveI htwo : Subsingleton ((M.cechComplex d).X 2) := by
    have h := isZero_cechCochain M (show 1 < 2 by omega) d
    rw [ModuleCat.isZero_iff_subsingleton] at h
    exact h
  have hy : y ∈ CochainComplex.cocyclesSub (M.cechComplex d) 1 := by
    rw [CochainComplex.cocyclesSub, LinearMap.mem_ker]
    exact Subsingleton.elim _ _
  obtain ⟨x, hx⟩ : y ∈ LinearMap.range ((M.cechComplex d).d 0 1).hom :=
    hex ▸ hy
  exact ⟨x, hx⟩

/-- For a projective-line graded module with vanishing first Čech cohomology,
the canonical Čech `H⁰` comparison is surjective after every coefficient change. -/
theorem cechHgrZeroCanonicalBaseChangeHom_surjective_of_subsingleton_one
    (M : GradedModule R 1) (d : ℤ)
    [Subsingleton ((M.cechHgr 1).obj d)] :
    Function.Surjective
      (cechHgrZeroCanonicalBaseChangeHom (A := A) M d) := by
  have hinv : Function.Surjective
      ((HomologicalComplex.homologyFunctor
      (ModuleCat.{u} A) (ComplexShape.up ℕ) 0).mapIso
      (cechComplexBaseChangeIso A M d)).inv.hom :=
    ConcreteCategory.bijective_of_isIso _ |>.2
  have hzero := homologyZeroBaseChangeHom_surjective_of_surjective
    (A := A) (M.cechComplex d)
      (cechD_zero_surjective_of_subsingleton_cechHgr_one M d)
  intro z
  obtain ⟨y, hy⟩ := hinv z
  obtain ⟨x, hx⟩ := hzero y
  refine ⟨x, ?_⟩
  change ((HomologicalComplex.homologyFunctor
    (ModuleCat.{u} A) (ComplexShape.up ℕ) 0).mapIso
      (cechComplexBaseChangeIso A M d)).inv.hom
        (homologyZeroBaseChangeHom (A := A) (M.cechComplex d) x) = z
  rw [hx, hy]

/-- The canonical Čech-H-zero coefficient-change maps commute with multiplication
by every homogeneous coordinate. -/
lemma cechHgrZeroCanonicalBaseChangeHom_mulX
    (M : GradedModule R n) (j : Fin (n + 1)) (d : ℤ) :
    (cechHgrZeroCanonicalBaseChangeHom (A := A) M (d + 1)).comp
        (LinearMap.baseChange A (((M.cechHgr 0).mulX j d).hom)) =
      ((((M.baseChange A).cechHgr 0).mulX j d).hom).comp
        (cechHgrZeroCanonicalBaseChangeHom (A := A) M d) := by
  apply LinearMap.ext
  intro x
  let e0 := (HomologicalComplex.homologyFunctor
    (ModuleCat.{u} A) (ComplexShape.up ℕ) 0).mapIso
      (cechComplexBaseChangeIso A M d)
  let e1 := (HomologicalComplex.homologyFunctor
    (ModuleCat.{u} A) (ComplexShape.up ℕ) 0).mapIso
      (cechComplexBaseChangeIso A M (d + 1))
  change e1.inv.hom
      (homologyZeroBaseChangeHom (A := A) (M.cechComplex (d + 1))
        ((LinearMap.baseChange A
          (HomologicalComplex.homologyMap (M.cechMulX j d) 0).hom) x)) =
    (HomologicalComplex.homologyMap ((M.baseChange A).cechMulX j d) 0).hom
      (e0.inv.hom
        (homologyZeroBaseChangeHom (A := A) (M.cechComplex d) x))
  have hnat := homologyZeroBaseChangeHom_naturality
    (A := A) (M.cechMulX j d)
  have hx := LinearMap.congr_fun hnat x
  simp only [LinearMap.comp_apply] at hx
  have hcech := congrArg
    (fun f ↦ HomologicalComplex.homologyMap f 0)
      (cechMulX_cechComplexBaseChangeIso A M j d)
  simp only [HomologicalComplex.homologyMap_comp] at hcech
  have hcech' :
      HomologicalComplex.homologyMap
          ((M.baseChange A).cechMulX j d) 0 ≫ e1.hom =
        e0.hom ≫ HomologicalComplex.homologyMap
          (GradedModule.cochainBaseChangeMap A (M.cechMulX j d)) 0 := by
    simpa only [e0, e1, Functor.mapIso_hom,
      HomologicalComplex.homologyFunctor_map] using hcech
  have step4 : ∀ u : (GradedModule.cochainBaseChange A
      (M.cechComplex d)).homology 0,
      e1.inv.hom
          ((HomologicalComplex.homologyMap
            (GradedModule.cochainBaseChangeMap A (M.cechMulX j d)) 0).hom u) =
        (HomologicalComplex.homologyMap
          ((M.baseChange A).cechMulX j d) 0).hom (e0.inv.hom u) := by
    intro u
    have h := congrArg (fun t ↦ e0.inv ≫ t ≫ e1.inv) hcech'
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.inv_hom_id_assoc] at h
    have h' := congrArg ModuleCat.Hom.hom h
    simp only [ModuleCat.hom_comp] at h'
    exact (LinearMap.congr_fun h' u).symm
  exact hx ▸ step4
    (homologyZeroBaseChangeHom (A := A) (M.cechComplex d) x)

/-- The preceding degreewise comparisons assemble into a graded morphism. -/
noncomputable def cechHgrZeroCanonicalBaseChangeMap
    (M : GradedModule R n) :
    (M.cechHgr 0).baseChange A ⟶ (M.baseChange A).cechHgr 0 where
  app d := ModuleCat.ofHom (cechHgrZeroCanonicalBaseChangeHom (A := A) M d)
  comm j d := by
    refine ModuleCat.hom_ext ?_
    exact (cechHgrZeroCanonicalBaseChangeHom_mulX
      (A := A) M j d).symm

end AlgebraicGeometry.ProjectiveSpace.GradedModule
