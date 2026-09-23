module

public import StacksAndModuli.API.ProjectiveGradedFreeStrictlyPerfect

/-!
# Strictly perfect replacements of universally exact flat complexes

Supporting API for the arbitrary-base cohomology-and-base-change argument.  A bounded complex
of flat modules which is exact in positive degrees and whose zeroth homology is finite
projective is universally represented by the one-term complex on its zeroth homology.  The
point is that bounded flatness makes positive exactness and zeroth homology commute with every
coefficient change, without any flatness hypothesis on the new coefficient ring.

This construction is the algebraic output needed after descending a projective-space family
to a noetherian coefficient ring: noetherian Serre finiteness proves the hypotheses there, and
the resulting one-term replacement is suitable for subsequent scalar extension.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

namespace AlgebraicGeometry.ProjectiveSpace.CochainComplex

open CategoryTheory TensorProduct

variable {R : Type u} [CommRing R] (C : CochainComplex (ModuleCat.{u} R) ℕ)

/-- Scalar extension of a subsingleton module is a subsingleton. -/
lemma subsingleton_baseChange_of_subsingleton {A : Type u} [CommRing A] [Algebra R A]
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

/-- Iterating coefficient change of a cochain complex agrees with changing coefficients
along the composite ring map. -/
noncomputable def cochainBaseChangeCompIso
    (A B : Type u) [CommRing A] [CommRing B] [Algebra R A] [Algebra A B]
    [Algebra R B] [IsScalarTower R A B] :
    GradedModule.cochainBaseChange B (GradedModule.cochainBaseChange A C) ≅
      GradedModule.cochainBaseChange B C :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p ↦ (TensorProduct.AlgebraTensorModule.cancelBaseChange
      R A B B (C.X p)).toModuleIso)
    (fun p q hpq ↦ by
      obtain rfl : q = p + 1 := hpq.symm
      simp only [GradedModule.cochainBaseChange, CochainComplex.of_d]
      apply ModuleCat.hom_ext
      apply TensorProduct.AlgebraTensorModule.ext
      intro b x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
      | tmul a y => simp [LinearMap.baseChange_tmul])

/-- Coefficient change carries an isomorphism of cochain complexes to an isomorphism. -/
noncomputable def cochainBaseChangeIso {C D : CochainComplex (ModuleCat.{u} R) ℕ}
    (e : C ≅ D) (A : Type u) [CommRing A] [Algebra R A] :
    GradedModule.cochainBaseChange A C ≅ GradedModule.cochainBaseChange A D :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p ↦ ((HomologicalComplex.Hom.isoApp e p).toLinearEquiv.baseChange R A).toModuleIso)
    (fun p q hpq ↦ by
      obtain rfl : q = p + 1 := hpq.symm
      simp only [GradedModule.cochainBaseChange, CochainComplex.of_d]
      apply ModuleCat.hom_ext
      apply TensorProduct.AlgebraTensorModule.ext
      intro a x
      change a ⊗ₜ[R] ((D.d p (p + 1)).hom ((e.hom.f p).hom x)) =
        a ⊗ₜ[R] ((e.hom.f (p + 1)).hom ((C.d p (p + 1)).hom x))
      have h := congrArg ModuleCat.Hom.hom (e.hom.comm p (p + 1))
      simp only [ModuleCat.hom_comp] at h
      exact congrArg (fun y ↦ a ⊗ₜ[R] y) (LinearMap.congr_fun h x))

/-- A bounded flat complex which is exact in positive degrees and has finite-projective
zeroth homology admits a universal strictly perfect replacement concentrated in degree zero.
-/
noncomputable def strictlyPerfectReplacementOfExact
    (hflat : ∀ p : ℕ, Module.Flat R (C.X p))
    {N : ℕ} (hvan : ∀ p : ℕ, N < p → Subsingleton (C.X p))
    (hex : ∀ j : ℕ, ExactAtSucc C j)
    (hfinite : Module.Finite R (C.homology 0))
    (hprojective : Module.Projective R (C.homology 0)) :
    StrictlyPerfectReplacement C := by
  let H := C.homology 0
  let D := (CochainComplex.single₀ (ModuleCat.{u} R)).obj H
  have hfinPositive : ∀ j : ℕ, Module.Finite R (C.homology (j + 1)) := by
    intro j
    haveI : Subsingleton (C.homology (j + 1)) := by
      rw [subsingleton_homology_succ_iff]
      exact hex j
    exact GradedModule.finiteDimensional_of_subsingleton
  have hfpZero : Module.FinitePresentation R (C.homology 0) := by
    letI : Module.Finite R (C.homology 0) := hfinite
    letI : Module.Projective R (C.homology 0) := hprojective
    exact Module.finitePresentation_of_projective R _
  have hbaseChange :=
    finite_projective_homologyZero_and_baseChange_of_finiteHomology
      C hflat hvan hfinPositive hfpZero (fun K _ _ j ↦ by
        have h := range_baseChange_d_eq_ker K hflat hvan
          (fun i _ ↦ hex i) (i := j) le_rfl
        rw [ExactAtSucc, cocyclesSub, cochainBaseChange_d_hom,
          cochainBaseChange_d_hom]
        exact h)
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
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 H p (by omega))
  · intro p
    by_cases hp : p = 0
    · subst p
      simpa [D, H] using hfinite
    · letI : Subsingleton (D.X p) := ModuleCat.subsingleton_of_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 H p hp)
      letI : Module.FinitePresentation R (D.X p) := inferInstance
      exact inferInstance
  · intro p
    by_cases hp : p = 0
    · subst p
      simpa [D, H] using hprojective
    · letI : Subsingleton (D.X p) := ModuleCat.subsingleton_of_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 H p hp)
      haveI : Module.Projective R (Fin 0 → R) := inferInstance
      exact Module.Projective.of_equiv'
        (default : (Fin 0 → R) ≃ₗ[R] (D.X p : Type u))
  · intro i
    rcases i with _ | j
    · exact
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0 H
          ).toLinearEquiv.trans (LinearEquiv.refl R (C.homology 0))
    · haveI hD : Subsingleton (D.homology (j + 1)) := by
        rw [subsingleton_homology_succ_iff]
        apply exactAtSucc_of_subsingleton_X
        exact ModuleCat.subsingleton_of_isZero
          (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 H
            (j + 1) (by omega))
      haveI hC : Subsingleton (C.homology (j + 1)) := by
        rw [subsingleton_homology_succ_iff]
        exact hex j
      exact LinearEquiv.ofSubsingleton _ _
  · intro A _ _ i
    rcases i with _ | j
    · exact (GradedModule.CochainComplex.baseChangeSingleZeroHomologyEquiv H A).trans
        (Classical.choice (hbaseChange.2.2 A))
    · haveI hD : Subsingleton
          ((GradedModule.cochainBaseChange A D).homology (j + 1)) := by
        rw [subsingleton_homology_succ_iff]
        apply exactAtSucc_of_subsingleton_X
        change Subsingleton (A ⊗[R] (D.X (j + 1)))
        letI : Subsingleton (D.X (j + 1)) := ModuleCat.subsingleton_of_isZero
          (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 H
            (j + 1) (by omega))
        exact subsingleton_baseChange_of_subsingleton
      haveI hC : Subsingleton
          ((GradedModule.cochainBaseChange A C).homology (j + 1)) := by
        rw [subsingleton_homology_succ_iff]
        have h := range_baseChange_d_eq_ker A hflat hvan
          (fun i _ ↦ hex i) (i := j) le_rfl
        rw [ExactAtSucc, cocyclesSub, cochainBaseChange_d_hom,
          cochainBaseChange_d_hom]
        exact h
      exact LinearEquiv.ofSubsingleton _ _

namespace StrictlyPerfectReplacement

/-- Transport a universal strictly perfect replacement across an isomorphism of the complex
being represented. -/
noncomputable def ofIso {D : CochainComplex (ModuleCat.{u} R) ℕ}
    (E : StrictlyPerfectReplacement C) (e : C ≅ D) :
    StrictlyPerfectReplacement D where
  complex := E.complex
  bound := E.bound
  bounded := E.bounded
  finite := E.finite
  projective := E.projective
  homologyEquiv i := (E.homologyEquiv i).trans
    ((HomologicalComplex.homologyFunctor
      (ModuleCat.{u} R) (ComplexShape.up ℕ) i).mapIso e).toLinearEquiv
  baseChangeHomologyEquiv A _ _ i := (E.baseChangeHomologyEquiv A i).trans
    ((HomologicalComplex.homologyFunctor
      (ModuleCat.{u} A) (ComplexShape.up ℕ) i).mapIso
        (cochainBaseChangeIso e A)).toLinearEquiv

/-- A universal strictly perfect replacement remains such after arbitrary scalar extension. -/
noncomputable def baseChange (E : StrictlyPerfectReplacement C)
    (A : Type u) [CommRing A] [Algebra R A] :
    StrictlyPerfectReplacement (GradedModule.cochainBaseChange A C) := by
  let D := GradedModule.cochainBaseChange A E.complex
  refine
    { complex := D
      bound := E.bound
      bounded := ?_
      finite := ?_
      projective := ?_
      homologyEquiv := E.baseChangeHomologyEquiv A
      baseChangeHomologyEquiv := ?_ }
  · intro p hp
    change Subsingleton (A ⊗[R] (E.complex.X p))
    letI : Subsingleton (E.complex.X p) := E.bounded p hp
    exact subsingleton_baseChange_of_subsingleton
  · intro p
    change Module.Finite A (A ⊗[R] (E.complex.X p))
    letI : Module.Finite R (E.complex.X p) := E.finite p
    exact inferInstance
  · intro p
    change Module.Projective A (A ⊗[R] (E.complex.X p))
    letI : Module.Projective R (E.complex.X p) := E.projective p
    exact Module.Projective.tensorProduct
  · intro B _ _ i
    letI : Algebra R B := ((algebraMap A B).comp (algebraMap R A)).toAlgebra
    letI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' rfl
    let eD := (HomologicalComplex.homologyFunctor
      (ModuleCat.{u} B) (ComplexShape.up ℕ) i).mapIso
        (cochainBaseChangeCompIso E.complex A B)
    let eC := (HomologicalComplex.homologyFunctor
      (ModuleCat.{u} B) (ComplexShape.up ℕ) i).mapIso
        (cochainBaseChangeCompIso C A B)
    exact eD.toLinearEquiv.trans
      ((E.baseChangeHomologyEquiv B i).trans eC.symm.toLinearEquiv)

end StrictlyPerfectReplacement

end AlgebraicGeometry.ProjectiveSpace.CochainComplex

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}

/-- The Čech complex in a fixed degree transports along an isomorphism of graded modules. -/
noncomputable def cechComplexMapIso {k : Type u} [CommRing k]
    {m : ℕ} {M N : GradedModule k m} (e : M ≅ N) (d : ℤ) :
    M.cechComplex d ≅ N.cechComplex d where
  hom := cechComplexMap e.hom d
  inv := cechComplexMap e.inv d
  hom_inv_id := by rw [← cechComplexMap_comp, e.hom_inv_id, cechComplexMap_id]
  inv_hom_id := by rw [← cechComplexMap_comp, e.inv_hom_id, cechComplexMap_id]

/-- Scalar extension of a graded module along the identity coefficient map recovers the
original graded module. -/
noncomputable def baseChangeSelfIso {k : Type u} [CommRing k]
    {m : ℕ} (M : GradedModule k m) : M.baseChange k ≅ M where
  hom :=
    { app := fun d ↦ ModuleCat.ofHom (TensorProduct.lid k (M.obj d)).toLinearMap
      comm := fun i d ↦ by
        apply ModuleCat.hom_ext
        apply TensorProduct.AlgebraTensorModule.ext
        intro r x
        simp [GradedModule.baseChange, LinearMap.baseChange_tmul] }
  inv :=
    { app := fun d ↦ ModuleCat.ofHom (TensorProduct.lid k (M.obj d)).symm.toLinearMap
      comm := fun i d ↦ by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        change LinearMap.baseChange k (M.mulX i d).hom
          ((TensorProduct.lid k (M.obj d)).symm x) =
            (TensorProduct.lid k (M.obj (d + 1))).symm ((M.mulX i d).hom x)
        rw [TensorProduct.lid_symm_apply, LinearMap.baseChange_tmul,
          TensorProduct.lid_symm_apply] }
  hom_inv_id := by
    apply hom_ext
    intro d
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact (TensorProduct.lid k (M.obj d)).symm_apply_apply
  inv_hom_id := by
    apply hom_ext
    intro d
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact (TensorProduct.lid k (M.obj d)).apply_symm_apply

/-- Over a noetherian coefficient ring, a finitely generated graded module whose fixed-degree
Čech cochains are flat and whose field fibres have no positive cohomology has a universal
strictly perfect Čech replacement in that degree. -/
noncomputable def strictlyPerfectReplacement_cechComplex_of_isFG
    (M : GradedModule R n) (hM : IsFG M) (d : ℤ)
    (hflat : ∀ p : ℕ, Module.Flat R ((M.cechComplex d).X p))
    (hfib : ∀ (K : Type u) [Field K] [Algebra R K] (i : ℕ), 1 ≤ i →
      Subsingleton (((M.baseChange K).cechHgr i).obj d)) :
    CochainComplex.StrictlyPerfectReplacement (M.cechComplex d) := by
  let C := M.cechComplex d
  have hbound : ∀ p : ℕ, n < p → Subsingleton (C.X p) := by
    intro p hp
    have h := isZero_cechCochain M hp d
    rw [ModuleCat.isZero_iff_subsingleton] at h
    exact h
  have hfinHom : ∀ j : ℕ, Module.Finite R (C.homology (j + 1)) := by
    intro j
    exact finiteDimensional_cechHgr_of_isFG M hM (j + 1) d
  have hfibExact : ∀ (K : Type u) [Field K] [Algebra R K] (j : ℕ),
      CochainComplex.ExactAtSucc (cochainBaseChange K C) j := by
    intro K _ _ j
    exact exactAtSucc_cochainBaseChange_of_subsingleton_arbitrary M d K j
      (hfib K (j + 1) (by omega))
  have hex : ∀ j : ℕ, CochainComplex.ExactAtSucc C j := by
    intro j
    exact CochainComplex.exactAtSucc_of_fibrewise C hflat hbound
      (fun i ↦ @CochainComplex.finite_cohomologySucc R _ C i (hfinHom i))
      hfibExact j
  have hfinite : Module.Finite R (C.homology 0) :=
    finiteDimensional_cechHgr_of_isFG M hM 0 d
  have hprojective : Module.Projective R (C.homology 0) :=
    projective_cechHgr_zero' hM hflat hfib
  exact CochainComplex.strictlyPerfectReplacementOfExact C hflat hbound hex
    hfinite hprojective

/-- A noetherian graded model satisfying the flat-cochain and field-fibre vanishing
hypotheses supplies a universal strictly perfect replacement after every coefficient change.
The target is the Čech complex of the base-changed graded module, not merely the coefficient
change of the original complex. -/
noncomputable def strictlyPerfectReplacement_cechComplex_baseChange_of_noetherian
    (M : GradedModule R n) (hM : IsFG M) (d : ℤ)
    (hflat : ∀ p : ℕ, Module.Flat R ((M.cechComplex d).X p))
    (hfib : ∀ (K : Type u) [Field K] [Algebra R K] (i : ℕ), 1 ≤ i →
      Subsingleton (((M.baseChange K).cechHgr i).obj d))
    (A : Type u) [CommRing A] [Algebra R A] :
    CochainComplex.StrictlyPerfectReplacement ((M.baseChange A).cechComplex d) := by
  let E := strictlyPerfectReplacement_cechComplex_of_isFG M hM d hflat hfib
  let EA := CochainComplex.StrictlyPerfectReplacement.baseChange (M.cechComplex d) E A
  exact CochainComplex.StrictlyPerfectReplacement.ofIso
    (GradedModule.cochainBaseChange A (M.cechComplex d)) EA
    (cechComplexBaseChangeIso A M d).symm

/-- A noetherian coefficient model carrying exactly the data needed to descend a fixed-degree
Čech complex.  Existence is the relative flat-spreading/noetherian-approximation input; this
structure deliberately makes no assertion that such a model exists. -/
structure NoetherianCechModel {A : Type u} [CommRing A]
    (M : GradedModule A n) (d : ℤ) where
  coefficientRing : Type u
  [coefficientRingCommRing : CommRing coefficientRing]
  [coefficientRingNoetherian : IsNoetherianRing coefficientRing]
  [coefficientAlgebra : Algebra coefficientRing A]
  model : GradedModule coefficientRing n
  model_isFG : IsFG model
  flatCochain : ∀ p : ℕ,
    Module.Flat coefficientRing ((model.cechComplex d).X p)
  fibreVanishing : ∀ (K : Type u) [Field K] [Algebra coefficientRing K]
    (i : ℕ), 1 ≤ i → Subsingleton (((model.baseChange K).cechHgr i).obj d)
  baseChangeIso : model.baseChange A ≅ M

namespace NoetherianCechModel

variable {A : Type u} [CommRing A] {M : GradedModule A n} {d : ℤ}

/-- Over an already noetherian coefficient ring, the original fixed-degree Čech complex is
its own noetherian model once the three Serre-theoretic hypotheses are supplied. -/
noncomputable def self (M : GradedModule R n) (d : ℤ)
    (hM : IsFG M)
    (hflat : ∀ p : ℕ, Module.Flat R ((M.cechComplex d).X p))
    (hfib : ∀ (K : Type u) [Field K] [Algebra R K] (i : ℕ), 1 ≤ i →
      Subsingleton (((M.baseChange K).cechHgr i).obj d)) :
    NoetherianCechModel M d where
  coefficientRing := R
  coefficientRingCommRing := inferInstance
  coefficientRingNoetherian := inferInstance
  coefficientAlgebra := inferInstance
  model := M
  model_isFG := hM
  flatCochain := hflat
  fibreVanishing := hfib
  baseChangeIso := baseChangeSelfIso M

/-- A noetherian fixed-degree Čech model supplies the universal strictly perfect replacement
over the original arbitrary coefficient ring. -/
noncomputable def strictlyPerfectReplacement (E : NoetherianCechModel M d) :
    CochainComplex.StrictlyPerfectReplacement (M.cechComplex d) := by
  letI : CommRing E.coefficientRing := E.coefficientRingCommRing
  letI : IsNoetherianRing E.coefficientRing := E.coefficientRingNoetherian
  letI : Algebra E.coefficientRing A := E.coefficientAlgebra
  let D := strictlyPerfectReplacement_cechComplex_baseChange_of_noetherian
    E.model E.model_isFG d E.flatCochain E.fibreVanishing A
  exact CochainComplex.StrictlyPerfectReplacement.ofIso
    ((E.model.baseChange A).cechComplex d) D
    (cechComplexMapIso E.baseChangeIso d)

end NoetherianCechModel

end AlgebraicGeometry.ProjectiveSpace.GradedModule

end

end
