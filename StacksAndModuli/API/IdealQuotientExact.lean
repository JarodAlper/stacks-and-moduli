module

public import StacksAndModuli.API.IdealQuotientModule
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Flat.Equalizer

/-!
# Exact presentations after quotienting by an ideal

For an ideal `I` of a coefficient ring, this file defines the map induced by a linear map
on the quotients by `I` and proves its compatibility with tensoring by `R ⧸ I`.

Right exactness is automatic.  If `0 → K → F → M → 0` is exact and `M` is flat,
then the induced map `K / IK → F / IF` is injective as well.  Thus the whole short exact
sequence survives on the closed fibre.  This is the relative closed-fibre step used in the
Noetherian proof of openness of the flat locus.

Main declarations:

* `LinearMap.quotientByIdeal`;
* `LinearMap.quotientByIdealOverQuotient`;
* `LinearMap.quotientByIdeal_shortExact_of_flat`.
-/

@[expose] public section

noncomputable section

universe u

open TensorProduct

namespace LinearMap

variable {R K F M : Type u} [CommRing R]
variable [AddCommGroup K] [Module R K]
variable [AddCommGroup F] [Module R F]
variable [AddCommGroup M] [Module R M]

/-- The map on quotients by the action of an ideal induced by a linear map. -/
noncomputable def quotientByIdeal (I : Ideal R) (f : K →ₗ[R] F) :
    (K ⧸ I • (⊤ : Submodule R K)) →ₗ[R]
      (F ⧸ I • (⊤ : Submodule R F)) :=
  (I • (⊤ : Submodule R K)).mapQ (I • (⊤ : Submodule R F)) f
    (Submodule.smul_top_le_comap_smul_top I f)

/-- The map induced on quotients, regarded as linear over the quotient ring. -/
noncomputable def quotientByIdealOverQuotient (I : Ideal R)
    (f : K →ₗ[R] F) :
    letI : SMul (R ⧸ I) (K ⧸ I • (⊤ : Submodule R K)) :=
      Ideal.Quotient.smulModuleQuotient I
    letI : Module (R ⧸ I) (K ⧸ I • (⊤ : Submodule R K)) :=
      Ideal.Quotient.moduleQuotient I
    letI : IsScalarTower R (R ⧸ I)
        (K ⧸ I • (⊤ : Submodule R K)) :=
      Ideal.Quotient.isScalarTower_moduleQuotient I
    letI : SMul (R ⧸ I) (F ⧸ I • (⊤ : Submodule R F)) :=
      Ideal.Quotient.smulModuleQuotient I
    letI : Module (R ⧸ I) (F ⧸ I • (⊤ : Submodule R F)) :=
      Ideal.Quotient.moduleQuotient I
    letI : IsScalarTower R (R ⧸ I)
        (F ⧸ I • (⊤ : Submodule R F)) :=
      Ideal.Quotient.isScalarTower_moduleQuotient I
    (K ⧸ I • (⊤ : Submodule R K)) →ₗ[R ⧸ I]
      (F ⧸ I • (⊤ : Submodule R F)) := by
  letI : SMul (R ⧸ I) (K ⧸ I • (⊤ : Submodule R K)) :=
    Ideal.Quotient.smulModuleQuotient I
  letI : Module (R ⧸ I) (K ⧸ I • (⊤ : Submodule R K)) :=
    Ideal.Quotient.moduleQuotient I
  letI : IsScalarTower R (R ⧸ I)
      (K ⧸ I • (⊤ : Submodule R K)) :=
    Ideal.Quotient.isScalarTower_moduleQuotient I
  letI : SMul (R ⧸ I) (F ⧸ I • (⊤ : Submodule R F)) :=
    Ideal.Quotient.smulModuleQuotient I
  letI : Module (R ⧸ I) (F ⧸ I • (⊤ : Submodule R F)) :=
    Ideal.Quotient.moduleQuotient I
  letI : IsScalarTower R (R ⧸ I)
      (F ⧸ I • (⊤ : Submodule R F)) :=
    Ideal.Quotient.isScalarTower_moduleQuotient I
  exact (quotientByIdeal I f).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective

@[simp]
lemma quotientByIdeal_mk (I : Ideal R) (f : K →ₗ[R] F) (x : K) :
    quotientByIdeal I f (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (f x) :=
  rfl

/-- Passing to quotients by the action of an ideal preserves composition. -/
theorem quotientByIdeal_comp
    {L : Type u} [AddCommGroup L] [Module R L]
    (I : Ideal R) (f : L →ₗ[R] K) (g : K →ₗ[R] F) :
    quotientByIdeal I (g.comp f) =
      (quotientByIdeal I g).comp (quotientByIdeal I f) := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x => rfl

/-- Passing the zero map to quotients by the action of an ideal gives the zero map. -/
@[simp]
theorem quotientByIdeal_zero (I : Ideal R) :
    quotientByIdeal I (0 : K →ₗ[R] F) = 0 := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x => rfl

/-- Tensoring by `R ⧸ I` and quotienting by the action of `I` carry a linear map to the
same map under the canonical equivalences. -/
lemma quotTensorEquivQuotSMul_naturality_quotientByIdeal
    (I : Ideal R) (f : K →ₗ[R] F) :
    (TensorProduct.quotTensorEquivQuotSMul F I).toLinearMap.comp
        (f.lTensor (R ⧸ I)) =
      (quotientByIdeal I f).comp
        (TensorProduct.quotTensorEquivQuotSMul K I).toLinearMap := by
  apply TensorProduct.ext'
  intro r x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective (I := I) r
  simp [quotientByIdeal]

/-- Injectivity after tensoring with `R ⧸ I` is equivalent to injectivity of the
induced map on quotients by the action of `I`. -/
theorem lTensor_injective_iff_quotientByIdeal_injective
    (I : Ideal R) (f : K →ₗ[R] F) :
    Function.Injective (f.lTensor (R ⧸ I)) ↔
      Function.Injective (quotientByIdeal I f) := by
  constructor
  · intro hinj x y hxy
    apply (TensorProduct.quotTensorEquivQuotSMul K I).symm.injective
    apply hinj
    apply (TensorProduct.quotTensorEquivQuotSMul F I).injective
    have hnat :=
      quotTensorEquivQuotSMul_naturality_quotientByIdeal I f
    have hx := LinearMap.congr_fun hnat
      ((TensorProduct.quotTensorEquivQuotSMul K I).symm x)
    have hy := LinearMap.congr_fun hnat
      ((TensorProduct.quotTensorEquivQuotSMul K I).symm y)
    have hx' :
        (TensorProduct.quotTensorEquivQuotSMul F I).toLinearMap
            (f.lTensor (R ⧸ I)
              ((TensorProduct.quotTensorEquivQuotSMul K I).symm x)) =
          quotientByIdeal I f x := by
      simpa only [LinearMap.comp_apply] using
        hx.trans (congrArg (quotientByIdeal I f)
          ((TensorProduct.quotTensorEquivQuotSMul K I).apply_symm_apply x))
    have hy' :
        (TensorProduct.quotTensorEquivQuotSMul F I).toLinearMap
            (f.lTensor (R ⧸ I)
              ((TensorProduct.quotTensorEquivQuotSMul K I).symm y)) =
          quotientByIdeal I f y := by
      simpa only [LinearMap.comp_apply] using
        hy.trans (congrArg (quotientByIdeal I f)
          ((TensorProduct.quotTensorEquivQuotSMul K I).apply_symm_apply y))
    exact hx'.trans (hxy.trans hy'.symm)
  · intro hinj x y hxy
    apply (TensorProduct.quotTensorEquivQuotSMul K I).injective
    apply hinj
    have hnat :=
      quotTensorEquivQuotSMul_naturality_quotientByIdeal I f
    have hx := LinearMap.congr_fun hnat x
    have hy := LinearMap.congr_fun hnat y
    exact hx.symm.trans
      ((congrArg (TensorProduct.quotTensorEquivQuotSMul F I) hxy).trans hy)

/-- Surjectivity is preserved on quotienting the source and target by an ideal. -/
theorem quotientByIdeal_surjective (I : Ideal R) (f : K →ₗ[R] F)
    (hf : Function.Surjective f) :
    Function.Surjective (quotientByIdeal I f) := by
  intro y
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective
    (I • (⊤ : Submodule R F)) y
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨Submodule.Quotient.mk x, rfl⟩

/-- Exactness at the middle term is preserved on quotienting by an ideal. -/
theorem quotientByIdeal_exact (I : Ideal R)
    (i : K →ₗ[R] F) (p : F →ₗ[R] M)
    (hexact : Function.Exact i p) (hp : Function.Surjective p) :
    Function.Exact (quotientByIdeal I i) (quotientByIdeal I p) :=
  (Function.Exact.iff_of_ladder_linearEquiv
    (quotTensorEquivQuotSMul_naturality_quotientByIdeal I i).symm
    (quotTensorEquivQuotSMul_naturality_quotientByIdeal I p).symm).mpr
      (lTensor_exact (R ⧸ I) hexact hp)

/-- If the cokernel in a short exact sequence is flat, the injection remains injective
after quotienting all three modules by an arbitrary ideal. -/
theorem quotientByIdeal_injective_of_exact_of_flat
    (I : Ideal R) (i : K →ₗ[R] F) (p : F →ₗ[R] M)
    (hi : Function.Injective i) (hexact : Function.Exact i p)
    (hp : Function.Surjective p) [Module.Flat R M] :
    Function.Injective (quotientByIdeal I i) := by
  have hinj : Function.Injective (i.lTensor (R ⧸ I)) :=
    LinearMap.lTensor_injective_of_exact_of_flat
      p hp i hi hexact (R ⧸ I)
  intro x y hxy
  apply (TensorProduct.quotTensorEquivQuotSMul K I).symm.injective
  apply hinj
  apply (TensorProduct.quotTensorEquivQuotSMul F I).injective
  have hnat := LinearMap.congr_fun
    (quotTensorEquivQuotSMul_naturality_quotientByIdeal I i)
      ((TensorProduct.quotTensorEquivQuotSMul K I).symm x)
  have hnat' := LinearMap.congr_fun
    (quotTensorEquivQuotSMul_naturality_quotientByIdeal I i)
      ((TensorProduct.quotTensorEquivQuotSMul K I).symm y)
  have hx :
      (TensorProduct.quotTensorEquivQuotSMul F I).toLinearMap
          (i.lTensor (R ⧸ I)
            ((TensorProduct.quotTensorEquivQuotSMul K I).symm x)) =
        quotientByIdeal I i x := by
    simpa only [LinearMap.comp_apply] using
      hnat.trans (congrArg (quotientByIdeal I i)
        ((TensorProduct.quotTensorEquivQuotSMul K I).apply_symm_apply x))
  have hy :
      (TensorProduct.quotTensorEquivQuotSMul F I).toLinearMap
          (i.lTensor (R ⧸ I)
            ((TensorProduct.quotTensorEquivQuotSMul K I).symm y)) =
        quotientByIdeal I i y := by
    simpa only [LinearMap.comp_apply] using
      hnat'.trans (congrArg (quotientByIdeal I i)
        ((TensorProduct.quotTensorEquivQuotSMul K I).apply_symm_apply y))
  exact hx.trans (hxy.trans hy.symm)

/-- A short exact sequence with flat cokernel remains short exact after quotienting by any
ideal of the coefficient ring. -/
theorem quotientByIdeal_shortExact_of_flat
    (I : Ideal R) (i : K →ₗ[R] F) (p : F →ₗ[R] M)
    (hi : Function.Injective i) (hexact : Function.Exact i p)
    (hp : Function.Surjective p) [Module.Flat R M] :
    Function.Injective (quotientByIdeal I i) ∧
      Function.Exact (quotientByIdeal I i) (quotientByIdeal I p) ∧
      Function.Surjective (quotientByIdeal I p) :=
  ⟨quotientByIdeal_injective_of_exact_of_flat I i p hi hexact hp,
    quotientByIdeal_exact I i p hexact hp,
    quotientByIdeal_surjective I p hp⟩

section ScalarTower

variable {S : Type u} [CommRing S] [Algebra R S]
variable [Module S K] [IsScalarTower R S K]
variable [Module S F] [IsScalarTower R S F]
variable [Module S M] [IsScalarTower R S M]

/-- If the cokernel is flat over a coefficient ring, quotienting an `S`-linear injection
by the extension of a coefficient ideal remains injective. -/
theorem quotientByMappedIdeal_injective_of_exact_of_flat
    (I : Ideal R) (i : K →ₗ[S] F) (p : F →ₗ[S] M)
    (hi : Function.Injective i) (hexact : Function.Exact i p)
    (hp : Function.Surjective p) [Module.Flat R M] :
    Function.Injective
      (quotientByIdeal (I.map (algebraMap R S)) i) := by
  let J := I.map (algebraMap R S)
  have hRinj : Function.Injective
      (quotientByIdeal I (i.restrictScalars R)) :=
    quotientByIdeal_injective_of_exact_of_flat I
      (i.restrictScalars R) (p.restrictScalars R) hi hexact hp
  intro x y hxy
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
    (J • (⊤ : Submodule S K)) x
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective
    (J • (⊤ : Submodule S K)) y
  apply (Submodule.Quotient.eq _).mpr
  have himageS : i (x - y) ∈ J • (⊤ : Submodule S F) := by
    rw [map_sub]
    exact (Submodule.Quotient.eq _).mp hxy
  have hJF :
      (J • (⊤ : Submodule S F)).restrictScalars R =
        I • (⊤ : Submodule R F) := by
    simpa [J] using
      Ideal.smul_restrictScalars I (⊤ : Submodule S F)
  have himageR : i (x - y) ∈ I • (⊤ : Submodule R F) := by
    rw [← hJF]
    exact himageS
  have hquotImage :
      quotientByIdeal I (i.restrictScalars R)
          (Submodule.Quotient.mk x) =
        quotientByIdeal I (i.restrictScalars R)
          (Submodule.Quotient.mk y) := by
    apply (Submodule.Quotient.eq _).mpr
    change i x - i y ∈ I • (⊤ : Submodule R F)
    simpa only [map_sub] using himageR
  have hquot := hRinj hquotImage
  have hIK :
      (J • (⊤ : Submodule S K)).restrictScalars R =
        I • (⊤ : Submodule R K) := by
    simpa [J] using
      Ideal.smul_restrictScalars I (⊤ : Submodule S K)
  have hmemR : x - y ∈ I • (⊤ : Submodule R K) :=
    (Submodule.Quotient.eq _).mp hquot
  rw [← hIK] at hmemR
  exact hmemR

/-- Injectivity after quotienting by an extended ideal implies injectivity of the
corresponding restricted-scalar quotient map. -/
theorem quotientByIdeal_restrictScalars_injective_of_mappedIdeal_injective
    (I : Ideal R) (i : K →ₗ[S] F)
    (hinj : Function.Injective
      (quotientByIdeal (I.map (algebraMap R S)) i)) :
    Function.Injective
      (quotientByIdeal I (i.restrictScalars R)) := by
  let J := I.map (algebraMap R S)
  intro x y hxy
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
    (I • (⊤ : Submodule R K)) x
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective
    (I • (⊤ : Submodule R K)) y
  apply (Submodule.Quotient.eq _).mpr
  have himageR : i (x - y) ∈ I • (⊤ : Submodule R F) := by
    rw [map_sub]
    exact (Submodule.Quotient.eq _).mp hxy
  have hJF :
      (J • (⊤ : Submodule S F)).restrictScalars R =
        I • (⊤ : Submodule R F) := by
    simpa [J] using
      Ideal.smul_restrictScalars I (⊤ : Submodule S F)
  have himageS : i (x - y) ∈ J • (⊤ : Submodule S F) := by
    change i (x - y) ∈
      (J • (⊤ : Submodule S F)).restrictScalars R
    rw [hJF]
    exact himageR
  have hquotImage :
      quotientByIdeal J i (Submodule.Quotient.mk x) =
        quotientByIdeal J i (Submodule.Quotient.mk y) := by
    apply (Submodule.Quotient.eq _).mpr
    change i x - i y ∈ J • (⊤ : Submodule S F)
    simpa only [map_sub] using himageS
  have hquot := hinj hquotImage
  have hIK :
      (J • (⊤ : Submodule S K)).restrictScalars R =
        I • (⊤ : Submodule R K) := by
    simpa [J] using
      Ideal.smul_restrictScalars I (⊤ : Submodule S K)
  have hmemS : x - y ∈ J • (⊤ : Submodule S K) :=
    (Submodule.Quotient.eq _).mp hquot
  rw [← hIK]
  exact hmemS

/-- A short exact sequence of `S`-modules with coefficient-flat cokernel remains short
exact after quotienting by the extension of a coefficient ideal. -/
theorem quotientByMappedIdeal_shortExact_of_flat
    (I : Ideal R) (i : K →ₗ[S] F) (p : F →ₗ[S] M)
    (hi : Function.Injective i) (hexact : Function.Exact i p)
    (hp : Function.Surjective p) [Module.Flat R M] :
    let J := I.map (algebraMap R S)
    Function.Injective (quotientByIdeal J i) ∧
      Function.Exact (quotientByIdeal J i) (quotientByIdeal J p) ∧
      Function.Surjective (quotientByIdeal J p) :=
  ⟨quotientByMappedIdeal_injective_of_exact_of_flat
      I i p hi hexact hp,
    quotientByIdeal_exact _ i p hexact hp,
    quotientByIdeal_surjective _ p hp⟩

end ScalarTower

end LinearMap

end

end
