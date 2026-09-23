module

public import StacksAndModuli.API.ProjectiveGradedImagePresentation
public import StacksAndModuli.API.ProjectiveGradedTwistedFreeTotal
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Finite presentation of flat graded quotients over a local ring

This file applies the relation-module criterion developed for Stacks Project tag 053C to the
total polynomial module of an StacksAndModuli graded module.  For a degreewise-surjective graded map,
the total relation module is the total module of the degreewise kernel.  Flatness of the target
over a local coefficient ring makes every target piece finite free, so every relation piece is
finite even though the total relation module is not yet known to be finite.

The remaining closed-fibre input is formal: the quotient of a polynomial ring by the extension
of the maximal ideal is isomorphic to a polynomial ring over the residue field and hence is
noetherian.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open DirectSum

universe uR uS uK uL

namespace LinearEquiv.Grading

variable {R : Type uR} {S : Type uS} {K : Type uK} {L : Type uL}
  [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup K] [Module R K] [Module S K] [IsScalarTower R S K]
  [AddCommGroup L] [Module R L] [Module S L] [IsScalarTower R S L]
  {ι : Type*} [DecidableEq ι]

/-- Transport one component of an internal grading along a linear equivalence. -/
def piece (e : K ≃ₗ[S] L) (𝒦 : ι → Submodule R K) (d : ι) : Submodule R L :=
  (𝒦 d).map (e.restrictScalars R).toLinearMap

/-- A grading component is equivalent to its transported component. -/
def pieceEquiv (e : K ≃ₗ[S] L) (𝒦 : ι → Submodule R K) (d : ι) :
    𝒦 d ≃ₗ[R] piece e 𝒦 d where
  toFun x := ⟨e x.1, ⟨x, x.2, rfl⟩⟩
  invFun y := ⟨e.symm y.1, by
    obtain ⟨x, hx, hxy⟩ := y.2
    have : e.symm y.1 = x := by
      rw [← hxy]
      exact e.symm_apply_apply x
    exact this ▸ hx⟩
  left_inv x := by apply Subtype.ext; exact e.symm_apply_apply x.1
  right_inv y := by apply Subtype.ext; exact e.apply_symm_apply y.1
  map_add' x y := by apply Subtype.ext; exact e.map_add x.1 y.1
  map_smul' r x := by apply Subtype.ext; exact (e.restrictScalars R).map_smul r x.1

/-- The linear equivalence which decomposes a module using a grading transported from a linearly
equivalent module. -/
def decompositionEquiv (e : K ≃ₗ[S] L) (𝒦 : ι → Submodule R K)
    [DirectSum.Decomposition 𝒦] :
    L ≃ₗ[R] ⨁ d : ι, piece e 𝒦 d :=
  (e.restrictScalars R).symm ≪≫ₗ DirectSum.decomposeLinearEquiv 𝒦 ≪≫ₗ
    DirectSum.congrLinearEquiv (pieceEquiv e 𝒦)

@[simp]
theorem decompositionEquiv_apply (e : K ≃ₗ[S] L) (𝒦 : ι → Submodule R K)
    [DirectSum.Decomposition 𝒦] (d : ι) (x : 𝒦 d) :
    decompositionEquiv e 𝒦 (e x.1) =
      DirectSum.lof R ι (fun d => piece e 𝒦 d) d (pieceEquiv e 𝒦 d x) := by
  simp only [decompositionEquiv, LinearEquiv.trans_apply]
  have he : (e.restrictScalars R).symm (e x.1) = x.1 := e.symm_apply_apply x.1
  rw [he, DirectSum.decomposeLinearEquiv_apply_coe]
  exact DirectSum.lmap_lof (fun d => (pieceEquiv e 𝒦 d).toLinearMap) d x

/-- A grading transports along a linear equivalence. -/
@[instance_reducible]
noncomputable def decomposition (e : K ≃ₗ[S] L) (𝒦 : ι → Submodule R K)
    [DirectSum.Decomposition 𝒦] : DirectSum.Decomposition (piece e 𝒦) := by
  classical
  refine DirectSum.Decomposition.ofLinearMap (piece e 𝒦)
    (decompositionEquiv e 𝒦).toLinearMap ?_ ?_
  · apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← DirectSum.sum_support_decompose 𝒦 x]
    simp only [map_sum, LinearMap.comp_apply, LinearMap.id_apply]
    apply Finset.sum_congr rfl
    intro d hd
    change DirectSum.coeLinearMap (piece e 𝒦)
      (decompositionEquiv e 𝒦 (e (DirectSum.decompose 𝒦 x d : K))) =
        e (DirectSum.decompose 𝒦 x d : K)
    rw [decompositionEquiv_apply, DirectSum.coeLinearMap_lof]
    rfl
  · apply DirectSum.linearMap_ext R
    intro d
    apply LinearMap.ext
    intro y
    obtain ⟨x, hx, hxy⟩ := y.2
    let x' : 𝒦 d := ⟨x, hx⟩
    have hy : y = pieceEquiv e 𝒦 d x' := by
      apply Subtype.ext
      exact hxy.symm
    rw [hy]
    simp only [LinearMap.comp_apply, LinearMap.id_apply, DirectSum.coeLinearMap_lof]
    change decompositionEquiv e 𝒦 (e x'.1) =
      DirectSum.lof R ι (fun i => piece e 𝒦 i) d (pieceEquiv e 𝒦 d x')
    rw [decompositionEquiv_apply]

variable {ιA : Type*} [DecidableEq ιA] [AddMonoid ιA] [AddAction ιA ι]

/-- A graded scalar action transports along a linear equivalence over the scalar ring. -/
theorem gradedSMul (𝒜 : ιA → Submodule R S) [GradedRing 𝒜]
    (e : K ≃ₗ[S] L) (𝒦 : ι → Submodule R K)
    [DirectSum.Decomposition 𝒦] [SetLike.GradedSMul 𝒜 𝒦] :
    SetLike.GradedSMul 𝒜 (piece e 𝒦) where
  smul_mem := by
    intro a d p y hp hy
    obtain ⟨x, hx, hxy⟩ := hy
    refine ⟨(p : S) • x, SetLike.GradedSMul.smul_mem hp hx, ?_⟩
    change e ((p : S) • x) = (p : S) • y
    rw [e.map_smul]
    exact congrArg ((p : S) • ·) hxy

end LinearEquiv.Grading

universe u

variable {R : Type u} [CommRing R]

/-- The kernel of a surjection from a finite module to a projective module is finite. -/
theorem Module.Finite.ker_of_surjective_of_projective
    {A B : Type*} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [Module.Finite R A] [Module.Projective R B]
    (f : A →ₗ[R] B) (hf : Function.Surjective f) :
    Module.Finite R f.ker := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property
    f (LinearMap.id : B →ₗ[R] B) hf
  let p : A →ₗ[R] f.ker :=
    LinearMap.codRestrict f.ker (LinearMap.id - s.comp f) fun x => by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, map_sub,
        LinearMap.comp_apply]
      have hsx := DFunLike.congr_fun hs (f x)
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using sub_eq_zero.mpr hsx.symm
  apply Module.Finite.of_surjective p
  intro x
  refine ⟨x.1, Subtype.ext ?_⟩
  change x.1 - s (f x.1) = x.1
  rw [LinearMap.mem_ker.mp x.2, map_zero, sub_zero]

namespace MvPolynomial

/-- The closed fibre of a polynomial ring over a local ring is a polynomial ring over the
residue field. -/
noncomputable def closedFiberEquiv
    {σ : Type*} (R : Type u) [CommRing R] [IsLocalRing R] :
    MvPolynomial σ R ⧸ (IsLocalRing.maximalIdeal R).map
      (algebraMap R (MvPolynomial σ R)) ≃+*
      MvPolynomial σ (R ⧸ IsLocalRing.maximalIdeal R) :=
  (Algebra.TensorProduct.quotIdealMapEquivQuotTensor
      (MvPolynomial σ R) (IsLocalRing.maximalIdeal R)).toRingEquiv.trans
    (MvPolynomial.algebraTensorAlgEquiv R
      (R ⧸ IsLocalRing.maximalIdeal R)).toRingEquiv

/-- The closed fibre of a finite-variable polynomial ring over a local ring is noetherian. -/
theorem isNoetherianRing_closedFiber
    {σ : Type*} [Finite σ] [IsLocalRing R] :
    IsNoetherianRing
      (MvPolynomial σ R ⧸ (IsLocalRing.maximalIdeal R).map
        (algebraMap R (MvPolynomial σ R))) := by
  letI : Field (R ⧸ IsLocalRing.maximalIdeal R) := by
    change Field (IsLocalRing.ResidueField R)
    infer_instance
  letI : IsNoetherianRing (R ⧸ IsLocalRing.maximalIdeal R) :=
    (isNoetherianRing_iff_ideal_fg _).mpr fun I => by
      rcases I.eq_bot_or_top with rfl | rfl
      · exact Submodule.fg_bot
      · exact Ideal.fg_top _
  exact isNoetherianRing_of_ringEquiv
    (MvPolynomial σ (R ⧸ IsLocalRing.maximalIdeal R))
    (closedFiberEquiv R).symm

end MvPolynomial

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule.Total

open CategoryTheory MvPolynomial

variable {n : ℕ}

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A degreewise-surjective map from a finitely generated graded source to a finitely generated,
degreewise-flat target induces a finite presentation on total polynomial modules, provided the
source total module is finitely presented. -/
theorem finitePresentation_of_surjective_of_isFG_of_isFlat
    [IsLocalRing R] {F M : GradedModule R n}
    (hF : IsFG F) (hM : IsFG M) (hMflat : IsFlat M)
    (f : F ⟶ M) (hf : ∀ d : ℤ, Function.Surjective ((f.app d).hom))
    [Module.FinitePresentation (MvPolynomial (Fin (n + 1)) R) (Total F)] :
    Module.FinitePresentation (MvPolynomial (Fin (n + 1)) R) (Total M) := by
  let S := MvPolynomial (Fin (n + 1)) R
  let ft : Total F →ₗ[S] Total M := map f
  let e : Total (ker f) ≃ₗ[S] LinearMap.ker ft := kernelLinearEquiv f
  let 𝒦 : ℤ → Submodule R (LinearMap.ker ft) :=
    LinearEquiv.Grading.piece e (degreePiece (ker f))
  letI : DirectSum.Decomposition 𝒦 :=
    LinearEquiv.Grading.decomposition e (degreePiece (ker f))
  letI : SetLike.GradedSMul
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) 𝒦 :=
    LinearEquiv.Grading.gradedSMul
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      e (degreePiece (ker f))
  have hfinite (d : ℤ) : Module.Finite R (𝒦 d) := by
    letI : Module.Finite R (F.obj d) := hF.1 d
    letI : Module.Finite R (M.obj d) := hM.1 d
    letI : Module.Flat R (M.obj d) := hMflat d
    letI : Module.Free R (M.obj d) := Module.free_of_flat_of_isLocalRing
    letI : Module.Projective R (M.obj d) := inferInstance
    letI : Module.Finite R (LinearMap.ker (f.app d).hom) :=
      Module.Finite.ker_of_surjective_of_projective (f.app d).hom (hf d)
    let hkerFinite : Module.Finite R ((ker f).obj d) := by
      change Module.Finite R (LinearMap.ker (f.app d).hom)
      infer_instance
    letI : Module.Finite R ((ker f).obj d) := hkerFinite
    letI : Module.Finite R (degreePiece (ker f) d) :=
      Module.Finite.equiv (pieceLinearEquiv (ker f) d)
    exact Module.Finite.equiv
      (LinearEquiv.Grading.pieceEquiv e (degreePiece (ker f)) d)
  letI : Module.Flat R (Total M) := hMflat.flat_total
  letI : IsNoetherianRing
      (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) :=
    MvPolynomial.isNoetherianRing_closedFiber
  exact Module.finitePresentation_of_flat_of_noetherian_closedFiber
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    ft (surjective_map_of_surjective f hf) 𝒦 hfinite

/-- Over a local coefficient ring, the image of the standard eventual free presentation of a
degreewise-flat graded module has finitely presented total polynomial module. -/
theorem finitePresentation_imgMod_of_isFlat_of_isLocalRing
    [IsLocalRing R] {r : ℕ} {M : GradedModule R n} (hMflat : IsFlat M)
    (d₀ : ℤ) (y : Fin r → M.obj d₀)
    (hy : Submodule.span R (Set.range y) = ⊤)
    (hgen : ∀ d : ℤ, d₀ ≤ d → M.mulSpan d (d + 1) = ⊤) :
    Module.FinitePresentation (MvPolynomial (Fin (n + 1)) R)
      (Total (imgMod M d₀ y)) := by
  letI : Module.FinitePresentation (MvPolynomial (Fin (n + 1)) R)
      (Total (((structureModule R n).twist (-d₀)).pow r)) :=
    finitePresentation_shiftedFree R n r d₀
  exact finitePresentation_of_surjective_of_isFG_of_isFlat
    ((isFG_structureModule.twist (-d₀)).pow r)
    (isFG_imgMod M d₀ y)
    (hMflat.freeGenImage d₀ y hy hgen)
    (freeGenToImg M d₀ y)
    (surjective_freeGenToImg M d₀ y)

end AlgebraicGeometry.ProjectiveSpace.GradedModule.Total

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

open MvPolynomial

variable {n : ℕ}

/-- Over a local coefficient ring, the relation module of the standard eventual free
presentation of a finitely generated degreewise-flat graded module is finitely generated. -/
theorem isFG_kernel_freeGenHom_of_isFlat_of_isLocalRing
    [IsLocalRing R] {r : ℕ} {M : GradedModule R n} (hMflat : IsFlat M)
    (d₀ : ℤ) (y : Fin r → M.obj d₀)
    (hy : Submodule.span R (Set.range y) = ⊤)
    (hgen : ∀ d : ℤ, d₀ ≤ d → M.mulSpan d (d + 1) = ⊤) :
    IsFG (ker (freeGenHom M d₀ y)) := by
  letI : Module.FinitePresentation (MvPolynomial (Fin (n + 1)) R)
      (Total (imgMod M d₀ y)) :=
    Total.finitePresentation_imgMod_of_isFlat_of_isLocalRing
      hMflat d₀ y hy hgen
  exact isFG_kernel_freeGenHom_of_finitePresentation_image M d₀ y

end AlgebraicGeometry.ProjectiveSpace.GradedModule

end
