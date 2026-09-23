module

public import Mathlib.RingTheory.Extension.Presentation.Core
public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Spreading out a flat finitely presented algebra

Stacks Project, Algebra, Lemma **02JO**
(`algebra-lemma-flat-finite-presentation-limit-flat`).

The finite-presentation part of the spreading-out construction is already available through
Mathlib's presentation API: after adjoining the finitely many coefficients of a presentation,
the original algebra is obtained by base change from a finitely presented algebra.  The theorem
below records that layer in the relative form needed for 02JO.

The remaining part of 02JO is to enlarge the coefficient algebra so that the model is flat.  The
exact finite-stage assertion is isolated below as `HasFlatIntegerModel`.  This file proves its
finite-presentation and finite-idempotent layers, including the complete finite-module case:
`Module.FinitePresentation.exists_fg_flat_baseChange` spreads out flatness for a fixed finitely
presented module.  The unresolved general case is relative: the module in 02JO is finitely
presented over a finitely presented algebra, but need not be finitely presented over the base.
-/

@[expose] public section

open TensorProduct

universe u v w

namespace Matrix

/-- The image of an idempotent endomorphism of a finite free module is projective. -/
theorem projective_range_toLin_of_idempotent {R : Type u} [CommRing R]
    {n : Type v} [Fintype n] [DecidableEq n] (P : Matrix n n R) (hP : P * P = P) :
    Module.Projective R (LinearMap.range (Matrix.toLin' P)) := by
  let e : (n → R) →ₗ[R] (n → R) := Matrix.toLin' P
  have he : e.comp e = e := by
    rw [← Matrix.toLin'_mul, hP]
  refine Module.Projective.of_split (LinearMap.range e).subtype e.rangeRestrict ?_
  apply LinearMap.ext
  rintro ⟨x, y, rfl⟩
  apply Subtype.ext
  exact LinearMap.congr_fun he y

/-- A finite idempotent matrix over an algebra is already defined over a finitely generated
subalgebra.  This is the finite-matrix part of spreading out a finite projective module. -/
theorem exists_fg_subalgebra_of_idempotent {R : Type u} {A : Type v} [CommRing R]
    [CommRing A] [Algebra R A] {n : Type w} [Fintype n]
    (P : Matrix n n A) (hP : P * P = P) :
    ∃ (A₀ : Subalgebra R A), A₀.FG ∧ ∃ Q : Matrix n n A₀,
      Q.map (algebraMap A₀ A) = P ∧ Q * Q = Q := by
  let c : n × n → A := fun ij ↦ P ij.1 ij.2
  let A₀ : Subalgebra R A := Algebra.adjoin R (Set.range c)
  let Q : Matrix n n A₀ := fun i j ↦
    ⟨P i j, Algebra.subset_adjoin ⟨(i, j), rfl⟩⟩
  have hQ : Q.map (algebraMap A₀ A) = P := by
    ext i j
    rfl
  refine ⟨A₀, Subalgebra.fg_def.mpr ⟨Set.range c, Set.finite_range c, rfl⟩, Q, hQ, ?_⟩
  apply Matrix.map_injective (f := algebraMap A₀ A) Subtype.val_injective
  change (Q * Q).map (algebraMap A₀ A) = Q.map (algebraMap A₀ A)
  rw [Matrix.map_mul, hQ, hP]

/-- Extending scalars in a matrix and in its associated endomorphism gives the same map under
the canonical identification of a base-changed finite free module with a finite free module. -/
theorem piScalarRight_toLin_map {R : Type u} {A : Type v} [CommRing R]
    [CommRing A] [Algebra R A] {m n : Type w} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (Q : Matrix m n R) :
    (TensorProduct.piScalarRight R A A m).toLinearMap.comp
        ((Matrix.toLin' Q).baseChange A) =
      (Matrix.toLin' (Q.map (algebraMap R A))).comp
        (TensorProduct.piScalarRight R A A n).toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a x
  funext i
  simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, Matrix.toLin'_apply]
  change (TensorProduct.piScalarRightHom R A A m (a ⊗ₜ[R] (Q *ᵥ x))) i =
    (Q.map (algebraMap R A) *ᵥ
      TensorProduct.piScalarRightHom R A A n (a ⊗ₜ[R] x)) i
  rw [TensorProduct.piScalarRightHom_tmul, TensorProduct.piScalarRightHom_tmul]
  simp only [Algebra.smul_def, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum,
    map_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_assoc]

end Matrix

namespace LinearMap

/-- Arbitrary scalar extension commutes with taking the range of a linear map, where scalar
extension of a submodule means the range of its base-changed inclusion. -/
theorem range_baseChange {R : Type u} {A : Type v} [CommRing R]
    [CommRing A] [Algebra R A] {M N : Type w} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) :
    (LinearMap.range f).baseChange A = LinearMap.range (f.baseChange A) := by
  apply le_antisymm
  · rw [Submodule.baseChange]
    rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simpa using Submodule.add_mem _ hx hy
    | tmul a y =>
      obtain ⟨x, hx⟩ := y.property
      refine ⟨a ⊗ₜ[R] x, ?_⟩
      simp [LinearMap.baseChange_tmul, hx]
  · rw [Submodule.baseChange]
    have hf : f = (LinearMap.range f).subtype.comp f.rangeRestrict := by ext; rfl
    have hbc : f.baseChange A = (LinearMap.range f).subtype.baseChange A ∘ₗ
        f.rangeRestrict.baseChange A := by
      rw [← LinearMap.baseChange_comp, ← hf]
    rw [hbc]
    exact LinearMap.range_comp_le_range (f := f.rangeRestrict.baseChange A)
      (g := (LinearMap.range f).subtype.baseChange A)

/-- The base-changed inclusion of the image of an idempotent endomorphism stays injective over
an arbitrary scalar extension.  No flatness of the scalar extension is needed because the
inclusion is split. -/
theorem toBaseChange_range_injective_of_idempotent {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] {M : Type w} [AddCommGroup M]
    [Module R M] (e : M →ₗ[R] M) (he : e.comp e = e) :
    Function.Injective ((LinearMap.range e).toBaseChange A) := by
  have hsplit : e.rangeRestrict.comp (LinearMap.range e).subtype = LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨x, y, rfl⟩
    apply Subtype.ext
    exact LinearMap.congr_fun he y
  have hsplitbc : e.rangeRestrict.baseChange A ∘ₗ
      (LinearMap.range e).subtype.baseChange A = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hsplit, LinearMap.baseChange_id]
  have hinj : Function.Injective ((LinearMap.range e).subtype.baseChange A) :=
    LinearMap.injective_of_comp_eq_id _ _ hsplitbc
  exact ((LinearMap.range e).subtype.baseChange A).injective_rangeRestrict_iff.mpr hinj

end LinearMap

namespace Matrix

/-- Under the canonical identification of base-changed finite free modules, the base change of
the range of a matrix is the range of the coefficientwise base-changed matrix. -/
theorem map_baseChange_range {R : Type u} {A : Type v} [CommRing R]
    [CommRing A] [Algebra R A] {m n : Type w} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (Q : Matrix m n R) :
    ((LinearMap.range (Matrix.toLin' Q)).baseChange A).map
      (TensorProduct.piScalarRight R A A m).toLinearMap =
      LinearMap.range (Matrix.toLin' (Q.map (algebraMap R A))) := by
  rw [LinearMap.range_baseChange]
  rw [← LinearMap.range_comp]
  rw [Matrix.piScalarRight_toLin_map]
  rw [LinearMap.range_comp]
  simp

/-- The range of a finite idempotent matrix commutes with arbitrary scalar extension. -/
noncomputable def rangeBaseChangeEquiv {R : Type u} {A : Type v} [CommRing R]
    [CommRing A] [Algebra R A] {n : Type w} [Fintype n] [DecidableEq n]
    (Q : Matrix n n R) (hQ : Q * Q = Q) :
    A ⊗[R] LinearMap.range (Matrix.toLin' Q) ≃ₗ[A]
      LinearMap.range (Matrix.toLin' (Q.map (algebraMap R A))) :=
  (LinearEquiv.ofBijective ((LinearMap.range (Matrix.toLin' Q)).toBaseChange A)
      ⟨LinearMap.toBaseChange_range_injective_of_idempotent _ <| by
        rw [← Matrix.toLin'_mul, hQ],
       (LinearMap.range (Matrix.toLin' Q)).toBaseChange_surjective A⟩).trans <|
    ((TensorProduct.piScalarRight R A A n).submoduleMap
      ((LinearMap.range (Matrix.toLin' Q)).baseChange A)).trans <|
      LinearEquiv.ofEq _ _ (Matrix.map_baseChange_range Q)

end Matrix

namespace Module.Finite

/-- A finite projective module is the image of an idempotent finite matrix. -/
theorem exists_linearEquiv_range_idempotent {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] :
    ∃ (n : ℕ) (P : Matrix (Fin n) (Fin n) R), P * P = P ∧
      Nonempty (M ≃ₗ[R] LinearMap.range (Matrix.toLin' P)) := by
  obtain ⟨n, f, g, hf, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  let e : (Fin n → R) →ₗ[R] (Fin n → R) := g.comp f
  have he : e.comp e = e := by
    apply LinearMap.ext
    intro x
    simpa [e, LinearMap.comp_apply] using congrArg g (LinearMap.congr_fun hfg (f x))
  let P : Matrix (Fin n) (Fin n) R := LinearMap.toMatrix' e
  have hP : P * P = P := by
    apply Matrix.toLin'.injective
    simpa [P, Matrix.toLin'_mul] using he
  let i : M →ₗ[R] LinearMap.range e := g.codRestrict (LinearMap.range e) fun x ↦ by
    obtain ⟨y, hy⟩ := hf x
    exact ⟨y, by simp [e, hy]⟩
  let r : LinearMap.range e →ₗ[R] M := f.comp (LinearMap.range e).subtype
  have hir : r.comp i = LinearMap.id := by
    ext x
    simpa [i, r, LinearMap.comp_apply] using LinearMap.congr_fun hfg x
  have hri : i.comp r = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    obtain ⟨y, hy⟩ := x.property
    have hex : e x = x := by
      rw [← hy, ← LinearMap.comp_apply, he]
    simpa [i, r, e, LinearMap.comp_apply] using hex
  let E : M ≃ₗ[R] LinearMap.range e := LinearEquiv.ofLinearMap i r hri hir
  refine ⟨n, P, hP, ?_⟩
  rw [show Matrix.toLin' P = e by exact Matrix.toLin'_toMatrix' e]
  exact ⟨E⟩

/-- A finite projective module over an algebra descends, together with its projectivity, to a
finitely generated coefficient subalgebra. -/
theorem exists_fg_projective_model {R : Type u} {A M : Type v} [CommRing R]
    [CommRing A] [Algebra R A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Projective A M] :
    ∃ (A₀ : Subalgebra R A) (M₀ : Type v) (_ : AddCommGroup M₀) (_ : Module A₀ M₀),
      A₀.FG ∧ Module.Finite A₀ M₀ ∧ Module.Projective A₀ M₀ ∧
        Nonempty (A ⊗[A₀] M₀ ≃ₗ[A] M) := by
  obtain ⟨n, P, hP, ⟨e⟩⟩ := Module.Finite.exists_linearEquiv_range_idempotent
    (R := A) (M := M)
  obtain ⟨A₀, hA₀, Q, hQmap, hQ⟩ :=
    Matrix.exists_fg_subalgebra_of_idempotent (R := R) P hP
  let eMap : LinearMap.range (Matrix.toLin' (Q.map (algebraMap A₀ A))) ≃ₗ[A]
      LinearMap.range (Matrix.toLin' P) := LinearEquiv.ofEq _ _ <| by rw [hQmap]
  let eBase : A ⊗[A₀] LinearMap.range (Matrix.toLin' Q) ≃ₗ[A] M :=
    (Matrix.rangeBaseChangeEquiv Q hQ).trans (eMap.trans e.symm)
  exact ⟨A₀, LinearMap.range (Matrix.toLin' Q), inferInstance, inferInstance,
    hA₀, inferInstance, Matrix.projective_range_toLin_of_idempotent Q hQ, ⟨eBase⟩⟩

end Module.Finite

namespace Module.FinitePresentation

/-- Let `M` be a finitely presented `R`-module.  If its scalar extension to an `R`-algebra
`A` is projective, then its projectivity is already visible over a finitely generated
`R`-subalgebra of `A`.

This is the finite-module spreading-out ingredient behind Stacks 02JO.  It does not by itself
settle 02JO for finitely presented algebras, since such an algebra need not be finite as a module
over its base (for example, a polynomial algebra). -/
theorem exists_fg_projective_baseChange {R : Type u} {A : Type v} {M : Type w}
    [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] [Module.Projective A (A ⊗[R] M)] :
    ∃ A₀ : Subalgebra R A, A₀.FG ∧ Module.Projective A₀ (A₀ ⊗[R] M) := by
  classical
  obtain ⟨n, m, f, g, hf, hgf⟩ := Module.FinitePresentation.exists_fin' R M
  let eN : A ⊗[R] (Fin n → R) ≃ₗ[A] (Fin n → A) :=
    TensorProduct.piScalarRight R A A (Fin n)
  let eM : A ⊗[R] (Fin m → R) ≃ₗ[A] (Fin m → A) :=
    TensorProduct.piScalarRight R A A (Fin m)
  let fA : (Fin n → A) →ₗ[A] A ⊗[R] M :=
    f.baseChange A ∘ₗ eN.symm.toLinearMap
  let gA : (Fin m → A) →ₗ[A] (Fin n → A) :=
    eN.toLinearMap ∘ₗ g.baseChange A ∘ₗ eM.symm.toLinearMap
  have hfA : Function.Surjective fA :=
    (LinearMap.lTensor_surjective A hf).comp eN.symm.surjective
  have hgfA : Function.Exact gA fA := by
    have hbc : Function.Exact (g.baseChange A) (f.baseChange A) := by
      simpa only [LinearMap.baseChange_eq_ltensor] using lTensor_exact A hgf hf
    have hconj : Function.Exact
        (eN.toLinearMap.comp (g.baseChange A))
        ((f.baseChange A).comp eN.symm.toLinearMap) :=
      (LinearEquiv.conj_exact_iff_exact (g.baseChange A) (f.baseChange A) eN).mpr hbc
    exact (LinearEquiv.precomp_exact_iff_exact
      (f := eN.toLinearMap.comp (g.baseChange A))
      (g := (f.baseChange A).comp eN.symm.toLinearMap)
      (e := eM.symm)).mpr hconj
  obtain ⟨s, hfs⟩ := Module.projective_lifting_property fA LinearMap.id hfA
  let pA : (Fin n → A) →ₗ[A] (Fin n → A) := s.comp fA
  have hpA : pA.comp pA = pA := by
    rw [show pA.comp pA = s.comp (fA.comp s) ∘ₗ fA by ext; rfl, hfs]
    rfl
  have hfpA : fA.comp pA = fA := by
    rw [show fA.comp pA = (fA.comp s) ∘ₗ fA by ext; rfl, hfs]
    rfl
  let dA : (Fin n → A) →ₗ[A] (Fin n → A) := pA - LinearMap.id
  have hdA_range : LinearMap.range dA ≤ LinearMap.range gA := by
    rintro _ ⟨y, rfl⟩
    rw [← hgfA.linearMap_ker_eq, LinearMap.mem_ker]
    change fA (pA y - y) = 0
    rw [map_sub]
    have h := LinearMap.congr_fun hfpA y
    change fA (pA y) = fA y at h
    rw [h, sub_self]
  let dAr : (Fin n → A) →ₗ[A] LinearMap.range gA :=
    dA.codRestrict (LinearMap.range gA) fun x ↦ hdA_range ⟨x, rfl⟩
  obtain ⟨hA, hhA⟩ := Module.projective_lifting_property gA.rangeRestrict dAr
    (LinearMap.range_eq_top.mp gA.range_rangeRestrict)
  have hgh : gA.comp hA = dA := by
    apply LinearMap.ext
    intro x
    exact congrArg Subtype.val (LinearMap.congr_fun hhA x)
  have hpg : pA.comp gA = 0 := by
    calc
      pA.comp gA = s.comp (fA.comp gA) := by ext; rfl
      _ = s.comp 0 := by rw [hgfA.linearMap_comp_eq_zero]
      _ = 0 := LinearMap.comp_zero s
  let G : Matrix (Fin n) (Fin m) R := LinearMap.toMatrix' g
  have hgA : gA = Matrix.toLin' (G.map (algebraMap R A)) := by
    calc
      gA = (eN.toLinearMap.comp (g.baseChange A)).comp eM.symm.toLinearMap := rfl
      _ = ((Matrix.toLin' (G.map (algebraMap R A))).comp eM.toLinearMap).comp
          eM.symm.toLinearMap := by
        apply congrArg (fun q : (A ⊗[R] (Fin m → R)) →ₗ[A] (Fin n → A) ↦
          q.comp eM.symm.toLinearMap)
        simpa only [G, Matrix.toLin'_toMatrix'] using
          Matrix.piScalarRight_toLin_map (A := A) G
      _ = Matrix.toLin' (G.map (algebraMap R A)) := by
        rw [LinearMap.comp_assoc, eM.comp_symm, LinearMap.comp_id]
  let P : Matrix (Fin n) (Fin n) A := LinearMap.toMatrix' pA
  let H : Matrix (Fin m) (Fin n) A := LinearMap.toMatrix' hA
  have hP : P * P = P := by
    apply Matrix.toLin'.injective
    simpa only [P, Matrix.toLin'_mul, Matrix.toLin'_toMatrix'] using hpA
  have hPG : P * G.map (algebraMap R A) = 0 := by
    apply Matrix.toLin'.injective
    simpa only [P, Matrix.toLin'_mul, Matrix.toLin'_toMatrix', map_zero,
      hgA] using hpg
  have hGH : G.map (algebraMap R A) * H = P - 1 := by
    apply Matrix.toLin'.injective
    simpa only [H, P, Matrix.toLin'_mul, Matrix.toLin'_toMatrix', map_sub,
      Matrix.toLin'_one, hgA] using hgh
  let c : ((Fin n × Fin n) ⊕ (Fin m × Fin n)) → A
    | Sum.inl ij => P ij.1 ij.2
    | Sum.inr ij => H ij.1 ij.2
  let A₀ : Subalgebra R A := Algebra.adjoin R (Set.range c)
  let P₀ : Matrix (Fin n) (Fin n) A₀ := fun i j ↦
    ⟨P i j, Algebra.subset_adjoin ⟨Sum.inl (i, j), rfl⟩⟩
  let H₀ : Matrix (Fin m) (Fin n) A₀ := fun i j ↦
    ⟨H i j, Algebra.subset_adjoin ⟨Sum.inr (i, j), rfl⟩⟩
  let G₀ : Matrix (Fin n) (Fin m) A₀ := G.map (algebraMap R A₀)
  have hA₀ : A₀.FG :=
    Subalgebra.fg_def.mpr ⟨Set.range c, Set.finite_range c, rfl⟩
  have hP₀map : P₀.map (algebraMap A₀ A) = P := by
    ext i j
    rfl
  have hH₀map : H₀.map (algebraMap A₀ A) = H := by
    ext i j
    rfl
  have hG₀map : G₀.map (algebraMap A₀ A) = G.map (algebraMap R A) := by
    ext i j
    simp only [G₀, Matrix.map_apply]
    exact IsScalarTower.algebraMap_apply R A₀ A (G i j)
  have hP₀ : P₀ * P₀ = P₀ := by
    apply Matrix.map_injective (f := algebraMap A₀ A) Subtype.val_injective
    change (P₀ * P₀).map (algebraMap A₀ A) = P₀.map (algebraMap A₀ A)
    rw [Matrix.map_mul, hP₀map, hP]
  have hP₀G₀ : P₀ * G₀ = 0 := by
    apply Matrix.map_injective (f := algebraMap A₀ A) Subtype.val_injective
    change (P₀ * G₀).map (algebraMap A₀ A) =
      (0 : Matrix (Fin n) (Fin m) A₀).map (algebraMap A₀ A)
    rw [Matrix.map_mul, hP₀map, hG₀map,
      Matrix.map_zero (algebraMap A₀ A) (map_zero _), hPG]
  have hG₀H₀ : G₀ * H₀ = P₀ - 1 := by
    apply Matrix.map_injective (f := algebraMap A₀ A) Subtype.val_injective
    change (G₀ * H₀).map (algebraMap A₀ A) =
      (P₀ - 1).map (algebraMap A₀ A)
    rw [Matrix.map_mul,
      Matrix.map_sub (algebraMap A₀ A) (map_sub _),
      Matrix.map_one (algebraMap A₀ A) (map_zero _) (map_one _),
      hG₀map, hH₀map, hP₀map, hGH]
  let eN₀ : A₀ ⊗[R] (Fin n → R) ≃ₗ[A₀] (Fin n → A₀) :=
    TensorProduct.piScalarRight R A₀ A₀ (Fin n)
  let eM₀ : A₀ ⊗[R] (Fin m → R) ≃ₗ[A₀] (Fin m → A₀) :=
    TensorProduct.piScalarRight R A₀ A₀ (Fin m)
  let f₀ : (Fin n → A₀) →ₗ[A₀] A₀ ⊗[R] M :=
    f.baseChange A₀ ∘ₗ eN₀.symm.toLinearMap
  let g₀ : (Fin m → A₀) →ₗ[A₀] (Fin n → A₀) := Matrix.toLin' G₀
  let p₀ : (Fin n → A₀) →ₗ[A₀] (Fin n → A₀) := Matrix.toLin' P₀
  let h₀ : (Fin n → A₀) →ₗ[A₀] (Fin m → A₀) := Matrix.toLin' H₀
  have hf₀ : Function.Surjective f₀ :=
    (LinearMap.lTensor_surjective A₀ hf).comp eN₀.symm.surjective
  have hgConj₀ :
      (eN₀.toLinearMap.comp (g.baseChange A₀)).comp eM₀.symm.toLinearMap = g₀ := by
    calc
      (eN₀.toLinearMap.comp (g.baseChange A₀)).comp eM₀.symm.toLinearMap =
          ((Matrix.toLin' (G.map (algebraMap R A₀))).comp eM₀.toLinearMap).comp
            eM₀.symm.toLinearMap := by
        apply congrArg (fun q : (A₀ ⊗[R] (Fin m → R)) →ₗ[A₀] (Fin n → A₀) ↦
          q.comp eM₀.symm.toLinearMap)
        simpa only [G, Matrix.toLin'_toMatrix'] using
          Matrix.piScalarRight_toLin_map (A := A₀) G
      _ = Matrix.toLin' (G.map (algebraMap R A₀)) := by
        rw [LinearMap.comp_assoc, eM₀.comp_symm, LinearMap.comp_id]
      _ = g₀ := rfl
  have hgf₀ : Function.Exact g₀ f₀ := by
    have hbc : Function.Exact (g.baseChange A₀) (f.baseChange A₀) := by
      simpa only [LinearMap.baseChange_eq_ltensor] using lTensor_exact A₀ hgf hf
    have hconj : Function.Exact
        (eN₀.toLinearMap.comp (g.baseChange A₀))
        ((f.baseChange A₀).comp eN₀.symm.toLinearMap) :=
      (LinearEquiv.conj_exact_iff_exact (g.baseChange A₀) (f.baseChange A₀) eN₀).mpr hbc
    have hpre : Function.Exact
        ((eN₀.toLinearMap.comp (g.baseChange A₀)).comp eM₀.symm.toLinearMap)
        ((f.baseChange A₀).comp eN₀.symm.toLinearMap) :=
      (LinearEquiv.precomp_exact_iff_exact
        (f := eN₀.toLinearMap.comp (g.baseChange A₀))
        (g := (f.baseChange A₀).comp eN₀.symm.toLinearMap)
        (e := eM₀.symm)).mpr hconj
    simpa only [hgConj₀, f₀] using hpre
  have hp₀ : p₀.comp p₀ = p₀ := by
    simpa only [p₀, Matrix.toLin'_mul] using congrArg Matrix.toLin' hP₀
  have hp₀g₀ : p₀.comp g₀ = 0 := by
    simpa only [p₀, g₀, Matrix.toLin'_mul, map_zero] using
      congrArg Matrix.toLin' hP₀G₀
  have hg₀h₀ : g₀.comp h₀ = p₀ - LinearMap.id := by
    simpa only [p₀, g₀, h₀, Matrix.toLin'_mul, map_sub, Matrix.toLin'_one] using
      congrArg Matrix.toLin' hG₀H₀
  have hfd₀ : f₀.comp (p₀ - LinearMap.id) = 0 := by
    calc
      f₀.comp (p₀ - LinearMap.id) = f₀.comp (g₀.comp h₀) := by rw [hg₀h₀]
      _ = (f₀.comp g₀).comp h₀ := by ext; rfl
      _ = 0 := by rw [hgf₀.linearMap_comp_eq_zero, LinearMap.zero_comp]
  have hfp₀ : f₀.comp p₀ = f₀ := by
    apply LinearMap.ext
    intro x
    have hx := LinearMap.congr_fun hfd₀ x
    change f₀ (p₀ x - x) = 0 at hx
    rw [map_sub] at hx
    exact sub_eq_zero.mp hx
  let fr : LinearMap.range p₀ →ₗ[A₀] A₀ ⊗[R] M :=
    f₀.comp (LinearMap.range p₀).subtype
  have hfrsurj : Function.Surjective fr := by
    intro y
    obtain ⟨x, hx⟩ := hf₀ y
    refine ⟨⟨p₀ x, ⟨x, rfl⟩⟩, ?_⟩
    change f₀ (p₀ x) = y
    rw [show f₀ (p₀ x) = f₀ x by exact LinearMap.congr_fun hfp₀ x, hx]
  have hfrinj : Function.Injective fr := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    apply Subtype.ext
    change f₀ x = f₀ y at hxy
    have hfix (z : Fin n → A₀) (hz : z ∈ LinearMap.range p₀) : p₀ z = z := by
      obtain ⟨t, rfl⟩ := hz
      exact LinearMap.congr_fun hp₀ t
    have hzker : x - y ∈ LinearMap.ker f₀ := by
      rw [LinearMap.mem_ker, map_sub, hxy, sub_self]
    rw [hgf₀.linearMap_ker_eq] at hzker
    obtain ⟨z, hz⟩ := hzker
    have hpzero : p₀ (x - y) = 0 := by
      rw [← hz, ← LinearMap.comp_apply, hp₀g₀, LinearMap.zero_apply]
    have hpfix : p₀ (x - y) = x - y := by
      rw [map_sub, hfix x hx, hfix y hy]
    exact sub_eq_zero.mp (by rw [← hpfix, hpzero])
  let e : LinearMap.range p₀ ≃ₗ[A₀] A₀ ⊗[R] M :=
    LinearEquiv.ofBijective fr ⟨hfrinj, hfrsurj⟩
  have hproj : Module.Projective A₀ (LinearMap.range p₀) := by
    simpa only [p₀] using Matrix.projective_range_toLin_of_idempotent P₀ hP₀
  let _ : Module.Projective A₀ (LinearMap.range p₀) := hproj
  exact ⟨A₀, hA₀, Module.Projective.of_equiv' e⟩

/-- A fixed finitely presented module which becomes flat after scalar extension is already flat
after passing to a finitely generated coefficient subalgebra.

Finite presentation is essential here: it turns flatness into projectivity, so that the finite
idempotent-matrix descent above applies. -/
theorem exists_fg_flat_baseChange {R : Type u} {A : Type v} {M : Type w}
    [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] [Module.Flat A (A ⊗[R] M)] :
    ∃ A₀ : Subalgebra R A, A₀.FG ∧ Module.Flat A₀ (A₀ ⊗[R] M) := by
  let _ : Module.Projective A (A ⊗[R] M) :=
    Module.Flat.projective_of_finitePresentation
  obtain ⟨A₀, hA₀, hM₀⟩ := exists_fg_projective_baseChange (R := R) (A := A) (M := M)
  let _ : Module.Projective A₀ (A₀ ⊗[R] M) := hM₀
  exact ⟨A₀, hA₀, inferInstance⟩

end Module.FinitePresentation

namespace Algebra.FinitePresentation

variable (R : Type u) (A : Type v) (B : Type w) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra A B]

/-- The special case `M = B` of the finite-stage conclusion in Stacks 02JO. -/
def HasFlatIntegerModel (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] : Prop :=
  ∃ (A₀ : Subalgebra ℤ A) (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra A₀ B₀),
    Algebra.FinitePresentation ℤ A₀ ∧ Algebra.FinitePresentation A₀ B₀ ∧
      Module.Flat A₀ B₀ ∧ Nonempty (B ≃ₐ[A] A ⊗[A₀] B₀)

/-- Smooth algebras satisfy the finite-stage flatness conclusion of 02JO.  This is the
formally-smooth subclass, supplied by Mathlib's coefficient descent for smooth presentations. -/
theorem HasFlatIntegerModel.of_smooth (A : Type u) (B : Type v) [CommRing A]
    [CommRing B] [Algebra A B] [Algebra.Smooth A B] : HasFlatIntegerModel A B := by
  obtain ⟨A₀, B₀, _, _, hA₀, hB₀, e⟩ := Algebra.Smooth.exists_subalgebra_fg ℤ A B
  let _ : Algebra.Smooth A₀ B₀ := hB₀
  exact ⟨A₀, B₀, inferInstance, inferInstance,
    Algebra.FinitePresentation.of_finiteType.mp
      ((Subalgebra.fg_iff_finiteType A₀).mp hA₀), inferInstance, inferInstance, e⟩

/-- The coefficient-model part of Stacks 02JO: a finitely presented `A`-algebra is obtained by
base change from a finitely presented algebra over a finitely generated `R`-subalgebra of `A`.

Unlike 02JO itself, this statement does not yet preserve flatness. -/
theorem exists_fg_model [Algebra.FinitePresentation A B] :
    ∃ (A₀ : Subalgebra R A) (B₀ : Type v) (_ : CommRing B₀) (_ : Algebra A₀ B₀),
      A₀.FG ∧ Algebra.FinitePresentation A₀ B₀ ∧ Nonempty (B ≃ₐ[A] A ⊗[A₀] B₀) := by
  let P := Algebra.Presentation.ofFinitePresentation A B
  let A₀ : Subalgebra R A := Algebra.adjoin R P.coeffs
  let _ : Algebra A₀ B := inferInstanceAs <| Algebra (Algebra.adjoin R P.coeffs) B
  let _ : IsScalarTower A₀ A B :=
    inferInstanceAs <| IsScalarTower (Algebra.adjoin R P.coeffs) A B
  have hcoeffs : P.HasCoeffs A₀ := ⟨by simp [A₀]⟩
  have hA₀ : A₀.FG := by
    refine Subalgebra.fg_def.mpr ⟨P.coeffs, P.finite_coeffs, rfl⟩
  exact ⟨A₀, P.ModelOfHasCoeffs A₀, inferInstance, inferInstance, hA₀,
    inferInstance, ⟨(P.tensorModelOfHasCoeffsEquiv A₀).symm⟩⟩

/-- The absolute coefficient-model part of Stacks 02JO.  Over `ℤ`, the finite type
coefficient ring furnished by a presentation is automatically finitely presented. -/
theorem exists_integer_model (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FinitePresentation A B] :
    ∃ (A₀ : Subalgebra ℤ A) (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra A₀ B₀),
      Algebra.FinitePresentation ℤ A₀ ∧ Algebra.FinitePresentation A₀ B₀ ∧
        Nonempty (B ≃ₐ[A] A ⊗[A₀] B₀) := by
  obtain ⟨A₀, B₀, _, _, hA₀, hB₀, e⟩ := exists_fg_model ℤ A B
  exact ⟨A₀, B₀, inferInstance, inferInstance,
    Algebra.FinitePresentation.of_finiteType.mp
      ((Subalgebra.fg_iff_finiteType A₀).mp hA₀), hB₀, e⟩

end Algebra.FinitePresentation

namespace Module.FinitePresentation

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable {σ : Type w}

/-- The finitely generated coefficient subalgebra containing all coefficients of a finite
matrix over a multivariate polynomial ring. -/
noncomputable def polynomialMatrixCoeffSubalgebra {m n : ℕ}
    (G : Matrix (Fin n) (Fin m) (MvPolynomial σ A)) : Subalgebra R A :=
  Algebra.adjoin R (⋃ i, ⋃ j, ((G i j).coeffs : Set A))

/-- The coefficient subalgebra of a finite polynomial matrix is finitely generated. -/
theorem polynomialMatrixCoeffSubalgebra_fg {m n : ℕ}
    (G : Matrix (Fin n) (Fin m) (MvPolynomial σ A)) :
    (polynomialMatrixCoeffSubalgebra (R := R) G).FG := by
  refine Subalgebra.fg_def.mpr ⟨_, ?_, rfl⟩
  exact Set.finite_iUnion fun i => Set.finite_iUnion fun j => Finset.finite_toSet _

/-- Every coefficient of the matrix lies in its coefficient subalgebra. -/
theorem polynomialMatrixCoeffSubalgebra_coeffs_subset {m n : ℕ}
    (G : Matrix (Fin n) (Fin m) (MvPolynomial σ A)) (i j) :
    ((G i j).coeffs : Set A) ⊆
      Set.range (algebraMap (polynomialMatrixCoeffSubalgebra (R := R) G) A) := by
  rw [Subalgebra.setRange_algebraMap]
  intro a ha
  exact Algebra.subset_adjoin <| Set.mem_iUnion_of_mem i <|
    Set.mem_iUnion_of_mem j ha

/-- A finite polynomial matrix lifted to its coefficient subalgebra. -/
noncomputable def polynomialMatrixLift {m n : ℕ}
    (G : Matrix (Fin n) (Fin m) (MvPolynomial σ A)) :
    Matrix (Fin n) (Fin m)
      (MvPolynomial σ (polynomialMatrixCoeffSubalgebra (R := R) G)) :=
  fun i j => (MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    (polynomialMatrixCoeffSubalgebra_coeffs_subset (R := R) G i j)).choose

/-- Mapping the lifted matrix back to the original coefficient ring recovers the matrix. -/
theorem map_polynomialMatrixLift {m n : ℕ}
    (G : Matrix (Fin n) (Fin m) (MvPolynomial σ A)) :
    (polynomialMatrixLift (R := R) G).map
        (MvPolynomial.map (algebraMap (polynomialMatrixCoeffSubalgebra (R := R) G) A)) = G := by
  funext i j
  exact (MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    (polynomialMatrixCoeffSubalgebra_coeffs_subset (R := R) G i j)).choose_spec

/-- The cokernel module presented by a finite polynomial matrix. -/
abbrev polynomialMatrixCokernel {B : Type*} [CommRing B] {m n : ℕ}
    (G : Matrix (Fin n) (Fin m) (MvPolynomial σ B)) :=
  (Fin n → MvPolynomial σ B) ⧸ LinearMap.range (Matrix.toLin' G)

/-- The polynomial-ring algebra structure induced by the inclusion of the matrix coefficient
subalgebra. -/
@[instance_reducible]
noncomputable def polynomialMatrixAlgebra {m n : ℕ}
    (G : Matrix (Fin n) (Fin m) (MvPolynomial σ A)) :
    Algebra
      (MvPolynomial σ (polynomialMatrixCoeffSubalgebra (R := R) G))
      (MvPolynomial σ A) :=
  MvPolynomial.algebraMvPolynomial

/-- The algebra map induced by `polynomialMatrixAlgebra` is coefficientwise polynomial map. -/
theorem polynomialMatrixAlgebra_algebraMap {m n : ℕ}
    (G : Matrix (Fin n) (Fin m) (MvPolynomial σ A)) :
    @algebraMap
      (MvPolynomial σ (polynomialMatrixCoeffSubalgebra (R := R) G))
      (MvPolynomial σ A) _ _ (polynomialMatrixAlgebra (R := R) G) =
      MvPolynomial.map
        (algebraMap (polynomialMatrixCoeffSubalgebra (R := R) G) A) :=
  rfl

/-- The cokernel of a finite polynomial matrix is finitely presented. -/
theorem finitePresentation_polynomialMatrixCokernel {B : Type*} [CommRing B]
    {m n : ℕ} (G : Matrix (Fin n) (Fin m) (MvPolynomial σ B)) :
    Module.FinitePresentation (MvPolynomial σ B) (polynomialMatrixCokernel G) := by
  apply Module.finitePresentation_of_surjective
    (LinearMap.range (Matrix.toLin' G)).mkQ
    (Submodule.mkQ_surjective _)
  simpa only [Submodule.ker_mkQ] using Submodule.fg_range (Matrix.toLin' G)

/-- A finite presentation matrix over a polynomial ring descends to its finitely generated
coefficient subalgebra, and extending the descended cokernel back along the canonical
polynomial-ring map recovers the original module. -/
noncomputable def polynomialPresentationBaseChangeEquiv
    {M : Type*} [AddCommGroup M] [Module (MvPolynomial σ A) M]
    {m n : ℕ} (f : (Fin n → MvPolynomial σ A) →ₗ[MvPolynomial σ A] M)
    (g : (Fin m → MvPolynomial σ A) →ₗ[MvPolynomial σ A]
      (Fin n → MvPolynomial σ A))
    (hf : Function.Surjective f) (hgf : Function.Exact g f) :
    let G := LinearMap.toMatrix' g
    let A₀ := polynomialMatrixCoeffSubalgebra (R := R) G
    letI : Algebra (MvPolynomial σ A₀) (MvPolynomial σ A) :=
      polynomialMatrixAlgebra (R := R) G
    (MvPolynomial σ A) ⊗[MvPolynomial σ A₀]
        polynomialMatrixCokernel (polynomialMatrixLift (R := R) G) ≃ₗ[MvPolynomial σ A] M := by
  classical
  let S := MvPolynomial σ A
  let G := LinearMap.toMatrix' g
  let A₀ := polynomialMatrixCoeffSubalgebra (R := R) G
  let S₀ := MvPolynomial σ A₀
  let G₀ := polynomialMatrixLift (R := R) G
  letI : Algebra S₀ S := polynomialMatrixAlgebra (R := R) G
  let M₀ := polynomialMatrixCokernel G₀
  let g₀ : (Fin m → S₀) →ₗ[S₀] (Fin n → S₀) := Matrix.toLin' G₀
  let q₀ : (Fin n → S₀) →ₗ[S₀] M₀ := (LinearMap.range g₀).mkQ
  let eN : S ⊗[S₀] (Fin n → S₀) ≃ₗ[S] (Fin n → S) :=
    TensorProduct.piScalarRight S₀ S S (Fin n)
  let eM : S ⊗[S₀] (Fin m → S₀) ≃ₗ[S] (Fin m → S) :=
    TensorProduct.piScalarRight S₀ S S (Fin m)
  let gS : (Fin m → S) →ₗ[S] (Fin n → S) :=
    (eN.toLinearMap.comp (g₀.baseChange S)).comp eM.symm.toLinearMap
  let qS : (Fin n → S) →ₗ[S] S ⊗[S₀] M₀ :=
    q₀.baseChange S ∘ₗ eN.symm.toLinearMap
  have hq₀ : Function.Surjective q₀ := Submodule.mkQ_surjective _
  have hgf₀ : Function.Exact g₀ q₀ := by
    rw [LinearMap.exact_iff]
    exact Submodule.ker_mkQ _
  have hbc : Function.Exact (g₀.baseChange S) (q₀.baseChange S) := by
    simpa only [LinearMap.baseChange_eq_ltensor] using lTensor_exact S hgf₀ hq₀
  have hconj : Function.Exact
      (eN.toLinearMap.comp (g₀.baseChange S))
      ((q₀.baseChange S).comp eN.symm.toLinearMap) :=
    (LinearEquiv.conj_exact_iff_exact (g₀.baseChange S) (q₀.baseChange S) eN).mpr hbc
  have hexS : Function.Exact gS qS :=
    (LinearEquiv.precomp_exact_iff_exact
      (f := eN.toLinearMap.comp (g₀.baseChange S))
      (g := (q₀.baseChange S).comp eN.symm.toLinearMap)
      (e := eM.symm)).mpr hconj
  have hgS : gS = g := by
    calc
      gS = ((Matrix.toLin'
          (G₀.map (algebraMap S₀ S))).comp eM.toLinearMap).comp
            eM.symm.toLinearMap := by
        apply congrArg (fun q : S ⊗[S₀] (Fin m → S₀) →ₗ[S] (Fin n → S) =>
          q.comp eM.symm.toLinearMap)
        simpa only [gS, g₀] using Matrix.piScalarRight_toLin_map (A := S) G₀
      _ = Matrix.toLin' (G₀.map (algebraMap S₀ S)) := by
        rw [LinearMap.comp_assoc, eM.comp_symm, LinearMap.comp_id]
      _ = Matrix.toLin' G := by
        congr 1
        change G₀.map
          (MvPolynomial.map (algebraMap A₀ A)) = G
        exact map_polynomialMatrixLift (R := R) G
      _ = g := Matrix.toLin'_toMatrix' g
  have hqS : Function.Surjective qS :=
    (LinearMap.lTensor_surjective S hq₀).comp eN.symm.surjective
  have hker : LinearMap.ker qS = LinearMap.ker f := by
    calc
      LinearMap.ker qS = LinearMap.range gS := hexS.linearMap_ker_eq
      _ = LinearMap.range g := by rw [hgS]
      _ = LinearMap.ker f := hgf.linearMap_ker_eq.symm
  let eKer : ((Fin n → S) ⧸ LinearMap.ker qS) ≃ₗ[S]
      ((Fin n → S) ⧸ LinearMap.ker f) :=
    Submodule.Quotient.equiv (LinearMap.ker qS) (LinearMap.ker f)
      (LinearEquiv.refl S (Fin n → S)) (by simpa using hker)
  exact (qS.quotKerEquivOfSurjective hqS).symm.trans <|
    eKer.trans (f.quotKerEquivOfSurjective hf)

/-- Scalar extension of a finite polynomial presentation along an arbitrary coefficient-ring
map recovers the presented module, provided the relation matrices agree after applying the
coefficient map. -/
noncomputable def polynomialPresentationBaseChangeEquivOfMap
    {B : Type*} [CommRing B] [Algebra B A]
    {M : Type*} [AddCommGroup M] [Module (MvPolynomial σ A) M]
    {m n : ℕ} (f : (Fin n → MvPolynomial σ A) →ₗ[MvPolynomial σ A] M)
    (g : (Fin m → MvPolynomial σ A) →ₗ[MvPolynomial σ A]
      (Fin n → MvPolynomial σ A))
    (G₀ : Matrix (Fin n) (Fin m) (MvPolynomial σ B))
    (hG₀ : G₀.map (MvPolynomial.map (algebraMap B A)) = LinearMap.toMatrix' g)
    (hf : Function.Surjective f) (hgf : Function.Exact g f) :
    letI : Algebra (MvPolynomial σ B) (MvPolynomial σ A) :=
      MvPolynomial.algebraMvPolynomial
    (MvPolynomial σ A) ⊗[MvPolynomial σ B]
        polynomialMatrixCokernel G₀ ≃ₗ[MvPolynomial σ A] M := by
  classical
  let S := MvPolynomial σ A
  let S₀ := MvPolynomial σ B
  letI : Algebra S₀ S := MvPolynomial.algebraMvPolynomial
  let M₀ := polynomialMatrixCokernel G₀
  let g₀ : (Fin m → S₀) →ₗ[S₀] (Fin n → S₀) := Matrix.toLin' G₀
  let q₀ : (Fin n → S₀) →ₗ[S₀] M₀ := (LinearMap.range g₀).mkQ
  let eN : S ⊗[S₀] (Fin n → S₀) ≃ₗ[S] (Fin n → S) :=
    TensorProduct.piScalarRight S₀ S S (Fin n)
  let eM : S ⊗[S₀] (Fin m → S₀) ≃ₗ[S] (Fin m → S) :=
    TensorProduct.piScalarRight S₀ S S (Fin m)
  let gS : (Fin m → S) →ₗ[S] (Fin n → S) :=
    (eN.toLinearMap.comp (g₀.baseChange S)).comp eM.symm.toLinearMap
  let qS : (Fin n → S) →ₗ[S] S ⊗[S₀] M₀ :=
    q₀.baseChange S ∘ₗ eN.symm.toLinearMap
  have hq₀ : Function.Surjective q₀ := Submodule.mkQ_surjective _
  have hgf₀ : Function.Exact g₀ q₀ := by
    rw [LinearMap.exact_iff]
    exact Submodule.ker_mkQ _
  have hbc : Function.Exact (g₀.baseChange S) (q₀.baseChange S) := by
    simpa only [LinearMap.baseChange_eq_ltensor] using lTensor_exact S hgf₀ hq₀
  have hconj : Function.Exact
      (eN.toLinearMap.comp (g₀.baseChange S))
      ((q₀.baseChange S).comp eN.symm.toLinearMap) :=
    (LinearEquiv.conj_exact_iff_exact (g₀.baseChange S) (q₀.baseChange S) eN).mpr hbc
  have hexS : Function.Exact gS qS :=
    (LinearEquiv.precomp_exact_iff_exact
      (f := eN.toLinearMap.comp (g₀.baseChange S))
      (g := (q₀.baseChange S).comp eN.symm.toLinearMap)
      (e := eM.symm)).mpr hconj
  have hgS : gS = g := by
    calc
      gS = ((Matrix.toLin'
          (G₀.map (algebraMap S₀ S))).comp eM.toLinearMap).comp
            eM.symm.toLinearMap := by
        apply congrArg (fun q : S ⊗[S₀] (Fin m → S₀) →ₗ[S] (Fin n → S) =>
          q.comp eM.symm.toLinearMap)
        simpa only [gS, g₀] using Matrix.piScalarRight_toLin_map (A := S) G₀
      _ = Matrix.toLin' (G₀.map (algebraMap S₀ S)) := by
        rw [LinearMap.comp_assoc, eM.comp_symm, LinearMap.comp_id]
      _ = Matrix.toLin' (LinearMap.toMatrix' g) := by
        rw [show algebraMap S₀ S = MvPolynomial.map (algebraMap B A) from rfl, hG₀]
      _ = g := Matrix.toLin'_toMatrix' g
  have hqS : Function.Surjective qS :=
    (LinearMap.lTensor_surjective S hq₀).comp eN.symm.surjective
  have hker : LinearMap.ker qS = LinearMap.ker f := by
    calc
      LinearMap.ker qS = LinearMap.range gS := hexS.linearMap_ker_eq
      _ = LinearMap.range g := by rw [hgS]
      _ = LinearMap.ker f := hgf.linearMap_ker_eq.symm
  let eKer : ((Fin n → S) ⧸ LinearMap.ker qS) ≃ₗ[S]
      ((Fin n → S) ⧸ LinearMap.ker f) :=
    Submodule.Quotient.equiv (LinearMap.ker qS) (LinearMap.ker f)
      (LinearEquiv.refl S (Fin n → S)) (by simpa using hker)
  exact (qS.quotKerEquivOfSurjective hqS).symm.trans <|
    eKer.trans (f.quotKerEquivOfSurjective hf)

/-- Finite free presentation data for a module over a polynomial ring. -/
structure PolynomialModel (A : Type v) [CommRing A] (σ : Type w)
    (M : Type*) [AddCommGroup M] [Module (MvPolynomial σ A) M] where
  generators : ℕ
  relations : ℕ
  quotient : (Fin generators → MvPolynomial σ A) →ₗ[MvPolynomial σ A] M
  relation : (Fin relations → MvPolynomial σ A) →ₗ[MvPolynomial σ A]
    (Fin generators → MvPolynomial σ A)
  quotient_surjective : Function.Surjective quotient
  exact : Function.Exact relation quotient

namespace PolynomialModel

variable {M : Type*} [AddCommGroup M] [Module (MvPolynomial σ A) M]

/-- A finitely presented module over a polynomial ring admits finite free presentation data. -/
theorem nonempty [Module.FinitePresentation (MvPolynomial σ A) M] :
    Nonempty (PolynomialModel A σ M) := by
  obtain ⟨n, m, f, g, hf, hgf⟩ :=
    Module.FinitePresentation.exists_fin' (MvPolynomial σ A) M
  exact ⟨⟨n, m, f, g, hf, hgf⟩⟩

/-- Choose finite presentation data for a finitely presented module over a polynomial ring. -/
noncomputable def ofFinitePresentation [Module.FinitePresentation (MvPolynomial σ A) M] :
    PolynomialModel A σ M :=
  Classical.choice nonempty

/-- The finitely generated coefficient ring containing the entries of the relation matrix. -/
noncomputable abbrev coefficientRing (D : PolynomialModel A σ M) : Subalgebra R A :=
  polynomialMatrixCoeffSubalgebra (R := R) (LinearMap.toMatrix' D.relation)

/-- The relation matrix over the coefficient ring. -/
noncomputable abbrev modelRelation (D : PolynomialModel A σ M) :
    Matrix (Fin D.generators) (Fin D.relations)
      (MvPolynomial σ (D.coefficientRing (R := R))) :=
  polynomialMatrixLift (R := R) (LinearMap.toMatrix' D.relation)

/-- The finitely presented module over the coefficient ring obtained from the descended matrix. -/
noncomputable abbrev modelModule (D : PolynomialModel A σ M) :=
  polynomialMatrixCokernel (D.modelRelation (R := R))

/-- The canonical polynomial-ring map from the model to the original coefficient ring. -/
noncomputable abbrev modelAlgebra (D : PolynomialModel A σ M) :
    Algebra (MvPolynomial σ (D.coefficientRing (R := R))) (MvPolynomial σ A) :=
  polynomialMatrixAlgebra (R := R) (LinearMap.toMatrix' D.relation)

/-- The model's coefficient ring is finitely generated. -/
theorem coefficientRing_fg (D : PolynomialModel A σ M) :
    (D.coefficientRing (R := R)).FG :=
  polynomialMatrixCoeffSubalgebra_fg (R := R) (LinearMap.toMatrix' D.relation)

/-- The descended relation matrix maps to the original relation matrix. -/
theorem modelRelation_map (D : PolynomialModel A σ M) :
    (D.modelRelation (R := R)).map
      (MvPolynomial.map (algebraMap (D.coefficientRing (R := R)) A)) =
        LinearMap.toMatrix' D.relation :=
  map_polynomialMatrixLift (R := R) (LinearMap.toMatrix' D.relation)

/-- The descended model module is finitely presented over the smaller polynomial ring. -/
theorem modelModule_finitePresentation (D : PolynomialModel A σ M) :
    Module.FinitePresentation
      (MvPolynomial σ (D.coefficientRing (R := R)))
      (D.modelModule (R := R)) :=
  finitePresentation_polynomialMatrixCokernel (D.modelRelation (R := R))

/-- Extending the descended module back to the original polynomial ring recovers the module. -/
noncomputable def baseChangeEquiv (D : PolynomialModel A σ M) :
    letI : Algebra
        (MvPolynomial σ (D.coefficientRing (R := R))) (MvPolynomial σ A) :=
      D.modelAlgebra (R := R)
    (MvPolynomial σ A) ⊗[MvPolynomial σ (D.coefficientRing (R := R))]
      (D.modelModule (R := R)) ≃ₗ[MvPolynomial σ A] M :=
  polynomialPresentationBaseChangeEquiv D.quotient D.relation
    D.quotient_surjective D.exact

/-- Coefficient-ring scalar extension of the descended module recovers the original module.
This is the module component of the polynomial algebra pushout, expressed over the coefficient
rings rather than over the two polynomial rings. -/
noncomputable def coefficientBaseChangeEquiv (D : PolynomialModel A σ M) :
    letI : Module A M := Module.compHom M (algebraMap A (MvPolynomial σ A))
    A ⊗[D.coefficientRing (R := R)] (D.modelModule (R := R)) ≃ₗ[A] M := by
  let A₀ := D.coefficientRing (R := R)
  let S₀ := MvPolynomial σ A₀
  let S := MvPolynomial σ A
  let M₀ := D.modelModule (R := R)
  letI : Module A M := Module.compHom M (algebraMap A S)
  letI : IsScalarTower A S M := IsScalarTower.of_compHom A S M
  letI : Algebra S₀ S := D.modelAlgebra (R := R)
  letI : IsScalarTower A S (S ⊗[S₀] M₀) :=
    IsScalarTower.of_algebraMap_smul fun a x => by
      induction x with
      | zero => rw [TensorProduct.smul_zero, TensorProduct.smul_zero]
      | add x y hx hy =>
        rw [TensorProduct.smul_add, TensorProduct.smul_add, hx, hy]
      | tmul s m => simp [Algebra.smul_def, TensorProduct.smul_tmul']
  exact (Algebra.IsPushout.cancelBaseChange A₀ A S₀ S M₀).symm.trans
    ((D.baseChangeEquiv (R := R)).restrictScalars A)

/-- A finite coefficient model of a polynomial presentation for which the descended module is
flat over the coefficient ring.  Existence of this structure is precisely the relative flatness
spreading input missing from the current formalization of Stacks 02JO; no existence claim is
made here. -/
structure FlatCoefficientModel (D : PolynomialModel A σ M) where
  coefficientRing : Subalgebra R A
  coefficientRing_fg : coefficientRing.FG
  relation : Matrix (Fin D.generators) (Fin D.relations)
    (MvPolynomial σ coefficientRing)
  relation_map : relation.map
    (MvPolynomial.map (algebraMap coefficientRing A)) = LinearMap.toMatrix' D.relation
  flat :
    let N := polynomialMatrixCokernel relation
    letI : Module coefficientRing N :=
      Module.compHom N (algebraMap coefficientRing (MvPolynomial σ coefficientRing))
    Module.Flat coefficientRing N

namespace FlatCoefficientModel

variable {D : PolynomialModel A σ M}

/-- The descended polynomial module in a flat coefficient model. -/
noncomputable abbrev modelModule (E : FlatCoefficientModel (R := R) D) :=
  polynomialMatrixCokernel E.relation

/-- The descended module in a flat coefficient model is finitely presented over the descended
polynomial ring. -/
theorem modelModule_finitePresentation (E : FlatCoefficientModel (R := R) D) :
    Module.FinitePresentation (MvPolynomial σ E.coefficientRing) E.modelModule :=
  finitePresentation_polynomialMatrixCokernel E.relation

/-- Polynomial-ring scalar extension of a flat coefficient model recovers the original
module. -/
noncomputable def baseChangeEquiv (E : FlatCoefficientModel (R := R) D) :
    letI : Algebra (MvPolynomial σ E.coefficientRing) (MvPolynomial σ A) :=
      MvPolynomial.algebraMvPolynomial
    (MvPolynomial σ A) ⊗[MvPolynomial σ E.coefficientRing] E.modelModule
      ≃ₗ[MvPolynomial σ A] M :=
  polynomialPresentationBaseChangeEquivOfMap D.quotient D.relation E.relation
    E.relation_map D.quotient_surjective D.exact

/-- Coefficient-ring scalar extension of a flat coefficient model recovers the original
module. -/
noncomputable def coefficientBaseChangeEquiv (E : FlatCoefficientModel (R := R) D) :
    letI : Module A M := Module.compHom M (algebraMap A (MvPolynomial σ A))
    A ⊗[E.coefficientRing] E.modelModule ≃ₗ[A] M := by
  let B := E.coefficientRing
  let S₀ := MvPolynomial σ B
  let S := MvPolynomial σ A
  let M₀ := E.modelModule
  letI : Module A M := Module.compHom M (algebraMap A S)
  letI : IsScalarTower A S M := IsScalarTower.of_compHom A S M
  letI : Algebra S₀ S := MvPolynomial.algebraMvPolynomial
  letI : IsScalarTower A S (S ⊗[S₀] M₀) :=
    IsScalarTower.of_algebraMap_smul fun a x => by
      induction x with
      | zero => rw [TensorProduct.smul_zero, TensorProduct.smul_zero]
      | add x y hx hy =>
        rw [TensorProduct.smul_add, TensorProduct.smul_add, hx, hy]
      | tmul s m => simp [Algebra.smul_def, TensorProduct.smul_tmul']
  exact (Algebra.IsPushout.cancelBaseChange B A S₀ S M₀).symm.trans
    (E.baseChangeEquiv.restrictScalars A)

end FlatCoefficientModel

end PolynomialModel

end Module.FinitePresentation
