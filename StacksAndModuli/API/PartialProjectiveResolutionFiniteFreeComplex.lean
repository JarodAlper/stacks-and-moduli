module

public import StacksAndModuli.API.FiniteFreeComplexExactExpectedRanks
public import StacksAndModuli.API.PartialProjectiveResolutionFiniteFree
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksProject.Algebra.ColimitsAndMapsOfFinitePresentationII.«lemma-flat-finite-presentation-limit-flat»

/-!
# Finite free complexes from partial projective resolutions

This file compiles a partial projective resolution whose hidden projective terms are
certified finite free, and whose terminal syzygy is finite free, into a bounded matrix
complex in chosen standard bases.  The intermediate augmentation is retained long enough
to prove exactness, but is not part of `Matrix.FiniteFreeComplex` itself.

For a matrix cokernel, an anchored resolution remembers that its tail starts at the kernel
of the supplied matrix.  After flat coefficient extension and freeness of the terminal
syzygy, the compiler uses the canonical tensor-product bases on the first two terms.  Thus
the degree-zero differential of the resulting complex is literally the coefficientwise
image of the supplied matrix, rather than merely conjugate to it.

Main declarations:

* `Module.IsPartialProjectiveResolution.append`;
* `Module.IsPartialProjectiveResolution.AnchoredMatrixCokernel`;
* `Matrix.FiniteFreeComplex.AnchoredAt`;
* `Matrix.FiniteFreeComplex.IsResolutionOf`;
* `Module.IsPartialProjectiveResolution.exists_finiteFreeComplex`;
* `Module.IsPartialProjectiveResolution.AnchoredMatrixCokernel.
    exists_finiteFreeComplex_baseChange`;
* `Module.IsPartialProjectiveResolution.AnchoredMatrixCokernel.
    exists_finiteFreeComplex_away`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u v

namespace Module.IsPartialProjectiveResolution

/-- Concatenate two partial projective resolutions at their common syzygy. -/
theorem append
    {R : Type u} [CommRing R]
    {e d : ℕ} {M K L : Type v}
    [AddCommGroup M] [Module R M]
    [AddCommGroup K] [Module R K]
    [AddCommGroup L] [Module R L]
    (h₁ : Module.IsPartialProjectiveResolution R e M K)
    (h₂ : Module.IsPartialProjectiveResolution R d K L) :
    Module.IsPartialProjectiveResolution R (e + d + 1) M L := by
  induction h₂ with
  | zero f hf i hi hexact =>
      simpa only [Nat.add_zero] using
        Module.IsPartialProjectiveResolution.succ h₁ f hf i hi hexact
  | @succ d K _ _ L' _ _ L _ _ h₂ F _ _ _ f hf i hi hexact ih =>
      convert Module.IsPartialProjectiveResolution.succ (ih h₁) f hf i hi hexact using 1;
        omega

/-- Finite-free certificates concatenate along with their partial resolutions. -/
theorem HasFiniteFreeTerms.append
    {R : Type u} [CommRing R]
    {e d : ℕ} {M K L : Type v}
    [AddCommGroup M] [Module R M]
    [AddCommGroup K] [Module R K]
    [AddCommGroup L] [Module R L]
    {h₁ : Module.IsPartialProjectiveResolution R e M K}
    {h₂ : Module.IsPartialProjectiveResolution R d K L}
    (hh₁ : h₁.HasFiniteFreeTerms) (hh₂ : h₂.HasFiniteFreeTerms) :
    (h₁.append h₂).HasFiniteFreeTerms := by
  induction hh₂ with
  | zero f hf i hi hexact =>
      simpa only [append, Nat.add_zero] using
        HasFiniteFreeTerms.succ hh₁ f hf i hi hexact
  | succ hh₂ f hf i hi hexact ih =>
      simpa only [append] using
        HasFiniteFreeTerms.succ (ih hh₁) f hf i hi hexact

/-- Flat coefficient extension preserves the certificate that all hidden resolution terms
are finite free. -/
theorem HasFiniteFreeTerms.baseChange
    {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
    [Module.Flat R S]
    {e : ℕ} {M K : Type u}
    [AddCommGroup M] [Module R M]
    [AddCommGroup K] [Module R K]
    {h : Module.IsPartialProjectiveResolution R e M K}
    (hh : h.HasFiniteFreeTerms) :
    (h.baseChange S).HasFiniteFreeTerms := by
  induction hh with
  | @zero M _ _ K _ _ F _ _ _ _ f hf i hi hexact =>
      have hsurj : Function.Surjective (f.baseChange S) := by
        rw [LinearMap.baseChange_eq_ltensor]
        exact LinearMap.lTensor_surjective S hf
      have hinj : Function.Injective (i.baseChange S) := by
        rw [LinearMap.baseChange_eq_ltensor]
        exact Module.Flat.lTensor_preserves_injective_linearMap i hi
      have hex : Function.Exact (i.baseChange S) (f.baseChange S) := by
        rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
        exact Module.Flat.lTensor_exact S (LinearMap.exact_iff.mpr hexact.symm)
      simpa only [Module.IsPartialProjectiveResolution.baseChange] using
        HasFiniteFreeTerms.zero (f.baseChange S) hsurj
          (i.baseChange S) hinj (LinearMap.exact_iff.mp hex).symm
  | @succ e M _ _ K' _ _ K _ _ h hh F _ _ _ _ f hf i hi hexact ih =>
      have hsurj : Function.Surjective (f.baseChange S) := by
        rw [LinearMap.baseChange_eq_ltensor]
        exact LinearMap.lTensor_surjective S hf
      have hinj : Function.Injective (i.baseChange S) := by
        rw [LinearMap.baseChange_eq_ltensor]
        exact Module.Flat.lTensor_preserves_injective_linearMap i hi
      have hex : Function.Exact (i.baseChange S) (f.baseChange S) := by
        rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
        exact Module.Flat.lTensor_exact S (LinearMap.exact_iff.mpr hexact.symm)
      simpa only [Module.IsPartialProjectiveResolution.baseChange] using
        HasFiniteFreeTerms.succ ih (f.baseChange S) hsurj
          (i.baseChange S) hinj (LinearMap.exact_iff.mp hex).symm

/-- A partial resolution anchored at a matrix cokernel consists of a finite-free tail
starting at the kernel of the supplied matrix.  Appending it to the canonical first two
covers gives a resolution of the concrete matrix cokernel. -/
structure AnchoredMatrixCokernel
    {R : Type u} [CommRing R] {m n d : ℕ}
    (G : Matrix (Fin n) (Fin m) R)
    (K : Type u) [AddCommGroup K] [Module R K] : Prop where
  tail : Module.IsPartialProjectiveResolution R d
    (LinearMap.ker (Matrix.toLin' G)) K
  tail_hasFiniteFreeTerms : tail.HasFiniteFreeTerms

/-- A fixed choice of the canonical first two finite-free covers of a matrix cokernel. -/
theorem matrixCokernelFirstTwoSteps
    {R : Type u} [CommRing R] {m n : ℕ}
    (G : Matrix (Fin n) (Fin m) R) :
    Module.IsPartialProjectiveResolution R 1
      ((Fin n → R) ⧸ LinearMap.range (Matrix.toLin' G))
      (LinearMap.ker (Matrix.toLin' G)) :=
  (matrixCokernel_firstTwoSteps G).choose

/-- The fixed first two covers of a matrix cokernel have finite-free hidden terms. -/
theorem matrixCokernelFirstTwoSteps_hasFiniteFreeTerms
    {R : Type u} [CommRing R] {m n : ℕ}
    (G : Matrix (Fin n) (Fin m) R) :
    (matrixCokernelFirstTwoSteps G).HasFiniteFreeTerms :=
  (matrixCokernel_firstTwoSteps G).choose_spec

namespace AnchoredMatrixCokernel

variable {R : Type u} [CommRing R] {m n d : ℕ}
variable {G : Matrix (Fin n) (Fin m) R}
variable {K : Type u} [AddCommGroup K] [Module R K]

/-- The full partial resolution of the concrete matrix cokernel underlying an anchored
resolution. -/
theorem toResolution
    (h : AnchoredMatrixCokernel (d := d) G K) :
    Module.IsPartialProjectiveResolution R (d + 2)
      ((Fin n → R) ⧸ LinearMap.range (Matrix.toLin' G)) K := by
  convert (matrixCokernelFirstTwoSteps G).append h.tail using 1 <;> omega

/-- Every hidden term of the full matrix-cokernel resolution is finite free. -/
theorem toResolution_hasFiniteFreeTerms
    (h : AnchoredMatrixCokernel (d := d) G K) :
    (toResolution (d := d) h).HasFiniteFreeTerms := by
  have hh := (matrixCokernelFirstTwoSteps_hasFiniteFreeTerms G).append
    h.tail_hasFiniteFreeTerms
  convert hh using 1 <;> omega

end AnchoredMatrixCokernel

end Module.IsPartialProjectiveResolution

namespace Module

/-- Over a Noetherian ring, a matrix cokernel has anchored finite-free partial resolutions
with tails of arbitrary prescribed length. -/
theorem exists_anchoredMatrixCokernel_finiteFree
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {m n : ℕ} (G : Matrix (Fin n) (Fin m) R) (d : ℕ) :
    ∃ (K : Type u) (_ : AddCommGroup K) (_ : Module R K)
      (_ : Module.Finite R K),
      Module.IsPartialProjectiveResolution.AnchoredMatrixCokernel
        (d := d) G K := by
  obtain ⟨K, _, _, _, h, hh⟩ :=
    Module.exists_isPartialProjectiveResolution_finiteFree
      R (LinearMap.ker (Matrix.toLin' G)) d
  exact ⟨K, inferInstance, inferInstance, inferInstance, ⟨h, hh⟩⟩

end Module

namespace Matrix.FiniteFreeComplex

variable {R : Type u} [CommRing R]

/-- The finite free complex concentrated in degree zero. -/
def degreeZero (r : ℕ) : Matrix.FiniteFreeComplex R where
  termRank
    | 0 => r
    | _ + 1 => 0
  differential _ := 0
  differential_sq _ := by simp

@[simp]
theorem degreeZero_termRank_zero (r : ℕ) :
    (degreeZero (R := R) r).termRank 0 = r :=
  rfl

@[simp]
theorem degreeZero_termRank_succ (r i : ℕ) :
    (degreeZero (R := R) r).termRank (i + 1) = 0 :=
  rfl

@[simp]
theorem degreeZero_differential (r i : ℕ) :
    (degreeZero (R := R) r).differential i = 0 :=
  rfl

/-- Prepend a standard finite free term and one differential to a finite free complex. -/
def cons (C : Matrix.FiniteFreeComplex R) (r : ℕ)
    (B : Matrix (Fin r) (Fin (C.termRank 0)) R)
    (hsq : B * C.differential 0 = 0) : Matrix.FiniteFreeComplex R where
  termRank
    | 0 => r
    | i + 1 => C.termRank i
  differential
    | 0 => B
    | i + 1 => C.differential i
  differential_sq
    | 0 => hsq
    | i + 1 => C.differential_sq i

@[simp]
theorem cons_termRank_zero (C : Matrix.FiniteFreeComplex R) (r : ℕ)
    (B : Matrix (Fin r) (Fin (C.termRank 0)) R) (hsq) :
    (C.cons r B hsq).termRank 0 = r :=
  rfl

@[simp]
theorem cons_termRank_succ (C : Matrix.FiniteFreeComplex R) (r : ℕ)
    (B : Matrix (Fin r) (Fin (C.termRank 0)) R) (hsq) (i : ℕ) :
    (C.cons r B hsq).termRank (i + 1) = C.termRank i :=
  rfl

@[simp]
theorem cons_differential_zero (C : Matrix.FiniteFreeComplex R) (r : ℕ)
    (B : Matrix (Fin r) (Fin (C.termRank 0)) R) (hsq) :
    (C.cons r B hsq).differential 0 = B :=
  rfl

@[simp]
theorem cons_differential_succ (C : Matrix.FiniteFreeComplex R) (r : ℕ)
    (B : Matrix (Fin r) (Fin (C.termRank 0)) R) (hsq) (i : ℕ) :
    (C.cons r B hsq).differential (i + 1) = C.differential i :=
  rfl

/-- A finite free complex with two further terms whose first differential is a specified
matrix.  Keeping the two `cons` operations visible makes the first two term ranks and the
degree-zero differential definitionally fixed. -/
structure AnchoredAt {m n : ℕ} (G : Matrix (Fin n) (Fin m) R) where
  tail : Matrix.FiniteFreeComplex R
  nextDifferential : Matrix (Fin m) (Fin (tail.termRank 0)) R
  next_sq : nextDifferential * tail.differential 0 = 0
  anchor_sq : G * nextDifferential = 0

namespace AnchoredAt

variable {m n : ℕ} {G : Matrix (Fin n) (Fin m) R}

/-- The finite free complex obtained by adjoining the specified first differential and the
next differential to the stored tail. -/
def toFiniteFreeComplex (A : AnchoredAt G) : Matrix.FiniteFreeComplex R :=
  (A.tail.cons m A.nextDifferential A.next_sq).cons n G A.anchor_sq

@[simp]
theorem toFiniteFreeComplex_termRank_zero (A : AnchoredAt G) :
    A.toFiniteFreeComplex.termRank 0 = n :=
  rfl

@[simp]
theorem toFiniteFreeComplex_termRank_one (A : AnchoredAt G) :
    A.toFiniteFreeComplex.termRank 1 = m :=
  rfl

@[simp]
theorem toFiniteFreeComplex_differential_zero (A : AnchoredAt G) :
    A.toFiniteFreeComplex.differential 0 = G :=
  rfl

@[simp]
theorem toFiniteFreeComplex_differential_one (A : AnchoredAt G) :
    A.toFiniteFreeComplex.differential 1 = A.nextDifferential :=
  rfl

end AnchoredAt

/-- A finite free complex together with a surjective augmentation, exact at degree zero. -/
structure IsResolutionOf (C : Matrix.FiniteFreeComplex R) (N : ℕ)
    {M : Type v} [AddCommGroup M] [Module R M]
    (q : (Fin (C.termRank 0) → R) →ₗ[R] M) : Prop where
  bounded : C.IsBoundedAbove N
  exact : C.IsExactInPositiveDegreesUpTo N
  augmentation_surjective : Function.Surjective q
  exact_augmentation : Function.Exact
    (Matrix.toLin' (C.differential 0)) q

/-- Prepending a term shifts a bounded complex's upper bound by one. -/
theorem IsBoundedAbove.cons
    {C : Matrix.FiniteFreeComplex R} {N r : ℕ}
    {B : Matrix (Fin r) (Fin (C.termRank 0)) R} {hsq}
    (h : C.IsBoundedAbove N) :
    (C.cons r B hsq).IsBoundedAbove (N + 1) := by
  intro i hi
  cases i with
  | zero => omega
  | succ i =>
      rw [cons_termRank_succ]
      exact h i (by omega)

/-- Exactness at the newly inserted term and exactness of the old complex imply exactness
of the prepended complex. -/
theorem IsExactInPositiveDegreesUpTo.cons
    {C : Matrix.FiniteFreeComplex R} {N r : ℕ}
    {B : Matrix (Fin r) (Fin (C.termRank 0)) R} {hsq}
    (h : C.IsExactInPositiveDegreesUpTo N)
    (hzero : Function.Exact
      (Matrix.toLin' (C.differential 0)) (Matrix.toLin' B)) :
    (C.cons r B hsq).IsExactInPositiveDegreesUpTo (N + 1) := by
  intro i hi
  cases i with
  | zero =>
      change Function.Exact
        (Matrix.toLin' (C.differential 0)) (Matrix.toLin' B)
      exact hzero
  | succ i =>
      change Function.Exact
        (Matrix.toLin' (C.differential (i + 1)))
        (Matrix.toLin' (C.differential i))
      exact h i (by omega)

/-- A chosen basis identifies a finite free module with the degree-zero term of a complex
concentrated in degree zero. -/
theorem degreeZero_isResolutionOf
    {K : Type v} [AddCommGroup K] [Module R K]
    {r : ℕ} (b : Module.Basis (Fin r) R K) :
    (degreeZero (R := R) r).IsResolutionOf 0
      b.equivFun.symm.toLinearMap := by
  refine ⟨?_, ?_, b.equivFun.symm.surjective, ?_⟩
  · intro i hi
    cases i with
    | zero => omega
    | succ i => exact degreeZero_termRank_succ r i
  · intro i hi
    omega
  · change Function.Exact
      (0 : (Fin 0 → R) →ₗ[R] (Fin r → R))
      b.equivFun.symm.toLinearMap
    exact (LinearMap.exact_zero_iff_injective (Fin 0 → R)
      b.equivFun.symm.toLinearMap).mpr b.equivFun.symm.injective

/-- Prepending one finite-free cover to a resolved augmentation gives a new resolved
augmentation. -/
theorem IsResolutionOf.cons_linearEquiv
    {C : Matrix.FiniteFreeComplex R} {N : ℕ}
    {K : Type v} [AddCommGroup K] [Module R K]
    {q : (Fin (C.termRank 0) → R) →ₗ[R] K}
    (hC : C.IsResolutionOf N q)
    {M F : Type v}
    [AddCommGroup M] [Module R M]
    [AddCommGroup F] [Module R F]
    {r : ℕ} (e : F ≃ₗ[R] (Fin r → R))
    (f : F →ₗ[R] M) (hf : Function.Surjective f)
    (i : K →ₗ[R] F) (hi : Function.Injective i)
    (hexact : LinearMap.range i = LinearMap.ker f) :
    ∃ hsq :
        LinearMap.toMatrix' ((e.toLinearMap.comp i).comp q) *
          C.differential 0 = 0,
      IsResolutionOf
        (C.cons r (LinearMap.toMatrix' ((e.toLinearMap.comp i).comp q)) hsq)
        (N + 1) (f.comp e.symm.toLinearMap) := by
  let j : K →ₗ[R] (Fin r → R) := e.toLinearMap.comp i
  let q' : (Fin r → R) →ₗ[R] M := f.comp e.symm.toLinearMap
  let B : Matrix (Fin r) (Fin (C.termRank 0)) R :=
    LinearMap.toMatrix' (j.comp q)
  have hsq : B * C.differential 0 = 0 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', map_zero,
      LinearMap.comp_assoc]
    rw [hC.exact_augmentation.linearMap_comp_eq_zero, LinearMap.comp_zero]
  have hj : Function.Injective j := e.injective.comp hi
  have hshort : Function.Exact i f :=
    LinearMap.exact_iff.mpr hexact.symm
  have hjf : Function.Exact j q' := by
    exact (e.conj_exact_iff_exact i f).mpr hshort
  have hzero : Function.Exact
      (Matrix.toLin' (C.differential 0)) (Matrix.toLin' B) := by
    rw [Matrix.toLin'_toMatrix']
    exact (hj.comp_exact_iff_exact).mpr hC.exact_augmentation
  refine ⟨hsq, ?_⟩
  refine
    { bounded := hC.bounded.cons
      exact := hC.exact.cons hzero
      augmentation_surjective := hf.comp e.symm.surjective
      exact_augmentation := ?_ }
  change Function.Exact (Matrix.toLin' B) q'
  rw [Matrix.toLin'_toMatrix']
  exact (hC.augmentation_surjective.comp_exact_iff_exact).mpr hjf

/-- A basis supplies the coordinate equivalence needed to prepend a finite-free cover. -/
theorem IsResolutionOf.exists_cons
    {C : Matrix.FiniteFreeComplex R} {N : ℕ}
    {K : Type v} [AddCommGroup K] [Module R K]
    {q : (Fin (C.termRank 0) → R) →ₗ[R] K}
    (hC : C.IsResolutionOf N q)
    {M F : Type v}
    [AddCommGroup M] [Module R M]
    [AddCommGroup F] [Module R F]
    {r : ℕ} (b : Module.Basis (Fin r) R F)
    (f : F →ₗ[R] M) (hf : Function.Surjective f)
    (i : K →ₗ[R] F) (hi : Function.Injective i)
    (hexact : LinearMap.range i = LinearMap.ker f) :
    ∃ (C' : Matrix.FiniteFreeComplex R)
      (q' : (Fin (C'.termRank 0) → R) →ₗ[R] M),
      C'.IsResolutionOf (N + 1) q' := by
  let e : F ≃ₗ[R] (Fin r → R) := b.equivFun
  let q' : (Fin r → R) →ₗ[R] M := f.comp e.symm.toLinearMap
  let B : Matrix (Fin r) (Fin (C.termRank 0)) R :=
    LinearMap.toMatrix' ((e.toLinearMap.comp i).comp q)
  obtain ⟨hsq, hC'⟩ := hC.cons_linearEquiv e f hf i hi hexact
  exact ⟨C.cons r B hsq, q', hC'⟩

end Matrix.FiniteFreeComplex

namespace Module.IsPartialProjectiveResolution

open Matrix.FiniteFreeComplex

variable {R : Type u} [CommRing R]

/-- Extend an already matrix-compiled resolution of the terminal syzygy backwards through
all finite-free covers in a partial projective resolution. -/
theorem HasFiniteFreeTerms.extend_finiteFreeComplex
    {e : ℕ} {M K : Type v}
    [AddCommGroup M] [Module R M]
    [AddCommGroup K] [Module R K]
    {h : Module.IsPartialProjectiveResolution R e M K}
    (hh : h.HasFiniteFreeTerms) :
    ∀ (C : Matrix.FiniteFreeComplex R) (N : ℕ)
      (q : (Fin (C.termRank 0) → R) →ₗ[R] K),
      C.IsResolutionOf N q →
      ∃ (C' : Matrix.FiniteFreeComplex R)
        (q' : (Fin (C'.termRank 0) → R) →ₗ[R] M),
        C'.IsResolutionOf (N + e + 1) q' := by
  induction hh with
  | @zero M _ _ K _ _ F _ _ _ _ f hf i hi hexact =>
      intro C N q hC
      let b := (Module.Free.chooseBasis R F).reindex (Fintype.equivFin _)
      simpa only [Nat.add_zero] using hC.exists_cons b f hf i hi hexact
  | @succ e M _ _ K' _ _ K _ _ h hh F _ _ _ _ f hf i hi hexact ih =>
      intro C N q hC
      let b := (Module.Free.chooseBasis R F).reindex (Fintype.equivFin _)
      obtain ⟨D, qD, hD⟩ := hC.exists_cons b f hf i hi hexact
      obtain ⟨C', q', hC'⟩ := ih D (N + 1) qD hD
      refine ⟨C', q', ?_⟩
      convert hC' using 1 <;> omega

/-- Compile a finite-free partial projective resolution with finite-free final syzygy into
a bounded exact matrix complex resolving the original module. -/
theorem exists_finiteFreeComplex
    {e : ℕ} {M K : Type v}
    [AddCommGroup M] [Module R M]
    [AddCommGroup K] [Module R K]
    (h : Module.IsPartialProjectiveResolution R e M K)
    (hh : h.HasFiniteFreeTerms)
    [Module.Free R K] [Module.Finite R K] :
    ∃ (C : Matrix.FiniteFreeComplex R)
      (q : (Fin (C.termRank 0) → R) →ₗ[R] M),
      C.IsResolutionOf (e + 1) q := by
  let r := Fintype.card (Module.Free.ChooseBasisIndex R K)
  let b : Module.Basis (Fin r) R K :=
    (Module.Free.chooseBasis R K).reindex (Fintype.equivFin _)
  let C₀ := Matrix.FiniteFreeComplex.degreeZero (R := R) r
  let q₀ := b.equivFun.symm.toLinearMap
  have h₀ : C₀.IsResolutionOf 0 q₀ := by
    simpa only [C₀, q₀, Fintype.card_fin] using
      Matrix.FiniteFreeComplex.degreeZero_isResolutionOf b
  obtain ⟨C, q, hC⟩ := hh.extend_finiteFreeComplex C₀ 0 q₀ h₀
  refine ⟨C, q, ?_⟩
  convert hC using 1 <;> omega

end Module.IsPartialProjectiveResolution

namespace Module.IsPartialProjectiveResolution.AnchoredMatrixCokernel

open TensorProduct

/-- After flat coefficient extension makes the terminal syzygy free, an anchored matrix
cokernel resolution compiles to a bounded exact finite free complex whose degree-zero
differential is literally the coefficientwise image of the anchoring matrix. -/
theorem exists_finiteFreeComplex_baseChange
    {R T : Type u} [CommRing R] [CommRing T] [Algebra R T]
    [Module.Flat R T]
    {m n d : ℕ} {G : Matrix (Fin n) (Fin m) R}
    {K : Type u} [AddCommGroup K] [Module R K] [Module.Finite R K]
    (h : AnchoredMatrixCokernel (d := d) G K)
    [Module.Free T (T ⊗[R] K)] :
    ∃ A : Matrix.FiniteFreeComplex.AnchoredAt
        (G.map (algebraMap R T)),
      A.toFiniteFreeComplex.IsBoundedAbove (d + 3) ∧
        A.toFiniteFreeComplex.IsExactInPositiveDegreesUpTo (d + 3) := by
  let g : (Fin m → R) →ₗ[R] (Fin n → R) := Matrix.toLin' G
  let GT : Matrix (Fin n) (Fin m) T := G.map (algebraMap R T)
  let gT : (Fin m → T) →ₗ[T] (Fin n → T) := Matrix.toLin' GT
  have hhT : (h.tail.baseChange T).HasFiniteFreeTerms :=
    h.tail_hasFiniteFreeTerms.baseChange T
  obtain ⟨D, qD, hD⟩ :=
    (h.tail.baseChange T).exists_finiteFreeComplex hhT
  let eM := TensorProduct.piScalarRight R T T (Fin m)
  let eN := TensorProduct.piScalarRight R T T (Fin n)
  let j : (T ⊗[R] LinearMap.ker g) →ₗ[T] (Fin m → T) :=
    eM.toLinearMap.comp ((LinearMap.ker g).subtype.baseChange T)
  have hjBase : Function.Injective
      ((LinearMap.ker g).subtype.baseChange T) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _
      (Submodule.injective_subtype _)
  have hj : Function.Injective j := eM.injective.comp hjBase
  have hbase : Function.Exact
      ((LinearMap.ker g).subtype.baseChange T) (g.baseChange T) := by
    rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_exact T (LinearMap.exact_subtype_ker_map g)
  have hjg : Function.Exact j gT := by
    exact (Function.Exact.iff_of_ladder_linearEquiv
      (f₁₂ := (LinearMap.ker g).subtype.baseChange T)
      (f₂₃ := g.baseChange T) (g₁₂ := j) (g₂₃ := gT)
      (e₁ := LinearEquiv.refl T (T ⊗[R] LinearMap.ker g))
      (e₂ := eM) (e₃ := eN)
      (by simp only [j, LinearEquiv.refl_toLinearMap,
        LinearMap.comp_id])
      (by
        simpa only [g, gT, GT, eM, eN] using
          (Matrix.piScalarRight_toLin_map (A := T) G).symm)).mpr hbase
  have hjRange : LinearMap.range j = LinearMap.ker gT.rangeRestrict := by
    rw [LinearMap.ker_rangeRestrict]
    exact (LinearMap.exact_iff.mp hjg).symm
  let idM : (Fin m → T) ≃ₗ[T] (Fin m → T) := LinearEquiv.refl T _
  let B₁ : Matrix (Fin m) (Fin (D.termRank 0)) T :=
    LinearMap.toMatrix' ((idM.toLinearMap.comp j).comp qD)
  obtain ⟨hsq₁, hC₁⟩ := hD.cons_linearEquiv idM gT.rangeRestrict
    gT.surjective_rangeRestrict j hj hjRange
  let C₁ := D.cons m B₁ hsq₁
  let q₁ : (Fin m → T) →ₗ[T] LinearMap.range gT :=
    gT.rangeRestrict.comp idM.symm.toLinearMap
  have hC₁' : C₁.IsResolutionOf ((d + 1) + 1) q₁ := hC₁
  let rangeGT := LinearMap.range gT
  let iGT : rangeGT →ₗ[T] (Fin n → T) := rangeGT.subtype
  have hiGT : Function.Injective iGT := Submodule.injective_subtype _
  have hq₁ : iGT.comp q₁ = gT := by
    apply LinearMap.ext
    intro x
    rfl
  have hzero : Function.Exact
      (Matrix.toLin' (C₁.differential 0)) gT := by
    have hz := (hiGT.comp_exact_iff_exact).mpr hC₁'.exact_augmentation
    rw [hq₁] at hz
    exact hz
  have hsq₀ : GT * B₁ = 0 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, map_zero]
    change gT.comp (Matrix.toLin' B₁) = 0
    have hz := hzero.linearMap_comp_eq_zero
    change gT.comp (Matrix.toLin' B₁) = 0 at hz
    exact hz
  let A : Matrix.FiniteFreeComplex.AnchoredAt GT :=
    { tail := D
      nextDifferential := B₁
      next_sq := hsq₁
      anchor_sq := hsq₀ }
  refine ⟨A, ?_, ?_⟩
  · change (C₁.cons n GT hsq₀).IsBoundedAbove (d + 3)
    exact hC₁'.bounded.cons
  · change (C₁.cons n GT hsq₀).IsExactInPositiveDegreesUpTo (d + 3)
    exact hC₁'.exact.cons hzero

/-- Away-localized form of `exists_finiteFreeComplex_baseChange`.  The freeness hypothesis
is accepted on Mathlib's canonical localized module and transported internally to the tensor
product used by `LinearMap.baseChange`. -/
theorem exists_finiteFreeComplex_away
    {R : Type u} [CommRing R]
    {m n d : ℕ} {G : Matrix (Fin n) (Fin m) R}
    {K : Type u} [AddCommGroup K] [Module R K] [Module.Finite R K]
    (h : AnchoredMatrixCokernel (d := d) G K) (a : R)
    (hfree : Module.Free (Localization.Away a)
      (LocalizedModule.Away a K)) :
    ∃ A : Matrix.FiniteFreeComplex.AnchoredAt
        (G.map (algebraMap R (Localization.Away a))),
      A.toFiniteFreeComplex.IsBoundedAbove (d + 3) ∧
        A.toFiniteFreeComplex.IsExactInPositiveDegreesUpTo (d + 3) := by
  let T := Localization.Away a
  let _ : Module.Free T (LocalizedModule.Away a K) := hfree
  let e : LocalizedModule.Away a K ≃ₗ[T] (T ⊗[R] K) :=
    LocalizedModule.equivTensorProduct (Submonoid.powers a) K
  let _ : Module.Free T (T ⊗[R] K) := Module.Free.of_equiv e
  exact h.exists_finiteFreeComplex_baseChange (T := T)

end Module.IsPartialProjectiveResolution.AnchoredMatrixCokernel

end
