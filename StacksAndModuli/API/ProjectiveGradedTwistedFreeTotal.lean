module

public import StacksAndModuli.API.ProjectiveGradedTotalDecomposition
public import StacksAndModuli.API.ProjectiveLaurentModel
public import Mathlib.Algebra.Module.FinitePresentation

/-!
# Total modules of finite shifted free graded modules

The total module of a finite direct sum of twists of the polynomial structure module is finite
free over the polynomial ring.  This file gives an explicit linear equivalence: it forgets the
grading by summing the homogeneous components in each coordinate, while its inverse decomposes
each coordinate polynomial into homogeneous pieces.

The finite-presentation consequence supplies the source finiteness needed when a graded image is
treated as a quotient of a finite shifted free module.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule.Total

open DirectSum MvPolynomial

variable {R : Type u} [CommRing R] {n r : ℕ} (a : ℤ)

/-- The rank-`r` free graded module whose generators lie in degree `-a`. -/
abbrev shiftedFree (R : Type u) [CommRing R] (n r : ℕ) (a : ℤ) :
    GradedModule R n := (((structureModule R n).twist a).pow r)

private lemma one_mem_polySubmodule_zero' :
    (1 : MvPolynomial (Fin (n + 1)) R) ∈ polySubmodule R n 0 := by
  rw [polySubmodule_of_nonneg R n (by omega),
    MvPolynomial.mem_homogeneousSubmodule]
  exact MvPolynomial.isHomogeneous_one (Fin (n + 1)) R

private def basisOne : polySubmodule R n (-a + a) := by
  exact ⟨1, by
    rw [show -a + a = 0 by ring]
    exact one_mem_polySubmodule_zero' (R := R) (n := n)⟩

@[simp] private lemma basisOne_val : (basisOne (R := R) (n := n) a).1 = 1 := by
  simp [basisOne]

private def basisVector (i : Fin r) : (shiftedFree R n r a).obj (-a) :=
  Pi.single i (basisOne (R := R) (n := n) a)

@[simp] private lemma basisVector_apply_same (i : Fin r) :
    basisVector (R := R) (n := n) a i i = basisOne (R := R) (n := n) a := by
  simp [basisVector]

@[simp] private lemma basisVector_apply_ne (i j : Fin r) (hij : i ≠ j) :
    basisVector (R := R) (n := n) a i j = 0 := by
  simp [basisVector, hij]

private def basisElem (i : Fin r) : Total (shiftedFree R n r a) :=
  tof (shiftedFree R n r a) (-a) (basisVector (R := R) (n := n) a i)

private def freeToTotal :
    (Fin r → MvPolynomial (Fin (n + 1)) R) →ₗ[MvPolynomial (Fin (n + 1)) R]
      Total (shiftedFree R n r a) where
  toFun v := ∑ i, v i • basisElem (R := R) (n := n) a i
  map_add' v w := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' p v := by
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, smul_smul, smul_eq_mul]

private lemma listExp_monoList (b : Fin (n + 1) →₀ ℕ) : listExp (monoList b) = b := by
  classical
  ext i
  rw [listExp_apply]
  rw [← Multiset.coe_count, monoList_coe, Multiset.count_sum',
    Finset.sum_eq_single i (fun j _ hji ↦ by
      simp [Multiset.count_replicate, hji])
      (fun hi ↦ absurd (Finset.mem_univ i) hi), Multiset.count_replicate]
  simp

private lemma structureModule_mulMono_val (b : Fin (n + 1) →₀ ℕ) (d e : ℤ)
    (h : d + (b.degree : ℤ) = e) (x : (structureModule R n).obj d) :
    (((structureModule R n).mulMono b d e h).hom x).1 =
      MvPolynomial.monomial b 1 * x.1 := by
  rw [mulMono, structureModule_mulList_monomial, listExp_monoList]

private lemma shiftedFree_mulMono_val (b : Fin (n + 1) →₀ ℕ) (d e : ℤ)
    (h : d + (b.degree : ℤ) = e) (x : (shiftedFree R n r a).obj d) (i : Fin r) :
    (((shiftedFree R n r a).mulMono b d e h).hom x i).1 =
      MvPolynomial.monomial b 1 * (x i).1 := by
  rw [mulMono]
  have hpow := pow_mulList ((structureModule R n).twist a) r (monoList b) d e
    (by rw [monoList_length]; exact h) x i
  have htw := twist_mulList (structureModule R n) a (monoList b) d e
    (by rw [monoList_length]; exact h)
  have htwApply := congrArg (fun f ↦ f.hom (x i)) htw
  have htwVal := congrArg Subtype.val htwApply
  have hstruct := structureModule_mulList_monomial (k := R) (n := n)
    (monoList b) (d + a) (e + a) (by rw [monoList_length]; omega) (x i)
  exact (congrArg Subtype.val hpow).trans
    (htwVal.trans (hstruct.trans (congrArg (fun z ↦ MvPolynomial.monomial z 1 * (x i).1)
      (listExp_monoList b))))

private def monomialPiece (b : Fin (n + 1) →₀ ℕ) (c : R) :
    polySubmodule R n (((b.degree : ℕ) : ℤ) - a + a) := by
  exact ⟨MvPolynomial.monomial b c, by
    rw [show ((b.degree : ℕ) : ℤ) - a + a = (b.degree : ℤ) by ring,
      polySubmodule_of_nonneg R n (by omega), MvPolynomial.mem_homogeneousSubmodule]
    exact MvPolynomial.isHomogeneous_monomial c rfl⟩

@[simp] private lemma monomialPiece_val (b : Fin (n + 1) →₀ ℕ) (c : R) :
    (monomialPiece (R := R) (n := n) a b c).1 = MvPolynomial.monomial b c := by
  simp [monomialPiece]

private def monomialVector (b : Fin (n + 1) →₀ ℕ) (c : R) (i : Fin r) :
    (shiftedFree R n r a).obj (((b.degree : ℕ) : ℤ) - a) :=
  Pi.single i (monomialPiece (R := R) (n := n) a b c)

@[simp] private lemma monomialVector_apply_same (b : Fin (n + 1) →₀ ℕ) (c : R)
    (i : Fin r) :
    monomialVector (R := R) (n := n) a b c i i = monomialPiece (R := R) (n := n) a b c := by
  simp [monomialVector]

@[simp] private lemma monomialVector_apply_ne (b : Fin (n + 1) →₀ ℕ) (c : R)
    (i j : Fin r)
    (hij : i ≠ j) : monomialVector (R := R) (n := n) a b c i j = 0 := by
  simp [monomialVector, hij]

private lemma monomial_smul_basisElem (b : Fin (n + 1) →₀ ℕ) (c : R) (i : Fin r) :
    (MvPolynomial.monomial b c : MvPolynomial (Fin (n + 1)) R) •
        basisElem (R := R) (n := n) a i =
      tof (shiftedFree R n r a) (((b.degree : ℕ) : ℤ) - a)
        (monomialVector (R := R) (n := n) a b c i) := by
  rw [basisElem, monomial_smul_tof (shiftedFree R n r a) b c
    (show -a + (b.degree : ℤ) = ((b.degree : ℕ) : ℤ) - a by ring)]
  rw [← map_smul]
  congr 1
  funext j
  apply Subtype.ext
  have hval := shiftedFree_mulMono_val (R := R) (n := n) a b (-a)
    (((b.degree : ℕ) : ℤ) - a)
    (show -a + (b.degree : ℤ) = ((b.degree : ℕ) : ℤ) - a by ring)
    (basisVector (R := R) (n := n) a i) j
  by_cases hij : i = j
  · subst j
    calc
      ((c • ((shiftedFree R n r a).mulMono b (-a)
          (((b.degree : ℕ) : ℤ) - a) (by ring)).hom
            (basisVector (R := R) (n := n) a i)) i).1 =
          c • (((shiftedFree R n r a).mulMono b (-a)
            (((b.degree : ℕ) : ℤ) - a) (by ring)).hom
              (basisVector (R := R) (n := n) a i) i).1 := rfl
      _ = c • (MvPolynomial.monomial b 1 *
          (basisVector (R := R) (n := n) a i i).1) := congrArg (c • ·) hval
      _ = (monomialPiece (R := R) (n := n) a b c).1 := by
        rw [basisVector_apply_same, basisOne_val, monomialPiece_val, mul_one,
          smul_monomial, smul_eq_mul, mul_one]
      _ = (monomialVector (R := R) (n := n) a b c i i).1 := by simp
  · calc
      ((c • ((shiftedFree R n r a).mulMono b (-a)
          (((b.degree : ℕ) : ℤ) - a) (by ring)).hom
            (basisVector (R := R) (n := n) a i)) j).1 =
          c • (((shiftedFree R n r a).mulMono b (-a)
            (((b.degree : ℕ) : ℤ) - a) (by ring)).hom
              (basisVector (R := R) (n := n) a i) j).1 := rfl
      _ = c • (MvPolynomial.monomial b 1 *
          (basisVector (R := R) (n := n) a i j).1) := congrArg (c • ·) hval
      _ = 0 := by simp [hij]
      _ = (monomialVector (R := R) (n := n) a b c i j).1 := by simp [hij]

private def homogeneousPiece (D : ℕ) (p : MvPolynomial (Fin (n + 1)) R)
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R D) :
    polySubmodule R n ((D : ℤ) - a + a) :=
  ⟨p, by
    rw [show (D : ℤ) - a + a = (D : ℤ) by ring,
      polySubmodule_of_nonneg R n (by omega)]
    exact hp⟩

@[simp] private lemma homogeneousPiece_val (D : ℕ) (p : MvPolynomial (Fin (n + 1)) R)
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R D) :
    (homogeneousPiece (R := R) (n := n) a D p hp).1 = p := rfl

private def homogeneousVector (D : ℕ) (p : MvPolynomial (Fin (n + 1)) R)
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R D) (i : Fin r) :
    (shiftedFree R n r a).obj ((D : ℤ) - a) :=
  Pi.single i (homogeneousPiece (R := R) (n := n) a D p hp)

@[simp] private lemma homogeneousVector_apply_same (D : ℕ)
    (p : MvPolynomial (Fin (n + 1)) R)
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R D) (i : Fin r) :
    homogeneousVector (R := R) (n := n) a D p hp i i =
      homogeneousPiece (R := R) (n := n) a D p hp := by
  simp [homogeneousVector]

@[simp] private lemma homogeneousVector_apply_ne (D : ℕ)
    (p : MvPolynomial (Fin (n + 1)) R)
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R D) (i j : Fin r)
    (hij : i ≠ j) : homogeneousVector (R := R) (n := n) a D p hp i j = 0 := by
  simp [homogeneousVector, hij]

private lemma monomial_coeff_mem_homogeneous {D : ℕ}
    (p : MvPolynomial (Fin (n + 1)) R)
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R D)
    (b : Fin (n + 1) →₀ ℕ) :
    MvPolynomial.monomial b (MvPolynomial.coeff b p) ∈
      MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R D := by
  rw [MvPolynomial.mem_homogeneousSubmodule] at hp ⊢
  by_cases hc : MvPolynomial.coeff b p = 0
  · rw [hc, MvPolynomial.monomial_zero]
    exact MvPolynomial.isHomogeneous_zero (R := R) (Fin (n + 1)) D
  · apply MvPolynomial.isHomogeneous_monomial
    rw [degree_eq_weight_one]
    exact hp hc

private lemma homogeneous_smul_basisElem {D : ℕ} (p : MvPolynomial (Fin (n + 1)) R)
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R D) (i : Fin r) :
    p • basisElem (R := R) (n := n) a i =
      tof (shiftedFree R n r a) ((D : ℤ) - a)
        (homogeneousVector (R := R) (n := n) a D p hp i) := by
  classical
  have hp' : p.IsHomogeneous D := hp
  have hterm : ∀ b ∈ p.support,
      (MvPolynomial.monomial b (MvPolynomial.coeff b p) :
          MvPolynomial (Fin (n + 1)) R) • basisElem (R := R) (n := n) a i =
        tof (shiftedFree R n r a) ((D : ℤ) - a)
          (homogeneousVector (R := R) (n := n) a D
            (MvPolynomial.monomial b (MvPolynomial.coeff b p))
            (monomial_coeff_mem_homogeneous p hp b) i) := by
    intro b hb
    have hdeg : b.degree = D := by
      rw [degree_eq_weight_one]
      exact hp' (MvPolynomial.mem_support_iff.mp hb)
    subst D
    simpa [homogeneousVector, homogeneousPiece, monomialVector, monomialPiece] using
      monomial_smul_basisElem (R := R) (n := n) (r := r) a b (MvPolynomial.coeff b p) i
  calc
    p • basisElem (R := R) (n := n) a i =
        (∑ b ∈ p.support, MvPolynomial.monomial b (MvPolynomial.coeff b p)) •
          basisElem (R := R) (n := n) a i := by
      exact congrArg (fun q ↦ q • basisElem (R := R) (n := n) a i)
        (MvPolynomial.as_sum p)
    _ = ∑ b ∈ p.support,
        (MvPolynomial.monomial b (MvPolynomial.coeff b p) :
          MvPolynomial (Fin (n + 1)) R) • basisElem (R := R) (n := n) a i := by
      rw [Finset.sum_smul]
    _ = ∑ b ∈ p.support,
        tof (shiftedFree R n r a) ((D : ℤ) - a)
          (homogeneousVector (R := R) (n := n) a D
            (MvPolynomial.monomial b (MvPolynomial.coeff b p))
            (monomial_coeff_mem_homogeneous p hp b) i) := by
      exact Finset.sum_congr rfl fun b hb ↦ hterm b hb
    _ = tof (shiftedFree R n r a) ((D : ℤ) - a)
        (∑ b ∈ p.support,
          homogeneousVector (R := R) (n := n) a D
            (MvPolynomial.monomial b (MvPolynomial.coeff b p))
            (monomial_coeff_mem_homogeneous p hp b) i) := by
      rw [map_sum]
    _ = tof (shiftedFree R n r a) ((D : ℤ) - a)
        (homogeneousVector (R := R) (n := n) a D p hp i) := by
      congr 1
      funext j
      by_cases hij : i = j
      · subst j
        have hleft :
            (∑ b ∈ p.support,
              homogeneousVector (R := R) (n := n) a D
                (MvPolynomial.monomial b (MvPolynomial.coeff b p))
                (monomial_coeff_mem_homogeneous p hp b) i) i =
              ∑ b ∈ p.support,
                homogeneousPiece (R := R) (n := n) a D
                  (MvPolynomial.monomial b (MvPolynomial.coeff b p))
                  (monomial_coeff_mem_homogeneous p hp b) := by
          rw [Finset.sum_apply]
          exact Finset.sum_congr rfl fun b hb ↦
            homogeneousVector_apply_same (R := R) (n := n) a D _ _ i
        rw [hleft, homogeneousVector_apply_same]
        apply Subtype.ext
        change (polySubmodule R n ((D : ℤ) - a + a)).subtype
          (∑ b ∈ p.support,
            homogeneousPiece (R := R) (n := n) a D
              (MvPolynomial.monomial b (MvPolynomial.coeff b p))
              (monomial_coeff_mem_homogeneous p hp b)) = p
        rw [map_sum]
        exact (Finset.sum_congr rfl fun b hb ↦ rfl).trans
            (MvPolynomial.as_sum p).symm
      · rw [Finset.sum_apply]
        simp only [Finset.sum_const_zero, homogeneousVector_apply_ne (hij := hij)]

private def pieceToFree (d : ℤ) :
    (shiftedFree R n r a).obj d →ₗ[R] (Fin r → MvPolynomial (Fin (n + 1)) R) where
  toFun x i := (x i).1
  map_add' x y := by
    funext i
    rfl
  map_smul' c x := by
    funext i
    rfl

private def totalToFreeLinear :
    Total (shiftedFree R n r a) →ₗ[R] (Fin r → MvPolynomial (Fin (n + 1)) R) :=
  DirectSum.toModule R ℤ (Fin r → MvPolynomial (Fin (n + 1)) R)
    (pieceToFree (R := R) (n := n) a)

@[simp] private lemma totalToFreeLinear_tof (d : ℤ) (x : (shiftedFree R n r a).obj d) :
    totalToFreeLinear (R := R) (n := n) a
      (tof (shiftedFree R n r a) d x) = fun i ↦ (x i).1 := by
  exact DirectSum.toModule_lof (R := R) (M := fun d ↦
    ((shiftedFree R n r a).obj d : Type u))
    (N := Fin r → MvPolynomial (Fin (n + 1)) R) d x

private lemma totalToFreeLinear_monomial_smul (b : Fin (n + 1) →₀ ℕ) (c : R)
    (t : Total (shiftedFree R n r a)) :
    totalToFreeLinear (R := R) (n := n) a
        ((MvPolynomial.monomial b c : MvPolynomial (Fin (n + 1)) R) • t) =
      (MvPolynomial.monomial b c : MvPolynomial (Fin (n + 1)) R) •
        totalToFreeLinear (R := R) (n := n) a t := by
  induction t using DirectSum.induction_on with
  | zero => simp
  | of d x =>
      rw [show DirectSum.of (fun d ↦ ((shiftedFree R n r a).obj d : Type u)) d x =
        tof (shiftedFree R n r a) d x from rfl]
      rw [monomial_smul_tof (shiftedFree R n r a) b c
        (rfl : d + (b.degree : ℤ) = d + (b.degree : ℤ)), map_smul,
        totalToFreeLinear_tof, totalToFreeLinear_tof]
      funext i
      change c • (((shiftedFree R n r a).mulMono b d (d + (b.degree : ℤ)) rfl).hom x i).1 =
        MvPolynomial.monomial b c * (x i).1
      rw [shiftedFree_mulMono_val (R := R) (n := n) a b d
        (d + (b.degree : ℤ)) rfl x i, ← smul_mul_assoc, smul_monomial]
      simp
  | add x y hx hy =>
      simp only [smul_add, map_add, hx, hy]

private lemma totalToFreeLinear_smul (p : MvPolynomial (Fin (n + 1)) R)
    (t : Total (shiftedFree R n r a)) :
    totalToFreeLinear (R := R) (n := n) a (p • t) =
      p • totalToFreeLinear (R := R) (n := n) a t := by
  induction p using MvPolynomial.induction_on' with
  | monomial b c => exact totalToFreeLinear_monomial_smul (R := R) (n := n) a b c t
  | add p q hp hq => simp only [add_smul, map_add, hp, hq]

private def totalToFree :
    Total (shiftedFree R n r a) →ₗ[MvPolynomial (Fin (n + 1)) R]
      (Fin r → MvPolynomial (Fin (n + 1)) R) where
  toFun := totalToFreeLinear (R := R) (n := n) a
  map_add' := (totalToFreeLinear (R := R) (n := n) a).map_add
  map_smul' := totalToFreeLinear_smul (R := R) (n := n) a

@[simp] private lemma totalToFree_tof (d : ℤ) (x : (shiftedFree R n r a).obj d) :
    totalToFree (R := R) (n := n) a (tof (shiftedFree R n r a) d x) =
      fun i ↦ (x i).1 := totalToFreeLinear_tof (R := R) (n := n) a d x

private lemma totalToFree_basisElem (i : Fin r) :
    totalToFree (R := R) (n := n) a (basisElem (R := R) (n := n) a i) =
      Pi.single i (1 : MvPolynomial (Fin (n + 1)) R) := by
  rw [basisElem, totalToFree_tof]
  funext j
  by_cases hij : i = j
  · subst j
    exact (congrArg Subtype.val
      (basisVector_apply_same (R := R) (n := n) a i)).trans
        ((basisOne_val (R := R) (n := n) a).trans
          (Pi.single_eq_same
            (M := fun _ : Fin r ↦ MvPolynomial (Fin (n + 1)) R)
            i (1 : MvPolynomial (Fin (n + 1)) R)).symm)
  · exact (congrArg Subtype.val
      (basisVector_apply_ne (R := R) (n := n) a i j hij)).trans
        (Pi.single_eq_of_ne
          (M := fun _ : Fin r ↦ MvPolynomial (Fin (n + 1)) R)
          (Ne.symm hij) (1 : MvPolynomial (Fin (n + 1)) R)).symm

private lemma totalToFree_freeToTotal
    (v : Fin r → MvPolynomial (Fin (n + 1)) R) :
    totalToFree (R := R) (n := n) a (freeToTotal (R := R) (n := n) a v) = v := by
  change totalToFree (R := R) (n := n) a
      (∑ i, v i • basisElem (R := R) (n := n) a i) = v
  calc
    _ = ∑ i, v i •
        totalToFree (R := R) (n := n) a (basisElem (R := R) (n := n) a i) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun i hi ↦ map_smul _ _ _
    _ = ∑ i, v i • Pi.single i (1 : MvPolynomial (Fin (n + 1)) R) := by
      exact Finset.sum_congr rfl fun i hi ↦ congrArg (v i • ·)
        (totalToFree_basisElem (R := R) (n := n) a i)
    _ = v := (pi_eq_sum_univ' v).symm

private lemma tof_homogeneousVector_eq_single {D : ℕ} {d : ℤ}
    (hdeg : (D : ℤ) - a = d)
    (p : MvPolynomial (Fin (n + 1)) R)
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R D)
    (i : Fin r) (q : polySubmodule R n (d + a)) (hq : q.1 = p) :
    tof (shiftedFree R n r a) ((D : ℤ) - a)
        (homogeneousVector (R := R) (n := n) a D p hp i) =
      tof (shiftedFree R n r a) d (Pi.single i q) := by
  subst d
  congr 1
  funext j
  by_cases hij : i = j
  · subst j
    rw [homogeneousVector_apply_same,
      Pi.single_eq_same (M := fun _ : Fin r ↦
        polySubmodule R n (((D : ℤ) - a) + a))]
    apply Subtype.ext
    exact hq.symm
  · exact (homogeneousVector_apply_ne (R := R) (n := n) a D p hp i j hij).trans
      (Pi.single_eq_of_ne (M := fun _ : Fin r ↦
        polySubmodule R n (((D : ℤ) - a) + a)) (Ne.symm hij) q).symm

private lemma freeToTotal_totalToFree_tof (d : ℤ) (x : (shiftedFree R n r a).obj d) :
    freeToTotal (R := R) (n := n) a
        (totalToFree (R := R) (n := n) a (tof (shiftedFree R n r a) d x)) =
      tof (shiftedFree R n r a) d x := by
  rw [totalToFree_tof]
  change (∑ i, (x i).1 • basisElem (R := R) (n := n) a i) =
    tof (shiftedFree R n r a) d x
  rcases lt_or_ge (d + a) 0 with hneg | hpos
  · have hx : x = 0 := by
      funext i
      apply Subtype.ext
      change (x i).1 = 0
      have hi0 : (x i).1 ∈
          (⊥ : Submodule R (MvPolynomial (Fin (n + 1)) R)) :=
        (le_of_eq (polySubmodule_of_neg R n hneg)) (x i).2
      exact (Submodule.mem_bot R).mp hi0
    calc
      (∑ i, (x i).1 • basisElem (R := R) (n := n) a i) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [show (x i).1 = 0 from congrArg Subtype.val (congrFun hx i), zero_smul]
      _ = tof (shiftedFree R n r a) d x := by
        rw [hx, map_zero]
  · let D : ℕ := (d + a).toNat
    have hD : (D : ℤ) = d + a := by
      exact Int.toNat_of_nonneg hpos
    have hp (i : Fin r) :
        (x i).1 ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R D := by
      exact (le_of_eq (polySubmodule_of_nonneg R n hpos)) (x i).2
    have hdeg : (D : ℤ) - a = d := by omega
    calc
      (∑ i, (x i).1 • basisElem (R := R) (n := n) a i) =
          ∑ i, tof (shiftedFree R n r a) d (Pi.single i (x i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        have h := homogeneous_smul_basisElem (R := R) (n := n) (r := r)
          a (x i).1 (hp i) i
        rw [h]
        exact tof_homogeneousVector_eq_single (R := R) (n := n) (r := r)
          a hdeg (x i).1 (hp i) i (x i) rfl
      _ = tof (shiftedFree R n r a) d (∑ i, Pi.single i (x i)) := by
        rw [map_sum]
      _ = tof (shiftedFree R n r a) d x := by
        congr 1
        exact Finset.univ_sum_single x

private lemma freeToTotal_totalToFree (t : Total (shiftedFree R n r a)) :
    freeToTotal (R := R) (n := n) a (totalToFree (R := R) (n := n) a t) = t := by
  induction t using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | of d x =>
      rw [show DirectSum.of (fun e ↦ ((shiftedFree R n r a).obj e : Type u)) d x =
        tof (shiftedFree R n r a) d x from rfl]
      exact freeToTotal_totalToFree_tof (R := R) (n := n) a d x

private def shiftedFreeLinearEquivAux :
    (Fin r → MvPolynomial (Fin (n + 1)) R) ≃ₗ[MvPolynomial (Fin (n + 1)) R]
      Total (shiftedFree R n r a) where
  toFun := freeToTotal (R := R) (n := n) a
  invFun := totalToFree (R := R) (n := n) a
  left_inv := totalToFree_freeToTotal (R := R) (n := n) a
  right_inv := freeToTotal_totalToFree (R := R) (n := n) a
  map_add' := (freeToTotal (R := R) (n := n) a).map_add
  map_smul' := (freeToTotal (R := R) (n := n) a).map_smul

/-- The standard total-module basis equivalence together with its computation on one
homogeneous component.  Packaging the computation before sealing the construction keeps
the large inverse implementation opaque without losing its usable basis rule. -/
opaque shiftedFreeLinearEquivPackage :
    { e : (Fin r → MvPolynomial (Fin (n + 1)) R) ≃ₗ[
        MvPolynomial (Fin (n + 1)) R] Total (shiftedFree R n r a) //
      ∀ (d : ℤ) (x : (shiftedFree R n r a).obj d),
        e.symm (tof (shiftedFree R n r a) d x) = fun i ↦ (x i).1 } :=
  ⟨shiftedFreeLinearEquivAux (R := R) (n := n) a, by
    intro d x
    change totalToFree (R := R) (n := n) a
        (tof (shiftedFree R n r a) d x) = fun i ↦ (x i).1
    exact totalToFree_tof (R := R) (n := n) a d x⟩

/-- The total module of a finite shifted free graded module is explicitly finite free. -/
noncomputable def shiftedFreeLinearEquiv :
    (Fin r → MvPolynomial (Fin (n + 1)) R) ≃ₗ[MvPolynomial (Fin (n + 1)) R]
      Total (shiftedFree R n r a) :=
  (shiftedFreeLinearEquivPackage (R := R) (n := n) (r := r) a).1

/-- The inverse standard basis equivalence forgets the homogeneous-piece wrapper on a
single totalized component. -/
@[simp]
theorem shiftedFreeLinearEquiv_symm_tof (d : ℤ) (x : (shiftedFree R n r a).obj d) :
    (shiftedFreeLinearEquiv (R := R) (n := n) (r := r) a).symm
        (tof (shiftedFree R n r a) d x) = fun i ↦ (x i).1 :=
  (shiftedFreeLinearEquivPackage (R := R) (n := n) (r := r) a).2 d x

/-- A finite shifted free graded module has finitely presented total module. -/
theorem finitePresentation_shiftedFree
    (R : Type u) [CommRing R] (n r : ℕ) (d₀ : ℤ) :
    Module.FinitePresentation (MvPolynomial (Fin (n + 1)) R)
      (Total (((structureModule R n).twist (-d₀)).pow r)) := by
  exact Module.FinitePresentation.of_equiv
    (shiftedFreeLinearEquiv (R := R) (n := n) (-d₀))

end AlgebraicGeometry.ProjectiveSpace.GradedModule.Total
