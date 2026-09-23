module

public import StacksAndModuli.API.ProjectiveGradedTotal
public import Mathlib.Algebra.DirectSum.Decomposition

/-!
# The internal grading on the total module

`GradedModule.Total M` is definitionally the external direct sum of the pieces of `M`.
This file also presents those summands as submodules of the total module and records the
resulting internal direct-sum decomposition.  The polynomial action respects this grading.

This is the bridge from StacksAndModuli's diagrammatic `GradedModule` to Mathlib's native graded-module
API.  In particular, it lets graded commutative-algebra results such as Stacks Project tag 053C
be applied to `Total M` over an arbitrary commutative coefficient ring.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule.Total

open DirectSum MvPolynomial

variable {R : Type u} [CommRing R] {n : ℕ} (M : GradedModule R n)

/-- The standard action of a nonnegative polynomial degree on an integral module degree. -/
instance natVAddInt : VAdd ℕ ℤ where
  vadd e d := (e : ℤ) + d

/-- Addition of polynomial degrees acts associatively on integral module degrees. -/
instance natAddActionInt : AddAction ℕ ℤ where
  zero_vadd d := by
    change (0 : ℤ) + d = d
    simp
  add_vadd e e' d := by
    change ((e + e' : ℕ) : ℤ) + d = (e : ℤ) + ((e' : ℤ) + d)
    push_cast
    ring

@[simp]
lemma nat_vadd_int (e : ℕ) (d : ℤ) : e +ᵥ d = (e : ℤ) + d := rfl

/-- The degree-`d` summand, regarded as a submodule of the total module. -/
def degreePiece (d : ℤ) : Submodule R (Total M) := LinearMap.range (tof M d)

/-- A graded piece is linearly equivalent to its image in the total module. -/
def pieceLinearEquiv (d : ℤ) : M.obj d ≃ₗ[R] degreePiece M d where
  toFun x := ⟨tof M d x, LinearMap.mem_range_self _ _⟩
  invFun z := tcomp M d z.1
  left_inv x := tcomp_tof M d x
  right_inv z := by
    apply Subtype.ext
    obtain ⟨x, hx⟩ := z.2
    change tof M d (tcomp M d z.1) = z.1
    rw [← hx, tcomp_tof]
  map_add' x y := by
    apply Subtype.ext
    exact map_add (tof M d) x y
  map_smul' r x := by
    apply Subtype.ext
    exact map_smul (tof M d) r x

@[simp]
lemma pieceLinearEquiv_apply (d : ℤ) (x : M.obj d) :
    (pieceLinearEquiv M d x : Total M) = tof M d x := rfl

@[simp]
lemma pieceLinearEquiv_symm_apply (d : ℤ) (x : degreePiece M d) :
    (pieceLinearEquiv M d).symm x = tcomp M d x.1 := rfl

/-- The tautological linear equivalence from the external grading of `Total M` to its
internal degree submodules. -/
def degreeDecompositionEquiv : Total M ≃ₗ[R] ⨁ d : ℤ, degreePiece M d :=
  DirectSum.congrLinearEquiv fun d => pieceLinearEquiv M d

@[simp]
lemma degreeDecompositionEquiv_tof (d : ℤ) (x : M.obj d) :
    degreeDecompositionEquiv M (tof M d x) =
      DirectSum.lof R ℤ (fun e => degreePiece M e) d (pieceLinearEquiv M d x) := by
  exact DirectSum.lmap_lof (fun e => (pieceLinearEquiv M e).toLinearMap) d x

/-- The internal direct-sum decomposition of the total module by its degree pieces. -/
noncomputable instance degreePiece_decomposition :
    DirectSum.Decomposition (degreePiece M) := by
  refine DirectSum.Decomposition.ofLinearMap (degreePiece M)
    (degreeDecompositionEquiv M).toLinearMap ?_ ?_
  · apply DirectSum.linearMap_ext
    intro d
    apply LinearMap.ext
    intro x
    change DirectSum.coeLinearMap (degreePiece M)
      (degreeDecompositionEquiv M (tof M d x)) = tof M d x
    rw [degreeDecompositionEquiv_tof, DirectSum.coeLinearMap_lof]
    rfl
  · apply DirectSum.linearMap_ext
    intro d
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.id_apply,
      DirectSum.coeLinearMap_lof]
    change degreeDecompositionEquiv M x.1 =
      DirectSum.lof R ℤ (fun e => degreePiece M e) d x
    obtain ⟨y, hy⟩ := x.2
    rw [← hy, degreeDecompositionEquiv_tof]
    congr 1
    exact Subtype.ext hy

/-- A homogeneous polynomial sends a pure degree element to the predicted degree. -/
lemma homogeneous_smul_tof {e : ℕ} {p : MvPolynomial (Fin (n + 1)) R}
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R e)
    (d : ℤ) (x : M.obj d) :
    p • tof M d x ∈ degreePiece M ((e : ℤ) + d) := by
  classical
  rw [MvPolynomial.mem_homogeneousSubmodule] at hp
  have hp_sum : p = ∑ b ∈ p.support, monomial b (coeff b p) := MvPolynomial.as_sum p
  rw [hp_sum]
  rw [Finset.sum_smul]
  apply Submodule.sum_mem
  intro b hb
  have hcoeff : coeff b p ≠ 0 := MvPolynomial.mem_support_iff.mp hb
  have hdeg : b.degree = e := by
    rw [degree_eq_weight_one]
    exact hp hcoeff
  have hde : d + (b.degree : ℤ) = (e : ℤ) + d := by omega
  rw [monomial_smul_tof M b (coeff b p) hde x]
  exact ⟨(coeff b p) • (M.mulMono b d ((e : ℤ) + d) hde).hom x, by
    rw [map_smul]⟩

/-- The polynomial grading acts on the internal grading of `Total M`. -/
instance gradedSMul_degreePiece :
    SetLike.GradedSMul
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (degreePiece M) where
  smul_mem := by
    intro e d p x hp hx
    obtain ⟨y, rfl⟩ := hx
    simpa only [nat_vadd_int] using homogeneous_smul_tof M hp d y

end AlgebraicGeometry.ProjectiveSpace.GradedModule.Total

end
