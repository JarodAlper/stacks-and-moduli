module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Data.Sym.Card
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# The dimension of the space of forms of a given degree

Supporting API with no Stacks Project counterpart, developed for §2.3 (Castelnuovo–Mumford
regularity) of *Stacks and Moduli*.

Over a field `K`, the space of homogeneous polynomials of degree `e` in `N` variables has
dimension `C(N + e - 1, e)`; for `N = n+1` variables this is `C(n + e, n)`, the value
`h⁰(ℙⁿ, 𝒪(e))` that appears in Mumford's bound in **Theorem 2.3.8**
(`thm:boundedness-of-regularity`). Mathlib has the two halves — the basis
`MvPolynomial.basisRestrictSupport` of a support-restricted subspace, and the stars-and-bars
count `Sym.card_sym_eq_choose` — but not the combination.

Main declarations:
- `Finsupp.degreeEquivSym`: exponent vectors of total degree `e` are multisets of size `e`.
- `MvPolynomial.finrank_homogeneousSubmodule`: the dimension count.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

/-- Exponent vectors of total degree `e` on an alphabet `α` are the same thing as multisets of
size `e` over `α`. -/
noncomputable def Finsupp.degreeEquivSym (α : Type*) [DecidableEq α] (e : ℕ) :
    ↥{d : α →₀ ℕ | d.degree = e} ≃ Sym α e :=
  Equiv.subtypeEquiv (Multiset.toFinsupp (α := α)).symm.toEquiv fun d => by
    have h2 : ((Multiset.toFinsupp (α := α)).symm.toEquiv d) = Finsupp.toMultiset d := rfl
    have h : Multiset.card ((Multiset.toFinsupp (α := α)).symm.toEquiv d) = d.degree := by
      rw [h2, Finsupp.card_toMultiset, Finsupp.degree_apply]
      rfl
    rw [Set.mem_setOf_eq, h]

noncomputable instance Finsupp.fintypeDegree (α : Type*) [Fintype α] [DecidableEq α] (e : ℕ) :
    Fintype ↥{d : α →₀ ℕ | d.degree = e} :=
  Fintype.ofEquiv _ (Finsupp.degreeEquivSym α e).symm

lemma Finsupp.card_degree (α : Type*) [Fintype α] [DecidableEq α] (e : ℕ) :
    Fintype.card ↥{d : α →₀ ℕ | d.degree = e} = (Fintype.card α + e - 1).choose e := by
  rw [Fintype.card_congr (Finsupp.degreeEquivSym α e), Sym.card_sym_eq_choose]

namespace MvPolynomial

/-- **Stars and bars for forms**: over a field, the space of homogeneous polynomials of degree
`e` in `Fintype.card σ` variables has dimension `C(#σ + e - 1, e)`. -/
lemma finrank_homogeneousSubmodule (σ : Type*) [Fintype σ] [DecidableEq σ] (K : Type u)
    [Field K] (e : ℕ) :
    Module.finrank K (homogeneousSubmodule σ K e) = (Fintype.card σ + e - 1).choose e := by
  rw [homogeneousSubmodule_eq_finsupp_supported]
  rw [show AddMonoidAlgebra.supported K K {d : σ →₀ ℕ | d.degree = e}
      = restrictSupport K {d : σ →₀ ℕ | d.degree = e} from rfl,
    Module.finrank_eq_card_basis (basisRestrictSupport K {d : σ →₀ ℕ | d.degree = e})]
  exact Finsupp.card_degree σ e

/-- The dimension of the space of forms of degree `e` in `n+1` variables is `C(n+e, n)`. -/
lemma finrank_homogeneousSubmodule_fin (n : ℕ) (K : Type u) [Field K] (e : ℕ) :
    Module.finrank K (homogeneousSubmodule (Fin (n + 1)) K e) = (n + e).choose n := by
  rw [finrank_homogeneousSubmodule, Fintype.card_fin]
  have h1 : n + 1 + e - 1 = n + e := by omega
  rw [h1]
  exact (Nat.choose_symm_add (a := n) (b := e)).symm

end MvPolynomial
