module

public import StacksProject.Algebra.LociMaps.«lemma-cokernel-flat»
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Lower semicontinuity of the fibrewise rank

For a map `f : M → N` of finite projective modules, the rank of the fibre
`f ⊗ κ(p)` is a lower semicontinuous function of `p`: the locus where it is at
least `r` is open.

This is the engine of **Theorem A.6.4** part (1): once Theorem A.6.2 provides a
bounded complex `K^•` of finite locally free modules computing the cohomology of
every base change, the book's Equation A.6.5 reads
`h^i(X_y, F_y) = dim K^i ⊗ κ(y) − rank(d^i ⊗ κ(y)) − rank(d^{i-1} ⊗ κ(y))`,
so upper semicontinuity of `y ↦ h^i(X_y, F_y)` is exactly lower semicontinuity of
the two fibrewise ranks proved here, together with local constancy of
`dim K^i ⊗ κ(y)`.

The proof writes the rank-`≥ r` locus as a union, over all `u : R^r → M`, of the
loci where `f ∘ u` is fibrewise injective, each of which is open by Stacks Project
Tag 00O0 (`LinearMap.isOpen_tensorInjectiveLocus`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open Module TensorProduct

namespace AlgebraicGeometry.FibrewiseRank

universe u v w

variable {R : Type u} [CommRing R] {M : Type v} {N : Type w}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Background definition for Theorem A.6.4: the rank of the fibre of `f` at a point
of the spectrum. -/
noncomputable def rankAt (f : M →ₗ[R] N) (p : PrimeSpectrum R) : ℕ :=
  finrank p.residueField (LinearMap.range (f.baseChange p.residueField))

/-- API lemma used in the proof of Theorem A.6.4: the fibre of a finite free module
has the expected dimension. -/
theorem finrank_baseChange_pi (r : ℕ) (p : PrimeSpectrum R) :
    finrank p.residueField (p.residueField ⊗[R] (Fin r → R)) = r := by
  have e : p.residueField ⊗[R] (Fin r → R) ≃ₗ[p.residueField] (Fin r → p.residueField) :=
    TensorProduct.piScalarRight R p.residueField p.residueField (Fin r)
  rw [e.finrank_eq]
  simp

/-- API lemma used in the proof of Theorem A.6.4 (easy direction): if `f ∘ u` is
injective on the fibre at `q` for some `u : R^r → M`, then the fibre of `f` at `q`
has rank at least `r`. -/
theorem le_rankAt_of_mem_tensorInjectiveLocus [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] N) (r : ℕ) (u : (Fin r → R) →ₗ[R] M) {q : PrimeSpectrum R}
    (hq : q ∈ (f ∘ₗ u).tensorInjectiveLocus) : r ≤ rankAt f q := by
  rw [LinearMap.mem_tensorInjectiveLocus] at hq
  have hinj : Function.Injective ((f ∘ₗ u).baseChange q.residueField) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact hq
  have hle : LinearMap.range ((f ∘ₗ u).baseChange q.residueField) ≤
      LinearMap.range (f.baseChange q.residueField) := by
    rw [LinearMap.baseChange_comp]
    exact LinearMap.range_comp_le_range _ _
  have hr : finrank q.residueField
      (LinearMap.range ((f ∘ₗ u).baseChange q.residueField)) = r := by
    rw [LinearMap.finrank_range_of_inj hinj, finrank_baseChange_pi]
  rw [rankAt, ← hr]
  exact Submodule.finrank_mono hle

/-- API lemma used in the proof of Theorem A.6.4 (hard direction): if the fibre of `f`
at `p` has rank at least `r`, then some `u : R^r → M` makes `f ∘ u` injective on the
fibre at `p`. -/
theorem exists_mem_tensorInjectiveLocus_of_le_rankAt
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] N) (r : ℕ) {p : PrimeSpectrum R} (hp : r ≤ rankAt f p) :
    ∃ u : (Fin r → R) →ₗ[R] M, p ∈ (f ∘ₗ u).tensorInjectiveLocus := by
  classical
  -- the fibrewise images of the elements of `M`; they span the fibrewise range
  set v : M → p.residueField ⊗[R] N :=
    fun x ↦ f.baseChange p.residueField (1 ⊗ₜ[R] x) with hv
  have hspan : Submodule.span p.residueField (Set.range v)
      = LinearMap.range (f.baseChange p.residueField) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      exact ⟨1 ⊗ₜ[R] x, rfl⟩
    · rintro y ⟨z, rfl⟩
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul c x =>
        have hcx : f.baseChange p.residueField (c ⊗ₜ[R] x) = c • v x := by
          simp only [hv, LinearMap.baseChange_tmul]
          rw [TensorProduct.smul_tmul']
          simp
        rw [hcx]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
      | add z₁ z₂ h₁ h₂ =>
        rw [map_add]
        exact Submodule.add_mem _ h₁ h₂
  -- extract a linearly independent subfamily spanning the same subspace
  obtain ⟨ι, a, ha_inj, ha_span, ha_li⟩ :=
    exists_linearIndependent' p.residueField v
  -- it is finite, and its cardinality is the fibrewise rank
  have hfin : Finite ι := by
    by_contra hcon
    rw [not_finite_iff_infinite] at hcon
    exact Module.Finite.not_linearIndependent_of_infinite (v ∘ a) ha_li
  have _ : Fintype ι := Fintype.ofFinite ι
  have hcard : Fintype.card ι = rankAt f p := by
    rw [← finrank_span_eq_card ha_li, ha_span, hspan]
    rfl
  -- choose `r` of its members
  obtain ⟨w⟩ : Nonempty (Fin r ↪ ι) := by
    apply Function.Embedding.nonempty_of_card_le
    simpa [hcard] using hp
  set x : Fin r → M := a ∘ w with hx
  have hli : LinearIndependent p.residueField (fun i ↦ v (x i)) :=
    ha_li.comp w w.injective
  -- the induced map out of `R^r`
  refine ⟨(Pi.basisFun R (Fin r)).constr R x, ?_⟩
  rw [LinearMap.mem_tensorInjectiveLocus, ← LinearMap.baseChange_eq_ltensor]
  -- identify the base-changed composite with the map determined by the chosen basis
  set B : Module.Basis (Fin r) p.residueField
      (p.residueField ⊗[R] (Fin r → R)) :=
    (Pi.basisFun R (Fin r)).baseChange p.residueField with hB
  have hagree : (f ∘ₗ (Pi.basisFun R (Fin r)).constr R x).baseChange p.residueField
      = B.constr p.residueField (fun i ↦ v (x i)) := by
    refine B.ext fun i ↦ ?_
    rw [Module.Basis.constr_basis, hB, Module.Basis.baseChange_apply]
    simp [hv]
  rw [hagree]
  exact B.injective_constr_of_linearIndependent hli

/-- API lemma used in the proof of Theorem A.6.4 (the semicontinuity engine of
part (1)): the locus where the fibre of `f` has rank at least `r` is open, i.e. the
fibrewise rank is lower semicontinuous. -/
theorem isOpen_setOf_le_rankAt [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N] (f : M →ₗ[R] N) (r : ℕ) :
    IsOpen {p : PrimeSpectrum R | r ≤ rankAt f p} := by
  rw [isOpen_iff_forall_mem_open]
  intro p hp
  obtain ⟨u, hu⟩ := exists_mem_tensorInjectiveLocus_of_le_rankAt f r hp
  exact ⟨(f ∘ₗ u).tensorInjectiveLocus,
    fun q hq ↦ le_rankAt_of_mem_tensorInjectiveLocus f r u hq,
    LinearMap.isOpen_tensorInjectiveLocus _, hu⟩

end AlgebraicGeometry.FibrewiseRank
