module

public import StacksAndModuli.API.PolynomialVectorMinimalGrowth
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
public import Mathlib.RingTheory.Polynomial.DegreeLT

/-!
# Rank-controlled growth for polynomial-vector subspaces

This file isolates the elementary one-variable rank argument behind the projective-line
module-Gotzmann theorem.  If `V` is a finite-dimensional subspace of polynomial vectors,
its `K[X]`-span has a well-defined finite rank `polynomialSpanRank K I V`.

Three inequalities control forward growth under coordinatewise multiplication by `X`:

* the increments of `V`, `V + XV`, `V + XV + X(V + XV)`, ... are nonincreasing;
* every increment is at least the polynomial-span rank;
* a degree-`< n` slice has dimension at most `n` times the polynomial-span rank.

Consequently, if the first increment is `s` and the first forward span is too large to
fit in a polynomial module of rank `s - 1`, then the next increment is again `s`.  This is
the honest arbitrary-growth extension of the growth-one theorem in
`PolynomialVectorMinimalGrowth`: without the largeness hypothesis, growth by more than one
need not persist.

The rank floor and bounded-slice inequalities are the two substantive PID arguments.  They
are stated separately because they are useful independently in later iterated-growth and
homogeneous-dehomogenization bridges.

Main declarations:

* `Submodule.finrank_forwardSpan_le_add_of_eq_add`;
* `Polynomial.polynomialSpanRank`;
* `Polynomial.finrank_add_polynomialSpanRank_le_finrank_forwardSpan`;
* `Polynomial.finrank_le_polynomialSpanRank_mul_of_le_vectorDegreeLT`;
* `Polynomial.finrank_forwardSpan_xMulVector_eq_add_of_large`.
-/

@[expose] public section

noncomputable section

set_option linter.style.haveILetI false

namespace Submodule

variable {K M : Type*} [DivisionRing K] [AddCommGroup M] [Module K M]

/-- For an injective endomorphism, the successive finite-dimensional forward-span
increments are nonincreasing. -/
theorem finrank_forwardSpan_le_add_of_eq_add
    (V : Submodule K M) [FiniteDimensional K V]
    (f : M →ₗ[K] M) (hf : Function.Injective f) (s : ℕ)
    (hgrowth : Module.finrank K (V.forwardSpan f) =
      Module.finrank K V + s) :
    Module.finrank K ((V.forwardSpan f).forwardSpan f) ≤
      Module.finrank K (V.forwardSpan f) + s := by
  let W := V.forwardSpan f
  letI : FiniteDimensional K (V.map f) := Module.Finite.map V f
  letI : FiniteDimensional K W := by
    dsimp only [W, forwardSpan]
    exact Submodule.finiteDimensional_sup V (V.map f)
  letI : FiniteDimensional K (W.map f) := Module.Finite.map W f
  have hVmap : Module.finrank K (V.map f) = Module.finrank K V :=
    finrank_map_eq_of_injective V f hf
  have hWmap : Module.finrank K (W.map f) = Module.finrank K W :=
    finrank_map_eq_of_injective W f hf
  have hVmap_le : V.map f ≤ W ⊓ W.map f := by
    refine le_inf ?_ ?_
    · exact le_sup_right
    · exact Submodule.map_mono le_sup_left
  have hfinrank_le :
      Module.finrank K (V.map f) ≤
        Module.finrank K (W ⊓ W.map f : Submodule K M) :=
    LinearMap.finrank_le_finrank_of_injective
      (f := Submodule.inclusion hVmap_le)
      (Submodule.inclusion_injective hVmap_le)
  have hdimension := Submodule.finrank_sup_add_finrank_inf_eq W (W.map f)
  have hgrowthW : Module.finrank K W = Module.finrank K V + s := by
    simpa only [W] using hgrowth
  have hsum :
      Module.finrank K (W.forwardSpan f) + Module.finrank K (V.map f) ≤
        Module.finrank K W + Module.finrank K (W.map f) := by
    calc
      Module.finrank K (W.forwardSpan f) + Module.finrank K (V.map f) ≤
          Module.finrank K (W.forwardSpan f) +
            Module.finrank K (W ⊓ W.map f : Submodule K M) :=
        Nat.add_le_add_left hfinrank_le _
      _ = Module.finrank K W + Module.finrank K (W.map f) := by
        simpa only [forwardSpan] using hdimension
  rw [hVmap, hWmap] at hsum
  change Module.finrank K (W.forwardSpan f) ≤ Module.finrank K W + s
  omega

/-- A finite-dimensional subspace of a finite product of copies of a field is detected by
as many coordinate projections as its dimension. -/
theorem exists_coordinate_restriction_injective
    (F I : Type*) [Field F] [Finite I]
    (S : Submodule F (I → F)) [FiniteDimensional F S] :
    ∃ c : Fin (Module.finrank F S) → I,
      Function.Injective
        (LinearMap.pi fun j ↦ (LinearMap.proj (c j)).comp S.subtype) := by
  classical
  letI := Fintype.ofFinite I
  let L : I → Module.Dual F S :=
    fun i ↦ (LinearMap.proj i).comp S.subtype
  have hcommon : (⨅ i, LinearMap.ker (L i)) ≤ ⊥ := by
    intro x hx
    rw [Submodule.mem_bot]
    apply Subtype.ext
    funext i
    have hi := (Submodule.mem_iInf _).1 hx i
    exact (LinearMap.mem_ker.1 hi)
  have hspan : Submodule.span F (Set.range L) = ⊤ := by
    apply top_unique
    intro f _
    exact FiniteDimensional.mem_span_of_iInf_ker_le_ker
      (hcommon.trans bot_le)
  obtain ⟨f, hf_mem, hf_span, -⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq F (Set.range L)
  have hrank :
      Module.finrank F (Submodule.span F (Set.range L)) =
        Module.finrank F S := by
    rw [hspan, _root_.finrank_top, Subspace.dual_finrank_eq]
  let e : Fin (Module.finrank F (Submodule.span F (Set.range L))) ≃
      Fin (Module.finrank F S) := finCongr hrank
  choose c hc using fun j : Fin (Module.finrank F S) ↦ hf_mem (e.symm j)
  have hselected_span :
      Submodule.span F (Set.range fun j ↦ L (c j)) = ⊤ := by
    apply top_unique
    have hle : Submodule.span F (Set.range f) ≤
        Submodule.span F (Set.range fun j ↦ L (c j)) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      apply Submodule.subset_span
      refine ⟨e j, ?_⟩
      simpa using hc (e j)
    rw [hf_span, hspan] at hle
    exact hle
  refine ⟨c, ?_⟩
  intro x y hxy
  have hselected (j : Fin (Module.finrank F S)) :
      L (c j) (x - y) = 0 := by
    have hj := congrFun hxy j
    change x.1 (c j) = y.1 (c j) at hj
    simp [L, hj]
  let ev : Module.Dual F S →ₗ[F] F := LinearMap.applyₗ (R := F) (x - y)
  have hspan_le :
      Submodule.span F (Set.range fun j ↦ L (c j)) ≤ LinearMap.ker ev := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact (LinearMap.mem_ker).2 (by
      simpa only [ev, LinearMap.applyₗ_apply_apply] using hselected j)
  rw [hselected_span] at hspan_le
  apply Subtype.ext
  funext i
  have hi := hspan_le (show L i ∈ (⊤ : Submodule F (Module.Dual F S)) from trivial)
  have hi' := (LinearMap.mem_ker.1 hi)
  change x.1 i - y.1 i = 0 at hi'
  exact sub_eq_zero.mp hi'

end Submodule

namespace Polynomial

variable (K : Type*) [Field K] (I : Type*)

/-- The `K[X]`-submodule generated by a `K`-linear space of polynomial vectors. -/
def polynomialSpan (V : Submodule K (I → K[X])) :
    Submodule K[X] (I → K[X]) :=
  Submodule.span K[X] (V : Set (I → K[X]))

/-- A finite-dimensional space of polynomial vectors generates a finite `K[X]`-module. -/
theorem polynomialSpan_fg (V : Submodule K (I → K[X]))
    [FiniteDimensional K V] :
    (polynomialSpan K I V).FG := by
  exact ((Submodule.fg_iff_finiteDimensional V).2 inferInstance).span

/-- The rank of the polynomial module generated by a space of polynomial vectors. -/
def polynomialSpanRank (V : Submodule K (I → K[X])) : ℕ :=
  Module.finrank K[X] (polynomialSpan K I V)

/-- Adjoining the `X`-multiples of a subspace does not change the polynomial module it
generates. -/
theorem polynomialSpan_forwardSpan_xMulVector
    (V : Submodule K (I → K[X])) :
    polynomialSpan K I (V.forwardSpan (xMulVector K I)) =
      polynomialSpan K I V := by
  let M := polynomialSpan K I V
  have hforward : V.forwardSpan (xMulVector K I) ≤ M.restrictScalars K := by
    apply sup_le
    · intro p hp
      exact Submodule.subset_span hp
    · rw [Submodule.map_le_iff_le_comap]
      intro p hp
      change xMulVector K I p ∈ M
      rw [show xMulVector K I p = (X : K[X]) • p by
        ext i
        rfl]
      exact M.smul_mem X (Submodule.subset_span hp)
  apply le_antisymm
  · rw [polynomialSpan, Submodule.span_le]
    exact fun _ hp ↦ hforward hp
  · apply Submodule.span_mono
    intro p hp
    exact (show V ≤ V.forwardSpan (xMulVector K I) from le_sup_left) hp

/-- The polynomial-span rank is unchanged by one forward-span step. -/
@[simp]
theorem polynomialSpanRank_forwardSpan_xMulVector
    (V : Submodule K (I → K[X])) :
    polynomialSpanRank K I (V.forwardSpan (xMulVector K I)) =
      polynomialSpanRank K I V := by
  change Module.finrank K[X]
      (polynomialSpan K I (V.forwardSpan (xMulVector K I))) =
    Module.finrank K[X] (polynomialSpan K I V)
  rw [polynomialSpan_forwardSpan_xMulVector]

/-- The first `X`-forward-span increment is at least the rank of the polynomial module
generated by the original subspace.

The proof reduces the generated torsion-free finite module over the PID `K[X]` modulo `X`.
The images of `V` generate that fibre, while `V ∩ XV` lies in the kernel. -/
theorem finrank_add_polynomialSpanRank_le_finrank_forwardSpan
    (V : Submodule K (I → K[X])) [FiniteDimensional K V] :
    Module.finrank K V + polynomialSpanRank K I V ≤
      Module.finrank K (V.forwardSpan (xMulVector K I)) := by
  classical
  let M := polynomialSpan K I V
  letI : Module.Finite K[X] M :=
    Module.Finite.iff_fg.mpr (polynomialSpan_fg K I V)
  letI : Module.Free K[X] M :=
    Module.free_of_finite_type_torsion_free'
  let B := Module.basisOfFiniteTypeTorsionFree'
    (R := K[X]) (M := M)
  let m := B.1
  let b : Module.Basis (Fin m) K[X] M := B.2
  let coords : M →ₗ[K] (Fin m → K) :=
    { toFun := fun p j ↦ (b.repr p j).coeff 0
      map_add' := by
        intro p q
        funext j
        simp
      map_smul' := by
        intro c p
        funext j
        rw [← IsScalarTower.algebraMap_smul K[X] c p, map_smul]
        simp [Finsupp.smul_apply, smul_eq_mul] }
  let inclusion : V →ₗ[K] M :=
    { toFun := fun p ↦ ⟨p.1, Submodule.subset_span p.2⟩
      map_add' := by
        intro p q
        ext i
        rfl
      map_smul' := by
        intro c p
        ext i
        rfl }
  let φ : V →ₗ[K] (Fin m → K) := coords.comp inclusion
  have hcoords_smul (a : K[X]) (p : I → K[X]) (hp : p ∈ M) :
      coords ⟨a • p, M.smul_mem a hp⟩ =
        a.coeff 0 • coords ⟨p, hp⟩ := by
    ext j
    change (b.repr (⟨a • p, M.smul_mem a hp⟩ : M) j).coeff 0 =
      a.coeff 0 * (b.repr (⟨p, hp⟩ : M) j).coeff 0
    rw [show (⟨a • p, M.smul_mem a hp⟩ : M) = a • (⟨p, hp⟩ : M) by rfl,
      map_smul]
    simp [Finsupp.smul_apply, smul_eq_mul, Polynomial.mul_coeff_zero]
  have hcoords_range (p : I → K[X]) (hp : p ∈ M) :
      coords ⟨p, hp⟩ ∈ LinearMap.range φ := by
    induction hp using Submodule.span_induction with
    | mem p hp =>
        refine ⟨⟨p, hp⟩, ?_⟩
        rfl
    | zero =>
        change coords (0 : M) ∈ LinearMap.range φ
        rw [map_zero]
        exact (LinearMap.range φ).zero_mem
    | add p q hp hq ihp ihq =>
        change coords ((⟨p, hp⟩ : M) + ⟨q, hq⟩) ∈ LinearMap.range φ
        rw [map_add]
        exact (LinearMap.range φ).add_mem ihp ihq
    | smul a p hp ihp =>
        change p ∈ M at hp
        rw [show coords ⟨a • p, _⟩ = a.coeff 0 • coords ⟨p, hp⟩ from
          hcoords_smul a p hp]
        exact (LinearMap.range φ).smul_mem (a.coeff 0) ihp
  have hcoords_surjective : Function.Surjective coords := by
    intro y
    let c : Fin m →₀ K[X] :=
      Finsupp.equivFunOnFinite.symm (fun j ↦ Polynomial.C (y j))
    let p : M := b.repr.symm c
    refine ⟨p, ?_⟩
    ext j
    simp [coords, p, c]
  have hφ_surjective : Function.Surjective φ := by
    intro y
    obtain ⟨p, hp⟩ := hcoords_surjective y
    obtain ⟨v, hv⟩ := hcoords_range p.1 p.2
    exact ⟨v, hv.trans hp⟩
  let A := V ⊓ V.map (xMulVector K I)
  let toV : A →ₗ[K] V := Submodule.inclusion inf_le_left
  have hzero (z : A) : φ (toV z) = 0 := by
    obtain ⟨p, hp, hzp⟩ := z.2.2
    have hzV : xMulVector K I p ∈ V := by
      rw [hzp]
      exact z.2.1
    have hspanp : p ∈ M := Submodule.subset_span hp
    have hinclusion :
        inclusion ⟨xMulVector K I p, hzV⟩ =
          (X : K[X]) • inclusion ⟨p, hp⟩ := by
      ext i
      rfl
    rw [show toV z = ⟨xMulVector K I p, hzV⟩ by
      apply Subtype.ext
      exact hzp.symm]
    change coords (inclusion ⟨xMulVector K I p, hzV⟩) = 0
    rw [hinclusion]
    have := hcoords_smul X p hspanp
    change coords ((X : K[X]) • inclusion ⟨p, hp⟩) = 0
    rw [show (X : K[X]) • inclusion ⟨p, hp⟩ =
      (⟨(X : K[X]) • p, M.smul_mem X hspanp⟩ : M) by rfl,
      this]
    simp
  let toKer : A →ₗ[K] LinearMap.ker φ :=
    LinearMap.codRestrict (LinearMap.ker φ) toV fun z ↦
      (LinearMap.mem_ker).2 (hzero z)
  have htoKer_injective : Function.Injective toKer := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg
      (fun z : LinearMap.ker φ ↦ ((z.1 : V) : I → K[X])) hxy
  have hinter : Module.finrank K A ≤ Module.finrank K (LinearMap.ker φ) :=
    LinearMap.finrank_le_finrank_of_injective htoKer_injective
  have hmap : Module.finrank K (V.map (xMulVector K I)) =
      Module.finrank K V :=
    Submodule.finrank_map_eq_of_injective V (xMulVector K I)
      (xMulVector_injective K I)
  have hdimension :=
    Submodule.finrank_sup_add_finrank_inf_eq V (V.map (xMulVector K I))
  have hnullity := LinearMap.finrank_range_add_finrank_ker φ
  have hrange : Module.finrank K (LinearMap.range φ) = m := by
    rw [LinearMap.range_eq_top.mpr hφ_surjective, finrank_top,
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hrank : polynomialSpanRank K I V = m := by
    rw [polynomialSpanRank, Module.finrank_eq_card_basis b, Fintype.card_fin]
  dsimp only [A, Submodule.forwardSpan] at hinter hdimension ⊢
  rw [hmap] at hdimension
  rw [hrange] at hnullity
  rw [hrank]
  omega

/-- A degree-bounded slice of a polynomial-vector module has dimension at most the
polynomial-module rank times the length of the degree interval. -/
theorem finrank_le_polynomialSpanRank_mul_of_le_vectorDegreeLT
    [Finite I] (V : Submodule K (I → K[X])) [FiniteDimensional K V]
    (n : ℕ) (hdegree : V ≤ vectorDegreeLT K I n) :
    Module.finrank K V ≤ polynomialSpanRank K I V * n := by
  classical
  letI := Fintype.ofFinite I
  let M := polynomialSpan K I V
  letI : Module.Finite K[X] M :=
    Module.Finite.iff_fg.mpr (polynomialSpan_fg K I V)
  letI : Module.Free K[X] M :=
    Module.free_of_finite_type_torsion_free'
  let B := Module.basisOfFiniteTypeTorsionFree'
    (R := K[X]) (M := M)
  let m := B.1
  let b : Module.Basis (Fin m) K[X] M := B.2
  let extend : (I → K[X]) →ₗ[K[X]] (I → RatFunc K) :=
    LinearMap.pi fun i ↦
      (Algebra.linearMap K[X] (RatFunc K)).comp (LinearMap.proj i)
  let bR : Fin m → I → K[X] := M.subtype ∘ b
  let bF : Fin m → I → RatFunc K :=
    fun j ↦ (algebraMap K[X] (RatFunc K)) ∘ bR j
  have hbR : LinearIndependent K[X] bR := by
    exact b.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hbF : LinearIndependent (RatFunc K) bF := by
    exact (linearIndependent_algebraMap_comp_iff
      (R := K[X]) (S := RatFunc K) (v := bR)).2 hbR
  let S : Submodule (RatFunc K) (I → RatFunc K) :=
    Submodule.span (RatFunc K) (Set.range bF)
  have hSrank : Module.finrank (RatFunc K) S = m := by
    simpa only [S, Fintype.card_fin] using finrank_span_eq_card hbF
  obtain ⟨c, hc⟩ :=
    Submodule.exists_coordinate_restriction_injective (RatFunc K) I S
  have hextend_mem (p : M) : extend p.1 ∈ S := by
    have hp : p ∈ Submodule.span K[X] (Set.range b) := b.mem_span p
    induction hp using Submodule.span_induction with
    | mem q hq =>
        obtain ⟨j, rfl⟩ := hq
        apply Submodule.subset_span
        refine ⟨j, ?_⟩
        ext i
        rfl
    | zero =>
        change extend (0 : I → K[X]) ∈ S
        rw [map_zero]
        exact S.zero_mem
    | add p q hp hq ihp ihq =>
        change extend ((p : I → K[X]) + (q : I → K[X])) ∈ S
        rw [map_add]
        exact S.add_mem ihp ihq
    | smul a p hp ihp =>
        change extend (a • (p : I → K[X])) ∈ S
        rw [map_smul]
        simpa only [IsScalarTower.algebraMap_smul] using
          S.smul_mem (algebraMap K[X] (RatFunc K) a) ihp
  let ψ : V →ₗ[K]
      (Fin (Module.finrank (RatFunc K) S) → Polynomial.degreeLT K n) :=
    { toFun := fun p j ↦
        ⟨p.1 (c j),
          (mem_vectorDegreeLT K I).1 (hdegree p.2) (c j)⟩
      map_add' := by
        intro p q
        funext j
        apply Subtype.ext
        rfl
      map_smul' := by
        intro a p
        funext j
        apply Subtype.ext
        rfl }
  have hψ_injective : Function.Injective ψ := by
    intro p q hpq
    let pM : M := ⟨p.1, Submodule.subset_span p.2⟩
    let qM : M := ⟨q.1, Submodule.subset_span q.2⟩
    have hselected :
        (LinearMap.pi fun j ↦
            (LinearMap.proj (c j)).comp S.subtype)
            (⟨extend p.1, hextend_mem pM⟩ : S) =
          (LinearMap.pi fun j ↦
            (LinearMap.proj (c j)).comp S.subtype)
            (⟨extend q.1, hextend_mem qM⟩ : S) := by
      funext j
      have hj := congrFun hpq j
      have hj' : p.1 (c j) = q.1 (c j) :=
        congrArg Subtype.val hj
      exact congrArg (algebraMap K[X] (RatFunc K)) hj'
    have hextend : extend p.1 = extend q.1 :=
      congrArg Subtype.val (hc hselected)
    apply Subtype.ext
    funext i
    apply RatFunc.algebraMap_injective K
    exact congrFun hextend i
  have hψ :=
    LinearMap.finrank_le_finrank_of_injective hψ_injective
  have htarget :
      Module.finrank K
          (Fin (Module.finrank (RatFunc K) S) → Polynomial.degreeLT K n) =
        Module.finrank (RatFunc K) S * n := by
    rw [Module.finrank_pi_fintype]
    simp [Module.finrank_eq_card_basis (Polynomial.degreeLT.basis K n)]
  have hrank : polynomialSpanRank K I V = m := by
    rw [polynomialSpanRank, Module.finrank_eq_card_basis b, Fintype.card_fin]
  rw [htarget, hSrank, ← hrank] at hψ
  exact hψ

/-- Arbitrary one-variable growth persists for one step once the bounded slice is too
large to have polynomial-module rank strictly below the observed increment.

The largeness condition is essential.  For example, in one coordinate the span of
`1` and `X ^ m` has growth two until the two monomial intervals meet, after which the
growth drops to one. -/
theorem finrank_forwardSpan_xMulVector_eq_add_of_large
    [Finite I] (V : Submodule K (I → K[X])) [FiniteDimensional K V]
    (s n : ℕ)
    (hgrowth : Module.finrank K (V.forwardSpan (xMulVector K I)) =
      Module.finrank K V + s)
    (hdegree : V.forwardSpan (xMulVector K I) ≤ vectorDegreeLT K I n)
    (hlarge : (s - 1) * n <
      Module.finrank K (V.forwardSpan (xMulVector K I))) :
    Module.finrank K
        ((V.forwardSpan (xMulVector K I)).forwardSpan (xMulVector K I)) =
      Module.finrank K (V.forwardSpan (xMulVector K I)) + s := by
  let W := V.forwardSpan (xMulVector K I)
  letI : FiniteDimensional K (V.map (xMulVector K I)) :=
    Module.Finite.map V (xMulVector K I)
  letI : FiniteDimensional K W := by
    dsimp only [W, Submodule.forwardSpan]
    exact Submodule.finiteDimensional_sup V (V.map (xMulVector K I))
  letI : FiniteDimensional K (W.map (xMulVector K I)) :=
    Module.Finite.map W (xMulVector K I)
  letI : FiniteDimensional K (W.forwardSpan (xMulVector K I)) := by
    dsimp only [Submodule.forwardSpan]
    exact Submodule.finiteDimensional_sup W (W.map (xMulVector K I))
  have hfloorV :=
    finrank_add_polynomialSpanRank_le_finrank_forwardSpan K I V
  have hrank_le : polynomialSpanRank K I W ≤ s := by
    rw [polynomialSpanRank_forwardSpan_xMulVector K I V]
    omega
  have hcapacity :
      Module.finrank K W ≤ polynomialSpanRank K I W * n :=
    finrank_le_polynomialSpanRank_mul_of_le_vectorDegreeLT K I W n hdegree
  have hrank : polynomialSpanRank K I W = s := by
    apply le_antisymm hrank_le
    by_contra hnot
    have hlt : polynomialSpanRank K I W < s :=
      Nat.lt_of_not_ge hnot
    have hpred : polynomialSpanRank K I W ≤ s - 1 := by omega
    have hmul : polynomialSpanRank K I W * n ≤ (s - 1) * n :=
      Nat.mul_le_mul_right n hpred
    exact (not_lt_of_ge (hcapacity.trans hmul)) hlarge
  have hlower :=
    finrank_add_polynomialSpanRank_le_finrank_forwardSpan K I W
  have hupper := Submodule.finrank_forwardSpan_le_add_of_eq_add
    V (xMulVector K I) (xMulVector_injective K I) s hgrowth
  dsimp only [W] at hrank hlower ⊢
  rw [hrank] at hlower
  exact le_antisymm hupper hlower

end Polynomial

end
