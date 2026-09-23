module

public import StacksAndModuli.«Section6.2-Nodal».«part6.2.1-nodes»
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

/-!
# Formal branches of a split node

This file defines the formal branches at a point as the minimal primes of its completed
local ring.  It computes the minimal primes of the standard split-node ring
`k[[x,y]]/(xy)` and concludes that a split node has exactly two formal branches, without
including a choice of node coordinates in the branch type.

The algebraic computation is factored through two reusable equivalences: minimal primes
are invariant under ring equivalence, and minimal primes of a quotient correspond to
minimal primes above the quotient ideal.

## Main definitions

* `Ideal.minimalPrimesEquivOfRingEquiv`: transport of minimal primes across a ring
  equivalence.
* `Ideal.minimalPrimesQuotientEquiv`: the minimal primes of `R/I` are equivalent to the
  minimal primes of `R` above `I`.
* `AlgebraicGeometry.Scheme.nodeAxisIdeal`: one of the two coordinate-axis ideals in
  `k[[x,y]]`.
* `AlgebraicGeometry.Scheme.FormalBranchesAt`: the formal branches at a scheme point.
* `AlgebraicGeometry.Scheme.SplitNodePoints`: the coordinate-free subtype of split-node
  points of a scheme.
* `AlgebraicGeometry.Scheme.SplitNodeBranches`: the total type of formal branches over all
  split-node points.

## Main results

* `AlgebraicGeometry.Scheme.mem_nodeIdeal_minimalPrimes_iff`: the only minimal primes over
  `(xy)` are `(x)` and `(y)`.
* `AlgebraicGeometry.Scheme.nodeIdeal_minimalPrimes_eq_pair`: the corresponding equality
  of sets of ideals.
* `AlgebraicGeometry.Scheme.nodeFormalBranchesEquivFinTwo`: the standard node has two
  formal branches.
* `AlgebraicGeometry.Scheme.formalBranchesEquivOfIso`: formal branches are invariant under
  scheme isomorphism.
* `AlgebraicGeometry.Scheme.IsSplitNodeAt.nonempty_formalBranchesEquivFinTwo`: every split
  node has two formal branches, independently of a choice of coordinates.
* `AlgebraicGeometry.Scheme.splitNodeBranchFiberEquiv`: the fibre of the branch-to-node
  projection over a node is its intrinsic formal-branch type.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open scoped MvPowerSeries

universe u v

namespace Ideal

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A ring equivalence induces an equivalence between the types of minimal prime ideals. -/
noncomputable def minimalPrimesEquivOfRingEquiv (e : R ≃+* S) :
    minimalPrimes R ≃ minimalPrimes S :=
  Equiv.ofBijective
    (fun p ↦ ⟨p.1.map e, by
      have h := Ideal.minimalPrimes_comap_of_surjective
        (f := e.symm.toRingHom) e.symm.surjective p.2
      have hbot : Ideal.comap e.symm.toRingHom (⊥ : Ideal R) = ⊥ :=
        Ideal.comap_bot_of_injective e.symm.toRingHom e.symm.injective
      rw [hbot] at h
      change p.1.comap (e.symm : S →+* R) ∈ minimalPrimes S at h
      exact (Ideal.comap_symm e) ▸ h⟩)
    ⟨fun p q h ↦ by
        apply Subtype.ext
        apply Ideal.comap_injective_of_surjective e.symm e.symm.surjective
        simpa only [Ideal.comap_symm] using congrArg Subtype.val h,
      fun q ↦ by
        let p : minimalPrimes R :=
          ⟨q.1.map e.symm, by
            have h := Ideal.minimalPrimes_comap_of_surjective
              (f := e.toRingHom) e.surjective q.2
            have hbot : Ideal.comap e.toRingHom (⊥ : Ideal S) = ⊥ :=
              Ideal.comap_bot_of_injective e.toRingHom e.injective
            rw [hbot] at h
            change q.1.comap (e : R →+* S) ∈ minimalPrimes R at h
            exact (Ideal.map_symm e).symm ▸ h⟩
        refine ⟨p, Subtype.ext ?_⟩
        change (q.1.map e.symm).map e = q.1
        rw [Ideal.map_symm e, Ideal.map_comap_eq_self_of_equiv]⟩

/-- Under `minimalPrimesEquivOfRingEquiv`, a minimal prime is sent to its ideal-theoretic
image. -/
@[simp]
lemma minimalPrimesEquivOfRingEquiv_apply (e : R ≃+* S) (p : minimalPrimes R) :
    (minimalPrimesEquivOfRingEquiv e p : Ideal S) = p.1.map e :=
  by simp [minimalPrimesEquivOfRingEquiv]

/-- Minimal primes of `R/I` correspond to minimal primes of `R` containing `I`. -/
noncomputable def minimalPrimesQuotientEquiv (I : Ideal R) :
    minimalPrimes (R ⧸ I) ≃ I.minimalPrimes :=
  Equiv.ofBijective
    (fun p ↦ ⟨p.1.comap (Ideal.Quotient.mk I), by
      have h := Ideal.minimalPrimes_comap_of_surjective
        (f := Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective p.2
      rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at h
      exact h⟩)
    ⟨fun p q h ↦ by
        apply Subtype.ext
        exact Ideal.comap_injective_of_surjective
          (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective (congrArg Subtype.val h),
      fun q ↦ by
        have hq : q.1 ∈ Ideal.comap (Ideal.Quotient.mk I) '' minimalPrimes (R ⧸ I) := by
          rw [← Ideal.minimalPrimes_eq_comap]
          exact q.2
        obtain ⟨p, hp, hpq⟩ := hq
        exact ⟨⟨p, hp⟩, Subtype.ext hpq⟩⟩

/-- The quotient-minimal-prime equivalence is given by contraction along the quotient
map. -/
@[simp]
lemma minimalPrimesQuotientEquiv_apply (I : Ideal R) (p : minimalPrimes (R ⧸ I)) :
    (minimalPrimesQuotientEquiv I p : Ideal R) =
      p.1.comap (Ideal.Quotient.mk I) :=
  rfl

end Ideal

namespace AlgebraicGeometry.Scheme

/-- The coordinate-axis ideal `(X_i)` in the two-variable formal power series ring. -/
noncomputable def nodeAxisIdeal (k : Type u) [CommRing k] (i : Fin 2) :
    Ideal (MvPowerSeries (Fin 2) k) :=
  Ideal.span ({MvPowerSeries.X i} : Set (MvPowerSeries (Fin 2) k))

/-- The first coordinate-axis ideal in `k[[x,y]]` is prime. -/
lemma nodeAxisIdeal_zero_isPrime (k : Type u) [Field k] :
    (nodeAxisIdeal k 0).IsPrime := by
  let e := (MvPowerSeries.finSuccEquiv k 1).toRingEquiv
  let _ : IsDomain (MvPowerSeries (Fin 1) k) := NoZeroDivisors.to_isDomain _
  have hmap : Ideal.map e (nodeAxisIdeal k 0) =
      Ideal.span ({PowerSeries.X} :
        Set (PowerSeries (MvPowerSeries (Fin 1) k))) := by
    rw [nodeAxisIdeal, Ideal.map_span]
    simp [e]
  have hprime : (Ideal.map e (nodeAxisIdeal k 0)).IsPrime := by
    rw [hmap]
    exact PowerSeries.span_X_isPrime
  have hcomap :
      (Ideal.comap e (Ideal.map e (nodeAxisIdeal k 0))).IsPrime :=
    hprime.comap e
  simpa only [Ideal.comap_map_of_bijective e e.bijective] using hcomap

/-- The second coordinate-axis ideal in `k[[x,y]]` is prime. -/
lemma nodeAxisIdeal_one_isPrime (k : Type u) [Field k] :
    (nodeAxisIdeal k 1).IsPrime := by
  let e : MvPowerSeries (Fin 2) k ≃+* MvPowerSeries (Fin 2) k :=
    (MvPowerSeries.renameEquiv k (Equiv.swap (0 : Fin 2) (1 : Fin 2))).toRingEquiv
  have hmap : Ideal.map e (nodeAxisIdeal k 1) = nodeAxisIdeal k 0 := by
    simp [nodeAxisIdeal, Ideal.map_span, e]
  have hprime : (Ideal.map e (nodeAxisIdeal k 1)).IsPrime := by
    rw [hmap]
    exact nodeAxisIdeal_zero_isPrime k
  have hcomap :
      (Ideal.comap e (Ideal.map e (nodeAxisIdeal k 1))).IsPrime :=
    hprime.comap e
  simpa only [Ideal.comap_map_of_bijective e e.bijective] using hcomap

/-- Every coordinate-axis ideal in `k[[x,y]]` is prime. -/
lemma nodeAxisIdeal_isPrime (k : Type u) [Field k] (i : Fin 2) :
    (nodeAxisIdeal k i).IsPrime := by
  fin_cases i
  · exact nodeAxisIdeal_zero_isPrime k
  · exact nodeAxisIdeal_one_isPrime k

/-- A coordinate variable does not lie in the ideal generated by the other variable. -/
lemma nodeVariable_not_mem_nodeAxisIdeal (k : Type u) [Field k]
    {i j : Fin 2} (hij : i ≠ j) :
    MvPowerSeries.X i ∉ nodeAxisIdeal k j := by
  rw [nodeAxisIdeal, Ideal.mem_span_singleton]
  intro h
  rw [MvPowerSeries.X_dvd_iff] at h
  have hcoeff := h (Finsupp.single i 1) (by simp [hij])
  exact one_ne_zero <|
    (MvPowerSeries.coeff_index_single_self_X (R := k) i).symm.trans hcoeff

/-- The two coordinate-axis ideals in `k[[x,y]]` are distinct. -/
lemma nodeAxisIdeal_zero_ne_one (k : Type u) [Field k] :
    nodeAxisIdeal k 0 ≠ nodeAxisIdeal k 1 := by
  intro h
  exact nodeVariable_not_mem_nodeAxisIdeal k (by decide : (0 : Fin 2) ≠ 1) <|
    h ▸ Ideal.subset_span (Set.mem_singleton (MvPowerSeries.X (0 : Fin 2)))

/-- The node ideal `(xy)` is contained in each coordinate-axis ideal. -/
lemma nodeIdeal_le_nodeAxisIdeal (k : Type u) [Field k] (i : Fin 2) :
    nodeIdeal k ≤ nodeAxisIdeal k i := by
  rw [nodeIdeal, Ideal.span_le]
  rintro z (rfl : z = MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2))
  fin_cases i
  · exact Ideal.mul_mem_right _ _ <|
      Ideal.subset_span (Set.mem_singleton (MvPowerSeries.X (0 : Fin 2)))
  · exact Ideal.mul_mem_left _ _ <|
      Ideal.subset_span (Set.mem_singleton (MvPowerSeries.X (1 : Fin 2)))

/-- Each coordinate-axis ideal is a minimal prime over `(xy)`. -/
lemma nodeAxisIdeal_mem_minimalPrimes (k : Type u) [Field k] (i : Fin 2) :
    nodeAxisIdeal k i ∈ (nodeIdeal k).minimalPrimes := by
  refine ⟨⟨nodeAxisIdeal_isPrime k i, nodeIdeal_le_nodeAxisIdeal k i⟩, ?_⟩
  intro q hq hqle
  have hxy : MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) ∈ q :=
    hq.2 <| Ideal.subset_span <| Set.mem_singleton _
  rcases hq.1.mem_or_mem hxy with hx | hy
  · fin_cases i
    · exact Ideal.span_le.mpr fun _ hz ↦ Set.mem_singleton_iff.mp hz ▸ hx
    · exact False.elim <| nodeVariable_not_mem_nodeAxisIdeal k
        (by decide : (0 : Fin 2) ≠ 1) (hqle hx)
  · fin_cases i
    · exact False.elim <| nodeVariable_not_mem_nodeAxisIdeal k
        (by decide : (1 : Fin 2) ≠ 0) (hqle hy)
    · exact Ideal.span_le.mpr fun _ hz ↦ Set.mem_singleton_iff.mp hz ▸ hy

/-- The only minimal primes over `(xy)` are the two coordinate-axis ideals. -/
lemma mem_nodeIdeal_minimalPrimes_iff (k : Type u) [Field k]
    (p : Ideal (MvPowerSeries (Fin 2) k)) :
    p ∈ (nodeIdeal k).minimalPrimes ↔
      p = nodeAxisIdeal k 0 ∨ p = nodeAxisIdeal k 1 := by
  constructor
  · intro hp
    have hxy : MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) ∈ p :=
      hp.le <| Ideal.subset_span <| Set.mem_singleton _
    rcases hp.isPrime.mem_or_mem hxy with hx | hy
    · left
      let haxis : nodeAxisIdeal k 0 ≤ p :=
        Ideal.span_le.mpr fun _ hz ↦ Set.mem_singleton_iff.mp hz ▸ hx
      exact le_antisymm (hp.2 (nodeAxisIdeal_mem_minimalPrimes k 0).1 haxis) haxis
    · right
      let haxis : nodeAxisIdeal k 1 ≤ p :=
        Ideal.span_le.mpr fun _ hz ↦ Set.mem_singleton_iff.mp hz ▸ hy
      exact le_antisymm (hp.2 (nodeAxisIdeal_mem_minimalPrimes k 1).1 haxis) haxis
  · rintro (rfl | rfl)
    · exact nodeAxisIdeal_mem_minimalPrimes k 0
    · exact nodeAxisIdeal_mem_minimalPrimes k 1

/-- The set of minimal primes over `(xy)` is exactly the pair of coordinate-axis ideals. -/
lemma nodeIdeal_minimalPrimes_eq_pair (k : Type u) [Field k] :
    (nodeIdeal k).minimalPrimes =
      {nodeAxisIdeal k 0, nodeAxisIdeal k 1} := by
  ext p
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
    mem_nodeIdeal_minimalPrimes_iff k p

/-- The two-element type parametrizes the minimal primes over the node ideal. -/
noncomputable def finTwoEquivNodeIdealMinimalPrimes (k : Type u) [Field k] :
    Fin 2 ≃ (nodeIdeal k).minimalPrimes :=
  Equiv.ofBijective
    (fun i ↦ ⟨nodeAxisIdeal k i, nodeAxisIdeal_mem_minimalPrimes k i⟩)
    ⟨fun i j h ↦ by
        fin_cases i <;> fin_cases j
        · rfl
        · exact False.elim <| nodeAxisIdeal_zero_ne_one k (congrArg Subtype.val h)
        · exact False.elim <| nodeAxisIdeal_zero_ne_one k (congrArg Subtype.val h).symm
        · rfl,
      fun p ↦ by
        rcases (mem_nodeIdeal_minimalPrimes_iff k p.1).mp p.2 with hp | hp
        · exact ⟨0, Subtype.ext hp.symm⟩
        · exact ⟨1, Subtype.ext hp.symm⟩⟩

/-- The minimal prime indexed by `i : Fin 2` is the corresponding coordinate-axis ideal. -/
@[simp]
lemma finTwoEquivNodeIdealMinimalPrimes_apply (k : Type u) [Field k] (i : Fin 2) :
    (finTwoEquivNodeIdealMinimalPrimes k i : Ideal (MvPowerSeries (Fin 2) k)) =
      nodeAxisIdeal k i := by
  simp [finTwoEquivNodeIdealMinimalPrimes]

/-- The type of formal branches of the standard node `k[[x,y]]/(xy)`. -/
abbrev nodeFormalBranches (k : Type u) [Field k] : Type u :=
  minimalPrimes (nodeRing k)

/-- The standard split node has exactly two formal branches. -/
noncomputable def nodeFormalBranchesEquivFinTwo (k : Type u) [Field k] :
    nodeFormalBranches k ≃ Fin 2 :=
  (Ideal.minimalPrimesQuotientEquiv (nodeIdeal k)).trans
    (finTwoEquivNodeIdealMinimalPrimes k).symm

/-- The formal branches at a scheme point are the minimal primes of its completed local
ring.  This definition is intrinsic: it includes no choice of local coordinates. -/
abbrev FormalBranchesAt (C : Scheme.{u}) (x : C) : Type u :=
  minimalPrimes (C.completedLocalRing x)

/-- An isomorphism of schemes induces an equivalence between the intrinsic formal branches
at corresponding points. -/
noncomputable def formalBranchesEquivOfIso {X Y : Scheme.{u}} (e : X ≅ Y) (x : X) :
    Y.FormalBranchesAt (e.hom x) ≃ X.FormalBranchesAt x :=
  Ideal.minimalPrimesEquivOfRingEquiv (completedLocalRingRingEquivOfIso e x)

/-- The coordinate-free type of split-node points of a `k`-scheme.

The proof of `IsSplitNodeAt` is retained only as a subtype witness; in particular, no
choice of node coordinates belongs to an element of this type. -/
abbrev SplitNodePoints (C : Scheme.{u}) (k : Type u) [Field k]
    [C.Over (Spec (CommRingCat.of k))] : Type u :=
  {x : C // C.IsSplitNodeAt k x}

/-- The total type of intrinsic formal branches over the split-node points of a
`k`-scheme.  This is a dependent sum, with the branch type allowed to depend on its node. -/
abbrev SplitNodeBranches (C : Scheme.{u}) (k : Type u) [Field k]
    [C.Over (Spec (CommRingCat.of k))] : Type u :=
  Σ x : C.SplitNodePoints k, C.FormalBranchesAt x.1

/-- The projection sending a formal branch to the split node on which it lies. -/
def SplitNodeBranches.toNode {C : Scheme.{u}} {k : Type u} [Field k]
    [C.Over (Spec (CommRingCat.of k))] (b : C.SplitNodeBranches k) :
    C.SplitNodePoints k :=
  b.1

/-- The branch-to-node projection sends a dependent pair to its node. -/
@[simp]
lemma SplitNodeBranches.toNode_mk {C : Scheme.{u}} {k : Type u} [Field k]
    [C.Over (Spec (CommRingCat.of k))] (x : C.SplitNodePoints k)
    (b : C.FormalBranchesAt x.1) :
    SplitNodeBranches.toNode (⟨x, b⟩ : C.SplitNodeBranches k) = x :=
  rfl

/-- The type-theoretic fibre of the formal-branch projection over a split node. -/
abbrev SplitNodeBranchFiber {C : Scheme.{u}} {k : Type u} [Field k]
    [C.Over (Spec (CommRingCat.of k))] (x : C.SplitNodePoints k) : Type u :=
  {b : C.SplitNodeBranches k // b.toNode = x}

/-- The fibre of the branch-to-node projection over `x` is canonically equivalent to the
intrinsic formal-branch type at the underlying scheme point. -/
def splitNodeBranchFiberEquiv {C : Scheme.{u}} {k : Type u} [Field k]
    [C.Over (Spec (CommRingCat.of k))] (x : C.SplitNodePoints k) :
    SplitNodeBranchFiber x ≃ C.FormalBranchesAt x.1 where
  toFun b := by
    rcases b with ⟨⟨y, a⟩, h⟩
    change y = x at h
    subst y
    exact a
  invFun a := ⟨⟨x, a⟩, rfl⟩
  left_inv b := by
    rcases b with ⟨⟨y, a⟩, h⟩
    change y = x at h
    subst y
    rfl
  right_inv _ := rfl

/-- On the evident element of a projection fibre, `splitNodeBranchFiberEquiv` returns the
given formal branch. -/
@[simp]
lemma splitNodeBranchFiberEquiv_apply_mk {C : Scheme.{u}} {k : Type u} [Field k]
    [C.Over (Spec (CommRingCat.of k))] (x : C.SplitNodePoints k)
    (b : C.FormalBranchesAt x.1) :
    splitNodeBranchFiberEquiv x ⟨⟨x, b⟩, rfl⟩ = b :=
  rfl

/-- A choice of split-node coordinates identifies the intrinsic formal branches with the
two-element type. -/
noncomputable def formalBranchesEquivFinTwoOfRingEquiv
    {k : Type u} [Field k] {C : Scheme.{u}} (x : C)
    (e : C.completedLocalRing x ≃+* nodeRing k) :
    C.FormalBranchesAt x ≃ Fin 2 :=
  (Ideal.minimalPrimesEquivOfRingEquiv e).trans
    (nodeFormalBranchesEquivFinTwo k)

/-- A split node has exactly two intrinsic formal branches.  The equivalence is merely
asserted to exist because a split node does not include a chosen coordinate chart. -/
theorem IsSplitNodeAt.nonempty_formalBranchesEquivFinTwo
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] {x : C} (h : C.IsSplitNodeAt k x) :
    Nonempty (C.FormalBranchesAt x ≃ Fin 2) := by
  let _ := stalkAlgebra (C ↘ Spec (CommRingCat.of k)) x
  change Nonempty (C.completedLocalRing x ≃ₐ[k] nodeRing k) at h
  obtain ⟨e⟩ := h
  exact ⟨formalBranchesEquivFinTwoOfRingEquiv (k := k) x e.toRingEquiv⟩

/-- The formal-branch type at a split node is finite. -/
theorem IsSplitNodeAt.finite_formalBranchesAt
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] {x : C} (h : C.IsSplitNodeAt k x) :
    Finite (C.FormalBranchesAt x) := by
  obtain ⟨e⟩ := h.nonempty_formalBranchesEquivFinTwo
  exact Finite.of_equiv (Fin 2) e.symm

/-- Every fibre of the formal-branch-to-node projection is noncanonically equivalent to
`Fin 2`.  The noncanonicity comes only from choosing split-node coordinates. -/
theorem nonempty_splitNodeBranchFiberEquivFinTwo
    {C : Scheme.{u}} {k : Type u} [Field k]
    [C.Over (Spec (CommRingCat.of k))] (x : C.SplitNodePoints k) :
    Nonempty (SplitNodeBranchFiber x ≃ Fin 2) := by
  obtain ⟨e⟩ := x.2.nonempty_formalBranchesEquivFinTwo
  exact ⟨(splitNodeBranchFiberEquiv x).trans e⟩

/-- Every fibre of the formal-branch-to-node projection is finite.  No finiteness of the
global split-node subtype is asserted. -/
theorem finite_splitNodeBranchFiber
    {C : Scheme.{u}} {k : Type u} [Field k]
    [C.Over (Spec (CommRingCat.of k))] (x : C.SplitNodePoints k) :
    Finite (SplitNodeBranchFiber x) := by
  obtain ⟨e⟩ := nonempty_splitNodeBranchFiberEquivFinTwo x
  exact Finite.of_equiv (Fin 2) e.symm

/-- Every fibre of the formal-branch-to-node projection has cardinality two. -/
theorem encard_splitNodeBranchFiber
    {C : Scheme.{u}} {k : Type u} [Field k]
    [C.Over (Spec (CommRingCat.of k))] (x : C.SplitNodePoints k) :
    Set.encard (Set.univ : Set (SplitNodeBranchFiber x)) = 2 := by
  obtain ⟨e⟩ := nonempty_splitNodeBranchFiberEquivFinTwo x
  rw [Set.encard_univ]
  simpa using ENat.card_congr e

/-- The formal-branch type at a split node has cardinality two. -/
theorem IsSplitNodeAt.encard_formalBranchesAt
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] {x : C} (h : C.IsSplitNodeAt k x) :
    Set.encard (Set.univ : Set (C.FormalBranchesAt x)) = 2 := by
  obtain ⟨e⟩ := h.nonempty_formalBranchesEquivFinTwo
  rw [Set.encard_univ]
  simpa using ENat.card_congr e

end AlgebraicGeometry.Scheme
