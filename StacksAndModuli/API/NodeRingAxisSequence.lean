module

public import StacksAndModuli.API.NodalBranches
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The coordinate-axis sequence of the standard node ring

For a field `k`, restriction to the two coordinate axes gives an injective algebra map

`k[[x,y]]/(xy) ⟶ k[[x]] × k[[y]]`.

Its image consists precisely of the pairs with equal constant coefficient.  Consequently,
the difference of constant coefficients completes this map to the short exact sequence

`0 ⟶ k[[x,y]]/(xy) ⟶ k[[x]] × k[[y]] ⟶ k ⟶ 0`.

This file proves that local algebra calculation for the standard coordinate ring only.  It
does not assert that the two-axis algebra is the normalization of a completed local ring or
identify its factors with points of a scheme-theoretic normalization fibre.

## Main definitions

* `AlgebraicGeometry.Scheme.nodeAxisRestriction`: restriction of a two-variable power
  series to one coordinate axis.
* `AlgebraicGeometry.Scheme.nodeToAxes`: the induced map from the standard node ring to
  the product of its two axes.
* `AlgebraicGeometry.Scheme.nodeConstantDifference`: the difference of the two constant
  coefficients.
* `AlgebraicGeometry.Scheme.nodeDefectLinearEquiv`: the resulting one-dimensional defect
  quotient.

## Main results

* `AlgebraicGeometry.Scheme.nodeToAxes_injective`: the node ring embeds in the product of
  its axes.
* `AlgebraicGeometry.Scheme.nodeToAxes_exact`: the image is the kernel of the constant-term
  difference.
* `AlgebraicGeometry.Scheme.nodeAxisSequence_shortExact`: injectivity, middle exactness,
  and surjectivity of the coordinate-axis sequence.
* `AlgebraicGeometry.Scheme.nodeDefect_finrank`: its defect has dimension one over `k`.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped MvPowerSeries PowerSeries

universe u

namespace AlgebraicGeometry.Scheme

/-- The embedding of the one-variable index type as coordinate `i` of `Fin 2`. -/
def nodeAxisEmbedding (i : Fin 2) : Unit ↪ Fin 2 where
  toFun _ := i
  inj' _ _ _ := Subsingleton.elim _ _

/-- Restriction of a two-variable formal power series to coordinate axis `i`, obtained by
sending the other variable to zero. -/
def nodeAxisRestriction (k : Type u) [CommRing k] (i : Fin 2) :
    MvPowerSeries (Fin 2) k →ₐ[k] PowerSeries k :=
  MvPowerSeries.killCompl (nodeAxisEmbedding i)

/-- Simultaneous restriction of a two-variable formal power series to both coordinate
axes. -/
def nodeAxisRestrictions (k : Type u) [CommRing k] :
    MvPowerSeries (Fin 2) k →ₐ[k] PowerSeries k × PowerSeries k :=
  (nodeAxisRestriction k 0).prod (nodeAxisRestriction k 1)

/-- The coefficient of an axis restriction is the corresponding pure-axis coefficient of
the original two-variable series. -/
@[simp]
lemma nodeAxisRestriction_coeff (k : Type u) [CommRing k] (i : Fin 2)
    (f : MvPowerSeries (Fin 2) k) (n : ℕ) :
    PowerSeries.coeff n (nodeAxisRestriction k i f) =
      MvPowerSeries.coeff (Finsupp.single i n) f := by
  rw [nodeAxisRestriction, PowerSeries.coeff]
  rw [MvPowerSeries.coeff_killCompl]
  simp [nodeAxisEmbedding]

/-- Restriction to either coordinate axis preserves the constant coefficient. -/
@[simp]
lemma nodeAxisRestriction_constantCoeff (k : Type u) [CommRing k] (i : Fin 2)
    (f : MvPowerSeries (Fin 2) k) :
    PowerSeries.constantCoeff (nodeAxisRestriction k i f) =
      MvPowerSeries.constantCoeff f := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    nodeAxisRestriction_coeff, Finsupp.single_zero,
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply]

/-- Restriction to an axis preserves constant power series. -/
@[simp]
lemma nodeAxisRestriction_C (k : Type u) [CommRing k] (i : Fin 2) (a : k) :
    nodeAxisRestriction k i (MvPowerSeries.C a) = PowerSeries.C a := by
  change MvPowerSeries.killCompl (nodeAxisEmbedding i) (MvPowerSeries.C a) =
    MvPowerSeries.C a
  exact MvPowerSeries.killCompl_C a

/-- The coordinate variable along an axis restricts to the one-variable parameter. -/
@[simp]
lemma nodeAxisRestriction_X_self (k : Type u) [CommRing k] (i : Fin 2) :
    nodeAxisRestriction k i (MvPowerSeries.X i) = PowerSeries.X := by
  change MvPowerSeries.killCompl (nodeAxisEmbedding i) (MvPowerSeries.X i) =
    MvPowerSeries.X ()
  exact MvPowerSeries.killCompl_X ()

/-- The coordinate variable transverse to an axis restricts to zero. -/
@[simp]
lemma nodeAxisRestriction_X_of_ne (k : Type u) [CommRing k] {i j : Fin 2}
    (hij : i ≠ j) :
    nodeAxisRestriction k i (MvPowerSeries.X j) = 0 := by
  apply MvPowerSeries.killCompl_X_eq_zero
  rintro ⟨a, ha⟩
  exact hij ha

/-- Restricting a series inserted along the same axis recovers that series. -/
@[simp]
lemma nodeAxisRestriction_rename_self (k : Type u) [CommRing k] (i : Fin 2)
    (f : PowerSeries k) :
    nodeAxisRestriction k i (MvPowerSeries.rename (nodeAxisEmbedding i) f) = f := by
  exact MvPowerSeries.killCompl_rename_app f

/-- The node ideal `(xy)` vanishes under simultaneous restriction to the two axes. -/
lemma nodeAxisRestrictions_nodeIdeal (k : Type u) [CommRing k] :
    nodeIdeal k ≤ RingHom.ker (nodeAxisRestrictions k).toRingHom := by
  rw [nodeIdeal, Ideal.span_le]
  rintro _ rfl
  change nodeAxisRestrictions k (MvPowerSeries.X 0 * MvPowerSeries.X 1) = 0
  ext <;> simp [nodeAxisRestrictions]

/-- The algebra map from the standard node ring `k[[x,y]]/(xy)` to the product of the two
coordinate-axis power-series rings. -/
def nodeToAxes (k : Type u) [CommRing k] :
    nodeRing k →ₐ[k] PowerSeries k × PowerSeries k :=
  Ideal.Quotient.liftₐ (nodeIdeal k) (nodeAxisRestrictions k)
    (fun _f hf ↦ RingHom.mem_ker.mp (nodeAxisRestrictions_nodeIdeal k hf))

/-- The map from the node ring is induced by simultaneous axis restriction. -/
@[simp]
lemma nodeToAxes_mk (k : Type u) [CommRing k] (f : MvPowerSeries (Fin 2) k) :
    nodeToAxes k (Ideal.Quotient.mk (nodeIdeal k) f) = nodeAxisRestrictions k f := by
  simp [nodeToAxes]

/-- Restricting a series inserted along the other axis retains only its constant
coefficient. -/
lemma nodeAxisRestriction_rename_of_ne (k : Type u) [CommRing k]
    {i j : Fin 2} (hij : i ≠ j) (f : PowerSeries k) :
    nodeAxisRestriction k i (MvPowerSeries.rename (nodeAxisEmbedding j) f) =
      PowerSeries.C (PowerSeries.constantCoeff f) := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp only [nodeAxisRestriction_coeff, Finsupp.single_zero,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      MvPowerSeries.constantCoeff_rename, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.constantCoeff_C]
    rfl
  · rw [nodeAxisRestriction_coeff]
    rw [MvPowerSeries.coeff_rename_eq_zero]
    · exact (PowerSeries.coeff_C_of_ne_zero hn).symm
    · rintro ⟨d, hd⟩
      have hi : i ∉ Set.range (nodeAxisEmbedding j) := by
        rintro ⟨a, ha⟩
        exact hij ha.symm
      have hdi := Finsupp.mapDomain_of_notMem_range d i hi
      rw [hd] at hdi
      exact hn (by simpa using hdi)

/-- The kernel of simultaneous restriction to the two axes is exactly the node ideal
`(xy)`. -/
lemma nodeAxisRestrictions_ker (k : Type u) [Field k] :
    RingHom.ker (nodeAxisRestrictions k).toRingHom = nodeIdeal k := by
  apply le_antisymm
  · intro f hf
    rw [RingHom.mem_ker] at hf
    have hzero : nodeAxisRestriction k 0 f = 0 := congrArg Prod.fst hf
    have hone : nodeAxisRestriction k 1 f = 0 := congrArg Prod.snd hf
    let x : MvPowerSeries (Fin 2) k := MvPowerSeries.X 0
    let y : MvPowerSeries (Fin 2) k := MvPowerSeries.X 1
    have hx : x ∣ f := by
      rw [MvPowerSeries.X_dvd_iff]
      intro m hm
      have hm' : m = Finsupp.single (1 : Fin 2) (m 1) := by
        ext i
        fin_cases i
        · simpa using hm
        · simp
      rw [hm']
      exact (nodeAxisRestriction_coeff k 1 f (m 1)).symm.trans <|
        congrArg (PowerSeries.coeff (m 1)) hone
    have hy : y ∣ f := by
      rw [MvPowerSeries.X_dvd_iff]
      intro m hm
      have hm' : m = Finsupp.single (0 : Fin 2) (m 0) := by
        ext i
        fin_cases i
        · simp
        · simpa using hm
      rw [hm']
      exact (nodeAxisRestriction_coeff k 0 f (m 0)).symm.trans <|
        congrArg (PowerSeries.coeff (m 0)) hzero
    have hy0 : y ≠ 0 := by
      intro hyz
      dsimp [y] at hyz
      apply nodeVariable_not_mem_nodeAxisIdeal k (by decide : (1 : Fin 2) ≠ 0)
      rw [hyz]
      exact Ideal.zero_mem _
    have hyp : Prime y :=
      (Ideal.span_singleton_prime hy0).mp <| by
        simpa [nodeAxisIdeal, y] using nodeAxisIdeal_one_isPrime k
    have hyx : ¬y ∣ x := by
      intro h
      exact nodeVariable_not_mem_nodeAxisIdeal k (by decide : (0 : Fin 2) ≠ 1) <| by
        rw [nodeAxisIdeal, Ideal.mem_span_singleton]
        exact h
    obtain ⟨a, ha⟩ := hx
    have hya : y ∣ a := (hyp.dvd_or_dvd (ha ▸ hy)).resolve_left hyx
    obtain ⟨b, hb⟩ := hya
    rw [nodeIdeal, Ideal.mem_span_singleton]
    refine ⟨b, ?_⟩
    simp only [x, y] at ha hb ⊢
    rw [ha, hb, mul_assoc]
  · exact nodeAxisRestrictions_nodeIdeal k

/-- The standard node ring embeds in the product of its two coordinate axes. -/
theorem nodeToAxes_injective (k : Type u) [Field k] :
    Function.Injective (nodeToAxes k) := by
  apply RingHom.lift_injective_of_ker_le_ideal
  exact (nodeAxisRestrictions_ker k).le

/-- The linear map on the product of the axes given by subtracting the second constant
coefficient from the first. -/
def nodeConstantDifference (k : Type u) [Field k] :
    PowerSeries k × PowerSeries k →ₗ[k] k where
  toFun f := PowerSeries.constantCoeff f.1 - PowerSeries.constantCoeff f.2
  map_add' _ _ := by simp [sub_add_sub_comm]
  map_smul' _ _ := by simp [mul_sub]

/-- The difference-of-constant-coefficients map is surjective. -/
theorem nodeConstantDifference_surjective (k : Type u) [Field k] :
    Function.Surjective (nodeConstantDifference k) := by
  intro a
  exact ⟨(PowerSeries.C a, 0), by simp [nodeConstantDifference]⟩

/-- The composite from the node ring through the two axes to their constant-term
difference is zero. -/
lemma nodeConstantDifference_nodeToAxes (k : Type u) [Field k] :
    nodeConstantDifference k ∘ₗ (nodeToAxes k).toLinearMap = 0 := by
  apply LinearMap.ext
  intro z
  refine Quotient.inductionOn' z ?_
  intro f
  change nodeConstantDifference k (nodeAxisRestrictions k f) = 0
  simp [nodeConstantDifference, nodeAxisRestrictions]

/-- A pair of axis series comes from the node ring exactly when its two constant
coefficients agree. -/
lemma nodeToAxes_range_eq_ker_nodeConstantDifference (k : Type u) [Field k] :
    LinearMap.range (nodeToAxes k).toLinearMap =
      LinearMap.ker (nodeConstantDifference k) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨f, rfl⟩ := hz
    rw [LinearMap.mem_ker]
    exact LinearMap.congr_fun (nodeConstantDifference_nodeToAxes k) f
  · rintro ⟨p, q⟩ hpq
    rw [LinearMap.mem_ker] at hpq
    change PowerSeries.constantCoeff p - PowerSeries.constantCoeff q = 0 at hpq
    have hc : PowerSeries.constantCoeff p = PowerSeries.constantCoeff q :=
      sub_eq_zero.mp hpq
    let f : MvPowerSeries (Fin 2) k :=
      MvPowerSeries.rename (nodeAxisEmbedding 0) p +
        MvPowerSeries.rename (nodeAxisEmbedding 1) q -
          MvPowerSeries.C (PowerSeries.constantCoeff p)
    refine ⟨Ideal.Quotient.mk (nodeIdeal k) f, ?_⟩
    change nodeToAxes k (Ideal.Quotient.mk (nodeIdeal k) f) = (p, q)
    rw [nodeToAxes_mk]
    apply Prod.ext
    · simp only [nodeAxisRestrictions, AlgHom.prod_apply]
      rw [map_sub, map_add, nodeAxisRestriction_rename_self,
        nodeAxisRestriction_rename_of_ne k (by decide : (0 : Fin 2) ≠ 1),
        nodeAxisRestriction_C]
      rw [← hc]
      abel
    · simp only [nodeAxisRestrictions, AlgHom.prod_apply]
      rw [map_sub, map_add,
        nodeAxisRestriction_rename_of_ne k (by decide : (1 : Fin 2) ≠ 0),
        nodeAxisRestriction_rename_self, nodeAxisRestriction_C]
      abel

/-- The coordinate-axis embedding is exact in the middle with respect to the
difference-of-constant-coefficients map. -/
theorem nodeToAxes_exact (k : Type u) [Field k] :
    Function.Exact (nodeToAxes k).toLinearMap (nodeConstantDifference k) := by
  rw [LinearMap.exact_iff]
  exact (nodeToAxes_range_eq_ker_nodeConstantDifference k).symm

/-- The function-level coordinate-axis sequence is short exact: its first map is
injective, it is exact in the middle, and its last map is surjective. -/
theorem nodeAxisSequence_shortExact (k : Type u) [Field k] :
    Function.Injective (nodeToAxes k) ∧
      Function.Exact (nodeToAxes k).toLinearMap (nodeConstantDifference k) ∧
        Function.Surjective (nodeConstantDifference k) :=
  ⟨nodeToAxes_injective k, nodeToAxes_exact k, nodeConstantDifference_surjective k⟩

/-- The quotient of the two-axis algebra by the image of the node ring is linearly
equivalent to the coefficient field. -/
def nodeDefectLinearEquiv (k : Type u) [Field k] :
    ((PowerSeries k × PowerSeries k) ⧸
      LinearMap.range (nodeToAxes k).toLinearMap) ≃ₗ[k] k :=
  (Submodule.quotEquivOfEq _ _
      (nodeToAxes_range_eq_ker_nodeConstantDifference k)).trans
    ((nodeConstantDifference k).quotKerEquivOfSurjective
      (nodeConstantDifference_surjective k))

/-- On a quotient class, the defect equivalence is the difference of constant
coefficients. -/
@[simp]
lemma nodeDefectLinearEquiv_mk (k : Type u) [Field k]
    (p : PowerSeries k × PowerSeries k) :
    nodeDefectLinearEquiv k (Submodule.Quotient.mk p) =
      nodeConstantDifference k p := by
  simp [nodeDefectLinearEquiv]

/-- The coordinate-axis defect of the standard node ring is one-dimensional over the
coefficient field. -/
theorem nodeDefect_finrank (k : Type u) [Field k] :
    Module.finrank k
      ((PowerSeries k × PowerSeries k) ⧸
        LinearMap.range (nodeToAxes k).toLinearMap) = 1 := by
  rw [LinearEquiv.finrank_eq (nodeDefectLinearEquiv k)]
  exact CommSemiring.finrank_self k

end AlgebraicGeometry.Scheme
