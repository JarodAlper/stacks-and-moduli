module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Limits.Preorder
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import StacksAndModuli.API.ProjectiveGradedCohomology

/-!
# Castelnuovo–Mumford regularity: definition and basic properties

This module corresponds to the first subsection ("Definition and basic properties") of
§2.3 (Castelnuovo–Mumford regularity) of Chapter 2 of *Stacks and Moduli*,
label `sec:regularity`.

**Definition 2.3.1** (`def:regularity`) reads: a coherent sheaf `F` on `ℙ^n`
over a field is `m`-regular if `H^i(ℙ^n, F(m - i)) = 0` for all `i ≥ 1`. It is to be
provided at the natural generality of the projective spectrum of a graded ring by
`ProjectiveSpectrum.Proj.IsMRegular` (Stacks Project tag 08A3).

The implementation combines Mathlib's sheaf cohomology `CategoryTheory.Sheaf.H` with
integer-indexed Serre twists `O(n)` on `Proj` (Stacks 01MN, `constructions-definition-twist`),
which Mathlib does not provide and which are an outstanding obligation for
`stacks-project-lean`. This module records the book-facing
specialization and the identification of `H⁰` with global sections. The later regularity
lemmas still require the long exact cohomology sequence and computations of the
cohomology of twisting sheaves; those dependencies remain outstanding obligations.

The definition itself is given in the graded-module model of quasi-coherent sheaves on `ℙⁿ_k`
(`StacksAndModuli/API/ProjectiveGradedModule.lean`) relative to a packaged cohomology theory
(`StacksAndModuli/API/ProjectiveGradedCohomology.lean`); see this folder's COMMENTARY.md for the
reasons and the alternatives considered.

Main results:
- `AlgebraicGeometry.ProjectiveSpace.Cohomology.IsMRegular`: **Definition 2.3.1**
  (`def:regularity`), Castelnuovo–Mumford `m`-regularity, and
  `Cohomology.HasRegularity`, the regularity of a sheaf.
- `Cohomology.isMRegular_restrictL`: **Lemma 2.3.2** (`lem:regularity-induction`).
- `Cohomology.isMRegular_twistingModule` and `Cohomology.isMRegular_coker_mulPolyHom`:
  **Exercise 2.3.3**(a,b) (`exer:regularity-resolution`).
- `Cohomology.isMRegular_of_shortExact`: **Exercise 2.3.4** (`exer:regularity-in-sequences`).
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section DefRegularity

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

/- OBLIGATION (`AlgebraicGeometry.ProjectiveSpectrum.Proj.IsMRegular`).

Background implementation obligation for Definition 2.3.1: a sheaf of modules `F` on
the projective spectrum of a graded ring is `m`-regular exactly when every positive-degree cohomology
group of `F(m-i)` is zero. This is the general form of the book's definition;
projective space is obtained from the standard graded polynomial ring.

What must be defined and proven, in `stacks-project-lean`:

1. The integer-indexed Serre twists `O(d)` on `Proj 𝒜` and the twist `F(d)` of a sheaf of
   modules — Stacks 01MN, `constructions-definition-twist` (`constructions.tex`, §01MM).
   Mathlib has `AlgebraicGeometry.Proj` but no twisting sheaf of any kind. Note the Stacks
   Project is careful here: `O(d)` is *not* invertible in general (Stacks 01MS gives the
   condition), so the definition cannot assume invertibility.
2. `m`-regularity itself: `F` is `m`-regular if `Hⁱ(Proj 𝒜, F(m - i)) = 0` for all `i ≥ 1` —
   Stacks 08A3, `varieties-definition-regularity`. Note this lives in `varieties.tex` §08A2,
   *not* in `coherent.tex`, and the Stacks Project calls it *m-regularity*, never
   "Castelnuovo–Mumford regularity".

The cohomology to use is Mathlib's `CategoryTheory.Sheaf.H`, as fixed by the two `example`s
below. -/

/- Background cohomology vocabulary for Definition 2.3.1:
sheaf cohomology of an abelian sheaf on (the underlying space of) a scheme, via
Mathlib's `CategoryTheory.Sheaf.H` (defined as `Ext^n` from the constant sheaf `ℤ` in the
category of abelian sheaves). This is the cohomology used by `Proj.IsMRegular`. -/
example (X : Scheme.{u}) (F : TopCat.Sheaf AddCommGrpCat.{u} X) (i : ℕ) : Type u :=
  F.H i

/- Background cohomology vocabulary for Definition 2.3.1:
`Sheaf.H.equiv₀` identifies `H⁰(X, F)` with the sections over a terminal object of the
site: for the site of opens of a scheme, `H⁰(X, F) ≃ F(X)` is the group of global
sections. -/
-- TODO: restore this recall. `Sheaf.H F 0` elaborates fine as a type (previous `example`),
-- but the `≃+` needs `AddCommGroup (Ext _ F 0)`, whose Mathlib instance is not found here:
-- `Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic` derives it through
-- `HasDerivedCategory.standard`, and the universe at which `IsGrothendieckAbelian.hasExt`
-- supplies `HasExt` does not line up. This is a Mathlib instance/universe issue, unrelated
-- to the Stacks obligations above; it needs the right `HasDerivedCategory` import or an
-- explicit `letI`.
-- noncomputable example (X : Scheme.{u}) (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
--     F.H 0 ≃+ F.1.obj (Opposite.op ⊤) :=
--   Sheaf.H.equiv₀ F Limits.isTerminalTop

/-- **Definition 2.3.1** (`def:regularity`): a coherent sheaf `F` on projective space `ℙⁿ` over
a field `k` is **`m`-regular** if `Hⁱ(ℙⁿ, F(m-i)) = 0` for all `i ≥ 1`.

Formalised in the graded-module model: `M` is a `ℤ`-graded module over `k[x₀, …, x_n]`
presenting the sheaf `F = M~`, and `C.Hgr M i` is the graded module `⨁_d Hⁱ(ℙⁿ, F(d))`, so
that the vanishing asked for is that of the degree-`m-i` piece. See this folder's
COMMENTARY.md. -/
def AlgebraicGeometry.ProjectiveSpace.Cohomology.IsMRegular {k : Type u} [Field k]
    (C : AlgebraicGeometry.ProjectiveSpace.Cohomology k) {n : ℕ}
    (M : AlgebraicGeometry.ProjectiveSpace.GradedModule k n) (m : ℤ) : Prop :=
  ∀ i : ℕ, 1 ≤ i → Subsingleton ((C.Hgr M i).obj (m - i))

namespace AlgebraicGeometry.ProjectiveSpace.Cohomology

variable {k : Type u} [Field k] (C : Cohomology k)

/-- **Definition 2.3.1** (`def:regularity`) (the regularity of `F`): `m` is *the* regularity
of `F` when `F` is `m`-regular and `m` is least with that property.

The book writes "the smallest integer `m` such that `F(m)` is `m`-regular"; the twist is a
typo, see this folder's COMMENTARY.md. -/
def HasRegularity {n : ℕ} (M : GradedModule k n) (m : ℤ) : Prop :=
  IsLeast {m' : ℤ | C.IsMRegular M m'} m

lemma isMRegular_def {n : ℕ} (M : GradedModule k n) (m : ℤ) :
    C.IsMRegular M m ↔ ∀ i : ℕ, 1 ≤ i → Subsingleton ((C.Hgr M i).obj (m - i)) := Iff.rfl

/-- Transport of vanishing along the twist comparison. -/
lemma subsingleton_Hgr_twist_iff {n : ℕ} (M : GradedModule k n) (a : ℤ) (i : ℕ) (d : ℤ) :
    Subsingleton ((C.Hgr (M.twist a) i).obj d) ↔ Subsingleton ((C.Hgr M i).obj (d + a)) :=
  ⟨fun _ => (C.twistIso M a i d).symm.toLinearEquiv.toEquiv.subsingleton,
   fun _ => (C.twistIso M a i d).toLinearEquiv.toEquiv.subsingleton⟩

/-- Regularity depends only on the cohomology, so it transports along any comparison map
that is bijective in every cohomological degree — in particular along the quotient of a
coherent sheaf by its irrelevant torsion. -/
lemma isMRegular_congr {n : ℕ} {M N : GradedModule k n} (φ : M ⟶ N)
    (hφ : ∀ (i : ℕ) (d : ℤ), Function.Bijective ((C.map φ i).app d).hom) (m : ℤ) :
    C.IsMRegular M m ↔ C.IsMRegular N m := by
  constructor
  · intro h i hi
    have hs := h i hi
    exact ⟨fun x y => by
      obtain ⟨a, rfl⟩ := (hφ i (m - i)).2 x
      obtain ⟨b, rfl⟩ := (hφ i (m - i)).2 y
      rw [Subsingleton.elim a b]⟩
  · intro h i hi
    have hs := h i hi
    exact ⟨fun x y => (hφ i (m - i)).1 (Subsingleton.elim _ _)⟩

/-- API lemma for Definition 2.3.1 (the remark following it): if `F` is `m`-regular
then `F(a)` is `(m-a)`-regular. -/
lemma isMRegular_twist {n : ℕ} {M : GradedModule k n} {m : ℤ} (hM : C.IsMRegular M m) (a : ℤ) :
    C.IsMRegular (M.twist a) (m - a) := by
  intro i hi
  rw [subsingleton_Hgr_twist_iff]
  have heq : m - a - (i : ℤ) + a = m - i := by ring
  rw [heq]
  exact hM i hi

end AlgebraicGeometry.ProjectiveSpace.Cohomology

end DefRegularity

section LemRegularityInduction

open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.ProjectiveSpace.GradedModule

universe u

namespace AlgebraicGeometry.ProjectiveSpace.Cohomology

variable {k : Type u} [Field k] (C : Cohomology k)

/-- **Lemma 2.3.2** (`lem:regularity-induction`): let `F` be an `m`-regular coherent sheaf on
`ℙⁿ⁺¹` over a field. If `H = V(L)` is a hyperplane avoiding the associated points of `F` —
equivalently, if the linear form `L = ∑ cᵢxᵢ` is a nonzerodivisor on `F` — then `F|_H` is
`m`-regular on `H ≅ ℙⁿ`. -/
theorem isMRegular_restrictL {n : ℕ} {M : GradedModule k (n + 1)} {m : ℤ}
    (hM : C.IsMRegular M m) (c : Fin (n + 2) → k) (j : Fin (n + 2)) (hj : IsUnit (c j))
    (hcoh : C.IsCoherent (M.restrictL c j))
    (hL : ∀ d, Function.Injective ((M.mulLHom c).app d).hom) :
    C.IsMRegular (M.restrictL c j) m := by
  intro i hi
  have hSE : ShortExact (M.mulLHom c) (toCoker (M.mulLHom c)) := shortExact_toCoker _ hL
  have h1 : Subsingleton ((C.Hgr M i).obj (m - i)) := hM i hi
  have h2 : Subsingleton ((C.Hgr (M.twist (-1)) (i + 1)).obj (m - i)) := by
    rw [subsingleton_Hgr_twist_iff]
    have heq : m - (i : ℤ) + -1 = m - ((i : ℤ) + 1) := by ring
    rw [heq]
    have := hM (i + 1) (by omega)
    rwa [Nat.cast_add, Nat.cast_one] at this
  have h3 : Subsingleton ((C.Hgr (M.quotL c) i).obj (m - i)) :=
    C.subsingleton_H_X₃ hSE i (m - i) h1 h2
  have hkill : ∀ (d e : ℤ) (h : d + 1 = e), (M.quotL c).mulL c d e h = 0 :=
    fun d e h => quotL_mulL_eq_zero M c d e h
  have : Subsingleton (((C.Hgr (M.quotL c) i).dropVar j).obj (m - i)) := h3
  exact (isoApp (C.dropVarIso (M.quotL c) c j hj hkill hcoh i)
    (m - i)).toLinearEquiv.toEquiv.subsingleton

end AlgebraicGeometry.ProjectiveSpace.Cohomology

end LemRegularityInduction

section ExerRegularityResolution

open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.ProjectiveSpace.GradedModule

universe u

namespace AlgebraicGeometry.ProjectiveSpace.Cohomology

variable {k : Type u} [Field k] (C : Cohomology k)

/-- **Exercise 2.3.3** (`exer:regularity-resolution`, part (a)): the twisting sheaf `𝒪(a)` on `ℙⁿ` is
`(-a)`-regular.

Part (c) — the structure sheaf of a smooth curve of genus `g` is `(2g-1)`-regular — is
discussed in this folder's COMMENTARY.md. -/
theorem isMRegular_twistingModule (n : ℕ) (a : ℤ) :
    C.IsMRegular (twistingModule k n a) (-a) := by
  intro i hi
  rw [twistingModule, subsingleton_Hgr_twist_iff]
  have heq : -a - (i : ℤ) + a = -(i : ℤ) := by ring
  rw [heq]
  refine C.subsingleton_Hgr_structureModule i (-(i : ℤ)) hi ?_
  by_cases hin : i = n
  · exact Or.inr (by omega)
  · exact Or.inl hin

/-- **Exercise 2.3.3** (`exer:regularity-resolution`, part (b)): the structure sheaf of a hypersurface
`H = V(q) ⊆ ℙⁿ` of degree `e ≥ 1` is `(e-1)`-regular.

`𝒪_H` is the cokernel of multiplication by `q`, i.e. of `𝒪(-e) → 𝒪`; the two outer terms of the
long exact sequence vanish exactly because `e ≥ 1`. -/
theorem isMRegular_coker_mulPolyHom (n : ℕ) {e : ℕ} (he : 1 ≤ e)
    {q : MvPolynomial (Fin (n + 1)) k} (hq : q ∈ polySubmodule k n e) (hq0 : q ≠ 0) :
    C.IsMRegular (coker (mulPolyHom hq)) ((e : ℤ) - 1) := by
  intro i hi
  have hSE : ShortExact (mulPolyHom hq) (toCoker (mulPolyHom hq)) :=
    shortExact_toCoker _ (injective_mulPolyHom_app hq hq0)
  refine C.subsingleton_H_X₃ hSE i ((e : ℤ) - 1 - i) ?_ ?_
  · refine C.subsingleton_Hgr_structureModule i ((e : ℤ) - 1 - i) hi ?_
    by_cases hin : i = n
    · exact Or.inr (by omega)
    · exact Or.inl hin
  · rw [C.subsingleton_Hgr_twist_iff]
    have heq : (e : ℤ) - 1 - (i : ℤ) + -(e : ℤ) = -(i : ℤ) - 1 := by ring
    rw [heq]
    rcases lt_or_ge (n : ℕ) (i + 1) with hlt | hge
    · exact C.subsingleton_of_lt _ (i + 1) _ hlt
    · refine C.subsingleton_Hgr_structureModule (i + 1) (-(i : ℤ) - 1) (by omega) ?_
      by_cases hin : i + 1 = n
      · exact Or.inr (by omega)
      · exact Or.inl hin

end AlgebraicGeometry.ProjectiveSpace.Cohomology

end ExerRegularityResolution

section ExerRegularityInSequences

open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.ProjectiveSpace.GradedModule

universe u

namespace AlgebraicGeometry.ProjectiveSpace.Cohomology

variable {k : Type u} [Field k] (C : Cohomology k)

/-- **Exercise 2.3.4** (`exer:regularity-in-sequences`): let `0 → K → F → Q → 0` be a short
exact sequence of coherent sheaves on `ℙⁿ`. If `K` is `(m+1)`-regular and `F` is `m`-regular,
then `Q` is `m`-regular. -/
theorem isMRegular_of_shortExact {n : ℕ} {K F Q : GradedModule k n} {f : K ⟶ F} {g : F ⟶ Q}
    (hfg : ShortExact f g) {m : ℤ} (hK : C.IsMRegular K (m + 1)) (hF : C.IsMRegular F m) :
    C.IsMRegular Q m := by
  intro i hi
  refine C.subsingleton_H_X₃ hfg i (m - i) (hF i hi) ?_
  have := hK (i + 1) (by omega)
  have heq : m + 1 - ((i : ℤ) + 1) = m - (i : ℤ) := by ring
  rwa [Nat.cast_add, Nat.cast_one, heq] at this

end AlgebraicGeometry.ProjectiveSpace.Cohomology

end ExerRegularityInSequences
