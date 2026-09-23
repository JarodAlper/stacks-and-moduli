module

public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sets.Opens

/-!
# Krull dimension of a topological space at a point

Stacks Project tag **0055**, label `topology-definition-Krull`, in `topology.tex`,
§`0054` (Krull dimension).

> The *Krull dimension* of a topological space is the supremum of the lengths of chains of
> irreducible closed subsets. The dimension of `X` *at a point* `x` is the infimum of the
> dimensions of the open neighbourhoods of `x`.

Mathlib has the global notion as `topologicalKrullDim` (`Mathlib/Topology/KrullDimension.lean`)
but no pointwise version — `grep topologicalKrullDimAt` over Mathlib comes up empty. §4.5 of the
book needs the pointwise one, because the dimension of an algebraic stack at a point is defined
by comparing dimensions at points upstairs and downstairs on a presentation.

Unlike most obligations in this directory this one is fully proved.  The well-founded order on
`WithBot ℕ∞` shows that the displayed infimum is attained, so it agrees with the minimum in
the source.  The API also records monotonicity under shrinking and invariance under open
embeddings. Note the Stacks Project's related lemma `0B7I`
(`topology-lemma-dimension-supremum-local-dimensions`), that the global dimension is the supremum
of the local ones, is *not* proved here.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open TopologicalSpace

universe u v

/-- **Stacks 0055** (`topology-definition-Krull`), pointwise form. The Krull dimension of `T` at
`x` is the infimum of the Krull dimensions of the open neighbourhoods of `x`; the infimum is a
minimum by `exists_open_topologicalKrullDim_eq_atPoint`. -/
@[stacks 0055]
noncomputable def topologicalKrullDimAtPoint (T : Type u) [TopologicalSpace T] (x : T) :
    WithBot ℕ∞ :=
  ⨅ U : {U : Opens T // x ∈ U}, topologicalKrullDim U.1

/-- The dimension at a point is at most the dimension of any open neighbourhood. -/
theorem topologicalKrullDimAtPoint_le {T : Type u} [TopologicalSpace T] {x : T} (U : Opens T)
    (hx : x ∈ U) : topologicalKrullDimAtPoint T x ≤ topologicalKrullDim U :=
  iInf_le (fun U : {U : Opens T // x ∈ U} ↦ topologicalKrullDim U.1) ⟨U, hx⟩

/-- The dimension at a point is at most the dimension of the whole space. -/
theorem topologicalKrullDimAtPoint_le_topologicalKrullDim {T : Type u} [TopologicalSpace T]
    (x : T) : topologicalKrullDimAtPoint T x ≤ topologicalKrullDim T := by
  refine le_trans (topologicalKrullDimAtPoint_le ⊤ (by trivial)) ?_
  exact topologicalKrullDim_subspace_le T _

/-- The infimum defining the dimension at a point is attained by an open neighbourhood.

This uses the special well-founded order on `WithBot ℕ∞`; the analogous statement for an
arbitrary complete linear order would be false. -/
theorem exists_open_topologicalKrullDim_eq_atPoint
    {T : Type u} [TopologicalSpace T] (x : T) :
    ∃ U : Opens T, x ∈ U ∧ topologicalKrullDim U = topologicalKrullDimAtPoint T x := by
  let Nhd := {U : Opens T // x ∈ U}
  let _ : Nonempty Nhd := ⟨⟨⊤, by trivial⟩⟩
  obtain ⟨U, hU⟩ := ciInf_mem (fun U : Nhd ↦ topologicalKrullDim U.1)
  exact ⟨U.1, U.2, hU⟩

/-- If the dimension at a point is the finite value `n`, some open neighbourhood already has
dimension `n`. -/
theorem exists_open_topologicalKrullDim_eq_nat
    {T : Type u} [TopologicalSpace T] {x : T} {n : ℕ}
    (h : topologicalKrullDimAtPoint T x = (n : WithBot ℕ∞)) :
    ∃ U : Opens T, x ∈ U ∧ topologicalKrullDim U = (n : WithBot ℕ∞) := by
  obtain ⟨U, hxU, hU⟩ := exists_open_topologicalKrullDim_eq_atPoint x
  exact ⟨U, hxU, hU.trans h⟩

/-- Shrinking an open subspace cannot increase its topological Krull dimension. -/
theorem topologicalKrullDim_opens_mono
    {T : Type u} [TopologicalSpace T] {U V : Opens T} (hUV : U ≤ V) :
    topologicalKrullDim U ≤ topologicalKrullDim V :=
  (Opens.isOpenEmbedding_of_le hUV).isInducing.topologicalKrullDim_le

/-- Pointwise topological Krull dimension is invariant under open embeddings. -/
theorem Topology.IsOpenEmbedding.topologicalKrullDimAtPoint_eq
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsOpenEmbedding f) (x : X) :
    topologicalKrullDimAtPoint X x = topologicalKrullDimAtPoint Y (f x) := by
  apply le_antisymm
  · obtain ⟨V, hfxV, hV⟩ := exists_open_topologicalKrullDim_eq_atPoint (f x)
    let U : Opens X := Opens.comap ⟨f, hf.continuous⟩ V
    let hUV : (U : Set X).MapsTo f (V : Set Y) := fun _ h ↦ h
    calc
      topologicalKrullDimAtPoint X x ≤ topologicalKrullDim U :=
        topologicalKrullDimAtPoint_le U hfxV
      _ ≤ topologicalKrullDim V :=
        (hf.isEmbedding.restrict hUV).isInducing.topologicalKrullDim_le
      _ = topologicalKrullDimAtPoint Y (f x) := hV
  · obtain ⟨U, hxU, hU⟩ := exists_open_topologicalKrullDim_eq_atPoint x
    let V : Opens Y := ⟨f '' (U : Set X), hf.isOpenMap _ U.isOpen⟩
    let e : U ≃ₜ V := hf.isEmbedding.homeomorphImage (U : Set X)
    calc
      topologicalKrullDimAtPoint Y (f x) ≤ topologicalKrullDim V :=
        topologicalKrullDimAtPoint_le V ⟨x, hxU, rfl⟩
      _ = topologicalKrullDim U :=
        (IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph).symm
      _ = topologicalKrullDimAtPoint X x := hU
