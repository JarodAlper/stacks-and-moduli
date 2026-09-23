module

public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv

/-!
# The opens of an open subspace are the opens below it

For `U : Opens X` the poset `Opens ↥U` is isomorphic to the slice `Over U` in `Opens X`: an
open of the subspace is the same thing as an open of `X` contained in `U`.

This is the categorical bookkeeping that lets a statement about `Hⁿ` on the space `↥U` be read
as a statement about the *site-local* cohomology `H'ⁿ(U, -)` on `X`, since
`StacksAndModuli/API/SheafCohomologyOpenExact.lean` identifies `F.H' n U` with `Hⁿ` on the slice site
`Over U`.

Both functors are already in Mathlib — `TopologicalSpace.Opens.isOpenEmbedding.functor` and
`TopologicalSpace.Opens.map U.inclusion'` — and what is added here is that they are mutually
inverse on the slice.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory TopologicalSpace

namespace TopologicalSpace.Opens

variable {X : TopCat.{u}} (U : Opens X)

/-- The image of an open of `↥U` is contained in `U`. -/
lemma isOpenEmbedding_functor_obj_le (V : Opens ↥U) :
    U.isOpenEmbedding.functor.obj V ≤ U := by
  rintro x ⟨y, -, rfl⟩
  exact y.2

/-- Pulling an open of `↥U` back after pushing it forward changes nothing. -/
lemma map_inclusion_functor_obj (V : Opens ↥U) :
    (Opens.map U.inclusion').obj (U.isOpenEmbedding.functor.obj V) = V := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact (Subtype.ext hxy : y = x) ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Pushing an open of `X` below `U` forward after pulling it back changes nothing. -/
lemma functor_obj_map_inclusion {V : Opens X} (hV : V ≤ U) :
    U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion').obj V) = V := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, hV hx⟩, hx, rfl⟩

/-- The slice `Over U` in `Opens X` is thin, being a slice of a poset. -/
instance : Quiver.IsThin (Over U) := fun _ _ => ⟨fun _ _ => Over.OverMorphism.ext
  (Subsingleton.elim _ _)⟩

/-- **The opens of an open subspace are the opens below it.** -/
noncomputable def overEquiv : Opens ↥U ≌ Over U where
  functor :=
    { obj := fun V => Over.mk (homOfLE (isOpenEmbedding_functor_obj_le U V))
      map := fun {V W} i => Over.homMk (U.isOpenEmbedding.functor.map i) }
  inverse :=
    { obj := fun V => (Opens.map U.inclusion').obj V.left
      map := fun {V W} i => (Opens.map U.inclusion').map i.left }
  unitIso := NatIso.ofComponents
    (fun V => eqToIso (map_inclusion_functor_obj U V).symm)
    (fun _ => Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents
    (fun V => Over.isoMk (eqToIso (functor_obj_map_inclusion U (leOfHom V.hom)))
      (Subsingleton.elim _ _))
    (fun _ => Subsingleton.elim _ _)

/-- Membership in the slice topology is pointwise on the underlying open. -/
lemma mem_over_grothendieckTopology {V : Over U} (S : Sieve V) :
    S ∈ ((Opens.grothendieckTopology X).over U) V ↔
      ∀ x ∈ V.left, ∃ (W : Over U) (f : W ⟶ V), S.arrows f ∧ x ∈ W.left := by
  rw [GrothendieckTopology.mem_over_iff, Opens.mem_grothendieckTopology]
  constructor
  · intro h x hx
    obtain ⟨W, f, hf, hxW⟩ := h x hx
    obtain ⟨W', g, i, hg, -⟩ := hf
    exact ⟨W', g, hg, i.le hxW⟩
  · intro h x hx
    obtain ⟨W, f, hf, hxW⟩ := h x hx
    exact ⟨W.left, f.left, ⟨W, f, 𝟙 _, hf, by simp⟩, hxW⟩

instance isEquivalence_overEquiv_inverse : (overEquiv U).inverse.IsEquivalence :=
  inferInstanceAs ((overEquiv U).inverse.IsEquivalence)

/-- **The slice site over `U` is the site of opens of `↥U`.** -/
instance isDenseSubsite_overEquiv_inverse :
    (overEquiv U).inverse.IsDenseSubsite ((Opens.grothendieckTopology X).over U)
      (Opens.grothendieckTopology ↥U) where
  functorPushforward_mem_iff {V S} := by
    rw [mem_over_grothendieckTopology, Opens.mem_grothendieckTopology]
    constructor
    · intro h x hx
      have hxU : x ∈ U := (leOfHom V.hom) hx
      obtain ⟨W', f', hf', hyW'⟩ := h ⟨x, hxU⟩ hx
      obtain ⟨W₀, g, i, hg, -⟩ := hf'
      exact ⟨W₀, g, hg, (leOfHom i) hyW'⟩
    · intro h y hy
      obtain ⟨W, f, hf, hxW⟩ := h (y : X) hy
      exact ⟨(overEquiv U).inverse.obj W, (overEquiv U).inverse.map f,
        ⟨W, f, 𝟙 _, hf, by simp⟩, hxW⟩

end TopologicalSpace.Opens
