module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Refining a smooth surjection by one from an affine scheme

A smooth surjective morphism `g : X' ⟶ X` onto a *quasi-compact* scheme admits an affine
refinement: there are an affine `W` and `ρ : W ⟶ X'` with `ρ ≫ g` still smooth and
surjective. Take the affine cover of `X'`, push its pieces forward — their images are open
because a smooth morphism is universally open — extract a finite subcover of `X`, and let
`W` be the (finite, hence affine) coproduct of the chosen pieces.

This is the reduction step that turns a ring-level descent statement along a smooth
faithfully flat map into a statement about morphisms of schemes: given an affine `V` in the
target, it produces an affine `W` mapping smooth-surjectively onto `V`, so that the
corresponding map of global sections is smooth and faithfully flat. Together with
`StacksAndModuli/API/FiniteTypeSmoothDescent.lean` it is what source-locality of "locally of finite
type" along smooth surjections needs — see the `def:properties-of-morphisms-of-stacks` entry
in `StacksAndModuli/Section4.3-Properties/COMMENTARY.md`.

## Main results

* `AlgebraicGeometry.exists_affine_smooth_surjective`: the affine refinement. The refining
  morphism `ρ` is itself étale, hence locally of finite type and formally unramified (it is
  a finite coproduct of open immersions), which is what lets a finite-type or
  formally-unramified hypothesis on `g ≫ f` be transported to `ρ ≫ g ≫ f`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A smooth surjective morphism onto a quasi-compact scheme is refined by one from an
affine scheme. -/
lemma exists_affine_smooth_surjective {X X' : Scheme.{u}} [CompactSpace X] (g : X' ⟶ X)
    [Smooth g] [Surjective g] :
    ∃ (W : Scheme.{u}) (_ : IsAffine W) (ρ : W ⟶ X'),
      Etale ρ ∧ Smooth (ρ ≫ g) ∧ Surjective (ρ ≫ g) := by
  classical
  let 𝒰 := X'.affineCover
  have hgopen : IsOpenMap g.base := by
    have : UniversallyOpen g := inferInstance
    exact this.universally_isOpenMap _ _ _ (IsPullback.of_id_snd (f := g))
  have hrange : ∀ i, Set.range ((𝒰.f i ≫ g).base) = g.base '' (Set.range (𝒰.f i).base) := by
    intro i
    simp [Scheme.Hom.comp_base, Set.range_comp]
  have hopen : ∀ i, IsOpen (g.base '' (Set.range (𝒰.f i).base)) := fun i ↦
    hgopen _ (𝒰.f i).isOpenEmbedding.isOpen_range
  have hcover : (Set.univ : Set X) ⊆ ⋃ i, g.base '' (Set.range (𝒰.f i).base) := by
    intro x _
    obtain ⟨x', hx'⟩ := (Surjective.surj (f := g)) x
    obtain ⟨i, y, hy⟩ := 𝒰.exists_eq x'
    exact Set.mem_iUnion.mpr ⟨i, ⟨x', ⟨y, hy⟩, hx'⟩⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _ hopen hcover
  refine ⟨∐ (fun i : t ↦ 𝒰.X i.1), inferInstance,
    Sigma.desc (fun i : t ↦ 𝒰.f i.1), ?_, ?_, ?_⟩
  · exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale) (fun _ ↦ inferInstance)
  · have he : (Sigma.desc (fun i : t ↦ 𝒰.f i.1) ≫ g) =
        Sigma.desc (fun i : t ↦ 𝒰.f i.1 ≫ g) := by
      apply Sigma.hom_ext
      intro i
      simp
    rw [he]
    exact IsZariskiLocalAtSource.sigmaDesc (fun _ ↦ inferInstance)
  · have he : (Sigma.desc (fun i : t ↦ 𝒰.f i.1) ≫ g) =
        Sigma.desc (fun i : t ↦ 𝒰.f i.1 ≫ g) := by
      apply Sigma.hom_ext
      intro i
      simp
    rw [he]
    refine Surjective.sigmaDesc_of_union_range_eq_univ ?_
    refine Set.eq_univ_of_univ_subset ?_
    intro x _
    have hx := ht (Set.mem_univ x)
    simp only [Set.mem_iUnion, exists_prop] at hx
    obtain ⟨i, hi, hxi⟩ := hx
    exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, by rw [hrange]; exact hxi⟩

end AlgebraicGeometry
