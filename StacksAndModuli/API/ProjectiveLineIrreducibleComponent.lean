module

public import StacksAndModuli.API.ProjectiveSpaceOverSpecComparison
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.Topology.KrullDimension

/-!
# Projective-line images in one-dimensional spaces

A closed embedding of an irreducible space into a one-dimensional space has
irreducible-component image as soon as the source has a nontrivial chain of
irreducible closed subsets.  The projective line has such a chain: on
`Proj k[x₀, x₁]`, the zero homogeneous prime is a generic point and the closure of
the homogeneous prime `(x₀)` is a proper irreducible closed subset.

## Main results

* `TopologicalSpace.range_mem_irreducibleComponents_of_closedEmbedding_of_krullDim_le_one`:
  the general closed-embedding criterion.
* `AlgebraicGeometry.ProjectiveSpace.projectiveLine_irreducibleSpace`: projective
  one-space over a field is irreducible.
* `AlgebraicGeometry.ProjectiveSpace.projectiveLine_isReduced`: projective one-space
  over a field is reduced.
* `AlgebraicGeometry.ProjectiveSpace.exists_irreducibleClosed_lt_univ_projectiveLine`:
  its irreducible closed subsets contain a nontrivial chain.
* `AlgebraicGeometry.ProjectiveSpace.
    range_mem_irreducibleComponents_of_projectiveLine_closedEmbedding`: the image of
  a closed embedding of `ℙ¹` into a space of dimension at most one is an irreducible
  component.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace TopologicalSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The whole space, bundled as an irreducible closed subset of an irreducible
space. -/
def IrreducibleCloseds.univOfIrreducibleSpace [IrreducibleSpace X] :
    IrreducibleCloseds X :=
  ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩

/-- A closed embedding of an irreducible space with a proper irreducible closed
subset into a space of topological Krull dimension at most one has image an
irreducible component.

The image is a closed irreducible subset.  Dimension at most one says that it is
minimal or maximal in the poset of irreducible closed subsets.  Strict monotonicity
of the map on irreducible closeds rules out minimality. -/
theorem range_mem_irreducibleComponents_of_closedEmbedding_of_krullDim_le_one
    [IrreducibleSpace X] (f : X → Y) (hf : IsClosedEmbedding f)
    (hX : ∃ Z : IrreducibleCloseds X,
      Z < IrreducibleCloseds.univOfIrreducibleSpace)
    (hY : topologicalKrullDim Y ≤ 1) :
    Set.range f ∈ irreducibleComponents Y := by
  let U : IrreducibleCloseds X :=
    IrreducibleCloseds.univOfIrreducibleSpace
  let I : IrreducibleCloseds Y :=
    IrreducibleCloseds.map f hf.continuous U
  have hI : (I : Set Y) = Set.range f := by
    change closure (f '' Set.univ) = Set.range f
    rw [Set.image_univ, hf.isClosed_range.closure_eq]
  have hI_not_min : ¬ IsMin I := by
    obtain ⟨Z, hZ⟩ := hX
    have hmap : IrreducibleCloseds.map f hf.continuous Z < I :=
      IrreducibleCloseds.map_strictMono_of_isInducing hf.isInducing hZ
    intro hmin
    exact hmap.2 (hmin hmap.1)
  have hI_max : IsMax I :=
    ((Order.krullDim_le_one_iff.mp hY) I).resolve_left hI_not_min
  rw [irreducibleComponents_eq_maximals_closed]
  refine ⟨⟨hI ▸ I.isClosed, hI ▸ I.isIrreducible⟩, ?_⟩
  intro T hT hle
  let J : IrreducibleCloseds Y := ⟨T, hT.2, hT.1⟩
  have hIJ : I ≤ J := by
    change (I : Set Y) ⊆ T
    rwa [hI]
  have hJI := hI_max hIJ
  change T ⊆ Set.range f
  rw [← hI]
  exact hJI

end TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpace

open TopologicalSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

local notation "lineGrading" =>
  MvPolynomial.homogeneousSubmodule (Fin 2) k

/-- The zero homogeneous prime, regarded as the generic point of intrinsic
polynomial `Proj k[x₀, x₁]`. -/
noncomputable def polynomialLineGenericPoint :
    ProjectiveSpectrum lineGrading where
  asHomogeneousIdeal := ⊥
  isPrime := by
    change (⊥ : Ideal (MvPolynomial (Fin 2) k)).IsPrime
    exact Ideal.isPrime_bot
  not_irrelevant_le := by
    intro h
    have hX : MvPolynomial.X (0 : Fin 2) ∈
        HomogeneousIdeal.irrelevant lineGrading :=
      HomogeneousIdeal.mem_irrelevant_of_mem lineGrading Nat.one_pos
        (MvPolynomial.isHomogeneous_X k 0)
    have hXbot := h hX
    change MvPolynomial.X (0 : Fin 2) ∈
      (⊥ : Ideal (MvPolynomial (Fin 2) k)) at hXbot
    rw [Ideal.mem_bot] at hXbot
    exact MvPolynomial.X_ne_zero (R := k) (0 : Fin 2) hXbot

/-- The homogeneous prime `(x₀)` of intrinsic polynomial `Proj k[x₀, x₁]`. -/
noncomputable def polynomialLineAxisPoint :
    ProjectiveSpectrum lineGrading where
  asHomogeneousIdeal :=
    ⟨Ideal.span {MvPolynomial.X (0 : Fin 2)},
      Ideal.homogeneous_span lineGrading _ (by
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst x
        exact ⟨1, MvPolynomial.isHomogeneous_X k 0⟩)⟩
  isPrime := by
    change (Ideal.span {MvPolynomial.X (0 : Fin 2)}).IsPrime
    exact (Ideal.span_singleton_prime
      (MvPolynomial.X_ne_zero (R := k) (0 : Fin 2))).mpr
        MvPolynomial.X_prime
  not_irrelevant_le := by
    intro h
    have hX : MvPolynomial.X (1 : Fin 2) ∈
        HomogeneousIdeal.irrelevant lineGrading :=
      HomogeneousIdeal.mem_irrelevant_of_mem lineGrading Nat.one_pos
        (MvPolynomial.isHomogeneous_X k 1)
    have hmem := h hX
    change MvPolynomial.X (1 : Fin 2) ∈
      Ideal.span {MvPolynomial.X (0 : Fin 2)} at hmem
    rw [Ideal.mem_span_singleton, MvPolynomial.X_dvd_X] at hmem
    omega

/-- The zero homogeneous prime is a generic point of intrinsic polynomial
`Proj k[x₀, x₁]`. -/
theorem polynomialLineGenericPoint_closure :
    closure ({polynomialLineGenericPoint k} :
      Set (ProjectiveSpectrum lineGrading)) = Set.univ := by
  ext x
  constructor
  · intro
    exact Set.mem_univ _
  · intro
    rw [← ProjectiveSpectrum.le_iff_mem_closure]
    change (⊥ : HomogeneousIdeal lineGrading) ≤ x.asHomogeneousIdeal
    exact bot_le

/-- Intrinsic polynomial `Proj k[x₀, x₁]` is irreducible. -/
instance polynomialLine_irreducibleSpace :
    IrreducibleSpace (ProjectiveSpectrum lineGrading) := by
  rw [irreducibleSpace_def]
  change IsIrreducible (Set.univ : Set (ProjectiveSpectrum lineGrading))
  rw [← polynomialLineGenericPoint_closure k]
  exact isIrreducible_singleton.closure

/-- Intrinsic polynomial `Proj k[x₀, x₁]` is reduced. -/
instance polynomialLine_isReduced : IsReduced (Proj lineGrading) := by
  refine @isReduced_of_isReduced_stalk (Proj lineGrading) ?_
  intro x
  let _ : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
  let _ : _root_.IsReduced
      (HomogeneousLocalization.AtPrime lineGrading
        x.asHomogeneousIdeal.toIdeal) := isReduced_of_injective
    (algebraMap
      (HomogeneousLocalization.AtPrime lineGrading
        x.asHomogeneousIdeal.toIdeal)
      (Localization x.asHomogeneousIdeal.toIdeal.primeCompl))
    (by
      intro a b hab
      apply HomogeneousLocalization.val_injective
        x.asHomogeneousIdeal.toIdeal.primeCompl
      simpa only [HomogeneousLocalization.algebraMap_apply] using hab)
  exact isReduced_of_injective (Proj.stalkIso lineGrading x).hom.hom
    (ConcreteCategory.bijective_of_isIso
      (Proj.stalkIso lineGrading x).hom).1

/-- The closure of the axis point `(x₀)` in intrinsic polynomial
`Proj k[x₀, x₁]`, bundled as an irreducible closed subset. -/
noncomputable def polynomialLineAxisClosure :
    IrreducibleCloseds (ProjectiveSpectrum lineGrading) where
  carrier := closure ({polynomialLineAxisPoint k} :
    Set (ProjectiveSpectrum lineGrading))
  isIrreducible' := isIrreducible_singleton.closure
  isClosed' := isClosed_closure

/-- The axis closure is a proper irreducible closed subset of intrinsic
polynomial `Proj k[x₀, x₁]`. -/
theorem polynomialLineAxisClosure_lt_univ :
    polynomialLineAxisClosure k <
      IrreducibleCloseds.univOfIrreducibleSpace := by
  constructor
  · exact Set.subset_univ _
  · intro h
    have hmem : polynomialLineGenericPoint k ∈
        (polynomialLineAxisClosure k : Set (ProjectiveSpectrum lineGrading)) :=
      h (Set.mem_univ _)
    rw [show (polynomialLineAxisClosure k :
        Set (ProjectiveSpectrum lineGrading)) =
      closure ({polynomialLineAxisPoint k} :
        Set (ProjectiveSpectrum lineGrading)) from rfl,
      ← ProjectiveSpectrum.le_iff_mem_closure] at hmem
    have hXaxis : MvPolynomial.X (0 : Fin 2) ∈
        (polynomialLineAxisPoint k).asHomogeneousIdeal := by
      change MvPolynomial.X (0 : Fin 2) ∈
        Ideal.span {MvPolynomial.X (0 : Fin 2)}
      exact Ideal.mem_span_singleton_self _
    have hXbot := hmem hXaxis
    change MvPolynomial.X (0 : Fin 2) ∈
      (⊥ : Ideal (MvPolynomial (Fin 2) k)) at hXbot
    rw [Ideal.mem_bot] at hXbot
    exact MvPolynomial.X_ne_zero (R := k) (0 : Fin 2) hXbot

/-- The existing comparison with polynomial `Proj`, viewed on underlying spaces. -/
noncomputable def projectiveLinePolynomialHomeomorph :
    Scheme.projectiveSpaceOver 1 (Spec (CommRingCat.of k)) ≃ₜ
      ProjectiveSpectrum lineGrading :=
  (projectiveSpaceOverSpecIso 1 k).hom.homeomorph

/-- Projective one-space over a field is irreducible. -/
instance projectiveLine_irreducibleSpace :
    IrreducibleSpace
      (Scheme.projectiveSpaceOver 1 (Spec (CommRingCat.of k))) :=
  (projectiveLinePolynomialHomeomorph k).irreducibleSpace_iff.mpr inferInstance

/-- Projective one-space over a field is reduced. -/
instance projectiveLine_isReduced :
    IsReduced (Scheme.projectiveSpaceOver 1 (Spec (CommRingCat.of k))) := by
  have hraw : IsReduced
      (Proj (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) k)) := by
    change IsReduced (Proj lineGrading)
    infer_instance
  exact ObjectProperty.prop_of_iso (fun X : Scheme ↦ IsReduced X)
    (projectiveSpaceOverSpecIso 1 k).symm hraw

/-- The transport of the intrinsic axis closure to relative projective one-space. -/
noncomputable def projectiveLineAxisClosure :
    IrreducibleCloseds
      (Scheme.projectiveSpaceOver 1 (Spec (CommRingCat.of k))) :=
  IrreducibleCloseds.map (projectiveLinePolynomialHomeomorph k).symm
    (projectiveLinePolynomialHomeomorph k).symm.continuous
      (polynomialLineAxisClosure k)

/-- The transported axis closure is a proper irreducible closed subset of relative
projective one-space. -/
theorem projectiveLineAxisClosure_lt_univ :
    projectiveLineAxisClosure k <
      IrreducibleCloseds.univOfIrreducibleSpace := by
  let e := projectiveLinePolynomialHomeomorph k
  have hlt := IrreducibleCloseds.map_strictMono_of_isInducing
    e.symm.isInducing (polynomialLineAxisClosure_lt_univ k)
  change projectiveLineAxisClosure k < _
  have hmap_univ :
      IrreducibleCloseds.map e.symm e.symm.continuous
          IrreducibleCloseds.univOfIrreducibleSpace =
        (IrreducibleCloseds.univOfIrreducibleSpace :
          IrreducibleCloseds
            (Scheme.projectiveSpaceOver 1 (Spec (CommRingCat.of k)))) := by
    apply IrreducibleCloseds.ext
    change closure (e.symm '' Set.univ) = Set.univ
    rw [Set.image_univ, e.symm.surjective.range_eq, closure_univ]
  rw [hmap_univ] at hlt
  exact hlt

/-- Relative projective one-space has a proper irreducible closed subset. -/
theorem exists_irreducibleClosed_lt_univ_projectiveLine :
    ∃ Z : IrreducibleCloseds
        (Scheme.projectiveSpaceOver 1 (Spec (CommRingCat.of k))),
      Z < IrreducibleCloseds.univOfIrreducibleSpace :=
  ⟨projectiveLineAxisClosure k, projectiveLineAxisClosure_lt_univ k⟩

/-- The image of a closed embedding of projective one-space into a space of
topological Krull dimension at most one is an irreducible component. -/
theorem range_mem_irreducibleComponents_of_projectiveLine_closedEmbedding
    {Y : Type*} [TopologicalSpace Y]
    (f : Scheme.projectiveSpaceOver 1 (Spec (CommRingCat.of k)) → Y)
    (hf : IsClosedEmbedding f) (hY : topologicalKrullDim Y ≤ 1) :
    Set.range f ∈ irreducibleComponents Y :=
  TopologicalSpace.range_mem_irreducibleComponents_of_closedEmbedding_of_krullDim_le_one
    f hf (exists_irreducibleClosed_lt_univ_projectiveLine k) hY

end AlgebraicGeometry.ProjectiveSpace

end
