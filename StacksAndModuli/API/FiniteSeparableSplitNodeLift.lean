module

public import StacksAndModuli.API.SplitNodeResidueFieldDescent

/-!
# Finite separable lifts to split nodes

This file packages the finite-separable splitting condition for a node over an arbitrary
field. It is the literal condition (5) in Proposition 6.2.4 of *Stacks and Moduli*: after
a finite separable field extension, a point above the original point is a split node.

The condition is exposed independently of the proposition's five-way equivalence. The
results here prove only its immediate residue-field consequences, using
`SplitNodeResidueFieldDescent`; they do not claim Proposition 6.2.4.

## Main definitions and results

* `AlgebraicGeometry.Scheme.fieldExtensionBaseChange`;
* `AlgebraicGeometry.Scheme.fieldExtensionBaseChangeTransition`;
* `AlgebraicGeometry.Scheme.HasFiniteSeparableSplitNodeLiftAt`;
* `AlgebraicGeometry.Scheme.
  hasFiniteSeparableSplitNodeLiftAt_of_splitNode_afterBaseChange`;
* `AlgebraicGeometry.Scheme.SplitNodeCoordinatesDescendToFiniteSeparableAt`;
* `AlgebraicGeometry.Scheme.IsNodeAt.
  hasFiniteSeparableSplitNodeLiftAt_of_coordinates_descend`;
* `AlgebraicGeometry.Scheme.HasFiniteSeparableSplitNodeLiftAt.
  residueField_finiteDimensional`;
* `AlgebraicGeometry.Scheme.HasFiniteSeparableSplitNodeLiftAt.
  residueField_isSeparable`.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- Base change of a scheme over `k` along a field extension `K/k`. -/
noncomputable abbrev fieldExtensionBaseChange
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))] : Scheme.{u} :=
  pullback (C ↘ Spec (CommRingCat.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))

/-- The projection from a field-extension base change to the original scheme. -/
noncomputable abbrev fieldExtensionBaseChangeProjection
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))] :
    fieldExtensionBaseChange k K C ⟶ C :=
  pullback.fst (C ↘ Spec (CommRingCat.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))

/-- The structure morphism of a field-extension base change. -/
noncomputable abbrev fieldExtensionBaseChangeStructure
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))] :
    fieldExtensionBaseChange k K C ⟶ Spec (CommRingCat.of K) :=
  pullback.snd (C ↘ Spec (CommRingCat.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))

/-- A `k`-embedding `K → L` induces the transition map `C_L ⟶ C_K` between
field-extension base changes. -/
noncomputable def fieldExtensionBaseChangeTransition
    (k K L : Type u) [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] (i : K →ₐ[k] L)
    (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))] :
    fieldExtensionBaseChange k L C ⟶ fieldExtensionBaseChange k K C :=
  pullback.lift
    (fieldExtensionBaseChangeProjection k L C)
    (fieldExtensionBaseChangeStructure k L C ≫
      Spec.map (CommRingCat.ofHom i))
    (by
      rw [Category.assoc, ← Spec.map_comp]
      have hi : (CommRingCat.ofHom (algebraMap k K)) ≫
          CommRingCat.ofHom i = CommRingCat.ofHom (algebraMap k L) := by
        ext a
        exact i.commutes a
      rw [hi]
      exact pullback.condition)

/-- A field-base-change transition followed by projection is the original projection. -/
@[reassoc (attr := simp)]
theorem fieldExtensionBaseChangeTransition_fst
    (k K L : Type u) [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] (i : K →ₐ[k] L)
    (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))] :
    fieldExtensionBaseChangeTransition k K L i C ≫
      fieldExtensionBaseChangeProjection k K C =
        fieldExtensionBaseChangeProjection k L C :=
  pullback.lift_fst _ _ _

/-- The structure map after a field-base-change transition is induced by the field
embedding. -/
@[reassoc (attr := simp)]
theorem fieldExtensionBaseChangeTransition_snd
    (k K L : Type u) [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] (i : K →ₐ[k] L)
    (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))] :
    fieldExtensionBaseChangeTransition k K L i C ≫
      fieldExtensionBaseChangeStructure k K C =
        fieldExtensionBaseChangeStructure k L C ≫
          Spec.map (CommRingCat.ofHom i) :=
  pullback.lift_snd _ _ _

/-- Background predicate for Proposition 6.2.4, condition (5): there is a finite separable
extension `K/k` and a point of `C_K` above `x` whose
completed local ring is the split-node ring over `K`.

This declaration packages the condition but asserts none of its equivalences with the
other conditions in Proposition 6.2.4. -/
noncomputable def HasFiniteSeparableSplitNodeLiftAt
    (k : Type u) [Field k] (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))] (x : C) : Prop :=
  ∃ (K : Type u) (hK : Field K),
    letI := hK
    ∃ hAlg : Algebra k K,
      letI := hAlg
      FiniteDimensional k K ∧
        Algebra.IsSeparable k K ∧
          ∃ y : (pullback (C ↘ Spec (CommRingCat.of k))
              (Spec.map (CommRingCat.ofHom (algebraMap k K)))).carrier,
            pullback.fst (C ↘ Spec (CommRingCat.of k))
                (Spec.map (CommRingCat.ofHom (algebraMap k K))) y = x ∧
              (letI : (pullback (C ↘ Spec (CommRingCat.of k))
                    (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Over
                    (Spec (CommRingCat.of K)) :=
                  ⟨pullback.snd (C ↘ Spec (CommRingCat.of k))
                    (Spec.map (CommRingCat.ofHom (algebraMap k K)))⟩;
                (pullback (C ↘ Spec (CommRingCat.of k))
                  (Spec.map (CommRingCat.ofHom (algebraMap k K)))).IsSplitNodeAt K y)

/-- A supplied split node above `x` after a finite separable field extension witnesses
`HasFiniteSeparableSplitNodeLiftAt`. -/
theorem hasFiniteSeparableSplitNodeLiftAt_of_splitNode_afterBaseChange
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [Algebra.IsSeparable k K]
    {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))] {x : C}
    (y : (pullback (C ↘ Spec (CommRingCat.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).carrier)
    (hyx : pullback.fst (C ↘ Spec (CommRingCat.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) y = x)
    (hy : (letI : (pullback (C ↘ Spec (CommRingCat.of k))
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Over
            (Spec (CommRingCat.of K)) :=
          ⟨pullback.snd (C ↘ Spec (CommRingCat.of k))
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))⟩;
        (pullback (C ↘ Spec (CommRingCat.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).IsSplitNodeAt K y)) :
    HasFiniteSeparableSplitNodeLiftAt k C x := by
  refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, y, hyx, ?_⟩
  exact hy

/-- The precise formal-local descent input needed to obtain a finite-separable model of a
geometric split node: its split completed-local chart is already defined at the image of
the point over some finite separable intermediate field of the chosen algebraic closure.

This predicate does not assert that such a field exists. Proving that assertion is the
missing completed-local descent step in the `(1) ⇒ (5)` direction of Proposition 6.2.4. -/
noncomputable def SplitNodeCoordinatesDescendToFiniteSeparableAt
    (k : Type u) [Field k]
    (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))]
    (y : geometricBaseChange k C) : Prop :=
  (geometricBaseChange k C).IsSplitNodeAt (AlgebraicClosure k) y →
    ∃ K : IntermediateField k (AlgebraicClosure k),
      FiniteDimensional k K ∧
        Algebra.IsSeparable k K ∧
          letI : (fieldExtensionBaseChange k K C).Over
              (Spec (CommRingCat.of K)) :=
            ⟨fieldExtensionBaseChangeStructure k K C⟩
          (fieldExtensionBaseChange k K C).IsSplitNodeAt K
            (fieldExtensionBaseChangeTransition k K (AlgebraicClosure k) K.val C y)

/-- A descended split chart at a geometric point above `x` supplies the exact
finite-separable split-node lift of `x`. -/
theorem SplitNodeCoordinatesDescendToFiniteSeparableAt.hasFiniteSeparableSplitNodeLiftAt
    {k : Type u} [Field k]
    {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))] {x : C}
    {y : geometricBaseChange k C}
    (hdesc : SplitNodeCoordinatesDescendToFiniteSeparableAt k C y)
    (hyx : geometricBaseChangeProjection k C y = x)
    (hy : (geometricBaseChange k C).IsSplitNodeAt (AlgebraicClosure k) y) :
    HasFiniteSeparableSplitNodeLiftAt k C x := by
  rcases hdesc hy with ⟨K, hfinite, hseparable, hsplit⟩
  let _ := hfinite
  let _ := hseparable
  let _ : (fieldExtensionBaseChange k K C).Over
      (Spec (CommRingCat.of K)) :=
    ⟨fieldExtensionBaseChangeStructure k K C⟩
  apply hasFiniteSeparableSplitNodeLiftAt_of_splitNode_afterBaseChange
    (fieldExtensionBaseChangeTransition k K (AlgebraicClosure k) K.val C y)
  · change (fieldExtensionBaseChangeTransition k K (AlgebraicClosure k) K.val C ≫
      fieldExtensionBaseChangeProjection k K C) y = x
    rw [fieldExtensionBaseChangeTransition_fst, hyx]
  · exact hsplit

/-- Reduction for Proposition 6.2.4 `(1) ⇒ (5)`: a geometric node has a finite
separable split-node lift once split completed-local coordinates descend at every
geometric witness above the point. No extra hypotheses on the scheme are used. -/
theorem IsNodeAt.hasFiniteSeparableSplitNodeLiftAt_of_coordinates_descend
    {k : Type u} [Field k]
    {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))] {x : C}
    (h : C.IsNodeAt k x)
    (hdesc : ∀ y : geometricBaseChange k C,
      geometricBaseChangeProjection k C y = x →
        SplitNodeCoordinatesDescendToFiniteSeparableAt k C y) :
    HasFiniteSeparableSplitNodeLiftAt k C x := by
  rcases h with ⟨y, hyx, hy⟩
  exact (hdesc y hyx).hasFiniteSeparableSplitNodeLiftAt hyx hy

/-- The finite-separable split-lift condition forces the residue field of the point to be
finite-dimensional over the ground field. -/
theorem HasFiniteSeparableSplitNodeLiftAt.residueField_finiteDimensional
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k))] {x : C}
    (h : HasFiniteSeparableSplitNodeLiftAt k C x) :
    letI := residueFieldAlgebra (C ↘ Spec (CommRingCat.of k)) x
    FiniteDimensional k (C.residueField x) := by
  rcases h with ⟨K, hK, hAlg, hfinite, hseparable, y, hyx, hy⟩
  let _ := hK
  let _ := hAlg
  let _ := hfinite
  let _ := hseparable
  let _ : (pullback (C ↘ Spec (CommRingCat.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Over
      (Spec (CommRingCat.of K)) :=
    ⟨pullback.snd (C ↘ Spec (CommRingCat.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))⟩
  have hresult := residueField_finiteDimensional_of_splitNode_after_baseChange
    (C ↘ Spec (CommRingCat.of k)) y hy
  rw [hyx] at hresult
  exact hresult

/-- The finite-separable split-lift condition forces the residue field of the point to be
separable over the ground field. -/
theorem HasFiniteSeparableSplitNodeLiftAt.residueField_isSeparable
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k))] {x : C}
    (h : HasFiniteSeparableSplitNodeLiftAt k C x) :
    letI := residueFieldAlgebra (C ↘ Spec (CommRingCat.of k)) x
    Algebra.IsSeparable k (C.residueField x) := by
  rcases h with ⟨K, hK, hAlg, hfinite, hseparable, y, hyx, hy⟩
  let _ := hK
  let _ := hAlg
  let _ := hfinite
  let _ := hseparable
  let _ : (pullback (C ↘ Spec (CommRingCat.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Over
      (Spec (CommRingCat.of K)) :=
    ⟨pullback.snd (C ↘ Spec (CommRingCat.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))⟩
  have hresult := residueField_isSeparable_of_splitNode_after_baseChange
    (C ↘ Spec (CommRingCat.of k)) y hy
  rw [hyx] at hresult
  exact hresult

end AlgebraicGeometry.Scheme
