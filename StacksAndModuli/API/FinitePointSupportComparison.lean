module

public import StacksAndModuli.API.PointSupportStalkSupport
public import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Maps to finite sums of residue-point modules

A morphism from a scheme module to the residue-point module at `x` is adjoint to a
morphism from its pullback to `Spec κ(x)`.  This file combines those adjoint
transposes over a finite family of points, using the finite coproduct as a biproduct.

It also supplies a cokernel interface: a morphism defined after pullback which kills a
given map descends automatically from that map's cokernel.  Finally, for a family of
distinct closed points, a finite point-support comparison is an isomorphism once its
component at each point is an isomorphism on that point's stalk.

## Main definitions and results

* `AlgebraicGeometry.Scheme.Modules.residuePointSupportAdjoint`: transpose a morphism
  after pullback to the canonical residue-point module.
* `AlgebraicGeometry.Scheme.Modules.cokernelToResiduePointSupportOfPullbackCompEqZero`:
  descend such a transpose through a cokernel.
* `AlgebraicGeometry.Scheme.Modules.finiteResiduePointSupportLift`: assemble finitely
  many component maps into the finite residue-point module.
* `AlgebraicGeometry.Scheme.Modules.isIso_finiteResiduePointSupportLift_of_stalkwise`:
  the componentwise stalk criterion for a supported source.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v w z

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Transpose a morphism from the pullback of `M` to the structure module of
`Spec κ(x)` into a morphism from `M` to the canonical residue-point module at `x`. -/
noncomputable def residuePointSupportAdjoint (M : X.Modules) (x : X)
    (f : (pullback (X.fromSpecResidueField x)).obj M ⟶
      structureModule (Spec (X.residueField x))) :
    M ⟶ residuePointSupportModule X x :=
  (pullbackPushforwardAdjunction (X.fromSpecResidueField x)).homEquiv _ _ f

/-- Transposing after precomposition agrees with precomposing the transpose. -/
@[reassoc]
lemma comp_residuePointSupportAdjoint {M N : X.Modules} (g : M ⟶ N) (x : X)
    (f : (pullback (X.fromSpecResidueField x)).obj N ⟶
      structureModule (Spec (X.residueField x))) :
    g ≫ residuePointSupportAdjoint N x f =
      residuePointSupportAdjoint M x
        ((pullback (X.fromSpecResidueField x)).map g ≫ f) := by
  exact
    ((pullbackPushforwardAdjunction
      (X.fromSpecResidueField x)).homEquiv_naturality_left g f).symm

/-- A morphism defined after pullback to a residue point and killing `g` descends from
the cokernel of `g` to the residue-point module. -/
noncomputable def cokernelToResiduePointSupportOfPullbackCompEqZero
    {M N : X.Modules} (g : M ⟶ N) (x : X)
    (f : (pullback (X.fromSpecResidueField x)).obj N ⟶
      structureModule (Spec (X.residueField x)))
    (hf : (pullback (X.fromSpecResidueField x)).map g ≫ f = 0) :
    cokernel g ⟶ residuePointSupportModule X x :=
  cokernel.desc g (residuePointSupportAdjoint N x f) (by
    rw [comp_residuePointSupportAdjoint, hf]
    exact (pullbackPushforwardAdjunction
      (X.fromSpecResidueField x)).homAddEquiv_zero _ _)

/-- The cokernel projection followed by the descended residue-point comparison is the
adjoint transpose from the middle term. -/
@[reassoc (attr := simp)]
lemma cokernel_π_cokernelToResiduePointSupportOfPullbackCompEqZero
    {M N : X.Modules} (g : M ⟶ N) (x : X)
    (f : (pullback (X.fromSpecResidueField x)).obj N ⟶
      structureModule (Spec (X.residueField x)))
    (hf : (pullback (X.fromSpecResidueField x)).map g ≫ f = 0) :
    cokernel.π g ≫
        cokernelToResiduePointSupportOfPullbackCompEqZero g x f hf =
      residuePointSupportAdjoint N x f := by
  apply cokernel.π_desc

/-- Assemble a finite family of morphisms to residue-point modules into one morphism
to their finite coproduct.  Finiteness makes this coproduct a biproduct. -/
noncomputable def finiteResiduePointSupportLift
    {J : Type u} [Finite J] (M : X.Modules) (x : J → X)
    (f : ∀ j, M ⟶ residuePointSupportModule X (x j)) :
    M ⟶ finiteResiduePointSupportModule X x := by
  classical
  let _ := Fintype.ofFinite J
  exact ∑ j, f j ≫ Sigma.ι
    (fun i ↦ residuePointSupportModule X (x i)) j

/-- The projection from a finite residue-point module to one of its summands. -/
noncomputable def finiteResiduePointSupportπ
    {J : Type u} [Finite J] (x : J → X) (j : J) :
    finiteResiduePointSupportModule X x ⟶
      residuePointSupportModule X (x j) := by
  classical
  exact Sigma.π (fun i ↦ residuePointSupportModule X (x i)) j

/-- Projection of a finite residue-point-support lift to one summand recovers the
corresponding component map. -/
@[reassoc (attr := simp)]
lemma finiteResiduePointSupportLift_comp_π
    {J : Type u} [Finite J] (M : X.Modules) (x : J → X)
    (f : ∀ j, M ⟶ residuePointSupportModule X (x j)) (j : J) :
    finiteResiduePointSupportLift M x f ≫
        finiteResiduePointSupportπ x j = f j := by
  classical
  let _ := Fintype.ofFinite J
  change finiteResiduePointSupportLift M x f ≫
      Sigma.π (fun i ↦ residuePointSupportModule X (x i)) j = f j
  rw [finiteResiduePointSupportLift, Preadditive.sum_comp]
  calc
    ∑ i, (f i ≫ Sigma.ι
        (fun l ↦ residuePointSupportModule X (x l)) i) ≫
          Sigma.π (fun l ↦ residuePointSupportModule X (x l)) j =
        (f j ≫ Sigma.ι
          (fun l ↦ residuePointSupportModule X (x l)) j) ≫
            Sigma.π (fun l ↦ residuePointSupportModule X (x l)) j := by
      apply Fintype.sum_eq_single j
      intro i hij
      rw [Category.assoc, Sigma.ι_π_of_ne _ hij, comp_zero]
    _ = f j := by
      rw [Category.assoc, Sigma.ι_π_eq_id, Category.comp_id]

/-- Assemble morphisms given on the residue-point pullbacks of `M`. -/
noncomputable def finiteResiduePointSupportLiftOfPullback
    {J : Type u} [Finite J] (M : X.Modules) (x : J → X)
    (f : ∀ j, (pullback (X.fromSpecResidueField (x j))).obj M ⟶
      structureModule (Spec (X.residueField (x j)))) :
    M ⟶ finiteResiduePointSupportModule X x :=
  finiteResiduePointSupportLift M x fun j ↦
    residuePointSupportAdjoint M (x j) (f j)

/-- Assemble finite residue-point maps obtained by descending local pullback maps from
a common cokernel. -/
noncomputable def cokernelToFiniteResiduePointSupportOfPullbackCompEqZero
    {J : Type u} [Finite J] {M N : X.Modules} (g : M ⟶ N) (x : J → X)
    (f : ∀ j, (pullback (X.fromSpecResidueField (x j))).obj N ⟶
      structureModule (Spec (X.residueField (x j))))
    (hf : ∀ j, (pullback (X.fromSpecResidueField (x j))).map g ≫ f j = 0) :
    cokernel g ⟶ finiteResiduePointSupportModule X x :=
  finiteResiduePointSupportLift (cokernel g) x fun j ↦
    cokernelToResiduePointSupportOfPullbackCompEqZero g (x j) (f j) (hf j)

/-- A functor sends the projection of a finite coproduct to an isomorphism if all the
other summands become zero. -/
theorem isIso_map_coproduct_π_of_isZero
    {C : Type v} {D : Type w} [Category.{u} C] [Preadditive C]
    [Category.{u} D] [Preadditive D]
    {J : Type z} [Finite J] [DecidableEq J] (F : C ⥤ D) [F.Additive]
    (A : J → C) [HasCoproduct A] (j : J)
    (hA : ∀ i, i ≠ j → IsZero (F.obj (A i))) :
    IsIso (F.map (Sigma.π A j)) := by
  let _ := Fintype.ofFinite J
  have htotal : ∑ i, Sigma.π A i ≫ Sigma.ι A i = 𝟙 (∐ A) := by
    apply Sigma.hom_ext
    intro i
    rw [Preadditive.comp_sum]
    rw [Category.comp_id]
    calc
      ∑ j, Sigma.ι A i ≫ Sigma.π A j ≫ Sigma.ι A j =
          Sigma.ι A i ≫ Sigma.π A i ≫ Sigma.ι A i := by
        apply Fintype.sum_eq_single i
        intro j hij
        rw [← Category.assoc, Sigma.ι_π_of_ne _ (Ne.symm hij), zero_comp]
      _ = Sigma.ι A i := by
        rw [← Category.assoc, Sigma.ι_π_eq_id,
          Category.id_comp]
  let e : F.obj (∐ A) ≅ F.obj (A j) :=
    { hom := F.map (Sigma.π A j)
      inv := F.map (Sigma.ι A j)
      hom_inv_id := by
        rw [← F.map_comp, ← F.map_id, ← htotal]
        have hmapsum : F.map (∑ i, Sigma.π A i ≫ Sigma.ι A i) =
            ∑ i, F.map (Sigma.π A i ≫ Sigma.ι A i) := by
          change F.mapAddHom (∑ i, Sigma.π A i ≫ Sigma.ι A i) =
            ∑ i, F.mapAddHom (Sigma.π A i ≫ Sigma.ι A i)
          apply map_sum
        rw [hmapsum]
        symm
        apply Finset.sum_eq_single j
        · intro i _ hij
          rw [F.map_comp,
            hA i hij |>.eq_of_tgt (F.map (Sigma.π A i)) 0,
            zero_comp]
        · intro hj
          exact (hj (Finset.mem_univ j)).elim
      inv_hom_id := by
        rw [← F.map_comp, Sigma.ι_π_eq_id, F.map_id] }
  exact e.isIso_hom

/-- For distinct closed points, the projection from the finite residue-point module to
the summand at `x j` is an isomorphism on the stalk at `x j`. -/
theorem isIso_stalkFunctor_map_finiteResiduePointSupportπ
    {J : Type u} [Finite J] (x : J → X) (hx : ∀ j, IsClosed ({x j} : Set X))
    (hinj : Function.Injective x) (j : J) :
    IsIso (((toPresheaf X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (x j)).map
        (finiteResiduePointSupportπ x j))) := by
  classical
  let _ := Fintype.ofFinite J
  let _ : (toPresheaf X).Additive :=
    { map_add := by
        intro A B f g
        rfl }
  change IsIso (((toPresheaf X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (x j)).map
      (Sigma.π (fun i ↦ residuePointSupportModule X (x i)) j)))
  apply isIso_map_coproduct_π_of_isZero
  intro i hij
  have hne : x j ≠ x i := by
    intro h
    exact hij (hinj h.symm)
  have hsupp := stalkSupport_residuePointSupportModule_subset_singleton
    X (x i) (hx i)
  have hnot : x j ∉ stalkSupport (residuePointSupportModule X (x i)) := by
    intro hmem
    exact hne (hsupp hmem)
  simpa only [stalkSupport, Set.mem_ofPred_eq, not_not] using hnot

/-- A comparison from a module supported on a finite family of distinct closed points
to the corresponding finite residue-point module is an isomorphism if each component
map is an isomorphism on the stalk of its own point. -/
theorem isIso_finiteResiduePointSupportLift_of_stalkwise
    {J : Type u} [Finite J] (M : X.Modules) (x : J → X)
    (hx : ∀ j, IsClosed ({x j} : Set X)) (hinj : Function.Injective x)
    (hM : stalkSupport M ⊆ Set.range x)
    (f : ∀ j, M ⟶ residuePointSupportModule X (x j))
    (hf : ∀ j, IsIso ((toPresheaf X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (x j)).map (f j))) :
    IsIso (finiteResiduePointSupportLift M x f) := by
  let _ := Fintype.ofFinite J
  apply isIso_of_stalkFunctor_map_iso_on_support
    (finiteResiduePointSupportLift M x f) (Set.range x) hM
    (stalkSupport_finiteResiduePointSupportModule_subset_range X x hx)
  intro y hy
  obtain ⟨j, rfl⟩ := hy
  let F := toPresheaf X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (x j)
  have hproj : IsIso (F.map
      (finiteResiduePointSupportπ x j)) :=
    isIso_stalkFunctor_map_finiteResiduePointSupportπ x hx hinj j
  let _ : IsIso (F.map
      (finiteResiduePointSupportπ x j)) := hproj
  let _ : IsIso (F.map (f j)) := hf j
  have hcomp : IsIso
      (F.map (finiteResiduePointSupportLift M x f) ≫
        F.map (finiteResiduePointSupportπ x j)) := by
    rw [← F.map_comp, finiteResiduePointSupportLift_comp_π]
    infer_instance
  let _ : IsIso
      (F.map (finiteResiduePointSupportLift M x f) ≫
        F.map (finiteResiduePointSupportπ x j)) := hcomp
  exact IsIso.of_isIso_comp_right
    (F.map (finiteResiduePointSupportLift M x f))
    (F.map (finiteResiduePointSupportπ x j))

end AlgebraicGeometry.Scheme.Modules

end
