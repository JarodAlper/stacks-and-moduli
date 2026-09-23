module

public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.CategoryTheory.HomCongr

/-!
# Faithfully flat descent for module properties

Supporting API with no Stacks Project counterpart of its own: the module-level descent
statements used by the affine-local form of
`prop:fpqc-descent-for-properties-of-quasi-coherent-sheaves` in §3.1.

Mathlib supplies the `Module.Finite` case as
`Module.Finite.of_finite_tensorProduct_of_faithfullyFlat`, and the `Module.Flat` case as
`Module.Flat.of_flat_tensorProduct`. It does **not** supply the `Module.FinitePresentation`
case: `Mathlib/RingTheory/Finiteness/Descent.lean` descends `Algebra.FinitePresentation`, not
`Module.FinitePresentation`. That gap, and the `Module.Projective` case which depends on it,
are filled here.

Main declarations:
- `Module.Finite.of_baseChange_faithfullyFlat`;
- `Module.FinitePresentation.of_baseChange_faithfullyFlat`;
- `Module.Projective.of_baseChange_faithfullyFlat`.
- `ModuleCat.overlapCancel`: identifies the module on the tensor-square overlap with
  the extension/restriction comonad.
- `ModuleCat.overlapHomEquiv`: turns a kernel-pair overlap morphism into a Beck
  coalgebra coaction.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open TensorProduct
open scoped ChangeOfRings

universe u v w

variable (R : Type u) (M : Type w) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module.FaithfullyFlat R S]

/-- A module is finitely generated if its base change along a faithfully flat ring map is. -/
theorem Module.Finite.of_baseChange_faithfullyFlat [Module.Finite S (S ⊗[R] M)] :
    Module.Finite R M :=
  Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S

/-- The range of the base change of a submodule inclusion is the base change of the
submodule. -/
theorem Submodule.range_baseChange_subtype (K : Submodule R M) :
    LinearMap.range (K.subtype.baseChange S) = K.baseChange S := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s k =>
      rw [LinearMap.baseChange_tmul]
      exact Submodule.tmul_mem_baseChange_of_mem s k.2
    | add x y hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy
  · rw [Submodule.baseChange_eq_span, Submodule.span_le]
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨(1 : S) ⊗ₜ ⟨k, hk⟩, rfl⟩

/-- Finite generation of a submodule descends along a faithfully flat base change. -/
theorem Submodule.FG.of_baseChange_faithfullyFlat (K : Submodule R M)
    (hfg : (K.baseChange S).FG) : K.FG := by
  classical
  obtain ⟨gens, hgens⟩ := hfg
  have hmem : ∀ g ∈ gens, (g : S ⊗[R] M) ∈ LinearMap.range (K.subtype.baseChange S) := by
    intro g hg
    rw [Submodule.range_baseChange_subtype]
    rw [← hgens]
    exact Submodule.subset_span hg
  choose lift hlift using fun (g : gens) ↦ hmem g g.2
  have hrepr : ∀ g : gens, ∃ t : Finset (S × K),
      lift g = ∑ x ∈ t, x.1 ⊗ₜ[R] x.2 := by
    intro g
    obtain ⟨t, ht⟩ := TensorProduct.exists_finset (lift g)
    exact ⟨t, ht⟩
  choose supp hsupp using hrepr
  set T : Finset M := Finset.univ.biUnion
    (fun g : gens ↦ (supp g).image (fun x ↦ (x.2 : M))) with hT
  have hTK : (T : Set M) ⊆ K := by
    intro k hk
    simp only [hT, Finset.coe_biUnion, Finset.coe_image, Set.mem_iUnion] at hk
    obtain ⟨g, -, x, -, rfl⟩ := hk
    exact x.2.2
  set K₀ : Submodule R M := Submodule.span R (T : Set M) with hK₀
  have hle : K₀ ≤ K := Submodule.span_le.mpr hTK
  have hbase : K.baseChange S ≤ K₀.baseChange S := by
    rw [← hgens, Submodule.span_le]
    intro g hg
    have h1 : (g : S ⊗[R] M) = (K.subtype.baseChange S) (lift ⟨g, hg⟩) :=
      (hlift ⟨g, hg⟩).symm
    rw [h1, hsupp ⟨g, hg⟩, map_sum]
    apply Submodule.sum_mem
    intro x hx
    rw [LinearMap.baseChange_tmul]
    refine Submodule.tmul_mem_baseChange_of_mem _ ?_
    apply Submodule.subset_span
    simp only [hT, Finset.coe_biUnion, Finset.coe_image, Set.mem_iUnion]
    exact ⟨⟨g, hg⟩, Finset.mem_coe.mpr (Finset.mem_univ _), x, Finset.mem_coe.mpr hx, rfl⟩
  have hincl : Function.Surjective (Submodule.inclusion hle) := by
    rw [← Module.FaithfullyFlat.lTensor_surjective_iff_surjective R S]
    intro y
    have hy : (K.subtype.baseChange S) y ∈ K₀.baseChange S := by
      apply hbase
      rw [← Submodule.range_baseChange_subtype]
      exact ⟨y, rfl⟩
    rw [← Submodule.range_baseChange_subtype] at hy
    obtain ⟨z, hz⟩ := hy
    refine ⟨z, ?_⟩
    have hcomp : K.subtype.comp (Submodule.inclusion hle) = K₀.subtype := rfl
    have hinj : Function.Injective (K.subtype.baseChange S) := by
      rw [LinearMap.baseChange_eq_ltensor]
      exact Module.Flat.lTensor_preserves_injective_linearMap _
        (Submodule.subtype_injective K)
    apply hinj
    have h2 : (K.subtype.baseChange S)
        ((LinearMap.lTensor S (Submodule.inclusion hle)) z) =
        (K₀.subtype.baseChange S) z := by
      rw [← LinearMap.baseChange_eq_ltensor, ← LinearMap.comp_apply,
        ← LinearMap.baseChange_comp, hcomp]
    rw [h2, hz]
  have hKeq : K = K₀ := by
    apply le_antisymm ?_ hle
    intro k hk
    obtain ⟨⟨k₀, hk₀⟩, hkk⟩ := hincl ⟨k, hk⟩
    have : k₀ = k := congrArg Subtype.val hkk
    rwa [← this]
  rw [hKeq]
  exact ⟨T, rfl⟩

/-- A module is finitely presented if its base change along a faithfully flat ring map is.

OBLIGATION. Mathlib has no module-level version of this — `Mathlib/RingTheory/Finiteness/Descent.lean`
descends `Algebra.FinitePresentation` (`FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat`),
not `Module.FinitePresentation`.

Proof route. `M` is finite over `R` by `Module.Finite.of_baseChange_faithfullyFlat`, so choose a
surjection `l : (Fin n → R) →ₗ[R] M`. Since `S` is flat over `R`, base change is exact and
`S ⊗[R] ker l ≃ ker (S ⊗[R] l)`. As `S ⊗[R] M` is finitely presented over `S`,
`Module.FinitePresentation.fg_ker` makes `ker (S ⊗[R] l)` finitely generated over `S`. It
remains to descend finite generation of a submodule along a faithfully flat ring map — Mathlib
has this only for ideals (`Ideal.FG.of_FG_map_of_faithfullyFlat`), so the submodule form has to
be proved too. Then `Module.finitePresentation_of_surjective` finishes.

This is the affine-local content of Stacks 03C4 (`algebra-lemma-descend-properties-modules`) part
(2). -/
theorem Module.FinitePresentation.of_baseChange_faithfullyFlat
    [Module.FinitePresentation S (S ⊗[R] M)] : Module.FinitePresentation R M := by
  haveI : Module.Finite R M := Module.Finite.of_baseChange_faithfullyFlat R M S
  obtain ⟨n, l, hl⟩ := Module.Finite.exists_fin' R M
  refine Module.finitePresentation_of_surjective l hl ?_
  apply Submodule.FG.of_baseChange_faithfullyFlat R _ S
  have hker : (LinearMap.ker l).baseChange S = LinearMap.ker (l.baseChange S) := by
    rw [← Submodule.range_baseChange_subtype]
    have hker' := Module.Flat.ker_lTensor_eq (S := S) (M := S) l
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
      have hzero : l.comp (LinearMap.ker l).subtype = 0 := by
        ext y
        simpa using y.2
      rw [hzero]
      simp
    · intro y hy
      have hy' : y ∈ LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor S S l) := hy
      rw [hker'] at hy'
      obtain ⟨x, hx⟩ := hy'
      exact ⟨x, hx⟩
  rw [hker]
  exact Module.FinitePresentation.fg_ker (l.baseChange S) (by
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective S hl)

/-- A finite module is projective if its base change along a faithfully flat ring map is.

OBLIGATION, downstream of `Module.FinitePresentation.of_baseChange_faithfullyFlat`.

Proof route. `S ⊗[R] M` projective implies it is flat, so `M` is flat by
`Module.Flat.of_flat_tensorProduct`. `S ⊗[R] M` is finite and projective hence finitely
presented, so `M` is finitely presented by the previous lemma. Then `M` is flat and finitely
presented, so `Module.Flat.projective_of_finitePresentation` gives projectivity.

Note the finiteness hypothesis is genuinely needed: over a general ring, flat and finite does
not imply projective without finite presentation.

This is Stacks 058S (`algebra-proposition-ffdescent-finite-projectivity`). -/
theorem Module.Projective.of_baseChange_faithfullyFlat [Module.Finite R M]
    [Module.Projective S (S ⊗[R] M)] : Module.Projective R M := by
  haveI : Module.Flat S (S ⊗[R] M) := Module.Flat.of_projective
  haveI : Module.Flat R M := Module.Flat.of_flat_tensorProduct R M S
  haveI : Module.Finite S (S ⊗[R] M) := Module.Finite.base_change R S M
  haveI : Module.FinitePresentation S (S ⊗[R] M) :=
    Module.finitePresentation_of_projective S _
  haveI : Module.FinitePresentation R M :=
    Module.FinitePresentation.of_baseChange_faithfullyFlat R M S
  exact Module.Flat.projective_of_finitePresentation

namespace ModuleCat

open CategoryTheory

universe u'

variable {A B : Type u'} [CommRing A] [CommRing B] (f : A →+* B)

/-- Base-change cancellation for the explicit tensor-product pushout of two ring maps.

For `f : A → B`, `g : A → C`, and a `C`-module `N`, restriction along the
left inclusion after extension along the right inclusion identifies with extension
of the `A`-module underlying `N` along `f`. Keeping the two algebra structures on
`B ⊗[A] C` explicit avoids the typeclass diamonds that arise in kernel-pair and
triple-overlap calculations. -/
noncomputable def tensorPushoutCancel {C : Type u'} [CommRing C]
    (g : A →+* C) (N : ModuleCat.{u'} C) :
    letI : Algebra A B := f.toAlgebra
    letI : Algebra A C := g.toAlgebra
    let T := B ⊗[A] C
    let l : B →+* T := Algebra.TensorProduct.includeLeftRingHom
    let r : C →+* T := Algebra.TensorProduct.includeRight.toRingHom
    ((restrictScalars l).obj ((extendScalars r).obj N)) ≅
      (extendScalars f).obj ((restrictScalars g).obj N) := by
  letI : Algebra A B := f.toAlgebra
  letI : Algebra A C := g.toAlgebra
  let T := B ⊗[A] C
  let l : B →+* T := Algebra.TensorProduct.includeLeftRingHom
  let r : C →+* T := Algebra.TensorProduct.includeRight.toRingHom
  let algR : Algebra C T := r.toAlgebra
  let algL : Algebra B T := l.toAlgebra
  let algA : Algebra A T := inferInstance
  let hRA :=
    @IsScalarTower.of_algebraMap_eq' A C T _ _ _ g.toAlgebra algR algA
      (by
        change algebraMap A T = r.comp g
        exact Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap)
  let hLA :=
    @IsScalarTower.of_algebraMap_eq' A B T _ _ _ f.toAlgebra algL algA
      (by rfl)
  let mapR : C →ₗ[A] T :=
    (@IsScalarTower.toAlgHom A C T _ _ _ g.toAlgebra algR algA hRA).toLinearMap
  let hout : @IsBaseChange A C T B _ _ _ _ f.toAlgebra
      g.toAlgebra.toModule algA.toModule algL.toModule hLA mapR := by
    delta IsBaseChange
    convert! TensorProduct.isTensorProduct A B C using 1
    ext b c
    simp only [mapR]
    change l b * r c = b ⊗ₜ[A] c
    change (b ⊗ₜ[A] (1 : C)) * ((1 : B) ⊗ₜ[A] c) = b ⊗ₜ[A] c
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  let hp : @Algebra.IsPushout A B _ _ f.toAlgebra C T _ _
      g.toAlgebra algL algR algA hRA hLA :=
    @Algebra.IsPushout.mk A B _ _ f.toAlgebra C T _ _
      g.toAlgebra algL algR algA hRA hLA hout
  let hN := @IsScalarTower.restrictScalars A C N _ _ _ g.toAlgebra N.isModule
  let e := @Algebra.IsPushout.cancelBaseChange A B _ _ f.toAlgebra C T _ _
      g.toAlgebra algA algR algL hRA hLA hp N _
      ((restrictScalars g).obj N).isModule N.isModule hN
  let source := (restrictScalars l).obj ((extendScalars r).obj N)
  let target := (extendScalars f).obj ((restrictScalars g).obj N)
  let ef : source → target := fun x ↦ e x
  let eg : target → source := fun x ↦ e.symm x
  let e' : source ≃ₗ[B] target :=
    { toFun := ef
      invFun := eg
      left_inv := fun x ↦ by
        change e.symm (e x) = x
        simp
      right_inv := fun x ↦ by
        change e (e.symm x) = x
        simp
      map_add' := fun x y ↦ e.map_add x y
      map_smul' := by
        intro b x
        change e (l b • x) = b • e x
        convert e.map_smul b x using 1
        apply e.symm.injective
        simp only [e.symm_apply_apply]
        rfl }
  exact LinearEquiv.toModuleIso e'

/-- `tensorPushoutCancel` sends the canonical pure tensor to the canonical
pure tensor after cancelling the pushout square. -/
lemma tensorPushoutCancel_one_tmul {C : Type u'} [CommRing C]
    (g : A →+* C) (N : ModuleCat.{u'} C) (n : N) :
    letI : Algebra A B := f.toAlgebra
    letI : Algebra A C := g.toAlgebra
    let T := B ⊗[A] C
    let l : B →+* T := Algebra.TensorProduct.includeLeftRingHom
    let r : C →+* T := Algebra.TensorProduct.includeRight.toRingHom
    (tensorPushoutCancel f g N).hom ((1 : T) ⊗ₜ[C,r] n) =
      (1 : B) ⊗ₜ[A] (show (restrictScalars g).obj N from n) := by
  letI : Algebra A B := f.toAlgebra
  letI : Algebra A C := g.toAlgebra
  let T := B ⊗[A] C
  let l : B →+* T := Algebra.TensorProduct.includeLeftRingHom
  let r : C →+* T := Algebra.TensorProduct.includeRight.toRingHom
  let algR : Algebra C T := r.toAlgebra
  let algL : Algebra B T := l.toAlgebra
  let algA : Algebra A T := inferInstance
  let hRA :=
    @IsScalarTower.of_algebraMap_eq' A C T _ _ _ g.toAlgebra algR algA
      (by
        change algebraMap A T = r.comp g
        exact Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap)
  let hLA :=
    @IsScalarTower.of_algebraMap_eq' A B T _ _ _ f.toAlgebra algL algA
      (by rfl)
  let mapR : C →ₗ[A] T :=
    (@IsScalarTower.toAlgHom A C T _ _ _ g.toAlgebra algR algA hRA).toLinearMap
  let hout : @IsBaseChange A C T B _ _ _ _ f.toAlgebra
      g.toAlgebra.toModule algA.toModule algL.toModule hLA mapR := by
    delta IsBaseChange
    convert! TensorProduct.isTensorProduct A B C using 1
    ext b c
    simp only [mapR]
    change l b * r c = b ⊗ₜ[A] c
    change (b ⊗ₜ[A] (1 : C)) * ((1 : B) ⊗ₜ[A] c) = b ⊗ₜ[A] c
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  let hp : @Algebra.IsPushout A B _ _ f.toAlgebra C T _ _
      g.toAlgebra algL algR algA hRA hLA :=
    @Algebra.IsPushout.mk A B _ _ f.toAlgebra C T _ _
      g.toAlgebra algL algR algA hRA hLA hout
  let hN := @IsScalarTower.restrictScalars A C N _ _ _ g.toAlgebra N.isModule
  let e := @Algebra.IsPushout.cancelBaseChange A B _ _ f.toAlgebra C T _ _
      g.toAlgebra algA algR algL hRA hLA hp N _
      ((restrictScalars g).obj N).isModule N.isModule hN
  change e ((1 : T) ⊗ₜ[C,r] n) =
    (1 : B) ⊗ₜ[A] (show (restrictScalars g).obj N from n)
  exact @Algebra.IsPushout.cancelBaseChange_tmul A B _ _ f.toAlgebra C T _ _
    g.toAlgebra algA algR algL hRA hLA hp N _
    ((restrictScalars g).obj N).isModule N.isModule hN n

/-- Base-change cancellation for a tensor-product pushout when the right-hand
algebra structure is already present. Unlike `tensorPushoutCancel`, this keeps
that inherited structure unchanged, which is essential for iterated tensor
products. -/
noncomputable def tensorPushoutCancelRightAlgebra {C : Type u'} [CommRing C]
    [Algebra A C] (N : ModuleCat.{u'} C) :
    letI : Algebra A B := f.toAlgebra
    let T := B ⊗[A] C
    let l : B →+* T := Algebra.TensorProduct.includeLeftRingHom
    let r : C →+* T := Algebra.TensorProduct.includeRight.toRingHom
    ((restrictScalars l).obj ((extendScalars r).obj N)) ≅
      (extendScalars f).obj ((restrictScalars (algebraMap A C)).obj N) := by
  letI : Algebra A B := f.toAlgebra
  let T := B ⊗[A] C
  let l : B →+* T := Algebra.TensorProduct.includeLeftRingHom
  let r : C →+* T := Algebra.TensorProduct.includeRight.toRingHom
  let algR : Algebra C T := r.toAlgebra
  let algL : Algebra B T := l.toAlgebra
  let algA : Algebra A T := inferInstance
  let hRA :=
    @IsScalarTower.of_algebraMap_eq' A C T _ _ _ (inferInstance : Algebra A C)
      algR algA
      (by
        change algebraMap A T = r.comp (algebraMap A C)
        exact Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap)
  let hLA :=
    @IsScalarTower.of_algebraMap_eq' A B T _ _ _ f.toAlgebra algL algA (by rfl)
  let mapR : C →ₗ[A] T :=
    (@IsScalarTower.toAlgHom A C T _ _ _ (inferInstance : Algebra A C)
      algR algA hRA).toLinearMap
  let hout : @IsBaseChange A C T B _ _ _ _ f.toAlgebra
      (inferInstance : Algebra A C).toModule algA.toModule algL.toModule hLA mapR := by
    delta IsBaseChange
    convert! TensorProduct.isTensorProduct A B C using 1
    ext b c
    simp only [mapR]
    change l b * r c = b ⊗ₜ[A] c
    change (b ⊗ₜ[A] (1 : C)) * ((1 : B) ⊗ₜ[A] c) = b ⊗ₜ[A] c
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  let hp : @Algebra.IsPushout A B _ _ f.toAlgebra C T _ _
      (inferInstance : Algebra A C) algL algR algA hRA hLA :=
    @Algebra.IsPushout.mk A B _ _ f.toAlgebra C T _ _
      (inferInstance : Algebra A C) algL algR algA hRA hLA hout
  let modAN : Module A N := Module.compHom N (algebraMap A C)
  let hN : @IsScalarTower A C N (inferInstance : SMul A C)
      N.isModule.toSMul modAN.toSMul :=
    @IsScalarTower.of_compHom A C N _ _ (inferInstance : Algebra A C)
      N.isModule.toMulAction
  let e := @Algebra.IsPushout.cancelBaseChange A B _ _ f.toAlgebra C T _ _
      (inferInstance : Algebra A C) algA algR algL hRA hLA hp N _
      modAN N.isModule hN
  let source := (restrictScalars l).obj ((extendScalars r).obj N)
  let target := (extendScalars f).obj ((restrictScalars (algebraMap A C)).obj N)
  let ef : source → target := fun x ↦ e x
  let eg : target → source := fun x ↦ e.symm x
  let e' : source ≃ₗ[B] target :=
    { toFun := ef
      invFun := eg
      left_inv := fun x ↦ by change e.symm (e x) = x; simp
      right_inv := fun x ↦ by change e (e.symm x) = x; simp
      map_add' := fun x y ↦ e.map_add x y
      map_smul' := by
        intro b x
        change e (l b • x) = b • e x
        convert e.map_smul b x using 1
        apply e.symm.injective
        simp only [e.symm_apply_apply]
        rfl }
  exact LinearEquiv.toModuleIso e'

/-- `tensorPushoutCancelRightAlgebra` preserves the canonical pure tensor. -/
lemma tensorPushoutCancelRightAlgebra_one_tmul {C : Type u'} [CommRing C]
    [Algebra A C] (N : ModuleCat.{u'} C) (n : N) :
    letI : Algebra A B := f.toAlgebra
    let T := B ⊗[A] C
    let l : B →+* T := Algebra.TensorProduct.includeLeftRingHom
    let r : C →+* T := Algebra.TensorProduct.includeRight.toRingHom
    (tensorPushoutCancelRightAlgebra f N).hom ((1 : T) ⊗ₜ[C,r] n) =
      (1 : B) ⊗ₜ[A]
        (show (restrictScalars (algebraMap A C)).obj N from n) := by
  letI : Algebra A B := f.toAlgebra
  let T := B ⊗[A] C
  let l : B →+* T := Algebra.TensorProduct.includeLeftRingHom
  let r : C →+* T := Algebra.TensorProduct.includeRight.toRingHom
  let algR : Algebra C T := r.toAlgebra
  let algL : Algebra B T := l.toAlgebra
  let algA : Algebra A T := inferInstance
  let hRA :=
    @IsScalarTower.of_algebraMap_eq' A C T _ _ _ (inferInstance : Algebra A C)
      algR algA
      (by
        change algebraMap A T = r.comp (algebraMap A C)
        exact Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap)
  let hLA :=
    @IsScalarTower.of_algebraMap_eq' A B T _ _ _ f.toAlgebra algL algA (by rfl)
  let mapR : C →ₗ[A] T :=
    (@IsScalarTower.toAlgHom A C T _ _ _ (inferInstance : Algebra A C)
      algR algA hRA).toLinearMap
  let hout : @IsBaseChange A C T B _ _ _ _ f.toAlgebra
      (inferInstance : Algebra A C).toModule algA.toModule algL.toModule hLA mapR := by
    delta IsBaseChange
    convert! TensorProduct.isTensorProduct A B C using 1
    ext b c
    simp only [mapR]
    change l b * r c = b ⊗ₜ[A] c
    change (b ⊗ₜ[A] (1 : C)) * ((1 : B) ⊗ₜ[A] c) = b ⊗ₜ[A] c
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  let hp : @Algebra.IsPushout A B _ _ f.toAlgebra C T _ _
      (inferInstance : Algebra A C) algL algR algA hRA hLA :=
    @Algebra.IsPushout.mk A B _ _ f.toAlgebra C T _ _
      (inferInstance : Algebra A C) algL algR algA hRA hLA hout
  let modAN : Module A N := Module.compHom N (algebraMap A C)
  let hN : @IsScalarTower A C N (inferInstance : SMul A C)
      N.isModule.toSMul modAN.toSMul :=
    @IsScalarTower.of_compHom A C N _ _ (inferInstance : Algebra A C)
      N.isModule.toMulAction
  let e := @Algebra.IsPushout.cancelBaseChange A B _ _ f.toAlgebra C T _ _
      (inferInstance : Algebra A C) algA algR algL hRA hLA hp N _
      modAN N.isModule hN
  change e ((1 : T) ⊗ₜ[C,r] n) =
    (1 : B) ⊗ₜ[A] (show (restrictScalars (algebraMap A C)).obj N from n)
  exact @Algebra.IsPushout.cancelBaseChange_tmul A B _ _ f.toAlgebra C T _ _
    (inferInstance : Algebra A C) algA algR algL hRA hLA hp N _
    modAN N.isModule hN n

/-- On the tensor-square overlap of `A → B`, restriction along the left projection
after extension along the right projection is the comonad
`extendScalars f ⋙ restrictScalars f`.

The explicit pushout construction is needed to keep the two `B`-algebra structures on
`B ⊗[A] B` distinct.  In particular, using Mathlib's default left algebra structure for
both projections creates a non-definitional typeclass diamond. -/
noncomputable def overlapCancel (N : ModuleCat.{u'} B) :
    letI : Algebra A B := f.toAlgebra
    let C := B ⊗[A] B
    let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
    let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
    ((restrictScalars l).obj ((extendScalars r).obj N)) ≅
      (extendScalars f).obj ((restrictScalars f).obj N) := by
  letI : Algebra A B := f.toAlgebra
  let C := B ⊗[A] B
  let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
  let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
  let algR : Algebra B C := r.toAlgebra
  let algL : Algebra B C := l.toAlgebra
  let algA : Algebra A C := inferInstance
  let hRA :=
    @IsScalarTower.of_algebraMap_eq' A B C _ _ _ f.toAlgebra algR algA
      (by
        change algebraMap A C = r.comp f
        exact Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap)
  let hLA :=
    @IsScalarTower.of_algebraMap_eq' A B C _ _ _ f.toAlgebra algL algA
      (by rfl)
  let mapR : B →ₗ[A] C :=
    (@IsScalarTower.toAlgHom A B C _ _ _ f.toAlgebra algR algA hRA).toLinearMap
  let hout : @IsBaseChange A B C B _ _ _ _ f.toAlgebra
      f.toAlgebra.toModule algA.toModule algL.toModule hLA mapR := by
    delta IsBaseChange
    convert! TensorProduct.isTensorProduct A B B using 1
    ext b x
    simp only [mapR]
    change l b * r x = b ⊗ₜ[A] x
    change (b ⊗ₜ[A] (1 : B)) * ((1 : B) ⊗ₜ[A] x) = b ⊗ₜ[A] x
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  let hp : @Algebra.IsPushout A B _ _ f.toAlgebra B C _ _
      f.toAlgebra algL algR algA hRA hLA :=
    @Algebra.IsPushout.mk A B _ _ f.toAlgebra B C _ _
      f.toAlgebra algL algR algA hRA hLA hout
  let hN := @IsScalarTower.restrictScalars A B N _ _ _ f.toAlgebra N.isModule
  let e := @Algebra.IsPushout.cancelBaseChange A B _ _ f.toAlgebra B C _ _
      f.toAlgebra algA algR algL hRA hLA hp N _
      ((restrictScalars f).obj N).isModule N.isModule hN
  let source := (restrictScalars l).obj ((extendScalars r).obj N)
  let target := (extendScalars f).obj ((restrictScalars f).obj N)
  let ef : source → target := fun x ↦ e x
  let eg : target → source := fun x ↦ e.symm x
  let e' : source ≃ₗ[B] target :=
    { toFun := ef
      invFun := eg
      left_inv := fun x ↦ by
        change e.symm (e x) = x
        simp
      right_inv := fun x ↦ by
        change e (e.symm x) = x
        simp
      map_add' := fun x y ↦ e.map_add x y
      map_smul' := by
        intro b x
        change e (l b • x) = b • e x
        convert e.map_smul b x using 1
        apply e.symm.injective
        simp only [e.symm_apply_apply]
        rfl }
  exact LinearEquiv.toModuleIso e'

/-- `overlapCancel` sends the canonical pure tensor on the overlap to the
canonical pure tensor in the extension/restriction comonad. -/
lemma overlapCancel_one_tmul (N : ModuleCat.{u'} B) (n : N) :
    letI : Algebra A B := f.toAlgebra
    let C := B ⊗[A] B
    let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
    let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
    (overlapCancel f N).hom ((1 : C) ⊗ₜ[B] n) =
      (1 : B) ⊗ₜ[A] (show (restrictScalars f).obj N from n) := by
  letI : Algebra A B := f.toAlgebra
  let C := B ⊗[A] B
  let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
  let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
  let algR : Algebra B C := r.toAlgebra
  let algL : Algebra B C := l.toAlgebra
  let algA : Algebra A C := inferInstance
  let hRA :=
    @IsScalarTower.of_algebraMap_eq' A B C _ _ _ f.toAlgebra algR algA
      (by
        change algebraMap A C = r.comp f
        exact Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap)
  let hLA :=
    @IsScalarTower.of_algebraMap_eq' A B C _ _ _ f.toAlgebra algL algA
      (by rfl)
  let mapR : B →ₗ[A] C :=
    (@IsScalarTower.toAlgHom A B C _ _ _ f.toAlgebra algR algA hRA).toLinearMap
  let hout : @IsBaseChange A B C B _ _ _ _ f.toAlgebra
      f.toAlgebra.toModule algA.toModule algL.toModule hLA mapR := by
    delta IsBaseChange
    convert! TensorProduct.isTensorProduct A B B using 1
    ext b x
    simp only [mapR]
    change l b * r x = b ⊗ₜ[A] x
    change (b ⊗ₜ[A] (1 : B)) * ((1 : B) ⊗ₜ[A] x) = b ⊗ₜ[A] x
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  let hp : @Algebra.IsPushout A B _ _ f.toAlgebra B C _ _
      f.toAlgebra algL algR algA hRA hLA :=
    @Algebra.IsPushout.mk A B _ _ f.toAlgebra B C _ _
      f.toAlgebra algL algR algA hRA hLA hout
  let hN := @IsScalarTower.restrictScalars A B N _ _ _ f.toAlgebra N.isModule
  let e := @Algebra.IsPushout.cancelBaseChange A B _ _ f.toAlgebra B C _ _
      f.toAlgebra algA algR algL hRA hLA hp N _
      ((restrictScalars f).obj N).isModule N.isModule hN
  change e ((1 : C) ⊗ₜ[B,r] n) =
    (1 : B) ⊗ₜ[A] (show (restrictScalars f).obj N from n)
  exact @Algebra.IsPushout.cancelBaseChange_tmul A B _ _ f.toAlgebra B C _ _
    f.toAlgebra algA algR algL hRA hLA hp N _
    ((restrictScalars f).obj N).isModule N.isModule hN n

/-- Cancellation on the triple tensor-product overlap. It identifies pullback
from the first to the third projection with two iterations of the
extension/restriction comonad. -/
noncomputable def tripleCancel (N : ModuleCat.{u'} B) :
    letI : Algebra A B := f.toAlgebra
    let C := B ⊗[A] B
    let cL : B →+* C := Algebra.TensorProduct.includeLeftRingHom
    let cR : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
    let T := B ⊗[A] C
    let tL : B →+* T := Algebra.TensorProduct.includeLeftRingHom
    let tR : C →+* T := Algebra.TensorProduct.includeRight.toRingHom
    let i₁ : B →+* T := tL
    let i₃ : B →+* T := tR.comp cR
    (restrictScalars i₁).obj ((extendScalars i₃).obj N) ≅
      (extendScalars f).obj ((restrictScalars f).obj
        ((extendScalars f).obj ((restrictScalars f).obj N))) := by
  letI : Algebra A B := f.toAlgebra
  let C := B ⊗[A] B
  let cL : B →+* C := Algebra.TensorProduct.includeLeftRingHom
  let cR : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
  let T := B ⊗[A] C
  let tL : B →+* T := Algebra.TensorProduct.includeLeftRingHom
  let tR : C →+* T := Algebra.TensorProduct.includeRight.toRingHom
  let i₁ : B →+* T := tL
  let i₃ : B →+* T := tR.comp cR
  let g : A →+* C := algebraMap A C
  let X : ModuleCat.{u'} C := (extendScalars cR).obj N
  let e₁ : (restrictScalars i₁).obj ((extendScalars i₃).obj N) ≅
      (restrictScalars tL).obj ((extendScalars tR).obj X) :=
    (restrictScalars tL).mapIso ((extendScalarsComp cR tR).app N)
  let e₂ : (restrictScalars tL).obj ((extendScalars tR).obj X) ≅
      (extendScalars f).obj ((restrictScalars g).obj X) :=
    by simpa only [g, tL, tR, T] using tensorPushoutCancelRightAlgebra f X
  let eA : (restrictScalars g).obj X ≅
      (restrictScalars f).obj
        ((extendScalars f).obj ((restrictScalars f).obj N)) :=
    (restrictScalarsComp f cL).app X ≪≫
      (restrictScalars f).mapIso (overlapCancel f N)
  let e₃ : (extendScalars f).obj ((restrictScalars g).obj X) ≅
      (extendScalars f).obj ((restrictScalars f).obj
        ((extendScalars f).obj ((restrictScalars f).obj N))) :=
    (extendScalars f).mapIso eA
  exact e₁ ≪≫ e₂ ≪≫ e₃

/-- `tripleCancel` sends the canonical pure tensor to the twice-iterated
canonical pure tensor. -/
lemma tripleCancel_one_tmul (N : ModuleCat.{u'} B) (n : N) :
    letI : Algebra A B := f.toAlgebra
    let C := B ⊗[A] B
    let cL : B →+* C := Algebra.TensorProduct.includeLeftRingHom
    let cR : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
    let T := B ⊗[A] C
    let tL : B →+* T := Algebra.TensorProduct.includeLeftRingHom
    let tR : C →+* T := Algebra.TensorProduct.includeRight.toRingHom
    let i₁ : B →+* T := tL
    let i₃ : B →+* T := tR.comp cR
    (tripleCancel f N).hom ((1 : T) ⊗ₜ[B,i₃] n) =
      (1 : B) ⊗ₜ[A]
        (show (restrictScalars f).obj ((extendScalars f).obj
          ((restrictScalars f).obj N)) from
          (1 : B) ⊗ₜ[A] (show (restrictScalars f).obj N from n)) := by
  letI : Algebra A B := f.toAlgebra
  let C := B ⊗[A] B
  let cL : B →+* C := Algebra.TensorProduct.includeLeftRingHom
  let cR : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
  let T := B ⊗[A] C
  let tL : B →+* T := Algebra.TensorProduct.includeLeftRingHom
  let tR : C →+* T := Algebra.TensorProduct.includeRight.toRingHom
  let i₁ : B →+* T := tL
  let i₃ : B →+* T := tR.comp cR
  let g : A →+* C := algebraMap A C
  let X : ModuleCat.{u'} C := (extendScalars cR).obj N
  let e₁ : (restrictScalars i₁).obj ((extendScalars i₃).obj N) ≅
      (restrictScalars tL).obj ((extendScalars tR).obj X) :=
    (restrictScalars tL).mapIso ((extendScalarsComp cR tR).app N)
  let e₂ : (restrictScalars tL).obj ((extendScalars tR).obj X) ≅
      (extendScalars f).obj ((restrictScalars g).obj X) :=
    by simpa only [g, tL, tR, T] using tensorPushoutCancelRightAlgebra f X
  let eA : (restrictScalars g).obj X ≅
      (restrictScalars f).obj
        ((extendScalars f).obj ((restrictScalars f).obj N)) :=
    (restrictScalarsComp f cL).app X ≪≫
      (restrictScalars f).mapIso (overlapCancel f N)
  let e₃ : (extendScalars f).obj ((restrictScalars g).obj X) ≅
      (extendScalars f).obj ((restrictScalars f).obj
        ((extendScalars f).obj ((restrictScalars f).obj N))) :=
    (extendScalars f).mapIso eA
  change e₃.hom (e₂.hom (e₁.hom ((1 : T) ⊗ₜ[B,i₃] n))) = _
  rw [show e₁.hom ((1 : T) ⊗ₜ[B,i₃] n) =
      (1 : T) ⊗ₜ[C,tR] ((1 : C) ⊗ₜ[B,cR] n) by
    exact extendScalarsComp_hom_app_one_tmul cR tR N n]
  rw [show e₂.hom
      ((1 : T) ⊗ₜ[C,tR] ((1 : C) ⊗ₜ[B,cR] n)) =
        (1 : B) ⊗ₜ[A]
          (show (restrictScalars g).obj X from
            (1 : C) ⊗ₜ[B,cR] n) by
    dsimp only [e₂]
    change (tensorPushoutCancelRightAlgebra f X).hom
      ((1 : T) ⊗ₜ[C,tR] ((1 : C) ⊗ₜ[B,cR] n)) = _
    exact tensorPushoutCancelRightAlgebra_one_tmul f X
      (show X from (1 : C) ⊗ₜ[B,cR] n)]
  rw [show e₃.hom
      ((1 : B) ⊗ₜ[A]
        (show (restrictScalars g).obj X from
          (1 : C) ⊗ₜ[B,cR] n)) =
      (1 : B) ⊗ₜ[A]
        (eA.hom (show (restrictScalars g).obj X from
          (1 : C) ⊗ₜ[B,cR] n)) by
    exact ExtendScalars.map_tmul f eA.hom 1
      (show (restrictScalars g).obj X from
        (1 : C) ⊗ₜ[B,cR] n)]
  congr 1
  change (overlapCancel f N).hom ((1 : C) ⊗ₜ[B,cR] n) = _
  exact overlapCancel_one_tmul f N n

/-- The inverse of `overlapCancel` sends a pure tensor to the corresponding
left-projection scalar on the tensor-square overlap. -/
lemma overlapCancel_inv_tmul (N : ModuleCat.{u'} B) (b : B) (n : N) :
    letI : Algebra A B := f.toAlgebra
    let C := B ⊗[A] B
    let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
    let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
    (overlapCancel f N).inv
        (b ⊗ₜ[A] (show (restrictScalars f).obj N from n)) =
      l b ⊗ₜ[B,r] n := by
  letI : Algebra A B := f.toAlgebra
  dsimp only
  let C := B ⊗[A] B
  let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
  let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
  let algR : Algebra B C := r.toAlgebra
  let algL : Algebra B C := l.toAlgebra
  let algA : Algebra A C := inferInstance
  let hRA :=
    @IsScalarTower.of_algebraMap_eq' A B C _ _ _ f.toAlgebra algR algA
      (by
        change algebraMap A C = r.comp f
        exact Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap)
  let hLA :=
    @IsScalarTower.of_algebraMap_eq' A B C _ _ _ f.toAlgebra algL algA
      (by rfl)
  let mapR : B →ₗ[A] C :=
    (@IsScalarTower.toAlgHom A B C _ _ _ f.toAlgebra algR algA hRA).toLinearMap
  let hout : @IsBaseChange A B C B _ _ _ _ f.toAlgebra
      f.toAlgebra.toModule algA.toModule algL.toModule hLA mapR := by
    delta IsBaseChange
    convert! TensorProduct.isTensorProduct A B B using 1
    ext b x
    simp only [mapR]
    change l b * r x = b ⊗ₜ[A] x
    change (b ⊗ₜ[A] (1 : B)) * ((1 : B) ⊗ₜ[A] x) = b ⊗ₜ[A] x
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  let hp : @Algebra.IsPushout A B _ _ f.toAlgebra B C _ _
      f.toAlgebra algL algR algA hRA hLA :=
    @Algebra.IsPushout.mk A B _ _ f.toAlgebra B C _ _
      f.toAlgebra algL algR algA hRA hLA hout
  letI modAN : Module A N := Module.compHom N f
  let hN := @IsScalarTower.restrictScalars A B N _ _ _ f.toAlgebra N.isModule
  let e := @Algebra.IsPushout.cancelBaseChange A B _ _ f.toAlgebra B C _ _
      f.toAlgebra algA algR algL hRA hLA hp N _ modAN N.isModule hN
  change e.symm (b ⊗ₜ[A] n) = l b ⊗ₜ[B,r] n
  exact @Algebra.IsPushout.cancelBaseChange_symm_tmul A B _ _ f.toAlgebra B C _ _
    f.toAlgebra algA algR algL hRA hLA hp N _ modAN N.isModule hN b n

/-- A morphism between the two pullbacks of a `B`-module to `B ⊗[A] B` is
equivalently a candidate coaction for the extension/restriction comonad of `A → B`.

The forward map first uses the extension/restriction adjunction for the left tensor
projection, then `overlapCancel`. -/
noncomputable def overlapHomEquiv (N : ModuleCat.{u'} B) :
    letI : Algebra A B := f.toAlgebra
    let C := B ⊗[A] B
    let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
    let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
    (((extendScalars l).obj N ⟶ (extendScalars r).obj N) ≃
      (N ⟶ (extendScalars f).obj ((restrictScalars f).obj N))) := by
  letI : Algebra A B := f.toAlgebra
  let C := B ⊗[A] B
  let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
  let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
  exact ((extendRestrictScalarsAdj l).homEquiv N ((extendScalars r).obj N)).trans
    (CategoryTheory.Iso.homCongr (Iso.refl N) (overlapCancel f N))

/-- Elementwise formula for `overlapHomEquiv`: evaluate the overlap morphism on
`1 ⊗ n`, then apply `overlapCancel`. -/
lemma overlapHomEquiv_apply (N : ModuleCat.{u'} B) :
    letI : Algebra A B := f.toAlgebra
    let C := B ⊗[A] B
    let l : B →+* C := Algebra.TensorProduct.includeLeftRingHom
    let r : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
    ∀ (θ : (extendScalars l).obj N ⟶ (extendScalars r).obj N) (n : N),
      overlapHomEquiv f N θ n =
        (overlapCancel f N).hom (θ ((1 : C) ⊗ₜ[B] n)) := by
  dsimp only
  intro θ n
  simp only [overlapHomEquiv, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.refl_inv, Category.id_comp]
  rfl

end ModuleCat
