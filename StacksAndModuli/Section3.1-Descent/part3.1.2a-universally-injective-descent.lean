module

public import StacksAndModuli.«Section3.1-Descent».«part3.1.2-descent-quasi-coherent»
public import Mathlib.Algebra.Module.CharacterModule

/-!
# Universally injective descent

This module records the live character-module infrastructure for Remark 3.1.6
(`rmk:universally-injective-descent`) of §3.1 (Descent theory,
`sec:descent-theory`) of *Stacks and Moduli*.
It covers Stacks Project Tags 08WQ, 08WV, 08WR,
08X1, and the split-(co)equalizer lemmas used toward Mesablishvili’s theorem.
The headline equivalence and remaining deferred steps are retained as commented-out
OBLIGATION blocks here and in this folder’s `OBLIGATIONS.md`.
-/

@[expose] public section
set_option maxErrors 2000

-- These files were written when Lean’s backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section RmkUniversallyInjectiveDescent

-- **Remark 3.1.6** (`rmk:universally-injective-descent`): Mesablishvili's theorem —
-- `A → B` is universally injective iff the descent-data functor for modules is an
-- equivalence (Stacks 08XA). The live declarations below are the character-module
-- infrastructure (Tags 08WQ, 08WV, 08WR, 08X1 and split-(co)equalizer lemmas); the
-- headline equivalence and the remaining tags are retained as commented-out OBLIGATION
-- blocks later in this section (see OBLIGATIONS.md, cluster 2).

open TensorProduct
open CategoryTheory Limits

universe u vC vD uC uD

/-- Evaluation into the double character module, linear for the natural module structure on
character modules. -/
def CharacterModule.evaluation {R A : Type u} [CommRing R] [AddCommGroup A] [Module R A] :
    A →ₗ[R] CharacterModule (CharacterModule A) where
  toFun a :=
    { toFun := fun c ↦ c a
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  map_add' a b := by
    ext c
    exact c.map_add a b
  map_smul' _ _ := by ext; rfl

@[simp]
lemma CharacterModule.evaluation_apply {R A : Type u} [CommRing R] [AddCommGroup A]
    [Module R A] (a : A) (c : CharacterModule A) :
    CharacterModule.evaluation (R := R) a c = c a := rfl

/-- **Stacks 08WQ.** The contravariant character-module functor
`M ↦ Hom_ℤ(M, ℚ/ℤ)` on modules over a commutative ring. -/
@[stacks 08WQ]
noncomputable def ModuleCat.characterModuleFunctor (R : Type u) [CommRing R] :
    Functor (ModuleCat.{u} R)ᵒᵖ (ModuleCat.{u} R) where
  obj M := ModuleCat.of R (CharacterModule M.unop)
  map f := ModuleCat.ofHom (CharacterModule.dual f.unop.hom)
  map_id M := by
    apply ModuleCat.hom_ext
    ext c x
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    ext c x
    rfl

@[simp]
lemma ModuleCat.characterModuleFunctor_obj (R : Type u) [CommRing R]
    (M : (ModuleCat.{u} R)ᵒᵖ) :
    (ModuleCat.characterModuleFunctor R).obj M =
      ModuleCat.of R (CharacterModule M.unop) := rfl

@[simp]
lemma ModuleCat.characterModuleFunctor_map_hom (R : Type u) [CommRing R]
    {M N : (ModuleCat.{u} R)ᵒᵖ} (f : M ⟶ N) :
    ((ModuleCat.characterModuleFunctor R).map f).hom =
      CharacterModule.dual f.unop.hom := rfl

-- OBLIGATION (deleted `the deleted upstream library` scaffolding): retained verbatim but commented out.
-- Depends on the chosen-pullback / descent-data API that `the deleted upstream library` supplied and that
-- has no Mathlib counterpart. See OBLIGATIONS.md, cluster 2. Preferred restoration is to
-- re-derive from `ModuleCat.comonadicExtendScalars` (Stacks 023N), not to rebuild it.
-- /-- **Stacks 08WU, forward implication.** A universally injective module map becomes a split
-- surjection after
-- applying the character-module duality functor. -/
-- @[stacks 08WU "forward"]
-- theorem LinearMap.UniversallyInjective.characterModule_dual_isSplitEpi
--     {R M N : Type u} [CommRing R] [AddCommGroup M] [Module R M]
--     [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (hf : f.UniversallyInjective) :
--     ∃ s : CharacterModule M →ₗ[R] CharacterModule N,
--       (CharacterModule.dual f).comp s = LinearMap.id := by
--   have ht : Function.Injective (f.rTensor (CharacterModule M)) := hf _
--   have hs : Function.Surjective
--       (f.lcomp R (CharacterModule (CharacterModule M))) :=
--     rTensor_injective_iff_lcomp_surjective.mp ht
--   obtain ⟨g, hg⟩ := hs (CharacterModule.evaluation (R := R) (A := M))
--   let s : CharacterModule M →ₗ[R] CharacterModule N :=
--     (CharacterModule.dual g).comp
--       (CharacterModule.evaluation (R := R) (A := CharacterModule M))
--   refine ⟨s, ?_⟩
--   ext c m
--   have hgm := DFunLike.congr_fun hg m
--   exact congrArg (fun k : CharacterModule (CharacterModule M) ↦ k c) hgm
--
/-- The functorial section on character modules induced by a section of `CharacterModule.dual f`.
This is the explicit construction used in Stacks 08WV. -/
noncomputable def CharacterModule.dual_lTensorSection
    {R M N : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (s : CharacterModule M →ₗ[R] CharacterModule N)
    (P : Type u) [AddCommGroup P] [Module R P] :
    CharacterModule (P ⊗[R] M) →ₗ[R] CharacterModule (P ⊗[R] N) :=
  (CharacterModule.homEquiv (R := R) (A := P) (B := N)).toLinearMap.comp
    ((LinearMap.llcomp R P (CharacterModule M) (CharacterModule N) s).comp
      (CharacterModule.homEquiv (R := R) (A := P) (B := M)).symm.toLinearMap)

/-- The explicit 08WV section is a right inverse after applying character duality. -/
theorem CharacterModule.dual_lTensorSection_rightInverse
    {R M N : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    (s : CharacterModule M →ₗ[R] CharacterModule N)
    (hs : (CharacterModule.dual f).comp s = LinearMap.id)
    (P : Type u) [AddCommGroup P] [Module R P] :
    (CharacterModule.dual (f.lTensor P)).comp
      (CharacterModule.dual_lTensorSection s P) = LinearMap.id := by
  let eM := CharacterModule.homEquiv (R := R) (A := P) (B := M)
  ext c x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p m =>
      have hscm := DFunLike.congr_fun
        (LinearMap.congr_fun hs ((eM.symm c) p)) m
      exact hscm
  | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy

/-- **Stacks 08WV.** A chosen splitting of the character dual of `f` induces, functorially
in `P`, a splitting after tensoring `f` on the left by `P`. -/
@[stacks 08WV]
theorem CharacterModule.exists_rightInverse_dual_lTensor
    {R M N : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    (s : CharacterModule M →ₗ[R] CharacterModule N)
    (hs : (CharacterModule.dual f).comp s = LinearMap.id)
    (P : Type u) [AddCommGroup P] [Module R P] :
    ∃ t : CharacterModule (P ⊗[R] M) →ₗ[R] CharacterModule (P ⊗[R] N),
      (CharacterModule.dual (f.lTensor P)).comp t = LinearMap.id := by
  exact ⟨CharacterModule.dual_lTensorSection s P,
    CharacterModule.dual_lTensorSection_rightInverse f s hs P⟩

/-- The sections constructed in 08WV are natural in the left tensor factor. -/
theorem CharacterModule.dual_lTensorSection_naturality
    {R M N P Q : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q]
    (s : CharacterModule M →ₗ[R] CharacterModule N) (k : P →ₗ[R] Q) :
    (CharacterModule.dual (k.rTensor N)).comp
        (CharacterModule.dual_lTensorSection s Q) =
      (CharacterModule.dual_lTensorSection s P).comp
        (CharacterModule.dual (k.rTensor M)) := by
  ext c x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p n => rfl
  | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy

/-- Apply a morphism between character modules underneath a right tensor factor. -/
noncomputable def CharacterModule.mapOnDualRightTensor
    {R M N : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (s : CharacterModule M →ₗ[R] CharacterModule N)
    (P : Type u) [AddCommGroup P] [Module R P] :
    CharacterModule (M ⊗[R] P) →ₗ[R] CharacterModule (N ⊗[R] P) :=
  (CharacterModule.dual (_root_.TensorProduct.comm R N P).toLinearMap).comp
    ((CharacterModule.dual_lTensorSection s P).comp
      (CharacterModule.dual (_root_.TensorProduct.comm R M P).symm.toLinearMap))

theorem CharacterModule.mapOnDualRightTensor_id
    {R M P : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup P] [Module R P] :
    CharacterModule.mapOnDualRightTensor
      (LinearMap.id : CharacterModule M →ₗ[R] CharacterModule M) P = LinearMap.id := by
  ext c x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m p => rfl
  | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy

theorem CharacterModule.mapOnDualRightTensor_comp
    {R L M N P : Type u} [CommRing R]
    [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (s : CharacterModule L →ₗ[R] CharacterModule M)
    (t : CharacterModule M →ₗ[R] CharacterModule N) :
    CharacterModule.mapOnDualRightTensor (t.comp s) P =
      (CharacterModule.mapOnDualRightTensor t P).comp
        (CharacterModule.mapOnDualRightTensor s P) := by
  ext c x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul l p => rfl
  | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy

theorem CharacterModule.mapOnDualRightTensor_dual
    {R M N P : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (f : M →ₗ[R] N) :
    CharacterModule.mapOnDualRightTensor (CharacterModule.dual f) P =
      CharacterModule.dual (f.rTensor P) := by
  ext c x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m p => rfl
  | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy

/-- Tensoring inside character duality preserves split coequalizer diagrams. -/
noncomputable def CharacterModule.splitCoequalizerRightTensor
    {R X Y Z P : Type u} [CommRing R]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    [AddCommGroup Z] [Module R Z] [AddCommGroup P] [Module R P]
    {f g : CharacterModule X →ₗ[R] CharacterModule Y}
    {π : CharacterModule Y →ₗ[R] CharacterModule Z}
    (q : IsSplitCoequalizer (ModuleCat.ofHom f) (ModuleCat.ofHom g)
      (ModuleCat.ofHom π)) :
    IsSplitCoequalizer
      (ModuleCat.ofHom (CharacterModule.mapOnDualRightTensor f P))
      (ModuleCat.ofHom (CharacterModule.mapOnDualRightTensor g P))
      (ModuleCat.ofHom (CharacterModule.mapOnDualRightTensor π P)) where
  rightSection := ModuleCat.ofHom
    (CharacterModule.mapOnDualRightTensor q.rightSection.hom P)
  leftSection := ModuleCat.ofHom
    (CharacterModule.mapOnDualRightTensor q.leftSection.hom P)
  condition := by
    apply ModuleCat.hom_ext
    change (CharacterModule.mapOnDualRightTensor π P).comp
        (CharacterModule.mapOnDualRightTensor f P) =
      (CharacterModule.mapOnDualRightTensor π P).comp
        (CharacterModule.mapOnDualRightTensor g P)
    rw [← CharacterModule.mapOnDualRightTensor_comp,
      ← CharacterModule.mapOnDualRightTensor_comp]
    exact congrArg (fun z ↦ CharacterModule.mapOnDualRightTensor z P)
      (congrArg ModuleCat.Hom.hom q.condition)
  rightSection_π := by
    apply ModuleCat.hom_ext
    change (CharacterModule.mapOnDualRightTensor π P).comp
        (CharacterModule.mapOnDualRightTensor q.rightSection.hom P) = LinearMap.id
    rw [← CharacterModule.mapOnDualRightTensor_comp,
      ← CharacterModule.mapOnDualRightTensor_id (R := R) (M := Z) (P := P)]
    exact congrArg (fun z ↦ CharacterModule.mapOnDualRightTensor z P)
      (congrArg ModuleCat.Hom.hom q.rightSection_π)
  leftSection_bottom := by
    apply ModuleCat.hom_ext
    change (CharacterModule.mapOnDualRightTensor g P).comp
        (CharacterModule.mapOnDualRightTensor q.leftSection.hom P) = LinearMap.id
    rw [← CharacterModule.mapOnDualRightTensor_comp,
      ← CharacterModule.mapOnDualRightTensor_id (R := R) (M := Y) (P := P)]
    exact congrArg (fun z ↦ CharacterModule.mapOnDualRightTensor z P)
      (congrArg ModuleCat.Hom.hom q.leftSection_bottom)
  leftSection_top := by
    apply ModuleCat.hom_ext
    change (CharacterModule.mapOnDualRightTensor f P).comp
        (CharacterModule.mapOnDualRightTensor q.leftSection.hom P) =
      (CharacterModule.mapOnDualRightTensor q.rightSection.hom P).comp
        (CharacterModule.mapOnDualRightTensor π P)
    rw [← CharacterModule.mapOnDualRightTensor_comp,
      ← CharacterModule.mapOnDualRightTensor_comp]
    exact congrArg (fun z ↦ CharacterModule.mapOnDualRightTensor z P)
      (congrArg ModuleCat.Hom.hom q.leftSection_top)

-- OBLIGATION (deleted `the deleted upstream library` scaffolding): retained verbatim but commented out.
-- Depends on the chosen-pullback / descent-data API that `the deleted upstream library` supplied and that
-- has no Mathlib counterpart. See OBLIGATIONS.md, cluster 2. Preferred restoration is to
-- re-derive from `ModuleCat.comonadicExtendScalars` (Stacks 023N), not to rebuild it.
-- /-- **Stacks 08WU.** A module map is universally injective if and only if its character dual
-- is a split epimorphism. -/
-- @[stacks 08WU "iff"]
-- theorem LinearMap.universallyInjective_iff_characterModule_dual_isSplitEpi
--     {R M N : Type u} [CommRing R] [AddCommGroup M] [Module R M]
--     [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
--     f.UniversallyInjective ↔
--       ∃ s : CharacterModule M →ₗ[R] CharacterModule N,
--         (CharacterModule.dual f).comp s = LinearMap.id := by
--   constructor
--   · exact LinearMap.UniversallyInjective.characterModule_dual_isSplitEpi f
--   · rintro ⟨s, hs⟩ Q _ _
--     obtain ⟨t, ht⟩ := CharacterModule.exists_rightInverse_dual_lTensor f s hs Q
--     have hdual : Function.Surjective (CharacterModule.dual (f.lTensor Q)) := by
--       intro c
--       refine ⟨t c, ?_⟩
--       exact DFunLike.congr_fun ht c
--     have hl : Function.Injective (f.lTensor Q) :=
--       CharacterModule.dual_surjective_iff_injective.mp hdual
--     intro x y hxy
--     apply (TensorProduct.comm R M Q).injective
--     apply hl
--     simp only [LinearMap.lTensor_comm, hxy]
--
-- OBLIGATION (deleted `the deleted upstream library` scaffolding): retained verbatim but commented out.
-- Depends on the chosen-pullback / descent-data API that `the deleted upstream library` supplied and that
-- has no Mathlib counterpart. See OBLIGATIONS.md, cluster 2. Preferred restoration is to
-- re-derive from `ModuleCat.comonadicExtendScalars` (Stacks 023N), not to rebuild it.
-- /-- For a universally injective algebra map, the character dual of every map
-- `P ⊗[A] A → P ⊗[A] B` induced by scalar extension is split surjective. -/
-- theorem Algebra.exists_rightInverse_characterModule_dual_lTensor
--     {A B P : Type u} [CommRing A] [CommRing B] [Algebra A B]
--     [AddCommGroup P] [Module A P]
--     (hAB : LinearMap.UniversallyInjective (Algebra.linearMap A B)) :
--     ∃ t : CharacterModule (P ⊗[A] A) →ₗ[A] CharacterModule (P ⊗[A] B),
--       (CharacterModule.dual ((Algebra.linearMap A B).lTensor P)).comp t =
--         LinearMap.id := by
--   obtain ⟨s, hs⟩ :=
--     LinearMap.UniversallyInjective.characterModule_dual_isSplitEpi
--       (Algebra.linearMap A B) hAB
--   exact CharacterModule.exists_rightInverse_dual_lTensor
--     (Algebra.linearMap A B) s hs P
--
/-- The unit map from an `A`-module to its tensor product with an `A`-algebra. -/
def Algebra.tensorUnit (A B P : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup P] [Module A P] : P →ₗ[A] P ⊗[A] B :=
  (Algebra.linearMap A B).lTensor P |>.comp
    (_root_.TensorProduct.rid A P).symm.toLinearMap

@[simp]
theorem Algebra.tensorUnit_apply (A B P : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup P] [Module A P] (p : P) :
    Algebra.tensorUnit A B P p = p ⊗ₜ[A] (1 : B) := by
  simp [Algebra.tensorUnit]

theorem Algebra.tensorUnit_naturality
    {A B P Q : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
    (k : P →ₗ[A] Q) :
    (k.rTensor B).comp (Algebra.tensorUnit A B P) =
      (Algebra.tensorUnit A B Q).comp k := by
  ext p
  simp

-- OBLIGATION (deleted `the deleted upstream library` scaffolding): retained verbatim but commented out.
-- Depends on the chosen-pullback / descent-data API that `the deleted upstream library` supplied and that
-- has no Mathlib counterpart. See OBLIGATIONS.md, cluster 2. Preferred restoration is to
-- re-derive from `ModuleCat.comonadicExtendScalars` (Stacks 023N), not to rebuild it.
-- /-- A fixed character-dual section of a universally injective algebra map.  Keeping this
-- choice independent of the auxiliary tensor factor is essential for the naturality in 08WV. -/
-- noncomputable def Algebra.characterModuleDualSection
--     {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
--     (hAB : LinearMap.UniversallyInjective (Algebra.linearMap A B)) :
--     CharacterModule A →ₗ[A] CharacterModule B :=
--   Classical.choose
--     (LinearMap.UniversallyInjective.characterModule_dual_isSplitEpi
--       (Algebra.linearMap A B) hAB)
--
-- OBLIGATION (deleted `the deleted upstream library` scaffolding): retained verbatim but commented out.
-- Depends on the chosen-pullback / descent-data API that `the deleted upstream library` supplied and that
-- has no Mathlib counterpart. See OBLIGATIONS.md, cluster 2. Preferred restoration is to
-- re-derive from `ModuleCat.comonadicExtendScalars` (Stacks 023N), not to rebuild it.
-- theorem Algebra.characterModuleDualSection_rightInverse
--     {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
--     (hAB : LinearMap.UniversallyInjective (Algebra.linearMap A B)) :
--     (CharacterModule.dual (Algebra.linearMap A B)).comp
--       (Algebra.characterModuleDualSection hAB) = LinearMap.id :=
--   Classical.choose_spec
--     (LinearMap.UniversallyInjective.characterModule_dual_isSplitEpi
--       (Algebra.linearMap A B) hAB)
--
-- OBLIGATION (deleted `the deleted upstream library` scaffolding): retained verbatim but commented out.
-- Depends on the chosen-pullback / descent-data API that `the deleted upstream library` supplied and that
-- has no Mathlib counterpart. See OBLIGATIONS.md, cluster 2. Preferred restoration is to
-- re-derive from `ModuleCat.comonadicExtendScalars` (Stacks 023N), not to rebuild it.
-- /-- Universal injectivity supplies a chosen character-dual section of the tensor unit.
-- This is the vertical splitting used in the proof of Stacks 08X7. -/
-- noncomputable def Algebra.characterModuleTensorUnitSection
--     {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
--     (hAB : LinearMap.UniversallyInjective (Algebra.linearMap A B))
--     (P : Type u) [AddCommGroup P] [Module A P] :
--     CharacterModule P →ₗ[A] CharacterModule (P ⊗[A] B) :=
--   (CharacterModule.dual_lTensorSection
--       (Algebra.characterModuleDualSection hAB) P).comp
--     (CharacterModule.dual (_root_.TensorProduct.rid A P).toLinearMap)
--
-- OBLIGATION (deleted `the deleted upstream library` scaffolding): retained verbatim but commented out.
-- Depends on the chosen-pullback / descent-data API that `the deleted upstream library` supplied and that
-- has no Mathlib counterpart. See OBLIGATIONS.md, cluster 2. Preferred restoration is to
-- re-derive from `ModuleCat.comonadicExtendScalars` (Stacks 023N), not to rebuild it.
-- /-- The character-dual tensor-unit section is a right inverse. -/
-- theorem Algebra.characterModuleTensorUnitSection_rightInverse
--     {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
--     (hAB : LinearMap.UniversallyInjective (Algebra.linearMap A B))
--     (P : Type u) [AddCommGroup P] [Module A P] :
--     (CharacterModule.dual (Algebra.tensorUnit A B P)).comp
--         (Algebra.characterModuleTensorUnitSection hAB P) = LinearMap.id := by
--   let s := Algebra.characterModuleDualSection hAB
--   have hs := Algebra.characterModuleDualSection_rightInverse hAB
--   have hsTensor := CharacterModule.dual_lTensorSection_rightInverse
--     (Algebra.linearMap A B) s hs P
--   change (CharacterModule.dual
--       ((Algebra.linearMap A B).lTensor P |>.comp
--         (_root_.TensorProduct.rid A P).symm.toLinearMap)).comp
--       ((CharacterModule.dual_lTensorSection s P).comp (CharacterModule.dual
--         (_root_.TensorProduct.rid A P).toLinearMap)) = LinearMap.id
--   rw [CharacterModule.dual_comp]
--   ext c p
--   have hsc := DFunLike.congr_fun hsTensor
--     (CharacterModule.dual (_root_.TensorProduct.rid A P).toLinearMap c)
--   have hval := DFunLike.congr_fun hsc
--     ((_root_.TensorProduct.rid A P).symm p)
--   rw [_root_.TensorProduct.rid_symm_apply] at hval
--   change
--     (CharacterModule.dual ((Algebra.linearMap A B).lTensor P)
--       (CharacterModule.dual_lTensorSection s P
--         (CharacterModule.dual (_root_.TensorProduct.rid A P).toLinearMap c)))
--         ((_root_.TensorProduct.rid A P).symm p) = c p
--   rw [_root_.TensorProduct.rid_symm_apply]
--   apply hval.trans
--   change c ((_root_.TensorProduct.rid A P) (p ⊗ₜ[A] (1 : A))) = c p
--   rw [_root_.TensorProduct.rid_tmul, one_smul]
--
-- OBLIGATION (deleted `the deleted upstream library` scaffolding): retained verbatim but commented out.
-- Depends on the chosen-pullback / descent-data API that `the deleted upstream library` supplied and that
-- has no Mathlib counterpart. See OBLIGATIONS.md, cluster 2. Preferred restoration is to
-- re-derive from `ModuleCat.comonadicExtendScalars` (Stacks 023N), not to rebuild it.
-- /-- The chosen character-dual sections of the tensor units are natural in the module. -/
-- theorem Algebra.characterModuleTensorUnitSection_naturality
--     {A B P Q : Type u} [CommRing A] [CommRing B] [Algebra A B]
--     [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
--     (hAB : LinearMap.UniversallyInjective (Algebra.linearMap A B))
--     (k : P →ₗ[A] Q) :
--     (CharacterModule.dual (k.rTensor B)).comp
--         (Algebra.characterModuleTensorUnitSection hAB Q) =
--       (Algebra.characterModuleTensorUnitSection hAB P).comp
--         (CharacterModule.dual k) := by
--   let s := Algebra.characterModuleDualSection hAB
--   change (CharacterModule.dual (k.rTensor B)).comp
--       ((CharacterModule.dual_lTensorSection s Q).comp
--         (CharacterModule.dual (_root_.TensorProduct.rid A Q).toLinearMap)) =
--     ((CharacterModule.dual_lTensorSection s P).comp
--       (CharacterModule.dual (_root_.TensorProduct.rid A P).toLinearMap)).comp
--         (CharacterModule.dual k)
--   have hr :
--       (CharacterModule.dual (k.rTensor A)).comp
--           (CharacterModule.dual (_root_.TensorProduct.rid A Q).toLinearMap) =
--         (CharacterModule.dual (_root_.TensorProduct.rid A P).toLinearMap).comp
--           (CharacterModule.dual k) := by
--     rw [← CharacterModule.dual_comp, ← CharacterModule.dual_comp]
--     congr 1
--     ext p
--     simp
--   rw [← LinearMap.comp_assoc,
--     CharacterModule.dual_lTensorSection_naturality s k,
--     LinearMap.comp_assoc, hr]
--   exact (LinearMap.comp_assoc _ _ _).symm
--
/-- **Stacks 08WR, exactness.** Character duality reverses exact pairs of module maps. -/
@[stacks 08WR "exact"]
theorem CharacterModule.exact_dual
    {R L M N : Type u} [CommRing R]
    [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : L →ₗ[R] M) (g : M →ₗ[R] N)
    (hfg : Function.Exact f g) :
    Function.Exact (CharacterModule.dual g) (CharacterModule.dual f) := by
  apply LinearMap.exact_of_comp_of_mem_range
  · rw [← CharacterModule.dual_comp, hfg.linearMap_comp_eq_zero,
      CharacterModule.dual_zero]
  · intro c hc
    have hc_ker (m : M) (hm : g m = 0) : c m = 0 := by
      obtain ⟨l, hl⟩ := hfg m |>.mp hm
      have hc' := DFunLike.congr_fun hc l
      change c (f l) = 0 at hc'
      rw [← hl]
      exact hc'
    let preimage (y : LinearMap.range g) : M := Classical.choose y.property
    have preimage_spec (y : LinearMap.range g) : g (preimage y) = y :=
      Classical.choose_spec y.property
    let d₀ : CharacterModule (LinearMap.range g) :=
      { toFun := fun y ↦ c (preimage y)
        map_zero' := by
          apply hc_ker
          exact preimage_spec 0
        map_add' := fun y z ↦ by
          have hk : g (preimage (y + z) - (preimage y + preimage z)) = 0 := by
            rw [map_sub, map_add, preimage_spec, preimage_spec, preimage_spec]
            simp
          have hc0 := hc_ker _ hk
          rw [map_sub, map_add, sub_eq_zero] at hc0
          exact hc0 }
    obtain ⟨d, hd⟩ := CharacterModule.dual_surjective_of_injective
      (LinearMap.range g).subtype (Submodule.injective_subtype _) d₀
    refine ⟨d, ?_⟩
    ext m
    let y : LinearMap.range g := ⟨g m, LinearMap.mem_range_self g m⟩
    have hk : g (preimage y - m) = 0 := by
      rw [map_sub, preimage_spec, sub_self]
    have hcpre : c (preimage y) = c m := by
      have := hc_ker _ hk
      rwa [map_sub, sub_eq_zero] at this
    have hdy := DFunLike.congr_fun hd y
    exact hdy.trans hcpre

/-- **Stacks 08X1.** Applying character duality to a split equalizer produces a split
coequalizer. -/
@[stacks 08X1]
def CharacterModule.splitCoequalizerOfSplitEqualizer
    {R : Type u} [CommRing R] {W X Y : ModuleCat.{u} R}
    {f g : X ⟶ Y} {i : W ⟶ X} (q : IsSplitEqualizer f g i) :
    IsSplitCoequalizer
      (ModuleCat.ofHom (CharacterModule.dual f.hom))
      (ModuleCat.ofHom (CharacterModule.dual g.hom))
      (ModuleCat.ofHom (CharacterModule.dual i.hom)) where
  rightSection := ModuleCat.ofHom (CharacterModule.dual q.leftRetraction.hom)
  leftSection := ModuleCat.ofHom (CharacterModule.dual q.rightRetraction.hom)
  condition := by
    apply ModuleCat.hom_ext
    ext c w
    exact congrArg c (ConcreteCategory.congr_hom q.condition w)
  rightSection_π := by
    apply ModuleCat.hom_ext
    ext c w
    exact congrArg c (ConcreteCategory.congr_hom q.ι_leftRetraction w)
  leftSection_bottom := by
    apply ModuleCat.hom_ext
    ext c x
    exact congrArg c (ConcreteCategory.congr_hom q.bottom_rightRetraction x)
  leftSection_top := by
    apply ModuleCat.hom_ext
    ext c x
    exact congrArg c (ConcreteCategory.congr_hom q.top_rightRetraction x)

/-- Character duality reflects an equalizer sequence when the dual sequence is split. This is
the faithfulness step used in the proof of Stacks 08X7. -/
theorem CharacterModule.exact_of_splitCoequalizer_dual
    {R L M N : Type u} [CommRing R]
    [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (i : L →ₗ[R] M) (f g : M →ₗ[R] N)
    (hi : (f - g).comp i = 0)
    (q : IsSplitCoequalizer
      (ModuleCat.ofHom (CharacterModule.dual f))
      (ModuleCat.ofHom (CharacterModule.dual g))
      (ModuleCat.ofHom (CharacterModule.dual i))) :
    Function.Exact i (f - g) := by
  have hbottom := congrArg ModuleCat.Hom.hom q.leftSection_bottom
  change (CharacterModule.dual g).comp q.leftSection.hom = LinearMap.id at hbottom
  have htop := congrArg ModuleCat.Hom.hom q.leftSection_top
  change (CharacterModule.dual f).comp q.leftSection.hom =
    q.rightSection.hom.comp (CharacterModule.dual i) at htop
  have hdual_sub : CharacterModule.dual (f - g) =
      CharacterModule.dual f - CharacterModule.dual g := by
    ext c x
    exact c.map_sub (f x) (g x)
  have hdual_exact : Function.Exact (CharacterModule.dual (f - g))
      (CharacterModule.dual i) := by
    apply LinearMap.exact_of_comp_of_mem_range
    · rw [← CharacterModule.dual_comp, hi, CharacterModule.dual_zero]
    · intro c hc
      refine ⟨-q.leftSection.hom c, ?_⟩
      rw [hdual_sub, LinearMap.sub_apply, map_neg, map_neg]
      have hf := DFunLike.congr_fun htop c
      have hg := DFunLike.congr_fun hbottom c
      change CharacterModule.dual f (q.leftSection.hom c) =
        q.rightSection.hom (CharacterModule.dual i c) at hf
      change CharacterModule.dual g (q.leftSection.hom c) = c at hg
      rw [hf, hg, hc]
      simp
  apply LinearMap.exact_of_comp_of_mem_range hi
  intro x hx
  by_contra hxr
  have hqx : (Submodule.Quotient.mk x : M ⧸ LinearMap.range i) ≠ 0 := by
    intro h
    apply hxr
    rw [← Submodule.Quotient.mk_eq_zero]
    exact h
  obtain ⟨c₀, hc₀⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hqx
  let c : CharacterModule M :=
    c₀.comp (Submodule.mkQ (LinearMap.range i)).toAddMonoidHom
  have hci : CharacterModule.dual i c = 0 := by
    ext l
    change c₀ (Submodule.Quotient.mk (i l)) = 0
    have hm : (Submodule.Quotient.mk (i l) : M ⧸ LinearMap.range i) = 0 := by
      rw [Submodule.Quotient.mk_eq_zero]
      exact LinearMap.mem_range_self i l
    rw [hm, map_zero]
  obtain ⟨d, hd⟩ := hdual_exact c |>.mp hci
  have hcx : c x = 0 := by
    have hdx := DFunLike.congr_fun hd x
    change d ((f - g) x) = c x at hdx
    rw [hx, map_zero] at hdx
    exact hdx.symm
  exact hc₀ hcx

/-- A module fork is an equalizer whenever its character-dual cofork is split. -/
noncomputable def CharacterModule.isLimitFork_of_splitCoequalizer_dual
    {R : Type u} [CommRing R] {M N : ModuleCat.{u} R}
    {f g : M ⟶ N} (s : Fork f g)
    (q : IsSplitCoequalizer
      (ModuleCat.ofHom (CharacterModule.dual f.hom))
      (ModuleCat.ofHom (CharacterModule.dual g.hom))
      (ModuleCat.ofHom (CharacterModule.dual s.ι.hom))) :
    IsLimit s := by
  have hi : (f.hom - g.hom).comp s.ι.hom = 0 := by
    ext x
    exact sub_eq_zero.mpr (ConcreteCategory.congr_hom s.condition x)
  have hex := CharacterModule.exact_of_splitCoequalizer_dual
    s.ι.hom f.hom g.hom hi q
  have hdualSurj : Function.Surjective (CharacterModule.dual s.ι.hom) := by
    intro c
    refine ⟨q.rightSection.hom c, ?_⟩
    have h := DFunLike.congr_fun
      (congrArg ModuleCat.Hom.hom q.rightSection_π) c
    exact h
  have hinj : Function.Injective s.ι.hom :=
    CharacterModule.dual_surjective_iff_injective.mp hdualSurj
  have hk := ModuleCat.isLimitKernelFork s.ι
    (ModuleCat.ofHom (f.hom - g.hom)) hex hinj
  apply IsLimit.ofIsoLimit (CategoryTheory.Preadditive.isLimitForkOfKernelFork hk)
  exact Fork.ext (Iso.refl _)

/-- A retract of a split coequalizer diagram is again a split coequalizer. The morphisms
`b, c` include the last two objects of the smaller diagram into the split one, while
`a', b', c'` provide the compatible maps back. -/
def CategoryTheory.IsSplitCoequalizer.ofRetract
    {C : Type uC} [Category.{vC} C]
    {X Y Z X' Y' Z' : C} {f g : X ⟶ Y} {π : Y ⟶ Z}
    {f' g' : X' ⟶ Y'} {π' : Y' ⟶ Z'}
    (q : IsSplitCoequalizer f' g' π')
    (b : Y ⟶ Y') (c : Z ⟶ Z')
    (a' : X' ⟶ X) (b' : Y' ⟶ Y) (c' : Z' ⟶ Z)
    (hb : b ≫ b' = 𝟙 Y) (hc : c ≫ c' = 𝟙 Z)
    (hf : a' ≫ f = f' ≫ b') (hg : a' ≫ g = g' ≫ b')
    (hπ : b' ≫ π = π' ≫ c') (hπ' : π ≫ c = b ≫ π')
    (hcond : f ≫ π = g ≫ π) :
    IsSplitCoequalizer f g π where
  rightSection := c ≫ q.rightSection ≫ b'
  leftSection := b ≫ q.leftSection ≫ a'
  condition := hcond
  rightSection_π := by
    simp only [Category.assoc]
    rw [hπ]
    simp only [q.rightSection_π_assoc, hc]
  leftSection_bottom := by
    simp only [Category.assoc]
    rw [hg]
    simp only [q.leftSection_bottom_assoc, hb]
  leftSection_top := by
    simp only [Category.assoc]
    rw [hf, reassoc_of% hπ']
    simp only [q.leftSection_top_assoc]

/-- Transport a split equalizer along an isomorphism of functors. -/
def CategoryTheory.IsSplitEqualizer.mapNatIso
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    {F G : C ⥤ D} (e : F ≅ G) {X Y : C} {W : D} {f g : X ⟶ Y}
    {h : W ⟶ F.obj X} (q : IsSplitEqualizer (F.map f) (F.map g) h) :
    IsSplitEqualizer (G.map f) (G.map g) (h ≫ e.hom.app X) where
  leftRetraction := e.inv.app X ≫ q.leftRetraction
  rightRetraction := e.inv.app Y ≫ q.rightRetraction ≫ e.hom.app X
  condition := by
    simp only [Category.assoc]
    rw [← e.hom.naturality f, ← e.hom.naturality g, q.condition_assoc]
  ι_leftRetraction := by simp
  bottom_rightRetraction := by
    rw [← Category.assoc, e.inv.naturality g, Category.assoc,
      q.bottom_rightRetraction_assoc]
    simp
  top_rightRetraction := by
    rw [← Category.assoc, e.inv.naturality f, Category.assoc,
      q.top_rightRetraction_assoc]
    simp only [Category.assoc]

/-- Character duality sends an equalizer of module maps to a coequalizer. -/
noncomputable def CharacterModule.isColimitCofork_of_isLimitFork
    {R : Type u} [CommRing R] {M N E : ModuleCat.{u} R}
    {f g : M ⟶ N} {i : E ⟶ M} (hifg : i ≫ f = i ≫ g)
    (hi : IsLimit (Fork.ofι i hifg)) :
    IsColimit (Cofork.ofπ
      (ModuleCat.ofHom (CharacterModule.dual i.hom)) (by
        apply ModuleCat.hom_ext
        ext c e
        exact congrArg c (ConcreteCategory.congr_hom hifg e)) : Cofork
          (ModuleCat.ofHom (CharacterModule.dual f.hom))
          (ModuleCat.ofHom (CharacterModule.dual g.hom))) := by
  have hexact : Function.Exact i.hom (f.hom - g.hom) := by
    apply LinearMap.exact_of_comp_of_mem_range
    · ext e
      exact sub_eq_zero.mpr (ConcreteCategory.congr_hom hifg e)
    · intro m hm
      have hfgm : f.hom m = g.hom m := sub_eq_zero.mp hm
      let l : ModuleCat.of R R ⟶ M :=
        ModuleCat.ofHom (LinearMap.toSpanSingleton R M m)
      have hl : l ≫ f = l ≫ g := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro r
        dsimp [l]
        simp only [LinearMap.toSpanSingleton_apply, _root_.map_smul, hfgm]
      let eMap : ModuleCat.of R R ⟶ E := hi.lift (Fork.ofι l hl)
      refine ⟨eMap.hom 1, ?_⟩
      have he := ConcreteCategory.congr_hom
        (hi.fac (Fork.ofι l hl) WalkingParallelPair.zero) (1 : R)
      simpa [eMap, l] using he
  have hiinj : Function.Injective i.hom := by
    rw [← ModuleCat.mono_iff_injective]
    exact mono_of_isLimit_fork hi
  have hdualSurj : Function.Surjective (CharacterModule.dual i.hom) :=
    CharacterModule.dual_surjective_iff_injective.mpr hiinj
  have hdualExact := CharacterModule.exact_dual i.hom (f.hom - g.hom) hexact
  have hdualSub : CharacterModule.dual (f.hom - g.hom) =
      CharacterModule.dual f.hom - CharacterModule.dual g.hom := by
    ext c m
    exact c.map_sub (f.hom m) (g.hom m)
  rw [hdualSub] at hdualExact
  exact CategoryTheory.Preadditive.isColimitCoforkOfCokernelCofork
    (ModuleCat.isColimitCokernelCofork
      (ModuleCat.ofHom (CharacterModule.dual f.hom - CharacterModule.dual g.hom))
      (ModuleCat.ofHom (CharacterModule.dual i.hom)) hdualExact hdualSurj)

-- OBLIGATION (deleted `the deleted upstream library` scaffolding): retained verbatim but commented out.
-- Depends on the chosen-pullback / descent-data API that `the deleted upstream library` supplied and that
-- has no Mathlib counterpart. See OBLIGATIONS.md, cluster 2. Preferred restoration is to
-- re-derive from `ModuleCat.comonadicExtendScalars` (Stacks 023N), not to rebuild it.
-- /-- **Stacks 08X7, character-dual retract form.** If tensoring a parallel pair with a
-- universally injective algebra produces a split equalizer, then the character dual of any
-- equalizer fork of the original pair is a split coequalizer. -/
-- @[stacks 08X7 "dual retract"]
-- noncomputable def CharacterModule.splitCoequalizerOfTensorSplitEqualizer
--     {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
--     (hAB : LinearMap.UniversallyInjective (Algebra.linearMap A B))
--     {M N E W : ModuleCat.{u} A} {f g : M ⟶ N} {i : E ⟶ M}
--     (hifg : i ≫ f = i ≫ g) (hi : IsLimit (Fork.ofι i hifg))
--     {h : W ⟶ ModuleCat.of A (M ⊗[A] B)}
--     (q : IsSplitEqualizer
--       (ModuleCat.ofHom (f.hom.rTensor B))
--       (ModuleCat.ofHom (g.hom.rTensor B)) h) :
--     IsSplitCoequalizer
--       (ModuleCat.ofHom (CharacterModule.dual f.hom))
--       (ModuleCat.ofHom (CharacterModule.dual g.hom))
--       (ModuleCat.ofHom (CharacterModule.dual i.hom)) := by
--   let qdual := CharacterModule.splitCoequalizerOfSplitEqualizer q
--   let secMap (P : ModuleCat.{u} A) :
--       ModuleCat.of A (CharacterModule P) ⟶
--         ModuleCat.of A (CharacterModule (P ⊗[A] B)) :=
--     ModuleCat.ofHom (Algebra.characterModuleTensorUnitSection hAB P)
--   let dualCofork : Cofork
--       (ModuleCat.ofHom (CharacterModule.dual f.hom))
--       (ModuleCat.ofHom (CharacterModule.dual g.hom)) :=
--     Cofork.ofπ (ModuleCat.ofHom (CharacterModule.dual i.hom)) (by
--       apply ModuleCat.hom_ext
--       ext c e
--       exact congrArg c (ConcreteCategory.congr_hom hifg e))
--   let hdualColim : IsColimit dualCofork :=
--     CharacterModule.isColimitCofork_of_isLimitFork hifg hi
--   let πq : ModuleCat.of A (CharacterModule (M ⊗[A] B)) ⟶
--       ModuleCat.of A (CharacterModule W) :=
--     ModuleCat.ofHom (CharacterModule.dual h.hom)
--   let πlarge : ModuleCat.of A (CharacterModule M) ⟶
--       ModuleCat.of A (CharacterModule W) :=
--     secMap M ≫ πq
--   have hπlarge :
--       ModuleCat.ofHom (CharacterModule.dual f.hom) ≫ πlarge =
--         ModuleCat.ofHom (CharacterModule.dual g.hom) ≫ πlarge := by
--     simp only [πlarge]
--     rw [← Category.assoc, ← Category.assoc]
--     rw [show ModuleCat.ofHom (CharacterModule.dual f.hom) ≫ secMap M =
--         secMap N ≫ ModuleCat.ofHom (CharacterModule.dual (f.hom.rTensor B)) by
--       apply ModuleCat.hom_ext
--       exact (Algebra.characterModuleTensorUnitSection_naturality hAB f.hom).symm]
--     rw [show ModuleCat.ofHom (CharacterModule.dual g.hom) ≫ secMap M =
--         secMap N ≫ ModuleCat.ofHom (CharacterModule.dual (g.hom.rTensor B)) by
--       apply ModuleCat.hom_ext
--       exact (Algebra.characterModuleTensorUnitSection_naturality hAB g.hom).symm]
--     have hq := qdual.condition
--     change ModuleCat.ofHom (CharacterModule.dual (f.hom.rTensor B)) ≫ πq =
--       ModuleCat.ofHom (CharacterModule.dual (g.hom.rTensor B)) ≫ πq at hq
--     simpa only [Category.assoc] using congrArg (fun z ↦ secMap N ≫ z) hq
--   let c : ModuleCat.of A (CharacterModule E) ⟶
--       ModuleCat.of A (CharacterModule W) :=
--     hdualColim.desc (Cofork.ofπ πlarge hπlarge)
--   let πsmall : ModuleCat.of A (CharacterModule (M ⊗[A] B)) ⟶
--       ModuleCat.of A (CharacterModule E) :=
--     ModuleCat.ofHom (CharacterModule.dual (Algebra.tensorUnit A B M)) ≫
--       ModuleCat.ofHom (CharacterModule.dual i.hom)
--   have hπsmall :
--       ModuleCat.ofHom (CharacterModule.dual (f.hom.rTensor B)) ≫ πsmall =
--         ModuleCat.ofHom (CharacterModule.dual (g.hom.rTensor B)) ≫ πsmall := by
--     dsimp only [πsmall]
--     apply ModuleCat.hom_ext
--     ext c e
--     have he := ConcreteCategory.congr_hom hifg e
--     change c ((f.hom.rTensor B) (Algebra.tensorUnit A B M (i.hom e))) =
--       c ((g.hom.rTensor B) (Algebra.tensorUnit A B M (i.hom e)))
--     simpa [Algebra.tensorUnit_apply] using
--       congrArg c (congrArg (fun n ↦ n ⊗ₜ[A] (1 : B)) he)
--   let c' : ModuleCat.of A (CharacterModule W) ⟶
--       ModuleCat.of A (CharacterModule E) :=
--     qdual.isCoequalizer.desc (Cofork.ofπ πsmall hπsmall)
--   apply CategoryTheory.IsSplitCoequalizer.ofRetract qdual
--     (secMap M)
--     c
--     (ModuleCat.ofHom (CharacterModule.dual (Algebra.tensorUnit A B N)))
--     (ModuleCat.ofHom (CharacterModule.dual (Algebra.tensorUnit A B M)))
--     c'
--   · apply ModuleCat.hom_ext
--     exact Algebra.characterModuleTensorUnitSection_rightInverse hAB M
--   · apply Cofork.IsColimit.hom_ext hdualColim
--     rw [← Category.assoc]
--     rw [show dualCofork.π ≫ c = πlarge from
--       hdualColim.fac (Cofork.ofπ πlarge hπlarge) WalkingParallelPair.one]
--     change πlarge ≫ c' = dualCofork.π
--     rw [show πlarge = secMap M ≫ πq from rfl, Category.assoc]
--     have qfac := qdual.isCoequalizer.fac (Cofork.ofπ πsmall hπsmall)
--       WalkingParallelPair.one
--     change πq ≫ c' = πsmall at qfac
--     rw [qfac]
--     change secMap M ≫
--       (ModuleCat.ofHom (CharacterModule.dual (Algebra.tensorUnit A B M)) ≫
--         dualCofork.π) = dualCofork.π
--     rw [← Category.assoc]
--     have hb : secMap M ≫
--         ModuleCat.ofHom (CharacterModule.dual (Algebra.tensorUnit A B M)) =
--           𝟙 _ := by
--       apply ModuleCat.hom_ext
--       exact Algebra.characterModuleTensorUnitSection_rightInverse hAB M
--     rw [hb, Category.id_comp]
--   · apply ModuleCat.hom_ext
--     ext c n
--     rfl
--   · apply ModuleCat.hom_ext
--     ext c n
--     rfl
--   · change ModuleCat.ofHom (CharacterModule.dual (Algebra.tensorUnit A B M)) ≫
--       ModuleCat.ofHom (CharacterModule.dual i.hom) = πq ≫ c'
--     exact (qdual.isCoequalizer.fac (Cofork.ofπ πsmall hπsmall)
--       WalkingParallelPair.one).symm
--   · change dualCofork.π ≫ c = secMap M ≫ πq
--     exact hdualColim.fac (Cofork.ofπ πlarge hπlarge) WalkingParallelPair.one
--   · apply ModuleCat.hom_ext
--     ext c e
--     exact congrArg c (ConcreteCategory.congr_hom hifg e)
--
-- OBLIGATION (deleted `the deleted upstream library` scaffolding): retained verbatim but commented out.
-- Depends on the chosen-pullback / descent-data API that `the deleted upstream library` supplied and that
-- has no Mathlib counterpart. See OBLIGATIONS.md, cluster 2. Preferred restoration is to
-- re-derive from `ModuleCat.comonadicExtendScalars` (Stacks 023N), not to rebuild it.
-- /-- **Stacks 08X7.** Tensoring with a universally injective algebra preserves every
-- equalizer whose tensor image is a split equalizer. -/
-- @[stacks 08X7]
-- noncomputable def ModuleCat.isLimit_rTensor_of_splitEqualizer
--     {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
--     (hAB : LinearMap.UniversallyInjective (Algebra.linearMap A B))
--     {M N E W : ModuleCat.{u} A} {f g : M ⟶ N} {i : E ⟶ M}
--     (hifg : i ≫ f = i ≫ g) (hi : IsLimit (Fork.ofι i hifg))
--     {h : W ⟶ ModuleCat.of A (M ⊗[A] B)}
--     (q : IsSplitEqualizer
--       (ModuleCat.ofHom (f.hom.rTensor B))
--       (ModuleCat.ofHom (g.hom.rTensor B)) h) :
--     IsLimit (Fork.ofι (ModuleCat.ofHom (i.hom.rTensor B)) (by
--       apply ModuleCat.hom_ext
--       change (f.hom.rTensor B).comp (i.hom.rTensor B) =
--         (g.hom.rTensor B).comp (i.hom.rTensor B)
--       rw [← LinearMap.rTensor_comp, ← LinearMap.rTensor_comp]
--       exact congrArg (fun z : E →ₗ[A] N ↦ z.rTensor B)
--         (congrArg ModuleCat.Hom.hom hifg)) : Fork
--           (ModuleCat.ofHom (f.hom.rTensor B))
--           (ModuleCat.ofHom (g.hom.rTensor B))) := by
--   let q₀ := CharacterModule.splitCoequalizerOfTensorSplitEqualizer hAB hifg hi q
--   let q₁ := CharacterModule.splitCoequalizerRightTensor (P := B) q₀
--   have q₂ : IsSplitCoequalizer
--       (ModuleCat.ofHom (CharacterModule.dual (f.hom.rTensor B)))
--       (ModuleCat.ofHom (CharacterModule.dual (g.hom.rTensor B)))
--       (ModuleCat.ofHom (CharacterModule.dual (i.hom.rTensor B))) := by
--     simpa only [CharacterModule.mapOnDualRightTensor_dual] using q₁
--   exact CharacterModule.isLimitFork_of_splitCoequalizer_dual _ q₂
--
-- OBLIGATION (deleted `the deleted upstream library` scaffolding): retained verbatim but commented out.
-- Depends on the chosen-pullback / descent-data API that `the deleted upstream library` supplied and that
-- has no Mathlib counterpart. See OBLIGATIONS.md, cluster 2. Preferred restoration is to
-- re-derive from `ModuleCat.comonadicExtendScalars` (Stacks 023N), not to rebuild it.
-- /-- The easy direction of Mesablishvili's theorem: if extension of scalars is comonadic,
-- then the algebra map is universally injective. -/
-- theorem Algebra.universallyInjective_of_comonadicLeftAdjoint_extendScalars
--     {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
--     (hcom : CategoryTheory.ComonadicLeftAdjoint
--       (ModuleCat.extendScalars.{u, u, u} (algebraMap A B))) :
--     LinearMap.UniversallyInjective (Algebra.linearMap A B) := by
--   let F := ModuleCat.extendScalars.{u, u, u} (algebraMap A B)
--   let adj := ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap A B)
--   letI : F.Faithful := CategoryTheory.ComonadicLeftAdjoint.faithful F (by
--     simpa [F] using hcom)
--   intro Q _ _ x y hxy
--   let M := ModuleCat.of A Q
--   letI : Module A Q := M.isModule
--   haveI : Mono (adj.unit.app M) := by
--     apply F.mono_of_mono_map
--     letI : IsSplitMono (F.map (adj.unit.app M)) :=
--       IsSplitMono.mk' ⟨adj.counit.app (F.obj M), adj.left_triangle_components M⟩
--     infer_instance
--   have hunit : Function.Injective (adj.unit.app M) := by
--     rw [← ModuleCat.mono_iff_injective]
--     infer_instance
--   have hunit_apply (q : Q) :=
--     ModuleCat.extendRestrictScalarsAdj_unit_app_apply
--       (algebraMap A B) (ModuleCat.of A Q) q
--   let e := ModuleCat.extendScalarsObjEquiv (R := A) (S := B) M
--   have heunit (q : Q) : e (adj.unit.app M q) = (1 : B) ⊗ₜ[A] q := by
--     rw [hunit_apply]
--     exact ModuleCat.extendScalarsObjEquiv_tmul M 1 q
--   have hzero : (LinearMap.rTensor Q (Algebra.linearMap A B)) (x - y) = 0 := by
--     rw [map_sub, hxy, sub_self]
--   let q := _root_.TensorProduct.lid A Q (x - y)
--   have hxmy : x - y = TensorProduct.tmul A (1 : A) q := by
--     calc
--       x - y = (_root_.TensorProduct.lid A Q).symm q :=
--         ((_root_.TensorProduct.lid A Q).symm_apply_apply (x - y)).symm
--       _ = TensorProduct.tmul A (1 : A) q := rfl
--   rw [hxmy] at hzero
--   have hq0 : q = 0 := by
--     apply hunit
--     apply e.injective
--     rw [heunit q, heunit 0]
--     simpa only [LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one,
--       TensorProduct.tmul_zero] using hzero
--   apply sub_eq_zero.mp
--   rw [hxmy, hq0, tmul_zero]
--
-- OBLIGATION (deleted `the deleted upstream library` scaffolding): retained verbatim but commented out.
-- Depends on the chosen-pullback / descent-data API that `the deleted upstream library` supplied and that
-- has no Mathlib counterpart. See OBLIGATIONS.md, cluster 2. Preferred restoration is to
-- re-derive from `ModuleCat.comonadicExtendScalars` (Stacks 023N), not to rebuild it.
-- /-- Universal injectivity of an algebra map implies injectivity of every scalar-extension
-- unit `M → B ⊗[A] M`. -/
-- theorem Algebra.one_tmul_injective_of_universallyInjective
--     {A B M : Type u} [CommRing A] [CommRing B] [Algebra A B]
--     [AddCommGroup M] [Module A M]
--     (h : LinearMap.UniversallyInjective (Algebra.linearMap A B)) :
--     Function.Injective (fun m : M ↦ (1 : B) ⊗ₜ[A] m) := by
--   intro x y hxy
--   have ht := h M
--   have hsource : (1 : A) ⊗ₜ[A] x = (1 : A) ⊗ₜ[A] y := by
--     apply ht
--     simpa using hxy
--   simpa using congrArg (_root_.TensorProduct.lid A M) hsource
--
-- OBLIGATION (deleted `the deleted upstream library` scaffolding): retained verbatim but commented out.
-- Depends on the chosen-pullback / descent-data API that `the deleted upstream library` supplied and that
-- has no Mathlib counterpart. See OBLIGATIONS.md, cluster 2. Preferred restoration is to
-- re-derive from `ModuleCat.comonadicExtendScalars` (Stacks 023N), not to rebuild it.
-- /-- A universally injective scalar extension reflects bijectivity of module maps. -/
-- theorem LinearMap.bijective_of_baseChange_of_universallyInjective
--     {A B M N : Type u} [CommRing A] [CommRing B] [Algebra A B]
--     [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
--     (hAB : LinearMap.UniversallyInjective (Algebra.linearMap A B))
--     (f : M →ₗ[A] N) (hf : Function.Bijective (LinearMap.baseChange B f)) :
--     Function.Bijective f := by
--   constructor
--   · intro x y hxy
--     apply Algebra.one_tmul_injective_of_universallyInjective hAB
--     apply hf.1
--     simpa using congrArg (fun z ↦ (1 : B) ⊗ₜ[A] z) hxy
--   · intro y
--     let q : N →ₗ[A] N ⧸ LinearMap.range f := Submodule.mkQ (LinearMap.range f)
--     obtain ⟨z, hz⟩ := hf.2 ((1 : B) ⊗ₜ[A] y)
--     have hq : (1 : B) ⊗ₜ[A] q y = 0 := by
--       calc
--         _ = (LinearMap.baseChange B q) ((1 : B) ⊗ₜ[A] y) := by simp
--         _ = (LinearMap.baseChange B q) ((LinearMap.baseChange B f) z) := by rw [hz]
--         _ = 0 := by
--           clear hz
--           induction z using TensorProduct.induction_on with
--           | zero => simp
--           | tmul b m =>
--               rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
--               have hm : q (f m) = 0 := by
--                 change (Submodule.Quotient.mk (f m) : N ⧸ LinearMap.range f) = 0
--                 rw [Submodule.Quotient.mk_eq_zero]
--                 exact LinearMap.mem_range_self f m
--               rw [hm, tmul_zero]
--           | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
--     have : q y = 0 :=
--       (Algebra.one_tmul_injective_of_universallyInjective hAB) (by simpa using hq)
--     change (Submodule.Quotient.mk y : N ⧸ LinearMap.range f) = 0 at this
--     rw [Submodule.Quotient.mk_eq_zero] at this
--     exact this
--
-- OBLIGATION (deleted `the deleted upstream library` scaffolding): retained verbatim but commented out.
-- Depends on the chosen-pullback / descent-data API that `the deleted upstream library` supplied and that
-- has no Mathlib counterpart. See OBLIGATIONS.md, cluster 2. Preferred restoration is to
-- re-derive from `ModuleCat.comonadicExtendScalars` (Stacks 023N), not to rebuild it.
-- /-- Under the standard equivalences identifying categorical extension of scalars with tensor
-- products, the image of a module morphism is its usual linear-map base change. -/
-- theorem ModuleCat.extendScalarsObjEquiv_map
--     {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
--     {M N : ModuleCat.{u} A} (f : M ⟶ N) (x : (ModuleCat.extendScalars
--       (algebraMap A B)).obj M) :
--     ModuleCat.extendScalarsObjEquiv (R := A) (S := B) N
--         (((ModuleCat.extendScalars (algebraMap A B)).map f) x) =
--       LinearMap.baseChange B f.hom
--         (ModuleCat.extendScalarsObjEquiv (R := A) (S := B) M x) := by
--   let eM := ModuleCat.extendScalarsObjEquiv (R := A) (S := B) M
--   let eN := ModuleCat.extendScalarsObjEquiv (R := A) (S := B) N
--   have h := DFunLike.congr_fun
--     (ModuleCat.extendScalarsObjEquiv_naturality (R := A) (S := B) f) (eM x)
--   change eN (((ModuleCat.extendScalars (algebraMap A B)).map f) (eM.symm (eM x))) =
--     LinearMap.baseChange B f.hom (eM x) at h
--   simpa using h
--
-- OBLIGATION (deleted `the deleted upstream library` scaffolding): retained verbatim but commented out.
-- Depends on the chosen-pullback / descent-data API that `the deleted upstream library` supplied and that
-- has no Mathlib counterpart. See OBLIGATIONS.md, cluster 2. Preferred restoration is to
-- re-derive from `ModuleCat.comonadicExtendScalars` (Stacks 023N), not to rebuild it.
-- /-- Extension of scalars along a universally injective algebra map reflects
-- isomorphisms. -/
-- theorem ModuleCat.reflectsIsomorphisms_extendScalars_of_universallyInjective
--     {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
--     (hAB : LinearMap.UniversallyInjective (Algebra.linearMap A B)) :
--     (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).ReflectsIsomorphisms := by
--   constructor
--   intro M N f hf
--   rw [ConcreteCategory.isIso_iff_bijective] at hf ⊢
--   apply LinearMap.bijective_of_baseChange_of_universallyInjective hAB f.hom
--   let F := ModuleCat.extendScalars.{u, u, u} (algebraMap A B)
--   let eM := ModuleCat.extendScalarsObjEquiv (R := A) (S := B) M
--   let eN := ModuleCat.extendScalarsObjEquiv (R := A) (S := B) N
--   have hcomm (x : F.obj M) :
--       eN ((F.map f) x) = (LinearMap.baseChange B f.hom) (eM x) := by
--     exact ModuleCat.extendScalarsObjEquiv_map f x
--   constructor
--   · intro x y hxy
--     apply eM.symm.injective
--     apply hf.1
--     apply eN.injective
--     rw [hcomm, hcomm, eM.apply_symm_apply, eM.apply_symm_apply, hxy]
--   · intro y
--     obtain ⟨z, hz⟩ := hf.2 (eN.symm y)
--     refine ⟨eM z, ?_⟩
--     rw [← hcomm, hz, eN.apply_symm_apply]
--
-- OBLIGATION (deleted `the deleted upstream library` scaffolding): retained verbatim but commented out.
-- Depends on the chosen-pullback / descent-data API that `the deleted upstream library` supplied and that
-- has no Mathlib counterpart. See OBLIGATIONS.md, cluster 2. Preferred restoration is to
-- re-derive from `ModuleCat.comonadicExtendScalars` (Stacks 023N), not to rebuild it.
-- /-- The Beck preservation hypothesis for extension of scalars along a universally injective
-- algebra map.  This is the categorical form of Stacks 08X7. -/
-- theorem ModuleCat.preservesLimitOfIsCosplitPair_extendScalars_of_universallyInjective
--     {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
--     (hAB : LinearMap.UniversallyInjective (Algebra.linearMap A B)) :
--     Comonad.PreservesLimitOfIsCosplitPair
--       (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)) := by
--   let F := ModuleCat.extendScalars.{u, u, u} (algebraMap A B)
--   let G := ModuleCat.restrictScalars.{u, u, u} (algebraMap A B)
--   let T := MonoidalCategory.tensorRight (ModuleCat.of A B)
--   refine ⟨?_⟩
--   intro M N f g hcosplit
--   letI : F.IsCosplitPair f g := hcosplit
--   obtain ⟨W, h, ⟨q⟩⟩ := HasSplitEqualizer.splittable
--     (f := F.map f) (g := F.map g)
--   let qFG := q.map G
--   let e : F ⋙ G ≅ T := by
--     let eLeft : F ⋙ G ≅ MonoidalCategory.tensorLeft (ModuleCat.of A B) :=
--       NatIso.ofComponents
--         (fun P ↦ by
--           letI : Module A (F.obj P) := Module.compHom _ (algebraMap A B)
--           let eB := ModuleCat.extendScalarsObjEquiv (R := A) (S := B) P
--           let eA : F.obj P ≃ₗ[A] B ⊗[A] P :=
--             { eB.toEquiv with
--               map_add' := eB.map_add
--               map_smul' := fun a x ↦ by
--                 change eB ((algebraMap A B) a • x) = a • eB x
--                 rw [← IsScalarTower.algebraMap_smul B a]
--                 exact eB.map_smul (algebraMap A B a) x }
--           exact eA.toModuleIso)
--         (fun {P Q} k ↦ by
--           apply ModuleCat.hom_ext
--           ext x
--           exact ModuleCat.extendScalarsObjEquiv_map k x)
--     exact eLeft.trans (BraidedCategory.tensorLeftIsoTensorRight _)
--   let qT := qFG.mapNatIso e
--   letI : PreservesLimit (parallelPair f g) T := by
--     apply preservesLimit_of_preserves_limit_cone (equalizerIsEqualizer f g)
--     refine (isLimitMapConeForkEquiv T (equalizer.condition f g)).symm ?_
--     change IsLimit (Fork.ofι
--       (ModuleCat.ofHom ((equalizer.ι f g).hom.rTensor B)) (by
--         apply ModuleCat.hom_ext
--         change (f.hom.rTensor B).comp ((equalizer.ι f g).hom.rTensor B) =
--           (g.hom.rTensor B).comp ((equalizer.ι f g).hom.rTensor B)
--         rw [← LinearMap.rTensor_comp, ← LinearMap.rTensor_comp]
--         exact congrArg (fun z ↦ z.rTensor B)
--           (congrArg ModuleCat.Hom.hom (equalizer.condition f g))) : Fork
--             (ModuleCat.ofHom (f.hom.rTensor B))
--             (ModuleCat.ofHom (g.hom.rTensor B)))
--     refine ModuleCat.isLimit_rTensor_of_splitEqualizer
--       (W := G.obj W) (h := G.map h ≫ e.hom.app M) hAB
--       (equalizer.condition f g) (equalizerIsEqualizer f g) ?_
--     dsimp [T] at qT
--     exact qT
--   letI : PreservesLimit (parallelPair f g) (F ⋙ G) :=
--     preservesLimit_of_natIso (parallelPair f g) e.symm
--   exact preservesLimit_of_reflects_of_preserves F G
--
-- OBLIGATION (deleted `the deleted upstream library` scaffolding): retained verbatim but commented out.
-- Depends on the chosen-pullback / descent-data API that `the deleted upstream library` supplied and that
-- has no Mathlib counterpart. See OBLIGATIONS.md, cluster 2. Preferred restoration is to
-- re-derive from `ModuleCat.comonadicExtendScalars` (Stacks 023N), not to rebuild it.
-- /-- **Mesablishvili's theorem** (Stacks 08XA): a ring map $A \to B$ is universally
-- injective (as a map of $A$-modules) if and only if extension of scalars along it is
-- comonadic, i.e. if and only if the category of $A$-modules is equivalent to the category of
-- descent data for $A \to B$. In particular descent for modules holds along all universally
-- injective ring maps, not only faithfully flat ones.
--
-- Source: *Stacks and Moduli*, Chapter 3, §3.1 (Descent theory),
-- `rmk:universally-injective-descent`. -/
-- theorem Algebra.universallyInjective_iff_comonadicLeftAdjoint_extendScalars
--     {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] :
--     LinearMap.UniversallyInjective (Algebra.linearMap A B) ↔
--       Nonempty (CategoryTheory.ComonadicLeftAdjoint
--         (ModuleCat.extendScalars.{u, u, u} (algebraMap A B))) := by
--   constructor
--   · intro h
--     let F := ModuleCat.extendScalars.{u, u, u} (algebraMap A B)
--     let adj := ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap A B)
--     letI : F.ReflectsIsomorphisms :=
--       ModuleCat.reflectsIsomorphisms_extendScalars_of_universallyInjective h
--     letI : Comonad.HasEqualizerOfIsCosplitPair F :=
--       ⟨fun _ _ ↦ inferInstance⟩
--     letI : Comonad.PreservesLimitOfIsCosplitPair F :=
--       ModuleCat.preservesLimitOfIsCosplitPair_extendScalars_of_universallyInjective h
--     exact ⟨Comonad.comonadicOfHasPreservesFSplitEqualizersOfReflectsIsomorphisms adj⟩
--   · rintro ⟨hcom⟩
--     exact _root_.Algebra.universallyInjective_of_comonadicLeftAdjoint_extendScalars hcom
--
end RmkUniversallyInjectiveDescent
