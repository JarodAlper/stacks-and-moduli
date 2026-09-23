module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.LocallyFree
public import Mathlib.RingTheory.Flat.Localization
public import StacksAndModuli.API.ModuleDescent
public import StacksAndModuli.API.PullbackAdjoint
public import StacksAndModuli.API.SemilinearTransport
public import StacksAndModuli.API.SpecSections
public import StacksAndModuli.API.FlatLocal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.AlgebraicGeometry.Modules.Presheaf

/-!
# Pullback of quasi-coherent modules along Spec-morphisms

Supporting infrastructure for §2.1 (The Grassmannian, Hilbert, and Quot functors) of
Chapter 2 of *Stacks and Moduli* (the section
heading carries no `sec:` label): computing the
pullback of quasi-coherent sheaves of modules over affine schemes. This file contains no
declaration corresponding to a labelled book result. The pullback of the
tilde of a module along `Spec.map φ` is the tilde of its extension of scalars, by
uniqueness of left adjoints: the pushforward composed with global sections is global
sections composed with restriction of scalars.

Main declarations:
- `AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpen`: restriction of a
  quasicoherent module on an affine scheme to a basic open is module localization.
- `AlgebraicGeometry.Scheme.Modules.isLocalizedModule_sectionsToBasicOpenLinearMap` and
  `flat_sections_top_of_basicOpen_span`: the intrinsic section-level localization and
  coefficient-ring flatness descent over a basic-open cover.
- `AlgebraicGeometry.Scheme.Modules.modulesSpecToSheafObjLinearEquiv`: the explicit
  carrier-preserving equivalence bridging Mathlib's constant-ring sheaf convention and
  intrinsic sections.
- `AlgebraicGeometry.pushforwardCompModuleSpecΓFunctorIso`: global sections of a
  pushforward along `Spec.map φ` as restriction of scalars.
- `AlgebraicGeometry.tildeCompPullbackIso`: pullback of quasi-coherent modules over
  affines is base change.
- `AlgebraicGeometry.pullbackQuasicoherentIso`: the corresponding comparison for an
  arbitrary quasicoherent module on an affine scheme.
- `AlgebraicGeometry.pullbackAffineIsoSpecIso`: the pseudofunctorial comparison between
  affine pullback and pullback after conjugating both schemes by `isoSpec`.
- `AlgebraicGeometry.pullbackQuasicoherentSectionsLinearEquiv`: on global sections, the
  comparison is a linear equivalence with extension of scalars.
- `AlgebraicGeometry.pullbackQuasicoherentIso_naturality` and
  `pullbackQuasicoherentSectionsLinearEquiv_naturality`: the sheaf-level and
  global-sections comparison squares for a morphism of quasicoherent modules.
- `AlgebraicGeometry.pullbackQuasicoherentSections_flat`: affine pullback preserves
  flatness of global sections.
- `AlgebraicGeometry.moduleSpecΓFunctor_flat_to_top_restrictScalars` and
  `moduleSpecΓFunctor_flat_of_top_restrictScalars`: the same affine section comparison
  while retaining an external coefficient ring.
- `AlgebraicGeometry.pullbackQuasicoherentSections_flat_of_isPushout` and
  `pullbackQuasicoherentSections_flat_of_ring_isPushout`: relative affine base change
  over algebraic and categorical pushout squares of coordinate rings.
- `AlgebraicGeometry.pullbackQuasicoherentSections_flat_of_scheme_isPullback`: relative
  flatness of affine global sections across a cartesian square of affine schemes.
- `AlgebraicGeometry.Scheme.Modules.restrict_sections_flat` and
  `pullback_openImmersion_sections_flat`: flatness transport along open immersions.
- `AlgebraicGeometry.Scheme.Modules.restrict_sections_flat_restrictScalars` and
  `pullback_openImmersion_sections_flat_restrictScalars`: the corresponding transport
  over an external coefficient ring.
- `AlgebraicGeometry.pullbackQuasicoherentSections_finite_projective_rank`: consequently,
  finite projectivity and constant rank of affine global sections are preserved.
- `AlgebraicGeometry.moduleSpecΓFunctor_finite_projective_rank_top`: converts the
  `R`-module convention used by `moduleSpecΓFunctor` to the intrinsic section ring
  `Γ(Spec R, ⊤)`.
- `AlgebraicGeometry.exists_finitePresentation_of_moduleSpecΓFunctor`: constructs a
  finite global presentation of an affine quasicoherent sheaf from a finite presentation
  of its global-sections module.
-/

@[expose] public section

open CategoryTheory Limits

universe v₁ v₂ v₃ u₁ u₂ u₃ u

namespace SheafOfModules

section Helper

variable {A B : Type*} [Category A] [Category B]
  {L₁ L₂ : A ⥤ B} {R₁ R₂ : B ⥤ A}

private lemma homEquiv_comp_conjugate (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : L₂ ⟶ L₁) (X : A) (Y : B) (m : L₁.obj X ⟶ Y) :
    adj₂.homEquiv X Y (α.app X ≫ m) =
      adj₁.homEquiv X Y m ≫ (conjugateEquiv adj₁ adj₂ α).app Y := by
  rw [Adjunction.homEquiv_apply, Adjunction.homEquiv_apply, Functor.map_comp]
  let γ := conjugateEquiv adj₁ adj₂ α
  calc
    _ = (adj₁.unit.app X ≫ γ.app (L₁.obj X)) ≫ R₂.map m := by
      rw [← Category.assoc, unit_conjugateEquiv]
    _ = adj₁.unit.app X ≫ (γ.app (L₁.obj X) ≫ R₂.map m) := by
      simp only [Category.assoc]
    _ = adj₁.unit.app X ≫ (R₁.map m ≫ γ.app Y) := by
      rw [γ.naturality m]
    _ = (adj₁.unit.app X ≫ R₁.map m) ≫ γ.app Y := by
      simp only [Category.assoc]

end Helper

variable {C : Type u₁} [Category.{v₁} C]
  {D : Type u₂} [Category.{v₂} D]
  {D' : Type u₃} [Category.{v₃} D']
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {K' : GrothendieckTopology D'}
  {F : C ⥤ D} {G : D ⥤ D'}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  {R' : Sheaf K' RingCat.{u}}
  [Functor.IsContinuous F J K] [Functor.IsContinuous G K K']
  [Functor.IsContinuous (F ⋙ G) J K']
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K K').obj R')
  [(pushforward.{u} φ).IsRightAdjoint]
  [(pushforward.{u} ψ).IsRightAdjoint]
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical rank-one comparison for pullback of sheaves of modules satisfies
the composition cocycle. -/
lemma pullbackObjUnitToUnit_comp :
    letI : (pushforward.{u} (F := F ⋙ G)
      (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ)).IsRightAdjoint :=
      Functor.isRightAdjoint_of_iso (pushforwardComp.{u} φ ψ)
    (pullbackComp φ ψ).hom.app (unit S) ≫
      pullbackObjUnitToUnit (F := F ⋙ G)
        (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ) =
    (pullback ψ).map (pullbackObjUnitToUnit φ) ≫
      pullbackObjUnitToUnit ψ := by
  let χ := φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ
  rw [← cancel_epi ((pullbackComp φ ψ).inv.app (unit S))]
  simp only [Iso.inv_hom_id_app_assoc]
  apply (pullbackPushforwardAdjunction (F := F ⋙ G) χ).homEquiv _ _ |>.injective
  rw [pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]
  rw [homEquiv_comp_conjugate]
  rw [conjugateEquiv_pullbackComp_inv]
  rw [Adjunction.comp_homEquiv]
  change unitToPushforwardObjUnit χ =
    (pullbackPushforwardAdjunction φ).homEquiv _ _
      ((pullbackPushforwardAdjunction ψ).homEquiv _ _
        ((pullback ψ).map (pullbackObjUnitToUnit φ) ≫
          pullbackObjUnitToUnit ψ)) ≫
      (pushforwardComp φ ψ).hom.app (unit R')
  rw [(pullbackPushforwardAdjunction ψ).homEquiv_naturality_left,
    pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]
  rw [(pullbackPushforwardAdjunction φ).homEquiv_naturality_right,
    pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]
  ext U
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical rank-one comparison for pullback along an identity morphism is the
standard pullback identity comparison. -/
lemma pullbackObjUnitToUnit_id (X : AlgebraicGeometry.Scheme.{u}) :
    letI : (pushforward.{u} (𝟙 X : X ⟶ X).toRingCatSheafHom).IsRightAdjoint :=
      (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
        (𝟙 X)).isRightAdjoint
    pullbackObjUnitToUnit (𝟙 X : X ⟶ X).toRingCatSheafHom =
      (AlgebraicGeometry.Scheme.Modules.pullbackId X).hom.app (unit X.ringCatSheaf) := by
  let _ : (pushforward.{u} (𝟙 X : X ⟶ X).toRingCatSheafHom).IsRightAdjoint :=
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
      (𝟙 X)).isRightAdjoint
  apply (pullbackPushforwardAdjunction
    (𝟙 X : X ⟶ X).toRingCatSheafHom).homEquiv _ _ |>.injective
  rw [pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]
  change unitToPushforwardObjUnit (𝟙 X : X ⟶ X).toRingCatSheafHom =
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).homEquiv _ _
      ((AlgebraicGeometry.Scheme.Modules.pullbackId X).hom.app
        (unit X.ringCatSheaf))
  rw [← Category.comp_id
    ((AlgebraicGeometry.Scheme.Modules.pullbackId X).hom.app (unit X.ringCatSheaf))]
  rw [homEquiv_comp_conjugate
    (adj₁ := Adjunction.id)
    (adj₂ := AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X))
    (α := (AlgebraicGeometry.Scheme.Modules.pullbackId X).hom)]
  rw [AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackId_hom]
  ext U
  rfl

end SheafOfModules


/-- The inverse-image functor on open subsets is final.  For every open `U` of the
source, the structured-arrow category has the object `U ≤ f ⁻¹(⊤)` as a terminal
object.  This supplies the categorical input showing that pullback preserves canonical
free sheaves of modules. -/
instance TopologicalSpace.Opens.map_final {X Y : TopCat.{u}} (f : X ⟶ Y) :
    (TopologicalSpace.Opens.map f).Final where
  out U := by
    let t : StructuredArrow U (TopologicalSpace.Opens.map f) :=
      StructuredArrow.mk
        (show U ⟶ (TopologicalSpace.Opens.map f).obj ⊤ from homOfLE le_top)
    apply isConnected_of_isTerminal _ (x := t)
    refine ⟨fun _ ↦ StructuredArrow.homMk (homOfLE le_top), ?_, ?_⟩
    · intro _ j
      exact PEmpty.elim j.as
    · intro _ m _
      apply StructuredArrow.hom_ext
      exact Subsingleton.elim _ _

/-- Pullback of the canonical free module sheaf along an arbitrary scheme morphism is
canonically free on the source. -/
noncomputable def AlgebraicGeometry.Scheme.Modules.pullbackFreeIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (I : Type u) :
    (pullback f).obj (SheafOfModules.free (R := Y.ringCatSheaf) I) ≅
      SheafOfModules.free (R := X.ringCatSheaf) I :=
  SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I

/-- The canonical free-sheaf pullback identification is compatible with replacing a
scheme morphism by an equal one. -/
lemma AlgebraicGeometry.Scheme.Modules.pullbackFreeIso_congr
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (I : Type u) :
    (pullbackFreeIso g I).inv ≫
        (pullbackCongr h).inv.app (SheafOfModules.free I) =
      (pullbackFreeIso f I).inv := by
  subst h
  simp only [pullbackCongr]
  change (pullbackFreeIso f I).inv ≫ 𝟙 _ = (pullbackFreeIso f I).inv
  exact Category.comp_id _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- A standard free generator followed by the inverse pullback comparison is the
pulled-back generator, preceded by the inverse rank-one comparison. -/
lemma AlgebraicGeometry.Scheme.Modules.ιFree_comp_pullbackFreeIso_inv
    {X Y : Scheme.{u}} (f : X ⟶ Y) (I : Type u) (i : I) :
    SheafOfModules.ιFree i ≫ (pullbackFreeIso f I).inv =
      inv (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ≫
        (pullback f).map (SheafOfModules.ιFree i) := by
  rw [← cancel_mono (pullbackFreeIso f I).hom]
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc]
  change SheafOfModules.ιFree i =
    inv (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ≫
      (SheafOfModules.pullback f.toRingCatSheafHom).map (SheafOfModules.ιFree i) ≫
        (SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I).hom
  rw [SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom,
    IsIso.inv_hom_id_assoc]

/-- Pull a presentation of the unit sheaf back along a scheme morphism and normalize
both its free source and rank-one target by the canonical pullback isomorphisms. -/
noncomputable def AlgebraicGeometry.Scheme.Modules.pullbackUnitPresentation
    {X Y : Scheme.{u}} (f : X ⟶ Y) (I : Type u)
    (π : SheafOfModules.free (R := Y.ringCatSheaf) I ⟶
      SheafOfModules.unit Y.ringCatSheaf) :
    SheafOfModules.free (R := X.ringCatSheaf) I ⟶
      SheafOfModules.unit X.ringCatSheaf :=
  (pullbackFreeIso f I).inv ≫ (pullback f).map π ≫
    SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- On each free generator, a normalized pulled-back unit presentation is the
normalized pullback of the corresponding original generator morphism. -/
lemma AlgebraicGeometry.Scheme.Modules.ιFree_comp_pullbackUnitPresentation
    {X Y : Scheme.{u}} (f : X ⟶ Y) (I : Type u)
    (π : SheafOfModules.free (R := Y.ringCatSheaf) I ⟶
      SheafOfModules.unit Y.ringCatSheaf) (i : I) :
    SheafOfModules.ιFree i ≫ pullbackUnitPresentation f I π =
      inv (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ≫
        (pullback f).map (SheafOfModules.ιFree i ≫ π) ≫
  SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom := by
  rw [pullbackUnitPresentation]
  slice_lhs 1 2 => rw [ιFree_comp_pullbackFreeIso_inv]
  simp only [Category.assoc, ← Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- Normalized pullback preserves the assertion that a chosen free generator maps
identically to the unit sheaf. -/
lemma AlgebraicGeometry.Scheme.Modules.ιFree_comp_pullbackUnitPresentation_eq_id
    {X Y : Scheme.{u}} (f : X ⟶ Y) (I : Type u)
    (π : SheafOfModules.free (R := Y.ringCatSheaf) I ⟶
      SheafOfModules.unit Y.ringCatSheaf) (i : I)
    (h : SheafOfModules.ιFree i ≫ π = 𝟙 (SheafOfModules.unit Y.ringCatSheaf)) :
    SheafOfModules.ιFree i ≫ pullbackUnitPresentation f I π =
      𝟙 (SheafOfModules.unit X.ringCatSheaf) := by
  rw [ιFree_comp_pullbackUnitPresentation]
  simp only [h]
  have hmap : (pullback f).map (𝟙 (SheafOfModules.unit Y.ringCatSheaf)) =
      𝟙 ((pullback f).obj (SheafOfModules.unit Y.ringCatSheaf)) :=
    (pullback f).map_id _
  rw [hmap]
  have hid : 𝟙 ((pullback f).obj (SheafOfModules.unit Y.ringCatSheaf)) ≫
      SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom =
        SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom :=
    Category.id_comp _
  rw [hid]
  exact IsIso.inv_hom_id _

/-- A global section of a sheaf of modules on a scheme is determined by its value
on the top open. -/
lemma AlgebraicGeometry.Scheme.Modules.sections_ext_top
    {X : Scheme.{u}} {M : X.Modules} {s t : M.sections}
    (h : s.1 (Opposite.op ⊤) = t.1 (Opposite.op ⊤)) : s = t := by
  ext U
  rw [← s.property (homOfLE le_top).op, ← t.property (homOfLE le_top).op, h]

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- A morphism of sheaves of modules is monic exactly when its underlying maps on all
stalks of additive groups are monic. -/
lemma AlgebraicGeometry.Scheme.Modules.mono_iff_stalk_mono
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) :
    Mono f ↔ ∀ x : X, Mono
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        ((SheafOfModules.toSheaf X.ringCatSheaf).map f).1) := by
  constructor
  · intro hm
    -- `X.Modules` and `SheafOfModules X.ringCatSheaf` carry syntactically distinct category
    -- instances, so the `Mono` hypothesis has to be transported explicitly.
    haveI : Mono (C := SheafOfModules X.ringCatSheaf) f := hm
    haveI : (SheafOfModules.toSheaf X.ringCatSheaf).PreservesMonomorphisms :=
      CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _
    haveI : Mono ((SheafOfModules.toSheaf X.ringCatSheaf).map f) :=
      Functor.map_mono (SheafOfModules.toSheaf X.ringCatSheaf) f
    exact TopCat.Presheaf.stalk_mono_of_mono _
  · intro h
    haveI : ∀ x : X, Mono
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          ((SheafOfModules.toSheaf X.ringCatSheaf).map f).1) := h
    haveI : Mono ((SheafOfModules.toSheaf X.ringCatSheaf).map f) :=
      TopCat.Presheaf.mono_of_stalk_mono _
    exact CategoryTheory.Functor.mono_of_mono_map
      (SheafOfModules.toSheaf X.ringCatSheaf) inferInstance

/-- Morphisms of sheaves of modules are equal when their underlying maps on every
stalk of additive groups are equal. -/
lemma AlgebraicGeometry.Scheme.Modules.hom_ext_stalk
    {X : Scheme.{u}} {M N : X.Modules} {f g : M ⟶ N}
    (h : ∀ x : X,
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          ((SheafOfModules.toSheaf X.ringCatSheaf).map f).1 =
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          ((SheafOfModules.toSheaf X.ringCatSheaf).map g).1) :
    f = g := by
  apply (SheafOfModules.toSheaf X.ringCatSheaf).map_injective
  ext U s
  apply TopCat.Presheaf.section_ext
  intro x hx
  rw [← TopCat.Presheaf.stalkFunctor_map_germ_apply,
    ← TopCat.Presheaf.stalkFunctor_map_germ_apply, h x]

/-- A morphism out of the source of an epimorphism of module sheaves descends globally
when its composite with the kernel vanishes on every stalk. -/
noncomputable def AlgebraicGeometry.Scheme.Modules.epiDescOfStalkKernel
    {X : Scheme.{u}} {M Q N : X.Modules} (p : M ⟶ Q) [Epi p] (g : M ⟶ N)
    (h : ∀ x : X,
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          ((SheafOfModules.toSheaf X.ringCatSheaf).map (kernel.ι p ≫ g)).1 =
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          ((SheafOfModules.toSheaf X.ringCatSheaf).map (0 : kernel p ⟶ N)).1) :
    Q ⟶ N :=
  Abelian.epiDesc p g (by
    apply AlgebraicGeometry.Scheme.Modules.hom_ext_stalk
    exact h)

/-- The stalkwise-constructed descent morphism recovers the original map after the
epimorphism. -/
@[reassoc (attr := simp)]
lemma AlgebraicGeometry.Scheme.Modules.comp_epiDescOfStalkKernel
    {X : Scheme.{u}} {M Q N : X.Modules} (p : M ⟶ Q) [Epi p] (g : M ⟶ N)
    (h : ∀ x : X,
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          ((SheafOfModules.toSheaf X.ringCatSheaf).map (kernel.ι p ≫ g)).1 =
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          ((SheafOfModules.toSheaf X.ringCatSheaf).map (0 : kernel p ⟶ N)).1) :
    p ≫ AlgebraicGeometry.Scheme.Modules.epiDescOfStalkKernel p g h = g := by
  unfold AlgebraicGeometry.Scheme.Modules.epiDescOfStalkKernel
  apply Abelian.comp_epiDesc

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- A stalkwise factorization through an epimorphism annihilates the stalk of its
kernel. -/
lemma AlgebraicGeometry.Scheme.Modules.stalk_kernel_comp_eq_zero_of_factorization
    {X : Scheme.{u}} {M Q N : X.Modules} (p : M ⟶ Q) (g : M ⟶ N) (x : X)
    (h : let Φ := SheafOfModules.toSheaf X.ringCatSheaf ⋙
        TopCat.Sheaf.forget AddCommGrpCat X ⋙
        TopCat.Presheaf.stalkFunctor (X := X) AddCommGrpCat x
      ∃ t : Φ.obj Q ⟶ Φ.obj N, Φ.map g = Φ.map p ≫ t) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        ((SheafOfModules.toSheaf X.ringCatSheaf).map (kernel.ι p ≫ g)).1 =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        ((SheafOfModules.toSheaf X.ringCatSheaf).map (0 : kernel p ⟶ N)).1 := by
  let Φ := SheafOfModules.toSheaf X.ringCatSheaf ⋙
    TopCat.Sheaf.forget AddCommGrpCat X ⋙
    TopCat.Presheaf.stalkFunctor (X := X) AddCommGrpCat x
  letI : (SheafOfModules.toSheaf X.ringCatSheaf).PreservesZeroMorphisms :=
    ⟨fun _ _ ↦ rfl⟩
  letI : (TopCat.Sheaf.forget AddCommGrpCat X).PreservesZeroMorphisms :=
    ⟨fun _ _ ↦ rfl⟩
  letI : Φ.PreservesZeroMorphisms := by
    dsimp only [Φ]
    infer_instance
  obtain ⟨t, ht⟩ := h
  change Φ.map (kernel.ι p ≫ g) = Φ.map 0
  rw [Functor.map_comp, ht, ← Category.assoc, ← Functor.map_comp,
    kernel.condition, Functor.map_zero, zero_comp, Functor.map_zero]

/-- A morphism from the source of an epic module-sheaf quotient descends globally if
it factors through the quotient on every stalk. -/
noncomputable def AlgebraicGeometry.Scheme.Modules.epiDescOfStalkFactorization
    {X : Scheme.{u}} {M Q N : X.Modules} (p : M ⟶ Q) [Epi p] (g : M ⟶ N)
    (h : ∀ x : X,
      let Φ := SheafOfModules.toSheaf X.ringCatSheaf ⋙
        TopCat.Sheaf.forget AddCommGrpCat X ⋙
        TopCat.Presheaf.stalkFunctor (X := X) AddCommGrpCat x
      ∃ t : Φ.obj Q ⟶ Φ.obj N, Φ.map g = Φ.map p ≫ t) :
    Q ⟶ N :=
  epiDescOfStalkKernel p g fun x ↦
    stalk_kernel_comp_eq_zero_of_factorization p g x (h x)

/-- The factor obtained from stalkwise factorizations recovers the original morphism. -/
@[reassoc (attr := simp)]
lemma AlgebraicGeometry.Scheme.Modules.comp_epiDescOfStalkFactorization
    {X : Scheme.{u}} {M Q N : X.Modules} (p : M ⟶ Q) [Epi p] (g : M ⟶ N)
    (h : ∀ x : X,
      let Φ := SheafOfModules.toSheaf X.ringCatSheaf ⋙
        TopCat.Sheaf.forget AddCommGrpCat X ⋙
        TopCat.Presheaf.stalkFunctor (X := X) AddCommGrpCat x
      ∃ t : Φ.obj Q ⟶ Φ.obj N, Φ.map g = Φ.map p ≫ t) :
    p ≫ epiDescOfStalkFactorization p g h = g := by
  apply comp_epiDescOfStalkKernel

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- A morphism of sheaves of modules is an isomorphism exactly when its underlying
maps on all stalks of additive groups are isomorphisms. -/
lemma AlgebraicGeometry.Scheme.Modules.isIso_iff_stalk_isIso
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) :
    IsIso f ↔ ∀ x : X, IsIso
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        ((SheafOfModules.toSheaf X.ringCatSheaf).map f).1) := by
  rw [← TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso]
  exact ⟨fun _ ↦ Functor.map_isIso (SheafOfModules.toSheaf X.ringCatSheaf) f,
    fun _ ↦ by
      haveI : IsIso ((AlgebraicGeometry.Scheme.Modules.toPresheaf X).map f) := by
        change IsIso ((TopCat.Sheaf.forget AddCommGrpCat X).map
          ((SheafOfModules.toSheaf X.ringCatSheaf).map f))
        infer_instance
      exact isIso_of_reflects_iso f
        (AlgebraicGeometry.Scheme.Modules.toPresheaf X)⟩

/-- Precomposing a morphism by an isomorphism does not change its categorical image. -/
noncomputable def CategoryTheory.Abelian.imageIsoImageOfIsoComp
    {C : Type*} [Category C] [Abelian C] {A A' B : C}
    (e : A' ≅ A) (f : A ⟶ B) :
    Abelian.image (e.hom ≫ f) ≅ Abelian.image f := by
  letI : StrongEpi (e.hom ≫ Abelian.factorThruImage f) :=
    strongEpi_of_epi _
  exact Abelian.imageIsoImage _ ≪≫
    (Limits.image.isoStrongEpiMono
      (e.hom ≫ Abelian.factorThruImage f)
      (Abelian.image.ι f) (by simp)).symm

/-- The image comparison for precomposition by an isomorphism commutes with
the canonical inclusions into the target. -/
@[reassoc]
lemma CategoryTheory.Abelian.imageIsoImageOfIsoComp_hom_ι
    {C : Type*} [Category C] [Abelian C] {A A' B : C}
    (e : A' ≅ A) (f : A ⟶ B) :
    (Abelian.imageIsoImageOfIsoComp e f).hom ≫ Abelian.image.ι f =
      Abelian.image.ι (e.hom ≫ f) := by
  rw [Abelian.imageIsoImageOfIsoComp, Iso.trans_hom, Category.assoc,
    Iso.symm_hom, Limits.image.isoStrongEpiMono_inv_comp_mono,
    Abelian.imageIsoImage_hom_comp_image_ι]

/-- The image comparison for precomposition by an isomorphism also commutes
with the canonical epimorphisms onto the images. -/
@[reassoc]
lemma CategoryTheory.Abelian.factorThruImage_comp_imageIsoImageOfIsoComp_hom
    {C : Type*} [Category C] [Abelian C] {A A' B : C}
    (e : A' ≅ A) (f : A ⟶ B) :
    Abelian.factorThruImage (e.hom ≫ f) ≫
        (Abelian.imageIsoImageOfIsoComp e f).hom =
      e.hom ≫ Abelian.factorThruImage f := by
  rw [← cancel_mono (Abelian.image.ι f), Category.assoc,
    Abelian.imageIsoImageOfIsoComp_hom_ι, Abelian.image.fac,
    Category.assoc, Abelian.image.fac]

/-- If a morphism factors through an epimorphism followed by a split monomorphism,
then its categorical image projects isomorphically onto the middle object. -/
lemma CategoryTheory.Abelian.isIso_image_ι_comp_of_epi_splitMono
    {C : Type*} [Category C] [Abelian C] {A B P : C}
    (f : A ⟶ P) (q : A ⟶ B) [Epi q] (t : B ⟶ P) (r : P ⟶ B)
    (hf : q ≫ t = f) (htr : t ≫ r = 𝟙 B) :
    IsIso (Abelian.image.ι f ≫ r) := by
  let p := Abelian.factorThruImage f
  let c := Abelian.image.ι f ≫ r
  have hpc : p ≫ c = q := by
    dsimp only [p, c]
    conv_lhs => rw [← Category.assoc]
    rw [Abelian.image.fac, ← hf, Category.assoc, htr,
      Category.comp_id]
  haveI : Epi p := by dsimp only [p]; infer_instance
  haveI : Epi c := by
    haveI : Epi (p ≫ c) := hpc ▸ inferInstance
    exact epi_of_epi p c
  have hct : c ≫ t = Abelian.image.ι f := by
    rw [← cancel_epi p]
    conv_lhs => rw [← Category.assoc]
    rw [hpc, hf, Abelian.image.fac]
  haveI : Mono c := mono_of_mono_fac hct
  exact isIso_of_mono_of_epi c

namespace AlgebraicGeometry

open Scheme


set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Canonical pullback identifications of free sheaves satisfy the composition cocycle. -/
lemma Scheme.Modules.pullbackFreeIso_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (I : Type u) :
    letI : IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) := inferInstance
    letI : IsIso (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom) := inferInstance
    letI : IsIso (SheafOfModules.pullbackObjUnitToUnit (f ≫ g).toRingCatSheafHom) :=
      inferInstance
    ((Modules.pullbackFreeIso f I).inv ≫
        (Modules.pullback f).map (Modules.pullbackFreeIso g I).inv) ≫
      (Modules.pullbackComp f g).hom.app (SheafOfModules.free I) =
    (Modules.pullbackFreeIso (f ≫ g) I).inv := by
  let _ : IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) := inferInstance
  let _ : IsIso (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom) := inferInstance
  let _ : IsIso (SheafOfModules.pullbackObjUnitToUnit (f ≫ g).toRingCatSheafHom) :=
    inferInstance
  apply Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan I)
  intro i
  change SheafOfModules.ιFree i ≫ _ = SheafOfModules.ιFree i ≫ _
  calc
    _ = (SheafOfModules.ιFree i ≫ (Modules.pullbackFreeIso f I).inv) ≫
        (Modules.pullback f).map (Modules.pullbackFreeIso g I).inv ≫
          (Modules.pullbackComp f g).hom.app (SheafOfModules.free I) := by
      simp only [Category.assoc]
    _ = (inv (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ≫
        (Modules.pullback f).map (SheafOfModules.ιFree i)) ≫
          (Modules.pullback f).map (Modules.pullbackFreeIso g I).inv ≫
            (Modules.pullbackComp f g).hom.app (SheafOfModules.free I) := by
      rw [Scheme.Modules.ιFree_comp_pullbackFreeIso_inv]
    _ = inv (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ≫
        (Modules.pullback f).map
          (SheafOfModules.ιFree i ≫ (Modules.pullbackFreeIso g I).inv) ≫
            (Modules.pullbackComp f g).hom.app (SheafOfModules.free I) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = inv (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ≫
        (Modules.pullback f).map
          (inv (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom) ≫
            (Modules.pullback g).map (SheafOfModules.ιFree i)) ≫
              (Modules.pullbackComp f g).hom.app (SheafOfModules.free I) := by
      rw [Scheme.Modules.ιFree_comp_pullbackFreeIso_inv]
    _ = _ := by
      have hunit :
          (Modules.pullbackComp f g).hom.app (SheafOfModules.unit Z.ringCatSheaf) ≫
              SheafOfModules.pullbackObjUnitToUnit (f ≫ g).toRingCatSheafHom =
            (Modules.pullback f).map
                (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom) ≫
              SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom := by
        have hg := SheafOfModules.pullbackObjUnitToUnit_comp
          g.toRingCatSheafHom f.toRingCatSheafHom
        change (Modules.pullbackComp f g).hom.app
              (SheafOfModules.unit Z.ringCatSheaf) ≫
            SheafOfModules.pullbackObjUnitToUnit (f ≫ g).toRingCatSheafHom =
          (Modules.pullback f).map
              (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom) ≫
            SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom at hg
        exact hg
      have hinv :
          inv (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ≫
              (Modules.pullback f).map
                (inv (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom)) ≫
                (Modules.pullbackComp f g).hom.app
                  (SheafOfModules.unit Z.ringCatSheaf) =
            inv (SheafOfModules.pullbackObjUnitToUnit (f ≫ g).toRingCatSheafHom) := by
        rw [← cancel_mono
          (SheafOfModules.pullbackObjUnitToUnit (f ≫ g).toRingCatSheafHom)]
        simp only [Category.assoc]
        rw [hunit]
        simp only [← Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id]
        rw [show (Modules.pullback f).map
            (𝟙 (SheafOfModules.unit Y.ringCatSheaf)) = 𝟙 _ from
          (Modules.pullback f).map_id _]
        calc
          _ = inv (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ≫
              SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom :=
            congrArg (fun k ↦ k ≫
              SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
                (Category.comp_id _)
          _ = _ := by
            have hh := IsIso.inv_hom_id_assoc
              (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
              (𝟙 (SheafOfModules.unit X.ringCatSheaf))
            change inv (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ≫
                (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom ≫ 𝟙 _) =
              𝟙 _ at hh
            rw [Category.comp_id] at hh
            exact hh
      rw [Functor.map_comp]
      simp only [Category.assoc]
      have hnat := (Modules.pullbackComp f g).hom.naturality
        (SheafOfModules.ιFree i)
      change (Modules.pullback f).map
          ((Modules.pullback g).map (SheafOfModules.ιFree i)) ≫
          (Modules.pullbackComp f g).hom.app (SheafOfModules.free I) =
        (Modules.pullbackComp f g).hom.app (SheafOfModules.unit Z.ringCatSheaf) ≫
          (Modules.pullback (f ≫ g)).map (SheafOfModules.ιFree i) at hnat
      rw [hnat]
      calc
        _ = (inv (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ≫
              (Modules.pullback f).map
                (inv (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom)) ≫
                (Modules.pullbackComp f g).hom.app
                  (SheafOfModules.unit Z.ringCatSheaf)) ≫
              (Modules.pullback (f ≫ g)).map (SheafOfModules.ιFree i) := by
          simp only [Category.assoc]
        _ = inv (SheafOfModules.pullbackObjUnitToUnit (f ≫ g).toRingCatSheafHom) ≫
              (Modules.pullback (f ≫ g)).map (SheafOfModules.ιFree i) := by
          rw [hinv]
        _ = _ :=
          (Scheme.Modules.ιFree_comp_pullbackFreeIso_inv (f ≫ g) I i).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical pullback identification of a free sheaf along an identity morphism
agrees with the standard pullback identity comparison. -/
lemma Scheme.Modules.pullbackFreeIso_id (X : Scheme.{u}) (I : Type u) :
    (Modules.pullbackFreeIso (𝟙 X) I).inv ≫
      (Modules.pullbackId X).hom.app (SheafOfModules.free I) = 𝟙 _ := by
  apply Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan I)
  intro i
  change SheafOfModules.ιFree i ≫
      ((Modules.pullbackFreeIso (𝟙 X) I).inv ≫
        (Modules.pullbackId X).hom.app (SheafOfModules.free I)) =
    SheafOfModules.ιFree i
  rw [← Category.assoc, Scheme.Modules.ιFree_comp_pullbackFreeIso_inv]
  rw [Category.assoc, (Modules.pullbackId X).hom.naturality
    (SheafOfModules.ιFree i), ← Category.assoc]
  have hunit := SheafOfModules.pullbackObjUnitToUnit_id X
  have hinv : inv (SheafOfModules.pullbackObjUnitToUnit
        (𝟙 X : X ⟶ X).toRingCatSheafHom) ≫
      (Modules.pullbackId X).hom.app (SheafOfModules.unit X.ringCatSheaf) = 𝟙 _ := by
    rw [← hunit]
    exact IsIso.inv_hom_id_assoc _ (𝟙 _)
  rw [hinv, Category.id_comp]
  rfl
end AlgebraicGeometry

namespace ModuleCat

/-- Extension of scalars commutes with a free module: `S ⊗[R] (I →₀ R)` is
canonically the free `S`-module `I →₀ S`. -/
noncomputable def extendScalarsFinsuppEquiv
    {R S : CommRingCat.{u}} (f : R ⟶ S) (I : Type u) :
    (extendScalars f.hom).obj (ModuleCat.of R (I →₀ R)) ≃ₗ[S] (I →₀ S) := by
  classical
  letI : Algebra R S := f.hom.toAlgebra
  exact TensorProduct.finsuppScalarRight R S S I

@[simp]
lemma extendScalarsFinsuppEquiv_tmul_single
    {R S : CommRingCat.{u}} (f : R ⟶ S) (I : Type u) (i : I) (s : S) :
    extendScalarsFinsuppEquiv f I
      (s ⊗ₜ[R] Finsupp.single i 1) = Finsupp.single i s := by
  classical
  let _ : Algebra R S := f.hom.toAlgebra
  change TensorProduct.finsuppScalarRight R S S I
    (s ⊗ₜ[R] Finsupp.single i 1) = _
  rw [TensorProduct.finsuppScalarRight_apply_tmul]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Under the standard free-module scalar-extension equivalence, extension of a
standard basis injection is the corresponding basis injection applied to the
rank-one tensor coordinate. -/
lemma extendScalarsFinsuppEquiv_map_lsingle
    {R S : CommRingCat.{u}} (f : R ⟶ S) (I : Type u) (i : I)
    (x : (extendScalars f.hom).obj (ModuleCat.of R R)) :
    letI : Algebra R S := f.hom.toAlgebra
    extendScalarsFinsuppEquiv f I
        ((extendScalars f.hom).map
          (ModuleCat.ofHom (Finsupp.lsingle i (R := R) (M := ModuleCat.of R R))) x) =
      Finsupp.single i (TensorProduct.AlgebraTensorModule.rid R S S x) := by
  classical
  let _ : Algebra R S := f.hom.toAlgebra
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s r =>
      rw [ExtendScalars.map_tmul]
      change TensorProduct.finsuppScalarRight R S S I
        (s ⊗ₜ[R] Finsupp.single i r) = _
      rw [TensorProduct.finsuppScalarRight_apply_tmul]
      simp
  | add x y hx hy => simp only [map_add, hx, hy, Finsupp.single_add]

end ModuleCat

namespace AlgebraicGeometry

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

set_option backward.isDefEq.respectTransparency.types false in
instance moduleSpecΓFunctor_additive :
    (moduleSpecΓFunctor (R := R)).Additive where
  map_add := by
    intros
    rfl

noncomputable instance moduleSpecΓFunctor_preservesFiniteCoproducts :
    PreservesFiniteCoproducts (moduleSpecΓFunctor (R := R)) := by
  infer_instance

/-- The canonical affine global-sections equivalence for the structure sheaf, viewed
as a rank-one free module. -/
noncomputable def unitModuleSpecΓIso (R : CommRingCat.{u}) :
    ModuleCat.of R R ≅ moduleSpecΓFunctor.obj
      (SheafOfModules.unit (Spec R).ringCatSheaf) :=
  tilde.toTildeΓNatIso.app (ModuleCat.of R R)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
lemma unitModuleSpecΓIso_hom_one (R : CommRingCat.{u}) :
    (unitModuleSpecΓIso R).hom 1 = (Scheme.ΓSpecIso R).inv 1 := by
  simp only [unitModuleSpecΓIso, tilde.toTildeΓNatIso, map_one]
  change algebraMap R Γ(Spec R, ⊤) 1 = 1
  exact map_one _

/-- The rank-one affine module comparison is the inverse `ΓSpec` equivalence on
every scalar, not only on `1`. -/
lemma unitModuleSpecΓIso_hom_apply (R : CommRingCat.{u}) (r : R) :
    (unitModuleSpecΓIso R).hom r = (Scheme.ΓSpecIso R).inv r := by
  simp only [unitModuleSpecΓIso, tilde.toTildeΓNatIso]
  rfl

/-- The isomorphism from the tilde of a finite free module to the corresponding free
sheaf identifies each coproduct injection with the image of the standard basis
injection.  The factor `tildeSelf.inv` expresses the canonical identification of the
structure sheaf with the tilde of the rank-one free module. -/
lemma tildeSelf_inv_comp_tildeFinsupp_hom (R : CommRingCat.{u}) (I : Type u) (i : I) :
    ((tildeSelf (R := R)).inv ≫
      tilde.map (ModuleCat.ofHom (Finsupp.lsingle i (R := R)
        (M := ModuleCat.of R R)))) ≫
      (tildeFinsupp I).hom = SheafOfModules.ιFree i := by
  let H : IsColimit <| (tilde.functor R).mapCocone
      (ModuleCat.finsuppCocone R R I) :=
    isColimitOfPreserves (tilde.functor R)
      (ModuleCat.finsuppCoconeIsColimit R R I)
  let e : (Discrete.functor fun (_ : I) ↦ ModuleCat.of R R) ⋙ tilde.functor R ≅
      Discrete.functor fun _ ↦ SheafOfModules.unit.{u} (Spec R).ringCatSheaf :=
    Discrete.natIso (fun _ ↦ tildeSelf (R := R))
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    ((IsColimit.precomposeHomEquiv e.symm _).symm H)
    (coproductIsCoproduct fun _ : I ↦ SheafOfModules.unit (Spec R).ringCatSheaf)
    ⟨i⟩
  change ((e.inv.app ⟨i⟩ ≫
    tilde.map (ModuleCat.ofHom (Finsupp.lsingle i))) ≫
      (((IsColimit.precomposeHomEquiv e.symm _).symm H).coconePointUniqueUpToIso
        (coproductIsCoproduct fun _ : I ↦
          SheafOfModules.unit (Spec R).ringCatSheaf)).hom) =
    Sigma.ι (fun _ : I ↦ SheafOfModules.unit (Spec R).ringCatSheaf) i
  exact h

private lemma id_comp_comp_eq_cancel {C : Type*} [Category C] {X Y Z : C}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z)
    (h : 𝟙 X ≫ (a ≫ b) = c) : a ≫ b = c := by
  simpa only [Category.id_comp] using h

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- After applying affine global sections, the standard basis injection followed by
the `tildeFinsupp` comparison is the global-sections map of the corresponding free
sheaf injection. -/
lemma moduleSpecΓFunctor_map_tildeFinsupp_generator
    (R : CommRingCat.{u}) (I : Type u) (i : I) :
    moduleSpecΓFunctor.map
        ((tilde.functor R).map (ModuleCat.ofHom (Finsupp.lsingle i (R := R)
          (M := ModuleCat.of R R)))) ≫
      moduleSpecΓFunctor.map (tildeFinsupp I).hom =
      moduleSpecΓFunctor.map (SheafOfModules.ιFree i) := by
  have h : moduleSpecΓFunctor.map (tildeSelf (R := R)).inv ≫
      moduleSpecΓFunctor.map
        ((tilde.functor R).map (ModuleCat.ofHom (Finsupp.lsingle i))) ≫
      moduleSpecΓFunctor.map (tildeFinsupp I).hom =
      moduleSpecΓFunctor.map (SheafOfModules.ιFree i) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (fun k ↦ moduleSpecΓFunctor.map k)
      (tildeSelf_inv_comp_tildeFinsupp_hom R I i)
  dsimp only [tildeSelf, Iso.refl_inv] at h
  have hid := moduleSpecΓFunctor.map_id (tilde (ModuleCat.of R R))
  rw [hid] at h
  exact id_comp_comp_eq_cancel _ _ _ h

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the affine tilde–global-sections comparison on a standard free
generator, followed by the canonical comparison with the free sheaf. -/
lemma toTildeΓNatIso_lsingle_comp_tildeFinsupp
    (R : CommRingCat.{u}) (I : Type u) (i : I) :
    ModuleCat.ofHom (Finsupp.lsingle i (R := R) (M := ModuleCat.of R R)) ≫
      tilde.toTildeΓNatIso.hom.app (ModuleCat.of R (I →₀ R)) ≫
        moduleSpecΓFunctor.map (tildeFinsupp I).hom =
      tilde.toTildeΓNatIso.hom.app (ModuleCat.of R R) ≫
        moduleSpecΓFunctor.map (SheafOfModules.ιFree i) := by
  have hn := tilde.toTildeΓNatIso.hom.naturality
    (ModuleCat.ofHom (Finsupp.lsingle i (R := R) (M := ModuleCat.of R R)))
  dsimp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map] at hn
  rw [← Category.assoc, hn, Category.assoc,
    moduleSpecΓFunctor_map_tildeFinsupp_generator R I i]

/-- Global sections of the canonical free sheaf on an affine spectrum are the free
module on the same indexing type. -/
noncomputable def freeModuleSpecΓIso (I : Type u) :
    ModuleCat.of R (I →₀ R) ≅
      moduleSpecΓFunctor.obj
        (SheafOfModules.free (R := (Spec R).ringCatSheaf) I) :=
  tilde.toTildeΓNatIso.app (ModuleCat.of R (I →₀ R)) ≪≫
    moduleSpecΓFunctor.mapIso (tildeFinsupp I)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The affine global-sections equivalence for a free sheaf sends each standard basis
injection to the global-sections map of the corresponding sheaf injection. -/
lemma lsingle_comp_freeModuleSpecΓIso_hom (I : Type u) (i : I) :
    ModuleCat.ofHom (Finsupp.lsingle i (R := R) (M := ModuleCat.of R R)) ≫
        (freeModuleSpecΓIso (R := R) I).hom =
      (unitModuleSpecΓIso R).hom ≫
        moduleSpecΓFunctor.map (SheafOfModules.ιFree i) := by
  simpa only [freeModuleSpecΓIso, unitModuleSpecΓIso, Iso.trans_hom,
    Iso.app_hom, Functor.mapIso_hom] using
    toTildeΓNatIso_lsingle_comp_tildeFinsupp R I i

instance free_isQuasicoherent (I : Type u) :
    (SheafOfModules.free (R := (Spec R).ringCatSheaf) I).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    (tildeFinsupp I) inferInstance

/-- An epimorphism between quasicoherent module sheaves on an affine spectrum is
surjective on global sections. -/
lemma Scheme.Modules.moduleSpecΓFunctor_map_surjective_of_epi
    {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) [Epi f] : Function.Surjective (moduleSpecΓFunctor.map f) := by
  let P := SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
  let M' : P.FullSubcategory := ⟨M, inferInstance⟩
  let N' : P.FullSubcategory := ⟨N, inferInstance⟩
  let f' : M' ⟶ N' := ⟨f⟩
  letI : Epi f' := by
    constructor
    intro Z g h e
    apply ObjectProperty.hom_ext
    apply (cancel_epi f).1
    exact congrArg (fun k ↦ k.hom) e
  haveI : Epi ((tildeEquiv (R := R)).inverse.map f') := inferInstance
  have hs := (ModuleCat.epi_iff_surjective
    ((tildeEquiv (R := R)).inverse.map f')).mp inferInstance
  exact hs

/-- On an affine scheme, restriction of a quasicoherent module to a basic open is the
localization of its global-sections module. -/
lemma Scheme.Modules.isLocalizedModule_basicOpen (M : (Spec R).Modules)
    [M.IsQuasicoherent] (r : R) :
    IsLocalizedModule (.powers r)
      ((modulesSpecToSheaf.obj M).obj.map (PrimeSpectrum.basicOpen r).leTop.op).hom := by
  haveI : IsIso M.fromTildeΓ :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  exact (isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance r

/-- The value of the underlying `R`-module sheaf has the same carrier and `R`-module
structure as the corresponding sections of the original sheaf of modules. -/
noncomputable def Scheme.Modules.modulesSpecToSheafObjLinearEquiv
    (M : (Spec R).Modules) (U : (Spec R).Opens) :
    (modulesSpecToSheaf.obj M).obj.obj (.op U) ≃ₗ[R] Γ(M, U) :=
  LinearEquiv.refl R _

/-- Restriction from global sections to a basic open, expressed through the underlying
constant-ring module sheaf. -/
noncomputable def Scheme.Modules.sectionsToBasicOpenLinearMap
    (M : (Spec R).Modules) (r : R) :
    Γ(M, ⊤) →ₗ[R] Γ(M, PrimeSpectrum.basicOpen r) where
  toFun := M.presheaf.map
    (homOfLE (le_top : (PrimeSpectrum.basicOpen r : (Spec R).Opens) ≤ ⊤)).op
  map_add' := map_add _
  map_smul' := fun c x ↦ M.map_smul_Spec _ c x

/-- Restriction of sections of a quasicoherent module to a basic open is localization,
in the intrinsic section-module convention. -/
lemma Scheme.Modules.isLocalizedModule_sectionsToBasicOpenLinearMap
    (M : (Spec R).Modules) [M.IsQuasicoherent] (r : R) :
    IsLocalizedModule (.powers r) (Scheme.Modules.sectionsToBasicOpenLinearMap M r) := by
  letI : IsLocalizedModule (.powers r)
      ((modulesSpecToSheaf.obj M).obj.map (PrimeSpectrum.basicOpen r).leTop.op).hom :=
    Scheme.Modules.isLocalizedModule_basicOpen M r
  change IsLocalizedModule (.powers r)
    ((modulesSpecToSheaf.obj M).obj.map (PrimeSpectrum.basicOpen r).leTop.op).hom
  infer_instance

/-- For a quasicoherent module on an affine spectrum, flatness over a coefficient ring
descends from a spanning basic-open cover. -/
lemma Scheme.Modules.flat_sections_top_of_basicOpen_span
    {R₀ : Type*} [CommRing R₀] {A : CommRingCat.{u}} [Algebra R₀ A]
    (M : (Spec A).Modules) [M.IsQuasicoherent] (s : Set A) (hs : Ideal.span s = ⊤)
    (hflat : ∀ r : s,
      letI := Module.compHom Γ(M, PrimeSpectrum.basicOpen (r : A)) (algebraMap R₀ A)
      Module.Flat R₀ Γ(M, PrimeSpectrum.basicOpen (r : A))) :
    letI := Module.compHom Γ(M, ⊤) (algebraMap R₀ A)
    Module.Flat R₀ Γ(M, ⊤) := by
  letI : Module R₀ Γ(M, ⊤) := Module.compHom Γ(M, ⊤) (algebraMap R₀ A)
  letI : IsScalarTower R₀ A Γ(M, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let Mₗ (r : s) : Type u := Γ(M, PrimeSpectrum.basicOpen (r : A))
  letI (r : s) : Module R₀ (Mₗ r) := Module.compHom (Mₗ r) (algebraMap R₀ A)
  letI (r : s) : IsScalarTower R₀ A (Mₗ r) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let res (r : s) : Γ(M, ⊤) →ₗ[A] Mₗ r :=
    Scheme.Modules.sectionsToBasicOpenLinearMap M (r : A)
  letI (r : s) : IsLocalizedModule.Away (r : A) (res r) :=
    Scheme.Modules.isLocalizedModule_sectionsToBasicOpenLinearMap M (r : A)
  exact Module.Flat.of_isLocalizedModule_span_of_isScalarTower s hs Mₗ res hflat

/-- Flatness of quasicoherent global sections over an external coefficient ring
passes to the sections on any basic open. -/
lemma Scheme.Modules.flat_sections_basicOpen_of_top
    {R₀ : Type*} [CommRing R₀] {A : CommRingCat.{u}} [Algebra R₀ A]
    (M : (Spec A).Modules) [M.IsQuasicoherent] (r : A)
    (hflat :
      letI := Module.compHom Γ(M, ⊤) (algebraMap R₀ A)
      Module.Flat R₀ Γ(M, ⊤)) :
    letI := Module.compHom Γ(M, PrimeSpectrum.basicOpen r) (algebraMap R₀ A)
    Module.Flat R₀ Γ(M, PrimeSpectrum.basicOpen r) := by
  letI : Module R₀ Γ(M, ⊤) :=
    Module.compHom Γ(M, ⊤) (algebraMap R₀ A)
  letI : Module.Flat R₀ Γ(M, ⊤) := hflat
  letI : IsScalarTower R₀ A Γ(M, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : Module R₀ Γ(M, PrimeSpectrum.basicOpen r) :=
    Module.compHom Γ(M, PrimeSpectrum.basicOpen r) (algebraMap R₀ A)
  letI : IsScalarTower R₀ A Γ(M, PrimeSpectrum.basicOpen r) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : IsLocalizedModule (.powers r)
      (Scheme.Modules.sectionsToBasicOpenLinearMap M r) :=
    Scheme.Modules.isLocalizedModule_sectionsToBasicOpenLinearMap M r
  exact Module.Flat.of_isLocalizedModule_of_flat_base R₀ (.powers r)
    (Scheme.Modules.sectionsToBasicOpenLinearMap M r)

/-- Flatness of quasicoherent global sections follows if every point has a basic-open
neighborhood on which the sections are flat over the external coefficient ring. -/
lemma Scheme.Modules.flat_sections_top_of_pointwise_basicOpen
    {R₀ : Type*} [CommRing R₀] {A : CommRingCat.{u}} [Algebra R₀ A]
    (M : (Spec A).Modules) [M.IsQuasicoherent]
    (hflat : ∀ x : Spec A, ∃ r : A, x ∈ PrimeSpectrum.basicOpen r ∧
      (letI := Module.compHom Γ(M, PrimeSpectrum.basicOpen r) (algebraMap R₀ A)
       Module.Flat R₀ Γ(M, PrimeSpectrum.basicOpen r))) :
    letI := Module.compHom Γ(M, ⊤) (algebraMap R₀ A)
    Module.Flat R₀ Γ(M, ⊤) := by
  let s : Set A := { r |
    letI : Module R₀ Γ(M, PrimeSpectrum.basicOpen r) :=
      Module.compHom Γ(M, PrimeSpectrum.basicOpen r) (algebraMap R₀ A)
    Module.Flat R₀ Γ(M, PrimeSpectrum.basicOpen r) }
  have hcover : (⨆ r ∈ s, PrimeSpectrum.basicOpen r) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨r, hxr, hr⟩ := hflat x
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨r, TopologicalSpace.Opens.mem_iSup.mpr ⟨hr, hxr⟩⟩
  have hs : Ideal.span s = ⊤ :=
    PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mp hcover
  apply Scheme.Modules.flat_sections_top_of_basicOpen_span M s hs
  intro r
  exact r.property

/-- Flatness of sections over an external coefficient ring is invariant under replacing
the open by an equal open. -/
lemma Scheme.Modules.sections_flat_of_eq
    {R₀ : Type*} [CommRing R₀] {X : Scheme.{u}} (M : X.Modules)
    (U V : X.Opens) (h : U = V) (a : R₀ →+* Γ(X, U))
    (hflat :
      letI := Module.compHom Γ(M, U) a
      Module.Flat R₀ Γ(M, U)) :
    let a' : R₀ →+* Γ(X, V) := h ▸ a
    letI := Module.compHom Γ(M, V) a'
    Module.Flat R₀ Γ(M, V) := by
  subst V
  exact hflat

/-- Transport of a section along equality of opens agrees with the presheaf map of the
corresponding `eqToHom`. -/
lemma Scheme.presheafMap_eq_transport {X : Scheme.{u}} (U V : X.Opens)
    (h : U = V) (r : Γ(X, U)) :
    X.presheaf.map (eqToHom h.symm).op r = h ▸ r := by
  subst V
  simp

/-- Evaluating a ring homomorphism transported across equality of opens agrees with
transporting its value. -/
lemma Scheme.ringHom_transport_apply {R : Type*} [NonAssocSemiring R]
    {X : Scheme.{u}} (U V : X.Opens) (h : U = V) (a : R →+* Γ(X, U)) (r : R) :
    (h ▸ a) r = h ▸ a r := by
  subst V
  rfl

/-- Transporting an `appLE` ring homomorphism across equality of its source open gives
the `appLE` homomorphism for the transported open. -/
lemma Scheme.Hom.appLE_hom_transport
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V V' : X.Opens)
    (h : V = V') (e : V ≤ f ⁻¹ᵁ U) (e' : V' ≤ f ⁻¹ᵁ U) :
    h ▸ (f.appLE U V e).hom = (f.appLE U V' e').hom := by
  subst V'
  rfl

/-- Flatness for a restriction-of-scalars module is invariant under equality of the
coefficient maps. -/
lemma Module.Flat.compHom_congr
    {R₀ S M : Type*} [CommRing R₀] [CommRing S] [AddCommGroup M] [Module S M]
    (a b : R₀ →+* S) (h : a = b)
    (hflat :
      letI := Module.compHom M a
      Module.Flat R₀ M) :
    letI := Module.compHom M b
    Module.Flat R₀ M := by
  subst b
  exact hflat

/-- Transfer flatness between two restriction-of-scalars module structures when their
coefficient maps are conjugate by an isomorphism of coefficient rings. -/
lemma Module.Flat.compHom_of_ringEquiv
    {R S A M : Type*} [CommRing R] [CommRing S] [CommRing A]
    [AddCommGroup M] [Module A M] (e : R ≃+* S) (a : R →+* A) (b : S →+* A)
    (h : b.comp e.toRingHom = a)
    (hflat :
      letI := Module.compHom M a
      Module.Flat R M) :
    letI := Module.compHom M b
    Module.Flat S M := by
  letI : Module R M := Module.compHom M a
  letI : Module.Flat R M := hflat
  letI : Module S M := Module.compHom M b
  letI : RingHomInvPair (e : R →+* S) (e.symm : S →+* R) :=
    RingHomInvPair.of_ringEquiv e
  letI : RingHomInvPair (e.symm : S →+* R) (e : R →+* S) :=
    RingHomInvPair.of_ringEquiv e.symm
  let eM : M ≃ₛₗ[(e : R →+* S)] M :=
    { toEquiv := Equiv.refl M
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r m ↦ by
        change a r • m = b (e r) • m
        rw [← RingHom.congr_fun h r]
        rfl }
  exact Module.Flat.of_ringEquiv e eM

/-- The `iff` form of `Module.Flat.compHom_of_ringEquiv`. -/
lemma Module.Flat.compHom_ringEquiv_iff
    {R S A M : Type*} [CommRing R] [CommRing S] [CommRing A]
    [AddCommGroup M] [Module A M] (e : R ≃+* S) (a : R →+* A) (b : S →+* A)
    (h : b.comp e.toRingHom = a) :
    (letI := Module.compHom M a
     Module.Flat R M) ↔
    (letI := Module.compHom M b
     Module.Flat S M) := by
  constructor
  · exact Module.Flat.compHom_of_ringEquiv e a b h
  · intro hflat
    apply Module.Flat.compHom_of_ringEquiv e.symm b a
    · ext r
      have hr := RingHom.congr_fun h (e.symm r)
      simpa using hr.symm
    · exact hflat

/-- Flatness of sections over an external coefficient ring is invariant under an
isomorphism of module sheaves on the same scheme. -/
lemma Scheme.Modules.sections_flat_of_iso_restrictScalars
    {R₀ : Type*} [CommRing R₀] {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (U : X.Opens) (a : R₀ →+* Γ(X, U))
    (hflat :
      letI := Module.compHom Γ(M, U) a
      Module.Flat R₀ Γ(M, U)) :
    letI := Module.compHom Γ(N, U) a
    Module.Flat R₀ Γ(N, U) := by
  letI : Module R₀ Γ(M, U) := Module.compHom Γ(M, U) a
  letI : Module.Flat R₀ Γ(M, U) := hflat
  letI : Module R₀ Γ(N, U) := Module.compHom Γ(N, U) a
  let eUCat : M.val.obj (Opposite.op U) ≅ N.val.obj (Opposite.op U) :=
    { hom := e.hom.val.app (Opposite.op U)
      inv := e.inv.val.app (Opposite.op U)
      hom_inv_id := congrArg (fun k ↦ k.val.app (Opposite.op U)) e.hom_inv_id
      inv_hom_id := congrArg (fun k ↦ k.val.app (Opposite.op U)) e.inv_hom_id }
  let eU : Γ(M, U) ≃ₗ[R₀] Γ(N, U) :=
    { toEquiv := eUCat.toLinearEquiv.toEquiv
      map_add' := eUCat.toLinearEquiv.map_add
      map_smul' := fun r m ↦ by
        change e.hom.val.app (Opposite.op U) (a r • m) =
          a r • e.hom.val.app (Opposite.op U) m
        exact _root_.map_smul _ _ _ }
  exact Module.Flat.of_linearEquiv eU.symm

/-- Finite projectivity and constant rank of sections are preserved by an isomorphism
of module sheaves on the same scheme. -/
lemma Scheme.Modules.sections_finite_projective_rank_of_iso
    {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) (U : X.Opens) {q : ℕ}
    (hfin : Module.Finite Γ(X, U) Γ(M, U))
    (hproj : Module.Projective Γ(X, U) Γ(M, U))
    (hrank : ∀ p : PrimeSpectrum Γ(X, U), Module.rankAtStalk Γ(M, U) p = q) :
    Module.Finite Γ(X, U) Γ(N, U) ∧ Module.Projective Γ(X, U) Γ(N, U) ∧
      ∀ p : PrimeSpectrum Γ(X, U), Module.rankAtStalk Γ(N, U) p = q := by
  let eUCat : M.val.obj (Opposite.op U) ≅ N.val.obj (Opposite.op U) :=
    { hom := e.hom.val.app (Opposite.op U)
      inv := e.inv.val.app (Opposite.op U)
      hom_inv_id := congrArg (fun k ↦ k.val.app (Opposite.op U)) e.hom_inv_id
      inv_hom_id := congrArg (fun k ↦ k.val.app (Opposite.op U)) e.inv_hom_id }
  let eU : Γ(M, U) ≃ₗ[Γ(X, U)] Γ(N, U) := eUCat.toLinearEquiv
  refine ⟨@Module.Finite.equiv Γ(X, U) _ _ _ _ _ _ _ hfin eU,
    @Module.Projective.of_equiv _ _ _ _ _ _ _ _ _ _ _ _ _ _ eU hproj, ?_⟩
  intro p
  exact (congrFun (Module.rankAtStalk_eq_of_equiv eU) p).symm.trans (hrank p)

/-- On an affine spectrum, finite projectivity and constant rank for the `R`-module of
global sections imply the corresponding intrinsic statement over `Γ(Spec R, ⊤)`.
The two module structures differ by `Scheme.ΓSpecIso`. -/
lemma moduleSpecΓFunctor_finite_projective_rank_top (M : (Spec R).Modules) {q : ℕ}
    (hfin : Module.Finite R (moduleSpecΓFunctor.obj M))
    (hproj : Module.Projective R (moduleSpecΓFunctor.obj M))
    (hrank : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk (moduleSpecΓFunctor.obj M) p = q) :
    Module.Finite Γ(Spec R, ⊤) Γ(M, ⊤) ∧
      Module.Projective Γ(Spec R, ⊤) Γ(M, ⊤) ∧
      ∀ p : PrimeSpectrum Γ(Spec R, ⊤), Module.rankAtStalk Γ(M, ⊤) p = q := by
  let eR := (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv
  letI : Algebra R Γ(Spec R, ⊤) := eR.toRingHom.toAlgebra
  letI : RingHomInvPair (eR : R →+* Γ(Spec R, ⊤))
      (eR.symm : Γ(Spec R, ⊤) →+* R) := RingHomInvPair.of_ringEquiv eR
  letI : RingHomInvPair (eR.symm : Γ(Spec R, ⊤) →+* R)
      (eR : R →+* Γ(Spec R, ⊤)) := ⟨by ext; simp, by ext; simp⟩
  let eM : moduleSpecΓFunctor.obj M ≃ₛₗ[(eR : R →+* Γ(Spec R, ⊤))] Γ(M, ⊤) :=
    { toEquiv := Equiv.refl _
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact Module.finite_projective_rankAtStalk_of_semilinearEquiv eR rfl eM
    hfin hproj hrank

/-- Flatness in the `R`-module convention used by `moduleSpecΓFunctor` implies intrinsic
flatness over `Γ(Spec R, ⊤)`. -/
lemma moduleSpecΓFunctor_flat_to_top (M : (Spec R).Modules)
    [Module.Flat R (moduleSpecΓFunctor.obj M)] :
    Module.Flat Γ(Spec R, ⊤) Γ(M, ⊤) := by
  let eR := (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv
  letI : Algebra R Γ(Spec R, ⊤) := eR.toRingHom.toAlgebra
  letI : RingHomInvPair (eR : R →+* Γ(Spec R, ⊤))
      (eR.symm : Γ(Spec R, ⊤) →+* R) := RingHomInvPair.of_ringEquiv eR
  letI : RingHomInvPair (eR.symm : Γ(Spec R, ⊤) →+* R)
      (eR : R →+* Γ(Spec R, ⊤)) := ⟨by ext; simp, by ext; simp⟩
  let eM : moduleSpecΓFunctor.obj M ≃ₛₗ[(eR : R →+* Γ(Spec R, ⊤))]
      Γ(M, ⊤) :=
    { toEquiv := Equiv.refl _
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact Module.Flat.baseChange_of_semilinearEquiv eR rfl eM

/-- The preceding comparison with intrinsic top sections, while retaining an arbitrary
external coefficient ring. -/
lemma moduleSpecΓFunctor_flat_to_top_restrictScalars
    {R₀ : Type*} [CommRing R₀] (M : (Spec R).Modules) (f : R₀ →+* R)
    [Module R₀ (moduleSpecΓFunctor.obj M)]
    (hsmul : ∀ (r : R₀) (m : moduleSpecΓFunctor.obj M), r • m = f r • m)
    [Module.Flat R₀ (moduleSpecΓFunctor.obj M)] :
    letI := Module.compHom Γ(M, ⊤)
      ((Scheme.ΓSpecIso R).inv.hom.comp f)
    Module.Flat R₀ Γ(M, ⊤) := by
  letI : Module R₀ Γ(M, ⊤) := Module.compHom Γ(M, ⊤)
    ((Scheme.ΓSpecIso R).inv.hom.comp f)
  let e : moduleSpecΓFunctor.obj M ≃ₗ[R₀] Γ(M, ⊤) :=
    { toEquiv := Equiv.refl _
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r m ↦ by
        change r • m = (Scheme.ΓSpecIso R).inv (f r) •
          (show Γ(M, ⊤) from m)
        rw [hsmul]
        rfl }
  let h : Module.Flat R₀ Γ(M, ⊤) := Module.Flat.of_linearEquiv e.symm
  exact h

/-- The converse external-coefficient comparison between intrinsic top sections and
`moduleSpecΓFunctor`. -/
lemma moduleSpecΓFunctor_flat_of_top_restrictScalars
    {R₀ : Type*} [CommRing R₀] (M : (Spec R).Modules) (f : R₀ →+* R)
    [Module R₀ Γ(M, ⊤)]
    (hsmul : ∀ (r : R₀) (m : Γ(M, ⊤)),
      r • m = (Scheme.ΓSpecIso R).inv (f r) • m)
    [Module.Flat R₀ Γ(M, ⊤)] :
    letI := Module.compHom (moduleSpecΓFunctor.obj M) f
    Module.Flat R₀ (moduleSpecΓFunctor.obj M) := by
  letI : Module R₀ (moduleSpecΓFunctor.obj M) :=
    Module.compHom (moduleSpecΓFunctor.obj M) f
  let e : moduleSpecΓFunctor.obj M ≃ₗ[R₀] Γ(M, ⊤) :=
    { toEquiv := Equiv.refl _
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r m ↦ by
        change f r • m = r • (show Γ(M, ⊤) from m)
        rw [hsmul]
        rfl }
  exact Module.Flat.of_linearEquiv e

/-- The intrinsic flatness statement over `Γ(Spec R, ⊤)` implies the corresponding
statement for the `R`-module convention used by `moduleSpecΓFunctor`. -/
lemma moduleSpecΓFunctor_flat_of_top (M : (Spec R).Modules)
    [Module.Flat Γ(Spec R, ⊤) Γ(M, ⊤)] :
    Module.Flat R (moduleSpecΓFunctor.obj M) := by
  let eR := (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
  letI : Algebra Γ(Spec R, ⊤) R := eR.toRingHom.toAlgebra
  letI : RingHomInvPair (eR : Γ(Spec R, ⊤) →+* R)
      (eR.symm : R →+* Γ(Spec R, ⊤)) := RingHomInvPair.of_ringEquiv eR
  letI : RingHomInvPair (eR.symm : R →+* Γ(Spec R, ⊤))
      (eR : Γ(Spec R, ⊤) →+* R) := ⟨by ext; simp, by ext; simp⟩
  let eM : Γ(M, ⊤) ≃ₛₗ[(eR : Γ(Spec R, ⊤) →+* R)]
      moduleSpecΓFunctor.obj M :=
    { toEquiv := Equiv.refl _
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r m ↦ by
        change r • m = (Scheme.ΓSpecIso R).inv ((Scheme.ΓSpecIso R).hom r) • m
        simp }
  exact Module.Flat.baseChange_of_semilinearEquiv eR rfl eM

/-- The intrinsic finite-projective statement over `Γ(Spec R, ⊤)` implies the
corresponding statement for the `R`-module convention used by `moduleSpecΓFunctor`. -/
lemma moduleSpecΓFunctor_finite_projective_of_top (M : (Spec R).Modules)
    (hfin : Module.Finite Γ(Spec R, ⊤) Γ(M, ⊤))
    (hproj : Module.Projective Γ(Spec R, ⊤) Γ(M, ⊤)) :
    Module.Finite R (moduleSpecΓFunctor.obj M) ∧
      Module.Projective R (moduleSpecΓFunctor.obj M) := by
  let eR := (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
  letI : Algebra Γ(Spec R, ⊤) R := eR.toRingHom.toAlgebra
  letI : RingHomInvPair (eR : Γ(Spec R, ⊤) →+* R)
      (eR.symm : R →+* Γ(Spec R, ⊤)) := RingHomInvPair.of_ringEquiv eR
  letI : RingHomInvPair (eR.symm : R →+* Γ(Spec R, ⊤))
      (eR : Γ(Spec R, ⊤) →+* R) := ⟨by ext; simp, by ext; simp⟩
  let eM : Γ(M, ⊤) ≃ₛₗ[(eR : Γ(Spec R, ⊤) →+* R)]
      moduleSpecΓFunctor.obj M :=
    { toEquiv := Equiv.refl _
      map_add' := fun _ _ => rfl
      map_smul' := fun r m => by
        change r • m = (Scheme.ΓSpecIso R).inv ((Scheme.ΓSpecIso R).hom r) • m
        simp }
  exact Module.finite_projective_of_semilinearEquiv eR rfl eM hfin hproj

/-- Restricting a module sheaf along an open immersion transports flatness of sections
from the corresponding image open. -/
lemma Scheme.Modules.restrict_sections_flat
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules) (U : X.Opens)
    [Module.Flat Γ(Y, f ''ᵁ U) Γ(M, f ''ᵁ U)] :
    Module.Flat Γ(X, U) Γ(M.restrict f, U) := by
  let eR := (f.appIso U).commRingCatIsoToRingEquiv
  letI : Algebra Γ(Y, f ''ᵁ U) Γ(X, U) := eR.toRingHom.toAlgebra
  letI : RingHomInvPair (eR : Γ(Y, f ''ᵁ U) →+* Γ(X, U))
      (eR.symm : Γ(X, U) →+* Γ(Y, f ''ᵁ U)) := RingHomInvPair.of_ringEquiv eR
  letI : RingHomInvPair (eR.symm : Γ(X, U) →+* Γ(Y, f ''ᵁ U))
      (eR : Γ(Y, f ''ᵁ U) →+* Γ(X, U)) := ⟨by ext; simp, by ext; simp⟩
  let eM : Γ(M, f ''ᵁ U) ≃ₛₗ[(eR : Γ(Y, f ''ᵁ U) →+* Γ(X, U))]
      Γ(M.restrict f, U) :=
    { toEquiv :=
        { toFun := (M.restrictAppIso f U).inv
          invFun := (M.restrictAppIso f U).hom
          left_inv := fun m ↦ by simp
          right_inv := fun m ↦ by simp }
      map_add' := fun _ _ ↦ map_add _ _ _
      map_smul' := fun r m ↦ by
        change (M.restrictAppIso f U).inv (r • m) =
          (f.appIso U).hom r • (M.restrictAppIso f U).inv m
        simp }
  exact Module.Flat.baseChange_of_semilinearEquiv eR rfl eM

/-- Restriction along an open immersion preserves flatness over an arbitrary external
coefficient ring. -/
lemma Scheme.Modules.restrict_sections_flat_restrictScalars
    {R₀ : Type*} [CommRing R₀] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules) (U : X.Opens)
    (a : R₀ →+* Γ(Y, f ''ᵁ U))
    (hflat :
      letI := Module.compHom Γ(M, f ''ᵁ U) a
      Module.Flat R₀ Γ(M, f ''ᵁ U)) :
    letI := Module.compHom Γ(M.restrict f, U)
      ((f.appIso U).hom.hom.comp a)
    Module.Flat R₀ Γ(M.restrict f, U) := by
  letI : Module R₀ Γ(M, f ''ᵁ U) := Module.compHom Γ(M, f ''ᵁ U) a
  letI : Module.Flat R₀ Γ(M, f ''ᵁ U) := hflat
  letI : Module R₀ Γ(M.restrict f, U) := Module.compHom Γ(M.restrict f, U)
    ((f.appIso U).hom.hom.comp a)
  let e : Γ(M, f ''ᵁ U) ≃ₗ[R₀] Γ(M.restrict f, U) :=
    { toEquiv :=
        { toFun := (M.restrictAppIso f U).inv
          invFun := (M.restrictAppIso f U).hom
          left_inv := fun m ↦ by simp
          right_inv := fun m ↦ by simp }
      map_add' := map_add _
      map_smul' := fun r m ↦ by
        change (M.restrictAppIso f U).inv (a r • m) =
          (f.appIso U).hom (a r) • (M.restrictAppIso f U).inv m
        simp }
  exact Module.Flat.of_linearEquiv e.symm

/-- Conversely, the intrinsic finite-projective constant-rank statement over
`Γ(Spec R, ⊤)` implies the corresponding statement for the `R`-module convention used
by `moduleSpecΓFunctor`. -/
lemma moduleSpecΓFunctor_finite_projective_rank_of_top (M : (Spec R).Modules) {q : ℕ}
    (hfin : Module.Finite Γ(Spec R, ⊤) Γ(M, ⊤))
    (hproj : Module.Projective Γ(Spec R, ⊤) Γ(M, ⊤))
    (hrank : ∀ p : PrimeSpectrum Γ(Spec R, ⊤),
      Module.rankAtStalk Γ(M, ⊤) p = q) :
    Module.Finite R (moduleSpecΓFunctor.obj M) ∧
      Module.Projective R (moduleSpecΓFunctor.obj M) ∧
      ∀ p : PrimeSpectrum R,
        Module.rankAtStalk (moduleSpecΓFunctor.obj M) p = q := by
  let eR := (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
  letI : Algebra Γ(Spec R, ⊤) R := eR.toRingHom.toAlgebra
  letI : RingHomInvPair (eR : Γ(Spec R, ⊤) →+* R)
      (eR.symm : R →+* Γ(Spec R, ⊤)) := RingHomInvPair.of_ringEquiv eR
  letI : RingHomInvPair (eR.symm : R →+* Γ(Spec R, ⊤))
      (eR : Γ(Spec R, ⊤) →+* R) := ⟨by ext; simp, by ext; simp⟩
  let eM : Γ(M, ⊤) ≃ₛₗ[(eR : Γ(Spec R, ⊤) →+* R)]
      moduleSpecΓFunctor.obj M :=
    { toEquiv := Equiv.refl _
      map_add' := fun _ _ => rfl
      map_smul' := fun r m => by
        change r • m = (Scheme.ΓSpecIso R).inv ((Scheme.ΓSpecIso R).hom r) • m
        simp }
  exact Module.finite_projective_rankAtStalk_of_semilinearEquiv eR rfl eM
    hfin hproj hrank

/-- Restricting a module sheaf along an open immersion transports finite projectivity
from the corresponding image open. -/
lemma Scheme.Modules.restrict_sections_finite_projective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules) (U : X.Opens)
    (hfin : Module.Finite Γ(Y, f ''ᵁ U) Γ(M, f ''ᵁ U))
    (hproj : Module.Projective Γ(Y, f ''ᵁ U) Γ(M, f ''ᵁ U)) :
    Module.Finite Γ(X, U) Γ(M.restrict f, U) ∧
      Module.Projective Γ(X, U) Γ(M.restrict f, U) := by
  let eR := (f.appIso U).commRingCatIsoToRingEquiv
  letI : Algebra Γ(Y, f ''ᵁ U) Γ(X, U) := eR.toRingHom.toAlgebra
  letI : RingHomInvPair (eR : Γ(Y, f ''ᵁ U) →+* Γ(X, U))
      (eR.symm : Γ(X, U) →+* Γ(Y, f ''ᵁ U)) := RingHomInvPair.of_ringEquiv eR
  letI : RingHomInvPair (eR.symm : Γ(X, U) →+* Γ(Y, f ''ᵁ U))
      (eR : Γ(Y, f ''ᵁ U) →+* Γ(X, U)) := ⟨by ext; simp, by ext; simp⟩
  let eM : Γ(M, f ''ᵁ U) ≃ₛₗ[(eR : Γ(Y, f ''ᵁ U) →+* Γ(X, U))]
      Γ(M.restrict f, U) :=
    { toEquiv :=
        { toFun := (M.restrictAppIso f U).inv
          invFun := (M.restrictAppIso f U).hom
          left_inv := fun m => by simp
          right_inv := fun m => by simp }
      map_add' := fun _ _ => map_add _ _ _
      map_smul' := fun r m => by
        change (M.restrictAppIso f U).inv (r • m) =
          (f.appIso U).hom r • (M.restrictAppIso f U).inv m
        simp }
  exact Module.finite_projective_of_semilinearEquiv eR rfl eM hfin hproj

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Restriction of sheaves of modules along an open immersion preserves kernels.

After forgetting the module and sheaf structures, restriction is precomposition on
abelian-group-valued presheaves, where limits are computed pointwise. -/
lemma Scheme.Modules.restrictFunctor_preservesKernel
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {M N : Y.Modules} (g : M ⟶ N) :
    PreservesLimit (parallelPair g 0) (Scheme.Modules.restrictFunctor f) := by
  let _ : (SheafOfModules.forget X.ringCatSheaf).Full :=
    (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).full
  let _ : (SheafOfModules.forget X.ringCatSheaf).Faithful :=
    (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).faithful
  let _ : PreservesLimit (parallelPair g 0)
      (Scheme.Modules.restrictFunctor f ⋙
        SheafOfModules.forget X.ringCatSheaf) := by
    let R := SheafOfModules.forget Y.ringCatSheaf ⋙
      PresheafOfModules.toPresheaf Y.ringCatSheaf.obj ⋙
      (CategoryTheory.Functor.whiskeringLeft _ _ _).obj f.opensFunctor.op
    let L := (Scheme.Modules.restrictFunctor f ⋙
      SheafOfModules.forget X.ringCatSheaf) ⋙
      PresheafOfModules.toPresheaf X.ringCatSheaf.obj
    let e : R ≅ L := NatIso.ofComponents (fun _ ↦ Iso.refl _)
    let _ : PreservesLimit (parallelPair g 0) R := by
      dsimp only [R]
      let _ : PreservesLimit (parallelPair g 0)
          (SheafOfModules.forget Y.ringCatSheaf ⋙
            PresheafOfModules.toPresheaf Y.ringCatSheaf.obj) := by
        let _ : PreservesFiniteLimits
            (SheafOfModules.forget Y.ringCatSheaf) :=
          SheafOfModules.Finite.forgetPreservesFiniteLimits _
        let _ : PreservesFiniteLimits
            (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj) :=
          PresheafOfModules.toPresheaf_preservesFiniteLimits _
        let _ : PreservesFiniteLimits
            (SheafOfModules.forget Y.ringCatSheaf ⋙
              PresheafOfModules.toPresheaf Y.ringCatSheaf.obj) :=
          comp_preservesFiniteLimits _ _
        infer_instance
      let _ : PreservesLimit
          (parallelPair g 0 ⋙ (SheafOfModules.forget Y.ringCatSheaf ⋙
            PresheafOfModules.toPresheaf Y.ringCatSheaf.obj))
          ((CategoryTheory.Functor.whiskeringLeft _ _ _).obj
            f.opensFunctor.op) := by
        infer_instance
      exact Limits.comp_preservesLimit
        (SheafOfModules.forget Y.ringCatSheaf ⋙
          PresheafOfModules.toPresheaf Y.ringCatSheaf.obj)
        ((CategoryTheory.Functor.whiskeringLeft _ _ _).obj
          f.opensFunctor.op)
    let _ : PreservesLimit (parallelPair g 0) L :=
      preservesLimit_of_natIso _ e
    apply preservesLimit_of_reflects_of_preserves
      (Scheme.Modules.restrictFunctor f ⋙
        SheafOfModules.forget X.ringCatSheaf)
      (PresheafOfModules.toPresheaf _)
  apply preservesLimit_of_reflects_of_preserves
    (Scheme.Modules.restrictFunctor f) (SheafOfModules.forget _)

/-- Restriction of a global module section along an open immersion, normalized by
the canonical identification between the restricted and source structure sheaves. -/
noncomputable def Scheme.Modules.restrictSection
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (s : M.sections) :
    ((Scheme.Modules.restrictFunctor f).obj M).sections :=
    ((Scheme.Modules.restrictFunctor f).obj M).unitHomEquiv
    ((Scheme.Modules.restrictUnitIso f).inv ≫
      (Scheme.Modules.restrictFunctor f).map (M.unitHomEquiv.symm s))

/-- On the top open of an open subscheme, its `appIso` followed by `topIso` is the
ordinary transport of ambient sections across `U.ι ''ᵁ ⊤ = U`. -/
lemma Scheme.Opens.topIso_hom_appIso_top_hom {X : Scheme.{u}} (U : X.Opens)
    (s : Γ(X, U.ι ''ᵁ (⊤ : U.toScheme.Opens))) :
    U.topIso.hom ((U.ι.appIso ⊤).hom s) =
      X.presheaf.map (eqToHom U.ι_image_top.symm).op s := by
  change U.topIso.hom
    (((X.ofRestrict U.isOpenEmbedding).appIso ⊤).hom s) = _
  rw [Scheme.ofRestrict_appIso]
  rfl

/-- Component formula for restriction of a global module section. -/
lemma Scheme.Modules.restrictSection_apply
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (s : M.sections) (U : X.Opens) :
    (Scheme.Modules.restrictSection f M s).1 (Opposite.op U) =
      s.1 (Opposite.op (f ''ᵁ U)) := by
  change ((f.appIso U).inv (1 : Γ(X, U)) : Γ(Y, f ''ᵁ U)) •
      (show M.val.obj (Opposite.op (f ''ᵁ U)) from
        s.1 (Opposite.op (f ''ᵁ U))) =
      (show M.val.obj (Opposite.op (f ''ᵁ U)) from
        s.1 (Opposite.op (f ''ᵁ U)))
  rw [map_one, one_smul]

/-- Sections of the restriction of a module sheaf are canonically linearly equivalent
to sections of its pullback.  This packages the componentwise form of
`Scheme.Modules.restrictFunctorIsoPullback`. -/
noncomputable def Scheme.Modules.restrictSectionsLinearEquivPullback
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (U : X.Opens) :
    Γ(M.restrict f, U) ≃ₗ[Γ(X, U)] Γ((Scheme.Modules.pullback f).obj M, U) :=
  let e := (Scheme.Modules.restrictFunctorIsoPullback f).app M
  ({ hom := e.hom.val.app (Opposite.op U)
     inv := e.inv.val.app (Opposite.op U)
     hom_inv_id := congrArg (fun k ↦ k.val.app (Opposite.op U)) e.hom_inv_id
     inv_hom_id := congrArg (fun k ↦ k.val.app (Opposite.op U)) e.inv_hom_id } :
    ((M.restrict f).val.obj (Opposite.op U)) ≅
      (((Scheme.Modules.pullback f).obj M).val.obj (Opposite.op U))).toLinearEquiv

/-- Pullback along an open immersion transports finite projectivity from the
corresponding image open. -/
lemma Scheme.Modules.pullback_openImmersion_sections_finite_projective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules) (U : X.Opens)
    (hfin : Module.Finite Γ(Y, f ''ᵁ U) Γ(M, f ''ᵁ U))
    (hproj : Module.Projective Γ(Y, f ''ᵁ U) Γ(M, f ''ᵁ U)) :
    Module.Finite Γ(X, U) Γ((Scheme.Modules.pullback f).obj M, U) ∧
      Module.Projective Γ(X, U) Γ((Scheme.Modules.pullback f).obj M, U) := by
  obtain ⟨hfin', hproj'⟩ :=
    Scheme.Modules.restrict_sections_finite_projective f M U hfin hproj
  let eU := Scheme.Modules.restrictSectionsLinearEquivPullback f M U
  exact ⟨Module.Finite.equiv eU, Module.Projective.of_equiv eU⟩

/-- Pullback along an open immersion transports flatness of sections from the
corresponding image open. -/
lemma Scheme.Modules.pullback_openImmersion_sections_flat
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules) (U : X.Opens)
    [Module.Flat Γ(Y, f ''ᵁ U) Γ(M, f ''ᵁ U)] :
    Module.Flat Γ(X, U) Γ((Scheme.Modules.pullback f).obj M, U) := by
  let hflat : Module.Flat Γ(X, U) Γ(M.restrict f, U) :=
    Scheme.Modules.restrict_sections_flat f M U
  let e := (Scheme.Modules.restrictFunctorIsoPullback f).app M
  let eUCat : ((M.restrict f).val.obj (Opposite.op U)) ≅
      (((Scheme.Modules.pullback f).obj M).val.obj (Opposite.op U)) :=
    { hom := e.hom.val.app (Opposite.op U)
      inv := e.inv.val.app (Opposite.op U)
      hom_inv_id := congrArg (fun k ↦ k.val.app (Opposite.op U)) e.hom_inv_id
      inv_hom_id := congrArg (fun k ↦ k.val.app (Opposite.op U)) e.inv_hom_id }
  exact @Module.Flat.of_linearEquiv _ _ _ _ _ _ _ _ hflat eUCat.toLinearEquiv.symm

/-- Pullback along an open immersion preserves flatness over an arbitrary external
coefficient ring. -/
lemma Scheme.Modules.pullback_openImmersion_sections_flat_restrictScalars
    {R₀ : Type*} [CommRing R₀] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules) (U : X.Opens)
    (a : R₀ →+* Γ(Y, f ''ᵁ U))
    (hflat :
      letI := Module.compHom Γ(M, f ''ᵁ U) a
      Module.Flat R₀ Γ(M, f ''ᵁ U)) :
    letI := Module.compHom Γ((Scheme.Modules.pullback f).obj M, U)
      ((f.appIso U).hom.hom.comp a)
    Module.Flat R₀ Γ((Scheme.Modules.pullback f).obj M, U) := by
  letI : Module R₀ Γ(M.restrict f, U) := Module.compHom Γ(M.restrict f, U)
    ((f.appIso U).hom.hom.comp a)
  let hrestrict : Module.Flat R₀ Γ(M.restrict f, U) :=
    Scheme.Modules.restrict_sections_flat_restrictScalars f M U a hflat
  let N := (Scheme.Modules.pullback f).obj M
  letI : Module R₀ Γ(N, U) := Module.compHom Γ(N, U)
    ((f.appIso U).hom.hom.comp a)
  let E := (Scheme.Modules.restrictFunctorIsoPullback f).app M
  let eCat : ((M.restrict f).val.obj (Opposite.op U)) ≅
      (N.val.obj (Opposite.op U)) :=
    { hom := E.hom.val.app (Opposite.op U)
      inv := E.inv.val.app (Opposite.op U)
      hom_inv_id := congrArg (fun k ↦ k.val.app (Opposite.op U)) E.hom_inv_id
      inv_hom_id := congrArg (fun k ↦ k.val.app (Opposite.op U)) E.inv_hom_id }
  let e : Γ(M.restrict f, U) ≃ₗ[R₀] Γ(N, U) :=
    { toEquiv := eCat.toLinearEquiv.toEquiv
      map_add' := map_add _
      map_smul' := fun r m ↦ by
        change E.hom.val.app (Opposite.op U)
          ((f.appIso U).hom (a r) • m) =
            (f.appIso U).hom (a r) • E.hom.val.app (Opposite.op U) m
        exact _root_.map_smul _ _ _ }
  exact @Module.Flat.of_linearEquiv _ _ _ _ _ _ _ _ hrestrict e.symm

/-- The converse section transport for an open immersion: external flatness after
pullback is equivalent to flatness on the corresponding image open. -/
lemma Scheme.Modules.sections_flat_of_pullback_openImmersion_restrictScalars
    {R₀ : Type*} [CommRing R₀] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules) (U : X.Opens)
    (a : R₀ →+* Γ(Y, f ''ᵁ U))
    (hflat :
      letI := Module.compHom Γ((Scheme.Modules.pullback f).obj M, U)
        ((f.appIso U).hom.hom.comp a)
      Module.Flat R₀ Γ((Scheme.Modules.pullback f).obj M, U)) :
    letI := Module.compHom Γ(M, f ''ᵁ U) a
    Module.Flat R₀ Γ(M, f ''ᵁ U) := by
  let N := (Scheme.Modules.pullback f).obj M
  letI : Module R₀ Γ(N, U) := Module.compHom Γ(N, U)
    ((f.appIso U).hom.hom.comp a)
  letI : Module.Flat R₀ Γ(N, U) := hflat
  let E := (Scheme.Modules.restrictFunctorIsoPullback f).app M
  let eCat : ((M.restrict f).val.obj (Opposite.op U)) ≅
      (N.val.obj (Opposite.op U)) :=
    { hom := E.hom.val.app (Opposite.op U)
      inv := E.inv.val.app (Opposite.op U)
      hom_inv_id := congrArg (fun k ↦ k.val.app (Opposite.op U)) E.hom_inv_id
      inv_hom_id := congrArg (fun k ↦ k.val.app (Opposite.op U)) E.inv_hom_id }
  letI : Module R₀ Γ(M.restrict f, U) := Module.compHom Γ(M.restrict f, U)
    ((f.appIso U).hom.hom.comp a)
  let e : Γ(M.restrict f, U) ≃ₗ[R₀] Γ(N, U) :=
    { toEquiv := eCat.toLinearEquiv.toEquiv
      map_add' := map_add _
      map_smul' := fun r m ↦ by
        change E.hom.val.app (Opposite.op U)
          ((f.appIso U).hom (a r) • m) =
            (f.appIso U).hom (a r) • E.hom.val.app (Opposite.op U) m
        exact _root_.map_smul _ _ _ }
  have hrestrict : Module.Flat R₀ Γ(M.restrict f, U) :=
    @Module.Flat.of_linearEquiv _ _ _ _ _ _ _ _ hflat e
  letI : Module R₀ Γ(M, f ''ᵁ U) := Module.compHom Γ(M, f ''ᵁ U) a
  let eRestrict : Γ(M, f ''ᵁ U) ≃ₗ[R₀] Γ(M.restrict f, U) :=
    { toEquiv :=
        { toFun := (M.restrictAppIso f U).inv
          invFun := (M.restrictAppIso f U).hom
          left_inv := fun m ↦ by simp
          right_inv := fun m ↦ by simp }
      map_add' := map_add _
      map_smul' := fun r m ↦ by
        change (M.restrictAppIso f U).inv (a r • m) =
          (f.appIso U).hom (a r) • (M.restrictAppIso f U).inv m
        simp }
  exact @Module.Flat.of_linearEquiv _ _ _ _ _ _ _ _ hrestrict eRestrict

/-- Push external flatness out through an open immersion, choosing the ambient
coefficient map canonically by the inverse of the section-ring equivalence. -/
lemma Scheme.Modules.sections_flat_of_pullback_openImmersion
    {R₀ : Type*} [CommRing R₀] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules) (U : X.Opens)
    (b : R₀ →+* Γ(X, U))
    (hflat :
      letI := Module.compHom Γ((Scheme.Modules.pullback f).obj M, U) b
      Module.Flat R₀ Γ((Scheme.Modules.pullback f).obj M, U)) :
    let a := (f.appIso U).inv.hom.comp b
    letI := Module.compHom Γ(M, f ''ᵁ U) a
    Module.Flat R₀ Γ(M, f ''ᵁ U) := by
  let a := (f.appIso U).inv.hom.comp b
  have hmap : (f.appIso U).hom.hom.comp a = b := by
    ext r
    simp [a]
  have hflat' :
      letI := Module.compHom Γ((Scheme.Modules.pullback f).obj M, U)
        ((f.appIso U).hom.hom.comp a)
      Module.Flat R₀ Γ((Scheme.Modules.pullback f).obj M, U) :=
    Module.Flat.compHom_congr b ((f.appIso U).hom.hom.comp a) hmap.symm hflat
  exact Scheme.Modules.sections_flat_of_pullback_openImmersion_restrictScalars
    f M U a hflat'

/-- Pullback along an isomorphism preserves flatness over an external coefficient ring,
on global sections. -/
lemma Scheme.Modules.pullback_isIso_sections_flat_restrictScalars
    {R₀ : Type*} [CommRing R₀] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIso f] (M : Y.Modules) (a : R₀ →+* Γ(Y, ⊤))
    (hflat :
      letI := Module.compHom Γ(M, ⊤) a
      Module.Flat R₀ Γ(M, ⊤)) :
    let him : (⊤ : Y.Opens) = f ''ᵁ (⊤ : X.Opens) := by
      rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]
    let a' : R₀ →+* Γ(Y, f ''ᵁ (⊤ : X.Opens)) := him ▸ a
    letI := Module.compHom Γ((Scheme.Modules.pullback f).obj M, ⊤)
      ((f.appIso ⊤).hom.hom.comp a')
    Module.Flat R₀ Γ((Scheme.Modules.pullback f).obj M, ⊤) := by
  letI : IsOpenImmersion f := inferInstance
  have him : (⊤ : Y.Opens) = f ''ᵁ (⊤ : X.Opens) := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]
  let a' : R₀ →+* Γ(Y, f ''ᵁ (⊤ : X.Opens)) := him ▸ a
  have hflat' :
      letI := Module.compHom Γ(M, f ''ᵁ (⊤ : X.Opens)) a'
      Module.Flat R₀ Γ(M, f ''ᵁ (⊤ : X.Opens)) :=
    Scheme.Modules.sections_flat_of_eq M ⊤ (f ''ᵁ ⊤) him a hflat
  exact Scheme.Modules.pullback_openImmersion_sections_flat_restrictScalars
    f M ⊤ a' hflat'

/-- For an isomorphism, the global-sections map obtained from its open-immersion
`appIso` agrees with `appTop`. -/
noncomputable def Scheme.Hom.appIsoTopHom
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] : Γ(Y, ⊤) →+* Γ(X, ⊤) :=
  letI : IsOpenImmersion f := inferInstance
  let h : f ''ᵁ (⊤ : X.Opens) = (⊤ : Y.Opens) := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]
  (f.appIso ⊤).hom.hom.comp
    (Y.presheaf.map (eqToHom h).op).hom

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
lemma Scheme.Hom.appIsoTopHom_eq_appTop
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    CommRingCat.ofHom f.appIsoTopHom = f.appTop := by
  dsimp [Scheme.Hom.appIsoTopHom]
  rw [Scheme.Hom.appIso_hom, ← Category.assoc, Scheme.Hom.naturality, Category.assoc,
    ← Functor.map_comp]
  rw [show X.presheaf.map _ = 𝟙 _ by
    rw [← X.presheaf.map_id]
    exact congrArg X.presheaf.map (Subsingleton.elim _ _)]
  simp
set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- Restricting a global section of the unit sheaf along an isomorphism and then
identifying the restricted unit sheaf with the source unit sheaf applies the usual
`appTop` map to its top component. -/
lemma Scheme.Modules.sectionsMap_restrictUnitIso_restrictSection_appTop
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (s : (SheafOfModules.unit Y.ringCatSheaf).sections) :
    (SheafOfModules.sectionsMap (restrictUnitIso f).hom
      (restrictSection f (SheafOfModules.unit Y.ringCatSheaf) s)).1
        (Opposite.op ⊤) = f.appTop.hom (s.1 (Opposite.op ⊤)) := by
  letI : IsOpenImmersion f := inferInstance
  rw [← congrArg CommRingCat.Hom.hom (f.appIsoTopHom_eq_appTop)]
  change (f.appIso ⊤).hom
      ((restrictSection f (SheafOfModules.unit Y.ringCatSheaf) s).1
        (Opposite.op ⊤)) = f.appIsoTopHom (s.1 (Opposite.op ⊤))
  rw [restrictSection_apply]
  let h : f ''ᵁ (⊤ : X.Opens) = (⊤ : Y.Opens) := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]
  change (f.appIso ⊤).hom (s.1 (Opposite.op (f ''ᵁ ⊤))) =
    (f.appIso ⊤).hom
      ((Y.presheaf.map (eqToHom h).op).hom (s.1 (Opposite.op ⊤)))
  exact congrArg (f.appIso ⊤).hom
    (s.property (eqToHom h).op).symm

/-- `pullback_isIso_sections_flat_restrictScalars`, expressed with the ordinary
`appTop` map on coefficient rings. -/
lemma Scheme.Modules.pullback_isIso_sections_flat_restrictScalars_appTop
    {R₀ : Type*} [CommRing R₀] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIso f] (M : Y.Modules) (a : R₀ →+* Γ(Y, ⊤))
    (hflat :
      letI := Module.compHom Γ(M, ⊤) a
      Module.Flat R₀ Γ(M, ⊤)) :
    letI := Module.compHom Γ((Scheme.Modules.pullback f).obj M, ⊤)
      (f.appTop.hom.comp a)
    Module.Flat R₀ Γ((Scheme.Modules.pullback f).obj M, ⊤) := by
  letI : IsOpenImmersion f := inferInstance
  have him : (⊤ : Y.Opens) = f ''ᵁ (⊤ : X.Opens) := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]
  let a' : R₀ →+* Γ(Y, f ''ᵁ (⊤ : X.Opens)) := him ▸ a
  let c : R₀ →+* Γ(X, ⊤) := (f.appIso ⊤).hom.hom.comp a'
  have hc : c = f.appTop.hom.comp a := by
    rw [← congrArg CommRingCat.Hom.hom (f.appIsoTopHom_eq_appTop)]
    ext r
    apply congrArg (f.appIso ⊤).hom.hom
    rw [show a' r = him ▸ a r from
      Scheme.ringHom_transport_apply _ _ him a r]
    exact (Scheme.presheafMap_eq_transport (⊤ : Y.Opens)
      (f ''ᵁ (⊤ : X.Opens)) him (a r)).symm
  have hpull :
      letI := Module.compHom Γ((Scheme.Modules.pullback f).obj M, ⊤) c
      Module.Flat R₀ Γ((Scheme.Modules.pullback f).obj M, ⊤) :=
    Scheme.Modules.pullback_isIso_sections_flat_restrictScalars f M a hflat
  exact Module.Flat.compHom_congr c (f.appTop.hom.comp a) hc hpull

/-- On an affine scheme, external flatness of intrinsic global sections becomes
external flatness in the `moduleSpecΓFunctor` convention after transport by
`isoSpec.inv`. -/
lemma Scheme.Modules.moduleSpecΓFunctor_pullback_isoSpec_inv_flat_restrictScalars
    {R₀ : Type*} [CommRing R₀] {X : Scheme.{u}} [IsAffine X]
    (M : X.Modules) (a : R₀ →+* Γ(X, ⊤))
    (hflat :
      letI := Module.compHom Γ(M, ⊤) a
      Module.Flat R₀ Γ(M, ⊤)) :
    let Mspec := (Scheme.Modules.pullback X.isoSpec.inv).obj M
    letI := Module.compHom (moduleSpecΓFunctor.obj Mspec) a
    Module.Flat R₀ (moduleSpecΓFunctor.obj Mspec) := by
  let Mspec := (Scheme.Modules.pullback X.isoSpec.inv).obj M
  have hi : X.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(X, ⊤)).inv := by
    rw [← cancel_mono X.isoSpec.hom.appTop, ← Scheme.Hom.comp_appTop]
    simp [Scheme.isoSpec]
  have htop :
      letI := Module.compHom Γ(Mspec, ⊤)
        ((Scheme.ΓSpecIso Γ(X, ⊤)).inv.hom.comp a)
      Module.Flat R₀ Γ(Mspec, ⊤) := by
    rw [← hi]
    exact Scheme.Modules.pullback_isIso_sections_flat_restrictScalars_appTop
      X.isoSpec.inv M a hflat
  letI : Module R₀ Γ(Mspec, ⊤) := Module.compHom Γ(Mspec, ⊤)
    ((Scheme.ΓSpecIso Γ(X, ⊤)).inv.hom.comp a)
  letI : Module.Flat R₀ Γ(Mspec, ⊤) := htop
  exact moduleSpecΓFunctor_flat_of_top_restrictScalars Mspec a
    (fun _ _ ↦ rfl)

/-- On an arbitrary affine scheme, after passing to its canonical spectrum chart,
external flatness of global sections remains flat on every basic open. -/
lemma Scheme.Modules.pullback_isoSpec_inv_flat_sections_basicOpen
    {R₀ : Type*} [CommRing R₀] {X : Scheme.{u}} [IsAffine X]
    (M : X.Modules) [M.IsQuasicoherent] (a : R₀ →+* Γ(X, ⊤))
    (hflat :
      letI := Module.compHom Γ(M, ⊤) a
      Module.Flat R₀ Γ(M, ⊤)) (r : Γ(X, ⊤)) :
    let Mspec := (Scheme.Modules.pullback X.isoSpec.inv).obj M
    letI := Module.compHom Γ(Mspec, PrimeSpectrum.basicOpen r) a
    Module.Flat R₀ Γ(Mspec, PrimeSpectrum.basicOpen r) := by
  let Mspec := (Scheme.Modules.pullback X.isoSpec.inv).obj M
  letI : Mspec.IsQuasicoherent := by
    letI : IsOpenImmersion X.isoSpec.inv := inferInstance
    let e := (Scheme.Modules.restrictFunctorIsoPullback X.isoSpec.inv).app M
    exact (SheafOfModules.isQuasicoherent (Spec Γ(X, ⊤)).ringCatSheaf).prop_of_iso
      e inferInstance
  letI : Algebra R₀ Γ(X, ⊤) := a.toAlgebra
  have htopModule :
      letI := Module.compHom (moduleSpecΓFunctor.obj Mspec) a
      Module.Flat R₀ (moduleSpecΓFunctor.obj Mspec) :=
    Scheme.Modules.moduleSpecΓFunctor_pullback_isoSpec_inv_flat_restrictScalars
      M a hflat
  have htop :
      letI := Module.compHom Γ(Mspec, ⊤) a
      Module.Flat R₀ Γ(Mspec, ⊤) := htopModule
  exact Scheme.Modules.flat_sections_basicOpen_of_top Mspec r htop

/-- The map from the coordinate ring of an affine scheme to sections on an open of
its canonical spectrum is the `appLE` map of `isoSpec.inv`. -/
lemma Scheme.isoSpec_inv_appLE_eq_algebraMap
    {X : Scheme.{u}} [IsAffine X] (U : (Spec Γ(X, ⊤)).Opens) :
    (X.isoSpec.inv.appLE ⊤ U le_top).hom = algebraMap Γ(X, ⊤) Γ(Spec Γ(X, ⊤), U) := by
  have hi : X.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(X, ⊤)).inv := by
    rw [← cancel_mono X.isoSpec.hom.appTop, ← Scheme.Hom.comp_appTop]
    simp [Scheme.isoSpec]
  ext r
  simp [Scheme.Hom.appLE, hi]

/-- Restriction from an affine open's section ring to an open of its canonical
spectrum is the `appLE` map of `fromSpec`. -/
lemma IsAffineOpen.fromSpec_appLE_eq_algebraMap
    {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (V : (Spec Γ(X, U)).Opens) :
    (hU.fromSpec.appLE U V (by simp)).hom = algebraMap Γ(X, U) Γ(Spec Γ(X, U), V) := by
  ext r
  simp [Scheme.Hom.appLE, hU.fromSpec_app_self, ← Functor.map_comp]

/-- Conversely, external flatness in the `moduleSpecΓFunctor` convention after
transport by `isoSpec.inv` implies external flatness of the original intrinsic global
sections. -/
lemma Scheme.Modules.flat_sections_of_moduleSpecΓFunctor_pullback_isoSpec_inv
    {R₀ : Type*} [CommRing R₀] {X : Scheme.{u}} [IsAffine X]
    (M : X.Modules) (a : R₀ →+* Γ(X, ⊤))
    (hflat :
      let Mspec := (Scheme.Modules.pullback X.isoSpec.inv).obj M
      letI := Module.compHom (moduleSpecΓFunctor.obj Mspec) a
      Module.Flat R₀ (moduleSpecΓFunctor.obj Mspec)) :
    letI := Module.compHom Γ(M, ⊤) a
    Module.Flat R₀ Γ(M, ⊤) := by
  let Mspec := (Scheme.Modules.pullback X.isoSpec.inv).obj M
  letI : Module R₀ (moduleSpecΓFunctor.obj Mspec) :=
    Module.compHom (moduleSpecΓFunctor.obj Mspec) a
  letI : Module.Flat R₀ (moduleSpecΓFunctor.obj Mspec) := hflat
  let b : R₀ →+* Γ(Spec Γ(X, ⊤), ⊤) :=
    (Scheme.ΓSpecIso Γ(X, ⊤)).inv.hom.comp a
  letI : Module R₀ Γ(Mspec, ⊤) := Module.compHom Γ(Mspec, ⊤) b
  letI : Module.Flat R₀ Γ(Mspec, ⊤) :=
    moduleSpecΓFunctor_flat_to_top_restrictScalars Mspec a (fun _ _ ↦ rfl)
  let N := (Scheme.Modules.pullback X.isoSpec.hom).obj Mspec
  let c : R₀ →+* Γ(X, ⊤) := X.isoSpec.hom.appTop.hom.comp b
  have hpull :
      letI := Module.compHom Γ(N, ⊤) c
      Module.Flat R₀ Γ(N, ⊤) :=
    Scheme.Modules.pullback_isIso_sections_flat_restrictScalars_appTop
      X.isoSpec.hom Mspec b inferInstance
  have hi : X.isoSpec.hom.appTop = (Scheme.ΓSpecIso Γ(X, ⊤)).hom := by
    simp [Scheme.isoSpec]
  have hc : c = a := by
    ext r
    simp [c, b, hi]
  have hN :
      letI := Module.compHom Γ(N, ⊤) a
      Module.Flat R₀ Γ(N, ⊤) :=
    Module.Flat.compHom_congr c a hc hpull
  let eBack : N ≅ M :=
    (Scheme.Modules.pullbackComp X.isoSpec.hom X.isoSpec.inv).app M ≪≫
      (Scheme.Modules.pullbackCongr X.isoSpec.hom_inv_id).app M ≪≫
      (Scheme.Modules.pullbackId _).app M
  exact Scheme.Modules.sections_flat_of_iso_restrictScalars eBack ⊤ a hN

/-- Pulling a module sheaf from an affine scheme to its canonical spectrum and back
is naturally isomorphic to the original sheaf. -/
noncomputable def Scheme.Modules.pullbackIsoSpecInvHomIso
    (X : Scheme.{u}) [IsAffine X] :
    pullback X.isoSpec.inv ⋙ pullback X.isoSpec.hom ≅ 𝟭 X.Modules :=
  pullbackComp X.isoSpec.hom X.isoSpec.inv ≪≫
    pullbackCongr X.isoSpec.hom_inv_id ≪≫ pullbackId X

/-- Restricting a module sheaf along an open immersion transports finite projectivity
and constant rank from the corresponding image open.  This is the section-level form
used to pass between affine opens and their open subschemes. -/
lemma Scheme.Modules.restrict_sections_finite_projective_rank
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules) (U : X.Opens)
    {q : ℕ}
    (hfin : Module.Finite Γ(Y, f ''ᵁ U) Γ(M, f ''ᵁ U))
    (hproj : Module.Projective Γ(Y, f ''ᵁ U) Γ(M, f ''ᵁ U))
    (hrank : ∀ p : PrimeSpectrum Γ(Y, f ''ᵁ U),
      Module.rankAtStalk Γ(M, f ''ᵁ U) p = q) :
    Module.Finite Γ(X, U) Γ(M.restrict f, U) ∧
      Module.Projective Γ(X, U) Γ(M.restrict f, U) ∧
      ∀ p : PrimeSpectrum Γ(X, U), Module.rankAtStalk Γ(M.restrict f, U) p = q := by
  let eR := (f.appIso U).commRingCatIsoToRingEquiv
  letI : Algebra Γ(Y, f ''ᵁ U) Γ(X, U) := eR.toRingHom.toAlgebra
  letI : RingHomInvPair (eR : Γ(Y, f ''ᵁ U) →+* Γ(X, U))
      (eR.symm : Γ(X, U) →+* Γ(Y, f ''ᵁ U)) := RingHomInvPair.of_ringEquiv eR
  letI : RingHomInvPair (eR.symm : Γ(X, U) →+* Γ(Y, f ''ᵁ U))
      (eR : Γ(Y, f ''ᵁ U) →+* Γ(X, U)) := ⟨by ext; simp, by ext; simp⟩
  let eM : Γ(M, f ''ᵁ U) ≃ₛₗ[(eR : Γ(Y, f ''ᵁ U) →+* Γ(X, U))]
      Γ(M.restrict f, U) :=
    { toEquiv :=
        { toFun := (M.restrictAppIso f U).inv
          invFun := (M.restrictAppIso f U).hom
          left_inv := fun m => by simp
          right_inv := fun m => by simp }
      map_add' := fun _ _ => map_add _ _ _
      map_smul' := fun r m => by
        change (M.restrictAppIso f U).inv (r • m) =
          (f.appIso U).hom r • (M.restrictAppIso f U).inv m
        simp }
  exact Module.finite_projective_rankAtStalk_of_semilinearEquiv eR rfl eM
    hfin hproj hrank

/-- Pullback along an open immersion transports finite projectivity and constant rank
from the image open to the corresponding source open. -/
lemma Scheme.Modules.pullback_openImmersion_sections_finite_projective_rank
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules) (U : X.Opens)
    {q : ℕ}
    (hfin : Module.Finite Γ(Y, f ''ᵁ U) Γ(M, f ''ᵁ U))
    (hproj : Module.Projective Γ(Y, f ''ᵁ U) Γ(M, f ''ᵁ U))
    (hrank : ∀ p : PrimeSpectrum Γ(Y, f ''ᵁ U),
      Module.rankAtStalk Γ(M, f ''ᵁ U) p = q) :
    Module.Finite Γ(X, U) Γ((Scheme.Modules.pullback f).obj M, U) ∧
      Module.Projective Γ(X, U) Γ((Scheme.Modules.pullback f).obj M, U) ∧
      ∀ p : PrimeSpectrum Γ(X, U),
        Module.rankAtStalk Γ((Scheme.Modules.pullback f).obj M, U) p = q := by
  obtain ⟨hfin', hproj', hrank'⟩ :=
    Scheme.Modules.restrict_sections_finite_projective_rank f M U hfin hproj hrank
  let e := (Scheme.Modules.restrictFunctorIsoPullback f).app M
  let eUCat : ((M.restrict f).val.obj (Opposite.op U)) ≅
      (((Scheme.Modules.pullback f).obj M).val.obj (Opposite.op U)) :=
    { hom := e.hom.val.app (Opposite.op U)
      inv := e.inv.val.app (Opposite.op U)
      hom_inv_id := congrArg (fun k ↦ k.val.app (Opposite.op U)) e.hom_inv_id
      inv_hom_id := congrArg (fun k ↦ k.val.app (Opposite.op U)) e.inv_hom_id }
  let eU : Γ(M.restrict f, U) ≃ₗ[Γ(X, U)]
      Γ((Scheme.Modules.pullback f).obj M, U) := eUCat.toLinearEquiv
  refine ⟨@Module.Finite.equiv Γ(X, U) _ _ _ _ _ _ _ hfin' eU,
    @Module.Projective.of_equiv _ _ _ _ _ _ _ _ _ _ _ _ _ _ eU hproj', ?_⟩
  intro p
  exact (congrFun (Module.rankAtStalk_eq_of_equiv eU) p).symm.trans (hrank' p)

/-- For an open immersion, finite projectivity and constant rank of sections can also be
transported back from the pulled-back sheaf to the corresponding image open. -/
lemma Scheme.Modules.sections_finite_projective_rank_of_pullback_openImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules) (U : X.Opens)
    {q : ℕ}
    (hfin : Module.Finite Γ(X, U) Γ((Scheme.Modules.pullback f).obj M, U))
    (hproj : Module.Projective Γ(X, U) Γ((Scheme.Modules.pullback f).obj M, U))
    (hrank : ∀ p : PrimeSpectrum Γ(X, U),
      Module.rankAtStalk Γ((Scheme.Modules.pullback f).obj M, U) p = q) :
    Module.Finite Γ(Y, f ''ᵁ U) Γ(M, f ''ᵁ U) ∧
      Module.Projective Γ(Y, f ''ᵁ U) Γ(M, f ''ᵁ U) ∧
      ∀ p : PrimeSpectrum Γ(Y, f ''ᵁ U),
        Module.rankAtStalk Γ(M, f ''ᵁ U) p = q := by
  let e := (Scheme.Modules.restrictFunctorIsoPullback f).app M
  let eUCat : ((M.restrict f).val.obj (Opposite.op U)) ≅
      (((Scheme.Modules.pullback f).obj M).val.obj (Opposite.op U)) :=
    { hom := e.hom.val.app (Opposite.op U)
      inv := e.inv.val.app (Opposite.op U)
      hom_inv_id := congrArg (fun k ↦ k.val.app (Opposite.op U)) e.hom_inv_id
      inv_hom_id := congrArg (fun k ↦ k.val.app (Opposite.op U)) e.inv_hom_id }
  let eU : Γ(M.restrict f, U) ≃ₗ[Γ(X, U)]
      Γ((Scheme.Modules.pullback f).obj M, U) := eUCat.toLinearEquiv
  have hfin' : Module.Finite Γ(X, U) Γ(M.restrict f, U) :=
    @Module.Finite.equiv Γ(X, U) _ _ _ _ _ _ _ hfin eU.symm
  have hproj' : Module.Projective Γ(X, U) Γ(M.restrict f, U) :=
    @Module.Projective.of_equiv _ _ _ _ _ _ _ _ _ _ _ _ _ _ eU.symm hproj
  have hrank' : ∀ p : PrimeSpectrum Γ(X, U),
      Module.rankAtStalk Γ(M.restrict f, U) p = q := fun p ↦
    (congrFun (Module.rankAtStalk_eq_of_equiv eU) p).trans (hrank p)
  let eR := (f.appIso U).symm.commRingCatIsoToRingEquiv
  letI : Algebra Γ(X, U) Γ(Y, f ''ᵁ U) := eR.toRingHom.toAlgebra
  letI : RingHomInvPair (eR : Γ(X, U) →+* Γ(Y, f ''ᵁ U))
      (eR.symm : Γ(Y, f ''ᵁ U) →+* Γ(X, U)) := RingHomInvPair.of_ringEquiv eR
  letI : RingHomInvPair (eR.symm : Γ(Y, f ''ᵁ U) →+* Γ(X, U))
      (eR : Γ(X, U) →+* Γ(Y, f ''ᵁ U)) := ⟨by ext; simp, by ext; simp⟩
  let eM : Γ(M.restrict f, U) ≃ₛₗ[(eR : Γ(X, U) →+* Γ(Y, f ''ᵁ U))]
      Γ(M, f ''ᵁ U) :=
    { toEquiv :=
        { toFun := (M.restrictAppIso f U).hom
          invFun := (M.restrictAppIso f U).inv
          left_inv := fun m => by simp
          right_inv := fun m => by simp }
      map_add' := fun _ _ => map_add _ _ _
      map_smul' := fun r m => by
        change (M.restrictAppIso f U).hom (r • m) =
          (f.appIso U).inv r • (M.restrictAppIso f U).hom m
        simp }
  exact Module.finite_projective_rankAtStalk_of_semilinearEquiv eR rfl eM
    hfin' hproj' hrank'

/-- Global sections of the pushforward along `Spec.map φ` are the restriction of
scalars of the global sections. -/
noncomputable def pushforwardCompModuleSpecΓFunctorIso :
    Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor ≅
      moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars φ.hom :=
  Functor.isoWhiskerRight (pushforwardCompModulesSpecToSheafIso φ)
    (TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (.op ⊤))

/-- **Pullback of quasi-coherent modules over affines is base change**: the pullback of
the tilde of a module along `Spec.map φ` is the tilde of its extension of scalars
(uniqueness of left adjoints). -/
noncomputable def tildeCompPullbackIso :
    tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map φ) ≅
      ModuleCat.extendScalars φ.hom ⋙ tilde.functor S :=
  Adjunction.leftAdjointCompIso tilde.adjunction
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))
    ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp tilde.adjunction)
    (pushforwardCompModuleSpecΓFunctorIso φ)

/-- Pullback of an arbitrary quasicoherent module on an affine scheme is the tilde of
the scalar extension of its global-sections module. -/
noncomputable def pullbackQuasicoherentIso (M : (Spec R).Modules)
    [M.IsQuasicoherent] :
    (Scheme.Modules.pullback (Spec.map φ)).obj M ≅
      tilde (ModuleCat.extendScalars φ.hom |>.obj (moduleSpecΓFunctor.obj M)) := by
  letI : IsIso M.fromTildeΓ :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  exact ((Scheme.Modules.pullback (Spec.map φ)).mapIso (asIso M.fromTildeΓ)).symm ≪≫
    (tildeCompPullbackIso φ).app (moduleSpecΓFunctor.obj M)

set_option backward.isDefEq.respectTransparency.types false in
/-- The affine pullback/base-change comparison for quasicoherent modules is natural in
the module sheaf. -/
lemma pullbackQuasicoherentIso_naturality
    {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) :
    (Scheme.Modules.pullback (Spec.map φ)).map f ≫
        (pullbackQuasicoherentIso φ N).hom =
      (pullbackQuasicoherentIso φ M).hom ≫
        (tilde.functor S).map
          ((ModuleCat.extendScalars φ.hom).map (moduleSpecΓFunctor.map f)) := by
  let η := Scheme.Modules.fromTildeΓNatTrans (R := R)
  let _ : IsIso (η.app M) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  let _ : IsIso (η.app N) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent N
  have hf : f ≫ inv (η.app N) =
      inv (η.app M) ≫ (moduleSpecΓFunctor (R := R) ⋙ tilde.functor R).map f := by
    rw [← cancel_mono (η.app N)]
    simp only [Category.assoc]
    rw [η.naturality]
    simp
  change (Scheme.Modules.pullback (Spec.map φ)).map f ≫
        (Scheme.Modules.pullback (Spec.map φ)).map (inv (η.app N)) ≫
          (tildeCompPullbackIso φ).hom.app (moduleSpecΓFunctor.obj N) =
      (Scheme.Modules.pullback (Spec.map φ)).map (inv (η.app M)) ≫
        (tildeCompPullbackIso φ).hom.app (moduleSpecΓFunctor.obj M) ≫
          (tilde.functor S).map
            ((ModuleCat.extendScalars φ.hom).map (moduleSpecΓFunctor.map f))
  rw [← Category.assoc, ← Functor.map_comp, hf, Functor.map_comp]
  simp only [Functor.comp_obj, Functor.comp_map, Category.assoc]
  change (Scheme.Modules.pullback (Spec.map φ)).map (inv (η.app M)) ≫
      (((tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map φ)).map
          (moduleSpecΓFunctor.map f)) ≫
        (tildeCompPullbackIso φ).hom.app (moduleSpecΓFunctor.obj N)) =
    (Scheme.Modules.pullback (Spec.map φ)).map (inv (η.app M)) ≫
      ((tildeCompPullbackIso φ).hom.app (moduleSpecΓFunctor.obj M) ≫
        (ModuleCat.extendScalars φ.hom ⋙ tilde.functor S).map
          (moduleSpecΓFunctor.map f))
  rw [(tildeCompPullbackIso φ).hom.naturality]

/-- On global sections, affine pullback of a quasicoherent module is extension of
scalars, as an isomorphism in `ModuleCat`. -/
noncomputable def pullbackQuasicoherentSectionsIso (M : (Spec R).Modules)
    [M.IsQuasicoherent] :
    moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (Spec.map φ)).obj M) ≅
      ModuleCat.extendScalars φ.hom |>.obj (moduleSpecΓFunctor.obj M) :=
  moduleSpecΓFunctor.mapIso (pullbackQuasicoherentIso φ M) ≪≫
    (tilde.toTildeΓNatIso.app
      (ModuleCat.extendScalars φ.hom |>.obj (moduleSpecΓFunctor.obj M))).symm

/-- On global sections, affine pullback of a quasicoherent module is extension of
scalars, as a linear equivalence. -/
noncomputable def pullbackQuasicoherentSectionsLinearEquiv (M : (Spec R).Modules)
    [M.IsQuasicoherent] :
    moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (Spec.map φ)).obj M) ≃ₗ[S]
      ModuleCat.extendScalars φ.hom |>.obj (moduleSpecΓFunctor.obj M) :=
  (pullbackQuasicoherentSectionsIso φ M).toLinearEquiv

set_option backward.isDefEq.respectTransparency.types false in
/-- The global-sections affine pullback/base-change equivalence is natural in the
quasicoherent module sheaf. -/
lemma pullbackQuasicoherentSectionsLinearEquiv_naturality
    {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) :
    (pullbackQuasicoherentSectionsLinearEquiv φ N).toLinearMap.comp
        (moduleSpecΓFunctor.map
          ((Scheme.Modules.pullback (Spec.map φ)).map f)).hom =
      ((ModuleCat.extendScalars φ.hom).map
        (moduleSpecΓFunctor.map f)).hom.comp
          (pullbackQuasicoherentSectionsLinearEquiv φ M).toLinearMap := by
  have h := congrArg (fun k ↦ moduleSpecΓFunctor.map k)
    (pullbackQuasicoherentIso_naturality φ f)
  let g := (ModuleCat.extendScalars φ.hom).map (moduleSpecΓFunctor.map f)
  change moduleSpecΓFunctor.map
        ((Scheme.Modules.pullback (Spec.map φ)).map f) ≫
      moduleSpecΓFunctor.map (pullbackQuasicoherentIso φ N).hom =
    moduleSpecΓFunctor.map (pullbackQuasicoherentIso φ M).hom ≫
      (tilde.functor S ⋙ moduleSpecΓFunctor).map g at h
  let t := tilde.toTildeΓNatIso (R := S)
  have h' : moduleSpecΓFunctor.map
        ((Scheme.Modules.pullback (Spec.map φ)).map f) ≫
        (moduleSpecΓFunctor.map (pullbackQuasicoherentIso φ N).hom ≫
          t.inv.app ((ModuleCat.extendScalars φ.hom).obj
            (moduleSpecΓFunctor.obj N))) =
      (moduleSpecΓFunctor.map (pullbackQuasicoherentIso φ M).hom ≫
          t.inv.app ((ModuleCat.extendScalars φ.hom).obj
            (moduleSpecΓFunctor.obj M))) ≫ g := by
    calc
      _ = (moduleSpecΓFunctor.map
            ((Scheme.Modules.pullback (Spec.map φ)).map f) ≫
          moduleSpecΓFunctor.map (pullbackQuasicoherentIso φ N).hom) ≫
            t.inv.app ((ModuleCat.extendScalars φ.hom).obj
              (moduleSpecΓFunctor.obj N)) := (Category.assoc _ _ _).symm
      _ = (moduleSpecΓFunctor.map (pullbackQuasicoherentIso φ M).hom ≫
          (tilde.functor S ⋙ moduleSpecΓFunctor).map g) ≫
            t.inv.app ((ModuleCat.extendScalars φ.hom).obj
              (moduleSpecΓFunctor.obj N)) := by
            exact congrArg
              (fun k ↦ k ≫ t.inv.app ((ModuleCat.extendScalars φ.hom).obj
                (moduleSpecΓFunctor.obj N))) h
      _ = moduleSpecΓFunctor.map (pullbackQuasicoherentIso φ M).hom ≫
          ((tilde.functor S ⋙ moduleSpecΓFunctor).map g ≫
            t.inv.app ((ModuleCat.extendScalars φ.hom).obj
              (moduleSpecΓFunctor.obj N))) := Category.assoc _ _ _
      _ = moduleSpecΓFunctor.map (pullbackQuasicoherentIso φ M).hom ≫
          (t.inv.app ((ModuleCat.extendScalars φ.hom).obj
              (moduleSpecΓFunctor.obj M)) ≫ g) := by
            exact congrArg
              (fun k ↦ moduleSpecΓFunctor.map
                (pullbackQuasicoherentIso φ M).hom ≫ k)
              (t.inv.naturality g)
      _ = _ := (Category.assoc _ _ _).symm
  change (moduleSpecΓFunctor.map
        ((Scheme.Modules.pullback (Spec.map φ)).map f) ≫
      (moduleSpecΓFunctor.map (pullbackQuasicoherentIso φ N).hom ≫
        t.inv.app ((ModuleCat.extendScalars φ.hom).obj
          (moduleSpecΓFunctor.obj N)))).hom =
    ((moduleSpecΓFunctor.map (pullbackQuasicoherentIso φ M).hom ≫
        t.inv.app ((ModuleCat.extendScalars φ.hom).obj
          (moduleSpecΓFunctor.obj M))) ≫ g).hom
  exact congrArg ModuleCat.Hom.hom h'

set_option backward.isDefEq.respectTransparency.types false in
/-- The global-sections affine pullback/base-change isomorphism is natural as a
morphism equality in `ModuleCat`. -/
lemma pullbackQuasicoherentSectionsIso_naturality
    {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) :
    moduleSpecΓFunctor.map ((Scheme.Modules.pullback (Spec.map φ)).map f) ≫
        (pullbackQuasicoherentSectionsIso φ N).hom =
      (pullbackQuasicoherentSectionsIso φ M).hom ≫
        (ModuleCat.extendScalars φ.hom).map (moduleSpecΓFunctor.map f) := by
  apply ModuleCat.hom_ext
  exact pullbackQuasicoherentSectionsLinearEquiv_naturality φ f

/-- Global sections of the canonical free sheaf after affine pullback, compared with
extension of scalars of its original global sections. -/
noncomputable def freePullbackSectionsIso (I : Type u) :
    moduleSpecΓFunctor.obj
        (SheafOfModules.free (R := (Spec S).ringCatSheaf) I) ≅
      (ModuleCat.extendScalars φ.hom).obj
        (moduleSpecΓFunctor.obj
          (SheafOfModules.free (R := (Spec R).ringCatSheaf) I)) :=
  moduleSpecΓFunctor.mapIso
      (Scheme.Modules.pullbackFreeIso (Spec.map φ) I).symm ≪≫
    pullbackQuasicoherentSectionsIso φ _

set_option backward.isDefEq.respectTransparency.types false in
/-- Global sections of the structure sheaf after affine pullback, compared with
extension of scalars of its original global sections. -/
noncomputable def unitPullbackSectionsIso :
    moduleSpecΓFunctor.obj (SheafOfModules.unit (Spec S).ringCatSheaf) ≅
      (ModuleCat.extendScalars φ.hom).obj
        (moduleSpecΓFunctor.obj
          (SheafOfModules.unit (Spec R).ringCatSheaf)) := by
  letI : (SheafOfModules.unit (Spec R).ringCatSheaf).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
      (tildeSelf (R := R)) inferInstance
  haveI : IsIso (SheafOfModules.pullbackObjUnitToUnit
      (Spec.map φ).toRingCatSheafHom) := inferInstance
  exact moduleSpecΓFunctor.mapIso
      (asIso (SheafOfModules.pullbackObjUnitToUnit
        (Spec.map φ).toRingCatSheafHom)).symm ≪≫
    pullbackQuasicoherentSectionsIso φ _

private lemma map_iso_inv_comp_naturality {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B M N : C} {X Y : D} (u : A ≅ B) (v : M ≅ N)
    (i : B ⟶ N) (p : A ⟶ M) (h : i ≫ v.inv = u.inv ≫ p)
    (a : F.obj M ⟶ X) (b : F.obj A ⟶ Y) (g : Y ⟶ X)
    (hn : F.map p ≫ a = b ≫ g) :
    F.map i ≫ (F.map v.inv ≫ a) = (F.map u.inv ≫ b) ≫ g := by
  rw [← Category.assoc, ← F.map_comp, h, F.map_comp, Category.assoc, hn,
    ← Category.assoc]

private lemma iso_inv_comp_eq_iso_inv_comp_of_comp_eq {C : Type*} [Category C]
    {A B D E : C} (u : A ≅ B) (v : D ≅ E) (p : A ⟶ D) (i : B ⟶ E)
    (h : p ≫ v.hom = u.hom ≫ i) : i ≫ v.inv = u.inv ≫ p := by
  rw [← cancel_epi u.hom]
  rw [Iso.hom_inv_id_assoc]
  calc
    u.hom ≫ (i ≫ v.inv) = (u.hom ≫ i) ≫ v.inv := Category.assoc _ _ _ |>.symm
    _ = (p ≫ v.hom) ≫ v.inv := congrArg (fun k ↦ k ≫ v.inv) h.symm
    _ = p := by simp

set_option backward.isDefEq.respectTransparency.types false in
/-- The free affine pullback comparison is compatible with every canonical generator.
The rank-one comparison is independent of the generator, so this square is the key
diagonal form of the free-source base-change isomorphism. -/
lemma map_ιFree_comp_freePullbackSectionsIso_hom (I : Type u) (i : I) :
    moduleSpecΓFunctor.map (SheafOfModules.ιFree i) ≫
        (freePullbackSectionsIso φ I).hom =
      (unitPullbackSectionsIso φ).hom ≫
        (ModuleCat.extendScalars φ.hom).map
          (moduleSpecΓFunctor.map (SheafOfModules.ιFree i)) := by
  let _ : (SheafOfModules.unit (Spec R).ringCatSheaf).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
      (tildeSelf (R := R)) inferInstance
  let _ : IsIso (SheafOfModules.pullbackObjUnitToUnit
      (Spec.map φ).toRingCatSheafHom) := inferInstance
  let eU := asIso (SheafOfModules.pullbackObjUnitToUnit
    (Spec.map φ).toRingCatSheafHom)
  let eF := Scheme.Modules.pullbackFreeIso (Spec.map φ) I
  have hs : SheafOfModules.ιFree i ≫ eF.inv =
      eU.inv ≫ (Scheme.Modules.pullback (Spec.map φ)).map
        (SheafOfModules.ιFree i) := by
    apply iso_inv_comp_eq_iso_inv_comp_of_comp_eq
    exact SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom _ i
  dsimp only [freePullbackSectionsIso, unitPullbackSectionsIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom]
  apply map_iso_inv_comp_naturality
  · exact hs
  · exact pullbackQuasicoherentSectionsIso_naturality φ
      (SheafOfModules.ιFree i)

/-- The affine free-source pullback comparison, conjugated on both sides by the
canonical affine global-sections equivalences. -/
noncomputable def freePullbackCoordinateIso (I : Type u) :
    ModuleCat.of S (I →₀ S) ≅
      (ModuleCat.extendScalars φ.hom).obj (ModuleCat.of R (I →₀ R)) :=
  freeModuleSpecΓIso (R := S) I ≪≫ freePullbackSectionsIso φ I ≪≫
    (ModuleCat.extendScalars φ.hom).mapIso (freeModuleSpecΓIso (R := R) I).symm

/-- The rank-one affine pullback comparison, conjugated on both sides by the
canonical affine global-sections equivalences. -/
noncomputable def unitPullbackCoordinateIso :
    ModuleCat.of S S ≅
      (ModuleCat.extendScalars φ.hom).obj (ModuleCat.of R R) :=
  unitModuleSpecΓIso S ≪≫ unitPullbackSectionsIso φ ≪≫
    (ModuleCat.extendScalars φ.hom).mapIso (unitModuleSpecΓIso R).symm

private lemma comp_three_squares {C : Type*} [Category C]
    {A B C₁ D E F G H : C}
    (p : A ⟶ B) (a : B ⟶ C₁) (b : A ⟶ D) (q : D ⟶ C₁)
    (c : C₁ ⟶ E) (d : D ⟶ F) (r : F ⟶ E)
    (e : E ⟶ G) (t : F ⟶ H) (l : H ⟶ G)
    (h₁ : p ≫ a = b ≫ q) (h₂ : q ≫ c = d ≫ r) (h₃ : r ≫ e = t ≫ l) :
    p ≫ (a ≫ (c ≫ e)) = (b ≫ (d ≫ t)) ≫ l := by
  calc
    _ = ((p ≫ a) ≫ c) ≫ e := by simp only [Category.assoc]
    _ = ((b ≫ q) ≫ c) ≫ e := congrArg (fun k ↦ (k ≫ c) ≫ e) h₁
    _ = (b ≫ (q ≫ c)) ≫ e := congrArg (fun k ↦ k ≫ e) (Category.assoc b q c)
    _ = (b ≫ (d ≫ r)) ≫ e := congrArg (fun k ↦ (b ≫ k) ≫ e) h₂
    _ = ((b ≫ d) ≫ r) ≫ e := congrArg (fun k ↦ k ≫ e) (Category.assoc b d r).symm
    _ = (b ≫ d) ≫ (r ≫ e) := Category.assoc _ _ _
    _ = (b ≫ d) ≫ (t ≫ l) := congrArg (fun k ↦ (b ≫ d) ≫ k) h₃
    _ = ((b ≫ d) ≫ t) ≫ l := (Category.assoc _ _ _).symm
    _ = (b ≫ (d ≫ t)) ≫ l := congrArg (fun k ↦ k ≫ l) (Category.assoc b d t)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- In free-module coordinates, the affine pullback comparison carries every standard
basis injection through the same rank-one comparison.  Thus it is diagonal with a
common rank-one component and does not mix the generators. -/
lemma lsingle_comp_freePullbackCoordinateIso_hom (I : Type u) (i : I) :
    ModuleCat.ofHom (Finsupp.lsingle i (R := S) (M := ModuleCat.of S S)) ≫
        (freePullbackCoordinateIso φ I).hom =
      (unitPullbackCoordinateIso φ).hom ≫
        (ModuleCat.extendScalars φ.hom).map
          (ModuleCat.ofHom (Finsupp.lsingle i (R := R) (M := ModuleCat.of R R))) := by
  have hR := iso_inv_comp_eq_iso_inv_comp_of_comp_eq
    (unitModuleSpecΓIso R) (freeModuleSpecΓIso (R := R) I)
    (ModuleCat.ofHom (Finsupp.lsingle i (R := R) (M := ModuleCat.of R R)))
    (moduleSpecΓFunctor.map (SheafOfModules.ιFree i))
    (lsingle_comp_freeModuleSpecΓIso_hom (R := R) I i)
  have h3 := congrArg (fun k ↦ (ModuleCat.extendScalars φ.hom).map k) hR
  rw [Functor.map_comp, Functor.map_comp] at h3
  dsimp only [freePullbackCoordinateIso, unitPullbackCoordinateIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom]
  apply comp_three_squares
  · exact lsingle_comp_freeModuleSpecΓIso_hom (R := S) I i
  · exact map_ιFree_comp_freePullbackSectionsIso_hom φ I i
  · exact h3

/-- The common rank-one component of the affine free-source pullback comparison,
expressed as an `S`-linear automorphism of `S`. -/
noncomputable def unitPullbackScalarEquiv : S ≃ₗ[S] S := by
  letI : Algebra R S := φ.hom.toAlgebra
  exact (unitPullbackCoordinateIso φ).toLinearEquiv.trans
    (TensorProduct.AlgebraTensorModule.rid R S S)

/-- The affine free-source pullback comparison in the standard `I →₀ S`
coordinates on both sides. -/
noncomputable def freePullbackCoordinateLinearEquiv (I : Type u) :
    (I →₀ S) ≃ₗ[S] (I →₀ S) :=
  (freePullbackCoordinateIso φ I).toLinearEquiv.trans
    (ModuleCat.extendScalarsFinsuppEquiv φ I)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma freePullbackCoordinateLinearEquiv_single
    (I : Type u) (i : I) (s : S) :
    freePullbackCoordinateLinearEquiv φ I (Finsupp.single i s) =
      Finsupp.single i (unitPullbackScalarEquiv φ s) := by
  have h := congrArg (fun k ↦ k.hom s)
    (lsingle_comp_freePullbackCoordinateIso_hom φ I i)
  change (freePullbackCoordinateIso φ I).hom (Finsupp.single i s) =
    (ModuleCat.extendScalars φ.hom).map
      (ModuleCat.ofHom (Finsupp.lsingle i))
        ((unitPullbackCoordinateIso φ).hom s) at h
  change ModuleCat.extendScalarsFinsuppEquiv φ I
      ((freePullbackCoordinateIso φ I).hom (Finsupp.single i s)) = _
  rw [h, ModuleCat.extendScalarsFinsuppEquiv_map_lsingle]
  rfl

/-- A linear endomorphism of the rank-one free module is multiplication by its value
at `1`; applied to the rank-one pullback comparison this identifies its scalar. -/
lemma unitPullbackScalarEquiv_apply (s : S) :
    unitPullbackScalarEquiv φ s = s * unitPullbackScalarEquiv φ 1 := by
  calc
    _ = unitPullbackScalarEquiv φ (s • (1 : S)) := by simp [smul_eq_mul]
    _ = s • unitPullbackScalarEquiv φ 1 := map_smul _ _ _
    _ = _ := by rw [smul_eq_mul]

/-- The common scalar of the free-source pullback comparison is a unit. -/
lemma isUnit_unitPullbackScalarEquiv_one :
    IsUnit (unitPullbackScalarEquiv φ 1) := by
  let e := unitPullbackScalarEquiv φ
  refine isUnit_iff_exists.mpr ⟨e.symm 1, ?_, ?_⟩
  · rw [mul_comm]
    change (e.symm 1) • e 1 = 1
    rw [← e.map_smul]
    simp [e]
  · change (e.symm 1) • e 1 = 1
    rw [← e.map_smul]
    simp [e]

/-- In standard free coordinates, affine pullback is componentwise multiplication by
the common unit supplied by the rank-one comparison. -/
lemma freePullbackCoordinateLinearEquiv_apply_apply
    (I : Type u) (z : I →₀ S) (i : I) :
    freePullbackCoordinateLinearEquiv φ I z i =
      z i * unitPullbackScalarEquiv φ 1 := by
  classical
  induction z using Finsupp.induction with
  | zero => simp
  | single_add j s z hj hs ih =>
      rw [map_add, freePullbackCoordinateLinearEquiv_single]
      change Finsupp.single j (unitPullbackScalarEquiv φ s) i +
        freePullbackCoordinateLinearEquiv φ I z i =
        (Finsupp.single j s + z) i * unitPullbackScalarEquiv φ 1
      rw [ih, Finsupp.add_apply, add_mul]
      by_cases hji : j = i
      · subst j
        rw [Finsupp.single_eq_same, Finsupp.single_eq_same,
          unitPullbackScalarEquiv_apply]
      · simp [hji]

/-- The free-source coordinate automorphism is scalar multiplication by its common
rank-one unit. -/
lemma freePullbackCoordinateLinearEquiv_eq_smul
    (I : Type u) (z : I →₀ S) :
    freePullbackCoordinateLinearEquiv φ I z =
      unitPullbackScalarEquiv φ 1 • z := by
  classical
  ext i
  rw [freePullbackCoordinateLinearEquiv_apply_apply]
  simp [mul_comm]

/-- Precomposing a linear map with the free-source affine pullback coordinate
automorphism does not change its kernel, because that automorphism is multiplication
by a unit. -/
lemma ker_comp_freePullbackCoordinateLinearEquiv
    (I : Type u) {M : Type*} [AddCommGroup M] [Module S M]
    (g : (I →₀ S) →ₗ[S] M) :
    LinearMap.ker (g.comp (freePullbackCoordinateLinearEquiv φ I).toLinearMap) =
      LinearMap.ker g := by
  ext z
  simp only [LinearMap.mem_ker, LinearMap.comp_apply]
  have hz := congrArg g (freePullbackCoordinateLinearEquiv_eq_smul φ I z)
  constructor
  · intro h
    have hs : g (unitPullbackScalarEquiv φ 1 • z) = 0 := hz.symm.trans h
    rwa [map_smul, (isUnit_unitPullbackScalarEquiv_one φ).smul_eq_zero] at hs
  · intro h
    apply hz.trans
    rw [map_smul, (isUnit_unitPullbackScalarEquiv_one φ).smul_eq_zero, h]

/-- Pullback between affine schemes, conjugated by the canonical isomorphisms with
their spectra of global sections. -/
noncomputable def pullbackAffineIsoSpecIso
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) (M : Y.Modules) :
    (Scheme.Modules.pullback (Spec.map f.appTop)).obj
        ((Scheme.Modules.pullback Y.isoSpec.inv).obj M) ≅
      (Scheme.Modules.pullback X.isoSpec.inv).obj
        ((Scheme.Modules.pullback f).obj M) :=
  (Scheme.Modules.pullbackComp (Spec.map f.appTop) Y.isoSpec.inv).app M ≪≫
    (Scheme.Modules.pullbackCongr (Scheme.isoSpec_inv_naturality f)).app M ≪≫
    ((Scheme.Modules.pullbackComp X.isoSpec.inv f).app M).symm

/-- Flatness of global sections of a quasicoherent module is preserved by pullback
between affine schemes. This is the module-theoretic core of flatness of quasicoherent
sheaves under base change. -/
lemma pullbackQuasicoherentSections_flat (M : (Spec R).Modules)
    [M.IsQuasicoherent] [Module.Flat R (moduleSpecΓFunctor.obj M)] :
    Module.Flat S
      (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (Spec.map φ)).obj M)) := by
  algebraize [φ.hom]
  letI : Module.Flat S
      (ModuleCat.extendScalars φ.hom |>.obj (moduleSpecΓFunctor.obj M)) :=
    Module.Flat.baseChange R S (moduleSpecΓFunctor.obj M)
  exact Module.Flat.of_linearEquiv (pullbackQuasicoherentSectionsLinearEquiv φ M)

/-- Relative affine base change for quasicoherent modules over a pushout of rings. -/
lemma pullbackQuasicoherentSections_flat_of_isPushout
    {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra S B] [Algebra A B] [Algebra R B]
    [IsScalarTower R S B] [IsScalarTower R A B] [Algebra.IsPushout R S A B]
    (M : (Spec (.of A)).Modules) [M.IsQuasicoherent]
    [Module R ((moduleSpecΓFunctor (R := .of A)).obj M)]
    [IsScalarTower R A ((moduleSpecΓFunctor (R := .of A)).obj M)]
    [Module.Flat R ((moduleSpecΓFunctor (R := .of A)).obj M)] :
    let N := (moduleSpecΓFunctor (R := .of B)).obj
      ((Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj M)
    letI := Module.compHom N (algebraMap S B)
    Module.Flat S N := by
  let T := (ModuleCat.extendScalars (algebraMap A B)).obj
    ((moduleSpecΓFunctor (R := .of A)).obj M)
  letI : Module S T := Module.compHom T (algebraMap S B)
  letI : IsScalarTower S B T :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let B' := (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)
  letI : IsScalarTower A B B' :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let eB : B' ≃ₗ[B] B :=
    { toEquiv := Equiv.refl _
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let eB' := TensorProduct.AlgebraTensorModule.congr eB
    (LinearEquiv.refl A ((moduleSpecΓFunctor (R := .of A)).obj M))
  letI : Module S
      (TensorProduct A B' ((moduleSpecΓFunctor (R := .of A)).obj M)) :=
    Module.compHom _ (algebraMap S B)
  letI : IsScalarTower S B
      (TensorProduct A B' ((moduleSpecΓFunctor (R := .of A)).obj M)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let eT : T ≃ₗ[S]
      TensorProduct A B ((moduleSpecΓFunctor (R := .of A)).obj M) :=
    eB'.restrictScalars S
  letI : Module.Flat S
      (TensorProduct A B ((moduleSpecΓFunctor (R := .of A)).obj M)) :=
    Module.Flat.baseChange_of_isPushout (R := R) (S := S) (A := A) (B := B)
      (M := (moduleSpecΓFunctor (R := .of A)).obj M)
  letI : Module.Flat S T := Module.Flat.of_linearEquiv eT
  let N := (moduleSpecΓFunctor (R := .of B)).obj
    ((Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj M)
  letI : Module S N := Module.compHom N (algebraMap S B)
  letI : IsScalarTower S B N :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  exact Module.Flat.of_linearEquiv
    ((pullbackQuasicoherentSectionsLinearEquiv
      (CommRingCat.ofHom (algebraMap A B)) M).restrictScalars S)

/-- Relative affine base change, with the pushout supplied categorically as a square of
commutative rings. -/
lemma pullbackQuasicoherentSections_flat_of_ring_isPushout
    {R S A B : CommRingCat.{u}} (f : R ⟶ A) (g : R ⟶ S)
    (fst : A ⟶ B) (snd : S ⟶ B) (h : IsPushout f g fst snd)
    (M : (Spec A).Modules) [M.IsQuasicoherent]
    (hflat :
      letI := Module.compHom (moduleSpecΓFunctor.obj M) f.hom
      Module.Flat R (moduleSpecΓFunctor.obj M)) :
    let N := moduleSpecΓFunctor.obj
      ((Scheme.Modules.pullback (Spec.map fst)).obj M)
    letI := Module.compHom N snd.hom
    Module.Flat S N := by
  letI : Algebra R A := f.hom.toAlgebra
  letI : Algebra R S := g.hom.toAlgebra
  letI : Algebra A B := fst.hom.toAlgebra
  letI : Algebra S B := snd.hom.toAlgebra
  letI : Algebra R B := (fst.hom.comp f.hom).toAlgebra
  letI : IsScalarTower R A B :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hw : fst.hom.comp f.hom = snd.hom.comp g.hom :=
    congrArg CommRingCat.Hom.hom h.w
  letI : IsScalarTower R S B :=
    IsScalarTower.of_algebraMap_eq fun x ↦ DFunLike.congr_fun hw x
  have hp : IsPushout
      (CommRingCat.ofHom (algebraMap R S)) (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap S B)) (CommRingCat.ofHom (algebraMap A B)) := by
    change IsPushout g f snd fst
    exact h.flip
  letI : Algebra.IsPushout R S A B :=
    CommRingCat.isPushout_iff_isPushout.mp hp
  letI : Module R (moduleSpecΓFunctor.obj M) :=
    Module.compHom (moduleSpecΓFunctor.obj M) f.hom
  letI : IsScalarTower R A (moduleSpecΓFunctor.obj M) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : Module.Flat R (moduleSpecΓFunctor.obj M) := hflat
  let N := moduleSpecΓFunctor.obj
    ((Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj M)
  letI : Module S N := Module.compHom N (algebraMap S B)
  change Module.Flat S
    (moduleSpecΓFunctor.obj
      ((Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj M))
  exact pullbackQuasicoherentSections_flat_of_isPushout
    (R := R) (S := S) (A := A) (B := B) M

/-- Relative flatness of affine global sections is preserved across a cartesian square
of affine schemes. -/
lemma pullbackQuasicoherentSections_flat_of_scheme_isPullback
    {P X Y Z : Scheme.{u}} [IsAffine P] [IsAffine X] [IsAffine Y] [IsAffine Z]
    (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : IsPullback fst snd f g) (M : X.Modules) [M.IsQuasicoherent]
    (hflat :
      letI := Module.compHom Γ(M, ⊤) f.appTop.hom
      Module.Flat Γ(Z, ⊤) Γ(M, ⊤)) :
    let N := (Scheme.Modules.pullback fst).obj M
    letI := Module.compHom Γ(N, ⊤) snd.appTop.hom
    Module.Flat Γ(Y, ⊤) Γ(N, ⊤) := by
  let Mspec := (Scheme.Modules.pullback X.isoSpec.inv).obj M
  letI : Mspec.IsQuasicoherent := by
    letI : IsOpenImmersion X.isoSpec.inv := inferInstance
    let e := (Scheme.Modules.restrictFunctorIsoPullback X.isoSpec.inv).app M
    exact (SheafOfModules.isQuasicoherent (Spec Γ(X, ⊤)).ringCatSheaf).prop_of_iso
      e inferInstance
  have hMspec :
      letI := Module.compHom (moduleSpecΓFunctor.obj Mspec) f.appTop.hom
      Module.Flat Γ(Z, ⊤) (moduleSpecΓFunctor.obj Mspec) :=
    Scheme.Modules.moduleSpecΓFunctor_pullback_isoSpec_inv_flat_restrictScalars
      M f.appTop.hom hflat
  letI : Module Γ(Z, ⊤) (moduleSpecΓFunctor.obj Mspec) :=
    Module.compHom (moduleSpecΓFunctor.obj Mspec) f.appTop.hom
  letI : Module.Flat Γ(Z, ⊤) (moduleSpecΓFunctor.obj Mspec) := hMspec
  have hring : IsPushout f.appTop g.appTop fst.appTop snd.appTop :=
    isPushout_appTop_of_isPullback h
  let Aff := (Scheme.Modules.pullback (Spec.map fst.appTop)).obj Mspec
  have hAff :
      letI := Module.compHom (moduleSpecΓFunctor.obj Aff) snd.appTop.hom
      Module.Flat Γ(Y, ⊤) (moduleSpecΓFunctor.obj Aff) :=
    pullbackQuasicoherentSections_flat_of_ring_isPushout
      f.appTop g.appTop fst.appTop snd.appTop hring Mspec inferInstance
  let b : Γ(Y, ⊤) →+* Γ(Spec Γ(P, ⊤), ⊤) :=
    (Scheme.ΓSpecIso Γ(P, ⊤)).inv.hom.comp snd.appTop.hom
  letI : Module Γ(Y, ⊤) (moduleSpecΓFunctor.obj Aff) :=
    Module.compHom (moduleSpecΓFunctor.obj Aff) snd.appTop.hom
  letI : Module.Flat Γ(Y, ⊤) (moduleSpecΓFunctor.obj Aff) := hAff
  have hAffTop :
      letI := Module.compHom Γ(Aff, ⊤) b
      Module.Flat Γ(Y, ⊤) Γ(Aff, ⊤) :=
    moduleSpecΓFunctor_flat_to_top_restrictScalars Aff snd.appTop.hom
      (fun _ _ ↦ rfl)
  let N := (Scheme.Modules.pullback fst).obj M
  let Nspec := (Scheme.Modules.pullback P.isoSpec.inv).obj N
  let e : Aff ≅ Nspec := pullbackAffineIsoSpecIso fst M
  have hNspecTop :
      letI := Module.compHom Γ(Nspec, ⊤) b
      Module.Flat Γ(Y, ⊤) Γ(Nspec, ⊤) :=
    Scheme.Modules.sections_flat_of_iso_restrictScalars e ⊤ b hAffTop
  letI : Module Γ(Y, ⊤) Γ(Nspec, ⊤) := Module.compHom Γ(Nspec, ⊤) b
  letI : Module.Flat Γ(Y, ⊤) Γ(Nspec, ⊤) := hNspecTop
  have hNspec :
      letI := Module.compHom (moduleSpecΓFunctor.obj Nspec) snd.appTop.hom
      Module.Flat Γ(Y, ⊤) (moduleSpecΓFunctor.obj Nspec) :=
    moduleSpecΓFunctor_flat_of_top_restrictScalars Nspec snd.appTop.hom
      (fun _ _ ↦ rfl)
  exact Scheme.Modules.flat_sections_of_moduleSpecΓFunctor_pullback_isoSpec_inv
    N snd.appTop.hom hNspec

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- A finite presentation of the global-sections module of a quasicoherent sheaf on an
affine scheme induces a finite global presentation of the sheaf. -/
lemma exists_finitePresentation_of_moduleSpecΓFunctor
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    [hfp : Module.FinitePresentation R (moduleSpecΓFunctor.obj M)] :
    ∃ P : M.Presentation, P.IsFinite := by
  obtain ⟨s, hs, hker⟩ := hfp.out
  obtain ⟨t, htfin, ht⟩ := Submodule.fg_def.mp hker
  letI := htfin.fintype
  let s' : Set (moduleSpecΓFunctor.obj M) := ↑s
  let P := presentationTilde.{u} (moduleSpecΓFunctor.obj M) s'
    (by simpa using hs) (↑t : Set _)
    (by
      convert ht using 1 <;> subst s' <;> rfl)
  haveI : P.IsFinite :=
    { isFiniteType_generators := ⟨by
        dsimp [P, presentationTilde, SheafOfModules.presentationOfIsCokernelFree,
          SheafOfModules.generatorsOfIsCokernelFree]
        infer_instance⟩
      isFiniteType_relations := ⟨by
        dsimp [P, presentationTilde, SheafOfModules.presentationOfIsCokernelFree,
          SheafOfModules.relationsOfIsCokernelFree]
        infer_instance⟩ }
  letI : IsIso M.fromTildeΓ :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  let Q : M.Presentation := P.ofIsIso M.fromTildeΓ
  haveI : Q.IsFinite := inferInstance
  exact ⟨Q, inferInstance⟩
set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- A quasicoherent module sheaf on an affine scheme is finitely presented when its
module of global sections is finitely presented. This is the finite-presentation
refinement of the affine tilde equivalence. -/
lemma isFinitePresentation_of_moduleSpecΓFunctor
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    [Module.FinitePresentation R (moduleSpecΓFunctor.obj M)] :
    M.IsFinitePresentation := by
  obtain ⟨Q, hQ⟩ := exists_finitePresentation_of_moduleSpecΓFunctor M
  letI : Q.IsFinite := hQ
  apply SheafOfModules.IsFinitePresentation.mk (C := (Spec R).Opens)
  refine ⟨Q.quasicoherentData, ?_⟩
  constructor
  intro i
  constructor <;> constructor
  · change Finite Q.generators.I
    infer_instance
  · change Finite Q.relations.I
    infer_instance

/-- If the global sections of a quasicoherent module on `Spec R` are finite projective
of constant rank `q`, then the global sections of its pullback to `Spec S` have the same
properties. -/
lemma pullbackQuasicoherentSections_finite_projective_rank (M : (Spec R).Modules)
    [M.IsQuasicoherent] {q : ℕ}
    (hfin : Module.Finite R (moduleSpecΓFunctor.obj M))
    (hproj : Module.Projective R (moduleSpecΓFunctor.obj M))
    (hrank : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk (moduleSpecΓFunctor.obj M) p = q) :
    Module.Finite S
        (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (Spec.map φ)).obj M)) ∧
      Module.Projective S
        (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (Spec.map φ)).obj M)) ∧
      ∀ p : PrimeSpectrum S, Module.rankAtStalk
        (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (Spec.map φ)).obj M)) p = q := by
  algebraize [φ.hom]
  let e := pullbackQuasicoherentSectionsLinearEquiv φ M
  have hbase := @Module.finite_projective_rankAtStalk_baseChange R S
    (moduleSpecΓFunctor.obj M) _ _ _ _ _ hfin hproj q hrank
  refine ⟨@Module.Finite.equiv S _ _ _ _ _ _ _ hbase.1 e.symm,
    @Module.Projective.of_equiv _ _ _ _ _ _ _ _ _ _ _ _ _ _ e.symm hbase.2.1, ?_⟩
  intro p
  exact (congrFun (Module.rankAtStalk_eq_of_equiv e) p).trans (hbase.2.2 p)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- A section of a quasicoherent sheaf of modules over an affine open which restricts to
zero on a basic open is annihilated by a power of the defining function: sections over
the basic open are the localization of the sections over the affine open.  (Supporting
lemma for the proof of Proposition 2.4.2: the saturation argument multiplies a section
vanishing on the generic fibre by a power of the uniformizer.) -/
theorem Scheme.Modules.exists_pow_smul_eq_zero_of_res_basicOpen_eq_zero
    {P : Scheme.{u}} (N : P.Modules) [N.IsQuasicoherent]
    {U : P.Opens} (hU : IsAffineOpen U) (r : Γ(P, U)) (z : Γ(N, U))
    (hz : (N.presheaf.map (homOfLE (P.basicOpen_le r)).op).hom z = 0) :
    ∃ n : ℕ, r ^ n • z = 0 := by
  classical
  set j : Spec Γ(P, U) ⟶ P := hU.fromSpec with hj
  set Ns : (Spec Γ(P, U)).Modules := N.restrict j with hNs
  haveI : Ns.IsQuasicoherent :=
    inferInstanceAs (((Scheme.Modules.restrictFunctor j).obj N).IsQuasicoherent)
  have him : j ''ᵁ (⊤ : (Spec Γ(P, U)).Opens) = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]
  -- transport `z` to a global section of the restriction
  let ρ := (N.presheaf.map (eqToHom him).op).hom
  let z' : Γ(Ns, ⊤) := (N.restrictAppIso j ⊤).inv.hom (ρ z)
  -- the restriction of `z'` to the basic open vanishes
  have hz' : Scheme.Modules.sectionsToBasicOpenLinearMap Ns r z' = 0 := by
    have hmor : N.presheaf.map (eqToHom him).op ≫ (N.restrictAppIso j ⊤).inv ≫
        Ns.presheaf.map (homOfLE (le_top :
          (PrimeSpectrum.basicOpen r : (Spec Γ(P, U)).Opens) ≤ ⊤)).op =
        N.presheaf.map (homOfLE (P.basicOpen_le r)).op ≫
          N.presheaf.map (homOfLE
            (le_of_eq (hU.fromSpec_image_basicOpen (f := r)))).op ≫
          (N.restrictAppIso j (PrimeSpectrum.basicOpen r)).inv := by
      rw [Scheme.Modules.restrictAppIso_inv_map j N
        (U := PrimeSpectrum.basicOpen r) (V := ⊤)
        (homOfLE (le_top : (PrimeSpectrum.basicOpen r :
          (Spec Γ(P, U)).Opens) ≤ ⊤)).op]
      rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
      congr 1
    have happ := CategoryTheory.congr_fun hmor z
    refine Eq.trans ?_ (happ.trans ?_)
    · rfl
    · show ((N.restrictAppIso j (PrimeSpectrum.basicOpen r)).inv.hom)
        ((N.presheaf.map (homOfLE
          (le_of_eq (hU.fromSpec_image_basicOpen (f := r)))).op).hom
          ((N.presheaf.map (homOfLE (P.basicOpen_le r)).op).hom z)) = 0
      rw [hz, map_zero, map_zero]
  -- localization: a power of `r` kills `z'`
  haveI := Scheme.Modules.isLocalizedModule_sectionsToBasicOpenLinearMap Ns r
  obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq
    (S := Submonoid.powers r) (f := Scheme.Modules.sectionsToBasicOpenLinearMap Ns r)
    (x₁ := z') (x₂ := 0) (by rw [hz', map_zero])
  obtain ⟨n, hn⟩ := c.2
  rw [smul_zero] at hc
  have hcz : r ^ n • z' = 0 := by
    have := hc
    rw [Submonoid.smul_def] at this
    rw [← hn] at this
    exact this
  -- transport the annihilation statement back to `Γ(N, U)`
  refine ⟨n, ?_⟩
  have hρinj : Function.Injective ρ := fun a b hab ↦
    (ConcreteCategory.bijective_of_isIso (N.presheaf.map (eqToHom him).op)).injective hab
  apply hρinj
  rw [map_zero]
  -- `ρ` is semilinear over the restriction of scalars
  have hsemi : ρ (r ^ n • z) =
      (P.presheaf.map (eqToHom him).op).hom (r ^ n) • ρ z :=
    Scheme.Modules.map_smul N (eqToHom him) (r ^ n) z
  rw [hsemi]
  -- identify the two scalar actions on the global sections of the restriction
  have hscal : (P.presheaf.map (eqToHom him).op).hom (r ^ n) =
      (j.appIso ⊤).inv.hom (algebraMap Γ(P, U) Γ(Spec Γ(P, U), ⊤) (r ^ n)) := by
    have hpre : (⊤ : (Spec Γ(P, U)).Opens) ≤ j ⁻¹ᵁ U := by
      rw [hj, hU.fromSpec_preimage_self]
    have happ : (j.appLE U ⊤ hpre).hom =
        algebraMap Γ(P, U) Γ(Spec Γ(P, U), ⊤) :=
      hU.fromSpec_appLE_eq_algebraMap ⊤
    have hsplit : P.presheaf.map (eqToHom him).op ≫
        j.appLE (j ''ᵁ (⊤ : (Spec Γ(P, U)).Opens)) ⊤ (j.preimage_image_eq ⊤).ge =
          j.appLE U ⊤ hpre := by
      rw [Scheme.Hom.map_appLE]
    have happiso : (j.appIso ⊤).hom =
        (j.appLE (j ''ᵁ (⊤ : (Spec Γ(P, U)).Opens)) ⊤ (j.preimage_image_eq ⊤).ge) :=
      Scheme.Hom.appIso_hom' j ⊤
    apply (ConcreteCategory.bijective_of_isIso (j.appIso ⊤).hom).injective
    have h1 : (j.appIso ⊤).hom.hom ((P.presheaf.map (eqToHom him).op).hom (r ^ n)) =
        algebraMap Γ(P, U) Γ(Spec Γ(P, U), ⊤) (r ^ n) := by
      have hc := CategoryTheory.congr_fun hsplit (r ^ n)
      rw [← happ]
      refine Eq.trans ?_ hc
      rw [happiso]
      rfl
    have h2 : (j.appIso ⊤).hom.hom ((j.appIso ⊤).inv.hom
        (algebraMap Γ(P, U) Γ(Spec Γ(P, U), ⊤) (r ^ n))) =
        algebraMap Γ(P, U) Γ(Spec Γ(P, U), ⊤) (r ^ n) := by
      change ((j.appIso ⊤).inv ≫ (j.appIso ⊤).hom).hom
        (algebraMap Γ(P, U) Γ(Spec Γ(P, U), ⊤) (r ^ n)) = _
      rw [Iso.inv_hom_id]
      rfl
    exact h1.trans h2.symm
  rw [hscal]
  -- conclude via the `smul` description of the restricted module structure
  have hrs : (j.appIso ⊤).inv.hom (algebraMap Γ(P, U) Γ(Spec Γ(P, U), ⊤) (r ^ n)) • ρ z =
      (N.restrictAppIso j ⊤).hom.hom
        (algebraMap Γ(P, U) Γ(Spec Γ(P, U), ⊤) (r ^ n) • z') := by
    have := Scheme.Modules.smul_restrictAppIso_hom_apply j N ⊤
      (algebraMap Γ(P, U) Γ(Spec Γ(P, U), ⊤) (r ^ n)) z'
    rw [this]
    rfl
  rw [hrs]
  have hAsmul : algebraMap Γ(P, U) Γ(Spec Γ(P, U), ⊤) (r ^ n) • z' = 0 := by
    have htower : algebraMap Γ(P, U) Γ(Spec Γ(P, U), ⊤) (r ^ n) • z' = r ^ n • z' :=
      algebraMap_smul Γ(Spec Γ(P, U), ⊤) (r ^ n) z'
    rw [htower, hcz]
  rw [hAsmul, map_zero]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- A section of a quasicoherent sheaf of modules over a basic open extends to the
ambient affine open after clearing a power of the defining function: sections over the
basic open are the localization of the sections over the affine open (surjectivity
half).  (Supporting lemma for the proof of Proposition 2.4.2.) -/
theorem Scheme.Modules.exists_pow_smul_res_of_basicOpen
    {P : Scheme.{u}} (N : P.Modules) [N.IsQuasicoherent]
    {U : P.Opens} (hU : IsAffineOpen U) (r : Γ(P, U)) (z : Γ(N, P.basicOpen r)) :
    ∃ (z₀ : Γ(N, U)) (n : ℕ),
      (N.presheaf.map (homOfLE (P.basicOpen_le r)).op).hom z₀ =
        (P.presheaf.map (homOfLE (P.basicOpen_le r)).op).hom r ^ n • z := by
  classical
  set j : Spec Γ(P, U) ⟶ P := hU.fromSpec with hj
  set Ns : (Spec Γ(P, U)).Modules := N.restrict j with hNs
  haveI : Ns.IsQuasicoherent :=
    inferInstanceAs (((Scheme.Modules.restrictFunctor j).obj N).IsQuasicoherent)
  have him : j ''ᵁ (⊤ : (Spec Γ(P, U)).Opens) = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]
  have himD : j ''ᵁ (PrimeSpectrum.basicOpen r : (Spec Γ(P, U)).Opens) =
      P.basicOpen r := hU.fromSpec_image_basicOpen (f := r)
  -- transport `z` into the Spec model over the basic open
  let ρD := (N.presheaf.map (eqToHom himD).op).hom
  let zD : Γ(Ns, PrimeSpectrum.basicOpen r) :=
    (N.restrictAppIso j (PrimeSpectrum.basicOpen r)).inv.hom (ρD z)
  haveI := Scheme.Modules.isLocalizedModule_sectionsToBasicOpenLinearMap Ns r
  obtain ⟨⟨z₀', c⟩, hz₀'⟩ := IsLocalizedModule.surj
    (S := Submonoid.powers r) (f := Scheme.Modules.sectionsToBasicOpenLinearMap Ns r) zD
  obtain ⟨n, hn⟩ := c.2
  -- transport the numerator back to `Γ(N, U)`
  let ρ := (N.presheaf.map (eqToHom him).op).hom
  have hρbij : Function.Bijective ρ :=
    ConcreteCategory.bijective_of_isIso (N.presheaf.map (eqToHom him).op)
  obtain ⟨z₀, hz₀⟩ := hρbij.2 ((N.restrictAppIso j ⊤).hom.hom z₀')
  refine ⟨z₀, n, ?_⟩
  -- both sides live over the basic open; compare after moving to the Spec model
  have hρDinj : Function.Injective ρD :=
    (ConcreteCategory.bijective_of_isIso (N.presheaf.map (eqToHom himD).op)).injective
  have hres : ∀ y : Γ(N, U),
      ρD ((N.presheaf.map (homOfLE (P.basicOpen_le r)).op).hom y) =
        (N.restrictAppIso j (PrimeSpectrum.basicOpen r)).hom.hom
          ((Ns.presheaf.map (homOfLE (le_top : (PrimeSpectrum.basicOpen r :
            (Spec Γ(P, U)).Opens) ≤ ⊤)).op).hom
            ((N.restrictAppIso j ⊤).inv.hom (ρ y))) := by
    intro y
    have hmor : N.presheaf.map (homOfLE (P.basicOpen_le r)).op ≫
        N.presheaf.map (eqToHom himD).op =
        N.presheaf.map (eqToHom him).op ≫ (N.restrictAppIso j ⊤).inv ≫
          Ns.presheaf.map (homOfLE (le_top : (PrimeSpectrum.basicOpen r :
            (Spec Γ(P, U)).Opens) ≤ ⊤)).op ≫
          (N.restrictAppIso j (PrimeSpectrum.basicOpen r)).hom := by
      rw [Scheme.Modules.restrictAppIso_inv_map_assoc j N
        (U := PrimeSpectrum.basicOpen r) (V := ⊤)
        (homOfLE (le_top : (PrimeSpectrum.basicOpen r :
          (Spec Γ(P, U)).Opens) ≤ ⊤)).op]
      rw [Iso.inv_hom_id, Category.comp_id, ← Functor.map_comp, ← Functor.map_comp]
      congr 1
    exact CategoryTheory.congr_fun hmor y
  apply hρDinj
  rw [hres z₀, hz₀]
  -- reduce to the Spec-model identity produced by `IsLocalizedModule.surj`
  have hcollapse : (N.restrictAppIso j ⊤).inv.hom
      ((N.restrictAppIso j ⊤).hom.hom z₀') = z₀' := by
    rw [← CategoryTheory.comp_apply, Iso.hom_inv_id]
    rfl
  rw [hcollapse]
  -- the right-hand side: transport the scalar multiplication
  have hsmul : ρD ((P.presheaf.map (homOfLE (P.basicOpen_le r)).op).hom r ^ n • z) =
      (P.presheaf.map (eqToHom himD).op).hom
          ((P.presheaf.map (homOfLE (P.basicOpen_le r)).op).hom r ^ n) • ρD z := by
    rw [← map_pow]
    exact Scheme.Modules.map_smul N (eqToHom himD) _ z
  rw [hsmul, map_pow]
  -- identify the scalar with the algebra-map image of `r ^ n`
  have hscal : (P.presheaf.map (eqToHom himD).op).hom
      ((P.presheaf.map (homOfLE (P.basicOpen_le r)).op).hom r) =
      (j.appIso (PrimeSpectrum.basicOpen r)).inv.hom
        (algebraMap Γ(P, U) Γ(Spec Γ(P, U), PrimeSpectrum.basicOpen r) r) := by
    have hpre : (PrimeSpectrum.basicOpen r : (Spec Γ(P, U)).Opens) ≤ j ⁻¹ᵁ U := by
      rw [hj, hU.fromSpec_preimage_self]
      exact le_top
    have happ : (j.appLE U (PrimeSpectrum.basicOpen r) hpre).hom =
        algebraMap Γ(P, U) Γ(Spec Γ(P, U), PrimeSpectrum.basicOpen r) :=
      hU.fromSpec_appLE_eq_algebraMap (PrimeSpectrum.basicOpen r)
    have hsplit : P.presheaf.map (homOfLE (P.basicOpen_le r)).op ≫
        P.presheaf.map (eqToHom himD).op ≫
        j.appLE (j ''ᵁ (PrimeSpectrum.basicOpen r : (Spec Γ(P, U)).Opens))
          (PrimeSpectrum.basicOpen r) (j.preimage_image_eq _).ge =
          j.appLE U (PrimeSpectrum.basicOpen r) hpre := by
      rw [Scheme.Hom.map_appLE, Scheme.Hom.map_appLE]
    have happiso : (j.appIso (PrimeSpectrum.basicOpen r)).hom =
        (j.appLE (j ''ᵁ (PrimeSpectrum.basicOpen r : (Spec Γ(P, U)).Opens))
          (PrimeSpectrum.basicOpen r) (j.preimage_image_eq _).ge) :=
      Scheme.Hom.appIso_hom' j _
    apply (ConcreteCategory.bijective_of_isIso
      (j.appIso (PrimeSpectrum.basicOpen r)).hom).injective
    have h1 : (j.appIso (PrimeSpectrum.basicOpen r)).hom.hom
        ((P.presheaf.map (eqToHom himD).op).hom
          ((P.presheaf.map (homOfLE (P.basicOpen_le r)).op).hom r)) =
        algebraMap Γ(P, U) Γ(Spec Γ(P, U), PrimeSpectrum.basicOpen r) r := by
      have hc := CategoryTheory.congr_fun hsplit r
      rw [← happ]
      refine Eq.trans ?_ hc
      rw [happiso]
      rfl
    have h2 : (j.appIso (PrimeSpectrum.basicOpen r)).hom.hom
        ((j.appIso (PrimeSpectrum.basicOpen r)).inv.hom
          (algebraMap Γ(P, U) Γ(Spec Γ(P, U), PrimeSpectrum.basicOpen r) r)) =
        algebraMap Γ(P, U) Γ(Spec Γ(P, U), PrimeSpectrum.basicOpen r) r := by
      change ((j.appIso (PrimeSpectrum.basicOpen r)).inv ≫
        (j.appIso (PrimeSpectrum.basicOpen r)).hom).hom _ = _
      rw [Iso.inv_hom_id]
      rfl
    exact h1.trans h2.symm
  rw [hscal]
  -- conclude via the `smul` description of the restricted module structure
  have hrs : (j.appIso (PrimeSpectrum.basicOpen r)).inv.hom
        (algebraMap Γ(P, U) Γ(Spec Γ(P, U), PrimeSpectrum.basicOpen r) r) ^ n • ρD z =
      (N.restrictAppIso j (PrimeSpectrum.basicOpen r)).hom.hom
        (algebraMap Γ(P, U) Γ(Spec Γ(P, U), PrimeSpectrum.basicOpen r) r ^ n • zD) := by
    rw [← map_pow, ← map_pow]
    have := Scheme.Modules.smul_restrictAppIso_hom_apply j N (PrimeSpectrum.basicOpen r)
      (algebraMap Γ(P, U) Γ(Spec Γ(P, U), PrimeSpectrum.basicOpen r) (r ^ n)) zD
    rw [this]
    rfl
  rw [hrs]
  congr 1
  -- finally, the Spec-model identity
  have htower : algebraMap Γ(P, U) Γ(Spec Γ(P, U), PrimeSpectrum.basicOpen r) r ^ n • zD =
      (r ^ n : Γ(P, U)) • zD := by
    rw [← map_pow]
    exact algebraMap_smul Γ(Spec Γ(P, U), PrimeSpectrum.basicOpen r) (r ^ n) zD
  rw [htower]
  have hz₀'' : (r ^ n : Γ(P, U)) • zD =
      Scheme.Modules.sectionsToBasicOpenLinearMap Ns r z₀' := by
    have h0 := hz₀'
    rw [Submonoid.smul_def] at h0
    rw [← hn] at h0
    exact h0
  rw [hz₀'']
  rfl


set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- Restriction of sections of a quasi-coherent sheaf from an affine open of an arbitrary
scheme to a basic open, as a linear map over the sections of the structure sheaf. -/
noncomputable def Scheme.Modules.resBasicOpenLinearMap {P : Scheme.{u}} (N : P.Modules)
    {U : P.Opens} (r : Γ(P, U)) :
    letI : Algebra Γ(P, U) Γ(P, P.basicOpen r) :=
      ((P.presheaf.map (homOfLE (P.basicOpen_le r)).op).hom).toAlgebra
    letI : Module Γ(P, U) Γ(N, P.basicOpen r) :=
      Module.compHom _ ((P.presheaf.map (homOfLE (P.basicOpen_le r)).op).hom)
    Γ(N, U) →ₗ[Γ(P, U)] Γ(N, P.basicOpen r) :=
  letI : Algebra Γ(P, U) Γ(P, P.basicOpen r) :=
    ((P.presheaf.map (homOfLE (P.basicOpen_le r)).op).hom).toAlgebra
  letI : Module Γ(P, U) Γ(N, P.basicOpen r) :=
    Module.compHom _ ((P.presheaf.map (homOfLE (P.basicOpen_le r)).op).hom)
  { toFun := (N.presheaf.map (homOfLE (P.basicOpen_le r)).op).hom
    map_add' := map_add _
    map_smul' := fun c x ↦ Scheme.Modules.map_smul N (homOfLE (P.basicOpen_le r)) c x }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
/-- **Sections over a basic open are the localization**: for a quasi-coherent sheaf on an
arbitrary scheme and an affine open `U`, the sections over the basic open `D(r)` are the
localization of the sections over `U` away from `r`. -/
theorem Scheme.Modules.isLocalizedModule_resBasicOpenLinearMap {P : Scheme.{u}}
    (N : P.Modules) [N.IsQuasicoherent] {U : P.Opens} (hU : IsAffineOpen U)
    (r : Γ(P, U)) :
    letI : Algebra Γ(P, U) Γ(P, P.basicOpen r) :=
      ((P.presheaf.map (homOfLE (P.basicOpen_le r)).op).hom).toAlgebra
    letI : Module Γ(P, U) Γ(N, P.basicOpen r) :=
      Module.compHom _ ((P.presheaf.map (homOfLE (P.basicOpen_le r)).op).hom)
    IsLocalizedModule (Submonoid.powers r) (Scheme.Modules.resBasicOpenLinearMap N r) := by
  letI : Algebra Γ(P, U) Γ(P, P.basicOpen r) :=
    ((P.presheaf.map (homOfLE (P.basicOpen_le r)).op).hom).toAlgebra
  letI : Module Γ(P, U) Γ(N, P.basicOpen r) :=
    Module.compHom _ ((P.presheaf.map (homOfLE (P.basicOpen_le r)).op).hom)
  haveI : IsLocalization.Away r Γ(P, P.basicOpen r) := hU.isLocalization_basicOpen r
  refine ⟨?_, ?_, ?_⟩
  · -- powers of `r` act invertibly on the sections over the basic open
    rintro ⟨c, k, rfl⟩
    have hunit : IsUnit ((P.presheaf.map (homOfLE (P.basicOpen_le r)).op).hom (r ^ k)) := by
      rw [map_pow]
      exact ((IsLocalization.Away.algebraMap_isUnit
        (S := Γ(P, P.basicOpen r)) r)).pow k
    rw [Module.End.isUnit_iff]
    obtain ⟨u, hu⟩ := hunit
    constructor
    · intro a b hab
      have hstep : ((u⁻¹ : Γ(P, P.basicOpen r)ˣ) : Γ(P, P.basicOpen r)) •
          (((u : Γ(P, P.basicOpen r))) • a) =
          ((u⁻¹ : Γ(P, P.basicOpen r)ˣ) : Γ(P, P.basicOpen r)) •
            (((u : Γ(P, P.basicOpen r))) • b) := by
        rw [show ((u : Γ(P, P.basicOpen r))) • a =
          (P.presheaf.map (homOfLE (P.basicOpen_le r)).op).hom (r ^ k) • a from by rw [hu]]
        rw [show ((u : Γ(P, P.basicOpen r))) • b =
          (P.presheaf.map (homOfLE (P.basicOpen_le r)).op).hom (r ^ k) • b from by rw [hu]]
        exact congrArg _ hab
      rwa [smul_smul, smul_smul, Units.inv_mul, one_smul, one_smul] at hstep
    · intro y
      refine ⟨((u⁻¹ : Γ(P, P.basicOpen r)ˣ) : Γ(P, P.basicOpen r)) • y, ?_⟩
      show (P.presheaf.map (homOfLE (P.basicOpen_le r)).op).hom (r ^ k) •
        (((u⁻¹ : Γ(P, P.basicOpen r)ˣ) : Γ(P, P.basicOpen r)) • y) = y
      rw [← hu, smul_smul, Units.mul_inv, one_smul]
  · -- surjectivity up to denominators
    intro y
    obtain ⟨z₀, n, hz₀⟩ := Scheme.Modules.exists_pow_smul_res_of_basicOpen N hU r y
    refine ⟨⟨z₀, ⟨r ^ n, n, rfl⟩⟩, ?_⟩
    show (r ^ n : Γ(P, U)) • y = Scheme.Modules.resBasicOpenLinearMap N r z₀
    rw [← map_pow] at hz₀
    exact hz₀.symm
  · -- equality up to a power of `r`
    intro x₁ x₂ hx
    have hsub : (N.presheaf.map (homOfLE (P.basicOpen_le r)).op).hom (x₁ - x₂) = 0 := by
      rw [map_sub]
      exact sub_eq_zero_of_eq hx
    obtain ⟨n, hn⟩ :=
      Scheme.Modules.exists_pow_smul_eq_zero_of_res_basicOpen_eq_zero N hU r (x₁ - x₂) hsub
    refine ⟨⟨r ^ n, n, rfl⟩, ?_⟩
    show (r ^ n : Γ(P, U)) • x₁ = (r ^ n : Γ(P, U)) • x₂
    rw [smul_sub] at hn
    exact sub_eq_zero.mp hn


end AlgebraicGeometry
