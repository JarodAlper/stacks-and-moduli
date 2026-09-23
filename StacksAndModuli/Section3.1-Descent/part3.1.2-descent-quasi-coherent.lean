module

public import StacksAndModuli.«Section3.1-Descent».«part3.1.1-modules»
public import StacksAndModuli.Util.FpqcCover
public import StacksAndModuli.API.PullbackAdjoint
public import StacksAndModuli.API.PseudofunctorToCatPullbackComp
public import StacksAndModuli.API.ModuleDescent
public import StacksAndModuli.API.ModuleDescentData.Effectivity
public import StacksAndModuli.API.PseudofunctorAffineStackCriterion
public import StacksAndModuli.API.ConjugateRestrict
public import StacksAndModuli.API.ExtendScalarsAdjPseudofunctor
public import StacksAndModuli.API.PseudofunctorDescentStrongTrans
public import StacksAndModuli.API.PseudofunctorPrecompositionDescentEquivalence
public import StacksProject.Topologies.Fpqc.«lemma-fpqc-affine»
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Bicategory.Functor.Cat.ObjectProperty
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Sites.Descent.IsStack
public import Mathlib.CategoryTheory.Sites.Descent.Precoverage

/-!
# Fpqc descent for quasi-coherent sheaves

This module formalizes Proposition 3.1.4 (`prop:fpqc-descent-for-quasi-coherent-sheaves`)
of §3.1 (Descent theory, `sec:descent-theory`) of *Stacks and Moduli*,
first in the affine form to which the book's proof reduces
the general case — modules over a faithfully flat ring map `R → S` — and then in the
scheme-level form.

Affine part (1), descent for homomorphisms, is proved:
- `LinearMap.baseChange_injective`: base change is injective on homomorphism sets;
- `LinearMap.exists_baseChange_eq`: an `S`-linear map `ψ : S ⊗[R] M →ₗ[S] S ⊗[R] N`
  descends to `R` as soon as it sends elements `1 ⊗ m` to elements satisfying the Amitsur
  equalizer condition — by `Module.FaithfullyFlat.exists_one_tmul_eq_iff` this is the
  affine content of "a homomorphism whose two pullbacks agree descends".

Affine part (2), effectivity of descent data, is recorded through Mathlib's comonadicity of
extension of scalars (`ModuleCat.comonadicExtendScalars`): the category of `R`-modules is
equivalent to the category of comodules ("descent data") over the comonad induced by a
faithfully flat `R → S`.

The scheme-level form is stated as `AlgebraicGeometry.Scheme.Modules`
`.isStack_quasicoherentPseudofunctor` (proof pending): the fibered category
`X ↦ QCoh(X)`, `f ↦ f^*` is a stack for the fpqc topology. Building the fibered category
requires that quasi-coherence be stable under pullback along an *arbitrary* morphism of
schemes, which Mathlib has only for open immersions. That gap is filled here:

- `TopologicalSpace.Opens.final_map`: the preimage functor on opens is final, whence
- `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`: `f^* 𝒪_Y ≅ 𝒪_X` for arbitrary `f`;
- `AlgebraicGeometry.Scheme.Modules.pullbackMorphismRestrictIso`: base-change compatibility
  of pullback with restriction to an open;
- `SheafOfModules.Presentation.map_isFinite`: a generic finite-presentation mapping
  lemma for colimit-preserving functors carrying unit to unit;
- `AlgebraicGeometry.Scheme.Modules.presentationMap_isFinite`: mapping a finite
  presentation by a suitable colimit-preserving functor preserves its finiteness;
- `AlgebraicGeometry.Scheme.Modules.presentationPullback_isFinite`: pullback preserves
  finiteness of a chosen presentation;
- `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_of_presentation`: a finite
  chosen presentation defines a finite-presentation sheaf;
- `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_of_isOpenCover`: finite
  presentation glues from explicit finite presentations on an open cover;
- `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_pullback`: arbitrary pullback
  preserves finite presentation;
- `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_isOpenCover`: quasi-coherence is
  local on the base (converse of Mathlib's `exists_isOpenCover_presentation`);
- `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pullback`: the pullback stability;
- `AlgebraicGeometry.Scheme.Modules.quasicoherentPseudofunctor`: the fibered category
  `X ↦ QCoh(X)`, obtained from Mathlib's `Pseudofunctor.ObjectProperty.fullsubcategory`.
-/

@[expose] public section
set_option maxErrors 2000

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section PropFpqcDescentForQuasiCoherentSheaves

open TensorProduct

universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- API lemma used in the proof of Proposition 3.1.4 (part (1),
injectivity, affine form): let $R \to S$ be a faithfully flat ring map and let $M, N$ be
$R$-modules. Base change along $R \to S$ is injective on homomorphisms: an $R$-linear map
$M \to N$ is determined by its base change $S \otimes_R M \to S \otimes_R N$. -/
theorem LinearMap.baseChange_injective [Module.FaithfullyFlat R S] :
    Function.Injective (LinearMap.baseChange S : (M →ₗ[R] N) → _) := by
  intro φ φ' h
  ext m
  apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := R) (B := S) N
  have := LinearMap.congr_fun h ((1 : S) ⊗ₜ[R] m)
  simpa using this

/-- API lemma used in the proof of Proposition 3.1.4 (part (1),
surjectivity, affine form): let $R \to S$ be a faithfully flat ring map and let $M, N$ be
$R$-modules. An $S$-linear map $\psi \colon S \otimes_R M \to S \otimes_R N$ descends to
an $R$-linear map (i.e. is a base change) as soon as each $\psi(1 \otimes m)$ lies in the
image of $N \to S \otimes_R N$; by the Amitsur equalizer
(`Module.FaithfullyFlat.exists_one_tmul_eq_iff`) the latter condition is exactly the
agreement of the two pullbacks of $\psi(1 \otimes m)$ to
$S \otimes_R S \otimes_R N$. -/
theorem LinearMap.exists_baseChange_eq [Module.FaithfullyFlat R S]
    (ψ : S ⊗[R] M →ₗ[S] S ⊗[R] N)
    (h : ∀ m : M, ψ ((1 : S) ⊗ₜ[R] m) ∈ LinearMap.range (TensorProduct.mk R S N 1)) :
    ∃ φ : M →ₗ[R] N, LinearMap.baseChange S φ = ψ := by
  -- the descended map, defined via the injectivity of `N → S ⊗ N`
  choose φ hφ using fun m ↦ h m
  simp only [TensorProduct.mk_apply] at hφ
  have hinj := Module.FaithfullyFlat.tensorProduct_mk_injective (A := R) (B := S) N
  refine ⟨⟨⟨φ, fun m₁ m₂ ↦ ?_⟩, fun r m ↦ ?_⟩, ?_⟩
  · apply hinj
    simp only [TensorProduct.mk_apply]
    rw [hφ (m₁ + m₂), tmul_add, tmul_add, hφ m₁, hφ m₂, map_add]
  · apply hinj
    simp only [TensorProduct.mk_apply, RingHom.id_apply]
    rw [hφ (r • m), tmul_smul, tmul_smul, hφ m, LinearMap.map_smul_of_tower]
  · ext m
    simpa using hφ m

/-- API lemma used in the proof of Proposition 3.1.4 (part (1),
iff form): a linear map after faithfully flat base change descends if and only if its
values on the generators `1 ⊗ m` satisfy the Amitsur equalizer condition. This is the
exact affine cocycle criterion for the fullness part of fpqc descent of module
homomorphisms. -/
theorem LinearMap.exists_baseChange_eq_iff [Module.FaithfullyFlat R S]
    (ψ : S ⊗[R] M →ₗ[S] S ⊗[R] N) :
    (∃ φ : M →ₗ[R] N, LinearMap.baseChange S φ = ψ) ↔
      ∀ m : M, (1 : S) ⊗ₜ[R] ψ ((1 : S) ⊗ₜ[R] m) =
        LinearMap.lTensor S (TensorProduct.mk R S N 1) (ψ ((1 : S) ⊗ₜ[R] m)) := by
  constructor
  · rintro ⟨φ, rfl⟩ m
    apply (Module.FaithfullyFlat.exists_one_tmul_eq_iff
      (R := R) (S := S) (M := N) _).mp
    exact ⟨φ m, by simp⟩
  · intro h
    apply LinearMap.exists_baseChange_eq ψ
    intro m
    obtain ⟨n, hn⟩ := (Module.FaithfullyFlat.exists_one_tmul_eq_iff
      (R := R) (S := S) (M := N) _).mpr (h m)
    exact ⟨n, hn⟩

/-- Affine-case lemma used in the proof of Proposition 3.1.4 (part (2),
affine form): for a faithfully flat ring map, extension of scalars to modules equipped
with an ordinary overlap isomorphism satisfying the identity and cocycle conditions is
an equivalence. Thus every affine module descent datum in the literal sense used by the
book is effective. -/
theorem ModuleCat.isEquivalence_affineStandardDescentFunctor_of_faithfullyFlat
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : RingHom.FaithfullyFlat f) :
    (ModuleCat.affineStandardDescentFunctor f).IsEquivalence :=
  ModuleCat.affineStandardDescentFunctor_isEquivalence f hf

open CategoryTheory Limits

namespace SheafOfModules

variable {C D : Type u} [Category C] [Category D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Mapping a finite presentation by a colimit-preserving functor which carries the
unit module to the unit module preserves finiteness. -/
lemma Presentation.map_isFinite {M : SheafOfModules.{u} R} (P : Presentation M)
    [P.IsFinite] (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S)
    [PreservesColimitsOfSize.{u, u} F]
    (e : unit S ≅ F.obj (unit R)) : (P.map F e).IsFinite := by
  constructor
  · constructor
    simpa only [Presentation.map_generators_I] using
      (inferInstance : Finite P.generators.I)
  · constructor
    simpa only [Presentation.map_relations_I] using
      (inferInstance : Finite P.relations.I)

end SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory Limits

variable {X Y : Scheme.{u}}

/-- Mapping a finite presentation by a colimit-preserving functor which carries the
unit module to the unit module preserves finiteness of the presentation. -/
lemma presentationMap_isFinite {M : X.Modules} (P : SheafOfModules.Presentation M)
    [P.IsFinite] (F : X.Modules ⥤ Y.Modules) [PreservesColimitsOfSize.{u, u} F]
    (e : SheafOfModules.unit Y.ringCatSheaf ≅
      F.obj (SheafOfModules.unit X.ringCatSheaf)) : (P.map F e).IsFinite := by
  exact P.map_isFinite F e

/-- Let $f \colon X \to Y$ be a morphism of schemes. The canonical map
$f^* \mathcal{O}_Y \to \mathcal{O}_X$ is an isomorphism. (Mathlib records this only for open
immersions, as `AlgebraicGeometry.Scheme.Modules.restrictUnitIso`.) -/
noncomputable def pullbackUnitIso (f : X ⟶ Y) :
    (Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  haveI : IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) := inferInstance
  asIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)

set_option backward.isDefEq.respectTransparency.types false in
/-- Let $f \colon X \to Y$ be a morphism of schemes and $V \subseteq Y$ an open subscheme.
Restricting $f^* \mathcal{M}$ to $f^{-1}(V)$ agrees with pulling back $\mathcal{M}|_V$ along
the induced morphism $f^{-1}(V) \to V$. -/
noncomputable def pullbackMorphismRestrictIso (f : X ⟶ Y) (V : Y.Opens) :
    Modules.pullback f ⋙ Modules.pullback (f ⁻¹ᵁ V).ι ≅
      Modules.pullback V.ι ⋙ Modules.pullback (f ∣_ V) :=
  Modules.pullbackComp _ _ ≪≫
    Modules.pullbackCongr (morphismRestrict_ι f V).symm ≪≫
    (Modules.pullbackComp _ _).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- Let $f \colon X \to Y$ be a morphism of schemes and $\mathcal{M}$ an
$\mathcal{O}_Y$-module equipped with a presentation. Then $f^* \mathcal{M}$ inherits a
presentation, since $f^*$ preserves colimits and sends $\mathcal{O}_Y$ to $\mathcal{O}_X$.
(Compare `AlgebraicGeometry.Scheme.Modules.presentationRestrict`, the case of an open
immersion.) -/
noncomputable def presentationPullback (f : X ⟶ Y) {M : Y.Modules}
    (P : SheafOfModules.Presentation M) :
    SheafOfModules.Presentation ((Modules.pullback f).obj M) :=
  have : PreservesColimitsOfSize.{u, u} (Modules.pullback f) := inferInstance
  P.map (Modules.pullback f) (pullbackUnitIso f).symm

/-- Pullback preserves finiteness of a chosen presentation. -/
instance presentationPullback_isFinite (f : X ⟶ Y) {M : Y.Modules}
    (P : SheafOfModules.Presentation M) [P.IsFinite] :
    (presentationPullback f P).IsFinite := by
  dsimp [presentationPullback]
  exact presentationMap_isFinite P _ _

/-- A finite global presentation gives a finite-presentation sheaf.  This packages the
trivial-cover construction `Presentation.quasicoherentData`; the proof works directly
with its generator and relation index types, avoiding fragile typeclass search on the
definitionally equal over-sites `J.over (id U)` and `J.over U`. -/
theorem isFinitePresentation_of_presentation {M : X.Modules}
    (P : SheafOfModules.Presentation M) [P.IsFinite] : M.IsFinitePresentation := by
  apply SheafOfModules.IsFinitePresentation.mk (C := X.Opens)
  refine ⟨P.quasicoherentData, ?_⟩
  constructor
  intro U
  let hP := (inferInstance : P.IsFinite)
  exact {
    isFiniteType_generators := {
      finite := by
        change Finite P.generators.I
        exact hP.isFiniteType_generators.finite }
    isFiniteType_relations := {
      finite := by
        change Finite P.relations.I
        exact hP.isFiniteType_relations.finite } }

/-- Convert a presentation on the over-site of an open `U` into a presentation of the
restriction to the corresponding open subscheme. -/
noncomputable def presentationRestrictOfOver (M : X.Modules) (U : X.Opens)
    (P : SheafOfModules.Presentation (M.over U)) :
    SheafOfModules.Presentation (M.restrict U.ι) := by
  let e := Modules.overEquiv U
  letI : e.functor.IsLeftAdjoint := e.isLeftAdjoint_functor
  have hcolim : PreservesColimitsOfSize.{u, u} e.functor := inferInstance
  let η : SheafOfModules.unit U.toScheme.ringCatSheaf ≅
      e.functor.obj (SheafOfModules.unit (X.ringCatSheaf.over U)) :=
    (Modules.restrictUnitIso U.ι).symm ≪≫
      ((Modules.overFunctorEquiv U).app (SheafOfModules.unit X.ringCatSheaf)).symm
  let iso : e.functor.obj (M.over U) ≅ M.restrict U.ι :=
    (Modules.overFunctorEquiv U).app M
  let mapped := @SheafOfModules.Presentation.map _ _ _ _ _ _ _ _ _ _ _ _ _
    P e.functor hcolim η
  exact @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _
    iso.hom iso.isIso_hom mapped

/-- Restricting a finite presentation from an open over-site preserves its finite
generator and relation types. -/
instance presentationRestrictOfOver_isFinite (M : X.Modules) (U : X.Opens)
    (P : SheafOfModules.Presentation (M.over U)) [P.IsFinite] :
    (presentationRestrictOfOver M U P).IsFinite := by
  let hP := (inferInstance : P.IsFinite)
  exact {
    isFiniteType_generators := {
      finite := by
        change Finite P.generators.I
        exact hP.isFiniteType_generators.finite }
    isFiniteType_relations := {
      finite := by
        change Finite P.relations.I
        exact hP.isFiniteType_relations.finite } }

/-- Let $X$ be a scheme, $\mathcal{M}$ an $\mathcal{O}_X$-module and $(U_i)$ an open cover of
$X$ such that each restriction $\mathcal{M}|_{U_i}$ admits a presentation. Then $\mathcal{M}$
is quasi-coherent. This is the converse of
`AlgebraicGeometry.Scheme.Modules.exists_isOpenCover_presentation`. -/
theorem isQuasicoherent_of_isOpenCover (M : X.Modules) {ι : Type u} (U : ι → X.Opens)
    (hU : TopologicalSpace.IsOpenCover U)
    (pres : ∀ i, SheafOfModules.Presentation (M.restrict (U i).ι)) :
    M.IsQuasicoherent := by
  have hcov : (_root_.Opens.grothendieckTopology (X : Type u)).CoversTop U := by
    rw [_root_.Opens.coversTop_iff]; exact hU
  -- transport each presentation from `M.restrict (U i).ι` to `M.over (U i)`
  have hqc : ∀ i, (M.over (U i)).IsQuasicoherent := fun i ↦ by
    let e := Modules.overEquiv (U i)
    let oe := Modules.overFunctorEquiv (U i)
    have : PreservesColimitsOfSize.{u, u} e.inverse := inferInstance
    let η : SheafOfModules.unit (X.ringCatSheaf.over (U i)) ≅
        e.inverse.obj (SheafOfModules.unit (U i).toScheme.ringCatSheaf) :=
      e.unitIso.app _ ≪≫
        e.inverse.mapIso (oe.app (SheafOfModules.unit X.ringCatSheaf) ≪≫
          Modules.restrictUnitIso (U i).ι)
    let iso : e.inverse.obj (M.restrict (U i).ι) ≅ M.over (U i) :=
      e.inverse.mapIso (oe.app M).symm ≪≫ (e.unitIso.app _).symm
    exact (SheafOfModules.Presentation.ofIsIso.{u, u, u} iso.hom
      ((pres i).map e.inverse η)).isQuasicoherent
  exact SheafOfModules.IsQuasicoherent.of_coversTop M U hcov

/-- Finite presentation is local on an open cover when finite presentations of all
restrictions are supplied explicitly. -/
theorem isFinitePresentation_of_isOpenCover (M : X.Modules) {ι : Type u}
    (U : ι → X.Opens) (hU : TopologicalSpace.IsOpenCover U)
    (pres : ∀ i, SheafOfModules.Presentation (M.restrict (U i).ι))
    [hpres : ∀ i, (pres i).IsFinite] : M.IsFinitePresentation := by
  have hcov : (_root_.Opens.grothendieckTopology (X : Type u)).CoversTop U := by
    rw [_root_.Opens.coversTop_iff]
    exact hU
  let overPresentation (i : ι) : SheafOfModules.Presentation (M.over (U i)) := by
    let e := Modules.overEquiv (U i)
    let oe := Modules.overFunctorEquiv (U i)
    let η : SheafOfModules.unit (X.ringCatSheaf.over (U i)) ≅
        e.inverse.obj (SheafOfModules.unit (U i).toScheme.ringCatSheaf) :=
      e.unitIso.app _ ≪≫
        e.inverse.mapIso (oe.app (SheafOfModules.unit X.ringCatSheaf) ≪≫
          Modules.restrictUnitIso (U i).ι)
    let iso : e.inverse.obj (M.restrict (U i).ι) ≅ M.over (U i) :=
      e.inverse.mapIso (oe.app M).symm ≪≫ (e.unitIso.app _).symm
    exact SheafOfModules.Presentation.ofIsIso.{u, u, u} iso.hom
      ((pres i).map e.inverse η)
  let q : M.QuasicoherentData.{u} := {
    I := ι
    X := U
    coversTop := hcov
    presentation := overPresentation }
  apply SheafOfModules.IsFinitePresentation.mk (C := X.Opens)
  refine ⟨q, ?_⟩
  constructor
  intro i
  let hp := hpres i
  exact {
    isFiniteType_generators := {
      finite := by
        change Finite (pres i).generators.I
        exact hp.isFiniteType_generators.finite }
    isFiniteType_relations := {
      finite := by
        change Finite (pres i).relations.I
        exact hp.isFiniteType_relations.finite } }

/-- Finite type is local on an open cover when finite families of generating sections
of all restrictions are supplied explicitly. -/
theorem isFiniteType_of_isOpenCover_generatingSections (M : X.Modules) {ι : Type u}
    (U : ι → X.Opens) (hU : TopologicalSpace.IsOpenCover U)
    (generators : ∀ i, (M.restrict (U i).ι).GeneratingSections)
    [hgenerators : ∀ i, (generators i).IsFiniteType] : M.IsFiniteType := by
  have hcov : (_root_.Opens.grothendieckTopology (X : Type u)).CoversTop U := by
    rw [_root_.Opens.coversTop_iff]
    exact hU
  let overGenerators (i : ι) : (M.over (U i)).GeneratingSections := by
    let e := Modules.overEquiv (U i)
    let oe := Modules.overFunctorEquiv (U i)
    let η : SheafOfModules.unit (X.ringCatSheaf.over (U i)) ≅
        e.inverse.obj (SheafOfModules.unit (U i).toScheme.ringCatSheaf) :=
      e.unitIso.app _ ≪≫
        e.inverse.mapIso (oe.app (SheafOfModules.unit X.ringCatSheaf) ≪≫
          Modules.restrictUnitIso (U i).ι)
    let iso : e.inverse.obj (M.restrict (U i).ι) ≅ M.over (U i) :=
      e.inverse.mapIso (oe.app M).symm ≪≫ (e.unitIso.app _).symm
    exact ((generators i).map e.inverse η).ofEpi iso.hom
  let q : M.LocalGeneratorsData.{u} := {
    I := ι
    X := U
    coversTop := hcov
    generators := overGenerators }
  apply SheafOfModules.IsFiniteType.mk (C := X.Opens)
  refine ⟨q, ?_⟩
  constructor
  intro i
  dsimp [q, overGenerators]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-- Let $f \colon X \to Y$ be a morphism of schemes and $\mathcal{M}$ a quasi-coherent
$\mathcal{O}_Y$-module. Then $f^* \mathcal{M}$ is a quasi-coherent $\mathcal{O}_X$-module.
(Mathlib has this only for open immersions,
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_restrictFunctor`.) -/
-- A global instance, mirroring Mathlib's `isQuasicoherent_restrictFunctor`: the key is
-- syntactically `IsQuasicoherent ((pullback f).obj M)`, so it fires only on pullbacks.
instance isQuasicoherent_pullback (f : X ⟶ Y) (M : Y.Modules) [M.IsQuasicoherent] :
    ((Modules.pullback f).obj M).IsQuasicoherent := by
  obtain ⟨ι, V, pres, hV, -⟩ := M.exists_isOpenCover_presentation
  refine isQuasicoherent_of_isOpenCover _ (fun i ↦ f ⁻¹ᵁ V i) ?_ (fun i ↦ ?_)
  · -- preimages of an open cover form an open cover
    rw [TopologicalSpace.IsOpenCover] at hV ⊢
    rw [← Scheme.Hom.preimage_iSup, hV, Scheme.Hom.preimage_top]
  · -- transport the presentation of `M|_{V i}` along base change
    refine SheafOfModules.Presentation.ofIsIso.{u, u, u}
      ((Modules.pullback (f ∣_ V i)).map
            ((Modules.restrictFunctorIsoPullback (V i).ι).app M).hom ≫
          ((pullbackMorphismRestrictIso f (V i)).app M).inv ≫
          ((Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ V i).ι).app _).inv) ?_
    exact presentationPullback (f ∣_ V i) (pres i)

set_option backward.isDefEq.respectTransparency.types false in
/-- Pullback along an arbitrary morphism of schemes preserves finite presentation of
quasicoherent module sheaves. -/
instance isFinitePresentation_pullback (f : X ⟶ Y) (M : Y.Modules)
    [M.IsFinitePresentation] :
    ((Modules.pullback f).obj M).IsFinitePresentation := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  let pres (i : q.I) : SheafOfModules.Presentation
      (((Modules.pullback f).obj M).restrict (f ⁻¹ᵁ q.X i).ι) := by
    refine SheafOfModules.Presentation.ofIsIso.{u, u, u}
      ((Modules.pullback (f ∣_ q.X i)).map
            ((Modules.restrictFunctorIsoPullback (Scheme.Opens.ι (q.X i))).app M).hom ≫
          ((pullbackMorphismRestrictIso f (q.X i)).app M).inv ≫
          ((Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ q.X i).ι).app _).inv) ?_
    exact presentationPullback (f ∣_ q.X i)
      (presentationRestrictOfOver M (q.X i) (q.presentation i))
  have hfin (i : q.I) : (pres i).IsFinite := by
    dsimp [pres]
    let hp := hq.isFinite_presentation i
    exact {
      isFiniteType_generators := {
        finite := by
          change Finite (q.presentation i).generators.I
          exact hp.isFiniteType_generators.finite }
      isFiniteType_relations := {
        finite := by
          change Finite (q.presentation i).relations.I
          exact hp.isFiniteType_relations.finite } }
  apply isFinitePresentation_of_isOpenCover _ (fun i ↦ f ⁻¹ᵁ q.X i) _ pres
  rw [TopologicalSpace.IsOpenCover]
  rw [← Scheme.Hom.preimage_iSup]
  have hcov := q.coversTop
  rw [_root_.Opens.coversTop_iff, TopologicalSpace.IsOpenCover] at hcov
  rw [hcov, Scheme.Hom.preimage_top]

/-- Quasi-coherence, viewed as a property of the objects of the categories
$\mathcal{O}_X\text{-Mod}$ attached to the pseudofunctor
`AlgebraicGeometry.Scheme.Modules.pseudofunctorToCat`. -/
def isQuasicoherentProperty : pseudofunctorToCat.{u}.ObjectProperty where
  prop X := SheafOfModules.isQuasicoherent X.as.unop.ringCatSheaf

/-- Quasi-coherence is stable under the pullback functors, so it cuts out a
sub-pseudofunctor of `AlgebraicGeometry.Scheme.Modules.pseudofunctorToCat`. -/
lemma isClosedUnderMapObj_isQuasicoherentProperty :
    isQuasicoherentProperty.{u}.IsClosedUnderMapObj where
  map_obj {X Y M} hM f := by
    have : M.IsQuasicoherent := hM
    exact isQuasicoherent_pullback f.as.unop M

/-- Quasi-coherence is closed under isomorphisms of `𝒪`-modules, pointwise in the base
scheme.  This is one of the three fields of `Pseudofunctor.ObjectProperty.IsLocal`, the
hypothesis needed to deduce that `quasicoherentPseudofunctor` is a stack from the
corresponding statement for the ambient pseudofunctor of modules. -/
lemma isClosedUnderIsomorphisms_isQuasicoherentProperty :
    isQuasicoherentProperty.{u}.IsClosedUnderIsomorphisms where
  isClosedUnderIsomorphisms X := inferInstanceAs
    (SheafOfModules.isQuasicoherent X.as.unop.ringCatSheaf).IsClosedUnderIsomorphisms

attribute [local instance] isClosedUnderMapObj_isQuasicoherentProperty
attribute [local instance] isClosedUnderIsomorphisms_isQuasicoherentProperty

/-- The fibered category of quasi-coherent sheaves: the pseudofunctor sending a scheme $X$ to
the full subcategory $\mathrm{QCoh}(X)$ of quasi-coherent $\mathcal{O}_X$-modules, and a
morphism $f$ to the pullback functor $f^*$. -/
noncomputable def quasicoherentPseudofunctor :
    Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat :=
  isQuasicoherentProperty.fullsubcategory

/-! ### The affine pullback / extension-of-scalars bridge -/

/-- Pushforward along a morphism between affine schemes preserves quasi-coherence.

This packages the affine case proved by Mathlib's
`AlgebraicGeometry.isIso_fromTildeΓ_pushforward` in the form needed to restrict the
pullback/pushforward adjunction to quasi-coherent modules. -/
lemma isQuasicoherent_pushforward_Spec {R S : CommRingCat.{u}} (f : R ⟶ S)
    (M : (Spec S).Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pushforward (Spec.map f)).obj M).IsQuasicoherent := by
  haveI hM : IsIso (Scheme.Modules.fromTildeΓ M) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  let hpush := @isIso_fromTildeΓ_pushforward R S f M hM
  letI : IsIso (Scheme.Modules.fromTildeΓ
      ((Scheme.Modules.pushforward (Spec.map f)).obj M)) := hpush
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    (asIso (Scheme.Modules.fromTildeΓ
      ((Scheme.Modules.pushforward (Spec.map f)).obj M))) inferInstance

/-- The pushforward functor on affine quasi-coherent modules. -/
noncomputable def quasicoherentPushforward {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ Scheme.Modules.pushforward (Spec.map f)) fun M => by
      letI : M.obj.IsQuasicoherent := M.property
      exact isQuasicoherent_pushforward_Spec f M.obj

/-- Scalar multiplication on global sections of affine pushforward is restriction of scalars. -/
lemma smul_pushforward_Spec {R S : CommRingCat.{u}} (f : R ⟶ S)
    (M : (Spec S).Modules) (r : R) (x : Γ(M, ⊤)) :
    r • (show Γ((Scheme.Modules.pushforward (Spec.map f)).obj M, ⊤) from x) =
      f.hom r • x := by
  rw [Scheme.Modules.smul_Spec_def, Scheme.Modules.smul_Spec_def]
  change (Spec.map f).appTop ((Scheme.ΓSpecIso R).inv r) • x =
    (Scheme.ΓSpecIso S).inv (f.hom r) • x
  congr 1
  simpa only [← CommRingCat.comp_apply] using
    (congrArg (fun k : R ⟶ Γ(Spec S, ⊤) => k.hom r)
      (Scheme.ΓSpecIso_inv_naturality f)).symm

/-- On an affine tilde module, global sections after pushforward identify with restriction of
scalars. -/
noncomputable def pushforwardGammaIsoApp {R S : CommRingCat.{u}} (f : R ⟶ S)
    (M : ModuleCat.{u} S) :
    (moduleSpecΓFunctor (R := R)).obj
        ((Scheme.Modules.pushforward (Spec.map f)).obj ((tilde.functor S).obj M)) ≅
      (ModuleCat.restrictScalars f.hom).obj M := by
  let e : (ModuleCat.restrictScalars f.hom).obj M ≅
      (moduleSpecΓFunctor (R := R)).obj
        ((Scheme.Modules.pushforward (Spec.map f)).obj ((tilde.functor S).obj M)) :=
    LinearEquiv.toModuleIso (X₁ := (ModuleCat.restrictScalars f.hom).obj M)
      (X₂ := (moduleSpecΓFunctor (R := R)).obj
        ((Scheme.Modules.pushforward (Spec.map f)).obj ((tilde.functor S).obj M)))
      { __ := (tilde.isoTop M).toLinearEquiv.toAddEquiv
        map_smul' := by
          intro r m
          change (tilde.isoTop M).hom (f.hom r • (show M from m)) = _
          rw [(tilde.isoTop M).hom.hom.map_smul]
          exact (smul_pushforward_Spec f ((tilde.functor S).obj M) r _).symm }
  exact e.symm

/-- Global sections conjugate affine quasi-coherent pushforward to restriction of scalars. -/
noncomputable def pushforwardGammaIso {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (tilde.functor S) ⋙ Scheme.Modules.pushforward (Spec.map f) ⋙
        moduleSpecΓFunctor (R := R) ≅
      ModuleCat.restrictScalars f.hom :=
  NatIso.ofComponents (pushforwardGammaIsoApp f) (fun {M N} g => by
    apply ModuleCat.hom_ext
    ext x
    change (tilde.toTildeΓNatIso.inv.app N)
        ((moduleSpecΓFunctor (R := S)).map ((tilde.functor S).map g) x) =
      g ((tilde.toTildeΓNatIso.inv.app M) x)
    exact ConcreteCategory.congr_hom
      (tilde.toTildeΓNatIso.inv.naturality g) x)

/-- Componentwise form of the affine pushforward/restriction-of-scalars comparison. -/
noncomputable def pushforwardTildeIsoApp {R S : CommRingCat.{u}} (f : R ⟶ S)
    (M : ModuleCat.{u} S) :
    (Scheme.Modules.pushforward (Spec.map f)).obj ((tilde.functor S).obj M) ≅
      (tilde.functor R).obj ((ModuleCat.restrictScalars f.hom).obj M) := by
  letI hM : IsIso (Scheme.Modules.fromTildeΓ ((tilde.functor S).obj M)) := inferInstance
  letI hpush : IsIso (Scheme.Modules.fromTildeΓ
      ((Scheme.Modules.pushforward (Spec.map f)).obj ((tilde.functor S).obj M))) :=
    @isIso_fromTildeΓ_pushforward R S f ((tilde.functor S).obj M) hM
  exact (asIso (Scheme.Modules.fromTildeΓ
      ((Scheme.Modules.pushforward (Spec.map f)).obj ((tilde.functor S).obj M)))).symm ≪≫
    (tilde.functor R).mapIso (pushforwardGammaIsoApp f M)

/-- Under the affine equivalences, quasi-coherent pushforward is restriction of scalars. -/
noncomputable def tildeEquivPushforwardIso {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (tildeEquiv (R := S)).functor ⋙ quasicoherentPushforward f ≅
      ModuleCat.restrictScalars f.hom ⋙ (tildeEquiv (R := R)).functor := by
  apply ((SheafOfModules.isQuasicoherent
    (Spec R).ringCatSheaf).fullyFaithfulι.whiskeringRight _).preimageIso
  exact NatIso.ofComponents (fun M => pushforwardTildeIsoApp f M)
    (fun {X Y} g => by
      letI hX0 : IsIso (Scheme.Modules.fromTildeΓ ((tilde.functor S).obj X)) := inferInstance
      letI hY0 : IsIso (Scheme.Modules.fromTildeΓ ((tilde.functor S).obj Y)) := inferInstance
      letI hX : IsIso (Scheme.Modules.fromTildeΓ
          ((Scheme.Modules.pushforward (Spec.map f)).obj ((tilde.functor S).obj X))) :=
        @isIso_fromTildeΓ_pushforward R S f ((tilde.functor S).obj X) hX0
      letI hY : IsIso (Scheme.Modules.fromTildeΓ
          ((Scheme.Modules.pushforward (Spec.map f)).obj ((tilde.functor S).obj Y))) :=
        @isIso_fromTildeΓ_pushforward R S f ((tilde.functor S).obj Y) hY0
      dsimp [pushforwardTildeIsoApp, quasicoherentPushforward]
      change (Scheme.Modules.pushforward (Spec.map f)).map ((tilde.functor S).map g) ≫
          inv (Scheme.Modules.fromTildeΓ ((Scheme.Modules.pushforward (Spec.map f)).obj
            ((tilde.functor S).obj Y))) ≫
            (tilde.functor R).map (pushforwardGammaIsoApp f Y).hom =
        inv (Scheme.Modules.fromTildeΓ ((Scheme.Modules.pushforward (Spec.map f)).obj
            ((tilde.functor S).obj X))) ≫
          (tilde.functor R).map (pushforwardGammaIsoApp f X).hom ≫
            (tilde.functor R).map ((ModuleCat.restrictScalars f.hom).map g)
      rw [← Category.assoc]
      rw [show (Scheme.Modules.pushforward (Spec.map f)).map ((tilde.functor S).map g) ≫
          inv (Scheme.Modules.fromTildeΓ ((Scheme.Modules.pushforward (Spec.map f)).obj
            ((tilde.functor S).obj _))) =
        inv (Scheme.Modules.fromTildeΓ ((Scheme.Modules.pushforward (Spec.map f)).obj
            ((tilde.functor S).obj _))) ≫
          (tilde.functor R).map ((moduleSpecΓFunctor (R := R)).map
            ((Scheme.Modules.pushforward (Spec.map f)).map ((tilde.functor S).map g))) by
        apply (IsIso.comp_inv_eq _).2
        have hnat :
            (tilde.functor R).map ((moduleSpecΓFunctor (R := R)).map
                ((Scheme.Modules.pushforward (Spec.map f)).map ((tilde.functor S).map g))) ≫
              Scheme.Modules.fromTildeΓ ((Scheme.Modules.pushforward (Spec.map f)).obj
                ((tilde.functor S).obj Y)) =
            Scheme.Modules.fromTildeΓ ((Scheme.Modules.pushforward (Spec.map f)).obj
                ((tilde.functor S).obj X)) ≫
              (Scheme.Modules.pushforward (Spec.map f)).map ((tilde.functor S).map g) := by
          exact Scheme.Modules.fromTildeΓNatTrans.naturality
            ((Scheme.Modules.pushforward (Spec.map f)).map ((tilde.functor S).map g))
        rw [Category.assoc, hnat, IsIso.inv_hom_id_assoc]]
      simp only [← Functor.map_comp, Category.assoc]
      have hΓ :
          (moduleSpecΓFunctor (R := R)).map
              ((Scheme.Modules.pushforward (Spec.map f)).map ((tilde.functor S).map g)) ≫
            (pushforwardGammaIsoApp f Y).hom =
          (pushforwardGammaIsoApp f X).hom ≫
            (ModuleCat.restrictScalars f.hom).map g := by
        exact (pushforwardGammaIso f).hom.naturality g
      rw [hΓ])

/-- The pullback/pushforward adjunction restricts to affine quasi-coherent modules. -/
noncomputable def quasicoherentPullbackPushforwardAdjunction
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    isQuasicoherentProperty.map (Spec.map f).op.toLoc ⊣ quasicoherentPushforward f :=
  (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)).restrictFullyFaithful
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).fullyFaithfulι
    (SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf).fullyFaithfulι
    (Iso.refl _) (Iso.refl _)

/-- The adjunction obtained by conjugating affine quasi-coherent pullback through the source
affine equivalence. -/
noncomputable def pullbackConjugatedAdjunction {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (tildeEquiv (R := R)).functor ⋙ isQuasicoherentProperty.map (Spec.map f).op.toLoc ⊣
      quasicoherentPushforward f ⋙ (tildeEquiv (R := R)).inverse :=
  (tildeEquiv (R := R)).toAdjunction.comp (quasicoherentPullbackPushforwardAdjunction f)

/-- The extension/restriction adjunction followed by the target affine equivalence. -/
noncomputable def extendTildeAdjunction {R S : CommRingCat.{u}} (f : R ⟶ S) :
    ModuleCat.extendScalars f.hom ⋙ (tildeEquiv (R := S)).functor ⊣
      (tildeEquiv (R := S)).inverse ⋙ ModuleCat.restrictScalars f.hom :=
  (ModuleCat.extendRestrictScalarsAdj f.hom).comp (tildeEquiv (R := S)).toAdjunction

/-- The right adjoints in the two affine descriptions are naturally isomorphic. -/
noncomputable def quasicoherentRightAdjointIso {R S : CommRingCat.{u}} (f : R ⟶ S) :
    quasicoherentPushforward f ⋙ (tildeEquiv (R := R)).inverse ≅
      (tildeEquiv (R := S)).inverse ⋙ ModuleCat.restrictScalars f.hom :=
  (quasicoherentPushforward f ⋙ (tildeEquiv (R := R)).inverse).leftUnitor.symm ≪≫
  Functor.isoWhiskerRight (tildeEquiv (R := S)).counitIso.symm _ ≪≫
  Functor.associator _ _ _ ≪≫
  Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight (tildeEquivPushforwardIso f) _) ≪≫
  Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
  (Functor.associator _ _ _).symm ≪≫
  Functor.isoWhiskerLeft _ (tildeEquiv (R := R)).unitIso.symm ≪≫
  Functor.rightUnitor ((tildeEquiv (R := S)).inverse ⋙
    ModuleCat.restrictScalars f.hom)

/-- On affine schemes, pullback in the quasi-coherent pseudofunctor corresponds to extension
of scalars under `AlgebraicGeometry.tildeEquiv`. -/
noncomputable def tildeEquivMapIso {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (tildeEquiv (R := R)).functor ⋙
        isQuasicoherentProperty.map (Spec.map f).op.toLoc ≅
      ModuleCat.extendScalars f.hom ⋙ (tildeEquiv (R := S)).functor :=
  ((conjugateIsoEquiv (pullbackConjugatedAdjunction f) (extendTildeAdjunction f)).symm
    (quasicoherentRightAdjointIso f)).symm

/-- Affine quasi-coherent pullback is conjugate, through the affine equivalences, to extension
of scalars. -/
noncomputable def quasicoherentPullbackConjugationIso
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    isQuasicoherentProperty.map (Spec.map f).op.toLoc ≅
      (tildeEquiv (R := R)).inverse ⋙ ModuleCat.extendScalars f.hom ⋙
        (tildeEquiv (R := S)).functor :=
  (isQuasicoherentProperty.map (Spec.map f).op.toLoc).leftUnitor.symm ≪≫
    Functor.isoWhiskerRight (tildeEquiv (R := R)).counitIso.symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (tildeEquiv (R := R)).inverse (tildeEquivMapIso f) ≪≫
    (Functor.associator _ _ _).symm

/-- Faithfully flat affine pullback on quasi-coherent modules reflects isomorphisms. -/
lemma reflectsIsomorphisms_quasicoherentPullback_of_faithfullyFlat
    {R S : CommRingCat.{u}} (f : R ⟶ S) (hf : f.hom.FaithfullyFlat) :
    (isQuasicoherentProperty.map (Spec.map f).op.toLoc).ReflectsIsomorphisms := by
  letI : (ModuleCat.extendScalars f.hom).ReflectsIsomorphisms :=
    ModuleCat.reflectsIsomorphisms_extendScalars_of_faithfullyFlat hf
  apply reflectsIsomorphisms_of_iso (quasicoherentPullbackConjugationIso f).symm

/-- Affine quasi-coherent categories have the equalizers required by Beck's theorem. -/
lemma hasEqualizerOfIsCosplitPair_quasicoherentPullback
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    Comonad.HasEqualizerOfIsCosplitPair
      (isQuasicoherentProperty.map (Spec.map f).op.toLoc) := by
  letI : HasEqualizers (isQuasicoherentProperty.Obj (.mk (.op (Spec R)))) :=
    Adjunction.hasLimitsOfShape_of_equivalence (tildeEquiv (R := R)).inverse
  exact ⟨fun a b => HasLimitsOfShape.has_limit (parallelPair a b)⟩

/-- Faithfully flat affine quasi-coherent pullback preserves the equalizers required by Beck's
theorem. -/
lemma preservesLimitOfIsCosplitPair_quasicoherentPullback_of_faithfullyFlat
    {R S : CommRingCat.{u}} (f : R ⟶ S) (hf : f.hom.FaithfullyFlat) :
    Comonad.PreservesLimitOfIsCosplitPair
      (isQuasicoherentProperty.map (Spec.map f).op.toLoc) := by
  letI : PreservesFiniteLimits (ModuleCat.extendScalars f.hom) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf.flat
  refine ⟨?_⟩
  intro A B a b h
  apply preservesLimit_of_natIso (parallelPair a b)
    (quasicoherentPullbackConjugationIso f).symm

/-- Faithfully flat pullback between affine quasi-coherent categories is comonadic. -/
@[stacks 023S, instance_reducible]
noncomputable def comonadicQuasicoherentPullbackOfFaithfullyFlat
    {R S : CommRingCat.{u}} (f : R ⟶ S) (hf : f.hom.FaithfullyFlat) :
    ComonadicLeftAdjoint (isQuasicoherentProperty.map (Spec.map f).op.toLoc) := by
  letI : (isQuasicoherentProperty.map
      (Spec.map f).op.toLoc).ReflectsIsomorphisms :=
    reflectsIsomorphisms_quasicoherentPullback_of_faithfullyFlat f hf
  letI : Comonad.HasEqualizerOfIsCosplitPair
      (isQuasicoherentProperty.map (Spec.map f).op.toLoc) :=
    hasEqualizerOfIsCosplitPair_quasicoherentPullback f
  letI : Comonad.PreservesLimitOfIsCosplitPair
      (isQuasicoherentProperty.map (Spec.map f).op.toLoc) :=
    preservesLimitOfIsCosplitPair_quasicoherentPullback_of_faithfullyFlat f hf
  exact Comonad.comonadicOfHasPreservesFSplitEqualizersOfReflectsIsomorphisms
    (quasicoherentPullbackPushforwardAdjunction f)

/-- Over an affine target, effective fpqc descent reduces to effective descent for finite
affine flat refinements.  The prestack hypothesis is exactly what permits effectiveness to
ascend from the finer covering sieve to the original covering presieve.

This packages the topology/refinement part of the scheme-level reduction in Stacks Project
Tag 023S; the remaining input is effective descent for the finite affine family itself. -/
lemma isStackFor_fpqcPrecoverage_of_finite_affine_refinements
    [quasicoherentPseudofunctor.{u}.IsPrestack Scheme.fpqcTopology]
    {S : Scheme.{u}} [IsAffine S] {R : Presieve S}
    (hR : R ∈ Scheme.fpqcPrecoverage.coverings S)
    (h : ∀ (n : ℕ) (X : Fin n → Scheme.{u}) (p : ∀ i, X i ⟶ S),
      (∀ i, IsAffine (X i)) → (∀ i, Flat (p i)) →
        Presieve.ofArrows X p ∈ Scheme.fpqcPrecoverage.coverings S →
          quasicoherentPseudofunctor.{u}.IsStackFor (Presieve.ofArrows X p)) :
    quasicoherentPseudofunctor.{u}.IsStackFor R := by
  obtain ⟨n, X, p, hX, hp, hpR, hcover⟩ :=
    Scheme.exists_finite_affine_refinement_of_mem_fpqcPrecoverage hR
  have hrefines : Presieve.ofArrows X p ≤ (Sieve.generate R).arrows := by
    intro T q hq
    obtain ⟨i⟩ := hq
    exact hpR i
  have hgenerated :
      quasicoherentPseudofunctor.{u}.IsStackFor (Sieve.generate R).arrows :=
    Pseudofunctor.IsStackFor.of_le (F := quasicoherentPseudofunctor.{u})
      (h n X p hX hp hcover) (J := Scheme.fpqcTopology)
      (Precoverage.generate_mem_toGrothendieck hcover) hrefines
  exact (quasicoherentPseudofunctor.{u}.IsStackFor_generate_iff R).mp hgenerated

/-- To prove fpqc descent for quasi-coherent sheaves it is enough, and necessary, to prove
effective descent for every covering presieve in Mathlib's fpqc precoverage.  This exposes the
precise precoverage-level target used after affine refinement. -/
lemma isStack_quasicoherentPseudofunctor_iff_isStackFor_fpqcPrecoverage :
    quasicoherentPseudofunctor.{u}.IsStack Scheme.fpqcTopology ↔
      ∀ (S : Scheme.{u}) (R : Presieve S), R ∈ Scheme.fpqcPrecoverage.coverings S →
        quasicoherentPseudofunctor.{u}.IsStackFor R := by
  constructor
  · intro h S R hR
    letI : quasicoherentPseudofunctor.{u}.IsStack Scheme.fpqcTopology := h
    exact quasicoherentPseudofunctor.isStackFor R
      (Precoverage.generate_mem_toGrothendieck hR)
  · intro h
    exact Pseudofunctor.IsStack.of_precoverage h

open CategoryTheory.Bicategory

/-- Background definition for Proposition 3.1.4: quasi-coherent sheaves on affine
schemes, as a pseudofunctor on rings — the Spec-precomposition of the quasi-coherent
pseudofunctor, indexed as `ModuleCat.extendScalarsPseudofunctorOpOp`. -/
noncomputable abbrev quasicoherentSpecPseudofunctor :
    Pseudofunctor (LocallyDiscrete (CommRingCat.{u}ᵒᵖ)ᵒᵖ) Cat.{u, u + 1} :=
  Pseudofunctor.comp Scheme.Spec.op.toPseudofunctor quasicoherentPseudofunctor.{u}

/-- Background definition for Proposition 3.1.4: the adjunction-valued enhancement of
`quasicoherentSpecPseudofunctor` by the affine quasi-coherent pushforward functors. -/
noncomputable def quasicoherentSpecAdjPseudofunctor :
    Pseudofunctor (LocallyDiscrete (CommRingCat.{u}ᵒᵖ)ᵒᵖ)
      (Bicategory.Adj Cat.{u, u + 1}) :=
  Bicategory.Adj.adjPseudofunctorOfLeft quasicoherentSpecPseudofunctor.{u}
    (fun g ↦ (quasicoherentPushforward g.unop.unop).toCatHom)
    (fun g ↦ (quasicoherentPullbackPushforwardAdjunction g.unop.unop).toCat)

/-- Background definition for Proposition 3.1.4: the compositor of the affine
quasi-coherent pushforward functors. -/
noncomputable def quasicoherentPushforwardComp
    {R S' T : CommRingCat.{u}} (φ : R ⟶ S') (ψ : S' ⟶ T) :
    quasicoherentPushforward ψ ⋙ quasicoherentPushforward φ ≅
      quasicoherentPushforward (φ ≫ ψ) := by
  apply ((SheafOfModules.isQuasicoherent
    (Spec R).ringCatSheaf).fullyFaithfulι.whiskeringRight _).preimageIso
  exact NatIso.ofComponents
    (fun M ↦ (Scheme.Modules.pushforwardComp (Spec.map ψ) (Spec.map φ) ≪≫
      Scheme.Modules.pushforwardCongr (Spec.map_comp φ ψ).symm).app M.obj)
    (fun {M N} h ↦ (Scheme.Modules.pushforwardComp (Spec.map ψ) (Spec.map φ) ≪≫
      Scheme.Modules.pushforwardCongr (Spec.map_comp φ ψ).symm).hom.naturality h.hom)

/-- Background definition for Proposition 3.1.4: the unitor of the affine
quasi-coherent pushforward functors. -/
noncomputable def quasicoherentPushforwardId (R : CommRingCat.{u}) :
    quasicoherentPushforward (𝟙 R) ≅ 𝟭 _ := by
  apply ((SheafOfModules.isQuasicoherent
    (Spec R).ringCatSheaf).fullyFaithfulι.whiskeringRight _).preimageIso
  exact NatIso.ofComponents
    (fun M ↦ (Scheme.Modules.pushforwardCongr
        (show Spec.map (𝟙 R) = 𝟙 (Spec R) by simp) ≪≫
      Scheme.Modules.pushforwardId (Spec R)).app M.obj)
    (fun {M N} h ↦ (Scheme.Modules.pushforwardCongr
        (show Spec.map (𝟙 R) = 𝟙 (Spec R) by simp) ≪≫
      Scheme.Modules.pushforwardId (Spec R)).hom.naturality h.hom)

/-- API lemma used in the proof of Proposition 3.1.4: the underlying sheaf morphism of
a morphism of quasi-coherent modules is its image under the inclusion. -/
lemma isQuasicoherent_ι_map {X : Scheme.{u}}
    {M N : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory} (w : M ⟶ N) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.map w = w.hom := rfl

/-- API lemma used in the proof of Proposition 3.1.4: the same statement as
`isQuasicoherent_ι_map`, but in the `isQuasicoherentProperty` spelling produced by the
pseudofunctor.  The two spellings are definitionally equal and neither lemma matches a goal
written in the other, so both are needed; see this folder's INSIGHTS.md. -/
lemma qcProp_ι_map_hom {A : LocallyDiscrete Scheme.{u}ᵒᵖ}
    {M N : (isQuasicoherentProperty.prop A).FullSubcategory} (w : M ⟶ N) :
    (isQuasicoherentProperty.prop A).ι.map w = w.hom := rfl

/-- API lemma used in the proof of Proposition 3.1.4: the inclusion of quasi-coherent
modules commutes with the pullback, on objects.

This is the normalization that makes residual identity morphisms cancel in goals coming from
`Adjunction.conjugateEquiv_restrictFullyFaithful_comp_app`: without it the two sides of a
`𝟙 _ ≫ F.map (𝟙 _)` sit at definitionally equal but syntactically different objects, and
`Category.id_comp` never fires. -/
lemma qcProp_ι_obj_map_obj {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (X : (isQuasicoherentProperty.prop ⟨Opposite.op (Spec R)⟩).FullSubcategory) :
    (isQuasicoherentProperty.prop ⟨Opposite.op (Spec S)⟩).ι.obj
        ((isQuasicoherentProperty.map (Spec.map φ).op.toLoc).obj X) =
      (Scheme.Modules.pullback (Spec.map φ)).obj
        ((isQuasicoherentProperty.prop ⟨Opposite.op (Spec R)⟩).ι.obj X) := rfl

/-- API lemma used in the proof of Proposition 3.1.4: the unit of the affine
quasi-coherent adjunction is the restriction of the scheme-level unit. -/
lemma quasicoherentPullbackPushforwardAdjunction_unit_app_hom
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (M : (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory) :
    ((quasicoherentPullbackPushforwardAdjunction φ).unit.app M).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app M.obj := by
  have h := Adjunction.map_restrictFullyFaithful_unit_app
    (L := isQuasicoherentProperty.map (Spec.map φ).op.toLoc)
    (R := quasicoherentPushforward φ)
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).fullyFaithfulι
    (SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf).fullyFaithfulι
    (Iso.refl _) (Iso.refl _) M
  simp only [Iso.refl_hom, NatTrans.id_app] at h
  exact h

/-- API lemma used in the proof of Proposition 3.1.4: the counit of the affine
quasi-coherent adjunction is the restriction of the scheme-level counit. -/
lemma quasicoherentPullbackPushforwardAdjunction_counit_app_hom
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (M : (SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf).FullSubcategory) :
    ((quasicoherentPullbackPushforwardAdjunction φ).counit.app M).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).counit.app M.obj := by
  have h := Adjunction.map_restrictFullyFaithful_counit_app
    (L := isQuasicoherentProperty.map (Spec.map φ).op.toLoc)
    (R := quasicoherentPushforward φ)
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).fullyFaithfulι
    (SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf).fullyFaithfulι
    (Iso.refl _) (Iso.refl _) M
  simp only [Iso.refl_inv, NatTrans.id_app] at h
  refine h.trans ?_
  -- the two spellings of the source object agree only at default transparency
  show 𝟙 ((Scheme.Modules.pullback (Spec.map φ)).obj
        ((Scheme.Modules.pushforward (Spec.map φ)).obj M.obj)) ≫
      (Scheme.Modules.pullback (Spec.map φ)).map
          (𝟙 ((Scheme.Modules.pushforward (Spec.map φ)).obj M.obj)) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).counit.app M.obj =
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).counit.app M.obj
  simp

/-- Deferred input for Proposition 3.1.4 (restricted Beck–Chevalley, unit form): the
conjugate of the compositor of the Spec-precomposed quasi-coherent pseudofunctor at an
identity is the affine quasi-coherent pushforward unitor. -/
theorem conjugateEquiv_quasicoherentSpec_mapId
    (a : LocallyDiscrete (CommRingCat.{u}ᵒᵖ)ᵒᵖ) :
    conjugateEquiv Adjunction.id
      (quasicoherentPullbackPushforwardAdjunction (𝟙 a.as.unop.unop))
      (quasicoherentSpecPseudofunctor.{u}.mapId a).hom.toNatTrans =
      (quasicoherentPushforwardId a.as.unop.unop).inv := by
  -- Route: expand the conjugate by `conjugateEquiv_apply_app` (the `Adjunction.id`
  -- side gives a closed form), distribute all wrappers, push everything to the sheaf
  -- level, and close with the scheme-level
  -- `SheafOfModules.conjugateEquiv_pullbackId_hom` after substituting `Spec.map_id`.
  ext d
  simp only [conjugateEquiv_apply_app]
  simp only [Pseudofunctor.comp_mapId, Iso.trans_hom, Functor.toPseudofunctor_mapId,
    quasicoherentPseudofunctor, PrelaxFunctor.map₂Iso_eqToIso, eqToIso.hom,
    Pseudofunctor.ObjectProperty.fullsubcategory_mapId, Cat.Hom.isoMk_hom,
    Cat.Hom₂.comp_app, Cat.Hom₂.eqToHom_toNatTrans, NatTrans.toCatHom₂_toNatTrans,
    eqToHom_app, Pseudofunctor.ObjectProperty.mapId_hom_app, Functor.map_comp,
    CategoryTheory.Adjunction.id_counit, NatTrans.id_app]
  simp only [Functor.id_obj]
  simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
    quasicoherentPushforward, ObjectProperty.lift_map, Functor.comp_map]
  simp only [show ∀ (X Y : (SheafOfModules.isQuasicoherent
      (Spec a.as.unop.unop).ringCatSheaf).FullSubcategory) (w : X ⟶ Y),
      (SheafOfModules.isQuasicoherent
        (Spec a.as.unop.unop).ringCatSheaf).ι.map w = w.hom from fun _ _ _ ↦ rfl]
  simp only [ObjectProperty.homMk_hom]
  -- identify the restricted unit with the scheme-level unit
  have hunit : ((quasicoherentPullbackPushforwardAdjunction
      (𝟙 a.as.unop.unop)).unit.app d).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction
        (Spec.map (𝟙 a.as.unop.unop))).unit.app d.obj := by
    have h := Adjunction.map_restrictFullyFaithful_unit_app
      (L := isQuasicoherentProperty.map (Spec.map (𝟙 a.as.unop.unop)).op.toLoc)
      (R := quasicoherentPushforward (𝟙 a.as.unop.unop))
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (𝟙 a.as.unop.unop)))
      (SheafOfModules.isQuasicoherent
        (Spec a.as.unop.unop).ringCatSheaf).fullyFaithfulι
      (SheafOfModules.isQuasicoherent
        (Spec a.as.unop.unop).ringCatSheaf).fullyFaithfulι
      (Iso.refl _) (Iso.refl _) d
    simp only [Iso.refl_hom, NatTrans.id_app] at h
    exact h
  rw [hunit]
  simp only [show ∀ (X : (SheafOfModules.isQuasicoherent
      (Spec a.as.unop.unop).ringCatSheaf).FullSubcategory),
      (𝟙 X : X ⟶ X).hom = 𝟙 X.obj from fun _ ↦ rfl]
  simp only [Functor.comp_obj, Functor.id_obj]
  rw [show (pseudofunctorToCat.mapId
      (Scheme.Spec.op.toPseudofunctor.obj a)).hom.toNatTrans.app d.obj =
    (Scheme.Modules.pullbackId (Spec a.as.unop.unop)).hom.app d.obj from rfl]
  have heq : ∀ (X Y : (SheafOfModules.isQuasicoherent
      (Spec a.as.unop.unop).ringCatSheaf).FullSubcategory) (h : X = Y),
      (eqToHom h : X ⟶ Y).hom =
        eqToHom (congrArg ObjectProperty.FullSubcategory.obj h) := by
    rintro X Y rfl
    rfl
  simp only [heq]
  have hRHS : ((quasicoherentPushforwardId a.as.unop.unop).inv.app d).hom =
      (Scheme.Modules.pushforwardCongr
          (show Spec.map (𝟙 a.as.unop.unop) = 𝟙 (Spec a.as.unop.unop) by simp) ≪≫
        Scheme.Modules.pushforwardId (Spec a.as.unop.unop)).inv.app d.obj := rfl
  rw [hRHS]
  simp only [Iso.trans_inv, NatTrans.comp_app]
  rw! (castMode := .all) [show Spec.map (𝟙 (a.as.unop.unop)) =
    𝟙 (Spec a.as.unop.unop) from by simp]
  have hkey := congr_arg
    (fun (t : 𝟭 (Spec a.as.unop.unop).Modules ⟶
        Scheme.Modules.pushforward (𝟙 (Spec a.as.unop.unop))) ↦ t.app d.obj)
    (Scheme.Modules.conjugateEquiv_pullbackId_hom (Spec a.as.unop.unop))
  simp only [conjugateEquiv_apply_app, CategoryTheory.Adjunction.id_counit,
    NatTrans.id_app, Functor.id_obj] at hkey
  -- the pushforward comparison along a reflexivity proof is the identity
  have hcongr : ∀ (h : 𝟙 (Spec a.as.unop.unop) = 𝟙 (Spec a.as.unop.unop))
      (M : (Spec a.as.unop.unop).Modules),
      (Scheme.Modules.pushforwardCongr h).inv.app M = 𝟙 _ := by
    intro h M
    obtain rfl : h = rfl := Subsingleton.elim _ _
    ext U
    simp
  simp only [hcongr, Category.comp_id, eqToHom_refl, Category.assoc]
  exact hkey

/-- Deferred input for Proposition 3.1.4 (restricted Beck–Chevalley, composition form;
Stacks Project Tag 023S base-change comparison): the conjugate of the compositor of the
Spec-precomposed quasi-coherent pseudofunctor is the affine quasi-coherent pushforward
compositor. -/
theorem conjugateEquiv_quasicoherentSpec_mapComp
    {a b c : LocallyDiscrete (CommRingCat.{u}ᵒᵖ)ᵒᵖ} (f : a ⟶ b) (g : b ⟶ c) :
    conjugateEquiv
      ((quasicoherentPullbackPushforwardAdjunction f.as.unop.unop).comp
        (quasicoherentPullbackPushforwardAdjunction g.as.unop.unop))
      (quasicoherentPullbackPushforwardAdjunction (f ≫ g).as.unop.unop)
      (quasicoherentSpecPseudofunctor.{u}.mapComp f g).hom.toNatTrans =
      (quasicoherentPushforwardComp f.as.unop.unop g.as.unop.unop).hom := by
  -- Same route as `conjugateEquiv_quasicoherentSpec_mapId`: expand the conjugate,
  -- distribute the pseudofunctor wrappers, push everything to the sheaf level, and
  -- close with `SheafOfModules.conjugateEquiv_pullbackComp_inv` after substituting
  -- `Spec.map_comp`.  That whole reduction has been checked to work (the exact tactic
  -- chain and the three auxiliary `rfl`-lemmas it needs are recorded in this folder's
  -- COMMENTARY.md); the one blocking step is the final transport along `Spec.map_comp`,
  -- which reports `motive is not type correct` because a residual
  -- `(pushforward _).map (eqToHom ⋯).hom` depends on the term being rewritten and the
  -- rewrite of `(eqToHom h).hom` to `eqToHom (congrArg _ h)` — the step that cleared the
  -- analogous obstruction in the unit form — does not fire here.
  obtain ⟨f⟩ := f
  obtain ⟨g⟩ := g
  ext d
  simp only [conjugateEquiv_apply_app]
  simp only [Pseudofunctor.comp_mapComp, Iso.trans_hom,
    Functor.toPseudofunctor_mapComp, quasicoherentPseudofunctor,
    PrelaxFunctor.map₂Iso_eqToIso, eqToIso.hom,
    Pseudofunctor.ObjectProperty.fullsubcategory_mapComp, Cat.Hom.isoMk_hom,
    Cat.Hom₂.comp_app, Cat.Hom₂.eqToHom_toNatTrans, NatTrans.toCatHom₂_toNatTrans,
    eqToHom_app, Pseudofunctor.ObjectProperty.mapComp_hom_app, Functor.map_comp,
    CategoryTheory.Adjunction.comp_counit_app]
  simp only [Functor.comp_obj, Functor.id_obj]
  simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
    quasicoherentPushforward, ObjectProperty.lift_map, Functor.comp_map]
  sorry

/-- Background definition for Proposition 3.1.4: the component of the tilde comparison
at one ring, as a morphism of adjunctions from extension/restriction of scalars to
affine quasi-coherent pullback/pushforward. -/
noncomputable def tildeAdjApp (R : (CommRingCat.{u}ᵒᵖ)ᵒᵖ) :
    ModuleCat.extendRestrictScalarsAdjPseudofunctor.{u}.obj ⟨R⟩ ⟶
      quasicoherentSpecAdjPseudofunctor.{u}.obj ⟨R⟩ :=
  .mk (tildeEquiv (R := R.unop.unop)).toAdjunction.toCat

/-- Background definition for Proposition 3.1.4: the naturality constraint of the tilde
comparison. Its left component is `tildeEquivMapIso`, its right component is
`quasicoherentRightAdjointIso`, and the mate condition holds because the former is
defined as the conjugate of the latter. -/
noncomputable def tildeAdjNaturality {a b : LocallyDiscrete (CommRingCat.{u}ᵒᵖ)ᵒᵖ}
    (f : a ⟶ b) :
    ModuleCat.extendRestrictScalarsAdjPseudofunctor.{u}.map f ≫ tildeAdjApp b.as ≅
      tildeAdjApp a.as ≫ quasicoherentSpecAdjPseudofunctor.{u}.map f := by
  refine Bicategory.Adj.iso₂Mk
    (Cat.Hom.isoMk (tildeEquivMapIso f.as.unop.unop).symm)
    (Cat.Hom.isoMk (quasicoherentRightAdjointIso f.as.unop.unop)) ?_
  apply Cat.Hom₂.ext
  rw [show (ModuleCat.extendRestrictScalarsAdjPseudofunctor.{u}.map f ≫
      tildeAdjApp b.as).adj =
    (extendTildeAdjunction f.as.unop.unop).toCat from
      CategoryTheory.Adjunction.toCat_comp_toCat _ _]
  rw [show (tildeAdjApp a.as ≫ quasicoherentSpecAdjPseudofunctor.{u}.map f).adj =
    (pullbackConjugatedAdjunction f.as.unop.unop).toCat from
      CategoryTheory.Adjunction.toCat_comp_toCat _ _]
  rw [Bicategory.toNatTrans_conjugateEquiv]
  simp only [CategoryTheory.Adjunction.ofCat_toCat]
  exact congrArg Iso.hom (Equiv.apply_symm_apply
    (conjugateIsoEquiv (pullbackConjugatedAdjunction f.as.unop.unop)
      (extendTildeAdjunction f.as.unop.unop))
    (quasicoherentRightAdjointIso f.as.unop.unop))

@[simp]
lemma tildeAdjNaturality_hom_τl {a b : LocallyDiscrete (CommRingCat.{u}ᵒᵖ)ᵒᵖ}
    (f : a ⟶ b) :
    (tildeAdjNaturality f).hom.τl =
      (Cat.Hom.isoMk (tildeEquivMapIso f.as.unop.unop).symm).hom := rfl

@[simp]
lemma quasicoherentSpecAdjPseudofunctor_mapId_hom_τl
    (a : LocallyDiscrete (CommRingCat.{u}ᵒᵖ)ᵒᵖ) :
    (quasicoherentSpecAdjPseudofunctor.{u}.mapId a).hom.τl =
      (quasicoherentSpecPseudofunctor.{u}.mapId a).hom := rfl

@[simp]
lemma quasicoherentSpecAdjPseudofunctor_mapComp_hom_τl
    {a b c : LocallyDiscrete (CommRingCat.{u}ᵒᵖ)ᵒᵖ} (f : a ⟶ b) (g : b ⟶ c) :
    (quasicoherentSpecAdjPseudofunctor.{u}.mapComp f g).hom.τl =
      (quasicoherentSpecPseudofunctor.{u}.mapComp f g).hom := rfl

@[simp]
lemma extendRestrictScalarsAdjPseudofunctor_mapId_hom_τl
    (a : LocallyDiscrete (CommRingCat.{u}ᵒᵖ)ᵒᵖ) :
    (ModuleCat.extendRestrictScalarsAdjPseudofunctor.{u}.mapId a).hom.τl =
      (ModuleCat.extendScalarsPseudofunctorOpOp.{u}.mapId a).hom := rfl

@[simp]
lemma extendRestrictScalarsAdjPseudofunctor_mapComp_hom_τl
    {a b c : LocallyDiscrete (CommRingCat.{u}ᵒᵖ)ᵒᵖ} (f : a ⟶ b) (g : b ⟶ c) :
    (ModuleCat.extendRestrictScalarsAdjPseudofunctor.{u}.mapComp f g).hom.τl =
      (ModuleCat.extendScalarsPseudofunctorOpOp.{u}.mapComp f g).hom := rfl

/-- Deferred input for Proposition 3.1.4: the unit coherence of the tilde comparison.
Route: after `Bicategory.Adj.hom₂_ext` and the `τl` projections, conjugate the equation
through the composite adjunctions (`conjugateIsoEquiv` is injective); the mates of the
players are `quasicoherentRightAdjointIso` (by construction of `tildeEquivMapIso`),
`ModuleCat.conjugateEquiv_extendScalarsId_hom`, and
`conjugateEquiv_quasicoherentSpec_mapId`. -/
theorem tildeAdj_naturality_id (a : LocallyDiscrete (CommRingCat.{u}ᵒᵖ)ᵒᵖ) :
    (tildeAdjNaturality (𝟙 a)).hom ≫
        tildeAdjApp a.as ◁ (quasicoherentSpecAdjPseudofunctor.{u}.mapId a).hom =
      (ModuleCat.extendRestrictScalarsAdjPseudofunctor.{u}.mapId a).hom ▷
          tildeAdjApp a.as ≫
        (λ_ (tildeAdjApp a.as)).hom ≫ (ρ_ (tildeAdjApp a.as)).inv := by
  sorry

/-- Deferred input for Proposition 3.1.4: the composition coherence of the tilde
comparison — pseudonaturality of the tilde functor with respect to composition of
ring morphisms.  Route: as for `tildeAdj_naturality_id`, with
`ModuleCat.conjugateEquiv_extendScalarsComp_hom` and
`conjugateEquiv_quasicoherentSpec_mapComp` as the compositor mates, and
`conjugateEquiv_comp`/`conjugateEquiv_whiskerLeft`/`conjugateEquiv_whiskerRight`/
`conjugateEquiv_associator_hom` to distribute the conjugation over the composite. -/
theorem tildeAdj_naturality_comp
    {a b c : LocallyDiscrete (CommRingCat.{u}ᵒᵖ)ᵒᵖ} (f : a ⟶ b) (g : b ⟶ c) :
    (tildeAdjNaturality (f ≫ g)).hom ≫
        tildeAdjApp a.as ◁ (quasicoherentSpecAdjPseudofunctor.{u}.mapComp f g).hom =
      (ModuleCat.extendRestrictScalarsAdjPseudofunctor.{u}.mapComp f g).hom ▷
          tildeAdjApp c.as ≫
        (α_ _ _ _).hom ≫
          ModuleCat.extendRestrictScalarsAdjPseudofunctor.{u}.map f ◁
            (tildeAdjNaturality g).hom ≫
        (α_ _ _ _).inv ≫
          (tildeAdjNaturality f).hom ▷ quasicoherentSpecAdjPseudofunctor.{u}.map g ≫
        (α_ _ _ _).hom := by
  sorry

/-- Background definition for Proposition 3.1.4: the tilde comparison as a strong
transformation of adjunction-valued pseudofunctors on rings. -/
noncomputable def tildeAdjStrongTrans :
    Pseudofunctor.StrongTrans ModuleCat.extendRestrictScalarsAdjPseudofunctor.{u}
      quasicoherentSpecAdjPseudofunctor.{u} where
  app a := tildeAdjApp a.as
  naturality f := tildeAdjNaturality f
  naturality_naturality {a b f g} θ := by
    obtain rfl : f = g := LocallyDiscrete.eq_of_hom θ
    obtain rfl : θ = 𝟙 f := Subsingleton.elim _ _
    simp
  naturality_id a := tildeAdj_naturality_id a
  naturality_comp f g := tildeAdj_naturality_comp f g

/-- Deferred input for Proposition 3.1.4 (the Zariski half of the affine-singleton
criterion): the fibered category of quasi-coherent sheaves is a stack for the Zariski
topology.  The content is the classical gluing of sheaves of modules along an open
cover — objects glue and morphisms glue, with quasi-coherence supplied by
`isQuasicoherent_of_isOpenCover`.  The open immersions of a Zariski covering family
must first be compared with the restriction functors of
`Mathlib.AlgebraicGeometry.Modules.Sheaf` (`Scheme.Modules.restrictFunctor`). -/
theorem isStack_quasicoherentPseudofunctor_zariskiTopology :
    quasicoherentPseudofunctor.{u}.IsStack Scheme.zariskiTopology := by
  sorry

/-- Proposition 3.1.4, affine faithfully flat half of the affine-singleton criterion
(Stacks Project Tag 023S): effective descent for quasi-coherent modules along one
faithfully flat morphism of affine schemes.  The proof transports the affine
module-descent equivalence `ModuleCat.affineStandardDescentFunctor_isEquivalence`
along the tilde comparison `tildeAdjStrongTrans` and Spec-precomposition. -/
theorem isStackFor_quasicoherentPseudofunctor_singleton_of_faithfullyFlat
    {R S : CommRingCat.{u}} (q : R ⟶ S) (hflat : Flat (Spec.map q))
    (hsurj : Surjective (Spec.map q)) :
    quasicoherentPseudofunctor.{u}.IsStackFor (.singleton (Spec.map q)) := by
  have hff : q.hom.FaithfullyFlat := by
    rw [← flat_and_surjective_SpecMap_iff]
    exact ⟨hflat, hsurj⟩
  have h₁ : (ModuleCat.extendScalarsPseudofunctorOpOp.{u}.toDescentData
      (fun _ : Unit ↦ q.op)).IsEquivalence :=
    ModuleCat.affineStandardDescentFunctor_isEquivalence q.hom hff
  let _ : ∀ a, ((Bicategory.Adj.leftStrongTrans
      tildeAdjStrongTrans.{u}).app a).toFunctor.IsEquivalence := fun a ↦
    inferInstanceAs ((tildeEquiv (R := a.as.unop.unop)).functor.IsEquivalence)
  have h₂ : ((Bicategory.Adj.leftPseudofunctor
      quasicoherentSpecAdjPseudofunctor.{u}).toDescentData
        (fun _ : Unit ↦ q.op)).IsEquivalence := by
    rw [← Pseudofunctor.isEquivalence_toDescentData_iff
      (Bicategory.Adj.leftStrongTrans tildeAdjStrongTrans.{u})
      (fun _ : Unit ↦ q.op)]
    exact h₁
  let _ : ∀ a, ((Bicategory.Adj.adjPseudofunctorOfLeftComparison
      quasicoherentSpecPseudofunctor.{u}
      (fun g ↦ (quasicoherentPushforward g.unop.unop).toCatHom)
      (fun g ↦ (quasicoherentPullbackPushforwardAdjunction
        g.unop.unop).toCat)).app a).toFunctor.IsEquivalence := fun a ↦
    inferInstanceAs ((𝟭 _).IsEquivalence)
  have h₃ : (quasicoherentSpecPseudofunctor.{u}.toDescentData
      (fun _ : Unit ↦ q.op)).IsEquivalence := by
    rw [← Pseudofunctor.isEquivalence_toDescentData_iff
      (Bicategory.Adj.adjPseudofunctorOfLeftComparison
        quasicoherentSpecPseudofunctor.{u}
        (fun g ↦ (quasicoherentPushforward g.unop.unop).toCatHom)
        (fun g ↦ (quasicoherentPullbackPushforwardAdjunction g.unop.unop).toCat))
      (fun _ : Unit ↦ q.op)]
    exact h₂
  have h₄ : (Pseudofunctor.comp Scheme.Spec.op.toPseudofunctor
      quasicoherentPseudofunctor.{u}).IsStackFor
        (Presieve.ofArrows (fun _ : Unit ↦ Opposite.op S) (fun _ : Unit ↦ q.op)) := by
    rw [Pseudofunctor.isStackFor_ofArrows_iff]
    exact h₃
  let sq : ∀ _ _ : Unit, Limits.ChosenPullback q.op q.op := fun _ _ ↦
    Limits.ChosenPullback.ofHasPullback q.op q.op
  let sq₃ : ∀ i j k : Unit, Limits.ChosenPullback₃ (sq i j) (sq j k) (sq i k) :=
    fun i j k ↦ Limits.ChosenPullback₃.ofHasPullback (sq i j) (sq j k) (sq i k)
  have h₅ := Pseudofunctor.isStackFor_of_precomp_of_preservesChosenPullbacks
    Scheme.Spec quasicoherentPseudofunctor.{u} sq sq₃
    (fun i j ↦ Scheme.Spec.map_isPullback (sq i j).isPullback)
    (fun i j k ↦ Scheme.Spec.map_isPullback
      (sq₃ i j k).chosenPullback.isPullback)
    h₄
  have hsieve : Presieve.ofArrows (fun _ : Unit ↦ Scheme.Spec.obj (Opposite.op S))
      (fun _ : Unit ↦ Scheme.Spec.map q.op) =
        Presieve.singleton (Scheme.Spec.map q.op) :=
    Presieve.ofArrows_pUnit (Scheme.Spec.map q.op)
  rw [hsieve] at h₅
  exact h₅

/-- **Proposition 3.1.4** (`prop:fpqc-descent-for-quasi-coherent-sheaves`) (scheme-level
form of parts (1) and (2); cf. Equation 3.1.5): fpqc descent for
quasi-coherent sheaves. The fibered category $X \mapsto \mathrm{QCoh}(X)$,
$f \mapsto f^*$, is a stack for the fpqc topology on schemes. Descent data for
quasi-coherent sheaves along an fpqc covering is thus effective, and morphisms of
quasi-coherent sheaves glue.

The proof reduces along the affine-singleton criterion
(`AlgebraicGeometry.isStack_propQCTopology_iff_affine_singletons`, cf. Exercise 3.5.5)
to the two deferred inputs above: the Zariski stack condition and effective descent
along a single faithfully flat morphism of affine schemes. -/
theorem isStack_quasicoherentPseudofunctor :
    quasicoherentPseudofunctor.{u}.IsStack Scheme.fpqcTopology := by
  let _ : (Scheme.propQCTopology
      (@Flat : MorphismProperty Scheme.{u})).Subcanonical := by
    rw [← Scheme.fpqcTopology_eq_propQCTopology]
    infer_instance
  rw [Scheme.fpqcTopology_eq_propQCTopology]
  rw [isStack_propQCTopology_iff_affine_singletons (P := @Flat)]
  refine ⟨isStack_quasicoherentPseudofunctor_zariskiTopology, ?_⟩
  intro R S q hq hs
  exact isStackFor_quasicoherentPseudofunctor_singleton_of_faithfullyFlat q hq hs

end AlgebraicGeometry.Scheme.Modules

end PropFpqcDescentForQuasiCoherentSheaves
