module

public import StacksAndModuli.«Section3.1-Descent».«part3.1.4b-effective-descent-schemes»
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import StacksAndModuli.API.ModuleDescent
public import StacksProject.Algebra.DescendingProperties.«lemma-descent-Noetherian»
public import StacksProject.Algebra.DescendingProperties.«lemma-descent-reduced»
public import StacksProject.Algebra.DescendingProperties.«lemma-descent-normal»
public import StacksProject.Algebra.AscendingProperties.«lemma-reduced-goes-up»
public import StacksProject.Algebra.AscendingProperties.«lemma-smooth-normal»
public import StacksProject.Algebra.AscendingProperties.«lemma-smooth-regular»
public import StacksProject.Algebra.RegularFiniteGlDim.«lemma-flat-under-regular»
public import StacksProject.Algebra.SmoothOverField.«lemma-characterize-smooth-over-field»
public import StacksProject.Descent.FpqcLocalSource.«lemma-flat-fpqc-local-source»
public import StacksProject.Descent.FiniteAndSmoothnessProperties.«lemma-flat-finitely-presented-permanence-algebra»
public import StacksProject.Morphisms.EtaleSmoothUnramified.«lemma-etale-smooth-unramified»
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Descent
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Fpqc descent for properties of modules, rings, and schemes

This module formalizes Proposition 3.1.18
(`prop:fpqc-descent-for-properties-of-quasi-coherent-sheaves`), Lemma 3.1.19
(`lem:algebra-regular-descends-under-fppf`), Proposition 3.1.21
(`prop:fpqc-descent-for-properties-of-schemes`), Proposition 3.1.22
(`prop:fpqc-descent-for-properties-on-source`), Proposition 3.1.23
(`prop:fppf-smooth-local-properties-of-schemes`), and Remark 3.1.24
(`rmk:normality-ascends`) of §3.1 (Descent theory, `sec:descent-theory`) of *Stacks and
Moduli*. (Remark 3.1.25,
`rmk:completion-normal`, is not yet formalized; per-label completeness is tracked in this
folder's STATUS.md.)

The statements about quasi-coherent sheaves are formalized at the level of modules over
rings (their affine-local form, to which the book's proof reduces): for a faithfully flat
ring map `R → S`, a property of an `R`-module `M` holds if and only if it holds for the base
change `S ⊗[R] M`. Most descent directions are recalls from Mathlib, or obligations for
`stacks-project-lean` where Mathlib has no counterpart; the ascent directions are base-change
instances from Mathlib.

Main results include the fpqc-cover descent theorems
`Scheme.isLocallyNoetherian_of_fpqcCover`, `Scheme.isNoetherian_of_fpqcCover`,
`Scheme.isReduced_of_fpqcCover`, `Scheme.isNormalRing_stalk_of_fpqcCover`,
and `Scheme.forall_isRegularLocalRing_stalk_of_fpqcCover`; the corrected fppf
source-descent theorems
`Smooth.of_fppf_precomp` and `Etale.of_fppf_precomp`; and the four smooth-local
equivalences of Proposition 3.1.23.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

-- `@Smooth` and friends are declared in Mathlib under this option; without it the
-- `MorphismProperty` instances for them do not unify here.
set_option backward.isDefEq.respectTransparency.types false

section PropFpqcDescentForPropertiesOfQuasiCoherentSheaves

open TensorProduct

universe u v w

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
variable [Module.FaithfullyFlat R S]
variable {M N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Affine API lemma used in the proof of Proposition 3.1.18
(part (1), injectivity): a homomorphism of modules is injective if and only if its base
change along a faithfully flat ring map is injective. (Affine-local form of fpqc descent
for properties of quasi-coherent sheaves.) -/
theorem LinearMap.injective_baseChange_iff (f : M →ₗ[R] N) :
    Function.Injective (LinearMap.baseChange S f) ↔ Function.Injective f := by
  rw [← Module.FaithfullyFlat.lTensor_injective_iff_injective R S f]
  rfl

/-- Affine API lemma used in the proof of Proposition 3.1.18
(part (1), surjectivity): a homomorphism of modules is surjective if and only if its base
change along a faithfully flat ring map is surjective. -/
theorem LinearMap.surjective_baseChange_iff (f : M →ₗ[R] N) :
    Function.Surjective (LinearMap.baseChange S f) ↔ Function.Surjective f := by
  rw [← Module.FaithfullyFlat.lTensor_surjective_iff_surjective R S f]
  rfl

/-- Affine API lemma used in the proof of Proposition 3.1.18
(part (1), isomorphism): a homomorphism of modules is bijective if and only if its base
change along a faithfully flat ring map is bijective. -/
theorem LinearMap.bijective_baseChange_iff (f : M →ₗ[R] N) :
    Function.Bijective (LinearMap.baseChange S f) ↔ Function.Bijective f := by
  rw [← Module.FaithfullyFlat.lTensor_bijective_iff_bijective R S f]
  rfl

/-- Affine API lemma used in the proof of Proposition 3.1.18
(part (2), finite type): a module is finitely generated if and only if its base change
along a faithfully flat ring map is. -/
theorem Module.Finite.baseChange_iff :
    Module.Finite S (S ⊗[R] M) ↔ Module.Finite R M :=
  ⟨fun _ ↦ Module.Finite.of_baseChange_faithfullyFlat R M S, fun _ ↦ inferInstance⟩

/-- Affine API lemma used in the proof of Proposition 3.1.18
(part (2), finite presentation): a module is finitely presented if and only if its base
change along a faithfully flat ring map is. -/
theorem Module.FinitePresentation.baseChange_iff :
    Module.FinitePresentation S (S ⊗[R] M) ↔ Module.FinitePresentation R M :=
  ⟨fun _ ↦ Module.FinitePresentation.of_baseChange_faithfullyFlat R M S, fun _ ↦ inferInstance⟩

/- Affine API lemma used in the proof of Proposition 3.1.18
(part (2), flatness): a module is flat if and only if its base change along a faithfully
flat ring map is; this is Mathlib's `Module.Flat.iff_flat_tensorProduct`. -/
example : Module.Flat S (S ⊗[R] M) ↔ Module.Flat R M :=
  Module.Flat.iff_flat_tensorProduct R M S

/-- Affine API lemma used in the proof of Proposition 3.1.18
(part (2), vector bundles): a finite module is projective (equivalently, a vector bundle
on the spectrum: finite locally free) if and only if its base change along a faithfully
flat ring map is. -/
theorem Module.Projective.baseChange_iff [Module.Finite R M] :
    Module.Projective S (S ⊗[R] M) ↔ Module.Projective R M :=
  ⟨fun _ ↦ Module.Projective.of_baseChange_faithfullyFlat R M S, fun _ ↦ inferInstance⟩

/- Affine API lemma used in the proof of Proposition 3.1.18
(part (3)): for a quasi-coherent sheaf on an `R`-scheme — affine-locally, a module `N`
over an `R`-algebra `A` — flatness of `N` over the base `R` holds if and only if the
pullback to the faithfully flat cover, affine-locally the module `S ⊗[R] N`, is flat over
`S`. (Only the module structure over the base intervenes.) -/
example (A : Type*) [CommRing A] [Algebra R A] (N : Type*) [AddCommGroup N] [Module R N]
    [Module A N] [IsScalarTower R A N] :
    Module.Flat S (S ⊗[R] N) ↔ Module.Flat R N :=
  Module.Flat.iff_flat_tensorProduct R N S

end PropFpqcDescentForPropertiesOfQuasiCoherentSheaves

section LemAlgebraRegularDescendsUnderFppf

open AlgebraicGeometry CategoryTheory Limits

universe u

/- **Lemma 3.1.19** (`lem:algebra-regular-descends-under-fppf`): let $A \to B$ be a flat
local homomorphism of noetherian local rings. If $B$ is regular, then so is $A$. Stacks
00OF (`algebra-lemma-flat-under-regular`); absent from Mathlib and an outstanding
obligation for `stacks-project-lean`. -/
example (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A]
    [IsNoetherianRing A] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    [IsRegularLocalRing B] : IsRegularLocalRing A :=
  isRegularLocalRing_of_flat_of_isLocalHom A B

/-- Scheme-level API generalization of Lemma 3.1.19 (stalkwise
form; Stacks Project, Tag 00OF): regularity of local rings descends along a surjective
flat morphism of schemes.  This stalkwise formulation is used because Mathlib does not yet
package regular schemes as a scheme-level class.

For every `y : Y`, choose a point `x : X` above it.  The induced local homomorphism
`𝒪_{Y,y} → 𝒪_{X,x}` is flat, so regularity of the latter local ring descends to the
former. -/
@[stacks 00OF "scheme-level stalkwise form"]
theorem AlgebraicGeometry.Scheme.isRegularLocalRing_stalk_of_surjective_of_flat
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f] [Flat f]
    (hX : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) (y : Y) :
    IsRegularLocalRing (Y.presheaf.stalk y) := by
  obtain ⟨x, hx⟩ := f.surjective y
  subst y
  algebraize [(f.stalkMap x).hom]
  letI : IsRegularLocalRing (X.presheaf.stalk x) := hX x
  letI : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := Flat.stalkMap f x
  letI : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap f x) (f.toLRSHom.prop x)
  letI : IsNoetherianRing (Y.presheaf.stalk (f x)) :=
    isNoetherianRing_of_faithfullyFlat
      (R := Y.presheaf.stalk (f x)) (S := X.presheaf.stalk x)
  exact isRegularLocalRing_of_flat_of_isLocalHom
    (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)

/-- The canonical map from the fiber of a composite `g ≫ f` to the corresponding fiber of
`f`.  It is the base change of `g` by the residue-field point of the base. -/
noncomputable def AlgebraicGeometry.Scheme.Hom.precompFiberMap
    {X' X Y : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y) (y : Y) :
    (g ≫ f).fiber y ⟶ f.fiber y :=
  pullback.lift ((g ≫ f).fiberι y ≫ g) ((g ≫ f).fiberToSpecResidueField y) (by
    rw [Category.assoc, (g ≫ f).fiber_fac])

@[reassoc (attr := simp)]
theorem AlgebraicGeometry.Scheme.Hom.precompFiberMap_fiberι
    {X' X Y : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y) (y : Y) :
    g.precompFiberMap f y ≫ f.fiberι y = (g ≫ f).fiberι y ≫ g :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem AlgebraicGeometry.Scheme.Hom.precompFiberMap_fiberToSpecResidueField
    {X' X Y : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y) (y : Y) :
    g.precompFiberMap f y ≫ f.fiberToSpecResidueField y =
      (g ≫ f).fiberToSpecResidueField y :=
  pullback.lift_snd _ _ _

/-- The canonical square exhibiting `precompFiberMap g f y` as the base change of `g`. -/
theorem AlgebraicGeometry.Scheme.Hom.isPullback_precompFiberMap
    {X' X Y : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y) (y : Y) :
    IsPullback ((g ≫ f).fiberι y) (g.precompFiberMap f y) g (f.fiberι y) := by
  have hout : IsPullback ((g ≫ f).fiberι y) ((g ≫ f).fiberToSpecResidueField y)
      (g ≫ f) (Y.fromSpecResidueField y) := IsPullback.of_hasPullback _ _
  rw [← g.precompFiberMap_fiberToSpecResidueField f y] at hout
  exact hout.of_bot (g.precompFiberMap_fiberι f y).symm
    (IsPullback.of_hasPullback f (Y.fromSpecResidueField y))

instance AlgebraicGeometry.Scheme.Hom.precompFiberMap_surjective
    {X' X Y : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y) (y : Y) [Surjective g] :
    Surjective (g.precompFiberMap f y) :=
  MorphismProperty.of_isPullback (g.isPullback_precompFiberMap f y) inferInstance

instance AlgebraicGeometry.Scheme.Hom.precompFiberMap_flat
    {X' X Y : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y) (y : Y) [Flat g] :
    Flat (g.precompFiberMap f y) :=
  MorphismProperty.of_isPullback (g.isPullback_precompFiberMap f y) inferInstance

instance AlgebraicGeometry.Scheme.Hom.precompFiberMap_quasiCompact
    {X' X Y : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y) (y : Y) [QuasiCompact g] :
    QuasiCompact (g.precompFiberMap f y) :=
  MorphismProperty.of_isPullback (g.isPullback_precompFiberMap f y) inferInstance

instance AlgebraicGeometry.Scheme.Hom.precompFiberMap_locallyOfFinitePresentation
    {X' X Y : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y) (y : Y)
    [LocallyOfFinitePresentation g] : LocallyOfFinitePresentation (g.precompFiberMap f y) :=
  MorphismProperty.of_isPullback (g.isPullback_precompFiberMap f y) inferInstance

instance AlgebraicGeometry.Scheme.Hom.precompFiberMap_smooth
    {X' X Y : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y) (y : Y) [Smooth g] :
    Smooth (g.precompFiberMap f y) :=
  MorphismProperty.of_isPullback (g.isPullback_precompFiberMap f y) inferInstance

/-- Regularity of all local rings of a fiber descends from the fiber of an fpqc
precomposition.  This is the fiberwise form of Tag 00OF used in smooth permanence. -/
theorem AlgebraicGeometry.Scheme.Hom.isRegularLocalRing_stalk_fiber_of_fpqc_precomp
    {X' X Y : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y) [Surjective g] [Flat g]
    (y : Y) (h : ∀ z : (g ≫ f).fiber y,
      IsRegularLocalRing (((g ≫ f).fiber y).presheaf.stalk z))
    (x : f.fiber y) : IsRegularLocalRing ((f.fiber y).presheaf.stalk x) :=
  Scheme.isRegularLocalRing_stalk_of_surjective_of_flat (g.precompFiberMap f y) h x

/-- Every local ring of a scheme smooth over a field is regular.  This is the
scheme-theoretic form of the regularity of localizations of a smooth algebra. -/
theorem AlgebraicGeometry.Scheme.isRegularLocalRing_stalk_of_smooth_toSpec_field
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) [Smooth p]
    (x : X) : IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let e : K ≃+* Γ(Spec (.of K), ⊤) :=
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  letI : Field Γ(Spec (.of K), ⊤) := (e.symm.isField (Field.toIsField K)).toField
  let φ := p.appLE (⊤ : (Spec (.of K)).Opens) V (by simp)
  have hφ : φ.hom.Smooth := p.smooth_appLE (isAffineOpen_top _) hV (by simp)
  algebraize [φ.hom]
  letI : Algebra.Smooth Γ(Spec (.of K), ⊤) Γ(X, V) := by
    rw [← RingHom.smooth_algebraMap]
    exact hφ
  letI : IsNoetherianRing Γ(X, V) :=
    Algebra.FiniteType.isNoetherianRing Γ(Spec (.of K), ⊤) Γ(X, V)
  letI : Algebra Γ(X, V) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxV⟩
  let q := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  letI : q.IsPrime := (hV.primeIdealOf ⟨x, hxV⟩).isPrime
  letI : IsLocalization.AtPrime (X.presheaf.stalk x) q :=
    hV.isLocalization_stalk ⟨x, hxV⟩
  exact isRegularLocalRing_of_smooth_of_isLocalization_atPrime
    Γ(Spec (.of K), ⊤) Γ(X, V) q (X.presheaf.stalk x)

/-- Geometric regularity of a smooth scheme over a field: after any extension of the base
field, every local ring of the scalar extension remains regular. -/
theorem AlgebraicGeometry.Scheme.isRegularLocalRing_stalk_baseChange_of_smooth_toSpec_field
    {K L : Type u} [Field K] [Field L] [Algebra K L] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) [Smooth p]
    (x : (CategoryTheory.Limits.pullback p
      (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme.{u})) :
    IsRegularLocalRing
      (((CategoryTheory.Limits.pullback p
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme.{u})).presheaf.stalk x) := by
  let q : (CategoryTheory.Limits.pullback p
      (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme.{u}) ⟶ Spec (.of L) :=
    pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap K L)))
  letI : Smooth q :=
    MorphismProperty.pullback_snd p (Spec.map (CommRingCat.ofHom (algebraMap K L))) inferInstance
  exact Scheme.isRegularLocalRing_stalk_of_smooth_toSpec_field q x

/-- The canonical map between the base changes of `g ≫ p` and `p` by the same morphism. -/
noncomputable def AlgebraicGeometry.Scheme.Hom.precompBaseChangeMap
    {X' X S T : Scheme.{u}} (g : X' ⟶ X) (p : X ⟶ S) (t : T ⟶ S) :
    pullback (g ≫ p) t ⟶ pullback p t :=
  pullback.lift (pullback.fst (g ≫ p) t ≫ g) (pullback.snd (g ≫ p) t) (by
    rw [Category.assoc, pullback.condition])

@[reassoc (attr := simp)]
theorem AlgebraicGeometry.Scheme.Hom.precompBaseChangeMap_fst
    {X' X S T : Scheme.{u}} (g : X' ⟶ X) (p : X ⟶ S) (t : T ⟶ S) :
    g.precompBaseChangeMap p t ≫ pullback.fst p t = pullback.fst (g ≫ p) t ≫ g :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem AlgebraicGeometry.Scheme.Hom.precompBaseChangeMap_snd
    {X' X S T : Scheme.{u}} (g : X' ⟶ X) (p : X ⟶ S) (t : T ⟶ S) :
    g.precompBaseChangeMap p t ≫ pullback.snd p t = pullback.snd (g ≫ p) t :=
  pullback.lift_snd _ _ _

/-- `precompBaseChangeMap` is the base change of the precomposed morphism. -/
theorem AlgebraicGeometry.Scheme.Hom.isPullback_precompBaseChangeMap
    {X' X S T : Scheme.{u}} (g : X' ⟶ X) (p : X ⟶ S) (t : T ⟶ S) :
    IsPullback (pullback.fst (g ≫ p) t) (g.precompBaseChangeMap p t) g
      (pullback.fst p t) := by
  have hout : IsPullback (pullback.fst (g ≫ p) t) (pullback.snd (g ≫ p) t)
      (g ≫ p) t := IsPullback.of_hasPullback _ _
  rw [← g.precompBaseChangeMap_snd p t] at hout
  exact hout.of_bot (g.precompBaseChangeMap_fst p t).symm
    (IsPullback.of_hasPullback p t)

instance AlgebraicGeometry.Scheme.Hom.precompBaseChangeMap_surjective
    {X' X S T : Scheme.{u}} (g : X' ⟶ X) (p : X ⟶ S) (t : T ⟶ S) [Surjective g] :
    Surjective (g.precompBaseChangeMap p t) :=
  MorphismProperty.of_isPullback (g.isPullback_precompBaseChangeMap p t) inferInstance

instance AlgebraicGeometry.Scheme.Hom.precompBaseChangeMap_flat
    {X' X S T : Scheme.{u}} (g : X' ⟶ X) (p : X ⟶ S) (t : T ⟶ S) [Flat g] :
    Flat (g.precompBaseChangeMap p t) :=
  MorphismProperty.of_isPullback (g.isPullback_precompBaseChangeMap p t) inferInstance

/-- If an fpqc precomposition is smooth, then every local ring of every fiber of the
original morphism is regular.  This is the regularity half of smooth descent on fibers. -/
theorem AlgebraicGeometry.Scheme.Hom.isRegularLocalRing_stalk_fiber_of_smooth_fpqc_precomp
    {X' X Y : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y) [Surjective g] [Flat g]
    [Smooth (g ≫ f)] (y : Y) (x : f.fiber y) :
    IsRegularLocalRing ((f.fiber y).presheaf.stalk x) := by
  apply g.isRegularLocalRing_stalk_fiber_of_fpqc_precomp f y
  intro z
  -- Bind the fiber map with its target written as `Spec (.of _)`, as elsewhere in this file:
  -- `fiberToSpecResidueField` is a plain `def` for `pullback.snd`, so stating the type here is
  -- what lets instance search see through it.
  let q : (g ≫ f).fiber y ⟶ Spec (.of (Y.residueField y)) :=
    (g ≫ f).fiberToSpecResidueField y
  letI : Smooth q :=
    MorphismProperty.pullback_snd (g ≫ f) (Y.fromSpecResidueField y) inferInstance
  exact Scheme.isRegularLocalRing_stalk_of_smooth_toSpec_field q z

/-- Geometric regularity of the lower fibers in smooth fpqc permanence: after every field
extension of `κ(y)`, all local rings of the extended fiber remain regular. -/
theorem AlgebraicGeometry.Scheme.Hom.isRegularLocalRing_stalk_geometricFiber_of_smooth_fpqc_precomp
    {X' X Y : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y) [Surjective g] [Flat g]
    [Smooth (g ≫ f)] (y : Y) (L : Type u) [Field L] [Algebra (Y.residueField y) L]
    (x : (pullback (f.fiberToSpecResidueField y)
      (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) L))) : Scheme.{u})) :
    IsRegularLocalRing
      ((pullback (f.fiberToSpecResidueField y)
        (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) L))) : Scheme.{u})
        |>.presheaf.stalk x) := by
  let h := g.precompFiberMap f y
  let q := f.fiberToSpecResidueField y
  let t := Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) L))
  have hs : Smooth (h ≫ q) := by
    rw [g.precompFiberMap_fiberToSpecResidueField f y]
    exact MorphismProperty.pullback_snd (g ≫ f) (Y.fromSpecResidueField y) inferInstance
  letI : Smooth (h ≫ q) := hs
  apply Scheme.isRegularLocalRing_stalk_of_surjective_of_flat
    (h.precompBaseChangeMap q t) (y := x)
  intro z
  exact Scheme.isRegularLocalRing_stalk_baseChange_of_smooth_toSpec_field
    (K := Y.residueField y) (L := L) (h ≫ q) z

/-- An affine scheme locally of finite presentation over an algebraically closed field is
smooth when all of its local rings are regular. -/
theorem AlgebraicGeometry.Scheme.smooth_toSpec_of_isAlgClosed_of_regular_stalks_affine
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsAffine X]
    (p : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation p]
    (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) : Smooth p := by
  rw [HasRingHomProperty.iff_of_isAffine (P := @Smooth)]
  let e : K ≃+* Γ(Spec (.of K), ⊤) :=
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  letI : Field Γ(Spec (.of K), ⊤) := (e.symm.isField (Field.toIsField K)).toField
  letI : IsAlgClosed Γ(Spec (.of K), ⊤) :=
    IsAlgClosed.of_ringEquiv (k := K) Γ(Spec (.of K), ⊤) e
  have hpfin : (p.appTop).hom.FinitePresentation :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)).mp inferInstance
  algebraize [(p.appTop).hom]
  letI : Algebra.FinitePresentation Γ(Spec (.of K), ⊤) Γ(X, ⊤) := hpfin
  change Algebra.Smooth Γ(Spec (.of K), ⊤) Γ(X, ⊤)
  apply smooth_of_isAlgClosed_of_forall_isRegularLocalRing
  intro q hq
  letI : q.IsPrime := hq
  let x := (isAffineOpen_top X).fromSpec ⟨q, inferInstance⟩
  letI : Algebra Γ(X, ⊤) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, Set.mem_univ x⟩
  letI : IsLocalization.AtPrime (X.presheaf.stalk x) q :=
    (isAffineOpen_top X).isLocalization_stalk' ⟨q, inferInstance⟩ (by simp)
  letI : IsRegularLocalRing (X.presheaf.stalk x) := hreg x
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q)
      (X.presheaf.stalk x)).toRingEquiv.symm

/-- A scheme locally of finite presentation over an algebraically closed field is smooth
when all of its local rings are regular. -/
theorem AlgebraicGeometry.Scheme.smooth_toSpec_of_isAlgClosed_of_forall_isRegularLocalRing
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation p]
    (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) : Smooth p := by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @Smooth) X.affineCover]
  intro i
  apply Scheme.smooth_toSpec_of_isAlgClosed_of_regular_stalks_affine
  intro x
  letI : IsRegularLocalRing (X.presheaf.stalk ((X.affineCover.f i) x)) := hreg _
  exact IsRegularLocalRing.of_ringEquiv
    (asIso ((X.affineCover.f i).stalkMap x)).commRingCatIsoToRingEquiv

end LemAlgebraRegularDescendsUnderFppf

section PropFpqcDescentForPropertiesOfSchemes

open AlgebraicGeometry CategoryTheory Limits

universe u v

/-- Stronger topological lemma used in the proof of Proposition 3.1.21
(quasi-compactness): quasi-compactness descends along any surjective morphism of schemes. -/
theorem AlgebraicGeometry.Scheme.compactSpace_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Surjective f] [CompactSpace X] : CompactSpace Y := by
  constructor
  have : Set.range f.base = Set.univ := f.surjective.range_eq
  rw [← this]
  exact isCompact_range f.continuous

/- Ring-level background results used in the proof of Proposition 3.1.21 (noetherian,
reduced, and normal cases): the ring-theoretic content of the remaining parts: if
`R → S` is faithfully flat and `S` is noetherian (resp. reduced, an integrally closed
domain, a normal ring), then so is `R`. Stacks 033E, 033F, 033G
(`algebra-lemma-descent-{Noetherian,reduced,normal}`). Mathlib has the Noetherian case as
`IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat`; the reduced and normal
cases are obligations for `stacks-project-lean`. -/
example (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing S]
    [Module.FaithfullyFlat R S] : IsNoetherianRing R :=
  isNoetherianRing_of_faithfullyFlat (R := R) (S := S)

example (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [IsReduced S]
    [Module.FaithfullyFlat R S] : IsReduced R :=
  isReduced_of_faithfullyFlat (R := R) (S := S)

example (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [IsNormalRing S]
    [Module.FaithfullyFlat R S] : IsNormalRing R :=
  isNormalRing_of_faithfullyFlat (R := R) (S := S)

/-- Ring-level background theorem used in the proof of Proposition 3.1.21 (integrality):
a ring admitting a faithfully flat algebra which is a domain is a domain. -/
theorem IsDomain.of_faithfullyFlat (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain S] [Module.FaithfullyFlat R S] : IsDomain R :=
  (FaithfulSMul.algebraMap_injective R S).isDomain (algebraMap R S)

/-- Helper lemma used in the proof of Proposition 3.1.21 (reducedness):
reducedness of schemes descends along surjective flat morphisms. -/
theorem AlgebraicGeometry.Scheme.isReduced_of_surjective_of_flat {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Surjective f] [Flat f] [IsReduced X] : IsReduced Y := by
  letI : ∀ y : Y, _root_.IsReduced (Y.presheaf.stalk y) := fun y ↦ by
    obtain ⟨x, rfl⟩ := f.surjective y
    algebraize [(f.stalkMap x).hom]
    letI : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
      @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
        (Flat.stalkMap f x) (f.toLRSHom.prop x)
    exact isReduced_of_faithfullyFlat
      (R := Y.presheaf.stalk (f x)) (S := X.presheaf.stalk x)
  exact isReduced_of_isReduced_stalk Y

/-- Helper lemma used in the proof of Proposition 3.1.21
(normality): stalkwise normality descends along a surjective flat morphism of schemes.

This is the scheme-level form of faithfully flat descent of normal rings (Stacks 033G).
It is stated stalkwise because Mathlib does not currently bundle normality as a property
of schemes. -/
theorem AlgebraicGeometry.Scheme.isNormalRing_stalk_of_surjective_of_flat
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f] [Flat f]
    (hX : ∀ x : X, IsNormalRing (X.presheaf.stalk x)) (y : Y) :
    IsNormalRing (Y.presheaf.stalk y) := by
  obtain ⟨x, rfl⟩ := f.surjective y
  algebraize [(f.stalkMap x).hom]
  letI : IsNormalRing (X.presheaf.stalk x) := hX x
  letI : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap f x) (f.toLRSHom.prop x)
  exact isNormalRing_of_faithfullyFlat
    (R := Y.presheaf.stalk (f x)) (S := X.presheaf.stalk x)

/-- Helper lemma used in the proof of Proposition 3.1.21
(regularity): stalkwise regularity descends along a surjective flat morphism of schemes.

This packages the scheme-level form of Lemma 3.1.19 simultaneously at every point of
the target. -/
theorem AlgebraicGeometry.Scheme.forall_isRegularLocalRing_stalk_of_surjective_of_flat
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f] [Flat f]
    (hX : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) :
    ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y) :=
  fun y ↦ Scheme.isRegularLocalRing_stalk_of_surjective_of_flat f hX y

/-- Helper lemma used in the proof of Proposition 3.1.21 (local
noetherianness): local noetherianness of schemes descends along surjective flat
quasi-compact morphisms. -/
theorem AlgebraicGeometry.Scheme.isLocallyNoetherian_of_surjective_of_flat
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f] [Flat f] [QuasiCompact f]
    [IsLocallyNoetherian X] : IsLocallyNoetherian Y := by
  wlog hY : ∃ R : CommRingCat.{u}, Y = Spec R generalizing X Y
  · exact (isLocallyNoetherian_iff_openCover Y.affineCover).mpr fun i ↦ by
      letI hPull : IsLocallyNoetherian (pullback f (Y.affineCover.f i)) :=
        @isLocallyNoetherian_of_isOpenImmersion (pullback f (Y.affineCover.f i)) X
          (pullback.fst f (Y.affineCover.f i)) inferInstance ‹IsLocallyNoetherian X›
      exact this (pullback.snd f (Y.affineCover.f i)) ⟨_, rfl⟩
  obtain ⟨R, rfl⟩ := hY
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨Z, p, hpSurj, hpLocal, hZaff⟩ :=
    X.exists_hom_isAffine_of_isZariskiLocalAtSource @IsLocalIso
  letI : Surjective p := hpSurj
  letI : IsLocalIso p := hpLocal
  letI : IsAffine Z := hZaff
  letI : LocallyOfFiniteType p := by
    apply IsLocalIso.le_of_isZariskiLocalAtSource @LocallyOfFiniteType
    exact hpLocal
  letI : Flat p := by
    apply IsLocalIso.le_of_isZariskiLocalAtSource @Flat
    exact hpLocal
  letI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian p
  let q := Z.isoSpec.inv ≫ p ≫ f
  obtain ⟨φ, hφ⟩ := Spec.map_surjective q
  have hff : φ.hom.FaithfullyFlat := by
    rw [← flat_and_surjective_SpecMap_iff, hφ]
    exact ⟨inferInstance, inferInstance⟩
  algebraize [φ.hom]
  letI : IsNoetherianRing Γ(Z, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Z⟩
  letI : Module.FaithfullyFlat R Γ(Z, ⊤) := by
    rw [← RingHom.faithfullyFlat_algebraMap_iff]
    simpa only [RingHom.algebraMap_toAlgebra] using hff
  have hR : IsNoetherianRing R :=
    isNoetherianRing_of_faithfullyFlat (R := R) (S := Γ(Z, ⊤))
  exact isLocallyNoetherian_Spec.mpr hR

/-- **Proposition 3.1.21** (`prop:fpqc-descent-for-properties-of-schemes`) (local
noetherianness, fpqc-cover form): local Noetherianness descends along the book's
generalized singleton fpqc covers. -/
theorem AlgebraicGeometry.Scheme.isLocallyNoetherian_of_fpqcCover
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : Scheme.IsFpqcCover f)
    [IsLocallyNoetherian X] : IsLocallyNoetherian Y := by
  wlog hY : IsAffine Y generalizing X Y
  · rw [isLocallyNoetherian_iff_openCover Y.affineCover]
    intro i
    let f' := pullback.snd f (Y.affineCover.f i)
    letI hPull : IsLocallyNoetherian (pullback f (Y.affineCover.f i)) :=
      @isLocallyNoetherian_of_isOpenImmersion (pullback f (Y.affineCover.f i)) X
        (pullback.fst f (Y.affineCover.f i)) inferInstance ‹IsLocallyNoetherian X›
    exact this f' (MorphismProperty.pullback_snd f (Y.affineCover.f i) hf) inferInstance
  obtain ⟨V, hVc, hVY⟩ := hf.exists_compact_opens_image_eq (isAffineOpen_top Y)
  let g : (V : Scheme) ⟶ Y := V.ι ≫ f
  letI : Surjective g := ⟨fun y ↦ by
    obtain ⟨x, hxV, hxy⟩ := Set.ext_iff.mp hVY y |>.mpr (by simp)
    refine ⟨⟨x, hxV⟩, ?_⟩
    simpa [g] using hxy⟩
  letI : Flat g := by
    letI : Flat f := hf.flat
    dsimp [g]
    infer_instance
  letI : CompactSpace V := isCompact_iff_compactSpace.mp hVc
  letI : QuasiCompact g := by infer_instance
  exact Scheme.isLocallyNoetherian_of_surjective_of_flat g

/-- **Proposition 3.1.21** (`prop:fpqc-descent-for-properties-of-schemes`)
(noetherianness): noetherianness descends along the book's generalized singleton fpqc
covers. -/
theorem AlgebraicGeometry.Scheme.isNoetherian_of_fpqcCover
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : Scheme.IsFpqcCover f) [IsNoetherian X] :
    IsNoetherian Y := by
  letI : Surjective f := hf.surjective
  letI : Flat f := hf.flat
  exact
    { toIsLocallyNoetherian := Scheme.isLocallyNoetherian_of_fpqcCover f hf
      toCompactSpace := Scheme.compactSpace_of_surjective f }

/-- **Proposition 3.1.21** (`prop:fpqc-descent-for-properties-of-schemes`) (reducedness,
fpqc-cover form): reducedness descends along the book's generalized singleton fpqc
covers. -/
theorem AlgebraicGeometry.Scheme.isReduced_of_fpqcCover
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : Scheme.IsFpqcCover f) [IsReduced X] :
    IsReduced Y := by
  letI : Surjective f := hf.surjective
  letI : Flat f := hf.flat
  exact Scheme.isReduced_of_surjective_of_flat f

/-- **Proposition 3.1.21** (`prop:fpqc-descent-for-properties-of-schemes`) (normality,
fpqc-cover form): stalkwise normality descends along the book's generalized singleton
fpqc covers. -/
theorem AlgebraicGeometry.Scheme.isNormalRing_stalk_of_fpqcCover
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : Scheme.IsFpqcCover f)
    (hX : ∀ x : X, IsNormalRing (X.presheaf.stalk x)) (y : Y) :
    IsNormalRing (Y.presheaf.stalk y) := by
  letI : Surjective f := hf.surjective
  letI : Flat f := hf.flat
  exact Scheme.isNormalRing_stalk_of_surjective_of_flat f hX y

/-- **Proposition 3.1.21** (`prop:fpqc-descent-for-properties-of-schemes`) (regularity,
fpqc-cover form): stalkwise regularity descends along the book's generalized singleton
fpqc covers. -/
theorem AlgebraicGeometry.Scheme.forall_isRegularLocalRing_stalk_of_fpqcCover
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : Scheme.IsFpqcCover f)
    (hX : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) :
    ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y) := by
  letI : Surjective f := hf.surjective
  letI : Flat f := hf.flat
  exact Scheme.forall_isRegularLocalRing_stalk_of_surjective_of_flat f hX

/-- Helper lemma used in the proof of Proposition 3.1.21 (integrality):
integrality of schemes descends along surjective flat morphisms with irreducible target.
(Irreducibility itself does not descend — the property of being a domain is not even
Zariski-local — so it is a hypothesis here; the book's statement is about the underlying
ring-theoretic property, `IsDomain.of_faithfullyFlat`. See the `[decision]` entry for this
label in this folder's COMMENTARY.md.) -/
theorem AlgebraicGeometry.Scheme.isIntegral_of_surjective_of_flat {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Surjective f] [Flat f] [IsIntegral X] [IrreducibleSpace Y] :
    IsIntegral Y := by
  letI : IsReduced Y := Scheme.isReduced_of_surjective_of_flat f
  exact isIntegral_of_irreducibleSpace_of_isReduced Y

/-- Partial scheme-level result toward Proposition 3.1.21 (integrality): integrality
descends along a generalized singleton fpqc cover when the target is separately assumed
irreducible. -/
theorem AlgebraicGeometry.Scheme.isIntegral_of_fpqcCover {X Y : Scheme.{u}}
    (f : X ⟶ Y) (hf : Scheme.IsFpqcCover f) [IsIntegral X] [IrreducibleSpace Y] :
    IsIntegral Y := by
  letI : Surjective f := hf.surjective
  letI : Flat f := hf.flat
  exact Scheme.isIntegral_of_surjective_of_flat f

end PropFpqcDescentForPropertiesOfSchemes

section PropFpqcDescentForPropertiesOnSource

open AlgebraicGeometry CategoryTheory Limits

universe u

/-- A discrete scheme descends across a surjective flat quasi-compact morphism.  This is
the topological quotient-map argument used for the zero-dimensional fibers in the étale
case of fpqc descent on the source. -/
theorem AlgebraicGeometry.Scheme.discreteTopology_of_surjective_flat_quasiCompact
    {X Y : Scheme.{u}} (h : X ⟶ Y) [Surjective h] [Flat h] [QuasiCompact h]
    [DiscreteTopology X] : DiscreteTopology Y := by
  rw [discreteTopology_iff_forall_isOpen]
  intro s
  apply (Flat.isQuotientMap_of_surjective h).isOpen_preimage.mp
  exact isOpen_discrete _

/-- A discrete scheme descends across a surjective open morphism. -/
theorem AlgebraicGeometry.Scheme.discreteTopology_of_surjective_isOpenMap
    {X Y : Scheme.{u}} (h : X ⟶ Y) [Surjective h] (hop : IsOpenMap h)
    [DiscreteTopology X] : DiscreteTopology Y := by
  rw [discreteTopology_iff_forall_isOpen]
  intro s
  rw [← h.surjective.image_preimage s]
  exact hop _ (isOpen_discrete _)

/-- Helper lemma used in the proof of Proposition 3.1.22 (étale case,
dimension-zero step): local quasi-finiteness descends from an fpqc precomposition once
local finite type of the lower morphism is known.  On each fiber, the induced fpqc
morphism is a quotient map; the upper fiber is discrete, hence so is the lower fiber.

This isolates the dimension-zero argument in the book's proof of the étale case. -/
theorem AlgebraicGeometry.LocallyQuasiFinite.of_fpqc_precomp
    {X' X Y : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y)
    [Surjective g] [Flat g] [QuasiCompact g] [LocallyOfFiniteType f]
    [LocallyQuasiFinite (g ≫ f)] : LocallyQuasiFinite f := by
  rw [locallyQuasiFinite_iff_isDiscrete_preimage_singleton]
  intro y
  let h := g.precompFiberMap f y
  letI : DiscreteTopology ((g ≫ f).fiber y) := inferInstance
  letI : DiscreteTopology (f.fiber y) :=
    Scheme.discreteTopology_of_surjective_flat_quasiCompact h
  simpa [Scheme.Hom.range_fiberι] using
    (isDiscrete_univ_iff.mpr (inferInstanceAs (DiscreteTopology (f.fiber y)))).image
      (f.fiberι y).isEmbedding.toIsInducing

/-- Local quasi-finiteness descends from an fppf precomposition once local finite type of
the lower morphism is known.  The induced fiber map is surjective and open. -/
theorem AlgebraicGeometry.LocallyQuasiFinite.of_fppf_precomp
    {X' X Y : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g] [LocallyOfFiniteType f]
    [LocallyQuasiFinite (g ≫ f)] : LocallyQuasiFinite f := by
  rw [locallyQuasiFinite_iff_isDiscrete_preimage_singleton]
  intro y
  let h := g.precompFiberMap f y
  letI : DiscreteTopology ((g ≫ f).fiber y) := inferInstance
  letI : DiscreteTopology (f.fiber y) :=
    Scheme.discreteTopology_of_surjective_isOpenMap h h.isOpenMap
  simpa [Scheme.Hom.range_fiberι] using
    (isDiscrete_univ_iff.mpr (inferInstanceAs (DiscreteTopology (f.fiber y)))).image
      (f.fiberι y).isEmbedding.toIsInducing

/-- A smooth locally quasi-finite morphism of schemes is étale. -/
theorem AlgebraicGeometry.Etale.of_smooth_of_locallyQuasiFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] [LocallyQuasiFinite f] : Etale f := by
  constructor
  intro U hU V hV e
  exact RingHom.Etale.of_smooth_of_quasiFinite_of_ringHom (f.appLE U V e).hom
    (f.smooth_appLE hU hV e) (LocallyQuasiFinite.quasiFinite_appLE hU hV e)

/-- Helper lemma used in the proof of Proposition 3.1.22 (smooth case,
given local finite presentation): smoothness descends along an fpqc precomposition once
local finite presentation of the lower morphism is known.  Thus the only extra issue in
the book's unrestricted fpqc claim is descent of local finite presentation on the source;
flatness and geometric regularity of the fibers do descend under the stated hypotheses. -/
theorem AlgebraicGeometry.Smooth.of_fpqc_precomp_of_locallyOfFinitePresentation
    {X' X Y : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y)
    [Surjective g] [Flat g] [QuasiCompact g] [Smooth (g ≫ f)]
    [LocallyOfFinitePresentation f] : Smooth f := by
  letI : Flat f := (flat_comp_iff_of_surjective_flat g f).mp inferInstance
  apply Smooth.of_smooth_fiberToSpecResidueField
  intro y
  let K := Y.residueField y
  let L := AlgebraicClosure K
  let t : Spec (.of L) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K L))
  let q := f.fiberToSpecResidueField y
  haveI : Surjective t := by
    exact ((flat_and_surjective_SpecMap_iff _).mpr
      ((RingHom.faithfullyFlat_algebraMap_iff).mpr inferInstance)).2
  haveI : Flat t := by infer_instance
  haveI : QuasiCompact t := by infer_instance
  haveI : LocallyOfFinitePresentation q := by
    dsimp [q, Scheme.Hom.fiberToSpecResidueField, Scheme.Hom.fiber]
    infer_instance
  haveI : LocallyOfFinitePresentation (pullback.snd q t) := by infer_instance
  haveI : Smooth (pullback.snd q t) :=
    Scheme.smooth_toSpec_of_isAlgClosed_of_forall_isRegularLocalRing
      (pullback.snd q t) (fun x ↦
        g.isRegularLocalRing_stalk_geometricFiber_of_smooth_fpqc_precomp f y L x)
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := q) (g := t)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance

/-- Affine reduction used in the proof of Proposition 3.1.22 (corrected
finite-presentation cancellation, affine case): if `X' ⟶ X` is fppf between affine
schemes and `X' ⟶ Y` is locally of finite presentation, then `X ⟶ Y` is locally of
finite presentation.

The book states an fpqc hypothesis, but the cited Stacks Project Tags 05B5 and 036N require
the displayed additional hypothesis `LocallyOfFinitePresentation g`; see the erratum in
`COMMENTARY.md`. -/
theorem AlgebraicGeometry.LocallyOfFinitePresentation.of_comp_of_fppf_of_isAffine
    {X' X Y : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y)
    [IsAffine X'] [IsAffine X] [IsAffine Y] [Surjective g] [Flat g]
    [LocallyOfFinitePresentation g] [LocallyOfFinitePresentation (g ≫ f)] :
    LocallyOfFinitePresentation f := by
  apply HasRingHomProperty.iff_of_isAffine.mpr
  apply RingHom.FinitePresentation.of_comp_of_faithfullyFlat_permanence
    f.appTop.hom g.appTop.hom
  · rw [← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop]
    exact HasRingHomProperty.appTop @LocallyOfFinitePresentation (g ≫ f) inferInstance
  · exact HasRingHomProperty.appTop @LocallyOfFinitePresentation g inferInstance
  · exact (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine g).mp
      ⟨inferInstance, inferInstance⟩

/-- Helper lemma used in the proof of Proposition 3.1.22 (corrected
finite-presentation cancellation): if `g : X' ⟶ X` is surjective, flat, and locally of
finite presentation and `g ≫ f` is locally of finite presentation, then so is `f`.

This is the fppf statement supplied by the references cited for the book's fpqc claim.
The proof globalizes the affine permanence theorem Stacks 02KK by a finite affine
refinement over each affine chart of `X`. -/
theorem AlgebraicGeometry.LocallyOfFinitePresentation.of_fppf_precomp
    {X' X Y : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    [LocallyOfFinitePresentation (g ≫ f)] : LocallyOfFinitePresentation f := by
  constructor
  intro U hU V hV e
  let fVU := f.resLE U V e
  letI : IsAffine V := hV
  letI : IsAffine U := hU
  let gV := pullback.fst V.ι g
  haveI : Surjective gV := inferInstance
  haveI : Flat gV := inferInstance
  haveI : LocallyOfFinitePresentation gV := inferInstance
  let 𝒰 : Scheme.Cover (Scheme.precoverage (⊤ : MorphismProperty Scheme.{u})) V :=
    Scheme.Cover.mkOfCovers PUnit (fun _ ↦ pullback V.ι g) (fun _ ↦ gV)
      (fun x ↦ ⟨PUnit.unit, (gV.surjective x).choose,
        (gV.surjective x).choose_spec⟩)
      (fun _ ↦ trivial)
  letI : QuasiCompactCover 𝒰.toPreZeroHypercover :=
    QuasiCompactCover.of_isOpenMap fun _ ↦ gV.isOpenMap
  letI : IsZariskiLocalAtSource
      (@Flat : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Flat)
  letI : IsZariskiLocalAtSource
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FinitePresentation)
  letI : MorphismProperty.IsStableUnderBaseChange
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.isStableUnderBaseChange
      RingHom.finitePresentation_isStableUnderBaseChange
  letI : MorphismProperty.HasOfPostcompProperty
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u})
      (MorphismProperty.monomorphisms Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.hasOfPostcompProperty_monomorphisms
  letI : MorphismProperty.HasOfPostcompProperty
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) @IsOpenImmersion :=
    MorphismProperty.HasOfPostcompProperty.of_le
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u})
      (.monomorphisms Scheme.{u}) (fun _ _ i hi ↦ by
        letI : IsOpenImmersion i := hi
        infer_instance)
  letI : MorphismProperty.RespectsLeft (⊤ : MorphismProperty Scheme.{u})
      (@IsOpenImmersion : MorphismProperty Scheme.{u}) :=
    { precomp := fun _ _ _ _ ↦ trivial }
  obtain ⟨𝒱, r, hfin, hr⟩ := QuasiCompactCover.exists_hom 𝒰
  letI : Finite 𝒱.I₀ := hfin
  let p : (∐ fun j ↦ Spec (𝒱.X j)) ⟶ V := Sigma.desc 𝒱.f
  haveI : Surjective p := by
    change Surjective (Sigma.desc fun i ↦ 𝒱.cover.f i)
    infer_instance
  haveI : Flat p := by
    change Flat (Sigma.desc 𝒱.f)
    exact IsZariskiLocalAtSource.sigmaDesc
      (P := (@Flat : MorphismProperty Scheme.{u})) fun j ↦ by
        let j' : 𝒱.cover.I₀ := j
        change Flat (𝒱.cover.f j')
        rw [← r.w₀ j']
        change Flat (r.h₀ j' ≫ gV)
        letI : IsOpenImmersion (r.h₀ j') := hr j'
        exact MorphismProperty.comp_mem (@Flat : MorphismProperty Scheme.{u})
          (r.h₀ j') gV
          (HasRingHomProperty.of_isOpenImmersion RingHom.Flat.containsIdentities)
          (show Flat gV from inferInstance)
  haveI : LocallyOfFinitePresentation p := by
    apply IsZariskiLocalAtSource.sigmaDesc
      (P := (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}))
    intro j
    let j' : 𝒱.cover.I₀ := j
    change LocallyOfFinitePresentation (𝒱.cover.f j')
    rw [← r.w₀ j']
    change LocallyOfFinitePresentation (r.h₀ j' ≫ gV)
    letI : IsOpenImmersion (r.h₀ j') := hr j'
    exact MorphismProperty.comp_mem
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) (r.h₀ j') gV
      (HasRingHomProperty.of_isOpenImmersion
        RingHom.finitePresentation_holdsForLocalizationAway.containsIdentities)
      (show LocallyOfFinitePresentation gV from inferInstance)
  have hpcomp : LocallyOfFinitePresentation (p ≫ fVU) := by
    change LocallyOfFinitePresentation (Sigma.desc 𝒱.f ≫ fVU)
    have hpieces : ∀ j, LocallyOfFinitePresentation (𝒱.f j ≫ fVU) := by
      intro j
      let j' : 𝒱.cover.I₀ := j
      apply MorphismProperty.of_postcomp
        (W := (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}))
        (W' := (@IsOpenImmersion : MorphismProperty Scheme.{u}))
        (𝒱.f j ≫ fVU) U.ι inferInstance
      rw [Category.assoc]
      change LocallyOfFinitePresentation (𝒱.cover.f j' ≫ fVU ≫ U.ι)
      rw [← r.w₀ j']
      rw [Scheme.Hom.resLE_comp_ι]
      let q : 𝒰.X (r.s₀ j') ⟶ X' := by
        change pullback V.ι g ⟶ X'
        exact pullback.snd V.ι g
      have hq : 𝒰.f (r.s₀ j') ≫ V.ι = q ≫ g := by
        change pullback.fst V.ι g ≫ V.ι = pullback.snd V.ι g ≫ g
        exact pullback.condition
      change LocallyOfFinitePresentation
        (r.h₀ j' ≫ 𝒰.f (r.s₀ j') ≫ V.ι ≫ f)
      rw [show r.h₀ j' ≫ 𝒰.f (r.s₀ j') ≫ V.ι ≫ f =
        r.h₀ j' ≫ q ≫ g ≫ f by
          calc
            _ = (r.h₀ j' ≫ (𝒰.f (r.s₀ j') ≫ V.ι)) ≫ f :=
              congrArg (fun k ↦ k ≫ f)
                (Category.assoc (r.h₀ j') (𝒰.f (r.s₀ j')) V.ι)
            _ = (r.h₀ j' ≫ (q ≫ g)) ≫ f := by rw [hq]
            _ = _ := congrArg (fun k ↦ k ≫ f)
              (Category.assoc (r.h₀ j') q g).symm]
      letI : IsOpenImmersion (r.h₀ j') := hr j'
      letI : IsOpenImmersion q := by
        change IsOpenImmersion (pullback.snd V.ι g)
        infer_instance
      have hqfp : LocallyOfFinitePresentation q :=
        HasRingHomProperty.of_isOpenImmersion
          RingHom.finitePresentation_holdsForLocalizationAway.containsIdentities
      exact MorphismProperty.comp_mem
        (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u})
        (r.h₀ j' ≫ q) (g ≫ f)
        (MorphismProperty.comp_mem
          (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u})
          (r.h₀ j') q inferInstance hqfp) inferInstance
    have hall : LocallyOfFinitePresentation (Sigma.desc fun j ↦ 𝒱.f j ≫ fVU) :=
      IsZariskiLocalAtSource.sigmaDesc
        (P := (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u})) hpieces
    rw [← show Sigma.desc (fun j ↦ 𝒱.f j ≫ fVU) = Sigma.desc 𝒱.f ≫ fVU by
      ext j
      simp]
    exact hall
  letI := hpcomp
  have hfVU := LocallyOfFinitePresentation.of_comp_of_fppf_of_isAffine p fVU
  exact RingHom.finitePresentation_respectsIso.arrow_mk_iso_iff
    (arrowResLEAppIso f U V e) |>.mp
      (HasRingHomProperty.appTop
        (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) fVU hfVU)

/-- **Proposition 3.1.22** (`prop:fpqc-descent-for-properties-on-source`) (corrected
smooth case): if `g : X' ⟶ X` is surjective, flat, and locally of finite presentation
and `g ≫ f` is smooth, then `f` is smooth. This is exactly the smooth clause of Stacks
05B5; the extra finite-presentation hypothesis on `g` is absent from the book. -/
@[stacks 05B5 "smooth case"]
theorem AlgebraicGeometry.Smooth.of_fppf_precomp
    {X' X Y : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g] [Smooth (g ≫ f)] : Smooth f := by
  letI : LocallyOfFinitePresentation f :=
    LocallyOfFinitePresentation.of_fppf_precomp g f
  letI : Flat f := (flat_comp_iff_of_surjective_flat g f).mp inferInstance
  apply Smooth.of_smooth_fiberToSpecResidueField
  intro y
  let K := Y.residueField y
  let Ω : Type u := AlgebraicClosure K
  let t : Spec (.of Ω) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  let q : f.fiber y ⟶ Spec (.of (Y.residueField y)) := f.fiberToSpecResidueField y
  letI : LocallyOfFinitePresentation q :=
    MorphismProperty.pullback_snd f (Y.fromSpecResidueField y) inferInstance
  letI : LocallyOfFinitePresentation (pullback.snd q t) := inferInstance
  have hs : Smooth (pullback.snd q t) := by
    apply Scheme.smooth_toSpec_of_isAlgClosed_of_forall_isRegularLocalRing
    intro x
    exact g.isRegularLocalRing_stalk_geometricFiber_of_smooth_fpqc_precomp f y Ω x
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (f := q) (g := t) ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hs

/-- **Proposition 3.1.22** (`prop:fpqc-descent-for-properties-on-source`) (corrected
étale case): if `g : X' ⟶ X` is surjective, flat, and locally of finite presentation
and `g ≫ f` is étale, then `f` is étale. This is the étale clause of Stacks 05B5;
the extra finite-presentation hypothesis on `g` is absent from the book. -/
@[stacks 05B5 "étale case"]
theorem AlgebraicGeometry.Etale.of_fppf_precomp
    {X' X Y : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g] [Etale (g ≫ f)] : Etale f := by
  letI : Smooth f := Smooth.of_fppf_precomp g f
  letI : LocallyQuasiFinite (g ≫ f) := by
    constructor
    intro U hU V hV e
    exact RingHom.QuasiFinite.of_etale_of_ringHom ((g ≫ f).appLE U V e).hom
      ((g ≫ f).etale_appLE hU hV e)
  letI : LocallyQuasiFinite f := LocallyQuasiFinite.of_fppf_precomp g f
  exact Etale.of_smooth_of_locallyQuasiFinite f

end PropFpqcDescentForPropertiesOnSource

section PropFppfSmoothLocalPropertiesOfSchemes

open AlgebraicGeometry CategoryTheory

universe u

/-- **Proposition 3.1.23** (`prop:fppf-smooth-local-properties-of-schemes`) (part (1)): if
`X ⟶ Y` is a surjective, flat morphism locally of finite presentation (fppf), then `X` is
locally noetherian if and only if `Y` is. -/
theorem AlgebraicGeometry.Scheme.isLocallyNoetherian_iff_of_fppf {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Surjective f] [Flat f] [LocallyOfFinitePresentation f] :
    IsLocallyNoetherian X ↔ IsLocallyNoetherian Y := by
  constructor
  · intro hX
    letI := hX
    exact Scheme.isLocallyNoetherian_of_fpqcCover f (Scheme.IsFpqcCover.of_fppf f)
  · intro hY
    letI := hY
    exact LocallyOfFiniteType.isLocallyNoetherian f

/-- **Proposition 3.1.23** (`prop:fppf-smooth-local-properties-of-schemes`) (part (2),
reducedness): if `X ⟶ Y` is a surjective smooth morphism of schemes, then `X` is reduced
if and only if `Y` is. (The ring-theoretic ascent is Stacks 033B; the descent is
Proposition 3.1.21.) -/
theorem AlgebraicGeometry.Scheme.isReduced_iff_of_smooth_of_surjective {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Surjective f] [Smooth f] :
    IsReduced X ↔ IsReduced Y := by
  constructor
  · intro hX
    let _ := hX
    exact Scheme.isReduced_of_surjective_of_flat f
  · intro hY
    let _ := hY
    let _ : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x ↦ by
      obtain ⟨U, hU, V, hV, hxV, hVU, hsmooth⟩ := Smooth.exists_isStandardSmooth f x
      let _ : _root_.IsReduced Γ(Y, U) := inferInstance
      algebraize [(f.appLE U V hVU).hom]
      let _ : _root_.IsReduced Γ(X, V) :=
        isReduced_of_smooth Γ(Y, U) Γ(X, V)
      let _ : Algebra Γ(X, V) (X.presheaf.stalk x) :=
        X.presheaf.algebra_section_stalk ⟨x, hxV⟩
      let _ : IsLocalization (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
          (X.presheaf.stalk x) := hV.isLocalization_stalk ⟨x, hxV⟩
      exact isReduced_localizationPreserves
        (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl (X.presheaf.stalk x) inferInstance
    exact isReduced_of_isReduced_stalk X

/-- **Proposition 3.1.23** (`prop:fppf-smooth-local-properties-of-schemes`) (part (2),
normality): if `X ⟶ Y` is a surjective smooth morphism, then all stalks of `X` are
normal rings if and only if all stalks of `Y` are normal rings. -/
theorem AlgebraicGeometry.Scheme.forall_isNormalRing_stalk_iff_of_smooth_of_surjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f] [Smooth f] :
    (∀ x : X, IsNormalRing (X.presheaf.stalk x)) ↔
      ∀ y : Y, IsNormalRing (Y.presheaf.stalk y) := by
  constructor
  · intro hX y
    exact Scheme.isNormalRing_stalk_of_surjective_of_flat f hX y
  · intro hY x
    obtain ⟨U, hU, V, hV, hxV, hVU, hsmooth⟩ := Smooth.exists_isStandardSmooth f x
    let A := Γ(Y, U)
    let B := Γ(X, V)
    let q := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
    have hA : IsNormalRing A := by
      constructor
      · intro P hP
        let yP : PrimeSpectrum A := ⟨P, hP⟩
        let y : Y := hU.fromSpec yP
        have hy : y ∈ U := (hU.isoSpec.inv yP).2
        letI : Algebra A (Y.presheaf.stalk y) :=
          Y.presheaf.algebra_section_stalk ⟨y, hy⟩
        letI : IsLocalization.AtPrime (Y.presheaf.stalk y) P :=
          hU.isLocalization_stalk' yP hy
        letI : IsNormalRing (Y.presheaf.stalk y) := hY y
        letI : IsDomain (Y.presheaf.stalk y) :=
          IsNormalRing.isDomain_of_isLocalRing
        let e : Y.presheaf.stalk y ≃ₐ[A] Localization.AtPrime P :=
          IsLocalization.algEquiv P.primeCompl (Y.presheaf.stalk y)
            (Localization.AtPrime P)
        exact e.symm.injective.isDomain
      · intro P hP
        let yP : PrimeSpectrum A := ⟨P, hP⟩
        let y : Y := hU.fromSpec yP
        have hy : y ∈ U := (hU.isoSpec.inv yP).2
        letI : Algebra A (Y.presheaf.stalk y) :=
          Y.presheaf.algebra_section_stalk ⟨y, hy⟩
        letI : IsLocalization.AtPrime (Y.presheaf.stalk y) P :=
          hU.isLocalization_stalk' yP hy
        letI : IsNormalRing (Y.presheaf.stalk y) := hY y
        letI : IsDomain (Y.presheaf.stalk y) :=
          IsNormalRing.isDomain_of_isLocalRing
        letI : IsIntegrallyClosed (Y.presheaf.stalk y) :=
          IsNormalRing.isIntegrallyClosed_of_isLocalRing
        let e : Y.presheaf.stalk y ≃ₐ[A] Localization.AtPrime P :=
          IsLocalization.algEquiv P.primeCompl (Y.presheaf.stalk y)
            (Localization.AtPrime P)
        letI : IsDomain (Localization.AtPrime P) := e.symm.injective.isDomain
        exact IsIntegrallyClosed.of_equiv
          (R := Y.presheaf.stalk y) (S := Localization.AtPrime P) e.toRingEquiv
    algebraize [(f.appLE U V hVU).hom]
    letI : IsNormalRing A := hA
    letI : Algebra.Smooth A B := inferInstance
    letI : q.IsPrime := (hV.primeIdealOf ⟨x, hxV⟩).isPrime
    letI : IsNormalRing (Localization.AtPrime q) :=
      isNormalRing_localizationAtPrime_of_smooth A B q
    letI : Algebra B (X.presheaf.stalk x) :=
      X.presheaf.algebra_section_stalk ⟨x, hxV⟩
    letI : IsLocalization.AtPrime (X.presheaf.stalk x) q :=
      hV.isLocalization_stalk ⟨x, hxV⟩
    let e : Localization.AtPrime q ≃ₐ[B] X.presheaf.stalk x :=
      IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q)
        (X.presheaf.stalk x)
    letI : IsDomain (Localization.AtPrime q) :=
      IsNormalRing.isDomain_of_isLocalRing
    letI : IsIntegrallyClosed (Localization.AtPrime q) :=
      IsNormalRing.isIntegrallyClosed_of_isLocalRing
    letI : IsDomain (X.presheaf.stalk x) := e.symm.injective.isDomain
    letI : IsIntegrallyClosed (X.presheaf.stalk x) :=
      IsIntegrallyClosed.of_equiv
        (R := Localization.AtPrime q) (S := X.presheaf.stalk x) e.toRingEquiv
    exact IsNormalRing.of_isDomain_of_isIntegrallyClosed

/-- **Proposition 3.1.23** (`prop:fppf-smooth-local-properties-of-schemes`) (part (2),
regularity): if `X ⟶ Y` is a surjective smooth morphism, then all stalks of `X` are
regular local rings if and only if all stalks of `Y` are regular local rings. -/
theorem AlgebraicGeometry.Scheme.forall_isRegularLocalRing_stalk_iff_of_smooth_of_surjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f] [Smooth f] :
    (∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) ↔
      ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y) := by
  constructor
  · exact Scheme.forall_isRegularLocalRing_stalk_of_surjective_of_flat f
  · intro hY x
    obtain ⟨U, hU, V, hV, hxV, hVU, hsmooth⟩ := Smooth.exists_isStandardSmooth f x
    let A := Γ(Y, U)
    let B := Γ(X, V)
    let p := (hU.primeIdealOf ⟨f x, hVU hxV⟩).asIdeal
    let q := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
    have hpq : q.comap (f.appLE U V hVU).hom = p :=
      congrArg PrimeSpectrum.asIdeal
        (IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hxV)
    algebraize [(f.appLE U V hVU).hom]
    letI : Algebra.Smooth A B := inferInstance
    letI : Algebra A (Y.presheaf.stalk (f x)) :=
      Y.presheaf.algebra_section_stalk ⟨f x, hVU hxV⟩
    letI : IsLocalization.AtPrime (Y.presheaf.stalk (f x)) p :=
      hU.isLocalization_stalk ⟨f x, hVU hxV⟩
    letI : IsRegularLocalRing (Y.presheaf.stalk (f x)) := hY (f x)
    have hRp : IsRegularLocalRing (Localization.AtPrime p) :=
      IsRegularLocalRing.of_ringEquiv (R := Y.presheaf.stalk (f x))
        (IsLocalization.algEquiv p.primeCompl (Y.presheaf.stalk (f x))
          (Localization.AtPrime p)).toRingEquiv
    have hRq : IsRegularLocalRing (Localization.AtPrime q) :=
      letI : IsRegularLocalRing (Localization.AtPrime p) := hRp
      isRegularLocalRing_localization_of_smooth A B p q hpq.symm
    letI : Algebra B (X.presheaf.stalk x) :=
      X.presheaf.algebra_section_stalk ⟨x, hxV⟩
    letI : IsLocalization.AtPrime (X.presheaf.stalk x) q :=
      hV.isLocalization_stalk ⟨x, hxV⟩
    letI : IsRegularLocalRing (Localization.AtPrime q) := hRq
    exact IsRegularLocalRing.of_ringEquiv (R := Localization.AtPrime q)
      (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q)
        (X.presheaf.stalk x)).toRingEquiv

end PropFppfSmoothLocalPropertiesOfSchemes

section RmkNormalityAscends

universe u

/- Background result for Remark 3.1.24 (reducedness ascends): reducedness ascends
along flat maps with reduced fibers: if `R` is a reduced noetherian ring and `R → S` is
flat with reduced fibers, then `S` is reduced. Stacks 0C21
(`algebra-lemma-reduced-goes-up-noetherian`); absent from Mathlib and an outstanding
obligation for `stacks-project-lean`. -/
example (R : Type u) [CommRing R] [IsNoetherianRing R] [IsReduced R] (S : Type u)
    [CommRing S] [IsNoetherianRing S] [Algebra R S] [Module.Flat R S]
    (h : ∀ (p : Ideal R) [p.IsPrime], IsReduced (p.Fiber S)) : IsReduced S :=
  isReduced_of_flat_of_fibers_reduced_noetherian R S h

/-- **Remark 3.1.24** (`rmk:normality-ascends`) (normality ascends): normality ascends
along flat maps with normal fibers: if `R` is a normal noetherian ring and `R → S` is a
flat map of noetherian rings all of whose fibers are normal, then `S` is normal (Stacks
0C22). -/
theorem IsNormalRing.of_flat_of_fibers_normal (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S] [IsNormalRing R] [Module.Flat R S]
    (h : ∀ (p : Ideal R) [p.IsPrime], IsNormalRing (p.Fiber S)) :
    IsNormalRing S := by
  exact isNormalRing_of_flat_of_fibers_normal_noetherian R S h

end RmkNormalityAscends

section RmkCompletionNormal

/- Prose record of Remark 3.1.25: for a noetherian local ring `A`, the
completion map `A → Â` is faithfully flat, so reducedness, normality, and regularity
of `Â` descend to `A`.  The converse holds for regularity, and for reducedness and
normality under excellence; normalization then commutes with completion.

Mathlib currently has the adic-completion and local-ring constructions, but not the
faithful-flatness theorem for the noetherian local completion map nor the excellence
results cited here (Stacks 07NZ and 0C23).  In accordance with the repository policy for
broad literature remarks, these claims are therefore retained as prose. -/

-- STATUS: remark-complete

end RmkCompletionNormal
