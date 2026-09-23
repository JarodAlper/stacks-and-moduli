module

public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.1-definition-of-a-prestack»
public import StacksAndModuli.API.ArrowCartesianProperty
public import StacksAndModuli.API.ClassifyingPrestack
public import StacksAndModuli.API.QuasicoherentFamilies
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Scheme

/-!
# Examples of prestacks

This module formalizes `ex:presheaves-are-prestacks`, `ex:representable-prestacks` and
`ex:schemes-are-prestacks` of §3.4 (Prestacks) of *Stacks and Moduli*,
section label `sec:prestacks`.

Main declarations:
- `CategoryTheory.CostructuredArrow.proj_yoneda_isFiberedInGroupoids`: for a presheaf `F`
  on `𝒮`, the category of pairs `(S, a ∈ F(S))` — realized as `CostructuredArrow yoneda F`,
  whose objects are pairs `(S, yoneda S ⟶ F)` — is a prestack over `𝒮`;
- `CategoryTheory.Over.forget_isFiberedInGroupoids`: for `S : 𝒮`, the restricted category
  `𝒮/S` with its projection `Over.forget S` is a prestack over `𝒮` (the prestack
  represented by `S`);
- the specialization to the category of schemes (`ex:schemes-are-prestacks`).
- `AlgebraicGeometry.Scheme.smoothCurvePrestack`: the prestack of smooth, proper,
  geometrically connected relative curves (`ex:moduli-prestack-of-smooth-curves`).
- `AlgebraicGeometry.Scheme.Modules.quasicoherentFamilyPrestack`,
  `coherentSheafFamilyPrestack`, and `vectorBundleFamilyModuliPrestack`: the three
  sheaf-family prestacks of `ex:moduli-prestack-of-vector-bundles`.
- `AlgebraicGeometry.Scheme.classifyingStack`: the classifying prestack `BG` of a
  smooth affine group scheme (`def:classifying-prestack`).
-/

@[expose] public section

-- Mathlib declares `@Flat`, `@Etale`, ... under this option; without it their
-- `MorphismProperty` instances do not unify here.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false


section ExPresheavesArePrestacks

open CategoryTheory Functor

universe w v u

variable {𝒮 : Type u} [Category.{v} 𝒮]

/-- **Example 3.4.7** (`ex:presheaves-are-prestacks`): for a presheaf `F` on a category
`𝒮`, the category `𝒳_F` of pairs `(S, a)` with `S ∈ 𝒮` and `a ∈ F(S)` — realized as the
category `CostructuredArrow yoneda F` of pairs `(S, a : Mor(-, S) ⟶ F)` — is a prestack
over `𝒮`: a morphism `(S', a') ⟶ (S, a)` is a morphism `f : S' ⟶ S` with `f^* a = a'`, so
pullbacks exist and are unique. -/
instance CategoryTheory.CostructuredArrow.proj_yoneda_isFiberedInGroupoids
    (F : 𝒮ᵒᵖ ⥤ Type v) :
    (CostructuredArrow.proj yoneda F).IsFiberedInGroupoids where
  exists_isHomLift {a R} f := by
    have hw : yoneda.map f ≫ a.hom =
        (CostructuredArrow.mk (yoneda.map f ≫ a.hom)).hom := by simp
    refine ⟨CostructuredArrow.mk (yoneda.map f ≫ a.hom),
      (CostructuredArrow.homMk f hw.symm : CostructuredArrow.mk (yoneda.map f ≫ a.hom) ⟶ a),
      ?_⟩
    have h := IsHomLift.map (p := CostructuredArrow.proj yoneda F)
      (CostructuredArrow.homMk f hw.symm : CostructuredArrow.mk (yoneda.map f ≫ a.hom) ⟶ a)
    simpa [CostructuredArrow.proj] using h
  isStronglyCartesian {a b} φ := by
    constructor
    intro a' g ψ hψ
    -- the unique filler is induced by the base morphism underlying `ψ` factored through `g`
    have hg : g ≫ (CostructuredArrow.proj yoneda F).map φ =
        (CostructuredArrow.proj yoneda F).map ψ :=
      IsHomLift.eq_of_isHomLift _ _ _
    have hg' : g ≫ φ.left = ψ.left := by simpa [CostructuredArrow.proj] using hg
    have hga : yoneda.map g ≫ a.hom = a'.hom := by
      rw [← CostructuredArrow.w ψ, ← hg', Functor.map_comp, Category.assoc,
        CostructuredArrow.w]
    refine ⟨(CostructuredArrow.homMk g hga : a' ⟶ a), ⟨?_, ?_⟩, ?_⟩
    · have h := IsHomLift.map (p := CostructuredArrow.proj yoneda F)
        (CostructuredArrow.homMk g hga : a' ⟶ a)
      simpa [CostructuredArrow.proj] using h
    · apply CostructuredArrow.hom_ext
      simpa [CostructuredArrow.proj] using hg'
    · rintro χ ⟨hχ₁, hχ₂⟩
      apply CostructuredArrow.hom_ext
      have h := IsHomLift.eq_of_isHomLift (CostructuredArrow.proj yoneda F) g χ
      simpa [CostructuredArrow.proj] using h.symm

end ExPresheavesArePrestacks


section ExRepresentablePrestacks

open CategoryTheory Functor

universe v u

variable {𝒮 : Type u} [Category.{v} 𝒮]

/-- **Example 3.4.8** (`ex:representable-prestacks`): for an object `S` of a category
`𝒮`, the restricted category `𝒮/S` with its projection `(T ⟶ S) ↦ T` is a prestack over
`𝒮`, the prestack represented by `S`; it corresponds to the representable presheaf
`Mor(-, S)` under Example 3.4.7. -/
instance CategoryTheory.Over.forget_isFiberedInGroupoids (S : 𝒮) :
    (Over.forget S).IsFiberedInGroupoids where
  exists_isHomLift {a R} f := by
    have hw : (f ≫ a.hom : R ⟶ S) = (Over.mk (f ≫ a.hom)).hom := by simp
    refine ⟨Over.mk (f ≫ a.hom), (Over.homMk f hw.symm : Over.mk (f ≫ a.hom) ⟶ a), ?_⟩
    have h := IsHomLift.map (p := Over.forget S)
      (Over.homMk f hw.symm : Over.mk (f ≫ a.hom) ⟶ a)
    simpa using h
  isStronglyCartesian {a b} φ := by
    constructor
    intro a' g ψ hψ
    have hg : g ≫ (Over.forget S).map φ = (Over.forget S).map ψ :=
      IsHomLift.eq_of_isHomLift _ _ _
    have hg' : g ≫ φ.left = ψ.left := by simpa [CostructuredArrow.proj] using hg
    have hga : g ≫ a.hom = a'.hom := by
      rw [← Over.w φ, ← Over.w ψ, ← hg']
      simp
    refine ⟨(Over.homMk g hga : a' ⟶ a), ⟨?_, ?_⟩, ?_⟩
    · have h := IsHomLift.map (p := Over.forget S) (Over.homMk g hga : a' ⟶ a)
      simpa using h
    · apply Over.OverMorphism.ext
      simpa using hg'
    · rintro χ ⟨hχ₁, hχ₂⟩
      apply Over.OverMorphism.ext
      have h := IsHomLift.eq_of_isHomLift (Over.forget S) g χ
      simpa using h.symm

end ExRepresentablePrestacks


section ExSchemesArePrestacks

open CategoryTheory AlgebraicGeometry

universe u

/- **Example 3.4.9** (`ex:schemes-are-prestacks`): a scheme `X` defines the prestack
`Sch/X` of schemes over `X` — the special case of Example 3.4.8
for the category of schemes. (Recorded as an `example`,
which cannot carry a doc comment.) -/
example (X : Scheme.{u}) : (Over.forget X).IsFiberedInGroupoids :=
  inferInstance

end ExSchemesArePrestacks


section ExModuliPrestackOfSmoothCurves

open CategoryTheory Functor AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- Background definition for Example 3.4.10 (the smooth-curve morphism
property): a family of smooth curves is a proper, geometrically connected morphism which
is smooth of relative dimension one.  This is equivalent to the book's condition that
every geometric fiber is a connected smooth curve. -/
def smoothCurveProperty : MorphismProperty Scheme.{u} :=
  (@SmoothOfRelativeDimension 1 : MorphismProperty Scheme.{u}) ⊓
    ((@IsProper : MorphismProperty Scheme.{u}) ⊓
      (@GeometricallyConnected : MorphismProperty Scheme.{u}))

/-- The property of being a family of smooth curves is preserved by arbitrary base
change. -/
instance smoothCurveProperty_isStableUnderBaseChange :
    smoothCurveProperty.{u}.IsStableUnderBaseChange := by
  constructor
  intro X Y Y' S f g f' g' sq h
  change SmoothOfRelativeDimension 1 g ∧ IsProper g ∧ GeometricallyConnected g at h
  change SmoothOfRelativeDimension 1 g' ∧ IsProper g' ∧ GeometricallyConnected g'
  refine ⟨?_, ?_, ?_⟩
  · exact (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback sq h.1
  · exact (inferInstance : MorphismProperty.IsStableUnderBaseChange
      (@IsProper : MorphismProperty Scheme.{u})).of_isPullback sq h.2.1
  · exact (inferInstance : MorphismProperty.IsStableUnderBaseChange
      (@GeometricallyConnected : MorphismProperty Scheme.{u})).of_isPullback sq h.2.2

/-- Membership in the smooth-curve morphism property is precisely the conjunction used
in its definition. -/
lemma mem_smoothCurveProperty_iff {X S : Scheme.{u}} (f : X ⟶ S) :
    smoothCurveProperty.{u} f ↔
      SmoothOfRelativeDimension 1 f ∧ IsProper f ∧ GeometricallyConnected f :=
  Iff.rfl

/-- **Example 3.4.10** (`ex:moduli-prestack-of-smooth-curves`): the prestack `ℳ` of
families of smooth curves.  Its objects are smooth, proper, geometrically connected
relative curves `C → S`; its arrows are cartesian squares, and the projection remembers
`S`. -/
abbrev smoothCurvePrestack : BasedCategory Scheme.{u} :=
  CategoryTheory.arrowCartesianProperty smoothCurveProperty.{u}

/-- Supporting instance for Example 3.4.10 (prestack assertion):
families of smooth curves pull back along arbitrary morphisms, and cartesian squares
satisfy the required universal property. -/
instance smoothCurvePrestack_isFiberedInGroupoids :
    smoothCurvePrestack.{u}.p.IsFiberedInGroupoids :=
  inferInstance

/-- API construction associated to Example 3.4.10 (the genus-`g` full
subcategory, in invariant-parameter form): for any base-change-stable refinement `Q` of
the smooth-curve property (in particular, the condition that every geometric fiber has
genus `g`), the corresponding full subcategory is again a prestack. -/
abbrev smoothCurveSubprestack (Q : MorphismProperty Scheme.{u})
    [Q.IsStableUnderBaseChange] : BasedCategory Scheme.{u} :=
  CategoryTheory.arrowCartesianProperty (smoothCurveProperty.{u} ⊓ Q)

/-- A base-change-stable full subfamily of the smooth-curve prestack is a prestack; this
is the categorical assertion used for `ℳ_g`. -/
instance smoothCurveSubprestack_isFiberedInGroupoids (Q : MorphismProperty Scheme.{u})
    [Q.IsStableUnderBaseChange] :
    (smoothCurveSubprestack Q).p.IsFiberedInGroupoids :=
  inferInstance

end AlgebraicGeometry.Scheme

end ExModuliPrestackOfSmoothCurves


section ExModuliPrestackOfVectorBundles

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- **Example 3.4.12** (`ex:moduli-prestack-of-vector-bundles`): for a scheme `X → S`,
the prestack `QCoh(X)` over `Sch/S` has over `T → S` the groupoid of quasi-coherent
modules on `X ×_S T` which are flat over `T`.  Its arrows over `T' → T` are
isomorphisms between the pulled-back family and the family over `T'`.

The book takes `S = Spec(k)` for a field `k`; the same construction and proof work over
an arbitrary base scheme. -/
noncomputable abbrev quasicoherentFamilyPrestack {S : Scheme.{u}} (X : Over S) :
    BasedCategory (Over S) :=
  flatFamilyPrestack X

/-- Supporting instance for Example 3.4.12 (quasi-coherent case):
flat quasi-coherent families admit pullback along every base morphism and all arrows
are cartesian. -/
noncomputable instance quasicoherentFamilyPrestack_isFiberedInGroupoids
    {S : Scheme.{u}} (X : Over S) :
    (quasicoherentFamilyPrestack X).p.IsFiberedInGroupoids :=
  Pseudofunctor.CoGrothendieck.coreForgetIsFiberedInGroupoids
    (flatFamilyProperty X).fullsubcategory

/-- **Example 3.4.12** (`ex:moduli-prestack-of-vector-bundles`): the coherent-family
full subprestack `Coh(X) ⊆ QCoh(X)`, whose objects are additionally finitely
presented. -/
noncomputable abbrev coherentSheafFamilyPrestack {S : Scheme.{u}} (X : Over S) :
    BasedCategory (Over S) :=
  coherentFamilyPrestack X

/-- Supporting instance for Example 3.4.12 (coherent case):
coherent flat families form a prestack. -/
noncomputable instance coherentSheafFamilyPrestack_isFiberedInGroupoids
    {S : Scheme.{u}} (X : Over S) :
    (coherentSheafFamilyPrestack X).p.IsFiberedInGroupoids :=
  Pseudofunctor.CoGrothendieck.coreForgetIsFiberedInGroupoids
    (coherentFamilyProperty X).fullsubcategory

/-- **Example 3.4.12** (`ex:moduli-prestack-of-vector-bundles`): the vector-bundle
full subprestack `Bun(X) ⊆ QCoh(X)`, whose objects are finite locally free module
sheaves (and retain the flat-over-the-parameter condition of `QCoh(X)`). -/
noncomputable abbrev vectorBundleFamilyModuliPrestack {S : Scheme.{u}} (X : Over S) :
    BasedCategory (Over S) :=
  vectorBundleFamilyPrestack X

/-- Supporting instance for Example 3.4.12 (vector-bundle case):
vector-bundle families form a prestack. -/
noncomputable instance vectorBundleFamilyModuliPrestack_isFiberedInGroupoids
    {S : Scheme.{u}} (X : Over S) :
    (vectorBundleFamilyModuliPrestack X).p.IsFiberedInGroupoids :=
  Pseudofunctor.CoGrothendieck.coreForgetIsFiberedInGroupoids
    (vectorBundleFamilyProperty X).fullsubcategory

end AlgebraicGeometry.Scheme.Modules

end ExModuliPrestackOfVectorBundles


section DefClassifyingPrestack

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} (G : Over S) [GrpObj G] [Smooth G.hom]
  [IsAffineHom G.hom]

/-- **Definition 3.4.14** (`def:classifying-prestack`): for a smooth affine group
scheme `G → S`, the classifying stack `BG` is the category over `Scheme/S` whose
objects over `T` are principal `G`-bundles `P → T` and whose arrows are
`G`-equivariant cartesian squares. -/
noncomputable abbrev classifyingStack : BasedCategory (Over S) :=
  classifyingPrestack G

/-- Supporting instance for Definition 3.4.14 (prestack assertion):
pullback of principal bundles makes `BG` a prestack over `Scheme/S`. -/
noncomputable instance classifyingStack_isFiberedInGroupoids :
    (classifyingStack G).p.IsFiberedInGroupoids :=
  inferInstance

end AlgebraicGeometry.Scheme

end DefClassifyingPrestack
