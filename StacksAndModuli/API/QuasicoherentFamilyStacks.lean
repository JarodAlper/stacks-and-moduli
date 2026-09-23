module

public import StacksAndModuli.API.PseudofunctorPrecompositionDescentEquivalence
public import StacksAndModuli.API.FlatOverDescent
public import StacksAndModuli.API.QuasicoherentFamilies
public import StacksAndModuli.API.QuasicoherentVectorBundles
public import StacksAndModuli.«Section3.1-Descent».«part3.1.2-descent-quasi-coherent»
public import StacksAndModuli.«Section3.3-Presheaves-and-Sheaves».«part3.3.2-single-map-and-schemes-are-sheaves»

/-!
# Descent for quasicoherent families

This file develops stack and locality results for the pseudofunctors of quasicoherent
modules on a varying fiber product `X ×_S T`.  The ambient quasicoherent stack is
transported along the base-change functor `T ↦ X ×_S T`.
-/

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Quasicoherent modules on the varying schemes `X ×_S T` form an fpqc stack
over `Scheme/S`. -/
theorem isStack_familyModulesPseudofunctor {S : Scheme.{u}} (X : Over S) :
    (familyModulesPseudofunctor X).IsStack (Scheme.fpqcTopology.over S) := by
  letI : quasicoherentPseudofunctor.{u}.IsStack Scheme.fpqcTopology :=
    isStack_quasicoherentPseudofunctor
  exact Pseudofunctor.isStack_precomp_of_coverPreserving
    (J := Scheme.fpqcTopology.over S) (K := Scheme.fpqcTopology)
    (familySchemeFunctor X) quasicoherentPseudofunctor
    (CoverPreserving.comp (J := Scheme.fpqcTopology.over S)
      (K := Scheme.fpqcTopology.over X.left) (L := Scheme.fpqcTopology)
      (Scheme.fpqcTopology.coverPreserving_overPullback X.hom)
      (Scheme.fpqcTopology.over_forget_coverPreserving X.left))

/-- The étale topology on a slice of schemes is coarser than the fpqc
topology on that slice. -/
lemma etaleTopology_over_le_fpqcTopology_over (S : Scheme.{u}) :
    Scheme.etaleTopology.over S ≤ Scheme.fpqcTopology.over S := by
  intro T R hR
  rw [Scheme.etaleTopology.mem_over_iff] at hR
  rw [Scheme.fpqcTopology.mem_over_iff]
  exact Scheme.etaleTopology_le_fpqcTopology _ hR

/-- Quasicoherent modules on the varying schemes `X ×_S T` form an étale
stack over `Scheme/S`. -/
theorem isStack_familyModulesPseudofunctor_etale {S : Scheme.{u}} (X : Over S) :
    (familyModulesPseudofunctor X).IsStack (Scheme.etaleTopology.over S) := by
  letI : (familyModulesPseudofunctor X).IsStack (Scheme.fpqcTopology.over S) :=
    isStack_familyModulesPseudofunctor X
  exact Pseudofunctor.IsStack.of_le
    (etaleTopology_over_le_fpqcTopology_over S)

/-- Relative flatness of quasicoherent families is local for the étale topology
on schemes over the base. -/
instance flatFamilyProperty_isLocal_etale {S : Scheme.{u}} (X : Over S) :
    (flatFamilyProperty X).IsLocal (Scheme.etaleTopology.over S) where
  of_sieve {T} R hR M hM := by
    dsimp only [flatFamilyProperty]
    letI : M.obj.IsQuasicoherent := M.property
    let p := pullback.fst T.hom X.hom
    apply Scheme.Modules.FlatOver.of_etale_sieve p M.obj
      (Sieve.overEquiv T R)
    · exact (Scheme.etaleTopology.mem_over_iff R).mp hR
    · intro f
      let g : Over.mk (f.obj.hom ≫ T.hom) ⟶ T := Over.homMk f.obj.hom
      have hg : R g := (Sieve.overEquiv_iff R f.obj.hom).mp f.property
      let q : R.arrows.category := R.arrows.categoryMk g hg
      have hq := hM q
      dsimp only [flatFamilyProperty] at hq
      let G := ((Over.pullback X.hom).map g).left
      let p' := pullback.fst (f.obj.hom ≫ T.hom) X.hom
      have H : IsPullback G p' p f.obj.hom := overPullbackMap_isPullback g
      exact Scheme.Modules.FlatOver.canonical_pullback_of_isPullback
        G p' p f.obj.hom H M.obj hq

/-- Finite presentation of a quasicoherent family is local for the étale
topology on schemes over the base. -/
instance coherentFamilyProperty_isLocal_etale {S : Scheme.{u}} (X : Over S) :
    (coherentFamilyProperty X).IsLocal (Scheme.etaleTopology.over S) where
  of_sieve {T} R hR M hM := by
    constructor
    · apply Pseudofunctor.ObjectProperty.IsLocal.of_sieve
        (P := flatFamilyProperty X) R hR M
      intro q
      exact (hM q).1
    · let H := familySchemeFunctor X
      let R' := R.functorPushforward H
      have hR'etale : R' ∈ Scheme.etaleTopology (H.obj T) := by
        apply (CoverPreserving.comp
          (J := Scheme.etaleTopology.over S)
          (K := Scheme.etaleTopology.over X.left)
          (L := Scheme.etaleTopology)
          (Scheme.etaleTopology.coverPreserving_overPullback X.hom)
          (Scheme.etaleTopology.over_forget_coverPreserving X.left)).cover_preserve
        exact hR
      have hR'fpqc : R' ∈ Scheme.fpqcTopology (H.obj T) :=
        Scheme.etaleTopology_le_fpqcTopology _ hR'etale
      letI : M.obj.IsQuasicoherent := M.property
      apply isFinitePresentation_of_fpqc_sieve R' hR'fpqc M.obj
      intro Y f hf
      obtain ⟨Z, a, b, ha, hab⟩ := hf
      let q : R.arrows.category := R.arrows.categoryMk a ha
      have hqa := (hM q).2
      change ((Modules.pullback (H.map a)).obj M.obj).IsFinitePresentation at hqa
      letI : ((Modules.pullback (H.map a)).obj M.obj).IsFinitePresentation := hqa
      have hb : ((Modules.pullback b).obj
          ((Modules.pullback (H.map a)).obj M.obj)).IsFinitePresentation := by
        infer_instance
      exact ObjectProperty.prop_of_iso
        (P := SheafOfModules.isFinitePresentation Y.ringCatSheaf)
        ((Modules.pullbackComp b (H.map a)).app M.obj ≪≫
          ((Modules.pullbackCongr hab).app M.obj).symm)
        hb

/-- Finite local freeness of a quasicoherent family is local for the étale
topology on schemes over the base. -/
instance vectorBundleFamilyProperty_isLocal_etale {S : Scheme.{u}} (X : Over S) :
    (vectorBundleFamilyProperty X).IsLocal (Scheme.etaleTopology.over S) where
  of_sieve {T} R hR M hM := by
    constructor
    · apply Pseudofunctor.ObjectProperty.IsLocal.of_sieve
        (P := flatFamilyProperty X) R hR M
      intro q
      exact (hM q).1
    · let H := familySchemeFunctor X
      let R' := R.functorPushforward H
      have hR'etale : R' ∈ Scheme.etaleTopology (H.obj T) := by
        apply (CoverPreserving.comp
          (J := Scheme.etaleTopology.over S)
          (K := Scheme.etaleTopology.over X.left)
          (L := Scheme.etaleTopology)
          (Scheme.etaleTopology.coverPreserving_overPullback X.hom)
          (Scheme.etaleTopology.over_forget_coverPreserving X.left)).cover_preserve
        exact hR
      have hR'fpqc : R' ∈ Scheme.fpqcTopology (H.obj T) :=
        Scheme.etaleTopology_le_fpqcTopology _ hR'etale
      letI : M.obj.IsQuasicoherent := M.property
      apply isFiniteLocallyFree_of_fpqc_sieve R' hR'fpqc M.obj
      intro Y f hf
      obtain ⟨Z, a, b, ha, hab⟩ := hf
      let q : R.arrows.category := R.arrows.categoryMk a ha
      have hqa := (hM q).2
      change IsFiniteLocallyFree
        ((Modules.pullback (H.map a)).obj M.obj) at hqa
      have hb : IsFiniteLocallyFree ((Modules.pullback b).obj
          ((Modules.pullback (H.map a)).obj M.obj)) := by
        letI : M.obj.IsQuasicoherent := M.property
        exact hqa.pullback b
      exact hb.of_iso
        ((Modules.pullbackComp b (H.map a)).app M.obj ≪≫
          ((Modules.pullbackCongr hab).app M.obj).symm)

/-- Flat quasicoherent families form an étale stack. -/
theorem isStack_flatFamilyPseudofunctor_etale {S : Scheme.{u}} (X : Over S) :
    (flatFamilyPseudofunctor X).IsStack (Scheme.etaleTopology.over S) := by
  letI : (familyModulesPseudofunctor X).IsStack (Scheme.etaleTopology.over S) :=
    isStack_familyModulesPseudofunctor_etale X
  letI : (flatFamilyProperty X).fullsubcategory.IsStack
      (Scheme.etaleTopology.over S) :=
    (flatFamilyProperty X).fullsubcategory_isStack
  exact Pseudofunctor.core_isStack _

/-- Flat finitely presented quasicoherent families form an étale stack. -/
theorem isStack_coherentFamilyPseudofunctor_etale {S : Scheme.{u}} (X : Over S) :
    (coherentFamilyPseudofunctor X).IsStack (Scheme.etaleTopology.over S) := by
  letI : (familyModulesPseudofunctor X).IsStack (Scheme.etaleTopology.over S) :=
    isStack_familyModulesPseudofunctor_etale X
  letI : (coherentFamilyProperty X).fullsubcategory.IsStack
      (Scheme.etaleTopology.over S) :=
    (coherentFamilyProperty X).fullsubcategory_isStack
  exact Pseudofunctor.core_isStack _

/-- Flat vector-bundle families form an étale stack. -/
theorem isStack_vectorBundleFamilyPseudofunctor_etale
    {S : Scheme.{u}} (X : Over S) :
    (vectorBundleFamilyPseudofunctor X).IsStack
      (Scheme.etaleTopology.over S) := by
  letI : (familyModulesPseudofunctor X).IsStack (Scheme.etaleTopology.over S) :=
    isStack_familyModulesPseudofunctor_etale X
  letI : (vectorBundleFamilyProperty X).fullsubcategory.IsStack
      (Scheme.etaleTopology.over S) :=
    (vectorBundleFamilyProperty X).fullsubcategory_isStack
  exact Pseudofunctor.core_isStack _

end AlgebraicGeometry.Scheme.Modules
