module

public import StacksAndModuli.API.RepresentableSheafProperty
public import StacksAndModuli.API.SingletonRepresentableSheafDescent
public import StacksAndModuli.«Section3.1-Descent».«part3.1.4-descending-schemes»
public import StacksProject.MoreOnMorphisms.SlicingSmooth.«lemma-etale-nbhd-dominates-smooth»
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Singleton descent for representable sheaves over schemes

This file specializes `GrothendieckTopology.representableByProperty_of_map_obj` to the
two singleton covers used most often over schemes: surjective smooth morphisms for the big
étale topology and fppf morphisms for the big fppf topology.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Opposite

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- If a sheaf becomes represented by an open immersion after pullback along an fpqc
singleton cover which also covers for `J`, then it is represented by the descended open
subscheme. -/
theorem open_representableByProperty_of_fpqcCover
    (J : GrothendieckTopology Scheme.{u}) [J.Subcanonical]
    (hfpqc : IsFpqcCover f)
    (hf : Sieve.generate (Presieve.singleton f) ∈ J Y)
    (F : Sheaf (J.over Y) (Type u))
    (hF : (J.representableByProperty
      (@IsOpenImmersion : MorphismProperty Scheme.{u})).prop (.mk (op X))
        ((J.overMapPullback (Type u) f).obj F)) :
    (J.representableByProperty
      (@IsOpenImmersion : MorphismProperty Scheme.{u})).prop (.mk (op Y)) F := by
  obtain ⟨Z, hZ, ⟨e⟩⟩ := hF
  letI : IsOpenImmersion Z.hom := hZ
  have hker := representedOpenKernelPairEq J f F Z e
  obtain ⟨U, hU⟩ :=
    exists_opens_preimage_eq_of_fpqcCover hfpqc Z.hom.opensRange hker
  let W : Over Y := Over.mk U.ι
  letI : IsOpenImmersion W.hom := by
    dsimp [W]
    infer_instance
  letI : IsOpenImmersion ((Over.pullback f).obj W).hom := by
    change IsOpenImmersion (pullback.snd W.hom f)
    infer_instance
  have hrange : Z.hom.opensRange =
      ((Over.pullback f).obj W).hom.opensRange := by
    change Z.hom.opensRange = (pullback.snd U.ι f).opensRange
    rw [Scheme.Hom.opensRange_pullbackSnd]
    simpa using hU.symm
  let a : Z ≅ (Over.pullback f).obj W := openOverIsoOfOpensRangeEq hrange
  refine ⟨W, inferInstance, ⟨?_⟩⟩
  exact J.representableSheafIsoOfSingletonDescent f hf F Z e W a

/-- If a sheaf becomes represented by a closed immersion after pullback along an fpqc
singleton cover which also covers for `J`, then it is represented by the descended closed
subscheme. -/
theorem closed_representableByProperty_of_fpqcCover
    (J : GrothendieckTopology Scheme.{u}) [J.Subcanonical]
    (hfpqc : IsFpqcCover f)
    (hf : Sieve.generate (Presieve.singleton f) ∈ J Y)
    (F : Sheaf (J.over Y) (Type u))
    (hF : (J.representableByProperty
      (@IsClosedImmersion : MorphismProperty Scheme.{u})).prop (.mk (op X))
        ((J.overMapPullback (Type u) f).obj F)) :
    (J.representableByProperty
      (@IsClosedImmersion : MorphismProperty Scheme.{u})).prop (.mk (op Y)) F := by
  obtain ⟨Z, hZ, ⟨e⟩⟩ := hF
  letI : IsClosedImmersion Z.hom := hZ
  let α := J.representedKernelPairIso f F Z e
  let eGeom := (Over.forget (pullback f f)).mapIso α
  have hα := α.hom.w
  change eGeom.hom ≫ pullback.snd Z.hom (pullback.snd f f) =
      pullback.snd Z.hom (pullback.fst f f) at hα
  obtain ⟨T, i, hi, e', he'⟩ :=
    exists_isClosedImmersion_of_fpqcCover hfpqc Z.hom eGeom hα
  let W : Over Y := Over.mk i
  letI : IsClosedImmersion W.hom := by
    dsimp [W]
    exact hi
  let a : Z ≅ (Over.pullback f).obj W := Over.isoMk e' he'.symm
  refine ⟨W, inferInstance, ⟨?_⟩⟩
  exact J.representableSheafIsoOfSingletonDescent f hf F Z e W a

/-- A surjective smooth morphism generates a covering sieve for the big étale topology.
The geometric input is that smooth surjections admit étale-local sections (Stacks 055U
and 055V). -/
theorem generate_singleton_mem_etaleTopology_of_smooth [Surjective f] [Smooth f] :
    Sieve.generate (Presieve.singleton f) ∈ etaleTopology Y := by
  obtain ⟨R, hR, hle⟩ := Hom.exists_etale_sieve_le_of_hasEtaleLocalSections f
    (Hom.hasEtaleLocalSections_of_smooth' f)
  exact etaleTopology.superset_covering hle hR

/-- A surjective smooth morphism, regarded as a morphism between its canonical
objects over a fixed base, generates a covering sieve for the relative big étale
topology. -/
theorem generate_singleton_mem_etaleTopology_over_of_smooth
    {S : Scheme.{u}} (a : Y ⟶ S) [Surjective f] [Smooth f] :
    Sieve.generate
        (Presieve.singleton
          (Over.homMk f : Over.mk (f ≫ a) ⟶ Over.mk a)) ∈
      (etaleTopology.over S) (Over.mk a) := by
  rw [etaleTopology.mem_over_iff, ← Presieve.ofArrows_pUnit]
  rw [Sieve.overEquiv_ofArrows]
  change Sieve.generate
      (Presieve.ofArrows (fun _ : PUnit.{1} ↦ X) (fun _ ↦ f)) ∈ etaleTopology Y
  rw [Presieve.ofArrows_pUnit.{0}]
  exact generate_singleton_mem_etaleTopology_of_smooth f

/-- An fppf morphism generates a covering sieve for the big fppf topology. -/
theorem generate_singleton_mem_fppfTopology_of_fppf
    [Surjective f] [Flat f] [LocallyOfFinitePresentation f] :
    Sieve.generate (Presieve.singleton f) ∈ fppfTopology Y :=
  Precoverage.generate_mem_toGrothendieck f.singleton_mem_fppfPrecoverage

/-- Descent of representability by `P` along a surjective smooth morphism, once the
geometric representability property is known to be local for the big étale topology. -/
theorem etale_representableByProperty_of_smooth (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange]
    [Pseudofunctor.ObjectProperty.IsLocal
      (etaleTopology.representableByProperty P) etaleTopology]
    [Surjective f] [Smooth f]
    (F : Sheaf (etaleTopology.over Y) (Type u))
    (hF : (etaleTopology.representableByProperty P).prop (.mk (op X))
      ((etaleTopology.overMapPullback (Type u) f).obj F)) :
    (etaleTopology.representableByProperty P).prop (.mk (op Y)) F := by
  exact etaleTopology.representableByProperty_of_map_obj P f
    (generate_singleton_mem_etaleTopology_of_smooth f) F hF

/-- Descent of representability by `P` along an fppf morphism, once the geometric
representability property is known to be local for the big fppf topology. -/
theorem fppf_representableByProperty_of_fppf (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange]
    [Pseudofunctor.ObjectProperty.IsLocal
      (fppfTopology.representableByProperty P) fppfTopology]
    [Surjective f] [Flat f] [LocallyOfFinitePresentation f]
    (F : Sheaf (fppfTopology.over Y) (Type u))
    (hF : (fppfTopology.representableByProperty P).prop (.mk (op X))
      ((fppfTopology.overMapPullback (Type u) f).obj F)) :
    (fppfTopology.representableByProperty P).prop (.mk (op Y)) F := by
  exact fppfTopology.representableByProperty_of_map_obj P f
    (generate_singleton_mem_fppfTopology_of_fppf f) F hF

end AlgebraicGeometry.Scheme
