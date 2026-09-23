module

public import StacksAndModuli.API.QuasiAffineMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.CategoryTheory.EquivalenceRelation

/-!
# Saturating open subschemes under a scheme relation

For two morphisms `source target : E ⇉ V`, this file constructs the saturation of
an open `U ⊆ V` under the relation represented by `E`.  If `target` is universally
open, the saturation is open; if `source` is quasi-compact and `U` is compact, it is
compact.  When the represented point relation is an equivalence relation, the
saturation contains `U` and is stable under the two relation maps.

This packages the topological core of the saturated-open construction in Stacks
Project Tag 02W8.  In applications, reflexivity, symmetry, and transitivity are supplied
by the unit, inverse, and cocycle identities of a descent datum.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {E V X : Scheme.{u}}

/-- The point relation on `V` represented by a pair of scheme morphisms `E ⇉ V`. -/
def Hom.generatedRelation (source target : E ⟶ V) (x y : V) : Prop :=
  ∃ z : E, source z = x ∧ target z = y

section KernelPairDescentRelation

variable {S' S X' : Scheme.{u}} (p : X' ⟶ S') (f : S' ⟶ S)

/-- The relation object on `X'` associated to the kernel pair of `f : S' ⟶ S`.
It is the pullback of `X' ⟶ S'` along the first kernel-pair projection. -/
noncomputable abbrev Hom.kernelPairRelationObject : Scheme.{u} :=
  pullback p (pullback.fst f f)

/-- The source map of the relation associated to a kernel-pair descent isomorphism. -/
noncomputable def Hom.kernelPairRelationSource :
    p.kernelPairRelationObject f ⟶ X' :=
  pullback.fst p (pullback.fst f f)

/-- The target map of the relation associated to a kernel-pair descent isomorphism:
transport from the first pullback of `X'` to the second and then project to `X'`. -/
noncomputable def Hom.kernelPairRelationTarget
    (α : (Over.pullback (pullback.fst f f)).obj (Over.mk p) ≅
      (Over.pullback (pullback.snd f f)).obj (Over.mk p)) :
    p.kernelPairRelationObject f ⟶ X' :=
  α.hom.left ≫ pullback.fst p (pullback.snd f f)

/-- The source and target maps attached to a kernel-pair descent isomorphism are
jointly monic.  The two images recover the two points of `S' ×_S S'`, while the first
image also recovers the point of `X'`. -/
lemma Hom.kernelPairRelation_jointlyMono
    (α : (Over.pullback (pullback.fst f f)).obj (Over.mk p) ≅
      (Over.pullback (pullback.snd f f)).obj (Over.mk p)) :
    JointlyMono₂ (p.kernelPairRelationSource f) (p.kernelPairRelationTarget f α) := by
  constructor
  intro Y a b ha hb
  change a ≫ pullback.fst p (pullback.fst f f) =
    b ≫ pullback.fst p (pullback.fst f f) at ha
  change a ≫ (α.hom.left ≫ pullback.fst p (pullback.snd f f)) =
    b ≫ (α.hom.left ≫ pullback.fst p (pullback.snd f f)) at hb
  apply pullback.hom_ext
  · exact ha
  · apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [← pullback.condition]
      simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ p) ha
    · have hα := α.hom.w
      change α.hom.left ≫ pullback.snd p (pullback.snd f f) =
        pullback.snd p (pullback.fst f f) at hα
      simp only [Category.assoc]
      rw [← hα]
      rw [Category.assoc, ← pullback.condition]
      simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ p) hb

/-- The relation maps induced by a kernel-pair descent isomorphism, together with the
identity, inversion, and composition maps supplied by its unit, inverse, and cocycle
identities.  Only the endpoint equations are retained because they are precisely what
is needed to obtain an internal equivalence relation and to saturate opens. -/
structure Hom.KernelPairDescentRelation where
  /-- The descent isomorphism over `S' ×_S S'`. -/
  alpha : (Over.pullback (pullback.fst f f)).obj (Over.mk p) ≅
    (Over.pullback (pullback.snd f f)).obj (Over.mk p)
  /-- Identity arrows, induced by the unit identity on the diagonal. -/
  unit : X' ⟶ p.kernelPairRelationObject f
  unit_source : unit ≫ p.kernelPairRelationSource f = 𝟙 X'
  unit_target : unit ≫ p.kernelPairRelationTarget f alpha = 𝟙 X'
  /-- Inversion, induced by transposing the kernel pair and using `alpha.inv`. -/
  inverse : p.kernelPairRelationObject f ⟶ p.kernelPairRelationObject f
  inverse_source : inverse ≫ p.kernelPairRelationSource f =
    p.kernelPairRelationTarget f alpha
  inverse_target : inverse ≫ p.kernelPairRelationTarget f alpha =
    p.kernelPairRelationSource f
  /-- Composition of composable arrows, induced by the cocycle identity on the
  threefold fiber product. -/
  composition :
    pullback (p.kernelPairRelationTarget f alpha) (p.kernelPairRelationSource f) ⟶
      p.kernelPairRelationObject f
  composition_source : composition ≫ p.kernelPairRelationSource f =
    pullback.fst (p.kernelPairRelationTarget f alpha)
      (p.kernelPairRelationSource f) ≫ p.kernelPairRelationSource f
  composition_target : composition ≫ p.kernelPairRelationTarget f alpha =
    pullback.snd (p.kernelPairRelationTarget f alpha)
      (p.kernelPairRelationSource f) ≫ p.kernelPairRelationTarget f alpha

namespace Hom.KernelPairDescentRelation

/-- The internal equivalence relation assembled from the unit, inverse, and cocycle
maps of a kernel-pair descent relation. -/
noncomputable def equivalenceRelation (D : p.KernelPairDescentRelation f) :
    CategoryTheory.EquivalenceRelation
      (p.kernelPairRelationSource f) (p.kernelPairRelationTarget f D.alpha) where
  right_cancellation := (p.kernelPairRelation_jointlyMono f D.alpha).right_cancellation
  r := D.unit
  reflexivity₁ := D.unit_source
  reflexivity₂ := D.unit_target
  s := D.inverse
  symmetry₁ := D.inverse_source
  symmetry₂ := D.inverse_target
  c := pullback.cone (p.kernelPairRelationTarget f D.alpha)
    (p.kernelPairRelationSource f)
  isLimit := limit.isLimit _
  t := D.composition
  transitivity₁ := D.composition_source
  transitivity₂ := D.composition_target

end Hom.KernelPairDescentRelation

end KernelPairDescentRelation

/-- An internal equivalence relation of schemes induces an equivalence relation on
the underlying points.  Transitivity uses surjectivity of the comparison from the
scheme-theoretic pullback to the pullback of the underlying point sets; this is why it
cannot be obtained merely by asking the underlying-space functor to preserve
pullbacks. -/
lemma Hom.generatedRelation_equivalence (source target : E ⟶ V)
    (hrel : CategoryTheory.EquivalenceRelation source target) :
    Equivalence (source.generatedRelation target) where
  refl x := by
    refine ⟨hrel.r x, ?_, ?_⟩
    · have h := congrArg (fun k : V ⟶ V ↦ (Scheme.forget.map k) x)
        hrel.reflexivity₁
      change source (hrel.r x) = x at h
      exact h
    · have h := congrArg (fun k : V ⟶ V ↦ (Scheme.forget.map k) x)
        hrel.reflexivity₂
      change target (hrel.r x) = x at h
      exact h
  symm := by
    intro x y
    rintro ⟨z, hz₁, hz₂⟩
    refine ⟨hrel.s z, ?_, ?_⟩
    · have h := congrArg (fun k : E ⟶ V ↦ (Scheme.forget.map k) z)
        hrel.symmetry₁
      change source (hrel.s z) = target z at h
      exact h.trans hz₂
    · have h := congrArg (fun k : E ⟶ V ↦ (Scheme.forget.map k) z)
        hrel.symmetry₂
      change target (hrel.s z) = source z at h
      exact h.trans hz₁
  trans := by
    intro x y z
    rintro ⟨a, ha₁, ha₂⟩ ⟨b, hb₁, hb₂⟩
    obtain ⟨q, hq₁, hq₂⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := target) (g := source) a b (ha₂.trans hb₁.symm)
    let l : pullback target source ⟶ hrel.c.pt :=
      hrel.isLimit.lift (pullback.cone target source)
    refine ⟨hrel.t (l q), ?_, ?_⟩
    · have hl : hrel.c.fst (l q) = pullback.fst target source q := by
        have h := congrArg
          (fun k : pullback target source ⟶ E ↦ (Scheme.forget.map k) q)
          (hrel.isLimit.fac (pullback.cone target source) WalkingCospan.left)
        change hrel.c.fst (l q) = pullback.fst target source q at h
        exact h
      have ht := congrArg (fun k : hrel.c.pt ⟶ V ↦
        (Scheme.forget.map k) (l q)) hrel.transitivity₁
      change source (hrel.t (l q)) = source (hrel.c.fst (l q)) at ht
      calc
        source (hrel.t (l q)) = source (hrel.c.fst (l q)) := ht
        _ = source (pullback.fst target source q) := congrArg source hl
        _ = source a := congrArg source hq₁
        _ = x := ha₁
    · have hl : hrel.c.snd (l q) = pullback.snd target source q := by
        have h := congrArg
          (fun k : pullback target source ⟶ E ↦ (Scheme.forget.map k) q)
          (hrel.isLimit.fac (pullback.cone target source) WalkingCospan.right)
        change hrel.c.snd (l q) = pullback.snd target source q at h
        exact h
      have ht := congrArg (fun k : hrel.c.pt ⟶ V ↦
        (Scheme.forget.map k) (l q)) hrel.transitivity₂
      change target (hrel.t (l q)) = target (hrel.c.snd (l q)) at ht
      calc
        target (hrel.t (l q)) = target (hrel.c.snd (l q)) := ht
        _ = target (pullback.snd target source q) := congrArg target hl
        _ = target b := congrArg target hq₂
        _ = z := hb₂

/-- The set-theoretic saturation of `U` under the relation `source, target : E ⇉ V`. -/
def Hom.saturationSet (source target : E ⟶ V) (U : Set V) : Set V :=
  target.base '' (source.base ⁻¹' U)

/-- The saturation of an open under an open scheme relation. -/
def Hom.saturation (source target : E ⟶ V) [UniversallyOpen target]
    (U : V.Opens) : V.Opens :=
  ⟨target.base '' (source.base ⁻¹' (U : Set V)),
    target.isOpenMap _ (U.2.preimage source.continuous)⟩

@[simp]
lemma Hom.coe_saturation (source target : E ⟶ V) [UniversallyOpen target]
    (U : V.Opens) :
    (source.saturation target U : Set V) =
      target.base '' (source.base ⁻¹' (U : Set V)) := rfl

/-- Saturation preserves compactness when the source map of the relation is
quasi-compact. -/
lemma Hom.isCompact_saturation (source target : E ⟶ V) [UniversallyOpen target]
    [QuasiCompact source] (U : V.Opens) (hU : IsCompact (U : Set V)) :
    IsCompact (source.saturation target U : Set V) :=
  (QuasiCompact.isCompact_preimage (f := source) _ U.2 hU).image target.continuous

/-- An open is contained in its saturation under a reflexive relation. -/
lemma Hom.le_saturation (source target : E ⟶ V) [UniversallyOpen target]
    (hrel : Equivalence (source.generatedRelation target)) (U : V.Opens) :
    U ≤ source.saturation target U := by
  intro x hx
  obtain ⟨z, hz₁, hz₂⟩ := hrel.refl x
  refine ⟨z, ?_, hz₂⟩
  change source z ∈ U
  simpa [hz₁] using hx

/-- The saturation of an open under an equivalence relation is stable under the two
relation maps. -/
lemma Hom.preimage_saturation_eq (source target : E ⟶ V)
    [UniversallyOpen target]
    (hrel : Equivalence (source.generatedRelation target)) (U : V.Opens) :
    source ⁻¹ᵁ (source.saturation target U) =
      target ⁻¹ᵁ (source.saturation target U) := by
  ext z
  change source z ∈ source.saturation target U ↔
    target z ∈ source.saturation target U
  constructor
  · rintro ⟨w, hwU, hwz⟩
    have hr₁ : source.generatedRelation target (source w) (target w) := ⟨w, rfl, rfl⟩
    have hr₂ : source.generatedRelation target (target w) (target z) := by
      rw [hwz]
      exact ⟨z, rfl, rfl⟩
    obtain ⟨w', hw'₁, hw'₂⟩ := hrel.trans hr₁ hr₂
    refine ⟨w', ?_, hw'₂⟩
    change source w' ∈ U
    rw [hw'₁]
    exact hwU
  · rintro ⟨w, hwU, hwz⟩
    have hr₁ : source.generatedRelation target (source w) (target w) := ⟨w, rfl, rfl⟩
    have hr₂ : source.generatedRelation target (target w) (source z) := by
      rw [hwz]
      exact hrel.symm ⟨z, rfl, rfl⟩
    obtain ⟨w', hw'₁, hw'₂⟩ := hrel.trans hr₁ hr₂
    refine ⟨w', ?_, hw'₂⟩
    change source w' ∈ U
    rw [hw'₁]
    exact hwU

/-- In the affine-target situation of Tag 02W8, the saturation of a compact open in a
separated locally quasi-finite finite-type scheme is quasi-affine over the target. -/
lemma Hom.isQuasiAffine_saturation_comp (source target : E ⟶ V)
    [UniversallyOpen target] [QuasiCompact source]
    (U : V.Opens) (hU : IsCompact (U : Set V))
    (p : V ⟶ X) [IsAffine X] [LocallyOfFiniteType p] [LocallyQuasiFinite p]
    [IsSeparated p] :
    IsQuasiAffineHom ((source.saturation target U).ι ≫ p) := by
  letI : CompactSpace (source.saturation target U) :=
    isCompact_iff_compactSpace.mp (source.isCompact_saturation target U hU)
  apply isQuasiAffineHom_of_quasiCompact_locallyOfFiniteType_locallyQuasiFinite_isSeparated

/-- The stable quasi-affine chart produced by saturating a compact open under an
internal equivalence relation.  In descent applications, the relation's reflexivity,
symmetry, and transitivity maps are induced respectively by the unit, inverse, and
cocycle of the kernel-pair descent isomorphism. -/
lemma Hom.exists_saturated_quasiAffineOpen (source target : E ⟶ V)
    [UniversallyOpen target] [QuasiCompact source]
    (hrel : CategoryTheory.EquivalenceRelation source target)
    (U : V.Opens) (hU : IsCompact (U : Set V))
    (p : V ⟶ X) [IsAffine X] [LocallyOfFiniteType p] [LocallyQuasiFinite p]
    [IsSeparated p] :
    ∃ W : V.Opens,
      U ≤ W ∧ IsCompact (W : Set V) ∧
        source ⁻¹ᵁ W = target ⁻¹ᵁ W ∧ IsQuasiAffineHom (W.ι ≫ p) := by
  let hpoints := source.generatedRelation_equivalence target hrel
  exact ⟨source.saturation target U,
    source.le_saturation target hpoints U,
    source.isCompact_saturation target U hU,
    source.preimage_saturation_eq target hpoints U,
    source.isQuasiAffine_saturation_comp target U hU p⟩

/-- A kernel-pair descent relation turns every compact open into a larger compact,
stable, quasi-affine chart.  This is the form of the saturated-open construction used
in the proof of effective fppf descent for separated locally quasi-finite schemes. -/
lemma Hom.KernelPairDescentRelation.exists_saturated_quasiAffineOpen
    {S' S X' Y : Scheme.{u}} {p : X' ⟶ S'} {f : S' ⟶ S}
    (D : p.KernelPairDescentRelation f)
    [UniversallyOpen (p.kernelPairRelationTarget f D.alpha)]
    [QuasiCompact (p.kernelPairRelationSource f)]
    (U : X'.Opens) (hU : IsCompact (U : Set X'))
    (q : X' ⟶ Y) [IsAffine Y] [LocallyOfFiniteType q] [LocallyQuasiFinite q]
    [IsSeparated q] :
    ∃ W : X'.Opens,
      U ≤ W ∧ IsCompact (W : Set X') ∧
        p.kernelPairRelationSource f ⁻¹ᵁ W =
          p.kernelPairRelationTarget f D.alpha ⁻¹ᵁ W ∧
        IsQuasiAffineHom (W.ι ≫ q) :=
  Hom.exists_saturated_quasiAffineOpen
    (p.kernelPairRelationSource f) (p.kernelPairRelationTarget f D.alpha)
    D.equivalenceRelation U hU q

end AlgebraicGeometry.Scheme
