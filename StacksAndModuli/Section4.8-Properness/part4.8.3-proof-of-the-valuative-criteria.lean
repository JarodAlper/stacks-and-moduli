module

public import StacksAndModuli.API.DVRSpecialization
public import StacksAndModuli.API.QuasiSeparatedPoints
public import StacksAndModuli.«Section4.8-Properness».«part4.8.2-valuative-criteria»

/-!
# Properness and the valuative criterion: proof of the valuative criteria

This module formalizes `lem:lifting-criterion-for-closedness-stacks` and
`prop:geometry-dvrs-stacks`, and covers `exer:valuative-separated-diagonal`, of §4.8
(Properness and the Valuative Criterion) of *Stacks and Moduli*,
label `sec:valuative-criteria`.

Main declarations:
- `AlgebraicGeometry.BasedFunctor.isClosedMap_mapPoints_iff_specializingMap`: the lifting
  criterion for closedness — a quasi-compact morphism of algebraic stacks is closed if
  and only if specializations lift along it (statement; proof deferred);
- `AlgebraicGeometry.BasedCategory.IsNoetherian`: noetherian algebraic stacks,
  realizing the §4.3 ledger entry;
- `AlgebraicGeometry.BasedFunctor.exists_valuativeCommSq_of_specializes` and
  `AlgebraicGeometry.BasedCategory.exists_spec_isDiscreteValuationRing_of_specializes`:
  specializations in noetherian algebraic stacks are realized by spectra of discrete
  valuation rings (proved from the specialization-lifting exercise for open stack
  morphisms and the scheme-level geometry of DVRs).

The proofs of the valuative criteria themselves, and the exercise on the separated
diagonal, remain ledgered below.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false


section LemLiftingCriterionForClosednessStacks

open CategoryTheory Functor AlgebraicGeometry CategoryTheory.BasedCategory
  AlgebraicGeometry.BasedCategory

universe v₂ v₃ u₂ u₃ u

namespace AlgebraicGeometry.BasedFunctor

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} {𝒴 : BasedCategory.{v₃, u₃} Scheme.{u}}

/-- **Lemma 4.8.20** (`lem:lifting-criterion-for-closedness-stacks`; Lifting criterion
for closedness): let $f \colon \cX \to \cY$ be a quasi-compact morphism of algebraic
stacks. Then the induced map $|\cX| \to |\cY|$ is closed if and only if it is
specializing: for every point $x \in |\cX|$, every specialization
$f(x) \rightsquigarrow y_0$ lifts to a specialization $x \rightsquigarrow x_0$. -/
theorem isClosedMap_mapPoints_iff_specializingMap [IsAlgebraicStack 𝒳]
    [IsAlgebraicStack 𝒴] {F : 𝒳 ⥤ᵇ 𝒴} (hF : QuasiCompact F) :
    IsClosedMap (mapPoints F) ↔ SpecializingMap (mapPoints F) := by
  sorry

/- The forward implication needs no hypothesis on `f` (a closed map is specializing,
Mathlib's `IsClosedMap.specializingMap`); the converse reduces, by replacing `𝒳` with the
reduced closed substack structure on `closure {x}` (`exer:closed-subsets-and-substacks`,
§4.3), to the fact that a quasi-compact image closed under specialization is closed
(`exer:specialization-properties` (a), §4.3,
`AlgebraicGeometry.BasedFunctor.mem_closure_range_mapPoints_iff_specializes`). -/

end AlgebraicGeometry.BasedFunctor

end LemLiftingCriterionForClosednessStacks


section PropGeometryDvrsStacks

open CategoryTheory Functor AlgebraicGeometry CategoryTheory.BasedCategory
  AlgebraicGeometry.BasedCategory

universe v₂ v₃ u₂ u₃ u

namespace AlgebraicGeometry.BasedCategory

section DefQuasiCompact

/-- Named API specialization of Definition 4.3.11, part (2): an algebraic stack is
quasi-separated when its projection to the base is a quasi-separated morphism. This
realizes the absolute form used in the §4.3 ledger. -/
abbrev IsQuasiSeparated (𝒳 : BasedCategory.{v₂, u₂} Scheme.{u})
    [𝒳.p.IsFiberedInGroupoids] : Prop :=
  BasedFunctor.QuasiSeparated 𝒳.toBase

/-- **Definition 4.3.21** (`def:quasi-compact`) (noetherian algebraic stacks): an
algebraic stack is *noetherian* if it is locally noetherian, quasi-compact, and
quasi-separated. (This realizes the definition of noetherian algebraic stacks of §4.3,
recorded there as a ledger pending the §4.2 diagonal.) -/
def IsNoetherian (𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}) [𝒳.p.IsFiberedInGroupoids] :
    Prop :=
  IsLocallyNoetherian 𝒳 ∧ IsQuasiCompact 𝒳 ∧ IsQuasiSeparated 𝒳

end DefQuasiCompact

end AlgebraicGeometry.BasedCategory

namespace AlgebraicGeometry.BasedFunctor

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} {𝒴 : BasedCategory.{v₃, u₃} Scheme.{u}}

/-- **Proposition 4.8.21** (`prop:geometry-dvrs-stacks`; Geometry of DVRs for stacks):
let $f \colon \cX \to \cY$ be a finite type morphism of noetherian algebraic stacks, let
$x \in |\cX|$, and let $f(x) \rightsquigarrow y_0$ be a specialization. Then there is a
valuative square over $f$ whose top morphism $\Spec K \to \cX$ has image $x$ and whose
bottom morphism $\Spec R \to \cY$ realizes the specialization
$f(x) \rightsquigarrow y_0$, i.e. sends the closed point of $\Spec R$ to $y_0$. -/
theorem exists_valuativeCommSq_of_specializes [IsAlgebraicStack 𝒳] [IsAlgebraicStack 𝒴]
    (_h𝒳 : BasedCategory.IsNoetherian 𝒳) (h𝒴 : BasedCategory.IsNoetherian 𝒴)
    {F : 𝒳 ⥤ᵇ 𝒴} (hF : FiniteType F) (x : pointSpace 𝒳) {y₀ : pointSpace 𝒴}
    (h : mapPoints F x ⤳ y₀) :
    ∃ S : ValuativeCommSq F, pointSpace.mk S.fieldPoint = x ∧
      mapPoints S.y ((Spec (CommRingCat.of S.R)).toPointSpace
        (IsLocalRing.closedPoint S.R)) = y₀ := by
  classical
  obtain ⟨V, g, hg⟩ := IsAlgebraicStack.exists_presentation (𝒳 := 𝒴)
  have hopenNu : IsOpenMap (BasedCategory.quotientMapOfPresentation.nu g) :=
    BasedCategory.quotientMapOfPresentation.isOpenMap_nu g hg
  have hopen : IsOpenMap (mapPoints g) := by
    intro W hW
    have hpre : IsOpen (V.toPointSpace ⁻¹' W) :=
      hW.preimage (BasedCategory.quotientMapOfPresentation.continuous_toPointSpace V)
    have himage : BasedCategory.quotientMapOfPresentation.nu g ''
        (V.toPointSpace ⁻¹' W) = mapPoints g '' W := by
      change (mapPoints g ∘ V.toPointSpace) '' (V.toPointSpace ⁻¹' W) = _
      rw [Set.image_comp, Set.image_preimage_eq _ V.surjective_toPointSpace]
    rw [← himage]
    exact hopenNu _ hpre
  have hgsurj : Function.Surjective (mapPoints g) :=
    BasedCategory.surjective_mapPoints_of_representableWith g hg
  obtain ⟨v₀, hv₀⟩ := hgsurj y₀
  have hyqc : BasedCategory.HasQuasiCompactRepresentative (mapPoints F x) :=
    h𝒴.2.2.hasQuasiCompactRepresentative (mapPoints F x)
  obtain ⟨v, hvv₀, hv⟩ :=
    exists_specializes_of_isOpenMap_mapPoints hopen v₀ hyqc (hv₀ ▸ h)
  obtain ⟨z, hzx, hzv⟩ :=
    exists_mapPoints_fiberProduct_eq F g x v hv.symm
  let Z := fiberProduct F g
  let _ : IsAlgebraicStack Z := IsAlgebraicStack.fiberProduct F g
  obtain ⟨U, q, hq⟩ := IsAlgebraicStack.exists_presentation (𝒳 := Z)
  have hqsurj : Function.Surjective (mapPoints q) :=
    BasedCategory.surjective_mapPoints_of_representableWith q hq
  obtain ⟨uPoint, huPoint⟩ := hqsurj z
  obtain ⟨u, hu⟩ := U.surjective_toPointSpace uPoint
  let p := fiberProductSnd F g
  let f := (q.comp p).overHom
  obtain ⟨ef⟩ := CategoryTheory.BasedFunctor.nonempty_iso_overBased_map (q.comp p)
  have hfu : V.toPointSpace (f.base u) = v := by
    rw [← BasedCategory.quotientMapOfPresentation.mapPoints_overBased_map_toPointSpace f u]
    rw [← BasedCategory.quotientMapOfPresentation.mapPoints_eq_of_iso ef]
    rw [BasedCategory.quotientMapOfPresentation.mapPoints_comp, hu, huPoint, hzv]
  obtain ⟨v₀Point, hv₀Point⟩ := V.surjective_toPointSpace v₀
  have hinducing : Topology.IsInducing V.toPointSpace :=
    (Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
      (BasedCategory.quotientMapOfPresentation.continuous_toPointSpace V)
      V.injective_toPointSpace V.isOpenMap_toPointSpace).isInducing
  have hschemeSpecializes : f.base u ⤳ v₀Point := by
    apply hinducing.specializes_iff.mp
    rw [hfu, hv₀Point]
    exact hvv₀
  have hVloc : _root_.AlgebraicGeometry.IsLocallyNoetherian V := h𝒴.1 V g hg
  let _ : _root_.AlgebraicGeometry.IsLocallyNoetherian V := hVloc
  have hflft : _root_.AlgebraicGeometry.LocallyOfFiniteType f :=
    hF.1 V g hg U q hq
  let _ : _root_.AlgebraicGeometry.LocallyOfFiniteType f := hflft
  obtain ⟨D⟩ := f.dvrRealizesSpecializations_of_locallyOfFiniteType
    u v₀Point hschemeSpecializes
  let _ : IsDiscreteValuationRing D.sq.R := D.dvr
  let topPre : overBased (Spec (CommRingCat.of D.sq.K)) ⥤ᵇ Z :=
    (overBased.map D.sq.i₁).comp q
  let xMap : overBased (Spec (CommRingCat.of D.sq.K)) ⥤ᵇ 𝒳 :=
    topPre.comp (fiberProductFst F g)
  let yMap : overBased (Spec (CommRingCat.of D.sq.R)) ⥤ᵇ 𝒴 :=
    (overBased.map D.sq.i₂).comp g
  have eScheme : topPre.comp p ≅
      (overBased.map (Spec.map (CommRingCat.ofHom
        (algebraMap D.sq.R D.sq.K)))).comp (overBased.map D.sq.i₂) := by
    refine (isoWhiskerLeft (overBased.map D.sq.i₁) ef).trans ?_
    rw [← overBased.map_comp, ← overBased.map_comp, D.sq.commSq.w]
  have eComm : xMap.comp F ≅
      (overBased.map (Spec.map (CommRingCat.ofHom
        (algebraMap D.sq.R D.sq.K)))).comp yMap := by
    refine (isoWhiskerLeft topPre (fiberProductIsoComm F g)).trans ?_
    simpa only [xMap, yMap, topPre, p, CategoryTheory.BasedFunctor.comp_assoc] using
      isoWhiskerRight eScheme g
  let S : ValuativeCommSq F :=
    { R := D.sq.R
      K := D.sq.K
      x := xMap
      y := yMap
      isoComm := eComm }
  refine ⟨S, ?_, ?_⟩
  · have htop : pointSpace.mk
        (⟨D.sq.K, (overBased.map D.sq.i₁).comp
          (q.comp (fiberProductFst F g))⟩ : FieldPoint 𝒳) = x := by
      rw [BasedCategory.quotientMapOfPresentation.mk_comp_map_eq_nu
        D.sq.K D.sq.i₁ (q.comp (fiberProductFst F g))
        (IsLocalRing.closedPoint D.sq.K)]
      rw [D.generic_eq]
      change mapPoints (q.comp (fiberProductFst F g)) (U.toPointSpace u) = x
      rw [BasedCategory.quotientMapOfPresentation.mapPoints_comp, hu, huPoint, hzx]
    simpa only [S, ValuativeCommSq.fieldPoint, xMap, topPre,
      CategoryTheory.BasedFunctor.comp_assoc] using htop
  · have hbottom : mapPoints yMap
        ((Spec (CommRingCat.of D.sq.R)).toPointSpace
          (IsLocalRing.closedPoint D.sq.R)) = y₀ := by
      change BasedCategory.quotientMapOfPresentation.nu yMap
        (IsLocalRing.closedPoint D.sq.R) = y₀
      calc
        _ = BasedCategory.quotientMapOfPresentation.nu g
            (D.sq.i₂.base (IsLocalRing.closedPoint D.sq.R)) :=
          BasedCategory.quotientMapOfPresentation.nu_comp_map D.sq.i₂ g _
        _ = BasedCategory.quotientMapOfPresentation.nu g v₀Point :=
          congrArg (BasedCategory.quotientMapOfPresentation.nu g) D.closed_eq
        _ = mapPoints g (V.toPointSpace v₀Point) := rfl
        _ = y₀ := by rw [hv₀Point, hv₀]
    simpa only [S] using hbottom

/-- **Proposition 4.8.21** (`prop:geometry-dvrs-stacks`) (the "in particular" statement:
specializations within a single stack): every specialization $x \rightsquigarrow x_0$ in
a noetherian algebraic stack is realized by a morphism $\Spec R \to \cX$ from the
spectrum of a discrete valuation ring — the generic point of $\Spec R$ maps to $x$ and
the closed point to $x_0$. -/
theorem _root_.AlgebraicGeometry.BasedCategory.exists_spec_isDiscreteValuationRing_of_specializes
    [IsAlgebraicStack 𝒳] (h𝒳 : BasedCategory.IsNoetherian 𝒳) {x x₀ : pointSpace 𝒳}
    (h : x ⤳ x₀) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (y : overBased (Spec (CommRingCat.of R)) ⥤ᵇ 𝒳),
      mapPoints y ((Spec (CommRingCat.of R)).toPointSpace
        (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)) = x ∧
      mapPoints y ((Spec (CommRingCat.of R)).toPointSpace
        (IsLocalRing.closedPoint R)) = x₀ := by
  let F := BasedFunctor.id 𝒳
  have hltf : LocallyOfFiniteType F := by
    apply hasPropertyOfPresentations_of_exists
      AlgebraicGeometry.isSmoothLocal_locallyOfFiniteType.isLocalOnSourceAlong
      AlgebraicGeometry.isSmoothLocal_locallyOfFiniteType.isLocalOnTargetAlong
    obtain ⟨V, g, hg⟩ := IsAlgebraicStack.exists_presentation (𝒳 := 𝒳)
    let q := fiberProductIdInv g
    let _ : q.toFunctor.IsEquivalence := isEquivalence_fiberProductIdInv g
    let _ : (fiberProductSnd F g).toFunctor.IsEquivalence :=
      isEquivalence_fiberProductSnd_id g
    have hq : RepresentableWith
        (@_root_.AlgebraicGeometry.Surjective ⊓
          @_root_.AlgebraicGeometry.Smooth : MorphismProperty Scheme.{u}) q :=
      (RepresentableWith.surjectiveEtale_of_isEquivalence q).mono
        (inf_le_inf le_rfl etale_le_smooth)
    refine ⟨V, g, hg, V, q, hq, ?_⟩
    have he : (q.comp (fiberProductSnd F g)).toFunctor.IsEquivalence :=
      Functor.isEquivalence_trans q.toFunctor (fiberProductSnd F g).toFunctor
    have hi : CategoryTheory.IsIso (q.comp (fiberProductSnd F g)).overHom :=
      CategoryTheory.BasedFunctor.isIso_overHom_of_isEquivalence _ he
    infer_instance
  have hqc : QuasiCompact F := by
    intro B g
    change CompactSpace (pointSpace (fiberProduct F g))
    let E := fiberProductIdInv g
    have hE : E.toFunctor.IsEquivalence := isEquivalence_fiberProductIdInv g
    have hsurj : Function.Surjective (mapPoints E) :=
      surjective_mapPoints_of_isEquivalence E hE
    have hcompactSource : CompactSpace (pointSpace (overBased (Spec B))) := by
      obtain ⟨e⟩ := Scheme.nonempty_homeomorph_pointSpace (Spec B)
      exact e.symm.compactSpace
    let _ := hcompactSource
    rw [← isCompact_univ_iff]
    rw [← hsurj.range_eq]
    simpa only [Set.image_univ] using
      (isCompact_univ.image (continuous_mapPoints' E))
  have hft : FiniteType F := ⟨hltf, hqc⟩
  have hid : mapPoints F x = x := by simp [F]
  obtain ⟨S, hSx, hSx₀⟩ :=
    exists_valuativeCommSq_of_specializes h𝒳 h𝒳 hft x (hid ▸ h)
  refine ⟨S.R, inferInstance, inferInstance, inferInstance, S.y, ?_, hSx₀⟩
  rw [← hSx]
  let z : Spec (CommRingCat.of S.K) := ⟨⊥, Ideal.isPrime_bot⟩
  have hz : S.specFractionMap.base z =
      (⟨⊥, Ideal.isPrime_bot⟩ : Spec (CommRingCat.of S.R)) := by
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap S.R S.K) ⊥ = ⊥
    exact Ideal.comap_bot_of_injective _
      (FaithfulSMul.algebraMap_injective S.R S.K)
  rw [← hz,
    ← BasedCategory.quotientMapOfPresentation.mapPoints_overBased_map_toPointSpace]
  rw [← BasedCategory.quotientMapOfPresentation.mapPoints_comp]
  rw [← BasedCategory.quotientMapOfPresentation.mapPoints_eq_of_iso S.isoComm]
  rw [BasedCategory.quotientMapOfPresentation.mapPoints_comp]
  rw [BasedCategory.quotientMapOfPresentation.toPointSpace_spec_field]
  have hmapid : mapPoints F = id := mapPoints_id 𝒳
  rw [hmapid]
  change pointSpace.mk (⟨S.K, (BasedFunctor.id _).comp S.x⟩ : FieldPoint 𝒳) =
    pointSpace.mk S.fieldPoint
  rw [BasedFunctor.id_comp]

/- AXIOM LEDGER (`prop:geometry-dvrs-stacks`): the presentation argument is complete.
Quasi-separatedness of `𝒴` gives a quasi-compact representative of `mapPoints F x`, so
the corrected `BasedFunctor.exists_specializes_of_isOpenMap_mapPoints` (Exercise
4.3.31(b)) lifts the specialization to `V`; that theorem currently depends on part (a)
of the exercise. The scheme-level input is the axiom-clean theorem
`Scheme.Hom.dvrRealizesSpecializations_of_locallyOfFiniteType` from
`StacksAndModuli/API/DVRSpecialization.lean`, which formalizes the content of Proposition A.4.4.

LEDGER (proof of `thm:valuative-criteria-stacks`): beyond
`lem:lifting-criterion-for-closedness-stacks` and `prop:geometry-dvrs-stacks`, the proof
uses: the reduction of universal closedness to *finite type* base changes `T → Y` over a
noetherian base via `lem:technical-reduction` (appendix A.4 — no StacksAndModuli section yet);
the reduced closed substack structure on `closure {x}` (`exer:closed-subsets-and-substacks`,
§4.3); smooth-locality of universal closedness on the target
(`universallyClosed_iff_isClosedMap_mapPoints_fiberProductSnd`, part 4.8.1); and, for the
criteria (2) and (3), the observation that (assuming separated diagonal) the valuative
criterion for separatedness of `f` is the valuative criterion for universal closedness of
`Δ_f`. See also Stacks 0CLQ, 0CLS, 0CLV, 0CLY. -/

end AlgebraicGeometry.BasedFunctor

end PropGeometryDvrsStacks


section ExerValuativeSeparatedDiagonal

/- LEDGER (`exer:valuative-separated-diagonal`): the exercise asks to prove the valuative
criterion for separated diagonal, i.e. the equivalence
`AlgebraicGeometry.BasedFunctor.isSeparatedRepresentable_diag_iff_forall_lifting_hom_eq_id`
stated (with deferred proof) in part 4.8.2. The book's commented solution: for a lifting
`(x̃, β, γ)` of a valuative square and an automorphism `Θ` of it, the compatibilities
force `j^*Θ = id` and `f(Θ) = id`, so `(x̃, Θ)` defines an object of the relative inertia
`I_{𝒳/𝒴}` over `Spec R` (`part4.2.3-inertia`) and a valuative square over the double
diagonal `e : 𝒳 → I_{𝒳/𝒴}`; since `e` is a quasi-compact monomorphism representable by
schemes, the scheme-level valuative criterion (`thm:valuative-criteria-schemes`, DVR-based
— absent from Mathlib, whose `AlgebraicGeometry.ValuativeCriterion` is
valuation-ring-based) shows that `e` is a closed immersion, which is equivalent to `Δ_f`
being separated by `exer:diagonal-characterizations`, which is now *stated* — as
`AlgebraicGeometry.BasedFunctor.tfae_isSeparatedRepresentable_diag` in part4.8.1 — though
not proved. Still blocked on: the identification of liftings-with-automorphism with
`I_{𝒳/𝒴}`-valued squares (needs the 2-Yoneda lemma of §3.4.4, still sorried), on the proof
of `exer:diagonal-characterizations`, and on the DVR-based scheme criterion
(appendix A.4). -/

end ExerValuativeSeparatedDiagonal
