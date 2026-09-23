module

public import StacksAndModuli.API.AffineSheafMorphismZeroLocus
public import StacksAndModuli.API.OpenCoverModuleMorphismZero
public import StacksAndModuli.API.QuotFunctorPrecomposition
public import StacksAndModuli.API.QuotFunctorZariskiDescent
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Quotient-kernel zero loci from compatible affine finite models

This file supplies the gluing endgame between finite affine vanishing models and
`Scheme.QuotientKernelZeroLocusData`.

The input is deliberately split into the genuinely geometric assertions which
remain after the coefficient-ideal construction.

* `AffineFiniteFreeKernelVanishingCertificate` gives, on one affine test object, a
  `Modules.HasFiniteFreeVanishingModel`, identifies its vanishing condition with the
  Quotient-kernel condition, and identifies its coefficient-ideal factorization with
  the chosen global closed subscheme.

The sheaf-theoretic assertion that killing the pulled-back ambient kernel can be
checked on an arbitrary open cover is proved here, so it is not an input to the
finite-model data.

`CompatibleAffineFiniteFreeKernelModels.toQuotientKernelZeroLocusData` glues the local
factors by uniqueness (the target inclusion is a closed immersion, hence a mono).  The
result is the exact datum consumed by `quotFunctorPPrecomp_relative_closed`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme

namespace Modules

namespace QuotientPullbackData

variable {X S : Scheme.{u}} {F G : X.Modules} {f : X ⟶ S}
  {T T' : Over S}

/-- The normalized ambient identifications commute with precomposition by a map of
the ambient sheaves. -/
lemma ambientMap_comp_normalizedAmbientIso (p : G ⟶ F) (g : T' ⟶ T)
    [IsOpenImmersion g.left] :
    ambientMap (f := f) p T' ≫ (normalizedAmbientIso (F := F) T g).hom =
      (normalizedAmbientIso (F := G) T g).hom ≫
        (Modules.restrictFunctor ((Over.pullback f).map g).left).map
          (ambientMap (f := f) p T) := by
  simp [ambientMap, normalizedAmbientIso,
    PullbackQuotient.pullbackComparison]

/-- If a quotient kills the ambient kernel, every pullback of that quotient does as
well. -/
lemma kernel_ι_comp_pullback_π_eq_zero
    (p : G ⟶ F) [Epi p] (y : QuotientPullbackData G f T)
    (h : kernel.ι (ambientMap (f := f) p T) ≫ y.π = 0)
    (g : T' ⟶ T) :
    kernel.ι (ambientMap (f := f) p T') ≫ (y.pullback g).π = 0 := by
  let x := y.descendPrecomp p h
  have hcomm := pullback_precomp_r p g x
  have hpull := pullback_r (g := g) (precomp_descendPrecomp_r p y h)
  have hr : (QuotientPullbackData.setoid G f T').r
      ((x.pullback g).precomp p) (y.pullback g) :=
    (QuotientPullbackData.setoid G f T').trans
      ((QuotientPullbackData.setoid G f T').symm hcomm) hpull
  exact (kernel_ι_comp_eq_zero_iff_of_r p hr).mp
    (kernel_ι_comp_precomp_π p (x.pullback g))

/-- Killing the ambient kernel can be checked after restriction to an arbitrary
open cover of the test scheme. -/
lemma kernel_ι_comp_eq_zero_of_openCover
    (p : G ⟶ F) [Epi p] (T : Over S) (U : T.left.OpenCover)
    (y : QuotientPullbackData G f T)
    (h : ∀ i, kernel.ι (ambientMap (f := f) p (openCoverObjectOver T U i)) ≫
      (y.pullback (openCoverMapOver T U i)).π = 0) :
    kernel.ι (ambientMap (f := f) p T) ≫ y.π = 0 := by
  apply Modules.eq_zero_of_openCover_restrict (quotientTotalOpenCover f T U)
  intro i
  let j := openCoverMapOver T U i
  letI : IsOpenImmersion j.left := by
    change IsOpenImmersion (U.f i)
    exact U.map_prop i
  let jX := ((Over.pullback f).map j).left
  letI : IsOpenImmersion jX := by
    dsimp [jX]
    infer_instance
  let R := Modules.restrictFunctor jX
  change R.map (kernel.ι (ambientMap (f := f) p T) ≫ y.π) = 0
  let cG := normalizedAmbientIso (F := G) (f := f) T j
  let cF := normalizedAmbientIso (F := F) (f := f) T j
  let y' := restrictPullback T j y
  have hy' : kernel.ι (ambientMap (f := f) p (openCoverObjectOver T U i)) ≫
      y'.π = 0 :=
    (kernel_ι_comp_eq_zero_iff_of_r p
      (restrictPullback_r_pullback T j y)).mpr (h i)
  have hcompat :
      ambientMap (f := f) p (openCoverObjectOver T U i) ≫ cF.hom =
        cG.hom ≫ R.map (ambientMap (f := f) p T) :=
    ambientMap_comp_normalizedAmbientIso p j
  have hk :
      (R.map (kernel.ι (ambientMap (f := f) p T)) ≫ cG.inv) ≫
        ambientMap (f := f) p (openCoverObjectOver T U i) = 0 := by
    rw [← cancel_mono cF.hom]
    simp only [zero_comp, Category.assoc, hcompat, Iso.inv_hom_id_assoc,
      ← Functor.map_comp, kernel.condition, Functor.map_zero]
  let k : R.obj (kernel (ambientMap (f := f) p T)) ⟶
      kernel (ambientMap (f := f) p (openCoverObjectOver T U i)) :=
    kernel.lift (ambientMap (f := f) p (openCoverObjectOver T U i))
      (R.map (kernel.ι (ambientMap (f := f) p T)) ≫ cG.inv) hk
  change R.map (kernel.ι (ambientMap (f := f) p T) ≫ y.π) = 0
  rw [Functor.map_comp]
  rw [show R.map (kernel.ι (ambientMap (f := f) p T)) ≫ R.map y.π =
      (R.map (kernel.ι (ambientMap (f := f) p T)) ≫ cG.inv) ≫
        (cG.hom ≫ R.map y.π) by simp]
  change (R.map (kernel.ι (ambientMap (f := f) p T)) ≫ cG.inv) ≫ y'.π = 0
  rw [← kernel.lift_ι
    (ambientMap (f := f) p (openCoverObjectOver T U i))
    (R.map (kernel.ι (ambientMap (f := f) p T)) ≫ cG.inv) hk,
    Category.assoc, hy', comp_zero]

end QuotientPullbackData

end Modules

/-- A Quot class kills an ambient kernel exactly when every restriction to an open
cover does. -/
lemma quotientClassKillsAmbientKernel_iff_openCover
    {X S : Scheme.{u}} {F G : X.Modules} {f : X ⟶ S}
    (p : G ⟶ F) [Epi p] (T : Over S) (U : T.left.OpenCover)
    (z : (quotFunctor G f).obj (op T)) :
    QuotientClassKillsAmbientKernel p T z ↔
      ∀ i, QuotientClassKillsAmbientKernel p (openCoverObjectOver T U i)
        ((quotFunctor G f).map (openCoverMapOver T U i).op z) := by
  constructor
  · rintro ⟨y, hy, hzero⟩ i
    refine ⟨y.pullback (openCoverMapOver T U i), ?_,
      Modules.QuotientPullbackData.kernel_ι_comp_pullback_π_eq_zero p y hzero
        (openCoverMapOver T U i)⟩
    rw [← hy]
    rfl
  · intro hlocal
    obtain ⟨y, rfl⟩ := Quotient.exists_rep z
    refine ⟨y, rfl,
      Modules.QuotientPullbackData.kernel_ι_comp_eq_zero_of_openCover p T U y ?_⟩
    intro i
    obtain ⟨yi, hyi, hzeroi⟩ := hlocal i
    apply (Modules.QuotientPullbackData.kernel_ι_comp_eq_zero_iff_of_r p
      (Quotient.exact hyi)).mp hzeroi

namespace OpenCover

variable {S : Scheme.{u}} {W : Over S}

/-- A component of an open cover of the source, regarded as an object over the same
base scheme. -/
def overObj (U : W.left.OpenCover) (i : U.I₀) : Over S :=
  Over.mk (U.f i ≫ W.hom)

/-- The canonical morphism from an open-cover component to the covered object in the
over category. -/
def overHom (U : W.left.OpenCover) (i : U.I₀) : U.overObj i ⟶ W :=
  Over.homMk (U.f i) rfl

@[simp]
lemma overHom_left (U : W.left.OpenCover) (i : U.I₀) :
    (U.overHom i).left = U.f i :=
  rfl

end OpenCover

variable {S : Scheme.{u}} {n : ℕ}
variable {F G : (projectiveSpaceOver n S).Modules}
variable (p : G ⟶ F) [Epi p] (P : Polynomial ℚ)
variable {T : Over S} {z : (quotFunctorP G P).obj (op T)}

/-- The Quotient-kernel condition is local on the source for the chosen affine cover.

This is the sheaf-theoretic locality input: the global pulled-back kernel map vanishes
exactly when it vanishes after restriction to every member of `W.left.affineCover`. -/
def QuotientKernelConditionIsAffineLocal : Prop :=
  ∀ (W : Over S) (g : W ⟶ T),
    QuotientClassKillsAmbientKernel p W
        (((quotFunctorP G P).map g.op) z).1 ↔
      ∀ i : W.left.affineCover.I₀,
        QuotientClassKillsAmbientKernel p
          (W.left.affineCover.overObj i)
          (((quotFunctorP G P).map
            ((W.left.affineCover.overHom i ≫ g).op)) z).1

/-- The Quotient-kernel condition is affine-local on every source. -/
lemma quotientKernelConditionIsAffineLocal :
    QuotientKernelConditionIsAffineLocal p P (T := T) (z := z) := by
  intro W g
  have h := quotientClassKillsAmbientKernel_iff_openCover
    p W W.left.affineCover (((quotFunctorP G P).map g.op) z).1
  refine h.trans (forall_congr' fun i ↦ ?_)
  change QuotientClassKillsAmbientKernel p
      (W.left.affineCover.overObj i)
        ((quotFunctor G (projectiveSpaceOverπ n S)).map
          (W.left.affineCover.overHom i).op
          (((quotFunctorP G P).map g.op) z).1) ↔ _
  have hmap :
      (quotFunctor G (projectiveSpaceOverπ n S)).map
          (W.left.affineCover.overHom i).op
          (((quotFunctorP G P).map g.op) z).1 =
        (((quotFunctorP G P).map
          ((W.left.affineCover.overHom i ≫ g).op)) z).1 := by
    rw [show (W.left.affineCover.overHom i ≫ g).op =
      g.op ≫ (W.left.affineCover.overHom i).op from rfl,
      Functor.map_comp]
    rfl
  rw [hmap]

/-- A closed candidate zero locus whose universal property is known on affine test
schemes. -/
structure QuotientKernelAffineFactorizationData where
  /-- Candidate zero locus. -/
  Z : Over S
  /-- Candidate closed inclusion. -/
  ι : Z ⟶ T
  /-- The candidate inclusion is a closed immersion. -/
  isClosedImmersion : IsClosedImmersion ι.left
  /-- Universal factorization on affine test schemes. -/
  affine_factor_iff : ∀ (W : Over S) [IsAffine W.left] (g : W ⟶ T),
    QuotientClassKillsAmbientKernel p W
        (((quotFunctorP G P).map g.op) z).1 ↔
      ∃ h : W ⟶ Z, h ≫ ι = g

namespace QuotientKernelAffineFactorizationData

/-- Affine-local factorization data glue to the global universal closed zero locus. -/
noncomputable def toQuotientKernelZeroLocusData
    (D : QuotientKernelAffineFactorizationData p P (T := T) (z := z)) :
    QuotientKernelZeroLocusData p P T z where
  Z := D.Z
  ι := D.ι
  isClosedImmersion := D.isClosedImmersion
  factor_iff W g := by
    letI : IsClosedImmersion D.ι.left := D.isClosedImmersion
    letI : Mono D.ι.left := inferInstance
    let U := W.left.affineCover
    let Ui : U.I₀ → Over S := fun i ↦ U.overObj i
    let ji : ∀ i, Ui i ⟶ W := fun i ↦ U.overHom i
    constructor
    · intro hkill
      have hkill_i : ∀ i, QuotientClassKillsAmbientKernel p (Ui i)
          (((quotFunctorP G P).map ((ji i ≫ g).op)) z).1 :=
        (quotientKernelConditionIsAffineLocal p P W g).mp hkill
      haveI (i : U.I₀) : IsAffine (Ui i).left := by
        dsimp [Ui, OpenCover.overObj, U]
        infer_instance
      have hex : ∀ i, ∃ h : Ui i ⟶ D.Z, h ≫ D.ι = ji i ≫ g :=
        fun i ↦ (D.affine_factor_iff (Ui i) (ji i ≫ g)).mp (hkill_i i)
      choose hi hhi using hex
      have hcompat : ∀ i j,
          pullback.fst (U.f i) (U.f j) ≫ (hi i).left =
            pullback.snd (U.f i) (U.f j) ≫ (hi j).left := by
        intro i j
        rw [← cancel_mono D.ι.left]
        simp only [Category.assoc]
        have hhi' := congrArg Over.Hom.left (hhi i)
        have hhj' := congrArg Over.Hom.left (hhi j)
        dsimp [ji, Ui, OpenCover.overHom, OpenCover.overObj] at hhi' hhj'
        rw [hhi', hhj']
        change (pullback.fst (U.f i) (U.f j) ≫ U.f i) ≫ g.left =
          (pullback.snd (U.f i) (U.f j) ≫ U.f j) ≫ g.left
        rw [pullback.condition]
      let hleft : W.left ⟶ D.Z.left :=
        U.glueMorphisms (fun i ↦ (hi i).left) hcompat
      have hleft_over : hleft ≫ D.Z.hom = W.hom := by
        apply U.hom_ext
        intro i
        rw [← Category.assoc, U.ι_glueMorphisms]
        exact (hi i).w
      let h : W ⟶ D.Z := Over.homMk hleft hleft_over
      refine ⟨h, ?_⟩
      apply CommaMorphism.ext
      · apply U.hom_ext
        intro i
        change U.f i ≫ hleft ≫ D.ι.left = U.f i ≫ g.left
        rw [← Category.assoc, U.ι_glueMorphisms]
        exact congrArg Over.Hom.left (hhi i)
      · rfl
    · rintro ⟨h, hh⟩
      refine (quotientKernelConditionIsAffineLocal p P W g).mpr ?_
      intro i
      haveI : IsAffine (U.overObj i).left := by
        dsimp [OpenCover.overObj, U]
        infer_instance
      apply (D.affine_factor_iff (U.overObj i) (U.overHom i ≫ g)).mpr
      refine ⟨U.overHom i ≫ h, ?_⟩
      rw [Category.assoc, hh]

end QuotientKernelAffineFactorizationData

/-- A finite-free vanishing model on one affine chart, together with the two comparison
maps which make it a chart of a chosen global zero locus.

`detect` is the sheaf-to-finite-module comparison. `factorEquiv` is the overlap
compatibility datum: it identifies the coefficient-ideal zero-locus lifts with lifts to
the chosen global closed subscheme.  Requiring an equivalence, rather than only matching
truth values, records the uniqueness needed for gluing. -/
structure AffineFiniteFreeKernelVanishingCertificate
    (Z : Over S) (ι : Z ⟶ T) (W : Over S) (g : W ⟶ T) where
  /-- Coordinate ring used by the affine model. -/
  R : Type u
  [commRing : CommRing R]
  /-- Total space of the family over the affine chart. -/
  X : Scheme.{u}
  /-- Its structure morphism to the affine chart model. -/
  pX : X ⟶ Spec (.of R)
  /-- Source sheaf of the map whose vanishing is being cut out. -/
  E : X.Modules
  /-- Target sheaf of the map whose vanishing is being cut out. -/
  Q : X.Modules
  /-- The sheaf morphism encoding the pulled-back ambient-kernel map. -/
  q : E ⟶ Q
  /-- Finite-free coordinate model for universal vanishing of `q`. -/
  model : Modules.HasFiniteFreeVanishingModel pX q
  /-- The Quotient-kernel condition is detected by the identity base change of the
  finite model. -/
  detect :
    QuotientClassKillsAmbientKernel p W
        (((quotFunctorP G P).map g.op) z).1 ↔
      (Modules.pullback
        (pullback.snd
          (Spec.map (CommRingCat.ofHom (RingHom.id R))) pX)).map q = 0
  /-- Compatible identification of local coefficient-ideal lifts with lifts to the
  chosen global zero locus. -/
  factorEquiv :
    { h : Spec (.of R) ⟶ model.zeroLocus //
        h ≫ model.zeroLocusι =
          Spec.map (CommRingCat.ofHom (RingHom.id R)) } ≃
      { h : W ⟶ Z // h ≫ ι = g }

namespace AffineFiniteFreeKernelVanishingCertificate

attribute [instance] commRing

/-- A compatible finite-free affine certificate proves the required affine
factorization criterion. -/
lemma factor_iff
    (C : AffineFiniteFreeKernelVanishingCertificate p P Z ι W g
      (T := T) (z := z)) :
    QuotientClassKillsAmbientKernel p W
        (((quotFunctorP G P).map g.op) z).1 ↔
      ∃ h : W ⟶ Z, h ≫ ι = g := by
  refine C.detect.trans ?_
  refine (Modules.HasFiniteFreeVanishingModel.pullback_eq_zero_iff_exists_zeroLocusLift
    (pX := C.pX) (p := C.q) C.model C.R (RingHom.id C.R)).trans ?_
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨(C.factorEquiv ⟨h, hh⟩).1, (C.factorEquiv ⟨h, hh⟩).2⟩
  · rintro ⟨h, hh⟩
    let a := C.factorEquiv.symm ⟨h, hh⟩
    exact ⟨a.1, a.2⟩

end AffineFiniteFreeKernelVanishingCertificate

/-- A global closed candidate equipped with compatible finite-free models on every
affine test object. -/
structure CompatibleAffineFiniteFreeKernelModels where
  /-- Global candidate zero locus. -/
  Z : Over S
  /-- Global candidate inclusion. -/
  ι : Z ⟶ T
  /-- The global candidate is closed. -/
  isClosedImmersion : IsClosedImmersion ι.left
  /-- A compatible finite-free vanishing certificate on every affine test object. -/
  affineModel : ∀ (W : Over S) [IsAffine W.left] (g : W ⟶ T),
    Nonempty (AffineFiniteFreeKernelVanishingCertificate p P Z ι W g
      (T := T) (z := z))

namespace CompatibleAffineFiniteFreeKernelModels

/-- Compatible finite-free affine models supply affine factorization data. -/
noncomputable def toAffineFactorizationData
    (D : CompatibleAffineFiniteFreeKernelModels p P (T := T) (z := z)) :
    QuotientKernelAffineFactorizationData p P (T := T) (z := z) where
  Z := D.Z
  ι := D.ι
  isClosedImmersion := D.isClosedImmersion
  affine_factor_iff W _ g :=
    (Classical.choice (D.affineModel W (g := g))).factor_iff p P

/-- Compatible finite-free affine models glue to the exact universal zero-locus datum
used by the Quot precomposition API. -/
noncomputable def toQuotientKernelZeroLocusData
    (D : CompatibleAffineFiniteFreeKernelModels p P (T := T) (z := z)) :
    QuotientKernelZeroLocusData p P T z :=
  D.toAffineFactorizationData p P |>.toQuotientKernelZeroLocusData p P

end CompatibleAffineFiniteFreeKernelModels

/-- Compatible affine finite-free kernel models for every test quotient imply that
fixed-polynomial Quot precomposition is relatively representable by closed
immersions. -/
theorem quotFunctorPPrecomp_relative_closed_of_compatibleAffineFiniteFreeKernelModels
    (H : ∀ (T : Over S) (z : (quotFunctorP G P).obj (op T)),
      Nonempty (CompatibleAffineFiniteFreeKernelModels p P (T := T) (z := z))) :
    MorphismProperty.relative uliftYoneda.{u + 1}
      (MorphismProperty.over
        (@IsClosedImmersion : MorphismProperty Scheme.{u}))
      (quotFunctorPPrecomp p P) :=
  quotFunctorPPrecomp_relative_closed p P fun T z ↦
    ⟨(CompatibleAffineFiniteFreeKernelModels.toQuotientKernelZeroLocusData
      p P (Classical.choice (H T z)))⟩

end AlgebraicGeometry.Scheme
