module

public import StacksAndModuli.API.ProjectiveTwistedVanishingModel
public import StacksAndModuli.API.ProjectiveSpaceZeroCanonicalGlobalSectionsBaseChange
public import StacksAndModuli.API.QuotientKernelAffineIdealSheafZeroLocus
public import StacksAndModuli.API.TwistedFreeQuotCanonicalGlobalSectionsBaseChange

/-!
# Quotient-kernel models from positive projective twists

On an affine chart of a Quot parameter scheme, transport the ambient-kernel morphism to
polynomial projective space.  Once its target has eventual finite-projective global
sections with canonical arbitrary-base compatibility, the positive-twist construction
produces the finite-free equations required by the Quot zero-locus pipeline.

This file records the exact interface between those two arguments.  The chartwise input
contains only the transported morphism, its identification with the Quot kernel condition,
and eventual canonical Cohomology and Base Change for its target.  The construction of the
finite-free coefficient model and of the compatible ideal sheaf is then automatic.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry ProjectiveSpectrum.Twist

universe u

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

variable {S : Scheme.{u}} {n : ℕ}
variable {F G : (projectiveSpaceOver n S).Modules}
variable (p : G ⟶ F) [Epi p] (P : Polynomial ℚ)
variable {T : Over S} {z : (quotFunctorP G P).obj (op T)}

/-- A quotient sheaf on the relative-projective fibre product over an affine base,
transported to intrinsic polynomial `Proj`. -/
noncomputable def Modules.QuotientPullbackData.polynomialQuotient
    {R : Type u} [CommRing R] (sigma : Spec (.of R) ⟶ S)
    (y : Modules.QuotientPullbackData G (projectiveSpaceOverπ n S)
      (Over.mk sigma)) :
    (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules :=
  (Modules.pullback
    (ProjectiveSpace.projectiveSpaceOverSpecIso n R).inv).obj
      ((Modules.pullback
        (projectiveSpaceOverBaseChangeIso n sigma).inv).obj y.Q)

namespace Modules.QuotientPullbackData

/-- The polynomial-`Proj` normalization of a positive-dimensional twisted-free Quot
datum over an affine noetherian base has the canonical global-sections base-change package
needed by the finite-free vanishing construction. -/
noncomputable def
    polynomialQuotient_hasEventualFiniteProjectiveCanonicalGlobalSectionsBaseChange
    {S : Scheme.{u}} (n r : ℕ) (hn : 0 < n) (l : ℤ)
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (sigma : Spec (.of R) ⟶ S)
    (y : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) (Over.mk sigma)) :
    Proj.HasEventualFiniteProjectiveCanonicalGlobalSectionsBaseChange
      (y.polynomialQuotient sigma) :=
  hasEventualFiniteProjectiveCanonicalGlobalSectionsBaseChange_twistedFree
      n r hn l sigma y

/-- The polynomial-`Proj` normalization of a twisted-free Quot datum on projective
zero-space has the canonical global-sections base-change package in every degree.
Unlike the positive-dimensional construction, this needs no Noetherian hypothesis. -/
noncomputable def
    polynomialQuotient_hasEventualFiniteProjectiveCanonicalGlobalSectionsBaseChange_zero
    {S : Scheme.{u}} (r : ℕ) (l : ℤ)
    {R : Type u} [CommRing R]
    (sigma : Spec (.of R) ⟶ S)
    (y : QuotientPullbackData
      (twistedFreeAmbient (n := 0) (r := r) (l := l))
      (Scheme.projectiveSpaceOverπ 0 S) (Over.mk sigma)) :
    Proj.HasEventualFiniteProjectiveCanonicalGlobalSectionsBaseChange
      (y.polynomialQuotient sigma) := by
  let T : Over S := Over.mk sigma
  let Q := quotDataOnProjectiveSpace
    (n := 0) (S := S) (T := T)
    (twistedFreeAmbient (n := 0) (r := r) (l := l)) y
  haveI hQfp : Q.IsFinitePresentation :=
    quotDataOnProjectiveSpace_isFinitePresentation_over T y
  let F := (Scheme.Modules.pullback
    (ProjectiveSpace.projectiveSpaceOverSpecIso 0 R).inv).obj Q
  haveI hFfp : F.IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ hQfp
  haveI hFqc : F.IsQuasicoherent := inferInstance
  have hflat : Q.FlatOver (Scheme.projectiveSpaceOverπ 0 (Spec (.of R))) :=
    quotDataOnProjectiveSpace_flatOver_over T y
  have hflat' : F.FlatOver (Proj.polynomialToSpec (Fin 1) R) :=
    Scheme.Modules.FlatOver.pullback_isIso
      (ProjectiveSpace.projectiveSpaceOverSpecIso 0 R).inv Q
      (ProjectiveSpace.projectiveSpaceOverSpecIso_inv_comp_projectiveSpaceOverπ 0 R)
      hflat
  exact Proj.hasEventualFiniteProjectiveCanonicalGlobalSectionsBaseChange_zero R F hflat'

end Modules.QuotientPullbackData

/-- The positive-twist input on one affine chart of a Quot parameter scheme.

In the intended construction, `q` is the ambient-kernel morphism for a representative of
the universal quotient, transported from relative projective space to polynomial `Proj`.
The `detect` field records that this transport and subsequent affine base changes agree
with the intrinsic Quot kernel condition. -/
structure QuotientKernelAffineCanonicalCBCModel (U : T.left.affineOpens) where
  /-- Source of the transported kernel morphism. -/
  E : (Proj (MvPolynomial.homogeneousSubmodule
    (Fin (n + 1)) Γ(T.left, U.1))).Modules
  /-- Target of the transported kernel morphism. -/
  Q : (Proj (MvPolynomial.homogeneousSubmodule
    (Fin (n + 1)) Γ(T.left, U.1))).Modules
  /-- Transported ambient-kernel morphism. -/
  q : E ⟶ Q
  /-- The source admits a finite positive-twist presentation. -/
  source_finitePresentation : E.IsFinitePresentation
  /-- Eventual finite projectivity and canonical arbitrary-base compatibility for the
  target twists. -/
  target_cbc : Proj.HasEventualFiniteProjectiveCanonicalGlobalSectionsBaseChange Q
  /-- The transported morphism detects the Quot kernel condition after every affine
  base change of the chart. -/
  detect : ∀ (A : Type u) [CommRing A] (f : Γ(T.left, U.1) →+* A),
    QuotientClassKillsAmbientKernel p
        (Over.mk
          ((Spec.map (CommRingCat.ofHom f) ≫ U.2.isoSpec.inv ≫ U.1.ι) ≫ T.hom))
        (((quotFunctorP G P).map
          ((Over.homMk
            (Spec.map (CommRingCat.ofHom f) ≫ U.2.isoSpec.inv ≫ U.1.ι) :
              Over.mk
                ((Spec.map (CommRingCat.ofHom f) ≫ U.2.isoSpec.inv ≫ U.1.ι) ≫
                  T.hom) ⟶ T).op)) z).1 ↔
      (Modules.pullback
        (Limits.pullback.snd (Spec.map (CommRingCat.ofHom f))
          (Proj.polynomialToSpec (Fin (n + 1)) Γ(T.left, U.1)))).map q = 0

/-- The weakest chartwise input needed by the canonical positive-twist
construction: a representative of the actual Quot class whose transported target
has eventual finite-projective canonical global-sections base change. -/
def QuotientKernelAffineRepresentativeCBC
    (U : T.left.affineOpens) : Prop :=
  ∃ y : Modules.QuotientPullbackData G (projectiveSpaceOverπ n S)
      (Over.mk ((U.2.isoSpec.inv ≫ U.1.ι) ≫ T.hom)),
    Quotient.mk _ y =
        (((quotFunctorP G P).map
          ((Over.homMk (U.2.isoSpec.inv ≫ U.1.ι) :
            Over.mk ((U.2.isoSpec.inv ≫ U.1.ι) ≫ T.hom) ⟶ T).op)) z).1 ∧
      Nonempty
        (Proj.HasEventualFiniteProjectiveCanonicalGlobalSectionsBaseChange
          (y.polynomialQuotient
            ((U.2.isoSpec.inv ≫ U.1.ι) ≫ T.hom)))

namespace QuotientKernelAffineCanonicalCBCModel

/-- The positive-twist input on one affine chart canonically produces a finite-free
kernel model on that chart. -/
theorem toFiniteFreeModel
    {U : T.left.affineOpens}
    (C : QuotientKernelAffineCanonicalCBCModel p P U (z := z)) :
    Nonempty (QuotientKernelAffineFiniteFreeModel p P U (z := z)) := by
  letI : C.E.IsFinitePresentation := C.source_finitePresentation
  obtain ⟨H⟩ := C.target_cbc.nonempty_finiteFreeVanishingModel C.q
  exact ⟨
    { X := Proj (MvPolynomial.homogeneousSubmodule
        (Fin (n + 1)) Γ(T.left, U.1))
      pX := Proj.polynomialToSpec (Fin (n + 1)) Γ(T.left, U.1)
      E := C.E
      Q := C.Q
      q := C.q
      model := H
      detect := C.detect }⟩

set_option maxHeartbeats 800000 in
-- Elaborating the dependent affine-chart transports requires extra heartbeats.
/-- A representative of the actual chartwise Quot class, together with canonical
base change only for its transported quotient sheaf, canonically supplies the
positive-twist kernel model.  Finite presentation of the transported source is
deduced from local Noetherianity and the ambient presentation. -/
theorem nonempty_of_representative
    [IsLocallyNoetherian T.left]
    [G.IsQuasicoherent] [G.IsFinitePresentation] [F.IsQuasicoherent]
    (U : T.left.affineOpens)
    (y : Modules.QuotientPullbackData G (projectiveSpaceOverπ n S)
      (Over.mk ((U.2.isoSpec.inv ≫ U.1.ι) ≫ T.hom)))
    (hy : Quotient.mk _ y =
      (((quotFunctorP G P).map
        ((Over.homMk (U.2.isoSpec.inv ≫ U.1.ι) :
          Over.mk ((U.2.isoSpec.inv ≫ U.1.ι) ≫ T.hom) ⟶ T).op)) z).1)
    (Hcbc : Nonempty
      (Proj.HasEventualFiniteProjectiveCanonicalGlobalSectionsBaseChange
        (y.polynomialQuotient
          ((U.2.isoSpec.inv ≫ U.1.ι) ≫ T.hom)))) :
    Nonempty (QuotientKernelAffineCanonicalCBCModel p P U (z := z)) := by
  classical
  let R := Γ(T.left, U.1)
  let j : Spec (.of R) ⟶ T.left := U.2.isoSpec.inv ≫ U.1.ι
  let sigma : Spec (.of R) ⟶ S := j ≫ T.hom
  let TU : Over S := Over.mk sigma
  let gU : TU ⟶ T := Over.homMk j rfl
  change Quotient.mk _ y = (((quotFunctorP G P).map gU.op) z).1 at hy
  let X := ((Over.pullback (projectiveSpaceOverπ n S)).obj TU).left
  let a := Modules.QuotientPullbackData.ambientMap
    (f := projectiveSpaceOverπ n S) p TU
  let k := kernel.ι a ≫ y.π
  let eR := projectiveSpaceOverBaseChangeIso n sigma
  let eSpecR := ProjectiveSpace.projectiveSpaceOverSpecIso n R
  let E' := (Modules.pullback eSpecR.inv).obj
    ((Modules.pullback eR.inv).obj (kernel a))
  let Q' := y.polynomialQuotient sigma
  let q' : E' ⟶ Q' := (Modules.pullback eSpecR.inv).map
    ((Modules.pullback eR.inv).map k)
  haveI : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian U
  letI : IsLocallyNoetherian (projectiveSpaceOver n (Spec (.of R))) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (projectiveSpaceOverπ n (Spec (.of R)))
  letI : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian eR.hom
  haveI : ((Modules.pullback
      ((Over.pullback (projectiveSpaceOverπ n S)).obj TU).hom).obj G).IsQuasicoherent :=
    inferInstance
  haveI : ((Modules.pullback
      ((Over.pullback (projectiveSpaceOverπ n S)).obj TU).hom).obj G).IsFinitePresentation :=
    inferInstance
  haveI : ((Modules.pullback
      ((Over.pullback (projectiveSpaceOverπ n S)).obj TU).hom).obj F).IsQuasicoherent :=
    inferInstance
  letI : (kernel a).IsFinitePresentation := Modules.kernel_isFinitePresentation a
  have hE : E'.IsFinitePresentation := inferInstance
  refine ⟨{
    E := E'
    Q := Q'
    q := q'
    source_finitePresentation := hE
    target_cbc := Classical.choice Hcbc
    detect := ?_ }⟩
  intro A _ f
  let TA : Over S := Over.mk
    ((Spec.map (CommRingCat.ofHom f) ≫ j) ≫ T.hom)
  let h : TA ⟶ TU := Over.homMk (Spec.map (CommRingCat.ofHom f)) (by
    simp [TA, TU, sigma, Category.assoc])
  let gA : TA ⟶ T := Over.homMk
    (Spec.map (CommRingCat.ofHom f) ≫ j) rfl
  have hg : gA = h ≫ gU := by
    ext
    rfl
  have hmapP := ConcreteCategory.congr_hom
    ((quotFunctorP G P).map_comp gU.op h.op) z
  have hmap := congrArg Subtype.val hmapP
  have hclass : (((quotFunctorP G P).map gA.op) z).1 =
      (quotFunctor G (projectiveSpaceOverπ n S)).map h.op (Quotient.mk _ y) := by
    rw [hg]
    change (((quotFunctorP G P).map (gU.op ≫ h.op)) z).1 = _
    rw [hmap]
    rw [hy]
    rfl
  change QuotientClassKillsAmbientKernel p TA
      (((quotFunctorP G P).map gA.op) z).1 ↔
    (Modules.pullback
      (Limits.pullback.snd (Spec.map (CommRingCat.ofHom f))
        (Proj.polynomialToSpec (Fin (n + 1)) R))).map q' = 0
  rw [hclass]
  exact (quotientClassKillsAmbientKernel_map_mk_iff p h y).trans
    ((y.pullback_kernelComposite_eq_zero_iff p h).trans
      ((polynomialProjectiveTransport_pullback_eq_zero_iff sigma f k).symm.trans
        (Proj.pullback_map_eq_zero_iff_polynomialMap q' f).symm))

end QuotientKernelAffineCanonicalCBCModel

/-- Positive-twist and canonical-CBC input on every affine chart.  No choices on
overlaps are required. -/
structure QuotientKernelAffineCanonicalCBCModels where
  /-- The positive-twist input on each canonical affine chart. -/
  affineModel : ∀ U : T.left.affineOpens,
    Nonempty (QuotientKernelAffineCanonicalCBCModel p P U (z := z))

namespace QuotientKernelAffineCanonicalCBCModels

set_option maxHeartbeats 800000 in
-- The result type retains all dependent affine-chart transports.
/-- Weakest representative-level canonical-CBC input on every affine chart
constructs all canonical positive-twist kernel models. -/
theorem nonempty_of_representativeCBC
    [IsLocallyNoetherian T.left]
    [G.IsQuasicoherent] [G.IsFinitePresentation] [F.IsQuasicoherent]
    (Hcbc : ∀ U : T.left.affineOpens,
      QuotientKernelAffineRepresentativeCBC P U (z := z)) :
    Nonempty (QuotientKernelAffineCanonicalCBCModels p P (T := T) (z := z)) := by
  classical
  refine ⟨{ affineModel := fun U ↦ ?_ }⟩
  obtain ⟨y, hy, Hcbc⟩ := Hcbc U
  exact QuotientKernelAffineCanonicalCBCModel.nonempty_of_representative
    p P U y hy Hcbc

set_option maxHeartbeats 800000 in
-- Choosing representatives of the quotient classes produces large dependent terms.
/-- Construct the chartwise canonical-CBC models directly from intrinsic quotient
data.  The theorem itself chooses a representative of each affine pullback of `z`;
the sole remaining geometric input is eventual canonical global-sections base change
for a representative of that actual quotient class. -/
theorem nonempty_of_quotientTargetCBC
    [IsLocallyNoetherian T.left]
    [G.IsQuasicoherent] [G.IsFinitePresentation] [F.IsQuasicoherent]
    (Hcbc : ∀ (U : T.left.affineOpens)
      (y : Modules.QuotientPullbackData G (projectiveSpaceOverπ n S)
        (Over.mk ((U.2.isoSpec.inv ≫ U.1.ι) ≫ T.hom))),
      Quotient.mk _ y =
          (((quotFunctorP G P).map
            ((Over.homMk (U.2.isoSpec.inv ≫ U.1.ι) :
              Over.mk ((U.2.isoSpec.inv ≫ U.1.ι) ≫ T.hom) ⟶ T).op)) z).1 →
        Nonempty
          (Proj.HasEventualFiniteProjectiveCanonicalGlobalSectionsBaseChange
            (y.polynomialQuotient
              ((U.2.isoSpec.inv ≫ U.1.ι) ≫ T.hom)))) :
    Nonempty (QuotientKernelAffineCanonicalCBCModels p P (T := T) (z := z)) := by
  apply nonempty_of_representativeCBC p P
  intro U
  obtain ⟨y, hy⟩ := Quotient.exists_rep
    ((((quotFunctorP G P).map
      ((Over.homMk (U.2.isoSpec.inv ≫ U.1.ι) :
        Over.mk ((U.2.isoSpec.inv ≫ U.1.ι) ≫ T.hom) ⟶ T).op)) z).1)
  exact ⟨y, hy, Hcbc U y hy⟩

set_option maxHeartbeats 800000 in
-- The target remembers the chosen representatives on every affine chart.
/-- For positive-dimensional projective space, intrinsic twisted-free Quot data on a
locally noetherian base canonically produce all affine finite-free kernel models. -/
theorem nonempty_twistedFree_of_positive_dimension
    {S : Scheme.{u}} (n r : ℕ) (hn : 0 < n) (l : ℤ)
    {F : (projectiveSpaceOver n S).Modules}
    (p : Modules.QuotientPullbackData.twistedFreeAmbient
      (S := S) (n := n) (r := r) (l := l) ⟶ F) [Epi p]
    (P : Polynomial ℚ) {T : Over S} [IsLocallyNoetherian T.left]
    [F.IsQuasicoherent]
    (z : (quotFunctorP
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (S := S) (n := n) (r := r) (l := l)) P).obj (op T)) :
    Nonempty (QuotientKernelAffineCanonicalCBCModels p P (T := T) (z := z)) := by
  letI : (Modules.QuotientPullbackData.twistedFreeAmbient
      (S := S) (n := n) (r := r) (l := l)).IsQuasicoherent := by
    dsimp only [Modules.QuotientPullbackData.twistedFreeAmbient]
    exact Modules.projectiveSpaceOverTwistCoproduct_isQuasicoherent
      (ULift.{u} (Fin r)) n S (-l)
  letI : (Modules.QuotientPullbackData.twistedFreeAmbient
      (S := S) (n := n) (r := r) (l := l)).IsFinitePresentation :=
    twistedFreeAmbient_isFinitePresentation n S l r
  apply nonempty_of_quotientTargetCBC p P
  intro U y _
  letI : IsNoetherianRing Γ(T.left, U.1) :=
    IsLocallyNoetherian.component_noetherian U
  exact
    ⟨y.polynomialQuotient_hasEventualFiniteProjectiveCanonicalGlobalSectionsBaseChange
      n r hn l ((U.2.isoSpec.inv ≫ U.1.ι) ≫ T.hom)⟩

set_option maxHeartbeats 800000 in
-- Choosing representatives on every affine chart creates large dependent terms.
/-- On projective zero-space, intrinsic twisted-free Quot data on a locally
Noetherian base canonically produce all affine finite-free kernel models.  Canonical
base change is automatic in this dimension. -/
theorem nonempty_twistedFree_zero
    {S : Scheme.{u}} (r : ℕ) (l : ℤ)
    {F : (projectiveSpaceOver 0 S).Modules}
    (p : Modules.QuotientPullbackData.twistedFreeAmbient
      (S := S) (n := 0) (r := r) (l := l) ⟶ F) [Epi p]
    (P : Polynomial ℚ) {T : Over S} [IsLocallyNoetherian T.left]
    [F.IsQuasicoherent]
    (z : (quotFunctorP
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (S := S) (n := 0) (r := r) (l := l)) P).obj (op T)) :
    Nonempty (QuotientKernelAffineCanonicalCBCModels p P (T := T) (z := z)) := by
  letI : (Modules.QuotientPullbackData.twistedFreeAmbient
      (S := S) (n := 0) (r := r) (l := l)).IsQuasicoherent := by
    dsimp only [Modules.QuotientPullbackData.twistedFreeAmbient]
    exact Modules.projectiveSpaceOverTwistCoproduct_isQuasicoherent
      (ULift.{u} (Fin r)) 0 S (-l)
  letI : (Modules.QuotientPullbackData.twistedFreeAmbient
      (S := S) (n := 0) (r := r) (l := l)).IsFinitePresentation :=
    twistedFreeAmbient_isFinitePresentation 0 S l r
  apply nonempty_of_quotientTargetCBC p P
  intro U y _
  exact
    ⟨y.polynomialQuotient_hasEventualFiniteProjectiveCanonicalGlobalSectionsBaseChange_zero
      r l ((U.2.isoSpec.inv ≫ U.1.ι) ≫ T.hom)⟩

/-- Construct the chartwise finite-free models used by the affine-predicate pipeline. -/
theorem toFiniteFreeModels
    (D : QuotientKernelAffineCanonicalCBCModels p P (T := T) (z := z)) :
    QuotientKernelAffineFiniteFreeModels p P (T := T) (z := z) where
  affineModel U :=
    (Classical.choice (D.affineModel U)).toFiniteFreeModel p P

/-- Construct affine coefficient ideals representing the Quotient-kernel condition.
No compatibility choices on overlaps are needed: compatibility follows from the
represented pullback-stable predicate. -/
noncomputable def toAffineQuotientKernelIdealModels
    (D : QuotientKernelAffineCanonicalCBCModels p P (T := T) (z := z)) :
    AffineQuotientKernelIdealModels p P (T := T) (z := z) where
  data := (D.toFiniteFreeModels p P).toAffineMorphismPredicate p P
  detects _ _ _ := Iff.rfl

/-- Construct the universal closed zero locus for the ambient-kernel condition from
positive-twist and canonical-CBC input on every affine chart. -/
noncomputable def toQuotientKernelZeroLocusData
    (D : QuotientKernelAffineCanonicalCBCModels p P (T := T) (z := z)) :
    QuotientKernelZeroLocusData p P T z :=
  (D.toAffineQuotientKernelIdealModels p P).toQuotientKernelZeroLocusData p P

/-- The intrinsic representative-and-CBC input produces the universal closed
zero locus for the fixed Quot point. -/
theorem nonempty_zeroLocusData_of_representativeCBC
    [IsLocallyNoetherian T.left]
    [G.IsQuasicoherent] [G.IsFinitePresentation] [F.IsQuasicoherent]
    (Hcbc : ∀ U : T.left.affineOpens,
      QuotientKernelAffineRepresentativeCBC P U (z := z)) :
    Nonempty (QuotientKernelZeroLocusData p P T z) := by
  obtain ⟨D⟩ := nonempty_of_representativeCBC p P Hcbc
  exact ⟨D.toQuotientKernelZeroLocusData p P⟩

end QuotientKernelAffineCanonicalCBCModels

/-- Chartwise positive-twist presentations with canonical arbitrary-base Cohomology
and Base Change make fixed-polynomial Quot precomposition relatively representable by
closed immersions. -/
theorem quotFunctorPPrecomp_relative_closed_of_affineCanonicalCBCModels
    (H : ∀ (T : Over S) (z : (quotFunctorP G P).obj (op T)),
      Nonempty (QuotientKernelAffineCanonicalCBCModels p P (T := T) (z := z))) :
    MorphismProperty.relative uliftYoneda.{u + 1}
      (MorphismProperty.over
        (@IsClosedImmersion : MorphismProperty Scheme.{u}))
      (quotFunctorPPrecomp p P) :=
  quotFunctorPPrecomp_relative_closed_of_affineQuotientKernelIdealModels p P
    (fun T z ↦
      ⟨(Classical.choice (H T z)).toAffineQuotientKernelIdealModels p P⟩)

/-- On a locally Noetherian representing scheme for the source Quot functor,
chartwise eventual canonical base change for representatives of the universal
quotient cuts out the target Quot functor as a projective closed subscheme. -/
theorem
    exists_quotFunctorP_representableBy_isHProjective_of_universal_representativeCBC
    (p : G ⟶ F) [Epi p]
    (Q₀ : Over S) [IsLocallyNoetherian Q₀.left]
    (eG : (quotFunctorP G P).RepresentableBy Q₀)
    (hQ₀ : IsHProjective Q₀.hom)
    [G.IsQuasicoherent] [G.IsFinitePresentation] [F.IsQuasicoherent]
    (Hcbc : ∀ U : Q₀.left.affineOpens,
      QuotientKernelAffineRepresentativeCBC P U
        (z := eG.homEquiv (𝟙 Q₀))) :
    ∃ Q : Over S,
      Nonempty ((quotFunctorP F P).RepresentableBy Q) ∧
        IsHProjective Q.hom := by
  let D : QuotientKernelZeroLocusData p P Q₀ (eG.homEquiv (𝟙 Q₀)) :=
    Classical.choice
      (QuotientKernelAffineCanonicalCBCModels.nonempty_zeroLocusData_of_representativeCBC
        p P Hcbc)
  exact
    exists_quotFunctorP_representableBy_isHProjective_of_universal_precomp_zeroLocus
      p P Q₀ eG hQ₀ D

set_option maxHeartbeats 800000 in
-- Choosing the universal quotient representatives leaves large dependent chart terms.
/-- Intrinsic universal-quotient target CBC is enough for projective
representability.  Representatives of the universal Quot class are chosen internally;
no transported kernel morphism or detection compatibility is assumed. -/
theorem
    exists_quotFunctorP_representableBy_isHProjective_of_universal_quotientTargetCBC
    (p : G ⟶ F) [Epi p]
    (Q₀ : Over S) [IsLocallyNoetherian Q₀.left]
    (eG : (quotFunctorP G P).RepresentableBy Q₀)
    (hQ₀ : IsHProjective Q₀.hom)
    [G.IsQuasicoherent] [G.IsFinitePresentation] [F.IsQuasicoherent]
    (Hcbc : ∀ (U : Q₀.left.affineOpens)
      (y : Modules.QuotientPullbackData G (projectiveSpaceOverπ n S)
        (Over.mk ((U.2.isoSpec.inv ≫ U.1.ι) ≫ Q₀.hom))),
      Quotient.mk _ y =
          (((quotFunctorP G P).map
            ((Over.homMk (U.2.isoSpec.inv ≫ U.1.ι) :
              Over.mk ((U.2.isoSpec.inv ≫ U.1.ι) ≫ Q₀.hom) ⟶ Q₀).op))
                (eG.homEquiv (𝟙 Q₀))).1 →
        Nonempty
          (Proj.HasEventualFiniteProjectiveCanonicalGlobalSectionsBaseChange
            (y.polynomialQuotient
              ((U.2.isoSpec.inv ≫ U.1.ι) ≫ Q₀.hom)))) :
    ∃ Q : Over S,
      Nonempty ((quotFunctorP F P).RepresentableBy Q) ∧
        IsHProjective Q.hom := by
  let M : QuotientKernelAffineCanonicalCBCModels p P
      (T := Q₀) (z := eG.homEquiv (𝟙 Q₀)) :=
    Classical.choice
      (QuotientKernelAffineCanonicalCBCModels.nonempty_of_quotientTargetCBC
        p P Hcbc)
  let D : QuotientKernelZeroLocusData p P Q₀ (eG.homEquiv (𝟙 Q₀)) :=
    M.toQuotientKernelZeroLocusData p P
  exact
    exists_quotFunctorP_representableBy_isHProjective_of_universal_precomp_zeroLocus
      p P Q₀ eG hQ₀ D

set_option maxHeartbeats 800000 in
-- The universal quotient point carries a dependent family of affine representatives.
/-- A positive-dimensional twisted-free source has projective fixed-polynomial Quot
precomposition over any locally noetherian projective representative.  Canonical
global-sections base change and the closed zero locus are constructed internally. -/
theorem
    exists_quotFunctorP_representableBy_isHProjective_of_universal_twistedFree
    {S : Scheme.{u}} (n r : ℕ) (hn : 0 < n) (l : ℤ)
    {F : (projectiveSpaceOver n S).Modules}
    (p : Modules.QuotientPullbackData.twistedFreeAmbient
      (S := S) (n := n) (r := r) (l := l) ⟶ F) [Epi p]
    (P : Polynomial ℚ)
    (Q₀ : Over S) [IsLocallyNoetherian Q₀.left]
    (eG : (quotFunctorP
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (S := S) (n := n) (r := r) (l := l)) P).RepresentableBy Q₀)
    (hQ₀ : IsHProjective Q₀.hom) [F.IsQuasicoherent] :
    ∃ Q : Over S,
      Nonempty ((quotFunctorP F P).RepresentableBy Q) ∧
        IsHProjective Q.hom := by
  let M : QuotientKernelAffineCanonicalCBCModels p P
      (T := Q₀) (z := eG.homEquiv (𝟙 Q₀)) :=
    Classical.choice
      (QuotientKernelAffineCanonicalCBCModels.nonempty_twistedFree_of_positive_dimension
        n r hn l p P
          (eG.homEquiv (𝟙 Q₀)))
  let D : QuotientKernelZeroLocusData p P Q₀ (eG.homEquiv (𝟙 Q₀)) :=
    M.toQuotientKernelZeroLocusData p P
  exact
    exists_quotFunctorP_representableBy_isHProjective_of_universal_precomp_zeroLocus
      p P Q₀ eG hQ₀ D

set_option maxHeartbeats 800000 in
-- The universal quotient point carries a dependent family of affine representatives.
/-- A twisted-free source on projective zero-space has projective fixed-polynomial
Quot precomposition over any locally Noetherian projective representative.  The
canonical base-change package and closed zero locus are constructed internally. -/
theorem
    exists_quotFunctorP_representableBy_isHProjective_of_universal_twistedFree_zero
    {S : Scheme.{u}} (r : ℕ) (l : ℤ)
    {F : (projectiveSpaceOver 0 S).Modules}
    (p : Modules.QuotientPullbackData.twistedFreeAmbient
      (S := S) (n := 0) (r := r) (l := l) ⟶ F) [Epi p]
    (P : Polynomial ℚ)
    (Q₀ : Over S) [IsLocallyNoetherian Q₀.left]
    (eG : (quotFunctorP
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (S := S) (n := 0) (r := r) (l := l)) P).RepresentableBy Q₀)
    (hQ₀ : IsHProjective Q₀.hom) [F.IsQuasicoherent] :
    ∃ Q : Over S,
      Nonempty ((quotFunctorP F P).RepresentableBy Q) ∧
        IsHProjective Q.hom := by
  let M : QuotientKernelAffineCanonicalCBCModels p P
      (T := Q₀) (z := eG.homEquiv (𝟙 Q₀)) :=
    Classical.choice
      (QuotientKernelAffineCanonicalCBCModels.nonempty_twistedFree_zero
        r l p P (eG.homEquiv (𝟙 Q₀)))
  let D : QuotientKernelZeroLocusData p P Q₀ (eG.homEquiv (𝟙 Q₀)) :=
    M.toQuotientKernelZeroLocusData p P
  exact
    exists_quotFunctorP_representableBy_isHProjective_of_universal_precomp_zeroLocus
      p P Q₀ eG hQ₀ D

end AlgebraicGeometry.Scheme

end

end
