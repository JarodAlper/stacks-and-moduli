module

public import StacksAndModuli.API.AffineRepresentedPredicateIdealSheaf
public import StacksAndModuli.API.QuotientKernelFiniteModelZeroLocus
public import StacksAndModuli.API.RightExactFunctorKernelVanishing

/-!
# Affine equations for the kernel condition in Quot

This file turns finite-free vanishing models for the pulled-back ambient-kernel map on
the affine charts of a representing scheme into one geometric affine predicate.  The
coefficient ideal of each model represents the condition that the corresponding Quot
class kills the kernel of the ambient presentation.

The models need not be chosen compatibly on overlaps.  Compatibility of their coefficient
ideals follows from the common geometric predicate through
`Scheme.AffineMorphismPredicate.toIdealSheafData`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {n : ℕ}
variable {F G : (projectiveSpaceOver n S).Modules}
variable (p : G ⟶ F) [Epi p] (P : Polynomial ℚ)
variable {T : Over S} {z : (quotFunctorP G P).obj (op T)}

/-- For a chosen representative, the intrinsic Quot-class kernel condition is exactly
the vanishing of that representative's ambient-kernel composite. -/
lemma quotientClassKillsAmbientKernel_mk_iff
    (y : Modules.QuotientPullbackData G (projectiveSpaceOverπ n S) T) :
    QuotientClassKillsAmbientKernel p T (Quotient.mk _ y) ↔
      kernel.ι (Modules.QuotientPullbackData.ambientMap
        (f := projectiveSpaceOverπ n S) p T) ≫ y.π = 0 := by
  constructor
  · rintro ⟨y', hy', hzero⟩
    exact (Modules.QuotientPullbackData.kernel_ι_comp_eq_zero_iff_of_r p
      (Quotient.exact hy')).mp hzero
  · intro hzero
    exact ⟨y, rfl, hzero⟩

/-- The kernel condition for the pullback of a represented Quot class is detected by
the ambient-kernel composite of the canonical pulled-back representative. -/
lemma quotientClassKillsAmbientKernel_map_mk_iff
    {T' : Over S} (g : T' ⟶ T)
    (y : Modules.QuotientPullbackData G (projectiveSpaceOverπ n S) T) :
    QuotientClassKillsAmbientKernel p T'
        ((quotFunctor G (projectiveSpaceOverπ n S)).map g.op (Quotient.mk _ y)) ↔
      kernel.ι (Modules.QuotientPullbackData.ambientMap
        (f := projectiveSpaceOverπ n S) p T') ≫ (y.pullback g).π = 0 := by
  change QuotientClassKillsAmbientKernel p T' (Quotient.mk _ (y.pullback g)) ↔ _
  exact quotientClassKillsAmbientKernel_mk_iff p (y.pullback g)

/-- Pulling back the ambient-kernel composite itself detects the intrinsic kernel
condition for the pulled-back quotient.  Pullback need not preserve kernels; the
equivalence instead uses that it is a left adjoint and hence preserves the cokernel
presentation of the ambient epimorphism. -/
lemma Modules.QuotientPullbackData.pullback_kernelComposite_eq_zero_iff
    {X S : Scheme.{u}} {F G : X.Modules} {f : X ⟶ S}
    {T T' : Over S} (p : G ⟶ F) [Epi p] (g : T' ⟶ T)
    (y : Modules.QuotientPullbackData G f T) :
    kernel.ι (Modules.QuotientPullbackData.ambientMap (f := f) p T') ≫
        (y.pullback g).π = 0 ↔
      (Modules.pullback ((Over.pullback f).map g).left).map
        (kernel.ι (Modules.QuotientPullbackData.ambientMap (f := f) p T) ≫
          y.π) = 0 := by
  let H := Modules.pullback ((Over.pullback f).map g).left
  let a := Modules.QuotientPullbackData.ambientMap (f := f) p T
  let a' := Modules.QuotientPullbackData.ambientMap (f := f) p T'
  let cG := Modules.PullbackQuotient.pullbackComparison G ((Over.pullback f).map g)
  let cF := Modules.PullbackQuotient.pullbackComparison F ((Over.pullback f).map g)
  have ha : a' ≫ cF.hom = cG.hom ≫ H.map a := by
    simp [a, a', H, Modules.QuotientPullbackData.ambientMap, cG, cF,
      Modules.PullbackQuotient.pullbackComparison]
  change kernel.ι a' ≫ (cG.hom ≫ H.map y.π) = 0 ↔
    H.map (kernel.ι a ≫ y.π) = 0
  rw [CategoryTheory.map_kernel_ι_comp_eq_zero_iff_of_isLeftAdjoint]
  constructor
  · intro h
    let d' := Abelian.epiDesc a' (cG.hom ≫ H.map y.π) (by
      simpa only [Category.assoc] using h)
    let d : H.obj ((Modules.pullback
        ((Over.pullback f).obj T).hom).obj F) ⟶ H.obj y.Q := cF.inv ≫ d'
    have hd : H.map a ≫ d = H.map y.π := by
      rw [← cancel_epi cG.hom]
      dsimp only [d]
      calc
        cG.hom ≫ H.map a ≫ cF.inv ≫ d' =
            (a' ≫ cF.hom) ≫ cF.inv ≫ d' := by
              simp only [Category.assoc, ha]
        _ = a' ≫ d' := by simp
        _ = cG.hom ≫ H.map y.π := Abelian.comp_epiDesc _ _ _
    rw [← hd, ← Category.assoc, kernel.condition, zero_comp]
  · intro h
    let d := Abelian.epiDesc (H.map a) (H.map y.π) h
    have hd : a' ≫ (cF.hom ≫ d) = cG.hom ≫ H.map y.π := by
      rw [← Category.assoc, ha, Category.assoc, Abelian.comp_epiDesc]
    rw [← hd]
    simp only [← Category.assoc, kernel.condition, zero_comp]

/-- A finite-free vanishing model on one canonical affine chart of a Quot parameter
scheme.

The total space `X` and the morphism `q` are deliberately abstract.  In the application,
`X` is projective space over the chart and `q` is the pullback of the ambient kernel map
followed by the universal quotient.  The `detect` field is the only comparison with that
geometric construction needed by the zero-locus argument. -/
structure QuotientKernelAffineFiniteFreeModel (U : T.left.affineOpens) where
  /-- Total space carrying the chartwise kernel morphism. -/
  X : Scheme.{u}
  /-- Structure morphism to the canonical spectrum of the affine chart. -/
  pX : X ⟶ Spec (.of Γ(T.left, U.1))
  /-- Source of the chartwise kernel morphism. -/
  E : X.Modules
  /-- Target of the chartwise kernel morphism. -/
  Q : X.Modules
  /-- Chartwise morphism whose vanishing is the ambient-kernel condition. -/
  q : E ⟶ Q
  /-- Finite-free coefficient model for universal vanishing of `q`. -/
  model : Modules.HasFiniteFreeVanishingModel pX q
  /-- After every affine base change of the chart, the kernel-killing condition is
  exactly the vanishing condition detected by `model`. -/
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
        (Limits.pullback.snd (Spec.map (CommRingCat.ofHom f)) pX)).map q = 0

/-- A chartwise finite-free kernel model on every affine open of a Quot parameter
scheme.  No overlap data are required. -/
structure QuotientKernelAffineFiniteFreeModels where
  /-- A finite-free model on every canonical affine chart. -/
  affineModel : ∀ U : T.left.affineOpens,
    Nonempty (QuotientKernelAffineFiniteFreeModel p P U (z := z))

namespace QuotientKernelAffineFiniteFreeModels

/-- The geometric predicate on a morphism to the parameter scheme: the induced Quot
class kills the kernel of the ambient epimorphism. -/
def kernelCondition
    (W : Scheme.{u}) [IsAffine W] (g : W ⟶ T.left) : Prop :=
  QuotientClassKillsAmbientKernel p
    (Over.mk (g ≫ T.hom))
    (((quotFunctorP G P).map
      ((Over.homMk g : Over.mk (g ≫ T.hom) ⟶ T).op)) z).1

/-- Chartwise finite-free kernel models represent the geometric kernel condition by
their coefficient ideals. -/
noncomputable def toAffineMorphismPredicate
    (D : QuotientKernelAffineFiniteFreeModels p P (T := T) (z := z)) :
    AffineMorphismPredicate T.left where
  condition W _ g := kernelCondition p P W g (z := z)
  ideal U := (Classical.choice (D.affineModel U)).model.ideal
  represents U A _ f := by
    let C := Classical.choice (D.affineModel U)
    refine (C.detect A f).trans ?_
    rw [C.model.pullback_zero_iff A f]
    exact C.model.coordinates.baseChangeToPi_eq_zero_iff f

@[simp]
lemma toAffineMorphismPredicate_ideal
    (D : QuotientKernelAffineFiniteFreeModels p P (T := T) (z := z))
    (U : T.left.affineOpens) :
    (D.toAffineMorphismPredicate p P).ideal U =
      (Classical.choice (D.affineModel U)).model.ideal :=
  rfl

end QuotientKernelAffineFiniteFreeModels

end AlgebraicGeometry.Scheme
