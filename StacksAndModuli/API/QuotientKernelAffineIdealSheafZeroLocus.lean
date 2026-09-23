module

public import StacksAndModuli.API.AffineRepresentedPredicateIdealSheaf
public import StacksAndModuli.API.IdealSheafAffineCharts
public import StacksAndModuli.API.QuotientKernelAffinePredicate
public import StacksAndModuli.API.QuotientKernelFiniteModelZeroLocus
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Global Quotient-kernel zero loci from affine ideals

Finite presentations on affine opens produce coefficient ideals, but not canonical
presentations on overlaps. `AffineMorphismPredicate` shows that the ideals nevertheless
form an ideal sheaf, since they represent the same pullback-stable condition. This file
then proves that its closed subscheme universally represents the condition that a Quot
class kills the pulled-back ambient kernel.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {n : ℕ}
variable {F G : (projectiveSpaceOver n S).Modules}
variable (p : G ⟶ F) [Epi p] (P : Polynomial ℚ)
variable {T : Over S} {z : (quotFunctorP G P).obj (op T)}

/-- Pulling back a Quot class preserves the condition of killing the ambient
kernel. -/
lemma quotientClassKillsAmbientKernel_map
    {W V : Over S} (g : V ⟶ W)
    {x : (quotFunctor G (projectiveSpaceOverπ n S)).obj (op W)}
    (h : QuotientClassKillsAmbientKernel p W x) :
    QuotientClassKillsAmbientKernel p V
      ((quotFunctor G (projectiveSpaceOverπ n S)).map g.op x) := by
  obtain ⟨y, hy, hzero⟩ := h
  refine ⟨y.pullback g, ?_,
    Modules.QuotientPullbackData.kernel_ι_comp_pullback_π_eq_zero
      p y hzero g⟩
  rw [← hy]
  rfl

/-- Killing the ambient kernel is invariant under an isomorphism of test objects. -/
lemma quotientClassKillsAmbientKernel_map_iso_iff
    {W V : Over S} (e : V ≅ W)
    (x : (quotFunctor G (projectiveSpaceOverπ n S)).obj (op W)) :
    QuotientClassKillsAmbientKernel p V
        ((quotFunctor G (projectiveSpaceOverπ n S)).map e.hom.op x) ↔
      QuotientClassKillsAmbientKernel p W x := by
  constructor
  · intro h
    have h' := quotientClassKillsAmbientKernel_map p e.inv h
    have hmap := ConcreteCategory.congr_hom
      ((quotFunctor G (projectiveSpaceOverπ n S)).map_comp
        e.hom.op e.inv.op) x
    change (quotFunctor G (projectiveSpaceOverπ n S)).map
        (e.hom.op ≫ e.inv.op) x =
      (quotFunctor G (projectiveSpaceOverπ n S)).map e.inv.op
        ((quotFunctor G (projectiveSpaceOverπ n S)).map e.hom.op x) at hmap
    rw [show e.hom.op ≫ e.inv.op = 𝟙 _ by simp] at hmap
    rw [← hmap] at h'
    simpa using h'
  · exact quotientClassKillsAmbientKernel_map p e.hom

/-- The kernel-vanishing condition, phrased for an ordinary scheme morphism into the
parameter scheme. -/
def QuotientKernelMorphismCondition (W : Scheme.{u}) (g : W ⟶ T.left) : Prop :=
  QuotientClassKillsAmbientKernel p (Over.mk (g ≫ T.hom))
    (((quotFunctorP G P).map (Over.homMk g rfl :
      Over.mk (g ≫ T.hom) ⟶ T).op) z).1

/-- The kernel-vanishing condition is preserved by pullback. -/
lemma quotientKernelMorphismCondition_comp
    {W V : Scheme.{u}} (g : W ⟶ T.left) (k : V ⟶ W)
    (h : QuotientKernelMorphismCondition p P W g (z := z)) :
    QuotientKernelMorphismCondition p P V (k ≫ g) (z := z) := by
  let W' : Over S := Over.mk (g ≫ T.hom)
  let V' : Over S := Over.mk ((k ≫ g) ≫ T.hom)
  let kg : W' ⟶ T := Over.homMk g rfl
  let kk : V' ⟶ W' := Over.homMk k (by simp [W', V'])
  change QuotientClassKillsAmbientKernel p W'
      (((quotFunctorP G P).map kg.op) z).1 at h
  change QuotientClassKillsAmbientKernel p V'
      (((quotFunctorP G P).map (Over.homMk (k ≫ g) rfl : V' ⟶ T).op) z).1
  have h' := quotientClassKillsAmbientKernel_map p kk h
  change QuotientClassKillsAmbientKernel p V'
    ((quotFunctor G (projectiveSpaceOverπ n S)).map kk.op
      (((quotFunctorP G P).map kg.op) z).1) at h'
  have hcomp : (Over.homMk (k ≫ g) rfl : V' ⟶ T) = kk ≫ kg := by
    ext
    rfl
  rw [hcomp]
  change QuotientClassKillsAmbientKernel p V'
    (((quotFunctorP G P).map (kg.op ≫ kk.op)) z).1
  have hmapP := ConcreteCategory.congr_hom
    ((quotFunctorP G P).map_comp kg.op kk.op) z
  have hmap := congrArg Subtype.val hmapP
  change (((quotFunctorP G P).map (kg.op ≫ kk.op)) z).1 =
    (quotFunctor G (projectiveSpaceOverπ n S)).map kk.op
      (((quotFunctorP G P).map kg.op) z).1 at hmap
  rw [hmap]
  exact h'

/-- The kernel-vanishing condition is invariant under changing an affine source by an
isomorphism. -/
lemma quotientKernelMorphismCondition_iso_iff
    (W W' : Scheme.{u}) (e : W ≅ W') (g : W' ⟶ T.left) :
    QuotientKernelMorphismCondition p P W (e.hom ≫ g) (z := z) ↔
      QuotientKernelMorphismCondition p P W' g (z := z) := by
  constructor
  · intro h
    have h' := quotientKernelMorphismCondition_comp p P (e.hom ≫ g) e.inv h
    simpa using h'
  · exact quotientKernelMorphismCondition_comp p P g e.hom

/-- The kernel-vanishing condition can be checked on an arbitrary open cover. -/
lemma quotientKernelMorphismCondition_iff_openCover
    (W : Scheme.{u}) (g : W ⟶ T.left) (U : W.OpenCover.{u}) :
    QuotientKernelMorphismCondition p P W g (z := z) ↔
      ∀ i, QuotientKernelMorphismCondition p P (U.X i) (U.f i ≫ g) (z := z) := by
  constructor
  · intro h i
    exact quotientKernelMorphismCondition_comp p P g (U.f i) h
  · intro h
    let W' : Over S := Over.mk (g ≫ T.hom)
    let kg : W' ⟶ T := Over.homMk g rfl
    change QuotientClassKillsAmbientKernel p W'
      (((quotFunctorP G P).map kg.op) z).1
    apply (quotientClassKillsAmbientKernel_iff_openCover p W' U
      (((quotFunctorP G P).map kg.op) z).1).mpr
    intro i
    let O : Over S := openCoverObjectOver W' U i
    let j : O ⟶ W' := openCoverMapOver W' U i
    let V' : Over S := Over.mk ((U.f i ≫ g) ≫ T.hom)
    let c : V' ⟶ T := Over.homMk (U.f i ≫ g) rfl
    let e : V' ≅ O := Over.isoMk (Iso.refl _) (by
      simp [V', O, W', openCoverObjectOver])
    let xO : (quotFunctor G (projectiveSpaceOverπ n S)).obj (op O) :=
      (quotFunctor G (projectiveSpaceOverπ n S)).map j.op
        (((quotFunctorP G P).map kg.op) z).1
    apply (quotientClassKillsAmbientKernel_map_iso_iff p e xO).mp
    have hi := h i
    change QuotientClassKillsAmbientKernel p V'
      (((quotFunctorP G P).map c.op) z).1 at hi
    have hc : e.hom ≫ j ≫ kg = c := by
      ext
      simp [e, j, kg, c]
    have hP :
        (quotFunctorP G P).map e.hom.op
            ((quotFunctorP G P).map j.op
              ((quotFunctorP G P).map kg.op z)) =
          (quotFunctorP G P).map c.op z := by
      simpa only [← Functor.map_comp_apply, ← op_comp, hc]
    have hx :
        (quotFunctor G (projectiveSpaceOverπ n S)).map e.hom.op xO =
          (((quotFunctorP G P).map c.op) z).1 :=
      congrArg Subtype.val hP
    rw [hx]
    exact hi

/-- Affine coefficient ideals representing the Quotient-kernel condition on every
affine open of the parameter scheme. -/
structure AffineQuotientKernelIdealModels where
  /-- The represented affine predicate and its coefficient ideals. -/
  data : T.left.AffineMorphismPredicate
  /-- The predicate represented by `data` is exactly Quotient-kernel vanishing. -/
  detects : ∀ (W : Scheme.{u}) [IsAffine W] (g : W ⟶ T.left),
    data.condition W g ↔ QuotientKernelMorphismCondition p P W g (z := z)

namespace AffineQuotientKernelIdealModels

variable (D : AffineQuotientKernelIdealModels p P (T := T) (z := z))

/-- The ideal sheaf obtained from the affine coefficient ideals. -/
noncomputable abbrev idealSheaf : T.left.IdealSheafData :=
  D.data.toIdealSheafData

/-- The ordinary-morphism formulation agrees with the intrinsic formulation on an
object already equipped with its map to the base. -/
lemma morphismCondition_iff_overCondition
    (W : Over S) (g : W ⟶ T) :
    QuotientKernelMorphismCondition p P W.left g.left (z := z) ↔
      QuotientClassKillsAmbientKernel p W
        (((quotFunctorP G P).map g.op) z).1 := by
  let W' : Over S := Over.mk (g.left ≫ T.hom)
  let c : W' ⟶ T := Over.homMk g.left rfl
  let e : W' ≅ W := Over.isoMk (Iso.refl _) (by
    change W.hom = g.left ≫ T.hom
    exact (Over.w g).symm)
  have hc : e.hom ≫ g = c := by
    ext
    simp [e, c]
  have hP :
      (quotFunctorP G P).map e.hom.op ((quotFunctorP G P).map g.op z) =
        (quotFunctorP G P).map c.op z := by
    simpa only [← Functor.map_comp_apply, ← op_comp, hc]
  change QuotientClassKillsAmbientKernel p W'
      (((quotFunctorP G P).map c.op) z).1 ↔ _
  rw [← congrArg Subtype.val hP]
  exact quotientClassKillsAmbientKernel_map_iso_iff p e _

/-- On a single target affine open, the coefficient-ideal chart has precisely the
universal property of the Quotient-kernel condition, for every affine source. -/
lemma condition_iff_exists_affineChartLift
    (U : T.left.affineOpens) (W : Scheme.{u}) [IsAffine W]
    (psi : W ⟶ U.1.toScheme) :
    QuotientKernelMorphismCondition p P W (psi ≫ U.1.ι) (z := z) ↔
      ∃ h : W ⟶ D.idealSheaf.glueDataObj U,
        h ≫ D.idealSheaf.glueDataObjι U = psi := by
  have hiso : ∀ (V V' : Scheme.{u}) [IsAffine V] [IsAffine V']
      (e : V ≅ V') (g : V' ⟶ T.left),
      D.data.condition V (e.hom ≫ g) ↔ D.data.condition V' g := by
    intro V V' _ _ e g
    exact (D.detects V (e.hom ≫ g)).trans
      ((quotientKernelMorphismCondition_iso_iff p P V V' e g).trans
        (D.detects V' g).symm)
  exact (D.detects W (psi ≫ U.1.ι)).symm.trans
    (D.data.condition_iff_exists_affineChartLift hiso U W psi)

/-- Globally, killing the ambient kernel is equivalent to locally factoring through
the affine coefficient-ideal charts. -/
lemma condition_iff_locallyFactors_affineChart
    (W : Scheme.{u}) (g : W ⟶ T.left) :
    QuotientKernelMorphismCondition p P W g (z := z) ↔
      LocallyFactors D.idealSheaf.affineChart (Over.mk g) := by
  constructor
  · intro h x
    let i := T.left.affineCover.idx (g.base x)
    let U : T.left.affineOpens :=
      ⟨(T.left.affineCover.f i).opensRange,
        isAffineOpen_opensRange (T.left.affineCover.f i)⟩
    have hxU : g.base x ∈ U.1 := T.left.affineCover.covers (g.base x)
    have hxpre : x ∈ g ⁻¹ᵁ U.1 := hxU
    obtain ⟨R, b, hb, hxb, hsub⟩ :=
      Scheme.exists_affine_mem_range_and_range_subset hxpre
    letI := hb
    have hsub' : Set.range (b ≫ g).base ⊆ Set.range U.1.ι.base := by
      rintro _ ⟨v, rfl⟩
      have hv : g.base (b.base v) ∈ U.1 := hsub ⟨v, rfl⟩
      exact ⟨⟨g.base (b.base v), hv⟩, rfl⟩
    let psi : Spec R ⟶ U.1.toScheme :=
      IsOpenImmersion.lift U.1.ι (b ≫ g) hsub'
    have hpsi : psi ≫ U.1.ι = b ≫ g :=
      IsOpenImmersion.lift_fac U.1.ι (b ≫ g) hsub'
    have hbcond := quotientKernelMorphismCondition_comp p P g b h
    have hpsicond :
        QuotientKernelMorphismCondition p P (Spec R) (psi ≫ U.1.ι)
          (z := z) := by
      rw [hpsi]
      exact hbcond
    obtain ⟨a, ha⟩ :=
      (condition_iff_exists_affineChartLift (p := p) (P := P)
        D U (Spec R) psi).mp hpsicond
    let V : Over T.left := Over.mk (b ≫ g)
    let k : V ⟶ Over.mk g := Over.homMk b rfl
    refine ⟨V, k, ?_, hxb, U, a, ?_⟩
    · change IsOpenImmersion b
      exact hb
    · change a ≫ (D.idealSheaf.glueDataObjι U ≫ U.1.ι) = b ≫ g
      rw [← Category.assoc, ha, hpsi]
  · intro hloc
    choose V k hk hx U a ha using hloc
    let COV : W.OpenCover :=
      openCoverOfMaps (fun x ↦ (V x).left) (fun x ↦ (k x).left) hk
        (fun x ↦ ⟨x, hx x⟩)
    apply (quotientKernelMorphismCondition_iff_openCover p P W g COV).mpr
    change ∀ x : W, QuotientKernelMorphismCondition p P (V x).left
      ((k x).left ≫ g) (z := z)
    intro x
    let C : Over T.left := D.idealSheaf.affineChart (U x)
    haveI : IsAffine (D.idealSheaf.glueDataObj (U x)) := by
      change IsAffine (Spec (.of
        (Γ(T.left, (U x).1) ⧸ D.idealSheaf.ideal (U x))))
      infer_instance
    have hC : QuotientKernelMorphismCondition p P C.left C.hom (z := z) := by
      change QuotientKernelMorphismCondition p P
        (D.idealSheaf.glueDataObj (U x))
        (D.idealSheaf.glueDataObjι (U x) ≫ (U x).1.ι) (z := z)
      exact (condition_iff_exists_affineChartLift (p := p) (P := P) D (U x)
        (D.idealSheaf.glueDataObj (U x))
        (D.idealSheaf.glueDataObjι (U x))).mpr ⟨𝟙 _, by simp⟩
    have hV := quotientKernelMorphismCondition_comp p P C.hom (a x) hC
    have heq : a x ≫ C.hom = (k x).left ≫ g :=
      (ha x).trans (Over.w (k x)).symm
    rw [heq] at hV
    change QuotientKernelMorphismCondition p P (V x).left
      ((k x).left ≫ g) (z := z)
    exact hV

/-- The global ideal-sheaf subscheme represents the Quotient-kernel condition on an
arbitrary test scheme. -/
lemma condition_iff_exists_subschemeLift
    (W : Scheme.{u}) (g : W ⟶ T.left) :
    QuotientKernelMorphismCondition p P W g (z := z) ↔
      ∃ h : W ⟶ D.idealSheaf.subscheme,
        h ≫ D.idealSheaf.subschemeι = g :=
  (condition_iff_locallyFactors_affineChart (p := p) (P := P) D W g).trans
    (D.idealSheaf.locallyFactors_affineChart_iff_exists_subschemeLift g)

/-- The closed subscheme associated to the coefficient ideal sheaf is the universal
zero locus for the ambient-kernel condition. -/
noncomputable def toQuotientKernelZeroLocusData :
    QuotientKernelZeroLocusData p P T z where
  Z := Over.mk (D.idealSheaf.subschemeι ≫ T.hom)
  ι := Over.homMk D.idealSheaf.subschemeι rfl
  isClosedImmersion := by
    change IsClosedImmersion D.idealSheaf.subschemeι
    infer_instance
  factor_iff W g := by
    constructor
    · intro hkill
      have hcond : QuotientKernelMorphismCondition p P W.left g.left (z := z) :=
        (morphismCondition_iff_overCondition (p := p) (P := P) W g).mpr hkill
      obtain ⟨k, hk⟩ :=
        (condition_iff_exists_subschemeLift (p := p) (P := P)
          D W.left g.left).mp hcond
      let h : W ⟶ Over.mk (D.idealSheaf.subschemeι ≫ T.hom) :=
        Over.homMk k (by
          change k ≫ (D.idealSheaf.subschemeι ≫ T.hom) = W.hom
          rw [← Category.assoc, hk, Over.w g])
      refine ⟨h, ?_⟩
      ext
      exact hk
    · rintro ⟨h, hh⟩
      have hk : h.left ≫ D.idealSheaf.subschemeι = g.left := by
        exact congrArg Over.Hom.left hh
      have hcond : QuotientKernelMorphismCondition p P W.left g.left (z := z) :=
        (condition_iff_exists_subschemeLift (p := p) (P := P)
          D W.left g.left).mpr ⟨h.left, hk⟩
      exact (morphismCondition_iff_overCondition (p := p) (P := P) W g).mp hcond

end AffineQuotientKernelIdealModels

/-- Affine coefficient-ideal models for every test quotient make fixed-polynomial
precomposition relatively representable by closed immersions. -/
theorem quotFunctorPPrecomp_relative_closed_of_affineQuotientKernelIdealModels
    (H : ∀ (T : Over S) (z : (quotFunctorP G P).obj (op T)),
      Nonempty (AffineQuotientKernelIdealModels p P (T := T) (z := z))) :
    MorphismProperty.relative uliftYoneda.{u + 1}
      (MorphismProperty.over
        (@IsClosedImmersion : MorphismProperty Scheme.{u}))
      (quotFunctorPPrecomp p P) :=
  quotFunctorPPrecomp_relative_closed p P fun T z ↦
    ⟨(AffineQuotientKernelIdealModels.toQuotientKernelZeroLocusData
      p P (Classical.choice (H T z)))⟩

end AlgebraicGeometry.Scheme
