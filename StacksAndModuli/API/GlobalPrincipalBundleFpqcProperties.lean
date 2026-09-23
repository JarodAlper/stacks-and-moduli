module

public import StacksAndModuli.API.FpqcMorphismPropertySieve
public import StacksAndModuli.API.GlobalPrincipalBundleFpqcTorsorDescent

/-!
# FPQC descent of the properties of a principal-bundle projection

Given a cartesian gluing of the underlying total spaces in a principal-bundle
descent datum, the descended projection is flat, surjective, locally of finite
presentation, and smooth.  The proof maps a small covering family from the
over-category to schemes and applies fpqc sieve-locality of morphism
properties.  Together with torsor-map descent, this removes every structural
hypothesis from the gluing theorem except construction of the underlying
cartesian total space.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {G : Over S} [GrpObj G]

namespace ClassifyingObj.UnderlyingGluing

variable {T : Over S} {R : Sieve T}
  {D : CategoryTheory.Functor R.arrows.category (ClassifyingObj G)}
  {hDobj : ∀ q : R.arrows.category,
    (classifyingPrestack G).p.obj (D.obj q) = q.obj.left}
  {hDmap : ∀ {q r : R.arrows.category} (k : q ⟶ r),
    IsHomLift (classifyingPrestack G).p k.hom.left (D.map k)}
  (A : ClassifyingObj.UnderlyingGluing D hDobj hDmap)

set_option maxHeartbeats 800000 in
/-- Any target-Zariski-local, base-change-stable property satisfying singleton
fpqc descent passes from the local bundle projections to the descended
projection in an underlying gluing. -/
lemma descended_property (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P] [P.IsStableUnderBaseChange]
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)]
    (hR : R ∈ Scheme.fpqcTopology.over S T)
    (hlocal : ∀ q : R.arrows.category, P (D.obj q).bundle.p.left) :
    P A.p.left := by
  let K : Precoverage (Over S) :=
    Scheme.fpqcPrecoverage.comap (Over.forget S)
  have hJK : Scheme.fpqcTopology.over S = K.toGrothendieck := by
    dsimp [K]
    exact over_toGrothendieck_eq_toGrothendieck_comap_forget
      Scheme.fpqcPrecoverage S
  have hRK : R ∈ K.toGrothendieck T := by
    rw [← hJK]
    exact hR
  obtain ⟨Q, hQ, hQR⟩ :=
    K.mem_toGrothendieck_iff_of_isStableUnderComposition.mp hRK
  let Ebig : K.ZeroHypercover T :=
    { __ := Q.preZeroHypercover
      mem₀ := by simpa using hQ }
  letI : Precoverage.Small.{u} Scheme.fpqcPrecoverage := by
    unfold Scheme.fpqcPrecoverage
    exact AlgebraicGeometry.Scheme.instSmallPropQCPrecoverage
  letI : Precoverage.Small.{u} K := by
    dsimp [K]
    infer_instance
  letI : Precoverage.ZeroHypercover.Small.{u} Ebig := inferInstance
  let E : K.ZeroHypercover.{u} T :=
    Precoverage.ZeroHypercover.restrictIndexOfSmall.{u} Ebig
  let E₀ : Scheme.fpqcPrecoverage.ZeroHypercover.{u} T.left :=
    E.map (Over.forget S) (by
      intro X U hU
      exact hU)
  apply MorphismProperty.of_fpqc_family (P := P) A.p.left E₀.f E₀.mem₀
  intro i
  change E.I₀ at i
  have hQi : Q (E.f i) := by
    change Q ((Q.preZeroHypercover).f
      (Precoverage.ZeroHypercover.Small.restrictFun.{u} Ebig i))
    exact (Precoverage.ZeroHypercover.Small.restrictFun.{u} Ebig i).2
  have hRi : R (E.f i) := by
    apply hQR
    exact hQi
  let q : R.arrows.category := R.arrows.categoryMk (E.f i) hRi
  let e : (D.obj q).base ⟶ E.X i := eqToHom (hDobj q)
  letI : IsIso e := by
    dsimp [e]
    infer_instance
  letI : IsIso e.left := by
    change IsIso ((Over.forget S).map e)
    infer_instance
  have hiso : IsPullback (e ≫ E.f i) e (𝟙 T) (E.f i) :=
    IsPullback.of_vert_isIso ⟨by simp⟩
  have hpbover : IsPullback (A.total q)
      ((D.obj q).bundle.p ≫ e) A.p (E.f i) := by
    simpa [q, e] using (A.isPullback q).paste_vert hiso
  have hpbscheme : IsPullback (A.total q).left
      ((D.obj q).bundle.p.left ≫ e.left) A.p.left (E.f i).left := by
    simpa using hpbover.map (Over.forget S)
  have hlocal' : P ((D.obj q).bundle.p.left ≫ e.left) := by
    rw [P.cancel_right_of_respectsIso]
    exact hlocal q
  change P (pullback.snd A.p.left (E.f i).left)
  rw [← P.cancel_left_of_respectsIso hpbscheme.isoPullback.hom,
    hpbscheme.isoPullback_hom_snd]
  exact hlocal'

/-- Flatness of the projection descends from the fpqc datum. -/
lemma descended_flat (hR : R ∈ Scheme.fpqcTopology.over S T) :
    Flat A.p.left := by
  letI : IsZariskiLocalAtTarget
      (@Flat : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _
  letI : MorphismProperty.DescendsAlong
      (@Flat : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) :=
    flat_descendsAlong_fpqc
  exact A.descended_property @Flat hR fun _ ↦ inferInstance

/-- Surjectivity of the projection descends from the fpqc datum. -/
lemma descended_surjective (hR : R ∈ Scheme.fpqcTopology.over S T) :
    Surjective A.p.left :=
  A.descended_property @Surjective hR fun _ ↦ inferInstance

/-- Local finite presentation of the projection descends from the fpqc datum. -/
lemma descended_locallyOfFinitePresentation
    (hR : R ∈ Scheme.fpqcTopology.over S T) :
    LocallyOfFinitePresentation A.p.left := by
  letI : IsZariskiLocalAtTarget
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _
  exact A.descended_property @LocallyOfFinitePresentation hR fun _ ↦ inferInstance

/-- Smoothness of the projection descends from the fpqc datum. -/
lemma descended_smooth (hR : R ∈ Scheme.fpqcTopology.over S T) :
    Smooth A.p.left := by
  letI : IsZariskiLocalAtTarget
      (@Smooth : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _
  exact A.descended_property @Smooth hR fun _ ↦ inferInstance

/-- An underlying cartesian gluing of the total spaces automatically carries
all remaining structure of the glued principal bundle. -/
theorem exists_gluing
    (A : ClassifyingObj.UnderlyingGluing D hDobj hDmap)
    (hR : R ∈ Scheme.fpqcTopology.over S T) :
    ∃ (a : ClassifyingObj G) (_ : (classifyingPrestack G).p.obj a = T)
      (ε : ∀ q : R.arrows.category, D.obj q ⟶ a),
      (∀ q : R.arrows.category,
        IsHomLift (classifyingPrestack G).p q.obj.hom (ε q)) ∧
      ∀ {q r : R.arrows.category} (k : q ⟶ r),
        D.map k ≫ ε r = ε q :=
  ClassifyingObj.UnderlyingGluing.exists_gluing_of_underlying_of_properties A hR
    (A.descended_flat hR) (A.descended_surjective hR)
    (A.descended_locallyOfFinitePresentation hR) (A.descended_smooth hR)

end ClassifyingObj.UnderlyingGluing

end AlgebraicGeometry.Scheme
