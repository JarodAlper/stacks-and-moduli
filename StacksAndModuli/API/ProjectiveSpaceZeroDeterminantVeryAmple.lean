module

public import StacksAndModuli.API.ProjectiveSpaceZeroGrassmannianImmersion
public import StacksAndModuli.API.RepresentedGrassmannianVeryAmple
public import StacksAndModuli.API.RelativeVeryAmpleEmpty
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianNatTrans

/-!
# Determinant very ampleness on projective zero-space

On relative projective zero-space, the fixed-polynomial twisted-free Quot functor is a
relative Grassmannian.  This file identifies every twisted pushforward of its universal
quotient with the vector-bundle quotient classified by that Grassmannian.  Consequently
the determinant is relatively very ample in every degree, without the higher-dimensional
regularity and flattening inputs.

Main declaration:
- `AlgebraicGeometry.Scheme.
  exists_eventually_isRelativelyVeryAmple_universalQuot_int_zero`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- Pullback along mutually inverse scheme morphisms gives an equivalence of module
categories. -/
noncomputable def pullbackEquivalenceOfInverse
    {X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ X)
    (hgf : g ≫ f = 𝟙 Y) (hfg : f ≫ g = 𝟙 X) :
    Y.Modules ≌ X.Modules where
  functor := pullback f
  inverse := pullback g
  unitIso := pullbackInverseUnit hgf
  counitIso := pullbackInverseCounit hfg
  functor_unitIso_comp := pullbackInverse_triangle hgf hfg

/-- For mutually inverse scheme morphisms, pushforward along one is canonically
isomorphic to pullback along the other. -/
noncomputable def pushforwardIsoPullbackInverse
    {X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ X)
    (hgf : g ≫ f = 𝟙 Y) (hfg : f ≫ g = 𝟙 X) :
    pushforward f ≅ pullback g :=
  (pullbackPushforwardAdjunction f).rightAdjointUniq
    (pullbackEquivalenceOfInverse f g hgf hfg).toAdjunction

/-- On projective zero-space, pushing forward any twist is canonically isomorphic to
pulling the untwisted module back along the inverse of `ℙ⁰_T ≅ T`. -/
noncomputable def projectiveSpaceZeroTwistPushforwardIso
    (T : Scheme.{u}) (Q : (Scheme.projectiveSpaceOver 0 T).Modules) (d : ℤ) :
    (pushforward (Scheme.projectiveSpaceOverπ 0 T)).obj
        (Scheme.projectiveSpaceOverTwistModule Q d) ≅
      (pullback (Scheme.projectiveSpaceOverZeroIso T).inv).obj Q := by
  let E := Scheme.projectiveSpaceOverZeroIso T
  have hgf : E.inv ≫ Scheme.projectiveSpaceOverπ 0 T = 𝟙 T := by
    rw [← Scheme.projectiveSpaceOverZeroIso_hom T]
    exact E.inv_hom_id
  have hfg : Scheme.projectiveSpaceOverπ 0 T ≫ E.inv =
      𝟙 (Scheme.projectiveSpaceOver 0 T) := by
    rw [← Scheme.projectiveSpaceOverZeroIso_hom T]
    exact E.hom_inv_id
  exact
    (pushforward (Scheme.projectiveSpaceOverπ 0 T)).mapIso
        (Scheme.projectiveSpaceOverZeroTwistModuleIso Q d) ≪≫
      (pushforwardIsoPullbackInverse
        (Scheme.projectiveSpaceOverπ 0 T) E.inv hgf hfg).app Q

namespace QuotientPullbackData

variable {S : Scheme.{u}} {l : ℤ} {r : ℕ} {T : Over S}

/-- The twisted pushforward of a projective-zero Quot target is its normalized
vector bundle on the parameter scheme. -/
noncomputable def zeroTwistPushforwardIsoNormalized
    (x : QuotientPullbackData
      (Scheme.projectiveSpaceOverTwistedFree 0 S l r)
      (Scheme.projectiveSpaceOverπ 0 S) T) (d : ℤ) :
    (pushforward (Scheme.projectiveSpaceOverπ 0 T.left)).obj
        (Scheme.projectiveSpaceOverTwistModule
          (quotDataOnProjectiveSpace (n := 0) (S := S)
            (Scheme.projectiveSpaceOverTwistedFree 0 S l r) x) d) ≅
      x.zeroNormalizedSheaf :=
  projectiveSpaceZeroTwistPushforwardIso T.left
    (quotDataOnProjectiveSpace (n := 0) (S := S)
      (Scheme.projectiveSpaceOverTwistedFree 0 S l r) x) d

end QuotientPullbackData

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

/-- For a constant Hilbert polynomial on relative projective zero-space, the
determinant of every twisted pushforward of the universal quotient is relatively very
ample.  The statement allows an arbitrary raw representative of the universal Quot
class, so in particular it applies to the representative selected by `Quotient.out`. -/
theorem isRelativelyVeryAmple_exteriorPower_zero_universalPushforward_C
    (S : Scheme.{u}) (l : ℤ) (r q : ℕ) (Q : Over S)
    (h : (quotFunctorP (projectiveSpaceOverTwistedFree 0 S l r)
      (Polynomial.C (q : ℚ))).RepresentableBy Q)
    (a : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := 0) (r := r) (l := l))
      (projectiveSpaceOverπ 0 S) Q)
    (ha : Quotient.mk _ a = (h.homEquiv (𝟙 Q)).1) (d : ℤ) :
    IsRelativelyVeryAmple Q.hom
      (Modules.exteriorPower
        ((Modules.pushforward (projectiveSpaceOverπ 0 Q.left)).obj
          (projectiveSpaceOverTwistModule
            (quotDataOnProjectiveSpace
              (Modules.QuotientPullbackData.twistedFreeAmbient
                (n := 0) (r := r) (l := l)) a) d)) q) := by
  let V : S.Modules :=
    SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin r))
  let z := h.homEquiv (𝟙 Q)
  let b := TwistedFreeQuotGrassmannianNatTransData.representative z
  have hbP : b.HasFiberwiseHilbertPolynomial (Polynomial.C (q : ℚ)) :=
    TwistedFreeQuotGrassmannianNatTransData.representative_hasFiberwiseHilbertPolynomial z
  have hba : (Modules.QuotientPullbackData.setoid
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := 0) (r := r) (l := l))
      (projectiveSpaceOverπ 0 S) Q).r b a := by
    apply Quotient.exact
    exact (TwistedFreeQuotGrassmannianNatTransData.representative_mk z).trans ha.symm
  obtain ⟨eba, heba⟩ := hba
  let y₀ : Modules.PullbackQuotient q V Q :=
    Modules.PullbackQuotient.ofQuotientPullbackDataZero (l := l) b hbP
  let E := Modules.zeroQuotPGrassmannianIso S l r q
  let y : Modules.PullbackQuotient q V Q := (E.hom.app (op Q) z).out
  have hy : Quotient.mk (Modules.PullbackQuotient.setoid q V Q) y =
      E.hom.app (op Q) z := Quotient.out_eq _
  have hy₀ : Quotient.mk (Modules.PullbackQuotient.setoid q V Q) y₀ =
      E.hom.app (op Q) z := by
    apply (Modules.zeroGrassmannianToQuotP_app_bijective
      (S := S) (l := l) (r := r) (q := q) (op Q)).1
    have hleft :
        (Modules.zeroGrassmannianToQuotP S l r q).app (op Q)
          (E.hom.app (op Q) z) = z := by
      change E.inv.app (op Q) (E.hom.app (op Q) z) = z
      simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply,
        CategoryTheory.id_apply] using
        ConcreteCategory.congr_hom (E.hom_inv_id_app (op Q)) z
    rw [hleft]
    apply Subtype.ext
    change Quotient.mk _
        (y₀.toQuotientPullbackDataZero (l := l)) = z.1
    rw [← TwistedFreeQuotGrassmannianNatTransData.representative_mk z]
    exact Quotient.sound
      (Modules.PullbackQuotient.toQuotientPullbackDataZero_ofQuotientPullbackDataZero b hbP)
  have hyy₀ : (Modules.PullbackQuotient.setoid q V Q).r y y₀ :=
    Quotient.exact (hy.trans hy₀.symm)
  obtain ⟨ey, -⟩ := hyy₀
  let ecomp : y₀.Q ≅ b.zeroNormalizedSheaf := by
    change (Modules.pullback
        ((projectiveSpaceOverZeroIso Q.left).inv ≫
          (projectiveSpaceOverBaseChangeIso 0 Q.hom).inv)).obj b.Q ≅
      (Modules.pullback (projectiveSpaceOverZeroIso Q.left).inv).obj
        ((Modules.pullback
          (projectiveSpaceOverBaseChangeIso 0 Q.hom).inv).obj b.Q)
    exact (Modules.pullbackComp
      (projectiveSpaceOverZeroIso Q.left).inv
      (projectiveSpaceOverBaseChangeIso 0 Q.hom).inv).symm.app b.Q
  let M : Q.left.Modules :=
    (Modules.pushforward (projectiveSpaceOverπ 0 Q.left)).obj
      (projectiveSpaceOverTwistModule
        (quotDataOnProjectiveSpace
          (Modules.QuotientPullbackData.twistedFreeAmbient
            (n := 0) (r := r) (l := l)) a) d)
  letI : M.IsQuasicoherent := by
    exact (SheafOfModules.isQuasicoherent Q.left.ringCatSheaf).prop_of_iso
      (a.zeroTwistPushforwardIsoNormalized d).symm
        a.zeroNormalizedSheaf_isQuasicoherent
  let ebaM :
      (Modules.pushforward (projectiveSpaceOverπ 0 Q.left)).obj
          (projectiveSpaceOverTwistModule
            (quotDataOnProjectiveSpace
              (Modules.QuotientPullbackData.twistedFreeAmbient
                (n := 0) (r := r) (l := l)) b) d) ≅ M := by
    dsimp only [M]
    exact (Modules.pushforward (projectiveSpaceOverπ 0 Q.left)).mapIso
      (Modules.tensorLeftIso
        (Modules.QuotientPullbackData.quotDataOnProjectiveSpaceIsoOfIsoOver Q eba)
        (projectiveSpaceOverTwist 0 Q.left d))
  let eM : y.Q ≅ M := ey ≪≫ ecomp ≪≫
    (b.zeroTwistPushforwardIsoNormalized d).symm ≪≫
    ebaM
  exact isRelativelyVeryAmple_exteriorPower_of_relativeGrassmannianImmersion_of_point
    V (Modules.free_isProjectiveOfRank S r) E.hom
      (relative_over_isImmersion_of_isIso E.hom) h
      (freeGrassmannianRepresentableBy S q r) y hy M eM

/-- On relative projective zero-space, the determinant of the universal quotient's
twisted pushforward is relatively very ample in every degree.  A nonempty representative
forces the Hilbert polynomial to be a natural-valued constant and the result is the
Plucker theorem under the Quot--Grassmannian isomorphism; for an empty representative it
is vacuous.  Thus this endpoint needs none of the eventual regularity, kernel-generation,
or flattening inputs used in positive relative dimension. -/
theorem exists_eventually_isRelativelyVeryAmple_universalQuot_int_zero
    (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (Q : Over S)
    (h : (quotFunctorP (projectiveSpaceOverTwistedFree 0 S l r) P).RepresentableBy Q) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ N : ℕ, (N : ℚ) = P.eval (d : ℚ) →
      IsRelativelyVeryAmple Q.hom
        (Modules.exteriorPower
          ((Modules.pushforward (projectiveSpaceOverπ 0 Q.left)).obj
            (projectiveSpaceOverTwistModule
              (quotDataOnProjectiveSpace
                (Modules.QuotientPullbackData.twistedFreeAmbient
                  (n := 0) (r := r) (l := l))
                (h.homEquiv (𝟙 Q)).1.out) d)) N) := by
  by_cases hQ : Nonempty Q.left
  · letI : Nonempty Q.left := hQ
    let z := h.homEquiv (𝟙 Q)
    obtain ⟨q, hP⟩ := quotFunctorP_zero_polynomial_eq_C_of_nonempty
      (projectiveSpaceOverTwistedFree 0 S l r) P Q z
    subst P
    refine ⟨0, fun d _ N hN ↦ ?_⟩
    have hNq : N = q := by
      have hNq' : (N : ℚ) = (q : ℚ) := by simpa using hN
      exact_mod_cast hNq'
    subst N
    exact isRelativelyVeryAmple_exteriorPower_zero_universalPushforward_C
      S l r q Q h (h.homEquiv (𝟙 Q)).1.out (Quotient.out_eq _) d
  · letI : IsEmpty Q.left := not_nonempty_iff.mp hQ
    exact ⟨0, fun _ _ _ _ ↦ isRelativelyVeryAmple_of_isEmpty Q.hom _⟩

end AlgebraicGeometry.Scheme

end
