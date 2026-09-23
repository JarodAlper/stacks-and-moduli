module

public import StacksAndModuli.API.TwistedFreeQuotGrassmannianNatTrans
public import StacksAndModuli.API.RepresentedGrassmannianVeryAmple

/-!
# The determinant attached to the Quot-to-Grassmannian transformation

This file relates the strict finite-free quotient used by the intrinsic
Quot-to-Grassmannian natural transformation to the universal quotient of the relative
free Grassmannian.  It is the choice-independent bridge needed to identify the Plücker
line bundle with the determinant of the fixed-degree pushforward.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

namespace TwistedFreeQuotGrassmannianQuotientNatTransData

variable {n : ℕ} {S : Scheme.{u}} {l : ℤ} {r : ℕ} {P : Polynomial ℚ}
  {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)} {m q : ℕ}
  {σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n)}

/-- The intrinsic Quot-to-absolute-Grassmannian transformation, transported through the
canonical equivalence to the relative Grassmannian of the free sheaf. -/
noncomputable def relativeNatTrans
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ) :
    quotFunctorP
        (Modules.QuotientPullbackData.twistedFreeAmbient
          (n := n) (r := r) (l := l)) P ⟶
      Modules.grassmannianOverFunctor q
        (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin m))) :=
  D.natTrans ≫
    (Modules.freeGrassmannianIsoGrassmannianFunctorOver
      (S := S) (n := m) q).inv

/-- The strict pushforward quotient, regarded as a relative quotient of the free sheaf on
the base. -/
noncomputable def relativeRepresentative
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ)
    {T : (Over S)ᵒᵖ}
    (x : (quotFunctorP
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l)) P).obj T) :
    Modules.PullbackQuotient q
      (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin m))) (unop T) :=
  Modules.PullbackQuotient.ofFreeQuotient (D.representativeFreeQuotient x)

/-- The concrete strict pushforward quotient represents the relative-Grassmannian image
of the given Quot point. -/
lemma relativeRepresentative_mk
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ)
    {T : (Over S)ᵒᵖ}
    (x : (quotFunctorP
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l)) P).obj T) :
    Quotient.mk (Modules.PullbackQuotient.setoid q
      (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin m))) (unop T))
        (D.relativeRepresentative x) =
      D.relativeNatTrans.app T x := by
  change Quotient.mk (Modules.PullbackQuotient.setoid q
      (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin m))) (unop T))
        (Modules.PullbackQuotient.ofFreeQuotient
          (D.representativeFreeQuotient x)) =
      (Modules.freeGrassmannianEquiv q (unop T)).symm
        (D.representativeFreeQuotient x).kernelPoint
  apply (Modules.freeGrassmannianEquiv q (unop T)).injective
  rw [Equiv.apply_symm_apply]
  apply Modules.FreeQuotient.kernelPoint_eq_of_r
  exact ⟨Iso.refl _, by simp [Modules.PullbackQuotient.toFreeQuotient,
    Modules.PullbackQuotient.ofFreeQuotient]⟩

/-- Replacing the raw representative selected by the natural transformation with any
equivalent Quot presentation induces the expected isomorphism of fixed-degree
pushforwards. -/
noncomputable def relativeRepresentativeIsoOfMkEq
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ)
    {T : (Over S)ᵒᵖ}
    (x : (quotFunctorP
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l)) P).obj T)
    (a : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) (unop T))
    (ha : Quotient.mk _ a = x.1) :
    (D.relativeRepresentative x).Q ≅
      twistedFreeQuotientTwistPushforward n S l r a d := by
  have hr : (Modules.QuotientPullbackData.setoid
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) (unop T)).r
      (TwistedFreeQuotGrassmannianNatTransData.representative x) a :=
    Quotient.exact
      ((TwistedFreeQuotGrassmannianNatTransData.representative_mk x).trans ha.symm)
  exact twistedFreeQuotientTwistPushforwardIsoOfIso n S l r
    (Classical.choose hr) d

/-- Relative-immersion form of the intrinsic transformation. -/
theorem relativeNatTrans_isImmersion
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ)
    (hD : MorphismProperty.relative uliftYoneda.{u + 1}
      (MorphismProperty.over (@IsImmersion : MorphismProperty Scheme.{u}))
      D.natTrans) :
    MorphismProperty.relative uliftYoneda.{u + 1}
      (MorphismProperty.over (@IsImmersion : MorphismProperty Scheme.{u}))
      D.relativeNatTrans :=
  relative_over_isImmersion_comp_iso_inv D.natTrans
    (Modules.freeGrassmannianIsoGrassmannianFunctorOver
      (S := S) (n := m) q) hD

/-- A relatively representable intrinsic Quot-to-Grassmannian transformation makes the
determinant of the normalized fixed-degree universal pushforward relatively very ample on
any chosen representative of the Quot functor. -/
theorem isRelativelyVeryAmple_exteriorPower_twistedFreeUniversalPushforward
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ)
    (hD : MorphismProperty.relative uliftYoneda.{u + 1}
      (MorphismProperty.over (@IsImmersion : MorphismProperty Scheme.{u}))
      D.natTrans)
    {Q : Over S}
    (h : (quotFunctorP
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l)) P).RepresentableBy Q) :
    IsRelativelyVeryAmple Q.hom
      (Modules.exteriorPower
        (twistedFreeQuotientTwistPushforward n S l r
          (h.homEquiv (𝟙 Q)).1.out d) q) := by
  let V : S.Modules :=
    SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin m))
  let z := h.homEquiv (𝟙 Q)
  let a : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) Q := z.1.out
  letI : (twistedFreeQuotientTwistPushforward n S l r a d).IsQuasicoherent :=
    twistedFreeQuotientTwistPushforward_isQuasicoherent n S l r a d
  let y : Modules.PullbackQuotient q V Q := D.relativeRepresentative z
  have hy : Quotient.mk (Modules.PullbackQuotient.setoid q V Q) y =
      D.relativeNatTrans.app (op Q) z := D.relativeRepresentative_mk z
  have ha : Quotient.mk _ a = z.1 := Quotient.out_eq _
  let ε : y.Q ≅ twistedFreeQuotientTwistPushforward n S l r a d :=
    D.relativeRepresentativeIsoOfMkEq z a ha
  exact isRelativelyVeryAmple_exteriorPower_of_relativeGrassmannianImmersion_of_point
    V (Modules.free_isProjectiveOfRank S m) D.relativeNatTrans
      (D.relativeNatTrans_isImmersion hD) h
      (freeGrassmannianRepresentableBy S q m) y hy _ ε

end TwistedFreeQuotGrassmannianQuotientNatTransData

end AlgebraicGeometry.Scheme

end

end
