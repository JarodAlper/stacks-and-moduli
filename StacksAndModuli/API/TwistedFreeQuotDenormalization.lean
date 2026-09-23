module

public import StacksAndModuli.API.TwistedFreeQuotGrassmannianNatTrans

/-!
# Denormalizing twisted-free Quot presentations

A raw point of the Quot functor over `T ⟶ S` is stored on the chosen fibre product
`T ×_S P^n_S`, whereas the Grassmannian reconstruction and projective flattening loci
naturally produce a quotient on the standard model `P^n_T`.  The canonical base-change
isomorphism identifies these schemes.  This file transports a quotient on `P^n_T` back to
an actual `QuotientPullbackData`, and records that normalizing it again recovers the given
quotient sheaf.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Modules.QuotientPullbackData

variable {n r : ℕ} {l : ℤ} {S : Scheme.{u}}

/-- The source comparison used when a raw twisted-free Quot presentation is normalized
onto `P^n_T`. -/
noncomputable def twistedFreeQuotientToProjectiveSpaceAmbientIso
    (T : Over S) :
    (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T.left (-l)) ≅
      (Modules.pullback (projectiveSpaceOverBaseChangeIso n T.hom).inv).obj
        ((Modules.pullback
          ((Over.pullback (projectiveSpaceOverπ n S)).obj T).hom).obj
            (twistedFreeAmbient (n := n) (r := r) (l := l))) :=
  (projectiveSpaceOverTwistedFree_pullbackIso n r l T.hom).symm ≪≫
    twistedFreeQuotientOnProjectiveSpaceAmbientIsoOver T

/-- The source comparison used to transport a normalized twisted-free quotient on
`P^n_T` back to the chosen fibre-product model `T ×_S P^n_S`. -/
noncomputable def twistedFreeQuotientFromProjectiveSpaceAmbientIso
    (T : Over S) :
    (Modules.pullback
      ((Over.pullback (projectiveSpaceOverπ n S)).obj T).hom).obj
        (twistedFreeAmbient (n := n) (r := r) (l := l)) ≅
      (Modules.pullback (projectiveSpaceOverBaseChangeIso n T.hom).hom).obj
        (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T.left (-l)) :=
  (Modules.pullbackInverseUnit
      (projectiveSpaceOverBaseChangeIso n T.hom).hom_inv_id).app
        ((Modules.pullback
          ((Over.pullback (projectiveSpaceOverπ n S)).obj T).hom).obj
            (twistedFreeAmbient (n := n) (r := r) (l := l))) ≪≫
    (Modules.pullback (projectiveSpaceOverBaseChangeIso n T.hom).hom).mapIso
      (twistedFreeQuotientToProjectiveSpaceAmbientIso
        (n := n) (r := r) (l := l) T).symm

/-- A quasicoherent finitely presented quotient on the standard relative projective
space `P^n_T`, flat over `T`, determines an actual raw point of the twisted-free Quot
functor over `T`. -/
noncomputable def ofTwistedFreeQuotientOnProjectiveSpace
    (T : Over S)
    (Q : (projectiveSpaceOver n T.left).Modules) [Q.IsQuasicoherent]
    (hQfp : Q.IsFinitePresentation)
    (hQflat : Q.FlatOver (projectiveSpaceOverπ n T.left))
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T.left (-l)) ⟶ Q) [Epi p] :
    QuotientPullbackData
      (twistedFreeAmbient (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T where
  Q := (Modules.pullback
    (projectiveSpaceOverBaseChangeIso n T.hom).hom).obj Q
  isQuasicoherent := inferInstance
  isFinitePresentation :=
    Modules.isFinitePresentation_pullback_of_isFinitePresentation _ hQfp
  flatOver :=
    FlatOver.pullback_isIso
      (projectiveSpaceOverBaseChangeIso n T.hom).hom Q
      (projectiveSpaceOverBaseChangeIso_hom_π n T.hom) hQflat
  π := (twistedFreeQuotientFromProjectiveSpaceAmbientIso
      (n := n) (r := r) (l := l) T).hom ≫
    (Modules.pullback
      (projectiveSpaceOverBaseChangeIso n T.hom).hom).map p
  epi := by infer_instance

/-- Normalizing a quotient constructed from `P^n_T` recovers its original quotient
sheaf. -/
noncomputable def ofTwistedFreeQuotientOnProjectiveSpace_quotDataIso
    (T : Over S)
    (Q : (projectiveSpaceOver n T.left).Modules) [Q.IsQuasicoherent]
    (hQfp : Q.IsFinitePresentation)
    (hQflat : Q.FlatOver (projectiveSpaceOverπ n T.left))
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T.left (-l)) ⟶ Q) [Epi p] :
    quotDataOnProjectiveSpace
        (twistedFreeAmbient (n := n) (r := r) (l := l))
        (ofTwistedFreeQuotientOnProjectiveSpace
          (n := n) (r := r) (l := l) T Q hQfp hQflat p) ≅ Q :=
  (Modules.pullbackInverseCounit
    (projectiveSpaceOverBaseChangeIso n T.hom).inv_hom_id).app Q

/-- A fixed fibrewise Hilbert polynomial on the normalized quotient is preserved by
denormalization. -/
theorem ofTwistedFreeQuotientOnProjectiveSpace_hasFiberwiseHilbertPolynomial
    (T : Over S)
    (Q : (projectiveSpaceOver n T.left).Modules) [Q.IsQuasicoherent]
    (hQfp : Q.IsFinitePresentation)
    (hQflat : Q.FlatOver (projectiveSpaceOverπ n T.left))
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T.left (-l)) ⟶ Q) [Epi p]
    (P : Polynomial ℚ) (hQP : Scheme.HasFiberwiseHilbertPolynomial Q P) :
    (ofTwistedFreeQuotientOnProjectiveSpace
      (n := n) (r := r) (l := l) T Q hQfp hQflat p
      ).HasFiberwiseHilbertPolynomial P := by
  exact Scheme.HasFiberwiseHilbertPolynomial.of_iso
    (ofTwistedFreeQuotientOnProjectiveSpace_quotDataIso
      (n := n) (r := r) (l := l) T Q hQfp hQflat p).symm hQP

/-- The point of the fixed-polynomial twisted-free Quot functor defined by a normalized
quotient on `P^n_T`. -/
noncomputable def quotFunctorPPointOfTwistedFreeQuotientOnProjectiveSpace
    (T : Over S)
    (Q : (projectiveSpaceOver n T.left).Modules) [Q.IsQuasicoherent]
    (hQfp : Q.IsFinitePresentation)
    (hQflat : Q.FlatOver (projectiveSpaceOverπ n T.left))
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T.left (-l)) ⟶ Q) [Epi p]
    (P : Polynomial ℚ) (hQP : Scheme.HasFiberwiseHilbertPolynomial Q P) :
    (quotFunctorP
      (twistedFreeAmbient (n := n) (r := r) (l := l)) P).obj (op T) :=
  let a := ofTwistedFreeQuotientOnProjectiveSpace
    (n := n) (r := r) (l := l) T Q hQfp hQflat p
  ⟨Quotient.mk _ a, a, rfl,
    ofTwistedFreeQuotientOnProjectiveSpace_hasFiberwiseHilbertPolynomial
      T Q hQfp hQflat p P hQP⟩

/-- The normalized quotient map of the denormalized presentation is the original map on
`P^n_T`. -/
lemma twistedFreeQuotientOnProjectiveSpaceOver_ofTwistedFreeQuotient_comp_quotDataIso
    (T : Over S)
    (Q : (projectiveSpaceOver n T.left).Modules) [Q.IsQuasicoherent]
    (hQfp : Q.IsFinitePresentation)
    (hQflat : Q.FlatOver (projectiveSpaceOverπ n T.left))
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T.left (-l)) ⟶ Q) [Epi p] :
    twistedFreeQuotientOnProjectiveSpaceOver T
        (ofTwistedFreeQuotientOnProjectiveSpace
          (n := n) (r := r) (l := l) T Q hQfp hQflat p) ≫
      (ofTwistedFreeQuotientOnProjectiveSpace_quotDataIso
        (n := n) (r := r) (l := l) T Q hQfp hQflat p).hom = p := by
  let E := projectiveSpaceOverBaseChangeIso n T.hom
  let A := (Modules.pullback
    ((Over.pullback (projectiveSpaceOverπ n S)).obj T).hom).obj
      (twistedFreeAmbient (n := n) (r := r) (l := l))
  let B := ∐ fun _ : ULift.{u} (Fin r) ↦
    projectiveSpaceOverTwist n T.left (-l)
  let ν : B ≅ (Modules.pullback E.inv).obj A :=
    twistedFreeQuotientToProjectiveSpaceAmbientIso
      (n := n) (r := r) (l := l) T
  let η := Modules.pullbackInverseUnit E.hom_inv_id
  let ε := Modules.pullbackInverseCounit E.inv_hom_id
  have hεp := ε.hom.naturality p
  have hεν := ε.hom.naturality ν.inv
  have hεp' :
      (Modules.pullback E.inv).map ((Modules.pullback E.hom).map p) ≫
          ε.hom.app Q = ε.hom.app B ≫ p := by
    simpa using hεp
  have hεν' :
      (Modules.pullback E.inv).map ((Modules.pullback E.hom).map ν.inv) ≫
          ε.hom.app B = ε.hom.app ((Modules.pullback E.inv).obj A) ≫ ν.inv := by
    simpa using hεν
  have htri := Modules.pullbackInverse_triangle
    E.hom_inv_id E.inv_hom_id A
  change ν.hom ≫
      (Modules.pullback E.inv).map
        (η.hom.app A ≫ (Modules.pullback E.hom).map ν.inv ≫
          (Modules.pullback E.hom).map p) ≫
        ε.hom.app Q = p
  rw [Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [hεp']
  slice_lhs 3 4 => rw [hεν']
  slice_lhs 2 3 => rw [htri]
  simp

end Modules.QuotientPullbackData

end AlgebraicGeometry.Scheme

end

end
