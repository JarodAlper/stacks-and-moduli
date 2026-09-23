module

public import StacksAndModuli.API.ProjectiveGammaStarMultiplicationComparison
public import StacksAndModuli.API.ProjectiveTwistHomogeneousSection
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianAmbientCoherence
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianNextDegree

/-!
# The reconstructed generated next-degree presentation

For a finite-free quotient in degree `d`, with kernel `K`, the algebraic
next-degree module is the cokernel of the finite relation obtained by multiplying
`K` by every projective variable.  This file compares that finite monomial
presentation with the same generated relation inside
`pi_*((O(-l)^r)(d+1))`.

The comparison is valid over an arbitrary base scheme.  It uses the canonical
monomial-basis isomorphism for the twisted-free ambient module, not cohomology and
base change for the reconstructed quotient.

This is deliberately the quotient by the generated relations `S_1 K`.  It is not
an unconditional identification with the generally larger quotient by all global
sections of the sheaf kernel in degree `d+1`; such an identification needs an
additional saturation or global-generation input.

Main declarations:

* `AlgebraicGeometry.Scheme.reconstructedGeneratedNextDegreeRelation`;
* `AlgebraicGeometry.Scheme.twistedFreeNextDegreeRelation_comp_monomialPushforwardMap`;
* `AlgebraicGeometry.Scheme.twistedFreeNextDegreeModuleIsoReconstructedGenerated`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Multiplying a relative monomial section by a degree-one basis monomial gives
the monomial section selected by `twistedFreeNextMonomialIndex`. -/
lemma twistMonomialSection_mul_degreeOne
    (n : ℕ) (T : Scheme.{u}) (e : ℕ)
    (j : Fin (n + 1)) (i : Fin ((n + e).choose n)) :
    Modules.Hom.app
        (twistMonomialMulHom n T (e : ℤ) ((e + 1 : ℕ) : ℤ) 1
          (by omega) (twistedFreeDegreeOneMonomialIndex n j)) ⊤
        (twistMonomialSection n T e i) =
      twistMonomialSection n T (e + 1)
        (twistedFreeNextMonomialIndex n e j i) := by
  let A := MvPolynomial.homogeneousSubmodule
    (Fin (n + 1)) (ULift.{u} ℤ)
  let h := Limits.pullback.snd
    (specULiftZIsTerminal.from T)
    (specULiftZIsTerminal.from (projectiveSpace n))
  let p := MvPolynomial.homogeneousSubmoduleFinBasis
    n (ULift.{u} ℤ) e i
  let q := MvPolynomial.homogeneousSubmoduleFinBasis
    n (ULift.{u} ℤ) 1 (twistedFreeDegreeOneMonomialIndex n j)
  let pnext := MvPolynomial.homogeneousSubmoduleFinBasis
    n (ULift.{u} ℤ) (e + 1) (twistedFreeNextMonomialIndex n e j i)
  have hpull := Scheme.Modules.pullbackGlobalSections_naturality h
    (ProjectiveSpectrum.Twist.mulHom A q (e : ℤ)
      ((e + 1 : ℕ) : ℤ) (by omega))
    (MvPolynomial.projectiveTwistGlobalSectionsBasis n (ULift.{u} ℤ) e i)
  change ((Modules.pullback h).map
      (ProjectiveSpectrum.Twist.mulHom A q (e : ℤ)
        ((e + 1 : ℕ) : ℤ) (by omega))).app ⊤
      (Scheme.Modules.pullbackGlobalSections h
        (ProjectiveSpectrum.Twist.twist A (e : ℤ))
        (MvPolynomial.projectiveTwistGlobalSectionsBasis
          n (ULift.{u} ℤ) e i)) =
    Scheme.Modules.pullbackGlobalSections h
      (ProjectiveSpectrum.Twist.twist A ((e + 1 : ℕ) : ℤ))
      (MvPolynomial.projectiveTwistGlobalSectionsBasis
        n (ULift.{u} ℤ) (e + 1)
          (twistedFreeNextMonomialIndex n e j i))
  rw [hpull]
  congr 1
  have hbasis :
      MvPolynomial.projectiveTwistGlobalSectionsBasis
          n (ULift.{u} ℤ) e i =
        ProjectiveSpectrum.Twist.homogeneousSection A p ⊤ := by
    change MvPolynomial.homogeneousSubmoduleGlobalSectionsLinearEquiv
        n (ULift.{u} ℤ) e p = _
    rfl
  rw [hbasis]
  change ProjectiveSpectrum.Twist.mulSectionHom A q
      (e : ℤ) ((e + 1 : ℕ) : ℤ) (by omega) (op ⊤)
      (ProjectiveSpectrum.Twist.homogeneousSection A p ⊤) = _
  rw [show ProjectiveSpectrum.Twist.homogeneousSection A p ⊤ =
      ProjectiveSpectrum.Twist.homogeneousSection' A p (e : ℤ) rfl ⊤ from rfl]
  rw [ProjectiveSpectrum.Twist.mulSectionHom_homogeneousSection']
  all_goals try omega
  have hpq :
      (⟨(p : MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ)) * q,
        SetLike.mul_mem_graded p.2 q.2⟩ : A (e + 1)) = pnext := by
    apply Subtype.ext
    exact twistedFreeMonomialBasis_mul_degreeOne n (ULift.{u} ℤ) e j i
  rw [hpq]
  change ProjectiveSpectrum.Twist.homogeneousSection A pnext ⊤ = _
  rfl

/-- Degree-one multiplication carries a monomial section in the chosen summand
of `O(-l)^r(d)` to the corresponding next monomial section in `O(-l)^r(d+1)`. -/
lemma twistedFreeMonomialSection_mul_degreeOne_generated
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ))
    (a : Fin (n + 1)) (j : ULift.{u} (Fin r))
    (i : Fin ((n + e).choose n)) :
    Modules.Hom.app
        (Modules.projectiveTwistMulOne n
          (∐ fun _ : ULift.{u} (Fin r) ↦
            projectiveSpaceOverTwist n T (-l)) d
          (twistedFreeDegreeOneMonomialIndex n a)) ⊤
        (twistedFreeMonomialSection n T l r d e he j i) =
      twistedFreeMonomialSection n T l r (d + 1) (e + 1)
        (by omega) j (twistedFreeNextMonomialIndex n e a i) := by
  rw [twistedFreeMonomialSection_eq_summand,
    twistedFreeMonomialSection_eq_summand]
  let F := ∐ fun _ : ULift.{u} (Fin r) ↦
    projectiveSpaceOverTwist n T (-l)
  let L := projectiveSpaceOverTwist n T (-l)
  let Od := projectiveSpaceOverTwist n T (d : ℤ)
  let Od1 := projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ)
  let k := twistedFreeDegreeOneMonomialIndex n a
  let m := twistMonomialMulHom n T (d : ℤ) ((d + 1 : ℕ) : ℤ)
    1 (by omega) k
  let inc := Sigma.ι
    (fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) j
  let addD := projectiveSpaceOverTwist_addIso_nat n T (-l) d
  let addD1 := projectiveSpaceOverTwist_addIso_nat n T (-l) (d + 1)
  have hexchange := Modules.tensorMap_exchange inc m
  change Modules.tensorMapRight L m ≫ Modules.tensorMapLeft inc Od1 =
      Modules.tensorMapLeft inc Od ≫ Modules.tensorMapRight F m at hexchange
  change Modules.Hom.app
      (Modules.tensorMapLeft inc Od ≫ Modules.tensorMapRight F m) ⊤ _ =
    Modules.Hom.app (Modules.tensorMapLeft inc Od1) ⊤ _
  rw [← hexchange]
  apply congrArg (fun z ↦ Modules.Hom.app
    (Modules.tensorMapLeft inc Od1) ⊤ z)
  let mout := twistMonomialMulHom n T (-l + (d : ℤ))
    (-l + ((d + 1 : ℕ) : ℤ)) 1 (by omega) k
  have hadd := tensorMapRight_twistMonomialMulHom_comp_addIso_nat
    n T (-l) d (d + 1) 1 (by omega) k
  change Modules.tensorMapRight L m ≫ addD1.hom = addD.hom ≫ mout at hadd
  have haddInv : addD.inv ≫ Modules.tensorMapRight L m = mout ≫ addD1.inv := by
    apply (cancel_mono addD1.hom).1
    calc
      (addD.inv ≫ Modules.tensorMapRight L m) ≫ addD1.hom =
          addD.inv ≫ (Modules.tensorMapRight L m ≫ addD1.hom) :=
        Category.assoc _ _ _
      _ = addD.inv ≫ (addD.hom ≫ mout) :=
        congrArg (fun z ↦ addD.inv ≫ z) hadd
      _ = mout := by simp
      _ = mout ≫ (addD1.inv ≫ addD1.hom) := by simp
      _ = (mout ≫ addD1.inv) ≫ addD1.hom :=
        (Category.assoc _ _ _).symm
  change Modules.Hom.app
      (addD.inv ≫ Modules.tensorMapRight L m) ⊤ _ =
    Modules.Hom.app addD1.inv ⊤ _
  rw [haddInv]
  apply congrArg (fun z ↦ Modules.Hom.app addD1.inv ⊤ z)
  let cIn : projectiveSpaceOverTwist n T (e : ℤ) ⟶
      projectiveSpaceOverTwist n T (-l + (d : ℤ)) :=
    eqToHom (congrArg (projectiveSpaceOverTwist n T) (by omega))
  let cOut : projectiveSpaceOverTwist n T ((e + 1 : ℕ) : ℤ) ⟶
      projectiveSpaceOverTwist n T (-l + ((d + 1 : ℕ) : ℤ)) :=
    eqToHom (congrArg (projectiveSpaceOverTwist n T) (by omega))
  let me := twistMonomialMulHom n T (e : ℤ) ((e + 1 : ℕ) : ℤ)
    1 (by omega) k
  have hin := eqToHom_comp_twistMonomialMulHom n T
    (e : ℤ) (-l + (d : ℤ)) (-l + ((d + 1 : ℕ) : ℤ)) 1
    (by omega) (by omega) (by omega) k
  have hout := twistMonomialMulHom_comp_eqToHom n T
    (e : ℤ) ((e + 1 : ℕ) : ℤ) (-l + ((d + 1 : ℕ) : ℤ)) 1
    (by omega) (by omega) k
  have hcasts : cIn ≫ mout = me ≫ cOut := by
    exact hin.trans hout.symm
  let cHe : projectiveSpaceOverTwist n T (e : ℤ) ⟶
      projectiveSpaceOverTwist n T ((d : ℤ) - l) :=
    eqToHom (congrArg (projectiveSpaceOverTwist n T) he.symm)
  let cD : projectiveSpaceOverTwist n T ((d : ℤ) - l) ⟶
      projectiveSpaceOverTwist n T (-l + (d : ℤ)) :=
    eqToHom (congrArg (projectiveSpaceOverTwist n T)
      (neg_add_eq_sub l (d : ℤ)).symm)
  have he1 : ((d + 1 : ℕ) : ℤ) - l = ((e + 1 : ℕ) : ℤ) := by omega
  let cHe1 : projectiveSpaceOverTwist n T ((e + 1 : ℕ) : ℤ) ⟶
      projectiveSpaceOverTwist n T (((d + 1 : ℕ) : ℤ) - l) :=
    eqToHom (congrArg (projectiveSpaceOverTwist n T) he1.symm)
  let cD1 : projectiveSpaceOverTwist n T (((d + 1 : ℕ) : ℤ) - l) ⟶
      projectiveSpaceOverTwist n T (-l + ((d + 1 : ℕ) : ℤ)) :=
    eqToHom (congrArg (projectiveSpaceOverTwist n T)
      (neg_add_eq_sub l ((d + 1 : ℕ) : ℤ)).symm)
  have hHe : (he ▸ twistMonomialSection n T e i) =
      Modules.Hom.app cHe ⊤ (twistMonomialSection n T e i) := by
    symm
    exact Modules.hom_app_eqToHom
      (fun z : ℤ ↦ projectiveSpaceOverTwist n T z) he.symm _
  have hHe1 : (he1 ▸ twistMonomialSection n T (e + 1)
        (twistedFreeNextMonomialIndex n e a i)) =
      Modules.Hom.app cHe1 ⊤
        (twistMonomialSection n T (e + 1)
          (twistedFreeNextMonomialIndex n e a i)) := by
    symm
    exact Modules.hom_app_eqToHom
      (fun z : ℤ ↦ projectiveSpaceOverTwist n T z) he1.symm _
  rw [hHe, hHe1]
  change Modules.Hom.app mout ⊤
      (Modules.Hom.app (cHe ≫ cD) ⊤
        (twistMonomialSection n T e i)) =
    Modules.Hom.app (cHe1 ≫ cD1) ⊤
      (twistMonomialSection n T (e + 1)
        (twistedFreeNextMonomialIndex n e a i))
  have hcIn : cHe ≫ cD = cIn := by
    dsimp only [cHe, cD, cIn]
    simp only [eqToHom_trans]
  have hcOut : cHe1 ≫ cD1 = cOut := by
    dsimp only [cHe1, cD1, cOut]
    simp only [eqToHom_trans]
  rw [hcIn, hcOut]
  change Modules.Hom.app (cIn ≫ mout) ⊤
      (twistMonomialSection n T e i) = _
  rw [hcasts]
  change Modules.Hom.app cOut ⊤
      (Modules.Hom.app me ⊤ (twistMonomialSection n T e i)) = _
  exact congrArg (fun z ↦ Modules.Hom.app cOut ⊤ z)
    (twistMonomialSection_mul_degreeOne n T e a i)

/-- The ambient monomial-basis map intertwines multiplication by a variable
with the corresponding finite reindexing of monomials. -/
lemma twistedFreeMonomialPushforwardMap_mul_degreeOne
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) (a : Fin (n + 1)) :
    SheafOfModules.freeMap (R := T.ringCatSheaf)
          (fun x : ULift.{u} (Fin r) × Fin ((n + e).choose n) ↦
            (x.1, twistedFreeNextMonomialIndex n e a x.2)) ≫
        twistedFreeMonomialPushforwardMap n T l r (d + 1) (e + 1)
          (by omega) =
      twistedFreeMonomialPushforwardMap n T l r d e he ≫
        (Modules.pushforward (projectiveSpaceOverπ n T)).map
          (Modules.projectiveTwistMulOne n
            (∐ fun _ : ULift.{u} (Fin r) ↦
              projectiveSpaceOverTwist n T (-l)) d
            (twistedFreeDegreeOneMonomialIndex n a)) := by
  dsimp only [twistedFreeMonomialPushforwardMap]
  rw [Modules.freeMap_comp_freeHomOfSections,
    Modules.freeHomOfSections_comp]
  congr 1
  funext x
  exact (twistedFreeMonomialSection_mul_degreeOne_generated
    n T l r d e he a x.1 x.2).symm

/-- The degree-`d+1` ambient relation generated by multiplying the degree-`d`
kernel relation by each projective variable. -/
noncomputable def reconstructedGeneratedNextDegreeRelation
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E) :
    (∐ fun _ : ULift.{u} (Fin (n + 1)) ↦ kernel u) ⟶
      (Modules.pushforward (projectiveSpaceOverπ n T)).obj
        (projectiveSpaceOverTwistModule
          (∐ fun _ : ULift.{u} (Fin r) ↦
            projectiveSpaceOverTwist n T (-l)) ((d + 1 : ℕ) : ℤ)) :=
  Sigma.desc (fun a ↦ kernel.ι u ≫
    twistedFreeMonomialPushforwardMap n T l r d e he ≫
      (Modules.pushforward (projectiveSpaceOverπ n T)).map
        (Modules.projectiveTwistMulOne n
          (∐ fun _ : ULift.{u} (Fin r) ↦
            projectiveSpaceOverTwist n T (-l)) d
          (twistedFreeDegreeOneMonomialIndex n a.down)))

/-- The algebraic next-degree relation, transported through the ambient
monomial-basis isomorphism, is the relation generated geometrically by
degree-one multiplication. -/
lemma twistedFreeNextDegreeRelation_comp_monomialPushforwardMap
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E) :
    twistedFreeNextDegreeRelation n T r e u ≫
        twistedFreeMonomialPushforwardMap n T l r (d + 1) (e + 1)
          (by omega) =
      reconstructedGeneratedNextDegreeRelation n T l r d e he u := by
  apply Sigma.hom_ext
  intro a
  dsimp only [twistedFreeNextDegreeRelation,
    reconstructedGeneratedNextDegreeRelation]
  rw [← Category.assoc, Sigma.ι_desc]
  rw [Sigma.ι_desc]
  simp only [Category.assoc]
  exact congrArg (fun z ↦ kernel.ι u ≫ z)
    (twistedFreeMonomialPushforwardMap_mul_degreeOne
      n T l r d e he a.down)

/-- The degree-`d+1` presentation generated from the reconstructed degree-`d`
kernel relation. -/
noncomputable def reconstructedGeneratedNextDegreeModule
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E) : T.Modules :=
  cokernel (reconstructedGeneratedNextDegreeRelation n T l r d e he u)

/-- The finite algebraic next-degree module is canonically the degree-`d+1`
presentation generated from the reconstructed degree-`d` kernel relation. -/
noncomputable def twistedFreeNextDegreeModuleIsoReconstructedGenerated
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E) :
    twistedFreeNextDegreeModule n T r e u ≅
      reconstructedGeneratedNextDegreeModule n T l r d e he u :=
  cokernel.mapIso
    (twistedFreeNextDegreeRelation n T r e u)
    (reconstructedGeneratedNextDegreeRelation n T l r d e he u)
    (Iso.refl _)
    (asIso (twistedFreeMonomialPushforwardMap
      n T l r (d + 1) (e + 1) (by omega)))
    (by simpa using
      (twistedFreeNextDegreeRelation_comp_monomialPushforwardMap
        n T l r d e he u))

/-- The next-degree comparison intertwines the algebraic and generated
cokernel projections. -/
lemma cokernel_π_comp_twistedFreeNextDegreeModuleIsoReconstructedGenerated_hom
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E) :
    cokernel.π (twistedFreeNextDegreeRelation n T r e u) ≫
        (twistedFreeNextDegreeModuleIsoReconstructedGenerated
          n T l r d e he u).hom =
      twistedFreeMonomialPushforwardMap
          n T l r (d + 1) (e + 1) (by omega) ≫
        cokernel.π
          (reconstructedGeneratedNextDegreeRelation n T l r d e he u) := by
  dsimp only [twistedFreeNextDegreeModuleIsoReconstructedGenerated]
  rw [cokernel.mapIso_hom, cokernel.π_desc]
  simp only [asIso_hom]

end AlgebraicGeometry.Scheme

end

end
