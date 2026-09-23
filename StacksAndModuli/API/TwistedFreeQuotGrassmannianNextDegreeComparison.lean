module

public import StacksAndModuli.API.ProjectiveFlatteningFiniteDegree
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianAmbientCoherence
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianNextDegree

/-!
# Comparing the algebraic and geometric next-degree quotients

The finite algebraic next-degree module attached to a quotient
`u : O_T^(r * binom(n+e,n)) → E` is the cokernel of the relations obtained by
multiplying `ker(u)` by the projective variables.  The reconstructed projective
quotient has a canonical degree-`d+1` twisted pushforward.  This file constructs
the canonical morphism

`twistedFreeNextDegreeModule n T r e u ⟶
  projectiveTwistedPushforward n (reconstructedQuotient' … u) (d+1)`.

The construction does not assert that this morphism is an isomorphism on the whole
Grassmannian.  Such a global assertion is false without additional regularity or
flatness hypotheses.  Instead, the morphism is obtained by showing directly that
the next-degree monomial map kills the algebraic next-degree relation.

Main declarations:

* `AlgebraicGeometry.Scheme.quotGrassmannianFreeMap_mul_degreeOne`;
* `AlgebraicGeometry.Scheme.twistedFreeNextDegreeRelation_comp_reconstructedPushforwardMap`;
* `AlgebraicGeometry.Scheme.twistedFreeNextDegreeModuleToReconstructedPushforward`.
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

/-- Multiplying a relative degree-`e` monomial map by the variable `X_j` is the
relative degree-`e+1` monomial map selected by `twistedFreeNextMonomialIndex`. -/
theorem twistMonomialMulHom_mul_degreeOne
    (n : ℕ) (T : Scheme.{u}) (e : ℕ)
    (j : Fin (n + 1)) (i : Fin ((n + e).choose n)) :
    twistMonomialMulHom n T 0 (e : ℤ) e (by omega) i ≫
        twistMonomialMulHom n T (e : ℤ) ((e + 1 : ℕ) : ℤ) 1
          (by omega) (twistedFreeDegreeOneMonomialIndex n j) =
      twistMonomialMulHom n T 0 ((e + 1 : ℕ) : ℤ) (e + 1)
        (by omega) (twistedFreeNextMonomialIndex n e j i) := by
  let 𝒜 := MvPolynomial.homogeneousSubmodule
    (Fin (n + 1)) (ULift.{u} ℤ)
  let p := MvPolynomial.homogeneousSubmoduleFinBasis n (ULift.{u} ℤ) e i
  let q := MvPolynomial.homogeneousSubmoduleFinBasis n (ULift.{u} ℤ) 1
    (twistedFreeDegreeOneMonomialIndex n j)
  let r := MvPolynomial.homogeneousSubmoduleFinBasis n (ULift.{u} ℤ) (e + 1)
    (twistedFreeNextMonomialIndex n e j i)
  dsimp only [twistMonomialMulHom]
  rw [← Functor.map_comp]
  rw [ProjectiveSpectrum.Twist.mulHom_comp]
  · exact congrArg
      (Modules.pullback
        (Limits.pullback.snd (specULiftZIsTerminal.from T)
          (specULiftZIsTerminal.from (projectiveSpace n)))).map
      (ProjectiveSpectrum.Twist.mulHom_congr 𝒜
        (⟨(p : MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ)) *
          (q : MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ)),
          SetLike.mul_mem_graded p.2 q.2⟩ : 𝒜 (e + 1)) r
        (twistedFreeMonomialBasis_mul_degreeOne n (ULift.{u} ℤ) e j i)
        0 ((e + 1 : ℕ) : ℤ) (by omega) (by omega))
  · omega

/-- Multiplication by `X_j` takes the morphism represented by a degree-`e`
monomial section to the successor monomial section. -/
theorem twistMonomialSectionHom_mul_degreeOne
    (n : ℕ) (T : Scheme.{u}) (e : ℕ)
    (j : Fin (n + 1)) (i : Fin ((n + e).choose n)) :
    twistMonomialSectionHom n T e i ≫
        twistMonomialMulHom n T (e : ℤ) ((e + 1 : ℕ) : ℤ) 1
          (by omega) (twistedFreeDegreeOneMonomialIndex n j) =
      twistMonomialSectionHom n T (e + 1)
        (twistedFreeNextMonomialIndex n e j i) := by
  rw [twistMonomialSectionHom_eq_zeroIso_inv_comp_mulHom,
    twistMonomialSectionHom_eq_zeroIso_inv_comp_mulHom]
  simp only [Category.assoc]
  rw [show twistMonomialMulHom n T 0 (e : ℤ) e (by omega) i ≫
        twistMonomialMulHom n T (e : ℤ) ((e + 1 : ℕ) : ℤ) 1
          (by omega) (twistedFreeDegreeOneMonomialIndex n j) =
      twistMonomialMulHom n T 0 ((e + 1 : ℕ) : ℤ) (e + 1)
        (by omega) (twistedFreeNextMonomialIndex n e j i) by
    exact twistMonomialMulHom_mul_degreeOne n T e j i]

/-- After twisting a summand `O(-l)` by `d`, multiplication by `X_j` takes a
degree-`e` monomial section to its degree-`e+1` successor. -/
theorem twistMonomialTwistedSectionHom_mul_degreeOne
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ))
    (j : Fin (n + 1)) (i : Fin ((n + e).choose n)) :
    twistMonomialTwistedSectionHom n T l d e he i ≫
        Modules.tensorMapRight (projectiveSpaceOverTwist n T (-l))
          (twistMonomialMulHom n T (d : ℤ) ((d + 1 : ℕ) : ℤ) 1
            (by omega) (twistedFreeDegreeOneMonomialIndex n j)) =
      twistMonomialTwistedSectionHom n T l (d + 1) (e + 1)
        (by omega) (twistedFreeNextMonomialIndex n e j i) := by
  let ad := projectiveSpaceOverTwist_addIso_nat n T (-l) d
  let an := projectiveSpaceOverTwist_addIso_nat n T (-l) (d + 1)
  let μd := twistMonomialMulHom n T (d : ℤ) ((d + 1 : ℕ) : ℤ) 1
    (by omega) (twistedFreeDegreeOneMonomialIndex n j)
  let μe := twistMonomialMulHom n T (e : ℤ) ((e + 1 : ℕ) : ℤ) 1
    (by omega) (twistedFreeDegreeOneMonomialIndex n j)
  let μs := twistMonomialMulHom n T (-l + (d : ℤ))
    (-l + ((d + 1 : ℕ) : ℤ)) 1 (by omega)
    (twistedFreeDegreeOneMonomialIndex n j)
  rw [← cancel_mono an.hom]
  rw [twistMonomialTwistedSectionHom_eq,
    twistMonomialTwistedSectionHom_eq]
  simp only [Category.assoc]
  have hadd := tensorMapRight_twistMonomialMulHom_comp_addIso_nat
    n T (-l) d (d + 1) 1 (by omega)
      (twistedFreeDegreeOneMonomialIndex n j)
  change Modules.tensorMapRight (projectiveSpaceOverTwist n T (-l)) μd ≫
      an.hom = ad.hom ≫ μs at hadd
  slice_lhs 5 6 => rw [hadd]
  slice_lhs 4 5 => rw [Iso.inv_hom_id]
  simp only [Category.id_comp]
  have hcast :
      eqToHom (congrArg
          (fun c : ℤ ↦ projectiveSpaceOverTwist n T c) he.symm) ≫
        eqToHom (congrArg
          (fun c : ℤ ↦ projectiveSpaceOverTwist n T c)
            (neg_add_eq_sub l (d : ℤ)).symm) ≫ μs =
      μe ≫
        eqToHom (congrArg
          (fun c : ℤ ↦ projectiveSpaceOverTwist n T c)
            (by omega : ((e + 1 : ℕ) : ℤ) =
              (d + 1 : ℕ) - l)) ≫
        eqToHom (congrArg
          (fun c : ℤ ↦ projectiveSpaceOverTwist n T c)
            (neg_add_eq_sub l ((d + 1 : ℕ) : ℤ)).symm) := by
    let h₀ : (e : ℤ) = -l + (d : ℤ) := by omega
    let h₁ : ((e + 1 : ℕ) : ℤ) = -l + ((d + 1 : ℕ) : ℤ) := by omega
    have hin := eqToHom_comp_twistMonomialMulHom n T
      (e : ℤ) (-l + (d : ℤ)) (-l + ((d + 1 : ℕ) : ℤ)) 1
      h₀ (by omega) (by omega) (twistedFreeDegreeOneMonomialIndex n j)
    have hout := twistMonomialMulHom_comp_eqToHom n T
      (e : ℤ) ((e + 1 : ℕ) : ℤ) (-l + ((d + 1 : ℕ) : ℤ)) 1
      (by omega) (by omega) (twistedFreeDegreeOneMonomialIndex n j)
    have hin' :
        eqToHom (congrArg
            (fun c : ℤ ↦ projectiveSpaceOverTwist n T c) he.symm) ≫
          eqToHom (congrArg
            (fun c : ℤ ↦ projectiveSpaceOverTwist n T c)
              (neg_add_eq_sub l (d : ℤ)).symm) ≫ μs =
        twistMonomialMulHom n T (e : ℤ)
          (-l + ((d + 1 : ℕ) : ℤ)) 1 (by omega)
            (twistedFreeDegreeOneMonomialIndex n j) := by
      simpa only [eqToHom_trans_assoc, μs] using hin
    have hout' :
        μe ≫
          eqToHom (congrArg
            (fun c : ℤ ↦ projectiveSpaceOverTwist n T c)
              (by omega : ((e + 1 : ℕ) : ℤ) =
                (d + 1 : ℕ) - l)) ≫
          eqToHom (congrArg
            (fun c : ℤ ↦ projectiveSpaceOverTwist n T c)
              (neg_add_eq_sub l ((d + 1 : ℕ) : ℤ)).symm) =
        twistMonomialMulHom n T (e : ℤ)
          (-l + ((d + 1 : ℕ) : ℤ)) 1 (by omega)
            (twistedFreeDegreeOneMonomialIndex n j) := by
      simpa only [Category.assoc, eqToHom_trans, μe] using hout
    exact hin'.trans hout'.symm
  slice_lhs 2 4 => rw [hcast]
  slice_lhs 1 2 => rw [twistMonomialSectionHom_mul_degreeOne]
  slice_rhs 4 5 => rw [Iso.inv_hom_id]
  exact (Category.assoc _ _ _).trans (Category.comp_id _).symm

/-- The morphism represented by a twisted-free monomial section decomposes as
the corresponding one-summand section followed by the tensor of the summand inclusion. -/
theorem unitHomOf_twistedFreeMonomialSection_eq
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) (j : ULift.{u} (Fin r))
    (i : Fin ((n + e).choose n)) :
    let F := ∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)
    let Fd := projectiveSpaceOverTwistModule F (d : ℤ)
    Fd.unitHomEquiv.symm ((Modules.sectionsTopEquiv Fd).symm
        (twistedFreeMonomialSection n T l r d e he j i)) =
      twistMonomialTwistedSectionHom n T l d e he i ≫
        Modules.tensorMapLeft
          (Sigma.ι (fun _ : ULift.{u} (Fin r) ↦
            projectiveSpaceOverTwist n T (-l)) j)
          (projectiveSpaceOverTwist n T (d : ℤ)) := by
  dsimp only
  let L := projectiveSpaceOverTwist n T (-l)
  let F := ∐ fun _ : ULift.{u} (Fin r) ↦ L
  let Fd := projectiveSpaceOverTwistModule F (d : ℤ)
  let Ld := projectiveSpaceOverTwistModule L (d : ℤ)
  let ι := Modules.tensorMapLeft
    (Sigma.ι (fun _ : ULift.{u} (Fin r) ↦ L) j)
    (projectiveSpaceOverTwist n T (d : ℤ))
  let core : Γ(Ld, ⊤) := Modules.Hom.app
    (projectiveSpaceOverTwist_addIso_nat n T (-l) d).inv ⊤
    (Modules.Hom.app
      (eqToHom (congrArg
        (fun c : ℤ ↦ projectiveSpaceOverTwist n T c)
        (neg_add_eq_sub l (d : ℤ)).symm)) ⊤
      (he ▸ twistMonomialSection n T e i))
  have hdec := twistedFreeMonomialSection_eq_summand
    n T l r d e he j i
  have hdecHom : Fd.unitHomEquiv.symm
        ((Modules.sectionsTopEquiv Fd).symm
          (twistedFreeMonomialSection n T l r d e he j i)) =
      Fd.unitHomEquiv.symm
        ((Modules.sectionsTopEquiv Fd).symm (Modules.Hom.app ι ⊤ core)) :=
    congrArg (fun s ↦ Fd.unitHomEquiv.symm
      ((Modules.sectionsTopEquiv Fd).symm s)) hdec
  have hsectionNat : Fd.unitHomEquiv.symm
        ((Modules.sectionsTopEquiv Fd).symm (Modules.Hom.app ι ⊤ core)) =
      Ld.unitHomEquiv.symm ((Modules.sectionsTopEquiv Ld).symm core) ≫ ι :=
    (Modules.unitHomOfSection_comp core ι).symm
  have hs : twistMonomialTwistedSectionHom n T l d e he i =
      Ld.unitHomEquiv.symm ((Modules.sectionsTopEquiv Ld).symm core) := rfl
  exact hdecHom.trans (hsectionNat.trans
    (congrArg (fun k ↦ k ≫ ι) hs.symm))

/-- Multiplication by `X_k` carries each twisted-free ambient monomial section
to the section at the successor monomial index. -/
theorem twistedFreeMonomialSection_mul_degreeOne
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) (j : ULift.{u} (Fin r))
    (k : Fin (n + 1)) (i : Fin ((n + e).choose n)) :
    let F := ∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)
    Modules.Hom.app
        (Modules.tensorMapRight F
          (twistMonomialMulHom n T (d : ℤ) ((d + 1 : ℕ) : ℤ) 1
            (by omega) (twistedFreeDegreeOneMonomialIndex n k))) ⊤
        (twistedFreeMonomialSection n T l r d e he j i) =
      twistedFreeMonomialSection n T l r (d + 1) (e + 1)
        (by omega) j (twistedFreeNextMonomialIndex n e k i) := by
  dsimp only
  let L := projectiveSpaceOverTwist n T (-l)
  let F := ∐ fun _ : ULift.{u} (Fin r) ↦ L
  let Od := projectiveSpaceOverTwist n T (d : ℤ)
  let On := projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ)
  let Fd := projectiveSpaceOverTwistModule F (d : ℤ)
  let Fn := projectiveSpaceOverTwistModule F ((d + 1 : ℕ) : ℤ)
  let ι := Sigma.ι (fun _ : ULift.{u} (Fin r) ↦ L) j
  let ιd := Modules.tensorMapLeft ι Od
  let ιn := Modules.tensorMapLeft ι On
  let μ := twistMonomialMulHom n T (d : ℤ) ((d + 1 : ℕ) : ℤ) 1
    (by omega) (twistedFreeDegreeOneMonomialIndex n k)
  let μL := Modules.tensorMapRight L μ
  let μF := Modules.tensorMapRight F μ
  let sd := twistedFreeMonomialSection n T l r d e he j i
  let sn := twistedFreeMonomialSection n T l r (d + 1) (e + 1)
    (by omega) j (twistedFreeNextMonomialIndex n e k i)
  let hd := twistMonomialTwistedSectionHom n T l d e he i
  let hn := twistMonomialTwistedSectionHom n T l (d + 1) (e + 1)
    (by omega) (twistedFreeNextMonomialIndex n e k i)
  apply (Modules.sectionsTopEquiv Fn).symm.injective
  apply Fn.unitHomEquiv.symm.injective
  have hnat := Modules.unitHomOfSection_comp sd μF
  change Fd.unitHomEquiv.symm ((Modules.sectionsTopEquiv Fd).symm sd) ≫ μF =
      Fn.unitHomEquiv.symm ((Modules.sectionsTopEquiv Fn).symm
        (Modules.Hom.app μF ⊤ sd)) at hnat
  rw [← hnat]
  have hsd := unitHomOf_twistedFreeMonomialSection_eq
    n T l r d e he j i
  change Fd.unitHomEquiv.symm ((Modules.sectionsTopEquiv Fd).symm sd) =
      hd ≫ ιd at hsd
  have hsn := unitHomOf_twistedFreeMonomialSection_eq
    n T l r (d + 1) (e + 1) (by omega) j
      (twistedFreeNextMonomialIndex n e k i)
  change Fn.unitHomEquiv.symm ((Modules.sectionsTopEquiv Fn).symm sn) =
      hn ≫ ιn at hsn
  rw [hsd, hsn]
  have hex := Modules.tensorMap_exchange ι μ
  change μL ≫ ιn = ιd ≫ μF at hex
  have hcore : hd ≫ μL = hn :=
    twistMonomialTwistedSectionHom_mul_degreeOne n T l d e he k i
  calc
    (hd ≫ ιd) ≫ μF = hd ≫ (ιd ≫ μF) := Category.assoc _ _ _
    _ = hd ≫ (μL ≫ ιn) := congrArg (fun z ↦ hd ≫ z) hex.symm
    _ = (hd ≫ μL) ≫ ιn := (Category.assoc _ _ _).symm
    _ = hn ≫ ιn := congrArg (fun z ↦ z ≫ ιn) hcore

/-- Multiplication by `X_k` carries the image of an ambient monomial section in
an arbitrary quotient to the successor quotient monomial section. -/
theorem quotMonomialSection_mul_degreeOne
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ))
    {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    (j : ULift.{u} (Fin r)) (k : Fin (n + 1))
    (i : Fin ((n + e).choose n)) :
    Modules.Hom.app
        (Modules.projectiveTwistMulOne n Q d
          (twistedFreeDegreeOneMonomialIndex n k)) ⊤
        (quotMonomialSection n T l r p d e he j i) =
      quotMonomialSection n T l r p (d + 1) (e + 1)
        (by omega) j (twistedFreeNextMonomialIndex n e k i) := by
  let F := ∐ fun _ : ULift.{u} (Fin r) ↦
    projectiveSpaceOverTwist n T (-l)
  let Od := projectiveSpaceOverTwist n T (d : ℤ)
  let On := projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ)
  let μ := twistMonomialMulHom n T (d : ℤ) ((d + 1 : ℕ) : ℤ) 1
    (by omega) (twistedFreeDegreeOneMonomialIndex n k)
  let pOd := Modules.tensorMapLeft p Od
  let pOn := Modules.tensorMapLeft p On
  let μF := Modules.tensorMapRight F μ
  let μQ := Modules.tensorMapRight Q μ
  let sd := twistedFreeMonomialSection n T l r d e he j i
  let sn := twistedFreeMonomialSection n T l r (d + 1) (e + 1)
    (by omega) j (twistedFreeNextMonomialIndex n e k i)
  change Modules.Hom.app μQ ⊤ (Modules.Hom.app pOd ⊤ sd) =
    Modules.Hom.app pOn ⊤ sn
  have hex := Modules.tensorMap_exchange p μ
  change μF ≫ pOn = pOd ≫ μQ at hex
  have happ := congrArg
    (fun f ↦ Modules.Hom.app f ⊤ sd) hex.symm
  rw [Modules.Hom.comp_app, Modules.Hom.comp_app] at happ
  change Modules.Hom.app μQ ⊤ (Modules.Hom.app pOd ⊤ sd) =
    Modules.Hom.app pOn ⊤ (Modules.Hom.app μF ⊤ sd) at happ
  rw [happ]
  exact congrArg (fun s ↦ Modules.Hom.app pOn ⊤ s)
    (twistedFreeMonomialSection_mul_degreeOne
      n T l r d e he j k i)

/-- The degree-`d+1` Grassmannian free map after successor reindexing is the
degree-`d` map followed by multiplication by the corresponding projective variable. -/
theorem quotGrassmannianFreeMap_mul_degreeOne
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ))
    {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    (k : Fin (n + 1)) :
    SheafOfModules.freeMap (R := T.ringCatSheaf)
        (fun x : ULift.{u} (Fin r) × Fin ((n + e).choose n) ↦
          (x.1, twistedFreeNextMonomialIndex n e k x.2)) ≫
      quotGrassmannianFreeMap n T l r p (d + 1) (e + 1) (by omega) =
    quotGrassmannianFreeMap n T l r p d e he ≫
      (Modules.pushforward (projectiveSpaceOverπ n T)).map
        (Modules.projectiveTwistMulOne n Q d
          (twistedFreeDegreeOneMonomialIndex n k)) := by
  dsimp only [quotGrassmannianFreeMap]
  rw [Modules.freeMap_comp_freeHomOfSections,
    Modules.freeHomOfSections_comp]
  apply congrArg Modules.freeHomOfSections
  funext x
  exact (quotMonomialSection_mul_degreeOne
    n T l r d e he p x.1 k x.2).symm

/-- The degree-`d+1` Grassmannian free map of the reconstructed quotient kills
the algebraic next-degree relation. -/
theorem twistedFreeNextDegreeRelation_comp_reconstructedPushforwardMap
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E) :
    twistedFreeNextDegreeRelation n T r e u ≫
        quotGrassmannianFreeMap n T l r
          (reconstructedQuotientMap' n T l r d e he u)
          (d + 1) (e + 1) (by omega) = 0 := by
  let p := reconstructedQuotientMap' n T l r d e he u
  let qd := quotGrassmannianFreeMap n T l r p d e he
  let qn := quotGrassmannianFreeMap n T l r p
    (d + 1) (e + 1) (by omega)
  have hambient := twistedFreeMonomialHom_eq_tensorMapLeft_cancel_of_single
    n T l r d e he (fun i ↦
      twistMonomialMulHom_eq_tensor_twistedSection_cancel
        n T l d e he i)
  have hkernel :=
    kernel_ι_comp_quotGrassmannianFreeMap_reconstructedQuotientMap'_eq_zero
      n T l r d e he u hambient
  change kernel.ι u ≫ qd = 0 at hkernel
  apply Sigma.hom_ext
  intro j
  let fj := SheafOfModules.freeMap (R := T.ringCatSheaf)
    (fun x : ULift.{u} (Fin r) × Fin ((n + e).choose n) ↦
      (x.1, twistedFreeNextMonomialIndex n e j.down x.2))
  have hi : Sigma.ι (fun _ : ULift.{u} (Fin (n + 1)) ↦ kernel u) j ≫
      twistedFreeNextDegreeRelation n T r e u = kernel.ι u ≫ fj := by
    dsimp only [twistedFreeNextDegreeRelation]
    exact Sigma.ι_desc _ j
  have hmul := quotGrassmannianFreeMap_mul_degreeOne
    n T l r d e he p j.down
  change fj ≫ qn =
    qd ≫ (Modules.pushforward (projectiveSpaceOverπ n T)).map
      (Modules.projectiveTwistMulOne n
        (reconstructedQuotient' n T l r d e he u) d
        (twistedFreeDegreeOneMonomialIndex n j.down)) at hmul
  have hzero : (kernel.ι u ≫ fj) ≫ qn = 0 := by
    calc
      (kernel.ι u ≫ fj) ≫ qn =
          kernel.ι u ≫ (fj ≫ qn) := Category.assoc _ _ _
      _ = kernel.ι u ≫
          (qd ≫ (Modules.pushforward (projectiveSpaceOverπ n T)).map
            (Modules.projectiveTwistMulOne n
              (reconstructedQuotient' n T l r d e he u) d
              (twistedFreeDegreeOneMonomialIndex n j.down))) :=
        congrArg (fun z ↦ kernel.ι u ≫ z) hmul
      _ = (kernel.ι u ≫ qd) ≫
          (Modules.pushforward (projectiveSpaceOverπ n T)).map
            (Modules.projectiveTwistMulOne n
              (reconstructedQuotient' n T l r d e he u) d
              (twistedFreeDegreeOneMonomialIndex n j.down)) :=
        (Category.assoc _ _ _).symm
      _ = 0 := by rw [hkernel, zero_comp]
  calc
    Sigma.ι (fun _ : ULift.{u} (Fin (n + 1)) ↦ kernel u) j ≫
          (twistedFreeNextDegreeRelation n T r e u ≫ qn) =
        (Sigma.ι (fun _ : ULift.{u} (Fin (n + 1)) ↦ kernel u) j ≫
          twistedFreeNextDegreeRelation n T r e u) ≫ qn :=
      (Category.assoc _ _ _).symm
    _ = (kernel.ι u ≫ fj) ≫ qn :=
      congrArg (fun z ↦ z ≫ qn) hi
    _ = 0 := hzero
    _ = Sigma.ι (fun _ : ULift.{u} (Fin (n + 1)) ↦ kernel u) j ≫ 0 :=
      comp_zero.symm

/-- The canonical comparison from the finite algebraic next-degree quotient to
the degree-`d+1` twisted pushforward of the reconstructed projective quotient. -/
noncomputable def twistedFreeNextDegreeModuleToReconstructedPushforward
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E) :
    twistedFreeNextDegreeModule n T r e u ⟶
      Modules.projectiveTwistedPushforward n
        (reconstructedQuotient' n T l r d e he u) (d + 1) :=
  cokernel.desc (twistedFreeNextDegreeRelation n T r e u)
    (quotGrassmannianFreeMap n T l r
      (reconstructedQuotientMap' n T l r d e he u)
      (d + 1) (e + 1) (by omega))
    (twistedFreeNextDegreeRelation_comp_reconstructedPushforwardMap
      n T l r d e he u)

/-- The comparison from the algebraic next-degree quotient is characterized by
its composite with the cokernel projection. -/
@[reassoc]
theorem twistedFreeNextDegreeModuleToReconstructedPushforward_fac
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E) :
    cokernel.π (twistedFreeNextDegreeRelation n T r e u) ≫
        twistedFreeNextDegreeModuleToReconstructedPushforward
          n T l r d e he u =
      quotGrassmannianFreeMap n T l r
        (reconstructedQuotientMap' n T l r d e he u)
        (d + 1) (e + 1) (by omega) := by
  exact cokernel.π_desc _ _ _

end AlgebraicGeometry.Scheme

end

end
