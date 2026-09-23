module

public import StacksAndModuli.API.DVRClosedFiberGlobalSectionsRank
public import StacksAndModuli.API.DVRClosedFiber
public import StacksAndModuli.API.FiniteProjectiveFiberRank
public import StacksAndModuli.API.ProjectiveDVRFlatGlobalSectionsRank
public import StacksAndModuli.API.ProjectiveSpaceOverMapIso

/-!
# Global-section ranks on the generic and closed fibres of projective space over a DVR

This file combines the generic- and closed-fibre rank calculations for a flat
quasicoherent module on projective space over a discrete valuation ring.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TensorProduct
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical principal closed fibre of projective space is projective
space over the quotient ring. -/
noncomputable def projectiveSpacePrincipalClosedFiberIso
    (n : ℕ) (R : CommRingCat.{u}) (r : R) :
    let p := Scheme.projectiveSpaceOverπ n (Spec R)
    principalClosedFiber (r := r) p ≅
      Scheme.projectiveSpaceOver n (Spec (principalClosedFiberRing r)) :=
  Limits.pullbackSymmetry _ _ ≪≫
    Scheme.projectiveSpaceOverBaseChangeIso n
      (Spec.map (principalClosedFiberRingHom r))

/-- The principal-fibre comparison followed by the standard base-change map
is the canonical inclusion into projective space over the original ring. -/
@[reassoc (attr := simp)]
theorem projectiveSpacePrincipalClosedFiberIso_hom_map
    (n : ℕ) (R : CommRingCat.{u}) (r : R) :
    let p := Scheme.projectiveSpaceOverπ n (Spec R)
    (projectiveSpacePrincipalClosedFiberIso n R r).hom ≫
        Scheme.projectiveSpaceOverMap n
          (Spec.map (principalClosedFiberRingHom r)) =
      principalClosedFiberι (r := r) p := by
  dsimp only
  unfold projectiveSpacePrincipalClosedFiberIso principalClosedFiberι
  rw [Iso.trans_hom, Category.assoc,
    Scheme.projectiveSpaceOverBaseChangeIso_hom_map]
  exact Limits.pullbackSymmetry_hom_comp_snd _ _

/-- The principal-fibre comparison preserves the projection to the quotient
ring. -/
@[reassoc (attr := simp)]
theorem projectiveSpacePrincipalClosedFiberIso_hom_π
    (n : ℕ) (R : CommRingCat.{u}) (r : R) :
    let p := Scheme.projectiveSpaceOverπ n (Spec R)
    (projectiveSpacePrincipalClosedFiberIso n R r).hom ≫
        Scheme.projectiveSpaceOverπ n
          (Spec (principalClosedFiberRing r)) =
      principalClosedFiberToQuotientSpec (r := r) p := by
  dsimp only
  unfold projectiveSpacePrincipalClosedFiberIso
    principalClosedFiberToQuotientSpec
  rw [Iso.trans_hom, Category.assoc,
    Scheme.projectiveSpaceOverBaseChangeIso_hom_π]
  exact Limits.pullbackSymmetry_hom_comp_fst _ _

/-- In inverse orientation, the principal-fibre comparison followed by the
canonical inclusion is the standard projective-space base-change map. -/
@[reassoc (attr := simp)]
theorem projectiveSpacePrincipalClosedFiberIso_inv_ι
    (n : ℕ) (R : CommRingCat.{u}) (r : R) :
    let p := Scheme.projectiveSpaceOverπ n (Spec R)
    (projectiveSpacePrincipalClosedFiberIso n R r).inv ≫
        principalClosedFiberι (r := r) p =
      Scheme.projectiveSpaceOverMap n
        (Spec.map (principalClosedFiberRingHom r)) := by
  dsimp only
  rw [← cancel_epi (projectiveSpacePrincipalClosedFiberIso n R r).hom]
  simp

/-- In inverse orientation, the principal-fibre comparison preserves the
structure morphism to the quotient ring. -/
@[reassoc (attr := simp)]
theorem projectiveSpacePrincipalClosedFiberIso_inv_π
    (n : ℕ) (R : CommRingCat.{u}) (r : R) :
    let p := Scheme.projectiveSpaceOverπ n (Spec R)
    (projectiveSpacePrincipalClosedFiberIso n R r).inv ≫
        principalClosedFiberToQuotientSpec (r := r) p =
      Scheme.projectiveSpaceOverπ n
        (Spec (principalClosedFiberRing r)) := by
  dsimp only
  rw [← cancel_epi (projectiveSpacePrincipalClosedFiberIso n R r).hom]
  simp

/-- Transporting the pullback of a module from the raw principal-fibre
pullback to standard projective space gives its usual coefficient base change. -/
noncomputable def pullbackProjectiveSpacePrincipalClosedFiberIso
    (n : ℕ) (R : CommRingCat.{u}) (r : R)
    (N : (Scheme.projectiveSpaceOver n (Spec R)).Modules) :
    let p := Scheme.projectiveSpaceOverπ n (Spec R)
    let i := principalClosedFiberι (r := r) p
    (pullback (projectiveSpacePrincipalClosedFiberIso n R r).inv).obj
        ((pullback i).obj N) ≅
      (pullback (Scheme.projectiveSpaceOverMap n
        (Spec.map (principalClosedFiberRingHom r)))).obj N :=
  (pullbackComp (projectiveSpacePrincipalClosedFiberIso n R r).inv
      (principalClosedFiberι (r := r)
        (Scheme.projectiveSpaceOverπ n (Spec R)))).app N ≪≫
    (pullbackCongr
      (projectiveSpacePrincipalClosedFiberIso_inv_ι n R r)).app N

/-- Pulling the quotient-ring closed fibre across its canonical identification
with the scheme-theoretic residue field gives the usual closed fibre. -/
noncomputable def principalClosedFiberToResidueFieldPullbackIso
    {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R]
    (n : ℕ) (Q : (Scheme.projectiveSpaceOver n
      (Spec (CommRingCat.of R))).Modules)
    {ϖ : R} (hϖ : Irreducible ϖ) :
    let e := principalClosedFiberRingIsoSchemeResidueField hϖ
    let q := Spec.map
      (principalClosedFiberRingHom (R := CommRingCat.of R) ϖ)
    let c := (Spec (CommRingCat.of R)).fromSpecResidueField
      (IsLocalRing.closedPoint R)
    let f := Scheme.projectiveSpaceOverMap n (Spec.map e.hom)
    let QS := (pullback (Scheme.projectiveSpaceOverMap n q)).obj Q
    let Qκ := (pullback (Scheme.projectiveSpaceOverMap n c)).obj Q
    (pullback f).obj QS ≅ Qκ := by
  dsimp only
  let e := principalClosedFiberRingIsoSchemeResidueField hϖ
  let q := Spec.map
    (principalClosedFiberRingHom (R := CommRingCat.of R) ϖ)
  let c := (Spec (CommRingCat.of R)).fromSpecResidueField
    (IsLocalRing.closedPoint R)
  let f := Scheme.projectiveSpaceOverMap n (Spec.map e.hom)
  exact (pullbackComp f (Scheme.projectiveSpaceOverMap n q)).app Q ≪≫
    (pullbackCongr
      (Scheme.projectiveSpaceOverMap_comp n (Spec.map e.hom) q)).app Q ≪≫
    (pullbackCongr (congrArg (Scheme.projectiveSpaceOverMap n)
      (SpecMap_schemeResidueFieldIso_hom_comp_principalClosedFiber hϖ))).app Q

/-- The Hilbert function on the quotient-ring model of a DVR's closed fibre is
the Hilbert function on the canonical scheme-theoretic residue-field fibre,
provided pullback is identified with the chosen twist. -/
theorem hilbertFunctionOver_principalClosedFiber_eq_residueField_of_twistIso
    {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R]
    (n : ℕ) (Q : (Scheme.projectiveSpaceOver n
      (Spec (CommRingCat.of R))).Modules)
    {ϖ : R} (hϖ : Irreducible ϖ) (d : ℤ)
    (eTwist :
      let e := principalClosedFiberRingIsoSchemeResidueField hϖ
      let q := Spec.map
        (principalClosedFiberRingHom (R := CommRingCat.of R) ϖ)
      let f := Scheme.projectiveSpaceOverMap n (Spec.map e.hom)
      let QS := (pullback (Scheme.projectiveSpaceOverMap n q)).obj Q
      (pullback f).obj (Scheme.projectiveSpaceOverTwistModule QS d) ≅
        Scheme.projectiveSpaceOverTwistModule ((pullback f).obj QS) d) :
    let q := Spec.map
      (principalClosedFiberRingHom (R := CommRingCat.of R) ϖ)
    let c := (Spec (CommRingCat.of R)).fromSpecResidueField
      (IsLocalRing.closedPoint R)
    let QS := (pullback (Scheme.projectiveSpaceOverMap n q)).obj Q
    let Qκ := (pullback (Scheme.projectiveSpaceOverMap n c)).obj Q
    Scheme.hilbertFunctionOver QS d = Scheme.hilbertFunctionOver Qκ d := by
  dsimp only at eTwist ⊢
  let S := principalClosedFiberRing (R := CommRingCat.of R) ϖ
  let κ := (Spec (CommRingCat.of R)).residueField
    (IsLocalRing.closedPoint R)
  let e : S ≅ κ := principalClosedFiberRingIsoSchemeResidueField hϖ
  let q := Spec.map
    (principalClosedFiberRingHom (R := CommRingCat.of R) ϖ)
  let c := (Spec (CommRingCat.of R)).fromSpecResidueField
    (IsLocalRing.closedPoint R)
  let QS := (pullback (Scheme.projectiveSpaceOverMap n q)).obj Q
  let Qκ := (pullback (Scheme.projectiveSpaceOverMap n c)).obj Q
  let _ : (Ideal.span {ϖ} : Ideal R).IsMaximal := by
    rw [← hϖ.maximalIdeal_eq]
    infer_instance
  letI : Field S := Ideal.Quotient.field (Ideal.span {ϖ})
  letI : Field κ := inferInstance
  have htransport := Scheme.hilbertFunctionOver_pullback_ringIso_of_twistIso
    n (Field.toIsField S) (Field.toIsField κ) e QS d eTwist
  exact htransport.trans
    (Scheme.hilbertFunctionOver_iso
      (principalClosedFiberToResidueFieldPullbackIso n Q hϖ) d)

/-- The quotient-ring and canonical residue-field models of a DVR's closed
fibre have the same Hilbert function. -/
theorem hilbertFunctionOver_principalClosedFiber_eq_residueField
    {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R]
    (n : ℕ) (Q : (Scheme.projectiveSpaceOver n
      (Spec (CommRingCat.of R))).Modules)
    {ϖ : R} (hϖ : Irreducible ϖ) (d : ℤ) :
    let q := Spec.map
      (principalClosedFiberRingHom (R := CommRingCat.of R) ϖ)
    let c := (Spec (CommRingCat.of R)).fromSpecResidueField
      (IsLocalRing.closedPoint R)
    let QS := (pullback (Scheme.projectiveSpaceOverMap n q)).obj Q
    let Qκ := (pullback (Scheme.projectiveSpaceOverMap n c)).obj Q
    Scheme.hilbertFunctionOver QS d = Scheme.hilbertFunctionOver Qκ d := by
  dsimp only
  let e := principalClosedFiberRingIsoSchemeResidueField hϖ
  let q := Spec.map
    (principalClosedFiberRingHom (R := CommRingCat.of R) ϖ)
  let QS := (pullback (Scheme.projectiveSpaceOverMap n q)).obj Q
  letI : IsIso (Spec.map e.hom) := (Scheme.Spec.mapIso e.op).isIso_hom
  exact hilbertFunctionOver_principalClosedFiber_eq_residueField_of_twistIso
    n Q hϖ d
      (Scheme.projectiveSpaceOverTwistModule_pullbackIso_of_isOpenImmersion
        n (Spec.map e.hom) QS d)

/-- A Hilbert polynomial on the quotient-ring model of a DVR's closed fibre
transports to the canonical scheme-theoretic residue-field fibre. -/
theorem hasHilbertPolynomialOver_residueField_of_principalClosedFiber
    {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R]
    (n : ℕ) (Q : (Scheme.projectiveSpaceOver n
      (Spec (CommRingCat.of R))).Modules)
    {ϖ : R} (hϖ : Irreducible ϖ) (P : Polynomial ℚ)
    (h :
      let q := Spec.map
        (principalClosedFiberRingHom (R := CommRingCat.of R) ϖ)
      let QS := (pullback (Scheme.projectiveSpaceOverMap n q)).obj Q
      Scheme.HasHilbertPolynomialOver QS P) :
    let c := (Spec (CommRingCat.of R)).fromSpecResidueField
      (IsLocalRing.closedPoint R)
    let Qκ := (pullback (Scheme.projectiveSpaceOverMap n c)).obj Q
    Scheme.HasHilbertPolynomialOver Qκ P := by
  dsimp only at h ⊢
  filter_upwards [h] with d hd
  rw [← hilbertFunctionOver_principalClosedFiber_eq_residueField
    (R := R) n Q hϖ]
  exact hd

/-- Global sections on the raw principal fibre agree linearly over the quotient
ring with global sections of the standard projective-space base change. -/
noncomputable def principalClosedFiberGlobalSectionsLinearEquiv_projectiveSpaceBaseChange
    (n : ℕ) (R : CommRingCat.{u}) (r : R)
    (N : (Scheme.projectiveSpaceOver n (Spec R)).Modules) :
    let p := Scheme.projectiveSpaceOverπ n (Spec R)
    let i := principalClosedFiberι (r := r) p
    let pZ := principalClosedFiberToQuotientSpec (r := r) p
    let S := principalClosedFiberRing r
    let NS := (pullback (Scheme.projectiveSpaceOverMap n
      (Spec.map (principalClosedFiberRingHom r)))).obj N
    letI : Module S Γ((pullback i).obj N, ⊤) :=
      globalSectionsModule pZ ((pullback i).obj N)
    letI : Module S Γ(NS, ⊤) := globalSectionsModule
      (Scheme.projectiveSpaceOverπ n (Spec S)) NS
    Γ((pullback i).obj N, ⊤) ≃ₗ[S] Γ(NS, ⊤) := by
  dsimp only
  let p := Scheme.projectiveSpaceOverπ n (Spec R)
  let i := principalClosedFiberι (r := r) p
  let pZ := principalClosedFiberToQuotientSpec (r := r) p
  let eX := projectiveSpacePrincipalClosedFiberIso n R r
  let eN := pullbackProjectiveSpacePrincipalClosedFiberIso n R r N
  let E := pullbackGlobalSectionsViaIsoLinearEquiv eX.inv pZ
    ((pullback i).obj N) eN
  rw [projectiveSpacePrincipalClosedFiberIso_inv_π] at E
  exact E

/-- If multiplication by a uniformizer has the expected geometric cokernel, the
dimensions of the global sections on the standard generic fibre and the chosen
principal closed fibre agree. -/
theorem FlatOver.finrank_projectiveSpaceBaseChange_eq_principalClosedFiber_of_finite
    (n : ℕ) (R : CommRingCat.{u}) [IsDomain R]
    [IsDiscreteValuationRing R]
    (N : (Scheme.projectiveSpaceOver n (Spec R)).Modules)
    [N.IsQuasicoherent]
    (hflat : N.FlatOver (Scheme.projectiveSpaceOverπ n (Spec R)))
    (ϖ : R) (hϖ : Irreducible ϖ)
    {Z : Scheme.{u}}
    (i : Z ⟶ Scheme.projectiveSpaceOver n (Spec R))
    (pZ : Z ⟶ Spec (principalClosedFiberRing ϖ))
    (hbase : i ≫ Scheme.projectiveSpaceOverπ n (Spec R) =
      pZ ≫ Spec.map (principalClosedFiberRingHom ϖ))
    (hH1 : Subsingleton (((SheafOfModules.toSheaf _).obj N).H 1))
    (eC : cokernel (N.mulByGlobalSection
        ((baseRingHom (Scheme.projectiveSpaceOverπ n (Spec R))).hom ϖ)) ≅
      (pushforward i).obj ((pullback i).obj N))
    (hfinite :
      letI : Module R Γ(N, ⊤) := globalSectionsModule
        (Scheme.projectiveSpaceOverπ n (Spec R)) N
      Module.Finite R Γ(N, ⊤)) :
    let φ : R ⟶ CommRingCat.of (FractionRing R) :=
      CommRingCat.ofHom (algebraMap R (FractionRing R))
    let j₀ := Spec.map φ
    let NK := (pullback (Scheme.projectiveSpaceOverMap n j₀)).obj N
    let S := principalClosedFiberRing ϖ
    let F := (pullback i).obj N
    letI : Module (FractionRing R) Γ(NK, ⊤) :=
      globalSectionsModule
        (Scheme.projectiveSpaceOverπ n
          (Spec (CommRingCat.of (FractionRing R)))) NK
    letI : Module S Γ(F, ⊤) := globalSectionsModule pZ F
    Module.finrank (FractionRing R) Γ(NK, ⊤) =
      Module.finrank S Γ(F, ⊤) := by
  dsimp only
  let p := Scheme.projectiveSpaceOverπ n (Spec R)
  let φ : R ⟶ CommRingCat.of (FractionRing R) :=
    CommRingCat.ofHom (algebraMap R (FractionRing R))
  let j₀ := Spec.map φ
  let NK := (pullback (Scheme.projectiveSpaceOverMap n j₀)).obj N
  let S := principalClosedFiberRing ϖ
  let F := (pullback i).obj N
  let _ : (Ideal.span {ϖ} : Ideal R).IsMaximal := by
    rw [← hϖ.maximalIdeal_eq]
    infer_instance
  letI : Field S := Ideal.Quotient.field (Ideal.span {ϖ})
  letI : Module R Γ(N, ⊤) := globalSectionsModule p N
  letI : Module (FractionRing R) Γ(NK, ⊤) :=
    globalSectionsModule
      (Scheme.projectiveSpaceOverπ n
        (Spec (CommRingCat.of (FractionRing R)))) NK
  letI : Module S Γ(F, ⊤) := globalSectionsModule pZ F
  have hgeneric :=
    hflat.finrank_projectiveSpaceBaseChange_globalSections_eq_of_finite
      n R N ϖ hϖ hfinite
  have hclosed :=
    hflat.finrank_principalClosedFiber_globalSections_eq_of_finite
      R p ϖ hϖ i pZ hbase N hH1 eC hfinite
  exact hgeneric.trans hclosed.symm

/-- In a fixed twist, the generic-fibre Hilbert function equals the dimension of
global sections of the pullback of that twist to a principal closed-fibre model.
Flatness is required only for the original sheaf `Q`; twisting preserves it. -/
theorem FlatOver.hilbertFunctionOver_fractionRing_eq_finrank_principalClosedFiber
    (n : ℕ) (R : CommRingCat.{u}) [IsDomain R]
    [IsDiscreteValuationRing R]
    (Q : (Scheme.projectiveSpaceOver n (Spec R)).Modules)
    [Q.IsQuasicoherent]
    (hflat : Q.FlatOver (Scheme.projectiveSpaceOverπ n (Spec R)))
    (d : ℤ) (ϖ : R) (hϖ : Irreducible ϖ)
    {Z : Scheme.{u}}
    (i : Z ⟶ Scheme.projectiveSpaceOver n (Spec R))
    (pZ : Z ⟶ Spec (principalClosedFiberRing ϖ))
    (hbase : i ≫ Scheme.projectiveSpaceOverπ n (Spec R) =
      pZ ≫ Spec.map (principalClosedFiberRingHom ϖ))
    (hH1 : Subsingleton (((SheafOfModules.toSheaf _).obj
      (Scheme.projectiveSpaceOverTwistModule Q d)).H 1))
    (eC : cokernel ((Scheme.projectiveSpaceOverTwistModule Q d).mulByGlobalSection
        ((baseRingHom (Scheme.projectiveSpaceOverπ n (Spec R))).hom ϖ)) ≅
      (pushforward i).obj
        ((pullback i).obj (Scheme.projectiveSpaceOverTwistModule Q d)))
    (hfinite :
      let Qd := Scheme.projectiveSpaceOverTwistModule Q d
      letI : Module R Γ(Qd, ⊤) := globalSectionsModule
        (Scheme.projectiveSpaceOverπ n (Spec R)) Qd
      Module.Finite R Γ(Qd, ⊤)) :
    let j₀ := Spec.map
      (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    let QK := (pullback (Scheme.projectiveSpaceOverMap n j₀)).obj Q
    let Qd := Scheme.projectiveSpaceOverTwistModule Q d
    let S := principalClosedFiberRing ϖ
    let Fd := (pullback i).obj Qd
    letI : Module S Γ(Fd, ⊤) := globalSectionsModule pZ Fd
    Scheme.hilbertFunctionOver QK d = Module.finrank S Γ(Fd, ⊤) := by
  dsimp only
  let p := Scheme.projectiveSpaceOverπ n (Spec R)
  let j₀ := Spec.map
    (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  let QK := (pullback (Scheme.projectiveSpaceOverMap n j₀)).obj Q
  let Qd := Scheme.projectiveSpaceOverTwistModule Q d
  let S := principalClosedFiberRing ϖ
  let Fd := (pullback i).obj Qd
  let _ : (Ideal.span {ϖ} : Ideal R).IsMaximal := by
    rw [← hϖ.maximalIdeal_eq]
    infer_instance
  letI : Field S := Ideal.Quotient.field (Ideal.span {ϖ})
  letI : Module R Γ(Qd, ⊤) := globalSectionsModule p Qd
  letI : Module S Γ(Fd, ⊤) := globalSectionsModule pZ Fd
  have hgeneric :=
    hflat.finrank_twistedGlobalSections_eq_hilbertFunctionOver_fractionRing_of_finite
      n R Q d ϖ hϖ hfinite
  have hflatQd := hflat.projectiveSpaceOverTwistModule n (Spec R) Q d
  have hclosed :=
    hflatQd.finrank_principalClosedFiber_globalSections_eq_of_finite
      R p ϖ hϖ i pZ hbase Qd hH1 eC hfinite
  exact hgeneric.symm.trans hclosed.symm

/-- In a fixed twist, the generic-fibre Hilbert function equals the dimension of
global sections on the canonical principal closed fibre.  The geometric cokernel
hypothesis in
`FlatOver.hilbertFunctionOver_fractionRing_eq_finrank_principalClosedFiber` is
automatic for this fibre. -/
theorem FlatOver.hilbertFunctionOver_fractionRing_eq_finrank_canonicalPrincipalClosedFiber
    (n : ℕ) (R : CommRingCat.{u}) [IsDomain R]
    [IsDiscreteValuationRing R]
    (Q : (Scheme.projectiveSpaceOver n (Spec R)).Modules)
    [Q.IsQuasicoherent]
    (hflat : Q.FlatOver (Scheme.projectiveSpaceOverπ n (Spec R)))
    (d : ℤ) (ϖ : R) (hϖ : Irreducible ϖ)
    (hH1 : Subsingleton (((SheafOfModules.toSheaf _).obj
      (Scheme.projectiveSpaceOverTwistModule Q d)).H 1))
    (hfinite :
      let Qd := Scheme.projectiveSpaceOverTwistModule Q d
      letI : Module R Γ(Qd, ⊤) := globalSectionsModule
        (Scheme.projectiveSpaceOverπ n (Spec R)) Qd
      Module.Finite R Γ(Qd, ⊤)) :
    let p := Scheme.projectiveSpaceOverπ n (Spec R)
    let i := principalClosedFiberι (r := ϖ) p
    let pZ := principalClosedFiberToQuotientSpec (r := ϖ) p
    let j₀ := Spec.map
      (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    let QK := (pullback (Scheme.projectiveSpaceOverMap n j₀)).obj Q
    let Qd := Scheme.projectiveSpaceOverTwistModule Q d
    let S := principalClosedFiberRing ϖ
    let Fd := (pullback i).obj Qd
    letI : Module S Γ(Fd, ⊤) := globalSectionsModule pZ Fd
    Scheme.hilbertFunctionOver QK d = Module.finrank S Γ(Fd, ⊤) := by
  dsimp only
  let p := Scheme.projectiveSpaceOverπ n (Spec R)
  let i := principalClosedFiberι (r := ϖ) p
  let pZ := principalClosedFiberToQuotientSpec (r := ϖ) p
  let Qd := Scheme.projectiveSpaceOverTwistModule Q d
  let eC : cokernel
      (Qd.mulByGlobalSection ((baseRingHom p).hom ϖ)) ≅
        (pushforward i).obj ((pullback i).obj Qd) :=
    asIso (principalClosedFiberCokernelToPushforwardPullback (r := ϖ) p Qd)
  exact hflat.hilbertFunctionOver_fractionRing_eq_finrank_principalClosedFiber
    n R Q d ϖ hϖ i pZ Limits.pullback.condition hH1 eC hfinite

/-- If pullback commutes with the chosen twist, the canonical principal-fibre
rank comparison is an equality of the ordinary Hilbert functions on projective
space over the fraction field and over the quotient field. -/
theorem FlatOver.hilbertFunction_fractionRing_eq_principalClosedFiber_of_twistIso
    (n : ℕ) (R : CommRingCat.{u}) [IsDomain R]
    [IsDiscreteValuationRing R]
    (Q : (Scheme.projectiveSpaceOver n (Spec R)).Modules)
    [Q.IsQuasicoherent]
    (hflat : Q.FlatOver (Scheme.projectiveSpaceOverπ n (Spec R)))
    (d : ℤ) (ϖ : R) (hϖ : Irreducible ϖ)
    (hH1 : Subsingleton (((SheafOfModules.toSheaf _).obj
      (Scheme.projectiveSpaceOverTwistModule Q d)).H 1))
    (hfinite :
      let Qd := Scheme.projectiveSpaceOverTwistModule Q d
      letI : Module R Γ(Qd, ⊤) := globalSectionsModule
        (Scheme.projectiveSpaceOverπ n (Spec R)) Qd
      Module.Finite R Γ(Qd, ⊤))
    (eTwist :
      (pullback (Scheme.projectiveSpaceOverMap n
        (Spec.map (principalClosedFiberRingHom ϖ)))).obj
          (Scheme.projectiveSpaceOverTwistModule Q d) ≅
        Scheme.projectiveSpaceOverTwistModule
          ((pullback (Scheme.projectiveSpaceOverMap n
            (Spec.map (principalClosedFiberRingHom ϖ)))).obj Q) d) :
    let j₀ := Spec.map
      (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    let QK := (pullback (Scheme.projectiveSpaceOverMap n j₀)).obj Q
    let q := Spec.map (principalClosedFiberRingHom ϖ)
    let QS := (pullback (Scheme.projectiveSpaceOverMap n q)).obj Q
    Scheme.hilbertFunctionOver QK d = Scheme.hilbertFunctionOver QS d := by
  dsimp only
  let p := Scheme.projectiveSpaceOverπ n (Spec R)
  let i := principalClosedFiberι (r := ϖ) p
  let pZ := principalClosedFiberToQuotientSpec (r := ϖ) p
  let j₀ := Spec.map
    (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  let QK := (pullback (Scheme.projectiveSpaceOverMap n j₀)).obj Q
  let S := principalClosedFiberRing ϖ
  let q := Spec.map (principalClosedFiberRingHom ϖ)
  let QS := (pullback (Scheme.projectiveSpaceOverMap n q)).obj Q
  let Qd := Scheme.projectiveSpaceOverTwistModule Q d
  let Fd := (pullback i).obj Qd
  let QSd := Scheme.projectiveSpaceOverTwistModule QS d
  let _ : (Ideal.span {ϖ} : Ideal R).IsMaximal := by
    rw [← hϖ.maximalIdeal_eq]
    infer_instance
  letI : Field S := Ideal.Quotient.field (Ideal.span {ϖ})
  letI : Module S Γ(Fd, ⊤) := globalSectionsModule pZ Fd
  let NSd := (pullback (Scheme.projectiveSpaceOverMap n q)).obj Qd
  letI : Module S Γ(NSd, ⊤) := globalSectionsModule
    (Scheme.projectiveSpaceOverπ n (Spec S)) NSd
  letI : Module S Γ(QSd, ⊤) := globalSectionsModule
    (Scheme.projectiveSpaceOverπ n (Spec S)) QSd
  have hraw :=
    hflat.hilbertFunctionOver_fractionRing_eq_finrank_canonicalPrincipalClosedFiber
      n R Q d ϖ hϖ hH1 hfinite
  let eRaw :=
    principalClosedFiberGlobalSectionsLinearEquiv_projectiveSpaceBaseChange
      n R ϖ Qd
  let eTwistΓ := globalSectionsLinearEquivOfIso
    (Scheme.projectiveSpaceOverπ n (Spec S)) eTwist
  change Scheme.hilbertFunctionOver QK d = Module.finrank S Γ(QSd, ⊤)
  exact hraw.trans (eRaw.finrank_eq.trans eTwistΓ.finrank_eq)

/-- If pullback to the quotient-ring closed fibre commutes with the chosen
twist, the generic Hilbert function equals the Hilbert function on the
canonical residue-field closed fibre. -/
theorem FlatOver.hilbertFunction_fractionRing_eq_residueField_of_twistIso
    (n : ℕ) (R : CommRingCat.{u}) [IsDomain R]
    [IsDiscreteValuationRing R]
    (Q : (Scheme.projectiveSpaceOver n (Spec R)).Modules)
    [Q.IsQuasicoherent]
    (hflat : Q.FlatOver (Scheme.projectiveSpaceOverπ n (Spec R)))
    (d : ℤ) (ϖ : R) (hϖ : Irreducible ϖ)
    (hH1 : Subsingleton (((SheafOfModules.toSheaf _).obj
      (Scheme.projectiveSpaceOverTwistModule Q d)).H 1))
    (hfinite :
      let Qd := Scheme.projectiveSpaceOverTwistModule Q d
      letI : Module R Γ(Qd, ⊤) := globalSectionsModule
        (Scheme.projectiveSpaceOverπ n (Spec R)) Qd
      Module.Finite R Γ(Qd, ⊤))
    (eTwist :
      (pullback (Scheme.projectiveSpaceOverMap n
        (Spec.map (principalClosedFiberRingHom ϖ)))).obj
          (Scheme.projectiveSpaceOverTwistModule Q d) ≅
        Scheme.projectiveSpaceOverTwistModule
          ((pullback (Scheme.projectiveSpaceOverMap n
            (Spec.map (principalClosedFiberRingHom ϖ)))).obj Q) d) :
    let j₀ := Spec.map
      (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    let QK := (pullback (Scheme.projectiveSpaceOverMap n j₀)).obj Q
    let c := (Spec R).fromSpecResidueField (IsLocalRing.closedPoint R)
    let Qκ := (pullback (Scheme.projectiveSpaceOverMap n c)).obj Q
    Scheme.hilbertFunctionOver QK d = Scheme.hilbertFunctionOver Qκ d := by
  dsimp only
  exact (hflat.hilbertFunction_fractionRing_eq_principalClosedFiber_of_twistIso
    n R Q d ϖ hϖ hH1 hfinite eTwist).trans
      (hilbertFunctionOver_principalClosedFiber_eq_residueField
        (R := R) n Q hϖ d)

/-- Eventual form of the canonical principal-fibre comparison.  This is the
precise numerical consequence of eventual finiteness of `H⁰(Q(d))` and Serre
vanishing for `H¹(Q(d))` needed in DVR constancy arguments. -/
theorem FlatOver.eventually_hilbertFunction_fractionRing_eq_principalClosedFiber_finrank
    (n : ℕ) (R : CommRingCat.{u}) [IsDomain R]
    [IsDiscreteValuationRing R]
    (Q : (Scheme.projectiveSpaceOver n (Spec R)).Modules)
    [Q.IsQuasicoherent]
    (hflat : Q.FlatOver (Scheme.projectiveSpaceOverπ n (Spec R)))
    (ϖ : R) (hϖ : Irreducible ϖ)
    (hH1 : ∀ᶠ d : ℕ in Filter.atTop,
      Subsingleton (((SheafOfModules.toSheaf _).obj
        (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))).H 1))
    (hfinite : ∀ᶠ d : ℕ in Filter.atTop,
      let Qd := Scheme.projectiveSpaceOverTwistModule Q (d : ℤ)
      letI : Module R Γ(Qd, ⊤) := globalSectionsModule
        (Scheme.projectiveSpaceOverπ n (Spec R)) Qd
      Module.Finite R Γ(Qd, ⊤)) :
    let p := Scheme.projectiveSpaceOverπ n (Spec R)
    let i := principalClosedFiberι (r := ϖ) p
    let pZ := principalClosedFiberToQuotientSpec (r := ϖ) p
    let j₀ := Spec.map
      (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    let QK := (pullback (Scheme.projectiveSpaceOverMap n j₀)).obj Q
    let S := principalClosedFiberRing ϖ
    ∀ᶠ d : ℕ in Filter.atTop,
      let Qd := Scheme.projectiveSpaceOverTwistModule Q (d : ℤ)
      let Fd := (pullback i).obj Qd
      letI : Module S Γ(Fd, ⊤) := globalSectionsModule pZ Fd
      Scheme.hilbertFunctionOver QK (d : ℤ) = Module.finrank S Γ(Fd, ⊤) := by
  dsimp only
  filter_upwards [hH1, hfinite] with d hH1d hfinitEd
  exact hflat.hilbertFunctionOver_fractionRing_eq_finrank_canonicalPrincipalClosedFiber
    n R Q (d : ℤ) ϖ hϖ hH1d hfinitEd

/-- Eventual generic-to-closed equality for the ordinary Hilbert functions on
projective space over the fraction field and the scheme-theoretic residue
field, given compatible identifications of the pulled-back twists. -/
theorem FlatOver.eventually_hilbertFunction_fractionRing_eq_residueField_of_twistIso
    (n : ℕ) (R : CommRingCat.{u}) [IsDomain R]
    [IsDiscreteValuationRing R]
    (Q : (Scheme.projectiveSpaceOver n (Spec R)).Modules)
    [Q.IsQuasicoherent]
    (hflat : Q.FlatOver (Scheme.projectiveSpaceOverπ n (Spec R)))
    (ϖ : R) (hϖ : Irreducible ϖ)
    (hH1 : ∀ᶠ d : ℕ in Filter.atTop,
      Subsingleton (((SheafOfModules.toSheaf _).obj
        (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))).H 1))
    (hfinite : ∀ᶠ d : ℕ in Filter.atTop,
      let Qd := Scheme.projectiveSpaceOverTwistModule Q (d : ℤ)
      letI : Module R Γ(Qd, ⊤) := globalSectionsModule
        (Scheme.projectiveSpaceOverπ n (Spec R)) Qd
      Module.Finite R Γ(Qd, ⊤))
    (eTwist : ∀ d : ℕ,
      (pullback (Scheme.projectiveSpaceOverMap n
        (Spec.map (principalClosedFiberRingHom ϖ)))).obj
          (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ)) ≅
        Scheme.projectiveSpaceOverTwistModule
          ((pullback (Scheme.projectiveSpaceOverMap n
            (Spec.map (principalClosedFiberRingHom ϖ)))).obj Q) (d : ℤ)) :
    let j₀ := Spec.map
      (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    let QK := (pullback (Scheme.projectiveSpaceOverMap n j₀)).obj Q
    let c := (Spec R).fromSpecResidueField (IsLocalRing.closedPoint R)
    let Qκ := (pullback (Scheme.projectiveSpaceOverMap n c)).obj Q
    ∀ᶠ d : ℕ in Filter.atTop,
      Scheme.hilbertFunctionOver QK (d : ℤ) =
        Scheme.hilbertFunctionOver Qκ (d : ℤ) := by
  dsimp only
  filter_upwards [hH1, hfinite] with d hH1d hfinitEd
  exact hflat.hilbertFunction_fractionRing_eq_residueField_of_twistIso
    n R Q (d : ℤ) ϖ hϖ hH1d hfinitEd (eTwist d)

/-- Eventual generic-to-closed equality for the ordinary Hilbert functions on
projective space over the fraction field and the scheme-theoretic residue
field. Pullback commutes canonically with twists in the natural degrees used
here. -/
theorem FlatOver.eventually_hilbertFunction_fractionRing_eq_residueField
    (n : ℕ) (R : CommRingCat.{u}) [IsDomain R]
    [IsDiscreteValuationRing R]
    (Q : (Scheme.projectiveSpaceOver n (Spec R)).Modules)
    [Q.IsQuasicoherent]
    (hflat : Q.FlatOver (Scheme.projectiveSpaceOverπ n (Spec R)))
    (ϖ : R) (hϖ : Irreducible ϖ)
    (hH1 : ∀ᶠ d : ℕ in Filter.atTop,
      Subsingleton (((SheafOfModules.toSheaf _).obj
        (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))).H 1))
    (hfinite : ∀ᶠ d : ℕ in Filter.atTop,
      let Qd := Scheme.projectiveSpaceOverTwistModule Q (d : ℤ)
      letI : Module R Γ(Qd, ⊤) := globalSectionsModule
        (Scheme.projectiveSpaceOverπ n (Spec R)) Qd
      Module.Finite R Γ(Qd, ⊤)) :
    let j₀ := Spec.map
      (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    let QK := (pullback (Scheme.projectiveSpaceOverMap n j₀)).obj Q
    let c := (Spec R).fromSpecResidueField (IsLocalRing.closedPoint R)
    let Qκ := (pullback (Scheme.projectiveSpaceOverMap n c)).obj Q
    ∀ᶠ d : ℕ in Filter.atTop,
      Scheme.hilbertFunctionOver QK (d : ℤ) =
        Scheme.hilbertFunctionOver Qκ (d : ℤ) := by
  exact hflat.eventually_hilbertFunction_fractionRing_eq_residueField_of_twistIso
    n R Q ϖ hϖ hH1 hfinite fun d ↦
      Scheme.projectiveSpaceOverTwistModule_pullbackIso_nat
        n (Spec.map (principalClosedFiberRingHom ϖ)) Q d

/-- Eventual finiteness of twisted global sections and vanishing of `H¹`
transport the generic Hilbert polynomial of a flat projective-space family to
its canonical closed residue-field fibre, given compatible identifications of
the pulled-back twists. -/
theorem FlatOver.hasHilbertPolynomialOver_residueField_of_fractionRing_of_twistIso
    (n : ℕ) (R : CommRingCat.{u}) [IsDomain R]
    [IsDiscreteValuationRing R]
    (Q : (Scheme.projectiveSpaceOver n (Spec R)).Modules)
    [Q.IsQuasicoherent]
    (hflat : Q.FlatOver (Scheme.projectiveSpaceOverπ n (Spec R)))
    (ϖ : R) (hϖ : Irreducible ϖ)
    (hH1 : ∀ᶠ d : ℕ in Filter.atTop,
      Subsingleton (((SheafOfModules.toSheaf _).obj
        (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))).H 1))
    (hfinite : ∀ᶠ d : ℕ in Filter.atTop,
      let Qd := Scheme.projectiveSpaceOverTwistModule Q (d : ℤ)
      letI : Module R Γ(Qd, ⊤) := globalSectionsModule
        (Scheme.projectiveSpaceOverπ n (Spec R)) Qd
      Module.Finite R Γ(Qd, ⊤))
    (eTwist : ∀ d : ℕ,
      (pullback (Scheme.projectiveSpaceOverMap n
        (Spec.map (principalClosedFiberRingHom ϖ)))).obj
          (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ)) ≅
        Scheme.projectiveSpaceOverTwistModule
          ((pullback (Scheme.projectiveSpaceOverMap n
            (Spec.map (principalClosedFiberRingHom ϖ)))).obj Q) (d : ℤ))
    (P : Polynomial ℚ)
    (hgeneric :
      let j₀ := Spec.map
        (CommRingCat.ofHom (algebraMap R (FractionRing R)))
      let QK := (pullback (Scheme.projectiveSpaceOverMap n j₀)).obj Q
      Scheme.HasHilbertPolynomialOver QK P) :
    let c := (Spec R).fromSpecResidueField (IsLocalRing.closedPoint R)
    let Qκ := (pullback (Scheme.projectiveSpaceOverMap n c)).obj Q
    Scheme.HasHilbertPolynomialOver Qκ P := by
  dsimp only at hgeneric ⊢
  have heq := hflat.eventually_hilbertFunction_fractionRing_eq_residueField_of_twistIso
    n R Q ϖ hϖ hH1 hfinite eTwist
  filter_upwards [hgeneric, heq] with d hd heqd
  rw [← heqd]
  exact hd

/-- Eventual finiteness of twisted global sections and vanishing of `H¹`
transport the generic Hilbert polynomial of a flat projective-space family to
its canonical closed residue-field fibre. -/
theorem FlatOver.hasHilbertPolynomialOver_residueField_of_fractionRing
    (n : ℕ) (R : CommRingCat.{u}) [IsDomain R]
    [IsDiscreteValuationRing R]
    (Q : (Scheme.projectiveSpaceOver n (Spec R)).Modules)
    [Q.IsQuasicoherent]
    (hflat : Q.FlatOver (Scheme.projectiveSpaceOverπ n (Spec R)))
    (ϖ : R) (hϖ : Irreducible ϖ)
    (hH1 : ∀ᶠ d : ℕ in Filter.atTop,
      Subsingleton (((SheafOfModules.toSheaf _).obj
        (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))).H 1))
    (hfinite : ∀ᶠ d : ℕ in Filter.atTop,
      let Qd := Scheme.projectiveSpaceOverTwistModule Q (d : ℤ)
      letI : Module R Γ(Qd, ⊤) := globalSectionsModule
        (Scheme.projectiveSpaceOverπ n (Spec R)) Qd
      Module.Finite R Γ(Qd, ⊤))
    (P : Polynomial ℚ)
    (hgeneric :
      let j₀ := Spec.map
        (CommRingCat.ofHom (algebraMap R (FractionRing R)))
      let QK := (pullback (Scheme.projectiveSpaceOverMap n j₀)).obj Q
      Scheme.HasHilbertPolynomialOver QK P) :
    let c := (Spec R).fromSpecResidueField (IsLocalRing.closedPoint R)
    let Qκ := (pullback (Scheme.projectiveSpaceOverMap n c)).obj Q
    Scheme.HasHilbertPolynomialOver Qκ P := by
  apply hflat.hasHilbertPolynomialOver_residueField_of_fractionRing_of_twistIso
    n R Q ϖ hϖ hH1 hfinite
      (fun d ↦ Scheme.projectiveSpaceOverTwistModule_pullbackIso_nat
        n (Spec.map (principalClosedFiberRingHom ϖ)) Q d)
      P hgeneric

end AlgebraicGeometry.Scheme.Modules

end
