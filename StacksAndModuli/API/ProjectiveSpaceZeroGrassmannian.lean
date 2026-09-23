module

public import StacksAndModuli.API.ProjectiveSpaceZeroLocalCohomology
public import StacksAndModuli.API.HilbertQuotientBridge
public import StacksAndModuli.API.ProjectiveSpaceTwistedFree
public import StacksAndModuli.«Section2.2-Grassmannian».«part2.2.3-relative-grassmannians»

/-!
# Projective zero-space and the Grassmannian reduction

Relative projective zero-space is canonically isomorphic to its base, every twist on it
is trivial, and consequently every finite twisted-free ambient sheaf is a canonical free
sheaf.  The Hilbert function of a module on projective zero-space is therefore constant;
the constant Hilbert-polynomial condition is exactly a statement about dimensions of
global sections after field-valued base change.

The final theorem records the exact remaining functorial comparison needed to identify
the fixed-polynomial Quot functor with a relative Grassmannian.  Once that natural
isomorphism is supplied, the existing Grassmannian theorem gives a strongly projective
representative without a noetherian hypothesis on the base.

Main declarations:

* `AlgebraicGeometry.Scheme.projectiveSpaceOverZeroIso`;
* `AlgebraicGeometry.Scheme.projectiveSpaceOverZeroTwistIsoUnit`;
* `AlgebraicGeometry.Scheme.projectiveSpaceOverZeroTwistedFreeIsoFree`;
* `AlgebraicGeometry.Scheme.hasFiberwiseHilbertPolynomial_zero_C_iff`;
* `AlgebraicGeometry.Scheme.
    exists_quotFunctorP_zero_C_representableBy_isStronglyProjective_of_iso`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ProjectiveSpectrum HomogeneousLocalization

universe u

namespace AlgebraicGeometry.Scheme

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Absolute projective zero-space is the terminal spectrum. -/
noncomputable def projectiveSpaceZeroIsoSpecULiftZ :
    projectiveSpace.{u} 0 ≅ Spec (CommRingCat.of (ULift.{u} ℤ)) := by
  let G := MvPolynomial.homogeneousSubmodule (Fin 1) (ULift.{u} ℤ)
  let i : Fin 1 := 0
  let U := Proj.polynomialStandardOpen 0 (ULift.{u} ℤ) i
  have hU : U = ⊤ := by
    apply top_unique
    rw [← Proj.iSup_polynomialStandardOpen_eq_top 0 (ULift.{u} ℤ)]
    refine iSup_le fun j ↦ ?_
    have hji : j = i := by
      apply Fin.ext
      omega
    rw [hji]
  let eTop : U.toScheme ≅ Proj G :=
    (Proj G).isoOfEq hU ≪≫ Scheme.topIso (Proj G)
  let eBasic : U.toScheme ≅ Spec (.of (Away G (MvPolynomial.X i))) :=
    Proj.basicOpenIsoSpec G (MvPolynomial.X i)
      (MvPolynomial.X_mem_homogeneousSubmodule_one 0 (ULift.{u} ℤ) i) Nat.one_pos
  letI : IsEmpty {j : Fin 1 // j ≠ i} :=
    ⟨fun j ↦ j.2 (Subsingleton.elim j.1 i)⟩
  let eRing : Away G (MvPolynomial.X i) ≃+* ULift.{u} ℤ :=
    (Proj.projectiveChartPolynomialEquivAway (Fin 1) i (ULift.{u} ℤ)).symm.trans
      (MvPolynomial.isEmptyRingEquiv (ULift.{u} ℤ) {j : Fin 1 // j ≠ i})
  exact eTop.symm ≪≫ eBasic ≪≫
    Scheme.Spec.mapIso eRing.symm.toCommRingCatIso.op

/-- Relative projective zero-space is canonically isomorphic to its base. -/
noncomputable def projectiveSpaceOverZeroIso (S : Scheme.{u}) :
    projectiveSpaceOver 0 S ≅ S := by
  have habs : IsIso
      (specULiftZIsTerminal.from (projectiveSpace.{u} 0)) := by
    rw [show specULiftZIsTerminal.from (projectiveSpace.{u} 0) =
        (projectiveSpaceZeroIsoSpecULiftZ.{u}).hom from
      specULiftZIsTerminal.hom_ext _ _]
    infer_instance
  letI : IsIso (specULiftZIsTerminal.from (projectiveSpace.{u} 0)) := habs
  have hπ : IsIso (pullback.fst
      (specULiftZIsTerminal.from S)
      (specULiftZIsTerminal.from (projectiveSpace.{u} 0))) :=
    pullback_fst_iso_of_right_iso _ _
  letI : IsIso (projectiveSpaceOverπ 0 S) := hπ
  exact asIso (projectiveSpaceOverπ 0 S)

@[simp]
theorem projectiveSpaceOverZeroIso_hom (S : Scheme.{u}) :
    (projectiveSpaceOverZeroIso S).hom = projectiveSpaceOverπ 0 S := by
  unfold projectiveSpaceOverZeroIso
  rfl

@[reassoc]
theorem projectiveSpaceOverZeroIso_naturality {S T : Scheme.{u}} (g : T ⟶ S) :
    projectiveSpaceOverMap 0 g ≫ (projectiveSpaceOverZeroIso S).hom =
      (projectiveSpaceOverZeroIso T).hom ≫ g := by
  rw [projectiveSpaceOverZeroIso_hom,
    projectiveSpaceOverZeroIso_hom, projectiveSpaceOverMap_π]

lemma projectiveSpaceZero_standardOpen_eq_top :
    Proj.polynomialStandardOpen 0 (ULift.{u} ℤ) (0 : Fin 1) = ⊤ := by
  apply top_unique
  rw [← Proj.iSup_polynomialStandardOpen_eq_top 0 (ULift.{u} ℤ)]
  refine iSup_le fun j ↦ ?_
  have hj : j = (0 : Fin 1) := by
    apply Fin.ext
    omega
  rw [hj]

/-- Every twisting sheaf on relative projective zero-space is trivial. -/
noncomputable def projectiveSpaceOverZeroTwistIsoUnit (S : Scheme.{u}) (d : ℤ) :
    projectiveSpaceOverTwist 0 S d ≅
      SheafOfModules.unit (projectiveSpaceOver 0 S).ringCatSheaf := by
  let G := MvPolynomial.homogeneousSubmodule (Fin 1) (ULift.{u} ℤ)
  let X := projectiveSpaceOver 0 S
  let g : X ⟶ Proj G := Limits.pullback.snd
    (specULiftZIsTerminal.from S)
    (specULiftZIsTerminal.from (projectiveSpace 0))
  let i : Fin 1 := 0
  let U := g ⁻¹ᵁ Proj.basicOpen G (MvPolynomial.X i)
  have hU : U = ⊤ := by
    dsimp only [U]
    have hbasic : Proj.basicOpen G (MvPolynomial.X i) = ⊤ := by
      exact projectiveSpaceZero_standardOpen_eq_top
    rw [hbasic]
    simp
  let eLocal := Twist.restrictPullbackTwistIsoUnitOfHom g d
    (MvPolynomial.X_mem_homogeneousSubmodule_one 0 (ULift.{u} ℤ) i)
  have hU' : g ⁻¹ᵁ Proj.basicOpen G (MvPolynomial.X i) = ⊤ := hU
  rw [hU'] at eLocal
  let eTop := Scheme.topIso X
  let L := projectiveSpaceOverTwist 0 S d
  let eSource :
      (Modules.pullback eTop.inv).obj
          ((Modules.restrictFunctor (⊤ : X.Opens).ι).obj L) ≅ L :=
    (Modules.pullback eTop.inv).mapIso
        ((Modules.restrictFunctorIsoPullback (⊤ : X.Opens).ι).app L) ≪≫
      (Modules.pullbackComp eTop.inv (⊤ : X.Opens).ι).app L ≪≫
      (Modules.pullbackCongr (Scheme.toIso_inv_ι X)).app L ≪≫
      (Modules.pullbackId X).app L
  letI : IsIso
      (SheafOfModules.pullbackObjUnitToUnit eTop.inv.toRingCatSheafHom) :=
    isIso_pullbackObjUnitToUnit eTop.inv
  exact eSource.symm ≪≫
    (Modules.pullback eTop.inv).mapIso eLocal ≪≫
    asIso (SheafOfModules.pullbackObjUnitToUnit eTop.inv.toRingCatSheafHom)

/-- On relative projective zero-space, twisting a module does nothing. -/
noncomputable def projectiveSpaceOverZeroTwistModuleIso
    {S : Scheme.{u}} (Q : (projectiveSpaceOver 0 S).Modules) (d : ℤ) :
    projectiveSpaceOverTwistModule Q d ≅ Q :=
  Modules.tensorRightIso Q (projectiveSpaceOverZeroTwistIsoUnit S d) ≪≫
    Modules.tensorUnitIso Q

/-- The twisted-free ambient sheaf on projective zero-space is the canonical free
sheaf; in particular it is independent of the twisting degree. -/
noncomputable def projectiveSpaceOverZeroTwistedFreeIsoFree
    (S : Scheme.{u}) (l : ℤ) (r : ℕ) :
    projectiveSpaceOverTwistedFree 0 S l r ≅
      SheafOfModules.free
        (R := (projectiveSpaceOver 0 S).ringCatSheaf) (ULift.{u} (Fin r)) := by
  unfold projectiveSpaceOverTwistedFree SheafOfModules.free
  exact Sigma.mapIso (fun _ : ULift.{u} (Fin r) ↦
    projectiveSpaceOverZeroTwistIsoUnit S (-l))

/-- The Hilbert function on projective zero-space is the constant dimension of
the untwisted global sections. -/
theorem hilbertFunctionOver_zero_eq_finrank
    {R : CommRingCat.{u}} (Q : (projectiveSpaceOver 0 (Spec R)).Modules) (d : ℤ) :
    letI := Modules.globalSectionsModule (projectiveSpaceOverπ 0 (Spec R)) Q
    hilbertFunctionOver Q d = Module.finrank R Γ(Q, ⊤) := by
  let p := projectiveSpaceOverπ 0 (Spec R)
  let Qd := projectiveSpaceOverTwistModule Q d
  letI := Modules.globalSectionsModule p Qd
  letI := Modules.globalSectionsModule p Q
  change Module.finrank R Γ(Qd, ⊤) = Module.finrank R Γ(Q, ⊤)
  exact (Modules.globalSectionsLinearEquivOfIso p
    (projectiveSpaceOverZeroTwistModuleIso Q d)).finrank_eq

/-- A sheaf on projective zero-space has constant Hilbert polynomial `q` exactly
when its global sections have dimension `q`. -/
theorem hasHilbertPolynomialOver_zero_C_iff
    {R : CommRingCat.{u}}
    (Q : (projectiveSpaceOver 0 (Spec R)).Modules) (q : ℕ) :
    HasHilbertPolynomialOver Q (Polynomial.C (q : ℚ)) ↔
      letI := Modules.globalSectionsModule
        (projectiveSpaceOverπ 0 (Spec R)) Q
      Module.finrank R Γ(Q, ⊤) = q := by
  let p := projectiveSpaceOverπ 0 (Spec R)
  letI := Modules.globalSectionsModule p Q
  constructor
  · intro h
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h
    have hdim := hN N le_rfl
    rw [hilbertFunctionOver_zero_eq_finrank, Polynomial.eval_C] at hdim
    exact_mod_cast hdim
  · intro hdim
    filter_upwards [] with d
    rw [hilbertFunctionOver_zero_eq_finrank, Polynomial.eval_C, hdim]

/-- For a family on projective zero-space, the constant fiberwise Hilbert-polynomial
condition is exactly constant dimension `q` after every field-valued base change. -/
theorem hasFiberwiseHilbertPolynomial_zero_C_iff
    {S : Scheme.{u}} (Q : (projectiveSpaceOver 0 S).Modules) (q : ℕ) :
    HasFiberwiseHilbertPolynomial Q (Polynomial.C (q : ℚ)) ↔
      ∀ (K : CommRingCat.{u}) (_ : IsField K) (s : Spec K ⟶ S),
        let Qs := (Modules.pullback (projectiveSpaceOverMap 0 s)).obj Q
        letI := Modules.globalSectionsModule
          (projectiveSpaceOverπ 0 (Spec K)) Qs
        Module.finrank K Γ(Qs, ⊤) = q := by
  constructor
  · intro h K hK s
    exact (hasHilbertPolynomialOver_zero_C_iff _ q).mp (h K hK s)
  · intro h K hK s
    exact (hasHilbertPolynomialOver_zero_C_iff _ q).mpr (h K hK s)

/-- A quasicoherent finitely presented sheaf which is flat over the identity is
finite locally free. This is the property conversion needed when a zero-space Quot
family is transported back to its parameter scheme. -/
theorem Modules.isFiniteLocallyFree_of_isFinitePresentation_flatOver_id
    {T : Scheme.{u}} (N : T.Modules) [N.IsQuasicoherent]
    (hfp : N.IsFinitePresentation) (hflat : N.FlatOver (𝟙 T)) :
    IsFiniteLocallyFree N := by
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ x) isOpen_univ
  let A : T.affineOpens := ⟨U, hU⟩
  have hfpA : Module.FinitePresentation Γ(T, A.1) Γ(N, A.1) :=
    (Modules.isFinitePresentation_iff_sections_affineOpens N).mp hfp A
  letI : Module.FinitePresentation Γ(T, A.1) Γ(N, A.1) := hfpA
  have hflatA : Module.Flat Γ(T, A.1) Γ(N, A.1) := by
    let hAA : A.1 ≤ (𝟙 T) ⁻¹ᵁ A.1 := by simp
    let a : Γ(T, A.1) →+* Γ(T, A.1) :=
      (Scheme.Hom.appLE (𝟙 T) A.1 A.1 hAA).hom
    have ha : a = RingHom.id Γ(T, A.1) := by
      ext z
      change (T.presheaf.map (𝟙 (Opposite.op A.1))).hom z = z
      rw [T.presheaf.map_id]
      rfl
    have hf :
        letI := Module.compHom Γ(N, A.1) a
        Module.Flat Γ(T, A.1) Γ(N, A.1) :=
      hflat A A hAA
    exact Module.Flat.compHom_congr a (RingHom.id Γ(T, A.1)) ha hf
  letI : Module.Flat Γ(T, A.1) Γ(N, A.1) := hflatA
  exact ⟨A, hxU, inferInstance,
    Module.Flat.projective_of_finitePresentation⟩

/-- A residue-fiber dimension calculation upgrades the preceding finite-local-freeness
criterion to fixed rank.  This isolates the algebraic rank obligation in the
zero-space Quot-to-Grassmannian comparison. -/
theorem Modules.isProjectiveOfRank_of_isFinitePresentation_flatOver_id
    {T : Scheme.{u}} (N : T.Modules) [N.IsQuasicoherent] (q : ℕ)
    (hfp : N.IsFinitePresentation) (hflat : N.FlatOver (𝟙 T))
    (hrank : ∀ (U : T.affineOpens) (p : PrimeSpectrum Γ(T, U.1)),
      Module.finrank p.asIdeal.ResidueField
        (p.asIdeal.Fiber Γ(N, U.1)) = q) :
    IsProjectiveOfRank q N := by
  have hloc : IsFiniteLocallyFree N :=
    Modules.isFiniteLocallyFree_of_isFinitePresentation_flatOver_id N hfp hflat
  intro x
  obtain ⟨U, hxU, hfin, hproj⟩ := hloc x
  refine ⟨U, hxU, hfin, hproj, fun p ↦ ?_⟩
  rw [← p.asIdeal.finrank_fiber_eq_rankAtStalk]
  exact hrank U p

/-- Exact Grassmannian reduction for the constant-polynomial zero-dimensional Quot
functor. Once the comparison natural isomorphism is supplied, the usual relative
Grassmannian gives a strongly projective representative, without a noetherian
hypothesis on the base. -/
theorem exists_quotFunctorP_zero_C_representableBy_isStronglyProjective_of_iso
    (S : Scheme.{u}) (l : ℤ) (r q : ℕ)
    (e : quotFunctorP (projectiveSpaceOverTwistedFree 0 S l r)
        (Polynomial.C (q : ℚ)) ≅
      Modules.grassmannianOverFunctor q
        (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin r)))) :
    ∃ G : Over S,
      Nonempty ((quotFunctorP (projectiveSpaceOverTwistedFree 0 S l r)
        (Polynomial.C (q : ℚ))).RepresentableBy G) ∧
      IsStronglyProjective G.hom := by
  obtain ⟨G, ⟨hG⟩, hproj⟩ :=
    exists_free_grassmannianOverFunctor_representableBy S q r
  exact ⟨G, ⟨hG.ofIso e.symm⟩, hproj⟩

end AlgebraicGeometry.Scheme

end
