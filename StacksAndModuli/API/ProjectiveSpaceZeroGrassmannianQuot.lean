module

public import StacksAndModuli.API.ProjectiveSpaceZeroQuotGrassmannian
public import StacksAndModuli.API.FlatOverDescent
public import StacksAndModuli.API.QuasicoherentVectorBundles
public import StacksAndModuli.API.ModulesPullbackCoherence

/-!
# Grassmannian quotients as Quot data on projective zero-space

Supporting API with no Stacks Project counterpart.

`API/ProjectiveSpaceZeroQuotGrassmannian.lean` transports a twisted-free Quot
presentation on relative projective zero-space to a relative Grassmannian quotient.
This file constructs the map in the other direction: a rank-`q` vector-bundle quotient
of the free rank-`r` sheaf, pulled back to the fibre product `T ×ₛ ℙ⁰ₛ`, is a
twisted-free Quot presentation with constant fibrewise Hilbert polynomial `C q`
(`PullbackQuotient.toQuotientPullbackDataZero`,
`toQuotientPullbackDataZero_hasFiberwiseHilbertPolynomial`).  The construction respects
the equivalence relations on both sides (`toQuotientPullbackDataZero_r`) and commutes
with base change in the parameter object (`toQuotientPullbackDataZero_pullback_r`),
which is the statement making the induced map of functors natural; its coherence core
is `Modules.pullback_theta_coherence_iso`.

Supporting lemmas on finite locally free sheaves (affine sections, flatness along a
flat morphism) and on `IsProjectiveOfRank` over a field open the file.

Main declarations:
- `Modules.PullbackQuotient.toQuotientPullbackDataZero`;
- `Modules.PullbackQuotient.toQuotientPullbackDataZero_hasFiberwiseHilbertPolynomial`;
- `Modules.PullbackQuotient.toQuotientPullbackDataZero_r`;
- `Modules.PullbackQuotient.toQuotientPullbackDataZero_pullback_r`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

/-- Sections of a finite locally free quasicoherent sheaf on an affine open form a
finite projective module. -/
lemma IsFiniteLocallyFree.sections_finite_projective_affine
    {X : Scheme.{u}} {M : X.Modules} [M.IsQuasicoherent]
    (hM : IsFiniteLocallyFree M) (U : X.affineOpens) :
    Module.Finite Γ(X, U.1) Γ(M, U.1) ∧
      Module.Projective Γ(X, U.1) Γ(M, U.1) := by
  let j := U.2.fromSpec
  let N := (Modules.pullback j).obj M
  have hN : IsFiniteLocallyFree N := hM.pullback j
  have hcoord := moduleSpecΓFunctor_finite_projective_of_isFiniteLocallyFree N hN
  have htop := AlgebraicGeometry.moduleSpecΓFunctor_finite_projective_top N
    hcoord.1 hcoord.2
  have hsections := sections_finite_projective_of_pullback_openImmersion
    j M (⊤ : (Spec (.of Γ(X, U.1))).Opens) htop.1 htop.2
  have himage : j ''ᵁ (⊤ : (Spec (.of Γ(X, U.1))).Opens) = U.1 := by
    rw [Scheme.Hom.image_top_eq_opensRange, U.2.opensRange_fromSpec]
  rw [himage] at hsections
  exact hsections

/-- A finite locally free quasicoherent sheaf is flat over any flat morphism. -/
lemma IsFiniteLocallyFree.flatOver_of_flat
    {X Y : Scheme.{u}} {M : X.Modules} [M.IsQuasicoherent]
    (hM : IsFiniteLocallyFree M) (f : X ⟶ Y) [Flat f] :
    M.FlatOver f := by
  intro U V hUV
  change
    letI := Module.compHom Γ(M, U.1) (f.appLE V.1 U.1 hUV).hom
    Module.Flat Γ(Y, V.1) Γ(M, U.1)
  let a : Γ(Y, V.1) →+* Γ(X, U.1) := (f.appLE V.1 U.1 hUV).hom
  have ha : a.Flat := f.flat_appLE V.2 U.2 hUV
  have hproj : Module.Projective Γ(X, U.1) Γ(M, U.1) :=
    (hM.sections_finite_projective_affine U).2
  letI : Algebra Γ(Y, V.1) Γ(X, U.1) := a.toAlgebra
  letI : Module.Flat Γ(Y, V.1) Γ(X, U.1) := ha
  letI : Module.Projective Γ(X, U.1) Γ(M, U.1) := hproj
  letI : Module.Flat Γ(X, U.1) Γ(M, U.1) := inferInstance
  letI : Module Γ(Y, V.1) Γ(M, U.1) := Module.compHom Γ(M, U.1) a
  letI : IsScalarTower Γ(Y, V.1) Γ(X, U.1) Γ(M, U.1) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  exact Module.Flat.trans Γ(Y, V.1) Γ(X, U.1) Γ(M, U.1)

/-- Over the spectrum of a field, a rank-`q` projective sheaf has `q`-dimensional
global sections (module form). -/
lemma IsProjectiveOfRank.finrank_moduleSpecΓFunctor_of_isField
    {K : CommRingCat.{u}} (hK : IsField K) {q : ℕ}
    {M : (Spec K).Modules} (hM : IsProjectiveOfRank q M) :
    Module.finrank K (moduleSpecΓFunctor.obj M) = q := by
  letI : Field K := hK.toField
  let x : Spec K := ⟨⊥, Ideal.isPrime_bot⟩
  obtain ⟨U, hxU, hfin, hproj, hrank⟩ := hM x
  have hU : U.1 = ⊤ := by
    refine top_unique ?_
    rintro y -
    have hy : y = x := by
      apply PrimeSpectrum.ext
      exact y.asIdeal.eq_bot_of_prime
    subst y
    exact hxU
  rw [hU] at hfin hproj hrank
  obtain ⟨hfin', hproj', hrank'⟩ :=
    moduleSpecΓFunctor_finite_projective_rank_of_top M hfin hproj hrank
  let p : PrimeSpectrum K := ⟨⊥, Ideal.isPrime_bot⟩
  let _ := p.nontrivial
  simpa [Module.rankAtStalk_eq_finrank_of_free] using hrank' p

/-- Over the spectrum of a field, a rank-`q` projective sheaf has `q`-dimensional
global sections. -/
lemma IsProjectiveOfRank.finrank_globalSections_spec_of_isField
    {K : CommRingCat.{u}} (hK : IsField K) {q : ℕ}
    {M : (Spec K).Modules} (hM : IsProjectiveOfRank q M) :
    letI := globalSectionsModule (𝟙 (Spec K)) M
    Module.finrank K Γ(M, ⊤) = q := by
  change Module.finrank K (moduleSpecΓFunctor.obj M) = q
  exact hM.finrank_moduleSpecΓFunctor_of_isField hK

/-- The pullback of a rank-`q` vector-bundle quotient to relative projective
zero-space has constant fibrewise Hilbert polynomial `q`. -/
theorem IsProjectiveOfRank.pullback_projectiveSpaceOverZero_hasFiberwise
    {T : Scheme.{u}} {Q : T.Modules} [Q.IsQuasicoherent] {q : ℕ}
    (hQ : IsProjectiveOfRank q Q) :
    Scheme.HasFiberwiseHilbertPolynomial
      ((Modules.pullback (Scheme.projectiveSpaceOverπ 0 T)).obj Q)
      (Polynomial.C (q : ℚ)) := by
  rw [Scheme.hasFiberwiseHilbertPolynomial_zero_C_iff]
  intro K hK s
  letI : Field K := hK.toField
  let pT := Scheme.projectiveSpaceOverπ 0 T
  let pK := Scheme.projectiveSpaceOverπ 0 (Spec K)
  let g := Scheme.projectiveSpaceOverMap 0 s
  let Qs := (Modules.pullback s).obj Q
  let N := (Modules.pullback pK).obj Qs
  let F := (Modules.pullback g).obj ((Modules.pullback pT).obj Q)
  have hQs : IsProjectiveOfRank q Qs := hQ.pullback s
  let e : F ≅ N :=
    (Modules.pullbackComp g pT).app Q ≪≫
      (Modules.pullbackCongr (Scheme.projectiveSpaceOverMap_π 0 s)).app Q ≪≫
      ((Modules.pullbackComp pK s).app Q).symm
  have hpKIso : IsIso pK := by
    change IsIso (Scheme.projectiveSpaceOverπ 0 (Spec K))
    rw [← Scheme.projectiveSpaceOverZeroIso_hom (Spec K)]
    infer_instance
  letI : IsIso pK := hpKIso
  letI : Module K Γ(Qs, ⊤) := globalSectionsModule (𝟙 (Spec K)) Qs
  have hQsfin : Module.finrank K Γ(Qs, ⊤) = q :=
    hQs.finrank_globalSections_spec_of_isField hK
  let moduleNComp : Module K Γ(N, ⊤) :=
    globalSectionsModule (pK ≫ 𝟙 (Spec K)) N
  letI : Module K Γ(N, ⊤) := moduleNComp
  let E := pullbackGlobalSectionsViaIsoLinearEquiv
    pK (𝟙 (Spec K)) Qs (Iso.refl N)
  have hNcomp : Module.finrank K Γ(N, ⊤) = q :=
    E.finrank_eq.symm.trans hQsfin
  let moduleN : Module K Γ(N, ⊤) := globalSectionsModule pK N
  have hmoduleN : moduleNComp = moduleN := by
    dsimp only [moduleNComp, moduleN]
    rw [Category.comp_id]
  have hN : @Module.finrank K Γ(N, ⊤) _ _ moduleN = q := by
    exact (congrArg
      (fun inst : Module K Γ(N, ⊤) ↦ @Module.finrank K Γ(N, ⊤) _ _ inst)
      hmoduleN.symm).trans hNcomp
  letI : Module K Γ(N, ⊤) := moduleN
  letI : Module K Γ(F, ⊤) := globalSectionsModule pK F
  exact (globalSectionsLinearEquivOfIso pK e).finrank_eq.trans hN

namespace PullbackQuotient

variable {S : Scheme.{u}} {q r : ℕ} {l : ℤ}
  {V : S.Modules} {T : Over S}

abbrev zeroFreeAmbient (S : Scheme.{u}) (r : ℕ) : S.Modules :=
  SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin r))

/-- On projective zero-space every twist is trivial, so the finite twisted-free
ambient sheaf is the pullback of the free rank-`r` sheaf on the base. -/
noncomputable def zeroTwistedFreeToPullbackFreeIso :
    Scheme.projectiveSpaceOverTwistedFree 0 S l r ≅
      (Modules.pullback (Scheme.projectiveSpaceOverπ 0 S)).obj
        (zeroFreeAmbient S r) :=
  Scheme.projectiveSpaceOverZeroTwistedFreeIsoFree S l r ≪≫
    (Modules.pullbackFreeIso (Scheme.projectiveSpaceOverπ 0 S)
      (ULift.{u} (Fin r))).symm

/-- The ambient comparison for the Grassmannian-to-Quot construction: the twisted-free
ambient sheaf pulled back to the fibre product agrees with the two-stage pullback of
the free rank-`r` sheaf on the base. -/
noncomputable def toQuotientPullbackDataZeroAmbientIso :
    (Modules.pullback
      ((Over.pullback (Scheme.projectiveSpaceOverπ 0 S)).obj T).hom).obj
        (Scheme.projectiveSpaceOverTwistedFree 0 S l r) ≅
      (Modules.pullback
        (Limits.pullback.fst T.hom (Scheme.projectiveSpaceOverπ 0 S))).obj
        ((Modules.pullback T.hom).obj (zeroFreeAmbient S r)) :=
  let snd := ((Over.pullback (Scheme.projectiveSpaceOverπ 0 S)).obj T).hom
  let fst := Limits.pullback.fst T.hom (Scheme.projectiveSpaceOverπ 0 S)
  (Modules.pullback snd).mapIso
      (zeroTwistedFreeToPullbackFreeIso (S := S) (l := l) (r := r)) ≪≫
    (Modules.pullbackComp snd (Scheme.projectiveSpaceOverπ 0 S)).app
      (zeroFreeAmbient S r) ≪≫
    (Modules.pullbackCongr
      (Limits.pullback.condition :
        fst ≫ T.hom = snd ≫ Scheme.projectiveSpaceOverπ 0 S).symm).app
      (zeroFreeAmbient S r) ≪≫
    ((Modules.pullbackComp fst T.hom).app (zeroFreeAmbient S r)).symm

/-- A rank-`q` vector-bundle quotient of the free rank-`r` sheaf determines a
twisted-free Quot presentation on relative projective zero-space, by pulling back to
the fibre product `T ×ₛ ℙ⁰ₛ`. -/
noncomputable def toQuotientPullbackDataZero
    (x : PullbackQuotient q (zeroFreeAmbient S r) T) :
    QuotientPullbackData
      (Scheme.projectiveSpaceOverTwistedFree 0 S l r)
      (Scheme.projectiveSpaceOverπ 0 S) T where
  Q := (Modules.pullback (Limits.pullback.fst T.hom
    (Scheme.projectiveSpaceOverπ 0 S))).obj x.Q
  isQuasicoherent := by
    letI : x.Q.IsQuasicoherent := x.isQuasicoherent
    infer_instance
  isFinitePresentation := by
    letI : x.Q.IsQuasicoherent := x.isQuasicoherent
    letI : x.Q.IsFinitePresentation := x.isFinitePresentation
    infer_instance
  flatOver := by
    letI : x.Q.IsQuasicoherent := x.isQuasicoherent
    let fst := Limits.pullback.fst T.hom (Scheme.projectiveSpaceOverπ 0 S)
    letI : IsIso (Scheme.projectiveSpaceOverπ 0 S) := by
      rw [← Scheme.projectiveSpaceOverZeroIso_hom S]
      infer_instance
    letI : IsIso fst := pullback_fst_iso_of_right_iso _ _
    have hrank : IsProjectiveOfRank q ((Modules.pullback fst).obj x.Q) :=
      x.isProjectiveOfRank.pullback fst
    exact hrank.isFiniteLocallyFree.flatOver_of_flat fst
  π := (toQuotientPullbackDataZeroAmbientIso
    (S := S) (T := T) (l := l) (r := r)).hom ≫
      (Modules.pullback (Limits.pullback.fst T.hom
        (Scheme.projectiveSpaceOverπ 0 S))).map x.π
  epi := by
    letI : x.Q.IsQuasicoherent := x.isQuasicoherent
    letI : Epi x.π := x.epi
    infer_instance

/-- The quotient sheaf of the associated Quot presentation, normalized onto `ℙ⁰_T`,
is the pullback of the vector-bundle quotient. -/
noncomputable def toQuotientPullbackDataZero_quotDataIso
    (x : PullbackQuotient q (zeroFreeAmbient S r) T) :
    quotDataOnProjectiveSpace
        (Scheme.projectiveSpaceOverTwistedFree 0 S l r)
        (x.toQuotientPullbackDataZero (l := l)) ≅
      (Modules.pullback (Scheme.projectiveSpaceOverπ 0 T.left)).obj x.Q :=
  (Modules.pullbackComp
    (Scheme.projectiveSpaceOverBaseChangeIso 0 T.hom).inv
    (Limits.pullback.fst T.hom (Scheme.projectiveSpaceOverπ 0 S))).app x.Q ≪≫
  (Modules.pullbackCongr
    (Scheme.projectiveSpaceOverBaseChangeIso_inv_fst 0 T.hom)).app x.Q

/-- The Quot presentation associated to a rank-`q` vector-bundle quotient has constant
fibrewise Hilbert polynomial `C q`. -/
theorem toQuotientPullbackDataZero_hasFiberwiseHilbertPolynomial
    (x : PullbackQuotient q (zeroFreeAmbient S r) T) :
    (x.toQuotientPullbackDataZero (l := l)).HasFiberwiseHilbertPolynomial
      (Polynomial.C (q : ℚ)) := by
  letI : x.Q.IsQuasicoherent := x.isQuasicoherent
  apply Scheme.HasFiberwiseHilbertPolynomial.of_iso
    (x.toQuotientPullbackDataZero_quotDataIso (l := l)).symm
  exact x.isProjectiveOfRank.pullback_projectiveSpaceOverZero_hasFiberwise

/-- The Grassmannian-to-Quot construction respects the equivalence relations on both
kinds of quotient presentations. -/
theorem toQuotientPullbackDataZero_r
    {x y : PullbackQuotient q (zeroFreeAmbient S r) T}
    (hxy : (PullbackQuotient.setoid q (zeroFreeAmbient S r) T).r x y) :
    (QuotientPullbackData.setoid
      (Scheme.projectiveSpaceOverTwistedFree 0 S l r)
      (Scheme.projectiveSpaceOverπ 0 S) T).r
        (x.toQuotientPullbackDataZero (l := l))
        (y.toQuotientPullbackDataZero (l := l)) := by
  obtain ⟨e, he⟩ := hxy
  refine ⟨(Modules.pullback (Limits.pullback.fst T.hom
    (Scheme.projectiveSpaceOverπ 0 S))).mapIso e, ?_⟩
  simp only [toQuotientPullbackDataZero, Functor.mapIso_hom,
    Category.assoc, ← Functor.map_comp, he]

/-- The comparison between the Quot data of a pulled-back vector-bundle quotient and
the pullback of its Quot data. -/
noncomputable def toQuotientPullbackDataZero_pullbackIso
    {T' : Over S} (g : T' ⟶ T)
    (x : PullbackQuotient q (zeroFreeAmbient S r) T) :
    ((x.pullback g).toQuotientPullbackDataZero (l := l)).Q ≅
      ((x.toQuotientPullbackDataZero (l := l)).pullback g).Q :=
  let G := ((Over.pullback (Scheme.projectiveSpaceOverπ 0 S)).map g).left
  let fst' := Limits.pullback.fst T'.hom (Scheme.projectiveSpaceOverπ 0 S)
  let fst := Limits.pullback.fst T.hom (Scheme.projectiveSpaceOverπ 0 S)
  (Modules.pullbackComp fst' g.left).app x.Q ≪≫
    (Modules.pullbackCongr
      (Scheme.overPullbackMap_isPullback (f :=
        Scheme.projectiveSpaceOverπ 0 S) g).w.symm).app x.Q ≪≫
    ((Modules.pullbackComp G fst).app x.Q).symm

/-- Base-change coherence of the ambient comparison: pulling the ambient comparison
back along a morphism of parameter objects and exchanging the two pullback squares
recovers the comparison for the base-changed object.  This is an instance of the theta
coherence `Modules.pullback_theta_coherence_iso`. -/
lemma toQuotientPullbackDataZeroAmbientIso_pullback_coherence
    {T' : Over S} (g : T' ⟶ T) :
    let G := ((Over.pullback (Scheme.projectiveSpaceOverπ 0 S)).map g).left
    let fst' := Limits.pullback.fst T'.hom (Scheme.projectiveSpaceOverπ 0 S)
    let fst := Limits.pullback.fst T.hom (Scheme.projectiveSpaceOverπ 0 S)
    (toQuotientPullbackDataZeroAmbientIso
        (S := S) (T := T') (l := l) (r := r)).hom ≫
      (Modules.pullback fst').map
        (PullbackQuotient.pullbackComparison (zeroFreeAmbient S r) g).hom ≫
      (Modules.pullbackComp fst' g.left).hom.app
        ((Modules.pullback T.hom).obj (zeroFreeAmbient S r)) ≫
      (Modules.pullbackCongr
        (Scheme.overPullbackMap_isPullback (f :=
          Scheme.projectiveSpaceOverπ 0 S) g).w.symm).hom.app
        ((Modules.pullback T.hom).obj (zeroFreeAmbient S r)) ≫
      (Modules.pullbackComp G fst).inv.app
        ((Modules.pullback T.hom).obj (zeroFreeAmbient S r)) =
    (PullbackQuotient.pullbackComparison
        (Scheme.projectiveSpaceOverTwistedFree 0 S l r)
        ((Over.pullback (Scheme.projectiveSpaceOverπ 0 S)).map g)).hom ≫
      (Modules.pullback G).map
        (toQuotientPullbackDataZeroAmbientIso
          (S := S) (T := T) (l := l) (r := r)).hom := by
  dsimp only
  simp only [toQuotientPullbackDataZeroAmbientIso,
    PullbackQuotient.pullbackComparison, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Iso.app_inv, Functor.mapIso_hom, CategoryTheory.Functor.map_comp, Category.assoc]
  exact Modules.pullback_theta_coherence_iso _ _ _ _ _ _ _ _ _
    Limits.pullback.condition.symm (Over.w g)
    (Scheme.overPullbackMap_isPullback
      (f := Scheme.projectiveSpaceOverπ 0 S) g).w.symm
    (Over.w ((Over.pullback (Scheme.projectiveSpaceOverπ 0 S)).map g))
    Limits.pullback.condition.symm _
    (zeroTwistedFreeToPullbackFreeIso (S := S) (l := l) (r := r))

/-- The Grassmannian-to-Quot construction commutes with base change of the parameter
object, up to the equivalence relation on Quot presentations.  This is the naturality
of the induced map from the relative Grassmannian functor to the fixed-polynomial Quot
functor. -/
theorem toQuotientPullbackDataZero_pullback_r
    {T' : Over S} (g : T' ⟶ T)
    (x : PullbackQuotient q (zeroFreeAmbient S r) T) :
    (QuotientPullbackData.setoid
      (Scheme.projectiveSpaceOverTwistedFree 0 S l r)
      (Scheme.projectiveSpaceOverπ 0 S) T').r
        ((x.pullback g).toQuotientPullbackDataZero (l := l))
        ((x.toQuotientPullbackDataZero (l := l)).pullback g) := by
  refine ⟨x.toQuotientPullbackDataZero_pullbackIso (l := l) g, ?_⟩
  have hheads := toQuotientPullbackDataZeroAmbientIso_pullback_coherence
    (S := S) (T := T) (l := l) (r := r) g
  dsimp only at hheads
  simp only [toQuotientPullbackDataZero, QuotientPullbackData.pullback,
    PullbackQuotient.pullback, toQuotientPullbackDataZero_pullbackIso,
    toQuotientPullbackDataZeroAmbientIso, PullbackQuotient.pullbackComparison,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    CategoryTheory.Functor.map_comp, Category.assoc] at hheads ⊢
  rw [← CategoryTheory.Functor.comp_map
      (Modules.pullback g.left)
      (Modules.pullback
        (Limits.pullback.fst T'.hom (Scheme.projectiveSpaceOverπ 0 S))) x.π,
    NatTrans.naturality_assoc ((Modules.pullbackComp
      (Limits.pullback.fst T'.hom (Scheme.projectiveSpaceOverπ 0 S)) g.left).hom)
      x.π,
    NatTrans.naturality_assoc ((Modules.pullbackCongr
      (Scheme.overPullbackMap_isPullback
        (f := Scheme.projectiveSpaceOverπ 0 S) g).w.symm).hom) x.π,
    NatTrans.naturality ((Modules.pullbackComp
      ((Over.pullback (Scheme.projectiveSpaceOverπ 0 S)).map g).left
      (Limits.pullback.fst T.hom (Scheme.projectiveSpaceOverπ 0 S))).inv) x.π,
    CategoryTheory.Functor.comp_map]
  simp only [← Category.assoc] at hheads ⊢
  rw [hheads]

end PullbackQuotient

end AlgebraicGeometry.Scheme.Modules

end
