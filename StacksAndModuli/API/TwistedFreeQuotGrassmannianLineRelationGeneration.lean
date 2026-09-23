module

public import StacksAndModuli.API.TwistedFreeQuotGrassmannianActualFamilyRelationGeneration
public import StacksAndModuli.API.ProjectiveLineFiniteLocallyFreeTwistOneCohomology
public import StacksAndModuli.API.QuotGrassmannianReconstructionIso

/-!
# Uniform relation generation on the projective line

For a Grassmannian quotient in degree `d`, the reconstructed quotient family determines
a second finite-free quotient by taking degree-`d` global sections.  On the relative
projective line this comparison is an isomorphism whenever both targets are finite locally
free of the expected rank: the relevant degree-`d` pushforward map is epic because `H¹`
of the pullback relation coefficient and `H²` of the remaining relation kernel vanish.

Transporting the already-proved relation-generation epimorphism for the reconstructed
family across this comparison yields a uniform theorem for arbitrary Grassmannian points.
Above one bound, expected rank together with flatness and the prescribed fibrewise Hilbert
polynomial of the reconstructed family imply exact next-degree relation generation.

## Main result

* `AlgebraicGeometry.ProjectiveSpace.
  exists_bound_twistedFreeQuotNextDegreeRelationGeneration_line`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
  AlgebraicGeometry.ProjectiveSpace

universe u

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The zero twisting sheaf on the relative projective line over a noetherian
affine base has vanishing first cohomology. -/
theorem subsingleton_H_one_projectiveSpaceOverTwist_zero
    (R : Type u) [CommRing R] [IsNoetherianRing R] :
    Subsingleton (Scheme.Modules.H
      (Scheme.projectiveSpaceOverTwist 1 (Spec (.of R)) 0) 1) := by
  let e := projectiveSpaceOverSpecIso 1 R
  let F := Scheme.projectiveSpaceOverTwist 1 (Spec (.of R)) 0
  let G := Scheme.Modules.restrict F e.inv
  have hO : Subsingleton (Scheme.Modules.H
      (Scheme.structureModule (Proj.projectiveLine R)) 1) :=
    Proj.subsingleton_H_one_projectiveLine_structure R
  have hpoly : Subsingleton (Scheme.Modules.H
      (ProjectiveSpectrum.Twist.twist
        (MvPolynomial.homogeneousSubmodule (Fin 2) R) 0) 1) :=
    Scheme.Modules.subsingleton_H_of_iso
      (ProjectiveSpectrum.Twist.zeroIso
        (MvPolynomial.homogeneousSubmodule (Fin 2) R)).symm 1 hO
  have hpull : Subsingleton (Scheme.Modules.H
      ((Scheme.Modules.pullback e.inv).obj F) 1) :=
    Scheme.Modules.subsingleton_H_of_iso
      (projectiveSpaceOverTwistPullbackIso 1 R 0).symm 1 hpoly
  have hG : Subsingleton (Scheme.Modules.H G 1) :=
    Scheme.Modules.subsingleton_H_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback e.inv).app F).symm 1 hpull
  have hback : Subsingleton
      (Scheme.Modules.H (Scheme.Modules.restrict G e.hom) 1) :=
    Scheme.subsingleton_H_restrict_of_iso e G 0 (by simpa using hG)
  let eBack : Scheme.Modules.restrict G e.hom ≅ F :=
    ((Scheme.Modules.restrictFunctorComp e.hom e.inv).app F).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr e.hom_inv_id).app F ≪≫
      (Scheme.Modules.restrictFunctorId).app F
  exact Scheme.Modules.subsingleton_H_of_iso eBack 1 hback

/-- A finite locally free coefficient pulled back to the relative projective line
and tensored with `O(0)` has vanishing first cohomology. -/
theorem subsingleton_H_one_projectiveSpaceOverTwistModule_pullback_zero_of_isFiniteLocallyFree
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {K : (Spec (.of R)).Modules} [K.IsQuasicoherent]
    (hK : Scheme.Modules.IsFiniteLocallyFree K) :
    Subsingleton (Scheme.Modules.H
      (Scheme.projectiveSpaceOverTwistModule
        ((Scheme.Modules.pullback
          (Scheme.projectiveSpaceOverπ 1 (Spec (.of R)))).obj K) 0) 1) := by
  obtain ⟨J, hJ, i, p, hip⟩ :=
    Scheme.Modules.exists_retract_free_of_isFiniteLocallyFree_of_isAffine hK
  letI : Finite J := hJ
  let π := Scheme.projectiveSpaceOverπ 1 (Spec (.of R))
  let O0 := Scheme.projectiveSpaceOverTwist 1 (Spec (.of R)) 0
  let F := Scheme.projectiveSpaceOverTwistModule
    ((Scheme.Modules.pullback π).obj K) 0
  let G := ∐ fun _ : J ↦ O0
  let eFree := Scheme.Modules.pullbackFreeIso π J
  let eTensor := Scheme.freeTensorTwistIso 1 (Spec (.of R)) J 0
  let iF : F ⟶ G :=
    Scheme.Modules.tensorMapLeft ((Scheme.Modules.pullback π).map i) O0 ≫
      (Scheme.Modules.tensorLeftIso eFree O0).hom ≫ eTensor.hom
  let pF : G ⟶ F :=
    eTensor.inv ≫ (Scheme.Modules.tensorLeftIso eFree O0).inv ≫
      Scheme.Modules.tensorMapLeft ((Scheme.Modules.pullback π).map p) O0
  have hiFpF : iF ≫ pF = 𝟙 F := by
    dsimp only [iF, pF]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Scheme.Modules.tensorMapLeft_comp, ← Functor.map_comp, hip]
    simp
    rfl
  have hO0 : Subsingleton (Scheme.Modules.H O0 1) := by
    dsimp only [O0]
    exact subsingleton_H_one_projectiveSpaceOverTwist_zero R
  have hG : Subsingleton (Scheme.Modules.H G 1) := by
    dsimp only [G]
    exact Scheme.Modules.subsingleton_H_coproduct_of_finite
      (fun _ : J ↦ O0) 1 (fun _ ↦ hO0)
  exact Scheme.Modules.subsingleton_H_of_retract iF pF hiFpF 1 hG

end AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Twisting the reconstructed relation source by `O(d)` cancels its `O(-d)`
factor and leaves the pullback relation coefficient tensored with `O(0)`. -/
noncomputable def reconstructedRelationSourceTwistIsoPullbackZero
    (n : ℕ) (T : Scheme.{u}) (d : ℕ) (K : T.Modules) :
    Modules.tensor
        (Modules.tensor
          ((Modules.pullback (projectiveSpaceOverπ n T)).obj K)
          (projectiveSpaceOverTwist n T (-(d : ℤ))))
        (projectiveSpaceOverTwist n T (d : ℤ)) ≅
      projectiveSpaceOverTwistModule
        ((Modules.pullback (projectiveSpaceOverπ n T)).obj K) 0 :=
  Modules.tensorAssocIso
      ((Modules.pullback (projectiveSpaceOverπ n T)).obj K)
      (projectiveSpaceOverTwist n T (-(d : ℤ)))
      (projectiveSpaceOverTwist n T (d : ℤ)) ≪≫
    Modules.tensorRightIso
      ((Modules.pullback (projectiveSpaceOverπ n T)).obj K)
      (projectiveSpaceOverTwist_addIso_nat n T (-(d : ℤ)) d ≪≫
        eqToIso (congrArg (projectiveSpaceOverTwist n T) (by omega)))

/-- The kernel left after mapping the degree-`d` reconstructed relations to their
image on the relative projective line has vanishing second cohomology. -/
theorem subsingleton_H_two_reconstructedDegreeRelationKernel_line
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (l : ℤ) (r d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    {E : (Spec (.of R)).Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E) :
    Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (kernel (Modules.tensorMapLeft
          (Abelian.factorThruImage
            (reconstructedRelation' 1 (Spec (.of R)) l r d e he u))
          (projectiveSpaceOverTwist 1 (Spec (.of R)) (d : ℤ))))).H 2) := by
  let T := Spec (.of R)
  let f := reconstructedRelation' 1 T l r d e he u
  let O := projectiveSpaceOverTwist 1 T (d : ℤ)
  let g := Modules.tensorMapLeft (Abelian.factorThruImage f) O
  haveI hkeruqc : (kernel u).IsQuasicoherent :=
    Modules.kernel_isQuasicoherent u
  haveI hpullKqc : ((Modules.pullback
      (projectiveSpaceOverπ 1 T)).obj (kernel u)).IsQuasicoherent :=
    Modules.isQuasicoherent_pullback (projectiveSpaceOverπ 1 T) _
  haveI hAqc : (Modules.tensor
      ((Modules.pullback (projectiveSpaceOverπ 1 T)).obj (kernel u))
      (projectiveSpaceOverTwist 1 T (-(d : ℤ)))).IsQuasicoherent := by
    change (projectiveSpaceOverTwistModule
      ((Modules.pullback (projectiveSpaceOverπ 1 T)).obj (kernel u))
      (-(d : ℤ))).IsQuasicoherent
    infer_instance
  haveI hFqc : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist 1 T (-l)).IsQuasicoherent :=
    Modules.projectiveSpaceOverTwistCoproduct_isQuasicoherent _ 1 T _
  haveI hIQC : (Abelian.image f).IsQuasicoherent := by
    dsimp only [Abelian.image]
    letI : (cokernel f).IsQuasicoherent :=
      Modules.isQuasicoherent_cokernel f
    exact Modules.kernel_isQuasicoherent (cokernel.π f)
  haveI hAOqc : (Modules.tensor
      (Modules.tensor
        ((Modules.pullback (projectiveSpaceOverπ 1 T)).obj (kernel u))
        (projectiveSpaceOverTwist 1 T (-(d : ℤ)))) O).IsQuasicoherent := by
    change (projectiveSpaceOverTwistModule
      (Modules.tensor
        ((Modules.pullback (projectiveSpaceOverπ 1 T)).obj (kernel u))
        (projectiveSpaceOverTwist 1 T (-(d : ℤ)))) (d : ℤ)).IsQuasicoherent
    infer_instance
  haveI hIOqc : (Modules.tensor (Abelian.image f) O).IsQuasicoherent := by
    change (projectiveSpaceOverTwistModule (Abelian.image f)
      (d : ℤ)).IsQuasicoherent
    infer_instance
  haveI hgqc : (kernel g).IsQuasicoherent :=
    Modules.kernel_isQuasicoherent g
  exact ProjectiveSpace.subsingleton_H_projectiveSpaceOver_one_of_two_le
    R (kernel g) 2 le_rfl

/-- For a finite locally free coefficient quotient, the degree-`d` global-sections
map of its reconstructed quotient on the relative projective line is epic. -/
theorem reconstructedDegreePushforwardMap_epi_of_finiteLocallyFree_line
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (l : ℤ) (r d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    {E : (Spec (.of R)).Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E)
    [Epi u] (hE : Modules.IsFiniteLocallyFree E) :
    Epi (quotGrassmannianFreeMap 1 (Spec (.of R)) l r
      (reconstructedQuotientMap' 1 (Spec (.of R)) l r d e he u)
      d e he) := by
  let T := Spec (.of R)
  let f := reconstructedRelation' 1 T l r d e he u
  let p := reconstructedQuotientMap' 1 T l r d e he u
  let Q := reconstructedQuotient' 1 T l r d e he u
  let F := ∐ fun _ : ULift.{u} (Fin r) ↦
    projectiveSpaceOverTwist 1 T (-l)
  let O := projectiveSpaceOverTwist 1 T (d : ℤ)
  let g := Modules.tensorMapLeft (Abelian.factorThruImage f) O
  haveI hQqc : Q.IsQuasicoherent :=
    reconstructedQuotient'_isQuasicoherent 1 T l r d e he u
  haveI hFqc : F.IsQuasicoherent :=
    Modules.projectiveSpaceOverTwistCoproduct_isQuasicoherent _ 1 T _
  haveI hFOqc : (Modules.tensor F O).IsQuasicoherent := by
    change (projectiveSpaceOverTwistModule F (d : ℤ)).IsQuasicoherent
    infer_instance
  haveI hQOqc : (Modules.tensor Q O).IsQuasicoherent := by
    change (projectiveSpaceOverTwistModule Q (d : ℤ)).IsQuasicoherent
    infer_instance
  have hSourceFinite : Modules.IsFiniteLocallyFree
      (SheafOfModules.free (R := T.ringCatSheaf)
        (ULift.{u} (Fin r) × Fin ((1 + e).choose 1))) := by
    let m := r * (1 + e).choose 1
    let σ : ULift.{u} (Fin m) ≃
        ULift.{u} (Fin r) × Fin ((1 + e).choose 1) :=
      twistedFreeMonomialIndexEquiv r ((1 + e).choose 1)
    let w := SheafOfModules.freeMap (R := T.ringCatSheaf) σ.symm
    haveI : IsIso w := Modules.freeMap_isIso_of_equiv σ.symm
    exact (Modules.free_isFiniteLocallyFree T m).of_iso (asIso w).symm
  have hK : Modules.IsFiniteLocallyFree (kernel u) :=
    Modules.kernel_isFiniteLocallyFree_of_epi_of_isFiniteLocallyFree
      hSourceFinite hE u
  letI : (kernel u).IsQuasicoherent := Modules.kernel_isQuasicoherent u
  have hpull0 : Subsingleton (((SheafOfModules.toSheaf _).obj
      (projectiveSpaceOverTwistModule
        ((Modules.pullback (projectiveSpaceOverπ 1 T)).obj (kernel u)) 0)).H 1) :=
    subsingleton_H_one_projectiveSpaceOverTwistModule_pullback_zero_of_isFiniteLocallyFree
      R hK
  have hsource1 : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (Modules.tensor
          (Modules.tensor
            ((Modules.pullback (projectiveSpaceOverπ 1 T)).obj (kernel u))
            (projectiveSpaceOverTwist 1 T (-(d : ℤ)))) O)).H 1) :=
    Modules.subsingleton_H_of_iso
      (reconstructedRelationSourceTwistIsoPullbackZero
        1 T d (kernel u)).symm 1 hpull0
  have hrelationKernel2 :=
    subsingleton_H_two_reconstructedDegreeRelationKernel_line
      R l r d e he u
  haveI hg : Epi g := by
    dsimp only [g]
    infer_instance
  let C := ShortComplex.mk (kernel.ι g) g (kernel.condition g)
  have hC : C.ShortExact := { exact := ShortComplex.exact_kernel g }
  have himage1 : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (Modules.tensor (Abelian.image f) O)).H 1) :=
    Modules.subsingleton_H_of_shortExact_right hC rfl hsource1
      hrelationKernel2
  let eK := projectiveSpaceOverTwistTensorKernelIso 1 T p (d : ℤ)
  have hkernel1 : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (kernel (Modules.tensorMapLeft p O))).H 1) :=
    Modules.subsingleton_H_of_iso eK 1 himage1
  haveI hpushed : Epi ((Modules.pushforward
      (projectiveSpaceOverπ 1 T)).map (Modules.tensorMapLeft p O)) :=
    Modules.projectiveSpacePushforward_map_epi_of_subsingleton_H_one_kernel
      1 T (Modules.tensorMapLeft p O) hkernel1
  exact quotGrassmannianFreeMap_epi_of_pushforward_epi
    1 T l r d e he p

/-- Compatible isomorphisms of finite-free quotient targets induce an isomorphism
between the sources of the associated next-degree relation maps. -/
noncomputable def twistedFreeNextDegreeRelationSourceIsoOfTargetIso
    (n : ℕ) (T : Scheme.{u}) (r e : ℕ) {E E' : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (v : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E')
    (ε : E ≅ E') (hε : u ≫ ε.hom = v) :
    (∐ fun _ : ULift.{u} (Fin (n + 1)) ↦ kernel u) ≅
      (∐ fun _ : ULift.{u} (Fin (n + 1)) ↦ kernel v) :=
  Sigma.mapIso (fun _ : ULift.{u} (Fin (n + 1)) ↦
    kernel.mapIso (f := u) v (Iso.refl _) ε hε)

/-- The next-degree relation map is natural under a compatible isomorphism of the
finite-free quotient target. -/
lemma twistedFreeNextDegreeRelation_naturality_targetIso
    (n : ℕ) (T : Scheme.{u}) (r e : ℕ) {E E' : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (v : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E')
    (ε : E ≅ E') (hε : u ≫ ε.hom = v) :
    (twistedFreeNextDegreeRelationSourceIsoOfTargetIso
        n T r e u v ε hε).hom ≫
      twistedFreeNextDegreeRelation n T r e v =
    twistedFreeNextDegreeRelation n T r e u := by
  let k : kernel u ≅ kernel v :=
    kernel.mapIso (f := u) v (Iso.refl _) ε hε
  have hk : k.hom ≫ kernel.ι v = kernel.ι u := by
    dsimp only [k, kernel.mapIso, kernel.map]
    exact kernel.lift_ι _ _ _
  apply Sigma.hom_ext
  intro j
  let m := SheafOfModules.freeMap (R := T.ringCatSheaf)
    (fun x : ULift.{u} (Fin r) × Fin ((n + e).choose n) ↦
      (x.1, twistedFreeNextMonomialIndex n e j.down x.2))
  let descV := Sigma.desc (fun j : ULift.{u} (Fin (n + 1)) ↦
    kernel.ι v ≫ SheafOfModules.freeMap (R := T.ringCatSheaf)
      (fun x : ULift.{u} (Fin r) × Fin ((n + e).choose n) ↦
        (x.1, twistedFreeNextMonomialIndex n e j.down x.2)))
  let descU := Sigma.desc (fun j : ULift.{u} (Fin (n + 1)) ↦
    kernel.ι u ≫ SheafOfModules.freeMap (R := T.ringCatSheaf)
      (fun x : ULift.{u} (Fin r) × Fin ((n + e).choose n) ↦
        (x.1, twistedFreeNextMonomialIndex n e j.down x.2)))
  have hmap := Sigma.ι_mapIso_hom
    (fun _ : ULift.{u} (Fin (n + 1)) ↦ k) j
  have hdescV : Sigma.ι (fun _ : ULift.{u} (Fin (n + 1)) ↦ kernel v) j ≫
      descV = kernel.ι v ≫ m := Sigma.ι_desc _ j
  have hdescU : Sigma.ι (fun _ : ULift.{u} (Fin (n + 1)) ↦ kernel u) j ≫
      descU = kernel.ι u ≫ m := Sigma.ι_desc _ j
  change (Sigma.ι (fun _ : ULift.{u} (Fin (n + 1)) ↦ kernel u) j ≫
      (Sigma.mapIso (fun _ : ULift.{u} (Fin (n + 1)) ↦ k)).hom) ≫ descV =
    Sigma.ι (fun _ : ULift.{u} (Fin (n + 1)) ↦ kernel u) j ≫ descU
  calc
    (Sigma.ι (fun _ : ULift.{u} (Fin (n + 1)) ↦ kernel u) j ≫
          (Sigma.mapIso (fun _ : ULift.{u} (Fin (n + 1)) ↦ k)).hom) ≫ descV =
        (k.hom ≫ Sigma.ι (fun _ : ULift.{u} (Fin (n + 1)) ↦ kernel v) j) ≫
          descV := congrArg (fun z ↦ z ≫ descV) hmap
    _ = k.hom ≫ (Sigma.ι (fun _ : ULift.{u} (Fin (n + 1)) ↦ kernel v) j ≫
          descV) := Category.assoc _ _ _
    _ = k.hom ≫ (kernel.ι v ≫ m) :=
      congrArg (fun z ↦ k.hom ≫ z) hdescV
    _ = (k.hom ≫ kernel.ι v) ≫ m := (Category.assoc _ _ _).symm
    _ = kernel.ι u ≫ m := congrArg (fun z ↦ z ≫ m) hk
    _ = Sigma.ι (fun _ : ULift.{u} (Fin (n + 1)) ↦ kernel u) j ≫ descU :=
      hdescU.symm

/-- Compatible isomorphisms of finite-free quotient targets identify the kernels
of the corresponding reconstructed next-degree quotient maps. -/
noncomputable def twistedFreeNextDegreeReconstructedKernelTargetIsoOfTargetIso
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E E' : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (v : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E')
    (ε : E ≅ E') (hε : u ≫ ε.hom = v) :
    kernel (quotGrassmannianFreeMap n T l r
        (reconstructedQuotientMap' n T l r d e he u)
        (d + 1) (e + 1) (by omega)) ≅
      kernel (quotGrassmannianFreeMap n T l r
        (reconstructedQuotientMap' n T l r d e he v)
        (d + 1) (e + 1) (by omega)) := by
  let δ := reconstructedQuotientIsoOfTargetIso
    n T l r d e he u v ε hε
  let qU := quotGrassmannianFreeMap n T l r
    (reconstructedQuotientMap' n T l r d e he u)
    (d + 1) (e + 1) (by omega)
  let qV := quotGrassmannianFreeMap n T l r
    (reconstructedQuotientMap' n T l r d e he v)
    (d + 1) (e + 1) (by omega)
  let t := Modules.projectiveTwistedPushforwardIso δ (d + 1)
  have hq : qU ≫ t.hom = qV := by
    calc
      qU ≫ t.hom = quotGrassmannianFreeMap n T l r
          (reconstructedQuotientMap' n T l r d e he u ≫ δ.hom)
          (d + 1) (e + 1) (by omega) :=
        quotGrassmannianFreeMap_comp_targetIso n T l r _ δ
          (d + 1) (e + 1) (by omega)
      _ = qV := congrArg
        (fun p ↦ quotGrassmannianFreeMap n T l r p
          (d + 1) (e + 1) (by omega))
        (reconstructedQuotientMap'_comp_reconstructedQuotientIsoOfTargetIso_hom
          n T l r d e he u v ε hε)
  exact kernel.mapIso (f := qU) qV (Iso.refl _) t hq

/-- The reconstructed-kernel isomorphism induced by a quotient-target isomorphism
commutes with the canonical kernel inclusions. -/
lemma twistedFreeNextDegreeReconstructedKernelTargetIsoOfTargetIso_hom_comp
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E E' : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (v : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E')
    (ε : E ≅ E') (hε : u ≫ ε.hom = v) :
    (twistedFreeNextDegreeReconstructedKernelTargetIsoOfTargetIso
      n T l r d e he u v ε hε).hom ≫
        kernel.ι (quotGrassmannianFreeMap n T l r
          (reconstructedQuotientMap' n T l r d e he v)
          (d + 1) (e + 1) (by omega)) =
      kernel.ι (quotGrassmannianFreeMap n T l r
        (reconstructedQuotientMap' n T l r d e he u)
        (d + 1) (e + 1) (by omega)) := by
  dsimp only [twistedFreeNextDegreeReconstructedKernelTargetIsoOfTargetIso,
    kernel.mapIso, kernel.map]
  exact kernel.lift_ι _ _ _

/-- The lift from next-degree relations to the reconstructed next-degree kernel is
natural under compatible isomorphisms of finite-free quotient targets. -/
theorem twistedFreeNextDegreeReconstructedKernelLift_naturality_targetIso
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E E' : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (v : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E')
    (ε : E ≅ E') (hε : u ≫ ε.hom = v) :
    (twistedFreeNextDegreeRelationSourceIsoOfTargetIso
        n T r e u v ε hε).hom ≫
      twistedFreeNextDegreeReconstructedKernelLift n T l r d e he v =
    twistedFreeNextDegreeReconstructedKernelLift n T l r d e he u ≫
      (twistedFreeNextDegreeReconstructedKernelTargetIsoOfTargetIso
        n T l r d e he u v ε hε).hom := by
  let s := (twistedFreeNextDegreeRelationSourceIsoOfTargetIso
    n T r e u v ε hε).hom
  let gu := twistedFreeNextDegreeReconstructedKernelLift
    n T l r d e he u
  let gv := twistedFreeNextDegreeReconstructedKernelLift
    n T l r d e he v
  let qU := quotGrassmannianFreeMap n T l r
    (reconstructedQuotientMap' n T l r d e he u)
    (d + 1) (e + 1) (by omega)
  let qV := quotGrassmannianFreeMap n T l r
    (reconstructedQuotientMap' n T l r d e he v)
    (d + 1) (e + 1) (by omega)
  let t := (twistedFreeNextDegreeReconstructedKernelTargetIsoOfTargetIso
    n T l r d e he u v ε hε).hom
  have hgu := twistedFreeNextDegreeReconstructedKernelLift_comp
    n T l r d e he u
  have hgv := twistedFreeNextDegreeReconstructedKernelLift_comp
    n T l r d e he v
  have hs := twistedFreeNextDegreeRelation_naturality_targetIso
    n T r e u v ε hε
  have ht :=
    twistedFreeNextDegreeReconstructedKernelTargetIsoOfTargetIso_hom_comp
      n T l r d e he u v ε hε
  apply (cancel_mono (kernel.ι qV)).mp
  change (s ≫ gv) ≫ kernel.ι qV = (gu ≫ t) ≫ kernel.ι qV
  calc
    (s ≫ gv) ≫ kernel.ι qV = s ≫ (gv ≫ kernel.ι qV) :=
      Category.assoc _ _ _
    _ = s ≫ twistedFreeNextDegreeRelation n T r e v :=
      congrArg (fun z ↦ s ≫ z) hgv
    _ = twistedFreeNextDegreeRelation n T r e u := hs
    _ = gu ≫ kernel.ι qU := hgu.symm
    _ = gu ≫ (t ≫ kernel.ι qV) :=
      congrArg (fun z ↦ gu ≫ z) ht.symm
    _ = (gu ≫ t) ≫ kernel.ι qV := (Category.assoc _ _ _).symm

/-- Epimorphy of the reconstructed next-degree kernel lift transports backwards
along a compatible isomorphism of finite-free quotient targets. -/
theorem twistedFreeNextDegreeReconstructedKernelLift_epi_of_targetIso
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E E' : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (v : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E')
    (ε : E ≅ E') (hε : u ≫ ε.hom = v)
    (hv : Epi (twistedFreeNextDegreeReconstructedKernelLift
      n T l r d e he v)) :
    Epi (twistedFreeNextDegreeReconstructedKernelLift
      n T l r d e he u) := by
  let s := (twistedFreeNextDegreeRelationSourceIsoOfTargetIso
    n T r e u v ε hε).hom
  let gu := twistedFreeNextDegreeReconstructedKernelLift
    n T l r d e he u
  let gv := twistedFreeNextDegreeReconstructedKernelLift
    n T l r d e he v
  let t := (twistedFreeNextDegreeReconstructedKernelTargetIsoOfTargetIso
    n T l r d e he u v ε hε).hom
  letI : Epi gv := hv
  haveI : Epi (s ≫ gv) := epi_comp s gv
  have h : s ≫ gv = gu ≫ t :=
    twistedFreeNextDegreeReconstructedKernelLift_naturality_targetIso
      n T l r d e he u v ε hε
  haveI : Epi (gu ≫ t) := h ▸ inferInstance
  exact (epi_comp_iff_of_isIso gu t).mp inferInstance

/-- If an expected-rank finite locally free quotient and the degree-`d`
pushforward of its reconstructed family have the same rank, the canonical map
between them is an isomorphism on the relative projective line. -/
noncomputable def reconstructedDegreeTargetIso_line
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (q : ℕ) (l : ℤ) (r d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    {E : (Spec (.of R)).Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E)
    [Epi u] (hE : Modules.IsProjectiveOfRank q E)
    (hM : Modules.IsProjectiveOfRank q
      (Modules.projectiveTwistedPushforward 1
        (reconstructedQuotient' 1 (Spec (.of R)) l r d e he u) d)) :
    E ≅ Modules.projectiveTwistedPushforward 1
      (reconstructedQuotient' 1 (Spec (.of R)) l r d e he u) d := by
  let T := Spec (.of R)
  let Q := reconstructedQuotient' 1 T l r d e he u
  let p := reconstructedQuotientMap' 1 T l r d e he u
  let v := quotGrassmannianFreeMap 1 T l r p d e he
  let M := Modules.projectiveTwistedPushforward 1 Q d
  haveI hQqc : Q.IsQuasicoherent :=
    reconstructedQuotient'_isQuasicoherent 1 T l r d e he u
  haveI hMqc : M.IsQuasicoherent :=
    Modules.isQuasicoherent_pushforward_of_qcqs
      (projectiveSpaceOverπ 1 T)
      (projectiveSpaceOverTwistModule Q (d : ℤ))
  haveI hv : Epi v :=
    reconstructedDegreePushforwardMap_epi_of_finiteLocallyFree_line
      R l r d e he u hE.isFiniteLocallyFree
  have hzero : kernel.ι u ≫ v = 0 :=
    kernel_ι_comp_quotGrassmannianFreeMap_reconstructedQuotientMap'_eq_zero
      1 T l r d e he u
        (twistedFreeAmbientReconstructionCompatibility 1 T l r d e he)
  exact Modules.freeQuotientTargetIsoOfKernelVanishing
    u v hzero hE hM

/-- The target comparison isomorphism for the reconstructed degree-`d` quotient
intertwines the original quotient with the canonical global-sections map. -/
lemma reconstructedDegreeTargetIso_line_comp
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (q : ℕ) (l : ℤ) (r d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    {E : (Spec (.of R)).Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E)
    [Epi u] (hE : Modules.IsProjectiveOfRank q E)
    (hM : Modules.IsProjectiveOfRank q
      (Modules.projectiveTwistedPushforward 1
        (reconstructedQuotient' 1 (Spec (.of R)) l r d e he u) d)) :
    u ≫ (reconstructedDegreeTargetIso_line
      R q l r d e he u hE hM).hom =
      quotGrassmannianFreeMap 1 (Spec (.of R)) l r
        (reconstructedQuotientMap' 1 (Spec (.of R)) l r d e he u)
        d e he := by
  let T := Spec (.of R)
  let Q := reconstructedQuotient' 1 T l r d e he u
  let p := reconstructedQuotientMap' 1 T l r d e he u
  let v := quotGrassmannianFreeMap 1 T l r p d e he
  let M := Modules.projectiveTwistedPushforward 1 Q d
  haveI hQqc : Q.IsQuasicoherent :=
    reconstructedQuotient'_isQuasicoherent 1 T l r d e he u
  haveI hMqc : M.IsQuasicoherent :=
    Modules.isQuasicoherent_pushforward_of_qcqs
      (projectiveSpaceOverπ 1 T)
      (projectiveSpaceOverTwistModule Q (d : ℤ))
  haveI hv : Epi v :=
    reconstructedDegreePushforwardMap_epi_of_finiteLocallyFree_line
      R l r d e he u hE.isFiniteLocallyFree
  have hzero : kernel.ι u ≫ v = 0 :=
    kernel_ι_comp_quotGrassmannianFreeMap_reconstructedQuotientMap'_eq_zero
      1 T l r d e he u
        (twistedFreeAmbientReconstructionCompatibility 1 T l r d e he)
  change u ≫ (Modules.freeQuotientTargetIsoOfKernelVanishing
    u v hzero hE hM).hom = v
  exact Modules.freeQuotientTargetIsoOfKernelVanishing_comp
    u v hzero hE hM

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- On the relative projective line, next-degree relations of every expected-rank
Grassmannian point whose reconstructed family is flat with fibrewise Hilbert
polynomial `P` are generated in degree one above a uniform bound. -/
theorem exists_bound_twistedFreeQuotNextDegreeRelationGeneration_line
    (r : ℕ) (l : ℤ) (P : Polynomial ℚ) :
    ∃ D : ℕ, ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
      (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
      (E : (Spec (.of R)).Modules) [E.IsQuasicoherent]
      (u : SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf)
        (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E) [Epi u],
      D ≤ d → Scheme.Modules.IsProjectiveOfRank (P.hilbertNatValue d) E →
      Scheme.Modules.TwistedFreeQuotNextDegreeRelationGeneration
        1 (Spec (.of R)) l r P d e he u := by
  obtain ⟨Dactual, hactual⟩ :=
    exists_bound_reconstruction_reflection_and_nextDegreeRelation_epi
      1 r (by omega) l P
  obtain ⟨d₀, hd₀, hpush⟩ :=
    Scheme.exists_bound_reconstructedQuotient_pushforward_isProjectiveOfRank
      1 r l P
  let Dpush := d₀.toNat
  have hDpush : (Dpush : ℤ) = d₀ := by
    dsimp only [Dpush]
    exact Int.toNat_of_nonneg hd₀
  refine ⟨max Dactual Dpush, ?_⟩
  intro R _ _ d e he E hEqc u hu hd hE
  have hdactual : Dactual ≤ d := le_trans (le_max_left _ _) hd
  have hdpushNat : Dpush ≤ d := le_trans (le_max_right _ _) hd
  have hdpush : d₀ ≤ (d : ℤ) := by
    rw [← hDpush]
    exact_mod_cast hdpushNat
  intro hfamily
  let T := Spec (.of R)
  let Q := Scheme.reconstructedQuotient' 1 T l r d e he u
  let p := Scheme.reconstructedQuotientMap' 1 T l r d e he u
  let v := Scheme.quotGrassmannianFreeMap 1 T l r p d e he
  haveI hQfp : Q.IsFinitePresentation :=
    Scheme.reconstructedQuotient'_isFinitePresentation 1 T l r d e he u
  haveI hp : Epi p := by
    dsimp only [p]
    infer_instance
  obtain ⟨_, hv⟩ := hactual d hdactual e he R Q hQfp p hp
    hfamily.1 hfamily.2
  have hM : Scheme.Modules.IsProjectiveOfRank (P.hilbertNatValue d)
      (Scheme.Modules.projectiveTwistedPushforward 1 Q d) :=
    hpush T d e he E u hfamily.1 hfamily.2 d hdpush
  let C := Scheme.reconstructedDegreeTargetIso_line
    R (P.hilbertNatValue d) l r d e he u hE hM
  have hC : u ≫ C.hom = v :=
    Scheme.reconstructedDegreeTargetIso_line_comp
      R (P.hilbertNatValue d) l r d e he u hE hM
  exact Scheme.twistedFreeNextDegreeReconstructedKernelLift_epi_of_targetIso
    1 T l r d e he u v C hC hv

end AlgebraicGeometry.ProjectiveSpace

end

end
