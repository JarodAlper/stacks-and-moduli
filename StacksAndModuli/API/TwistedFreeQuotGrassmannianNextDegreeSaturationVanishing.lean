module

public import StacksAndModuli.API.TwistedFreeQuotGrassmannianNextDegreeSaturation
public import StacksAndModuli.API.AffineQuasicoherentEpi
public import StacksAndModuli.API.SheafCohomologyLES
public import StacksAndModuli.API.OpenImmersionPullbackPushforwardCounitBaseChange

/-!
# Cohomological criteria for next-degree Grassmannian saturation

The first field of
`AlgebraicGeometry.Scheme.TwistedFreeNextDegreeReconstructionSaturation` says that
the standard monomials surject onto the degree-`d+1` twisted pushforward of the
reconstructed quotient.  Over an affine base, this file reduces that field to the
vanishing of `H¹` of the kernel of the twisted reconstructed quotient map.

The reconstructed presentation gives a more primitive sufficient condition.  Write
`A → F → Q` for the relation map and its cokernel, and twist by `d+1`.  The
kernel of `F(d+1) → Q(d+1)` is the twist of `im(A → F)`.  Its `H¹` vanishes if
`H¹(A(d+1))` and `H²(ker(A(d+1) → im(A → F)(d+1)))` vanish.  This isolates
the two derived-cohomology inputs needed for the reconstructed-pushforward epimorphism;
it does not assume pushforward base change.
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

/-- Over an affine base, vanishing of `H¹` of the kernel of an epimorphism makes
its projective-space pushforward an epimorphism. -/
theorem Modules.projectiveSpacePushforward_map_epi_of_subsingleton_H_one_kernel
    (n : ℕ) (T : Scheme.{u}) [IsAffine T]
    {M Q : (projectiveSpaceOver n T).Modules}
    [M.IsQuasicoherent] [Q.IsQuasicoherent]
    (f : M ⟶ Q) [Epi f]
    (hvan : Subsingleton
      (((SheafOfModules.toSheaf _).obj (kernel f)).H 1)) :
    Epi ((Modules.pushforward (projectiveSpaceOverπ n T)).map f) := by
  haveI hpushMqc : ((Modules.pushforward
      (projectiveSpaceOverπ n T)).obj M).IsQuasicoherent :=
    Modules.isQuasicoherent_pushforward_of_qcqs
      (projectiveSpaceOverπ n T) M
  haveI hpushQqc : ((Modules.pushforward
      (projectiveSpaceOverπ n T)).obj Q).IsQuasicoherent :=
    Modules.isQuasicoherent_pushforward_of_qcqs
      (projectiveSpaceOverπ n T) Q
  have hsurj : Function.Surjective (f.app ⊤).hom := by
    let C := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
    exact Modules.surjective_appTop_of_shortExact_of_subsingleton_H_one
      (S := C) { exact := ShortComplex.exact_kernel f } hvan
  have hpush : Function.Surjective
      (((Modules.pushforward (projectiveSpaceOverπ n T)).map f).app ⊤).hom := by
    change Function.Surjective
      (f.app ((projectiveSpaceOverπ n T) ⁻¹ᵁ (⊤ : T.Opens))).hom
    rw [Scheme.Hom.preimage_top]
    exact hsurj
  exact Modules.epi_of_appTop_surjective_of_isAffine _ hpush

/-- Epimorphy of the pushforward of a twisted quotient map implies epimorphy of
the corresponding finite-monomial Grassmannian map. -/
theorem quotGrassmannianFreeMap_epi_of_pushforward_epi
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r a b : ℕ)
    (hab : (a : ℤ) - l = (b : ℤ))
    {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    [Epi ((Modules.pushforward (projectiveSpaceOverπ n T)).map
      (Modules.tensorMapLeft p
        (projectiveSpaceOverTwist n T (a : ℤ))))] :
    Epi (quotGrassmannianFreeMap n T l r p a b hab) := by
  rw [quotGrassmannianFreeMap_eq]
  letI : Epi (twistedFreeMonomialPushforwardMap n T l r a b hab) :=
    twistedFreeMonomialPushforwardMap_epi n T l r a b hab
  change Epi (twistedFreeMonomialPushforwardMap n T l r a b hab ≫ _)
  infer_instance

/-- Over an affine base, vanishing of `H¹` of the twisted presentation kernel
makes the reconstructed degree-`d+1` monomial map an epimorphism. -/
theorem reconstructedNextDegreePushforwardMap_epi_of_subsingleton_H_one_kernel
    (n : ℕ) (T : Scheme.{u}) [IsAffine T] (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (hvan : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (kernel (Modules.tensorMapLeft
          (reconstructedQuotientMap' n T l r d e he u)
          (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ))))).H 1)) :
    Epi (quotGrassmannianFreeMap n T l r
      (reconstructedQuotientMap' n T l r d e he u)
      (d + 1) (e + 1) (by omega)) := by
  let p := reconstructedQuotientMap' n T l r d e he u
  let pd := Modules.tensorMapLeft p
    (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ))
  let Q := reconstructedQuotient' n T l r d e he u
  let F := ∐ fun _ : ULift.{u} (Fin r) ↦
    projectiveSpaceOverTwist n T (-l)
  haveI hQqc : Q.IsQuasicoherent :=
    reconstructedQuotient'_isQuasicoherent n T l r d e he u
  haveI hFqc : F.IsQuasicoherent :=
    Modules.projectiveSpaceOverTwistCoproduct_isQuasicoherent _ n T _
  haveI hFdqc : (Modules.tensor F
      (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ))).IsQuasicoherent := by
    change (projectiveSpaceOverTwistModule F
      ((d + 1 : ℕ) : ℤ)).IsQuasicoherent
    infer_instance
  haveI hQdqc : (Modules.tensor Q
      (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ))).IsQuasicoherent := by
    change (projectiveSpaceOverTwistModule Q
      ((d + 1 : ℕ) : ℤ)).IsQuasicoherent
    infer_instance
  haveI hpd : Epi pd := by
    dsimp only [pd, p]
    infer_instance
  haveI : Epi ((Modules.pushforward (projectiveSpaceOverπ n T)).map pd) :=
    Modules.projectiveSpacePushforward_map_epi_of_subsingleton_H_one_kernel
      n T pd hvan
  exact quotGrassmannianFreeMap_epi_of_pushforward_epi
    n T l r (d + 1) (e + 1) (by omega) p

/-- Twisting the source of the reconstructed relation by `d+1` cancels its
degree `-d` twist and leaves the pullback coefficient tensored with `O(1)`. -/
noncomputable def reconstructedNextDegreeRelationSourceTwistIsoPullbackOne
    (n : ℕ) (T : Scheme.{u}) (d : ℕ) (K : T.Modules) :
    Modules.tensor
        (Modules.tensor
          ((Modules.pullback (projectiveSpaceOverπ n T)).obj K)
          (projectiveSpaceOverTwist n T (-(d : ℤ))))
        (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ)) ≅
      projectiveSpaceOverTwistModule
        ((Modules.pullback (projectiveSpaceOverπ n T)).obj K) 1 :=
  Modules.tensorAssocIso
      ((Modules.pullback (projectiveSpaceOverπ n T)).obj K)
      (projectiveSpaceOverTwist n T (-(d : ℤ)))
      (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ)) ≪≫
    Modules.tensorRightIso
      ((Modules.pullback (projectiveSpaceOverπ n T)).obj K)
      (projectiveSpaceOverTwist_addIso_nat n T (-(d : ℤ)) (d + 1) ≪≫
        eqToIso (congrArg (projectiveSpaceOverTwist n T) (by omega)))

/-- For the reconstructed presentation over an affine base, `H¹` of the twisted
relation source and `H²` of the kernel of its map onto the twisted image imply
epimorphy of the degree-`d+1` reconstructed pushforward map. -/
theorem reconstructedNextDegreePushforwardMap_epi_of_relation_vanishing
    (n : ℕ) (T : Scheme.{u}) [IsAffine T] (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (hsource1 : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (Modules.tensor
          (Modules.tensor
            ((Modules.pullback (projectiveSpaceOverπ n T)).obj (kernel u))
            (projectiveSpaceOverTwist n T (-(d : ℤ))))
          (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ)))).H 1))
    (hrelationKernel2 : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (kernel (Modules.tensorMapLeft
          (Abelian.factorThruImage
            (reconstructedRelation' n T l r d e he u))
          (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ))))).H 2)) :
    Epi (quotGrassmannianFreeMap n T l r
      (reconstructedQuotientMap' n T l r d e he u)
      (d + 1) (e + 1) (by omega)) := by
  let f := reconstructedRelation' n T l r d e he u
  let p := reconstructedQuotientMap' n T l r d e he u
  let O := projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ)
  let g := Modules.tensorMapLeft (Abelian.factorThruImage f) O
  haveI hg : Epi g := by
    dsimp only [g]
    infer_instance
  let C := ShortComplex.mk (kernel.ι g) g (kernel.condition g)
  have hC : C.ShortExact := { exact := ShortComplex.exact_kernel g }
  have himage1 : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (Modules.tensor (Abelian.image f) O)).H 1) := by
    exact Modules.subsingleton_H_of_shortExact_right hC rfl hsource1
      hrelationKernel2
  let eK := projectiveSpaceOverTwistTensorKernelIso n T p
    ((d + 1 : ℕ) : ℤ)
  have hkernel1 : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (kernel (Modules.tensorMapLeft p O))).H 1) :=
    Modules.subsingleton_H_of_iso eK 1 himage1
  exact reconstructedNextDegreePushforwardMap_epi_of_subsingleton_H_one_kernel
    n T l r d e he u hkernel1

/-- In the preceding presentation criterion, the source `H¹` input may be stated
as vanishing for the pullback relation coefficient tensored with `O(1)`. -/
theorem reconstructedNextDegreePushforwardMap_epi_of_pullback_one_vanishing
    (n : ℕ) (T : Scheme.{u}) [IsAffine T] (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (hpullback1 : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (projectiveSpaceOverTwistModule
          ((Modules.pullback (projectiveSpaceOverπ n T)).obj (kernel u)) 1)).H 1))
    (hrelationKernel2 : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (kernel (Modules.tensorMapLeft
          (Abelian.factorThruImage
            (reconstructedRelation' n T l r d e he u))
          (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ))))).H 2)) :
    Epi (quotGrassmannianFreeMap n T l r
      (reconstructedQuotientMap' n T l r d e he u)
      (d + 1) (e + 1) (by omega)) := by
  have hsource1 : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (Modules.tensor
          (Modules.tensor
            ((Modules.pullback (projectiveSpaceOverπ n T)).obj (kernel u))
            (projectiveSpaceOverTwist n T (-(d : ℤ))))
          (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ)))).H 1) :=
    Modules.subsingleton_H_of_iso
      (reconstructedNextDegreeRelationSourceTwistIsoPullbackOne
        n T d (kernel u)).symm 1 hpullback1
  exact reconstructedNextDegreePushforwardMap_epi_of_relation_vanishing
    n T l r d e he u hsource1 hrelationKernel2

/-- Over an affine base, `H¹`-vanishing for the kernel of the twisted relation
map onto its image makes the pushforward of that map an epimorphism.  This is the
cohomological epimorphism needed on the sheaf side of the relation-generation
field of next-degree saturation. -/
theorem reconstructedNextDegreeRelationImagePushforwardMap_epi_of_subsingleton_H_one
    (n : ℕ) (T : Scheme.{u}) [IsAffine T] (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (hvan : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (kernel (Modules.tensorMapLeft
          (Abelian.factorThruImage
            (reconstructedRelation' n T l r d e he u))
          (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ))))).H 1)) :
    Epi ((Modules.pushforward (projectiveSpaceOverπ n T)).map
      (Modules.tensorMapLeft
        (Abelian.factorThruImage
          (reconstructedRelation' n T l r d e he u))
        (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ)))) := by
  let f := reconstructedRelation' n T l r d e he u
  let O := projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ)
  let g := Modules.tensorMapLeft (Abelian.factorThruImage f) O
  haveI hkeruqc : (kernel u).IsQuasicoherent :=
    Modules.kernel_isQuasicoherent u
  haveI hpullKqc : ((Modules.pullback
      (projectiveSpaceOverπ n T)).obj (kernel u)).IsQuasicoherent :=
    Modules.isQuasicoherent_pullback (projectiveSpaceOverπ n T) _
  haveI hAqc : (Modules.tensor
      ((Modules.pullback (projectiveSpaceOverπ n T)).obj (kernel u))
      (projectiveSpaceOverTwist n T (-(d : ℤ)))).IsQuasicoherent := by
    change (projectiveSpaceOverTwistModule
      ((Modules.pullback (projectiveSpaceOverπ n T)).obj (kernel u))
      (-(d : ℤ))).IsQuasicoherent
    infer_instance
  haveI hFqc : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)).IsQuasicoherent :=
    Modules.projectiveSpaceOverTwistCoproduct_isQuasicoherent _ n T _
  haveI hIQC : (Abelian.image f).IsQuasicoherent := by
    dsimp only [Abelian.image]
    letI : (cokernel f).IsQuasicoherent :=
      Modules.isQuasicoherent_cokernel f
    exact Modules.kernel_isQuasicoherent (cokernel.π f)
  haveI hAOqc : (Modules.tensor
      (Modules.tensor
        ((Modules.pullback (projectiveSpaceOverπ n T)).obj (kernel u))
        (projectiveSpaceOverTwist n T (-(d : ℤ)))) O).IsQuasicoherent := by
    change (projectiveSpaceOverTwistModule
      (Modules.tensor
        ((Modules.pullback (projectiveSpaceOverπ n T)).obj (kernel u))
        (projectiveSpaceOverTwist n T (-(d : ℤ))))
      ((d + 1 : ℕ) : ℤ)).IsQuasicoherent
    infer_instance
  haveI hIOqc : (Modules.tensor (Abelian.image f) O).IsQuasicoherent := by
    change (projectiveSpaceOverTwistModule (Abelian.image f)
      ((d + 1 : ℕ) : ℤ)).IsQuasicoherent
    infer_instance
  haveI : Epi g := by
    dsimp only [g]
    infer_instance
  exact Modules.projectiveSpacePushforward_map_epi_of_subsingleton_H_one_kernel
    n T g hvan

/-- The pushforward of the twisted image of the reconstructed relation is
canonically the kernel of the finite-monomial reconstructed pushforward map. -/
noncomputable def reconstructedNextDegreeRelationImagePushforwardIsoKernel
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E) :
    (Modules.pushforward (projectiveSpaceOverπ n T)).obj
        (Modules.tensor
          (Abelian.image (reconstructedRelation' n T l r d e he u))
          (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ))) ≅
      kernel (quotGrassmannianFreeMap n T l r
        (reconstructedQuotientMap' n T l r d e he u)
        (d + 1) (e + 1) (by omega)) :=
  (Modules.pushforward (projectiveSpaceOverπ n T)).mapIso
      (projectiveSpaceOverTwistTensorKernelIso n T
        (reconstructedQuotientMap' n T l r d e he u)
        ((d + 1 : ℕ) : ℤ)) ≪≫
    (quotGrassmannianTwistedKernelAdjunctIso n T l r
      (reconstructedQuotientMap' n T l r d e he u)
      (d + 1) (e + 1) (by omega)).symm

/-- The remaining comparison needed to identify degree-one algebraic relations
with all pushed-forward relations in the reconstructed presentation.

The source isomorphism is the expected projection-formula and degree-one-monomial
basis calculation.  The compatibility field says that, after mapping onto the
twisted image of the reconstructed relation and applying the canonical kernel
identification, it is exactly the algebraic reconstructed-kernel lift. -/
structure TwistedFreeNextDegreeRelationSourcePushforwardComparison
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E) where
  /-- Degree-one copies of the base relation kernel are the pushed-forward
  twisted relation source. -/
  sourceIso :
    (∐ fun _ : ULift.{u} (Fin (n + 1)) ↦ kernel u) ≅
      (Modules.pushforward (projectiveSpaceOverπ n T)).obj
        (Modules.tensor
          (Modules.tensor
            ((Modules.pullback (projectiveSpaceOverπ n T)).obj (kernel u))
            (projectiveSpaceOverTwist n T (-(d : ℤ))))
          (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ)))
  /-- The source identification intertwines the relation-to-image map with the
  algebraic reconstructed-kernel lift. -/
  compatibility :
    sourceIso.hom ≫
        (Modules.pushforward (projectiveSpaceOverπ n T)).map
          (Modules.tensorMapLeft
            (Abelian.factorThruImage
              (reconstructedRelation' n T l r d e he u))
            (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ))) ≫
        (reconstructedNextDegreeRelationImagePushforwardIsoKernel
          n T l r d e he u).hom =
      twistedFreeNextDegreeReconstructedKernelLift n T l r d e he u

/-- Over an affine base, the source comparison and `H¹`-vanishing for the
twisted relation kernel imply the relation-generation epimorphism in next-degree
saturation. -/
theorem reconstructedNextDegreeRelationKernelLift_epi_of_subsingleton_H_one
    (n : ℕ) (T : Scheme.{u}) [IsAffine T] (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (hvan : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (kernel (Modules.tensorMapLeft
          (Abelian.factorThruImage
            (reconstructedRelation' n T l r d e he u))
          (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ))))).H 1))
    (hcomparison : TwistedFreeNextDegreeRelationSourcePushforwardComparison
      n T l r d e he u) :
    Epi (twistedFreeNextDegreeReconstructedKernelLift
      n T l r d e he u) := by
  letI : Epi ((Modules.pushforward (projectiveSpaceOverπ n T)).map
      (Modules.tensorMapLeft
        (Abelian.factorThruImage
          (reconstructedRelation' n T l r d e he u))
        (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ)))) :=
    reconstructedNextDegreeRelationImagePushforwardMap_epi_of_subsingleton_H_one
      n T l r d e he u hvan
  rw [← hcomparison.compatibility]
  infer_instance

/-- Three explicit cohomology vanishings for the reconstructed presentation,
together with the canonical source comparison, imply full next-degree
saturation over an affine base. -/
theorem twistedFreeNextDegreeReconstructionSaturation_of_relation_vanishing
    (n : ℕ) (T : Scheme.{u}) [IsAffine T] (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (hsource1 : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (Modules.tensor
          (Modules.tensor
            ((Modules.pullback (projectiveSpaceOverπ n T)).obj (kernel u))
            (projectiveSpaceOverTwist n T (-(d : ℤ))))
          (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ)))).H 1))
    (hrelationKernel1 : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (kernel (Modules.tensorMapLeft
          (Abelian.factorThruImage
            (reconstructedRelation' n T l r d e he u))
          (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ))))).H 1))
    (hrelationKernel2 : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (kernel (Modules.tensorMapLeft
          (Abelian.factorThruImage
            (reconstructedRelation' n T l r d e he u))
          (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ))))).H 2))
    (hcomparison : TwistedFreeNextDegreeRelationSourcePushforwardComparison
      n T l r d e he u) :
    TwistedFreeNextDegreeReconstructionSaturation n T l r d e he u where
  reconstructedPushforwardMap_epi :=
    reconstructedNextDegreePushforwardMap_epi_of_relation_vanishing
      n T l r d e he u hsource1 hrelationKernel2
  relationKernelLift_epi :=
    reconstructedNextDegreeRelationKernelLift_epi_of_subsingleton_H_one
      n T l r d e he u hrelationKernel1 hcomparison

/-- Full next-degree saturation follows from `H¹` of the pullback relation
coefficient twisted by `O(1)`, `H¹` and `H²` of the twisted relation kernel,
and the relation-source pushforward comparison. -/
theorem twistedFreeNextDegreeReconstructionSaturation_of_pullback_one_vanishing
    (n : ℕ) (T : Scheme.{u}) [IsAffine T] (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (hpullback1 : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (projectiveSpaceOverTwistModule
          ((Modules.pullback (projectiveSpaceOverπ n T)).obj (kernel u)) 1)).H 1))
    (hrelationKernel1 : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (kernel (Modules.tensorMapLeft
          (Abelian.factorThruImage
            (reconstructedRelation' n T l r d e he u))
          (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ))))).H 1))
    (hrelationKernel2 : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (kernel (Modules.tensorMapLeft
          (Abelian.factorThruImage
            (reconstructedRelation' n T l r d e he u))
          (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ))))).H 2))
    (hcomparison : TwistedFreeNextDegreeRelationSourcePushforwardComparison
      n T l r d e he u) :
    TwistedFreeNextDegreeReconstructionSaturation n T l r d e he u where
  reconstructedPushforwardMap_epi :=
    reconstructedNextDegreePushforwardMap_epi_of_pullback_one_vanishing
      n T l r d e he u hpullback1 hrelationKernel2
  relationKernelLift_epi :=
    reconstructedNextDegreeRelationKernelLift_epi_of_subsingleton_H_one
      n T l r d e he u hrelationKernel1 hcomparison

end AlgebraicGeometry.Scheme

end

end
