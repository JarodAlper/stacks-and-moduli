module

public import StacksAndModuli.API.AffineQuasicoherentEpi
public import StacksAndModuli.API.ProjectiveGammaStarMultiplicationComparison
public import StacksAndModuli.API.ProjectiveOneStepIteratedBaseChange
public import StacksAndModuli.API.QuasicoherentFiniteCoproduct
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianNextDegreeSourceComparison
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianUniversalCompatibility
public import StacksAndModuli.API.TwistedFreeQuotKernelGlobalGeneration

/-!
# Kernel multiplication and reconstructed next-degree relations

For an actual twisted-free Quot presentation, the reconstructed relation map in degree
`d + 1` is conjugate to multiplication by projective variables on the degree-`d`
pushforward of the presentation kernel.  This file constructs the source and target
isomorphisms, proves the multiplication square, and transfers epimorphy across it.

Over a noetherian affine base, the existing uniform regularity theorem makes kernel
multiplication epimorphic in all sufficiently large degrees.  Together with uniform
global generation, this simultaneously yields a reflection witness
`ReconstructedRelationPresentsKernel` and epimorphic reconstructed relations in the
next degree for every actual Quot family with the prescribed Hilbert polynomial.

Main declarations:

* `Scheme.twistedFreeNextDegreeReconstructedKernelLift_comp_successorKernelIso`;
* `Scheme.twistedFreeNextDegreeReconstructedKernelLift_epi_of_reflection`;
* `ProjectiveSpace.exists_bound_projectiveTwistedPushforwardMul_epi_twistedFreeQuotKernel`;
* `ProjectiveSpace.exists_bound_reconstruction_reflection_and_nextDegreeRelation_epi`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry ProjectiveSpectrum.Twist

universe u

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The component of degree-one multiplication. -/
@[reassoc]
lemma projectiveTwistedPushforwardMul_ι
    {T : Scheme.{u}} (n : ℕ)
    (Q : (projectiveSpaceOver n T).Modules) (d : ℕ)
    (i : Fin ((n + 1).choose n)) :
    Sigma.ι (fun _ : Fin ((n + 1).choose n) ↦
        projectiveTwistedPushforward n Q d) i ≫
      projectiveTwistedPushforwardMul n Q d =
    (pushforward (projectiveSpaceOverπ n T)).map
      (projectiveTwistMulOne n Q d i) := by
  exact Sigma.ι_desc _ i

/-- Naturality of degree-one multiplication in the coefficient sheaf. -/
lemma projectiveTwistedPushforwardMul_naturality_component
    {T : Scheme.{u}} (n : ℕ)
    {Q Q' : (projectiveSpaceOver n T).Modules}
    (e : Q ≅ Q') (d : ℕ) (i : Fin ((n + 1).choose n)) :
    (projectiveTwistedPushforwardIso e d).hom ≫
        (pushforward (projectiveSpaceOverπ n T)).map
          (projectiveTwistMulOne n Q' d i) =
      (pushforward (projectiveSpaceOverπ n T)).map
          (projectiveTwistMulOne n Q d i) ≫
        (projectiveTwistedPushforwardIso e (d + 1)).hom := by
  change
    (pushforward (projectiveSpaceOverπ n T)).map
        (tensorMapLeft e.hom (projectiveSpaceOverTwist n T (d : ℤ))) ≫
      (pushforward (projectiveSpaceOverπ n T)).map
        (tensorMapRight Q'
          (Scheme.twistMonomialMulHom n T (d : ℤ) ((d + 1 : ℕ) : ℤ)
            1 (by omega) i)) =
    (pushforward (projectiveSpaceOverπ n T)).map
        (tensorMapRight Q
          (Scheme.twistMonomialMulHom n T (d : ℤ) ((d + 1 : ℕ) : ℤ)
            1 (by omega) i)) ≫
      (pushforward (projectiveSpaceOverπ n T)).map
        (tensorMapLeft e.hom
          (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ)))
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (pushforward (projectiveSpaceOverπ n T)).map
    (tensorMap_exchange e.hom
      (Scheme.twistMonomialMulHom n T (d : ℤ) ((d + 1 : ℕ) : ℤ)
        1 (by omega) i)).symm

/-- Naturality of one multiplication component for an arbitrary map. -/
lemma projectiveTwistedPushforwardMul_naturality_component_hom
    {T : Scheme.{u}} (n : ℕ)
    {Q Q' : (projectiveSpaceOver n T).Modules}
    (f : Q ⟶ Q') (d : ℕ) (i : Fin ((n + 1).choose n)) :
    (pushforward (projectiveSpaceOverπ n T)).map
          (tensorMapLeft f (projectiveSpaceOverTwist n T (d : ℤ))) ≫
        (pushforward (projectiveSpaceOverπ n T)).map
          (projectiveTwistMulOne n Q' d i) =
      (pushforward (projectiveSpaceOverπ n T)).map
          (projectiveTwistMulOne n Q d i) ≫
        (pushforward (projectiveSpaceOverπ n T)).map
          (tensorMapLeft f
            (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ))) := by
  change
    (pushforward (projectiveSpaceOverπ n T)).map
        (tensorMapLeft f (projectiveSpaceOverTwist n T (d : ℤ))) ≫
      (pushforward (projectiveSpaceOverπ n T)).map
        (tensorMapRight Q'
          (Scheme.twistMonomialMulHom n T (d : ℤ) ((d + 1 : ℕ) : ℤ)
            1 (by omega) i)) =
    (pushforward (projectiveSpaceOverπ n T)).map
        (tensorMapRight Q
          (Scheme.twistMonomialMulHom n T (d : ℤ) ((d + 1 : ℕ) : ℤ)
            1 (by omega) i)) ≫
      (pushforward (projectiveSpaceOverπ n T)).map
        (tensorMapLeft f
          (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ)))
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (pushforward (projectiveSpaceOverπ n T)).map
    (tensorMap_exchange f
      (Scheme.twistMonomialMulHom n T (d : ℤ) ((d + 1 : ℕ) : ℤ)
        1 (by omega) i)).symm

/-- Naturality of degree-one multiplication in the coefficient sheaf. -/
lemma projectiveTwistedPushforwardMul_naturality
    {T : Scheme.{u}} (n : ℕ)
    {Q Q' : (projectiveSpaceOver n T).Modules}
    (e : Q ≅ Q') (d : ℕ) :
    (Sigma.mapIso (fun _ : Fin ((n + 1).choose n) ↦
        projectiveTwistedPushforwardIso e d)).hom ≫
      projectiveTwistedPushforwardMul n Q' d =
    projectiveTwistedPushforwardMul n Q d ≫
      (projectiveTwistedPushforwardIso e (d + 1)).hom := by
  apply Sigma.hom_ext
  intro i
  rw [← Category.assoc, Sigma.ι_mapIso_hom]
  calc
    ((projectiveTwistedPushforwardIso e d).hom ≫
          Sigma.ι (fun _ : Fin ((n + 1).choose n) ↦
            projectiveTwistedPushforward n Q' d) i) ≫
        projectiveTwistedPushforwardMul n Q' d =
      (projectiveTwistedPushforwardIso e d).hom ≫
        (Sigma.ι (fun _ : Fin ((n + 1).choose n) ↦
            projectiveTwistedPushforward n Q' d) i ≫
          projectiveTwistedPushforwardMul n Q' d) :=
        Category.assoc _ _ _
    _ = (projectiveTwistedPushforwardIso e d).hom ≫
        (pushforward (projectiveSpaceOverπ n T)).map
          (projectiveTwistMulOne n Q' d i) :=
      congrArg (fun k ↦ (projectiveTwistedPushforwardIso e d).hom ≫ k)
        (projectiveTwistedPushforwardMul_ι n Q' d i)
    _ = (pushforward (projectiveSpaceOverπ n T)).map
          (projectiveTwistMulOne n Q d i) ≫
        (projectiveTwistedPushforwardIso e (d + 1)).hom :=
      projectiveTwistedPushforwardMul_naturality_component n e d i
    _ = (Sigma.ι (fun _ : Fin ((n + 1).choose n) ↦
            projectiveTwistedPushforward n Q d) i ≫
          projectiveTwistedPushforwardMul n Q d) ≫
        (projectiveTwistedPushforwardIso e (d + 1)).hom :=
      congrArg (fun k ↦ k ≫
          (projectiveTwistedPushforwardIso e (d + 1)).hom)
        (projectiveTwistedPushforwardMul_ι n Q d i).symm
    _ = Sigma.ι (fun _ : Fin ((n + 1).choose n) ↦
          projectiveTwistedPushforward n Q d) i ≫
        projectiveTwistedPushforwardMul n Q d ≫
          (projectiveTwistedPushforwardIso e (d + 1)).hom :=
      Category.assoc _ _ _

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Kernel identification in a fixed Grassmannian degree. -/
noncomputable def quotGrassmannianKernelTwistedPushforwardIso
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ)
    {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) :
    kernel (quotGrassmannianFreeMap n T l r p d e he) ≅
      Modules.projectiveTwistedPushforward n (kernel p) d :=
  quotGrassmannianTwistedKernelAdjunctIso n T l r p d e he ≪≫
    (Modules.pushforward (projectiveSpaceOverπ n T)).mapIso
      (projectiveSpaceOverTwistTensorKernelIso n T p (d : ℤ)).symm

/-- Characterization of the fixed-degree kernel identification. -/
@[reassoc]
lemma quotGrassmannianKernelTwistedPushforwardIso_hom_comp
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ)
    {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) :
    (quotGrassmannianKernelTwistedPushforwardIso
        n T l r p d e he).hom ≫
      (Modules.pushforward (projectiveSpaceOverπ n T)).map
        (Modules.tensorMapLeft (kernel.ι p)
          (projectiveSpaceOverTwist n T (d : ℤ))) =
    kernel.ι (quotGrassmannianFreeMap n T l r p d e he) ≫
      twistedFreeMonomialPushforwardMap n T l r d e he := by
  let O := projectiveSpaceOverTwist n T (d : ℤ)
  let kIso := projectiveSpaceOverTwistTensorKernelIso n T p (d : ℤ)
  let adj := quotGrassmannianTwistedKernelAdjunctIso n T l r p d e he
  have hadj := quotGrassmannianTwistedKernelAdjunctIso_hom_comp
    n T l r p d e he
  change adj.hom ≫
      (Modules.pushforward (projectiveSpaceOverπ n T)).map kIso.inv ≫
      (Modules.pushforward (projectiveSpaceOverπ n T)).map
        (Modules.tensorMapLeft (kernel.ι p) O) = _
  rw [← Functor.map_comp]
  have hk := PreservesKernel.iso_inv_ι
    (Modules.tensorRightFunctor O) p
  change kIso.inv ≫ Modules.tensorMapLeft (kernel.ι p) O =
    kernel.ι (Modules.tensorMapLeft p O) at hk
  rw [hk]
  exact hadj

/-- Reindexing of projective variables by the degree-one monomial basis. -/
noncomputable def twistedFreeDegreeOneMonomialIndexEquiv (n : ℕ) :
    ULift.{u} (Fin (n + 1)) ≃ Fin ((n + 1).choose n) :=
  Equiv.ulift.trans
    (ProjectiveSpace.GradedModule.degreeOneMonomialIndexEquiv n)

@[simp]
lemma twistedFreeDegreeOneMonomialIndexEquiv_apply
    (n : ℕ) (a : ULift.{u} (Fin (n + 1))) :
    twistedFreeDegreeOneMonomialIndexEquiv n a =
      twistedFreeDegreeOneMonomialIndex n a.down := by
  rfl

/-- Source identification for the kernel-multiplication square. -/
noncomputable def quotGrassmannianKernelMulSourceIso
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ)
    {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) :
    (∐ fun _ : ULift.{u} (Fin (n + 1)) ↦
      kernel (quotGrassmannianFreeMap n T l r p d e he)) ≅
      (∐ fun _ : Fin ((n + 1).choose n) ↦
        Modules.projectiveTwistedPushforward n (kernel p) d) :=
  Sigma.mapIso (fun _ : ULift.{u} (Fin (n + 1)) ↦
      quotGrassmannianKernelTwistedPushforwardIso
        n T l r p d e he) ≪≫
    Sigma.reindex (twistedFreeDegreeOneMonomialIndexEquiv n)
      (fun _ : Fin ((n + 1).choose n) ↦
        Modules.projectiveTwistedPushforward n (kernel p) d)

/-- The source identification on a degree-one variable summand. -/
lemma quotGrassmannianKernelMulSourceIso_ι_hom
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ)
    {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    (a : ULift.{u} (Fin (n + 1))) :
    Sigma.ι (fun _ : ULift.{u} (Fin (n + 1)) ↦
        kernel (quotGrassmannianFreeMap n T l r p d e he)) a ≫
      (quotGrassmannianKernelMulSourceIso
        n T l r p d e he).hom =
    (quotGrassmannianKernelTwistedPushforwardIso
        n T l r p d e he).hom ≫
      Sigma.ι (fun _ : Fin ((n + 1).choose n) ↦
        Modules.projectiveTwistedPushforward n (kernel p) d)
        (twistedFreeDegreeOneMonomialIndexEquiv n a) := by
  change Sigma.ι _ a ≫
      (Sigma.mapIso _).hom ≫ (Sigma.reindex _ _).hom = _
  rw [← Category.assoc, Sigma.ι_mapIso_hom]
  rw [Category.assoc]
  exact congrArg
    (fun z ↦ (quotGrassmannianKernelTwistedPushforwardIso
      n T l r p d e he).hom ≫ z)
    (Sigma.ι_reindex_hom
      (twistedFreeDegreeOneMonomialIndexEquiv n)
      (fun _ : Fin ((n + 1).choose n) ↦
        Modules.projectiveTwistedPushforward n (kernel p) d) a)

/-- The reflection target isomorphism intertwines the successor monomial maps. -/
lemma reconstructed_quotGrassmannianFreeMap_comp_targetIso
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    [Epi p]
    (D : ReconstructedRelationPresentsKernel n T l r d e he u p) :
    quotGrassmannianFreeMap n T l r
        (reconstructedQuotientMap' n T l r d e he u)
        (d + 1) (e + 1) (by omega) ≫
      (Modules.projectiveTwistedPushforwardIso D.quotientIso (d + 1)).hom =
    quotGrassmannianFreeMap n T l r p
      (d + 1) (e + 1) (by omega) := by
  calc
    _ = quotGrassmannianFreeMap n T l r
        (reconstructedQuotientMap' n T l r d e he u ≫
          D.quotientIso.hom) (d + 1) (e + 1) (by omega) :=
      quotGrassmannianFreeMap_comp_targetIso n T l r _ _
        (d + 1) (e + 1) (by omega)
    _ = _ := congrArg
      (fun k ↦ quotGrassmannianFreeMap n T l r k
        (d + 1) (e + 1) (by omega))
      D.reconstructedQuotientMap'_comp_quotientIso_hom

/-- Transport of the successor kernel through reconstruction reflection. -/
noncomputable def reconstructedSuccessorKernelIso
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    [Epi p]
    (D : ReconstructedRelationPresentsKernel n T l r d e he u p) :
    kernel (quotGrassmannianFreeMap n T l r
      (reconstructedQuotientMap' n T l r d e he u)
      (d + 1) (e + 1) (by omega)) ≅
      Modules.projectiveTwistedPushforward n (kernel p) (d + 1) := by
  let qR := quotGrassmannianFreeMap n T l r
    (reconstructedQuotientMap' n T l r d e he u)
    (d + 1) (e + 1) (by omega)
  let qP := quotGrassmannianFreeMap n T l r p
    (d + 1) (e + 1) (by omega)
  let t := (Modules.projectiveTwistedPushforwardIso
    D.quotientIso (d + 1)).hom
  let h : qR ≫ t = qP :=
    reconstructed_quotGrassmannianFreeMap_comp_targetIso
      n T l r d e he u p D
  exact (kernelCompMono qR t).symm ≪≫ kernelIsoOfEq h ≪≫
    quotGrassmannianKernelTwistedPushforwardIso
      n T l r p (d + 1) (e + 1) (by omega)

set_option maxHeartbeats 800000 in
-- Normalizing the composite of `kernelCompMono`, `kernelIsoOfEq`, and the twisted
-- pushforward kernel comparison exceeds the default elaboration budget.
/-- Characterization of the reflected successor-kernel identification. -/
lemma reconstructedSuccessorKernelIso_hom_comp
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    [Epi p]
    (D : ReconstructedRelationPresentsKernel n T l r d e he u p) :
    (reconstructedSuccessorKernelIso n T l r d e he u p D).hom ≫
      (Modules.pushforward (projectiveSpaceOverπ n T)).map
        (Modules.tensorMapLeft (kernel.ι p)
          (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ))) =
    kernel.ι (quotGrassmannianFreeMap n T l r
        (reconstructedQuotientMap' n T l r d e he u)
        (d + 1) (e + 1) (by omega)) ≫
      twistedFreeMonomialPushforwardMap n T l r
        (d + 1) (e + 1) (by omega) := by
  let qR := quotGrassmannianFreeMap n T l r
    (reconstructedQuotientMap' n T l r d e he u)
    (d + 1) (e + 1) (by omega)
  let qP := quotGrassmannianFreeMap n T l r p
    (d + 1) (e + 1) (by omega)
  let t := (Modules.projectiveTwistedPushforwardIso
    D.quotientIso (d + 1)).hom
  let h : qR ≫ t = qP :=
    reconstructed_quotGrassmannianFreeMap_comp_targetIso
      n T l r d e he u p D
  let c := kernelCompMono qR t
  let k := kernelIsoOfEq h
  let s := quotGrassmannianKernelTwistedPushforwardIso
    n T l r p (d + 1) (e + 1) (by omega)
  have hs := quotGrassmannianKernelTwistedPushforwardIso_hom_comp
    n T l r p (d + 1) (e + 1) (by omega)
  rw [show reconstructedSuccessorKernelIso n T l r d e he u p D =
    c.symm ≪≫ k ≪≫ s by rfl]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [hs]
  dsimp only [k]
  let m := twistedFreeMonomialPushforwardMap n T l r
    (d + 1) (e + 1) (by omega)
  have hk : (kernelIsoOfEq h).hom ≫ kernel.ι qP =
      kernel.ι (qR ≫ t) := kernelIsoOfEq_hom_comp_ι h
  have hc : c.inv ≫ kernel.ι (qR ≫ t) = kernel.ι qR := by
    dsimp only [c, kernelCompMono]
    exact kernel.lift_ι _ _ _
  calc
    c.inv ≫ (kernelIsoOfEq h).hom ≫ kernel.ι qP ≫ m =
        c.inv ≫ ((kernelIsoOfEq h).hom ≫ kernel.ι qP) ≫ m := by
      simp only [Category.assoc]
    _ = c.inv ≫ kernel.ι (qR ≫ t) ≫ m :=
      congrArg (fun z ↦ c.inv ≫ z ≫ m) hk
    _ = kernel.ι qR ≫ m := congrArg (fun z ↦ z ≫ m) hc

set_option maxHeartbeats 800000 in
-- After cancellation, elaborating the summandwise square retains both dependent kernel
-- transports and the projective-twist tensor instance tower.
/-- The kernel-multiplication square. -/
theorem twistedFreeNextDegreeReconstructedKernelLift_comp_successorKernelIso
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ))
    {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    [Epi p]
    (D : ReconstructedRelationPresentsKernel n T l r d e he
      (quotGrassmannianFreeMap n T l r p d e he) p) :
    (quotGrassmannianKernelMulSourceIso n T l r p d e he).hom ≫
        Modules.projectiveTwistedPushforwardMul n (kernel p) d =
      twistedFreeNextDegreeReconstructedKernelLift n T l r d e he
          (quotGrassmannianFreeMap n T l r p d e he) ≫
        (reconstructedSuccessorKernelIso n T l r d e he
          (quotGrassmannianFreeMap n T l r p d e he) p D).hom := by
  let u := quotGrassmannianFreeMap n T l r p d e he
  let F := ∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)
  let qR := quotGrassmannianFreeMap n T l r
    (reconstructedQuotientMap' n T l r d e he u)
    (d + 1) (e + 1) (by omega)
  let iNext := (Modules.pushforward (projectiveSpaceOverπ n T)).map
    (Modules.tensorMapLeft (kernel.ι p)
      (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ)))
  haveI : Mono iNext := by
    dsimp only [iNext]
    letI : Mono (Modules.tensorMapLeft (kernel.ι p)
        (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ))) :=
      projectiveSpaceOverTwist_tensorMapLeft_mono n T (kernel.ι p)
        ((d + 1 : ℕ) : ℤ)
    exact Functor.map_mono (Modules.pushforward (projectiveSpaceOverπ n T)) _
  apply (cancel_mono iNext).mp
  apply Sigma.hom_ext
  intro a
  let j := twistedFreeDegreeOneMonomialIndexEquiv n a
  let kIso := quotGrassmannianKernelTwistedPushforwardIso
    n T l r p d e he
  let sIso := quotGrassmannianKernelMulSourceIso n T l r p d e he
  let tIso := reconstructedSuccessorKernelIso n T l r d e he u p D
  let g := twistedFreeNextDegreeReconstructedKernelLift n T l r d e he u
  let iDegree := (Modules.pushforward (projectiveSpaceOverπ n T)).map
    (Modules.tensorMapLeft (kernel.ι p)
      (projectiveSpaceOverTwist n T (d : ℤ)))
  let μK := Modules.projectiveTwistedPushforwardMul n (kernel p) d
  let μF := Modules.projectiveTwistedPushforwardMul n F d
  let mDegree := twistedFreeMonomialPushforwardMap n T l r d e he
  let mNext := twistedFreeMonomialPushforwardMap n T l r
    (d + 1) (e + 1) (by omega)
  have hs := quotGrassmannianKernelMulSourceIso_ι_hom
    n T l r p d e he a
  have hk := quotGrassmannianKernelTwistedPushforwardIso_hom_comp
    n T l r p d e he
  have hμK := Modules.projectiveTwistedPushforwardMul_ι
    n (kernel p) d j
  have hnat := Modules.projectiveTwistedPushforwardMul_naturality_component_hom
    n (kernel.ι p) d j
  have ht := reconstructedSuccessorKernelIso_hom_comp
    n T l r d e he u p D
  have hg := twistedFreeNextDegreeReconstructedKernelLift_comp
    n T l r d e he u
  have hrel := twistedFreeNextDegreeRelation_comp_monomialPushforwardMap
    n T l r d e he u
  change Sigma.ι _ a ≫ sIso.hom ≫ μK ≫ iNext =
    Sigma.ι _ a ≫ g ≫ tIso.hom ≫ iNext
  slice_lhs 1 2 => rw [hs]
  slice_lhs 2 3 => rw [hμK]
  slice_lhs 2 3 => rw [← hnat]
  slice_lhs 1 2 => rw [hk]
  slice_rhs 3 4 => rw [ht]
  slice_rhs 2 3 => rw [hg]
  slice_rhs 2 3 => rw [hrel]
  dsimp only [reconstructedGeneratedNextDegreeRelation]
  slice_rhs 1 2 => rw [Sigma.ι_desc]
  rfl

/-- Epimorphy transfer across the kernel-multiplication square. -/
theorem twistedFreeNextDegreeReconstructedKernelLift_epi_of_reflection
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ))
    {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    [Epi p]
    (D : ReconstructedRelationPresentsKernel n T l r d e he
      (quotGrassmannianFreeMap n T l r p d e he) p)
    (hmul : Epi (Modules.projectiveTwistedPushforwardMul n (kernel p) d)) :
    Epi (twistedFreeNextDegreeReconstructedKernelLift n T l r d e he
      (quotGrassmannianFreeMap n T l r p d e he)) := by
  let s := (quotGrassmannianKernelMulSourceIso n T l r p d e he).hom
  let g := twistedFreeNextDegreeReconstructedKernelLift n T l r d e he
    (quotGrassmannianFreeMap n T l r p d e he)
  let t := (reconstructedSuccessorKernelIso n T l r d e he
    (quotGrassmannianFreeMap n T l r p d e he) p D).hom
  let μ := Modules.projectiveTwistedPushforwardMul n (kernel p) d
  letI : Epi μ := hmul
  haveI : Epi (s ≫ μ) := epi_comp s μ
  have h : s ≫ μ = g ≫ t :=
    twistedFreeNextDegreeReconstructedKernelLift_comp_successorKernelIso
      n T l r d e he p D
  haveI : Epi (g ≫ t) := h ▸ inferInstance
  exact (epi_comp_iff_of_isIso g t).mp inferInstance

/-- The geometric regularity endpoint for next-degree relation generation. -/
theorem twistedFreeNextDegreeReconstructedKernelLift_epi_of_globalGeneration
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ))
    {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    [Epi p]
    (hgen : TwistedFreeQuotKernelIsGloballyGenerated n T l r p d)
    (hmul : Epi (Modules.projectiveTwistedPushforwardMul n (kernel p) d)) :
    Epi (twistedFreeNextDegreeReconstructedKernelLift n T l r d e he
      (quotGrassmannianFreeMap n T l r p d e he)) := by
  letI : Epi (quotGrassmannianTwistedKernelMap n T l r p d e he) :=
    quotGrassmannianTwistedKernelMap_epi_of_isGloballyGenerated
      n T l r p d e he hgen
  let D := quotGrassmannianReconstructedRelationPresentsKernelOfTwistedKernelEpi
    n T l r p d e he
      (twistedFreeAmbientReconstructionCompatibility n T l r d e he)
  exact twistedFreeNextDegreeReconstructedKernelLift_epi_of_reflection
    n T l r d e he p D hmul

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

open GradedModule

theorem exists_bound_projectiveTwistedPushforwardMul_epi_twistedFreeQuotKernel
    (n r : ℕ) (hn : 0 < n) (l : ℤ) (P : Polynomial ℚ) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
      (Q : (Scheme.projectiveSpaceOver n (Spec (.of R))).Modules)
      (_ : Q.IsFinitePresentation)
      (q : (∐ fun _ : ULift.{u} (Fin r) ↦
        Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l)) ⟶ Q)
      (_ : Epi q)
      (_ : Q.FlatOver (Scheme.projectiveSpaceOverπ n (Spec (.of R))))
      (_ : Scheme.HasFiberwiseHilbertPolynomial Q P),
      Epi (Scheme.Modules.projectiveTwistedPushforwardMul n (kernel q) d) := by
  obtain ⟨d₀, hd₀, hspan⟩ :=
    exists_bound_mulSpan_cechHgr_gammaStar_kernel n r hn l P
  let D := d₀.toNat
  have hD : (D : ℤ) = d₀ := by
    dsimp only [D]
    exact Int.toNat_of_nonneg hd₀
  refine ⟨D, ?_⟩
  intro d hDd R _ _ Q hQfp q hq hflat hP
  let i := (projectiveSpaceOverSpecIso n R).inv
  let p := (Scheme.Modules.pullback i).map q
  let K := kernel p
  let K' := (Scheme.Modules.pullback i).obj (kernel q)
  let ΓK := Proj.gammaStar
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    (projSpecπ n R) K (stdVars n R)
  let ΓK' := Proj.gammaStar
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    (projSpecπ n R) K' (stdVars n R)
  haveI hp : Epi p := Functor.map_epi _ q
  haveI hAmbfp : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l)).IsFinitePresentation :=
    Scheme.Modules.projectiveSpaceOverTwistCoproduct_isFinitePresentation
      (ULift.{u} (Fin r)) n (Spec (.of R)) (-l)
  haveI hEfp : (projAmbient n r l (R := R)).IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  haveI hQ'fp : ((Scheme.Modules.pullback i).obj Q).IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  haveI hKfp : K.IsFinitePresentation :=
    Scheme.Modules.kernel_isFinitePresentation p
  haveI hKqc : K.IsQuasicoherent :=
    Scheme.Modules.kernel_isQuasicoherent p
  haveI hKtwistQc : ∀ a : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) K a).IsQuasicoherent :=
    fun a ↦ twistModule_std_isQuasicoherent K a
  have hd₀d : d₀ ≤ (d : ℤ) := by
    rw [← hD]
    exact_mod_cast hDd
  have hCech : (ΓK.cechHgr 0).mulSpan (d : ℤ) ((d + 1 : ℕ) : ℤ) = ⊤ :=
    hspan R Q hQfp hAmbfp p hp hflat hP (d : ℤ)
      ((d + 1 : ℕ) : ℤ) hd₀d (by omega)
  have hGamma : ΓK.mulSpan (d : ℤ) ((d + 1 : ℕ) : ℤ) = ⊤ := by
    apply GradedModule.mulSpan_eq_top_of_cechHgrZero_of_bijective_cechAug
    · exact bijective_gammaStar_cechAug_of_isFinitePresentation
        (projSpecπ n R) K (d : ℤ)
    · exact bijective_gammaStar_cechAug_of_isFinitePresentation
        (projSpecπ n R) K ((d + 1 : ℕ) : ℤ)
    · exact hCech
  let eK : K' ≅ K := PreservesKernel.iso (Scheme.Modules.pullback i) q
  have hGamma' : ΓK'.mulSpan (d : ℤ) ((d + 1 : ℕ) : ℤ) = ⊤ :=
    GradedModule.mulSpan_eq_top_of_iso
      (Proj.gammaStarMapIso
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (projSpecπ n R) (stdVars n R) eK).symm
      (d : ℤ) ((d + 1 : ℕ) : ℤ) hGamma
  let μ := Scheme.Modules.projectiveTwistedPushforwardMul n (kernel q) d
  have hsurj : Function.Surjective (Scheme.Modules.Hom.app μ ⊤) :=
    surjective_app_top_projectiveTwistedPushforwardMul_of_gammaStar_mulSpan
      (kernel q) d hGamma'
  letI : (kernel q).IsQuasicoherent := Scheme.Modules.kernel_isQuasicoherent q
  letI : (∐ fun _ : Fin ((n + 1).choose n) ↦
      Scheme.Modules.projectiveTwistedPushforward n (kernel q) d).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_coproduct_small _
  exact Scheme.Modules.epi_of_appTop_surjective μ hsurj

end AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A uniform noetherian-affine bound simultaneously supplies reflection of an actual
twisted-free Quot family from its Grassmannian point and generation of the reconstructed
relations in the next degree. -/
theorem exists_bound_reconstruction_reflection_and_nextDegreeRelation_epi
    (n r : ℕ) (hn : 0 < n) (l : ℤ) (P : Polynomial ℚ) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d → ∀ e : ℕ,
      (he : (d : ℤ) - l = (e : ℤ)) →
      ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
      (Q : (Scheme.projectiveSpaceOver n (Spec (.of R))).Modules)
      (_ : Q.IsFinitePresentation)
      (q : (∐ fun _ : ULift.{u} (Fin r) ↦
        Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l)) ⟶ Q)
      (_ : Epi q)
      (_ : Q.FlatOver (Scheme.projectiveSpaceOverπ n (Spec (.of R))))
      (_ : Scheme.HasFiberwiseHilbertPolynomial Q P),
      ∃ _Drel : Scheme.ReconstructedRelationPresentsKernel n (Spec (.of R))
          l r d e he (Scheme.quotGrassmannianFreeMap n (Spec (.of R))
            l r q d e he) q,
        Epi (Scheme.twistedFreeNextDegreeReconstructedKernelLift n
          (Spec (.of R)) l r d e he
          (Scheme.quotGrassmannianFreeMap n (Spec (.of R)) l r q d e he)) := by
  obtain ⟨Dgen, hgen⟩ :=
    exists_bound_pullbackPushforwardCounit_epi_twistedFreeQuotKernel_noetherian_affine
      n r hn l P
  obtain ⟨Dmul, hmul⟩ :=
    exists_bound_projectiveTwistedPushforwardMul_epi_twistedFreeQuotKernel
      n r hn l P
  refine ⟨max Dgen Dmul, ?_⟩
  intro d hd e he R _ _ Q hQfp q hq hflat hP
  have hdgen : Dgen ≤ d := le_trans (le_max_left _ _) hd
  have hdmul : Dmul ≤ d := le_trans (le_max_right _ _) hd
  letI : Epi q := hq
  have hglobal : Scheme.TwistedFreeQuotKernelIsGloballyGenerated
      n (Spec (.of R)) l r q d :=
    hgen d hdgen R Q hQfp q hq hflat hP
  have hmu : Epi (Scheme.Modules.projectiveTwistedPushforwardMul
      n (kernel q) d) := hmul d hdmul R Q hQfp q hq hflat hP
  letI : Epi (Scheme.quotGrassmannianTwistedKernelMap
      n (Spec (.of R)) l r q d e he) :=
    Scheme.quotGrassmannianTwistedKernelMap_epi_of_isGloballyGenerated
      n (Spec (.of R)) l r q d e he hglobal
  let Drel :=
    Scheme.quotGrassmannianReconstructedRelationPresentsKernelOfTwistedKernelEpi
      n (Spec (.of R)) l r q d e he
        (Scheme.twistedFreeAmbientReconstructionCompatibility
          n (Spec (.of R)) l r d e he)
  refine ⟨Drel, ?_⟩
  exact Scheme.twistedFreeNextDegreeReconstructedKernelLift_epi_of_reflection
    n (Spec (.of R)) l r d e he q Drel hmu

end AlgebraicGeometry.ProjectiveSpace
