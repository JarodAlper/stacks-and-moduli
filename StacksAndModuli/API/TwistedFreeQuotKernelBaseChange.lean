module

public import StacksAndModuli.API.PullbackPushforwardCounitBaseChangeEpi
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianCanonicalPackageFromGeometry
public import StacksAndModuli.API.OpenImmersionPullbackPushforwardCounitBaseChange
public import StacksAndModuli.API.RightExactFunctorKernelVanishing

/-!
# Base change of twisted-free Quot kernel generation

Relative global generation of the twisted kernel in the Quot-to-Grassmannian construction
is stable under arbitrary change of the parameter scheme.  The only presentation-specific
input is an epimorphism from the pullback of the old twisted kernel onto the twisted kernel
of the normalized pulled-back quotient.

This separates two logically distinct ingredients of noetherian approximation.  Once a flat
twisted-free quotient presentation has descended to a noetherian coefficient ring, its
eventual kernel-generation theorem propagates back to the original ring formally; neither
kernel preservation nor a pushforward Cohomology-and-Base-Change isomorphism is needed.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- Pullback of the tensorized twisted-free source, normalized to the standard
twisted-free source over the new base. -/
noncomputable def projectiveSpaceTwistedFreeTensorSourcePullbackIso
    (n r : ℕ) {T T' : Scheme.{u}} (g : T' ⟶ T)
    (l : ℤ) (d : ℕ) :
    (Modules.pullback (projectiveSpaceOverMap n g)).obj
        (Modules.tensor
          (∐ fun _ : ULift.{u} (Fin r) ↦
            projectiveSpaceOverTwist n T (-l))
          (projectiveSpaceOverTwist n T (d : ℤ))) ≅
      Modules.tensor
        (∐ fun _ : ULift.{u} (Fin r) ↦
          projectiveSpaceOverTwist n T' (-l))
        (projectiveSpaceOverTwist n T' (d : ℤ)) :=
  projectiveSpaceOverTwistModule_pullbackIso_nat n g
      (∐ fun _ : ULift.{u} (Fin r) ↦
        projectiveSpaceOverTwist n T (-l)) d ≪≫
    Modules.tensorLeftIso
      (projectiveSpaceOverTwistedFree_pullbackIso n r l g)
      (projectiveSpaceOverTwist n T' (d : ℤ))

/-- The normalized pullback comparisons intertwine a tensorized Quot map with the
tensorization of its standard pulled-back presentation. -/
lemma projectiveSpaceTwistedFreeTensorPullbackIso_naturality
    (n r : ℕ) {T T' : Scheme.{u}} (g : T' ⟶ T)
    (l : ℤ) {Q : (projectiveSpaceOver n T).Modules}
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)) ⟶ Q) (d : ℕ) :
    (Modules.pullback (projectiveSpaceOverMap n g)).map
          (Modules.tensorMapLeft q
            (projectiveSpaceOverTwist n T (d : ℤ))) ≫
        (projectiveSpaceOverTwistModule_pullbackIso_nat n g Q d).hom =
      (projectiveSpaceTwistedFreeTensorSourcePullbackIso
          n r g l d).hom ≫
        Modules.tensorMapLeft
          (projectiveSpaceTwistedFreeQuotientPullback n r g l q)
          (projectiveSpaceOverTwist n T' (d : ℤ)) := by
  have hn := projectiveSpaceOverTwistModule_pullbackIso_nat_naturality
    n g q d
  refine hn.trans ?_
  let EF := projectiveSpaceOverTwistModule_pullbackIso_nat n g
    (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) d
  let eF := projectiveSpaceOverTwistedFree_pullbackIso n r l g
  let DT := projectiveSpaceOverTwist n T' (d : ℤ)
  let f := (Modules.pullback (projectiveSpaceOverMap n g)).map q
  have hc : Modules.tensorMapLeft eF.hom DT ≫
        Modules.tensorMapLeft (eF.inv ≫ f) DT =
      Modules.tensorMapLeft f DT := by
    exact (Modules.tensorMapLeft_comp eF.hom (eF.inv ≫ f) DT).symm.trans <| by
      rw [Iso.hom_inv_id_assoc]
  exact (congrArg (fun k ↦ EF.hom ≫ k) hc.symm).trans <|
    (Category.assoc EF.hom (Modules.tensorMapLeft eF.hom DT)
      (Modules.tensorMapLeft (eF.inv ≫ f) DT)).symm

/-- The canonical map from the pullback of a twisted Quot kernel to the kernel of the
standard pulled-back twisted-free presentation. -/
noncomputable def projectiveSpaceTwistedFreeQuotKernelPullbackHom
    (n r : ℕ) {T T' : Scheme.{u}} (g : T' ⟶ T) (l : ℤ)
    {Q : (projectiveSpaceOver n T).Modules}
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)) ⟶ Q) (d : ℕ) :
    (Modules.pullback (projectiveSpaceOverMap n g)).obj
        (kernel (Modules.tensorMapLeft q
          (projectiveSpaceOverTwist n T (d : ℤ)))) ⟶
      kernel (Modules.tensorMapLeft
        (projectiveSpaceTwistedFreeQuotientPullback n r g l q)
        (projectiveSpaceOverTwist n T' (d : ℤ))) :=
  kernelComparison
      (Modules.tensorMapLeft q
        (projectiveSpaceOverTwist n T (d : ℤ)))
      (Modules.pullback (projectiveSpaceOverMap n g)) ≫
    (kernel.mapIso (f :=
        (Modules.pullback (projectiveSpaceOverMap n g)).map
          (Modules.tensorMapLeft q
            (projectiveSpaceOverTwist n T (d : ℤ))))
      (Modules.tensorMapLeft
        (projectiveSpaceTwistedFreeQuotientPullback n r g l q)
        (projectiveSpaceOverTwist n T' (d : ℤ)))
      (projectiveSpaceTwistedFreeTensorSourcePullbackIso n r g l d)
      (projectiveSpaceOverTwistModule_pullbackIso_nat n g Q d)
      (projectiveSpaceTwistedFreeTensorPullbackIso_naturality
        n r g l q d)).hom

/-- The canonical map from the pulled-back twisted kernel to the new normalized twisted
kernel is epimorphic.  This is right exactness of pullback; preservation of kernels is not
required. -/
instance projectiveSpaceTwistedFreeQuotKernelPullbackHom_epi
    (n r : ℕ) {T T' : Scheme.{u}} (g : T' ⟶ T) (l : ℤ)
    {Q : (projectiveSpaceOver n T).Modules}
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)) ⟶ Q) [Epi q] (d : ℕ) :
    Epi (projectiveSpaceTwistedFreeQuotKernelPullbackHom n r g l q d) := by
  let p := Modules.tensorMapLeft q
    (projectiveSpaceOverTwist n T (d : ℤ))
  haveI : Epi p := inferInstance
  haveI : Epi (kernelComparison p
      (Modules.pullback (projectiveSpaceOverMap n g))) :=
    CategoryTheory.kernelComparison_epi_of_isLeftAdjoint _ p
  dsimp only [projectiveSpaceTwistedFreeQuotKernelPullbackHom]
  infer_instance

/-- Changing the target of a twisted-free quotient presentation by an isomorphism induces
an isomorphism of its twisted kernels. -/
noncomputable def projectiveSpaceTwistedFreeQuotKernelCompIso
    (n r : ℕ) (T : Scheme.{u}) (l : ℤ)
    {Q Q' : (projectiveSpaceOver n T).Modules}
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    (e : Q ≅ Q') (d : ℕ) :
    kernel (Modules.tensorMapLeft q
        (projectiveSpaceOverTwist n T (d : ℤ))) ≅
      kernel (Modules.tensorMapLeft (q ≫ e.hom)
        (projectiveSpaceOverTwist n T (d : ℤ))) :=
  kernel.mapIso
    (Modules.tensorMapLeft q
      (projectiveSpaceOverTwist n T (d : ℤ)))
    (Modules.tensorMapLeft (q ≫ e.hom)
      (projectiveSpaceOverTwist n T (d : ℤ)))
    (Iso.refl _)
    (Modules.tensorLeftIso e
      (projectiveSpaceOverTwist n T (d : ℤ)))
    (by
      simp only [Iso.refl_hom, Category.id_comp, Modules.tensorLeftIso]
      exact (Modules.tensorMapLeft_comp q e.hom
        (projectiveSpaceOverTwist n T (d : ℤ))).symm)

/-- Kernel generation for a twisted-free quotient survives arbitrary base change when the
new twisted kernel is an epimorphic image of the pulled-back old twisted kernel. -/
theorem TwistedFreeQuotKernelIsGloballyGenerated.pullback_of_kernelEpi
    (n r : ℕ) {T T' : Scheme.{u}} (g : T' ⟶ T) (l : ℤ)
    {Q : (projectiveSpaceOver n T).Modules}
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    {Q' : (projectiveSpaceOver n T').Modules}
    (q' : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T' (-l)) ⟶ Q')
    (d : ℕ)
    (e : (Modules.pullback (projectiveSpaceOverMap n g)).obj
        (kernel (Modules.tensorMapLeft q
          (projectiveSpaceOverTwist n T (d : ℤ)))) ⟶
      kernel (Modules.tensorMapLeft q'
        (projectiveSpaceOverTwist n T' (d : ℤ))))
    [Epi e]
    (hgen : TwistedFreeQuotKernelIsGloballyGenerated n T l r q d) :
    TwistedFreeQuotKernelIsGloballyGenerated n T' l r q' d := by
  let M := kernel (Modules.tensorMapLeft q
    (projectiveSpaceOverTwist n T (d : ℤ)))
  let M' := kernel (Modules.tensorMapLeft q'
    (projectiveSpaceOverTwist n T' (d : ℤ)))
  letI : Epi ((Modules.pullbackPushforwardAdjunction
      (projectiveSpaceOverπ n T)).counit.app M) := hgen
  exact Modules.pullbackPushforwardCounit_epi_of_epi_pullback_of_comm
    (projectiveSpaceOverπ n T) (projectiveSpaceOverπ n T') g
    (projectiveSpaceOverMap n g) (projectiveSpaceOverMap_π n g) M M' e

/-- Relative global generation of the twisted kernel is unchanged when the target of the
quotient presentation is transported through an isomorphism. -/
theorem TwistedFreeQuotKernelIsGloballyGenerated.comp_iso
    (n r : ℕ) (T : Scheme.{u}) (l : ℤ)
    {Q Q' : (projectiveSpaceOver n T).Modules}
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    (e : Q ≅ Q') (d : ℕ)
    (hgen : TwistedFreeQuotKernelIsGloballyGenerated n T l r q d) :
    TwistedFreeQuotKernelIsGloballyGenerated n T l r (q ≫ e.hom) d := by
  let M := kernel (Modules.tensorMapLeft q
    (projectiveSpaceOverTwist n T (d : ℤ)))
  let M' := kernel (Modules.tensorMapLeft (q ≫ e.hom)
    (projectiveSpaceOverTwist n T (d : ℤ)))
  let eK : M ≅ M' :=
    projectiveSpaceTwistedFreeQuotKernelCompIso n r T l q e d
  letI : Epi ((Modules.pullbackPushforwardAdjunction
      (projectiveSpaceOverπ n T)).counit.app M) := hgen
  exact CategoryTheory.Adjunction.epi_counit_of_iso
    (Modules.pullbackPushforwardAdjunction (projectiveSpaceOverπ n T)) eK.symm

/-- Relative global generation of the twisted kernel is preserved by arbitrary base change,
with the quotient presentation normalized to the standard twisted-free source on the new
base. -/
theorem TwistedFreeQuotKernelIsGloballyGenerated.pullback
    (n r : ℕ) {T T' : Scheme.{u}} (g : T' ⟶ T) (l : ℤ)
    {Q : (projectiveSpaceOver n T).Modules}
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    [Epi q] (d : ℕ)
    (hgen : TwistedFreeQuotKernelIsGloballyGenerated n T l r q d) :
    TwistedFreeQuotKernelIsGloballyGenerated n T' l r
      (projectiveSpaceTwistedFreeQuotientPullback n r g l q) d :=
  pullback_of_kernelEpi n r g l q
    (projectiveSpaceTwistedFreeQuotientPullback n r g l q) d
    (projectiveSpaceTwistedFreeQuotKernelPullbackHom n r g l q d) hgen

/-- Relative global generation of the twisted kernel is stable under pullback of a
`QuotientPullbackData`; both the standard twisted-free source and the normalized quotient
target are handled canonically. -/
theorem TwistedFreeQuotKernelIsGloballyGenerated.pullback_quotientPullbackData
    (n r : ℕ) (S : Scheme.{u}) (l : ℤ)
    {T T' : Over S} (g : T' ⟶ T)
    (a : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T)
    (d : ℕ)
    (hgen : TwistedFreeQuotKernelIsGloballyGenerated n T.left l r
      (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T a) d) :
    TwistedFreeQuotKernelIsGloballyGenerated n T'.left l r
      (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver
        T' (a.pullback g)) d := by
  let q := Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T a
  letI : Epi q :=
    Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver_epi T a
  let qg := projectiveSpaceTwistedFreeQuotientPullback n r g.left l q
  let eQ := a.quotDataOnProjectiveSpace_pullbackIso (n := n) (S := S) g
  have hbase : TwistedFreeQuotKernelIsGloballyGenerated
      n T'.left l r qg d :=
    TwistedFreeQuotKernelIsGloballyGenerated.pullback
      n r g.left l q d hgen
  have hnormalized : TwistedFreeQuotKernelIsGloballyGenerated
      n T'.left l r (qg ≫ eQ.inv) d :=
    TwistedFreeQuotKernelIsGloballyGenerated.comp_iso
      n r T'.left l qg eQ.symm d hbase
  have hq :=
    Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver_pullback
      n r l S g a
  exact hq ▸ hnormalized

/-- Kernel generation for a twisted-free quotient survives arbitrary base change once the
pulled-back twisted kernel is identified with the twisted kernel of the chosen normalized
base-changed presentation. -/
theorem TwistedFreeQuotKernelIsGloballyGenerated.pullback_of_kernelIso
    (n r : ℕ) {T T' : Scheme.{u}} (g : T' ⟶ T) (l : ℤ)
    {Q : (projectiveSpaceOver n T).Modules}
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    {Q' : (projectiveSpaceOver n T').Modules}
    (q' : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T' (-l)) ⟶ Q')
    (d : ℕ)
    (e : (Modules.pullback (projectiveSpaceOverMap n g)).obj
        (kernel (Modules.tensorMapLeft q
          (projectiveSpaceOverTwist n T (d : ℤ)))) ≅
      kernel (Modules.tensorMapLeft q'
        (projectiveSpaceOverTwist n T' (d : ℤ))))
    (hgen : TwistedFreeQuotKernelIsGloballyGenerated n T l r q d) :
    TwistedFreeQuotKernelIsGloballyGenerated n T' l r q' d := by
  let M := kernel (Modules.tensorMapLeft q
    (projectiveSpaceOverTwist n T (d : ℤ)))
  let M' := kernel (Modules.tensorMapLeft q'
    (projectiveSpaceOverTwist n T' (d : ℤ)))
  letI : Epi ((Modules.pullbackPushforwardAdjunction
      (projectiveSpaceOverπ n T)).counit.app M) := hgen
  exact Modules.pullbackPushforwardCounit_epi_of_iso_pullback_of_comm
    (projectiveSpaceOverπ n T) (projectiveSpaceOverπ n T') g
    (projectiveSpaceOverMap n g) (projectiveSpaceOverMap_π n g) M M' e

end AlgebraicGeometry.Scheme

end

end
