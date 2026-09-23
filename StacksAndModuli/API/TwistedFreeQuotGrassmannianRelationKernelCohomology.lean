module

public import StacksAndModuli.API.TwistedFreeQuotGrassmannianNextDegreeSourceComparison

/-!
# Cohomology of the reconstructed relation kernel

The first cohomology of the kernel of the twisted reconstructed relation-to-image map is
the obstruction to lifting global sections of its image.  More precisely, when the twisted
relation source has vanishing first cohomology, vanishing for the relation kernel is
equivalent to surjectivity on global sections.  This identifies the remaining cohomological
input in next-degree saturation with a genuine relation-generation condition.
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

/-- If the twisted reconstructed relation source has vanishing `H¹`, then its
relation-to-image map has surjective global sections exactly when the kernel also has
vanishing `H¹`. -/
theorem subsingleton_H_one_reconstructedNextDegreeRelationKernel_iff_surjective_appTop
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (hsource1 : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (Modules.tensor
          (Modules.tensor
            ((Modules.pullback (projectiveSpaceOverπ n T)).obj (kernel u))
            (projectiveSpaceOverTwist n T (-(d : ℤ))))
          (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ)))).H 1)) :
    Subsingleton
        (((SheafOfModules.toSheaf _).obj
          (kernel (Modules.tensorMapLeft
            (Abelian.factorThruImage
              (reconstructedRelation' n T l r d e he u))
            (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ))))).H 1) ↔
      Function.Surjective
        ((Modules.tensorMapLeft
          (Abelian.factorThruImage
            (reconstructedRelation' n T l r d e he u))
          (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ))).val.app
            (Opposite.op ⊤)).hom := by
  let f := reconstructedRelation' n T l r d e he u
  let O := projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ)
  let g := Modules.tensorMapLeft (Abelian.factorThruImage f) O
  let C := ShortComplex.mk (kernel.ι g) g (kernel.condition g)
  have hC : C.ShortExact := { exact := ShortComplex.exact_kernel g }
  constructor
  · intro hkernel1
    exact Modules.surjective_appTop_of_shortExact_of_subsingleton_H_one
      hC hkernel1
  · intro hsurj
    exact Modules.subsingleton_H_one_of_shortExact_of_surjective_appTop
      hC hsurj hsource1

/-- Over an affine base, the preceding relation-kernel vanishing is equivalent to
epimorphy after pushforward to the base. -/
theorem subsingleton_H_one_reconstructedNextDegreeRelationKernel_iff_pushforward_epi
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
          (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ)))).H 1)) :
    Subsingleton
        (((SheafOfModules.toSheaf _).obj
          (kernel (Modules.tensorMapLeft
            (Abelian.factorThruImage
              (reconstructedRelation' n T l r d e he u))
            (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ))))).H 1) ↔
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
  haveI hpushAqc : ((Modules.pushforward
      (projectiveSpaceOverπ n T)).obj
        (Modules.tensor
          (Modules.tensor
            ((Modules.pullback (projectiveSpaceOverπ n T)).obj (kernel u))
            (projectiveSpaceOverTwist n T (-(d : ℤ)))) O)).IsQuasicoherent :=
    Modules.isQuasicoherent_pushforward_of_qcqs
      (projectiveSpaceOverπ n T) _
  haveI hpushIqc : ((Modules.pushforward
      (projectiveSpaceOverπ n T)).obj
        (Modules.tensor (Abelian.image f) O)).IsQuasicoherent :=
    Modules.isQuasicoherent_pushforward_of_qcqs
      (projectiveSpaceOverπ n T) _
  constructor
  · intro hkernel1
    exact Modules.projectiveSpacePushforward_map_epi_of_subsingleton_H_one_kernel
      n T g hkernel1
  · intro hpush
    letI : Epi ((Modules.pushforward (projectiveSpaceOverπ n T)).map g) := hpush
    have hsurjPush : Function.Surjective
        (((Modules.pushforward (projectiveSpaceOverπ n T)).map g).app ⊤).hom :=
      (Modules.epi_iff_appTop_surjective_of_isAffine _).mp inferInstance
    have hsurj : Function.Surjective (g.app ⊤).hom := by
      change Function.Surjective
        (g.app ((projectiveSpaceOverπ n T) ⁻¹ᵁ (⊤ : T.Opens))).hom at hsurjPush
      rw [Scheme.Hom.preimage_top] at hsurjPush
      exact hsurjPush
    exact
      (subsingleton_H_one_reconstructedNextDegreeRelationKernel_iff_surjective_appTop
        n T l r d e he u hsource1).2 hsurj

/-- When the degree-`d` relation coefficient is finite locally free, the canonical
source comparison identifies relation-kernel `H¹`-vanishing with the relation-generation
field of next-degree saturation. -/
theorem subsingleton_H_one_reconstructedNextDegreeRelationKernel_iff_kernelLift_epi
    (n : ℕ) (T : Scheme.{u}) [IsAffine T] (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (hK : Modules.IsFiniteLocallyFree (kernel u))
    (hsource1 : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (Modules.tensor
          (Modules.tensor
            ((Modules.pullback (projectiveSpaceOverπ n T)).obj (kernel u))
            (projectiveSpaceOverTwist n T (-(d : ℤ))))
          (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ)))).H 1)) :
    Subsingleton
        (((SheafOfModules.toSheaf _).obj
          (kernel (Modules.tensorMapLeft
            (Abelian.factorThruImage
              (reconstructedRelation' n T l r d e he u))
            (projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ))))).H 1) ↔
      Epi (twistedFreeNextDegreeReconstructedKernelLift
        n T l r d e he u) := by
  letI : (kernel u).IsQuasicoherent := Modules.kernel_isQuasicoherent u
  let f := reconstructedRelation' n T l r d e he u
  let O := projectiveSpaceOverTwist n T ((d + 1 : ℕ) : ℤ)
  let g := Modules.tensorMapLeft (Abelian.factorThruImage f) O
  let src := reconstructedNextDegreeRelationSourcePushforwardIso_of_isAffine
    n T d hK
  let imageIso := reconstructedNextDegreeRelationImagePushforwardIsoKernel
    n T l r d e he u
  let lift := twistedFreeNextDegreeReconstructedKernelLift
    n T l r d e he u
  let compatibility := twistedFreeNextDegreeCanonicalRelationSourceCompatibility
    n T l r d e he u hK
  constructor
  · intro hkernel1
    exact reconstructedNextDegreeRelationKernelLift_epi_of_subsingleton_H_one
      n T l r d e he u hkernel1
        (compatibility.toComparison n T l r d e he u hK)
  · intro hlift
    letI : Epi lift := hlift
    have hcompat : src.hom ≫
        (Modules.pushforward (projectiveSpaceOverπ n T)).map g ≫
        imageIso.hom = lift := compatibility
    haveI : Epi (src.hom ≫
        (Modules.pushforward (projectiveSpaceOverπ n T)).map g ≫
        imageIso.hom) := hcompat ▸ hlift
    haveI : Epi (src.hom ≫
        (Modules.pushforward (projectiveSpaceOverπ n T)).map g) :=
      (epi_comp_iff_of_isIso _ imageIso.hom).mp inferInstance
    haveI : Epi ((Modules.pushforward (projectiveSpaceOverπ n T)).map g) :=
      epi_of_epi src.hom _
    exact
      (subsingleton_H_one_reconstructedNextDegreeRelationKernel_iff_pushforward_epi
        n T l r d e he u hsource1).2 inferInstance

end AlgebraicGeometry.Scheme

end

end
