module

public import StacksAndModuli.«Section2.1-Intro».«part2.1.2-the-grassmannian-functor»

/-!
# Cokernels of quasicoherent module sheaves

The cokernel of a morphism between quasicoherent module sheaves is
quasicoherent.  On an affine scheme this follows because the tilde functor is a
left adjoint.  The general statement follows by restricting to an affine open
cover.

## Main results

* `AlgebraicGeometry.Scheme.Modules.quasicoherentCokernelSpecTildeIso`: on a
  spectrum, the sheaf cokernel is the tilde of the module cokernel.
* `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_cokernel`: cokernels of
  morphisms of quasicoherent module sheaves are quasicoherent.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Over a spectrum, the cokernel of a morphism of quasicoherent module
sheaves is the tilde of the cokernel of its map on global sections. -/
noncomputable def quasicoherentCokernelSpecTildeIso
    {A : CommRingCat.{u}} {N M : (Spec A).Modules} (i : N ⟶ M)
    [N.IsQuasicoherent] [M.IsQuasicoherent] :
    cokernel i ≅ (tilde.functor A).obj
      (cokernel (moduleSpecΓFunctor.map i)) :=
  haveI : IsIso (Scheme.Modules.fromTildeΓNatTrans.app N) :=
    inferInstanceAs (IsIso N.fromTildeΓ)
  haveI : IsIso (Scheme.Modules.fromTildeΓNatTrans.app M) :=
    inferInstanceAs (IsIso M.fromTildeΓ)
  haveI := (tilde.adjunction (R := A)).leftAdjoint_preservesColimits
  (cokernel.mapIso ((moduleSpecΓFunctor ⋙ tilde.functor A).map i) i
      (asIso (Scheme.Modules.fromTildeΓNatTrans.app N))
      (asIso (Scheme.Modules.fromTildeΓNatTrans.app M))
      (by
        simpa using
          Scheme.Modules.fromTildeΓNatTrans.naturality i)).symm ≪≫
    (PreservesCokernel.iso (tilde.functor A)
      (moduleSpecΓFunctor.map i)).symm

/-- On an affine scheme, the cokernel of a morphism of quasicoherent module
sheaves is quasicoherent. -/
lemma isQuasicoherent_cokernel_spec {A : CommRingCat.{u}}
    {N M : (Spec A).Modules} (i : N ⟶ M)
    [N.IsQuasicoherent] [M.IsQuasicoherent] :
    (cokernel i).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent
    (Spec A).ringCatSheaf).prop_of_iso
    (quasicoherentCokernelSpecTildeIso i).symm
    (inferInstanceAs (((tilde.functor A).obj
      (cokernel (moduleSpecΓFunctor.map i))).IsQuasicoherent))

/-- The cokernel of a morphism of quasicoherent module sheaves on a scheme is
quasicoherent. -/
lemma isQuasicoherent_cokernel {P : Scheme.{u}} {N M : P.Modules}
    (i : N ⟶ M) [N.IsQuasicoherent] [M.IsQuasicoherent] :
    (cokernel i).IsQuasicoherent := by
  let _ (a : P.affineCover.I₀) :
      ((restrictFunctor (P.affineCover.f a)).obj
        (cokernel i)).IsQuasicoherent := by
    let _ : (cokernel ((restrictFunctor (P.affineCover.f a)).map
        i)).IsQuasicoherent :=
      isQuasicoherent_cokernel_spec
        ((restrictFunctor (P.affineCover.f a)).map i)
    exact (SheafOfModules.isQuasicoherent
      (P.affineCover.X a).ringCatSheaf).prop_of_iso
      (PreservesCokernel.iso
        (restrictFunctor (P.affineCover.f a)) i).symm
      inferInstance
  exact isQuasicoherent_of_openCover_restrict _ P.affineCover

end AlgebraicGeometry.Scheme.Modules

end
