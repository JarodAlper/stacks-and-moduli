module

public import StacksAndModuli.API.AffineOpenSectionsExact
public import StacksAndModuli.API.FlatColimit
public import StacksAndModuli.API.OpenCoverQuotient
public import StacksAndModuli.API.ProjectiveTwistFlatOver
public import StacksAndModuli.API.SchemeModulesKernelFinitePresentation
public import StacksAndModuli.API.SchemeModulesKernelSections

/-!
# Relative flatness of kernels of flat quotients

For an epimorphism of quasicoherent module sheaves, affine-open sections form a short exact
sequence.  If the source and target are flat over the base, the algebraic kernel-flatness
criterion therefore shows that the kernel sheaf is flat over the base as well.

This is the flatness step needed when iterating finite twisted-free presentations of a flat
finitely presented sheaf on projective space.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X T : Scheme.{u}}

/-- The kernel of an epimorphism between quasicoherent sheaves flat over the base is flat over
the base. -/
theorem FlatOver.kernel_of_epi {E Q : X.Modules}
    [E.IsQuasicoherent] [Q.IsQuasicoherent]
    (g : X ⟶ T) (p : E ⟶ Q) [Epi p]
    (hE : E.FlatOver g) (hQ : Q.FlatOver g) :
    (kernel p).FlatOver g := by
  letI : (kernel p).IsQuasicoherent := kernel_isQuasicoherent p
  intro U V hUV
  let a : Γ(T, V.1) →+* Γ(X, U.1) :=
    (X.presheaf.map (homOfLE hUV).op).hom.comp (g.app V.1).hom
  letI := Module.compHom Γ(E, U.1) a
  letI := Module.compHom Γ(Q, U.1) a
  letI := Module.compHom Γ(kernel p, U.1) a
  let f : Γ(kernel p, U.1) →ₗ[Γ(T, V.1)] Γ(E, U.1) :=
    { toFun := ((kernel.ι p).app U.1).hom
      map_add' := ((kernel.ι p).app U.1).hom.map_add
      map_smul' := fun r x => by
        change ((kernel.ι p).val.app (op U.1)).hom (a r • x) =
          a r • ((kernel.ι p).val.app (op U.1)).hom x
        exact (((kernel.ι p).val.app (op U.1)).hom.map_smul (a r) x) }
  let q : Γ(E, U.1) →ₗ[Γ(T, V.1)] Γ(Q, U.1) :=
    { toFun := (p.app U.1).hom
      map_add' := (p.app U.1).hom.map_add
      map_smul' := fun r x => by
        change (p.val.app (op U.1)).hom (a r • x) =
          a r • (p.val.app (op U.1)).hom x
        exact ((p.val.app (op U.1)).hom.map_smul (a r) x) }
  haveI : Module.Flat Γ(T, V.1) Γ(E, U.1) := hE U V hUV
  haveI : Module.Flat Γ(T, V.1) Γ(Q, U.1) := hQ U V hUV
  apply Module.Flat.of_shortExact f q
  · change Function.Injective ((kernel.ι p).app U.1).hom
    exact app_injective_of_mono (kernel.ι p) U.1
  · change Function.Exact ((kernel.ι p).app U.1).hom (p.app U.1).hom
    exact exact_kernel_ι_app p U.1
  · change Function.Surjective (p.app U.1).hom
    have hS : (ShortComplex.mk (kernel.ι p) p (kernel.condition p)).ShortExact :=
      ({ exact := ShortComplex.exact_kernel p } :
        (ShortComplex.mk (kernel.ι p) p (kernel.condition p)).ShortExact)
    have hs : Function.Surjective (p.val.app (op U.1)).hom :=
      surjective_app_of_shortExact_of_isAffineOpen (S :=
        ShortComplex.mk (kernel.ι p) p (kernel.condition p)) U.2 hS
    exact hs

end AlgebraicGeometry.Scheme.Modules

end
