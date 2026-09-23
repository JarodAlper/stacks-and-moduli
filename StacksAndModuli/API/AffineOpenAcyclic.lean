module

public import StacksAndModuli.API.SheafCohomologyAffineOpen
public import StacksAndModuli.API.SchemeIsoCohomology
public import StacksAndModuli.API.AffineAcyclic
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Quasicoherent sheaves are acyclic on an affine open

The composite of the three links established in
`StacksAndModuli/API/SheafCohomologyAffineOpen.lean`, `StacksAndModuli/API/SchemeIsoCohomology.lean` and
`StacksAndModuli/API/AffineAcyclic.lean`:

```
H'ⁿ⁺¹(U, F)  =  Hⁿ⁺¹(U.toScheme, F|_U)  =  Hⁿ⁺¹(Spec Γ(X,U), …)  =  0.
```

Both identifications are definitional (`Scheme.Modules.restrictAppIso` is `Iso.refl`), so the
only mathematical input is Hartshorne III.3.5 on `Spec`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)

/-- Restricting to `U` and then transporting to `Spec Γ(X,U)` and back is the identity. -/
def restrictIsoSpecRoundTrip (F : X.Modules) :
    Scheme.Modules.restrict
        (Scheme.Modules.restrict (Scheme.Modules.restrict F U.ι) hU.isoSpec.inv)
        hU.isoSpec.hom ≅
      Scheme.Modules.restrict F U.ι :=
  ((Scheme.Modules.restrictFunctorComp hU.isoSpec.hom hU.isoSpec.inv).app
      (Scheme.Modules.restrict F U.ι)).symm ≪≫
    (Scheme.Modules.restrictFunctorCongr hU.isoSpec.hom_inv_id).app
      (Scheme.Modules.restrict F U.ι) ≪≫
    (Scheme.Modules.restrictFunctorId).app (Scheme.Modules.restrict F U.ι)

include hU in
/-- **Quasicoherent sheaves are acyclic on an affine open.** -/
theorem subsingleton_HPrime_of_isAffineOpen [IsNoetherianRing Γ(X, U)]
    (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    Subsingleton (((SheafOfModules.toSheaf X.ringCatSheaf).obj F).H' (n + 1) U) := by
  have h0 := AlgebraicGeometry.tilde.subsingleton_H_of_isQuasicoherent
    (Scheme.Modules.restrict (Scheme.Modules.restrict F U.ι) hU.isoSpec.inv) n
  have h1 := Scheme.subsingleton_H_restrict_of_iso hU.isoSpec
    (Scheme.Modules.restrict (Scheme.Modules.restrict F U.ι) hU.isoSpec.inv) n h0
  have h2 := Scheme.Modules.subsingleton_H_of_iso (restrictIsoSpecRoundTrip hU F) (n + 1) h1
  exact subsingleton_HPrime_of_modulesRestrict U F n h2

end AlgebraicGeometry.Scheme.Modules
