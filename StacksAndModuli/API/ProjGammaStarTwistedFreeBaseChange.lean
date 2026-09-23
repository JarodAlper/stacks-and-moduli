module

public import StacksAndModuli.API.ProjectiveGradedFreeBaseChange
public import StacksAndModuli.API.ProjectiveSpaceTwistProjComparison

/-!
# The base-change obligation for a twisted-free ambient sheaf

`AlgebraicGeometry.ProjectiveSpace.HasGammaStarBaseChangeCechHgrZero` is the single named
obligation on which `RelativeCohomology.SchemeGlobalSectionsComparison` rests
(`API/ProjectiveSpaceTwistProjComparison.lean`): base changing the graded module `Γ_*(F)` to a
field must compute the same degree-zero Čech cohomology as `Γ_*` of the base-changed sheaf.

For the ambient sheaves that actually occur — the twisted-free `𝒪(-l)^{⊕r}` of a Quot
presentation — the obligation needs **no chart-level base-change argument at all**.  If `Γ_*`
of the sheaf and of each of its field fibres is the twisted-free *graded* module, then the
comparison is a composite of three isomorphisms that already exist:

* `GradedModule.baseChangeMapIso` — base change transports an isomorphism of graded modules;
* `GradedModule.freeBaseChangeIso` — `(S_R(-l)^{⊕r}) ⊗_R A ≅ S_A(-l)^{⊕r}`;
* `GradedModule.cechHgrMapIso` and `GradedModule.appIso` — Čech cohomology and its degree-`d`
  piece transport along an isomorphism.

So the remaining content is purely the identification of `Γ_*` with the free graded module,
which is `AlgebraicGeometry.ProjectiveSpace.twistedFreeIsoGammaStar`
(`API/ProjGammaStarPow.lean`) once the ambient sheaf has been recognized as a finite direct
sum of twists on polynomial `Proj`.

Main declaration:

* `AlgebraicGeometry.ProjectiveSpace.hasGammaStarBaseChangeCechHgrZero_of_freeIso`.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

open GradedModule

/-- **The base-change obligation for a twisted-free ambient sheaf**, reduced to two
sheaf-level identifications: if `Γ_*` of the ambient sheaf and of each of its field fibres is
the twisted-free graded module `S(-l)^{⊕r}`, then `HasGammaStarBaseChangeCechHgrZero` holds,
and with it the whole of `RelativeCohomology.SchemeGlobalSectionsComparison`. -/
theorem hasGammaStarBaseChangeCechHgrZero_of_freeIso
    (n : ℕ) (R : Type u) [CommRing R]
    (Q : (Scheme.projectiveSpaceOver n (Spec (CommRingCat.of R))).Modules)
    (l : ℤ) (r : ℕ)
    (eR : Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (projSpecπ n R)
        ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q) (stdVars n R)
        ≅ ((GradedModule.structureModule R n).twist (-l)).pow r)
    (eK : ∀ (K : Type u) [Field K] (f : R →+* K),
        Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (projSpecπ n K)
          ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n K).inv).obj
            (Scheme.Modules.projectiveSpaceBaseChangeOfRingHom Q f)) (stdVars n K)
          ≅ ((GradedModule.structureModule K n).twist (-l)).pow r) :
    HasGammaStarBaseChangeCechHgrZero n R Q := by
  intro K _ f d
  letI : Algebra R K := f.toAlgebra
  exact ⟨(appIso (cechHgrMapIso (baseChangeMapIso K eR) 0) d).toLinearEquiv.trans
    (((appIso (cechHgrMapIso
        (freeBaseChangeIso (R := R) (A := K) (n := n) r (-l)) 0) d).toLinearEquiv).trans
      ((appIso (cechHgrMapIso (eK K f).symm 0) d).toLinearEquiv))⟩

end AlgebraicGeometry.ProjectiveSpace

end

end
