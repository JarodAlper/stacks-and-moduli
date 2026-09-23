module

public import StacksAndModuli.API.AffinePushforwardQuasicoherent
public import StacksAndModuli.API.IdealSheafFromQuasicoherent
public import StacksAndModuli.API.SheafifyComparison
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Quasicoherent quotients attached to closed immersions

A closed immersion `i : Z ⟶ X` determines the quasicoherent quotient
`i_* 𝒪_Z` of `𝒪_X`.  This file packages that quotient and proves that applying the
kernel-ideal construction recovers the defining ideal sheaf `i.ker`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The quasicoherent quotient module `i_* 𝒪_Z` associated to a closed immersion. -/
noncomputable def Hom.closedQuotient : X.Modules :=
  (Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)

/-- The quotient morphism `𝒪_X ⟶ i_* 𝒪_Z` associated to a closed immersion. -/
noncomputable def Hom.toClosedQuotient :
    SheafOfModules.unit X.ringCatSheaf ⟶ i.closedQuotient :=
  SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom

instance : i.closedQuotient.IsQuasicoherent :=
  let _ := Modules.unit_isQuasicoherent Z
  Modules.isQuasicoherent_pushforward_of_isAffineHom i _

/-- The structure sheaf map onto the quotient attached to a closed immersion is an
epimorphism of module sheaves. -/
instance : Epi i.toClosedQuotient := by
  refine SheafOfModules.epi_of_isLocallySurjective i.toClosedQuotient ?_
  constructor
  intro U t x hx
  obtain ⟨_, ⟨W', hW', rfl⟩, hxW, hWU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
  set W : X.affineOpens := ⟨W', hW'⟩
  obtain ⟨s, hs⟩ := i.app_surjective W.1 W.2
    ((i.closedQuotient).presheaf.map (homOfLE hWU).op t)
  exact ⟨W.1, homOfLE hWU, ⟨s, hs⟩, hxW⟩

/-- Taking affine-local kernels of `𝒪_X ⟶ i_* 𝒪_Z` recovers the defining ideal
sheaf of the closed immersion. -/
lemma Hom.kernelIdealSheafData_toClosedQuotient :
    Modules.Hom.kernelIdealSheafData i.closedQuotient i.toClosedQuotient = i.ker := by
  ext U x
  rw [Modules.Hom.kernelIdealSheafData_ideal,
    Modules.Hom.mem_kernelIdeal_iff, i.ker_apply]
  rfl

end AlgebraicGeometry.Scheme
