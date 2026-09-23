module

public import StacksAndModuli.API.OpensOverEquivalence
public import StacksAndModuli.API.SheafCohomologySiteEquivalence
public import StacksAndModuli.API.SheafCohomologyOpenExact
public import StacksAndModuli.API.SheafCohomologyLES
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Site-local cohomology on an open, computed on the subspace

This packages the chain established in `StacksAndModuli/API/OpensOverEquivalence.lean`,
`StacksAndModuli/API/SheafCohomologySiteEquivalence.lean` and
`StacksAndModuli/API/SheafCohomologyOpenExact.lean` into one statement:

`H'ⁿ(U, F)` on `X` vanishes as soon as `F` restricted to the subspace `↥U` — that is, some
sheaf on `Opens ↥U` whose transport to the slice site is `F.over U` — has vanishing `Hⁿ`.

The point of stating it this way is that the *topology* is fully discharged here.  Applying it
on an affine open of a scheme leaves only the identification of the restricted sheaf with a
quasicoherent module on the corresponding `Spec`, which is scheme theory, not sheaf theory.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace CategoryTheory.Sheaf

/-- Vanishing of sheaf cohomology transfers along an isomorphism of sheaves, on any site. -/
theorem subsingleton_H_of_isoOfSite {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
    {F G : Sheaf J AddCommGrpCat.{u}} (e : F ≅ G) (n : ℕ)
    (hF : Subsingleton (F.H n)) : Subsingleton (G.H n) := by
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  have hx : Sheaf.H.map e.hom n (Sheaf.H.map e.inv n x) = x := by
    rw [← Sheaf.H.map_comp_apply, e.inv_hom_id, Sheaf.H.map_id_apply]
  rw [← hx, @Subsingleton.elim _ hF (Sheaf.H.map e.inv n x) 0, map_zero]

variable {X : TopCat.{u}} (U : Opens X)

/-- The equivalence between sheaves on the slice site over `U` and sheaves on the subspace. -/
noncomputable abbrev overSubspaceEquiv :
    Sheaf ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u} ≌
      Sheaf (Opens.grothendieckTopology ↥U) AddCommGrpCat.{u} :=
  Functor.IsDenseSubsite.sheafEquiv ((Opens.grothendieckTopology X).over U)
    (Opens.grothendieckTopology ↥U) (TopologicalSpace.Opens.overEquiv U).inverse
    AddCommGrpCat.{u}

/-- The terminal object of the slice site is `U` itself. -/
noncomputable def isTerminalOverMkId : IsTerminal (Over.mk (𝟙 U)) :=
  Over.mkIdTerminal

/-- Its image on the subspace is the whole subspace. -/
noncomputable def isTerminalOverEquivInverseObj :
    IsTerminal ((TopologicalSpace.Opens.overEquiv U).inverse.obj (Over.mk (𝟙 U))) := by
  have h : (TopologicalSpace.Opens.overEquiv U).inverse.obj (Over.mk (𝟙 U))
      = (⊤ : Opens ↥U) := TopologicalSpace.Opens.inclusion'_map_eq_top U
  rw [h]
  exact isTerminalTop

/-- **Site-local cohomology on `U` is computed on the subspace `↥U`.**  If the sheaf `F.over U`
on the slice site is the transport of a sheaf `G` on `Opens ↥U` whose `Hⁿ⁺¹` vanishes, then
`H'ⁿ⁺¹(U, F)` vanishes. -/
theorem subsingleton_HPrime_of_subspace
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ)
    (G : Sheaf (Opens.grothendieckTopology ↥U) AddCommGrpCat.{u})
    (e : F.over U ≅ (overSubspaceEquiv U).inverse.obj G)
    (hG : Subsingleton (G.H (n + 1))) :
    Subsingleton (F.H' (n + 1) U) := by
  rw [subsingleton_HPrime_open_iff (Opens.grothendieckTopology X) F U (n + 1)]
  refine subsingleton_H_of_isoOfSite e.symm (n + 1) ?_
  exact Functor.IsDenseSubsite.subsingleton_H_sheafEquiv_inverse
    ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology ↥U)
    (TopologicalSpace.Opens.overEquiv U).inverse
    (isTerminalOverMkId U) (isTerminalOverEquivInverseObj U) G (n + 1) hG

/-- Pulling an open of `X` below `U` back to the subspace and pushing it forward again is the
forgetful functor of the slice. -/
noncomputable def overEquivInverseCompFunctorIso :
    (TopologicalSpace.Opens.overEquiv U).inverse ⋙ U.isOpenEmbedding.functor ≅
      Over.forget U :=
  NatIso.ofComponents
    (fun V => eqToIso (TopologicalSpace.Opens.functor_obj_map_inclusion U (leOfHom V.hom)))
    (fun _ => Subsingleton.elim _ _)

/-- **The slice-site restriction of `F` is the transport of its restriction to the
subspace.**  This is the isomorphism `subsingleton_HPrime_of_subspace` asks for, so on an
affine open only the cohomology of the restricted sheaf remains to be computed. -/
noncomputable def overIsoSheafRestrict (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    F.over U ≅ (overSubspaceEquiv U).inverse.obj (U.sheafRestrict.obj F) :=
  ObjectProperty.isoMk _
    (Functor.isoWhiskerRight (NatIso.op (overEquivInverseCompFunctorIso U)) F.obj)

/-- **Site-local cohomology on `U` is the cohomology of the restriction to `↥U`.** -/
theorem subsingleton_HPrime_of_sheafRestrict
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ)
    (hG : Subsingleton ((U.sheafRestrict.obj F).H (n + 1))) :
    Subsingleton (F.H' (n + 1) U) :=
  subsingleton_HPrime_of_subspace U F n _ (overIsoSheafRestrict U F) hG

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory.Sheaf

/-- The abelian sheaf of the restriction of a module sheaf to an open is *definitionally* the
restriction of its abelian sheaf: both are the sections over the image open. -/
noncomputable def toSheafRestrictIso {X : Scheme.{u}} (U : X.Opens) (F : X.Modules) :
    U.sheafRestrict.obj ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) ≅
      (SheafOfModules.toSheaf U.toScheme.ringCatSheaf).obj (Scheme.Modules.restrict F U.ι) :=
  Iso.refl _

/-- **Site-local cohomology of a module sheaf on an open is its cohomology on that open as a
scheme.**  With this, computing `H'ⁿ⁺¹(U, F)` for an affine open `U` is the same problem as
computing `Hⁿ⁺¹` of a quasicoherent sheaf on the affine scheme `U`. -/
theorem subsingleton_HPrime_of_modulesRestrict {X : Scheme.{u}} (U : X.Opens)
    (F : X.Modules) (n : ℕ)
    (hG : Subsingleton (((SheafOfModules.toSheaf U.toScheme.ringCatSheaf).obj
      (Scheme.Modules.restrict F U.ι)).H (n + 1))) :
    Subsingleton (((SheafOfModules.toSheaf X.ringCatSheaf).obj F).H' (n + 1) U) :=
  subsingleton_HPrime_of_sheafRestrict U _ n hG

end AlgebraicGeometry.Scheme.Modules
