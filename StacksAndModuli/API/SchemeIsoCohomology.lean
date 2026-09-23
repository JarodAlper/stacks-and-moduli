module

public import StacksAndModuli.API.SheafCohomologySiteEquivalence
public import StacksAndModuli.API.FlasqueVanishing
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv

/-!
# Cohomology is invariant under an isomorphism of schemes

For an isomorphism `e : Y ≅ Z` of schemes the image functor `e.hom.opensFunctor` is an
equivalence of the posets of opens, hence a dense subsite morphism; and the abelian sheaf of
the restricted module `M.restrict e.hom` is *definitionally* the transport of the abelian
sheaf of `M`, because `Scheme.Modules.restrictAppIso` is `Iso.refl`.

Consequently a vanishing theorem proved on `Spec R` can be read on any affine scheme, which is
the last step of the affine-open chain of `PLAN-hilbert-quot.md`.

The `HasExt`, `HasSheafify` and `EnoughInjectives` instances for `Sheaf (Opens ↥Y)
AddCommGrpCat` with `Y` a scheme resolve only once the `TopCat`-side setup of
`StacksAndModuli/API/FlasqueVanishing.lean` is imported; without that import the search does not
terminate.  See the root `INSIGHTS.md`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

variable {Y Z : Scheme.{u}} (e : Y ≅ Z)

lemma base_inv_hom (v : Y) : e.inv.base (e.hom.base v) = v := by
  show (e.hom ≫ e.inv).base v = v
  rw [e.hom_inv_id]
  rfl

lemma base_hom_inv (v : Z) : e.hom.base (e.inv.base v) = v := by
  show (e.inv ≫ e.hom).base v = v
  rw [e.inv_hom_id]
  rfl

lemma opensFunctor_inv_hom (V : Y.Opens) :
    e.inv.opensFunctor.obj (e.hom.opensFunctor.obj V) = V := by
  refine TopologicalSpace.Opens.ext ?_
  show e.inv.base '' (e.hom.base '' (V : Set Y)) = (V : Set Y)
  rw [Set.image_image]
  simp only [base_inv_hom e, Set.image_id']

lemma opensFunctor_hom_inv (V : Z.Opens) :
    e.hom.opensFunctor.obj (e.inv.opensFunctor.obj V) = V := by
  refine TopologicalSpace.Opens.ext ?_
  show e.hom.base '' (e.inv.base '' (V : Set Z)) = (V : Set Z)
  rw [Set.image_image]
  simp only [base_hom_inv e, Set.image_id']

/-- An isomorphism of schemes induces an equivalence of the posets of opens, modelled on
the direct-image functor `Scheme.Hom.opensFunctor`. (`Scheme.opensEquivOfIso` in
`API/SheafCohomologySchemeIso.lean` is the same equivalence built from `Opens.mapMapIso`;
the two files are independent, so both models exist.) -/
noncomputable def opensFunctorEquivOfIso : Y.Opens ≌ Z.Opens where
  functor := e.hom.opensFunctor
  inverse := e.inv.opensFunctor
  unitIso := NatIso.ofComponents
    (fun V => eqToIso (opensFunctor_inv_hom e V).symm)
    (fun _ => Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents
    (fun V => eqToIso (opensFunctor_hom_inv e V))
    (fun _ => Subsingleton.elim _ _)

instance isCocontinuous_opensEquivFunctor :
    (opensFunctorEquivOfIso e).functor.IsCocontinuous (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology Z) :=
  inferInstanceAs (e.hom.opensFunctor.IsCocontinuous _ _)

instance isCocontinuous_opensEquivInverse :
    (opensFunctorEquivOfIso e).inverse.IsCocontinuous (Opens.grothendieckTopology Z)
      (Opens.grothendieckTopology Y) :=
  inferInstanceAs (e.inv.opensFunctor.IsCocontinuous _ _)

instance isDenseSubsite_opensFunctor :
    e.hom.opensFunctor.IsDenseSubsite (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology Z) :=
  Equivalence.isDenseSubsite_functor_of_isCocontinuous _ _ (opensFunctorEquivOfIso e)

lemma opensFunctor_obj_top : e.hom.opensFunctor.obj (⊤ : Y.Opens) = (⊤ : Z.Opens) := by
  refine TopologicalSpace.Opens.ext ?_
  show e.hom.base '' (Set.univ : Set Y) = (Set.univ : Set Z)
  rw [Set.image_univ, Set.range_eq_univ]
  exact fun z => ⟨e.inv.base z, base_hom_inv e z⟩

/-- The image of the terminal open is terminal. -/
noncomputable def isTerminalOpensFunctorTop :
    IsTerminal (e.hom.opensFunctor.obj (⊤ : Y.Opens)) := by
  rw [opensFunctor_obj_top e]
  exact isTerminalTop

/-- **Vanishing transports along the equivalence of open-sites induced by an isomorphism of
schemes.** -/
theorem subsingleton_H_sheafEquivInverse
    (G : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}) (n : ℕ)
    (h : Subsingleton (G.H (n + 1))) :
    Subsingleton (((Functor.IsDenseSubsite.sheafEquiv (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology Z) e.hom.opensFunctor AddCommGrpCat.{u}).inverse.obj
        G).H (n + 1)) :=
  Functor.IsDenseSubsite.subsingleton_H_sheafEquiv_inverse
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology Z) e.hom.opensFunctor
    isTerminalTop (isTerminalOpensFunctorTop e) G (n + 1) h

/-- The abelian sheaf of a module restricted along an isomorphism is *definitionally* the
transport of its abelian sheaf: both are the sections over the image open. -/
noncomputable def toSheafRestrictTransportIso (M : Z.Modules) :
    (SheafOfModules.toSheaf Y.ringCatSheaf).obj (Scheme.Modules.restrict M e.hom) ≅
      (Functor.IsDenseSubsite.sheafEquiv (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology Z) e.hom.opensFunctor AddCommGrpCat.{u}).inverse.obj
        ((SheafOfModules.toSheaf Z.ringCatSheaf).obj M) :=
  Iso.refl _

/-- **Cohomology of a module sheaf is invariant under an isomorphism of schemes.** -/
theorem subsingleton_H_restrict_of_iso (M : Z.Modules) (n : ℕ)
    (h : Subsingleton (((SheafOfModules.toSheaf Z.ringCatSheaf).obj M).H (n + 1))) :
    Subsingleton (((SheafOfModules.toSheaf Y.ringCatSheaf).obj
      (Scheme.Modules.restrict M e.hom)).H (n + 1)) :=
  subsingleton_H_sheafEquivInverse e ((SheafOfModules.toSheaf Z.ringCatSheaf).obj M) n h

end AlgebraicGeometry.Scheme
