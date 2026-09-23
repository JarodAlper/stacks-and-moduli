module

public import StacksAndModuli.API.KernelIdealPullback
public import StacksAndModuli.API.AffinePushforwardQuasicoherent
public import StacksAndModuli.API.PseudofunctorToCatPullbackComp
public import StacksAndModuli.«Section3.1-Descent».«part3.1.2-descent-quasi-coherent»

/-!
# Comparison maps for quasicoherent descent

This supporting module identifies the compositors in the quasicoherent-sheaf
pseudofunctor with the concrete comparison isomorphisms for iterated pullback of
module sheaves.  It also records the resulting transition map in the canonical
descent datum of the structure sheaf.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Hom

/-- The structure sheaf as an object of the category of quasicoherent modules. -/
noncomputable def unitQuasicoherentObject (S : Scheme.{u}) :
    (Scheme.Modules.isQuasicoherentProperty.prop
      (.mk (.op S))).FullSubcategory :=
  ⟨SheafOfModules.unit S.ringCatSheaf, Scheme.Modules.unit_isQuasicoherent S⟩

/-- Forgetting quasicoherence from the pullback of a morphism gives the ordinary
pullback of the underlying module morphism. -/
lemma quasicoherentMap_hom {X Y : Scheme.{u}} (g : X ⟶ Y)
    {M N : (Scheme.Modules.isQuasicoherentProperty.prop
      (.mk (.op Y))).FullSubcategory} (k : M.obj ⟶ N.obj) :
    ((Scheme.Modules.quasicoherentPseudofunctor.map g.op.toLoc).toFunctor.map
      (CategoryTheory.ObjectProperty.homMk k)).hom =
      (Modules.pullback g).map k := by
  rfl

/-- The transition map in the canonical module descent datum is the concrete
comparison between the two iterated pullbacks. -/
lemma unitDescentDataBase_hom {S' S Y : Scheme.{u}} (f : S' ⟶ S)
    (q : Y ⟶ S) (i₁ i₂ : PUnit.{1}) (a b : Y ⟶ S')
    (ha : a ≫ f = q) (hb : b ≫ f = q) :
    (((Scheme.Modules.pseudofunctorToCat.toDescentData
      (fun _ : PUnit.{1} ↦ f)).obj
        (SheafOfModules.unit S.ringCatSheaf)).hom
        (i₁ := i₁) (i₂ := i₂) q a b ha hb) =
      (pullbackCompCongrIso a f b f (ha.trans hb.symm)
        (SheafOfModules.unit S.ringCatSheaf)).hom := by
  dsimp only [CategoryTheory.Pseudofunctor.toDescentData,
    CategoryTheory.Pseudofunctor.DescentData.ofObj]
  rw [pseudofunctorToCat_mapComp'_inv_app a f q ha,
    pseudofunctorToCat_mapComp'_hom_app b f q hb]
  dsimp only [pullbackCompCongrIso, Iso.trans_hom]
  have hcongr :
      (Modules.pullbackCongr ha.symm).inv.app
            (SheafOfModules.unit S.ringCatSheaf) ≫
          (Modules.pullbackCongr hb.symm).hom.app
            (SheafOfModules.unit S.ringCatSheaf) =
        (Modules.pullbackCongr (ha.trans hb.symm)).hom.app
          (SheafOfModules.unit S.ringCatSheaf) := by
    dsimp only [Modules.pullbackCongr]
    simp only [eqToIso.inv, eqToIso.hom, eqToHom_app, eqToHom_trans]
  simp only [Category.assoc]
  rw [reassoc_of% hcongr]
  rfl

set_option maxHeartbeats 1000000 in
-- Comparing the full-subpseudofunctor compositor with its ambient compositor is expensive.
/-- After forgetting quasicoherence, the canonical structure-sheaf descent
transition is the concrete iterated-pullback comparison. -/
lemma unitQuasicoherentObject_descent_hom_hom
    {S' S Y : Scheme.{u}} (f : S' ⟶ S) (q : Y ⟶ S)
    (i₁ i₂ : PUnit.{1}) (a b : Y ⟶ S')
    (ha : a ≫ f = q) (hb : b ≫ f = q) :
    (((Scheme.Modules.quasicoherentPseudofunctor.toDescentData
      (fun _ : PUnit.{1} ↦ f)).obj
        (unitQuasicoherentObject S)).hom
        (i₁ := i₁) (i₂ := i₂) q a b ha hb).hom =
      (pullbackCompCongrIso a f b f (ha.trans hb.symm)
        (SheafOfModules.unit S.ringCatSheaf)).hom := by
  change (((Scheme.Modules.pseudofunctorToCat.toDescentData
    (fun _ : PUnit.{1} ↦ f)).obj
      (SheafOfModules.unit S.ringCatSheaf)).hom
      (i₁ := i₁) (i₂ := i₂) q a b ha hb) = _
  exact unitDescentDataBase_hom f q i₁ i₂ a b ha hb

end AlgebraicGeometry.Scheme.Modules.Hom
