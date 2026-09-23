module

public import StacksAndModuli.API.SchemeModulesTensor
public import StacksAndModuli.API.SheafOfModulesColimits
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.Topology.Sheaves.Abelian

/-!
# Right exactness of tensor products of scheme modules

Tensoring a morphism of module sheaves with an arbitrary second module sheaf
preserves epimorphisms.  The proof checks epimorphy on stalks.  Stalks commute with
the presheaf tensor product, tensor products of modules preserve surjections, and
the sheafification unit induces an isomorphism on every stalk.

This is the right-exactness input needed to form short exact kernel sequences after
Serre twisting.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.Functor TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

private lemma colimitMap_epi_of_epi {F F' : X.Modules} (f : F ⟶ F') [Epi f]
    (x : X) : Epi (PresheafOfModules.StalkTensor.colimitMap X.presheaf x f.val) := by
  apply (ModuleCat.epi_iff_surjective _).mpr
  change Function.Surjective
    (((forget₂ (ModuleCat _) AddCommGrpCat).map
      (PresheafOfModules.StalkTensor.colimitMap X.presheaf x f.val)))
  rw [PresheafOfModules.StalkTensor.forget_colimitMap]
  apply (AddCommGrpCat.epi_iff_surjective _).mp
  change Epi (((TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((SheafOfModules.toSheaf X.ringCatSheaf).map f)))
  let _ : Epi ((SheafOfModules.toSheaf X.ringCatSheaf).map f) :=
    Functor.map_epi (SheafOfModules.toSheaf X.ringCatSheaf) f
  exact Functor.map_epi
    (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
    ((SheafOfModules.toSheaf X.ringCatSheaf).map f)

private lemma colimitMap_tensor_epi {F F' : X.Modules} (f : F ⟶ F') [Epi f]
    (G : X.Modules) (x : X) :
    Epi (PresheafOfModules.StalkTensor.colimitMap X.presheaf x
      (f.val ⊗ₘ 𝟙 G.val)) := by
  let cf := PresheafOfModules.StalkTensor.colimitMap X.presheaf x f.val
  let cg := PresheafOfModules.StalkTensor.colimitMap X.presheaf x (𝟙 G.val)
  let _ : Epi cf := colimitMap_epi_of_epi f x
  let _ : Epi cg := colimitMap_epi_of_epi (𝟙 G) x
  have ht : Epi (cf ⊗ₘ cg) := by
    rw [ModuleCat.epi_iff_surjective]
    exact TensorProduct.map_surjective
      ((ModuleCat.epi_iff_surjective cf).mp inferInstance)
      ((ModuleCat.epi_iff_surjective cg).mp inferInstance)
  let _ : Epi (cf ⊗ₘ cg) := ht
  let e := PresheafOfModules.StalkTensor.comparisonIso X.presheaf x
  have hnat := PresheafOfModules.StalkTensor.comparisonIso_hom_naturality
    X.presheaf x f.val (𝟙 G.val)
  have hc : Epi
      (PresheafOfModules.StalkTensor.colimitMap X.presheaf x
          (f.val ⊗ₘ 𝟙 G.val) ≫
        (e F'.val G.val).hom) := by
    rw [← hnat]
    infer_instance
  let _ : Epi
      (PresheafOfModules.StalkTensor.colimitMap X.presheaf x
          (f.val ⊗ₘ 𝟙 G.val) ≫
        (e F'.val G.val).hom) := hc
  have hi : Epi
      ((PresheafOfModules.StalkTensor.colimitMap X.presheaf x
          (f.val ⊗ₘ 𝟙 G.val) ≫
        (e F'.val G.val).hom) ≫ (e F'.val G.val).inv) := inferInstance
  simpa using hi

private lemma stalk_sheafification_map_epi
    {P Q : X.PresheafOfModules} (a : P ⟶ Q) (x : X)
    [Epi (PresheafOfModules.StalkTensor.colimitMap X.presheaf x a)] :
    Epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((SheafOfModules.toSheaf X.ringCatSheaf).map
        ((sheafification X).map a)).1) := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  let uP := adj.unit.app P
  let uQ := adj.unit.app Q
  let sa := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map a)
  let suP := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map uP)
  let suQ := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map uQ)
  let sb := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
      ((PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
        ((SheafOfModules.forget X.ringCatSheaf).map ((sheafification X).map a))))
  have hsa : Epi sa := by
    have hforget : Epi
        ((forget₂ (ModuleCat _) AddCommGrpCat).map
          (PresheafOfModules.StalkTensor.colimitMap X.presheaf x a)) :=
      Functor.map_epi (forget₂ (ModuleCat _) AddCommGrpCat)
        (PresheafOfModules.StalkTensor.colimitMap X.presheaf x a)
    rw [PresheafOfModules.StalkTensor.forget_colimitMap] at hforget
    exact hforget
  let _ : Epi sa := hsa
  have hsuQ : IsIso suQ := by
    dsimp [suQ, uQ, adj]
    exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
      x AddCommGrpCat.{u} Q.presheaf
  let _ : IsIso suQ := hsuQ
  have hleft : Epi (sa ≫ suQ) := inferInstance
  have hnat := adj.unit.naturality a
  have hnatAb := congrArg
    (fun k ↦ (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map k) hnat
  have hnatStalk := congrArg
    (fun k ↦ (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map k)
      hnatAb
  have hEq : sa ≫ suQ = suP ≫ sb := by
    simpa only [sa, suQ, suP, sb, uP, uQ, sheafification,
      Functor.map_comp, Functor.comp_map, Functor.id_map] using hnatStalk
  have hright : Epi (suP ≫ sb) := by
    rw [← hEq]
    exact hleft
  let _ : Epi (suP ≫ sb) := hright
  exact epi_of_epi suP sb

/-- Tensoring an epimorphism of module sheaves with any module sheaf preserves
epimorphy. -/
instance tensorMapLeft_epi {F F' : X.Modules} (f : F ⟶ F') [Epi f]
    (G : X.Modules) : Epi (tensorMapLeft f G) := by
  let a := tensorMapLeft f G
  let aAb := (SheafOfModules.toSheaf X.ringCatSheaf).map a
  have haAb : Epi aAb := by
    let S := ShortComplex.mk aAb
      (0 : (SheafOfModules.toSheaf X.ringCatSheaf).obj (F' ⊗ₘ G) ⟶
        (SheafOfModules.toSheaf X.ringCatSheaf).obj (F' ⊗ₘ G)) comp_zero
    have hS : S.Exact := by
      rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
      intro x
      rw [ShortComplex.exact_iff_epi]
      · dsimp [S]
        let p := MonoidalCategoryStruct.whiskerRight
          (C := X.PresheafOfModules) f.val G.val
        have hp : Epi
            (PresheafOfModules.StalkTensor.colimitMap X.presheaf x p) := by
          change Epi
            (PresheafOfModules.StalkTensor.colimitMap X.presheaf x
              (f.val ⊗ₘ 𝟙 G.val))
          exact colimitMap_tensor_epi f G x
        let _ : Epi
            (PresheafOfModules.StalkTensor.colimitMap X.presheaf x p) := hp
        exact stalk_sheafification_map_epi p x
      · simp [S]
    exact (S.exact_iff_epi (by simp [S])).mp hS
  exact ⟨fun {Z} g h e ↦ by
    apply (SheafOfModules.toSheaf X.ringCatSheaf).map_injective
    apply (cancel_epi aAb).mp
    simpa only [Functor.map_comp] using congrArg
      (fun k ↦ (SheafOfModules.toSheaf X.ringCatSheaf).map k) e⟩

end AlgebraicGeometry.Scheme.Modules

end
