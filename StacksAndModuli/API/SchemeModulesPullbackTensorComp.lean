module

public import StacksAndModuli.API.SchemeModulesPullbackTensor
public import StacksAndModuli.API.ModulesPullbackCoherence

/-!
# Composition coherence for pullback and tensor products

This file proves that the canonical tensor maps for pushforward and pullback are
compatible with composition of scheme morphisms.  The pullback theorem is the
coherence input needed when transporting twisted-free monomial sections through
successive projective-space base changes.

Main declarations:

* `AlgebraicGeometry.Scheme.Modules.pushforwardTensorHom_comp`;
* `AlgebraicGeometry.Scheme.Modules.comp_homEquiv_pullbackComp_hom`;
* `AlgebraicGeometry.Scheme.Modules.pullbackTensorComparison_comp`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry MonoidalCategory

universe u

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.Scheme.Modules

/-- The lax tensor structure on pushforward is compatible with composition of scheme
morphisms and the canonical pushforward-composition isomorphism. -/
lemma pushforwardTensorHom_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (F G : X.Modules) :
    pushforwardTensorHom g ((pushforward f).obj F) ((pushforward f).obj G) ≫
        (pushforward g).map (pushforwardTensorHom f F G) ≫
        (pushforwardComp f g).hom.app (tensor F G) =
      tensorMapLeft ((pushforwardComp f g).hom.app F)
          ((pushforward f ⋙ pushforward g).obj G) ≫
        tensorMapRight ((pushforward (f ≫ g)).obj F)
          ((pushforwardComp f g).hom.app G) ≫
        pushforwardTensorHom (f ≫ g) F G := by
  let adjZ := _root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 Z.ringCatSheaf.obj)
  apply (adjZ.homEquiv _ _).injective
  conv_lhs =>
    rw [Adjunction.homEquiv_naturality_right]
  let hZ :=
    (((SheafOfModules.forget Z.ringCatSheaf).map
      ((pushforwardComp f g).hom.app F)) ▷
        ((pushforward f ⋙ pushforward g).obj G).val) ≫
      (((pushforward (f ≫ g)).obj F).val ◁
        ((SheafOfModules.forget Z.ringCatSheaf).map
          ((pushforwardComp f g).hom.app G)))
  have hZh :
      tensorMapLeft ((pushforwardComp f g).hom.app F)
          ((pushforward f ⋙ pushforward g).obj G) ≫
        tensorMapRight ((pushforward (f ≫ g)).obj F)
          ((pushforwardComp f g).hom.app G) =
      (sheafification Z).map hZ := by
    dsimp only [tensorMapLeft, tensorMapRight, hZ]
    rw [← Functor.map_comp]
  have hright := adjZ.homEquiv_naturality_left hZ
    (pushforwardTensorHom (f ≫ g) F G)
  rw [← Category.assoc, hZh]
  change _ = adjZ.homEquiv _ _
    ((_root_.PresheafOfModules.sheafification
      (𝟙 Z.ringCatSheaf.obj)).map hZ ≫
      pushforwardTensorHom (f ≫ g) F G)
  rw [hright]
  rw [pushforwardTensorHom_homEquiv]
  have hcomp := pushforwardTensorHom_homEquiv (f ≫ g) F G
  have hcomp' :
      adjZ.homEquiv
          (((pushforward (f ≫ g)).obj F).val ⊗
            (SheafOfModules.forget Z.ringCatSheaf).obj
              ((pushforward (f ≫ g)).obj G))
          ((pushforward (f ≫ g)).obj (tensor F G))
          (pushforwardTensorHom (f ≫ g) F G) =
        pushforwardPresheafTensorHom (f ≫ g) F G ≫
          (_root_.PresheafOfModules.pushforward
            (f ≫ g).toRingCatSheafHom.hom).map
            ((_root_.PresheafOfModules.sheafificationAdjunction
              (𝟙 X.ringCatSheaf.obj)).unit.app (F.val ⊗ G.val)) := hcomp
  change _ = hZ ≫ adjZ.homEquiv _ _
    (pushforwardTensorHom (f ≫ g) F G)
  rw [hcomp']
  rw [Functor.map_comp]
  let adjY := _root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 Y.ringCatSheaf.obj)
  have hmf := pushforwardTensorHom_homEquiv f F G
  have hmf' :
      adjY.unit.app (((pushforward f).obj F).val ⊗
          ((pushforward f).obj G).val) ≫
        (SheafOfModules.forget Y.ringCatSheaf ⋙
          _root_.PresheafOfModules.restrictScalars
            (𝟙 Y.ringCatSheaf.obj)).map
          (pushforwardTensorHom f F G) =
      pushforwardPresheafTensorHom f F G ≫
        (_root_.PresheafOfModules.pushforward
          f.toRingCatSheafHom.hom).map
          ((_root_.PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).unit.app (F.val ⊗ G.val)) := by
    simpa only [Adjunction.homEquiv_apply] using hmf
  let pfg := _root_.PresheafOfModules.pushforward
    g.toRingCatSheafHom.hom
  change (pushforwardPresheafTensorHom g
        ((pushforward f).obj F) ((pushforward f).obj G) ≫
      pfg.map (adjY.unit.app (((pushforward f).obj F).val ⊗
        ((pushforward f).obj G).val))) ≫
      pfg.map ((SheafOfModules.forget Y.ringCatSheaf ⋙
        _root_.PresheafOfModules.restrictScalars
          (𝟙 Y.ringCatSheaf.obj)).map
        (pushforwardTensorHom f F G)) ≫ _ = _
  rw [← Category.assoc]
  slice_lhs 2 3 => rw [← pfg.map_comp, hmf', pfg.map_comp]
  apply _root_.PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  rfl

/-- Transposing after the canonical comparison from an iterated pullback agrees with
transposing along the composite and then applying the inverse pushforward comparison. -/
lemma comp_homEquiv_pullbackComp_hom {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) {A : Z.Modules} {B : X.Modules}
    (k : (pullback (f ≫ g)).obj A ⟶ B) :
    (((pullbackPushforwardAdjunction g).comp
      (pullbackPushforwardAdjunction f)).homEquiv A B)
        ((pullbackComp f g).hom.app A ≫ k) =
      (pullbackPushforwardAdjunction (f ≫ g)).homEquiv A B k ≫
        (pushforwardComp f g).inv.app B := by
  let adjComp := (pullbackPushforwardAdjunction g).comp
    (pullbackPushforwardAdjunction f)
  let adjComposite := pullbackPushforwardAdjunction (f ≫ g)
  have hconj := CategoryTheory.unit_conjugateEquiv
    adjComp adjComposite (pullbackComp f g).inv A
  rw [conjugateEquiv_pullbackComp_inv] at hconj
  have hunit : adjComp.unit.app A =
      adjComposite.unit.app A ≫
        (pushforward (f ≫ g)).map ((pullbackComp f g).inv.app A) ≫
        (pushforwardComp f g).inv.app
          ((pullback g ⋙ pullback f).obj A) := by
    rw [← Category.assoc, ← hconj, Category.assoc,
      Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  change adjComp.homEquiv A B ((pullbackComp f g).hom.app A ≫ k) = _
  rw [Adjunction.homEquiv_apply, Adjunction.homEquiv_apply,
    Functor.map_comp, hunit]
  simp only [Category.assoc]
  rw [← (pushforwardComp f g).inv.naturality_assoc
    ((pullbackComp f g).hom.app A)]
  slice_lhs 2 3 =>
    rw [← Functor.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id]
  calc
    _ = adjComposite.unit.app A ≫
        (pushforwardComp f g).inv.app ((pullback (f ≫ g)).obj A) ≫
        (pushforward f ⋙ pushforward g).map k :=
      congrArg (fun q ↦ adjComposite.unit.app A ≫ q ≫
        (pushforward f ⋙ pushforward g).map k)
        (Category.id_comp _)
    _ = _ := congrArg (fun q ↦ adjComposite.unit.app A ≫ q)
      ((pushforwardComp f g).inv.naturality k).symm

/-- The canonical oplax tensor comparison for pullback is compatible with composition
of scheme morphisms. -/
theorem pullbackTensorComparison_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (F G : Z.Modules) :
    (pullback f).map (pullbackTensorComparison g F G) ≫
        pullbackTensorComparison f ((pullback g).obj F) ((pullback g).obj G) ≫
        tensorMapLeft ((pullbackComp f g).hom.app F)
          ((pullback f).obj ((pullback g).obj G)) ≫
        tensorMapRight ((pullback (f ≫ g)).obj F)
          ((pullbackComp f g).hom.app G) =
      (pullbackComp f g).hom.app (tensor F G) ≫
        pullbackTensorComparison (f ≫ g) F G := by
  let adjg := pullbackPushforwardAdjunction g
  let adjf := pullbackPushforwardAdjunction f
  let adjcomp := adjg.comp adjf
  apply (adjcomp.homEquiv _ _).injective
  change adjg.homEquiv _ _ (adjf.homEquiv _ _
      ((pullback f).map (pullbackTensorComparison g F G) ≫
        pullbackTensorComparison f ((pullback g).obj F) ((pullback g).obj G) ≫
        tensorMapLeft ((pullbackComp f g).hom.app F)
          ((pullback f).obj ((pullback g).obj G)) ≫
        tensorMapRight ((pullback (f ≫ g)).obj F)
          ((pullbackComp f g).hom.app G))) =
    adjg.homEquiv _ _ (adjf.homEquiv _ _
      ((pullbackComp f g).hom.app (tensor F G) ≫
        pullbackTensorComparison (f ≫ g) F G))
  have hLf :
      adjf.homEquiv _ _
          ((pullback f).map (pullbackTensorComparison g F G) ≫
            pullbackTensorComparison f ((pullback g).obj F) ((pullback g).obj G) ≫
            tensorMapLeft ((pullbackComp f g).hom.app F)
              ((pullback f).obj ((pullback g).obj G)) ≫
            tensorMapRight ((pullback (f ≫ g)).obj F)
              ((pullbackComp f g).hom.app G)) =
        pullbackTensorComparison g F G ≫
          (tensorMapLeft (adjf.unit.app ((pullback g).obj F)) ((pullback g).obj G) ≫
            tensorMapRight ((pushforward f).obj ((pullback f).obj ((pullback g).obj F)))
              (adjf.unit.app ((pullback g).obj G)) ≫
            pushforwardTensorHom f ((pullback f).obj ((pullback g).obj F))
              ((pullback f).obj ((pullback g).obj G))) ≫
          (pushforward f).map
            (tensorMapLeft ((pullbackComp f g).hom.app F)
                ((pullback f).obj ((pullback g).obj G)) ≫
              tensorMapRight ((pullback (f ≫ g)).obj F)
                ((pullbackComp f g).hom.app G)) := by
    rw [Adjunction.homEquiv_naturality_left,
      Adjunction.homEquiv_naturality_right]
    dsimp only [pullbackTensorComparison]
    rw [Equiv.apply_symm_apply]
  rw [hLf]
  have hR := comp_homEquiv_pullbackComp_hom f g
    (pullbackTensorComparison (f ≫ g) F G)
  change adjg.homEquiv _ _ (adjf.homEquiv _ _
      ((pullbackComp f g).hom.app (tensor F G) ≫
        pullbackTensorComparison (f ≫ g) F G)) = _ at hR
  rw [hR]
  rw [Adjunction.homEquiv_naturality_right]
  dsimp only [pullbackTensorComparison]
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  apply (cancel_mono ((pushforwardComp f g).hom.app
    (tensor ((pullback (f ≫ g)).obj F) ((pullback (f ≫ g)).obj G)))).1
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp]
  have hnatg := pushforwardTensorHom_naturality g
    (adjf.unit.app ((pullback g).obj F))
    (adjf.unit.app ((pullback g).obj G))
  rw [Functor.map_comp] at hnatg
  have hnatg' :
      (tensorMapLeft
          ((pushforward g).map (adjf.unit.app ((pullback g).obj F)))
          ((pushforward g).obj ((pullback g).obj G)) ≫
        tensorMapRight
          ((pushforward g).obj ((pushforward f).obj
            ((pullback f).obj ((pullback g).obj F))))
          ((pushforward g).map (adjf.unit.app ((pullback g).obj G)))) ≫
        pushforwardTensorHom g
          ((pushforward f).obj ((pullback f).obj ((pullback g).obj F)))
          ((pushforward f).obj ((pullback f).obj ((pullback g).obj G))) =
      pushforwardTensorHom g ((pullback g).obj F) ((pullback g).obj G) ≫
        (pushforward g).map
          (tensorMapLeft (adjf.unit.app ((pullback g).obj F))
            ((pullback g).obj G)) ≫
        (pushforward g).map
          (tensorMapRight
            ((pushforward f).obj ((pullback f).obj ((pullback g).obj F)))
            (adjf.unit.app ((pullback g).obj G))) := hnatg
  slice_lhs 3 5 => rw [← hnatg']
  have hex :
      tensorMapRight ((pushforward g).obj ((pullback g).obj F))
          (adjg.unit.app G) ≫
        tensorMapLeft ((pushforward g).map
          (adjf.unit.app ((pullback g).obj F)))
          ((pushforward g).obj ((pullback g).obj G)) =
      tensorMapLeft ((pushforward g).map
          (adjf.unit.app ((pullback g).obj F))) G ≫
        tensorMapRight
          ((pushforward g).obj ((pushforward f).obj
            ((pullback f).obj ((pullback g).obj F))))
          (adjg.unit.app G) :=
    tensorMap_exchange _ _
  slice_lhs 2 3 => rw [hex]
  slice_lhs 1 2 => rw [← tensorMapLeft_comp]
  slice_lhs 2 3 => rw [← tensorMapRight_comp]
  have hunitF := Adjunction.comp_unit_app adjg adjf F
  have hunitG := Adjunction.comp_unit_app adjg adjf G
  change adjcomp.unit.app F = adjg.unit.app F ≫
    (pushforward g).map (adjf.unit.app ((pullback g).obj F)) at hunitF
  change adjcomp.unit.app G = adjg.unit.app G ≫
    (pushforward g).map (adjf.unit.app ((pullback g).obj G)) at hunitG
  rw [← hunitF, ← hunitG]
  let A : tensor ((pullback f).obj ((pullback g).obj F))
      ((pullback f).obj ((pullback g).obj G)) ⟶
      tensor ((pullback (f ≫ g)).obj F) ((pullback (f ≫ g)).obj G) :=
    tensorMapLeft ((pullbackComp f g).hom.app F)
      ((pullback f).obj ((pullback g).obj G)) ≫
      tensorMapRight ((pullback (f ≫ g)).obj F)
        ((pullbackComp f g).hom.app G)
  have hpc := (pushforwardComp f g).hom.naturality A
  change (pushforward g).map ((pushforward f).map A) ≫
      (pushforwardComp f g).hom.app _ =
    (pushforwardComp f g).hom.app _ ≫
      (pushforward (f ≫ g)).map A at hpc
  slice_lhs 5 6 => rw [hpc]
  have hpush :
      pushforwardTensorHom g
          ((pushforward f).obj ((pullback f).obj ((pullback g).obj F)))
          ((pushforward f).obj ((pullback f).obj ((pullback g).obj G))) ≫
        (pushforward g).map
          (pushforwardTensorHom f
            ((pullback f).obj ((pullback g).obj F))
            ((pullback f).obj ((pullback g).obj G))) ≫
        (pushforwardComp f g).hom.app
          (tensor ((pullback f).obj ((pullback g).obj F))
            ((pullback f).obj ((pullback g).obj G))) =
      tensorMapLeft
          ((pushforwardComp f g).hom.app
            ((pullback f).obj ((pullback g).obj F)))
          ((pushforward g).obj ((pushforward f).obj
            ((pullback f).obj ((pullback g).obj G)))) ≫
        tensorMapRight
          ((pushforward (f ≫ g)).obj
            ((pullback f).obj ((pullback g).obj F)))
          ((pushforwardComp f g).hom.app
            ((pullback f).obj ((pullback g).obj G))) ≫
        pushforwardTensorHom (f ≫ g)
          ((pullback f).obj ((pullback g).obj F))
          ((pullback f).obj ((pullback g).obj G)) :=
    pushforwardTensorHom_comp f g _ _
  slice_lhs 3 5 =>
    rw [hpush]
  have hex2 :
      tensorMapRight
          ((pushforward g).obj ((pushforward f).obj
            ((pullback f).obj ((pullback g).obj F))))
          (adjcomp.unit.app G) ≫
        tensorMapLeft
          ((pushforwardComp f g).hom.app
            ((pullback f).obj ((pullback g).obj F)))
          ((pushforward g).obj ((pushforward f).obj
            ((pullback f).obj ((pullback g).obj G)))) =
      tensorMapLeft
          ((pushforwardComp f g).hom.app
            ((pullback f).obj ((pullback g).obj F))) G ≫
        tensorMapRight
          ((pushforward (f ≫ g)).obj
            ((pullback f).obj ((pullback g).obj F)))
          (adjcomp.unit.app G) :=
    tensorMap_exchange _ _
  slice_lhs 2 3 => rw [hex2]
  slice_lhs 1 2 => rw [← tensorMapLeft_comp]
  slice_lhs 2 3 => rw [← tensorMapRight_comp]
  let adjk := pullbackPushforwardAdjunction (f ≫ g)
  have hconjF := CategoryTheory.unit_conjugateEquiv
    adjcomp adjk (pullbackComp f g).inv F
  have hconjG := CategoryTheory.unit_conjugateEquiv
    adjcomp adjk (pullbackComp f g).inv G
  rw [conjugateEquiv_pullbackComp_inv] at hconjF hconjG
  have hconjF' : adjcomp.unit.app F ≫
      (pushforwardComp f g).hom.app
        ((pullback f).obj ((pullback g).obj F)) =
    adjk.unit.app F ≫ (pushforward (f ≫ g)).map
      ((pullbackComp f g).inv.app F) := hconjF
  have hconjG' : adjcomp.unit.app G ≫
      (pushforwardComp f g).hom.app
        ((pullback f).obj ((pullback g).obj G)) =
    adjk.unit.app G ≫ (pushforward (f ≫ g)).map
      ((pullbackComp f g).inv.app G) := hconjG
  rw [hconjF', hconjG']
  rw [tensorMapLeft_comp, tensorMapRight_comp]
  slice_lhs 2 3 => rw [← tensorMap_exchange]
  let Ainv : tensor ((pullback (f ≫ g)).obj F)
      ((pullback (f ≫ g)).obj G) ⟶
      tensor ((pullback f).obj ((pullback g).obj F))
        ((pullback f).obj ((pullback g).obj G)) :=
    tensorMapLeft ((pullbackComp f g).inv.app F)
        ((pullback (f ≫ g)).obj G) ≫
      tensorMapRight ((pullback f).obj ((pullback g).obj F))
        ((pullbackComp f g).inv.app G)
  have hnatk := pushforwardTensorHom_naturality (f ≫ g)
    ((pullbackComp f g).inv.app F) ((pullbackComp f g).inv.app G)
  have hnatk' :
      (tensorMapLeft
          ((pushforward (f ≫ g)).map ((pullbackComp f g).inv.app F))
          ((pullback (f ≫ g) ⋙ pushforward (f ≫ g)).obj G) ≫
        tensorMapRight
          ((pushforward (f ≫ g)).obj
            ((pullback f).obj ((pullback g).obj F)))
          ((pushforward (f ≫ g)).map
            ((pullbackComp f g).inv.app G))) ≫
        pushforwardTensorHom (f ≫ g)
          ((pullback f).obj ((pullback g).obj F))
          ((pullback f).obj ((pullback g).obj G)) =
      pushforwardTensorHom (f ≫ g)
          ((pullback (f ≫ g)).obj F) ((pullback (f ≫ g)).obj G) ≫
        (pushforward (f ≫ g)).map Ainv := hnatk
  simp only [Category.assoc] at hnatk'
  slice_lhs 3 5 => rw [hnatk']
  have hAA : Ainv ≫ A =
      𝟙 (tensor ((pullback (f ≫ g)).obj F)
        ((pullback (f ≫ g)).obj G)) := by
    dsimp only [Ainv, A]
    simp only [Category.assoc]
    slice_lhs 2 3 => rw [tensorMap_exchange]
    slice_lhs 1 2 =>
      rw [← tensorMapLeft_comp, Iso.inv_hom_id_app, tensorMapLeft_id]
    simp only [Category.id_comp]
    rw [← tensorMapRight_comp, Iso.inv_hom_id_app, tensorMapRight_id]
  slice_lhs 4 5 => rw [← Functor.map_comp, hAA,
    CategoryTheory.Functor.map_id]
  simp only [Category.comp_id]
  rfl

/-- The tensor comparison for two successive pullbacks remains compatible after
identifying their composite with an equal morphism.  This is the form used for
cartesian squares, whose commuting triangle is usually propositionally rather than
definitionally equal. -/
theorem pullbackTensorComparison_comp_congr {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k)
    (F G : Z.Modules) :
    (pullback f).map (pullbackTensorComparison g F G) ≫
        pullbackTensorComparison f ((pullback g).obj F) ((pullback g).obj G) ≫
        tensorMapLeft
          ((pullbackComp f g).hom.app F ≫ (pullbackCongr h).hom.app F)
          ((pullback f).obj ((pullback g).obj G)) ≫
        tensorMapRight ((pullback k).obj F)
          ((pullbackComp f g).hom.app G ≫ (pullbackCongr h).hom.app G) =
      ((pullbackComp f g).hom.app (tensor F G) ≫
          (pullbackCongr h).hom.app (tensor F G)) ≫
        pullbackTensorComparison k F G := by
  subst k
  simp only [pullbackCongr_hom_app, eqToHom_refl, Category.comp_id]
  exact pullbackTensorComparison_comp f g F G

/-- Inverse form of `pullbackTensorComparison_comp_congr`: after identifying both
tensor factors and cancelling the outer tensor comparisons, the comparison for the
second pullback is the pullback of the inverse comparison for the first stage. -/
theorem pullbackTensorComparison_comp_congr_inv {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k)
    (F G : Z.Modules) [IsIso (pullbackTensorComparison g F G)]
    [IsIso (pullbackTensorComparison k F G)] :
    pullbackTensorComparison f ((pullback g).obj F) ((pullback g).obj G) ≫
        tensorMapLeft
          ((pullbackComp f g).hom.app F ≫ (pullbackCongr h).hom.app F)
          ((pullback f).obj ((pullback g).obj G)) ≫
        tensorMapRight ((pullback k).obj F)
          ((pullbackComp f g).hom.app G ≫ (pullbackCongr h).hom.app G) ≫
        inv (pullbackTensorComparison k F G) =
      (pullback f).map (inv (pullbackTensorComparison g F G)) ≫
        ((pullbackComp f g).hom.app (tensor F G) ≫
          (pullbackCongr h).hom.app (tensor F G)) := by
  rw [← cancel_epi ((pullback f).map (pullbackTensorComparison g F G))]
  slice_rhs 1 2 => rw [← Functor.map_comp, IsIso.hom_inv_id,
    (pullback f).map_id]
  simp only [Category.id_comp]
  rw [← cancel_mono (pullbackTensorComparison k F G)]
  slice_lhs 5 6 => rw [IsIso.inv_hom_id]
  simp only [Category.comp_id]
  exact pullbackTensorComparison_comp_congr f g k h F G

end AlgebraicGeometry.Scheme.Modules
