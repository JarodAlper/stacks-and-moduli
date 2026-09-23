module

public import StacksAndModuli.API.IdealSheafFromQuasicoherent
public import StacksAndModuli.«Section2.1-Intro».«part2.1.2-the-grassmannian-functor»
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.RingTheory.Flat.Equalizer

/-!
# Pullback of kernel ideal sheaves

This supporting module proves that the quasicoherent ideal sheaf obtained as the
kernel of a morphism `𝒪_Y ⟶ M` commutes with pullback along a flat morphism of
schemes.  The proof first establishes the coordinate calculation for spectra,
transports it to arbitrary affine schemes, and then globalizes over an affine
refinement of the inverse image of a target affine cover.

The main result is
`AlgebraicGeometry.Scheme.Modules.Hom.kernelIdealSheafData_pullback_of_flat`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

namespace Modules.Hom

variable {X Y : Scheme.{u}} {M : Y.Modules}

/-- The normalized pullback of a morphism from the structure sheaf, using the
canonical identification of the pulled-back structure sheaf with the source
structure sheaf. -/
noncomputable def pullbackUnitMap (f : X ⟶ Y)
    (phi : SheafOfModules.unit Y.ringCatSheaf ⟶ M) :
    SheafOfModules.unit X.ringCatSheaf ⟶ (Modules.pullback f).obj M :=
  inv (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ≫
    (Modules.pullback f).map phi

/-- Normalized pullback of structure-sheaf morphisms is natural in the target
module. -/
@[reassoc]
lemma pullbackUnitMap_naturality (f : X ⟶ Y)
    {M N : Y.Modules}
    (phi : SheafOfModules.unit Y.ringCatSheaf ⟶ M)
    (psi : SheafOfModules.unit Y.ringCatSheaf ⟶ N)
    (theta : M ⟶ N) (h : phi ≫ theta = psi) :
    pullbackUnitMap f phi ≫ (Modules.pullback f).map theta =
      pullbackUnitMap f psi := by
  dsimp only [pullbackUnitMap]
  rw [Category.assoc, ← Functor.map_comp, h]

/-- Normalized pullback preserves epimorphisms from the structure sheaf. -/
instance pullbackUnitMap_epi (f : X ⟶ Y)
    (phi : SheafOfModules.unit Y.ringCatSheaf ⟶ M) [Epi phi] :
    Epi (pullbackUnitMap f phi) := by
  let _ : Epi ((Modules.pullback f).map phi) :=
    CategoryTheory.Functor.map_epi (Modules.pullback f) phi
  let _ : Epi (inv (SheafOfModules.pullbackObjUnitToUnit
      f.toRingCatSheafHom)) := inferInstance
  dsimp only [pullbackUnitMap]
  infer_instance

/-- Normalized pullback of structure-sheaf morphisms is compatible with composition. -/
lemma pullbackUnitMap_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {M : Z.Modules} (phi : SheafOfModules.unit Z.ringCatSheaf ⟶ M) :
    pullbackUnitMap f (pullbackUnitMap g phi) ≫
        (Modules.pullbackComp f g).hom.app M =
      pullbackUnitMap (f ≫ g) phi := by
  let _ : IsIso (SheafOfModules.pullbackObjUnitToUnit
    f.toRingCatSheafHom) := inferInstance
  let _ : IsIso (SheafOfModules.pullbackObjUnitToUnit
    g.toRingCatSheafHom) := inferInstance
  let _ : IsIso (SheafOfModules.pullbackObjUnitToUnit
    (f ≫ g).toRingCatSheafHom) := inferInstance
  rw [pullbackUnitMap, pullbackUnitMap, pullbackUnitMap, Functor.map_comp]
  let a := inv (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
  let b := (Modules.pullback f).map
    (inv (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom))
  let c := (Modules.pullback f).map ((Modules.pullback g).map phi)
  let d := (Modules.pullbackComp f g).hom.app M
  let e := (Modules.pullbackComp f g).hom.app
    (SheafOfModules.unit Z.ringCatSheaf)
  let p := (Modules.pullback (f ≫ g)).map phi
  have hn : c ≫ d = e ≫ p := (Modules.pullbackComp f g).hom.naturality phi
  change (a ≫ b ≫ c) ≫ d = _
  calc
    _ = (a ≫ b) ≫ (c ≫ d) := by simp only [Category.assoc]
    _ = (a ≫ b) ≫ (e ≫ p) := by rw [hn]
    _ = (a ≫ b ≫ e) ≫ p := by simp only [Category.assoc]
    _ = _ := by rw [Modules.pullbackObjUnitToUnit_inv_comp_pullbackComp]

/-- Normalized pullback of a structure-sheaf morphism is compatible with replacing
the scheme morphism by an equal one. -/
lemma pullbackUnitMap_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    {M : Y.Modules} (phi : SheafOfModules.unit Y.ringCatSheaf ⟶ M) :
    pullbackUnitMap f phi ≫ (Modules.pullbackCongr h).hom.app M =
      pullbackUnitMap g phi := by
  let _ : IsIso (SheafOfModules.pullbackObjUnitToUnit
    f.toRingCatSheafHom) := inferInstance
  let _ : IsIso (SheafOfModules.pullbackObjUnitToUnit
    g.toRingCatSheafHom) := inferInstance
  rw [pullbackUnitMap, pullbackUnitMap]
  let a := inv (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
  let b := (Modules.pullback f).map phi
  let c := (Modules.pullbackCongr h).hom.app M
  let d := (Modules.pullbackCongr h).hom.app
    (SheafOfModules.unit Y.ringCatSheaf)
  let p := (Modules.pullback g).map phi
  have hn : b ≫ c = d ≫ p := (Modules.pullbackCongr h).hom.naturality phi
  change (a ≫ b) ≫ c = _
  calc
    _ = a ≫ (b ≫ c) := Category.assoc _ _ _
    _ = a ≫ (d ≫ p) := by rw [hn]
    _ = (a ≫ d) ≫ p := (Category.assoc _ _ _).symm
    _ = _ := by rw [Modules.pullbackObjUnitToUnit_inv_comp_pullbackCongr]

/-- The canonical comparison between the two iterated module pullbacks around a
commutative square. -/
noncomputable def pullbackCompCongrIso
    {W X Y Z : Scheme.{u}} (p : W ⟶ Y) (g : Y ⟶ Z)
    (f : W ⟶ X) (q : X ⟶ Z) (h : p ≫ g = f ≫ q)
    (M : Z.Modules) :
    (Modules.pullback p).obj ((Modules.pullback g).obj M) ≅
      (Modules.pullback f).obj ((Modules.pullback q).obj M) :=
  (Modules.pullbackComp p g).app M ≪≫
    (Modules.pullbackCongr h).app M ≪≫
    ((Modules.pullbackComp f q).app M).symm

/-- The comparison isomorphism around a commutative square identifies the two
iterated normalized pullbacks of a structure-sheaf morphism. -/
lemma pullbackUnitMap_comp_pullbackCompCongrIso
    {W X Y Z : Scheme.{u}} (p : W ⟶ Y) (g : Y ⟶ Z)
    (f : W ⟶ X) (q : X ⟶ Z) (h : p ≫ g = f ≫ q)
    {M : Z.Modules} (phi : SheafOfModules.unit Z.ringCatSheaf ⟶ M) :
    pullbackUnitMap p (pullbackUnitMap g phi) ≫
        (pullbackCompCongrIso p g f q h M).hom =
      pullbackUnitMap f (pullbackUnitMap q phi) := by
  have h1 := pullbackUnitMap_comp p g phi
  have h2 := pullbackUnitMap_congr h phi
  have h3 := pullbackUnitMap_comp f q phi
  dsimp only [pullbackCompCongrIso, Iso.trans_hom, Iso.symm_hom]
  change (pullbackUnitMap p (pullbackUnitMap g phi) ≫
      (Modules.pullbackComp p g).hom.app M) ≫
    ((Modules.pullbackCongr h).hom.app M ≫
      (Modules.pullbackComp f q).inv.app M) = _
  rw [h1, ← Category.assoc, h2]
  rw [← h3]
  change (pullbackUnitMap f (pullbackUnitMap q phi) ≫
      ((Modules.pullbackComp f q).app M).hom) ≫
    ((Modules.pullbackComp f q).app M).inv = _
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- The coordinate linear map of a morphism from the structure sheaf on an affine
spectrum. -/
noncomputable def affineUnitLinearMap (M : (Spec R).Modules)
    (phi : SheafOfModules.unit (Spec R).ringCatSheaf ⟶ M) :
    R →ₗ[R] moduleSpecΓFunctor.obj M :=
  ((unitModuleSpecΓIso R).hom ≫ moduleSpecΓFunctor.map phi).hom

/-- The ideal underlying the kernel of an `R`-linear map out of the rank-one free
module `R`. -/
noncomputable def linearKernelIdeal {R : Type*} [CommRing R]
    {N : Type*} [AddCommGroup N] [Module R N] (l : R →ₗ[R] N) : Ideal R where
  __ := LinearMap.ker l

/-- Extend a section on the top open to a compatible family over all opens. -/
noncomputable def sectionsOfTop {X : Scheme.{u}} (M : X.Modules)
    (x : Γ(M, ⊤)) : M.sections :=
  M.val.sectionsMk
    (fun U ↦ M.presheaf.map (homOfLE (le_top (a := U.unop))).op x)
    (fun {U V} g ↦ by
      let a := (homOfLE (le_top (a := U.unop))).op
      let b := (homOfLE (le_top (a := V.unop))).op
      change M.presheaf.map g (M.presheaf.map a x) = M.presheaf.map b x
      have hab : a ≫ g = b := Subsingleton.elim _ _
      have hm : M.presheaf.map a ≫ M.presheaf.map g = M.presheaf.map b := by
        rw [← M.presheaf.map_comp, hab]
      exact ConcreteCategory.congr_hom hm x)

/-- The top component of `sectionsOfTop` is the original section. -/
@[simp]
lemma sectionsOfTop_apply_top {X : Scheme.{u}} (M : X.Modules)
    (x : Γ(M, ⊤)) :
    (sectionsOfTop M x).1 (.op ⊤) = x := by
  change M.presheaf.map (homOfLE (le_top (a := (⊤ : X.Opens)))).op x = x
  let a := (homOfLE (le_top (a := (⊤ : X.Opens)))).op
  have ha : a = 𝟙 (Opposite.op (⊤ : X.Opens)) := Subsingleton.elim _ _
  have hm : M.presheaf.map a = 𝟙 _ := by rw [ha, M.presheaf.map_id]
  exact ConcreteCategory.congr_hom hm x

/-- Restriction of compatible families is natural in a morphism of module sheaves. -/
lemma restrictSection_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] {M N : Y.Modules} (g : M ⟶ N) (s : M.sections) :
    SheafOfModules.sectionsMap ((Modules.restrictFunctor f).map g)
        (Modules.restrictSection f M s) =
      Modules.restrictSection f N (SheafOfModules.sectionsMap g s) := by
  apply Modules.sections_ext_top
  rw [Modules.restrictSection_apply]
  change Modules.Hom.app ((Modules.restrictFunctor f).map g) ⊤
      ((Modules.restrictSection f M s).1 (.op ⊤)) =
    Modules.Hom.app g (f ''ᵁ ⊤) (s.1 (.op (f ''ᵁ ⊤)))
  rw [Modules.restrictSection_apply]
  rfl

/-- Along a scheme isomorphism, a global section is killed by a normalized pulled-back
map exactly when the original global section is killed. -/
lemma pullbackUnitMap_appTop_zero_iff_of_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] {M : Y.Modules}
    (phi : SheafOfModules.unit Y.ringCatSheaf ⟶ M) (y : Γ(Y, ⊤)) :
    Modules.Hom.app (pullbackUnitMap f phi) ⊤ (f.appTop.hom y) = 0 ↔
      Modules.Hom.app phi ⊤ y = 0 := by
  letI : IsOpenImmersion f := inferInstance
  let s := sectionsOfTop (SheafOfModules.unit Y.ringCatSheaf) y
  let r := Modules.restrictSection f
    (SheafOfModules.unit Y.ringCatSheaf) s
  let a := SheafOfModules.sectionsMap (Modules.restrictUnitIso f).hom r
  have haTop : a.1 (.op ⊤) = f.appTop.hom y := by
    simpa only [a, s, sectionsOfTop_apply_top] using
      Modules.sectionsMap_restrictUnitIso_restrictSection_appTop f s
  have ha : a = sectionsOfTop (SheafOfModules.unit X.ringCatSheaf)
      (f.appTop.hom y) := by
    apply Modules.sections_ext_top
    rw [haTop, sectionsOfTop_apply_top]
  have hp := Modules.pullbackObjUnitToUnit_inv_comp_pullback_map f phi
  have hps := congrArg
    (fun k : SheafOfModules.unit X.ringCatSheaf ⟶
        (Modules.pullback f).obj M ↦ SheafOfModules.sectionsMap k a) hp
  have hcancel : SheafOfModules.sectionsMap (Modules.restrictUnitIso f).inv a = r := by
    change SheafOfModules.sectionsMap (Modules.restrictUnitIso f).inv
      (SheafOfModules.sectionsMap (Modules.restrictUnitIso f).hom r) = r
    rw [← SheafOfModules.sectionsMap_comp,
      (Modules.restrictUnitIso f).hom_inv_id,
      SheafOfModules.sectionsMap_id]
  have hps' : SheafOfModules.sectionsMap (pullbackUnitMap f phi) a =
      SheafOfModules.sectionsMap
        ((Modules.restrictFunctorIsoPullback f).hom.app M)
        (Modules.restrictSection f M
          (SheafOfModules.sectionsMap phi s)) := by
    calc
      _ = SheafOfModules.sectionsMap
          ((Modules.restrictUnitIso f).inv ≫
            (Modules.restrictFunctor f).map phi ≫
            (Modules.restrictFunctorIsoPullback f).hom.app M) a := hps
      _ = SheafOfModules.sectionsMap
          ((Modules.restrictFunctorIsoPullback f).hom.app M)
          (SheafOfModules.sectionsMap ((Modules.restrictFunctor f).map phi)
            (SheafOfModules.sectionsMap (Modules.restrictUnitIso f).inv a)) := rfl
      _ = _ := by rw [hcancel, restrictSection_naturality]
  have htop := congrArg (fun z ↦ z.1 (.op ⊤)) hps'
  change Modules.Hom.app (pullbackUnitMap f phi) ⊤ (a.1 (.op ⊤)) =
    ((Modules.restrictFunctorIsoPullback f).hom.app M).val.app (.op ⊤)
      ((Modules.restrictSection f M
        (SheafOfModules.sectionsMap phi s)).1 (.op ⊤)) at htop
  rw [haTop] at htop
  rw [htop]
  let eU : (((Modules.restrictFunctor f).obj M).val.obj (.op ⊤)) ≅
      (((Modules.pullback f).obj M).val.obj (.op ⊤)) :=
    { hom := (Modules.restrictFunctorIsoPullback f).hom.app M |>.val.app (.op ⊤)
      inv := (Modules.restrictFunctorIsoPullback f).inv.app M |>.val.app (.op ⊤)
      hom_inv_id := congrArg (fun k ↦ k.val.app (.op ⊤))
        ((Modules.restrictFunctorIsoPullback f).app M).hom_inv_id
      inv_hom_id := congrArg (fun k ↦ k.val.app (.op ⊤))
        ((Modules.restrictFunctorIsoPullback f).app M).inv_hom_id }
  change eU.hom.hom
      ((Modules.restrictSection f M
        (SheafOfModules.sectionsMap phi s)).1 (.op ⊤)) = 0 ↔ _
  have hezero (z : ((Modules.restrictFunctor f).obj M).val.obj (.op ⊤)) :
      eU.hom.hom z = 0 ↔ z = 0 := by
    constructor
    · intro hz
      have hz' : eU.toLinearEquiv z = eU.toLinearEquiv 0 := by
        change eU.hom.hom z = eU.hom.hom 0
        simpa only [map_zero] using hz
      exact eU.toLinearEquiv.injective hz'
    · intro hz
      rw [hz, map_zero]
  rw [hezero]
  rw [Modules.restrictSection_apply]
  have him : f ''ᵁ (⊤ : X.Opens) = (⊤ : Y.Opens) := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]
  let sy := SheafOfModules.sectionsMap phi s
  have hres : M.presheaf.map (eqToHom him).op (sy.1 (.op ⊤)) =
      sy.1 (.op (f ''ᵁ ⊤)) := sy.property (eqToHom him).op
  have hzero : sy.1 (.op (f ''ᵁ ⊤)) = 0 ↔ sy.1 (.op ⊤) = 0 := by
    constructor
    · intro hz
      let a := (eqToHom him).op
      let b := (eqToHom him.symm).op
      have hab : a ≫ b = 𝟙 _ := Subsingleton.elim _ _
      have hm : M.presheaf.map a ≫ M.presheaf.map b = 𝟙 _ := by
        rw [← M.presheaf.map_comp, hab, M.presheaf.map_id]
      calc
        sy.1 (.op ⊤) = M.presheaf.map b
            (M.presheaf.map a (sy.1 (.op ⊤))) := by
          simpa using (ConcreteCategory.congr_hom hm (sy.1 (.op ⊤))).symm
        _ = M.presheaf.map b (sy.1 (.op (f ''ᵁ ⊤))) := by rw [hres]
        _ = 0 := by rw [hz, map_zero]
    · intro hz
      rw [← hres, hz, map_zero]
  change sy.1 (.op (f ''ᵁ ⊤)) = 0 ↔ Modules.Hom.app phi ⊤ y = 0
  rw [hzero]
  change Modules.Hom.app phi ⊤ (s.1 (.op ⊤)) = 0 ↔
    Modules.Hom.app phi ⊤ y = 0
  rw [show s.1 (.op ⊤) = y from sectionsOfTop_apply_top _ _]

/-- Along an open immersion, a section over the image of the source is killed by a
normalized pulled-back map exactly when it is killed by the original map. -/
lemma pullbackUnitMap_appTop_zero_iff_of_isOpenImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {M : Y.Modules}
    (phi : SheafOfModules.unit Y.ringCatSheaf ⟶ M)
    (y : Γ(Y, f ''ᵁ (⊤ : X.Opens))) :
    Modules.Hom.app (pullbackUnitMap f phi) ⊤
        ((f.appIso ⊤).hom.hom y) = 0 ↔
      Modules.Hom.app phi (f ''ᵁ (⊤ : X.Opens)) y = 0 := by
  let r := sectionsOfTop
    ((Modules.restrictFunctor f).obj
      (SheafOfModules.unit Y.ringCatSheaf)) y
  let a := SheafOfModules.sectionsMap (Modules.restrictUnitIso f).hom r
  have haTop : a.1 (.op ⊤) = (f.appIso ⊤).hom.hom y := by
    change (f.appIso ⊤).hom.hom (r.1 (.op ⊤)) = _
    rw [show r.1 (.op ⊤) = y from sectionsOfTop_apply_top _ _]
  have hp := Modules.pullbackObjUnitToUnit_inv_comp_pullback_map f phi
  have hps := congrArg
    (fun k : SheafOfModules.unit X.ringCatSheaf ⟶
        (Modules.pullback f).obj M ↦ SheafOfModules.sectionsMap k a) hp
  have hcancel : SheafOfModules.sectionsMap
      (Modules.restrictUnitIso f).inv a = r := by
    change SheafOfModules.sectionsMap (Modules.restrictUnitIso f).inv
      (SheafOfModules.sectionsMap (Modules.restrictUnitIso f).hom r) = r
    rw [← SheafOfModules.sectionsMap_comp,
      (Modules.restrictUnitIso f).hom_inv_id,
      SheafOfModules.sectionsMap_id]
  have hps' : SheafOfModules.sectionsMap (pullbackUnitMap f phi) a =
      SheafOfModules.sectionsMap
        ((Modules.restrictFunctorIsoPullback f).hom.app M)
        (SheafOfModules.sectionsMap ((Modules.restrictFunctor f).map phi) r) := by
    calc
      _ = SheafOfModules.sectionsMap
          ((Modules.restrictUnitIso f).inv ≫
            (Modules.restrictFunctor f).map phi ≫
            (Modules.restrictFunctorIsoPullback f).hom.app M) a := hps
      _ = SheafOfModules.sectionsMap
          ((Modules.restrictFunctorIsoPullback f).hom.app M)
          (SheafOfModules.sectionsMap ((Modules.restrictFunctor f).map phi)
            (SheafOfModules.sectionsMap (Modules.restrictUnitIso f).inv a)) := rfl
      _ = _ := by rw [hcancel]
  have htop := congrArg (fun z ↦ z.1 (.op ⊤)) hps'
  change Modules.Hom.app (pullbackUnitMap f phi) ⊤ (a.1 (.op ⊤)) =
    ((Modules.restrictFunctorIsoPullback f).hom.app M).val.app (.op ⊤)
      ((SheafOfModules.sectionsMap
        ((Modules.restrictFunctor f).map phi) r).1 (.op ⊤)) at htop
  rw [haTop] at htop
  rw [htop]
  let eU : (((Modules.restrictFunctor f).obj M).val.obj (.op ⊤)) ≅
      (((Modules.pullback f).obj M).val.obj (.op ⊤)) :=
    { hom := (Modules.restrictFunctorIsoPullback f).hom.app M |>.val.app (.op ⊤)
      inv := (Modules.restrictFunctorIsoPullback f).inv.app M |>.val.app (.op ⊤)
      hom_inv_id := congrArg (fun k ↦ k.val.app (.op ⊤))
        ((Modules.restrictFunctorIsoPullback f).app M).hom_inv_id
      inv_hom_id := congrArg (fun k ↦ k.val.app (.op ⊤))
        ((Modules.restrictFunctorIsoPullback f).app M).inv_hom_id }
  change eU.hom.hom
      ((SheafOfModules.sectionsMap
        ((Modules.restrictFunctor f).map phi) r).1 (.op ⊤)) = 0 ↔ _
  have hezero (z : ((Modules.restrictFunctor f).obj M).val.obj (.op ⊤)) :
      eU.hom.hom z = 0 ↔ z = 0 := by
    constructor
    · intro hz
      have hz' : eU.toLinearEquiv z = eU.toLinearEquiv 0 := by
        change eU.hom.hom z = eU.hom.hom 0
        simpa only [map_zero] using hz
      exact eU.toLinearEquiv.injective hz'
    · intro hz
      rw [hz, map_zero]
  rw [hezero]
  change Modules.Hom.app phi (f ''ᵁ (⊤ : X.Opens))
      (r.1 (.op ⊤)) = 0 ↔ _
  rw [show r.1 (.op ⊤) = y from sectionsOfTop_apply_top _ _]

/-- On an affine source, the kernel ideal sheaf of a normalized pullback along an open
immersion is the pullback of the original kernel ideal sheaf. -/
lemma kernelIdealSheafData_pullback_of_isOpenImmersion_of_isAffineSource
    {X Y : Scheme.{u}} [IsAffine X] (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) [M.IsQuasicoherent]
    [((Modules.pullback f).obj M).IsQuasicoherent]
    (phi : SheafOfModules.unit Y.ringCatSheaf ⟶ M) :
    kernelIdealSheafData ((Modules.pullback f).obj M) (pullbackUnitMap f phi) =
      (kernelIdealSheafData M phi).comap f := by
  apply IdealSheafData.ext_of_isAffine
  rw [IdealSheafData.ideal_comap_of_isOpenImmersion]
  ext x
  simp only [kernelIdealSheafData_ideal, Ideal.mem_comap]
  rw [mem_kernelIdeal_iff, mem_kernelIdeal_iff]
  let e := f.appIso (⊤ : X.Opens)
  have h := pullbackUnitMap_appTop_zero_iff_of_isOpenImmersion f phi (e.inv.hom x)
  have hex : e.hom.hom (e.inv.hom x) = x := by
    simpa using ConcreteCategory.congr_hom e.hom_inv_id x
  rw [hex] at h
  exact h

/-- Isomorphic quasicoherent targets with compatible structure-sheaf morphisms have
the same kernel ideal-sheaf data. -/
lemma kernelIdealSheafData_eq_of_iso {X : Scheme.{u}} (M N : X.Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (phi : SheafOfModules.unit X.ringCatSheaf ⟶ M)
    (psi : SheafOfModules.unit X.ringCatSheaf ⟶ N)
    (e : M ≅ N) (h : phi ≫ e.hom = psi) :
    kernelIdealSheafData M phi = kernelIdealSheafData N psi := by
  ext U x
  simp only [kernelIdealSheafData_ideal, mem_kernelIdeal_iff]
  have hx := congrArg
    (fun k : SheafOfModules.unit X.ringCatSheaf ⟶ N ↦
      Modules.Hom.app k U.1 x) h
  change e.hom.val.app (.op U.1) (Modules.Hom.app phi U.1 x) =
    Modules.Hom.app psi U.1 x at hx
  rw [← hx]
  let eU : M.val.obj (.op U.1) ≅ N.val.obj (.op U.1) :=
    { hom := e.hom.val.app (.op U.1)
      inv := e.inv.val.app (.op U.1)
      hom_inv_id := congrArg (fun k ↦ k.val.app (.op U.1)) e.hom_inv_id
      inv_hom_id := congrArg (fun k ↦ k.val.app (.op U.1)) e.inv_hom_id }
  change Modules.Hom.app phi U.1 x = 0 ↔
    eU.hom.hom (Modules.Hom.app phi U.1 x) = 0
  constructor
  · intro hx
    rw [hx, map_zero]
  · intro hx
    have hx' : eU.toLinearEquiv (Modules.Hom.app phi U.1 x) =
        eU.toLinearEquiv 0 := by
      change eU.hom.hom (Modules.Hom.app phi U.1 x) = eU.hom.hom 0
      simpa only [map_zero] using hx
    exact eU.toLinearEquiv.injective hx'

/-- If a linear map out of `R` is surjective, its kernel ideal after scalar extension
to `S` is the extension of its original kernel ideal. -/
lemma linearKernelIdeal_baseChange_rid {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] {N : Type*} [AddCommGroup N] [Module R N]
    (l : R →ₗ[R] N) (hl : Function.Surjective l) :
    linearKernelIdeal ((l.baseChange S).comp
      (TensorProduct.AlgebraTensorModule.rid R S S).symm.toLinearMap) =
      (linearKernelIdeal l).map (algebraMap R S) := by
  let e := TensorProduct.AlgebraTensorModule.rid R S S
  let g := (l.baseChange S).comp e.symm.toLinearMap
  have hk : LinearMap.ker (LinearMap.lTensor S l) =
      LinearMap.range (LinearMap.lTensor S (LinearMap.ker l).subtype) :=
    (lTensor_exact S l.exact_subtype_ker_map hl).linearMap_ker_eq
  apply le_antisymm
  · intro s hs
    have hmem_all (x : TensorProduct R S (LinearMap.ker l)) :
        e ((LinearMap.lTensor S (LinearMap.ker l).subtype) x) ∈
          (linearKernelIdeal l).map (algebraMap R S) := by
      induction x using TensorProduct.induction_on with
      | zero => simpa using Ideal.zero_mem _
      | tmul a k =>
          simpa [e, linearKernelIdeal, Algebra.smul_def, mul_comm] using
            Ideal.mul_mem_left ((linearKernelIdeal l).map (algebraMap R S)) a
              (Ideal.mem_map_of_mem (algebraMap R S) k.2)
      | add x y hxmem hymem =>
          simpa only [map_add] using Ideal.add_mem _ hxmem hymem
    have hs' : e.symm s ∈ LinearMap.ker (LinearMap.lTensor S l) := by
      rw [LinearMap.mem_ker]
      have hsg : g s = 0 := hs
      change l.baseChange S (e.symm s) = 0 at hsg
      simpa only [LinearMap.baseChange_eq_ltensor] using hsg
    rw [hk] at hs'
    obtain ⟨x, hx⟩ := hs'
    have hmem := hmem_all x
    rw [hx, e.apply_symm_apply] at hmem
    exact hmem
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change g (algebraMap R S r) = 0
    change l.baseChange S (e.symm (algebraMap R S r)) = 0
    rw [show e.symm (algebraMap R S r) = 1 ⊗ₜ[R] r by
      apply e.injective
      simp [e, Algebra.smul_def]]
    rw [LinearMap.baseChange_tmul]
    have hlr : l r = 0 := hr
    rw [hlr, TensorProduct.tmul_zero]

/-- If `S` is flat over `R`, the kernel ideal of any linear map out of `R` commutes
with scalar extension to `S`. -/
lemma linearKernelIdeal_baseChange_rid_of_flat {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [Module.Flat R S]
    {N : Type*} [AddCommGroup N] [Module R N] (l : R →ₗ[R] N) :
    linearKernelIdeal ((l.baseChange S).comp
      (TensorProduct.AlgebraTensorModule.rid R S S).symm.toLinearMap) =
      (linearKernelIdeal l).map (algebraMap R S) := by
  let e := TensorProduct.AlgebraTensorModule.rid R S S
  let g := (l.baseChange S).comp e.symm.toLinearMap
  have hk : LinearMap.ker (LinearMap.lTensor S l) =
      LinearMap.range (LinearMap.lTensor S (LinearMap.ker l).subtype) :=
    (Module.Flat.lTensor_exact S l.exact_subtype_ker_map).linearMap_ker_eq
  apply le_antisymm
  · intro s hs
    have hmem_all (x : TensorProduct R S (LinearMap.ker l)) :
        e ((LinearMap.lTensor S (LinearMap.ker l).subtype) x) ∈
          (linearKernelIdeal l).map (algebraMap R S) := by
      induction x using TensorProduct.induction_on with
      | zero => simpa using Ideal.zero_mem _
      | tmul a k =>
          simpa [e, linearKernelIdeal, Algebra.smul_def, mul_comm] using
            Ideal.mul_mem_left ((linearKernelIdeal l).map (algebraMap R S)) a
              (Ideal.mem_map_of_mem (algebraMap R S) k.2)
      | add x y hxmem hymem =>
          simpa only [map_add] using Ideal.add_mem _ hxmem hymem
    have hs' : e.symm s ∈ LinearMap.ker (LinearMap.lTensor S l) := by
      rw [LinearMap.mem_ker]
      have hsg : g s = 0 := hs
      change l.baseChange S (e.symm s) = 0 at hsg
      simpa only [LinearMap.baseChange_eq_ltensor] using hsg
    rw [hk] at hs'
    obtain ⟨x, hx⟩ := hs'
    have hmem := hmem_all x
    rw [hx, e.apply_symm_apply] at hmem
    exact hmem
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change g (algebraMap R S r) = 0
    change l.baseChange S (e.symm (algebraMap R S r)) = 0
    rw [show e.symm (algebraMap R S r) = 1 ⊗ₜ[R] r by
      apply e.injective
      simp [e, Algebra.smul_def]]
    rw [LinearMap.baseChange_tmul]
    have hlr : l r = 0 := hr
    rw [hlr, TensorProduct.tmul_zero]

/-- In a pushout square of commutative rings whose lower input map is surjective, the
kernel of the upper output map is the extension of the lower input kernel. -/
lemma CommRingCat.ker_eq_map_of_isPushout_of_surjective
    {R A B P : CommRingCat.{u}} {f : R ⟶ A} {g : R ⟶ B}
    {a : A ⟶ P} {b : B ⟶ P} (h : IsPushout f g a b)
    (hg : Function.Surjective g.hom) :
    RingHom.ker a.hom = (RingHom.ker g.hom).map f.hom := by
  algebraize [f.hom, g.hom]
  let hT := CommRingCat.isPushout_tensorProduct R A B
  let e := (hT.isoIsPushout A B h).commRingCatIsoToRingEquiv
  have ha : CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := B)) ≫
        e.toCommRingCatIso.hom = a := hT.inl_isoIsPushout_hom A B h
  rw [← ha]
  change RingHom.ker (e.toRingHom.comp
      (Algebra.TensorProduct.includeLeftRingHom (R := R)
        (A := A) (B := B))) = _
  rw [RingHom.ker_equiv_comp]
  let l : R →ₗ[R] B := Algebra.linearMap R B
  have hl : Function.Surjective l := by
    change Function.Surjective (algebraMap R B)
    exact hg
  let rid := TensorProduct.AlgebraTensorModule.rid R A A
  have hmap : (l.baseChange A).comp rid.symm.toLinearMap =
      (Algebra.TensorProduct.includeLeft (R := R)
        (A := A) (B := B)).toLinearMap := by
    ext x
    simp [l, rid]
  have hk := linearKernelIdeal_baseChange_rid
    (R := R) (S := A) (N := B) l hl
  change RingHom.ker (Algebra.TensorProduct.includeLeftRingHom (R := R)
      (A := A) (B := B)) =
    (RingHom.ker (algebraMap R B)).map (algebraMap R A)
  ext x
  have hkx := SetLike.ext_iff.mp hk x
  change ((l.baseChange A).comp rid.symm.toLinearMap) x = 0 ↔
    x ∈ (RingHom.ker (algebraMap R B)).map (algebraMap R A) at hkx
  rw [hmap] at hkx
  exact hkx

/-- Pullback of ideal-sheaf data between affine schemes is extension of the ideal of
global sections along the induced coordinate-ring map. -/
lemma IdealSheafData.comap_ideal_top_of_isAffine
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (I : Y.IdealSheafData) (f : X ⟶ Y) :
    (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ =
      (I.ideal ⟨⊤, isAffineOpen_top Y⟩).map f.appTop.hom := by
  letI : IsAffine I.subscheme := isAffine_of_isAffineHom I.subschemeι
  rw [IdealSheafData.comap, Scheme.Hom.ker_apply]
  change RingHom.ker (CategoryTheory.Limits.pullback.fst f I.subschemeι).appTop.hom = _
  rw [CommRingCat.ker_eq_map_of_isPushout_of_surjective
    (isPushout_appTop_of_isPullback
      (IsPullback.of_hasPullback f I.subschemeι)) (by
        simpa using I.subschemeι_app_surjective
          ⟨⊤, isAffineOpen_top Y⟩)]
  have hker := I.ker_subschemeι_app ⟨⊤, isAffineOpen_top Y⟩
  change RingHom.ker I.subschemeι.appTop.hom =
    I.ideal ⟨⊤, isAffineOpen_top Y⟩ at hker
  rw [hker]

/-- On affine schemes, kernel ideal-sheaf data commute with pullback along an
isomorphism. -/
lemma kernelIdealSheafData_pullback_of_isIso_of_isAffine
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) [IsIso f]
    (M : Y.Modules) [M.IsQuasicoherent]
    [((Modules.pullback f).obj M).IsQuasicoherent]
    (phi : SheafOfModules.unit Y.ringCatSheaf ⟶ M) :
    kernelIdealSheafData ((Modules.pullback f).obj M) (pullbackUnitMap f phi) =
      (kernelIdealSheafData M phi).comap f := by
  apply IdealSheafData.ext_of_isAffine
  rw [IdealSheafData.comap_ideal_top_of_isAffine]
  simp only [kernelIdealSheafData_ideal]
  ext x
  rw [mem_kernelIdeal_iff,
    Ideal.mem_map_iff_of_surjective f.appTop.hom
      (ConcreteCategory.bijective_of_isIso f.appTop).2]
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := (ConcreteCategory.bijective_of_isIso f.appTop).2 x
    exact ⟨y, (pullbackUnitMap_appTop_zero_iff_of_isIso f phi y).mp hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact (pullbackUnitMap_appTop_zero_iff_of_isIso f phi y).mpr hy

/-- On a spectrum, the top-open component of kernel ideal-sheaf data is the coordinate
kernel ideal, transported through the canonical global-sections isomorphism. -/
lemma kernelIdeal_top_eq_map_affineUnitLinearMap
    {R : CommRingCat.{u}} (M : (Spec R).Modules)
    (phi : SheafOfModules.unit (Spec R).ringCatSheaf ⟶ M) :
    kernelIdeal phi ⟨⊤, isAffineOpen_top (Spec R)⟩ =
      (linearKernelIdeal (affineUnitLinearMap M phi)).map
        (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv := by
  let e := (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv
  ext x
  rw [← Ideal.symm_apply_mem_of_equiv_iff (f := e)]
  change AlgebraicGeometry.Scheme.Modules.Hom.app phi ⊤ x = 0 ↔
    affineUnitLinearMap M phi (e.symm x) = 0
  change AlgebraicGeometry.Scheme.Modules.Hom.app phi ⊤ x = 0 ↔
    AlgebraicGeometry.Scheme.Modules.Hom.app phi ⊤
      ((unitModuleSpecΓIso R).hom ((Scheme.ΓSpecIso R).hom x)) = 0
  rw [unitModuleSpecΓIso_hom_apply]
  simp

/-- Precomposition by the scalar automorphism occurring in normalized rank-one
pullback does not change a linear kernel. -/
lemma ker_comp_unitPullbackScalarEquiv {R S : CommRingCat.{u}}
    (f : R ⟶ S) {N : Type*} [AddCommGroup N] [Module S N]
    (g : S →ₗ[S] N) :
    LinearMap.ker (g.comp (unitPullbackScalarEquiv f).toLinearMap) =
      LinearMap.ker g := by
  ext s
  simp only [LinearMap.mem_ker, LinearMap.comp_apply]
  have hs : unitPullbackScalarEquiv f s =
      unitPullbackScalarEquiv f 1 • s := by
    rw [unitPullbackScalarEquiv_apply, smul_eq_mul, mul_comm]
  constructor
  · intro h
    change g (unitPullbackScalarEquiv f s) = 0 at h
    rw [hs, g.map_smul,
      (isUnit_unitPullbackScalarEquiv_one f).smul_eq_zero] at h
    exact h
  · intro h
    change g (unitPullbackScalarEquiv f s) = 0
    rw [hs, g.map_smul,
      (isUnit_unitPullbackScalarEquiv_one f).smul_eq_zero, h]

/-- The global-sections map of normalized pullback on spectra agrees with extension
of scalars after the canonical source and target identifications. -/
lemma affine_pullbackUnitMap_sections_naturality
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    (phi : SheafOfModules.unit (Spec R).ringCatSheaf ⟶ M) :
    moduleSpecΓFunctor.map (pullbackUnitMap (Spec.map f) phi) ≫
        (pullbackQuasicoherentSectionsIso f M).hom =
      (unitPullbackSectionsIso f).hom ≫
        (ModuleCat.extendScalars f.hom).map
          (moduleSpecΓFunctor.map phi) := by
  let _ : (SheafOfModules.unit (Spec R).ringCatSheaf).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
      (tildeSelf (R := R)) inferInstance
  have hn := pullbackQuasicoherentSectionsIso_naturality f phi
  rw [pullbackUnitMap, Functor.map_comp]
  simp only [Category.assoc]
  rw [hn]
  rfl

/-- Coordinate linear maps for normalized pullback on spectra commute with extension
of scalars. -/
lemma affine_pullbackUnitMap_naturality
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    (phi : SheafOfModules.unit (Spec R).ringCatSheaf ⟶ M) :
    (unitModuleSpecΓIso S).hom ≫
        moduleSpecΓFunctor.map (pullbackUnitMap (Spec.map f) phi) ≫
        (pullbackQuasicoherentSectionsIso f M).hom =
      (unitPullbackCoordinateIso f).hom ≫
        (ModuleCat.extendScalars f.hom).map
          ((unitModuleSpecΓIso R).hom ≫ moduleSpecΓFunctor.map phi) := by
  rw [affine_pullbackUnitMap_sections_naturality]
  dsimp only [unitPullbackCoordinateIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom]
  simp only [Category.assoc, Functor.map_comp]
  simp

/-- For a surjective structure-sheaf map on a spectrum, its coordinate kernel ideal
commutes with arbitrary scalar extension. -/
lemma linearKernelIdeal_affine_pullback {R S : CommRingCat.{u}}
    (f : R ⟶ S) (M : (Spec R).Modules) [M.IsQuasicoherent]
    (phi : SheafOfModules.unit (Spec R).ringCatSheaf ⟶ M) [Epi phi] :
    linearKernelIdeal
        (affineUnitLinearMap ((Modules.pullback (Spec.map f)).obj M)
          (pullbackUnitMap (Spec.map f) phi)) =
      (linearKernelIdeal (affineUnitLinearMap M phi)).map f.hom := by
  letI : Algebra R S := f.hom.toAlgebra
  let l := affineUnitLinearMap M phi
  let N := (Modules.pullback (Spec.map f)).obj M
  let psi := pullbackUnitMap (Spec.map f) phi
  let l' := affineUnitLinearMap N psi
  let t := pullbackQuasicoherentSectionsIso f M
  let c := unitPullbackCoordinateIso f
  let e := TensorProduct.AlgebraTensorModule.rid R S S
  let b := (l.baseChange S).comp e.symm.toLinearMap
  let u := unitPullbackScalarEquiv f
  let _ : (SheafOfModules.unit (Spec R).ringCatSheaf).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
      (tildeSelf (R := R)) inferInstance
  have hl : Function.Surjective l := by
    have h := Scheme.Modules.moduleSpecΓFunctor_map_surjective_of_epi phi
    exact h.comp (ConcreteCategory.bijective_of_isIso
      (unitModuleSpecΓIso R).hom).2
  have hn := affine_pullbackUnitMap_naturality f M phi
  have hnval (s : S) : t.hom.hom (l' s) = b (u s) := by
    have hs := congrArg (fun k : ModuleCat.of S S ⟶ _ ↦ k.hom s) hn
    have hs' : t.hom.hom (l' s) =
        ((ModuleCat.extendScalars f.hom).map
          ((unitModuleSpecΓIso R).hom ≫ moduleSpecΓFunctor.map phi)).hom
            (c.hom.hom s) := by
      simpa [l', t, N, psi, c, affineUnitLinearMap,
        CategoryTheory.comp_apply] using hs
    rw [hs']
    dsimp only [b, LinearMap.comp_apply]
    have hu : e.symm (u s) = c.hom.hom s := by
      change e.symm (e (c.hom.hom s)) = c.hom.hom s
      exact e.symm_apply_apply _
    change
      ((ModuleCat.extendScalars f.hom).map
        ((unitModuleSpecΓIso R).hom ≫ moduleSpecΓFunctor.map phi)).hom
          (c.hom.hom s) = l.baseChange S (e.symm (u s))
    rw [hu]
    change
      ((ModuleCat.extendScalars f.hom).map
        ((unitModuleSpecΓIso R).hom ≫ moduleSpecΓFunctor.map phi)).hom
          (c.hom.hom s) = l.baseChange S (c.hom.hom s)
    rfl
  have hker : LinearMap.ker l' = LinearMap.ker b := by
    calc
      LinearMap.ker l' =
          LinearMap.ker (b.comp (unitPullbackScalarEquiv f).toLinearMap) := by
        ext s
        simp only [LinearMap.mem_ker, LinearMap.comp_apply]
        constructor
        · intro hs
          change l' s = 0 at hs
          change b (u s) = 0
          rw [← hnval]
          rw [hs, map_zero]
        · intro hs
          change b (u s) = 0 at hs
          change l' s = 0
          apply (ConcreteCategory.bijective_of_isIso t.hom).1
          rw [hnval, hs, map_zero]
      _ = LinearMap.ker b := ker_comp_unitPullbackScalarEquiv f b
  have hb := linearKernelIdeal_baseChange_rid
    (R := R) (S := S) (N := moduleSpecΓFunctor.obj M) l hl
  ext s
  change l' s = 0 ↔ s ∈ (linearKernelIdeal l).map f.hom
  rw [← LinearMap.mem_ker, hker]
  exact SetLike.ext_iff.mp hb s

/-- For a flat coordinate-ring map, the coordinate kernel ideal of any
structure-sheaf morphism commutes with pullback. -/
lemma linearKernelIdeal_affine_pullback_of_flat {R S : CommRingCat.{u}}
    (f : R ⟶ S)
    (hflat : letI : Algebra R S := f.hom.toAlgebra; Module.Flat R S)
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    (phi : SheafOfModules.unit (Spec R).ringCatSheaf ⟶ M) :
    linearKernelIdeal
        (affineUnitLinearMap ((Modules.pullback (Spec.map f)).obj M)
          (pullbackUnitMap (Spec.map f) phi)) =
      (linearKernelIdeal (affineUnitLinearMap M phi)).map f.hom := by
  letI : Algebra R S := f.hom.toAlgebra
  letI : Module.Flat R S := hflat
  let l := affineUnitLinearMap M phi
  let N := (Modules.pullback (Spec.map f)).obj M
  let psi := pullbackUnitMap (Spec.map f) phi
  let l' := affineUnitLinearMap N psi
  let t := pullbackQuasicoherentSectionsIso f M
  let c := unitPullbackCoordinateIso f
  let e := TensorProduct.AlgebraTensorModule.rid R S S
  let b := (l.baseChange S).comp e.symm.toLinearMap
  let u := unitPullbackScalarEquiv f
  let _ : (SheafOfModules.unit (Spec R).ringCatSheaf).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
      (tildeSelf (R := R)) inferInstance
  have hn := affine_pullbackUnitMap_naturality f M phi
  have hnval (s : S) : t.hom.hom (l' s) = b (u s) := by
    have hs := congrArg (fun k : ModuleCat.of S S ⟶ _ ↦ k.hom s) hn
    have hs' : t.hom.hom (l' s) =
        ((ModuleCat.extendScalars f.hom).map
          ((unitModuleSpecΓIso R).hom ≫ moduleSpecΓFunctor.map phi)).hom
            (c.hom.hom s) := by
      simpa [l', t, N, psi, c, affineUnitLinearMap,
        CategoryTheory.comp_apply] using hs
    rw [hs']
    dsimp only [b, LinearMap.comp_apply]
    have hu : e.symm (u s) = c.hom.hom s := by
      change e.symm (e (c.hom.hom s)) = c.hom.hom s
      exact e.symm_apply_apply _
    change
      ((ModuleCat.extendScalars f.hom).map
        ((unitModuleSpecΓIso R).hom ≫ moduleSpecΓFunctor.map phi)).hom
          (c.hom.hom s) = l.baseChange S (e.symm (u s))
    rw [hu]
    rfl
  have hker : LinearMap.ker l' = LinearMap.ker b := by
    calc
      LinearMap.ker l' =
          LinearMap.ker (b.comp (unitPullbackScalarEquiv f).toLinearMap) := by
        ext s
        simp only [LinearMap.mem_ker, LinearMap.comp_apply]
        constructor
        · intro hs
          change l' s = 0 at hs
          change b (u s) = 0
          rw [← hnval, hs, map_zero]
        · intro hs
          change b (u s) = 0 at hs
          change l' s = 0
          apply (ConcreteCategory.bijective_of_isIso t.hom).1
          rw [hnval, hs, map_zero]
      _ = LinearMap.ker b := ker_comp_unitPullbackScalarEquiv f b
  have hb := linearKernelIdeal_baseChange_rid_of_flat
    (R := R) (S := S) (N := moduleSpecΓFunctor.obj M) l
  ext s
  change l' s = 0 ↔ s ∈ (linearKernelIdeal l).map f.hom
  rw [← LinearMap.mem_ker, hker]
  exact SetLike.ext_iff.mp hb s

/-- On spectra, kernel ideal-sheaf data of a surjective structure-sheaf map commute
with arbitrary base change. -/
lemma kernelIdealSheafData_pullback_specMap {R S : CommRingCat.{u}}
    (f : R ⟶ S) (M : (Spec R).Modules) [M.IsQuasicoherent]
    [((Modules.pullback (Spec.map f)).obj M).IsQuasicoherent]
    (phi : SheafOfModules.unit (Spec R).ringCatSheaf ⟶ M) [Epi phi] :
    kernelIdealSheafData ((Modules.pullback (Spec.map f)).obj M)
      (pullbackUnitMap (Spec.map f) phi) =
      (kernelIdealSheafData M phi).comap (Spec.map f) := by
  apply IdealSheafData.ext_of_isAffine
  rw [IdealSheafData.comap_ideal_top_of_isAffine]
  simp only [kernelIdealSheafData_ideal]
  rw [kernelIdeal_top_eq_map_affineUnitLinearMap,
    kernelIdeal_top_eq_map_affineUnitLinearMap,
    linearKernelIdeal_affine_pullback]
  change
    Ideal.map (Scheme.ΓSpecIso S).inv.hom
        (Ideal.map f.hom (linearKernelIdeal (affineUnitLinearMap M phi))) =
      Ideal.map (Spec.map f).appTop.hom
        (Ideal.map (Scheme.ΓSpecIso R).inv.hom
          (linearKernelIdeal (affineUnitLinearMap M phi)))
  rw [Ideal.map_map, Ideal.map_map, ← CommRingCat.hom_comp,
    ← CommRingCat.hom_comp, Scheme.ΓSpecIso_inv_naturality]

/-- On spectra, kernel ideal-sheaf data commute with flat base change. -/
lemma kernelIdealSheafData_pullback_specMap_of_flat {R S : CommRingCat.{u}}
    (f : R ⟶ S)
    (hflat : letI : Algebra R S := f.hom.toAlgebra; Module.Flat R S)
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    [((Modules.pullback (Spec.map f)).obj M).IsQuasicoherent]
    (phi : SheafOfModules.unit (Spec R).ringCatSheaf ⟶ M) :
    kernelIdealSheafData ((Modules.pullback (Spec.map f)).obj M)
      (pullbackUnitMap (Spec.map f) phi) =
      (kernelIdealSheafData M phi).comap (Spec.map f) := by
  apply IdealSheafData.ext_of_isAffine
  rw [IdealSheafData.comap_ideal_top_of_isAffine]
  simp only [kernelIdealSheafData_ideal]
  rw [kernelIdeal_top_eq_map_affineUnitLinearMap,
    kernelIdeal_top_eq_map_affineUnitLinearMap,
    linearKernelIdeal_affine_pullback_of_flat f hflat]
  change
    Ideal.map (Scheme.ΓSpecIso S).inv.hom
        (Ideal.map f.hom (linearKernelIdeal (affineUnitLinearMap M phi))) =
      Ideal.map (Spec.map f).appTop.hom
        (Ideal.map (Scheme.ΓSpecIso R).inv.hom
          (linearKernelIdeal (affineUnitLinearMap M phi)))
  rw [Ideal.map_map, Ideal.map_map, ← CommRingCat.hom_comp,
    ← CommRingCat.hom_comp, Scheme.ΓSpecIso_inv_naturality]

/-- Pullback of ideal-sheaf data along a scheme isomorphism is injective. -/
lemma IdealSheafData.comap_injective_of_isIso {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIso f] : Function.Injective (fun I : Y.IdealSheafData ↦ I.comap f) := by
  intro I J h
  have h' := congrArg (fun K : X.IdealSheafData ↦ K.comap (inv f)) h
  simpa only [← IdealSheafData.comap_comp, IsIso.inv_hom_id,
    IdealSheafData.comap_id] using h'

/-- Ideal-sheaf data are determined by their pullbacks to an affine open cover. -/
lemma IdealSheafData.eq_of_comap_eq_affineOpenCover
    {X : Scheme.{u}} (𝒰 : X.OpenCover) [∀ i, IsAffine (𝒰.X i)]
    (I J : X.IdealSheafData)
    (h : ∀ i, I.comap (𝒰.f i) = J.comap (𝒰.f i)) : I = J := by
  let U (i : 𝒰.I₀) : X.affineOpens :=
    ⟨𝒰.f i ''ᵁ (⊤ : (𝒰.X i).Opens),
      (isAffineOpen_top (𝒰.X i)).image_of_isOpenImmersion (𝒰.f i)⟩
  apply IdealSheafData.ext_of_iSup_eq_top U
  · change ⨆ i, 𝒰.f i ''ᵁ (⊤ : (𝒰.X i).Opens) = ⊤
    simpa only [Scheme.Hom.image_top_eq_opensRange] using 𝒰.iSup_opensRange
  · intro i
    have hi := congrArg
      (fun K : (𝒰.X i).IdealSheafData ↦
        K.ideal ⟨⊤, isAffineOpen_top (𝒰.X i)⟩) (h i)
    rw [IdealSheafData.ideal_comap_of_isOpenImmersion,
      IdealSheafData.ideal_comap_of_isOpenImmersion] at hi
    exact Ideal.comap_injective_of_surjective
      ((𝒰.f i).appIso ⊤).inv.hom
      (ConcreteCategory.bijective_of_isIso ((𝒰.f i).appIso ⊤).inv).2 hi

/-- Between affine schemes, kernel ideal-sheaf data of a surjective structure-sheaf
map commute with arbitrary pullback. -/
lemma kernelIdealSheafData_pullback_of_isAffine
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (M : Y.Modules) [M.IsQuasicoherent]
    [((Modules.pullback f).obj M).IsQuasicoherent]
    (phi : SheafOfModules.unit Y.ringCatSheaf ⟶ M) [Epi phi] :
    kernelIdealSheafData ((Modules.pullback f).obj M) (pullbackUnitMap f phi) =
      (kernelIdealSheafData M phi).comap f := by
  let jY := Y.isoSpec.inv
  let jX := X.isoSpec.inv
  let g := Spec.map f.appTop
  let MY := (Modules.pullback jY).obj M
  let phiY := pullbackUnitMap jY phi
  let A := (Modules.pullback g).obj MY
  let psiA := pullbackUnitMap g phiY
  let N := (Modules.pullback f).obj M
  let NX := (Modules.pullback jX).obj N
  let phiX := pullbackUnitMap jX (pullbackUnitMap f phi)
  let e := pullbackAffineIsoSpecIso f M
  letI : MY.IsQuasicoherent := by dsimp [MY]; infer_instance
  letI : A.IsQuasicoherent := by dsimp [A]; infer_instance
  letI : NX.IsQuasicoherent := by dsimp [NX]; infer_instance
  haveI : Epi ((Modules.pullback jY).map phi) := inferInstance
  haveI : Epi (inv (SheafOfModules.pullbackObjUnitToUnit
      jY.toRingCatSheafHom)) := inferInstance
  haveI : Epi phiY := by dsimp [phiY, pullbackUnitMap]; infer_instance
  have h1 := pullbackUnitMap_comp g jY phi
  have h2 := pullbackUnitMap_congr (Scheme.isoSpec_inv_naturality f) phi
  have h3 := pullbackUnitMap_comp jX f phi
  have he : psiA ≫ e.hom = phiX := by
    dsimp only [e, pullbackAffineIsoSpecIso, Iso.trans_hom, Iso.symm_hom]
    change (psiA ≫ (Modules.pullbackComp g jY).hom.app M) ≫
      ((Modules.pullbackCongr (Scheme.isoSpec_inv_naturality f)).hom.app M ≫
        (Modules.pullbackComp jX f).inv.app M) = phiX
    rw [h1, ← Category.assoc, h2]
    rw [← h3]
    change (phiX ≫ ((Modules.pullbackComp jX f).app M).hom) ≫
      ((Modules.pullbackComp jX f).app M).inv = phiX
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hIso : kernelIdealSheafData A psiA = kernelIdealSheafData NX phiX :=
    kernelIdealSheafData_eq_of_iso A NX psiA phiX e he
  have hSpec : kernelIdealSheafData A psiA =
      (kernelIdealSheafData MY phiY).comap g :=
    kernelIdealSheafData_pullback_specMap f.appTop MY phiY
  have hY : kernelIdealSheafData MY phiY =
      (kernelIdealSheafData M phi).comap jY :=
    kernelIdealSheafData_pullback_of_isIso_of_isAffine jY M phi
  have hX : kernelIdealSheafData NX phiX =
      (kernelIdealSheafData N (pullbackUnitMap f phi)).comap jX :=
    kernelIdealSheafData_pullback_of_isIso_of_isAffine jX N
      (pullbackUnitMap f phi)
  apply IdealSheafData.comap_injective_of_isIso jX
  calc
    (kernelIdealSheafData N (pullbackUnitMap f phi)).comap jX =
        kernelIdealSheafData NX phiX := hX.symm
    _ = kernelIdealSheafData A psiA := hIso.symm
    _ = (kernelIdealSheafData MY phiY).comap g := hSpec
    _ = ((kernelIdealSheafData M phi).comap jY).comap g := by rw [hY]
    _ = (kernelIdealSheafData M phi).comap (g ≫ jY) :=
      (IdealSheafData.comap_comp _ _ _).symm
    _ = (kernelIdealSheafData M phi).comap (jX ≫ f) := by
      rw [Scheme.isoSpec_inv_naturality]
    _ = ((kernelIdealSheafData M phi).comap f).comap jX :=
      IdealSheafData.comap_comp _ _ _

/-- Between affine schemes, kernel ideal-sheaf data commute with flat pullback. -/
lemma kernelIdealSheafData_pullback_of_isAffine_of_flat
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) [Flat f]
    (M : Y.Modules) [M.IsQuasicoherent]
    [((Modules.pullback f).obj M).IsQuasicoherent]
    (phi : SheafOfModules.unit Y.ringCatSheaf ⟶ M) :
    kernelIdealSheafData ((Modules.pullback f).obj M) (pullbackUnitMap f phi) =
      (kernelIdealSheafData M phi).comap f := by
  let jY := Y.isoSpec.inv
  let jX := X.isoSpec.inv
  let g := Spec.map f.appTop
  let MY := (Modules.pullback jY).obj M
  let phiY := pullbackUnitMap jY phi
  let A := (Modules.pullback g).obj MY
  let psiA := pullbackUnitMap g phiY
  let N := (Modules.pullback f).obj M
  let NX := (Modules.pullback jX).obj N
  let phiX := pullbackUnitMap jX (pullbackUnitMap f phi)
  let e := pullbackAffineIsoSpecIso f M
  letI : MY.IsQuasicoherent := by dsimp [MY]; infer_instance
  letI : A.IsQuasicoherent := by dsimp [A]; infer_instance
  letI : NX.IsQuasicoherent := by dsimp [NX]; infer_instance
  have h1 := pullbackUnitMap_comp g jY phi
  have h2 := pullbackUnitMap_congr (Scheme.isoSpec_inv_naturality f) phi
  have h3 := pullbackUnitMap_comp jX f phi
  have he : psiA ≫ e.hom = phiX := by
    dsimp only [e, pullbackAffineIsoSpecIso, Iso.trans_hom, Iso.symm_hom]
    change (psiA ≫ (Modules.pullbackComp g jY).hom.app M) ≫
      ((Modules.pullbackCongr (Scheme.isoSpec_inv_naturality f)).hom.app M ≫
        (Modules.pullbackComp jX f).inv.app M) = phiX
    rw [h1, ← Category.assoc, h2]
    rw [← h3]
    change (phiX ≫ ((Modules.pullbackComp jX f).app M).hom) ≫
      ((Modules.pullbackComp jX f).app M).inv = phiX
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hIso : kernelIdealSheafData A psiA = kernelIdealSheafData NX phiX :=
    kernelIdealSheafData_eq_of_iso A NX psiA phiX e he
  have hSpec : kernelIdealSheafData A psiA =
      (kernelIdealSheafData MY phiY).comap g :=
    kernelIdealSheafData_pullback_specMap_of_flat f.appTop f.flat_appTop MY phiY
  have hY : kernelIdealSheafData MY phiY =
      (kernelIdealSheafData M phi).comap jY :=
    kernelIdealSheafData_pullback_of_isIso_of_isAffine jY M phi
  have hX : kernelIdealSheafData NX phiX =
      (kernelIdealSheafData N (pullbackUnitMap f phi)).comap jX :=
    kernelIdealSheafData_pullback_of_isIso_of_isAffine jX N
      (pullbackUnitMap f phi)
  apply IdealSheafData.comap_injective_of_isIso jX
  calc
    (kernelIdealSheafData N (pullbackUnitMap f phi)).comap jX =
        kernelIdealSheafData NX phiX := hX.symm
    _ = kernelIdealSheafData A psiA := hIso.symm
    _ = (kernelIdealSheafData MY phiY).comap g := hSpec
    _ = ((kernelIdealSheafData M phi).comap jY).comap g := by rw [hY]
    _ = (kernelIdealSheafData M phi).comap (g ≫ jY) :=
      (IdealSheafData.comap_comp _ _ _).symm
    _ = (kernelIdealSheafData M phi).comap (jX ≫ f) := by
      rw [Scheme.isoSpec_inv_naturality]
    _ = ((kernelIdealSheafData M phi).comap f).comap jX :=
      IdealSheafData.comap_comp _ _ _

/-- Kernel ideal-sheaf data of an epimorphism from the structure sheaf to a
quasicoherent module commute with arbitrary pullback. -/
lemma kernelIdealSheafData_pullback_of_epi
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) [M.IsQuasicoherent]
    [((Modules.pullback f).obj M).IsQuasicoherent]
    (phi : SheafOfModules.unit Y.ringCatSheaf ⟶ M) [Epi phi] :
    kernelIdealSheafData ((Modules.pullback f).obj M) (pullbackUnitMap f phi) =
      (kernelIdealSheafData M phi).comap f := by
  let Ucover := Y.affineOpenCover.openCover
  let Pcover : X.OpenCover := Ucover.pullback₁ f
  let Acover : X.OpenCover := Pcover.affineRefinement.openCover
  apply IdealSheafData.eq_of_comap_eq_affineOpenCover Acover
  intro i
  let r := Pcover.fromAffineRefinement
  let j := r.s₀ i
  let c := r.h₀ i
  let a := Acover.f i
  let b := Ucover.f j
  let p := c ≫ Ucover.pullbackHom f j
  have hsquare : p ≫ b = a ≫ f := by
    calc
      p ≫ b = c ≫ (Ucover.pullbackHom f j ≫ b) := Category.assoc _ _ _
      _ = c ≫ (Pcover.f j ≫ f) := by rw [Ucover.pullbackHom_map]
      _ = (c ≫ Pcover.f j) ≫ f := (Category.assoc _ _ _).symm
      _ = a ≫ f := by rw [r.w₀]
  let MY := (Modules.pullback b).obj M
  let phiY := pullbackUnitMap b phi
  let MP := (Modules.pullback p).obj MY
  let phiP := pullbackUnitMap p phiY
  let N := (Modules.pullback f).obj M
  let phiN := pullbackUnitMap f phi
  let NA := (Modules.pullback a).obj N
  let phiA := pullbackUnitMap a phiN
  let e := pullbackCompCongrIso p b a f hsquare M
  let hMY : MY.IsQuasicoherent := by dsimp [MY]; infer_instance
  let hMP : MP.IsQuasicoherent := by dsimp [MP]; infer_instance
  let hNA : NA.IsQuasicoherent := by dsimp [NA]; infer_instance
  have hmapEpi : Epi ((Modules.pullback b).map phi) := inferInstance
  have hunitEpi : Epi (inv (SheafOfModules.pullbackObjUnitToUnit
      b.toRingCatSheafHom)) := inferInstance
  have hphiY : Epi phiY := by dsimp [phiY, pullbackUnitMap]; infer_instance
  have he : phiP ≫ e.hom = phiA :=
    pullbackUnitMap_comp_pullbackCompCongrIso p b a f hsquare phi
  have hIso : kernelIdealSheafData MP phiP = kernelIdealSheafData NA phiA :=
    kernelIdealSheafData_eq_of_iso MP NA phiP phiA e he
  have hp : kernelIdealSheafData MP phiP =
      (kernelIdealSheafData MY phiY).comap p :=
    kernelIdealSheafData_pullback_of_isAffine p MY phiY
  have ha : kernelIdealSheafData NA phiA =
      (kernelIdealSheafData N phiN).comap a :=
    kernelIdealSheafData_pullback_of_isOpenImmersion_of_isAffineSource a N phiN
  have hb : kernelIdealSheafData MY phiY =
      (kernelIdealSheafData M phi).comap b :=
    kernelIdealSheafData_pullback_of_isOpenImmersion_of_isAffineSource b M phi
  calc
    (kernelIdealSheafData N phiN).comap a =
        kernelIdealSheafData NA phiA := ha.symm
    _ = kernelIdealSheafData MP phiP := hIso.symm
    _ = (kernelIdealSheafData MY phiY).comap p := hp
    _ = ((kernelIdealSheafData M phi).comap b).comap p := by rw [hb]
    _ = (kernelIdealSheafData M phi).comap (p ≫ b) :=
      (IdealSheafData.comap_comp _ _ _).symm
    _ = (kernelIdealSheafData M phi).comap (a ≫ f) := by rw [hsquare]
    _ = ((kernelIdealSheafData M phi).comap f).comap a :=
      IdealSheafData.comap_comp _ _ _

/-- Kernel ideal-sheaf data of a morphism from the structure sheaf to a quasicoherent
module commute with pullback along an arbitrary flat morphism of schemes. -/
lemma kernelIdealSheafData_pullback_of_flat
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (M : Y.Modules) [M.IsQuasicoherent]
    [((Modules.pullback f).obj M).IsQuasicoherent]
    (phi : SheafOfModules.unit Y.ringCatSheaf ⟶ M) :
    kernelIdealSheafData ((Modules.pullback f).obj M) (pullbackUnitMap f phi) =
      (kernelIdealSheafData M phi).comap f := by
  let Ucover := Y.affineOpenCover.openCover
  let Pcover : X.OpenCover := Ucover.pullback₁ f
  let Acover : X.OpenCover := Pcover.affineRefinement.openCover
  apply IdealSheafData.eq_of_comap_eq_affineOpenCover Acover
  intro i
  let r := Pcover.fromAffineRefinement
  let j := r.s₀ i
  let c := r.h₀ i
  let a := Acover.f i
  let b := Ucover.f j
  let p := c ≫ Ucover.pullbackHom f j
  have hsquare : p ≫ b = a ≫ f := by
    calc
      p ≫ b = c ≫ (Ucover.pullbackHom f j ≫ b) := Category.assoc _ _ _
      _ = c ≫ (Pcover.f j ≫ f) := by rw [Ucover.pullbackHom_map]
      _ = (c ≫ Pcover.f j) ≫ f := (Category.assoc _ _ _).symm
      _ = a ≫ f := by rw [r.w₀]
  let MY := (Modules.pullback b).obj M
  let phiY := pullbackUnitMap b phi
  let MP := (Modules.pullback p).obj MY
  let phiP := pullbackUnitMap p phiY
  let N := (Modules.pullback f).obj M
  let phiN := pullbackUnitMap f phi
  let NA := (Modules.pullback a).obj N
  let phiA := pullbackUnitMap a phiN
  let e := pullbackCompCongrIso p b a f hsquare M
  letI : MY.IsQuasicoherent := by dsimp [MY]; infer_instance
  letI : MP.IsQuasicoherent := by dsimp [MP]; infer_instance
  letI : NA.IsQuasicoherent := by dsimp [NA]; infer_instance
  letI : IsOpenImmersion c := by dsimp [c, r]; infer_instance
  letI : Flat c := inferInstance
  letI : Flat (Ucover.pullbackHom f j) := by
    dsimp only [Scheme.Cover.pullbackHom]
    infer_instance
  letI : Flat p := by dsimp only [p]; infer_instance
  have he : phiP ≫ e.hom = phiA :=
    pullbackUnitMap_comp_pullbackCompCongrIso p b a f hsquare phi
  have hIso : kernelIdealSheafData MP phiP = kernelIdealSheafData NA phiA :=
    kernelIdealSheafData_eq_of_iso MP NA phiP phiA e he
  have hp : kernelIdealSheafData MP phiP =
      (kernelIdealSheafData MY phiY).comap p :=
    kernelIdealSheafData_pullback_of_isAffine_of_flat p MY phiY
  have ha : kernelIdealSheafData NA phiA =
      (kernelIdealSheafData N phiN).comap a :=
    kernelIdealSheafData_pullback_of_isOpenImmersion_of_isAffineSource a N phiN
  have hb : kernelIdealSheafData MY phiY =
      (kernelIdealSheafData M phi).comap b :=
    kernelIdealSheafData_pullback_of_isOpenImmersion_of_isAffineSource b M phi
  calc
    (kernelIdealSheafData N phiN).comap a =
        kernelIdealSheafData NA phiA := ha.symm
    _ = kernelIdealSheafData MP phiP := hIso.symm
    _ = (kernelIdealSheafData MY phiY).comap p := hp
    _ = ((kernelIdealSheafData M phi).comap b).comap p := by rw [hb]
    _ = (kernelIdealSheafData M phi).comap (p ≫ b) :=
      (IdealSheafData.comap_comp _ _ _).symm
    _ = (kernelIdealSheafData M phi).comap (a ≫ f) := by rw [hsquare]
    _ = ((kernelIdealSheafData M phi).comap f).comap a :=
      IdealSheafData.comap_comp _ _ _

end Modules.Hom

end AlgebraicGeometry.Scheme
