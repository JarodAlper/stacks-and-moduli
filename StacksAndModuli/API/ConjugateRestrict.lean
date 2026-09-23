module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Conjugation commutes with restriction of adjunctions

For adjunctions restricted along fully faithful inclusions
(`Adjunction.restrictFullyFaithful`), the conjugate of a restricted 2-cell is the
restriction of the conjugate.  This supplies the mate compatibility missing from
Mathlib's `Adjunction.Restrict`, needed to restrict Beck–Chevalley-type mate
identities (such as `conjugateEquiv_pullbackComp_inv` for sheaves of modules) to a
full subcategory such as the quasi-coherent modules.

Main declarations:

* `conjugateEquiv_restrictFullyFaithful_app`: the conjugate of a restricted 2-cell
  is the restriction of the conjugate;
* `restrictFullyFaithful_comp`: restriction commutes with composition of
  adjunctions;
* `conjugateEquiv_restrictFullyFaithful_comp_app`: the two combined — a mate
  identity for a *composite* of restricted adjunctions, the shape arising from a
  pseudofunctor compositor, reduced to the corresponding identity upstairs.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory.Adjunction

open Category

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {C' : Type u₃} [Category.{v₃} C']
variable {D' : Type u₄} [Category.{v₄} D']
variable {iC : C ⥤ C'} {iD : D ⥤ D'}
  {L₁' L₂' : C' ⥤ D'} {R₁' R₂' : D' ⥤ C'}
  (adj₁' : L₁' ⊣ R₁') (adj₂' : L₂' ⊣ R₂')
  (hiC : iC.FullyFaithful) (hiD : iD.FullyFaithful)
  {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
  (comm1₁ : iC ⋙ L₁' ≅ L₁ ⋙ iD) (comm2₁ : iD ⋙ R₁' ≅ R₁ ⋙ iC)
  (comm1₂ : iC ⋙ L₂' ≅ L₂ ⋙ iD) (comm2₂ : iD ⋙ R₂' ≅ R₂ ⋙ iC)

/-- The conjugate of a restricted 2-cell along restricted adjunctions is the
restriction of the conjugate of the original 2-cell. -/
theorem conjugateEquiv_restrictFullyFaithful_app
    (α : L₂ ⟶ L₁) (α' : L₂' ⟶ L₁')
    (hα : ∀ X : C, α'.app (iC.obj X) =
      comm1₂.hom.app X ≫ iD.map (α.app X) ≫ comm1₁.inv.app X)
    (d : D) :
    (conjugateEquiv adj₁' adj₂' α').app (iD.obj d) =
      comm2₁.hom.app d ≫
        iC.map ((conjugateEquiv
          (adj₁'.restrictFullyFaithful hiC hiD comm1₁ comm2₁)
          (adj₂'.restrictFullyFaithful hiC hiD comm1₂ comm2₂) α).app d) ≫
        comm2₂.inv.app d := by
  set adj₁ := adj₁'.restrictFullyFaithful hiC hiD comm1₁ comm2₁ with hadj₁
  set adj₂ := adj₂'.restrictFullyFaithful hiC hiD comm1₂ comm2₂ with hadj₂
  set γ := conjugateEquiv adj₁ adj₂ α with hγ
  apply (adj₂'.homEquiv _ _).symm.injective
  rw [homEquiv_counit, homEquiv_counit]
  rw [conjugateEquiv_counit]
  -- the two restricted counit descriptions, solved for the composite with `counit'`
  have hcounit₂ : L₂'.map (comm2₂.inv.app d) ≫ adj₂'.counit.app (iD.obj d) =
      comm1₂.hom.app (R₂.obj d) ≫ iD.map (adj₂.counit.app d) := by
    rw [← cancel_epi (comm1₂.inv.app (R₂.obj d))]
    rw [Iso.inv_hom_id_app_assoc]
    exact (adj₂'.map_restrictFullyFaithful_counit_app hiC hiD comm1₂ comm2₂ d).symm
  have hcounit₁ : comm1₁.hom.app (R₁.obj d) ≫ iD.map (adj₁.counit.app d) =
      L₁'.map (comm2₁.inv.app d) ≫ adj₁'.counit.app (iD.obj d) := by
    rw [← cancel_epi (comm1₁.inv.app (R₁.obj d))]
    rw [Iso.inv_hom_id_app_assoc]
    exact adj₁'.map_restrictFullyFaithful_counit_app hiC hiD comm1₁ comm2₁ d
  have hsmall : L₂.map (γ.app d) ≫ adj₂.counit.app d =
      α.app (R₁.obj d) ≫ adj₁.counit.app d :=
    conjugateEquiv_counit adj₁ adj₂ α d
  symm
  calc
    L₂'.map (comm2₁.hom.app d ≫ iC.map (γ.app d) ≫ comm2₂.inv.app d) ≫
        adj₂'.counit.app (iD.obj d)
      = L₂'.map (comm2₁.hom.app d) ≫ L₂'.map (iC.map (γ.app d)) ≫
          (L₂'.map (comm2₂.inv.app d) ≫ adj₂'.counit.app (iD.obj d)) := by
        simp [Functor.map_comp]
    _ = L₂'.map (comm2₁.hom.app d) ≫ L₂'.map (iC.map (γ.app d)) ≫
          comm1₂.hom.app (R₂.obj d) ≫ iD.map (adj₂.counit.app d) := by
        rw [hcounit₂]
    _ = L₂'.map (comm2₁.hom.app d) ≫ comm1₂.hom.app (R₁.obj d) ≫
          iD.map (L₂.map (γ.app d)) ≫ iD.map (adj₂.counit.app d) := by
        have hn : L₂'.map (iC.map (γ.app d)) ≫ comm1₂.hom.app (R₂.obj d) =
            comm1₂.hom.app (R₁.obj d) ≫ iD.map (L₂.map (γ.app d)) :=
          comm1₂.hom.naturality (γ.app d)
        rw [reassoc_of% hn]
    _ = L₂'.map (comm2₁.hom.app d) ≫ comm1₂.hom.app (R₁.obj d) ≫
          iD.map (α.app (R₁.obj d)) ≫ iD.map (adj₁.counit.app d) := by
        rw [← Functor.map_comp, hsmall, Functor.map_comp]
    _ = L₂'.map (comm2₁.hom.app d) ≫ α'.app (iC.obj (R₁.obj d)) ≫
          comm1₁.hom.app (R₁.obj d) ≫ iD.map (adj₁.counit.app d) := by
        rw [hα (R₁.obj d)]
        simp
    _ = α'.app (R₁'.obj (iD.obj d)) ≫ L₁'.map (comm2₁.hom.app d) ≫
          comm1₁.hom.app (R₁.obj d) ≫ iD.map (adj₁.counit.app d) := by
        have hn : L₂'.map (comm2₁.hom.app d) ≫ α'.app (iC.obj (R₁.obj d)) =
            α'.app (R₁'.obj (iD.obj d)) ≫ L₁'.map (comm2₁.hom.app d) :=
          α'.naturality (comm2₁.hom.app d)
        rw [reassoc_of% hn]
    _ = α'.app (R₁'.obj (iD.obj d)) ≫ L₁'.map (comm2₁.hom.app d) ≫
          L₁'.map (comm2₁.inv.app d) ≫ adj₁'.counit.app (iD.obj d) := by
        rw [hcounit₁]
    _ = α'.app (R₁'.obj (iD.obj d)) ≫ adj₁'.counit.app (iD.obj d) := by
        rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
        simp

section Comp

variable {E : Type*} [Category E] {E' : Type*} [Category E']
variable {iE : E ⥤ E'}

/-- Restriction of adjunctions along fully faithful inclusions commutes with
composition of adjunctions.  The commutation data for the composite are assembled
from those of the factors. -/
theorem restrictFullyFaithful_comp
    {L₁' : C' ⥤ D'} {R₁' : D' ⥤ C'} (adj₁' : L₁' ⊣ R₁')
    {L₂' : D' ⥤ E'} {R₂' : E' ⥤ D'} (adj₂' : L₂' ⊣ R₂')
    (hiC : iC.FullyFaithful) (hiD : iD.FullyFaithful) (hiE : iE.FullyFaithful)
    {L₁ : C ⥤ D} {R₁ : D ⥤ C}
    (comm1₁ : iC ⋙ L₁' ≅ L₁ ⋙ iD) (comm2₁ : iD ⋙ R₁' ≅ R₁ ⋙ iC)
    {L₂ : D ⥤ E} {R₂ : E ⥤ D}
    (comm1₂ : iD ⋙ L₂' ≅ L₂ ⋙ iE) (comm2₂ : iE ⋙ R₂' ≅ R₂ ⋙ iD) :
    (adj₁'.restrictFullyFaithful hiC hiD comm1₁ comm2₁).comp
        (adj₂'.restrictFullyFaithful hiD hiE comm1₂ comm2₂) =
      (adj₁'.comp adj₂').restrictFullyFaithful hiC hiE
        ((Functor.associator iC L₁' L₂').symm ≪≫
          Functor.isoWhiskerRight comm1₁ L₂' ≪≫ Functor.associator L₁ iD L₂' ≪≫
          Functor.isoWhiskerLeft L₁ comm1₂ ≪≫ (Functor.associator L₁ L₂ iE).symm)
        ((Functor.associator iE R₂' R₁').symm ≪≫
          Functor.isoWhiskerRight comm2₂ R₁' ≪≫ Functor.associator R₂ iD R₁' ≪≫
          Functor.isoWhiskerLeft R₂ comm2₁ ≪≫ (Functor.associator R₂ R₁ iC).symm) := by
  apply Adjunction.ext
  ext X
  apply hiC.map_injective
  simp only [Adjunction.comp_unit_app, map_restrictFullyFaithful_unit_app,
    Iso.trans_hom, Iso.symm_hom, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.comp_obj, Functor.map_comp,
    Category.assoc, Category.id_comp, Category.comp_id]
  have hnat := (comm2₁.hom.naturality
    ((adj₂'.restrictFullyFaithful hiD hiE comm1₂ comm2₂).unit.app (L₁.obj X))).symm
  simp only [Functor.comp_map, Functor.id_obj, Functor.comp_obj] at hnat
  have h2 := adj₂'.unit.naturality (comm1₁.hom.app X)
  simp only [Functor.id_map, Functor.comp_map, Functor.comp_obj] at h2
  rw [hnat, map_restrictFullyFaithful_unit_app]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, h2, Functor.map_comp, Category.assoc]
  simp only [Functor.comp_map]

/-- Mate identity for a *composite* of restricted adjunctions: the conjugate
downstairs is determined by the conjugate upstairs.  This is the form needed when
the composite arises as the compositor of a pseudofunctor, and it is what makes the
Beck–Chevalley identities of Mathlib available after restriction to a full
subcategory. -/
theorem conjugateEquiv_restrictFullyFaithful_comp_app
    {L₁' : C' ⥤ D'} {R₁' : D' ⥤ C'} (adj₁' : L₁' ⊣ R₁')
    {L₂' : D' ⥤ E'} {R₂' : E' ⥤ D'} (adj₂' : L₂' ⊣ R₂')
    {L₃' : C' ⥤ E'} {R₃' : E' ⥤ C'} (adj₃' : L₃' ⊣ R₃')
    (hiC : iC.FullyFaithful) (hiD : iD.FullyFaithful) (hiE : iE.FullyFaithful)
    {L₁ : C ⥤ D} {R₁ : D ⥤ C}
    (comm1₁ : iC ⋙ L₁' ≅ L₁ ⋙ iD) (comm2₁ : iD ⋙ R₁' ≅ R₁ ⋙ iC)
    {L₂ : D ⥤ E} {R₂ : E ⥤ D}
    (comm1₂ : iD ⋙ L₂' ≅ L₂ ⋙ iE) (comm2₂ : iE ⋙ R₂' ≅ R₂ ⋙ iD)
    {L₃ : C ⥤ E} {R₃ : E ⥤ C}
    (comm1₃ : iC ⋙ L₃' ≅ L₃ ⋙ iE) (comm2₃ : iE ⋙ R₃' ≅ R₃ ⋙ iC)
    (α : L₃ ⟶ L₁ ⋙ L₂) (α' : L₃' ⟶ L₁' ⋙ L₂')
    (hα : ∀ X : C, α'.app (iC.obj X) =
      comm1₃.hom.app X ≫ iE.map (α.app X) ≫
        ((Functor.associator iC L₁' L₂').symm ≪≫
          Functor.isoWhiskerRight comm1₁ L₂' ≪≫ Functor.associator L₁ iD L₂' ≪≫
          Functor.isoWhiskerLeft L₁ comm1₂ ≪≫
          (Functor.associator L₁ L₂ iE).symm).inv.app X)
    (d : E) :
    (conjugateEquiv (adj₁'.comp adj₂') adj₃' α').app (iE.obj d) =
      ((Functor.associator iE R₂' R₁').symm ≪≫
        Functor.isoWhiskerRight comm2₂ R₁' ≪≫ Functor.associator R₂ iD R₁' ≪≫
        Functor.isoWhiskerLeft R₂ comm2₁ ≪≫
        (Functor.associator R₂ R₁ iC).symm).hom.app d ≫
        iC.map ((conjugateEquiv
          ((adj₁'.restrictFullyFaithful hiC hiD comm1₁ comm2₁).comp
            (adj₂'.restrictFullyFaithful hiD hiE comm1₂ comm2₂))
          (adj₃'.restrictFullyFaithful hiC hiE comm1₃ comm2₃) α).app d) ≫
        comm2₃.inv.app d := by
  rw [restrictFullyFaithful_comp]
  exact conjugateEquiv_restrictFullyFaithful_app _ _ _ _ _ _ _ _ α α' hα d

end Comp

end CategoryTheory.Adjunction
