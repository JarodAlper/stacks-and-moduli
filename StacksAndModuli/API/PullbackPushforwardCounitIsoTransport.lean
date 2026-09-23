module

public import StacksAndModuli.API.SchemeModulesGlobalSectionsIso
public import StacksAndModuli.API.PullbackAdjoint


/-!
# Transporting evaluation epimorphisms across scheme isomorphisms

The pullback--pushforward counit for a morphism remains epimorphic after transporting
the source scheme and the module sheaf through an isomorphism.  The proof compares the
adjunction of the composite with the composite adjunction by conjugating their left
adjoints, then uses that pullback along an isomorphism reflects epimorphisms.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Adjunction

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}

theorem epi_counit_of_leftAdjointIso
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (e : L₂ ≅ L₁) (X : D)
    [Epi (adj₂.counit.app X)] : Epi (adj₁.counit.app X) := by
  let eR : R₁ ≅ R₂ := (conjugateIsoEquiv adj₁ adj₂) e
  have h := conjugateEquiv_counit adj₁ adj₂ e.hom X
  change L₂.map (eR.hom.app _) ≫ adj₂.counit.app X =
    e.hom.app _ ≫ adj₁.counit.app X at h
  haveI : Epi (L₂.map (eR.hom.app _) ≫ adj₂.counit.app X) := epi_comp _ _
  haveI : Epi (e.hom.app _ ≫ adj₁.counit.app X) := h ▸ inferInstance
  exact (epi_comp_iff_of_epi (e.hom.app _) (adj₁.counit.app X)).mp inferInstance

/-- Epimorphicity of an adjunction counit is invariant under isomorphism of the object at
which the counit is evaluated. -/
theorem epi_counit_of_iso
    (adj : L₁ ⊣ R₁) {X Y : D} (e : X ≅ Y)
    [Epi (adj.counit.app Y)] : Epi (adj.counit.app X) := by
  have h := adj.counit.naturality e.hom
  haveI : Epi ((R₁ ⋙ L₁).map e.hom ≫ adj.counit.app Y) := epi_comp _ _
  haveI : Epi (adj.counit.app X ≫ e.hom) := h ▸ inferInstance
  exact (epi_comp_iff_of_isIso (adj.counit.app X) e.hom).mp inferInstance

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Scheme.Modules

universe u

theorem epi_pullbackPushforwardCounit_of_comp_of_isIso
    {X Y Z : Scheme.{u}} (i : X ⟶ Y) [IsIso i] (p : Y ⟶ Z) (M : Y.Modules)
    [Epi ((pullbackPushforwardAdjunction (i ≫ p)).counit.app
      ((pullback i).obj M))] :
    Epi ((pullbackPushforwardAdjunction p).counit.app M) := by
  let adjP := pullbackPushforwardAdjunction p
  let adjI := pullbackPushforwardAdjunction i
  let adjC := adjP.comp adjI
  let adjPI := pullbackPushforwardAdjunction (i ≫ p)
  let M' := (pullback i).obj M
  haveI hcomp : Epi (adjC.counit.app M') :=
    CategoryTheory.Adjunction.epi_counit_of_leftAdjointIso adjC adjPI
      (pullbackComp i p).symm M'
  haveI : IsIso adjI.counit :=
    Adjunction.counit_isIso_of_R_fully_faithful adjI
  haveI hmappedComp : Epi
      ((pullback i).map (adjP.counit.app ((pushforward i).obj M')) ≫
        adjI.counit.app M') := by
    simpa only [adjC, adjP, adjI, M', Adjunction.comp_counit_app] using hcomp
  haveI hmapped : Epi
      ((pullback i).map (adjP.counit.app ((pushforward i).obj M'))) :=
    (epi_comp_iff_of_isIso _ (adjI.counit.app M')).mp inferInstance
  haveI hsource : Epi (adjP.counit.app ((pushforward i).obj M')) :=
    (pullback i).epi_of_epi_map inferInstance
  haveI : IsIso adjI.unit :=
    Adjunction.unit_isIso_of_L_fully_faithful adjI
  let b : (pushforward i).obj M' ≅ M := (asIso (adjI.unit.app M)).symm
  have hnat := adjP.counit.naturality b.hom
  haveI hrhs : Epi (adjP.counit.app ((pushforward i).obj M') ≫ b.hom) := epi_comp _ _
  haveI hlhs : Epi
      ((pushforward p ⋙ pullback p).map b.hom ≫ adjP.counit.app M) := hnat.symm ▸ hrhs
  exact (epi_comp_iff_of_epi ((pushforward p ⋙ pullback p).map b.hom)
    (adjP.counit.app M)).mp inferInstance

end AlgebraicGeometry.Scheme.Modules

end
