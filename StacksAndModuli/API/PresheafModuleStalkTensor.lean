module

public import StacksAndModuli.API.PresheafModuleColimitTensor
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward

/-!
# Stalks and tensor products of presheaves of modules

This file specializes the filtered-colimit tensor comparison to the diagram of open
neighborhoods of a point.  In particular, it records the naturality needed to show
that a stalkwise isomorphism remains a stalkwise isomorphism after tensoring.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  TopologicalSpace Opposite

universe u

namespace PresheafOfModules

variable {X : TopCat.{u}} (R : X.Presheaf CommRingCat.{u}) (x : X)

/-- The restriction of the coefficient-ring presheaf to the cofiltered category of
open neighborhoods of a point. -/
abbrev openNhdsRing : Functor (OpenNhds x)ᵒᵖ CommRingCat.{u} :=
  (OpenNhds.inclusion x).op ⋙ R

/-- Restriction of a presheaf of modules to the open neighborhoods of a point. -/
noncomputable abbrev openNhdsRestriction
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.{u} (openNhdsRing R x ⋙ forget₂ CommRingCat RingCat) :=
  (pushforward₀OfCommRingCat (OpenNhds.inclusion x) R).obj M

/-- Restriction of a morphism of module presheaves to the open neighborhoods of a
point. -/
noncomputable abbrev openNhdsRestrictionMap
    {M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)} (f : M ⟶ N) :
    openNhdsRestriction R x M ⟶ openNhdsRestriction R x N :=
  (pushforward₀OfCommRingCat (OpenNhds.inclusion x) R).map f

@[simp]
lemma openNhdsRestrictionMap_app
    {M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)} (f : M ⟶ N)
    (U : (OpenNhds x)ᵒᵖ) :
    (openNhdsRestrictionMap R x f).app U =
      f.app ((OpenNhds.inclusion x).op.obj U) := rfl

/-- Restriction to open neighborhoods commutes with the pointwise tensor product. -/
noncomputable def openNhdsRestrictionTensorIso
    (M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) :
    openNhdsRestriction R x (M ⊗ N) ≅
      openNhdsRestriction R x M ⊗ openNhdsRestriction R x N :=
  isoMk (fun _ ↦ Iso.refl _)
    (fun U _ _ ↦ by
      simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      apply ModuleCat.MonoidalCategory.tensor_ext
        (R := (openNhdsRing R x).obj U)
      intro m n
      rfl)

@[reassoc]
lemma openNhdsRestrictionTensorIso_hom_naturality
    {M M' N N' : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
    (f : M ⟶ M') (g : N ⟶ N') :
    openNhdsRestrictionMap R x (f ⊗ₘ g) ≫
        (openNhdsRestrictionTensorIso R x M' N').hom =
      (openNhdsRestrictionTensorIso R x M N).hom ≫
        (openNhdsRestrictionMap R x f ⊗ₘ openNhdsRestrictionMap R x g) := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
    (R := (openNhdsRing R x).obj U)
  intro m n
  rfl

namespace StalkTensor

noncomputable local instance : InitiallySmall.{u} (OpenNhds x) :=
  initiallySmall_of_essentiallySmall _

local notation "Rₓ" => openNhdsRing R x
local notation "cRₓ" => colimit.cocone Rₓ
local notation "hcRₓ" => colimit.isColimit Rₓ

@[instance_reducible]
noncomputable local instance moduleColimitOverCommRing
    {P : PresheafOfModules.{u} (Rₓ ⋙ forget₂ CommRingCat RingCat)} :
    Module (cRₓ).pt
      (ModuleColimit (isColimitOfPreserves (forget₂ CommRingCat RingCat) hcRₓ)
        (colimit.isColimit P.presheaf)) :=
  inferInstanceAs
    (Module ((forget₂ CommRingCat RingCat).mapCocone cRₓ).pt
      (ModuleColimit (isColimitOfPreserves (forget₂ CommRingCat RingCat) hcRₓ)
        (colimit.isColimit P.presheaf)))

/-- The colimit module attached to the restriction of a module presheaf to the open
neighborhoods of `x`. -/
noncomputable abbrev colimitModule
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) :
    ModuleCat.{u} (cRₓ).pt :=
  (colimitFunctor (isColimitOfPreserves (forget₂ CommRingCat RingCat) hcRₓ)).obj
    (openNhdsRestriction R x M)

/-- The map of colimit modules induced by a morphism of presheaves.  Its
underlying additive map is the usual map on stalk colimits. -/
noncomputable abbrev colimitMap
    {M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)} (f : M ⟶ N) :
    colimitModule R (x := x) M ⟶ colimitModule R (x := x) N :=
  (colimitFunctor (isColimitOfPreserves (forget₂ CommRingCat RingCat) hcRₓ)).map
    (openNhdsRestrictionMap R x f)

/-- After forgetting the module structure, `colimitMap` is the ordinary map on
stalk colimits. -/
lemma forget_colimitMap
    {M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)} (f : M ⟶ N) :
    (forget₂ (ModuleCat (cRₓ).pt) AddCommGrpCat).map (colimitMap R x f) =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        ((toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map f) := by
  rfl

/-- A morphism inducing an isomorphism on the ordinary stalk colimit also induces
an isomorphism on the corresponding colimit module. -/
lemma colimitMap_isIso
    {M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)} (f : M ⟶ N)
    [IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      ((toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map f))] :
    IsIso (colimitMap R x f) := by
  letI : IsIso ((forget₂ (ModuleCat (cRₓ).pt) AddCommGrpCat).map
      (colimitMap R x f)) := by
    rw [forget_colimitMap]
    infer_instance
  exact isIso_of_reflects_iso (colimitMap R x f)
    (forget₂ (ModuleCat (cRₓ).pt) AddCommGrpCat)

/-- The canonical comparison between the colimit of pointwise tensor products over
the open neighborhoods of `x` and the tensor product of the two colimit modules. -/
noncomputable def comparisonIso
    (M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) :
    colimitModule R (x := x) (M ⊗ N) ≅
      colimitModule R (x := x) M ⊗ colimitModule R (x := x) N :=
  (colimitFunctor (isColimitOfPreserves (forget₂ CommRingCat RingCat) hcRₓ)).mapIso
      (openNhdsRestrictionTensorIso R x M N) ≪≫
    ModuleColimit.tensorComparisonIso hcRₓ
      (colimit.isColimit (openNhdsRestriction R x M).presheaf)
      (colimit.isColimit (openNhdsRestriction R x N).presheaf)
      (colimit.isColimit
        (openNhdsRestriction R x M ⊗ openNhdsRestriction R x N).presheaf)

@[simp]
lemma comparisonIso_hom_ι_tmul
    (M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    {U : (OpenNhds x)ᵒᵖ} (m : M.obj ((OpenNhds.inclusion x).op.obj U))
    (n : N.obj ((OpenNhds.inclusion x).op.obj U)) :
    (comparisonIso R x M N).hom
        (ModuleColimit.ιM
          (hcR := isColimitOfPreserves (forget₂ CommRingCat RingCat) hcRₓ)
          (hcM := colimit.isColimit (openNhdsRestriction R x (M ⊗ N)).presheaf)
          (m ⊗ₜ[((openNhdsRing R x).obj U)] n)) =
      (show colimitModule R (x := x) M from
        ModuleColimit.ιM
          (hcR := isColimitOfPreserves (forget₂ CommRingCat RingCat) hcRₓ)
          (hcM := colimit.isColimit (openNhdsRestriction R x M).presheaf) m) ⊗ₜ
        (show colimitModule R (x := x) N from
          ModuleColimit.ιM
            (hcR := isColimitOfPreserves (forget₂ CommRingCat RingCat) hcRₓ)
            (hcM := colimit.isColimit (openNhdsRestriction R x N).presheaf) n) := by
  change
    ModuleColimit.tensorComparison hcRₓ
        (colimit.isColimit (openNhdsRestriction R x M).presheaf)
        (colimit.isColimit (openNhdsRestriction R x N).presheaf)
        (colimit.isColimit
          (openNhdsRestriction R x M ⊗ openNhdsRestriction R x N).presheaf)
      (ModuleColimit.map
        (isColimitOfPreserves (forget₂ CommRingCat RingCat) hcRₓ)
        (colimit.isColimit (openNhdsRestriction R x (M ⊗ N)).presheaf)
        (colimit.isColimit
          (openNhdsRestriction R x M ⊗ openNhdsRestriction R x N).presheaf)
        (openNhdsRestrictionTensorIso R x M N).hom
        (ModuleColimit.ιM
          (hcR := isColimitOfPreserves (forget₂ CommRingCat RingCat) hcRₓ)
          (hcM := colimit.isColimit (openNhdsRestriction R x (M ⊗ N)).presheaf)
          (m ⊗ₜ[((openNhdsRing R x).obj U)] n))) = _
  rw [ModuleColimit.map_apply, ModuleColimit.tensorComparison_ιM]
  rfl

@[reassoc]
lemma comparisonIso_hom_naturality
    {M M' N N' : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
    (f : M ⟶ M') (g : N ⟶ N') :
    (comparisonIso R x M N).hom ≫ (colimitMap R x f ⊗ₘ colimitMap R x g) =
      colimitMap R x (f ⊗ₘ g) ≫ (comparisonIso R x M' N').hom := by
  ext z
  obtain ⟨U, t, rfl⟩ := ModuleColimit.ιM_jointly_surjective
    (hcR := isColimitOfPreserves (forget₂ CommRingCat RingCat) hcRₓ)
    (hcM := colimit.isColimit (openNhdsRestriction R x (M ⊗ N)).presheaf) z
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul m n =>
      change
        (colimitMap R x f ⊗ₘ colimitMap R x g)
            ((comparisonIso R x M N).hom
              (ModuleColimit.ιM
                (hcR := isColimitOfPreserves (forget₂ CommRingCat RingCat) hcRₓ)
                (hcM := colimit.isColimit (openNhdsRestriction R x (M ⊗ N)).presheaf)
                (m ⊗ₜ[((openNhdsRing R x).obj U)] n))) =
          (comparisonIso R x M' N').hom
            (colimitMap R x (f ⊗ₘ g)
              (ModuleColimit.ιM
                (hcR := isColimitOfPreserves (forget₂ CommRingCat RingCat) hcRₓ)
                (hcM := colimit.isColimit (openNhdsRestriction R x (M ⊗ N)).presheaf)
                (m ⊗ₜ[((openNhdsRing R x).obj U)] n)))
      rw [comparisonIso_hom_ι_tmul]
      dsimp only [colimitMap]
      change
        ModuleColimit.map _ _ _ (openNhdsRestrictionMap R x f)
              (ModuleColimit.ιM m) ⊗ₜ
            ModuleColimit.map _ _ _ (openNhdsRestrictionMap R x g)
              (ModuleColimit.ιM n) = _
      rw [ModuleColimit.map_apply]
      change _ =
        (comparisonIso R x M' N').hom
          (ModuleColimit.map
            (isColimitOfPreserves (forget₂ CommRingCat RingCat) hcRₓ)
            (colimit.isColimit (openNhdsRestriction R x (M ⊗ N)).presheaf)
            (colimit.isColimit (openNhdsRestriction R x (M' ⊗ N')).presheaf)
            (openNhdsRestrictionMap R x (f ⊗ₘ g))
            (ModuleColimit.ιM
              (hcR := isColimitOfPreserves (forget₂ CommRingCat RingCat) hcRₓ)
              (hcM := colimit.isColimit (openNhdsRestriction R x (M ⊗ N)).presheaf)
              (m ⊗ₜ[((openNhdsRing R x).obj U)] n)) )
      have hmap := ModuleColimit.map_apply
        (isColimitOfPreserves (forget₂ CommRingCat RingCat) hcRₓ)
        (colimit.isColimit (openNhdsRestriction R x (M ⊗ N)).presheaf)
        (colimit.isColimit (openNhdsRestriction R x (M' ⊗ N')).presheaf)
        (openNhdsRestrictionMap R x (f ⊗ₘ g))
        (m ⊗ₜ[((openNhdsRing R x).obj U)] n)
      rw [hmap]
      change _ =
        (comparisonIso R x M' N').hom
          (ModuleColimit.ιM
            (hcR := isColimitOfPreserves (forget₂ CommRingCat RingCat) hcRₓ)
            (hcM := colimit.isColimit (openNhdsRestriction R x (M' ⊗ N')).presheaf)
            (f.app ((OpenNhds.inclusion x).op.obj U) m ⊗ₜ[((openNhdsRing R x).obj U)]
              g.app ((OpenNhds.inclusion x).op.obj U) n))
      rw [comparisonIso_hom_ι_tmul R x M' N']
      rw [ModuleColimit.map_apply]
      rfl
  | add a b ha hb =>
      simpa only [map_add] using congrArg₂ (fun p q ↦ p + q) ha hb

end StalkTensor

end PresheafOfModules
