module

public import StacksAndModuli.API.GenericFunctionFieldLocalSections
public import StacksAndModuli.API.SheafOfModulesColimits
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.Topology.Sheaves.Skyscraper

/-!
# Stalks of the generic principal-parts sheaf

For an integral scheme, sections of the pushed-forward function-field sheaf on every
nonempty open set are the function field.  It follows that the germ map from global
sections to any stalk is an additive equivalence.  Taking stalks is exact, so the stalk
of the generic principal-parts sheaf is the quotient of this function-field stalk by the
image of the structure-sheaf stalk.

These results are the sheaf-theoretic bridge needed to turn algebraic weak approximation
in a function field into a statement about global sections of the principal-parts sheaf.

## Main results

* `AlgebraicGeometry.Scheme.genericFunctionField_germ_top_bijective`;
* `AlgebraicGeometry.Scheme.functionFieldToGenericFunctionFieldStalkAddEquiv`;
* `AlgebraicGeometry.Scheme.functionFieldToGenericFunctionFieldStalk_mem_range_iff`;
* `AlgebraicGeometry.Scheme.genericPrincipalPartsStalkAddEquiv`.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsIntegral X]

/-- Restriction of the underlying additive function-field sheaf from the whole scheme to
an open containing the generic point is bijective. -/
theorem genericFunctionFieldAdd_restrictTop_bijective
    (U : X.Opens) (hηU : genericPoint X ∈ U) :
    Function.Bijective
      (X.genericFunctionFieldAddSheaf.presheaf.map
        (homOfLE (show U ≤ ⊤ from le_top)).op).hom := by
  change Function.Bijective
    (X.genericFunctionFieldModule.presheaf.map
      (homOfLE (show U ≤ ⊤ from le_top)).op).hom
  exact X.genericFunctionField_restrictTop_bijective U hηU

/-- The germ map from global sections of the generic function-field sheaf to any stalk
is bijective. -/
theorem genericFunctionField_germ_top_bijective (x : X) :
    Function.Bijective
      (X.genericFunctionFieldAddSheaf.presheaf.germ ⊤ x
        (Set.mem_univ x)).hom := by
  constructor
  · intro s t hst
    obtain ⟨W, hxW, iS, iT, hW⟩ :=
      X.genericFunctionFieldAddSheaf.presheaf.germ_eq
        x (Set.mem_univ x) (Set.mem_univ x) s t hst
    cases Subsingleton.elim iS iT
    have hηW : genericPoint X ∈ W :=
      (genericPoint_specializes x).mem_open W.isOpen hxW
    apply (X.genericFunctionFieldAdd_restrictTop_bijective W hηW).1
    rw [show iS = homOfLE (show W ≤ ⊤ from le_top) from
      Subsingleton.elim _ _] at hW
    exact hW
  · intro z
    obtain ⟨U, hxU, s, hs⟩ :=
      X.genericFunctionFieldAddSheaf.presheaf.exists_germ_eq z
    have hηU : genericPoint X ∈ U :=
      (genericPoint_specializes x).mem_open U.isOpen hxU
    let e :
        X.genericFunctionFieldAddSheaf.presheaf.obj (op ⊤) ≃+
          X.genericFunctionFieldAddSheaf.presheaf.obj (op U) :=
      AddEquiv.ofBijective
        (X.genericFunctionFieldAddSheaf.presheaf.map
          (homOfLE (show U ≤ ⊤ from le_top)).op).hom
        (X.genericFunctionFieldAdd_restrictTop_bijective U hηU)
    refine ⟨e.symm s, ?_⟩
    calc
      X.genericFunctionFieldAddSheaf.presheaf.germ ⊤ x
          (Set.mem_univ x) (e.symm s) =
          X.genericFunctionFieldAddSheaf.presheaf.germ U x hxU
            (X.genericFunctionFieldAddSheaf.presheaf.map
              (homOfLE (show U ≤ ⊤ from le_top)).op (e.symm s)) := by
        symm
        exact X.genericFunctionFieldAddSheaf.presheaf.germ_res_apply
          (homOfLE (show U ≤ ⊤ from le_top)) x hxU _
      _ = X.genericFunctionFieldAddSheaf.presheaf.germ U x hxU s := by
        exact congrArg _ (e.apply_symm_apply s)
      _ = z := hs

/-- Global sections of the generic function-field sheaf are additively equivalent to
each of its stalks. -/
noncomputable def genericFunctionFieldGlobalSectionsStalkAddEquiv (x : X) :
    X.genericFunctionFieldAddSheaf.presheaf.obj (op ⊤) ≃+
      X.genericFunctionFieldAddSheaf.presheaf.stalk x :=
  AddEquiv.ofBijective
    (X.genericFunctionFieldAddSheaf.presheaf.germ ⊤ x
      (Set.mem_univ x)).hom
    (X.genericFunctionField_germ_top_bijective x)

/-- The function field is additively equivalent to the stalk at any point of its
pushed-forward sheaf. -/
noncomputable def functionFieldToGenericFunctionFieldStalkAddEquiv (x : X) :
    X.functionField ≃+ X.genericFunctionFieldAddSheaf.presheaf.stalk x :=
  X.genericFunctionFieldGlobalSectionsAddEquiv.symm.trans
    (X.genericFunctionFieldGlobalSectionsStalkAddEquiv x)

/-- The functor which forgets a scheme module to an additive sheaf and takes its stalk
at `x`. -/
abbrev moduleAddStalkFunctor (x : X) : X.Modules ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf X.ringCatSheaf ⋙
    (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)

/-- The additive stalk of the structure module is canonically the underlying additive
group of the local ring. -/
noncomputable def structureModuleAddStalkRingEquiv (x : X) :
    (X.moduleAddStalkFunctor x).obj (structureModule X) ≃+
      X.presheaf.stalk x :=
  (Limits.colimit.isoColimitCocone
    ⟨_, Limits.isColimitOfPreserves
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
      (Limits.colimit.isColimit
        ((OpenNhds.inclusion x).op ⋙ X.presheaf))⟩).addCommGroupIsoToAddEquiv

omit [IsIntegral X] in
/-- The structure-module stalk equivalence sends an additive germ to the same germ in
the local ring. -/
theorem structureModuleAddStalkRingEquiv_germ
    (x : X) (U : X.Opens) (hxU : x ∈ U) (s : X.presheaf.obj (op U)) :
    X.structureModuleAddStalkRingEquiv x
        ((TopCat.Presheaf.germ
          ((SheafOfModules.toSheaf X.ringCatSheaf).obj
            (structureModule X)).obj U x hxU).hom s) =
      X.presheaf.germ U x hxU s := by
  let α :
      TopCat.Presheaf.stalk
          ((SheafOfModules.toSheaf X.ringCatSheaf).obj
            (structureModule X)).obj x ≅
        (forget₂ CommRingCat RingCat ⋙
          forget₂ RingCat AddCommGrpCat).obj (X.presheaf.stalk x) :=
    Limits.colimit.isoColimitCocone
      ⟨_, Limits.isColimitOfPreserves
        (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
        (Limits.colimit.isColimit
          ((OpenNhds.inclusion x).op ⋙ X.presheaf))⟩
  change α.hom
    ((TopCat.Presheaf.germ
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj
        (structureModule X)).obj U x hxU).hom s) = _
  have h :
      TopCat.Presheaf.germ
          ((SheafOfModules.toSheaf X.ringCatSheaf).obj
            (structureModule X)).obj U x hxU ≫ α.hom =
        (forget₂ CommRingCat RingCat ⋙
          forget₂ RingCat AddCommGrpCat).map
            (X.presheaf.germ U x hxU) :=
    Limits.colimit.isoColimitCocone_ι_hom (C := AddCommGrpCat) ..
  exact congr($h s)

/-- The function-field identification of local pushed-forward sections sends the
structure-sheaf section to its germ at the generic point. -/
theorem genericFunctionFieldSectionsAddEquiv_structure
    (U : X.Opens) [Nonempty U] (hηU : genericPoint X ∈ U)
    (s : X.presheaf.obj (op U)) :
    X.genericFunctionFieldSectionsAddEquiv U hηU
        (X.structureToGenericFunctionField.val.app (op U) s) =
      X.germToFunctionField U s := by
  have hlocal :
      X.structureToGenericFunctionField.val.app (op U) s =
        X.genericFunctionFieldModule.presheaf.map
          (homOfLE (show U ≤ ⊤ from le_top)).op
          (X.genericFunctionFieldGlobalSectionsAddEquiv.symm
            (X.germToFunctionField U s)) := by
    change X.genericPointMap.app U s = _
    rw [Scheme.fromSpecStalk_app hηU]
    change
      ((X.presheaf.germ U (genericPoint X) hηU ≫
          (Scheme.ΓSpecIso X.functionField).inv ≫
            (Spec X.functionField).presheaf.map
              (homOfLE (show X.genericPointMap ⁻¹ᵁ U ≤
                X.genericPointMap ⁻¹ᵁ (⊤ : X.Opens) from
                  Scheme.Hom.preimage_mono _ le_top)).op).hom s) =
        (Spec X.functionField).presheaf.map
            (homOfLE (show X.genericPointMap ⁻¹ᵁ U ≤
              X.genericPointMap ⁻¹ᵁ (⊤ : X.Opens) from
                Scheme.Hom.preimage_mono _ le_top)).op
          ((Scheme.ΓSpecIso X.functionField).inv
            (X.germToFunctionField U s))
    rfl
  calc
    _ = X.genericFunctionFieldSectionsAddEquiv U hηU
        (X.genericFunctionFieldModule.presheaf.map
          (homOfLE (show U ≤ ⊤ from le_top)).op
          (X.genericFunctionFieldGlobalSectionsAddEquiv.symm
            (X.germToFunctionField U s))) := congrArg _ hlocal
    _ = X.genericFunctionFieldGlobalSectionsAddEquiv
        (X.genericFunctionFieldGlobalSectionsAddEquiv.symm
          (X.germToFunctionField U s)) :=
      X.genericFunctionFieldSectionsAddEquiv_restrictTop U hηU _
    _ = _ := AddEquiv.apply_symm_apply _ _

/-- The function-field-to-stalk equivalence sends a rational function represented on
an open neighborhood to the germ of that section in the pushed-forward function-field
sheaf. -/
@[simp]
theorem functionFieldToGenericFunctionFieldStalkAddEquiv_germToFunctionField
    (x : X) (U : X.Opens) [Nonempty U]
    (hxU : x ∈ U) (hηU : genericPoint X ∈ U)
    (s : X.presheaf.obj (op U)) :
    X.functionFieldToGenericFunctionFieldStalkAddEquiv x
        (X.germToFunctionField U s) =
      X.genericFunctionFieldAddSheaf.presheaf.germ U x hxU
        (X.structureToGenericFunctionField.val.app (op U) s) := by
  let t := X.genericFunctionFieldGlobalSectionsAddEquiv.symm
    (X.germToFunctionField U s)
  have hres :
      X.genericFunctionFieldModule.presheaf.map
          (homOfLE (show U ≤ ⊤ from le_top)).op t =
        X.structureToGenericFunctionField.val.app (op U) s := by
    apply (X.genericFunctionFieldSectionsAddEquiv U hηU).injective
    rw [X.genericFunctionFieldSectionsAddEquiv_restrictTop,
      X.genericFunctionFieldSectionsAddEquiv_structure]
    exact AddEquiv.apply_symm_apply _ _
  change X.genericFunctionFieldAddSheaf.presheaf.germ ⊤ x
      (Set.mem_univ x) t = _
  calc
    _ = X.genericFunctionFieldAddSheaf.presheaf.germ U x hxU
        (X.genericFunctionFieldModule.presheaf.map
          (homOfLE (show U ≤ ⊤ from le_top)).op t) := by
      symm
      exact X.genericFunctionFieldAddSheaf.presheaf.germ_res_apply
        (homOfLE (show U ≤ ⊤ from le_top)) x hxU t
    _ = _ := congrArg _ hres

/-- On stalks, the structure-sheaf inclusion is the local-ring map into the function
field, under the canonical additive stalk equivalences. -/
theorem structureToGenericFunctionField_stalk_apply
    (x : X) (a : (X.moduleAddStalkFunctor x).obj (structureModule X)) :
    ((X.moduleAddStalkFunctor x).map
        X.structureToGenericFunctionField).hom a =
      X.functionFieldToGenericFunctionFieldStalkAddEquiv x
        (algebraMap (X.presheaf.stalk x) X.functionField
          (X.structureModuleAddStalkRingEquiv x a)) := by
  obtain ⟨U, hxU, s, hs⟩ :=
    TopCat.Presheaf.exists_germ_eq
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj
        (structureModule X)).obj a
  rw [← hs]
  have hηU : genericPoint X ∈ U :=
    (genericPoint_specializes x).mem_open U.isOpen hxU
  let _ : Nonempty U := ⟨⟨genericPoint X, hηU⟩⟩
  rw [X.structureModuleAddStalkRingEquiv_germ]
  rw [X.algebraMap_germ_eq_germToFunctionField hxU]
  rw [X.functionFieldToGenericFunctionFieldStalkAddEquiv_germToFunctionField
    x U hxU hηU s]
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply
    U x hxU
      ((SheafOfModules.toSheaf X.ringCatSheaf).map
        X.structureToGenericFunctionField).hom s

/-- A rational function belongs to the local ring at `x` exactly when its function-field
stalk belongs to the image of the structure-sheaf stalk. -/
theorem functionFieldToGenericFunctionFieldStalk_mem_range_iff
    (x : X) (f : X.functionField) :
    X.functionFieldToGenericFunctionFieldStalkAddEquiv x f ∈
        AddMonoidHom.range
          ((X.moduleAddStalkFunctor x).map
            X.structureToGenericFunctionField).hom ↔
      ∃ a : X.presheaf.stalk x,
        algebraMap (X.presheaf.stalk x) X.functionField a = f := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨X.structureModuleAddStalkRingEquiv x a, ?_⟩
    apply (X.functionFieldToGenericFunctionFieldStalkAddEquiv x).injective
    rw [← ha, X.structureToGenericFunctionField_stalk_apply]
  · rintro ⟨a, ha⟩
    refine ⟨(X.structureModuleAddStalkRingEquiv x).symm a, ?_⟩
    rw [X.structureToGenericFunctionField_stalk_apply,
      AddEquiv.apply_symm_apply, ha]

noncomputable instance sheafAddStalkFunctor_preservesFiniteColimits (x : X) :
    PreservesFiniteColimits
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) :=
  PreservesColimits.preservesFiniteColimits _

noncomputable instance moduleAddStalkFunctor_preservesFiniteColimits (x : X) :
    PreservesFiniteColimits (X.moduleAddStalkFunctor x) := by
  let _ : PreservesFiniteColimits
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) :=
    X.sheafAddStalkFunctor_preservesFiniteColimits x
  exact comp_preservesFiniteColimits
    (SheafOfModules.toSheaf X.ringCatSheaf)
    (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)

/-- The stalk of the generic principal-parts sheaf is the categorical cokernel of the
stalk map from the structure sheaf to the generic function-field sheaf. -/
noncomputable def genericPrincipalPartsStalkIsoCokernel (x : X) :
    X.genericPrincipalPartsAddSheaf.presheaf.stalk x ≅
      cokernel ((X.moduleAddStalkFunctor x).map
        X.structureToGenericFunctionField) :=
  PreservesCokernel.iso (X.moduleAddStalkFunctor x)
    X.structureToGenericFunctionField

/-- The stalk of the generic principal-parts sheaf is the quotient of the generic
function-field stalk by the image of the structure-sheaf stalk. -/
noncomputable def genericPrincipalPartsStalkAddEquiv (x : X) :
    X.genericPrincipalPartsAddSheaf.presheaf.stalk x ≃+
      (X.genericFunctionFieldAddSheaf.presheaf.stalk x ⧸
        AddMonoidHom.range
          ((X.moduleAddStalkFunctor x).map
            X.structureToGenericFunctionField).hom) :=
  (X.genericPrincipalPartsStalkIsoCokernel x ≪≫
    AddCommGrpCat.cokernelIsoQuotient _).addCommGroupIsoToAddEquiv

/-- Under the quotient description of a principal-parts stalk, the germ of the
principal-parts projection is the ordinary quotient map from the function-field
stalk. -/
@[simp]
theorem genericPrincipalPartsStalkAddEquiv_germ_projection
    (x : X) (s : X.genericFunctionFieldAddSheaf.presheaf.obj (op ⊤)) :
    X.genericPrincipalPartsStalkAddEquiv x
        (X.genericPrincipalPartsAddSheaf.presheaf.germ ⊤ x
          (Set.mem_univ x)
          (X.genericPrincipalPartsProjectionAdd.hom.app (op ⊤) s)) =
      QuotientAddGroup.mk'
        (AddMonoidHom.range
          ((X.moduleAddStalkFunctor x).map
            X.structureToGenericFunctionField).hom)
        (X.genericFunctionFieldAddSheaf.presheaf.germ ⊤ x
          (Set.mem_univ x) s) := by
  have hgerm :
      X.genericPrincipalPartsAddSheaf.presheaf.germ ⊤ x
          (Set.mem_univ x)
          (X.genericPrincipalPartsProjectionAdd.hom.app (op ⊤) s) =
        (X.moduleAddStalkFunctor x).map
          X.genericPrincipalPartsProjection
          (X.genericFunctionFieldAddSheaf.presheaf.germ ⊤ x
            (Set.mem_univ x) s) := by
    symm
    exact TopCat.Presheaf.stalkFunctor_map_germ_apply
      ⊤ x (Set.mem_univ x) X.genericPrincipalPartsProjectionAdd.hom s
  rw [hgerm]
  change ((X.moduleAddStalkFunctor x).map
      (cokernel.π X.structureToGenericFunctionField) ≫
        (PreservesCokernel.iso (X.moduleAddStalkFunctor x)
          X.structureToGenericFunctionField).hom ≫
            (AddCommGrpCat.cokernelIsoQuotient _).hom)
      (X.genericFunctionFieldAddSheaf.presheaf.germ ⊤ x
        (Set.mem_univ x) s) = _
  have hmaps :
      (X.moduleAddStalkFunctor x).map
          (cokernel.π X.structureToGenericFunctionField) ≫
            (PreservesCokernel.iso (X.moduleAddStalkFunctor x)
              X.structureToGenericFunctionField).hom ≫
                (AddCommGrpCat.cokernelIsoQuotient _).hom =
        cokernel.π ((X.moduleAddStalkFunctor x).map
            X.structureToGenericFunctionField) ≫
          (AddCommGrpCat.cokernelIsoQuotient _).hom := by
    rw [PreservesCokernel.π_iso_hom_assoc]
  rw [hmaps]
  simp [AddCommGrpCat.cokernelIsoQuotient]

/-- The principal part of a rational function has zero germ at `x` exactly when the
rational function belongs to the local ring at `x`. -/
theorem germ_functionFieldToGenericPrincipalParts_eq_zero_iff
    (x : X) (f : X.functionField) :
    X.genericPrincipalPartsAddSheaf.presheaf.germ ⊤ x
        (Set.mem_univ x)
        (X.functionFieldToGenericPrincipalPartsGlobalSections f) = 0 ↔
      ∃ a : X.presheaf.stalk x,
        algebraMap (X.presheaf.stalk x) X.functionField a = f := by
  have htransform :
      X.genericPrincipalPartsStalkAddEquiv x
          (X.genericPrincipalPartsAddSheaf.presheaf.germ ⊤ x
            (Set.mem_univ x)
            (X.functionFieldToGenericPrincipalPartsGlobalSections f)) =
        QuotientAddGroup.mk'
          (AddMonoidHom.range
            ((X.moduleAddStalkFunctor x).map
              X.structureToGenericFunctionField).hom)
          (X.functionFieldToGenericFunctionFieldStalkAddEquiv x f) := by
    change X.genericPrincipalPartsStalkAddEquiv x
        (X.genericPrincipalPartsAddSheaf.presheaf.germ ⊤ x
          (Set.mem_univ x)
          (X.genericPrincipalPartsProjectionAdd.hom.app (op ⊤)
            (X.genericFunctionFieldGlobalSectionsAddEquiv.symm f))) = _
    rw [X.genericPrincipalPartsStalkAddEquiv_germ_projection]
    rfl
  rw [← (X.genericPrincipalPartsStalkAddEquiv x).map_eq_zero_iff]
  rw [htransform]
  have hzero :
      QuotientAddGroup.mk'
          (AddMonoidHom.range
            ((X.moduleAddStalkFunctor x).map
              X.structureToGenericFunctionField).hom)
          (X.functionFieldToGenericFunctionFieldStalkAddEquiv x f) = 0 ↔
        X.functionFieldToGenericFunctionFieldStalkAddEquiv x f ∈
          AddMonoidHom.range
            ((X.moduleAddStalkFunctor x).map
              X.structureToGenericFunctionField).hom :=
    QuotientAddGroup.eq_zero_iff _
  rw [hzero, X.functionFieldToGenericFunctionFieldStalk_mem_range_iff]

/-- Every principal-parts stalk class is represented by the germ of one global rational
function. -/
theorem exists_functionField_germ_principalParts_eq
    (x : X) (q : X.genericPrincipalPartsAddSheaf.presheaf.stalk x) :
    ∃ f : X.functionField,
      X.genericPrincipalPartsAddSheaf.presheaf.germ ⊤ x
        (Set.mem_univ x)
        (X.functionFieldToGenericPrincipalPartsGlobalSections f) = q := by
  obtain ⟨z, hz⟩ := QuotientAddGroup.mk'_surjective
    (AddMonoidHom.range
      ((X.moduleAddStalkFunctor x).map
        X.structureToGenericFunctionField).hom)
    (X.genericPrincipalPartsStalkAddEquiv x q)
  obtain ⟨f, rfl⟩ :=
    (X.functionFieldToGenericFunctionFieldStalkAddEquiv x).surjective z
  refine ⟨f, ?_⟩
  apply (X.genericPrincipalPartsStalkAddEquiv x).injective
  rw [show X.functionFieldToGenericPrincipalPartsGlobalSections f =
      X.genericPrincipalPartsProjectionAdd.hom.app (op ⊤)
        (X.genericFunctionFieldGlobalSectionsAddEquiv.symm f) from rfl]
  rw [X.genericPrincipalPartsStalkAddEquiv_germ_projection]
  exact hz

end AlgebraicGeometry.Scheme
