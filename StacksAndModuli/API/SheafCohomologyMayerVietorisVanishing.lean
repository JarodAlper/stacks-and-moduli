module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
public import Mathlib.Topology.Sheaves.MayerVietoris
public import Mathlib.Algebra.Category.Grp.Biproducts
public import StacksAndModuli.API.SheafCohomologyOpenLES
public import StacksAndModuli.API.SheafCohomologyFiniteCoproduct
public import StacksAndModuli.API.SheafCohomologyTerminalMayerVietoris

/-!
# First-cohomology vanishing from Mayer--Vietoris

This file packages the standard vanishing consequence of the Mayer--Vietoris sequence.
If the degree-zero difference map for a Mayer--Vietoris square is surjective and degree-one
cohomology vanishes on the two covering objects, then degree-one cohomology vanishes on the
fourth object. When that object is terminal, the conclusion is global sheaf cohomology.

For a scheme covered by two opens, the final theorem rewrites the local terms as
structure-sheaf cohomology of the corresponding open subschemes. This reduces computations
such as `H¹(ℙ¹, 𝒪) = 0` to affine vanishing on the standard opens and surjectivity of
the usual difference map on sections.

## Main results

* `CategoryTheory.GrothendieckTopology.MayerVietorisSquare.
    subsingleton_HPrime_one_of_surjective_fromBiprod`;
* `CategoryTheory.GrothendieckTopology.MayerVietorisSquare.
    subsingleton_H_one_of_terminal_of_surjective_fromBiprod`;
* `CategoryTheory.GrothendieckTopology.MayerVietorisSquare.sectionsDifference`;
* `CategoryTheory.GrothendieckTopology.MayerVietorisSquare.
    surjective_fromBiprod_of_surjective_sectionsDifference`;
* `AlgebraicGeometry.Scheme.Modules.subsingleton_H_one_structureModule_of_openCover`;
* `CategoryTheory.Sheaf.subsingleton_HPrime_sup`.

A second, independent consequence of the same long exact sequence is the degree-shifted
vanishing statement for an open cover of a topological space: the stretch

`Hⁿ⁰(U ⊓ V) ⟶ Hⁿ¹(U ⊔ V) ⟶ Hⁿ¹(U) ⊞ Hⁿ¹(V)`

is exact at the middle term (`sequence_exact` at index `2`), so `Hⁿ¹(U ⊔ V, F)` vanishes
whenever `Hⁿ⁰(U ⊓ V, F)`, `Hⁿ¹(U, F)` and `Hⁿ¹(V, F)` do, with `n₀ + 1 = n₁`. This is the
form a cohomological induction over a finite open cover needs.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe w v u

namespace CategoryTheory.GrothendieckTopology.MayerVietorisSquare

open Category Opposite Limits Abelian ComposableArrows

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type v)] [HasSheafify J AddCommGrpCat.{v}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

/-- If the degree-zero difference map is surjective and degree-one cohomology vanishes
on both covering objects, then degree-one cohomology vanishes on the fourth object of a
Mayer--Vietoris square. -/
theorem subsingleton_HPrime_one_of_surjective_fromBiprod
    (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v})
    (hsurj : Function.Surjective (S.fromBiprod F 0))
    [Subsingleton (F.H' 1 S.X₂)] [Subsingleton (F.H' 1 S.X₃)] :
    Subsingleton (F.H' 1 S.X₄) := by
  let _ : Epi (S.fromBiprod F 0) :=
    (AddCommGrpCat.epi_iff_surjective _).mpr hsurj
  have hδ : S.δ F 0 1 rfl = 0 := by
    rw [← cancel_epi (S.fromBiprod F 0)]
    exact S.fromBiprod_δ F 0 1 rfl
  let _ : Mono (S.toBiprod F 1) :=
    ((S.sequence_exact F 0 1 rfl).exact 2).mono_g hδ
  constructor
  intro x y
  apply (AddCommGrpCat.mono_iff_injective (S.toBiprod F 1)).mp inferInstance
  apply (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.injective
  exact Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)

/-- If the fourth object is terminal, the preceding Mayer--Vietoris criterion gives
vanishing of global first sheaf cohomology. -/
theorem subsingleton_H_one_of_terminal_of_surjective_fromBiprod
    (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v})
    (hT : IsTerminal S.X₄)
    (hsurj : Function.Surjective (S.fromBiprod F 0))
    [Subsingleton (F.H' 1 S.X₂)] [Subsingleton (F.H' 1 S.X₃)] :
    Subsingleton (F.H 1) := by
  rw [← CategoryTheory.Sheaf.subsingleton_HPrime_terminal_iff J F 1 hT]
  exact S.subsingleton_HPrime_one_of_surjective_fromBiprod F hsurj

end CategoryTheory.GrothendieckTopology.MayerVietorisSquare

namespace CategoryTheory.Sheaf

open CategoryTheory.Abelian Opposite

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u}]

/-- The degree-zero local-cohomology-to-sections equivalence intertwines restriction in
the cohomology presheaf with restriction of sheaf sections. -/
theorem HPrimeAddEquivZero_map
    (F : Sheaf J AddCommGrpCat.{u}) {U V : C} (i : op U ⟶ op V)
    (x : F.H' 0 U) :
    HPrimeAddEquivZero J F V ((F.cohomologyPresheaf 0).map i x) =
      F.obj.map i (HPrimeAddEquivZero J F U x) := by
  let a := ((yoneda ⋙
    (Functor.whiskeringRight Cᵒᵖ (Type u) AddCommGrpCat.{u}).obj
      AddCommGrpCat.free ⋙ presheafToSheaf J AddCommGrpCat.{u}).op.map i).unop
  have h₀ : Ext.addEquiv₀ ((Ext.mk₀ a).comp x (zero_add 0)) =
      a ≫ Ext.addEquiv₀ x := by
    apply (Ext.mk₀_bijective _ F).injective
    calc
      Ext.mk₀ (Ext.addEquiv₀ ((Ext.mk₀ a).comp x (zero_add 0))) =
          (Ext.mk₀ a).comp x (zero_add 0) :=
        Ext.mk₀_addEquiv₀_apply _
      _ = (Ext.mk₀ a).comp (Ext.mk₀ (Ext.addEquiv₀ x)) (zero_add 0) := by
        rw [Ext.mk₀_addEquiv₀_apply]
      _ = Ext.mk₀ (a ≫ Ext.addEquiv₀ x) := Ext.mk₀_comp_mk₀ _ _
  change (freeAbelianYonedaCorepresentableBy J V).homEquiv
      (Ext.addEquiv₀ ((Ext.mk₀ a).comp x (zero_add 0))) = _
  calc
    _ = (freeAbelianYonedaCorepresentableBy J V).homEquiv
        (a ≫ Ext.addEquiv₀ x) := congrArg _ h₀
    _ = _ := by
      let g : (presheafToSheaf J AddCommGrpCat.{u}).obj
          (yoneda.obj U ⋙ AddCommGrpCat.free) ⟶ F := Ext.addEquiv₀ x
      have hadj := (freeAbelianSheafAdjunction J).homEquiv_naturality_left
        (yoneda.map i.unop) g
      change yonedaEquiv
          ((freeAbelianSheafAdjunction J).homEquiv (yoneda.obj V) F
            ((presheafToSheaf J AddCommGrpCat.{u}).map
              (Functor.whiskerRight (yoneda.map i.unop) AddCommGrpCat.free) ≫ g)) = _
      calc
        _ = yonedaEquiv (yoneda.map i.unop ≫
            (freeAbelianSheafAdjunction J).homEquiv (yoneda.obj U) F g) :=
          congrArg yonedaEquiv hadj
        _ = F.obj.map i (yonedaEquiv
            ((freeAbelianSheafAdjunction J).homEquiv (yoneda.obj U) F g)) :=
          (yonedaEquiv_naturality _ _).symm
        _ = _ := rfl

end CategoryTheory.Sheaf

namespace CategoryTheory.GrothendieckTopology.MayerVietorisSquare

open Category Opposite Limits Abelian

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type u)] [HasSheafify J AddCommGrpCat.{u}]
  [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]

/-- The difference of the two restriction maps on actual sheaf sections associated to a
Mayer--Vietoris square. -/
noncomputable def sectionsDifference
    (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{u}) :
    (F.obj.obj (op S.X₂) × F.obj.obj (op S.X₃)) →+
      F.obj.obj (op S.X₁) where
  toFun x := F.obj.map S.f₁₂.op x.1 - F.obj.map S.f₁₃.op x.2
  map_zero' := by simp
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add, map_add, sub_add_sub_comm]

/-- Under the canonical degree-zero local cohomology equivalences, `fromBiprod` is the
difference of the two restriction maps on actual sheaf sections. -/
theorem HPrimeAddEquivZero_fromBiprod_biprodIsoProd_inv
    (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{u})
    (x₂ : F.H' 0 S.X₂) (x₃ : F.H' 0 S.X₃) :
    CategoryTheory.Sheaf.HPrimeAddEquivZero J F S.X₁
        (S.fromBiprod F 0
          ((AddCommGrpCat.biprodIsoProd _ _).inv ⟨x₂, x₃⟩)) =
      S.sectionsDifference F
        ⟨CategoryTheory.Sheaf.HPrimeAddEquivZero J F S.X₂ x₂,
          CategoryTheory.Sheaf.HPrimeAddEquivZero J F S.X₃ x₃⟩ := by
  rw [S.fromBiprod_biprodIsoProd_inv_apply]
  simp only [map_sub]
  rw [CategoryTheory.Sheaf.HPrimeAddEquivZero_map,
    CategoryTheory.Sheaf.HPrimeAddEquivZero_map]
  rfl

/-- Surjectivity of the difference map on actual sheaf sections implies surjectivity of
the degree-zero Mayer--Vietoris map. -/
theorem surjective_fromBiprod_of_surjective_sectionsDifference
    (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{u})
    (h : Function.Surjective (S.sectionsDifference F)) :
    Function.Surjective (S.fromBiprod F 0) := by
  intro y
  obtain ⟨⟨s₂, s₃⟩, hs⟩ := h
    (CategoryTheory.Sheaf.HPrimeAddEquivZero J F S.X₁ y)
  let x₂ := (CategoryTheory.Sheaf.HPrimeAddEquivZero J F S.X₂).symm s₂
  let x₃ := (CategoryTheory.Sheaf.HPrimeAddEquivZero J F S.X₃).symm s₃
  refine ⟨(AddCommGrpCat.biprodIsoProd _ _).inv ⟨x₂, x₃⟩, ?_⟩
  apply (CategoryTheory.Sheaf.HPrimeAddEquivZero J F S.X₁).injective
  rw [S.HPrimeAddEquivZero_fromBiprod_biprodIsoProd_inv]
  simpa only [x₂, x₃, AddEquiv.apply_symm_apply] using hs

/-- If the fourth object is terminal, surjectivity of the difference map on actual
sections and local degree-one vanishing imply global degree-one vanishing. -/
theorem subsingleton_H_one_of_terminal_of_surjective_sectionsDifference
    (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{u})
    (hT : IsTerminal S.X₄)
    (h : Function.Surjective (S.sectionsDifference F))
    [Subsingleton (F.H' 1 S.X₂)] [Subsingleton (F.H' 1 S.X₃)] :
    Subsingleton (F.H 1) :=
  S.subsingleton_H_one_of_terminal_of_surjective_fromBiprod F hT
    (S.surjective_fromBiprod_of_surjective_sectionsDifference F h)

end CategoryTheory.GrothendieckTopology.MayerVietorisSquare

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory

/-- Let `U` and `V` cover a scheme `X`. If first structure-sheaf cohomology vanishes on
the two open subschemes and the Mayer--Vietoris degree-zero difference map is surjective,
then `H¹(X, 𝒪_X)` vanishes. -/
theorem subsingleton_H_one_structureModule_of_openCover
    (X : Scheme.{u}) (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    (hsurj : Function.Surjective
      ((_root_.Opens.mayerVietorisSquare U V).fromBiprod
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj (structureModule X)) 0))
    [Subsingleton (H (structureModule U.toScheme) 1)]
    [Subsingleton (H (structureModule V.toScheme) 1)] :
    Subsingleton (H (structureModule X) 1) := by
  let F := (SheafOfModules.toSheaf X.ringCatSheaf).obj (structureModule X)
  let S := _root_.Opens.mayerVietorisSquare U V
  let _ : Subsingleton (F.H' 1 U) :=
    (structureCohomologyOpenAddEquiv X U 1).toEquiv.subsingleton_congr.mpr
      inferInstance
  let _ : Subsingleton (F.H' 1 V) :=
    (structureCohomologyOpenAddEquiv X V 1).toEquiv.subsingleton_congr.mpr
      inferInstance
  let _ : Subsingleton (F.H' 1 S.X₂) := by
    change Subsingleton (F.H' 1 U)
    infer_instance
  let _ : Subsingleton (F.H' 1 S.X₃) := by
    change Subsingleton (F.H' 1 V)
    infer_instance
  have hT : IsTerminal (U ⊔ V) :=
    IsTerminal.ofIso isTerminalTop (eqToIso hcover).symm
  change Subsingleton (F.H 1)
  exact S.subsingleton_H_one_of_terminal_of_surjective_fromBiprod
    F hT hsurj

/-- Let `U` and `V` cover a scheme `X`. If first structure-sheaf cohomology vanishes
on both open subschemes and the difference of the restriction maps on actual sections is
surjective, then `H¹(X, 𝒪_X)` vanishes. -/
theorem subsingleton_H_one_structureModule_of_openCover_of_sections
    (X : Scheme.{u}) (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    (hsurj : Function.Surjective
      ((_root_.Opens.mayerVietorisSquare U V).sectionsDifference
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj (structureModule X))))
    [Subsingleton (H (structureModule U.toScheme) 1)]
    [Subsingleton (H (structureModule V.toScheme) 1)] :
    Subsingleton (H (structureModule X) 1) := by
  apply subsingleton_H_one_structureModule_of_openCover X U V hcover
  let S := _root_.Opens.mayerVietorisSquare U V
  exact S.surjective_fromBiprod_of_surjective_sectionsDifference _ hsurj

end AlgebraicGeometry.Scheme.Modules

section OpensDegreeShift

open TopologicalSpace Opposite

namespace CategoryTheory.Sheaf

variable {T : TopCat.{u}} (F : _root_.TopCat.Sheaf AddCommGrpCat.{u} T)

/-- A biproduct of two subsingleton abelian groups is a subsingleton. -/
lemma subsingleton_biprod {A B : AddCommGrpCat.{u}} (hA : Subsingleton A)
    (hB : Subsingleton B) : Subsingleton ((A ⊞ B : AddCommGrpCat.{u})) := by
  refine ⟨fun a b => ?_⟩
  have hinj : Function.Injective (AddCommGrpCat.biprodIsoProd A B).hom := by
    intro x y hxy
    have := congrArg (AddCommGrpCat.biprodIsoProd A B).inv hxy
    rwa [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      (AddCommGrpCat.biprodIsoProd A B).hom_inv_id, ConcreteCategory.id_apply,
      ConcreteCategory.id_apply] at this
  exact hinj (@Subsingleton.elim _ (@instSubsingletonProd _ _ hA hB) _ _)

/-- **Mayer–Vietoris vanishing.**  `Hⁿ¹(U ⊔ V, F) = 0` when `Hⁿ⁰(U ⊓ V, F)`, `Hⁿ¹(U, F)` and
`Hⁿ¹(V, F)` vanish. -/
theorem subsingleton_HPrime_sup (U V : Opens T) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (h₁ : Subsingleton (F.H' n₀ (U ⊓ V)))
    (h₂ : Subsingleton (F.H' n₁ U)) (h₃ : Subsingleton (F.H' n₁ V)) :
    Subsingleton (F.H' n₁ (U ⊔ V)) := by
  set S := Opens.mayerVietorisSquare U V with hS
  have hex := (S.sequence_exact F n₀ n₁ h).exact 2 (by omega)
  rw [ShortComplex.ab_exact_iff_function_exact] at hex
  refine ⟨fun a b => ?_⟩
  have key : ∀ x : (F.H' n₁ (U ⊔ V) : Type u), x = 0 := by
    intro x
    have hbip : Subsingleton ((F.H' n₁ S.X₂) ⊞ (F.H' n₁ S.X₃) : AddCommGrpCat.{u}) :=
      subsingleton_biprod h₂ h₃
    have hx : (S.toBiprod F n₁) x = 0 := @Subsingleton.elim _ hbip _ _
    obtain ⟨y, hy⟩ := (hex x).mp hx
    rw [← hy, @Subsingleton.elim _ h₁ y 0, map_zero]
  rw [key a, key b]

end CategoryTheory.Sheaf

end OpensDegreeShift

end
