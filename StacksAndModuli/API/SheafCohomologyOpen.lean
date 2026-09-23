module

public import StacksAndModuli.API.ExtAdjunction
public import StacksAndModuli.API.SheafCohomologyTerminal
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Sheaf cohomology on an object of a site

For an object `U` of a site, degree-zero local sheaf cohomology is naturally
equivalent to degree-zero global cohomology of the restricted sheaf `F.over U`.
In every degree, the source used to define `F.H' n U` is canonically identified
with the sheaf-pullback of the constant abelian sheaf on the slice site over `U`.

The latter identification reduces the general comparison
`F.H' n U ≃+ (F.over U).H n` to the derived `Ext` adjunction for sheaf-pullback
and sheaf-pushforward along `Over.forget U`.  That adjunction is implemented
below under the single remaining hypothesis that slice extension preserves
monomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open Opposite

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
variable [HasSheafify J AddCommGrpCat.{u}]
variable (F : Sheaf J AddCommGrpCat.{u}) (U : C)

/-- Degree-zero local sheaf cohomology is additively equivalent to evaluation
of the coefficient sheaf on the given object of the site. -/
noncomputable def HPrimeAddEquivZero :
    F.H' 0 U ≃+ F.obj.obj (op U) where
  toEquiv := Ext.addEquiv₀.toEquiv.trans
    (freeAbelianYonedaCorepresentableBy J U).homEquiv
  map_add' x y := by
    change (freeAbelianYonedaCorepresentableBy J U).homEquiv
      (Ext.addEquiv₀ (x + y)) =
        (freeAbelianYonedaCorepresentableBy J U).homEquiv (Ext.addEquiv₀ x) +
          (freeAbelianYonedaCorepresentableBy J U).homEquiv (Ext.addEquiv₀ y)
    rw [map_add]
    rfl

/-- The degree-zero local cohomology equivalence is natural in the coefficient
sheaf. -/
theorem HPrimeAddEquivZero_naturality
    {F G : Sheaf J AddCommGrpCat.{u}} (f : F ⟶ G) (U : C)
    (x : F.H' 0 U) :
    f.hom.app (op U) (HPrimeAddEquivZero J F U x) =
      HPrimeAddEquivZero J G U (x.comp (Ext.mk₀ f) (add_zero 0)) := by
  simp only [HPrimeAddEquivZero]
  have h₀ : Ext.addEquiv₀
      (x.comp (Ext.mk₀ f) (add_zero 0)) = Ext.addEquiv₀ x ≫ f := by
    apply (Ext.mk₀_bijective _ G).injective
    rw [Ext.mk₀_addEquiv₀_apply, ← Ext.mk₀_comp_mk₀,
      Ext.mk₀_addEquiv₀_apply]
  calc
    _ = (freeAbelianYonedaCorepresentableBy J U).homEquiv
        (Ext.addEquiv₀ x ≫ f) :=
      ((freeAbelianYonedaCorepresentableBy J U).homEquiv_comp f _).symm
    _ = (freeAbelianYonedaCorepresentableBy J U).homEquiv
          (Ext.addEquiv₀ (x.comp (Ext.mk₀ f) (add_zero 0))) :=
      congrArg ((freeAbelianYonedaCorepresentableBy J U).homEquiv (Y := G)) h₀.symm

/-- The degree-zero case of the local-to-slice comparison:
`F.H' 0 U` is naturally additively equivalent to global degree-zero
cohomology of `F.over U`. -/
noncomputable def HPrimeOpenEquivHZero : F.H' 0 U ≃+ (F.over U).H 0 :=
  (HPrimeAddEquivZero J F U).trans
    (H.equiv₀ ((J.overPullback AddCommGrpCat.{u} U).obj F)
      Over.mkIdTerminal).symm

/-- The degree-zero local-to-slice comparison is natural in the coefficient
sheaf. -/
theorem HPrimeOpenEquivHZero_naturality
    {F G : Sheaf J AddCommGrpCat.{u}} (f : F ⟶ G) (U : C)
    (x : F.H' 0 U) :
    H.map ((J.overPullback AddCommGrpCat.{u} U).map f) 0
        (HPrimeOpenEquivHZero J F U x) =
      HPrimeOpenEquivHZero J G U (x.comp (Ext.mk₀ f) (add_zero 0)) := by
  apply (H.equiv₀ ((J.overPullback AddCommGrpCat.{u} U).obj G)
    Over.mkIdTerminal).injective
  rw [← H.equiv₀_naturality
    (f := (J.overPullback AddCommGrpCat.{u} U).map f)
    (hT := Over.mkIdTerminal)]
  simp only [HPrimeOpenEquivHZero, AddEquiv.trans_apply]
  erw [(H.equiv₀ ((J.overPullback AddCommGrpCat.{u} U).obj F)
      Over.mkIdTerminal).apply_symm_apply,
    (H.equiv₀ ((J.overPullback AddCommGrpCat.{u} U).obj G)
      Over.mkIdTerminal).apply_symm_apply]
  change f.hom.app (op U) (HPrimeAddEquivZero J F U x) =
    HPrimeAddEquivZero J G U (x.comp (Ext.mk₀ f) (add_zero 0))
  exact HPrimeAddEquivZero_naturality J f U x

/-- The pullback to the ambient site of the constant abelian sheaf on the
slice site over `U` corepresents sections at `U`. -/
noncomputable def openConstantCorepresentableBy :
    (sectionsUnderlyingFunctor J U).CorepresentableBy
      (((Over.forget U).sheafPullback AddCommGrpCat.{u} (J.over U) J).obj
        ((constantSheaf (J.over U) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift ℤ)))) where
  homEquiv :=
    ((Functor.sheafAdjunctionContinuous (Over.forget U) AddCommGrpCat.{u}
      (J.over U) J).homEquiv _ _).trans
        (constantSheafCorepresentableBy (J.over U) Over.mkIdTerminal).homEquiv
  homEquiv_comp g f := by
    rw [Equiv.trans_apply, Equiv.trans_apply,
      Adjunction.homEquiv_naturality_right]
    exact (constantSheafCorepresentableBy
      (J.over U) Over.mkIdTerminal).homEquiv_comp
        ((J.overPullback AddCommGrpCat.{u} U).map g) _

/-- The sheafification of the free abelian representable at `U` is canonically
the pullback to the ambient site of the constant abelian sheaf on the slice
site over `U`. -/
noncomputable def openFreeAbelianYonedaIsoSheafPullbackConstant :
    (presheafToSheaf J AddCommGrpCat.{u}).obj
        (yoneda.obj U ⋙ AddCommGrpCat.free) ≅
      ((Over.forget U).sheafPullback AddCommGrpCat.{u} (J.over U) J).obj
        ((constantSheaf (J.over U) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift ℤ))) :=
  (freeAbelianYonedaCorepresentableBy J U).uniqueUpToIso
    (openConstantCorepresentableBy J U)

/-- Applying the contravariant argument of `Ext` to the canonical source
identification gives the natural source comparison underlying the local
cohomology comparison in every degree. -/
noncomputable def HPrimeOpenSourceNatIso (n : ℕ) :
    (Abelian.extFunctor n).obj
        (op ((presheafToSheaf J AddCommGrpCat.{u}).obj
          (yoneda.obj U ⋙ AddCommGrpCat.free))) ≅
      (Abelian.extFunctor n).obj
        (op (((Over.forget U).sheafPullback AddCommGrpCat.{u} (J.over U) J).obj
          ((constantSheaf (J.over U) AddCommGrpCat.{u}).obj
            (AddCommGrpCat.of (ULift ℤ))))) :=
  (Abelian.extFunctor n).mapIso
    (openFreeAbelianYonedaIsoSheafPullbackConstant J U).symm.op

/-- In every degree, `F.H' n U` is canonically the `Ext` group from the
pullback to the ambient site of the constant abelian sheaf on the slice site.
This is the source identification used by the conditional derived `Ext`
adjunction below. -/
noncomputable def HPrimeOpenSourceIso (n : ℕ) :
    F.H' n U ≅ AddCommGrpCat.of
      (Ext
        (((Over.forget U).sheafPullback AddCommGrpCat.{u} (J.over U) J).obj
          ((constantSheaf (J.over U) AddCommGrpCat.{u}).obj
            (AddCommGrpCat.of (ULift ℤ)))) F n) :=
  (HPrimeOpenSourceNatIso J U n).app F

/-- Restriction from a site to the slice site over `U` preserves finite
colimits of abelian sheaves.  It is the left adjoint in the continuous and
cocontinuous direct-image adjunction. -/
noncomputable instance overPullbackAddCommGrp_preservesFiniteColimits :
    PreservesFiniteColimits (J.overPullback AddCommGrpCat.{u} U) := by
  let _ : (J.overPullback AddCommGrpCat.{u} U).IsLeftAdjoint :=
    (Functor.sheafAdjunctionCocontinuous (Over.forget U)
      AddCommGrpCat.{u} (J.over U) J).isLeftAdjoint
  infer_instance

/-- Restriction from a site to the slice site over `U` is additive on abelian
sheaves. -/
noncomputable instance overPullbackAddCommGrp_additive :
    (J.overPullback AddCommGrpCat.{u} U).Additive := by
  let _ := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (J.overPullback AddCommGrpCat.{u} U)
  apply Functor.additive_of_preservesBinaryBiproducts

/-- The left adjoint of restriction to the slice site over `U` is additive on
abelian sheaves. -/
noncomputable instance overForgetSheafPullbackAddCommGrp_additive :
    ((Over.forget U).sheafPullback AddCommGrpCat.{u}
      (J.over U) J).Additive :=
  (Functor.sheafAdjunctionContinuous (Over.forget U)
    AddCommGrpCat.{u} (J.over U) J).left_adjoint_additive

/-- Conditional all-degree form of Mathlib's open-object cohomology TODO.
It remains only to show that the left adjoint of restriction to the slice site
preserves monomorphisms; all other exact-adjunction hypotheses are automatic. -/
noncomputable def HPrimeOpenEquivH_of_preservesMonomorphisms (n : ℕ)
    [((Over.forget U).sheafPullback AddCommGrpCat.{u}
      (J.over U) J).PreservesMonomorphisms] :
    F.H' n U ≃+ (F.over U).H n :=
  (HPrimeOpenSourceIso J F U n).addCommGroupIsoToAddEquiv.trans
    ((Functor.sheafAdjunctionContinuous (Over.forget U)
      AddCommGrpCat.{u} (J.over U) J).extAddEquiv
        ((constantSheaf (J.over U) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift ℤ))) F n)

/-- The conditional all-degree local-to-slice comparison is natural in the
coefficient sheaf. -/
theorem HPrimeOpenEquivH_of_preservesMonomorphisms_naturality
    {F G : Sheaf J AddCommGrpCat.{u}} (f : F ⟶ G) (U : C) (n : ℕ)
    [((Over.forget U).sheafPullback AddCommGrpCat.{u}
      (J.over U) J).PreservesMonomorphisms]
    (x : F.H' n U) :
    H.map ((J.overPullback AddCommGrpCat.{u} U).map f) n
        (HPrimeOpenEquivH_of_preservesMonomorphisms J F U n x) =
      HPrimeOpenEquivH_of_preservesMonomorphisms J G U n
        (x.comp (Ext.mk₀ f) (add_zero n)) := by
  change (HPrimeOpenEquivH_of_preservesMonomorphisms J F U n x).comp
      (Ext.mk₀ ((J.overPullback AddCommGrpCat.{u} U).map f)) (add_zero n) = _
  simp only [HPrimeOpenEquivH_of_preservesMonomorphisms, AddEquiv.trans_apply]
  rw [← (Functor.sheafAdjunctionContinuous (Over.forget U)
    AddCommGrpCat.{u} (J.over U) J).extAddEquiv_postcomp_mk₀]
  congr 1
  have h := congrArg (fun q ↦ q x)
    ((HPrimeOpenSourceNatIso J U n).hom.naturality f)
  exact h.symm

/-- Under monomorphism preservation by slice extension, vanishing of local
cohomology at `U` is equivalent to vanishing of global cohomology on the slice
site. -/
theorem subsingleton_HPrime_open_iff_of_preservesMonomorphisms (n : ℕ)
    [((Over.forget U).sheafPullback AddCommGrpCat.{u}
      (J.over U) J).PreservesMonomorphisms] :
    Subsingleton (F.H' n U) ↔ Subsingleton ((F.over U).H n) :=
  (HPrimeOpenEquivH_of_preservesMonomorphisms J F U n).toEquiv.subsingleton_congr

end CategoryTheory.Sheaf
