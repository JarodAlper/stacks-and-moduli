module

public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import StacksAndModuli.API.SheafCohomologyModule

/-!
# The cohomology of an `𝒪_X`-module over an open, as a module over its sections

`StacksAndModuli/API/SheafCohomologyModule.lean` makes `Hⁿ(X, F)` a `Γ(X, 𝒪_X)`-module by letting a
*global* section act on `F` and transporting the action through `Ext`.  For higher direct
images that is not enough: the presheaf `U ↦ Hⁱ(f⁻¹U, F)` must be a presheaf of
`𝒪_Y`-modules, and a section `r ∈ Γ(Y, U)` acts on `F` only after restriction to `f⁻¹U`.
It therefore gives no endomorphism of the global sheaf `F`, and the functoriality of
`Sheaf.cohomologyPresheaf` in `F` — the only one Mathlib provides — cannot produce the
action.

This file supplies the missing ingredient by working on the **over-site**.  For `V : X.Opens`,
`Sheaf.over` restricts the underlying abelian sheaf of `F` to `J.over V`, and multiplication
by `r : Γ(X, V)` *is* an endomorphism there: on an object `W ⟶ V` it is multiplication by
`r|_W`.  Transporting that ring map through `CategoryTheory.Abelian.Ext.moduleOfRingHom`
makes `Sheaf.H (F.over V) i` a `Γ(X, V)`-module.

Nothing here compares the over-site cohomology with `Sheaf.cohomologyPresheaf`; that
comparison is a TODO in Mathlib
(`CategoryTheory/Sites/SheafCohomology/Basic.lean`) and is deliberately avoided — the higher
direct image should be *defined* through the over-site rather than compared with it.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.restrictLE`: restriction of `𝒪_X`-sections along an
  inclusion of opens, as a ring homomorphism.
* `…smulNatTransOver`, `…smulSheafHomOver`: multiplication by `r : Γ(X, V)` on the
  restriction of `F` to the over-site of `V`.
* `…smulEndOver'`: the ring homomorphism `Γ(X, V) →+* End (F.over V)`.
* `…instModuleHOver`: `Hⁱ(V, F)` is a `Γ(X, V)`-module.

## The restriction maps

* `CategoryTheory.overMapPullbackAdjunction`: the over-site restriction functor is a **left**
  adjoint.  It is *defined* as `sheafPushforwardContinuous`, which `Sites/Pullback.lean`
  exhibits as a right adjoint; `(Over.map f).IsCocontinuous` and
  `Functor.sheafAdjunctionCocontinuous` make the same functor a left adjoint too.  That
  two-sidedness is what makes restriction exact, and hence `Ext`-functorial.
* `CategoryTheory.overMapPullbackConstantSheafIso`: restriction carries the constant sheaf to
  the constant sheaf.
* `CategoryTheory.Sheaf.HOverRestrict`: the resulting map `Hⁱ(V, F) → Hⁱ(V', F)`.

## What remains for `Rⁱ f_*`

Functoriality of `HOverRestrict` (identity and composition), its semilinearity over
`Γ(X, V) → Γ(X, V')`, and then assembling `V ↦ Hⁱ(f⁻¹V, F)` into a presheaf of `𝒪_Y`-modules
and sheafifying.  See the §A.6 COMMENTARY.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace CategoryTheory

open Limits

section OverRestrictionExact

variable {X : TopCat.{u}} {V' V : TopologicalSpace.Opens X} (h : V' ≤ V)

/-- **The over-site restriction functor is a left adjoint.**  `overMapPullback` is defined as
`sheafPushforwardContinuous`, which `Sites/Pullback.lean` exhibits as a *right* adjoint; but
`Over.map` is also cocontinuous (`Sites/Over.lean`), and `sheafAdjunctionCocontinuous` then
makes the very same functor a *left* adjoint as well.  That two-sidedness is what makes
restriction to a smaller open exact. -/
noncomputable def overMapPullbackAdjunction :
    (Opens.grothendieckTopology X).overMapPullback AddCommGrpCat.{u} (homOfLE h) ⊣
      (Over.map (homOfLE h)).sheafPushforwardCocontinuous AddCommGrpCat.{u} _ _ :=
  Functor.sheafAdjunctionCocontinuous _ _ _ _

/-- Restriction along an inclusion of opens preserves finite colimits, being a left
adjoint. -/
noncomputable instance :
    PreservesFiniteColimits
      ((Opens.grothendieckTopology X).overMapPullback AddCommGrpCat.{u} (homOfLE h)) := by
  have : PreservesColimitsOfSize.{0, 0}
      ((Opens.grothendieckTopology X).overMapPullback AddCommGrpCat.{u} (homOfLE h)) :=
    (overMapPullbackAdjunction h).leftAdjoint_preservesColimits
  infer_instance

/-- Restriction along an inclusion of opens is additive. -/
noncomputable instance :
    ((Opens.grothendieckTopology X).overMapPullback AddCommGrpCat.{u} (homOfLE h)).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **Restriction carries the constant sheaf to the constant sheaf.**

Mathlib has no lemma to this effect on the over-site, but `constantSheaf J D` is
`Functor.const Cᵒᵖ ⋙ presheafToSheaf J D`, and restricting a constant presheaf along
`(Over.map f).op` gives the constant presheaf definitionally; what is left is that restriction
commutes with sheafification, which is exactly
`Functor.pushforwardContinuousSheafificationCompatibility`. -/
noncomputable def overMapPullbackConstantSheafIso (M : AddCommGrpCat.{u}) :
    ((Opens.grothendieckTopology X).overMapPullback AddCommGrpCat.{u} (homOfLE h)).obj
        ((constantSheaf ((Opens.grothendieckTopology X).over V) AddCommGrpCat.{u}).obj M) ≅
      (constantSheaf ((Opens.grothendieckTopology X).over V') AddCommGrpCat.{u}).obj M :=
  ((Functor.pushforwardContinuousSheafificationCompatibility (Over.map (homOfLE h))
      AddCommGrpCat.{u} ((Opens.grothendieckTopology X).over V')
      ((Opens.grothendieckTopology X).over V)).app
    ((Functor.const ((Over V)ᵒᵖ)).obj M)).symm

/-- **The restriction map on over-site cohomology**, `Hⁱ(V, F) → Hⁱ(V', F)` for `V' ≤ V`.

This is the missing structure map of the presheaf `V ↦ Hⁱ(V, F)`, and hence the last piece
needed to build `Rⁱ f_* F` as a sheaf of `𝒪_Y`-modules through the over-site.  It is
`Abelian.Ext.mapExactFunctor` applied to the restriction functor — legitimate because that
functor is additive and preserves finite limits *and* colimits, the latter because it is a
left adjoint (`overMapPullbackAdjunction`) — followed by transport along the two
identifications of the endpoints: `overMapPullbackConstantSheafIso` on the source and
`Sheaf.pushforwardOverMapIso` on the target. -/
noncomputable def Sheaf.HOverRestrict
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H (F.over V) n → Sheaf.H (F.over V') n := fun e =>
  ((Abelian.Ext.mk₀ (overMapPullbackConstantSheafIso h
        (AddCommGrpCat.of (ULift.{u, 0} ℤ))).inv).comp
      (e.mapExactFunctor
        ((Opens.grothendieckTopology X).overMapPullback AddCommGrpCat.{u} (homOfLE h)))
      (zero_add n)).comp
    (Abelian.Ext.mk₀ (F.pushforwardOverMapIso (homOfLE h)).hom) (add_zero n)

/-- The restriction map is additive, so `Hⁱ(V, F)` is a presheaf of abelian groups on the
opens of `X`.  Additivity comes from `Abelian.Ext.mapExactFunctor_add` together with
bilinearity of `Ext.comp`. -/
noncomputable def Sheaf.HOverRestrictAddHom
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H (F.over V) n →+ Sheaf.H (F.over V') n where
  toFun := Sheaf.HOverRestrict h F n
  map_zero' := by
    simp only [Sheaf.HOverRestrict, Abelian.Ext.mapExactFunctor_zero,
      Abelian.Ext.comp_zero, Abelian.Ext.zero_comp]
  map_add' e₁ e₂ := by
    simp only [Sheaf.HOverRestrict, Abelian.Ext.mapExactFunctor_add,
      Abelian.Ext.comp_add, Abelian.Ext.add_comp]

end OverRestrictionExact

end CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (F : X.Modules)

/-- Restriction of sections of `𝒪_X` along an inclusion of opens, as a ring map. -/
noncomputable def restrictLE {V W : X.Opens} (h : W ≤ V) : Γ(X, V) →+* Γ(X, W) :=
  (X.presheaf.map (homOfLE h).op).hom

/-- Multiplication by `r : Γ(X, V)` on the restriction of `F` to the over-site of `V`. -/
noncomputable def smulNatTransOver (V : X.Opens) (r : Γ(X, V)) :
    (((SheafOfModules.toSheaf X.ringCatSheaf).obj F).over V).obj ⟶
      (((SheafOfModules.toSheaf X.ringCatSheaf).obj F).over V).obj where
  app W := F.smul (restrictLE (leOfHom W.unop.hom) r)
  naturality W W' i := by
    have key : restrictLE (leOfHom W'.unop.hom) r =
        X.presheaf.map (i.unop.left).op (restrictLE (leOfHom W.unop.hom) r) := by
      rw [restrictLE, restrictLE, ← ConcreteCategory.comp_apply,
        ← X.presheaf.map_comp, ← op_comp]
      rfl
    rw [key]
    exact (F.map_comp_smul i.unop.left (restrictLE (leOfHom W.unop.hom) r)).symm

/-- Multiplication by `r : Γ(X, V)` as an endomorphism of the sheaf `F.over V`. -/
noncomputable def smulSheafHomOver (V : X.Opens) (r : Γ(X, V)) :
    End (((SheafOfModules.toSheaf X.ringCatSheaf).obj F).over V) :=
  Sheaf.homEquiv.symm (smulNatTransOver F V r)

/-- Two endomorphisms of `F.over V` agree as soon as they agree on sections. -/
lemma sheafHomOver_ext {V : X.Opens}
    {f g : End (((SheafOfModules.toSheaf X.ringCatSheaf).obj F).over V)}
    (h : ∀ W : (Over V)ᵒᵖ, f.hom.app W = g.hom.app W) : f = g :=
  Sheaf.homEquiv.injective (NatTrans.ext (funext h))

/-- The `Γ(X, V)`-action on sections over an object of the over-site. -/
noncomputable def smulEndOverSection {V : X.Opens} (W : Over V) :
    Γ(X, V) →+* End Γ(F, W.left) :=
  (F.smul).comp (restrictLE (leOfHom W.hom))

/-- **The scalars acting on the cohomology of `F` over an open `V`.** -/
noncomputable def smulEndOver' (V : X.Opens) :
    Γ(X, V) →+* End (((SheafOfModules.toSheaf X.ringCatSheaf).obj F).over V) where
  toFun := smulSheafHomOver F V
  map_one' := sheafHomOver_ext F fun W ↦ (smulEndOverSection F W.unop).map_one
  map_mul' r s := sheafHomOver_ext F fun W ↦ (smulEndOverSection F W.unop).map_mul r s
  map_zero' := sheafHomOver_ext F fun W ↦ (smulEndOverSection F W.unop).map_zero
  map_add' r s := sheafHomOver_ext F fun W ↦ (smulEndOverSection F W.unop).map_add r s

/-- `Hⁱ(V, F)` is a `Γ(X, V)`-module. -/
noncomputable instance instModuleHOver (V : X.Opens) (i : ℕ) :
    Module Γ(X, V)
      (Sheaf.H (((SheafOfModules.toSheaf X.ringCatSheaf).obj F).over V) i) :=
  CategoryTheory.Abelian.Ext.moduleOfRingHom (smulEndOver' F V) i

end AlgebraicGeometry.Scheme.Modules
