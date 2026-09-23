module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-!
# `Ext`-modules from a ring homomorphism into an endomorphism ring

Mathlib puts an `R`-module structure on `Ext X Y n` when the ambient abelian category is
`R`-linear (`Mathlib/Algebra/Homology/DerivedCategory/Ext/Linear.lean`). That hypothesis is
too strong for sheaf cohomology: the category `TopCat.Sheaf AddCommGrpCat X` of abelian
sheaves on a scheme is `ℤ`-linear and nothing more, yet `Hⁿ(X, F)` is a module over
`Γ(X, 𝒪_X)` whenever `F` is a sheaf of `𝒪_X`-modules — the scalars act on the *single
object* `F`, not on the whole category.

This file provides that weaker input: a ring homomorphism `φ : R →+* End G` makes every
`Ext A G n` an `R`-module, with `r` acting by postcomposition with `mk₀ (φ r)`. This is
nothing but the additivity of `Ext` in its second variable, packaged as a module structure.
When the category *is* `R`-linear and `φ` is the canonical map, the two agree
(`moduleOfRingHom_algebraMap`).

The scalar action is deliberately *not* an instance: `G` cannot be recovered from `R`, so
instance search would loop. Downstream files introduce the instance they need with `letI`,
or register a specialization whose head symbol pins `G` — see
`StacksAndModuli/API/SheafCohomologyModule.lean`.

## Main definitions

* `CategoryTheory.Abelian.Ext.smulOfRingHom`: the scalar action of `R` on `Ext A G n`.
* `CategoryTheory.Abelian.Ext.moduleOfRingHom`: the resulting `R`-module structure.

## Main results

* `CategoryTheory.Abelian.Ext.moduleOfRingHom_smul`: the defining equation of the action.
* `CategoryTheory.Abelian.Ext.moduleOfRingHom_algebraMap`: agreement with the module
  structure coming from `R`-linearity of the ambient category.

## Upstream

This is the content of Mathlib PR
[#42716](https://github.com/leanprover-community/mathlib4/pull/42716)
(Raphael Douglas Giles), still open at the time of writing; it is reproduced here so that
StacksAndModuli can depend on it. Delete this file once the PR lands.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe w v u t

namespace CategoryTheory

namespace Abelian

namespace Ext

section RingHom

variable {R : Type t} [Semiring R] {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {A G : C} (φ : R →+* End G)

/-- Auxiliary definition for `Abelian.Ext.moduleOfRingHom`: the scalar multiplication in
which `r : R` acts on `Ext A G n` by postcomposition with `mk₀ (φ r)`. -/
@[reducible] noncomputable def smulOfRingHom (n : ℕ) : SMul R (Ext A G n) where
  smul r x := x.comp (mk₀ (φ r)) (add_zero n)

lemma smulOfRingHom_smul (n : ℕ) (r : R) (x : Ext A G n) :
    letI := smulOfRingHom φ n (A := A) (G := G)
    r • x = x.comp (mk₀ (φ r)) (add_zero n) := rfl

/-- A ring homomorphism `φ : R →+* End G` makes each `Ext A G n` an `R`-module, with `r`
acting by postcomposition with `mk₀ (φ r)`; this is the additivity of `Ext` in its second
variable packaged as a module structure.

Note that this does not require the ambient category to be `R`-linear: only the single
object `G` needs an action of `R`. There is also an `R`-module instance on `Ext A G n` in
the case where `C` is `R`-linear; when `C` is `R`-linear the two agree, see
`Abelian.Ext.moduleOfRingHom_algebraMap`. -/
@[reducible] noncomputable def moduleOfRingHom (n : ℕ) : Module R (Ext A G n) where
  __ := smulOfRingHom φ n (A := A) (G := G)
  one_smul x := by simp [smulOfRingHom_smul, End.one_def]
  mul_smul r s x := by
    simp only [smulOfRingHom_smul]
    rw [map_mul, End.mul_def, ← mk₀_comp_mk₀, comp_assoc_of_third_deg_zero]
  smul_zero r := by simp [smulOfRingHom_smul]
  zero_smul x := by
    simp only [smulOfRingHom_smul]
    rw [map_zero, show (0 : End G) = (0 : G ⟶ G) from rfl, mk₀_zero, comp_zero]
  smul_add r x y := by simp [smulOfRingHom_smul]
  add_smul r s x := by
    simp only [smulOfRingHom_smul]
    rw [map_add, show mk₀ (φ r + φ s) = mk₀ (φ r) + mk₀ (φ s) from mk₀_add (φ r) (φ s),
      comp_add]

lemma moduleOfRingHom_smul (n : ℕ) (r : R) (x : Ext A G n) :
    letI := moduleOfRingHom φ n (A := A) (G := G)
    r • x = x.comp (mk₀ (φ r)) (add_zero n) := rfl

end RingHom

section CommRing

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- In an `R`-linear category over a commutative ring, the `Module R (Ext X Y n)` instance
is `Abelian.Ext.moduleOfRingHom` for the canonical ring homomorphism `R →+* End Y`. -/
lemma moduleOfRingHom_algebraMap {R : Type t} [CommRing R] [Linear R C] {X Y : C} {n : ℕ} :
    moduleOfRingHom (algebraMap R (End Y)) n (A := X) = (inferInstance : Module R (Ext X Y n)) :=
  Module.ext' _ _ fun r x => by
    rw [moduleOfRingHom_smul, smul_eq_comp_mk₀]
    congr 2

end CommRing

end Ext

end Abelian

end CategoryTheory
