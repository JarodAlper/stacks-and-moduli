module

public import StacksAndModuli.API.ModuleExtDepth
public import Mathlib.RingTheory.KrullDimension.Regular

/-!
# Cohen--Macaulay modules of finite support dimension

Stacks Project tag **00N3**, in `commalg.tex`, section "Cohen-Macaulay modules",
defines a finite module over a Noetherian local ring to be Cohen--Macaulay when its
depth equals the dimension of its support.  Mathlib does not yet bundle depth as a
numerical invariant.  For a specified finite support dimension `d`, Rees's theorem
expresses the same condition as Ext-vanishing below `d`; this is the formulation used
here.

The unindexed predicate existentially packages the finite support dimension.  The
dimension-indexed predicate is the useful induction interface: quotienting by a regular
element changes the index from `d + 1` to `d`.

Main declarations:

* `Module.IsCohenMacaulayOfDimension`;
* `Module.IsCohenMacaulay`;
* `Module.IsCohenMacaulayOfDimension.of_isRegular`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u v

open IsLocalRing

namespace Module

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
  [Small.{v} R] [IsLocalRing R]

/-- **Stacks 00N3** (`commalg-definition-CM`), finite-dimensional form.  A module whose
support has dimension `d` is Cohen--Macaulay when its Ext-depth along the maximal ideal
is at least `d`.  Rees's theorem identifies the second condition with the existence of
a regular sequence of length `d` in the maximal ideal. -/
@[stacks 00N3]
def IsCohenMacaulayOfDimension (d : ℕ) : Prop :=
  supportDim R M = (d : WithBot ℕ∞) ∧
    ModuleCat.ExtDepthAtLeast (maximalIdeal R) (ModuleCat.of R M) d

/-- A finite-dimensional module is Cohen--Macaulay if it is Cohen--Macaulay of some
natural-number support dimension. -/
def IsCohenMacaulay : Prop :=
  ∃ d : ℕ, IsCohenMacaulayOfDimension R M d

namespace IsCohenMacaulayOfDimension

variable {R M}

/-- The support-dimension equality contained in the indexed Cohen--Macaulay predicate. -/
theorem supportDim_eq {d : ℕ} (h : IsCohenMacaulayOfDimension R M d) :
    supportDim R M = (d : WithBot ℕ∞) :=
  h.1

/-- The maximal-ideal Ext-depth bound contained in the indexed Cohen--Macaulay predicate. -/
theorem extDepthAtLeast {d : ℕ} (h : IsCohenMacaulayOfDimension R M d) :
    ModuleCat.ExtDepthAtLeast (maximalIdeal R) (ModuleCat.of R M) d :=
  h.2

/-- A maximal-ideal regular sequence whose length equals the support dimension exhibits
a finite module as Cohen--Macaulay. -/
theorem of_isRegular [IsNoetherianRing R] [Module.Finite R M] [Nontrivial M]
    {d : ℕ} (hdim : supportDim R M = (d : WithBot ℕ∞))
    (rs : List R) (hlen : rs.length = d)
    (hmem : ∀ x ∈ rs, x ∈ maximalIdeal R)
    (hreg : RingTheory.Sequence.IsRegular M rs) :
    IsCohenMacaulayOfDimension R M d := by
  refine ⟨hdim, ?_⟩
  have hsmul : maximalIdeal R • (⊤ : Submodule R M) < ⊤ := by
    rw [← IsLocalRing.ringJacobson_eq_maximalIdeal]
    exact Submodule.jacobson_smul_lt_top _
  apply (ModuleCat.extDepthAtLeast_iff_exists_isRegular
    (maximalIdeal R) (ModuleCat.of R M) d hsmul).mpr
  exact ⟨rs, hlen, hmem, hreg⟩

end IsCohenMacaulayOfDimension

end Module

end

end
