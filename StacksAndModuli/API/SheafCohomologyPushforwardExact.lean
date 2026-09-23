module

public import StacksAndModuli.API.ExtAdjunction
public import StacksAndModuli.API.SheafCohomologyPushforwardDegreeZero
public import StacksAndModuli.API.SheafCohomologySchemeIso

/-!
# Sheaf cohomology and exact pushforward

For a continuous map `g : S ⟶ T`, exactness of pushforward on abelian sheaves makes the
canonical comparison

`Hⁿ(T, g_* F) ⟶ Hⁿ(S, F)`

an additive equivalence in every degree.  This is the counit direction of the Ext
adjunction: apply inverse image to an Ext class, postcompose with the
inverse-image--pushforward counit, and transport the constant source sheaf across its
canonical isomorphism.

The application lemmas identify this construction with the canonical maps already defined
in `SheafCohomologyPushforwardDegreeZero.lean` and
`SheafCohomologyPushforward.lean`.  In particular, the scheme-module theorem proves
bijectivity of `AlgebraicGeometry.Scheme.Modules.pushforwardCohomologyMap` itself.

This theorem does not directly apply to an affine morphism with a quasicoherent
coefficient: affine pushforward is exact on quasicoherent modules, whereas the hypothesis
here concerns its action on all abelian sheaves.  Bridging that gap still requires affine
quasicoherent acyclicity or a derived comparison for the quasicoherent inclusion.

## Main results

* `TopCat.Sheaf.pushforwardCohomologyMapExactAddEquiv`: cohomology comparison for an
  exact pushforward of abelian sheaves.
* `AlgebraicGeometry.Scheme.Modules.pushforwardCohomologyMapExactAddEquiv`: the same
  comparison for the underlying abelian sheaf of a scheme module.
* `AlgebraicGeometry.Scheme.Modules.pushforwardCohomologyMap_bijective_of_exact`:
  bijectivity of the canonical scheme-module pushforward cohomology map.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace TopCat.Sheaf

attribute [local instance] reflectsLimits_of_reflectsIsomorphisms

variable {S T : TopCat.{u}} (g : S ⟶ T)

/-- If pushforward of abelian sheaves along `g` is exact, its canonical cohomology map is
an additive equivalence in every degree. -/
noncomputable def pushforwardCohomologyMapExactAddEquiv
    (F : Sheaf AddCommGrpCat.{u} S) (n : ℕ)
    [PreservesFiniteColimits (pushforward AddCommGrpCat.{u} g)] :
    CategoryTheory.Sheaf.H
        ((pushforward AddCommGrpCat.{u} g).obj F) n ≃+
      CategoryTheory.Sheaf.H F n := by
  let L := pullback AddCommGrpCat.{u} g
  let R := pushforward AddCommGrpCat.{u} g
  let adj := pullbackPushforwardAdjunction AddCommGrpCat.{u} g
  let c := (pullbackConstantAddCommGrpIso g).app
    (AddCommGrpCat.of (ULift ℤ))
  let _ : L.Additive := pullback_additive_addCommGrp g
  let _ : R.Additive := adj.right_adjoint_additive
  let _ : PreservesFiniteLimits L :=
    pullback_preservesFiniteLimits_addCommGrp g
  let _ : L.PreservesMonomorphisms := by infer_instance
  exact (adj.extAddEquivInv
    ((constantSheaf (Opens.grothendieckTopology T)
      AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))) F n).trans
        (CategoryTheory.Abelian.Ext.isoAddEquiv c (Iso.refl _) n)

/-- The exact-pushforward equivalence has the repository's canonical pushforward
cohomology map as its underlying function. -/
@[simp]
lemma pushforwardCohomologyMapExactAddEquiv_apply
    (F : Sheaf AddCommGrpCat.{u} S) (n : ℕ)
    [PreservesFiniteColimits (pushforward AddCommGrpCat.{u} g)]
    (x : CategoryTheory.Sheaf.H
      ((pushforward AddCommGrpCat.{u} g).obj F) n) :
    pushforwardCohomologyMapExactAddEquiv g F n x =
      pushforwardCohomologyMap g F n x := by
  let L := pullback AddCommGrpCat.{u} g
  let R := pushforward AddCommGrpCat.{u} g
  let adj := pullbackPushforwardAdjunction AddCommGrpCat.{u} g
  let _ : L.Additive := pullback_additive_addCommGrp g
  let _ : R.Additive := adj.right_adjoint_additive
  let _ : PreservesFiniteLimits L :=
    pullback_preservesFiniteLimits_addCommGrp g
  let _ : L.PreservesMonomorphisms := by infer_instance
  simp only [pushforwardCohomologyMapExactAddEquiv, AddEquiv.trans_apply,
    CategoryTheory.Adjunction.extAddEquivInv_apply,
    CategoryTheory.Adjunction.extAddHomInv_apply]
  erw [CategoryTheory.Abelian.Ext.isoAddEquiv_apply]
  simp only [Iso.refl_hom, CategoryTheory.Abelian.Ext.comp_mk₀_id]
  rw [← CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero]
  rfl

/-- If pushforward of abelian sheaves along `g` is exact, the canonical pushforward
cohomology map is bijective in every degree. -/
lemma pushforwardCohomologyMap_bijective_of_exact
    (F : Sheaf AddCommGrpCat.{u} S) (n : ℕ)
    [PreservesFiniteColimits (pushforward AddCommGrpCat.{u} g)] :
    Function.Bijective (pushforwardCohomologyMap g F n) := by
  rw [← funext (pushforwardCohomologyMapExactAddEquiv_apply g F n)]
  exact (pushforwardCohomologyMapExactAddEquiv g F n).bijective

end TopCat.Sheaf

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- If pushforward of abelian sheaves along the underlying continuous map of `f` is
exact, the canonical scheme-module pushforward comparison is an additive equivalence. -/
noncomputable def pushforwardCohomologyMapExactAddEquiv
    (M : X.Modules) (n : ℕ)
    [PreservesFiniteColimits
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base)] :
    H ((pushforward f).obj M) n ≃+ H M n :=
  TopCat.Sheaf.pushforwardCohomologyMapExactAddEquiv f.base
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) n

/-- The scheme-module exact-pushforward equivalence has
`Modules.pushforwardCohomologyMap` as its underlying function. -/
@[simp]
lemma pushforwardCohomologyMapExactAddEquiv_apply
    (M : X.Modules) (n : ℕ)
    [PreservesFiniteColimits
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base)]
    (x : H ((pushforward f).obj M) n) :
    pushforwardCohomologyMapExactAddEquiv f M n x =
      pushforwardCohomologyMap f M n x := by
  change TopCat.Sheaf.pushforwardCohomologyMapExactAddEquiv f.base
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) n x =
    TopCat.Sheaf.pushforwardCohomologyMap f.base
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) n x
  apply TopCat.Sheaf.pushforwardCohomologyMapExactAddEquiv_apply

/-- If pushforward of abelian sheaves along the underlying continuous map of `f` is
exact, `Modules.pushforwardCohomologyMap` is bijective in every degree. -/
lemma pushforwardCohomologyMap_bijective_of_exact
    (M : X.Modules) (n : ℕ)
    [PreservesFiniteColimits
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base)] :
    Function.Bijective (pushforwardCohomologyMap f M n) := by
  rw [← funext (pushforwardCohomologyMapExactAddEquiv_apply f M n)]
  exact (pushforwardCohomologyMapExactAddEquiv f M n).bijective

end AlgebraicGeometry.Scheme.Modules
