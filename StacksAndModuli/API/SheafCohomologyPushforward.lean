module

public import StacksAndModuli.API.SheafCohomologyModule
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Topology.Sheaves.Functors

/-!
# The canonical cohomology map from a pushforward

For a morphism of schemes `f : X ⟶ Y` and an `𝒪_X`-module `M`, this file constructs the
canonical map

`Hⁿ(Y, f_* M) ⟶ Hⁿ(X, M)`.

On underlying abelian sheaves, the construction applies the exact inverse-image functor to an
`Ext` class, identifies the inverse image of the constant sheaf with the constant sheaf, and
then postcomposes with the counit `f⁻¹ f_* M ⟶ M`.  The map is semilinear for pullback of
global functions and linear over a common affine base respected by `f`.

This file deliberately does not claim that the canonical map is an equivalence.  For an affine
morphism and a quasicoherent module, that assertion requires affine acyclicity (or an equivalent
Leray/Čech-to-derived comparison), which is not currently available in Mathlib.  Instead,
`h_pushforward_eq_of_bijective` isolates the precise missing input as bijectivity of the canonical
map; it does not ask the caller to supply an unrelated equivalence.

## Main definitions and results

* `TopCat.Sheaf.pullbackConstantAddCommGrpIso`: inverse image preserves constant abelian sheaves.
* `AlgebraicGeometry.Scheme.Modules.pushforwardCohomologyMap`: the canonical additive map.
* `AlgebraicGeometry.Scheme.Modules.pushforwardCohomologyMap_smul`: semilinearity for global
  functions.
* `AlgebraicGeometry.Scheme.Modules.pushforwardCohomologyLinearMap`: linearity over a common base.
* `AlgebraicGeometry.Scheme.Modules.h_pushforward_eq_of_bijective`: bijectivity of the canonical
  map implies equality of cohomology dimensions.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace TopCat.Sheaf

attribute [local instance] reflectsLimits_of_reflectsIsomorphisms

variable {S T : TopCat.{u}} (g : S ⟶ T)

/-- Taking sections over the top open after pushforward is definitionally taking sections over
the top open of the source. -/
noncomputable def pushforwardSectionsTopIso :
    pushforward AddCommGrpCat.{u} g ⋙
        (sheafSections (Opens.grothendieckTopology T) AddCommGrpCat.{u}).obj
          (Opposite.op (⊤ : Opens T)) ≅
      (sheafSections (Opens.grothendieckTopology S) AddCommGrpCat.{u}).obj
        (Opposite.op (⊤ : Opens S)) :=
  Iso.refl _

/-- The inverse image of a constant sheaf of abelian groups is canonically constant.

Both sides are left adjoint to sections over the top open, so this is the uniqueness
isomorphism between left adjoints. -/
noncomputable def pullbackConstantAddCommGrpIso :
    constantSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u} ⋙
        pullback AddCommGrpCat.{u} g ≅
      constantSheaf (Opens.grothendieckTopology S) AddCommGrpCat.{u} := by
  let adj := (constantSheafAdj (Opens.grothendieckTopology T)
      AddCommGrpCat.{u} (isTerminalTop : IsTerminal (⊤ : Opens T))).comp
    (pullbackPushforwardAdjunction AddCommGrpCat.{u} g)
  let adj' := adj.ofNatIsoRight (pushforwardSectionsTopIso g)
  exact adj'.leftAdjointUniq
    (constantSheafAdj (Opens.grothendieckTopology S)
      AddCommGrpCat.{u} (isTerminalTop : IsTerminal (⊤ : Opens S)))

/-- Inverse image of abelian sheaves preserves finite limits. -/
instance pullback_preservesFiniteLimits_addCommGrp :
    PreservesFiniteLimits (pullback AddCommGrpCat.{u} g) :=
  CategoryTheory.Functor.sheafPullbackConstruction.preservesFiniteLimits
    (Opens.map g) AddCommGrpCat.{u}
      (Opens.grothendieckTopology T) (Opens.grothendieckTopology S)

set_option linter.style.haveILetI false in
/-- Inverse image of abelian sheaves is additive. -/
instance pullback_additive_addCommGrp :
    (pullback AddCommGrpCat.{u} g).Additive := by
  letI := preservesBinaryBiproducts_of_preservesBinaryProducts
    (pullback AddCommGrpCat.{u} g)
  exact Functor.additive_of_preservesBinaryBiproducts _

end TopCat.Sheaf

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Pushforward carries multiplication by the pullback of a global function to multiplication
by that function on the pushed-forward module. -/
lemma pushforward_map_smulSheafHom (M : X.Modules) (r : Γ(Y, ⊤)) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).map
        (smulSheafHom M (f.appTop r)) =
      smulSheafHom ((pushforward f).obj M) r := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U ↦ ?_))
  refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
  change (M.smul (restrictTop X (f ⁻¹ᵁ U.unop) (f.appTop r))).hom x =
    (M.smul (f.app U.unop (restrictTop Y U.unop r))).hom x
  exact congrArg (fun q ↦ (M.smul q).hom x)
    (ConcreteCategory.congr_hom (f.naturality (Opens.leTop U.unop).op) r).symm

/-- The counit of inverse image and pushforward intertwines multiplication by corresponding
global functions. -/
lemma pullbackPushforwardCounit_smul (M : X.Modules) (r : Γ(Y, ⊤)) :
    (TopCat.Sheaf.pullback AddCommGrpCat.{u} f.base).map
          (smulSheafHom ((pushforward f).obj M) r) ≫
        (TopCat.Sheaf.pullbackPushforwardAdjunction
          AddCommGrpCat.{u} f.base).counit.app
            ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) =
      (TopCat.Sheaf.pullbackPushforwardAdjunction
          AddCommGrpCat.{u} f.base).counit.app
            ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) ≫
        smulSheafHom M (f.appTop r) := by
  rw [← pushforward_map_smulSheafHom f M r]
  exact (TopCat.Sheaf.pullbackPushforwardAdjunction
    AddCommGrpCat.{u} f.base).counit.naturality
      (smulSheafHom M (f.appTop r))

/-- The part of the pushforward cohomology map obtained by applying the exact inverse-image
functor to an `Ext` class. -/
noncomputable def pushforwardCohomologyPullbackMap (M : X.Modules) (n : ℕ) :
    H ((pushforward f).obj M) n →+
      Abelian.Ext
        ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f.base).obj
          ((constantSheaf (Opens.grothendieckTopology Y)
            AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))))
        ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f.base).obj
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).obj
            ((SheafOfModules.toSheaf X.ringCatSheaf).obj M))) n :=
  (TopCat.Sheaf.pullback AddCommGrpCat.{u} f.base).mapExtAddHom
    ((constantSheaf (Opens.grothendieckTopology Y)
      AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ)))
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).obj
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)) n

/-- Applying inverse image to an `Ext` class commutes with postcomposition by a morphism. -/
lemma pushforwardCohomologyPullbackMap_comp (M : X.Modules) (n : ℕ)
    (x : H ((pushforward f).obj M) n)
    (q : End ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).obj
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M))) :
    pushforwardCohomologyPullbackMap f M n
        (x.comp (Abelian.Ext.mk₀ q) (add_zero n)) =
      (pushforwardCohomologyPullbackMap f M n x).comp
        (Abelian.Ext.mk₀
          ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f.base).map q))
        (add_zero n) := by
  let P := TopCat.Sheaf.pullback AddCommGrpCat.{u} f.base
  let hP : P.Additive := TopCat.Sheaf.pullback_additive_addCommGrp f.base
  let hL : PreservesFiniteLimits P :=
    TopCat.Sheaf.pullback_preservesFiniteLimits_addCommGrp f.base
  let hC : PreservesFiniteColimits P := by infer_instance
  change (@Abelian.Ext.mapExactFunctor _ _ _ _ _ _ P hP hL hC
    (by infer_instance) (by infer_instance) _ _ _
      (x.comp (Abelian.Ext.mk₀ q) (add_zero n))) = _
  rw [@Abelian.Ext.mapExactFunctor_comp _ _ _ _ _ _ P hP hL hC
    (by infer_instance) (by infer_instance) _ _ _ _ _ x
      (Abelian.Ext.mk₀ q) _ (add_zero n)]
  rw [@Abelian.Ext.mapExactFunctor_mk₀ _ _ _ _ _ _ P hP hL hC
    (by infer_instance) (by infer_instance) _ _ q]
  rfl

/-- The canonical cohomology map `Hⁿ(Y, f_* M) ⟶ Hⁿ(X, M)`.

It is the Leray edge map constructed directly in `Ext`: apply the exact inverse-image functor,
precompose with the inverse-image comparison for the constant sheaf, and postcompose with the
inverse-image--pushforward counit. -/
noncomputable def pushforwardCohomologyMap (M : X.Modules) (n : ℕ) :
    H ((pushforward f).obj M) n →+ H M n := by
  let c := (TopCat.Sheaf.pullbackConstantAddCommGrpIso f.base).app
    (AddCommGrpCat.of (ULift ℤ))
  let ε := (TopCat.Sheaf.pullbackPushforwardAdjunction
    AddCommGrpCat.{u} f.base).counit.app
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)
  exact ((Abelian.Ext.mk₀ ε).postcomp _ (add_zero n)).comp
    (((Abelian.Ext.mk₀ c.inv).precomp _ (zero_add n)).comp
      (pushforwardCohomologyPullbackMap f M n))

/-- Formula for the canonical pushforward cohomology map in terms of `Ext` composition. -/
lemma pushforwardCohomologyMap_apply (M : X.Modules) (n : ℕ)
    (x : H ((pushforward f).obj M) n) :
    pushforwardCohomologyMap f M n x =
      ((Abelian.Ext.mk₀
          ((TopCat.Sheaf.pullbackConstantAddCommGrpIso f.base).app
            (AddCommGrpCat.of (ULift ℤ))).inv).comp
        (pushforwardCohomologyPullbackMap f M n x) (zero_add n)).comp
        (Abelian.Ext.mk₀
          ((TopCat.Sheaf.pullbackPushforwardAdjunction
            AddCommGrpCat.{u} f.base).counit.app
              ((SheafOfModules.toSheaf X.ringCatSheaf).obj M))) (add_zero n) :=
  rfl

/-- The canonical pushforward cohomology map is semilinear for pullback of global functions. -/
lemma pushforwardCohomologyMap_smul (M : X.Modules) (n : ℕ)
    (r : Γ(Y, ⊤)) (x : H ((pushforward f).obj M) n) :
    pushforwardCohomologyMap f M n (r • x) =
      f.appTop r • pushforwardCohomologyMap f M n x := by
  simp only [smul_def, pushforwardCohomologyMap_apply,
    pushforwardCohomologyPullbackMap_comp]
  simp only [Abelian.Ext.comp_assoc_of_second_deg_zero,
    Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀]
  rw [pullbackPushforwardCounit_smul f M r]

/-- For a morphism over a common affine base, the canonical pushforward cohomology map is
linear over the base ring. -/
noncomputable def pushforwardCohomologyLinearMap
    (k : Type u) [CommRing k]
    [X.Over (Spec (CommRingCat.of k))]
    [Y.Over (Spec (CommRingCat.of k))]
    (hf : f ≫ (Y ↘ Spec (CommRingCat.of k)) =
      X ↘ Spec (CommRingCat.of k))
    (M : X.Modules) (n : ℕ) :
    H ((pushforward f).obj M) n →ₗ[k] H M n where
  __ := pushforwardCohomologyMap f M n
  map_smul' a x := by
    have hring : baseRingHom (Y ↘ Spec (CommRingCat.of k)) ≫ f.appTop =
        baseRingHom (X ↘ Spec (CommRingCat.of k)) :=
      (baseRingHom_comp_appTop f (Y ↘ Spec (CommRingCat.of k))).trans
        (congrArg baseRingHom hf)
    have hbase : f.appTop (Y.baseRingHom (CommRingCat.of k) a) =
        X.baseRingHom (CommRingCat.of k) a :=
      ConcreteCategory.congr_hom hring a
    calc
      pushforwardCohomologyMap f M n (a • x) =
          pushforwardCohomologyMap f M n
            (Y.baseRingHom (CommRingCat.of k) a • x) :=
        congrArg (pushforwardCohomologyMap f M n)
          (base_smul_eq_globalSections_smul ((pushforward f).obj M) n a x)
      _ = f.appTop (Y.baseRingHom (CommRingCat.of k) a) •
          pushforwardCohomologyMap f M n x :=
        pushforwardCohomologyMap_smul f M n _ x
      _ = X.baseRingHom (CommRingCat.of k) a •
          pushforwardCohomologyMap f M n x := congrArg
        (fun r ↦ r • pushforwardCohomologyMap f M n x) hbase
      _ = a • pushforwardCohomologyMap f M n x :=
        (base_smul_eq_globalSections_smul M n a _).symm

/-- A bijective canonical pushforward cohomology map upgrades to a base-linear equivalence. -/
noncomputable def pushforwardCohomologyLinearEquivOfBijective
    (k : Type u) [CommRing k]
    [X.Over (Spec (CommRingCat.of k))]
    [Y.Over (Spec (CommRingCat.of k))]
    (hf : f ≫ (Y ↘ Spec (CommRingCat.of k)) =
      X ↘ Spec (CommRingCat.of k))
    (M : X.Modules) (n : ℕ)
    (hb : Function.Bijective (pushforwardCohomologyMap f M n)) :
    H ((pushforward f).obj M) n ≃ₗ[k] H M n :=
  LinearEquiv.ofBijective (pushforwardCohomologyLinearMap f k hf M n) hb

/-- Finite dimensionality transfers from a module to its pushforward when the canonical
cohomology map is bijective. -/
lemma finiteDimensional_H_pushforward_of_bijective
    (k : Type u) [Field k]
    [X.Over (Spec (CommRingCat.of k))]
    [Y.Over (Spec (CommRingCat.of k))]
    (hf : f ≫ (Y ↘ Spec (CommRingCat.of k)) =
      X ↘ Spec (CommRingCat.of k))
    (M : X.Modules) (n : ℕ)
    (hb : Function.Bijective (pushforwardCohomologyMap f M n))
    [FiniteDimensional k (H M n)] :
    FiniteDimensional k (H ((pushforward f).obj M) n) :=
  Module.Finite.equiv
    (pushforwardCohomologyLinearEquivOfBijective f k hf M n hb).symm

/-- If the canonical pushforward cohomology map is bijective, pushforward preserves the
corresponding cohomology dimension over a field. -/
lemma h_pushforward_eq_of_bijective
    (k : Type u) [Field k]
    [X.Over (Spec (CommRingCat.of k))]
    [Y.Over (Spec (CommRingCat.of k))]
    (hf : f ≫ (Y ↘ Spec (CommRingCat.of k)) =
      X ↘ Spec (CommRingCat.of k))
    (M : X.Modules) (n : ℕ)
    (hb : Function.Bijective (pushforwardCohomologyMap f M n)) :
    h k ((pushforward f).obj M) n = h k M n :=
  (pushforwardCohomologyLinearEquivOfBijective f k hf M n hb).finrank_eq

end AlgebraicGeometry.Scheme.Modules
