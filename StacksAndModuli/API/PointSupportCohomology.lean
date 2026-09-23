module

public import StacksAndModuli.API.FlasqueVanishing
public import StacksAndModuli.API.GlobalSectionsField
public import StacksAndModuli.API.ProjectiveTwistedFreeGlobalSectionsFinite
public import StacksAndModuli.API.SheafCohomologyFiniteCoproduct
public import StacksAndModuli.API.SheafCohomologyPushforwardZero
public import StacksAndModuli.API.SheafCohomologySchemeIso
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# Cohomology of modules supported at points

For a point `x : X`, its canonical residue-field morphism
`Spec κ(x) ⟶ X` gives an `𝒪_X`-module by pushing forward the structure module of
`Spec κ(x)`.  This file computes the cohomology of that module.  More generally, it treats
pushforwards from arbitrary one-point schemes, rational points, and finite direct sums of
point-supported modules.

The key observation is that every abelian sheaf on a one-point space is flasque and that
pushforward preserves flasqueness.  Thus every positive cohomology group vanishes.  For a
closed point on a scheme locally of finite type over an algebraically closed field `k`,
Mathlib identifies the residue field with `k`; the degree-zero cohomology then has
`k`-dimension one.  A finite direct sum has degree-zero dimension equal to the number of
summands and the same positive-degree vanishing.

These results are intended for finite-length defects, such as those occurring near nodes.
Nothing in this file identifies a point-supported module with a normalization cokernel;
such an identification requires a separate global exact-sequence theorem.

## Main definitions

* `AlgebraicGeometry.Scheme.residuePointSupportModule`: the pushforward from
  `Spec κ(x)` along the canonical residue-field point.
* `AlgebraicGeometry.Scheme.Hom.pointSupportModule`: the pushforward from a rational
  point `Spec k ⟶ X`.
* `AlgebraicGeometry.Scheme.finiteResiduePointSupportModule`: a finite direct sum of
  residue-point modules.

## Main results

* `AlgebraicGeometry.Scheme.residuePointSupportHZeroAddEquiv`: `H⁰` of the canonical
  residue-point module is additively equivalent to `κ(x)`.
* `AlgebraicGeometry.Scheme.subsingleton_H_residuePointSupportModule`: all positive
  cohomology of a residue-point module vanishes.
* `AlgebraicGeometry.Scheme.h_residuePointSupportModule_zero_of_isClosed`: over an
  algebraically closed field, a closed residue point contributes one to `h⁰`.
* `AlgebraicGeometry.Scheme.h_finiteResiduePointSupportModule_zero_of_isClosed`: a finite
  direct sum of closed residue points contributes its number of summands to `h⁰`.
* `AlgebraicGeometry.Scheme.finiteResiduePointSupportHZeroLinearEquivOfIsClosed`: the
  corresponding linear equivalence `H⁰ ≃ₗ[k] (J → k)`.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

namespace Modules

/-- Global sections of a pushed-forward module are additively equivalent to the original
global sections, without choosing a common base ring. -/
noncomputable def pushforwardGlobalSectionsAddEquiv
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : X.Modules) :
    Γ((pushforward f).obj M, ⊤) ≃+ Γ(M, ⊤) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Degree-zero cohomology is additively invariant under pushforward.  This is the
base-free counterpart of `pushforwardGlobalSectionsLinearEquiv`. -/
noncomputable def HZeroPushforwardAddEquiv
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : X.Modules) :
    H ((pushforward f).obj M) 0 ≃+ H M 0 :=
  (HZeroLinearEquiv ((pushforward f).obj M)).toAddEquiv |>.trans
    (pushforwardGlobalSectionsAddEquiv f M) |>.trans
      (HZeroLinearEquiv M).symm.toAddEquiv

/-- A module pushed forward from a scheme with at most one point has vanishing positive
cohomology.  Indeed, every sheaf on the source is flasque, and pushforward preserves
flasqueness. -/
lemma subsingleton_H_pushforward_of_subsingleton
    {X Y : Scheme.{u}} [Subsingleton X] (f : X ⟶ Y) (M : X.Modules) (n : ℕ) :
    Subsingleton (H ((pushforward f).obj M) (n + 1)) := by
  apply subsingleton_H_of_isFlasque
  let F : TopCat.Sheaf AddCommGrpCat.{u} X :=
    (SheafOfModules.toSheaf X.ringCatSheaf).obj M
  let _ : F.IsFlasque := TopCat.Sheaf.isFlasque_of_subsingleton F
  exact TopCat.Sheaf.IsFlasque.pushforward_isFlasque F f.base

end Modules

/-- The canonical point-supported module at `x`: the structure module on `Spec κ(x)`,
pushed forward along `X.fromSpecResidueField x`. -/
noncomputable abbrev residuePointSupportModule (X : Scheme.{u}) (x : X) : X.Modules :=
  (Modules.pushforward (X.fromSpecResidueField x)).obj
    (structureModule (Spec (X.residueField x)))

/-- Degree-zero cohomology of the canonical residue-point module is the residue field as
an additive group.  No base field for `X` is required. -/
noncomputable def residuePointSupportHZeroAddEquiv (X : Scheme.{u}) (x : X) :
    Modules.H (residuePointSupportModule X x) 0 ≃+ X.residueField x := by
  exact (Modules.HZeroPushforwardAddEquiv (X.fromSpecResidueField x)
      (structureModule (Spec (X.residueField x)))).trans <|
    (Modules.HZeroLinearEquiv
      (structureModule (Spec (X.residueField x)))).toAddEquiv |>.trans <|
        (Modules.structureModuleSectionsEquiv
          (Spec (X.residueField x)) ⊤).toAddEquiv |>.trans <|
          (Scheme.ΓSpecIso (X.residueField x)).commRingCatIsoToRingEquiv.toAddEquiv

/-- Every positive cohomology group of the canonical residue-point module is trivial. -/
lemma subsingleton_H_residuePointSupportModule (X : Scheme.{u}) (x : X) (n : ℕ) :
    Subsingleton (Modules.H (residuePointSupportModule X x) (n + 1)) :=
  Modules.subsingleton_H_pushforward_of_subsingleton
    (X.fromSpecResidueField x) _ n

/-- Over any field of definition for `X`, every positive cohomology dimension of the
canonical residue-point module is zero. -/
lemma h_residuePointSupportModule_succ_eq_zero
    {k : Type u} [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] (x : X) (n : ℕ) :
    Modules.h k (residuePointSupportModule X x) (n + 1) = 0 :=
  Modules.h_eq_zero_of_subsingleton k _ _
    (subsingleton_H_residuePointSupportModule X x n)

/-- The structure module on `Spec k`, pushed forward along a `k`-valued point. -/
noncomputable abbrev Hom.pointSupportModule {k : Type u} [Field k]
    {X : Scheme.{u}} (s : Spec (CommRingCat.of k) ⟶ X) : X.Modules :=
  (Modules.pushforward s).obj (structureModule (Spec (CommRingCat.of k)))

/-- Every positive cohomology group of a rational-point module is trivial. -/
lemma Hom.subsingleton_H_pointSupportModule {k : Type u} [Field k]
    {X : Scheme.{u}} (s : Spec (CommRingCat.of k) ⟶ X) (n : ℕ) :
    Subsingleton (Modules.H s.pointSupportModule (n + 1)) :=
  Modules.subsingleton_H_pushforward_of_subsingleton s _ n

/-- Every positive cohomology dimension of a rational-point module is zero. -/
lemma Hom.h_pointSupportModule_succ_eq_zero {k : Type u} [Field k]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    (s : Spec (CommRingCat.of k) ⟶ X) (n : ℕ) :
    Modules.h k s.pointSupportModule (n + 1) = 0 :=
  Modules.h_eq_zero_of_subsingleton k _ _ (s.subsingleton_H_pointSupportModule n)

/-- A rational point respecting the `k`-scheme structures contributes one to degree-zero
cohomology. -/
lemma Hom.h_pointSupportModule_zero {k : Type u} [Field k]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    (s : Spec (CommRingCat.of k) ⟶ X)
    (hs : s ≫ (X ↘ Spec (CommRingCat.of k)) =
      Spec (CommRingCat.of k) ↘ Spec (CommRingCat.of k)) :
    Modules.h k s.pointSupportModule 0 = 1 := by
  rw [Modules.h_zero_pushforward_eq k s hs]
  exact h_structureModule_spec_zero k

/-- The two-term Euler characteristic of a rational-point module is one. -/
lemma Hom.eulerChar_pointSupportModule {k : Type u} [Field k]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    (s : Spec (CommRingCat.of k) ⟶ X)
    (hs : s ≫ (X ↘ Spec (CommRingCat.of k)) =
      Spec (CommRingCat.of k) ↘ Spec (CommRingCat.of k)) :
    Modules.eulerChar k s.pointSupportModule = 1 := by
  rw [Modules.eulerChar_def, s.h_pointSupportModule_zero hs,
    s.h_pointSupportModule_succ_eq_zero 0]
  norm_num

/-- Global sections of a rational-point module are linearly equivalent to the ground
field when the point respects the `k`-scheme structures. -/
noncomputable def Hom.pointSupportGlobalSectionsLinearEquiv
    {k : Type u} [Field k]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    (s : Spec (CommRingCat.of k) ⟶ X)
    (hs : s ≫ (X ↘ Spec (CommRingCat.of k)) =
      Spec (CommRingCat.of k) ↘ Spec (CommRingCat.of k)) :
    letI := Modules.globalSectionsModule
      (X ↘ Spec (CommRingCat.of k)) s.pointSupportModule
    Γ(s.pointSupportModule, ⊤) ≃ₗ[k] k := by
  letI := Modules.globalSectionsModule
    (X ↘ Spec (CommRingCat.of k)) s.pointSupportModule
  letI := Modules.globalSectionsModule
    (Spec (CommRingCat.of k) ↘ Spec (CommRingCat.of k))
      (structureModule (Spec (CommRingCat.of k)))
  letI : IsScalarTower k Γ(Spec (CommRingCat.of k), ⊤)
      Γ(structureModule (Spec (CommRingCat.of k)), ⊤) :=
    Modules.isScalarTower_globalSections k _
  exact (Modules.pushforwardGlobalSectionsLinearEquiv s _ _ hs _).trans <|
    (LinearEquiv.restrictScalars k
      (Modules.structureModuleSectionsEquiv (Spec (CommRingCat.of k)) ⊤)).trans <|
      (LinearEquiv.ofBijective
        (Algebra.linearMap k Γ(Spec (CommRingCat.of k), ⊤))
        (bijective_baseRingHom_spec (CommRingCat.of k))).symm

/-- The finite direct sum of modules pushed forward from rational points.  Repeated points
are retained as repeated summands. -/
noncomputable abbrev finitePointSupportModule
    {k : Type u} [Field k] {X : Scheme.{u}}
    {J : Type u} [Finite J]
    (s : J → (Spec (CommRingCat.of k) ⟶ X)) : X.Modules :=
  ∐ fun j ↦ (s j).pointSupportModule

/-- Every positive cohomology group of a finite direct sum of rational-point modules is
trivial. -/
lemma subsingleton_H_finitePointSupportModule
    {k : Type u} [Field k] {X : Scheme.{u}}
    {J : Type u} [Finite J]
    (s : J → (Spec (CommRingCat.of k) ⟶ X)) (n : ℕ) :
    Subsingleton (Modules.H (finitePointSupportModule s) (n + 1)) := by
  apply Modules.subsingleton_H_coproduct_of_finite
  intro j
  exact (s j).subsingleton_H_pointSupportModule n

/-- Every positive cohomology dimension of a finite direct sum of rational-point modules
is zero. -/
lemma h_finitePointSupportModule_succ_eq_zero
    {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))]
    {J : Type u} [Finite J]
    (s : J → (Spec (CommRingCat.of k) ⟶ X)) (n : ℕ) :
    Modules.h k (finitePointSupportModule s) (n + 1) = 0 :=
  Modules.h_eq_zero_of_subsingleton k _ _
    (subsingleton_H_finitePointSupportModule s n)

/-- The degree-zero cohomology dimension of a finite direct sum of `k`-rational-point
modules is the number of summands. -/
lemma h_finitePointSupportModule_zero
    {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))]
    {J : Type u} [Fintype J]
    (s : J → (Spec (CommRingCat.of k) ⟶ X))
    (hs : ∀ j, s j ≫ (X ↘ Spec (CommRingCat.of k)) =
      Spec (CommRingCat.of k) ↘ Spec (CommRingCat.of k)) :
    Modules.h k (finitePointSupportModule s) 0 = Fintype.card J := by
  let p := X ↘ Spec (CommRingCat.of k)
  let _ (j : J) := Modules.globalSectionsModule p (s j).pointSupportModule
  let _ := Modules.globalSectionsModule p (finitePointSupportModule s)
  rw [Modules.h_zero_eq_finrank_globalSections,
    (Modules.globalSectionsFiniteCoproductLinearEquiv p
      (fun j ↦ (s j).pointSupportModule)).finrank_eq]
  let e : (∀ j, Γ((s j).pointSupportModule, ⊤)) ≃ₗ[k] (J → k) :=
    LinearEquiv.piCongrRight fun j ↦
      (s j).pointSupportGlobalSectionsLinearEquiv (hs j)
  rw [e.finrank_eq, Module.finrank_pi]

/-- The two-term Euler characteristic of a finite direct sum of rational-point modules is
the number of summands. -/
lemma eulerChar_finitePointSupportModule
    {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))]
    {J : Type u} [Fintype J]
    (s : J → (Spec (CommRingCat.of k) ⟶ X))
    (hs : ∀ j, s j ≫ (X ↘ Spec (CommRingCat.of k)) =
      Spec (CommRingCat.of k) ↘ Spec (CommRingCat.of k)) :
    Modules.eulerChar k (finitePointSupportModule s) = Fintype.card J := by
  rw [Modules.eulerChar_def, h_finitePointSupportModule_zero s hs,
    h_finitePointSupportModule_succ_eq_zero s 0]
  norm_num

/-- The rational-point model of a closed point on a scheme locally of finite type over an
algebraically closed field. -/
noncomputable abbrev closedPointSupportModule
    {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    (x : X) (hx : IsClosed ({x} : Set X)) : X.Modules :=
  (pointOfClosedPoint (X ↘ Spec (CommRingCat.of k)) x hx).pointSupportModule

/-- At a closed point over an algebraically closed field, the rational-point model is
isomorphic to the canonical residue-point module.

The isomorphism uses Mathlib's `residueFieldIsoBase`.  It is an isomorphism of
`𝒪_X`-modules, not an identification with any normalization quotient. -/
noncomputable def closedPointSupportModuleIsoResidue
    {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    closedPointSupportModule (k := k) x hx ≅ residuePointSupportModule X x := by
  let e : Spec (CommRingCat.of k) ≅ Spec (X.residueField x) :=
    Scheme.Spec.mapIso
      (residueFieldIsoBase (X ↘ Spec (CommRingCat.of k)) x hx).op
  exact (((Modules.pushforward (X.fromSpecResidueField x)).mapIso
    (structureModulePushforwardIso e)) ≪≫
      (Modules.pushforwardComp e.hom (X.fromSpecResidueField x)).app
        (structureModule (Spec (CommRingCat.of k)))).symm

/-- At a closed point over an algebraically closed field, global sections of the canonical
residue-point module are linearly equivalent to the ground field. -/
noncomputable def residuePointSupportGlobalSectionsLinearEquivOfIsClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    letI := Modules.globalSectionsModule
      (X ↘ Spec (CommRingCat.of k)) (residuePointSupportModule X x)
    Γ(residuePointSupportModule X x, ⊤) ≃ₗ[k] k := by
  let p := X ↘ Spec (CommRingCat.of k)
  letI := Modules.globalSectionsModule p (residuePointSupportModule X x)
  letI := Modules.globalSectionsModule p
    (closedPointSupportModule (k := k) x hx)
  exact (Modules.globalSectionsLinearEquivOfIso p
    (closedPointSupportModuleIsoResidue (k := k) x hx)).symm.trans
      ((pointOfClosedPoint p x hx).pointSupportGlobalSectionsLinearEquiv
        (pointOfClosedPoint_comp p x hx))

/-- The rational-point model of a closed point has degree-zero cohomology dimension one. -/
lemma h_closedPointSupportModule_zero
    {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    Modules.h k (closedPointSupportModule (k := k) x hx) 0 = 1 := by
  apply Hom.h_pointSupportModule_zero
  simp

/-- The canonical residue-point module of a closed point over an algebraically closed
field has degree-zero cohomology dimension one. -/
lemma h_residuePointSupportModule_zero_of_isClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    Modules.h k (residuePointSupportModule X x) 0 = 1 := by
  calc
    Modules.h k (residuePointSupportModule X x) 0 =
        Modules.h k (closedPointSupportModule (k := k) x hx) 0 :=
      (Modules.h_eq_of_iso k
        (closedPointSupportModuleIsoResidue (k := k) (X := X) x hx) 0).symm
    _ = 1 := h_closedPointSupportModule_zero (k := k) x hx

/-- The canonical residue-point module of a closed point over an algebraically closed
field has two-term Euler characteristic one. -/
lemma eulerChar_residuePointSupportModule_of_isClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    Modules.eulerChar k (residuePointSupportModule X x) = 1 := by
  rw [Modules.eulerChar_def,
    h_residuePointSupportModule_zero_of_isClosed (k := k) x hx,
    h_residuePointSupportModule_succ_eq_zero (k := k) X x 0]
  norm_num

/-- Every positive cohomology dimension of the rational-point model of a closed point is
zero. -/
lemma h_closedPointSupportModule_succ_eq_zero
    {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    (x : X) (hx : IsClosed ({x} : Set X)) (n : ℕ) :
    Modules.h k (closedPointSupportModule (k := k) x hx) (n + 1) = 0 :=
  Hom.h_pointSupportModule_succ_eq_zero _ n

/-- The finite direct sum of the canonical residue-point modules at a family of points.
Repeated points are retained as repeated summands. -/
noncomputable abbrev finiteResiduePointSupportModule
    (X : Scheme.{u}) {J : Type u} [Finite J] (x : J → X) : X.Modules :=
  ∐ fun j ↦ residuePointSupportModule X (x j)

/-- Every positive cohomology group of a finite direct sum of residue-point modules is
trivial. -/
lemma subsingleton_H_finiteResiduePointSupportModule
    (X : Scheme.{u}) {J : Type u} [Finite J]
    (x : J → X) (n : ℕ) :
    Subsingleton (Modules.H (finiteResiduePointSupportModule X x) (n + 1)) := by
  apply Modules.subsingleton_H_coproduct_of_finite
  intro j
  exact subsingleton_H_residuePointSupportModule X (x j) n

/-- For finitely many closed points over an algebraically closed field, global sections of
the direct sum of their canonical residue-point modules are linearly equivalent to one copy
of the ground field per summand. -/
noncomputable def finiteResiduePointSupportGlobalSectionsLinearEquivOfIsClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    {J : Type u} [Finite J]
    (x : J → X) (hx : ∀ j, IsClosed ({x j} : Set X)) :
    letI := Modules.globalSectionsModule (X ↘ Spec (CommRingCat.of k))
      (finiteResiduePointSupportModule X x)
    Γ(finiteResiduePointSupportModule X x, ⊤) ≃ₗ[k] (J → k) := by
  let p := X ↘ Spec (CommRingCat.of k)
  let _ (j : J) := Modules.globalSectionsModule p
    (residuePointSupportModule X (x j))
  let _ := Modules.globalSectionsModule p
    (finiteResiduePointSupportModule X x)
  exact (Modules.globalSectionsFiniteCoproductLinearEquiv p
    (fun j ↦ residuePointSupportModule X (x j))).trans <|
      LinearEquiv.piCongrRight fun j ↦
        residuePointSupportGlobalSectionsLinearEquivOfIsClosed (k := k) (x j) (hx j)

/-- For finitely many closed points over an algebraically closed field, degree-zero
cohomology of the direct sum of their canonical residue-point modules is linearly
equivalent to one copy of the ground field per summand. -/
noncomputable def finiteResiduePointSupportHZeroLinearEquivOfIsClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    {J : Type u} [Finite J]
    (x : J → X) (hx : ∀ j, IsClosed ({x j} : Set X)) :
    Modules.H (finiteResiduePointSupportModule X x) 0 ≃ₗ[k] (J → k) := by
  let p := X ↘ Spec (CommRingCat.of k)
  let _ := Modules.globalSectionsModule p
    (finiteResiduePointSupportModule X x)
  let _ : IsScalarTower k Γ(X, ⊤)
      Γ(finiteResiduePointSupportModule X x, ⊤) :=
    Modules.isScalarTower_globalSections k _
  exact (LinearEquiv.restrictScalars k
    (Modules.HZeroLinearEquiv (finiteResiduePointSupportModule X x))).trans
      (finiteResiduePointSupportGlobalSectionsLinearEquivOfIsClosed (k := k) x hx)

/-- Degree-zero cohomology of a finite direct sum of closed residue-point modules over an
algebraically closed field is finite dimensional. -/
lemma finiteDimensional_H_finiteResiduePointSupportModule_zero_of_isClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    {J : Type u} [Finite J]
    (x : J → X) (hx : ∀ j, IsClosed ({x j} : Set X)) :
    FiniteDimensional k
      (Modules.H (finiteResiduePointSupportModule X x) 0) := by
  let _ := Fintype.ofFinite J
  exact Module.Finite.equiv
    (finiteResiduePointSupportHZeroLinearEquivOfIsClosed (k := k) x hx).symm

/-- For finitely many closed points over an algebraically closed field, the degree-zero
cohomology dimension of the direct sum of their canonical residue-point modules is the
number of summands. -/
lemma h_finiteResiduePointSupportModule_zero_of_isClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    {J : Type u} [Fintype J]
    (x : J → X) (hx : ∀ j, IsClosed ({x j} : Set X)) :
    Modules.h k (finiteResiduePointSupportModule X x) 0 =
      Fintype.card J :=
  (finiteResiduePointSupportHZeroLinearEquivOfIsClosed (k := k) x hx).finrank_eq.trans
    (Module.finrank_pi k)

/-- Every positive cohomology dimension of a finite direct sum of residue-point modules is
zero. -/
lemma h_finiteResiduePointSupportModule_succ_eq_zero
    {k : Type u} [Field k]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    {J : Type u} [Finite J]
    (x : J → X) (n : ℕ) :
    Modules.h k (finiteResiduePointSupportModule X x) (n + 1) = 0 := by
  exact Modules.h_eq_zero_of_subsingleton k _ _
    (subsingleton_H_finiteResiduePointSupportModule X x n)

/-- The two-term Euler characteristic of a finite direct sum of closed residue-point
modules over an algebraically closed field is the number of summands. -/
lemma eulerChar_finiteResiduePointSupportModule_of_isClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    {J : Type u} [Fintype J]
    (x : J → X) (hx : ∀ j, IsClosed ({x j} : Set X)) :
    Modules.eulerChar k (finiteResiduePointSupportModule X x) =
      Fintype.card J := by
  rw [Modules.eulerChar_def,
    h_finiteResiduePointSupportModule_zero_of_isClosed (k := k) x hx,
    h_finiteResiduePointSupportModule_succ_eq_zero (k := k) x 0]
  norm_num

/-- The `k`-point associated to a closed point has image exactly that point. -/
lemma range_pointOfClosedPoint
    {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    Set.range (pointOfClosedPoint f x hx) = {x} :=
  Set.range_eq_singleton (pointOfClosedPoint_apply f x hx)

end AlgebraicGeometry.Scheme

end
