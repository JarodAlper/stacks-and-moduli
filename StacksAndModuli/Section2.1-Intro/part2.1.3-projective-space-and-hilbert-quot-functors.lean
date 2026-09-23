module

public import StacksAndModuli.«Section2.1-Intro».«part2.1.2-the-grassmannian-functor»
public import StacksAndModuli.API.MvPolynomialDegreeZero
public import StacksAndModuli.API.ProjectiveTwistBaseChange
public import StacksAndModuli.API.SchemeModulesPullbackTensor
public import StacksAndModuli.API.SchemeModulesPullbackPolynomialTwist
public import StacksAndModuli.API.SchemeModulesTensorQuasicoherent
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import «StacksProject».«Constructions».«InvertibleSheavesOnProj».«definition-twist»
public import StacksAndModuli.API.GlobalSectionsOverBase
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Projective space and the Hilbert and Quot functors

This module formalizes the definitions of relative projective space and of the Hilbert and
Quot functors, together with the currently statable forms of Theorem 2.1.2
(`thm:hilbert-scheme-representable`) and Theorem 2.1.3 (`thm:quot-scheme-representable`)
of §2.1 (The Grassmannian, Hilbert, and Quot functors) of Chapter 2 of *Stacks and
Moduli* (the section heading carries no `sec:`
label).

Projective space `ℙ^n_ℤ` is defined as the `Proj` of the standard graded polynomial ring
`ℤ[x_0, …, x_n]` (with `ℤ` lifted to the ambient universe), and `ℙ^n_S` by base change.

The twisting sheaves, Hilbert functions, fiberwise Hilbert-polynomial condition, and the
fixed-polynomial Quot functor `Quot^P(F/ℙ^n_S/S)` are formalized below. The file also
formalizes the polynomial-free functors `Hilb(X/S)` and `Quot(F/X/S)` (which the book
introduces in `rem:quot-remarks`(4)). The following supplemental part deduces Hilbert
representability from Quot; Quot representability and projectivity of the fixed-polynomial
loci remain the substantive geometric obligations.

A note on the `caution` environment of §2.1: the book abuses notation by writing
`Gr(q, V)`, `Hilb^P(ℙ^n_S)`, `Quot^P(F/ℙ^n_S)` both for the functors and for their
representing schemes; in the formalization the functor and a chosen representing object
(`Functor.RepresentableBy`) are always distinguished.

The final declaration of Theorem 2.1.3 is in the immediately following supplemental
part `part2.1.3a-quot-representability-endpoint`, after the projectivity API on which its
proof depends.  This file supplies all of its definitions and reduction lemmas.

The projective-space constructions, Hilbert and Quot functors, and polynomial-free
representability statement in this file are supporting API. The final Hilbert-scheme
statement is deduced in the supplemental part following this file.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section ThmHilbertSchemeRepresentable

open CategoryTheory Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/- The total-degree grading on multivariate polynomial rings is deliberately not a global
instance in Mathlib; it is the grading used for projective space. -/
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Background definition for Theorem 2.1.2 (the ambient projective space
`ℙⁿ_ℤ`): projective `n`-space over the integers (in the ambient universe), the `Proj` of
the standard graded polynomial ring `ℤ[x_0, …, x_n]`, where the grading is by total
degree. -/
noncomputable def Scheme.projectiveSpace (n : ℕ) : Scheme.{u} :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))

/-- Background definition for Theorem 2.1.2 (the ambient relative
projective space `ℙⁿ_S`): relative projective `n`-space over a scheme `S`, the base change
of `ℙ^n_ℤ` along the (unique) morphism `S → Spec ℤ`. -/
noncomputable def Scheme.projectiveSpaceOver (n : ℕ) (S : Scheme.{u}) : Scheme.{u} :=
  pullback (specULiftZIsTerminal.from S)
    (specULiftZIsTerminal.from (Scheme.projectiveSpace n))

/-- The structure morphism `ℙ^n_S → S` of relative projective `n`-space. -/
noncomputable def Scheme.projectiveSpaceOverπ (n : ℕ) (S : Scheme.{u}) :
    Scheme.projectiveSpaceOver n S ⟶ S :=
  pullback.fst _ _

/-- The structure morphism from projective space over the integers is proper.

Source: *Stacks and Moduli*, Chapter 2, §2.1 (The Grassmannian, Hilbert, and Quot
functors), Theorem 2.1.2 (properness of the ambient projective
space). -/
instance Scheme.projectiveSpace_isProper (n : ℕ) :
    IsProper.{u} (specULiftZIsTerminal.from (Scheme.projectiveSpace n)) := by
  let e : Spec (.of ((MvPolynomial.homogeneousSubmodule (Fin (n + 1))
      (ULift.{u} ℤ)) 0)) ≅ Spec (.of (ULift.{u} ℤ)) :=
    Scheme.Spec.mapIso (MvPolynomial.degreeZeroRingEquiv (Fin (n + 1))
      (ULift.{u} ℤ)).toCommRingCatIso.op
  haveI : IsProper (Proj.toSpecZero (MvPolynomial.homogeneousSubmodule
      (Fin (n + 1)) (ULift.{u} ℤ))) := inferInstance
  have h : specULiftZIsTerminal.from (Scheme.projectiveSpace n) =
      Proj.toSpecZero (MvPolynomial.homogeneousSubmodule
        (Fin (n + 1)) (ULift.{u} ℤ)) ≫ e.hom := specULiftZIsTerminal.hom_ext _ _
  have hp : IsProper
    (Proj.toSpecZero (MvPolynomial.homogeneousSubmodule
      (Fin (n + 1)) (ULift.{u} ℤ)) ≫ e.hom) := inferInstance
  rw [← h] at hp
  exact hp

/-- The structure morphism from projective space over the integers is locally of
finite presentation. -/
instance Scheme.projectiveSpace_isLocallyOfFinitePresentation (n : ℕ) :
    LocallyOfFinitePresentation
      (specULiftZIsTerminal.from (Scheme.projectiveSpace n : Scheme.{u})) := by
  letI : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ (ULift.ringEquiv.symm)
  letI : IsLocallyNoetherian (Spec (CommRingCat.of (ULift.{u} ℤ))) := inferInstance
  haveI : LocallyOfFiniteType
      (specULiftZIsTerminal.from (Scheme.projectiveSpace n : Scheme.{u})) :=
    inferInstance
  infer_instance

/-- Relative projective space is proper over its base.

Source: *Stacks and Moduli*, Chapter 2, §2.1 (The Grassmannian, Hilbert, and Quot
functors), Theorem 2.1.2. -/
instance Scheme.projectiveSpaceOverπ_isProper (n : ℕ) (S : Scheme.{u}) :
    IsProper.{u} (Scheme.projectiveSpaceOverπ n S) := by
  letI : IsProper.{u} (specULiftZIsTerminal.from
      (Scheme.projectiveSpace n : Scheme.{u})) :=
    Scheme.projectiveSpace_isProper.{u} n
  dsimp only [Scheme.projectiveSpaceOverπ]
  infer_instance

/-- Relative projective space is locally of finite presentation over its base. -/
instance Scheme.projectiveSpaceOverπ_isLocallyOfFinitePresentation
    (n : ℕ) (S : Scheme.{u}) :
    LocallyOfFinitePresentation (Scheme.projectiveSpaceOverπ n S) := by
  dsimp only [Scheme.projectiveSpaceOverπ]
  infer_instance

/-- Background definition for Theorem 2.1.2 (the implicit definition of
`𝒪_{ℙ^n_S}(d)`): the `d`-th twisting sheaf on relative projective space, the pullback of
`𝒪_{ℙ^n_ℤ}(d)` (Stacks 01MN) along the projection `ℙ^n_S → ℙ^n_ℤ`.

Relative projective space is the base change of `ℙ^n_ℤ`, so its twisting sheaves are the
base changes of those of `ℙ^n_ℤ`. These are what give meaning to the *fixed Hilbert
polynomial* subfunctors `Hilb^P` and `Quot^P`. -/
noncomputable def Scheme.projectiveSpaceOverTwist (n : ℕ) (S : Scheme.{u}) (d : ℤ) :
    (Scheme.projectiveSpaceOver n S).Modules :=
  (Scheme.Modules.pullback (Limits.pullback.snd
      (specULiftZIsTerminal.from S)
      (specULiftZIsTerminal.from (Scheme.projectiveSpace n)))).obj
    (ProjectiveSpectrum.Twist.twist
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) d)

/-- Supporting instance for Theorem 2.1.2 (twist finiteness):
the twisting sheaf `𝒪(d)` on relative projective space is finitely presented. -/
instance Scheme.projectiveSpaceOverTwist_isFinitePresentation
    (n : ℕ) (S : Scheme.{u}) (d : ℤ) :
    (Scheme.projectiveSpaceOverTwist n S d).IsFinitePresentation := by
  unfold Scheme.projectiveSpaceOverTwist
  exact ProjectiveSpectrum.Twist.pullbackPolynomialTwist_isFinitePresentation
    (R := ULift.{u} ℤ) (Fin (n + 1))
      (Limits.pullback.snd
        (specULiftZIsTerminal.from S)
        (specULiftZIsTerminal.from (Scheme.projectiveSpace n))) d

/-- Supporting instance for Theorem 2.1.2 (twist
quasicoherence): the twisting sheaf `𝒪(d)` on relative projective space is
quasicoherent. -/
instance Scheme.projectiveSpaceOverTwist_isQuasicoherent
    (n : ℕ) (S : Scheme.{u}) (d : ℤ) :
    (Scheme.projectiveSpaceOverTwist n S d).IsQuasicoherent := by
  unfold Scheme.projectiveSpaceOverTwist
  exact ProjectiveSpectrum.Twist.pullbackPolynomialTwist_isQuasicoherent
    (R := ULift.{u} ℤ) (Fin (n + 1))
      (Limits.pullback.snd
        (specULiftZIsTerminal.from S)
        (specULiftZIsTerminal.from (Scheme.projectiveSpace n))) d

/-- Background definition for Theorem 2.1.2 (the implicit definition of
`F(d)`): the `d`-th twist of a sheaf of modules on relative projective space. -/
noncomputable def Scheme.projectiveSpaceOverTwistModule {n : ℕ} {S : Scheme.{u}}
    (Q : (Scheme.projectiveSpaceOver n S).Modules) (d : ℤ) :
    (Scheme.projectiveSpaceOver n S).Modules :=
  Scheme.Modules.tensor Q (Scheme.projectiveSpaceOverTwist n S d)

/-- Supporting instance for Theorem 2.1.2 (twisted module
quasicoherence): twisting a quasicoherent module on relative projective space preserves
quasicoherence. -/
instance Scheme.projectiveSpaceOverTwistModule_isQuasicoherent
    {n : ℕ} {S : Scheme.{u}}
    (Q : (Scheme.projectiveSpaceOver n S).Modules) [Q.IsQuasicoherent] (d : ℤ) :
    (Scheme.projectiveSpaceOverTwistModule Q d).IsQuasicoherent := by
  let X := Scheme.projectiveSpaceOver n S
  let 𝒜 := MvPolynomial.homogeneousSubmodule
    (Fin (n + 1)) (ULift.{u} ℤ)
  let f : X ⟶ Proj 𝒜 := Limits.pullback.snd
    (specULiftZIsTerminal.from S)
    (specULiftZIsTerminal.from (Scheme.projectiveSpace n))
  let U (j : ULift.{u} (Fin (n + 1))) : X.Opens :=
    f ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j.down)
  have hU : IsOpenCover U := by
    rw [TopologicalSpace.IsOpenCover]
    dsimp [U]
    rw [← Scheme.Hom.preimage_iSup, iSup_ulift]
    rw [ProjectiveSpectrum.Twist.polynomialCoordinateCover_iSup_eq_top,
      Scheme.Hom.preimage_top]
  let 𝒰 : Scheme.OpenCover.{u} X := X.openCoverOfIsOpenCover U hU
  let _ (j : 𝒰.I₀) :
      ((Scheme.Modules.restrictFunctor (𝒰.f j)).obj
        (Scheme.projectiveSpaceOverTwistModule Q d)).IsQuasicoherent := by
    change ((Scheme.Modules.restrictFunctor (U j).ι).obj
      (Scheme.Modules.tensor Q (Scheme.projectiveSpaceOverTwist n S d))).IsQuasicoherent
    let Qj := (Scheme.Modules.restrictFunctor (U j).ι).obj Q
    let Lj := (Scheme.Modules.restrictFunctor (U j).ι).obj
      (Scheme.projectiveSpaceOverTwist n S d)
    letI : Qj.IsQuasicoherent := by
      dsimp [Qj]
      infer_instance
    let hX : MvPolynomial.X j.down ∈ 𝒜 1 :=
      (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
        (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j.down)
    let eL : Lj ≅ SheafOfModules.unit (U j).toScheme.ringCatSheaf := by
      dsimp [Lj, Scheme.projectiveSpaceOverTwist, U, f, X, 𝒜]
      exact ProjectiveSpectrum.Twist.restrictPullbackTwistIsoUnitOfHom
        (Limits.pullback.snd
          (specULiftZIsTerminal.from S)
          (specULiftZIsTerminal.from (Scheme.projectiveSpace n))) d hX
    have hTensor : (Scheme.Modules.tensor Qj Lj).IsQuasicoherent :=
      Scheme.Modules.tensor_isQuasicoherent_of_iso_unit Qj Lj eL
    exact (SheafOfModules.isQuasicoherent (U j).toScheme.ringCatSheaf).prop_of_iso
      (Scheme.Modules.restrictTensorIso (U j).ι Q
        (Scheme.projectiveSpaceOverTwist n S d)).symm hTensor
  exact Scheme.Modules.isQuasicoherent_of_openCover_restrict _ 𝒰

/-- Supporting instance for Theorem 2.1.2 (twisted module finite
presentation): twisting a finitely presented module on relative projective space
preserves finite presentation. -/
instance Scheme.projectiveSpaceOverTwistModule_isFinitePresentation
    {n : ℕ} {S : Scheme.{u}}
    (Q : (Scheme.projectiveSpaceOver n S).Modules) [Q.IsFinitePresentation] (d : ℤ) :
    (Scheme.projectiveSpaceOverTwistModule Q d).IsFinitePresentation := by
  let X := Scheme.projectiveSpaceOver n S
  let 𝒜 := MvPolynomial.homogeneousSubmodule
    (Fin (n + 1)) (ULift.{u} ℤ)
  let f : X ⟶ Proj 𝒜 := Limits.pullback.snd
    (specULiftZIsTerminal.from S)
    (specULiftZIsTerminal.from (Scheme.projectiveSpace n))
  let U (j : ULift.{u} (Fin (n + 1))) : X.Opens :=
    f ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j.down)
  have hU : ⨆ j, U j = ⊤ := by
    dsimp [U]
    rw [← Scheme.Hom.preimage_iSup, iSup_ulift]
    rw [ProjectiveSpectrum.Twist.polynomialCoordinateCover_iSup_eq_top,
      Scheme.Hom.preimage_top]
  apply Scheme.Modules.tensor_isFinitePresentation_of_iSup_iso_unit
    Q (Scheme.projectiveSpaceOverTwist n S d) U hU
  intro j
  let hX : MvPolynomial.X j.down ∈ 𝒜 1 :=
    (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
      (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j.down)
  dsimp [Scheme.projectiveSpaceOverTwist, U, f, X, 𝒜]
  exact ProjectiveSpectrum.Twist.restrictPullbackTwistIsoUnitOfHom
    (Limits.pullback.snd
      (specULiftZIsTerminal.from S)
      (specULiftZIsTerminal.from (Scheme.projectiveSpace n))) d hX

/-- Functoriality of relative projective space in the base: a morphism `T ⟶ S` induces
`ℙ^n_T ⟶ ℙ^n_S`.

Taken at the residue field of a point this is the inclusion of the fiber
`ℙ^n_{κ(s)} ↪ ℙ^n_S`, which is what makes *fiberwise* conditions expressible. -/
noncomputable def Scheme.projectiveSpaceOverMap (n : ℕ) {S T : Scheme.{u}} (g : T ⟶ S) :
    Scheme.projectiveSpaceOver n T ⟶ Scheme.projectiveSpaceOver n S :=
  Limits.pullback.lift (Scheme.projectiveSpaceOverπ n T ≫ g)
    (Limits.pullback.snd _ _) (specULiftZIsTerminal.hom_ext _ _)

@[reassoc (attr := simp)]
theorem Scheme.projectiveSpaceOverMap_π (n : ℕ) {S T : Scheme.{u}} (g : T ⟶ S) :
    Scheme.projectiveSpaceOverMap n g ≫ Scheme.projectiveSpaceOverπ n S =
      Scheme.projectiveSpaceOverπ n T ≫ g :=
  Limits.pullback.lift_fst _ _ _

/-- API lemma for Theorem 2.1.2 (functoriality
coherence): the map on relative projective spaces preserves the projection to the
absolute projective space. -/
@[reassoc]
lemma Scheme.projectiveSpaceOverMap_absolute_snd
    (n : ℕ) {S T : Scheme.{u}} (g : T ⟶ S) :
    Scheme.projectiveSpaceOverMap n g ≫
        Limits.pullback.snd (specULiftZIsTerminal.from S)
          (specULiftZIsTerminal.from (Scheme.projectiveSpace n)) =
      Limits.pullback.snd (specULiftZIsTerminal.from T)
        (specULiftZIsTerminal.from (Scheme.projectiveSpace n)) := by
  simp [Scheme.projectiveSpaceOverMap]

/-- API lemma for Theorem 2.1.2 (functoriality
coherence): relative projective space maps preserve composition of base maps. -/
@[reassoc]
lemma Scheme.projectiveSpaceOverMap_comp
    (n : ℕ) {S T U : Scheme.{u}} (f : U ⟶ T) (g : T ⟶ S) :
    Scheme.projectiveSpaceOverMap n f ≫ Scheme.projectiveSpaceOverMap n g =
      Scheme.projectiveSpaceOverMap n (f ≫ g) := by
  apply Limits.pullback.hom_ext
  · change (Scheme.projectiveSpaceOverMap n f ≫
        Scheme.projectiveSpaceOverMap n g) ≫
      Scheme.projectiveSpaceOverπ n S =
        Scheme.projectiveSpaceOverMap n (f ≫ g) ≫
          Scheme.projectiveSpaceOverπ n S
    rw [Category.assoc, Scheme.projectiveSpaceOverMap_π,
      ← Category.assoc, Scheme.projectiveSpaceOverMap_π]
    rw [Scheme.projectiveSpaceOverMap_π, Category.assoc]
  · simp only [Category.assoc, Scheme.projectiveSpaceOverMap_absolute_snd]

/-- Background definition for Theorem 2.1.2 (twist base change):
pulling `𝒪(d)` back along the map induced by `T ⟶ S` gives `𝒪(d)` on
`ℙⁿ_T`. -/
noncomputable def Scheme.projectiveSpaceOverTwist_pullbackIso
    (n : ℕ) {S T : Scheme.{u}} (g : T ⟶ S) (d : ℤ) :
    (Scheme.Modules.pullback (Scheme.projectiveSpaceOverMap n g)).obj
        (Scheme.projectiveSpaceOverTwist n S d) ≅
      Scheme.projectiveSpaceOverTwist n T d :=
  (Scheme.Modules.pullbackComp (Scheme.projectiveSpaceOverMap n g)
      (Limits.pullback.snd (specULiftZIsTerminal.from S)
        (specULiftZIsTerminal.from (Scheme.projectiveSpace n)))).app
          (ProjectiveSpectrum.Twist.twist
            (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) d) ≪≫
    (Scheme.Modules.pullbackCongr
      (Scheme.projectiveSpaceOverMap_absolute_snd n g)).app
        (ProjectiveSpectrum.Twist.twist
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) d)

/-- Background definition for Theorem 2.1.2 (nonnegative twist-module
base change): for a natural degree `d`, pulling `Q(d)` back along the relative
projective-space map agrees with twisting the pullback of `Q`. -/
noncomputable def Scheme.projectiveSpaceOverTwistModule_pullbackIso_nat
    (n : ℕ) {S T : Scheme.{u}} (g : T ⟶ S)
    (Q : (Scheme.projectiveSpaceOver n S).Modules) (d : ℕ) :
    (Scheme.Modules.pullback (Scheme.projectiveSpaceOverMap n g)).obj
        (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ)) ≅
      Scheme.projectiveSpaceOverTwistModule
        ((Scheme.Modules.pullback (Scheme.projectiveSpaceOverMap n g)).obj Q)
          (d : ℤ) := by
  let h := Limits.pullback.snd
    (specULiftZIsTerminal.from S)
    (specULiftZIsTerminal.from (Scheme.projectiveSpace n))
  let hc : IsIso (Scheme.Modules.pullbackTensorComparison
      (Scheme.projectiveSpaceOverMap n g) Q
      (Scheme.projectiveSpaceOverTwist n S (d : ℤ))) := by
    exact MvPolynomial.pullbackTensorComparison_pullback_polynomialTwist_nat_isIso
      n (ULift.{u} ℤ) (Scheme.projectiveSpaceOverMap n g) h Q d
  let e := @asIso _ _ _ _ (Scheme.Modules.pullbackTensorComparison
      (Scheme.projectiveSpaceOverMap n g) Q
      (Scheme.projectiveSpaceOverTwist n S (d : ℤ))) hc
  exact e ≪≫
    Scheme.Modules.tensorRightIso
      ((Scheme.Modules.pullback (Scheme.projectiveSpaceOverMap n g)).obj Q)
      (Scheme.projectiveSpaceOverTwist_pullbackIso n g (d : ℤ))

/-- Background definition for Theorem 2.1.2 (the implicit base-change
comparison): relative projective space commutes with base change, `T ×_S ℙ^n_S ≅ ℙ^n_T`.

This is pullback pasting: `ℙ^n_S = ℙ^n_ℤ ×_{Spec ℤ} S`, so `T ×_S (ℙ^n_ℤ ×_{Spec ℤ} S)` is
`ℙ^n_ℤ ×_{Spec ℤ} T`, the two morphisms to `Spec ℤ` agreeing by terminality. It is what lets
a family over `T` pulled back from `ℙ^n_S` be read as a family on `ℙ^n_T`, and hence what
the fixed-Hilbert-polynomial subfunctors need in order to impose a fiberwise condition. -/
noncomputable def Scheme.projectiveSpaceOverBaseChangeIso
    (n : ℕ) {S T : Scheme.{u}} (g : T ⟶ S) :
    Limits.pullback g (Scheme.projectiveSpaceOverπ n S) ≅ Scheme.projectiveSpaceOver n T :=
  Limits.pullbackRightPullbackFstIso _ _ g ≪≫
    Limits.pullback.congrHom (specULiftZIsTerminal.hom_ext _ _) rfl

@[reassoc (attr := simp)]
theorem Scheme.projectiveSpaceOverBaseChangeIso_hom_π
    (n : ℕ) {S T : Scheme.{u}} (g : T ⟶ S) :
    (Scheme.projectiveSpaceOverBaseChangeIso n g).hom ≫ Scheme.projectiveSpaceOverπ n T =
      Limits.pullback.fst _ _ := by
  simp [Scheme.projectiveSpaceOverBaseChangeIso, Scheme.projectiveSpaceOverπ]

/-- API lemma for Theorem 2.1.2 (base-change
coherence): the comparison with `ℙⁿ_T` preserves the absolute projective-space
projection. -/
@[reassoc]
lemma Scheme.projectiveSpaceOverBaseChangeIso_hom_absolute_snd
    (n : ℕ) {S T : Scheme.{u}} (g : T ⟶ S) :
    (Scheme.projectiveSpaceOverBaseChangeIso n g).hom ≫
        Limits.pullback.snd (specULiftZIsTerminal.from T)
          (specULiftZIsTerminal.from (Scheme.projectiveSpace n)) =
      Limits.pullback.snd g (Scheme.projectiveSpaceOverπ n S) ≫
        Limits.pullback.snd (specULiftZIsTerminal.from S)
          (specULiftZIsTerminal.from (Scheme.projectiveSpace n)) := by
  unfold Scheme.projectiveSpaceOverBaseChangeIso
  rw [Iso.trans_hom, Category.assoc]
  rw [show (Limits.pullback.congrHom (specULiftZIsTerminal.hom_ext _ _) rfl).hom ≫
      Limits.pullback.snd (specULiftZIsTerminal.from T)
        (specULiftZIsTerminal.from (Scheme.projectiveSpace n)) =
    Limits.pullback.snd (g ≫ specULiftZIsTerminal.from S)
      (specULiftZIsTerminal.from (Scheme.projectiveSpace n)) by
    simp [Limits.pullback.congrHom]]
  exact Limits.pullbackRightPullbackFstIso_hom_snd _ _ _

/-- API lemma for Theorem 2.1.2 (base-change
coherence): the comparison followed by `ℙⁿ_T ⟶ ℙⁿ_S` is the second
pullback projection. -/
@[reassoc]
lemma Scheme.projectiveSpaceOverBaseChangeIso_hom_map
    (n : ℕ) {S T : Scheme.{u}} (g : T ⟶ S) :
    (Scheme.projectiveSpaceOverBaseChangeIso n g).hom ≫
      Scheme.projectiveSpaceOverMap n g = Limits.pullback.snd _ _ := by
  apply Limits.pullback.hom_ext
  · change ((Scheme.projectiveSpaceOverBaseChangeIso n g).hom ≫
        Scheme.projectiveSpaceOverMap n g) ≫
      Scheme.projectiveSpaceOverπ n S =
        Limits.pullback.snd g (Scheme.projectiveSpaceOverπ n S) ≫
          Scheme.projectiveSpaceOverπ n S
    rw [Category.assoc, Scheme.projectiveSpaceOverMap_π,
      ← Category.assoc, Scheme.projectiveSpaceOverBaseChangeIso_hom_π]
    exact Limits.pullback.condition
  · change ((Scheme.projectiveSpaceOverBaseChangeIso n g).hom ≫
        Scheme.projectiveSpaceOverMap n g) ≫
      Limits.pullback.snd (specULiftZIsTerminal.from S)
        (specULiftZIsTerminal.from (Scheme.projectiveSpace n)) =
      Limits.pullback.snd g (Scheme.projectiveSpaceOverπ n S) ≫
        Limits.pullback.snd (specULiftZIsTerminal.from S)
          (specULiftZIsTerminal.from (Scheme.projectiveSpace n))
    rw [Category.assoc]
    rw [show Scheme.projectiveSpaceOverMap n g ≫
        Limits.pullback.snd (specULiftZIsTerminal.from S)
          (specULiftZIsTerminal.from (Scheme.projectiveSpace n)) =
      Limits.pullback.snd (specULiftZIsTerminal.from T)
        (specULiftZIsTerminal.from (Scheme.projectiveSpace n)) by
      simp [Scheme.projectiveSpaceOverMap]]
    exact Scheme.projectiveSpaceOverBaseChangeIso_hom_absolute_snd n g

/-- Supporting instance for Theorem 2.1.2 (open base
change): an open immersion of bases induces an open immersion of relative
projective spaces. -/
instance Scheme.projectiveSpaceOverMap_isOpenImmersion
    (n : ℕ) {S T : Scheme.{u}} (g : T ⟶ S) [IsOpenImmersion g] :
    IsOpenImmersion (Scheme.projectiveSpaceOverMap n g) := by
  rw [← MorphismProperty.cancel_left_of_respectsIso
    (P := @IsOpenImmersion)
    (Scheme.projectiveSpaceOverBaseChangeIso n g).hom]
  rw [Scheme.projectiveSpaceOverBaseChangeIso_hom_map]
  infer_instance

/-- Background definition for Theorem 2.1.2 (open base
change for twists): along an open immersion of bases, pulling back `Q(d)`
agrees with twisting the pullback of `Q`. -/
noncomputable def Scheme.projectiveSpaceOverTwistModule_pullbackIso_of_isOpenImmersion
    (n : ℕ) {S T : Scheme.{u}} (g : T ⟶ S) [IsOpenImmersion g]
    (Q : (Scheme.projectiveSpaceOver n S).Modules) (d : ℤ) :
    (Scheme.Modules.pullback (Scheme.projectiveSpaceOverMap n g)).obj
        (Scheme.projectiveSpaceOverTwistModule Q d) ≅
      Scheme.projectiveSpaceOverTwistModule
        ((Scheme.Modules.pullback (Scheme.projectiveSpaceOverMap n g)).obj Q) d :=
  (Scheme.Modules.pullbackTensorIsoOfIsOpenImmersion
    (Scheme.projectiveSpaceOverMap n g) Q
      (Scheme.projectiveSpaceOverTwist n S d)).trans
    (Scheme.Modules.tensorRightIso
      ((Scheme.Modules.pullback (Scheme.projectiveSpaceOverMap n g)).obj Q)
      (Scheme.projectiveSpaceOverTwist_pullbackIso n g d))

/-- API lemma for Theorem 2.1.2 (base-change
coherence): the comparison `T ×_S ℙⁿ_S ≅ ℙⁿ_T` is natural in an
`S`-morphism `T' ⟶ T`. -/
@[reassoc]
lemma Scheme.projectiveSpaceOverBaseChangeIso_hom_naturality
    (n : ℕ) {S : Scheme.{u}} {T T' : Over S} (g : T' ⟶ T) :
    ((Over.pullback (Scheme.projectiveSpaceOverπ n S)).map g).left ≫
        (Scheme.projectiveSpaceOverBaseChangeIso n T.hom).hom =
      (Scheme.projectiveSpaceOverBaseChangeIso n T'.hom).hom ≫
        Scheme.projectiveSpaceOverMap n g.left := by
  apply Limits.pullback.hom_ext
  · change (((Over.pullback (Scheme.projectiveSpaceOverπ n S)).map g).left ≫
        (Scheme.projectiveSpaceOverBaseChangeIso n T.hom).hom) ≫
      Scheme.projectiveSpaceOverπ n T.left =
        ((Scheme.projectiveSpaceOverBaseChangeIso n T'.hom).hom ≫
          Scheme.projectiveSpaceOverMap n g.left) ≫
            Scheme.projectiveSpaceOverπ n T.left
    simp only [Category.assoc, Scheme.projectiveSpaceOverBaseChangeIso_hom_π,
      Scheme.projectiveSpaceOverMap_π]
    change Limits.pullback.lift
        (Limits.pullback.fst T'.hom (Scheme.projectiveSpaceOverπ n S) ≫ g.left)
        (Limits.pullback.snd T'.hom (Scheme.projectiveSpaceOverπ n S)) _ ≫
          Limits.pullback.fst T.hom (Scheme.projectiveSpaceOverπ n S) = _
    simp
  · change (((Over.pullback (Scheme.projectiveSpaceOverπ n S)).map g).left ≫
        (Scheme.projectiveSpaceOverBaseChangeIso n T.hom).hom) ≫
      Limits.pullback.snd (specULiftZIsTerminal.from T.left)
        (specULiftZIsTerminal.from (Scheme.projectiveSpace n)) =
        ((Scheme.projectiveSpaceOverBaseChangeIso n T'.hom).hom ≫
          Scheme.projectiveSpaceOverMap n g.left) ≫
            Limits.pullback.snd (specULiftZIsTerminal.from T.left)
              (specULiftZIsTerminal.from (Scheme.projectiveSpace n))
    simp only [Category.assoc,
      Scheme.projectiveSpaceOverBaseChangeIso_hom_absolute_snd,
      Scheme.projectiveSpaceOverMap_absolute_snd]
    change Limits.pullback.lift
        (Limits.pullback.fst T'.hom (Scheme.projectiveSpaceOverπ n S) ≫ g.left)
        (Limits.pullback.snd T'.hom (Scheme.projectiveSpaceOverπ n S)) _ ≫
          Limits.pullback.snd T.hom (Scheme.projectiveSpaceOverπ n S) ≫ _ = _
    simp only [Limits.pullback.lift_snd_assoc]

/-- API lemma for Theorem 2.1.2 (base-change
coherence): inverse form of the naturality of
`T ×_S ℙⁿ_S ≅ ℙⁿ_T`. -/
lemma Scheme.projectiveSpaceOverBaseChangeIso_inv_naturality
    (n : ℕ) {S : Scheme.{u}} {T T' : Over S} (g : T' ⟶ T) :
    (Scheme.projectiveSpaceOverBaseChangeIso n T'.hom).inv ≫
        ((Over.pullback (Scheme.projectiveSpaceOverπ n S)).map g).left =
      Scheme.projectiveSpaceOverMap n g.left ≫
        (Scheme.projectiveSpaceOverBaseChangeIso n T.hom).inv := by
  rw [← cancel_epi (Scheme.projectiveSpaceOverBaseChangeIso n T'.hom).hom]
  rw [Iso.hom_inv_id_assoc, ← Category.assoc,
    ← Scheme.projectiveSpaceOverBaseChangeIso_hom_naturality]
  simp

/-- Background definition for Theorem 2.1.2 (the implicit definition of the
Hilbert function): for a sheaf of modules on `ℙ^n_{Spec R}`, the `R`-rank of the global
sections of its `d`-th twist, `d ↦ dim_R H^0(ℙ^n_R, F(d))`.

The `R`-module structure on global sections comes from the structure morphism
`ℙ^n_{Spec R} → Spec R` (`StacksAndModuli/API/GlobalSectionsOverBase.lean`). The book applies this
with `R` a residue field of the base. -/
noncomputable def Scheme.hilbertFunctionOver {n : ℕ} {R : CommRingCat.{u}}
    (F : (Scheme.projectiveSpaceOver n (Spec R)).Modules) (d : ℤ) : ℕ :=
  letI := Scheme.Modules.globalSectionsModule (Scheme.projectiveSpaceOverπ n (Spec R))
    (Scheme.projectiveSpaceOverTwistModule F d)
  Module.finrank R Γ(Scheme.projectiveSpaceOverTwistModule F d, ⊤)

/-- Background definition for Theorem 2.1.2 (the implicit definition of the
Hilbert polynomial): `F` on `ℙ^n_{Spec R}` has Hilbert polynomial `P ∈ ℚ[z]` when its
Hilbert function agrees with `P` in all sufficiently large degrees.

For a coherent sheaf over a field this is the usual Hilbert polynomial: the higher
cohomology of `F(d)` vanishes for `d ≫ 0`, so `χ(F(d)) = h^0(F(d))` there, and a polynomial
is determined by its values in large degree. See `StacksAndModuli/API/HilbertPolynomialProj.lean`
for the same notion on `Proj` and for uniqueness. -/
def Scheme.HasHilbertPolynomialOver {n : ℕ} {R : CommRingCat.{u}}
    (F : (Scheme.projectiveSpaceOver n (Spec R)).Modules) (P : Polynomial ℚ) : Prop :=
  ∀ᶠ d : ℕ in Filter.atTop, (Scheme.hilbertFunctionOver F (d : ℤ) : ℚ) = P.eval (d : ℚ)

/-- API lemma for Theorem 2.1.2 (isomorphism
invariance): isomorphic sheaves on projective space have the same Hilbert function. -/
theorem Scheme.hilbertFunctionOver_iso
    {n : ℕ} {R : CommRingCat.{u}}
    {F G : (Scheme.projectiveSpaceOver n (Spec R)).Modules} (e : F ≅ G) (d : ℤ) :
    Scheme.hilbertFunctionOver F d = Scheme.hilbertFunctionOver G d := by
  let f := Scheme.projectiveSpaceOverπ n (Spec R)
  let FM := Scheme.projectiveSpaceOverTwistModule F d
  let GM := Scheme.projectiveSpaceOverTwistModule G d
  letI := Scheme.Modules.globalSectionsModule f FM
  letI := Scheme.Modules.globalSectionsModule f GM
  let e' := Scheme.Modules.tensorLeftIso e (Scheme.projectiveSpaceOverTwist n (Spec R) d)
  change Module.finrank R Γ(FM, ⊤) = Module.finrank R Γ(GM, ⊤)
  exact (Scheme.Modules.globalSectionsLinearEquivOfIso
    (M := FM) (N := GM) f e').finrank_eq

/-- API lemma for Theorem 2.1.2 (isomorphism
invariance): the Hilbert-polynomial condition is invariant under isomorphism of
module sheaves. -/
theorem Scheme.HasHilbertPolynomialOver.iso
    {n : ℕ} {R : CommRingCat.{u}}
    {F G : (Scheme.projectiveSpaceOver n (Spec R)).Modules} (e : F ≅ G)
    {P : Polynomial ℚ} (h : Scheme.HasHilbertPolynomialOver F P) :
    Scheme.HasHilbertPolynomialOver G P := by
  filter_upwards [h] with d hd
  rw [← Scheme.hilbertFunctionOver_iso e]
  exact hd

/-- Background definition for Theorem 2.1.3 (the implicit definition of the
fiber `Q_s`): the restriction of a sheaf on `ℙ^n_S` to the fiber `ℙ^n_{κ(s)}` over a point
`s ∈ S`, pulled back along `ℙ^n_{κ(s)} → ℙ^n_S`. -/
noncomputable def Scheme.fiberOverPoint {n : ℕ} {S : Scheme.{u}}
    (Q : (Scheme.projectiveSpaceOver n S).Modules) (s : S) :
    (Scheme.projectiveSpaceOver n (Spec (S.residueField s))).Modules :=
  (Scheme.Modules.pullback
    (Scheme.projectiveSpaceOverMap n (S.fromSpecResidueField s))).obj Q

/-- Background definition for Theorem 2.1.3 (the implicit definition of the
fixed-Hilbert-polynomial condition): a sheaf on `ℙ^n_S` has **fiberwise Hilbert polynomial**
`P` when its pullback to `ℙ^n_K` has Hilbert polynomial `P` for every field-valued point
`Spec K ⟶ S`.

This is the functorial, field-valued-points rendering of the book's condition on every
fiber `Q_s` over `κ(s)`. It includes those residue-field points directly. Conversely, the
residue-field rendering implies this one by invariance of Hilbert polynomials under field
extension.  For quasicoherent sheaves, the required comparison is proved downstream by
`Scheme.projectiveSpaceGlobalSectionsBaseChangeLinearEquiv`; the packaged consequence
`Scheme.HasHilbertPolynomialOver.hasFiberwise_over_field` upgrades a Hilbert polynomial
over any coefficient field to this all-field-valued condition. -/
def Scheme.HasFiberwiseHilbertPolynomial {n : ℕ} {S : Scheme.{u}}
    (Q : (Scheme.projectiveSpaceOver n S).Modules) (P : Polynomial ℚ) : Prop :=
  ∀ (K : CommRingCat.{u}) (_ : IsField K) (s : Spec K ⟶ S),
    Scheme.HasHilbertPolynomialOver
      ((Scheme.Modules.pullback (Scheme.projectiveSpaceOverMap n s)).obj Q) P

/-- Background definition for Subsection 2.4.4 (the implicit definition
of *H-projective*): a morphism of schemes `f : X ⟶ S` is **H-projective** if it factors as
a closed immersion `X ⟶ ℙ^n_S` followed by the projection, for some `n`. This is the
notion of projectivity in Hartshorne; among the three notions discussed in §2.4 it is the
most restrictive one. -/
def IsHProjective {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ (n : ℕ) (ι : X ⟶ Scheme.projectiveSpaceOver n S),
    IsClosedImmersion ι ∧ ι ≫ Scheme.projectiveSpaceOverπ n S = f

/-- Every H-projective morphism is proper: closed immersions are proper, relative
projective space is proper over its base, and proper morphisms are stable under
composition.

Source: *Stacks and Moduli*, Chapter 2, §2.4 (Projectivity of Hilb and Quot),
Subsection 2.4.4. -/
theorem IsHProjective.isProper {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : IsHProjective f) : IsProper.{u} f := by
  obtain ⟨n, ι, hι, hcomp⟩ := hf
  letI : IsClosedImmersion ι := hι
  letI : IsProper.{u} ι := inferInstance
  letI : IsProper.{u} (Scheme.projectiveSpaceOverπ n S) := inferInstance
  have hp : IsProper.{u} (ι ≫ Scheme.projectiveSpaceOverπ n S) := inferInstance
  rw [hcomp] at hp
  exact hp

namespace Scheme

variable {X S : Scheme.{u}}

/-- Background definition for Theorem 2.1.2 (the implicit definition of a
point of the Hilbert functor): let `f : X ⟶ S` be a morphism of schemes, `T` a scheme over
`S`, and `I` an ideal sheaf on `X_T = T ×_S X`. The closed subscheme `Z = V(I) ⊆ X_T` is a
**flat, finitely presented family over `T`** if the composite `Z ⟶ X_T ⟶ T` is flat,
locally of finite presentation, quasi-compact, and quasi-separated. These are the
conditions defining the points of the Hilbert functor. -/
def IdealSheafData.IsFlatFamilyOver (f : X ⟶ S) (T : Over S)
    (I : ((Over.pullback f).obj T).left.IdealSheafData) : Prop :=
  Flat (I.subschemeι ≫ pullback.fst T.hom f) ∧
  LocallyOfFinitePresentation (I.subschemeι ≫ pullback.fst T.hom f) ∧
  QuasiCompact (I.subschemeι ≫ pullback.fst T.hom f) ∧
  QuasiSeparated (I.subschemeι ≫ pullback.fst T.hom f)

/-- The map between the two base changes of `X` induced by a morphism `T' ⟶ T` over
`S` forms a cartesian square with the projections to `T'` and `T`. -/
lemma overPullbackMap_isPullback {f : X ⟶ S} {T T' : Over S} (g : T' ⟶ T) :
    IsPullback ((Over.pullback f).map g).left (pullback.fst T'.hom f)
      (pullback.fst T.hom f) g.left := by
  let G := ((Over.pullback f).map g).left
  have hGfst : G ≫ pullback.fst T.hom f = pullback.fst T'.hom f ≫ g.left := by
    rw [show G = pullback.lift (pullback.fst T'.hom f ≫ g.left) (pullback.snd T'.hom f)
      (by simp [pullback.condition]) from rfl]
    simp
  have hGsnd : G ≫ pullback.snd T.hom f = pullback.snd T'.hom f := by
    rw [show G = pullback.lift (pullback.fst T'.hom f ≫ g.left) (pullback.snd T'.hom f)
      (by simp [pullback.condition]) from rfl]
    simp
  have s2big : IsPullback (G ≫ pullback.snd T.hom f) (pullback.fst T'.hom f) f
      (g.left ≫ T.hom) := by
    rw [hGsnd, Over.w g]
    exact (IsPullback.of_hasPullback T'.hom f).flip
  exact IsPullback.of_right s2big hGfst
    (IsPullback.of_hasPullback T.hom f).flip

/-- Being a flat, finitely presented family of closed subschemes is stable under base
change: the pullback of the ideal sheaf of such a family along `T' → T` again defines a
flat, finitely presented family over `T'`. -/
lemma IdealSheafData.IsFlatFamilyOver.comap {f : X ⟶ S} {T T' : Over S} (g : T' ⟶ T)
    {I : ((Over.pullback f).obj T).left.IdealSheafData}
    (hI : I.IsFlatFamilyOver f T) :
    (I.comap ((Over.pullback f).map g).left).IsFlatFamilyOver f T' := by
  obtain ⟨hflat, hlfp, hqc, hqs⟩ := hI
  set G := ((Over.pullback f).map g).left with hG
  -- the subscheme square is a pullback
  have sqL : IsPullback (I.comapIso G).hom (I.comap G).subschemeι
      (pullback.fst G I.subschemeι) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, IdealSheafData.comapIso_hom_fst]⟩
  have sqV := sqL.paste_horiz (IsPullback.of_hasPullback G I.subschemeι).flip
  rw [Category.id_comp] at sqV
  -- the ambient square is a pullback
  have sq2 := overPullbackMap_isPullback (f := f) g
  have sqBig := sqV.paste_vert sq2
  exact ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Flat)
      sqBig hflat,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @LocallyOfFinitePresentation) sqBig hlfp,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiCompact)
      sqBig hqc,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiSeparated)
      sqBig hqs⟩

/-- Background definition for Theorem 2.1.2 (the implicit definition of the
functor; polynomial-free variant of Remark 2.1.5(4)): let `f : X ⟶ S`
be a morphism of schemes. The **Hilbert functor** `Hilb(X/S)` on schemes over `S`: its
points over `T → S` are the closed subschemes `Z ⊆ X_T` (encoded by their ideal sheaves)
that are flat and finitely presented over `T`.

The fiberwise Hilbert-polynomial condition is available as
`Scheme.HasFiberwiseHilbertPolynomial`; assembling the analogous `Hilb^P` subfunctor is
still recorded in the chapter ledger. -/
noncomputable def hilbFunctor (f : X ⟶ S) : (Over S)ᵒᵖ ⥤ Type u where
  obj T := {I : ((Over.pullback f).obj (unop T)).left.IdealSheafData //
    I.IsFlatFamilyOver f (unop T)}
  map g := ↾fun I ↦ ⟨I.1.comap ((Over.pullback f).map g.unop).left, I.2.comap g.unop⟩
  map_id T := by
    refine ConcreteCategory.hom_ext _ _ fun I ↦ Subtype.ext ?_
    change I.1.comap ((Over.pullback f).map (𝟙 T).unop).left = I.1
    have h : ((Over.pullback f).map (𝟙 T).unop).left =
        𝟙 ((Over.pullback f).obj (unop T)).left := by
      rw [show (𝟙 T).unop = 𝟙 (unop T) from rfl, CategoryTheory.Functor.map_id]
      rfl
    rw [h, IdealSheafData.comap_id]
  map_comp {T T' T''} u v := by
    refine ConcreteCategory.hom_ext _ _ fun I ↦ Subtype.ext ?_
    change I.1.comap ((Over.pullback f).map (u ≫ v).unop).left =
      (I.1.comap ((Over.pullback f).map u.unop).left).comap
        ((Over.pullback f).map v.unop).left
    have h : ((Over.pullback f).map (u ≫ v).unop).left =
        ((Over.pullback f).map v.unop).left ≫ ((Over.pullback f).map u.unop).left := by
      rw [show (u ≫ v).unop = v.unop ≫ u.unop from rfl, Functor.map_comp]
      rfl
    rw [h, IdealSheafData.comap_comp]

end Scheme

end AlgebraicGeometry

end ThmHilbertSchemeRepresentable

section ThmQuotSchemeRepresentable

open CategoryTheory Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme

variable {X S : Scheme.{u}}

/-- Let `M` be a sheaf of modules on a scheme `W` and `g : W ⟶ T` a morphism of schemes.
`M` is **flat over `T`** if for all affine opens `U ⊆ W` and `V ⊆ T` with `U ⊆ g⁻¹(V)`,
the module of sections `Γ(M, U)` is flat over `Γ(T, V)` (via the pullback map on
functions). For quasi-coherent `M` this is the usual notion of a sheaf flat over the
base. -/
def Modules.FlatOver {W T : Scheme.{u}} (M : W.Modules) (g : W ⟶ T) : Prop :=
  ∀ (U : W.affineOpens) (V : T.affineOpens) (h : U.1 ≤ g ⁻¹ᵁ V.1),
    letI := Module.compHom Γ(M, U.1)
      ((W.presheaf.map (homOfLE h).op).hom.comp (g.app V.1).hom)
    Module.Flat Γ(T, V.1) Γ(M, U.1)

/-- The affine fiber-product chart obtained from affine opens `A ⊆ X`, `B ⊆ Y`, and
`C ⊆ Z`, when the maps from `A` and `B` land in `C`. -/
noncomputable abbrev affineOpenPullback {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    (A : X.affineOpens) (B : Y.affineOpens) (C : Z.affineOpens)
    (hA : A.1 ≤ f ⁻¹ᵁ C.1) (hB : B.1 ≤ g ⁻¹ᵁ C.1) : Scheme.{u} :=
  pullback (f.resLE C.1 A.1 hA) (g.resLE C.1 B.1 hB)

instance affineOpenPullback_isAffine {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    (A : X.affineOpens) (B : Y.affineOpens) (C : Z.affineOpens)
    (hA : A.1 ≤ f ⁻¹ᵁ C.1) (hB : B.1 ≤ g ⁻¹ᵁ C.1) :
    IsAffine (affineOpenPullback f g A B C hA hB) := inferInstance

/-- The canonical map from an affine pullback chart into the ambient fiber product. -/
noncomputable def affineOpenPullbackMap {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    (A : X.affineOpens) (B : Y.affineOpens) (C : Z.affineOpens)
    (hA : A.1 ≤ f ⁻¹ᵁ C.1) (hB : B.1 ≤ g ⁻¹ᵁ C.1) :
    affineOpenPullback f g A B C hA hB ⟶ pullback f g :=
  pullback.map (f.resLE C.1 A.1 hA) (g.resLE C.1 B.1 hB) f g
    A.1.ι B.1.ι C.1.ι (by simp) (by simp)

instance affineOpenPullbackMap_isOpenImmersion
    {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    (A : X.affineOpens) (B : Y.affineOpens) (C : Z.affineOpens)
    (hA : A.1 ≤ f ⁻¹ᵁ C.1) (hB : B.1 ≤ g ⁻¹ᵁ C.1) :
    IsOpenImmersion (affineOpenPullbackMap f g A B C hA hB) := by
  dsimp [affineOpenPullbackMap]
  infer_instance

@[reassoc (attr := simp)]
lemma affineOpenPullbackMap_fst {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    (A : X.affineOpens) (B : Y.affineOpens) (C : Z.affineOpens)
    (hA : A.1 ≤ f ⁻¹ᵁ C.1) (hB : B.1 ≤ g ⁻¹ᵁ C.1) :
    affineOpenPullbackMap f g A B C hA hB ≫ pullback.fst f g =
      pullback.fst (f.resLE C.1 A.1 hA) (g.resLE C.1 B.1 hB) ≫ A.1.ι := by
  simp [affineOpenPullbackMap]

@[reassoc (attr := simp)]
lemma affineOpenPullbackMap_snd {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    (A : X.affineOpens) (B : Y.affineOpens) (C : Z.affineOpens)
    (hA : A.1 ≤ f ⁻¹ᵁ C.1) (hB : B.1 ≤ g ⁻¹ᵁ C.1) :
    affineOpenPullbackMap f g A B C hA hB ≫ pullback.snd f g =
      pullback.snd (f.resLE C.1 A.1 hA) (g.resLE C.1 B.1 hB) ≫ B.1.ι := by
  simp [affineOpenPullbackMap]

/-- The affine pullback chart mapped into an arbitrary chosen cartesian square rather
than Mathlib's chosen pullback object. -/
noncomputable def affineOpenPullbackMapOfIsPullback
    {P X Y Z : Scheme.{u}} (fst : P ⟶ X) (snd : P ⟶ Y)
    (f : X ⟶ Z) (g : Y ⟶ Z) (H : IsPullback fst snd f g)
    (A : X.affineOpens) (B : Y.affineOpens) (C : Z.affineOpens)
    (hA : A.1 ≤ f ⁻¹ᵁ C.1) (hB : B.1 ≤ g ⁻¹ᵁ C.1) :
    affineOpenPullback f g A B C hA hB ⟶ P :=
  affineOpenPullbackMap f g A B C hA hB ≫ H.isoPullback.inv

instance affineOpenPullbackMapOfIsPullback_isOpenImmersion
    {P X Y Z : Scheme.{u}} (fst : P ⟶ X) (snd : P ⟶ Y)
    (f : X ⟶ Z) (g : Y ⟶ Z) (H : IsPullback fst snd f g)
    (A : X.affineOpens) (B : Y.affineOpens) (C : Z.affineOpens)
    (hA : A.1 ≤ f ⁻¹ᵁ C.1) (hB : B.1 ≤ g ⁻¹ᵁ C.1) :
    IsOpenImmersion
      (affineOpenPullbackMapOfIsPullback fst snd f g H A B C hA hB) := by
  dsimp [affineOpenPullbackMapOfIsPullback]
  infer_instance

@[reassoc (attr := simp)]
lemma affineOpenPullbackMapOfIsPullback_fst
    {P X Y Z : Scheme.{u}} (fst : P ⟶ X) (snd : P ⟶ Y)
    (f : X ⟶ Z) (g : Y ⟶ Z) (H : IsPullback fst snd f g)
    (A : X.affineOpens) (B : Y.affineOpens) (C : Z.affineOpens)
    (hA : A.1 ≤ f ⁻¹ᵁ C.1) (hB : B.1 ≤ g ⁻¹ᵁ C.1) :
    affineOpenPullbackMapOfIsPullback fst snd f g H A B C hA hB ≫ fst =
      pullback.fst (f.resLE C.1 A.1 hA) (g.resLE C.1 B.1 hB) ≫ A.1.ι := by
  simp [affineOpenPullbackMapOfIsPullback]

@[reassoc (attr := simp)]
lemma affineOpenPullbackMapOfIsPullback_snd
    {P X Y Z : Scheme.{u}} (fst : P ⟶ X) (snd : P ⟶ Y)
    (f : X ⟶ Z) (g : Y ⟶ Z) (H : IsPullback fst snd f g)
    (A : X.affineOpens) (B : Y.affineOpens) (C : Z.affineOpens)
    (hA : A.1 ≤ f ⁻¹ᵁ C.1) (hB : B.1 ≤ g ⁻¹ᵁ C.1) :
    affineOpenPullbackMapOfIsPullback fst snd f g H A B C hA hB ≫ snd =
      pullback.snd (f.resLE C.1 A.1 hA) (g.resLE C.1 B.1 hB) ≫ B.1.ι := by
  simp [affineOpenPullbackMapOfIsPullback]

/-- Every point in an affine pullback chart maps to a point whose two projections lie
in the selected affine opens. -/
lemma opensRange_affineOpenPullbackMapOfIsPullback_le
    {P X Y Z : Scheme.{u}} (fst : P ⟶ X) (snd : P ⟶ Y)
    (f : X ⟶ Z) (g : Y ⟶ Z) (H : IsPullback fst snd f g)
    (A : X.affineOpens) (B : Y.affineOpens) (C : Z.affineOpens)
    (hA : A.1 ≤ f ⁻¹ᵁ C.1) (hB : B.1 ≤ g ⁻¹ᵁ C.1) :
    (affineOpenPullbackMapOfIsPullback fst snd f g H A B C hA hB).opensRange ≤
      fst ⁻¹ᵁ A.1 ⊓ snd ⁻¹ᵁ B.1 := by
  rintro p ⟨q, rfl⟩
  constructor
  · change (affineOpenPullbackMapOfIsPullback fst snd f g H A B C hA hB ≫ fst) q ∈ A.1
    simp
  · change (affineOpenPullbackMapOfIsPullback fst snd f g H A B C hA hB ≫ snd) q ∈ B.1
    simp

/-- Every point of the chosen pullback whose projections lie in `A` and `B` lifts to
the canonical affine pullback chart. -/
lemma le_opensRange_affineOpenPullbackMap
    {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    (A : X.affineOpens) (B : Y.affineOpens) (C : Z.affineOpens)
    (hA : A.1 ≤ f ⁻¹ᵁ C.1) (hB : B.1 ≤ g ⁻¹ᵁ C.1) :
    pullback.fst f g ⁻¹ᵁ A.1 ⊓ pullback.snd f g ⁻¹ᵁ B.1 ≤
      (affineOpenPullbackMap f g A B C hA hB).opensRange := by
  intro p hp
  let l₁ := pullback.fst (pullback.fst f g) A.1.ι
  let l₂ := pullback.fst (pullback.snd f g) B.1.ι
  have hp₁ : p ∈ Set.range l₁ := by
    rw [IsOpenImmersion.range_pullbackFst A.1.ι (pullback.fst f g)]
    simpa [l₁] using hp.1
  have hp₂ : p ∈ Set.range l₂ := by
    rw [IsOpenImmersion.range_pullbackFst B.1.ι (pullback.snd f g)]
    simpa [l₂] using hp.2
  obtain ⟨p₂, hp₂eq⟩ := hp₂
  have hp₂₁ : p₂ ∈ l₂ ⁻¹ᵁ l₁.opensRange := by
    change l₂ p₂ ∈ Set.range l₁
    simpa [hp₂eq] using hp₁
  obtain ⟨q, hq⟩ :=
    (IsOpenImmersion.range_pullbackSnd l₁ l₂).ge hp₂₁
  let e := pullbackFstFstIso
    (f.resLE C.1 A.1 hA) (g.resLE C.1 B.1 hB) f g
    A.1.ι B.1.ι C.1.ι (by simp) (by simp)
  refine ⟨e.hom q, ?_⟩
  rw [show affineOpenPullbackMap f g A B C hA hB =
    e.inv ≫ pullback.snd l₁ l₂ ≫ l₂ by
      exact CategoryTheory.Limits.pullback_map_eq_pullbackFstFstIso_inv
        (f.resLE C.1 A.1 hA) (g.resLE C.1 B.1 hB) f g
          A.1.ι B.1.ι C.1.ι (by simp) (by simp)]
  simp only [Scheme.Hom.comp_apply]
  have heq : e.inv (e.hom q) = q := by
    change (e.hom ≫ e.inv) q = q
    rw [e.hom_inv_id]
    exact ConcreteCategory.id_apply q
  rw [heq, hq, hp₂eq]

lemma opensRange_affineOpenPullbackMap_le
    {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    (A : X.affineOpens) (B : Y.affineOpens) (C : Z.affineOpens)
    (hA : A.1 ≤ f ⁻¹ᵁ C.1) (hB : B.1 ≤ g ⁻¹ᵁ C.1) :
    (affineOpenPullbackMap f g A B C hA hB).opensRange ≤
      pullback.fst f g ⁻¹ᵁ A.1 ⊓ pullback.snd f g ⁻¹ᵁ B.1 := by
  rintro p ⟨q, rfl⟩
  constructor
  · change (affineOpenPullbackMap f g A B C hA hB ≫ pullback.fst f g) q ∈ A.1
    simp
  · change (affineOpenPullbackMap f g A B C hA hB ≫ pullback.snd f g) q ∈ B.1
    simp

/-- The image of a canonical affine pullback chart is exactly the intersection of the
inverse images of its two affine opens. -/
lemma opensRange_affineOpenPullbackMap
    {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    (A : X.affineOpens) (B : Y.affineOpens) (C : Z.affineOpens)
    (hA : A.1 ≤ f ⁻¹ᵁ C.1) (hB : B.1 ≤ g ⁻¹ᵁ C.1) :
    (affineOpenPullbackMap f g A B C hA hB).opensRange =
      pullback.fst f g ⁻¹ᵁ A.1 ⊓ pullback.snd f g ⁻¹ᵁ B.1 :=
  le_antisymm (opensRange_affineOpenPullbackMap_le f g A B C hA hB)
    (le_opensRange_affineOpenPullbackMap f g A B C hA hB)

/-- The image formula for an affine pullback chart in an arbitrary chosen cartesian
square. -/
lemma opensRange_affineOpenPullbackMapOfIsPullback
    {P X Y Z : Scheme.{u}} (fst : P ⟶ X) (snd : P ⟶ Y)
    (f : X ⟶ Z) (g : Y ⟶ Z) (H : IsPullback fst snd f g)
    (A : X.affineOpens) (B : Y.affineOpens) (C : Z.affineOpens)
    (hA : A.1 ≤ f ⁻¹ᵁ C.1) (hB : B.1 ≤ g ⁻¹ᵁ C.1) :
    (affineOpenPullbackMapOfIsPullback fst snd f g H A B C hA hB).opensRange =
      fst ⁻¹ᵁ A.1 ⊓ snd ⁻¹ᵁ B.1 := by
  apply le_antisymm
  · exact opensRange_affineOpenPullbackMapOfIsPullback_le
      fst snd f g H A B C hA hB
  · intro p hp
    have hp' : H.isoPullback.hom p ∈
        pullback.fst f g ⁻¹ᵁ A.1 ⊓ pullback.snd f g ⁻¹ᵁ B.1 := by
      simpa [← Scheme.Hom.comp_apply] using hp
    rw [← opensRange_affineOpenPullbackMap f g A B C hA hB] at hp'
    obtain ⟨q, hq⟩ := hp'
    refine ⟨q, ?_⟩
    change H.isoPullback.inv (affineOpenPullbackMap f g A B C hA hB q) = p
    rw [hq]
    change (H.isoPullback.hom ≫ H.isoPullback.inv) p = p
    rw [H.isoPullback.hom_inv_id]
    exact ConcreteCategory.id_apply p

/-- Every point of a cartesian square has a neighborhood given by an affine pullback
chart over an affine open of the base. -/
lemma exists_mem_affineOpenPullbackMapOfIsPullback
    {P X Y Z : Scheme.{u}} (fst : P ⟶ X) (snd : P ⟶ Y)
    (f : X ⟶ Z) (g : Y ⟶ Z) (H : IsPullback fst snd f g) (p : P) :
    ∃ (A : X.affineOpens) (B : Y.affineOpens) (C : Z.affineOpens)
      (hA : A.1 ≤ f ⁻¹ᵁ C.1) (hB : B.1 ≤ g ⁻¹ᵁ C.1),
      p ∈ (affineOpenPullbackMapOfIsPullback fst snd f g H A B C hA hB).opensRange := by
  obtain ⟨_, ⟨C, hC, rfl⟩, hpC, -⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f (fst p))) isOpen_univ
  let C' : Z.affineOpens := ⟨C, hC⟩
  have hpC' : g (snd p) ∈ C := by
    change (snd ≫ g) p ∈ C
    rw [← H.w]
    exact hpC
  obtain ⟨_, ⟨A, hAaff, rfl⟩, hpA, hA⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
    hpC (f ⁻¹ᵁ C).2
  obtain ⟨_, ⟨B, hBaff, rfl⟩, hpB, hB⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open
    hpC' (g ⁻¹ᵁ C).2
  let A' : X.affineOpens := ⟨A, hAaff⟩
  let B' : Y.affineOpens := ⟨B, hBaff⟩
  refine ⟨A', B', C', hA, hB, ?_⟩
  rw [opensRange_affineOpenPullbackMapOfIsPullback]
  exact ⟨hpA, hpB⟩

/-- The affine pullback chart through a point may be chosen with its base-side
affine open contained in any prescribed open neighborhood of the base projection. -/
lemma exists_mem_affineOpenPullbackMapOfIsPullback_le
    {P X Y Z : Scheme.{u}} (fst : P ⟶ X) (snd : P ⟶ Y)
    (f : X ⟶ Z) (g : Y ⟶ Z) (H : IsPullback fst snd f g) (p : P)
    (V : Y.Opens) (hpV : snd p ∈ V) :
    ∃ (A : X.affineOpens) (B : Y.affineOpens) (C : Z.affineOpens)
      (hA : A.1 ≤ f ⁻¹ᵁ C.1) (hB : B.1 ≤ g ⁻¹ᵁ C.1),
      B.1 ≤ V ∧
      p ∈ (affineOpenPullbackMapOfIsPullback fst snd f g H A B C hA hB).opensRange := by
  obtain ⟨_, ⟨C, hC, rfl⟩, hpC, -⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f (fst p))) isOpen_univ
  let C' : Z.affineOpens := ⟨C, hC⟩
  have hpC' : g (snd p) ∈ C := by
    change (snd ≫ g) p ∈ C
    rw [← H.w]
    exact hpC
  obtain ⟨_, ⟨A, hAaff, rfl⟩, hpA, hA⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hpC (f ⁻¹ᵁ C).2
  have hpBopen : snd p ∈ V ⊓ g ⁻¹ᵁ C := ⟨hpV, hpC'⟩
  obtain ⟨_, ⟨B, hBaff, rfl⟩, hpB, hB⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hpBopen (V ⊓ g ⁻¹ᵁ C).2
  let A' : X.affineOpens := ⟨A, hAaff⟩
  let B' : Y.affineOpens := ⟨B, hBaff⟩
  refine ⟨A', B', C', hA, hB.trans inf_le_right, hB.trans inf_le_left, ?_⟩
  rw [opensRange_affineOpenPullbackMapOfIsPullback]
  exact ⟨hpA, hpB⟩

/-- A point in an affine open of a cartesian pullback has a common ambient basic-open
neighborhood in that affine open and in an affine pullback chart whose base side is
contained in a prescribed affine base open. -/
lemma exists_common_basicOpen_affineOpenPullbackMapOfIsPullback
    {P X Y Z : Scheme.{u}} (fst : P ⟶ X) (snd : P ⟶ Y)
    (f : X ⟶ Z) (g : Y ⟶ Z) (H : IsPullback fst snd f g)
    (U : P.affineOpens) (V : Y.affineOpens) (p : P)
    (hpU : p ∈ U.1) (hpV : snd p ∈ V.1) :
    ∃ (A : X.affineOpens) (B : Y.affineOpens) (C : Z.affineOpens)
      (hA : A.1 ≤ f ⁻¹ᵁ C.1) (hB : B.1 ≤ g ⁻¹ᵁ C.1) (_hBV : B.1 ≤ V.1)
      (r : Γ(P, U.1))
      (s : Γ(P, (affineOpenPullbackMapOfIsPullback
        fst snd f g H A B C hA hB).opensRange)),
      P.basicOpen r = P.basicOpen s ∧ p ∈ P.basicOpen r := by
  obtain ⟨A, B, C, hA, hB, hBV, hpChart⟩ :=
    exists_mem_affineOpenPullbackMapOfIsPullback_le
      fst snd f g H p V.1 hpV
  let i := affineOpenPullbackMapOfIsPullback fst snd f g H A B C hA hB
  have hChart : IsAffineOpen i.opensRange := isAffineOpen_opensRange i
  obtain ⟨r, s, hrs, hpr⟩ :=
    exists_basicOpen_le_affine_inter U.2 hChart p ⟨hpU, hpChart⟩
  exact ⟨A, B, C, hA, hB, hBV, r, s, hrs, hpr⟩

/-- Under an open immersion from an affine scheme, the basic open obtained by
transporting a section of the image open maps back to the original ambient basic
open. -/
lemma image_basicOpen_appIsoTop
    {X Y : Scheme.{u}} [IsAffine X] (i : X ⟶ Y) [IsOpenImmersion i]
    (s : Γ(Y, i ''ᵁ (⊤ : X.Opens))) :
    i ''ᵁ X.basicOpen ((i.appIso ⊤).hom s) = Y.basicOpen s := by
  simp [Scheme.image_basicOpen]

/-- The same image formula using the canonical isomorphism from the source of an open
immersion to its range open subscheme. -/
lemma image_basicOpen_isoOpensRange
    {X Y : Scheme.{u}} [IsAffine X] (i : X ⟶ Y) [IsOpenImmersion i]
    (s : Γ(Y, i.opensRange)) :
    i ''ᵁ X.basicOpen
      ((i.appLE i.opensRange ⊤ (by simp)).hom s) = Y.basicOpen s := by
  have hpre : i ⁻¹ᵁ Y.basicOpen s = X.basicOpen
      ((i.appLE i.opensRange ⊤ (by simp)).hom s) := by
    rw [Scheme.preimage_basicOpen]
    simp [Scheme.Hom.appLE, Scheme.basicOpen_res]
  rw [← hpre, Scheme.Hom.image_preimage_eq_opensRange_inf]
  exact inf_eq_right.mpr (Y.basicOpen_le s)

/-- The corresponding basic open in the canonical spectrum chart has the same image
in the ambient scheme. -/
lemma isoSpecInv_comp_image_basicOpen_appIsoTop
    {X Y : Scheme.{u}} [IsAffine X] (i : X ⟶ Y) [IsOpenImmersion i]
    (s : Γ(Y, i ''ᵁ (⊤ : X.Opens))) :
    (X.isoSpec.inv ≫ i) ''ᵁ
        PrimeSpectrum.basicOpen ((i.appIso ⊤).hom s) = Y.basicOpen s := by
  have him : X.isoSpec.inv ''ᵁ
      PrimeSpectrum.basicOpen ((i.appIso ⊤).hom s) =
        X.basicOpen ((i.appIso ⊤).hom s) := by
    simpa only [← IsAffineOpen.fromSpec_top] using
      (isAffineOpen_top X).fromSpec_image_basicOpen ((i.appIso ⊤).hom s)
  rw [Scheme.Hom.comp_image]
  rw [him]
  exact image_basicOpen_appIsoTop i s

/-- Canonical-spectrum version of `image_basicOpen_isoOpensRange`. -/
lemma isoSpecInv_comp_image_basicOpen_isoOpensRange
    {X Y : Scheme.{u}} [IsAffine X] (i : X ⟶ Y) [IsOpenImmersion i]
    (s : Γ(Y, i.opensRange)) :
    (X.isoSpec.inv ≫ i) ''ᵁ PrimeSpectrum.basicOpen
        ((i.appLE i.opensRange ⊤ (by simp)).hom s) = Y.basicOpen s := by
  let t := (i.appLE i.opensRange ⊤ (by simp)).hom s
  have him : X.isoSpec.inv ''ᵁ PrimeSpectrum.basicOpen t = X.basicOpen t := by
    simpa only [← IsAffineOpen.fromSpec_top] using
      (isAffineOpen_top X).fromSpec_image_basicOpen t
  rw [Scheme.Hom.comp_image, him]
  exact image_basicOpen_isoOpensRange i s

namespace Modules

/-- Pulling a module sheaf back in two stages agrees with pulling it back along an
equal composite morphism. -/
noncomputable def pullbackPullbackIsoOfEq
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (e : f ≫ g = h) (M : Z.Modules) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M) ≅
      (Scheme.Modules.pullback h).obj M :=
  (Scheme.Modules.pullbackComp f g).app M ≪≫
    (Scheme.Modules.pullbackCongr e).app M

/-- On an affine pullback chart of a cartesian square, restricting the globally
pulled-back sheaf agrees with the local two-stage pullback through the affine source
chart. -/
noncomputable def affineOpenPullbackSheafIso
    {P X Y Z : Scheme.{u}} (fst : P ⟶ X) (snd : P ⟶ Y)
    (f : X ⟶ Z) (g : Y ⟶ Z) (H : IsPullback fst snd f g)
    (A : X.affineOpens) (B : Y.affineOpens) (C : Z.affineOpens)
    (hA : A.1 ≤ f ⁻¹ᵁ C.1) (hB : B.1 ≤ g ⁻¹ᵁ C.1) (M : X.Modules) :
    (Scheme.Modules.pullback
      (affineOpenPullbackMapOfIsPullback fst snd f g H A B C hA hB)).obj
        ((Scheme.Modules.pullback fst).obj M) ≅
      (Scheme.Modules.pullback
        (pullback.fst (f.resLE C.1 A.1 hA) (g.resLE C.1 B.1 hB))).obj
          ((Scheme.Modules.pullback A.1.ι).obj M) :=
  pullbackPullbackIsoOfEq
      (affineOpenPullbackMapOfIsPullback fst snd f g H A B C hA hB) fst
      (pullback.fst (f.resLE C.1 A.1 hA) (g.resLE C.1 B.1 hB) ≫ A.1.ι)
      (affineOpenPullbackMapOfIsPullback_fst fst snd f g H A B C hA hB) M ≪≫
    (pullbackPullbackIsoOfEq
      (pullback.fst (f.resLE C.1 A.1 hA) (g.resLE C.1 B.1 hB)) A.1.ι
      (pullback.fst (f.resLE C.1 A.1 hA) (g.resLE C.1 B.1 hB) ≫ A.1.ι)
      rfl M).symm

/-- Relative flatness of a module sheaf over a fixed base is invariant under
isomorphism of module sheaves. -/
lemma FlatOver.of_iso {W T : Scheme.{u}} {M N : W.Modules} {g : W ⟶ T}
    (e : M ≅ N) (hM : M.FlatOver g) : N.FlatOver g := by
  intro U V h
  exact Scheme.Modules.sections_flat_of_iso_restrictScalars e U.1
    ((W.presheaf.map (homOfLE h).op).hom.comp (g.app V.1).hom) (hM U V h)

/-- Two isomorphic module sheaves have the same relative-flatness property over a
fixed morphism. -/
lemma FlatOver.iso_iff {W T : Scheme.{u}} {M N : W.Modules} {g : W ⟶ T}
    (e : M ≅ N) : M.FlatOver g ↔ N.FlatOver g :=
  ⟨FlatOver.of_iso e, FlatOver.of_iso e.symm⟩

/-- Relative flatness is invariant under replacing the structure morphism by an equal
morphism. -/
lemma FlatOver.congr {W T : Scheme.{u}} {M : W.Modules} {g g' : W ⟶ T}
    (h : g = g') : M.FlatOver g ↔ M.FlatOver g' := by
  subst g'
  rfl

/-- If the target is changed by an isomorphism, the two coefficient maps on sections
are conjugate by the canonical equivalence between the section rings of an open and
its inverse image. -/
lemma exists_appLE_ringEquiv_comp_isIso {W T T' : Scheme.{u}} (g : W ⟶ T)
    (j : T ⟶ T') [IsIso j] (U : W.Opens) (V : T'.Opens)
    (h : U ≤ (g ≫ j) ⁻¹ᵁ V) :
    ∃ e : Γ(T, j ⁻¹ᵁ V) ≃+* Γ(T', V),
      ((g ≫ j).appLE V U h).hom.comp e.toRingHom =
        (g.appLE (j ⁻¹ᵁ V) U (by simpa using h)).hom := by
  have hV : j ''ᵁ (j ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Hom.opensRange_of_isIso, top_inf_eq]
  let eCat : Γ(T, j ⁻¹ᵁ V) ≅ Γ(T', V) :=
    (j.appIso (j ⁻¹ᵁ V)).symm ≪≫
      T'.presheaf.mapIso (eqToIso hV.symm).op
  let e := eCat.commRingCatIsoToRingEquiv
  refine ⟨e, ?_⟩
  have hj : (j.appIso (j ⁻¹ᵁ V)).inv ≫
      T'.presheaf.map (eqToHom hV.symm).op ≫ j.app V = 𝟙 _ := by
    rw [j.naturality, ← Category.assoc,
      Scheme.Hom.appIso_inv_app,
      ← T.presheaf.map_comp, ← T.presheaf.map_id]
    exact congrArg T.presheaf.map (Subsingleton.elim _ _)
  ext r
  dsimp [e, eCat]
  change (g.app (j ⁻¹ᵁ V) ≫ W.presheaf.map (homOfLE h).op).hom
    (((j.appIso (j ⁻¹ᵁ V)).inv ≫
      T'.presheaf.map (eqToHom hV.symm).op ≫ j.app V).hom r) = _
  rw [hj]
  rfl

/-- Composing the structure morphism with an isomorphism of base schemes preserves
relative flatness. -/
lemma FlatOver.comp_isIso {W T T' : Scheme.{u}} {M : W.Modules} {g : W ⟶ T}
    (j : T ⟶ T') [IsIso j] (hM : M.FlatOver g) : M.FlatOver (g ≫ j) := by
  intro U V h
  let Vpre : T.affineOpens :=
    ⟨j ⁻¹ᵁ V.1, V.2.preimage_of_isOpenImmersion j (by
      rw [Scheme.Hom.opensRange_of_isIso]
      exact le_top)⟩
  have hpre : U.1 ≤ g ⁻¹ᵁ Vpre.1 := by
    simpa [Vpre] using h
  let a : Γ(T, Vpre.1) →+* Γ(W, U.1) :=
    (g.appLE Vpre.1 U.1 hpre).hom
  let b : Γ(T', V.1) →+* Γ(W, U.1) :=
    ((g ≫ j).appLE V.1 U.1 h).hom
  obtain ⟨e, he⟩ := exists_appLE_ringEquiv_comp_isIso g j U.1 V.1 h
  have hflat :
      letI := Module.compHom Γ(M, U.1) a
      Module.Flat Γ(T, Vpre.1) Γ(M, U.1) := hM U Vpre hpre
  exact Module.Flat.compHom_of_ringEquiv e a b he hflat

/-- The `iff` form of `FlatOver.comp_isIso`. -/
lemma FlatOver.comp_isIso_iff {W T T' : Scheme.{u}} {M : W.Modules} {g : W ⟶ T}
    (j : T ⟶ T') [IsIso j] : M.FlatOver g ↔ M.FlatOver (g ≫ j) := by
  constructor
  · exact FlatOver.comp_isIso j
  · intro h
    have h' := FlatOver.comp_isIso (inv j) h
    exact (FlatOver.congr (M := M) (by simp)).mp h'

/-- If a structure morphism factors through an open subscheme of its base, relative
flatness over the ambient base implies relative flatness over that open subscheme. -/
lemma FlatOver.of_comp_isOpenImmersion {W T T' : Scheme.{u}} {M : W.Modules}
    {g : W ⟶ T} (j : T ⟶ T') [IsOpenImmersion j]
    (hM : M.FlatOver (g ≫ j)) : M.FlatOver g := by
  intro U V h
  let Vim : T'.affineOpens :=
    ⟨j ''ᵁ V.1, V.2.image_of_isOpenImmersion j⟩
  have him : U.1 ≤ (g ≫ j) ⁻¹ᵁ Vim.1 := by
    intro x hx
    exact ⟨g x, h hx, rfl⟩
  let a : Γ(T', Vim.1) →+* Γ(W, U.1) :=
    ((g ≫ j).appLE Vim.1 U.1 him).hom
  let b : Γ(T, V.1) →+* Γ(W, U.1) :=
    (g.appLE V.1 U.1 h).hom
  let e := (j.appIso V.1).commRingCatIsoToRingEquiv
  have he : b.comp e.toRingHom = a := by
    ext r
    dsimp [a, b, e]
    rw [Scheme.Hom.appIso_hom']
    change ((j.appLE Vim.1 V.1 (j.preimage_image_eq V.1).ge ≫
      g.appLE V.1 U.1 h).hom) r = ((g ≫ j).appLE Vim.1 U.1 him).hom r
    rw [Scheme.Hom.appLE_comp_appLE]
  have hflat :
      letI := Module.compHom Γ(M, U.1) a
      Module.Flat Γ(T', Vim.1) Γ(M, U.1) := hM U Vim him
  exact Module.Flat.compHom_of_ringEquiv e a b he hflat

/-- Pullback along an open immersion of source schemes preserves relative flatness. -/
lemma FlatOver.pullback_isOpenImmersion {W W' T : Scheme.{u}} (i : W' ⟶ W)
    [IsOpenImmersion i]
    (M : W.Modules) {g : W ⟶ T} {g' : W' ⟶ T} (hi : i ≫ g = g')
    (hM : M.FlatOver g) : ((Scheme.Modules.pullback i).obj M).FlatOver g' := by
  subst g'
  intro U V h
  let Uim : W.affineOpens :=
    ⟨i ''ᵁ U.1, U.2.image_of_isOpenImmersion i⟩
  have him : Uim.1 ≤ g ⁻¹ᵁ V.1 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    change g (i y) ∈ V.1
    exact h hy
  let a : Γ(T, V.1) →+* Γ(W, Uim.1) :=
    (W.presheaf.map (homOfLE him).op).hom.comp (g.app V.1).hom
  have hflat :
      letI := Module.compHom Γ(M, Uim.1) a
      Module.Flat Γ(T, V.1) Γ(M, Uim.1) := hM Uim V him
  have hpull :
      letI := Module.compHom Γ((Scheme.Modules.pullback i).obj M, U.1)
        ((i.appIso U.1).hom.hom.comp a)
      Module.Flat Γ(T, V.1) Γ((Scheme.Modules.pullback i).obj M, U.1) :=
    Scheme.Modules.pullback_openImmersion_sections_flat_restrictScalars i M U.1 a hflat
  let b : Γ(T, V.1) →+* Γ(W', U.1) :=
    (W'.presheaf.map (homOfLE h).op).hom.comp ((i ≫ g).app V.1).hom
  have hab : (i.appIso U.1).hom.hom.comp a = b := by
    ext r
    dsimp [a, b]
    rw [Scheme.Hom.appIso_hom']
    change ((g.appLE V.1 Uim.1 him ≫
      i.appLE Uim.1 U.1 (i.preimage_image_eq U.1).ge).hom) r =
        ((i ≫ g).appLE V.1 U.1 h).hom r
    rw [Scheme.Hom.appLE_comp_appLE]
  exact Module.Flat.compHom_congr _ b hab hpull

/-- Pullback along an isomorphism of source schemes preserves relative flatness. -/
lemma FlatOver.pullback_isIso {W W' T : Scheme.{u}} (i : W' ⟶ W) [IsIso i]
    (M : W.Modules) {g : W ⟶ T} {g' : W' ⟶ T} (hi : i ≫ g = g')
    (hM : M.FlatOver g) : ((Scheme.Modules.pullback i).obj M).FlatOver g' :=
  FlatOver.pullback_isOpenImmersion i M hi hM

/-- Restrict a relatively flat module sheaf simultaneously to an open subscheme of
its source and an open subscheme of its base. -/
lemma FlatOver.pullback_isOpenImmersion_of_comm
    {W W' T T' : Scheme.{u}} (i : W' ⟶ W) [IsOpenImmersion i]
    (j : T' ⟶ T) [IsOpenImmersion j] (M : W.Modules)
    {g : W ⟶ T} {g' : W' ⟶ T'} (hij : i ≫ g = g' ≫ j)
    (hM : M.FlatOver g) : ((Scheme.Modules.pullback i).obj M).FlatOver g' := by
  have hsource : ((Scheme.Modules.pullback i).obj M).FlatOver (i ≫ g) :=
    FlatOver.pullback_isOpenImmersion i M rfl hM
  have hcomp : ((Scheme.Modules.pullback i).obj M).FlatOver (g' ≫ j) :=
    (FlatOver.congr hij).mp hsource
  exact FlatOver.of_comp_isOpenImmersion j hcomp

/-- On an affine pullback chart, affine global sections of the base-changed
quasicoherent sheaf are flat over the affine base chart. -/
lemma FlatOver.affineOpenPullback_sections
    {W T Z : Scheme.{u}} {M : W.Modules} [M.IsQuasicoherent]
    (f : W ⟶ Z) (g : T ⟶ Z) (hM : M.FlatOver f)
    (A : W.affineOpens) (B : T.affineOpens) (C : Z.affineOpens)
    (hA : A.1 ≤ f ⁻¹ᵁ C.1) (hB : B.1 ≤ g ⁻¹ᵁ C.1) :
    let fA := f.resLE C.1 A.1 hA
    let gB := g.resLE C.1 B.1 hB
    let MA := (Scheme.Modules.pullback A.1.ι).obj M
    let N := (Scheme.Modules.pullback (pullback.fst fA gB)).obj MA
    letI := Module.compHom Γ(N, ⊤) (pullback.snd fA gB).appTop.hom
    Module.Flat Γ(B.1, ⊤) Γ(N, ⊤) := by
  dsimp only
  let fA := f.resLE C.1 A.1 hA
  let gB := g.resLE C.1 B.1 hB
  let MA := (Scheme.Modules.pullback A.1.ι).obj M
  have hMA : MA.FlatOver fA :=
    FlatOver.pullback_isOpenImmersion_of_comm A.1.ι C.1.ι M
      (by simp [fA]) hM
  let Atop : A.1.toScheme.affineOpens := ⟨⊤, isAffineOpen_top _⟩
  let Ctop : C.1.toScheme.affineOpens := ⟨⊤, isAffineOpen_top _⟩
  have htop : Atop.1 ≤ fA ⁻¹ᵁ Ctop.1 := by
    change (⊤ : A.1.toScheme.Opens) ≤ ⊤
    exact le_rfl
  have hflat :
      letI := Module.compHom Γ(MA, ⊤) fA.appTop.hom
      Module.Flat Γ(C.1, ⊤) Γ(MA, ⊤) := by
    have hraw := hMA Atop Ctop htop
    dsimp [Atop, Ctop] at hraw
    apply Module.Flat.compHom_congr _ fA.appTop.hom _ hraw
    ext r
    change ((A.1.toScheme.presheaf.map (homOfLE htop).op).hom
      (fA.appTop.hom r)) = fA.appTop.hom r
    rw [show A.1.toScheme.presheaf.map (homOfLE htop).op = 𝟙 _ by
      rw [← A.1.toScheme.presheaf.map_id]
      exact congrArg A.1.toScheme.presheaf.map (Subsingleton.elim _ _)]
    rfl
  exact pullbackQuasicoherentSections_flat_of_scheme_isPullback
    (pullback.fst fA gB) (pullback.snd fA gB) fA gB
    (IsPullback.of_hasPullback fA gB) MA hflat

/-- The restriction of the globally base-changed sheaf to an affine pullback chart has
flat global sections over the affine base chart. -/
lemma FlatOver.affineOpenPullback_global_sections
    {P W T Z : Scheme.{u}} (fst : P ⟶ W) (snd : P ⟶ T)
    (f : W ⟶ Z) (g : T ⟶ Z) (H : IsPullback fst snd f g)
    {M : W.Modules} [M.IsQuasicoherent] (hM : M.FlatOver f)
    (A : W.affineOpens) (B : T.affineOpens) (C : Z.affineOpens)
    (hA : A.1 ≤ f ⁻¹ᵁ C.1) (hB : B.1 ≤ g ⁻¹ᵁ C.1) :
    let fA := f.resLE C.1 A.1 hA
    let gB := g.resLE C.1 B.1 hB
    let i := affineOpenPullbackMapOfIsPullback fst snd f g H A B C hA hB
    let Q := (Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback fst).obj M)
    letI := Module.compHom Γ(Q, ⊤) (pullback.snd fA gB).appTop.hom
    Module.Flat Γ(B.1, ⊤) Γ(Q, ⊤) := by
  dsimp only
  let fA := f.resLE C.1 A.1 hA
  let gB := g.resLE C.1 B.1 hB
  let N := (Scheme.Modules.pullback (pullback.fst fA gB)).obj
    ((Scheme.Modules.pullback A.1.ι).obj M)
  have hN :
      letI := Module.compHom Γ(N, ⊤) (pullback.snd fA gB).appTop.hom
      Module.Flat Γ(B.1, ⊤) Γ(N, ⊤) :=
    FlatOver.affineOpenPullback_sections f g hM A B C hA hB
  let e := affineOpenPullbackSheafIso fst snd f g H A B C hA hB M
  exact Scheme.Modules.sections_flat_of_iso_restrictScalars e.symm ⊤
    (pullback.snd fA gB).appTop.hom hN

/-- Flatness on an affine pullback chart can be viewed over any larger affine open
containing its base-side chart. -/
lemma FlatOver.affineOpenPullback_global_sections_of_le
    {P W T Z : Scheme.{u}} (fst : P ⟶ W) (snd : P ⟶ T)
    (f : W ⟶ Z) (g : T ⟶ Z) (H : IsPullback fst snd f g)
    {M : W.Modules} [M.IsQuasicoherent] (hM : M.FlatOver f)
    (A : W.affineOpens) (B V : T.affineOpens) (C : Z.affineOpens)
    (hA : A.1 ≤ f ⁻¹ᵁ C.1) (hB : B.1 ≤ g ⁻¹ᵁ C.1) (hBV : B.1 ≤ V.1) :
    let i := affineOpenPullbackMapOfIsPullback fst snd f g H A B C hA hB
    let Q := (Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback fst).obj M)
    let hiV : (⊤ : (affineOpenPullback f g A B C hA hB).Opens) ≤
        (i ≫ snd) ⁻¹ᵁ V.1 := by
      intro x _
      dsimp [i]
      change (affineOpenPullbackMapOfIsPullback fst snd f g H A B C hA hB ≫ snd) x ∈ V.1
      rw [affineOpenPullbackMapOfIsPullback_snd]
      exact hBV ((pullback.snd (f.resLE C.1 A.1 hA)
        (g.resLE C.1 B.1 hB) x).2)
    letI := Module.compHom Γ(Q, ⊤) ((i ≫ snd).appLE V.1 ⊤ hiV).hom
    Module.Flat Γ(T, V.1) Γ(Q, ⊤) := by
  dsimp only
  let fA := f.resLE C.1 A.1 hA
  let gB := g.resLE C.1 B.1 hB
  let i := affineOpenPullbackMapOfIsPullback fst snd f g H A B C hA hB
  let Q := (Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback fst).obj M)
  let hiV : (⊤ : (affineOpenPullback f g A B C hA hB).Opens) ≤
      (i ≫ snd) ⁻¹ᵁ V.1 := by
    intro x _
    dsimp [i]
    change (affineOpenPullbackMapOfIsPullback fst snd f g H A B C hA hB ≫ snd) x ∈ V.1
    rw [affineOpenPullbackMapOfIsPullback_snd]
    exact hBV ((pullback.snd fA gB x).2)
  let hBtop : (⊤ : B.1.toScheme.Opens) ≤ B.1.ι ⁻¹ᵁ V.1 := by
    intro x _
    exact hBV x.2
  let hlocalTop : (⊤ : (affineOpenPullback f g A B C hA hB).Opens) ≤
      pullback.snd fA gB ⁻¹ᵁ (⊤ : B.1.toScheme.Opens) := le_top
  let a : Γ(T, V.1) →+* Γ(B.1, ⊤) := (B.1.ι.appLE V.1 ⊤ hBtop).hom
  let b : Γ(B.1, ⊤) →+* Γ(affineOpenPullback f g A B C hA hB, ⊤) :=
    (pullback.snd fA gB).appLE ⊤ ⊤ hlocalTop |>.hom
  have ha : a.Flat := B.1.ι.flat_appLE V.2 (isAffineOpen_top _) hBtop
  letI : Algebra Γ(T, V.1) Γ(B.1, ⊤) := a.toAlgebra
  letI : Module.Flat Γ(T, V.1) Γ(B.1, ⊤) := ha
  letI : Module Γ(B.1, ⊤) Γ(Q, ⊤) := Module.compHom Γ(Q, ⊤) b
  have hbRaw :
      letI := Module.compHom Γ(Q, ⊤) (pullback.snd fA gB).appTop.hom
      Module.Flat Γ(B.1, ⊤) Γ(Q, ⊤) :=
    FlatOver.affineOpenPullback_global_sections fst snd f g H hM A B C hA hB
  have hb : Module.Flat Γ(B.1, ⊤) Γ(Q, ⊤) := by
    apply Module.Flat.compHom_congr (pullback.snd fA gB).appTop.hom b
    · ext r
      dsimp [b]
      simp [Scheme.Hom.appLE]
    · exact hbRaw
  letI : Module.Flat Γ(B.1, ⊤) Γ(Q, ⊤) := hb
  letI : Module Γ(T, V.1) Γ(Q, ⊤) := Module.compHom Γ(Q, ⊤) (b.comp a)
  letI : IsScalarTower Γ(T, V.1) Γ(B.1, ⊤) Γ(Q, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hflat : Module.Flat Γ(T, V.1) Γ(Q, ⊤) :=
    Module.Flat.trans Γ(T, V.1) Γ(B.1, ⊤) Γ(Q, ⊤)
  apply Module.Flat.compHom_congr (b.comp a)
    ((i ≫ snd).appLE V.1 ⊤ hiV).hom
  · ext r
    dsimp [a, b, i, fA, gB]
    rw [← CommRingCat.comp_apply]
    rw [Scheme.Hom.appLE_comp_appLE]
    simp only [affineOpenPullbackMapOfIsPullback_snd]
  · exact hflat

/-- Basic-open flatness from an affine pullback chart, pushed back to the image open
in the ambient cartesian pullback.  The coefficient map on that image is the canonical
one obtained by transporting the chart's structural map through the open immersion. -/
lemma FlatOver.affineOpenPullback_ambient_basic_sections_of_le
    {P W T Z : Scheme.{u}} (fst : P ⟶ W) (snd : P ⟶ T)
    (f : W ⟶ Z) (g : T ⟶ Z) (H : IsPullback fst snd f g)
    {M : W.Modules} [M.IsQuasicoherent] (hM : M.FlatOver f)
    (A : W.affineOpens) (B V : T.affineOpens) (C : Z.affineOpens)
    (hA : A.1 ≤ f ⁻¹ᵁ C.1) (hB : B.1 ≤ g ⁻¹ᵁ C.1) (hBV : B.1 ≤ V.1)
    (t : Γ(affineOpenPullback f g A B C hA hB, ⊤)) :
    let i := affineOpenPullbackMapOfIsPullback fst snd f g H A B C hA hB
    let N := (Scheme.Modules.pullback fst).obj M
    let eSpec := (affineOpenPullback f g A B C hA hB).isoSpec.inv
    let D := PrimeSpectrum.basicOpen t
    let j := eSpec ≫ i
    let hiV : (⊤ : (affineOpenPullback f g A B C hA hB).Opens) ≤
        (i ≫ snd) ⁻¹ᵁ V.1 := by
      intro x _
      rw [affineOpenPullbackMapOfIsPullback_snd]
      exact hBV ((pullback.snd (f.resLE C.1 A.1 hA)
        (g.resLE C.1 B.1 hB) x).2)
    let c := ((i ≫ snd).appLE V.1 ⊤ hiV).hom
    let b : Γ(T, V.1) →+* Γ(Spec Γ(affineOpenPullback f g A B C hA hB, ⊤), D) :=
      (algebraMap Γ(affineOpenPullback f g A B C hA hB, ⊤) _).comp c
    let a := (j.appIso D).inv.hom.comp b
    letI := Module.compHom Γ(N, j ''ᵁ D) a
    Module.Flat Γ(T, V.1) Γ(N, j ''ᵁ D) := by
  dsimp only
  let Xchart := affineOpenPullback f g A B C hA hB
  let i := affineOpenPullbackMapOfIsPullback fst snd f g H A B C hA hB
  let N := (Scheme.Modules.pullback fst).obj M
  let Q := (Scheme.Modules.pullback i).obj N
  let eSpec := Xchart.isoSpec.inv
  let D := PrimeSpectrum.basicOpen t
  let j := eSpec ≫ i
  let hiV : (⊤ : Xchart.Opens) ≤ (i ≫ snd) ⁻¹ᵁ V.1 := by
    intro x _
    dsimp [i, Xchart]
    change (affineOpenPullbackMapOfIsPullback fst snd f g H A B C hA hB ≫ snd) x ∈ V.1
    rw [affineOpenPullbackMapOfIsPullback_snd]
    exact hBV ((pullback.snd (f.resLE C.1 A.1 hA)
      (g.resLE C.1 B.1 hB) x).2)
  let c : Γ(T, V.1) →+* Γ(Xchart, ⊤) := ((i ≫ snd).appLE V.1 ⊤ hiV).hom
  have htop :
      letI := Module.compHom Γ(Q, ⊤) c
      Module.Flat Γ(T, V.1) Γ(Q, ⊤) :=
    FlatOver.affineOpenPullback_global_sections_of_le
      fst snd f g H hM A B V C hA hB hBV
  let Qspec := (Scheme.Modules.pullback eSpec).obj Q
  have hbasic :
      letI := Module.compHom Γ(Qspec, D) c
      Module.Flat Γ(T, V.1) Γ(Qspec, D) :=
    Scheme.Modules.pullback_isoSpec_inv_flat_sections_basicOpen Q c htop t
  let b : Γ(T, V.1) →+* Γ(Spec Γ(Xchart, ⊤), D) :=
    (algebraMap Γ(Xchart, ⊤) _).comp c
  have hbasic' :
      letI := Module.compHom Γ(Qspec, D) b
      Module.Flat Γ(T, V.1) Γ(Qspec, D) := hbasic
  let Qdirect := (Scheme.Modules.pullback j).obj N
  let e : Qspec ≅ Qdirect :=
    Modules.pullbackPullbackIsoOfEq eSpec i j rfl N
  have hdirect :
      letI := Module.compHom Γ(Qdirect, D) b
      Module.Flat Γ(T, V.1) Γ(Qdirect, D) :=
    Scheme.Modules.sections_flat_of_iso_restrictScalars e D b hbasic'
  exact Scheme.Modules.sections_flat_of_pullback_openImmersion j N D b hdirect

/-- The coefficient homomorphism produced by pushing a canonical-spectrum basic open
through an open immersion is the ordinary structural `appLE` map on its image. -/
lemma openImmersion_isoSpec_basic_coefficient
    {X P T : Scheme.{u}} [IsAffine X] (i : X ⟶ P) [IsOpenImmersion i]
    (snd : P ⟶ T) (V : T.Opens)
    (hiV : (⊤ : X.Opens) ≤ (i ≫ snd) ⁻¹ᵁ V) (t : Γ(X, ⊤)) :
    let D := PrimeSpectrum.basicOpen t
    let j := X.isoSpec.inv ≫ i
    let c := ((i ≫ snd).appLE V ⊤ hiV).hom
    let b : Γ(T, V) →+* Γ(Spec Γ(X, ⊤), D) :=
      (algebraMap Γ(X, ⊤) _).comp c
    let a := (j.appIso D).inv.hom.comp b
    let hJD : j ''ᵁ D ≤ snd ⁻¹ᵁ V := by
      rintro _ ⟨x, -, rfl⟩
      exact hiV (Set.mem_univ (X.isoSpec.inv x))
    a = (snd.appLE V (j ''ᵁ D) hJD).hom := by
  dsimp only
  let D := PrimeSpectrum.basicOpen t
  let j := X.isoSpec.inv ≫ i
  let c : Γ(T, V) →+* Γ(X, ⊤) := ((i ≫ snd).appLE V ⊤ hiV).hom
  let b : Γ(T, V) →+* Γ(Spec Γ(X, ⊤), D) :=
    (algebraMap Γ(X, ⊤) _).comp c
  let a := (j.appIso D).inv.hom.comp b
  let hJD : j ''ᵁ D ≤ snd ⁻¹ᵁ V := by
    rintro _ ⟨x, -, rfl⟩
    exact hiV (Set.mem_univ (X.isoSpec.inv x))
  have hinj : Function.Injective
      (fun q : Γ(T, V) →+* Γ(P, j ''ᵁ D) ↦ (j.appIso D).hom.hom.comp q) := by
    intro q₁ q₂ hq
    ext r
    apply (ConcreteCategory.bijective_of_isIso (j.appIso D).hom).injective
    exact RingHom.congr_fun hq r
  apply hinj
  have hcancel : (j.appIso D).hom.hom.comp (j.appIso D).inv.hom = RingHom.id _ := by
    ext r
    simp
  change (j.appIso D).hom.hom.comp a =
    (j.appIso D).hom.hom.comp (snd.appLE V (j ''ᵁ D) hJD).hom
  have hleft : (j.appIso D).hom.hom.comp a = b := by
    change ((j.appIso D).hom.hom.comp (j.appIso D).inv.hom).comp b = b
    rw [hcancel, RingHom.id_comp]
  rw [hleft]
  rw [Scheme.Hom.appIso_hom']
  dsimp only [b]
  rw [← Scheme.isoSpec_inv_appLE_eq_algebraMap (X := X) D]
  ext r
  change ((((i ≫ snd).appLE V ⊤ hiV) ≫
    X.isoSpec.inv.appLE ⊤ D le_top).hom) r =
      ((snd.appLE V (j ''ᵁ D) hJD ≫
        j.appLE (j ''ᵁ D) D (j.preimage_image_eq D).ge).hom) r
  rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  rfl

/-- Coefficient-map comparison for an open in the canonical spectrum of an affine
open in an ambient scheme. -/
lemma affineOpen_fromSpec_coefficient
    {P T : Scheme.{u}} (snd : P ⟶ T) (U : P.affineOpens) (V : T.Opens)
    (hUV : U.1 ≤ snd ⁻¹ᵁ V) (D : (Spec Γ(P, U.1)).Opens) :
    let j := U.2.fromSpec
    let c := (snd.appLE V U.1 hUV).hom
    let b : Γ(T, V) →+* Γ(Spec Γ(P, U.1), D) :=
      (algebraMap Γ(P, U.1) _).comp c
    let a := (j.appIso D).inv.hom.comp b
    let hJD : j ''ᵁ D ≤ snd ⁻¹ᵁ V := by
      rintro _ ⟨x, -, rfl⟩
      apply hUV
      change U.1.ι (U.2.isoSpec.inv x) ∈ U.1
      exact (U.2.isoSpec.inv x).2
    let d := (snd.appLE V (j ''ᵁ D) hJD).hom
    a = d := by
  dsimp only
  let j := U.2.fromSpec
  let c : Γ(T, V) →+* Γ(P, U.1) := (snd.appLE V U.1 hUV).hom
  let b : Γ(T, V) →+* Γ(Spec Γ(P, U.1), D) :=
    (algebraMap Γ(P, U.1) _).comp c
  let a := (j.appIso D).inv.hom.comp b
  let hJD : j ''ᵁ D ≤ snd ⁻¹ᵁ V := by
    rintro _ ⟨x, -, rfl⟩
    apply hUV
    change U.1.ι (U.2.isoSpec.inv x) ∈ U.1
    exact (U.2.isoSpec.inv x).2
  let d : Γ(T, V) →+* Γ(P, j ''ᵁ D) := (snd.appLE V (j ''ᵁ D) hJD).hom
  have hinj : Function.Injective
      (fun q : Γ(T, V) →+* Γ(P, j ''ᵁ D) ↦ (j.appIso D).hom.hom.comp q) := by
    intro q₁ q₂ hq
    ext r
    apply (ConcreteCategory.bijective_of_isIso (j.appIso D).hom).injective
    exact RingHom.congr_fun hq r
  suffices hresult : a = d by
    simpa only [a, b, c, d, j] using hresult
  apply hinj
  have hcancel : (j.appIso D).hom.hom.comp (j.appIso D).inv.hom = RingHom.id _ := by
    ext r
    simp
  change (j.appIso D).hom.hom.comp a = (j.appIso D).hom.hom.comp d
  have hleft : (j.appIso D).hom.hom.comp a = b := by
    change ((j.appIso D).hom.hom.comp (j.appIso D).inv.hom).comp b = b
    rw [hcancel, RingHom.id_comp]
  rw [hleft, Scheme.Hom.appIso_hom']
  dsimp only [b]
  rw [← IsAffineOpen.fromSpec_appLE_eq_algebraMap U.2 D]
  ext r
  dsimp only [d]
  change ((snd.appLE V U.1 hUV ≫ U.2.fromSpec.appLE U.1 D (by simp)).hom) r =
    ((snd.appLE V (j ''ᵁ D) hJD ≫
      j.appLE (j ''ᵁ D) D (j.preimage_image_eq D).ge).hom) r
  rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]

/-- Flatness of sections on an affine open follows from pointwise flatness on ambient
basic opens contained in it.  This is the affine gluing interface used for relative
flatness after constructing cartesian pullback charts. -/
lemma FlatOver.flat_sections_affine_of_pointwise_basicOpen
    {P T : Scheme.{u}} (snd : P ⟶ T) (N : P.Modules) [N.IsQuasicoherent]
    (U : P.affineOpens) (V : T.affineOpens) (hUV : U.1 ≤ snd ⁻¹ᵁ V.1)
    (hlocal : ∀ p : P, p ∈ U.1 → ∃ r : Γ(P, U.1), p ∈ P.basicOpen r ∧
      (let hrV : P.basicOpen r ≤ snd ⁻¹ᵁ V.1 := (P.basicOpen_le r).trans hUV
       letI := Module.compHom Γ(N, P.basicOpen r)
         (snd.appLE V.1 (P.basicOpen r) hrV).hom
       Module.Flat Γ(T, V.1) Γ(N, P.basicOpen r))) :
    letI := Module.compHom Γ(N, U.1) (snd.appLE V.1 U.1 hUV).hom
    Module.Flat Γ(T, V.1) Γ(N, U.1) := by
  let j := U.2.fromSpec
  let Mspec := (Scheme.Modules.pullback j).obj N
  let dU : Γ(T, V.1) →+* Γ(P, U.1) := (snd.appLE V.1 U.1 hUV).hom
  letI : Algebra Γ(T, V.1) Γ(P, U.1) := dU.toAlgebra
  letI : Mspec.IsQuasicoherent := by
    let e := (Scheme.Modules.restrictFunctorIsoPullback j).app N
    exact (SheafOfModules.isQuasicoherent (Spec Γ(P, U.1)).ringCatSheaf).prop_of_iso
      e inferInstance
  have hpoint : ∀ x : Spec Γ(P, U.1), ∃ r : Γ(P, U.1),
      x ∈ PrimeSpectrum.basicOpen r ∧
      (letI := Module.compHom Γ(Mspec, PrimeSpectrum.basicOpen r) dU
       Module.Flat Γ(T, V.1) Γ(Mspec, PrimeSpectrum.basicOpen r)) := by
    intro x
    have hxU : j x ∈ U.1 := by
      change U.1.ι (U.2.isoSpec.inv x) ∈ U.1
      exact (U.2.isoSpec.inv x).2
    obtain ⟨r, hxr, hrflat⟩ := hlocal (j x) hxU
    refine ⟨r, ?_, ?_⟩
    · rw [← U.2.fromSpec_preimage_basicOpen]
      exact hxr
    · let D := PrimeSpectrum.basicOpen r
      let hDV : P.basicOpen r ≤ snd ⁻¹ᵁ V.1 := (P.basicOpen_le r).trans hUV
      let hJD : j ''ᵁ D ≤ snd ⁻¹ᵁ V.1 := by
        rintro _ ⟨y, -, rfl⟩
        apply hUV
        change U.1.ι (U.2.isoSpec.inv y) ∈ U.1
        exact (U.2.isoSpec.inv y).2
      let dD : Γ(T, V.1) →+* Γ(P, P.basicOpen r) :=
        (snd.appLE V.1 (P.basicOpen r) hDV).hom
      let dJ : Γ(T, V.1) →+* Γ(P, j ''ᵁ D) :=
        (snd.appLE V.1 (j ''ᵁ D) hJD).hom
      have hopen : j ''ᵁ D = P.basicOpen r := U.2.fromSpec_image_basicOpen r
      have htransport :
          let a' : Γ(T, V.1) →+* Γ(P, j ''ᵁ D) := hopen.symm ▸ dD
          letI := Module.compHom Γ(N, j ''ᵁ D) a'
          Module.Flat Γ(T, V.1) Γ(N, j ''ᵁ D) :=
        Scheme.Modules.sections_flat_of_eq N (P.basicOpen r) (j ''ᵁ D)
          hopen.symm dD hrflat
      have himage :
          letI := Module.compHom Γ(N, j ''ᵁ D) dJ
          Module.Flat Γ(T, V.1) Γ(N, j ''ᵁ D) := by
        apply Module.Flat.compHom_congr (hopen.symm ▸ dD) dJ
        · exact Scheme.Hom.appLE_hom_transport snd V.1 (P.basicOpen r)
            (j ''ᵁ D) hopen.symm hDV hJD
        · exact htransport
      have hpull :
          letI := Module.compHom Γ(Mspec, D) ((j.appIso D).hom.hom.comp dJ)
          Module.Flat Γ(T, V.1) Γ(Mspec, D) :=
        Scheme.Modules.pullback_openImmersion_sections_flat_restrictScalars
          j N D dJ himage
      let b : Γ(T, V.1) →+* Γ(Spec Γ(P, U.1), D) :=
        (algebraMap Γ(P, U.1) _).comp dU
      let a := (j.appIso D).inv.hom.comp b
      have ha : a = dJ := affineOpen_fromSpec_coefficient snd U V.1 hUV D
      have hcoef : (j.appIso D).hom.hom.comp dJ = b := by
        rw [← ha]
        change ((j.appIso D).hom.hom.comp (j.appIso D).inv.hom).comp b = b
        rw [show (j.appIso D).hom.hom.comp (j.appIso D).inv.hom = RingHom.id _ by
          ext z
          simp, RingHom.id_comp]
      exact Module.Flat.compHom_congr ((j.appIso D).hom.hom.comp dJ) b hcoef hpull
  have hSpec :
      letI := Module.compHom Γ(Mspec, ⊤) dU
      Module.Flat Γ(T, V.1) Γ(Mspec, ⊤) :=
    Scheme.Modules.flat_sections_top_of_pointwise_basicOpen Mspec hpoint
  let bTop : Γ(T, V.1) →+* Γ(Spec Γ(P, U.1), ⊤) :=
    (algebraMap Γ(P, U.1) _).comp dU
  have hSpec' :
      letI := Module.compHom Γ(Mspec, ⊤) bTop
      Module.Flat Γ(T, V.1) Γ(Mspec, ⊤) := hSpec
  have hpush :
      let a := (j.appIso ⊤).inv.hom.comp bTop
      letI := Module.compHom Γ(N, j ''ᵁ (⊤ : (Spec Γ(P, U.1)).Opens)) a
      Module.Flat Γ(T, V.1) Γ(N, j ''ᵁ (⊤ : (Spec Γ(P, U.1)).Opens)) :=
    Scheme.Modules.sections_flat_of_pullback_openImmersion j N ⊤ bTop hSpec'
  let htopV : j ''ᵁ (⊤ : (Spec Γ(P, U.1)).Opens) ≤ snd ⁻¹ᵁ V.1 := by
    rintro _ ⟨x, -, rfl⟩
    apply hUV
    change U.1.ι (U.2.isoSpec.inv x) ∈ U.1
    exact (U.2.isoSpec.inv x).2
  let dTop := (snd.appLE V.1 (j ''ᵁ (⊤ : (Spec Γ(P, U.1)).Opens)) htopV).hom
  let aTop := (j.appIso ⊤).inv.hom.comp bTop
  have haTop : aTop = dTop := affineOpen_fromSpec_coefficient snd U V.1 hUV ⊤
  have hpush' :
      letI := Module.compHom Γ(N, j ''ᵁ (⊤ : (Spec Γ(P, U.1)).Opens)) dTop
      Module.Flat Γ(T, V.1) Γ(N, j ''ᵁ (⊤ : (Spec Γ(P, U.1)).Opens)) :=
    Module.Flat.compHom_congr aTop dTop haTop hpush
  have hopenTop : j ''ᵁ (⊤ : (Spec Γ(P, U.1)).Opens) = U.1 := by
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact U.2.opensRange_fromSpec
  have htransportTop :
      let d' : Γ(T, V.1) →+* Γ(P, U.1) := hopenTop ▸ dTop
      letI := Module.compHom Γ(N, U.1) d'
      Module.Flat Γ(T, V.1) Γ(N, U.1) :=
    Scheme.Modules.sections_flat_of_eq N _ U.1 hopenTop dTop hpush'
  apply Module.Flat.compHom_congr (hopenTop ▸ dTop) dU
  · exact Scheme.Hom.appLE_hom_transport snd V.1 _ U.1 hopenTop htopV hUV
  · exact htransportTop

/-- The preceding chart calculation expressed on the ambient basic open determined
by a section of the chart image. -/
lemma FlatOver.affineOpenPullback_ambient_basicOpen_of_le
    {P W T Z : Scheme.{u}} (fst : P ⟶ W) (snd : P ⟶ T)
    (f : W ⟶ Z) (g : T ⟶ Z) (H : IsPullback fst snd f g)
    {M : W.Modules} [M.IsQuasicoherent] (hM : M.FlatOver f)
    (A : W.affineOpens) (B V : T.affineOpens) (C : Z.affineOpens)
    (hA : A.1 ≤ f ⁻¹ᵁ C.1) (hB : B.1 ≤ g ⁻¹ᵁ C.1) (hBV : B.1 ≤ V.1)
    (s : Γ(P, (affineOpenPullbackMapOfIsPullback
      fst snd f g H A B C hA hB).opensRange)) :
    let N := (Scheme.Modules.pullback fst).obj M
    let hsV : P.basicOpen s ≤ snd ⁻¹ᵁ V.1 := by
      intro p hp
      have hpRange := P.basicOpen_le s hp
      exact hBV ((opensRange_affineOpenPullbackMapOfIsPullback_le
        fst snd f g H A B C hA hB hpRange).2)
    letI := Module.compHom Γ(N, P.basicOpen s)
      (snd.appLE V.1 (P.basicOpen s) hsV).hom
    Module.Flat Γ(T, V.1) Γ(N, P.basicOpen s) := by
  dsimp only
  let i := affineOpenPullbackMapOfIsPullback fst snd f g H A B C hA hB
  let N := (Scheme.Modules.pullback fst).obj M
  let t := (i.appLE i.opensRange ⊤ (by simp)).hom s
  let D := PrimeSpectrum.basicOpen t
  let j := (affineOpenPullback f g A B C hA hB).isoSpec.inv ≫ i
  let hiV : (⊤ : (affineOpenPullback f g A B C hA hB).Opens) ≤
      (i ≫ snd) ⁻¹ᵁ V.1 := by
    intro x _
    dsimp [i]
    change (affineOpenPullbackMapOfIsPullback fst snd f g H A B C hA hB ≫ snd) x ∈ V.1
    rw [affineOpenPullbackMapOfIsPullback_snd]
    exact hBV ((pullback.snd (f.resLE C.1 A.1 hA)
      (g.resLE C.1 B.1 hB) x).2)
  let c : Γ(T, V.1) →+* Γ(affineOpenPullback f g A B C hA hB, ⊤) :=
    ((i ≫ snd).appLE V.1 ⊤ hiV).hom
  let b : Γ(T, V.1) →+* Γ(Spec Γ(affineOpenPullback f g A B C hA hB, ⊤), D) :=
    (algebraMap Γ(affineOpenPullback f g A B C hA hB, ⊤) _).comp c
  let a := (j.appIso D).inv.hom.comp b
  have hflat :
      letI := Module.compHom Γ(N, j ''ᵁ D) a
      Module.Flat Γ(T, V.1) Γ(N, j ''ᵁ D) :=
    FlatOver.affineOpenPullback_ambient_basic_sections_of_le
      fst snd f g H hM A B V C hA hB hBV t
  let hJD : j ''ᵁ D ≤ snd ⁻¹ᵁ V.1 := by
    rintro _ ⟨x, -, rfl⟩
    exact hiV (Set.mem_univ ((affineOpenPullback f g A B C hA hB).isoSpec.inv x))
  have ha : a = (snd.appLE V.1 (j ''ᵁ D) hJD).hom :=
    openImmersion_isoSpec_basic_coefficient i snd V.1 hiV t
  have hflat' :
      letI := Module.compHom Γ(N, j ''ᵁ D)
        (snd.appLE V.1 (j ''ᵁ D) hJD).hom
      Module.Flat Γ(T, V.1) Γ(N, j ''ᵁ D) :=
    Module.Flat.compHom_congr a _ ha hflat
  let hopen : j ''ᵁ D = P.basicOpen s :=
    isoSpecInv_comp_image_basicOpen_isoOpensRange i s
  have htransport :
      let a' : Γ(T, V.1) →+* Γ(P, P.basicOpen s) :=
        hopen ▸ (snd.appLE V.1 (j ''ᵁ D) hJD).hom
      letI := Module.compHom Γ(N, P.basicOpen s) a'
      Module.Flat Γ(T, V.1) Γ(N, P.basicOpen s) :=
    Scheme.Modules.sections_flat_of_eq N (j ''ᵁ D) (P.basicOpen s)
      hopen (snd.appLE V.1 (j ''ᵁ D) hJD).hom hflat'
  let hsV : P.basicOpen s ≤ snd ⁻¹ᵁ V.1 := by
    intro p hp
    have hpRange := P.basicOpen_le s hp
    exact hBV ((opensRange_affineOpenPullbackMapOfIsPullback_le
      fst snd f g H A B C hA hB hpRange).2)
  apply Module.Flat.compHom_congr
    (hopen ▸ (snd.appLE V.1 (j ''ᵁ D) hJD).hom)
    (snd.appLE V.1 (P.basicOpen s) hsV).hom
  · exact Scheme.Hom.appLE_hom_transport snd V.1 (j ''ᵁ D)
      (P.basicOpen s) hopen hJD hsV
  · exact htransport

variable (F : X.Modules) (f : X ⟶ S)

/-- Background definition for Theorem 2.1.3 (the implicit definition of a
point of the Quot functor): let `F` be a sheaf of modules on `X` and `f : X ⟶ S` a
morphism of schemes. For a scheme `T` over `S`, a **flat family of finitely presented
quotients of `F`** over `T`: a quasi-coherent, finitely presented sheaf of modules `Q` on
`X_T = T ×_S X`, flat over `T`, with an epimorphism `F_{X_T} ↠ Q` from the pullback of
`F`. Two such quotients define the same point of the Quot functor when they are isomorphic
compatibly with the projections. -/
structure QuotientPullbackData (T : Over S) : Type (u + 1) where
  /-- The quotient sheaf of modules on `X_T`. -/
  Q : ((Over.pullback f).obj T).left.Modules
  /-- The quotient is quasi-coherent. -/
  isQuasicoherent : Q.IsQuasicoherent
  /-- The quotient is finitely presented. -/
  isFinitePresentation : Q.IsFinitePresentation
  /-- The quotient is flat over the base `T`. -/
  flatOver : Q.FlatOver (pullback.fst T.hom f)
  /-- The projection from the pullback of `F` to `X_T`. -/
  π : (Modules.pullback ((Over.pullback f).obj T).hom).obj F ⟶ Q
  /-- The projection is an epimorphism. -/
  epi : Epi π

namespace QuotientPullbackData

variable {F f} {T T' : Over S}

/-- Two flat families of finitely presented quotients of `F` over `T` are equivalent if
they are isomorphic compatibly with the projections. -/
protected def setoid (F : X.Modules) (f : X ⟶ S) (T : Over S) :
    Setoid (QuotientPullbackData F f T) where
  r x y := ∃ e : x.Q ≅ y.Q, x.π ≫ e.hom = y.π
  iseqv := by
    refine ⟨fun x ↦ ⟨Iso.refl _, Category.comp_id _⟩, ?_, ?_⟩
    · rintro x y ⟨e, he⟩
      refine ⟨e.symm, ?_⟩
      rw [← he]
      simp
    · rintro x y z ⟨e, he⟩ ⟨e', he'⟩
      exact ⟨e ≪≫ e', by rw [Iso.trans_hom, ← Category.assoc, he, he']⟩

/-- Pull back a flat family of finitely presented quotients of `F` along a morphism
`T' ⟶ T` of schemes over `S`. -/
noncomputable def pullback (g : T' ⟶ T) (x : QuotientPullbackData F f T) :
    QuotientPullbackData F f T' where
  Q := (Modules.pullback ((Over.pullback f).map g).left).obj x.Q
  isQuasicoherent :=
    haveI := x.isQuasicoherent
    inferInstance
  isFinitePresentation := by
    haveI := x.isFinitePresentation
    infer_instance
  flatOver := by
    haveI := x.isQuasicoherent
    let G := ((Over.pullback f).map g).left
    let p' := pullback.fst T'.hom f
    let p := pullback.fst T.hom f
    let N := (Modules.pullback G).obj x.Q
    have H : IsPullback G p' p g.left := overPullbackMap_isPullback g
    intro U V hUV
    apply FlatOver.flat_sections_affine_of_pointwise_basicOpen p' N U V hUV
    intro q hqU
    obtain ⟨A, B, C, hA, hB, hBV, r, s, hrs, hqr⟩ :=
      exists_common_basicOpen_affineOpenPullbackMapOfIsPullback
        G p' p g.left H U V q hqU (hUV hqU)
    refine ⟨r, hqr, ?_⟩
    let hsV : (Limits.pullback T'.hom f).basicOpen s ≤ p' ⁻¹ᵁ V.1 := by
      intro y hy
      have hyRange := (Limits.pullback T'.hom f).basicOpen_le s hy
      exact hBV ((opensRange_affineOpenPullbackMapOfIsPullback_le
        G p' p g.left H A B C hA hB hyRange).2)
    have hflatS :
        letI := Module.compHom Γ(N, (Limits.pullback T'.hom f).basicOpen s)
          (p'.appLE V.1 ((Limits.pullback T'.hom f).basicOpen s) hsV).hom
        Module.Flat Γ(T'.left, V.1)
          Γ(N, (Limits.pullback T'.hom f).basicOpen s) :=
      FlatOver.affineOpenPullback_ambient_basicOpen_of_le
        G p' p g.left H x.flatOver A B V C hA hB hBV s
    let hrV : (Limits.pullback T'.hom f).basicOpen r ≤ p' ⁻¹ᵁ V.1 :=
      ((Limits.pullback T'.hom f).basicOpen_le r).trans hUV
    have htransport :
        let d' : Γ(T'.left, V.1) →+*
            Γ(Limits.pullback T'.hom f, (Limits.pullback T'.hom f).basicOpen r) :=
          hrs.symm ▸
            (p'.appLE V.1 ((Limits.pullback T'.hom f).basicOpen s) hsV).hom
        letI := Module.compHom Γ(N, (Limits.pullback T'.hom f).basicOpen r) d'
        Module.Flat Γ(T'.left, V.1)
          Γ(N, (Limits.pullback T'.hom f).basicOpen r) :=
      Scheme.Modules.sections_flat_of_eq N _ _ hrs.symm
        (p'.appLE V.1 ((Limits.pullback T'.hom f).basicOpen s) hsV).hom hflatS
    apply Module.Flat.compHom_congr
      (hrs.symm ▸ (p'.appLE V.1
        ((Limits.pullback T'.hom f).basicOpen s) hsV).hom)
      (p'.appLE V.1 ((Limits.pullback T'.hom f).basicOpen r) hrV).hom
    · exact Scheme.Hom.appLE_hom_transport p' V.1 _ _ hrs.symm hsV hrV
    · exact htransport
  π := (PullbackQuotient.pullbackComparison F ((Over.pullback f).map g)).hom ≫
    (Modules.pullback ((Over.pullback f).map g).left).map x.π
  epi :=
    haveI := x.epi
    inferInstance

/-- Pulling back flat families of finitely presented quotients preserves equivalence. -/
lemma pullback_r {g : T' ⟶ T} {x y : QuotientPullbackData F f T}
    (h : (QuotientPullbackData.setoid F f T).r x y) :
    (QuotientPullbackData.setoid F f T').r (x.pullback g) (y.pullback g) := by
  obtain ⟨e, he⟩ := h
  refine ⟨(Modules.pullback ((Over.pullback f).map g).left).mapIso e, ?_⟩
  simp only [QuotientPullbackData.pullback, Functor.mapIso_hom, Category.assoc,
    ← Functor.map_comp, he]

/-- Pulling back along the identity is equivalent to not pulling back at all. -/
lemma pullback_id_r (x : QuotientPullbackData F f T) :
    (QuotientPullbackData.setoid F f T).r (x.pullback (𝟙 T)) x :=
  ⟨(Modules.pullbackCongr (congrArg CommaMorphism.left
      ((Over.pullback f).map_id T) :
        CommaMorphism.left ((Over.pullback f).map (𝟙 T)) =
          𝟙 ((Over.pullback f).obj T).left)).app x.Q
    ≪≫ (Modules.pullbackId ((Over.pullback f).obj T).left).app x.Q,
    PullbackQuotient.comparison_pullback_id F ((Over.pullback f).map (𝟙 T))
      ((Over.pullback f).map_id T) x.π⟩

/-- Pulling back along a composition is equivalent to the composite of the pullbacks. -/
lemma pullback_comp_r (g : T' ⟶ T) {T'' : Over S} (g' : T'' ⟶ T')
    (x : QuotientPullbackData F f T) :
    (QuotientPullbackData.setoid F f T'').r ((x.pullback g).pullback g')
      (x.pullback (g' ≫ g)) :=
  ⟨(Modules.pullbackComp (CommaMorphism.left ((Over.pullback f).map g'))
      (CommaMorphism.left ((Over.pullback f).map g))).app x.Q ≪≫
    ((Modules.pullbackCongr ((congrArg CommaMorphism.left
      (((Over.pullback f).map_comp g' g).symm :
        (Over.pullback f).map g' ≫ (Over.pullback f).map g =
          (Over.pullback f).map (g' ≫ g))).symm :
      CommaMorphism.left ((Over.pullback f).map (g' ≫ g)) =
        CommaMorphism.left ((Over.pullback f).map g') ≫
          CommaMorphism.left ((Over.pullback f).map g))).app x.Q).symm,
    PullbackQuotient.comparison_pullback_comp F ((Over.pullback f).map g)
      ((Over.pullback f).map g') (((Over.pullback f).map_comp g' g).symm) x.π⟩

end QuotientPullbackData

end Modules

/-- Background definition for Theorem 2.1.3 (the implicit definition of the
functor; polynomial-free variant): let `F` be a sheaf of modules on `X` and `f : X ⟶ S` a
morphism of schemes. The **Quot functor** `Quot(F/X/S)` on schemes over `S`: its points
over `T → S` are the isomorphism classes of quasi-coherent, finitely presented quotients
`F_{X_T} ↠ Q` on `X_T` that are flat over `T`.

The subfunctor `Quot^P` below cuts this down by a fixed fiberwise Hilbert polynomial.
Pseudofunctor coherence for pullback of module sheaves is handled explicitly in the
functor-law proofs. -/
noncomputable def quotFunctor (F : X.Modules) (f : X ⟶ S) : (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := Quotient (Modules.QuotientPullbackData.setoid F f (unop T))
  map g := ↾fun x ↦ Quotient.map
    (Modules.QuotientPullbackData.pullback (F := F) (f := f) g.unop)
    (fun _ _ h ↦ Modules.QuotientPullbackData.pullback_r h) x
  map_id T := by
    refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
    obtain ⟨a, rfl⟩ := Quotient.exists_rep x
    exact Quotient.sound (Modules.QuotientPullbackData.pullback_id_r a)
  map_comp u v := by
    refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
    obtain ⟨a, rfl⟩ := Quotient.exists_rep x
    exact Quotient.sound ((Modules.QuotientPullbackData.setoid F f _).symm
      (Modules.QuotientPullbackData.pullback_comp_r u.unop v.unop a))

/-- Background definition for Theorem 2.1.3 (the implicit transport): a Quot
datum over `T` lives on `X_T = T ×_S ℙ^n_S`; this reads it as a sheaf on `ℙ^n_T`, along the
base-change comparison `Scheme.projectiveSpaceOverBaseChangeIso`.

This is what lets a *fiberwise* condition be imposed on a Quot datum: fibers are taken over
points of `T`, and `ℙ^n_T` is the space whose fibers over those points are the `ℙ^n_{κ(t)}`
on which Hilbert polynomials are computed. -/
noncomputable def quotDataOnProjectiveSpace
    (F : (Scheme.projectiveSpaceOver n S).Modules) {T : Over S}
    (x : Modules.QuotientPullbackData F (Scheme.projectiveSpaceOverπ n S) T) :
    (Scheme.projectiveSpaceOver n T.left).Modules :=
  (Scheme.Modules.pullback
    (Scheme.projectiveSpaceOverBaseChangeIso n T.hom).inv).obj x.Q

/-- Background definition for Theorem 2.1.3 (pullback coherence):
reading a pulled-back Quot datum on `ℙⁿ_{T'}` agrees with pulling its sheaf on
`ℙⁿ_T` back along `ℙⁿ_{T'} ⟶ ℙⁿ_T`. -/
noncomputable def Modules.QuotientPullbackData.quotDataOnProjectiveSpace_pullbackIso
    {F : (Scheme.projectiveSpaceOver n S).Modules} {T T' : Over S}
    (g : T' ⟶ T)
    (x : Modules.QuotientPullbackData F (Scheme.projectiveSpaceOverπ n S) T) :
    quotDataOnProjectiveSpace F (x.pullback g) ≅
      (Scheme.Modules.pullback (Scheme.projectiveSpaceOverMap n g.left)).obj
        (quotDataOnProjectiveSpace F x) :=
  (Scheme.Modules.pullbackComp
      (Scheme.projectiveSpaceOverBaseChangeIso n T'.hom).inv
      ((Over.pullback (Scheme.projectiveSpaceOverπ n S)).map g).left).app x.Q ≪≫
    (Scheme.Modules.pullbackCongr
      (Scheme.projectiveSpaceOverBaseChangeIso_inv_naturality n g)).app x.Q ≪≫
    ((Scheme.Modules.pullbackComp (Scheme.projectiveSpaceOverMap n g.left)
      (Scheme.projectiveSpaceOverBaseChangeIso n T.hom).inv).app x.Q).symm

/-- Background definition for Theorem 2.1.3 (the implicit condition defining
`Quot^P`): a Quot datum has fiberwise Hilbert polynomial `P` when the sheaf it determines on
`ℙ^n_T` does. -/
def Modules.QuotientPullbackData.HasFiberwiseHilbertPolynomial
    {F : (Scheme.projectiveSpaceOver n S).Modules} {T : Over S}
    (x : Modules.QuotientPullbackData F (Scheme.projectiveSpaceOverπ n S) T)
    (P : Polynomial ℚ) : Prop :=
  Scheme.HasFiberwiseHilbertPolynomial (quotDataOnProjectiveSpace F x) P

/-- API lemma for Theorem 2.1.3 (well-definedness of `Quot^P`): the
fiberwise Hilbert polynomial of a Quot datum is stable under pullback along `T' ⟶ T`.

This is what makes `Quot^P` a subfunctor rather than merely a family of subsets: the fiber
over a field-valued point `Spec K ⟶ T'` is the fiber of the original family over the
composite `Spec K ⟶ T' ⟶ T`. The coefficient field therefore stays fixed, and the
proof is pullback composition together with naturality of
`Scheme.projectiveSpaceOverBaseChangeIso`. -/
theorem Modules.QuotientPullbackData.hasFiberwiseHilbertPolynomial_pullback
    {F : (Scheme.projectiveSpaceOver n S).Modules} {T T' : Over S} (g : T' ⟶ T)
    {x : Modules.QuotientPullbackData F (Scheme.projectiveSpaceOverπ n S) T}
    {P : Polynomial ℚ} (h : x.HasFiberwiseHilbertPolynomial P) :
    (x.pullback g).HasFiberwiseHilbertPolynomial P := by
  intro K hK s
  let e₀ := (Scheme.Modules.pullback (Scheme.projectiveSpaceOverMap n s)).mapIso
    (Modules.QuotientPullbackData.quotDataOnProjectiveSpace_pullbackIso g x)
  let e₁ := (Scheme.Modules.pullbackComp
    (Scheme.projectiveSpaceOverMap n s)
    (Scheme.projectiveSpaceOverMap n g.left)).app
      (quotDataOnProjectiveSpace F x)
  let e₂ := (Scheme.Modules.pullbackCongr
    (Scheme.projectiveSpaceOverMap_comp n s g.left)).app
      (quotDataOnProjectiveSpace F x)
  apply Scheme.HasHilbertPolynomialOver.iso (e₀ ≪≫ e₁ ≪≫ e₂).symm
  exact h K hK (s ≫ g.left)

/-- Background definition for Theorem 2.1.3 (the implicit definition of
`Quot^P`): the subfunctor of `Quot(F/ℙ^n_S/S)` consisting of those quotients all of whose
fibers have Hilbert polynomial `P`.

The condition is phrased as "*some* representative of the isomorphism class has fiberwise
Hilbert polynomial `P`", which is well defined on the quotient without needing to know in
advance that the condition is an isomorphism invariant. It is one, since isomorphic
quotients have isomorphic fibers; that fact is not needed to make the definition and is not
asserted here. -/
noncomputable def quotFunctorP (F : (Scheme.projectiveSpaceOver n S).Modules)
    (P : Polynomial ℚ) : (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := { x : (quotFunctor F (Scheme.projectiveSpaceOverπ n S)).obj T //
    ∃ a : Modules.QuotientPullbackData F (Scheme.projectiveSpaceOverπ n S) T.unop,
      Quotient.mk _ a = x ∧ a.HasFiberwiseHilbertPolynomial P }
  map g := ↾fun x ↦ ⟨(quotFunctor F (Scheme.projectiveSpaceOverπ n S)).map g x.1, by
    obtain ⟨a, ha, hP⟩ := x.2
    exact ⟨a.pullback g.unop, by rw [← ha]; rfl,
      Modules.QuotientPullbackData.hasFiberwiseHilbertPolynomial_pullback _ hP⟩⟩
  map_id T := by
    refine ConcreteCategory.hom_ext _ _ fun x ↦ Subtype.ext ?_
    exact ConcreteCategory.congr_hom
      ((quotFunctor F (Scheme.projectiveSpaceOverπ n S)).map_id T) x.1
  map_comp u v := by
    refine ConcreteCategory.hom_ext _ _ fun x ↦ Subtype.ext ?_
    exact ConcreteCategory.congr_hom
      ((quotFunctor F (Scheme.projectiveSpaceOverπ n S)).map_comp u v) x.1

/-- The forgetful map `Quot^P(F/ℙ^n_S) ⟶ Quot(F/ℙ^n_S)`. -/
noncomputable def quotFunctorPToQuotFunctor
    (F : (Scheme.projectiveSpaceOver n S).Modules) (P : Polynomial ℚ) :
    quotFunctorP F P ⟶ quotFunctor F (Scheme.projectiveSpaceOverπ n S) where
  app _ := ↾fun x ↦ x.1

/-- API lemma for Theorem 2.1.3 (small-model reduction):
representability of a universe-small strict model of Quot transports to the
isomorphism-class model. The remaining construction must supply such a strict kernel
model to which Zariski-local representability applies. -/
theorem exists_quotFunctor_representableBy_of_small_model
    (n : ℕ) (S : Scheme.{u}) (F : (Scheme.projectiveSpaceOver n S).Modules)
    (G : CategoryTheory.Functor (Over S)ᵒᵖ (Type u))
    (e : G ⋙ uliftFunctor.{u + 1, u} ≅
      quotFunctor F (Scheme.projectiveSpaceOverπ n S))
    (hG : ∃ Q : Over S, Nonempty (G.RepresentableBy Q) ∧ LocallyOfFiniteType Q.hom) :
    ∃ Q : Over S,
      Nonempty ((quotFunctor F (Scheme.projectiveSpaceOverπ n S)).RepresentableBy Q) ∧
      LocallyOfFiniteType Q.hom := by
  obtain ⟨Q, ⟨hQ⟩, hQft⟩ := hG
  exact ⟨Q, ⟨((Functor.representableByUliftFunctorEquiv).symm hQ).ofIso e⟩, hQft⟩

/-- API lemma for Theorem 2.1.3 (polynomial-free part):
representability of the Quot functor. Let `S` be a locally noetherian scheme, `n` a
natural number, and `F` a quasi-coherent, finitely presented sheaf of modules on `ℙ^n_S`.
The Quot functor `Quot(F/ℙ^n_S/S)` is representable by a scheme locally of finite type
over `S`.

The book's theorem asserts that each `Quot^P` (fixed fiberwise Hilbert polynomial, for `F`
a quotient of `O(-l)^{⊕r}`) is representable by a projective scheme over `S`. The twisting
sheaves that refinement needs now exist (Stacks 01MN), together with the fiberwise Hilbert
polynomial `Scheme.HasFiberwiseHilbertPolynomial` and the base-change comparison
`Scheme.projectiveSpaceOverBaseChangeIso`; the fixed-polynomial subfunctor is now
functorial, while its representability and projectivity remain the book's substantive
claims. See the section COMMENTARY.md. -/
theorem exists_quotFunctor_representableBy (n : ℕ) (S : Scheme.{u})
    [IsLocallyNoetherian S] (F : (Scheme.projectiveSpaceOver n S).Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation] :
    ∃ Q : Over S,
      Nonempty ((quotFunctor F (Scheme.projectiveSpaceOverπ n S)).RepresentableBy Q) ∧
      LocallyOfFiniteType Q.hom := by
  sorry

/-- Background definition for Theorem 2.1.3 (the printed presentation
hypothesis): `F` is a quotient of `O(-l)^{⊕r}` for some twist and finite rank. -/
def Modules.IsQuotientOfTwistedFree {n : ℕ} {S : Scheme.{u}}
    (F : (Scheme.projectiveSpaceOver n S).Modules) : Prop :=
  ∃ (l : ℤ) (r : ℕ)
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n S (-l)) ⟶ F), Epi p

/-- API lemma for Theorem 2.1.3 (closed-subfunctor
reduction): a relatively closed subfunctor of a projectively representable functor is
projectively representable. For `O(-l)^{⊕r} ↠ F`, this isolates the book's
closed-subfunctor exercise and the twisted-free Quot theorem. -/
theorem exists_quotFunctorP_representableBy_of_relative_closed
    {n : ℕ} {S : Scheme.{u}} {F : (Scheme.projectiveSpaceOver n S).Modules}
    {P : Polynomial ℚ} {G : CategoryTheory.Functor (Over S)ᵒᵖ (Type (u + 1))}
    (α : quotFunctorP F P ⟶ G)
    (hα : MorphismProperty.relative uliftYoneda.{u + 1}
      (MorphismProperty.over
        (@IsClosedImmersion : MorphismProperty Scheme.{u})) α)
    (hG : ∃ Q₀ : Over S, Nonempty (G.RepresentableBy Q₀) ∧ IsHProjective Q₀.hom) :
    ∃ Q : Over S, Nonempty ((quotFunctorP F P).RepresentableBy Q) ∧
      IsHProjective Q.hom := by
  obtain ⟨Q₀, ⟨eG⟩, hQ₀⟩ := hG
  let eG' : uliftYoneda.{u + 1}.obj Q₀ ≅ G :=
    (Functor.RepresentableBy.equivUliftYonedaIso G Q₀) eG
  let Q : Over S := hα.rep.pullback eG'.hom
  let j : Q ⟶ Q₀ := hα.rep.snd eG'.hom
  have hj : IsClosedImmersion j.left := hα.property_snd eG'.hom
  haveI : IsIso (hα.rep.fst eG'.hom) :=
    (hα.rep.isPullback eG'.hom).isIso_fst_of_isIso
  let eF' : uliftYoneda.{u + 1}.obj Q ≅ quotFunctorP F P :=
    asIso (hα.rep.fst eG'.hom)
  let eF : (quotFunctorP F P).RepresentableBy Q :=
    (Functor.RepresentableBy.equivUliftYonedaIso (quotFunctorP F P) Q).symm eF'
  refine ⟨Q, ⟨eF⟩, ?_⟩
  obtain ⟨m, i, hi, hcomp⟩ := hQ₀
  refine ⟨m, j.left ≫ i, ?_, ?_⟩
  · letI : IsClosedImmersion j.left := hj
    letI : IsClosedImmersion i := hi
    infer_instance
  · rw [Category.assoc, hcomp, Over.w j]

end AlgebraicGeometry.Scheme

end ThmQuotSchemeRepresentable
