module

public import StacksProject.Algebra.NormalRings.«definition-ring-normal»
public import StacksProject.Algebra.AscendingProperties.Normality
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Ascending reducedness and normality along flat ring maps

Stacks Project §`0336` (`algebra-section-ascending-properties`) of `algebra.tex`, tags
**0C21**, **033B** and **0C22**.

- **0C21** `algebra-lemma-reduced-goes-up-noetherian`:
  > Let `φ : R → S` be a ring map. Assume (1) `R` Noetherian, (2) `S` Noetherian, (3) `φ` flat,
  > (4) the fibre rings `S ⊗_R κ(p)` are reduced, (5) `R` reduced. Then `S` is reduced.

- **033B** `algebra-lemma-reduced-goes-up`:
  > Let `φ : R → S` be a ring map. Assume (1) `φ` smooth, (2) `R` reduced. Then `S` is reduced.

- **0C22** `algebra-lemma-normal-goes-up-noetherian`: the same statement for normality.

None of these is in Mathlib. The closest available result is
`IsReduced.tensorProduct_of_flat_of_forall_fg` (`Mathlib/RingTheory/Flat/Basic.lean:642`), which
is an ascent along a *limit* argument rather than the fibrewise criterion, and
`Mathlib/RingTheory/LocalProperties/Reduced.lean` for the Zariski-local API.

**Proof route (Stacks Project).** For Noetherian rings, reducedness is equivalent to Serre's
conditions `(S₁)` and `(R₀)` (`algebra-lemma-criterion-reduced`). Both ascend along a flat map
with the corresponding fibrewise property: `0339` (`algebra-lemma-Sk-goes-up`) and `033A`
(`algebra-lemma-Rk-goes-up`). Those in turn rest on the depth-additivity formula `0337`
(`algebra-lemma-apply-grothendieck`), `depth(S) = depth(R) + depth(S/m_R S)` for a flat local
homomorphism of Noetherian local rings, itself proved from `0338`
(`algebra-lemma-apply-grothendieck-module`) by a ~90-line induction on depth. **`0338` is the
deep root of this entire cluster**, and Mathlib has no depth theory beyond
`Mathlib/RingTheory/Depth/Rees.lean`.

`033B` is then deduced from `0C21` in the Noetherian case, plus a limit argument descending to a
finitely generated `ℤ`-subalgebra to remove the Noetherian hypothesis.

For `0C22`, the local normality criterion is implemented directly: reducedness first ascends by
`0C21`; `(R₁)` ascends using the dimension formula for flat local maps and regularity of normal
local rings in dimension at most one; and `(S₂)` ascends by constructing regular pairs in the
three possible base-depth cases. The reusable commutative-algebra details live in
`AscendingProperties.Normality`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- A flat morphism over a reduced scheme with finitely many irreducible components
has reduced source when its residue-field fibers are reduced.

This is the ordinary-fiber variant of
`GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents`; only the
fibers at the generic points are needed in that proof. -/
lemma isReduced_of_flat_of_finite_irreducibleComponents_of_fibers
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [IsReduced Y]
    [Finite (irreducibleComponents Y)]
    (h : ∀ y : Y, IsReduced (f.fiber y)) : IsReduced X := by
  let pt (Z : irreducibleComponents Y) :=
    Y.residueField Z.property.1.genericPoint
  let Z := ∐ fun Z ↦ Spec (pt Z)
  let g : Z ⟶ Y := Sigma.desc fun Z ↦
    Y.fromSpecResidueField Z.property.1.genericPoint
  have : Finite Z := (sigmaMk _).finite_iff.mp inferInstance
  have : QuasiCompact g := ⟨fun _ _ _ ↦ (Set.toFinite _).isCompact⟩
  have H : IsSchemeTheoreticallyDominant g := by
    rw [isSchemeTheoreticallyDominant_iff_isDominant, isDominant_iff,
      denseRange_iff_closure_range, Set.eq_univ_iff_forall]
    intro y
    let z : Z := Sigma.ι (fun Z ↦ Spec (pt Z))
      ⟨_, irreducibleComponent_mem_irreducibleComponents y⟩
      (IsLocalRing.closedPoint _)
    have hz : g z ⤳ y := by
      simp only [g, z, Z, ← Scheme.Hom.comp_apply, Sigma.ι_desc, pt,
        Scheme.fromSpecResidueField_apply]
      exact (IsIrreducible.isGenericPoint_genericPoint _
        isClosed_irreducibleComponent).specializes mem_irreducibleComponent
    exact hz.mem_closed isClosed_closure (subset_closure ⟨_, rfl⟩)
  suffices IsReduced (pullback f g) from
    IsSchemeTheoreticallyDominant.isReduced (pullback.fst f g)
  have H := IsUniversalColimit.isPullback_of_isColimit_left
    (X := fun Z ↦ Spec (pt Z))
    (FinitaryPreExtensive.isUniversal_finiteCoproducts (coproductIsCoproduct _))
    (fun Z ↦ Y.fromSpecResidueField Z.property.1.genericPoint) g f _ _
    (fun _ ↦ .of_hasPullback _ _) (coproductIsCoproduct _)
  apply +allowSynthFailures @isReduced_of_isOpenImmersion (f := H.isoPullback.inv)
  apply +allowSynthFailures @IsReduced.of_openCover (𝒰 := sigmaOpenCover _)
  exact fun i ↦ h i.property.1.genericPoint

end AlgebraicGeometry

/-- **Stacks 0C21** (`algebra-lemma-reduced-goes-up-noetherian`). A flat map of Noetherian rings
with reduced fibres, out of a reduced ring, has reduced target. -/
@[stacks 0C21]
theorem isReduced_of_flat_of_fibers_reduced_noetherian (R : Type u) (S : Type u) [CommRing R]
    [CommRing S] [IsNoetherianRing R] [IsReduced R] [IsNoetherianRing S] [Algebra R S]
    [Module.Flat R S] (h : ∀ (p : Ideal R) [p.IsPrime], IsReduced (p.Fiber S)) :
    IsReduced S := by
  let f : AlgebraicGeometry.Spec (.of S) ⟶ AlgebraicGeometry.Spec (.of R) :=
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R S))
  letI : AlgebraicGeometry.Flat f := by
    dsimp [f]
    exact AlgebraicGeometry.Flat.SpecMap_iff.mpr
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
  letI : AlgebraicGeometry.IsReduced (AlgebraicGeometry.Spec (.of R)) := inferInstance
  letI : Finite (irreducibleComponents (AlgebraicGeometry.Spec (.of R))) := by
    let : AlgebraicGeometry.IsNoetherian (AlgebraicGeometry.Spec (.of R)) := {}
    exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have hfib (p : AlgebraicGeometry.Spec (.of R)) :
      AlgebraicGeometry.IsReduced (f.fiber p) := by
    letI : p.asIdeal.IsPrime := p.isPrime
    letI : IsReduced (p.asIdeal.Fiber S) := h p.asIdeal
    let e := AlgebraicGeometry.Spec.fiberToSpecResidueFieldIso R S p
    have htarget : AlgebraicGeometry.IsReduced
        (AlgebraicGeometry.Spec (.of (p.asIdeal.Fiber S))) := inferInstance
    exact CategoryTheory.ObjectProperty.prop_of_iso (AlgebraicGeometry.IsReduced ·)
      (CategoryTheory.Arrow.leftFunc.mapIso e).symm htarget
  haveI : AlgebraicGeometry.IsReduced (AlgebraicGeometry.Spec (.of S)) :=
    AlgebraicGeometry.isReduced_of_flat_of_finite_irreducibleComponents_of_fibers
      f hfib
  exact (AlgebraicGeometry.affine_isReduced_iff (.of S)).mp inferInstance

/-- An étale algebra over a Noetherian reduced ring is reduced. -/
private lemma isReduced_of_etale_of_noetherian (R : Type u) (S : Type u) [CommRing R]
    [CommRing S] [Algebra R S] [IsNoetherianRing R] [IsReduced R]
    [Algebra.Etale R S] : IsReduced S := by
  haveI : IsNoetherianRing S :=
    Algebra.FiniteType.isNoetherianRing R S
  apply isReduced_of_flat_of_fibers_reduced_noetherian R S
  intro p hp
  exact Algebra.FormallyUnramified.isReduced_of_field p.ResidueField (p.Fiber S)

/-- A standard-smooth algebra over a field is reduced. -/
private lemma isReduced_of_isStandardSmooth_of_field (K : Type u) (S : Type u)
    [Field K] [CommRing S] [Algebra K S] [Algebra.IsStandardSmooth K S] :
    IsReduced S := by
  have hs : (algebraMap K S).IsStandardSmooth :=
    RingHom.isStandardSmooth_algebraMap.mpr inferInstance
  obtain ⟨n, g, -, hg⟩ := hs.exists_etale_mvPolynomial
  algebraize [g]
  haveI : Algebra.Etale (MvPolynomial (Fin n) K) S := hg.toAlgebra
  exact isReduced_of_etale_of_noetherian (MvPolynomial (Fin n) K) S

/-- A smooth algebra over a field is reduced. -/
private lemma isReduced_of_smooth_of_field (K : Type u) (S : Type u) [Field K]
    [CommRing S] [Algebra K S] [Algebra.Smooth K S] : IsReduced S := by
  obtain ⟨s, hs, hstd⟩ := Algebra.Smooth.exists_span_eq_top_isStandardSmooth K S
  apply IsReduced.mk
  intro x hx
  apply Localization.algebraMap_injective_of_span_eq_top s hs
  funext a
  haveI : Algebra.IsStandardSmooth K (Localization.Away a.1) := hstd a.1 a.2
  haveI : IsReduced (Localization.Away a.1) :=
    isReduced_of_isStandardSmooth_of_field K _
  change algebraMap S (Localization.Away a.1) x =
    algebraMap S (Localization.Away a.1) 0
  rw [map_zero]
  exact (hx.map (algebraMap S (Localization.Away a.1))).eq_zero

/-- **Stacks 033B** (`algebra-lemma-reduced-goes-up`). A smooth algebra over a reduced ring is
reduced. -/
@[stacks 033B]
theorem isReduced_of_smooth (R : Type u) (S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] [IsReduced R] : IsReduced S := by
  obtain ⟨R₀, S₀, _, _, hR₀, _, ⟨e⟩⟩ :=
    Algebra.Smooth.exists_subalgebra_fg ℤ R S
  haveI : Algebra.FiniteType ℤ R₀ :=
    (Subalgebra.fg_iff_finiteType R₀).mp hR₀
  haveI : IsNoetherianRing R₀ :=
    Algebra.FiniteType.isNoetherianRing ℤ R₀
  haveI : Module.Flat R₀ S₀ := Algebra.Smooth.flat R₀ S₀
  have ht : IsReduced (S₀ ⊗[R₀] R) :=
    IsReduced.tensorProduct_of_flat_of_forall_fg fun D hD ↦ by
      haveI : Algebra.FiniteType R₀ D :=
        (Subalgebra.fg_iff_finiteType D).mp hD
      haveI : IsNoetherianRing D :=
        Algebra.FiniteType.isNoetherianRing R₀ D
      haveI : IsReduced D := isReduced_of_injective D.val Subtype.val_injective
      haveI : IsNoetherianRing (D ⊗[R₀] S₀) :=
        Algebra.FiniteType.isNoetherianRing D (D ⊗[R₀] S₀)
      haveI : Algebra.Smooth D (D ⊗[R₀] S₀) :=
        Algebra.Smooth.baseChange R₀ S₀ D
      have hleft : IsReduced (D ⊗[R₀] S₀) := by
        apply isReduced_of_flat_of_fibers_reduced_noetherian D (D ⊗[R₀] S₀)
        intro p hp
        haveI : Algebra.Smooth p.ResidueField (p.Fiber (D ⊗[R₀] S₀)) :=
          Algebra.Smooth.baseChange D (D ⊗[R₀] S₀) p.ResidueField
        exact isReduced_of_smooth_of_field p.ResidueField (p.Fiber (D ⊗[R₀] S₀))
      exact isReduced_of_injective (Algebra.TensorProduct.comm R₀ S₀ D)
        (Algebra.TensorProduct.comm R₀ S₀ D).injective
  exact isReduced_of_injective
    ((Algebra.TensorProduct.comm R₀ R S₀).toRingEquiv.toRingHom.comp
      e.toRingEquiv.toRingHom)
    ((Algebra.TensorProduct.comm R₀ R S₀).injective.comp e.injective)

/-- **Stacks 0C22** (`algebra-lemma-normal-goes-up-noetherian`). A flat map of Noetherian rings
with normal fibres, out of a normal ring, has normal target. -/
@[stacks 0C22]
theorem isNormalRing_of_flat_of_fibers_normal_noetherian (R : Type u) (S : Type u) [CommRing R]
    [CommRing S] [IsNoetherianRing R] [IsNoetherianRing S] [Algebra R S] [IsNormalRing R]
    [Module.Flat R S] (h : ∀ (p : Ideal R) [p.IsPrime], IsNormalRing (p.Fiber S)) :
    IsNormalRing S := by
  letI : IsReduced R := IsNormalRing.isReduced
  letI : IsReduced S :=
    isReduced_of_flat_of_fibers_reduced_noetherian R S fun p hp ↦ by
      letI : p.IsPrime := hp
      letI : IsNormalRing (p.Fiber S) := h p
      exact IsNormalRing.isReduced
  exact IsNormalRing.of_serreOne_serreTwo
    (SerreOne.of_flat_of_fibers_normal h)
    (SerreTwo.of_flat_of_fibers_normal h)
