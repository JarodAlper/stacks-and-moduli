module

public import StacksAndModuli.API.CompletedLocalRing
public import StacksAndModuli.API.MvPowerSeriesFinTwoCoordinatePrime
public import StacksAndModuli.API.PureDimension
public import StacksAndModuli.API.ReducedClosedStalks
public import StacksAndModuli.API.SmoothPointIso
public import StacksAndModuli.API.SmoothStalkReduced
public import StacksAndModuli.«Section6.1-Smooth».«part6.1.1-curves»
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

/-!
# §6.2, Nodal curves — nodes

This file formalizes the node model and nodal curves from Definition 6.2.1 of
*Stacks and Moduli* (`sec:nodal-curves`). It includes both
the arbitrary-field geometric definition and the algebraically closed split-node
specialization used throughout §6.3.

## Main definitions

* `AlgebraicGeometry.Scheme.IsSplitNodeAt`: the completed local ring at a point is the
  standard node ring as a `k`-algebra.
* `AlgebraicGeometry.Scheme.IsNodeAt`: a point has a split lift after base change to the
  canonical algebraic closure.
* `AlgebraicGeometry.Scheme.IsGeometricallyNodalCurveOver`: the arbitrary-field nodal
  curve predicate from the book.

## Supporting definitions and API

* `AlgebraicGeometry.Scheme.nodeRing`: the standard node ring `k[[x,y]]/(xy)`.
* `AlgebraicGeometry.Scheme.IsNodalCurveOver`: the algebraically closed specialization.
* `AlgebraicGeometry.Scheme.nodeIdeal_isRadical`: the ideal `(xy)` is radical over a domain.
* `AlgebraicGeometry.Scheme.IsSplitNodeAt.isReduced_stalk`: a split node on a locally
  Noetherian scheme has reduced local ring.
* `AlgebraicGeometry.Scheme.IsNodalCurveOver.isReduced`: a nodal curve over an
  algebraically closed field is reduced.
* `AlgebraicGeometry.Scheme.IsNodalCurveOver.isNoetherian`: a nodal curve over an
  algebraically closed field is Noetherian.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

section DefNodes

/-- Background definition for Definition 6.2.1 (implicit standard model): the ideal `(xy)` in the
two-variable formal power series ring. -/
noncomputable def nodeIdeal (k : Type u) [CommRing k] : Ideal (MvPowerSeries (Fin 2) k) :=
  Ideal.span
    ({MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2)} :
      Set (MvPowerSeries (Fin 2) k))

/-- Background definition for Definition 6.2.1 (implicit standard model): the completed local model
`k[[x,y]]/(xy)` of a split node. -/
abbrev nodeRing (k : Type u) [CommRing k] :=
  MvPowerSeries (Fin 2) k ⧸ nodeIdeal k

/-- The ideal `(xy)` in a two-variable formal power series ring over a domain is radical. -/
theorem nodeIdeal_isRadical (k : Type u) [CommRing k] [IsDomain k] :
    (nodeIdeal k).IsRadical := by
  let x : MvPowerSeries (Fin 2) k := MvPowerSeries.X (0 : Fin 2)
  let y : MvPowerSeries (Fin 2) k := MvPowerSeries.X (1 : Fin 2)
  have hx0 : x ≠ 0 := by
    intro h
    have hcoeff := congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)) h
    simp [x] at hcoeff
  have hy0 : y ≠ 0 := by
    intro h
    have hcoeff := congrArg (MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1)) h
    simp [y] at hcoeff
  have hx : Prime x :=
    (Ideal.span_singleton_prime hx0).mp (mvPowerSeriesFinTwo_span_X_zero_isPrime k)
  have hy : Prime y :=
    (Ideal.span_singleton_prime hy0).mp (mvPowerSeriesFinTwo_span_X_one_isPrime k)
  have hyx : ¬y ∣ x := by
    intro h
    rw [MvPowerSeries.X_dvd_iff] at h
    have hcoeff := h (Finsupp.single (0 : Fin 2) 1) (by simp)
    simp [x] at hcoeff
  intro f hf
  rcases hf with ⟨n, hn⟩
  rw [nodeIdeal, Ideal.mem_span_singleton] at hn ⊢
  change x * y ∣ f ^ n at hn
  have hxf : x ∣ f := hx.dvd_of_dvd_pow ((dvd_mul_right x y).trans hn)
  have hyf : y ∣ f := hy.dvd_of_dvd_pow ((dvd_mul_left y x).trans (by
    simpa [mul_comm] using hn))
  obtain ⟨a, ha⟩ := hxf
  have hya : y ∣ a := (hy.dvd_or_dvd (ha ▸ hyf)).resolve_left hyx
  obtain ⟨b, hb⟩ := hya
  refine ⟨b, ?_⟩
  rw [ha, hb]
  change x * (y * b) = (x * y) * b
  rw [mul_assoc]

/-- The standard split-node ring `k[[x,y]]/(xy)` over a domain is reduced. -/
instance nodeRing_isReduced (k : Type u) [CommRing k] [IsDomain k] :
    _root_.IsReduced (nodeRing k) :=
  (Ideal.isRadical_iff_quotient_reduced (nodeIdeal k)).mp (nodeIdeal_isRadical k)

/-- **Definition 6.2.1** (`def:nodes`, split-node part): a point is a split node over `k`
when its completed local ring is `k`-algebra isomorphic to `k[[x,y]]/(xy)`.

The isomorphism is wrapped in `Nonempty`: formal coordinates witness the property but are
not part of the structure of a node. -/
noncomputable def IsSplitNodeAt (k : Type u) [Field k] (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))] (x : C) : Prop :=
  letI := stalkAlgebra (C ↘ Spec (CommRingCat.of k)) x
  Nonempty (C.completedLocalRing x ≃ₐ[k] nodeRing k)

/-- At a split node of a locally Noetherian scheme, the local ring is reduced. -/
theorem IsSplitNodeAt.isReduced_stalk {k : Type u} [Field k]
    {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))] [IsLocallyNoetherian C]
    {x : C} (h : C.IsSplitNodeAt k x) :
    _root_.IsReduced (C.presheaf.stalk x) := by
  let _ := stalkAlgebra (C ↘ Spec (CommRingCat.of k)) x
  rcases h with ⟨e⟩
  let _ : _root_.IsReduced (C.completedLocalRing x) :=
    _root_.isReduced_of_injective e e.injective
  apply _root_.isReduced_of_injective (C.toCompletedLocalRing x)
  intro a b hab
  apply AdicCompletion.of_injective
    (IsLocalRing.maximalIdeal (C.presheaf.stalk x)) (C.presheaf.stalk x)
  simpa only [C.toCompletedLocalRing_apply] using hab

/-- The defining completed-local-ring characterization of a split node. -/
theorem isSplitNodeAt_iff (k : Type u) [Field k] (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))] (x : C) :
    C.IsSplitNodeAt k x ↔
      letI := stalkAlgebra (C ↘ Spec (CommRingCat.of k)) x
      Nonempty (C.completedLocalRing x ≃ₐ[k] nodeRing k) :=
  Iff.rfl

/-- Split nodes are preserved and reflected by isomorphisms over the ground field. -/
theorem isSplitNodeAt_isoOver_iff {k : Type u} [Field k]
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [Y.Over (Spec (CommRingCat.of k))]
    (e : X.asOver (Spec (CommRingCat.of k)) ≅
      Y.asOver (Spec (CommRingCat.of k))) (x : X) :
    X.IsSplitNodeAt k x ↔
      Y.IsSplitNodeAt k (((Over.forget (Spec (CommRingCat.of k))).mapIso e).hom x) := by
  let E : X ≅ Y := (Over.forget (Spec (CommRingCat.of k))).mapIso e
  let _ := stalkAlgebra (X ↘ Spec (CommRingCat.of k)) x
  let _ := stalkAlgebra (Y ↘ Spec (CommRingCat.of k)) (E.hom x)
  let c : Y.completedLocalRing (E.hom x) ≃ₐ[k] X.completedLocalRing x :=
    completedLocalRingAlgEquivOfIsoOver E
      (X ↘ Spec (CommRingCat.of k)) (Y ↘ Spec (CommRingCat.of k)) e.hom.w x
  change Nonempty (X.completedLocalRing x ≃ₐ[k] nodeRing k) ↔
    Nonempty (Y.completedLocalRing (E.hom x) ≃ₐ[k] nodeRing k)
  constructor
  · rintro ⟨h⟩
    exact ⟨c.trans h⟩
  · rintro ⟨h⟩
    exact ⟨c.symm.trans h⟩

/-- Background definition for Definition 6.2.1 (implicit construction): base change of a
`k`-scheme to Mathlib's canonical algebraic closure of `k`. -/
noncomputable abbrev geometricBaseChange (k : Type u) [Field k]
    (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))] : Scheme.{u} :=
  pullback (C ↘ Spec (CommRingCat.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))

/-- Background definition for Definition 6.2.1 (implicit construction): the projection from
the geometric base change back to the original scheme. -/
noncomputable abbrev geometricBaseChangeProjection (k : Type u) [Field k]
    (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))] :
    geometricBaseChange k C ⟶ C :=
  pullback.fst (C ↘ Spec (CommRingCat.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))

/-- Supporting instance for Definition 6.2.1 (implicit construction): the geometric base
change carries its projection to the spectrum of the algebraic closure. -/
noncomputable instance geometricBaseChange_over (k : Type u) [Field k]
    (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))] :
    (geometricBaseChange k C).Over
      (Spec (CommRingCat.of (AlgebraicClosure k))) :=
  ⟨pullback.snd (C ↘ Spec (CommRingCat.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))⟩

/-- **Definition 6.2.1** (`def:nodes`, node part): a point of a scheme over an
arbitrary field is a node when some point above it after base change to the canonical
algebraic closure is a split node.

The surrounding nodal-curve predicate applies this definition only to closed points. -/
noncomputable def IsNodeAt (k : Type u) [Field k]
    (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))] (x : C) : Prop :=
  ∃ y : geometricBaseChange k C,
    geometricBaseChangeProjection k C y = x ∧
      (geometricBaseChange k C).IsSplitNodeAt (AlgebraicClosure k) y

/-- API lemma for Definition 6.2.1 (node part), unfolded: a node is witnessed by
a split point of the geometric base change lying above the given point. -/
theorem isNodeAt_iff (k : Type u) [Field k]
    (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))] (x : C) :
    C.IsNodeAt k x ↔
      ∃ y : geometricBaseChange k C,
        geometricBaseChangeProjection k C y = x ∧
          (geometricBaseChange k C).IsSplitNodeAt (AlgebraicClosure k) y :=
  Iff.rfl

/-- Geometric nodes are preserved and reflected by isomorphisms over the ground field. -/
theorem isNodeAt_isoOver_iff {k : Type u} [Field k]
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [Y.Over (Spec (CommRingCat.of k))]
    (e : X.asOver (Spec (CommRingCat.of k)) ≅
      Y.asOver (Spec (CommRingCat.of k))) (x : X) :
    X.IsNodeAt k x ↔
      Y.IsNodeAt k
        (((Over.forget (Spec (CommRingCat.of k))).mapIso e).hom x) := by
  let g : Spec (CommRingCat.of (AlgebraicClosure k)) ⟶
      Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  let E : X ≅ Y := (Over.forget (Spec (CommRingCat.of k))).mapIso e
  let eAC : (geometricBaseChange k X).asOver
        (Spec (CommRingCat.of (AlgebraicClosure k))) ≅
      (geometricBaseChange k Y).asOver
        (Spec (CommRingCat.of (AlgebraicClosure k))) :=
    (Over.pullback g).mapIso e
  let EAC : geometricBaseChange k X ≅ geometricBaseChange k Y :=
    (Over.forget (Spec (CommRingCat.of (AlgebraicClosure k)))).mapIso eAC
  have hprojection : EAC.hom ≫ geometricBaseChangeProjection k Y =
      geometricBaseChangeProjection k X ≫ E.hom := by
    dsimp [EAC, eAC, E, geometricBaseChangeProjection, geometricBaseChange, g]
    exact pullback.lift_fst _ _ _
  constructor
  · rintro ⟨y, hy, hnode⟩
    refine ⟨EAC.hom y, ?_, ?_⟩
    · change (EAC.hom ≫ geometricBaseChangeProjection k Y) y = E.hom x
      rw [hprojection]
      change E.hom (geometricBaseChangeProjection k X y) = E.hom x
      rw [hy]
    · exact (isSplitNodeAt_isoOver_iff eAC y).mp hnode
  · rintro ⟨y, hy, hnode⟩
    refine ⟨EAC.inv y, ?_, ?_⟩
    · apply E.hom.homeomorph.injective
      have hp := congrArg (fun q ↦ q (EAC.inv y)) hprojection
      refine hp.symm.trans ?_
      change geometricBaseChangeProjection k Y (EAC.hom (EAC.inv y)) = E.hom x
      have hEAC : EAC.hom (EAC.inv y) = y :=
        (Scheme.homeoOfIso EAC).apply_symm_apply y
      rw [hEAC, hy]
      rfl
    · exact (isSplitNodeAt_isoOver_iff eAC.symm y).mp hnode

/-- **Definition 6.2.1** (`def:nodes`, arbitrary-field nodal-curve part): a nodal
curve over any field is a pure one-dimensional curve whose closed points are smooth or
nodes after base change to an algebraic closure. -/
class IsGeometricallyNodalCurveOver (k : Type u) [Field k]
    (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))] : Prop where
  isCurve : IsCurveOver k C
  pureDimensionOne : C.IsPureOfDimension 1
  smooth_or_isNode : ∀ x : C, IsClosed ({x} : Set C) →
    ((C ↘ Spec (CommRingCat.of k)).stalkMap x).hom.FormallySmooth ∨
      C.IsNodeAt k x

-- A geometrically nodal curve is a curve over its base field.
attribute [instance] IsGeometricallyNodalCurveOver.isCurve

/-- API lemma for Definition 6.2.1 (arbitrary-field nodal-curve part), unfolded. -/
theorem isGeometricallyNodalCurveOver_iff (k : Type u) [Field k]
    (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))] :
    IsGeometricallyNodalCurveOver k C ↔
      IsCurveOver k C ∧ C.IsPureOfDimension 1 ∧
        ∀ x : C, IsClosed ({x} : Set C) →
          ((C ↘ Spec (CommRingCat.of k)).stalkMap x).hom.FormallySmooth ∨
            C.IsNodeAt k x := by
  constructor
  · intro h
    exact ⟨h.isCurve, h.pureDimensionOne, h.smooth_or_isNode⟩
  · rintro ⟨hcurve, hpure, hlocal⟩
    exact ⟨hcurve, hpure, hlocal⟩

/-- Arbitrary-field nodality is preserved by an isomorphism over the ground field. -/
theorem IsGeometricallyNodalCurveOver.isoOver {k : Type u} [Field k]
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [Y.Over (Spec (CommRingCat.of k))]
    (h : IsGeometricallyNodalCurveOver k X)
    (e : X.asOver (Spec (CommRingCat.of k)) ≅
      Y.asOver (Spec (CommRingCat.of k))) :
    IsGeometricallyNodalCurveOver k Y := by
  let E : X ≅ Y := (Over.forget (Spec (CommRingCat.of k))).mapIso e
  refine ⟨h.isCurve.isoOver e, h.pureDimensionOne.iso E, ?_⟩
  intro y hy
  let x : X := E.inv y
  have hx : IsClosed ({x} : Set X) := by
    have hpre : IsClosed (E.hom.homeomorph ⁻¹' ({y} : Set Y)) :=
      E.hom.homeomorph.isClosed_preimage.mpr hy
    have hpre_eq : E.hom.homeomorph ⁻¹' ({y} : Set Y) = ({x} : Set X) := by
      ext z
      constructor
      · intro hz
        apply E.hom.homeomorph.injective
        simpa [x] using hz
      · rintro rfl
        simp [x]
    rwa [hpre_eq] at hpre
  have hxy : ((Over.forget (Spec (CommRingCat.of k))).mapIso e).hom x = y := by
    change E.hom x = y
    simp [x]
  rcases h.smooth_or_isNode x hx with hsmooth | hnode
  · left
    rw [← hxy]
    exact (formallySmooth_stalkMap_isoOver_iff e x).mp hsmooth
  · right
    rw [← hxy]
    exact (isNodeAt_isoOver_iff e x).mp hnode

/-- Isomorphic curves over any field are simultaneously geometrically nodal. -/
theorem isGeometricallyNodalCurveOver_isoOver_iff
    {k : Type u} [Field k]
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [Y.Over (Spec (CommRingCat.of k))]
    (e : X.asOver (Spec (CommRingCat.of k)) ≅
      Y.asOver (Spec (CommRingCat.of k))) :
    IsGeometricallyNodalCurveOver k X ↔
      IsGeometricallyNodalCurveOver k Y :=
  ⟨fun h ↦ h.isoOver e, fun h ↦ h.isoOver e.symm⟩

/-- API lemma for Definition 6.2.1, finiteness consequence: a geometrically nodal
curve over an arbitrary field is Noetherian. -/
theorem IsGeometricallyNodalCurveOver.isNoetherian
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    (h : IsGeometricallyNodalCurveOver k C) : IsNoetherian C := by
  let _ : IsGeometricallyNodalCurveOver k C := h
  let _ : IsLocallyNoetherian C :=
    LocallyOfFiniteType.isLocallyNoetherian (C ↘ Spec (CommRingCat.of k))
  let _ : CompactSpace C :=
    QuasiCompact.compactSpace_of_compactSpace (C ↘ Spec (CommRingCat.of k))
  exact IsNoetherian.mk

/-- Background definition for Definition 6.2.1 (nodal-curve part), over an algebraically closed
field: a nodal curve is pure one-dimensional and every closed point is either smooth or a
split node.

Over an algebraically closed field every closed point of a finite-type scheme is rational,
so this is the split specialization used throughout §6.3. The exact arbitrary-field
predicate is `IsGeometricallyNodalCurveOver`. -/
class IsNodalCurveOver (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))] : Prop where
  isCurve : IsCurveOver k C
  pureDimensionOne : C.IsPureOfDimension 1
  smooth_or_isSplitNode : ∀ x : C, IsClosed ({x} : Set C) →
    ((C ↘ Spec (CommRingCat.of k)).stalkMap x).hom.FormallySmooth ∨
      C.IsSplitNodeAt k x

-- A nodal curve is a curve over its base field.
attribute [instance] IsNodalCurveOver.isCurve

/-- The unfolded characterization of a nodal curve over an algebraically closed field. -/
theorem isNodalCurveOver_iff (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))] :
    IsNodalCurveOver k C ↔
      IsCurveOver k C ∧ C.IsPureOfDimension 1 ∧
        ∀ x : C, IsClosed ({x} : Set C) →
          ((C ↘ Spec (CommRingCat.of k)).stalkMap x).hom.FormallySmooth ∨
            C.IsSplitNodeAt k x := by
  constructor
  · intro h
    exact ⟨h.isCurve, h.pureDimensionOne, h.smooth_or_isSplitNode⟩
  · rintro ⟨hcurve, hpure, hlocal⟩
    exact ⟨hcurve, hpure, hlocal⟩

/-- API lemma for Definition 6.2.1, reducedness consequence: a nodal curve over an
algebraically closed field is reduced. -/
theorem IsNodalCurveOver.isReduced {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    (h : IsNodalCurveOver k C) : IsReduced C := by
  let _ : IsNodalCurveOver k C := h
  let _ : JacobsonSpace C :=
    LocallyOfFiniteType.jacobsonSpace (C ↘ Spec (CommRingCat.of k))
  let _ : IsLocallyNoetherian C :=
    LocallyOfFiniteType.isLocallyNoetherian (C ↘ Spec (CommRingCat.of k))
  apply isReduced_of_formallySmooth_or_isReduced_closed_stalk
    (C ↘ Spec (CommRingCat.of k))
  intro x hx
  rcases h.smooth_or_isSplitNode x hx with hsmooth | hnode
  · exact Or.inl hsmooth
  · exact Or.inr hnode.isReduced_stalk

/-- API lemma for Definition 6.2.1, finiteness consequence: a nodal curve over an
algebraically closed field is Noetherian. -/
theorem IsNodalCurveOver.isNoetherian {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    (h : IsNodalCurveOver k C) : IsNoetherian C := by
  let _ : IsNodalCurveOver k C := h
  let _ : IsLocallyNoetherian C :=
    LocallyOfFiniteType.isLocallyNoetherian (C ↘ Spec (CommRingCat.of k))
  let _ : CompactSpace C :=
    QuasiCompact.compactSpace_of_compactSpace (C ↘ Spec (CommRingCat.of k))
  exact IsNoetherian.mk

/-- Nodality is preserved by an isomorphism over the ground field. -/
theorem IsNodalCurveOver.isoOver {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [Y.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k X)
    (e : X.asOver (Spec (CommRingCat.of k)) ≅
      Y.asOver (Spec (CommRingCat.of k))) :
    IsNodalCurveOver k Y := by
  let E : X ≅ Y := (Over.forget (Spec (CommRingCat.of k))).mapIso e
  refine ⟨h.isCurve.isoOver e, h.pureDimensionOne.iso E, ?_⟩
  intro y hy
  let x : X := E.inv y
  have hx : IsClosed ({x} : Set X) := by
    have hpre : IsClosed (E.hom.homeomorph ⁻¹' ({y} : Set Y)) :=
      E.hom.homeomorph.isClosed_preimage.mpr hy
    have hpre_eq : E.hom.homeomorph ⁻¹' ({y} : Set Y) = ({x} : Set X) := by
      ext z
      constructor
      · intro hz
        apply E.hom.homeomorph.injective
        simpa [x] using hz
      · rintro rfl
        simp [x]
    rwa [hpre_eq] at hpre
  have hxy : ((Over.forget (Spec (CommRingCat.of k))).mapIso e).hom x = y := by
    change E.hom x = y
    simp [x]
  rcases h.smooth_or_isSplitNode x hx with hsmooth | hnode
  · left
    rw [← hxy]
    exact (formallySmooth_stalkMap_isoOver_iff e x).mp hsmooth
  · right
    rw [← hxy]
    exact (isSplitNodeAt_isoOver_iff e x).mp hnode

/-- Isomorphic curves over an algebraically closed field are simultaneously nodal. -/
theorem isNodalCurveOver_isoOver_iff {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [Y.Over (Spec (CommRingCat.of k))]
    (e : X.asOver (Spec (CommRingCat.of k)) ≅
      Y.asOver (Spec (CommRingCat.of k))) :
    IsNodalCurveOver k X ↔ IsNodalCurveOver k Y :=
  ⟨fun h ↦ h.isoOver e, fun h ↦ h.isoOver e.symm⟩

end DefNodes

end AlgebraicGeometry.Scheme
