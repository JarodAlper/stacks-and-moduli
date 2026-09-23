module

public import StacksAndModuli.API.AlgebraicSpaceMarkedFamilies
public import StacksAndModuli.API.StableCurveSchemeFamilies

/-!
# Stable curves: families

This file formalizes Definition 6.3.20 at the book's stated generality: the total
space is an algebraic space over a scheme, not necessarily a scheme.  Geometric fibres
are represented by schemes before the curve predicates and induced markings are
evaluated.

The stable-family predicate uses the finite-automorphism presentation of stability from
`part6.3.1-definition`.  The semistable and prestable variants retain their
componentwise definitions. All family predicates are transported by equivalences of
marking index types; the curve and nodal predicates permit arbitrary reindexing because
they ignore the markings.

## Main definitions

- `IsFamilyOfNMarkedCurves`: an `n`-pointed family of curves.
- `IsFamilyOfNMarkedNodalCurves`: an `n`-pointed family of nodal curves.
- `IsFamilyOfNMarkedPrestableCurves`, `IsFamilyOfNMarkedSemistableCurves`, and
  `IsFamilyOfNMarkedStableCurves`: the three corresponding final family predicates.

The arbitrary-index engines, fixed-genus and unpointed specializations, projections,
reindexing lemmas, and evaluation lemmas below are supporting API.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

universe w v u

namespace AlgebraicGeometry

section DefFamilyOfCurves

/-- Background definition for Definition 6.3.20: a family of curves with markings
indexed by `I` is a proper, flat, finitely presented morphism from an algebraic space to
a scheme, together with `I` sections, whose geometric fibres are curves.

The scheme representing a geometric fibre and its induced sections are supplied by
`MarkedAlgebraicSpaceOver.HasPresentedGeometricFibers`. -/
def IsFamilyOfMarkedCurves {I : Type v} {S : Scheme.{u}}
    (F : MarkedAlgebraicSpaceOver I S) : Prop :=
  BasedFunctor.IsProper F.toBaseFunctor ∧
    BasedFunctor.Flat F.toBaseFunctor ∧
    BasedFunctor.FinitePresentation F.toBaseFunctor ∧
    F.HasPresentedGeometricFibers
      (MarkedGeometricFiberPredicate.ofUnmarked I
        Scheme.curveGeometricFiberPredicate)

/-- API lemma for Definition 6.3.20 (unfolding): the defining
conditions for a marked family of curves, displayed separately. -/
lemma isFamilyOfMarkedCurves_iff {I : Type v} {S : Scheme.{u}}
    (F : MarkedAlgebraicSpaceOver I S) :
    IsFamilyOfMarkedCurves F ↔
      BasedFunctor.IsProper F.toBaseFunctor ∧
        BasedFunctor.Flat F.toBaseFunctor ∧
        BasedFunctor.FinitePresentation F.toBaseFunctor ∧
        F.HasPresentedGeometricFibers
          (fun K _ _ Z _ _ ↦ Scheme.IsCurveOver K Z) :=
  Iff.rfl

/-- API lemma for Definition 6.3.20 (projection): the structure
morphism of a family of curves is proper. -/
lemma IsFamilyOfMarkedCurves.isProper {I : Type v} {S : Scheme.{u}}
    {F : MarkedAlgebraicSpaceOver I S} (h : IsFamilyOfMarkedCurves F) :
    BasedFunctor.IsProper F.toBaseFunctor :=
  h.1

/-- API lemma for Definition 6.3.20 (projection): the structure
morphism of a family of curves is flat. -/
lemma IsFamilyOfMarkedCurves.flat {I : Type v} {S : Scheme.{u}}
    {F : MarkedAlgebraicSpaceOver I S} (h : IsFamilyOfMarkedCurves F) :
    BasedFunctor.Flat F.toBaseFunctor :=
  h.2.1

/-- API lemma for Definition 6.3.20 (projection): the structure
morphism of a family of curves is finitely presented. -/
lemma IsFamilyOfMarkedCurves.finitePresentation {I : Type v} {S : Scheme.{u}}
    {F : MarkedAlgebraicSpaceOver I S} (h : IsFamilyOfMarkedCurves F) :
    BasedFunctor.FinitePresentation F.toBaseFunctor :=
  h.2.2.1

/-- API lemma for Definition 6.3.20 (projection): every geometric
fibre of a family of marked curves has a scheme presentation which is a curve. -/
lemma IsFamilyOfMarkedCurves.hasPresentedGeometricFibers
    {I : Type v} {S : Scheme.{u}} {F : MarkedAlgebraicSpaceOver I S}
    (h : IsFamilyOfMarkedCurves F) :
    F.HasPresentedGeometricFibers
      (MarkedGeometricFiberPredicate.ofUnmarked I
        Scheme.curveGeometricFiberPredicate) :=
  h.2.2.2

/-- API lemma for Definition 6.3.20 (reindexing): reindexing the
sections of a family of marked curves along any map preserves the curve-family
condition. -/
theorem IsFamilyOfMarkedCurves.reindex
    {I : Type v} {J : Type w} {S : Scheme.{u}}
    {F : MarkedAlgebraicSpaceOver I S} (h : IsFamilyOfMarkedCurves F)
    (e : J → I) : IsFamilyOfMarkedCurves (F.reindex e) := by
  refine ⟨h.isProper, h.flat, h.finitePresentation, ?_⟩
  exact MarkedAlgebraicSpaceOver.HasPresentedGeometricFibers.reindex F e
    (fun (_ : Type u) _ _ _ _ _ hcurve ↦ hcurve)
    h.hasPresentedGeometricFibers

/-- API lemma for Definition 6.3.20 (reindexing): equivalent marking
index types give equivalent curve-family conditions. -/
theorem isFamilyOfMarkedCurves_reindex_iff
    {I : Type v} {J : Type w} {S : Scheme.{u}}
    (F : MarkedAlgebraicSpaceOver I S) (e : J ≃ I) :
    IsFamilyOfMarkedCurves (F.reindex e) ↔ IsFamilyOfMarkedCurves F := by
  constructor
  · intro h
    have hback := h.reindex e.symm
    rwa [F.reindex_symm e] at hback
  · exact fun h ↦ h.reindex e

/-- API lemma for Definition 6.3.20 (evaluation): every scheme
presentation of a geometric fibre is a curve over its residue field. -/
lemma IsFamilyOfMarkedCurves.isCurveOnPresentedGeometricFiber
    {I : Type v} {S : Scheme.{u}} {F : MarkedAlgebraicSpaceOver I S}
    (h : IsFamilyOfMarkedCurves F) {K : Type u} [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ S)
  (P : F.PresentedGeometricFiber K s) :
    @Scheme.IsCurveOver K _ P.scheme ⟨P.toBase⟩ :=
  MarkedAlgebraicSpaceOver.HasPresentedGeometricFibers.prop
    (Q := MarkedGeometricFiberPredicate.ofUnmarked I
      Scheme.curveGeometricFiberPredicate) F h.2.2.2 s P

/-- **Definition 6.3.20** (`def:family-of-curves`): a family of `n`-pointed curves over a
scheme is a proper, flat, finitely presented algebraic space over it, equipped with `n`
ordered sections, whose geometric fibres are curves. -/
abbrev IsFamilyOfNMarkedCurves (n : ℕ) {S : Scheme.{u}}
    (F : MarkedAlgebraicSpaceOver (Fin n) S) : Prop :=
  IsFamilyOfMarkedCurves F

/-- Background definition for Definition 6.3.20 (unpointed form). -/
abbrev IsFamilyOfCurves {S : Scheme.{u}}
    (F : MarkedAlgebraicSpaceOver (Fin 0) S) : Prop :=
  IsFamilyOfNMarkedCurves 0 F

end DefFamilyOfCurves

section DefFamilyOfNodalCurves

/-- Background definition for Definition 6.3.20: a family of marked nodal
curves is a family of marked curves whose geometric fibres are nodal.

As in the book, nodal families impose no condition that the marked sections be distinct
or meet the smooth locus. -/
def IsFamilyOfMarkedNodalCurves {I : Type v} {S : Scheme.{u}}
    (F : MarkedAlgebraicSpaceOver I S) : Prop :=
    IsFamilyOfMarkedCurves F ∧
    F.HasPresentedGeometricFibers
      (MarkedGeometricFiberPredicate.ofUnmarked I
        Scheme.nodalCurveGeometricFiberPredicate)

/-- API lemma for Definition 6.3.20 (unfolding): the nodal-family
condition is the curve-family condition together with nodality of every geometric
fibre. -/
lemma isFamilyOfMarkedNodalCurves_iff {I : Type v} {S : Scheme.{u}}
    (F : MarkedAlgebraicSpaceOver I S) :
    IsFamilyOfMarkedNodalCurves F ↔
      IsFamilyOfMarkedCurves F ∧
        F.HasPresentedGeometricFibers
          (fun K _ _ Z _ _ ↦ Scheme.IsNodalCurveOver K Z) :=
  Iff.rfl

/-- API lemma for Definition 6.3.20 (projection): forgetting
nodality gives a family of marked curves. -/
lemma IsFamilyOfMarkedNodalCurves.isFamilyOfMarkedCurves
    {I : Type v} {S : Scheme.{u}} {F : MarkedAlgebraicSpaceOver I S}
    (h : IsFamilyOfMarkedNodalCurves F) : IsFamilyOfMarkedCurves F :=
  h.1

/-- API lemma for Definition 6.3.20 (reindexing): nodality
does not constrain the markings, so it is preserved along any map of index types. -/
theorem IsFamilyOfMarkedNodalCurves.reindex
    {I : Type v} {J : Type w} {S : Scheme.{u}}
    {F : MarkedAlgebraicSpaceOver I S} (h : IsFamilyOfMarkedNodalCurves F)
    (e : J → I) : IsFamilyOfMarkedNodalCurves (F.reindex e) := by
  refine ⟨h.isFamilyOfMarkedCurves.reindex e, ?_⟩
  exact MarkedAlgebraicSpaceOver.HasPresentedGeometricFibers.reindex F e
    (fun (_ : Type u) _ _ _ _ _ hnode ↦ hnode) h.2

/-- API lemma for Definition 6.3.20 (reindexing): equivalent
marking index types give equivalent nodal-family conditions. -/
theorem isFamilyOfMarkedNodalCurves_reindex_iff
    {I : Type v} {J : Type w} {S : Scheme.{u}}
    (F : MarkedAlgebraicSpaceOver I S) (e : J ≃ I) :
    IsFamilyOfMarkedNodalCurves (F.reindex e) ↔
      IsFamilyOfMarkedNodalCurves F := by
  constructor
  · intro h
    have hback := h.reindex e.symm
    rwa [F.reindex_symm e] at hback
  · exact fun h ↦ h.reindex e

/-- API lemma for Definition 6.3.20 (evaluation): every scheme
presentation of a geometric fibre is nodal over its residue field. -/
lemma IsFamilyOfMarkedNodalCurves.isNodalOnPresentedGeometricFiber
    {I : Type v} {S : Scheme.{u}} {F : MarkedAlgebraicSpaceOver I S}
    (h : IsFamilyOfMarkedNodalCurves F)
    {K : Type u} [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ S)
  (P : F.PresentedGeometricFiber K s) :
    @Scheme.IsNodalCurveOver K _ _ P.scheme ⟨P.toBase⟩ :=
  MarkedAlgebraicSpaceOver.HasPresentedGeometricFibers.prop
    (Q := MarkedGeometricFiberPredicate.ofUnmarked I
      Scheme.nodalCurveGeometricFiberPredicate) F h.2 s P

/-- **Definition 6.3.20** (`def:family-of-nodal-curves`): a family of `n`-pointed nodal
curves is a family of `n`-pointed curves whose geometric fibres are nodal. No
distinctness or smoothness condition is imposed on the markings. -/
abbrev IsFamilyOfNMarkedNodalCurves (n : ℕ) {S : Scheme.{u}}
    (F : MarkedAlgebraicSpaceOver (Fin n) S) : Prop :=
  IsFamilyOfMarkedNodalCurves F

/-- Background definition for Definition 6.3.20 (unpointed form). -/
abbrev IsFamilyOfNodalCurves {S : Scheme.{u}}
    (F : MarkedAlgebraicSpaceOver (Fin 0) S) : Prop :=
  IsFamilyOfNMarkedNodalCurves 0 F

end DefFamilyOfNodalCurves

section DefFamilyOfStableCurves

/-- Background definition for Definition 6.3.20 (prestable form): a family
of marked curves whose geometric fibres are prestable curves, with no fixed genus. -/
def IsFamilyOfPrestableMarkedCurves {I : Type v} {S : Scheme.{u}}
    (F : MarkedAlgebraicSpaceOver I S) : Prop :=
    IsFamilyOfMarkedCurves F ∧
    F.HasPresentedGeometricFibers
      (Scheme.prestableMarkedCurveGeometricFiberPredicate I)

/-- Background definition for Definition 6.3.20 (fixed-genus prestable
form). -/
def IsFamilyOfPrestableMarkedCurvesOfGenus (g : ℕ) {I : Type v}
    {S : Scheme.{u}} (F : MarkedAlgebraicSpaceOver I S) : Prop :=
  IsFamilyOfMarkedCurves F ∧
    F.HasPresentedGeometricFibers
      (Scheme.prestableMarkedCurveOfGenusGeometricFiberPredicate I g)

/-- API lemma for Definition 6.3.20 (prestable evaluation):
every presentation of a geometric fibre is prestable of some genus. -/
theorem IsFamilyOfPrestableMarkedCurves.exists_isPrestableOnPresentedGeometricFiber
    {I : Type v} {S : Scheme.{u}} {F : MarkedAlgebraicSpaceOver I S}
    (h : IsFamilyOfPrestableMarkedCurves F)
    {K : Type u} [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ S)
    (P : F.PresentedGeometricFiber K s) :
    ∃ g, @Scheme.IsPrestableMarkedCurveOfGenusOver K _ _ I g P.scheme
      ⟨P.toBase⟩ P.marking :=
  MarkedAlgebraicSpaceOver.HasPresentedGeometricFibers.prop
    (Q := Scheme.prestableMarkedCurveGeometricFiberPredicate I) F h.2 s P

/-- API lemma for Definition 6.3.20 (prestable evaluation):
every presentation of a fixed-genus geometric fibre is prestable of that genus. -/
theorem IsFamilyOfPrestableMarkedCurvesOfGenus.isPrestableOnPresentedGeometricFiber
    {g : ℕ} {I : Type v} {S : Scheme.{u}}
    {F : MarkedAlgebraicSpaceOver I S}
    (h : IsFamilyOfPrestableMarkedCurvesOfGenus g F)
    {K : Type u} [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ S)
    (P : F.PresentedGeometricFiber K s) :
    @Scheme.IsPrestableMarkedCurveOfGenusOver K _ _ I g P.scheme
      ⟨P.toBase⟩ P.marking :=
  MarkedAlgebraicSpaceOver.HasPresentedGeometricFibers.prop
    (Q := Scheme.prestableMarkedCurveOfGenusGeometricFiberPredicate I g)
    F h.2 s P

/-- API lemma for Definition 6.3.20 (prestable
reindexing): prestability is preserved by an equivalence of marking index types. -/
theorem IsFamilyOfPrestableMarkedCurves.reindex
    {I : Type v} {J : Type w} {S : Scheme.{u}}
    {F : MarkedAlgebraicSpaceOver I S}
    (h : IsFamilyOfPrestableMarkedCurves F) (e : J ≃ I) :
    IsFamilyOfPrestableMarkedCurves (F.reindex e) := by
  refine ⟨h.1.reindex e, ?_⟩
  exact MarkedAlgebraicSpaceOver.HasPresentedGeometricFibers.reindex F e
    (fun (_ : Type u) _ _ _ _ _ hpre ↦ by
      obtain ⟨g, hg⟩ := hpre
      exact ⟨g, hg.reindex e⟩) h.2

/-- API lemma for Definition 6.3.20 (fixed-genus
prestable reindexing): an equivalence of marking indices preserves the genus and
prestable fibre condition. -/
theorem IsFamilyOfPrestableMarkedCurvesOfGenus.reindex
    {g : ℕ} {I : Type v} {J : Type w} {S : Scheme.{u}}
    {F : MarkedAlgebraicSpaceOver I S}
    (h : IsFamilyOfPrestableMarkedCurvesOfGenus g F) (e : J ≃ I) :
    IsFamilyOfPrestableMarkedCurvesOfGenus g (F.reindex e) := by
  refine ⟨h.1.reindex e, ?_⟩
  exact MarkedAlgebraicSpaceOver.HasPresentedGeometricFibers.reindex F e
    (fun (_ : Type u) _ _ _ _ _ hpre ↦ hpre.reindex e) h.2

/-- API lemma for Definition 6.3.20 (prestable
reindexing): equivalent marking index types give equivalent prestable-family
conditions. -/
theorem isFamilyOfPrestableMarkedCurves_reindex_iff
    {I : Type v} {J : Type w} {S : Scheme.{u}}
    (F : MarkedAlgebraicSpaceOver I S) (e : J ≃ I) :
    IsFamilyOfPrestableMarkedCurves (F.reindex e) ↔
      IsFamilyOfPrestableMarkedCurves F := by
  constructor
  · intro h
    have hback := h.reindex e.symm
    rwa [F.reindex_symm e] at hback
  · exact fun h ↦ h.reindex e

/-- API lemma for Definition 6.3.20 (fixed-genus prestable
reindexing): equivalent marking index types preserve the exact genus stratum. -/
theorem isFamilyOfPrestableMarkedCurvesOfGenus_reindex_iff
    {g : ℕ} {I : Type v} {J : Type w} {S : Scheme.{u}}
    (F : MarkedAlgebraicSpaceOver I S) (e : J ≃ I) :
    IsFamilyOfPrestableMarkedCurvesOfGenus g (F.reindex e) ↔
      IsFamilyOfPrestableMarkedCurvesOfGenus g F := by
  constructor
  · intro h
    have hback := h.reindex e.symm
    rwa [F.reindex_symm e] at hback
  · exact fun h ↦ h.reindex e

/-- API lemma for Definition 6.3.20 (prestable consequence): a
fixed-genus prestable family is prestable after forgetting the genus. -/
theorem IsFamilyOfPrestableMarkedCurvesOfGenus.isFamilyOfPrestableMarkedCurves
    {g : ℕ} {I : Type v} {S : Scheme.{u}}
    {F : MarkedAlgebraicSpaceOver I S}
    (h : IsFamilyOfPrestableMarkedCurvesOfGenus g F) :
    IsFamilyOfPrestableMarkedCurves F := by
  refine ⟨h.1, ?_⟩
  intro K _ _ s
  obtain ⟨P, hP⟩ := h.2 K s
  exact ⟨P, g, hP⟩

/-- API lemma for Definition 6.3.20 (prestable consequence):
forgetting prestability gives a family of marked nodal curves. -/
theorem IsFamilyOfPrestableMarkedCurves.isFamilyOfMarkedNodalCurves
    {I : Type v} {S : Scheme.{u}} {F : MarkedAlgebraicSpaceOver I S}
    (h : IsFamilyOfPrestableMarkedCurves F) :
    IsFamilyOfMarkedNodalCurves F := by
  refine ⟨h.1, ?_⟩
  intro K _ _ s
  obtain ⟨P, g, hP⟩ := h.2 K s
  let _ : P.scheme.Over (Spec (CommRingCat.of K)) := ⟨P.toBase⟩
  exact ⟨P, hP.nodal⟩

/-- API lemma for Definition 6.3.20 (prestable consequence): a
fixed-genus prestable family is a family of marked nodal curves. -/
theorem IsFamilyOfPrestableMarkedCurvesOfGenus.isFamilyOfMarkedNodalCurves
    {g : ℕ} {I : Type v} {S : Scheme.{u}}
    {F : MarkedAlgebraicSpaceOver I S}
    (h : IsFamilyOfPrestableMarkedCurvesOfGenus g F) :
    IsFamilyOfMarkedNodalCurves F :=
  h.isFamilyOfPrestableMarkedCurves.isFamilyOfMarkedNodalCurves

/-- Background definition for Definition 6.3.20 (semistable form): a family
of marked curves whose geometric fibres are semistable curves of some genus. -/
def IsFamilyOfSemistableMarkedCurves {I : Type v} {S : Scheme.{u}}
    (F : MarkedAlgebraicSpaceOver I S) : Prop :=
    IsFamilyOfMarkedCurves F ∧
    F.HasPresentedGeometricFibers
      (Scheme.semistableMarkedCurveGeometricFiberPredicate I)

/-- Background definition for Definition 6.3.20 (fixed-genus semistable
form). -/
def IsFamilyOfSemistableMarkedCurvesOfGenus (g : ℕ) {I : Type v}
    {S : Scheme.{u}} (F : MarkedAlgebraicSpaceOver I S) : Prop :=
  IsFamilyOfMarkedCurves F ∧
    F.HasPresentedGeometricFibers
      (Scheme.semistableMarkedCurveOfGenusGeometricFiberPredicate I g)

/-- API lemma for Definition 6.3.20 (semistable evaluation):
every presentation of a geometric fibre is semistable of some genus. -/
theorem IsFamilyOfSemistableMarkedCurves.exists_isSemistableOnPresentedGeometricFiber
    {I : Type v} {S : Scheme.{u}} {F : MarkedAlgebraicSpaceOver I S}
    (h : IsFamilyOfSemistableMarkedCurves F)
    {K : Type u} [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ S)
    (P : F.PresentedGeometricFiber K s) :
    ∃ g, @Scheme.IsSemistableMarkedCurveOfGenusOver K _ _ I g P.scheme
      ⟨P.toBase⟩ P.marking :=
  MarkedAlgebraicSpaceOver.HasPresentedGeometricFibers.prop
    (Q := Scheme.semistableMarkedCurveGeometricFiberPredicate I) F h.2 s P

/-- API lemma for Definition 6.3.20 (semistable evaluation):
every presentation of a fixed-genus geometric fibre is semistable of that genus. -/
theorem IsFamilyOfSemistableMarkedCurvesOfGenus.isSemistableOnPresentedGeometricFiber
    {g : ℕ} {I : Type v} {S : Scheme.{u}}
    {F : MarkedAlgebraicSpaceOver I S}
    (h : IsFamilyOfSemistableMarkedCurvesOfGenus g F)
    {K : Type u} [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ S)
    (P : F.PresentedGeometricFiber K s) :
    @Scheme.IsSemistableMarkedCurveOfGenusOver K _ _ I g P.scheme
      ⟨P.toBase⟩ P.marking :=
  MarkedAlgebraicSpaceOver.HasPresentedGeometricFibers.prop
    (Q := Scheme.semistableMarkedCurveOfGenusGeometricFiberPredicate I g)
    F h.2 s P

/-- API lemma for Definition 6.3.20 (semistable
reindexing): semistability is preserved by an equivalence of marking index types. -/
theorem IsFamilyOfSemistableMarkedCurves.reindex
    {I : Type v} {J : Type w} {S : Scheme.{u}}
    {F : MarkedAlgebraicSpaceOver I S}
    (h : IsFamilyOfSemistableMarkedCurves F) (e : J ≃ I) :
    IsFamilyOfSemistableMarkedCurves (F.reindex e) := by
  refine ⟨h.1.reindex e, ?_⟩
  exact MarkedAlgebraicSpaceOver.HasPresentedGeometricFibers.reindex F e
    (fun (_ : Type u) _ _ _ _ _ hsemi ↦ by
      obtain ⟨g, hg⟩ := hsemi
      exact ⟨g, hg.reindex e⟩) h.2

/-- API lemma for Definition 6.3.20 (fixed-genus
semistable reindexing): an equivalence of marking indices preserves the genus and
semistable fibre condition. -/
theorem IsFamilyOfSemistableMarkedCurvesOfGenus.reindex
    {g : ℕ} {I : Type v} {J : Type w} {S : Scheme.{u}}
    {F : MarkedAlgebraicSpaceOver I S}
    (h : IsFamilyOfSemistableMarkedCurvesOfGenus g F) (e : J ≃ I) :
    IsFamilyOfSemistableMarkedCurvesOfGenus g (F.reindex e) := by
  refine ⟨h.1.reindex e, ?_⟩
  exact MarkedAlgebraicSpaceOver.HasPresentedGeometricFibers.reindex F e
    (fun (_ : Type u) _ _ _ _ _ hsemi ↦ hsemi.reindex e) h.2

/-- API lemma for Definition 6.3.20 (semistable
reindexing): equivalent marking index types give equivalent semistable-family
conditions. -/
theorem isFamilyOfSemistableMarkedCurves_reindex_iff
    {I : Type v} {J : Type w} {S : Scheme.{u}}
    (F : MarkedAlgebraicSpaceOver I S) (e : J ≃ I) :
    IsFamilyOfSemistableMarkedCurves (F.reindex e) ↔
      IsFamilyOfSemistableMarkedCurves F := by
  constructor
  · intro h
    have hback := h.reindex e.symm
    rwa [F.reindex_symm e] at hback
  · exact fun h ↦ h.reindex e

/-- API lemma for Definition 6.3.20 (fixed-genus
semistable reindexing): equivalent marking index types preserve the exact genus
stratum. -/
theorem isFamilyOfSemistableMarkedCurvesOfGenus_reindex_iff
    {g : ℕ} {I : Type v} {J : Type w} {S : Scheme.{u}}
    (F : MarkedAlgebraicSpaceOver I S) (e : J ≃ I) :
    IsFamilyOfSemistableMarkedCurvesOfGenus g (F.reindex e) ↔
      IsFamilyOfSemistableMarkedCurvesOfGenus g F := by
  constructor
  · intro h
    have hback := h.reindex e.symm
    rwa [F.reindex_symm e] at hback
  · exact fun h ↦ h.reindex e

/-- API lemma for Definition 6.3.20 (semistable consequence): a
fixed-genus semistable family is semistable after forgetting the genus. -/
theorem IsFamilyOfSemistableMarkedCurvesOfGenus.isFamilyOfSemistableMarkedCurves
    {g : ℕ} {I : Type v} {S : Scheme.{u}}
    {F : MarkedAlgebraicSpaceOver I S}
    (h : IsFamilyOfSemistableMarkedCurvesOfGenus g F) :
    IsFamilyOfSemistableMarkedCurves F := by
  refine ⟨h.1, ?_⟩
  intro K _ _ s
  obtain ⟨P, hP⟩ := h.2 K s
  exact ⟨P, g, hP⟩

/-- API lemma for Definition 6.3.20 (fixed-genus
semistable consequence): forgetting semistability retains a prestable family of the
same genus. -/
theorem IsFamilyOfSemistableMarkedCurvesOfGenus.isFamilyOfPrestableMarkedCurvesOfGenus
    {g : ℕ} {I : Type v} {S : Scheme.{u}}
    {F : MarkedAlgebraicSpaceOver I S}
    (h : IsFamilyOfSemistableMarkedCurvesOfGenus g F) :
    IsFamilyOfPrestableMarkedCurvesOfGenus g F := by
  refine ⟨h.1, ?_⟩
  exact MarkedAlgebraicSpaceOver.HasPresentedGeometricFibers.mono
    (Q := Scheme.semistableMarkedCurveOfGenusGeometricFiberPredicate I g)
    (R := Scheme.prestableMarkedCurveOfGenusGeometricFiberPredicate I g)
    F (fun (K : Type u) [Field K] [IsAlgClosed K]
      (Z : Scheme.{u}) [Z.Over (Spec (CommRingCat.of K))]
      (p : I → Z.SectionOver (Spec (CommRingCat.of K))) hfiber ↦ hfiber.1) h.2

/-- API lemma for Definition 6.3.20 (semistable consequence):
forgetting semistability gives a prestable family. -/
theorem IsFamilyOfSemistableMarkedCurves.isFamilyOfPrestableMarkedCurves
    {I : Type v} {S : Scheme.{u}} {F : MarkedAlgebraicSpaceOver I S}
    (h : IsFamilyOfSemistableMarkedCurves F) :
    IsFamilyOfPrestableMarkedCurves F := by
  refine ⟨h.1, ?_⟩
  intro K _ _ s
  obtain ⟨P, g, hP⟩ := h.2 K s
  exact ⟨P, g, hP.1⟩

/-- API lemma for Definition 6.3.20 (semistable consequence): a
fixed-genus semistable family is prestable. -/
theorem IsFamilyOfSemistableMarkedCurvesOfGenus.isFamilyOfPrestableMarkedCurves
    {g : ℕ} {I : Type v} {S : Scheme.{u}}
    {F : MarkedAlgebraicSpaceOver I S}
    (h : IsFamilyOfSemistableMarkedCurvesOfGenus g F) :
    IsFamilyOfPrestableMarkedCurves F :=
  h.isFamilyOfSemistableMarkedCurves.isFamilyOfPrestableMarkedCurves

/-- API lemma for Definition 6.3.20 (semistable consequence):
forgetting semistability gives a family of marked nodal curves. -/
theorem IsFamilyOfSemistableMarkedCurves.isFamilyOfMarkedNodalCurves
    {I : Type v} {S : Scheme.{u}} {F : MarkedAlgebraicSpaceOver I S}
    (h : IsFamilyOfSemistableMarkedCurves F) :
    IsFamilyOfMarkedNodalCurves F :=
  h.isFamilyOfPrestableMarkedCurves.isFamilyOfMarkedNodalCurves

/-- Background definition for Definition 6.3.20: a family of marked stable
curves is a family of marked curves whose geometric fibres are stable.  Stability uses
the finite automorphism group of each pointed geometric fibre. -/
def IsFamilyOfStableMarkedCurves {I : Type v} {S : Scheme.{u}}
    (F : MarkedAlgebraicSpaceOver I S) : Prop :=
  IsFamilyOfMarkedCurves F ∧
    F.HasPresentedGeometricFibers
      (Scheme.stableMarkedCurveGeometricFiberPredicate I)

/-- Background definition for Definition 6.3.20 (fixed-genus form). -/
def IsFamilyOfStableMarkedCurvesOfGenus (g : ℕ) {I : Type v}
    {S : Scheme.{u}} (F : MarkedAlgebraicSpaceOver I S) : Prop :=
  IsFamilyOfMarkedCurves F ∧
    F.HasPresentedGeometricFibers
      (Scheme.stableMarkedCurveOfGenusGeometricFiberPredicate I g)

/-- API lemma for Definition 6.3.20 (stable evaluation): every
presentation of a geometric fibre is stable. -/
theorem IsFamilyOfStableMarkedCurves.isStableOnPresentedGeometricFiber
    {I : Type v} {S : Scheme.{u}} {F : MarkedAlgebraicSpaceOver I S}
    (h : IsFamilyOfStableMarkedCurves F)
    {K : Type u} [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ S)
    (P : F.PresentedGeometricFiber K s) :
    @Scheme.IsStableMarkedCurveOver K _ _ I P.scheme ⟨P.toBase⟩ P.marking :=
  MarkedAlgebraicSpaceOver.HasPresentedGeometricFibers.prop
    (Q := Scheme.stableMarkedCurveGeometricFiberPredicate I) F h.2 s P

/-- API lemma for Definition 6.3.20 (stable evaluation): every
presentation of a fixed-genus geometric fibre is stable of that genus. -/
theorem IsFamilyOfStableMarkedCurvesOfGenus.isStableOnPresentedGeometricFiber
    {g : ℕ} {I : Type v} {S : Scheme.{u}}
    {F : MarkedAlgebraicSpaceOver I S}
    (h : IsFamilyOfStableMarkedCurvesOfGenus g F)
    {K : Type u} [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ S)
    (P : F.PresentedGeometricFiber K s) :
    @Scheme.IsStableMarkedCurveOfGenusOver K _ _ I g P.scheme
      ⟨P.toBase⟩ P.marking :=
  MarkedAlgebraicSpaceOver.HasPresentedGeometricFibers.prop
    (Q := Scheme.stableMarkedCurveOfGenusGeometricFiberPredicate I g)
    F h.2 s P

/-- API lemma for Definition 6.3.20 (stable reindexing):
stability is preserved by an equivalence of marking index types. -/
theorem IsFamilyOfStableMarkedCurves.reindex
    {I : Type v} {J : Type w} {S : Scheme.{u}}
    {F : MarkedAlgebraicSpaceOver I S}
    (h : IsFamilyOfStableMarkedCurves F) (e : J ≃ I) :
    IsFamilyOfStableMarkedCurves (F.reindex e) := by
  refine ⟨h.1.reindex e, ?_⟩
  exact MarkedAlgebraicSpaceOver.HasPresentedGeometricFibers.reindex F e
    (fun (_ : Type u) _ _ _ _ _ hstable ↦ hstable.reindex e) h.2

/-- API lemma for Definition 6.3.20 (fixed-genus stable
reindexing): an equivalence of marking indices preserves the genus and stable fibre
condition. -/
theorem IsFamilyOfStableMarkedCurvesOfGenus.reindex
    {g : ℕ} {I : Type v} {J : Type w} {S : Scheme.{u}}
    {F : MarkedAlgebraicSpaceOver I S}
    (h : IsFamilyOfStableMarkedCurvesOfGenus g F) (e : J ≃ I) :
    IsFamilyOfStableMarkedCurvesOfGenus g (F.reindex e) := by
  refine ⟨h.1.reindex e, ?_⟩
  exact MarkedAlgebraicSpaceOver.HasPresentedGeometricFibers.reindex F e
    (fun (_ : Type u) _ _ _ _ _ hstable ↦ hstable.reindex e) h.2

/-- API lemma for Definition 6.3.20 (stable reindexing):
equivalent marking index types give equivalent stable-family conditions. -/
theorem isFamilyOfStableMarkedCurves_reindex_iff
    {I : Type v} {J : Type w} {S : Scheme.{u}}
    (F : MarkedAlgebraicSpaceOver I S) (e : J ≃ I) :
    IsFamilyOfStableMarkedCurves (F.reindex e) ↔
      IsFamilyOfStableMarkedCurves F := by
  constructor
  · intro h
    have hback := h.reindex e.symm
    rwa [F.reindex_symm e] at hback
  · exact fun h ↦ h.reindex e

/-- API lemma for Definition 6.3.20 (fixed-genus stable
reindexing): equivalent marking index types preserve the exact genus stratum. -/
theorem isFamilyOfStableMarkedCurvesOfGenus_reindex_iff
    {g : ℕ} {I : Type v} {J : Type w} {S : Scheme.{u}}
    (F : MarkedAlgebraicSpaceOver I S) (e : J ≃ I) :
    IsFamilyOfStableMarkedCurvesOfGenus g (F.reindex e) ↔
      IsFamilyOfStableMarkedCurvesOfGenus g F := by
  constructor
  · intro h
    have hback := h.reindex e.symm
    rwa [F.reindex_symm e] at hback
  · exact fun h ↦ h.reindex e

/-- API lemma for Definition 6.3.20 (stable consequence): a
fixed-genus stable family is stable after forgetting the genus. -/
theorem IsFamilyOfStableMarkedCurvesOfGenus.isFamilyOfStableMarkedCurves
    {g : ℕ} {I : Type v} {S : Scheme.{u}}
    {F : MarkedAlgebraicSpaceOver I S}
    (h : IsFamilyOfStableMarkedCurvesOfGenus g F) :
    IsFamilyOfStableMarkedCurves F := by
  refine ⟨h.1, ?_⟩
  intro K _ _ s
  obtain ⟨P, hP⟩ := h.2 K s
  let _ : P.scheme.Over (Spec (CommRingCat.of K)) := ⟨P.toBase⟩
  exact ⟨P, hP.isStableMarkedCurveOver⟩

/-- API lemma for Definition 6.3.20 (stable consequence):
forgetting stability gives a family of marked nodal curves. -/
theorem IsFamilyOfStableMarkedCurves.isFamilyOfMarkedNodalCurves
    {I : Type v} {S : Scheme.{u}} {F : MarkedAlgebraicSpaceOver I S}
    (h : IsFamilyOfStableMarkedCurves F) :
    IsFamilyOfMarkedNodalCurves F := by
  refine ⟨h.1, ?_⟩
  intro K _ _ s
  obtain ⟨P, hP⟩ := h.2 K s
  let _ : P.scheme.Over (Spec (CommRingCat.of K)) := ⟨P.toBase⟩
  exact ⟨P, hP.nodal⟩

/-- API lemma for Definition 6.3.20 (stable consequence): a
fixed-genus stable family is a family of marked nodal curves. -/
theorem IsFamilyOfStableMarkedCurvesOfGenus.isFamilyOfMarkedNodalCurves
    {g : ℕ} {I : Type v} {S : Scheme.{u}}
    {F : MarkedAlgebraicSpaceOver I S}
    (h : IsFamilyOfStableMarkedCurvesOfGenus g F) :
    IsFamilyOfMarkedNodalCurves F :=
  h.isFamilyOfStableMarkedCurves.isFamilyOfMarkedNodalCurves

/-- **Definition 6.3.20** (`def:family-of-stable-curves`) (prestable part): a family of
`n`-pointed prestable curves is a family of `n`-pointed curves whose marked geometric
fibres are prestable. -/
abbrev IsFamilyOfNMarkedPrestableCurves (n : ℕ) {S : Scheme.{u}}
    (F : MarkedAlgebraicSpaceOver (Fin n) S) : Prop :=
  IsFamilyOfPrestableMarkedCurves F

/-- Background definition for Definition 6.3.20 (fixed-genus,
`n`-pointed prestable form). -/
abbrev IsFamilyOfNMarkedPrestableCurvesOfGenus (g n : ℕ) {S : Scheme.{u}}
    (F : MarkedAlgebraicSpaceOver (Fin n) S) : Prop :=
  IsFamilyOfPrestableMarkedCurvesOfGenus g F

/-- Background definition for Definition 6.3.20 (unpointed prestable
form). -/
abbrev IsFamilyOfPrestableCurves {S : Scheme.{u}}
    (F : MarkedAlgebraicSpaceOver (Fin 0) S) : Prop :=
  IsFamilyOfNMarkedPrestableCurves 0 F

/-- Background definition for Definition 6.3.20 (fixed-genus,
unpointed prestable form). -/
abbrev IsFamilyOfPrestableCurvesOfGenus (g : ℕ) {S : Scheme.{u}}
    (F : MarkedAlgebraicSpaceOver (Fin 0) S) : Prop :=
  IsFamilyOfNMarkedPrestableCurvesOfGenus g 0 F

/-- **Definition 6.3.20** (`def:family-of-stable-curves`) (semistable part): a family of
`n`-pointed semistable curves is a family of `n`-pointed curves whose marked geometric
fibres are semistable. -/
abbrev IsFamilyOfNMarkedSemistableCurves (n : ℕ) {S : Scheme.{u}}
    (F : MarkedAlgebraicSpaceOver (Fin n) S) : Prop :=
  IsFamilyOfSemistableMarkedCurves F

/-- Background definition for Definition 6.3.20 (fixed-genus,
`n`-pointed semistable form). -/
abbrev IsFamilyOfNMarkedSemistableCurvesOfGenus (g n : ℕ) {S : Scheme.{u}}
    (F : MarkedAlgebraicSpaceOver (Fin n) S) : Prop :=
  IsFamilyOfSemistableMarkedCurvesOfGenus g F

/-- Background definition for Definition 6.3.20 (unpointed semistable
form). -/
abbrev IsFamilyOfSemistableCurves {S : Scheme.{u}}
    (F : MarkedAlgebraicSpaceOver (Fin 0) S) : Prop :=
  IsFamilyOfNMarkedSemistableCurves 0 F

/-- Background definition for Definition 6.3.20 (fixed-genus,
unpointed semistable form). -/
abbrev IsFamilyOfSemistableCurvesOfGenus (g : ℕ) {S : Scheme.{u}}
    (F : MarkedAlgebraicSpaceOver (Fin 0) S) : Prop :=
  IsFamilyOfNMarkedSemistableCurvesOfGenus g 0 F

/-- **Definition 6.3.20** (`def:family-of-stable-curves`) (stable part): a family of
`n`-pointed stable curves is a family of `n`-pointed curves whose marked geometric fibres
are stable. Stability is expressed by the substantive finite-automorphism formulation. -/
abbrev IsFamilyOfNMarkedStableCurves (n : ℕ) {S : Scheme.{u}}
    (F : MarkedAlgebraicSpaceOver (Fin n) S) : Prop :=
  IsFamilyOfStableMarkedCurves F

/-- Background definition for Definition 6.3.20 (fixed-genus,
`n`-pointed stable form). -/
abbrev IsFamilyOfNMarkedStableCurvesOfGenus (g n : ℕ) {S : Scheme.{u}}
    (F : MarkedAlgebraicSpaceOver (Fin n) S) : Prop :=
  IsFamilyOfStableMarkedCurvesOfGenus g F

/-- Background definition for Definition 6.3.20 (unpointed stable form). -/
abbrev IsFamilyOfStableCurves {S : Scheme.{u}}
    (F : MarkedAlgebraicSpaceOver (Fin 0) S) : Prop :=
  IsFamilyOfNMarkedStableCurves 0 F

/-- Background definition for Definition 6.3.20 (fixed-genus, unpointed
stable form). -/
abbrev IsFamilyOfStableCurvesOfGenus (g : ℕ) {S : Scheme.{u}}
    (F : MarkedAlgebraicSpaceOver (Fin 0) S) : Prop :=
  IsFamilyOfNMarkedStableCurvesOfGenus g 0 F

end DefFamilyOfStableCurves

end AlgebraicGeometry
