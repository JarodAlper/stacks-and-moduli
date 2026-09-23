module

public import StacksAndModuli.API.ReducedClosedSubscheme
public import StacksAndModuli.«Section6.3-Stable».«part6.3.3-low-valence-rational-components»

/-!
# Stable curves: rational tails and bridges

This module follows the subsection "Rational tails and bridges" of §6.3 (Stable curves)
of *Stacks and Moduli*, section label
`sec:stable-curves`.

An irreducible smooth genus-zero subcurve is allowed over an arbitrary field. Its closed
complement is the reduced induced subscheme on the closure of the set-theoretic
complement, and its scheme-theoretic intersection with that complement is their
categorical pullback over the ambient curve.

## Main definitions

* `SmoothGenusZeroSubcurveOver.IsRationalTail`: the rational-tail predicate.
* `SmoothGenusZeroSubcurveOver.IsRationalBridge`: the rational-bridge predicate.

## Supporting definitions and API

* `AlgebraicGeometry.Scheme.SmoothGenusZeroSubcurveOver`: an irreducible smooth
  genus-zero closed subcurve over a field.
* `SmoothGenusZeroSubcurveOver.complement` and
  `SmoothGenusZeroSubcurveOver.intersection`: the complement and its scheme-theoretic
  intersection with the subcurve.
* `SmoothGenusZeroSubcurveOver.isRationalTail_iff`: the rational-tail conditions,
  unfolded.
* `SmoothGenusZeroSubcurveOver.isRationalBridge_iff`: the two rational-bridge cases,
  unfolded.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry.Scheme

section DefRationalTailsBridges

/-- Background definition for Definition 6.3.12 (implicit subcurve datum):
an irreducible smooth genus-zero closed subcurve `E ⊆ C` over an arbitrary field.

The source is bundled as an object over `Spec k`, so the inclusion is required to
preserve the specified `k`-scheme structures. The `IsCurveOver` field makes the word
"subcurve" literal rather than treating it as an arbitrary closed subscheme. -/
structure SmoothGenusZeroSubcurveOver (k : Type u) [Field k] (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))] where
  /-- The subcurve with its structure morphism to `Spec k`. -/
  curve : Over (Spec (CommRingCat.of k))
  /-- The inclusion of the subcurve, bundled over `Spec k`. -/
  ι : curve ⟶ C.asOver (Spec (CommRingCat.of k))
  /-- The inclusion is a closed immersion. -/
  isClosedImmersion : IsClosedImmersion ι.left
  /-- The source is a curve over `k`. -/
  isCurveOver : IsCurveOver k curve.left
  /-- The source is irreducible. -/
  irreducible : IrreducibleSpace curve.left
  /-- The source is smooth over `k`. -/
  smooth : Smooth curve.hom
  /-- The source has genus zero over `k`. -/
  genus_eq_zero : genusOver k curve.left = 0

namespace SmoothGenusZeroSubcurveOver

variable {k : Type u} [Field k] {C : Scheme.{u}}
  [C.Over (Spec (CommRingCat.of k))]

/-- Background definition for Definition 6.3.12 (implicit complement):
the closed subset `closure (C \ E)` underlying the complement closure of `E`. -/
noncomputable def complementClosed (E : SmoothGenusZeroSubcurveOver k C) : Closeds C :=
  Closeds.closure ((Set.range E.ι.left)ᶜ)

/-- Background definition for Definition 6.3.12 (implicit complement):
the canonical reduced closed subscheme on `closure (C \ E)`. -/
noncomputable def complement (E : SmoothGenusZeroSubcurveOver k C) : Scheme.{u} :=
  C.reducedClosedSubscheme E.complementClosed

/-- Background definition for Definition 6.3.12 (implicit complement):
the canonical closed immersion `Eᶜ ⟶ C`. -/
noncomputable def complementι (E : SmoothGenusZeroSubcurveOver k C) :
    E.complement ⟶ C :=
  C.reducedClosedSubschemeι E.complementClosed

/-- API lemma for Definition 6.3.12 (complement API): the
complement inclusion is the subtype inclusion on points. -/
@[simp]
theorem complementι_apply (E : SmoothGenusZeroSubcurveOver k C) (x : E.complement) :
    E.complementι x = x.1 :=
  rfl

/-- Helper lemma for Definition 6.3.12 (complement API): the
image of `Eᶜ ⟶ C` is exactly `closure (C \ E)`. -/
@[simp]
theorem range_complementι (E : SmoothGenusZeroSubcurveOver k C) :
    Set.range E.complementι = closure ((Set.range E.ι.left)ᶜ) := by
  exact (C.range_reducedClosedSubschemeι E.complementClosed).trans
    (Closeds.coe_closure _)

/-- Supporting instance for Definition 6.3.12 (complement API): the
canonical map `Eᶜ ⟶ C` is a closed immersion. -/
instance complementι_isClosedImmersion (E : SmoothGenusZeroSubcurveOver k C) :
    IsClosedImmersion E.complementι := by
  dsimp only [complementι, complement]
  infer_instance

/-- Supporting instance for Definition 6.3.12 (complement API): the
canonical closed complement carries the reduced induced scheme structure. -/
instance complement_isReduced (E : SmoothGenusZeroSubcurveOver k C) :
    IsReduced E.complement := by
  dsimp only [complement]
  infer_instance

/-- Background definition for Definition 6.3.12 (implicit complement):
the assertion that the canonical complement closure `Eᶜ` is nonempty. -/
def HasNonemptyComplement (E : SmoothGenusZeroSubcurveOver k C) : Prop :=
  Nonempty E.complement

/-- API lemma for Definition 6.3.12 (complement API): the
canonical complement closure is nonempty exactly when the set-theoretic complement of
the subcurve is nonempty. -/
theorem hasNonemptyComplement_iff (E : SmoothGenusZeroSubcurveOver k C) :
    E.HasNonemptyComplement ↔ (Set.range E.ι.left)ᶜ.Nonempty := by
  rw [← closure_nonempty_iff]
  constructor
  · rintro ⟨x⟩
    rw [← E.range_complementι]
    exact ⟨E.complementι x, x, rfl⟩
  · intro h
    rw [← E.range_complementι] at h
    obtain ⟨_, x, rfl⟩ := h
    exact ⟨x⟩

/-- Background definition for Definition 6.3.12 (implicit intersection):
the scheme-theoretic intersection `E ∩ Eᶜ`, formed as the pullback over `C`. -/
noncomputable abbrev intersection (E : SmoothGenusZeroSubcurveOver k C) : Scheme.{u} :=
  pullback E.ι.left E.complementι

/-- Background definition for Definition 6.3.12 (intersection API): the
first projection `E ∩ Eᶜ ⟶ E`. -/
noncomputable abbrev intersectionToSubcurve
    (E : SmoothGenusZeroSubcurveOver k C) : E.intersection ⟶ E.curve.left :=
  pullback.fst E.ι.left E.complementι

/-- Background definition for Definition 6.3.12 (intersection API): the
second projection `E ∩ Eᶜ ⟶ Eᶜ`. -/
noncomputable abbrev intersectionToComplement
    (E : SmoothGenusZeroSubcurveOver k C) : E.intersection ⟶ E.complement :=
  pullback.snd E.ι.left E.complementι

/-- Background definition for Definition 6.3.12 (intersection API): the
canonical map `E ∩ Eᶜ ⟶ C`. -/
noncomputable def intersectionι (E : SmoothGenusZeroSubcurveOver k C) :
    E.intersection ⟶ C :=
  E.intersectionToSubcurve ≫ E.ι.left

/-- API lemma for Definition 6.3.12 (intersection API): both
projections from the scheme-theoretic intersection induce the same map to `C`. -/
@[reassoc (attr := simp)]
theorem intersectionToComplement_comp_complementι
    (E : SmoothGenusZeroSubcurveOver k C) :
    E.intersectionToComplement ≫ E.complementι = E.intersectionι := by
  exact pullback.condition.symm

/-- Supporting instance for Definition 6.3.12 (intersection API): the
projection `E ∩ Eᶜ ⟶ E` is a closed immersion. -/
instance intersectionToSubcurve_isClosedImmersion
    (E : SmoothGenusZeroSubcurveOver k C) :
    IsClosedImmersion E.intersectionToSubcurve := by
  dsimp only [intersectionToSubcurve, intersection]
  infer_instance

/-- Supporting instance for Definition 6.3.12 (intersection API): the
projection `E ∩ Eᶜ ⟶ Eᶜ` is a closed immersion. -/
instance intersectionToComplement_isClosedImmersion
    (E : SmoothGenusZeroSubcurveOver k C) :
    IsClosedImmersion E.intersectionToComplement := by
  let _ : IsClosedImmersion E.ι.left := E.isClosedImmersion
  dsimp only [intersectionToComplement, intersection]
  infer_instance

/-- Supporting instance for Definition 6.3.12 (intersection API): the
canonical map `E ∩ Eᶜ ⟶ C` is a closed immersion. -/
instance intersectionι_isClosedImmersion (E : SmoothGenusZeroSubcurveOver k C) :
    IsClosedImmersion E.intersectionι := by
  let _ : IsClosedImmersion E.ι.left := E.isClosedImmersion
  dsimp only [intersectionι]
  infer_instance

/-- Background definition for Definition 6.3.12 (intersection API): the
canonical ring map `Γ(E, 𝒪_E) ⟶ Γ(E ∩ Eᶜ, 𝒪)` induced by the first projection. -/
noncomputable abbrev intersectionGlobalSectionsMap
    (E : SmoothGenusZeroSubcurveOver k C) :
    Γ(E.curve.left, ⊤) →+* Γ(E.intersection, ⊤) :=
  E.intersectionToSubcurve.appTop.hom

/-- Background definition for Definition 6.3.12 (intersection API): the
degree of `E ∩ Eᶜ` over `Γ(E, 𝒪_E)`, measured as the rank of its global sections.

In the prestable-curve context of the definition, `E` is proper, reduced, and connected,
so `Γ(E, 𝒪_E)` is a field and this is the usual vector-space degree. -/
noncomputable def intersectionDegree (E : SmoothGenusZeroSubcurveOver k C) : ℕ :=
  letI : Algebra Γ(E.curve.left, ⊤) Γ(E.intersection, ⊤) :=
    E.intersectionGlobalSectionsMap.toAlgebra
  Module.finrank Γ(E.curve.left, ⊤) Γ(E.intersection, ⊤)

/-- Background definition for Definition 6.3.12 (intersection API): the
canonical evaluation map `Γ(E, 𝒪_E) ⟶ κ(x)` at a point of the subcurve. -/
noncomputable abbrev globalSectionsToResidueField
    (E : SmoothGenusZeroSubcurveOver k C) (x : E.curve.left) :
    Γ(E.curve.left, ⊤) →+* E.curve.left.residueField x :=
  E.curve.left.Γevaluation x |>.hom

/-- Background definition for Definition 6.3.12 (single-point
intersection): `E ∩ Eᶜ` is the single reduced point `x` when its first projection is
the canonical residue-field point at `x`. -/
def IsSingleReducedIntersectionAt (E : SmoothGenusZeroSubcurveOver k C)
    (x : E.curve.left) : Prop :=
  E.intersectionToSubcurve.IsSingleReducedPointAt x

/-- API lemma for Definition 6.3.12 (single-point
intersection), unfolded into the compatible residue-field isomorphism. -/
lemma isSingleReducedIntersectionAt_iff
    (E : SmoothGenusZeroSubcurveOver k C) (x : E.curve.left) :
    E.IsSingleReducedIntersectionAt x ↔
      ∃ e : E.intersection ≅ Spec (E.curve.left.residueField x),
        e.hom ≫ E.curve.left.fromSpecResidueField x =
          E.intersectionToSubcurve :=
  Iff.rfl

/-- Background definition for Definition 6.3.12 (marking API): a marked
point lies on `E` when its underlying point belongs to the image of `E ⟶ C`. -/
def ContainsMarkedPoint (E : SmoothGenusZeroSubcurveOver k C)
    (q : C.SectionOver (Spec (CommRingCat.of k))) : Prop :=
  q.point ∈ Set.range E.ι.left

/-- Background definition for Definition 6.3.12 (marking API): no member
of the indexed marking family lies on `E`. -/
def ContainsNoMarkedPoints {I : Type v} (E : SmoothGenusZeroSubcurveOver k C)
    (p : I → C.SectionOver (Spec (CommRingCat.of k))) : Prop :=
  ∀ i, ¬ E.ContainsMarkedPoint (p i)

/-- Background definition for Definition 6.3.12 (marking API): the
canonical marking family obtained by deleting the marking indexed by `j`. -/
def deleteMarking {I : Type v}
    (p : I → C.SectionOver (Spec (CommRingCat.of k))) (j : I) :
    {i : I // i ≠ j} → C.SectionOver (Spec (CommRingCat.of k)) :=
  fun i ↦ p i.1

/-- API lemma for Definition 6.3.12 (marking API): evaluating
the deleted marking family forgets only its proof that the index differs from `j`. -/
@[simp]
theorem deleteMarking_apply {I : Type v}
    (p : I → C.SectionOver (Spec (CommRingCat.of k))) (j : I)
    (i : {i : I // i ≠ j}) :
    deleteMarking p j i = p i.1 :=
  rfl

/-- API lemma for Definition 6.3.12 (marking API): after
deleting `j`, no marked point lies on `E` exactly when every marking with index distinct
from `j` lies off `E`. -/
theorem containsNoMarkedPoints_deleteMarking_iff {I : Type v}
    (E : SmoothGenusZeroSubcurveOver k C)
    (p : I → C.SectionOver (Spec (CommRingCat.of k))) (j : I) :
    E.ContainsNoMarkedPoints (deleteMarking p j) ↔
      ∀ i, i ≠ j → ¬ E.ContainsMarkedPoint (p i) := by
  constructor
  · intro h i hi
    exact h ⟨i, hi⟩
  · intro h i
    exact h i.1 i.2

/-- **Definition 6.3.12** (`def:rational-tails-bridges`) (rational tail): an
irreducible smooth genus-zero subcurve is a rational tail when its complement is
nonempty, its scheme-theoretic intersection with the complement is one reduced point
`x`, the canonical map `Γ(E, 𝒪_E) ⟶ κ(x)` is an isomorphism, and it contains no marked
points. -/
def IsRationalTail {I : Type v} (E : SmoothGenusZeroSubcurveOver k C)
    (p : I → C.SectionOver (Spec (CommRingCat.of k))) : Prop :=
  E.HasNonemptyComplement ∧
    ∃ x : E.curve.left,
      E.IsSingleReducedIntersectionAt x ∧
        Function.Bijective (E.globalSectionsToResidueField x) ∧
          E.ContainsNoMarkedPoints p

/-- API lemma for Definition 6.3.12 (rational tail), unfolded
into its complement, intersection, global-functions, and marking conditions. -/
theorem isRationalTail_iff {I : Type v} (E : SmoothGenusZeroSubcurveOver k C)
    (p : I → C.SectionOver (Spec (CommRingCat.of k))) :
    E.IsRationalTail p ↔
      E.HasNonemptyComplement ∧
        ∃ x : E.curve.left,
          E.IsSingleReducedIntersectionAt x ∧
            Function.Bijective (E.globalSectionsToResidueField x) ∧
              E.ContainsNoMarkedPoints p :=
  Iff.rfl

/-- **Definition 6.3.12** (`def:rational-tails-bridges`) (rational bridge): an
irreducible smooth genus-zero subcurve with nonempty complement is a rational bridge if
either its intersection with the complement has degree two over `Γ(E, 𝒪_E)` and it has
no marked points, or it contains a marked point `p_j` and becomes a rational tail after
that marking is deleted. -/
def IsRationalBridge {I : Type v} (E : SmoothGenusZeroSubcurveOver k C)
    (p : I → C.SectionOver (Spec (CommRingCat.of k))) : Prop :=
  E.HasNonemptyComplement ∧
    ((E.intersectionDegree = 2 ∧ E.ContainsNoMarkedPoints p) ∨
      ∃ j : I,
        E.ContainsMarkedPoint (p j) ∧
          E.IsRationalTail (deleteMarking p j))

/-- API lemma for Definition 6.3.12 (rational bridge), unfolded
into the unmarked degree-two case and the one-marked rational-tail case. -/
theorem isRationalBridge_iff {I : Type v} (E : SmoothGenusZeroSubcurveOver k C)
    (p : I → C.SectionOver (Spec (CommRingCat.of k))) :
    E.IsRationalBridge p ↔
      E.HasNonemptyComplement ∧
        ((E.intersectionDegree = 2 ∧ E.ContainsNoMarkedPoints p) ∨
          ∃ j : I,
            E.ContainsMarkedPoint (p j) ∧
              E.IsRationalTail (deleteMarking p j)) :=
  Iff.rfl

/-- Helper lemma for Definition 6.3.12 (constructor): an
unmarked subcurve with nonempty complement and degree-two intersection is a rational
bridge. -/
theorem IsRationalBridge.of_degree_two {I : Type v}
    (E : SmoothGenusZeroSubcurveOver k C)
    (p : I → C.SectionOver (Spec (CommRingCat.of k)))
    (hcomplement : E.HasNonemptyComplement) (hdegree : E.intersectionDegree = 2)
    (hmarks : E.ContainsNoMarkedPoints p) : E.IsRationalBridge p :=
  ⟨hcomplement, Or.inl ⟨hdegree, hmarks⟩⟩

/-- Helper lemma for Definition 6.3.12 (constructor): a subcurve
containing `p_j` which is a rational tail after deleting `j` is a rational bridge. -/
theorem IsRationalBridge.of_marked_tail {I : Type v}
    (E : SmoothGenusZeroSubcurveOver k C)
    (p : I → C.SectionOver (Spec (CommRingCat.of k))) (j : I)
    (hmark : E.ContainsMarkedPoint (p j))
    (htail : E.IsRationalTail (deleteMarking p j)) : E.IsRationalBridge p :=
  ⟨htail.1, Or.inr ⟨j, hmark, htail⟩⟩

/-- API lemma for Definition 6.3.12 (uniqueness in the marked
bridge case): if `p_j` lies on `E` and deleting it makes `E` a rational tail, every other
marking lies off `E`. -/
theorem IsRationalTail.containsMarkedPoint_imp_eq {I : Type v}
    (E : SmoothGenusZeroSubcurveOver k C)
    (p : I → C.SectionOver (Spec (CommRingCat.of k))) (j i : I)
    (htail : E.IsRationalTail (deleteMarking p j))
    (hi : E.ContainsMarkedPoint (p i)) : i = j := by
  by_contra hij
  exact htail.2.choose_spec.2.2 ⟨i, hij⟩ hi

end SmoothGenusZeroSubcurveOver

end DefRationalTailsBridges

end AlgebraicGeometry.Scheme
