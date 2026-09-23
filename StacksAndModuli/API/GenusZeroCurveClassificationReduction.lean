module

public import StacksAndModuli.API.ProjectiveSpaceOverSpecComparison
public import StacksAndModuli.«Section6.1-Smooth».«part6.1.1-curves»
public import StacksProject.API.EtaleNeighborhood

/-!
# Reduction of the genus-zero curve classification

This file isolates the exact missing implication in the classification of proper
genus-zero curves. Over an algebraically closed field, geometric integrality makes the
curve nonempty, and smoothness then supplies a rational point. The comparison between
arithmetic genus and `genusOver` also turns arithmetic genus zero into cohomological
genus zero.

Thus the desired classification reduces to the pointed implication in Exercise 6.1.13:
a proper smooth geometrically integral curve of genus zero with a rational point is the
projective line. Proving that implication requires divisor degree and Riemann--Roch (or
an equivalent birational classification of regular proper curves), none of which is
currently available in Mathlib or this repository.

## Main results

* `AlgebraicGeometry.Scheme.exists_section_toSpec_of_smooth_of_surjective`;
* `AlgebraicGeometry.Scheme.exists_section_toSpec_of_smooth_of_geometricallyIntegral`;
* `AlgebraicGeometry.Scheme.HasPointedSmoothGenusZeroClassification`;
* `AlgebraicGeometry.Scheme.HasSmoothGenusZeroClassification`;
* `AlgebraicGeometry.Scheme.arithmeticGenus_eq_zero_iff_genusOver_eq_zero`;
* `AlgebraicGeometry.Scheme.genusOver_eq_zero_of_arithmeticGenus_eq_zero`;
* `AlgebraicGeometry.Scheme.HasPointedSmoothGenusZeroClassification.
    projectiveLineIso_of_genusOver_eq_zero`;
* `AlgebraicGeometry.Scheme.HasPointedSmoothGenusZeroClassification.
    projectiveLineIso_of_arithmeticGenus_eq_zero`.
* `AlgebraicGeometry.Scheme.hasSmoothGenusZeroClassification_iff_pointed`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- The relative projective line, bundled as an object over the spectrum of its
coefficient field. -/
abbrev projectiveLineAsOver (k : Type u) [Field k] :
    Over (Spec (CommRingCat.of k)) :=
  Over.mk (projectiveSpaceOverπ 1 (Spec (CommRingCat.of k)))

/-- A smooth surjective scheme over a separably closed field has a rational point. The
surjectivity hypothesis supplies the nonempty source required by the standard
smooth-point theorem. -/
theorem exists_section_toSpec_of_smooth_of_surjective
    (k : Type u) [Field k] [IsSepClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] [Surjective f] :
    ∃ s : Spec (CommRingCat.of k) ⟶ X, s ≫ f = 𝟙 _ := by
  let _ : Nonempty X :=
    ⟨(f.surjective (IsLocalRing.closedPoint k)).choose⟩
  exact StacksProject.exists_section_of_smooth_toSpec_of_isSepClosed f

/-- A smooth geometrically integral scheme over a separably closed field has a rational
point. Geometric integrality supplies nonemptiness, after which the standard smooth-point
theorem applies. -/
theorem exists_section_toSpec_of_smooth_of_geometricallyIntegral
    (k : Type u) [Field k] [IsSepClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] [GeometricallyIntegral f] :
    ∃ s : Spec (CommRingCat.of k) ⟶ X, s ≫ f = 𝟙 _ :=
  exists_section_toSpec_of_smooth_of_surjective k f

/-- The pointed implication in the classification of genus-zero curves.

This is Exercise 6.1.13 `(b) → (a)`, expressed with the repository's specified
`k`-scheme structure and `genusOver`. It is deliberately a proposition: downstream
results may accept a proof while the missing Riemann--Roch and divisor APIs are
developed. -/
def HasPointedSmoothGenusZeroClassification (k : Type u) [Field k] : Prop :=
  ∀ (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))]
    [IsCurveOver k C] [IsProper (C ↘ Spec (CommRingCat.of k))]
    [Smooth (C ↘ Spec (CommRingCat.of k))]
    [GeometricallyIntegral (C ↘ Spec (CommRingCat.of k))],
      genusOver k C = 0 →
      (∃ s : Spec (CommRingCat.of k) ⟶ C,
        s ≫ (C ↘ Spec (CommRingCat.of k)) = 𝟙 _) →
      Nonempty
        (projectiveLineAsOver k ≅ C.asOver (Spec (CommRingCat.of k)))

/-- The unpointed classification of proper smooth geometrically integral genus-zero
curves as projective lines. Over an algebraically closed field this is equivalent to
`HasPointedSmoothGenusZeroClassification`, since such a curve automatically has a
rational point. -/
def HasSmoothGenusZeroClassification (k : Type u) [Field k] : Prop :=
  ∀ (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))]
    [IsCurveOver k C] [IsProper (C ↘ Spec (CommRingCat.of k))]
    [Smooth (C ↘ Spec (CommRingCat.of k))]
    [GeometricallyIntegral (C ↘ Spec (CommRingCat.of k))],
      genusOver k C = 0 →
      Nonempty
        (projectiveLineAsOver k ≅ C.asOver (Spec (CommRingCat.of k)))

/-- For a geometrically integral proper scheme over an algebraically closed field,
arithmetic genus vanishes exactly when `genusOver` does. -/
theorem arithmeticGenus_eq_zero_iff_genusOver_eq_zero
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))]
    [IsProper (C ↘ Spec (CommRingCat.of k))]
    [GeometricallyIntegral (C ↘ Spec (CommRingCat.of k))]
    : arithmeticGenus k C = 0 ↔ genusOver k C = 0 := by
  let _ : IsIntegral C :=
    GeometricallyIntegral.isIntegral_of_subsingleton
      (C ↘ Spec (CommRingCat.of k))
  rw [arithmeticGenus_eq_genusOver k C
    (bijective_baseRingHom_of_isAlgClosed k C)]
  norm_cast

/-- For a geometrically integral proper scheme over an algebraically closed field,
arithmetic genus zero implies `genusOver = 0`. -/
theorem genusOver_eq_zero_of_arithmeticGenus_eq_zero
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))]
    [IsProper (C ↘ Spec (CommRingCat.of k))]
    [GeometricallyIntegral (C ↘ Spec (CommRingCat.of k))]
    (hgenus : arithmeticGenus k C = 0) :
    genusOver k C = 0 :=
  (arithmeticGenus_eq_zero_iff_genusOver_eq_zero k C).mp hgenus

namespace HasPointedSmoothGenusZeroClassification

/-- Over an algebraically closed field, the pointed genus-zero classification needs no
separate rational-point hypothesis: smoothness and geometric integrality produce it
automatically. This is the form consumed by component-genus calculations. -/
theorem projectiveLineIso_of_genusOver_eq_zero
    {k : Type u} [Field k] [IsAlgClosed k]
    (H : HasPointedSmoothGenusZeroClassification k)
    (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))]
    [IsCurveOver k C] [IsProper (C ↘ Spec (CommRingCat.of k))]
    [Smooth (C ↘ Spec (CommRingCat.of k))]
    [GeometricallyIntegral (C ↘ Spec (CommRingCat.of k))]
    (hgenus : genusOver k C = 0) :
    Nonempty
      (projectiveLineAsOver k ≅ C.asOver (Spec (CommRingCat.of k))) := by
  apply H C hgenus
  exact exists_section_toSpec_of_smooth_of_geometricallyIntegral k
    (C ↘ Spec (CommRingCat.of k))

/-- Over an algebraically closed field, the pointed genus-zero classification implies
the desired projective-line classification from arithmetic genus zero. No rational-point
hypothesis remains: smoothness and geometric integrality produce it automatically. -/
theorem projectiveLineIso_of_arithmeticGenus_eq_zero
    {k : Type u} [Field k] [IsAlgClosed k]
    (H : HasPointedSmoothGenusZeroClassification k)
    (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))]
    [IsCurveOver k C] [IsProper (C ↘ Spec (CommRingCat.of k))]
    [Smooth (C ↘ Spec (CommRingCat.of k))]
    [GeometricallyIntegral (C ↘ Spec (CommRingCat.of k))]
    (hgenus : arithmeticGenus k C = 0) :
    Nonempty
      (projectiveLineAsOver k ≅ C.asOver (Spec (CommRingCat.of k))) := by
  exact H.projectiveLineIso_of_genusOver_eq_zero C
    (genusOver_eq_zero_of_arithmeticGenus_eq_zero k C hgenus)

end HasPointedSmoothGenusZeroClassification

/-- Over an algebraically closed field, the pointed and unpointed smooth genus-zero
classifications are equivalent. The substantive implication still missing from the
library is the pointed one; the reverse reduction is supplied by automatic existence of
a rational point. -/
theorem hasSmoothGenusZeroClassification_iff_pointed
    (k : Type u) [Field k] [IsAlgClosed k] :
    HasSmoothGenusZeroClassification k ↔
      HasPointedSmoothGenusZeroClassification k := by
  constructor
  · intro H C _ _ _ _ _ hgenus _
    exact H C hgenus
  · intro H C _ _ _ _ _ hgenus
    exact H.projectiveLineIso_of_genusOver_eq_zero C hgenus

end AlgebraicGeometry.Scheme

end
