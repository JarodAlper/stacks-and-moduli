module

public import StacksAndModuli.API.FreeGrassmannianImmersion
public import StacksAndModuli.API.FreeQuotientRankBound
public import StacksAndModuli.API.ModuleFlatteningImmersion
public import StacksAndModuli.API.ProjectiveSpaceZeroEmptyQuot
public import StacksAndModuli.API.ProjectiveSpaceZeroQuotGrassmannianIsoCore
public import StacksAndModuli.API.TwistedFreeQuotPushforwardRank

/-!
# The projective-zero Quot--Grassmannian immersion

On relative projective zero-space the fixed-constant-polynomial twisted-free Quot
functor is naturally isomorphic to the relative Grassmannian of a free sheaf.  Composing
with the global comparison from the relative free Grassmannian to the kernel-encoded
Grassmannian gives exactly the target required by
`TwistedFreeQuotHasFreeGrassmannianImmersion`.

This file also records the general categorical fact used in that specialization: a
natural isomorphism of presheaves on schemes over a base is relatively representable by
immersions.

Main declarations:

* `AlgebraicGeometry.relative_over_isImmersion_of_isIso`;
* `AlgebraicGeometry.Scheme.Modules.zeroQuotPGrassmannianFunctorOverIso`;
* `AlgebraicGeometry.Scheme.twistedFreeQuotHasFreeGrassmannianImmersion_zero_C`;
* `AlgebraicGeometry.Scheme.
  twistedFreeQuotHasFreeGrassmannianImmersion_zero_of_nonempty_point`;
* `AlgebraicGeometry.Scheme.twistedFreeQuotHasFreeGrassmannianImmersion_zero`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace AlgebraicGeometry

variable {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type (u + 1)}

/-- A natural isomorphism of presheaves on schemes over `S` is relatively
representable by immersions. -/
theorem relative_over_isImmersion_of_isIso (f : F ⟶ G) [IsIso f] :
    MorphismProperty.relative uliftYoneda.{u + 1}
      (MorphismProperty.over
        (@IsImmersion : MorphismProperty Scheme.{u})) f := by
  apply MorphismProperty.relative.of_exists
  intro T g
  refine ⟨T, g ≫ inv f, 𝟙 T, ?_, ?_⟩
  · exact IsPullback.of_vert_isIso ⟨by simp⟩
  · change IsImmersion (𝟙 T.left)
    infer_instance

namespace Scheme.Modules

/-- The projective-zero fixed-constant-polynomial twisted-free Quot functor is
naturally isomorphic to the kernel-encoded free Grassmannian used by the
projectivity endgame. -/
noncomputable def zeroQuotPGrassmannianFunctorOverIso
    (S : Scheme.{u}) (l : ℤ) (r q : ℕ) :
    Scheme.quotFunctorP (Scheme.projectiveSpaceOverTwistedFree 0 S l r)
        (Polynomial.C (q : ℚ)) ≅
      grassmannianFunctorOver S q r :=
  zeroQuotPGrassmannianIso S l r q ≪≫
    freeGrassmannianIsoGrassmannianFunctorOver q

end Scheme.Modules

namespace Scheme

/-- The unique map from the empty `S`-scheme to the standard representative of
`Gr(0,0)`. -/
noncomputable def emptyOverToGrassmannianRepresentation (S : Scheme.{u}) :
    emptyOver S ⟶ grassmannianOverRepresentation S 0 0 :=
  Over.homMk (Scheme.emptyTo _) (Scheme.empty_ext _ _)

/-- The map from the empty `S`-scheme to the standard representative of
`Gr(0,0)` is an immersion. -/
theorem emptyOverToGrassmannianRepresentation_isImmersion (S : Scheme.{u}) :
    IsImmersion (emptyOverToGrassmannianRepresentation S).left := by
  dsimp [emptyOverToGrassmannianRepresentation]
  infer_instance

/-- If a fixed-polynomial twisted-free Quot functor has no points over any
nonempty test scheme, its empty representative immerses into `Gr(0,0)`.  This
supplies the Grassmannian-immersion predicate in every relative dimension. -/
theorem twistedFreeQuotHasFreeGrassmannianImmersion_of_isEmptyOnNonempty
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (hempty : QuotFunctorPEmptyOnNonempty
      (projectiveSpaceOverTwistedFree n S l r) P) :
    TwistedFreeQuotHasFreeGrassmannianImmersion n S l r P := by
  let F := quotFunctorP (projectiveSpaceOverTwistedFree n S l r) P
  let G := Modules.grassmannianFunctorOver S 0 0
  let Z := emptyOver S
  let T := grassmannianOverRepresentation S 0 0
  let eF : uliftYoneda.{u + 1}.obj Z ≅ F :=
    (Functor.RepresentableBy.equivUliftYonedaIso F Z)
      (quotFunctorPRepresentableByEmpty_of_isEmptyOnNonempty
        (projectiveSpaceOverTwistedFree n S l r) P hempty)
  let eG : uliftYoneda.{u + 1}.obj T ≅ G :=
    (Functor.RepresentableBy.equivUliftYonedaIso G T)
      (grassmannianFunctorOverRepresentableBy S 0 0)
  let j : Z ⟶ T := emptyOverToGrassmannianRepresentation S
  let α : F ⟶ G := eF.inv ≫ uliftYoneda.map j ≫ eG.hom
  have hcomm : eF.hom ≫ α = uliftYoneda.map j ≫ eG.hom := by
    simp [α]
  exact twistedFreeQuotHasFreeGrassmannianImmersion_of_relative
    n S l r P 0 0 (by simp) α
      (relative_over_isImmersion_of_iso α eF eG j
        (emptyOverToGrassmannianRepresentation_isImmersion S) hcomm)

/-- In relative dimension zero, and in the nonempty Grassmannian rank range,
the fixed-constant-polynomial twisted-free Quot functor has the precise
free-Grassmannian immersion required by the general projectivity endgame. -/
theorem twistedFreeQuotHasFreeGrassmannianImmersion_zero_C
    (S : Scheme.{u}) (l : ℤ) (r q : ℕ) (hq : q ≤ r) :
    TwistedFreeQuotHasFreeGrassmannianImmersion
      0 S l r (Polynomial.C (q : ℚ)) := by
  let e := Modules.zeroQuotPGrassmannianFunctorOverIso S l r q
  exact twistedFreeQuotHasFreeGrassmannianImmersion_of_relative
    0 S l r (Polynomial.C (q : ℚ)) q r hq e.hom
      (relative_over_isImmersion_of_isIso e.hom)

/-- A point of the projective-zero twisted-free Quot functor over a nonempty
test scheme forces its degree-zero Hilbert value to lie in the free rank range,
and supplies a relatively representable immersion into the corresponding
`Gr(P(0),r)`. -/
theorem exists_relative_isImmersion_zero_hilbertNatValue_of_nonempty_point
    (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (T : Over S) (hT : Nonempty T.left)
    (z : (quotFunctorP (projectiveSpaceOverTwistedFree 0 S l r) P).obj (op T)) :
    let q := P.hilbertNatValue 0
    q ≤ r ∧
      ∃ α : quotFunctorP (projectiveSpaceOverTwistedFree 0 S l r) P ⟶
          Modules.grassmannianFunctorOver S q r,
        MorphismProperty.relative uliftYoneda.{u + 1}
          (MorphismProperty.over
            (@IsImmersion : MorphismProperty Scheme.{u})) α := by
  letI : Nonempty T.left := hT
  obtain ⟨q, rfl⟩ := quotFunctorP_zero_polynomial_eq_C_of_nonempty
    (projectiveSpaceOverTwistedFree 0 S l r) P T z
  have hq : (Polynomial.C (q : ℚ)).hilbertNatValue 0 = q := by
    rw [Polynomial.hilbertNatValue]
    simp
  let e := Modules.zeroQuotPGrassmannianFunctorOverIso S l r q
  have hqr : q ≤ r := by
    let e₀ := Modules.zeroQuotPGrassmannianIso S l r q
    let y := e₀.hom.app (op T) z
    change Quotient (Modules.PullbackQuotient.setoid q
      (SheafOfModules.free (R := S.ringCatSheaf)
        (ULift.{u} (Fin r))) T) at y
    obtain ⟨a, -⟩ := Quotient.exists_rep y
    exact a.rank_le_of_nonempty hT
  rw [hq]
  exact ⟨hqr, e.hom, relative_over_isImmersion_of_isIso e.hom⟩

/-- A point over a nonempty test scheme supplies the precise projective-zero
twisted-free Quot Grassmannian-immersion predicate.  The target used in the
proof is `Gr(P.hilbertNatValue 0,r)`. -/
theorem twistedFreeQuotHasFreeGrassmannianImmersion_zero_of_nonempty_point
    (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (T : Over S) (hT : Nonempty T.left)
    (z : (quotFunctorP (projectiveSpaceOverTwistedFree 0 S l r) P).obj (op T)) :
    TwistedFreeQuotHasFreeGrassmannianImmersion 0 S l r P := by
  obtain ⟨hq, α, hα⟩ :=
    exists_relative_isImmersion_zero_hilbertNatValue_of_nonempty_point
      S l r P T hT z
  exact twistedFreeQuotHasFreeGrassmannianImmersion_of_relative
    0 S l r P (P.hilbertNatValue 0) r hq α hα

/-- In relative dimension zero, every fixed-polynomial twisted-free Quot
functor has a free-Grassmannian immersion.  If there is a point over a
nonempty test scheme, the target rank is `P.hilbertNatValue 0`; otherwise the
empty representative immerses into `Gr(0,0)`. -/
theorem twistedFreeQuotHasFreeGrassmannianImmersion_zero
    (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ) :
    TwistedFreeQuotHasFreeGrassmannianImmersion 0 S l r P := by
  by_cases hempty : QuotFunctorPEmptyOnNonempty
      (projectiveSpaceOverTwistedFree 0 S l r) P
  · exact twistedFreeQuotHasFreeGrassmannianImmersion_of_isEmptyOnNonempty
      0 S l r P hempty
  · change ¬ ∀ T : Over S, Nonempty T.left →
        IsEmpty ((quotFunctorP
          (projectiveSpaceOverTwistedFree 0 S l r) P).obj (op T)) at hempty
    obtain ⟨T, hT⟩ := Classical.not_forall.mp hempty
    obtain ⟨hT, hz⟩ := Classical.not_imp.mp hT
    have hz' : Nonempty
        ((quotFunctorP (projectiveSpaceOverTwistedFree 0 S l r) P).obj (op T)) :=
      not_isEmpty_iff.mp hz
    exact twistedFreeQuotHasFreeGrassmannianImmersion_zero_of_nonempty_point
      S l r P T hT (Classical.choice hz')

end Scheme

end AlgebraicGeometry

end
