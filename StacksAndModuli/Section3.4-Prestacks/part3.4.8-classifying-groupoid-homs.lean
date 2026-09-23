module

public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.7-universal-family»
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Morphisms between classifying groupoids

This module formalizes the ordinary-groupoid calculation underlying the final
unlabeled exercise of §3.4 (Prestacks) of *Stacks and Moduli*,
section label `sec:prestacks`.

For groups `H` and `G`, functors `B H → B G` are homomorphisms `H → G`, while
natural isomorphisms are conjugating elements of `G`.  Thus the functor groupoid
`MOR(B H, B G)` is equivalent to `[Hom(H,G)/G]`.  This is the exact groupoid
calculation on which the stated group-scheme/prestack result is based; extending it
to arbitrary torsors also requires induction of principal bundles, recorded in the
section commentary.

Main declaration:
- `CategoryTheory.ClassifyingGroupoidHom.equivalence`: the equivalence
  `MOR(B H, B G) ≃ [Hom(H,G)/G]` for ordinary groups.
-/

@[expose] public section

open CategoryTheory

universe u v

section FinalUnlabeledClassifyingHomExercise

namespace CategoryTheory.ClassifyingGroupoidHom

variable (H : Type u) (G : Type v) [Group H] [Group G]

/-- Background definition for the final unlabeled exercise in Section 3.4: a separate
carrier for homomorphisms `H → G`, used to install
the conjugation action without creating an orphan action on `MonoidHom`. -/
def ConjugationHom := H →* G

namespace ConjugationHom

/-- Regard a homomorphism as an object of the conjugation carrier. -/
def mk (phi : H →* G) : ConjugationHom H G := phi

/-- Recover the homomorphism underlying an object of the conjugation carrier. -/
def as (phi : ConjugationHom H G) : H →* G := phi

@[simp]
lemma as_mk (phi : H →* G) : as H G (mk H G phi) = phi := rfl

/-- Conjugate a homomorphism by an element of its target group. -/
def conjugate (g : G) (phi : ConjugationHom H G) : ConjugationHom H G :=
  mk H G ((MulAut.conj g).toMonoidHom.comp (as H G phi))

@[simp]
lemma conjugate_as_apply (g : G) (phi : ConjugationHom H G) (h : H) :
    as H G (conjugate H G g phi) h = g * as H G phi h * g⁻¹ :=
  rfl

/-- Background instance for the final unlabeled exercise in Section 3.4: `G` acts on
homomorphisms `H → G` by target conjugation. -/
instance : MulAction G (ConjugationHom H G) where
  smul := conjugate H G
  one_smul phi := by
    apply congrArg (mk H G)
    apply MonoidHom.ext
    intro h
    change 1 * as H G phi h * 1⁻¹ = as H G phi h
    simp
  mul_smul g k phi := by
    apply congrArg (mk H G)
    apply MonoidHom.ext
    intro h
    change (g * k) * as H G phi h * (g * k)⁻¹ =
      g * (k * as H G phi h * k⁻¹) * g⁻¹
    rw [mul_inv_rev]
    simp only [mul_assoc]

end ConjugationHom

/-- The action groupoid `[Hom(H,G)/G]` for target conjugation. -/
abbrev HomGroupoid := ActionGroupoid G (ConjugationHom H G)

/-- Background comparison for the final unlabeled exercise in Section 3.4: send a
functor `B H → B G` to its homomorphism on arrows,
and a natural transformation to its conjugating component. -/
def comparison : (SingleObj H ⥤ SingleObj G) ⥤ HomGroupoid H G where
  obj F :=
    ActionGroupoid.mk (ConjugationHom.mk H G ((SingleObj.mapHom H G).symm F))
  map {F K} alpha :=
    { gauge := alpha.app (SingleObj.star H)
      smul_eq := by
        apply MonoidHom.ext
        intro h
        have hn := alpha.naturality (SingleObj.toEnd H h)
        change alpha.app (SingleObj.star H) * F.map h *
            (alpha.app (SingleObj.star H))⁻¹ = K.map h
        rw [SingleObj.comp_as_mul, SingleObj.comp_as_mul] at hn
        change alpha.app (SingleObj.star H) * F.map h =
          K.map h * alpha.app (SingleObj.star H) at hn
        calc
          alpha.app (SingleObj.star H) * F.map h *
              (alpha.app (SingleObj.star H))⁻¹ =
            (K.map h * alpha.app (SingleObj.star H)) *
              (alpha.app (SingleObj.star H))⁻¹ := by rw [hn]
          _ = K.map h := by simp }
  map_id F := by
    apply ActionGroupoid.Hom.ext
    rfl
  map_comp alpha beta := by
    apply ActionGroupoid.Hom.ext
    rfl

instance comparison_faithful : (comparison H G).Faithful where
  map_injective {F K} alpha beta h := by
    apply NatTrans.ext
    funext x
    cases x
    exact congrArg ActionGroupoid.Hom.gauge h

instance comparison_full : (comparison H G).Full where
  map_surjective {F K} q := by
    let alpha : F ⟶ K := SingleObj.natTrans q.gauge (by
      intro h
      rw [SingleObj.comp_as_mul, SingleObj.comp_as_mul]
      have hs := congrArg
        (fun phi : ConjugationHom H G ↦ ConjugationHom.as H G phi h) q.smul_eq
      change q.gauge * F.map h * q.gauge⁻¹ = K.map h at hs
      rw [← hs]
      simp only [mul_assoc, inv_mul_cancel, mul_one])
    refine ⟨alpha, ?_⟩
    apply ActionGroupoid.Hom.ext
    rfl

instance comparison_essSurj : (comparison H G).EssSurj where
  mem_essImage phi := by
    refine ⟨(ConjugationHom.as H G (ActionGroupoid.as phi)).toFunctor, ?_⟩
    refine ⟨?_⟩
    exact eqToIso (by
      change ActionGroupoid.mk ((SingleObj.mapHom H G).symm
        (ConjugationHom.as H G (ActionGroupoid.as phi)).toFunctor) = phi
      cases phi
      rfl)

/-- Result of the final unlabeled exercise in Section 3.4 (ordinary-groupoid form):

`MOR(B H, B G) ≃ [Hom(H,G)/G]`,

where `G` acts on homomorphisms by conjugation. -/
noncomputable def equivalence :
    (SingleObj H ⥤ SingleObj G) ≌ HomGroupoid H G := by
  letI : (comparison H G).Faithful := comparison_faithful H G
  letI : (comparison H G).Full := comparison_full H G
  letI : (comparison H G).EssSurj := comparison_essSurj H G
  letI : (comparison H G).IsEquivalence := Functor.IsEquivalence.mk
  exact (comparison H G).asEquivalence

end CategoryTheory.ClassifyingGroupoidHom

end FinalUnlabeledClassifyingHomExercise
