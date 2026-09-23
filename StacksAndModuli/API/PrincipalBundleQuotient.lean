module

public import StacksAndModuli.API.GlobalPrincipalBundleEquivariantPullback
public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.5a-fiber-product-quotient-stacks»

/-!
# Quotients of principal bundles

For a principal `G`-bundle `P ⟶ T`, the natural representable family
`T ⟶ [P/G]` is an equivalence.  The inverse descends the invariant composite
from a quotient object to the base `T`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
  CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
  CategoryTheory.MonObj
open scoped CategoryTheory.Obj CategoryTheory.ModObj

universe u

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.Scheme

open CategoryTheory.BasedCategory

namespace PrincipalBundleQuotient

variable {S : Scheme.{u}} {G T : Over S} [GrpObj G]
  [Smooth G.hom] [IsAffineHom G.hom]

/-- A principal bundle, with its identity map to its total space, as an object
of the quotient of that total space. -/
noncomputable def quotientObject (B : GlobalPrincipalBundle G T) :
    ActionQuotientObj G B.P where
  carrier := ⟨T, B⟩
  map := 𝟙 B.P
  equivariant := inferInstance

variable (B : GlobalPrincipalBundle G T)

/-- The invariant map to `T` coequalizes the relation presented by the
source torsor projection. -/
lemma descendedBase_compatible (x : ActionQuotientObj G B.P) :
    ∀ {Z : Scheme.{u}} (a b : Z ⟶ x.carrier.bundle.P.left),
      a ≫ x.carrier.bundle.p.left = b ≫ x.carrier.bundle.p.left →
        a ≫ x.map.left ≫ B.p.left =
          b ≫ x.map.left ≫ B.p.left := by
  letI : IsModHom G x.map := x.equivariant
  intro Z a b hab
  let ZS : Over S := Over.mk (a ≫ x.carrier.bundle.P.hom)
  let aa : ZS ⟶ x.carrier.bundle.P := Over.homMk a rfl
  have hbS : b ≫ x.carrier.bundle.P.hom =
      a ≫ x.carrier.bundle.P.hom := by
    rw [← x.carrier.bundle.p.w]
    exact congrArg (fun q ↦ q ≫ x.carrier.base.hom) hab.symm
  let bb : ZS ⟶ x.carrier.bundle.P := Over.homMk b hbS
  have hp : aa ≫ x.carrier.bundle.p = bb ≫ x.carrier.bundle.p := by
    apply Over.OverMorphism.ext
    exact hab
  let d := x.carrier.bundle.torsorDifference aa bb hp
  have hmap : aa ≫ x.map = d • (bb ≫ x.map) := by
    rw [← IsModHom.map_smul,
      x.carrier.bundle.torsorDifference_smul]
  have hover : (aa ≫ x.map) ≫ B.p = (bb ≫ x.map) ≫ B.p := by
    rw [hmap]
    exact GlobalPrincipalBundle.smul_comp_projection B d (bb ≫ x.map)
  have hleft := congrArg Over.Hom.left hover
  change (a ≫ x.map.left) ≫ B.p.left =
    (b ≫ x.map.left) ≫ B.p.left at hleft
  simpa only [Category.assoc] using hleft

/-- The underlying scheme map descended from the invariant composite to the
base of a principal bundle. -/
noncomputable def descendedBaseLeft (x : ActionQuotientObj G B.P) :
    x.carrier.base.left ⟶ T.left :=
  EffectiveEpi.desc x.carrier.bundle.p.left
    (x.map.left ≫ B.p.left) (descendedBase_compatible B x)

@[reassoc (attr := simp)]
lemma projection_descendedBaseLeft (x : ActionQuotientObj G B.P) :
    x.carrier.bundle.p.left ≫ descendedBaseLeft B x =
      x.map.left ≫ B.p.left := by
  exact EffectiveEpi.fac x.carrier.bundle.p.left
    (x.map.left ≫ B.p.left) (descendedBase_compatible B x)

/-- The base map canonically descended from an object of `[P/G]`, where
`P ⟶ T` is a principal `G`-bundle. -/
noncomputable def descendedBase (x : ActionQuotientObj G B.P) :
    x.carrier.base ⟶ T :=
  Over.homMk (descendedBaseLeft B x) (by
    apply (cancel_epi x.carrier.bundle.p.left).mp
    rw [← Category.assoc, projection_descendedBaseLeft]
    calc
      (x.map.left ≫ B.p.left) ≫ T.hom =
          x.map.left ≫ (B.p.left ≫ T.hom) := Category.assoc _ _ _
      _ = x.map.left ≫ B.P.hom := by rw [B.p.w]
      _ = x.carrier.bundle.P.hom := x.map.w
      _ = x.carrier.bundle.p.left ≫ x.carrier.base.hom :=
        x.carrier.bundle.p.w.symm)

@[reassoc (attr := simp)]
lemma projection_descendedBase (x : ActionQuotientObj G B.P) :
    x.carrier.bundle.p ≫ descendedBase B x = x.map ≫ B.p := by
  apply Over.OverMorphism.ext
  exact projection_descendedBaseLeft B x

/-- Every quotient object maps cartesianly to the principal-bundle object
whose pullbacks define the representable family. -/
noncomputable def toQuotientObject (x : ActionQuotientObj G B.P) :
    x ⟶ quotientObject B where
  carrier :=
    { base := descendedBase B x
      total := x.map
      isPullback := GlobalPrincipalBundle.isPullback_of_equivariant
        x.carrier.bundle B (descendedBase B x) x.map
          (projection_descendedBase B x).symm x.equivariant
      equivariant := x.equivariant }
  map_naturality := Category.comp_id _

/-- The representable family `T ⟶ [P/G]` obtained by pulling back the
principal bundle `P ⟶ T`. -/
noncomputable abbrev family :
    overBased T ⥤ᵇ actionQuotientPrestack G B.P :=
  QuotientFiberProduct.family (quotientObject B)

/-- The classifying morphism `T ⟶ BG` of a principal bundle, obtained by
forgetting the canonical equivariant map from its quotient family. -/
noncomputable abbrev classifyingFamily :
    BasedFunctor (overBased T) (classifyingPrestack G) :=
  (family B).comp actionQuotientPrestack.forget

/-- The canonical cartesian map from a member of the pullback family to the
principal-bundle quotient object. -/
noncomputable def familyTo (X : Over T) :
    (family B).obj X ⟶ quotientObject B where
  carrier :=
    { base := X.hom
      total := Limits.pullback.fst B.p X.hom
      isPullback := IsPullback.of_hasPullback B.p X.hom
      equivariant := by
        constructor
        exact Limits.pullback.lift_fst _ _ _ }
  map_naturality := by
    change Limits.pullback.fst B.p X.hom ≫ 𝟙 B.P =
      Limits.pullback.fst B.p X.hom ≫ 𝟙 B.P
    rfl

lemma familyTo_isHomLift (X : Over T) :
    IsHomLift (actionQuotientPrestack G B.P).p X.hom (familyTo B X) :=
  Functor.IsHomLift.map (p := (actionQuotientPrestack G B.P).p) (familyTo B X)

noncomputable instance family_faithful : (family B).toFunctor.Faithful where
  map_injective {X Y} f g h := by
    apply Over.OverMorphism.ext
    exact congrArg (fun q ↦ q.carrier.base) h

noncomputable instance family_full : (family B).toFunctor.Full where
  map_surjective {X Y} q := by
    have htotal : q.carrier.total ≫
        Limits.pullback.fst B.p Y.hom =
        Limits.pullback.fst B.p X.hom := by
      have h := q.map_naturality
      change q.carrier.total ≫
          (Limits.pullback.fst B.p Y.hom ≫ 𝟙 B.P) =
        Limits.pullback.fst B.p X.hom ≫ 𝟙 B.P at h
      simpa only [Category.assoc, Category.comp_id] using h
    have hpullback : q.carrier.total ≫
        Limits.pullback.snd B.p Y.hom =
        Limits.pullback.snd B.p X.hom ≫ q.carrier.base := by
      have h := q.carrier.isPullback.w
      change q.carrier.total ≫ Limits.pullback.snd B.p Y.hom =
        Limits.pullback.snd B.p X.hom ≫ q.carrier.base at h
      exact h
    letI : Flat (Limits.pullback.snd B.p X.hom).left :=
      (B.pullback X.hom).flat
    letI : Surjective (Limits.pullback.snd B.p X.hom).left :=
      (B.pullback X.hom).surjective
    letI : Epi (Limits.pullback.snd B.p X.hom).left :=
      Flat.epi_of_flat_of_surjective _
    have hbase : q.carrier.base ≫ Y.hom = X.hom := by
      apply Over.OverMorphism.ext
      apply (cancel_epi (Limits.pullback.snd B.p X.hom).left).mp
      have hOver : Limits.pullback.snd B.p X.hom ≫
          (q.carrier.base ≫ Y.hom) =
          Limits.pullback.snd B.p X.hom ≫ X.hom := by
        calc
          Limits.pullback.snd B.p X.hom ≫
                (q.carrier.base ≫ Y.hom) =
              (Limits.pullback.snd B.p X.hom ≫
                q.carrier.base) ≫ Y.hom :=
            (Category.assoc _ _ _).symm
          _ = (q.carrier.total ≫
                Limits.pullback.snd B.p Y.hom) ≫ Y.hom := by
            rw [hpullback]
          _ = q.carrier.total ≫
                (Limits.pullback.snd B.p Y.hom ≫ Y.hom) :=
            Category.assoc _ _ _
          _ = q.carrier.total ≫
                (Limits.pullback.fst B.p Y.hom ≫ B.p) := by
            rw [Limits.pullback.condition]
          _ = (q.carrier.total ≫
                Limits.pullback.fst B.p Y.hom) ≫ B.p :=
            (Category.assoc _ _ _).symm
          _ = Limits.pullback.fst B.p X.hom ≫ B.p := by rw [htotal]
          _ = Limits.pullback.snd B.p X.hom ≫ X.hom :=
            Limits.pullback.condition
      exact congrArg Over.Hom.left hOver
    let f : X ⟶ Y := Over.homMk q.carrier.base hbase
    refine ⟨f, ?_⟩
    apply ActionQuotientHom.ext
    apply ClassifyingHom.ext
    · rfl
    · change QuotientFiberProduct.pullbackTotalMap B f = q.carrier.total
      apply Limits.pullback.hom_ext
      · rw [QuotientFiberProduct.pullbackTotalMap_fst]
        exact htotal.symm
      · rw [QuotientFiberProduct.pullbackTotalMap_snd]
        exact hpullback.symm

noncomputable instance family_essSurj : (family B).toFunctor.EssSurj where
  mem_essImage x := by
    let X : Over T := Over.mk (descendedBase B x)
    let eta := familyTo B X
    let xi := toQuotientObject B x
    let p := (actionQuotientPrestack G B.P).p
    letI heta : IsHomLift p X.hom eta := familyTo_isHomLift B X
    letI hcart : IsStronglyCartesian p X.hom eta :=
      Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift p X.hom eta
    letI hxi : IsHomLift p X.hom xi :=
      Functor.IsHomLift.map (p := p) xi
    let chi : x ⟶ (family B).obj X :=
      IsStronglyCartesian.map p X.hom eta (g := 𝟙 x.carrier.base)
        (f' := X.hom) (Category.id_comp X.hom) xi
    letI hchi : IsHomLift p (𝟙 x.carrier.base) chi :=
      IsStronglyCartesian.map_isHomLift p X.hom eta
        (Category.id_comp X.hom) xi
    letI : IsIso chi :=
      Functor.IsFiberedInGroupoids.isIso_of_isHomLift_isIso
        (p := p) (𝟙 x.carrier.base) chi
    exact ⟨X, ⟨(asIso chi).symm⟩⟩

/-- A principal bundle is the quotient of its total space by its structure
group: the natural family `T ⟶ [P/G]` is an equivalence. -/
theorem family_isEquivalence : (family B).toFunctor.IsEquivalence := by
  exact
    { faithful := family_faithful B
      full := family_full B
      essSurj := family_essSurj B }

end PrincipalBundleQuotient

end AlgebraicGeometry.Scheme
