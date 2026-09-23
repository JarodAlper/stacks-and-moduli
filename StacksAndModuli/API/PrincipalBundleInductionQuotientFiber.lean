module

public import StacksAndModuli.API.PrincipalBundleInductionTrivialization

/-!
# The right-coset quotient as a fiber of induction

Given effective extension of structure group along `H ⟶ G`, an equivariant map
from a principal `H`-bundle to the right-coset `H`-space `G` trivializes the
induced principal `G`-bundle.  This produces the canonical comparison
`[G/H] ⟶ BH ×_BG S`; the comparison is fully faithful.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
  CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
  CategoryTheory.MonObj
open scoped CategoryTheory.Obj CategoryTheory.ModObj

universe u

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.Scheme.ClassifyingStackCartesian

open CategoryTheory.BasedCategory
open PrincipalBundleInduction

variable {S : Scheme.{u}} {H G : Over S} [GrpObj H] [GrpObj G]
  (phi : H ⟶ G) [IsMonHom phi]

/-- The unique map from the right-coset quotient to the representable point. -/
noncomputable def quotientToPoint :
    quotientPrestack phi ⥤ᵇ overBased (𝟙_ (Over S)) := by
  letI : ModObj H G := ModObj.rightCoset phi
  exact
    { obj := fun x ↦ Over.mk (toUnit x.carrier.base)
      map := fun f ↦ Over.homMk f.carrier.base (by apply toUnit_unique)
      map_id := fun _ ↦ by apply Over.OverMorphism.ext; rfl
      map_comp := fun _ _ ↦ by apply Over.OverMorphism.ext; rfl
      w := rfl }

variable [Smooth G.hom] [IsAffineHom G.hom]

/-- Forget the equivariant map in a right-coset quotient object. -/
noncomputable abbrev quotientForget :
    quotientPrestack phi ⥤ᵇ classifyingPrestack H :=
  letI : ModObj H G := ModObj.rightCoset phi
  actionQuotientPrestack.forget

/-- The canonical trivialization of an induced bundle supplied by a quotient object. -/
noncomputable def quotientTrivialization
    (I : EffectiveInduction phi) (x : (quotientPrestack phi).obj) :
    letI : ModObj H G := ModObj.rightCoset phi
    Trivialization phi x (I.cocone x.carrier) := by
  letI : ModObj H G := ModObj.rightCoset phi
  exact Classical.choice
    (Trivialization.nonempty phi x (point_smul phi) (I.cocone x.carrier))

/-- The natural trivialization of the induced bundle over the right-coset quotient. -/
noncomputable def quotientTrivializationIso (I : EffectiveInduction phi) :
    (quotientForget phi).comp I.toBasedFunctor ≅
      (quotientToPoint phi).comp (pointFamily (G := G)) := by
  letI : ModObj H G := ModObj.rightCoset phi
  exact BasedNatIso.mkNatIso
    (NatIso.ofComponents
      (fun x ↦ (quotientTrivialization phi I x).iso)
      (fun {x y} f ↦ Trivialization.map_naturality phi x (point_smul phi) I f
        (quotientTrivialization phi I x) (quotientTrivialization phi I y)))
    (fun x ↦ (quotientTrivialization phi I x).hom_isHomLift)

/-- The canonical comparison `[G/H] ⟶ BH ×_BG S`. -/
noncomputable def quotientFiberComparison (I : EffectiveInduction phi) :
    quotientPrestack phi ⥤ᵇ
      fiberProduct I.toBasedFunctor (pointFamily (G := G)) := by
  letI : ModObj H G := ModObj.rightCoset phi
  exact fiberProductLift (quotientForget phi)
    (quotientToPoint phi) (quotientTrivializationIso phi I)

instance quotientFiberComparison_faithful (I : EffectiveInduction phi) :
    (quotientFiberComparison phi I).toFunctor.Faithful where
  map_injective {_ _} f g h := by
    apply ActionQuotientHom.ext
    exact congrArg FiberProductHom.fst h

instance quotientFiberComparison_full (I : EffectiveInduction phi) :
    (quotientFiberComparison phi I).toFunctor.Full where
  map_surjective {x y} q := by
    letI : ModObj H G := ModObj.rightCoset phi
    let f : x.carrier ⟶ y.carrier := q.fst
    let pointMap : (quotientToPoint phi).obj x ⟶ (quotientToPoint phi).obj y :=
      Over.homMk f.base (by apply toUnit_unique)
    have hsnd : q.snd = pointMap := by
      apply Over.OverMorphism.ext
      letI hqLift : IsHomLift (overBased (𝟙_ (Over S))).p f.base q.snd :=
        q.isHomLift
      have hq := IsHomLift.eq_of_isHomLift
        (p := (overBased (𝟙_ (Over S))).p)
        (a := (quotientToPoint phi).obj x) (b := (quotientToPoint phi).obj y)
        f.base q.snd
      exact hq.symm
    let F := quotientTrivialization phi I x
    let F' := quotientTrivialization phi I y
    have hglobal :
        DescendedHom.normalizedHom phi _ _ _ _ f (I.map f) ≫ F'.hom =
          F.hom ≫ trivialTargetCarrierMap x f := by
      have hw := q.w
      rw [hsnd] at hw
      change _ = F.hom ≫ trivialTargetCarrierMap x f at hw
      exact hw
    let B := x.carrier.bundle
    let B' := y.carrier.bundle
    let C := I.cocone x.carrier
    let C' := I.cocone y.carrier
    let q0 := selfCoverObj B
    let q1 := (mapCoverFunctor B B' f).obj q0
    have hind : C.comparison q0 ≫
        DescendedHom.normalizedHom phi B B' C C' f (I.map f) =
          mapCoconeLeg phi B B' C' f q0 := by
      apply ClassifyingHom.ext
      · letI := (I.map f).hom_isHomLift
        have hbase : f.base = (I.map f).hom.base :=
          IsHomLift.eq_of_isHomLift (classifyingPrestack G).p f.base (I.map f).hom
        have hb := congrArg ClassifyingHom.base ((I.map f).comparison_fac q0)
        change (C.comparison q0).base ≫ f.base = _
        rw [hbase]
        exact hb
      · exact congrArg (fun k ↦ k.total) ((I.map f).comparison_fac q0)
    have hlocal : mapLocalHom phi B B' f q0 ≫ localTrivialization phi y q1 =
        localTrivialization phi x q0 ≫ trivialTargetCarrierMap x f := by
      calc
        mapLocalHom phi B B' f q0 ≫ localTrivialization phi y q1 =
            mapLocalHom phi B B' f q0 ≫ (C'.comparison q1 ≫ F'.hom) := by
              rw [F'.comparison_fac]
        _ = (mapLocalHom phi B B' f q0 ≫ C'.comparison q1) ≫ F'.hom :=
          (Category.assoc _ _ _).symm
        _ = (C.comparison q0 ≫
              DescendedHom.normalizedHom phi B B' C C' f (I.map f)) ≫ F'.hom := by
          rw [hind]
          rfl
        _ = C.comparison q0 ≫
            (DescendedHom.normalizedHom phi B B' C C' f (I.map f) ≫ F'.hom) :=
          Category.assoc _ _ _
        _ = C.comparison q0 ≫ (F.hom ≫ trivialTargetCarrierMap x f) := by
          rw [hglobal]
        _ = (C.comparison q0 ≫ F.hom) ≫ trivialTargetCarrierMap x f :=
          (Category.assoc _ _ _).symm
        _ = localTrivialization phi x q0 ≫ trivialTargetCarrierMap x f := by
          rw [F.comparison_fac]
    have hsection := local_map_naturality_of_trivializations phi x
      (point_smul phi) f q0 hlocal
    letI : IsModHom H (f.total ≫ y.map) := by
      letI : IsModHom H f.total := f.equivariant
      letI : IsModHom H y.map := y.equivariant
      infer_instance
    letI : IsModHom H x.map := x.equivariant
    have hmap : f.total ≫ y.map = x.map :=
      equivariant_map_eq_of_localSection B (f.total ≫ y.map) x.map (by
        simpa only [Category.assoc] using hsection)
    let preimage : x ⟶ y := { carrier := f, map_naturality := hmap }
    refine ⟨preimage, ?_⟩
    apply FiberProductHom.ext
    · rfl
    · change pointMap = q.snd
      exact hsnd.symm

end AlgebraicGeometry.Scheme.ClassifyingStackCartesian
