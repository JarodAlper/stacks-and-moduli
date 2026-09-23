module

public import StacksAndModuli.API.AlgebraicStackDiagonalFiniteType
public import StacksAndModuli.API.FiberProductPostcomp
public import StacksAndModuli.API.RelativeDiagonalBaseChange
public import StacksAndModuli.API.RepresentableWithEquivalence

/-!
# Relative diagonal fibers over a faithful target

If the projection of the target prestack to the base is faithful, the compatibility
condition in a relative diagonal fiber is forced by its two components. Consequently,
the canonical map from a relative-diagonal fiber to the corresponding absolute-diagonal
fiber is an equivalence.

For an arbitrary target, every test point of a relative diagonal lifts to the square of
a scheme-valued base change.  This file also compares the original diagonal fiber with
the fiber over that lift and transfers `RepresentableWith` properties across both
comparisons.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ u

namespace CategoryTheory.BasedCategory

variable {S : Type u₁} [Category.{v₁} S]
  {X : BasedCategory.{v₂, u₂} S}
  {Y : BasedCategory.{v₃, u₃} S}
  {T : BasedCategory.{v₄, u₄} S}

/-- The point of the absolute-diagonal target underlying a point of a relative-diagonal
target. -/
abbrev relativeDiagonalAbsoluteTarget (F : X ⥤ᵇ Y)
    (g : T ⥤ᵇ fiberProduct F F) : T ⥤ᵇ prod X X :=
  g.comp (fiberProductPairMap F F)

/-- The relative diagonal followed by the forgetful map to the absolute product is the
absolute diagonal. -/
lemma relativeDiagonal_comp_fiberProductPairMap (F : X ⥤ᵇ Y) :
    F.diag.comp (fiberProductPairMap F F) = diag X := by
  apply BasedFunctor.ext_of_toFunctor_eq
  rfl

/-- The forgetful map from a relative fiber product to the product of its two factors is
faithful. -/
theorem fiberProductPairMap_faithful (F : X ⥤ᵇ Y) (G : T ⥤ᵇ Y) :
    (fiberProductPairMap F G).toFunctor.Faithful := by
  constructor
  intro a b f g h
  apply FiberProductHom.ext
  · exact congrArg (fun k ↦ k.fst) h
  · exact congrArg (fun k ↦ k.snd) h

/-- If the target projection is faithful, the forgetful map from a relative fiber
product to the product of its factors is full. -/
theorem fiberProductPairMap_full_of_projection_faithful
    (F : X ⥤ᵇ Y) (G : T ⥤ᵇ Y) [Y.p.Faithful] :
    (fiberProductPairMap F G).toFunctor.Full := by
  constructor
  intro a b q
  let r : a ⟶ b :=
    { fst := q.fst
      snd := q.snd
      isHomLift := q.isHomLift
      w := by
        apply Y.p.map_injective
        have hF : IsHomLift Y.p (X.p.map q.fst) (F.map q.fst) :=
          F.preserves_isHomLift _ _
        have hG : IsHomLift Y.p (X.p.map q.fst) (G.map q.snd) :=
          G.preserves_isHomLift _ _
        have ha : IsHomLift Y.p (𝟙 (X.p.obj a.fst)) a.iso.hom := a.isHomLift
        have hb : IsHomLift Y.p (𝟙 (X.p.obj b.fst)) b.iso.hom := b.isHomLift
        letI := hF
        letI := hG
        letI := ha
        letI := hb
        have hleft : IsHomLift Y.p (X.p.map q.fst)
            (F.map q.fst ≫ b.iso.hom) :=
          IsHomLift.comp_lift_id_right' Y.p (X.p.map q.fst)
            (F.map q.fst) (X.p.obj b.fst) b.iso.hom
        have hright : IsHomLift Y.p (X.p.map q.fst)
            (a.iso.hom ≫ G.map q.snd) :=
          IsHomLift.comp_lift_id_left' Y.p (X.p.obj a.fst)
            a.iso.hom (X.p.map q.fst) (G.map q.snd)
        rw [IsHomLift.fac' Y.p (X.p.map q.fst)
          (F.map q.fst ≫ b.iso.hom),
          IsHomLift.fac' Y.p (X.p.map q.fst)
            (a.iso.hom ≫ G.map q.snd)] }
  refine ⟨r, ?_⟩
  apply FiberProductHom.ext <;> rfl

/-- Forgetting the compatibility in the target sends a relative-diagonal fiber to the
corresponding absolute-diagonal fiber. -/
noncomputable def relativeDiagonalFiberToAbsolute (F : X ⥤ᵇ Y)
    (g : T ⥤ᵇ fiberProduct F F) :
    fiberProduct F.diag g ⥤ᵇ
      fiberProduct (diag X) (relativeDiagonalAbsoluteTarget F g) :=
  (fiberProductPostcomp F.diag g (fiberProductPairMap F F)).comp
    (fiberProductMapLeftIso
      (eqToIso (relativeDiagonal_comp_fiberProductPairMap F))
      (relativeDiagonalAbsoluteTarget F g))

/-- The relative-to-absolute diagonal-fiber comparison preserves the structural map to
the test prestack. -/
@[simp]
lemma relativeDiagonalFiberToAbsolute_comp_snd (F : X ⥤ᵇ Y)
    (g : T ⥤ᵇ fiberProduct F F) :
    (relativeDiagonalFiberToAbsolute F g).comp
        (fiberProductSnd (diag X) (relativeDiagonalAbsoluteTarget F g)) =
      fiberProductSnd F.diag g := by
  apply BasedFunctor.ext_of_toFunctor_eq
  rfl

/-- Over a target with faithful projection, a relative-diagonal fiber and its underlying
absolute-diagonal fiber are equivalent. -/
theorem isEquivalence_relativeDiagonalFiberToAbsolute (F : X ⥤ᵇ Y)
    (g : T ⥤ᵇ fiberProduct F F) [Y.p.Faithful] :
    (relativeDiagonalFiberToAbsolute F g).toFunctor.IsEquivalence := by
  let K := fiberProductPairMap F F
  let _ : K.toFunctor.Faithful := fiberProductPairMap_faithful F F
  let _ : K.toFunctor.Full :=
    fiberProductPairMap_full_of_projection_faithful F F
  let E₀ := fiberProductPostcomp F.diag g K
  let E₁ := fiberProductMapLeftIso
    (eqToIso (relativeDiagonal_comp_fiberProductPairMap F))
    (relativeDiagonalAbsoluteTarget F g)
  let _ : E₀.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductPostcomp F.diag g K
  let _ : E₁.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductMapLeftIso
      (eqToIso (relativeDiagonal_comp_fiberProductPairMap F))
      (relativeDiagonalAbsoluteTarget F g)
  exact Functor.isEquivalence_trans E₀.toFunctor E₁.toFunctor

/-- A fiber of a relative diagonal is canonically equivalent to a fiber of the diagonal
of the base change determined by the first component of its test point. -/
noncomputable def relativeDiagonalFiberToBaseChange (F : X ⥤ᵇ Y)
    (g : T ⥤ᵇ fiberProduct F F) :
    fiberProduct F.diag g ⥤ᵇ
      fiberProduct (relativeDiagonalBaseChangeSnd F g).diag
        (relativeDiagonalTargetLift F g) :=
  let q := (relativeDiagonalPointFst F g).comp F
  let H := relativeDiagonalBaseChangeSnd F g
  let L := relativeDiagonalTargetLift F g
  let K := baseChangeDiagonalTarget F q
  let C := baseChangeDiagonalComparison F q
  let Cinv := baseChangeDiagonalComparisonInv F q
  let π := fiberProductSnd F.diag K
  let eH : C.comp π ≅ H.diag :=
    eqToIso (baseChangeDiagonalComparison_comp_snd F q)
  let eC : Cinv.comp H.diag ≅ π :=
    (whiskerLeftIso Cinv eH.symm).trans
      ((eqToIso (BasedFunctor.comp_assoc Cinv C π).symm).trans
        ((whiskerRightIso (baseChangeDiagonalComparisonCounit F q) π).trans
          (eqToIso (BasedFunctor.id_comp π))))
  (((fiberProductMapRightIso F.diag
    (relativeDiagonalTargetLiftIso F g).symm).comp
      (fiberProductAssocInv F.diag K L)).comp
        (fiberProductMapLeftIso eC.symm L)).comp
          (fiberProductLeftMap H.diag L Cinv)

/-- The comparison from an arbitrary relative-diagonal fiber to its base-changed fiber
preserves the structural map to the test prestack. -/
@[simp]
lemma relativeDiagonalFiberToBaseChange_comp_snd (F : X ⥤ᵇ Y)
    (g : T ⥤ᵇ fiberProduct F F) :
    (relativeDiagonalFiberToBaseChange F g).comp
        (fiberProductSnd (relativeDiagonalBaseChangeSnd F g).diag
          (relativeDiagonalTargetLift F g)) =
      fiberProductSnd F.diag g := by
  apply BasedFunctor.ext_of_toFunctor_eq
  rfl

/-- The comparison from an arbitrary relative-diagonal fiber to its base-changed fiber
is an equivalence. -/
theorem isEquivalence_relativeDiagonalFiberToBaseChange (F : X ⥤ᵇ Y)
    (g : T ⥤ᵇ fiberProduct F F)
    [X.p.IsFiberedInGroupoids] [Y.p.IsFiberedInGroupoids]
    [T.p.IsFiberedInGroupoids] :
    (relativeDiagonalFiberToBaseChange F g).toFunctor.IsEquivalence := by
  let q := (relativeDiagonalPointFst F g).comp F
  let H := relativeDiagonalBaseChangeSnd F g
  let L := relativeDiagonalTargetLift F g
  let K := baseChangeDiagonalTarget F q
  let C := baseChangeDiagonalComparison F q
  let Cinv := baseChangeDiagonalComparisonInv F q
  let π := fiberProductSnd F.diag K
  let eH : C.comp π ≅ H.diag :=
    eqToIso (baseChangeDiagonalComparison_comp_snd F q)
  let eC : Cinv.comp H.diag ≅ π :=
    (whiskerLeftIso Cinv eH.symm).trans
      ((eqToIso (BasedFunctor.comp_assoc Cinv C π).symm).trans
        ((whiskerRightIso (baseChangeDiagonalComparisonCounit F q) π).trans
          (eqToIso (BasedFunctor.id_comp π))))
  let M := fiberProductMapRightIso F.diag
    (relativeDiagonalTargetLiftIso F g).symm
  let A := fiberProductAssocInv F.diag K L
  let I := fiberProductMapLeftIso eC.symm L
  let B := fiberProductLeftMap H.diag L Cinv
  let _ : Cinv.toFunctor.IsEquivalence :=
    Functor.IsEquivalence.mk' C.toFunctor
      ((BasedNatTrans.forgetful _ _).mapIso
        (baseChangeDiagonalComparisonCounit F q).symm)
      ((BasedNatTrans.forgetful _ _).mapIso
        (eqToIso (baseChangeDiagonalComparison_comp_inv F q)))
  let _ : M.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductMapRightIso F.diag
      (relativeDiagonalTargetLiftIso F g).symm
  let _ : A.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductAssocInv F.diag K L
  let _ : I.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductMapLeftIso eC.symm L
  let _ : B.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductLeftMap H.diag L Cinv
  let _ : (M.comp A).toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans M.toFunctor A.toFunctor
  let _ : ((M.comp A).comp I).toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans (M.comp A).toFunctor I.toFunctor
  exact Functor.isEquivalence_trans ((M.comp A).comp I).toFunctor B.toFunctor

end CategoryTheory.BasedCategory

namespace AlgebraicGeometry.BasedFunctor

open CategoryTheory.BasedCategory

variable {X : BasedCategory.{v₁, u₁} Scheme.{u}}
  {Y : BasedCategory.{v₂, u₂} Scheme.{u}}

/-- Over a target with faithful projection, every `RepresentableWith` property of the
absolute diagonal transfers to the relative diagonal. -/
theorem RepresentableWith.diag_of_target_projection_faithful
    {P : MorphismProperty Scheme.{u}} [Y.p.Faithful]
    [X.p.IsFiberedInGroupoids] [Y.p.IsFiberedInGroupoids]
    (F : X ⥤ᵇ Y) (h : RepresentableWith P (diag X)) :
    RepresentableWith P F.diag := by
  refine ⟨?_, ?_⟩
  · intro T g
    obtain ⟨A, hA, E, hE⟩ := h.1 T
      (relativeDiagonalAbsoluteTarget F g)
    let K := relativeDiagonalFiberToAbsolute F g
    let _ : K.toFunctor.IsEquivalence :=
      isEquivalence_relativeDiagonalFiberToAbsolute F g
    obtain ⟨J, ⟨α⟩, ⟨β⟩⟩ :=
      CategoryTheory.BasedFunctor.exists_inverse_of_toFunctor K
    have hJ : J.toFunctor.IsEquivalence :=
      Functor.IsEquivalence.mk' K.toFunctor
        ((BasedNatTrans.forgetful _ _).mapIso β).symm
        ((BasedNatTrans.forgetful _ _).mapIso α)
    exact ⟨A, hA, E.comp J,
      Functor.isEquivalence_trans E.toFunctor J.toFunctor⟩
  · intro T g A hA E hE U q hq
    let K := relativeDiagonalFiberToAbsolute F g
    have hK : K.toFunctor.IsEquivalence :=
      isEquivalence_relativeDiagonalFiberToAbsolute F g
    have hP := h.2 T (relativeDiagonalAbsoluteTarget F g) A hA
      (E.comp K) (Functor.isEquivalence_trans E.toFunctor K.toFunctor) U q hq
    dsimp only [K] at hP
    simpa only [CategoryTheory.BasedFunctor.comp_assoc,
      relativeDiagonalFiberToAbsolute_comp_snd] using hP

/-- If the diagonal of every scheme-valued base change of a morphism is representable
with `P`, then so is the original relative diagonal. -/
theorem RepresentableWith.diag_of_scheme_base_changes
    {P : MorphismProperty Scheme.{u}}
    [X.p.IsFiberedInGroupoids] [Y.p.IsFiberedInGroupoids]
    (F : X ⥤ᵇ Y)
    (h : ∀ (T : Scheme.{u}) (g : overBased T ⥤ᵇ fiberProduct F F),
      RepresentableWith P (relativeDiagonalBaseChangeSnd F g).diag) :
    RepresentableWith P F.diag := by
  refine ⟨?_, ?_⟩
  · intro T g
    let L := relativeDiagonalTargetLift F g
    obtain ⟨A, hA, E, hE⟩ := (h T g).1 T L
    let K := relativeDiagonalFiberToBaseChange F g
    let _ : K.toFunctor.IsEquivalence :=
      isEquivalence_relativeDiagonalFiberToBaseChange F g
    obtain ⟨J, ⟨α⟩, ⟨β⟩⟩ :=
      CategoryTheory.BasedFunctor.exists_inverse_of_toFunctor K
    have hJ : J.toFunctor.IsEquivalence :=
      Functor.IsEquivalence.mk' K.toFunctor
        ((BasedNatTrans.forgetful _ _).mapIso β).symm
        ((BasedNatTrans.forgetful _ _).mapIso α)
    exact ⟨A, hA, E.comp J,
      Functor.isEquivalence_trans E.toFunctor J.toFunctor⟩
  · intro T g A hA E hE U q hq
    let L := relativeDiagonalTargetLift F g
    let K := relativeDiagonalFiberToBaseChange F g
    have hK : K.toFunctor.IsEquivalence :=
      isEquivalence_relativeDiagonalFiberToBaseChange F g
    have hP := (h T g).2 T L A hA (E.comp K)
      (Functor.isEquivalence_trans E.toFunctor K.toFunctor) U q hq
    have hsnd : K.comp (BasedCategory.fiberProductSnd
        (relativeDiagonalBaseChangeSnd F g).diag L) =
        BasedCategory.fiberProductSnd F.diag g := by
      dsimp only [K, L]
      exact relativeDiagonalFiberToBaseChange_comp_snd F g
    rw [CategoryTheory.BasedFunctor.comp_assoc] at hP
    rw [hsnd] at hP
    exact hP

end AlgebraicGeometry.BasedFunctor
