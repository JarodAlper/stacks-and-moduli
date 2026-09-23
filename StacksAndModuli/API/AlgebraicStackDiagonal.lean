module

public import StacksAndModuli.API.AlgebraicSpaceEtaleLocal
public import StacksAndModuli.API.AlgebraicStackHomSmall
public import StacksAndModuli.API.FiberProductLegIso
public import StacksAndModuli.API.FiberProductPostcomp
public import StacksAndModuli.API.MagicSquareInverse
public import StacksAndModuli.API.OverPresheafTotalPrestack
public import StacksAndModuli.API.PresheafProductComparison
public import StacksAndModuli.API.ProductReassembly
public import StacksAndModuli.API.RepresentedFiberBaseChange
public import StacksAndModuli.API.TwoYonedaReconstruction

/-!
# Isom sheaves representing fibers of an algebraic-stack diagonal

For two objects of an algebraic stack over a scheme, the totalized Isom sheaf is
pointwise small after shrinking.  Its associated prestack is the corresponding fiber
of the diagonal.  This file packages that construction independently of the book's
Representability of the Diagonal theorem.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Limits Opposite
open CategoryTheory.BasedCategory

universe w v u v₂ u₂

namespace CategoryTheory.FunctorToTypes

variable {C : Type u} [Category.{v} C]

/-- Shrinking the values of a pointwise-small sheaf of types preserves the sheaf
condition. -/
theorem isSheaf_shrink {J : GrothendieckTopology C} (F : Cᵒᵖ ⥤ Type w)
    [FunctorToTypes.Small.{v} F] (hF : Presieve.IsSheaf J F) :
    Presieve.IsSheaf J (shrink.{v} F) := by
  apply Presieve.isSheaf_of_nat_equiv (fun _ ↦ equivShrink _)
  · intro X Y f x
    simp [FunctorToTypes.shrink]
  · exact hF

end CategoryTheory.FunctorToTypes

namespace AlgebraicGeometry

/-- The universe-small presheaf obtained by totalizing the Isom sheaf of two
algebraic-stack objects and shrinking its values. -/
noncomputable def IsAlgebraicStack.smallIsomTotal
    {Xcat : BasedCategory.{v₂, u₂} Scheme.{u}} [IsAlgebraicStack Xcat]
    {T : Scheme.{u}} (a b : Xcat.p.Fiber T) : Scheme.{u}ᵒᵖ ⥤ Type u := by
  let _ : FunctorToTypes.Small.{u} (isomPresheaf a b) :=
    IsAlgebraicStack.small_isomPresheaf a b
  let _ : FunctorToTypes.Small.{u}
      (PresheafOver.total (isomPresheaf a b)) :=
    PresheafOver.small_total_of_small (isomPresheaf a b)
  exact FunctorToTypes.shrink.{u} (PresheafOver.total (isomPresheaf a b))

/-- The shrunken total Isom presheaf is an étale sheaf. -/
theorem IsAlgebraicStack.smallIsomTotal_isSheaf
    {Xcat : BasedCategory.{v₂, u₂} Scheme.{u}} [IsAlgebraicStack Xcat]
    {T : Scheme.{u}} (a b : Xcat.p.Fiber T) :
    Presieve.IsSheaf Scheme.etaleTopology
      (IsAlgebraicStack.smallIsomTotal a b) := by
  let _ : FunctorToTypes.Small.{u} (isomPresheaf a b) :=
    IsAlgebraicStack.small_isomPresheaf a b
  let _ : FunctorToTypes.Small.{u}
      (PresheafOver.total (isomPresheaf a b)) :=
    PresheafOver.small_total_of_small (isomPresheaf a b)
  apply FunctorToTypes.isSheaf_shrink
  apply PresheafOver.isSheaf_total Scheme.etaleTopology
  exact (isSheaf_iff_isSheaf_of_type _ _).mp (isomPresheaf_isSheaf a b)

/-- The canonical comparison from the prestack of the shrunken total Isom sheaf to
the corresponding base change of the diagonal. -/
noncomputable def IsAlgebraicStack.smallIsomTotalComparison
    {Xcat : BasedCategory.{v₂, u₂} Scheme.{u}} [IsAlgebraicStack Xcat]
    {T : Scheme.{u}} (a b : Xcat.p.Fiber T) :
    ofPresheaf (IsAlgebraicStack.smallIsomTotal a b) ⥤ᵇ
      BasedCategory.fiberProduct (isomPairMap a b) (diag Xcat) := by
  let _ : FunctorToTypes.Small.{u} (isomPresheaf a b) :=
    IsAlgebraicStack.small_isomPresheaf a b
  let _ : FunctorToTypes.Small.{u}
      (PresheafOver.total (isomPresheaf a b)) :=
    PresheafOver.small_total_of_small (isomPresheaf a b)
  exact (PresheafOver.smallTotalPrestackComparison
    (isomPresheaf a b)).comp (isomPrestackComparison a b)

/-- The shrunken total Isom presheaf represents the diagonal fiber over the pair
classified by two objects of an algebraic stack. -/
theorem IsAlgebraicStack.isRepresentedBy_smallIsomTotal
    {Xcat : BasedCategory.{v₂, u₂} Scheme.{u}} [IsAlgebraicStack Xcat]
    {T : Scheme.{u}} (a b : Xcat.p.Fiber T) :
    (BasedCategory.fiberProduct (isomPairMap a b) (diag Xcat)).IsRepresentedByPresheaf
      (IsAlgebraicStack.smallIsomTotal a b) := by
  refine ⟨IsAlgebraicStack.smallIsomTotalComparison a b, ?_⟩
  let _ : FunctorToTypes.Small.{u} (isomPresheaf a b) :=
    IsAlgebraicStack.small_isomPresheaf a b
  let _ : FunctorToTypes.Small.{u}
      (PresheafOver.total (isomPresheaf a b)) :=
    PresheafOver.small_total_of_small (isomPresheaf a b)
  let _ : (PresheafOver.smallTotalPrestackComparison
      (isomPresheaf a b)).toFunctor.IsEquivalence :=
    PresheafOver.isEquivalence_smallTotalPrestackComparison (isomPresheaf a b)
  let _ : (isomPrestackComparison a b).toFunctor.IsEquivalence :=
    isEquivalence_isomPrestackComparison a b
  exact Functor.isEquivalence_trans
    (PresheafOver.smallTotalPrestackComparison (isomPresheaf a b)).toFunctor
    (isomPrestackComparison a b).toFunctor

/-- The canonical pair built from the two values of a morphism into a product is
isomorphic to the original morphism. -/
noncomputable def IsAlgebraicStack.isomPairMapIso
    {Xcat : BasedCategory.{v₂, u₂} Scheme.{u}} [IsAlgebraicStack Xcat]
    {T : Scheme.{u}} (g : overBased T ⥤ᵇ prod Xcat Xcat) :
    isomPairMap
        ((twoYonedaEval (𝒳 := Xcat) T).obj
          (g.comp (fiberProductFst Xcat.toBase Xcat.toBase)))
        ((twoYonedaEval (𝒳 := Xcat) T).obj
          (g.comp (fiberProductSnd Xcat.toBase Xcat.toBase))) ≅ g :=
  prodLiftIso
      (twoYonedaPullbackEvalIso
        (g.comp (fiberProductFst Xcat.toBase Xcat.toBase)))
      (twoYonedaPullbackEvalIso
        (g.comp (fiberProductSnd Xcat.toBase Xcat.toBase))) ≪≫
    prodLiftProjectionsIso g

/-- Every base change of the diagonal is represented by the shrunken total Isom
presheaf of the two objects classified by the given map into the product. -/
theorem IsAlgebraicStack.isRepresentedBy_smallIsomTotal_of_map
    {Xcat : BasedCategory.{v₂, u₂} Scheme.{u}} [IsAlgebraicStack Xcat]
    {T : Scheme.{u}} (g : overBased T ⥤ᵇ prod Xcat Xcat) :
    let a := (twoYonedaEval (𝒳 := Xcat) T).obj
      (g.comp (fiberProductFst Xcat.toBase Xcat.toBase))
    let b := (twoYonedaEval (𝒳 := Xcat) T).obj
      (g.comp (fiberProductSnd Xcat.toBase Xcat.toBase))
    (BasedCategory.fiberProduct g (diag Xcat)).IsRepresentedByPresheaf
      (IsAlgebraicStack.smallIsomTotal a b) := by
  dsimp only
  let a := (twoYonedaEval (𝒳 := Xcat) T).obj
    (g.comp (fiberProductFst Xcat.toBase Xcat.toBase))
  let b := (twoYonedaEval (𝒳 := Xcat) T).obj
    (g.comp (fiberProductSnd Xcat.toBase Xcat.toBase))
  obtain ⟨E, hE⟩ := IsAlgebraicStack.isRepresentedBy_smallIsomTotal a b
  let L := fiberProductMapLeftIso (IsAlgebraicStack.isomPairMapIso g) (diag Xcat)
  refine ⟨E.comp L, ?_⟩
  let _ : E.toFunctor.IsEquivalence := hE
  let _ : L.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductMapLeftIso
      (IsAlgebraicStack.isomPairMapIso g) (diag Xcat)
  exact Functor.isEquivalence_trans E.toFunctor L.toFunctor

/-- A pair of lifts to a smooth presentation gives an algebraic-space
representation of the corresponding diagonal fiber. -/
theorem BasedFunctor.RepresentableWith.exists_pair_diagonal_representation
    {Xcat : BasedCategory.{v₂, u₂} Scheme.{u}}
    [Xcat.p.IsFiberedInGroupoids] {U S : Scheme.{u}}
    {P : BasedFunctor (overBased U) Xcat}
    (hP : BasedFunctor.RepresentableWith
      (@_root_.AlgebraicGeometry.Surjective ⊓
        @_root_.AlgebraicGeometry.Smooth : MorphismProperty Scheme.{u}) P)
    (liftA liftB : BasedFunctor (overBased S) (overBased U)) :
    ∃ A : Functor Scheme.{u}ᵒᵖ (Type u), IsAlgebraicSpace A ∧
      (BasedCategory.fiberProduct
        ((prodLift liftA liftB).comp (prodMap P P))
        (diag Xcat)).IsRepresentedByPresheaf A := by
  obtain ⟨R, hR, ER, hER⟩ := hP.representable U P
  let _ : IsAlgebraicSpace R := hR
  let _ : ER.toFunctor.IsEquivalence := hER
  let _ : (fiberProductToProdMapDiag P P).toFunctor.IsEquivalence :=
    isEquivalence_fiberProductToProdMapDiag P P
  let E₀ := ER.comp (fiberProductToProdMapDiag P P)
  let _ : E₀.toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans ER.toFunctor
      (fiberProductToProdMapDiag P P).toFunctor
  let Eprod := (ofPresheafYonedaToOverBased (U ⨯ U)).comp
    (overBasedProdComparison U U)
  let _ : (overBasedProdComparison U U).toFunctor.IsEquivalence :=
    isEquivalence_overBasedProdComparison U U
  let _ : Eprod.toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans
      (ofPresheafYonedaToOverBased (U ⨯ U)).toFunctor
      (overBasedProdComparison U U).toFunctor
  let HR := E₀.comp (fiberProductFst (prodMap P P) (diag Xcat))
  let HS := (ofPresheafYonedaToOverBased S).comp (prodLift liftA liftB)
  let ρ := ofPresheaf.comparison Eprod HR
  let σ := ofPresheaf.comparison Eprod HS
  let A := Limits.pullback ρ σ
  let hA : IsAlgebraicSpace A := IsAlgebraicSpace.pullback ρ σ
  let L₀ := ofPresheafMapPullbackLift (φ := ρ) (ψ := σ)
  let _ : L₀.toFunctor.IsEquivalence :=
    isEquivalence_ofPresheafMapPullbackLift
  let L₁ := fiberProductPostcomp (ofPresheaf.map ρ)
    (ofPresheaf.map σ) Eprod
  let _ : L₁.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductPostcomp
      (ofPresheaf.map ρ) (ofPresheaf.map σ) Eprod
  let ηR := ofPresheaf.comparisonMapIso Eprod HR
  let L₂ := fiberProductMapLeftIso ηR ((ofPresheaf.map σ).comp Eprod)
  let _ : L₂.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductMapLeftIso ηR
      ((ofPresheaf.map σ).comp Eprod)
  let ηS := ofPresheaf.comparisonMapIso Eprod HS
  let L₃ := fiberProductMapRightIso HR ηS
  let _ : L₃.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductMapRightIso HR ηS
  let L₄ := fiberProductRightMap HR (prodLift liftA liftB)
    (ofPresheafYonedaToOverBased S)
  let _ : L₄.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductRightMap HR (prodLift liftA liftB)
      (ofPresheafYonedaToOverBased S)
  let L₅ := fiberProductSymm HR (prodLift liftA liftB)
  let L₆ := fiberProductRightMap (prodLift liftA liftB)
    (fiberProductFst (prodMap P P) (diag Xcat)) E₀
  let _ : L₆.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductRightMap (prodLift liftA liftB)
      (fiberProductFst (prodMap P P) (diag Xcat)) E₀
  let L₇ := pasteFwd (prodLift liftA liftB) (prodMap P P) (diag Xcat)
  let K := ((((((L₀.comp L₁).comp L₂).comp L₃).comp L₄).comp
    L₅).comp L₆).comp L₇
  refine ⟨A, hA, K, ?_⟩
  let _ : (L₀.comp L₁).toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans L₀.toFunctor L₁.toFunctor
  let _ : ((L₀.comp L₁).comp L₂).toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans (L₀.comp L₁).toFunctor L₂.toFunctor
  let _ : (((L₀.comp L₁).comp L₂).comp L₃).toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans ((L₀.comp L₁).comp L₂).toFunctor
      L₃.toFunctor
  let _ : ((((L₀.comp L₁).comp L₂).comp L₃).comp
      L₄).toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans
      (((L₀.comp L₁).comp L₂).comp L₃).toFunctor L₄.toFunctor
  let _ : (((((L₀.comp L₁).comp L₂).comp L₃).comp L₄).comp
      L₅).toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans
      ((((L₀.comp L₁).comp L₂).comp L₃).comp L₄).toFunctor
      L₅.toFunctor
  let _ : ((((((L₀.comp L₁).comp L₂).comp L₃).comp L₄).comp
      L₅).comp L₆).toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans
      (((((L₀.comp L₁).comp L₂).comp L₃).comp L₄).comp
        L₅).toFunctor L₆.toFunctor
  exact Functor.isEquivalence_trans
    ((((((L₀.comp L₁).comp L₂).comp L₃).comp L₄).comp
      L₅).comp L₆).toFunctor L₇.toFunctor

/-- The shrunken total Isom sheaf of two objects of an algebraic stack is an
algebraic space. -/
theorem IsAlgebraicStack.smallIsomTotal_isAlgebraicSpace
    {Xcat : BasedCategory.{v₂, u₂} Scheme.{u}} [IsAlgebraicStack Xcat]
    {T : Scheme.{u}} (a b : Xcat.p.Fiber T) :
    IsAlgebraicSpace (IsAlgebraicStack.smallIsomTotal a b) := by
  let K := IsAlgebraicStack.smallIsomTotal a b
  obtain ⟨E, hE⟩ := IsAlgebraicStack.isRepresentedBy_smallIsomTotal a b
  let _ : E.toFunctor.IsEquivalence := hE
  let π := representedFiberBaseMap E
  obtain ⟨U, P, hP⟩ := IsAlgebraicStack.exists_presentation (𝒳 := Xcat)
  obtain ⟨S, p, hpEtale, hpSurjective, liftA, liftB, ⟨eA⟩, ⟨eB⟩⟩ :=
    hP.exists_etale_surjective_pair_lift
      (twoYonedaPullback T a) (twoYonedaPullback T b)
  let _ : Etale p := hpEtale
  let _ : Surjective p := hpSurjective
  let pairLift := prodLift liftA liftB
  let pairIso : pairLift.comp (prodMap P P) ≅
      (overBased.map p).comp (isomPairMap a b) := by
    change (prodLift liftA liftB).comp (prodMap P P) ≅
      (overBased.map p).comp
        (prodLift (twoYonedaPullback T a) (twoYonedaPullback T b))
    rw [prodLift_comp_prodMap, comp_prodLift]
    exact prodLiftIso eA eB
  obtain ⟨A, hA, EA, hEA⟩ :=
    hP.exists_pair_diagonal_representation liftA liftB
  let _ : IsAlgebraicSpace A := hA
  let _ : EA.toFunctor.IsEquivalence := hEA
  let L := fiberProductMapLeftIso pairIso (diag Xcat)
  let _ : L.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductMapLeftIso pairIso (diag Xcat)
  let EA' := EA.comp L
  let _ : EA'.toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans EA.toFunctor L.toFunctor
  obtain ⟨EB, hEB⟩ :=
    isRepresentedByPresheaf_fiber_baseChange E p
  let _ : EB.toFunctor.IsEquivalence := hEB
  let B := Limits.pullback π (yoneda.map p)
  let e : A ≅ B := ofPresheaf.comparisonIso EB EA'
  let _ : IsAlgebraicSpace B := IsAlgebraicSpace.of_iso e
  exact IsAlgebraicSpace.of_etale_surjective_base_change
    (IsAlgebraicStack.smallIsomTotal_isSheaf a b) π p

/-- The diagonal of an algebraic stack is representable.  This is the API form of
the Representability of the Diagonal, proved from a smooth presentation. -/
theorem IsAlgebraicStack.representable_diag_of_presentation
    (Xcat : BasedCategory.{v₂, u₂} Scheme.{u}) [IsAlgebraicStack Xcat] :
    BasedFunctor.Representable (diag Xcat) := by
  intro T g
  let a := (twoYonedaEval (𝒳 := Xcat) T).obj
    (g.comp (fiberProductFst Xcat.toBase Xcat.toBase))
  let b := (twoYonedaEval (𝒳 := Xcat) T).obj
    (g.comp (fiberProductSnd Xcat.toBase Xcat.toBase))
  let K := IsAlgebraicStack.smallIsomTotal a b
  let hK : IsAlgebraicSpace K :=
    IsAlgebraicStack.smallIsomTotal_isAlgebraicSpace a b
  have hRep := IsAlgebraicStack.isRepresentedBy_smallIsomTotal_of_map g
  dsimp only at hRep
  obtain ⟨E, hE⟩ := hRep
  let _ : E.toFunctor.IsEquivalence := hE
  let L := fiberProductSymm g (diag Xcat)
  exact ⟨K, hK, E.comp L,
    Functor.isEquivalence_trans E.toFunctor L.toFunctor⟩

end AlgebraicGeometry
