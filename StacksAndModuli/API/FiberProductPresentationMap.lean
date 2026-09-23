module

public import StacksAndModuli.API.FiberProductEquivalence
public import StacksAndModuli.API.MagicSquareInverse
public import StacksAndModuli.API.OverBasedProducts

/-!
# The canonical map induced by two presentation morphisms

Given morphisms `P : U ⟶ X` and `Q : V ⟶ Y'` and a cospan
`X ⟶ Y ⟵ Y'`, this file constructs the canonical morphism

`U ×_Y V ⟶ X ×_Y Y'`.

The construction is stated for arbitrary based categories.  In applications, `U`
and `V` are the prestacks associated to schemes and `P`, `Q` are presentations.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Limits

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

namespace CategoryTheory.BasedCategory

variable {S : Type u₁} [Category.{v₁} S]
  {X : BasedCategory.{v₂, u₂} S} {Y : BasedCategory.{v₃, u₃} S}
  {Y' : BasedCategory.{v₄, u₄} S} {U : BasedCategory.{v₅, u₅} S}
  {V : BasedCategory.{v₆, u₆} S}

/-- The canonical map from the fiber product of two morphisms after precomposition
to the original fiber product.  For scheme presentations `P` and `Q`, this is the
map `U ×_Y V ⟶ X ×_Y Y'` induced by the two presentation maps. -/
def fiberProductPresentationMap (F : X ⥤ᵇ Y) (G : Y' ⥤ᵇ Y)
    (P : U ⥤ᵇ X) (Q : V ⥤ᵇ Y') :
    fiberProduct (P.comp F) (Q.comp G) ⥤ᵇ fiberProduct F G :=
  fiberProductLift
    ((fiberProductFst (P.comp F) (Q.comp G)).comp P)
    ((fiberProductSnd (P.comp F) (Q.comp G)).comp Q)
    (fiberProductIsoComm (P.comp F) (Q.comp G))

/-- The canonical presentation map followed by the first projection is the first
source projection followed by `P`. -/
@[simp]
lemma fiberProductPresentationMap_comp_fiberProductFst
    (F : X ⥤ᵇ Y) (G : Y' ⥤ᵇ Y) (P : U ⥤ᵇ X) (Q : V ⥤ᵇ Y') :
    (fiberProductPresentationMap F G P Q).comp (fiberProductFst F G) =
      (fiberProductFst (P.comp F) (Q.comp G)).comp P :=
  fiberProductLift_comp_fst _ _ _

/-- The canonical presentation map followed by the second projection is the second
source projection followed by `Q`. -/
@[simp]
lemma fiberProductPresentationMap_comp_fiberProductSnd
    (F : X ⥤ᵇ Y) (G : Y' ⥤ᵇ Y) (P : U ⥤ᵇ X) (Q : V ⥤ᵇ Y') :
    (fiberProductPresentationMap F G P Q).comp (fiberProductSnd F G) =
      (fiberProductSnd (P.comp F) (Q.comp G)).comp Q :=
  fiberProductLift_comp_snd _ _ _

@[simp]
lemma fiberProductPresentationMap_obj_fst
    (F : X ⥤ᵇ Y) (G : Y' ⥤ᵇ Y) (P : U ⥤ᵇ X) (Q : V ⥤ᵇ Y')
    (x : (fiberProduct (P.comp F) (Q.comp G)).obj) :
    ((fiberProductPresentationMap F G P Q).obj x).fst = P.obj x.fst :=
  rfl

@[simp]
lemma fiberProductPresentationMap_obj_snd
    (F : X ⥤ᵇ Y) (G : Y' ⥤ᵇ Y) (P : U ⥤ᵇ X) (Q : V ⥤ᵇ Y')
    (x : (fiberProduct (P.comp F) (Q.comp G)).obj) :
    ((fiberProductPresentationMap F G P Q).obj x).snd = Q.obj x.snd :=
  rfl

@[simp]
lemma fiberProductPresentationMap_obj_iso_hom
    (F : X ⥤ᵇ Y) (G : Y' ⥤ᵇ Y) (P : U ⥤ᵇ X) (Q : V ⥤ᵇ Y')
    (x : (fiberProduct (P.comp F) (Q.comp G)).obj) :
    ((fiberProductPresentationMap F G P Q).obj x).iso.hom = x.iso.hom :=
  rfl

@[simp]
lemma fiberProductPresentationMap_obj_iso_inv
    (F : X ⥤ᵇ Y) (G : Y' ⥤ᵇ Y) (P : U ⥤ᵇ X) (Q : V ⥤ᵇ Y')
    (x : (fiberProduct (P.comp F) (Q.comp G)).obj) :
    ((fiberProductPresentationMap F G P Q).obj x).iso.inv = x.iso.inv :=
  rfl

@[simp]
lemma fiberProductPresentationMap_map_fst
    (F : X ⥤ᵇ Y) (G : Y' ⥤ᵇ Y) (P : U ⥤ᵇ X) (Q : V ⥤ᵇ Y')
    {x y : (fiberProduct (P.comp F) (Q.comp G)).obj} (f : x ⟶ y) :
    ((fiberProductPresentationMap F G P Q).map f).fst = P.map f.fst :=
  rfl

@[simp]
lemma fiberProductPresentationMap_map_snd
    (F : X ⥤ᵇ Y) (G : Y' ⥤ᵇ Y) (P : U ⥤ᵇ X) (Q : V ⥤ᵇ Y')
    {x y : (fiberProduct (P.comp F) (Q.comp G)).obj} (f : x ⟶ y) :
    ((fiberProductPresentationMap F G P Q).map f).snd = Q.map f.snd :=
  rfl

/-- The target fiber product's canonical 2-cell pulls back to the source fiber
product's canonical 2-cell. -/
@[simp]
lemma fiberProductPresentationMap_isoComm_app
    (F : X ⥤ᵇ Y) (G : Y' ⥤ᵇ Y) (P : U ⥤ᵇ X) (Q : V ⥤ᵇ Y')
    (x : (fiberProduct (P.comp F) (Q.comp G)).obj) :
    (fiberProductIsoComm F G).hom.toNatTrans.app
        ((fiberProductPresentationMap F G P Q).obj x) =
      (fiberProductIsoComm (P.comp F) (Q.comp G)).hom.toNatTrans.app x :=
  rfl

/-- The canonical presentation map can equivalently be formed by changing its left
leg and then its right leg. -/
lemma fiberProductPresentationMap_eq_leftMap_comp_rightMap
    (F : X ⥤ᵇ Y) (G : Y' ⥤ᵇ Y) (P : U ⥤ᵇ X) (Q : V ⥤ᵇ Y') :
    fiberProductPresentationMap F G P Q =
      (fiberProductLeftMap F (Q.comp G) P).comp
        (fiberProductRightMap F G Q) := by
  apply BasedFunctor.ext_of_toFunctor_eq
  exact Functor.ext (fun x ↦ rfl)

/-- The fiber of the diagonal over the product of two morphisms from representable
prestacks maps canonically to their fiber product.  The product comparison accounts
for the fact that `overBased (T ⨯ U)` represents the product of the two source
prestacks. -/
noncomputable def overBasedPairDiagonalFiberComparison
    {T U : S} [HasBinaryProduct T U]
    (A : overBased T ⥤ᵇ Y) (B : overBased U ⥤ᵇ Y) :
    fiberProduct (diag Y)
        ((overBasedProdComparison T U).comp (prodMap A B)) ⥤ᵇ
      fiberProduct A B :=
  ((fiberProductRightMap (diag Y) (prodMap A B)
      (overBasedProdComparison T U)).comp
    (fiberProductSymm (diag Y) (prodMap A B))).comp
      (prodMapDiagToFiberProduct A B)

/-- The comparison from a diagonal fiber over a pair of representable prestacks to
the corresponding fiber product is an equivalence. -/
theorem isEquivalence_overBasedPairDiagonalFiberComparison
    {T U : S} [HasBinaryProduct T U]
    (A : overBased T ⥤ᵇ Y) (B : overBased U ⥤ᵇ Y) :
    (overBasedPairDiagonalFiberComparison A B).toFunctor.IsEquivalence := by
  let E₀ := overBasedProdComparison T U
  let _ : E₀.toFunctor.IsEquivalence :=
    isEquivalence_overBasedProdComparison T U
  let E₁ := fiberProductRightMap (diag Y) (prodMap A B) E₀
  let _ : E₁.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductRightMap (diag Y) (prodMap A B) E₀
  let E₂ := fiberProductSymm (diag Y) (prodMap A B)
  let _ : E₂.toFunctor.IsEquivalence := inferInstance
  let E₃ := prodMapDiagToFiberProduct A B
  let _ : E₃.toFunctor.IsEquivalence :=
    isEquivalence_prodMapDiagToFiberProduct A B
  let _ : (E₁.comp E₂).toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans E₁.toFunctor E₂.toFunctor
  exact Functor.isEquivalence_trans (E₁.comp E₂).toFunctor E₃.toFunctor

/-- A presheaf representing the appropriate fiber of the diagonal also represents
the fiber product of the two morphisms from representable prestacks. -/
theorem IsRepresentedByPresheaf.of_overBasedPairDiagonalFiber
    {T U : S} [HasBinaryProduct T U]
    (A : overBased T ⥤ᵇ Y) (B : overBased U ⥤ᵇ Y)
    {Z : Sᵒᵖ ⥤ Type v₁}
    (hZ : (fiberProduct (diag Y)
      ((overBasedProdComparison T U).comp (prodMap A B))).IsRepresentedByPresheaf Z) :
    (fiberProduct A B).IsRepresentedByPresheaf Z := by
  obtain ⟨E, hE⟩ := hZ
  let _ : E.toFunctor.IsEquivalence := hE
  let K := overBasedPairDiagonalFiberComparison A B
  let _ : K.toFunctor.IsEquivalence :=
    isEquivalence_overBasedPairDiagonalFiberComparison A B
  exact ⟨E.comp K, Functor.isEquivalence_trans E.toFunctor K.toFunctor⟩

end CategoryTheory.BasedCategory

namespace AlgebraicGeometry

open CategoryTheory.BasedCategory

universe v u vY uY

/-- If every base change of a prestack's diagonal by a scheme is represented by an
algebraic space, then the fiber product of any two scheme-valued points is represented
by an algebraic space.  The hypothesis is the unfolded form of representability of
the diagonal, allowing this result to be used before the bundled `Representable`
predicate is available. -/
theorem exists_isAlgebraicSpace_fiberProduct_of_representableDiagonal
    {Y : BasedCategory.{vY, uY} Scheme.{u}} {T U : Scheme.{u}}
    (A : overBased T ⥤ᵇ Y) (B : overBased U ⥤ᵇ Y)
    (hΔ : ∀ (W : Scheme.{u}) (g : overBased W ⥤ᵇ prod Y Y),
      ∃ Z : Scheme.{u}ᵒᵖ ⥤ Type u, IsAlgebraicSpace Z ∧
        (fiberProduct (diag Y) g).IsRepresentedByPresheaf Z) :
    ∃ Z : Scheme.{u}ᵒᵖ ⥤ Type u, IsAlgebraicSpace Z ∧
      (fiberProduct A B).IsRepresentedByPresheaf Z := by
  let E₀ := overBasedProdComparison T U
  let H := prodMap A B
  obtain ⟨Z, hZ, hrep⟩ := hΔ (T ⨯ U) (E₀.comp H)
  exact ⟨Z, hZ, hrep.of_overBasedPairDiagonalFiber A B⟩

end AlgebraicGeometry
