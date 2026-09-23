module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Whiskering

/-!
# Whiskering of 2-isomorphisms of based categories

Mathlib has `Functor.isoWhiskerLeft`/`Functor.isoWhiskerRight` for plain functors but no
based analogue. The right one is easy — the components of the whiskered isomorphism are
already homomorphism lifts over the correct base object. The left one needs the
identification `ℬ.p(H(a)) = 𝒜.p(a)` supplied by `BasedFunctor.w_obj`.

## Main results

* `CategoryTheory.BasedCategory.isoWhiskerLeft`: left whiskering of a 2-isomorphism.
* `CategoryTheory.BasedCategory.isoWhiskerRight`: right whiskering of a 2-isomorphism.
-/

@[expose] public section

namespace CategoryTheory

open CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒜 : BasedCategory.{v₂, u₂} 𝒮}
  {ℬ : BasedCategory.{v₃, u₃} 𝒮} {𝒞 : BasedCategory.{v₄, u₄} 𝒮}

namespace BasedCategory

/-- Whiskering a 2-isomorphism of morphisms of based categories on the left with a
morphism `H`: a 2-isomorphism `e : F ≅ G` of morphisms `ℬ ⥤ᵇ 𝒞` induces a 2-isomorphism
`F ∘ H ≅ G ∘ H` of morphisms `𝒜 ⥤ᵇ 𝒞`.

The components are the components of `e` at the objects in the image of `H`; they lift the
identity of the correct base object because `H` is a morphism over `𝒮`. -/
def isoWhiskerLeft (H : 𝒜 ⥤ᵇ ℬ) {F G : ℬ ⥤ᵇ 𝒞} (e : F ≅ G) : H.comp F ≅ H.comp G :=
  BasedNatIso.mkNatIso
    (Functor.isoWhiskerLeft H.toFunctor ((BasedNatTrans.forgetful ℬ 𝒞).mapIso e))
    (fun a => (H.w_obj a) ▸ e.hom.isHomLift' (H.obj a))

/-- Whiskering a 2-isomorphism of morphisms of based categories on the right with a
morphism `H`: a 2-isomorphism `e : F ≅ G` of morphisms `𝒜 ⥤ᵇ ℬ` induces a 2-isomorphism
`F ∘ H ≅ G ∘ H` of morphisms `𝒜 ⥤ᵇ 𝒞`. -/
def isoWhiskerRight {F G : 𝒜 ⥤ᵇ ℬ} (e : F ≅ G) (H : ℬ ⥤ᵇ 𝒞) : F.comp H ≅ G.comp H :=
  BasedNatIso.mkNatIso
    (Functor.isoWhiskerRight ((BasedNatTrans.forgetful 𝒜 ℬ).mapIso e) H.toFunctor)
    (fun a => BasedFunctor.preserves_isHomLift H (𝟙 (𝒜.p.obj a)) (e.hom.toNatTrans.app a))

end BasedCategory

end CategoryTheory
