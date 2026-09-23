module

public import StacksAndModuli.«Section4.1-Definitions».«part4.1.1-representable-morphisms-and-algebraic-spaces»

/-!
# Liftings of 2-commutative squares

This module formalizes Remark 4.7.3 (`rmk:lifting`) of §4.7 (Smoothness and the
Infinitesimal Lifting Criterion) of *Stacks and Moduli*
(the section and its subsections carry no `sec:`
labels). Its definitional content precedes Theorem 4.7.1
(`thm:infinitesimal-lifting-criterion-stacks`, part 4.7.2), whose statements quantify
over the liftings introduced here.

Given a morphism of prestacks `F : 𝒳 ⥤ᵇ 𝒴` over a category `𝒮` and a morphism `g : S ⟶ T`
of `𝒮`, a 2-commutative square is a pair of morphisms `x : 𝒮/S → 𝒳`, `y : 𝒮/T → 𝒴`
together with a 2-isomorphism `F ∘ x ≅ y ∘ g`. A lifting of such a square is a morphism
`x̃ : 𝒮/T → 𝒳` with 2-isomorphisms `β : x ≅ x̃ ∘ g` and `γ : F ∘ x̃ ≅ y` satisfying the
book's triangle identity, and liftings form a category which is a groupoid whenever `𝒳` is
fibered in groupoids.

Canonical declarations:
- `CategoryTheory.BasedFunctor.LiftingSq`: 2-commutative squares over a morphism of the
  base category;
- `CategoryTheory.BasedFunctor.LiftingSq.Lifting`: liftings of a 2-commutative square,
  together with `Lifting.Hom` and the `Groupoid` instance.

The whiskering and isomorphism lemmas in this module are supporting API for those
constructions.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section RmkLifting

open CategoryTheory Functor CategoryTheory.BasedCategory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.BasedCategory

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
  {𝒴 : BasedCategory.{v₃, u₃} 𝒮} {𝒵 : BasedCategory.{v₄, u₄} 𝒮}

/-- Left-whiskering of based natural transformations preserves identities. -/
@[simp]
lemma whiskerLeft_id (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴 ⥤ᵇ 𝒵) :
    whiskerLeft F (𝟙 G) = 𝟙 (F.comp G) := by
  apply BasedNatTrans.homCategory.ext
  rfl

/-- Left-whiskering of based natural transformations preserves composition. -/
@[simp]
lemma whiskerLeft_comp (F : 𝒳 ⥤ᵇ 𝒴) {G H K : 𝒴 ⥤ᵇ 𝒵} (α : G ⟶ H) (β : H ⟶ K) :
    whiskerLeft F (α ≫ β) = whiskerLeft F α ≫ whiskerLeft F β := by
  apply BasedNatTrans.homCategory.ext
  rfl

/-- Right-whiskering of based natural transformations preserves identities. -/
@[simp]
lemma whiskerRight_id (F : 𝒳 ⥤ᵇ 𝒴) (H : 𝒴 ⥤ᵇ 𝒵) :
    whiskerRight (𝟙 F) H = 𝟙 (F.comp H) := by
  apply BasedNatTrans.homCategory.ext
  ext a
  simp
  rfl

/-- Right-whiskering of based natural transformations preserves composition. -/
@[simp]
lemma whiskerRight_comp {F G K : 𝒳 ⥤ᵇ 𝒴} (α : F ⟶ G) (β : G ⟶ K) (H : 𝒴 ⥤ᵇ 𝒵) :
    whiskerRight (α ≫ β) H = whiskerRight α H ≫ whiskerRight β H := by
  apply BasedNatTrans.homCategory.ext
  ext a
  simp

end CategoryTheory.BasedCategory

namespace CategoryTheory.BasedFunctor

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
  {𝒴 : BasedCategory.{v₃, u₃} 𝒮}

/-- Let `𝒴` be a prestack over `𝒮`. Every 2-morphism between morphisms of prestacks
`𝒳 → 𝒴` is an isomorphism. (This is
`CategoryTheory.BasedNatTrans.isIso_of_isFiberedInGroupoids` of part 3.4.3, generalized
to based categories with unrelated universe parameters.) -/
instance isIso_of_target_isFiberedInGroupoids [𝒴.p.IsFiberedInGroupoids] {F G : 𝒳 ⥤ᵇ 𝒴}
    (α : F ⟶ G) : IsIso α := by
  have h : ∀ a : 𝒳.obj, IsIso (α.toNatTrans.app a) := fun a ↦
    Functor.IsFiberedInGroupoids.isIso_of_isHomLift_id (p := 𝒴.p)
      (S := 𝒳.p.obj a) (α.toNatTrans.app a)
  have : IsIso (X := F.toFunctor) (Y := G.toFunctor) α.toNatTrans :=
    NatIso.isIso_of_isIso_app α.toNatTrans
  exact BasedNatIso.isIso_of_toNatTrans_isIso α

/-- **Remark 4.7.3** (`rmk:lifting`) (the 2-commutative square, Equation 4.7.4): let
$F \colon \cX \to \cY$ be a morphism of prestacks over a category $\cS$ and let
$g \colon S \to T$ be a morphism of $\cS$. A *2-commutative square* over $(F, g)$ consists
of morphisms of prestacks $x \colon \cS/S \to \cX$ and $y \colon \cS/T \to \cY$ together
with a 2-isomorphism $\alpha \colon F \circ x \cong y \circ g$. For $\cS = \Sch$ this is
the 2-commutative diagram whose liftings the Infinitesimal Lifting Criteria concern. -/
structure LiftingSq (F : 𝒳 ⥤ᵇ 𝒴) {S T : 𝒮} (g : S ⟶ T) where
  /-- The top morphism `x : 𝒮/S → 𝒳` of the square. -/
  x : overBased S ⥤ᵇ 𝒳
  /-- The bottom morphism `y : 𝒮/T → 𝒴` of the square. -/
  y : overBased T ⥤ᵇ 𝒴
  /-- The 2-isomorphism `α : F ∘ x ≅ y ∘ g` making the square 2-commutative. -/
  isoComm : x.comp F ≅ (overBased.map g).comp y

namespace LiftingSq

variable {F : 𝒳 ⥤ᵇ 𝒴} {S T : 𝒮} {g : S ⟶ T}

/-- **Remark 4.7.3** (`rmk:lifting`) (the definition of a lifting): let
$\sigma = (x, y, \alpha)$ be a 2-commutative square over a morphism of prestacks
$F \colon \cX \to \cY$ and a morphism $g \colon S \to T$ of the base. A *lifting* of
$\sigma$ is a triple $(\tilde{x}, \beta, \gamma)$ of a morphism
$\tilde{x} \colon \cS/T \to \cX$ and 2-isomorphisms $\beta \colon x \cong \tilde{x} \circ g$
and $\gamma \colon F \circ \tilde{x} \cong y$ such that $\alpha$ is the composite of
$F(\beta)$ and $g^*\gamma$. -/
structure Lifting (σ : LiftingSq F g) where
  /-- The lifted morphism `x̃ : 𝒮/T → 𝒳`. -/
  lift : overBased T ⥤ᵇ 𝒳
  /-- The 2-isomorphism `β : x ≅ x̃ ∘ g`. -/
  isoX : σ.x ≅ (overBased.map g).comp lift
  /-- The 2-isomorphism `γ : F ∘ x̃ ≅ y`. -/
  isoY : lift.comp F ≅ σ.y
  /-- The triangle identity: the 2-isomorphism `α` of the square is the composite of the
  whiskerings `F(β)` and `g^*γ`. -/
  w : σ.isoComm.hom =
    whiskerRight isoX.hom F ≫ whiskerLeft (overBased.map g) isoY.hom

namespace Lifting

variable {σ : LiftingSq F g}

/-- **Remark 4.7.3** (`rmk:lifting`) (morphisms of liftings): a morphism of liftings
$(\tilde{x}, \beta, \gamma) \to (\tilde{x}', \beta', \gamma')$ of a 2-commutative square
is a 2-morphism $\Theta \colon \tilde{x} \to \tilde{x}'$ such that
$\beta' = g^*\Theta \circ \beta$ and $\gamma = \gamma' \circ F(\Theta)$. When the source of
the lifted morphisms is fibered in groupoids, every such $\Theta$ is a 2-isomorphism.
(The book prints the first compatibility as $\beta = g^*\Theta \circ \beta'$, which does
not typecheck; see the `[erratum]` entry for Remark 4.7.3 in this folder's
COMMENTARY.md.) -/
@[ext]
structure Hom (l l' : σ.Lifting) where
  /-- The underlying 2-morphism `Θ : x̃ → x̃'`. -/
  hom : l.lift ⟶ l'.lift
  /-- Compatibility with the 2-isomorphisms `β`: `β' = g^*Θ ∘ β`. -/
  wX : l.isoX.hom ≫ whiskerLeft (overBased.map g) hom = l'.isoX.hom
  /-- Compatibility with the 2-isomorphisms `γ`: `γ = γ' ∘ F(Θ)`. -/
  wY : whiskerRight hom F ≫ l'.isoY.hom = l.isoY.hom

/-- The identity morphism of a lifting. -/
@[simps]
def Hom.id (l : σ.Lifting) : Hom l l where
  hom := 𝟙 l.lift
  wX := by simp only [BasedCategory.whiskerLeft_id, Category.comp_id]
  wY := by simp only [BasedCategory.whiskerRight_id, Category.id_comp]

/-- The composition of morphisms of liftings. -/
@[simps]
def Hom.comp {l l' l'' : σ.Lifting} (φ : Hom l l') (ψ : Hom l' l'') : Hom l l'' where
  hom := φ.hom ≫ ψ.hom
  wX := by rw [BasedCategory.whiskerLeft_comp, ← Category.assoc, φ.wX, ψ.wX]
  wY := by rw [BasedCategory.whiskerRight_comp, Category.assoc, ψ.wY, φ.wY]

instance instCategory : Category σ.Lifting where
  Hom := Hom
  id := Hom.id
  comp φ ψ := φ.comp ψ
  id_comp φ := by
    apply Hom.ext
    simp only [Hom.comp_hom, Hom.id_hom, Category.id_comp]
  comp_id φ := by
    apply Hom.ext
    simp only [Hom.comp_hom, Hom.id_hom, Category.comp_id]
  assoc φ ψ χ := by
    apply Hom.ext
    simp only [Hom.comp_hom, Category.assoc]

/-- The underlying 2-morphism of the identity morphism of a lifting. -/
@[simp]
lemma id_hom (l : σ.Lifting) : Hom.hom (𝟙 l) = 𝟙 l.lift :=
  rfl

/-- The underlying 2-morphism of a composition of morphisms of liftings. -/
@[simp]
lemma comp_hom {l l' l'' : σ.Lifting} (φ : l ⟶ l') (ψ : l' ⟶ l'') :
    Hom.hom (φ ≫ ψ) = φ.hom ≫ ψ.hom :=
  rfl

/-- The inverse of a morphism of liftings whose underlying 2-morphism is invertible; in
particular, when `𝒳` is fibered in groupoids, every morphism of liftings is invertible. -/
@[simps]
noncomputable def Hom.inv [𝒳.p.IsFiberedInGroupoids] {l l' : σ.Lifting} (φ : l ⟶ l') :
    l' ⟶ l where
  hom := CategoryTheory.inv φ.hom
  wX := by
    rw [← φ.wX, Category.assoc, ← BasedCategory.whiskerLeft_comp, IsIso.hom_inv_id,
      BasedCategory.whiskerLeft_id, Category.comp_id]
  wY := by
    rw [← φ.wY, ← Category.assoc, ← BasedCategory.whiskerRight_comp, IsIso.inv_hom_id,
      BasedCategory.whiskerRight_id, Category.id_comp]

instance [𝒳.p.IsFiberedInGroupoids] {l l' : σ.Lifting} (φ : l ⟶ l') : IsIso φ :=
  ⟨Hom.inv φ, by apply Hom.ext; simp, by apply Hom.ext; simp⟩

/-- **Remark 4.7.3** (`rmk:lifting`) (liftings form a groupoid): the liftings of a
2-commutative square over a morphism of prestacks $F \colon \cX \to \cY$ form a groupoid:
every morphism of liftings is invertible, since its underlying 2-morphism lies over
identities of the base and $\cX$ is fibered in groupoids. -/
noncomputable instance [𝒳.p.IsFiberedInGroupoids] : Groupoid σ.Lifting :=
  Groupoid.ofIsIso fun _ ↦ inferInstance

end Lifting

/- Further interpretation from Remark 4.7.3 via the restriction functor Ψ:
a 2-commutative square `σ` over `(F, g)` determines an object `(x, y, α)` of the fiber
product of groupoids `𝒳(S) ×_{𝒴(S)} 𝒴(T)`, and the groupoid `σ.Lifting` is equivalent to
the fiber of the induced functor `Ψ : 𝒳(T) → 𝒳(S) ×_{𝒴(S)} 𝒴(T)` over this object (via
the 2-Yoneda lemma, Lemma 3.4.21 (`lem:2-yoneda`), part 3.4.4, which translates
`overBased T ⥤ᵇ 𝒳` into `𝒳(T)`). The
Infinitesimal Lifting Criteria of part 4.7.2 say that `F` is smooth (resp. étale,
unramified, has unramified diagonal) if and only if for the squares along small
extensions the functor `Ψ` is essentially surjective (resp. an equivalence, fully
faithful, faithful); in terms of the lifting groupoid these conditions are, verbatim,
`Nonempty σ.Lifting`, existence and uniqueness of morphisms between any two liftings, and
`Subsingleton (l ⟶ l)` for every lifting `l`, which is how part 4.7.2 states them. The
functor `Ψ` itself is not introduced: Mathlib has no iso-comma category of groupoids, and
the explicit lifting groupoid is primary. -/

end LiftingSq

end CategoryTheory.BasedFunctor

end RmkLifting
