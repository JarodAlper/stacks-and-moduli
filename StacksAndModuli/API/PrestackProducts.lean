module

public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.5-fiber-products-of-prestacks»
public import StacksAndModuli.API.BasedFunctorWhiskering

/-!
# Products and diagonals of based categories

Supporting API for products, diagonals, and the magic-square comparison of based
categories. These constructions first occur in §3.4 of *Stacks and Moduli* and are
reused by the representability theory of §4.2.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ u₁ u₂ u₃ u₄ u₅ u₆ u₇

namespace CategoryTheory.BasedCategory

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]

/-- Left-whiskering of a 2-isomorphism of based functors. -/
def whiskerLeftIso {𝒵 : BasedCategory.{v₄, u₄} 𝒮} {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
    {𝒴 : BasedCategory.{v₃, u₃} 𝒮} (H : 𝒵 ⥤ᵇ 𝒳) {F G : 𝒳 ⥤ᵇ 𝒴} (η : F ≅ G) :
    H.comp F ≅ H.comp G :=
  BasedNatIso.mkNatIso
    (Functor.isoWhiskerLeft H.toFunctor ((BasedNatTrans.forgetful 𝒳 𝒴).mapIso η))
    (fun a ↦ η.hom.isHomLift (H.w_obj a))

/-- Right-whiskering of a 2-isomorphism of based functors. -/
def whiskerRightIso {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    {𝒵 : BasedCategory.{v₄, u₄} 𝒮} {F G : 𝒳 ⥤ᵇ 𝒴} (η : F ≅ G) (H : 𝒴 ⥤ᵇ 𝒵) :
    F.comp H ≅ G.comp H :=
  BasedNatIso.mkNatIso
    (Functor.isoWhiskerRight ((BasedNatTrans.forgetful 𝒳 𝒴).mapIso η) H.toFunctor)
    (fun a ↦ by
      dsimp
      haveI : IsHomLift 𝒴.p (𝟙 (𝒳.p.obj a))
          (((BasedNatTrans.forgetful 𝒳 𝒴).map η.hom).app a) := η.hom.isHomLift' a
      exact BasedFunctor.preserves_isHomLift H _ _)

variable (𝒮) in
/-- The base category regarded as a based category over itself. -/
abbrev base : BasedCategory 𝒮 :=
  ofFunctor (𝟭 𝒮)

/-- The projection of a based category, regarded as a based functor to the base. -/
@[simps]
def toBase (𝒳 : BasedCategory.{v₂, u₂} 𝒮) : 𝒳 ⥤ᵇ base 𝒮 where
  toFunctor := 𝒳.p
  w := Functor.comp_id 𝒳.p

/-- Every based functor commutes with the projections to the base. -/
@[simp]
lemma _root_.CategoryTheory.BasedFunctor.comp_toBase {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
    {𝒴 : BasedCategory.{v₃, u₃} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) : F.comp 𝒴.toBase = 𝒳.toBase :=
  BasedFunctor.ext_of_toFunctor_eq F.w

/-- A morphism of the based base category over an identity is the corresponding
`eqToHom`. -/
lemma base_hom_eq_eqToHom {S : 𝒮} {a b : (base 𝒮).obj} (φ : a ⟶ b)
    [IsHomLift (base 𝒮).p (𝟙 S) φ] (h : a = b) : φ = eqToHom h := by
  have hfac := IsHomLift.fac' (base 𝒮).p (𝟙 S) φ
  rw [show (base 𝒮).p.map φ = φ from rfl] at hfac
  rw [hfac]
  simp

/-- Parallel morphisms in a fiber of the based base category are equal. -/
lemma base_hom_ext {S T : 𝒮} {a b : (base 𝒮).obj} (φ ψ : a ⟶ b)
    [IsHomLift (base 𝒮).p (𝟙 S) φ] [IsHomLift (base 𝒮).p (𝟙 T) ψ] : φ = ψ := by
  have h : a = b := (IsHomLift.domain_eq (base 𝒮).p (𝟙 S) φ).trans
    (IsHomLift.codomain_eq (base 𝒮).p (𝟙 S) φ).symm
  rw [base_hom_eq_eqToHom (S := S) φ h, base_hom_eq_eqToHom (S := T) ψ h]

/-- Two parallel arrows of the based base category lifting the same arrow are equal. -/
lemma base_hom_ext_of_lift {R S : 𝒮} {a b : (base 𝒮).obj} (f : R ⟶ S)
    (φ ψ : a ⟶ b) [IsHomLift (base 𝒮).p f φ] [IsHomLift (base 𝒮).p f ψ] : φ = ψ := by
  have hφ := IsHomLift.fac' (base 𝒮).p f φ
  have hψ := IsHomLift.fac' (base 𝒮).p f ψ
  change φ = _ at hφ
  change ψ = _ at hψ
  exact hφ.trans hψ.symm

/-- Composites of vertical morphisms in the based base category are vertical. -/
lemma base_isHomLift_comp {S T : 𝒮} {a b c : (base 𝒮).obj} (φ : a ⟶ b) (ψ : b ⟶ c)
    [IsHomLift (base 𝒮).p (𝟙 S) φ] [IsHomLift (base 𝒮).p (𝟙 T) ψ] :
    IsHomLift (base 𝒮).p (𝟙 S) (φ ≫ ψ) := by
  have h : S = T := ((IsHomLift.codomain_eq (base 𝒮).p (𝟙 S) φ).symm.trans
    (IsHomLift.domain_eq (base 𝒮).p (𝟙 T) ψ))
  subst h
  infer_instance

instance {𝒯 : BasedCategory.{v₂, u₂} 𝒮} (F G : 𝒯 ⥤ᵇ base 𝒮) : Subsingleton (F ⟶ G) := by
  constructor
  intro α β
  ext a
  exact base_hom_ext (S := 𝒯.p.obj a) (T := 𝒯.p.obj a) _ _

instance {𝒯 : BasedCategory.{v₂, u₂} 𝒮} (F G : 𝒯 ⥤ᵇ base 𝒮) : Subsingleton (F ≅ G) :=
  ⟨fun _ _ ↦ Iso.ext (Subsingleton.elim _ _)⟩

/-- The product of two based categories over their common base. -/
abbrev prod (𝒳 : BasedCategory.{v₂, u₂} 𝒮) (𝒴 : BasedCategory.{v₃, u₃} 𝒮) :
    BasedCategory 𝒮 :=
  fiberProduct 𝒳.toBase 𝒴.toBase

/-- The identity functor is fibered in groupoids. -/
instance id_isFiberedInGroupoids : (𝟭 𝒮).IsFiberedInGroupoids where
  exists_isHomLift {a} {R} f := ⟨R, f, IsHomLift.of_fac' (𝟭 𝒮) f f rfl rfl (by simp)⟩
  isStronglyCartesian {a b} φ := by
    refine ⟨fun {a'} g φ' => ⟨g, ⟨IsHomLift.of_fac' (𝟭 𝒮) g g rfl rfl (by simp), ?_⟩, ?_⟩⟩
    · have h := IsHomLift.fac' (𝟭 𝒮) (g ≫ (𝟭 𝒮).map φ) φ'
      simpa using h.symm
    · rintro χ ⟨hχ, hχ'⟩
      haveI := hχ
      have h := IsHomLift.fac' (𝟭 𝒮) g χ
      simpa using h

/-- The base category, regarded as a based category over itself, is fibered in
groupoids. -/
instance base_isFiberedInGroupoids : (base 𝒮).p.IsFiberedInGroupoids :=
  inferInstanceAs (𝟭 𝒮).IsFiberedInGroupoids

/-- A product of based categories fibered in groupoids is fibered in groupoids. -/
instance prod_isFiberedInGroupoids (𝒳 : BasedCategory.{v₂, u₂} 𝒮)
    (𝒴 : BasedCategory.{v₃, u₃} 𝒮) [𝒳.p.IsFiberedInGroupoids] [𝒴.p.IsFiberedInGroupoids] :
    (prod 𝒳 𝒴).p.IsFiberedInGroupoids :=
  inferInstanceAs (fiberProduct 𝒳.toBase 𝒴.toBase).p.IsFiberedInGroupoids

/-- The morphism to a product induced by a pair of based functors. -/
abbrev prodLift {𝒯 : BasedCategory.{v₄, u₄} 𝒮} {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
    {𝒴 : BasedCategory.{v₃, u₃} 𝒮} (a : 𝒯 ⥤ᵇ 𝒳) (b : 𝒯 ⥤ᵇ 𝒴) : 𝒯 ⥤ᵇ prod 𝒳 𝒴 :=
  fiberProductLift a b
    (eqToIso (by rw [BasedFunctor.comp_toBase, BasedFunctor.comp_toBase]))

/-- Precomposition commutes with the universal lift into a fiber product. -/
lemma comp_fiberProductLift {𝒯 : BasedCategory.{v₄, u₄} 𝒮}
    {𝒯' : BasedCategory.{v₅, u₅} 𝒮} {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
    {𝒴 : BasedCategory.{v₃, u₃} 𝒮} {𝒴' : BasedCategory.{v₆, u₆} 𝒮}
    {F : 𝒳 ⥤ᵇ 𝒴} {G : 𝒴' ⥤ᵇ 𝒴} (h : 𝒯' ⥤ᵇ 𝒯) (q₁ : 𝒯 ⥤ᵇ 𝒳)
    (q₂ : 𝒯 ⥤ᵇ 𝒴') (τ : q₁.comp F ≅ q₂.comp G) :
    h.comp (fiberProductLift q₁ q₂ τ) =
      fiberProductLift (h.comp q₁) (h.comp q₂) (whiskerLeftIso h τ) :=
  rfl

@[simp]
lemma fiberProductLift_obj_fst {𝒯 : BasedCategory.{v₄, u₄} 𝒮}
    {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    {𝒴' : BasedCategory.{v₆, u₆} 𝒮} {F : 𝒳 ⥤ᵇ 𝒴} {G : 𝒴' ⥤ᵇ 𝒴}
    (q₁ : 𝒯 ⥤ᵇ 𝒳) (q₂ : 𝒯 ⥤ᵇ 𝒴') (τ : q₁.comp F ≅ q₂.comp G) (t : 𝒯.obj) :
    ((fiberProductLift q₁ q₂ τ).obj t).fst = q₁.obj t :=
  rfl

@[simp]
lemma fiberProductLift_obj_snd {𝒯 : BasedCategory.{v₄, u₄} 𝒮}
    {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    {𝒴' : BasedCategory.{v₆, u₆} 𝒮} {F : 𝒳 ⥤ᵇ 𝒴} {G : 𝒴' ⥤ᵇ 𝒴}
    (q₁ : 𝒯 ⥤ᵇ 𝒳) (q₂ : 𝒯 ⥤ᵇ 𝒴') (τ : q₁.comp F ≅ q₂.comp G) (t : 𝒯.obj) :
    ((fiberProductLift q₁ q₂ τ).obj t).snd = q₂.obj t :=
  rfl

@[simp]
lemma fiberProductLift_map_fst {𝒯 : BasedCategory.{v₄, u₄} 𝒮}
    {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    {𝒴' : BasedCategory.{v₆, u₆} 𝒮} {F : 𝒳 ⥤ᵇ 𝒴} {G : 𝒴' ⥤ᵇ 𝒴}
    (q₁ : 𝒯 ⥤ᵇ 𝒳) (q₂ : 𝒯 ⥤ᵇ 𝒴') (τ : q₁.comp F ≅ q₂.comp G)
    {t t' : 𝒯.obj} (φ : t ⟶ t') :
    ((fiberProductLift q₁ q₂ τ).map φ).fst = q₁.map φ :=
  rfl

@[simp]
lemma fiberProductLift_map_snd {𝒯 : BasedCategory.{v₄, u₄} 𝒮}
    {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    {𝒴' : BasedCategory.{v₆, u₆} 𝒮} {F : 𝒳 ⥤ᵇ 𝒴} {G : 𝒴' ⥤ᵇ 𝒴}
    (q₁ : 𝒯 ⥤ᵇ 𝒳) (q₂ : 𝒯 ⥤ᵇ 𝒴') (τ : q₁.comp F ≅ q₂.comp G)
    {t t' : 𝒯.obj} (φ : t ⟶ t') :
    ((fiberProductLift q₁ q₂ τ).map φ).snd = q₂.map φ :=
  rfl

/-- Precomposition commutes with the lift into a product. -/
@[simp]
lemma comp_prodLift {𝒯 : BasedCategory.{v₄, u₄} 𝒮}
    {𝒯' : BasedCategory.{v₅, u₅} 𝒮} {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
    {𝒴 : BasedCategory.{v₃, u₃} 𝒮} (h : 𝒯' ⥤ᵇ 𝒯) (a : 𝒯 ⥤ᵇ 𝒳)
    (b : 𝒯 ⥤ᵇ 𝒴) :
    h.comp (prodLift a b) = prodLift (h.comp a) (h.comp b) := by
  rw [prodLift, comp_fiberProductLift]
  exact congrArg (fiberProductLift (h.comp a) (h.comp b)) (Subsingleton.elim _ _)

/-- The product of two based functors. -/
abbrev prodMap {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    {𝒳' : BasedCategory.{v₄, u₄} 𝒮} {𝒴' : BasedCategory.{v₅, u₅} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴)
    (F' : 𝒳' ⥤ᵇ 𝒴') : prod 𝒳 𝒳' ⥤ᵇ prod 𝒴 𝒴' :=
  prodLift ((fiberProductFst 𝒳.toBase 𝒳'.toBase).comp F)
    ((fiberProductSnd 𝒳.toBase 𝒳'.toBase).comp F')

@[simp]
lemma prodMap_map_fst {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
    {𝒴 : BasedCategory.{v₃, u₃} 𝒮} {𝒳' : BasedCategory.{v₄, u₄} 𝒮}
    {𝒴' : BasedCategory.{v₅, u₅} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) (F' : 𝒳' ⥤ᵇ 𝒴')
    {x y : (prod 𝒳 𝒳').obj} (q : x ⟶ y) :
    ((prodMap F F').map q).fst = F.map q.fst :=
  rfl

@[simp]
lemma prodMap_map_snd {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
    {𝒴 : BasedCategory.{v₃, u₃} 𝒮} {𝒳' : BasedCategory.{v₄, u₄} 𝒮}
    {𝒴' : BasedCategory.{v₅, u₅} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) (F' : 𝒳' ⥤ᵇ 𝒴')
    {x y : (prod 𝒳 𝒳').obj} (q : x ⟶ y) :
    ((prodMap F F').map q).snd = F'.map q.snd :=
  rfl

/-- Compatibility of product lifts with products of based functors. -/
@[simp]
lemma prodLift_comp_prodMap {𝒯 : BasedCategory.{v₆, u₆} 𝒮}
    {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    {𝒳' : BasedCategory.{v₄, u₄} 𝒮} {𝒴' : BasedCategory.{v₅, u₅} 𝒮}
    (a : 𝒯 ⥤ᵇ 𝒳) (b : 𝒯 ⥤ᵇ 𝒳') (F : 𝒳 ⥤ᵇ 𝒴) (F' : 𝒳' ⥤ᵇ 𝒴') :
    (prodLift a b).comp (prodMap F F') = prodLift (a.comp F) (b.comp F') := by
  rw [prodMap, comp_prodLift, ← BasedFunctor.comp_assoc, ← BasedFunctor.comp_assoc,
    fiberProductLift_comp_fst, fiberProductLift_comp_snd]

/-- The diagonal of a based category. -/
abbrev diag (𝒳 : BasedCategory.{v₂, u₂} 𝒮) : 𝒳 ⥤ᵇ prod 𝒳 𝒳 :=
  prodLift (BasedFunctor.id 𝒳) (BasedFunctor.id 𝒳)

@[simp]
lemma diag_map_fst (𝒳 : BasedCategory.{v₂, u₂} 𝒮) {x y : 𝒳.obj} (q : x ⟶ y) :
    ((diag 𝒳).map q).fst = q :=
  rfl

@[simp]
lemma diag_map_snd (𝒳 : BasedCategory.{v₂, u₂} 𝒮) {x y : 𝒳.obj} (q : x ⟶ y) :
    ((diag 𝒳).map q).snd = q :=
  rfl

/-- Composing with a diagonal gives the pair `(F,F)`. -/
@[simp]
lemma comp_diag {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    (F : 𝒳 ⥤ᵇ 𝒴) : F.comp (diag 𝒴) = prodLift F F := by
  rw [diag, comp_prodLift, BasedFunctor.comp_id]

/-- Naturality of the diagonal. -/
@[simp]
lemma diag_comp_prodMap {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    (F : 𝒳 ⥤ᵇ 𝒴) : (diag 𝒳).comp (prodMap F F) = F.comp (diag 𝒴) := by
  rw [diag, prodLift_comp_prodMap, BasedFunctor.id_comp, comp_diag]

/-- The relative diagonal of a based functor. -/
abbrev _root_.CategoryTheory.BasedFunctor.diag {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
    {𝒴 : BasedCategory.{v₃, u₃} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) : 𝒳 ⥤ᵇ fiberProduct F F :=
  fiberProductLift (BasedFunctor.id 𝒳) (BasedFunctor.id 𝒳)
    (Iso.refl ((BasedFunctor.id 𝒳).comp F))

/-- Construct an isomorphism in a fiber product from compatible component isomorphisms. -/
def FiberProductObj.isoMk {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
    {𝒴 : BasedCategory.{v₃, u₃} 𝒮} {𝒴' : BasedCategory.{v₄, u₄} 𝒮}
    {F : 𝒳 ⥤ᵇ 𝒴} {G : 𝒴' ⥤ᵇ 𝒴} {a b : FiberProductObj F G}
    (e₁ : a.fst ≅ b.fst) (e₂ : a.snd ≅ b.snd)
    (hl : IsHomLift 𝒴'.p (𝒳.p.map e₁.hom) e₂.hom)
    (w : F.map e₁.hom ≫ b.iso.hom = a.iso.hom ≫ G.map e₂.hom) : a ≅ b :=
  fiberProductObjIsoMk e₁ e₂ hl w

@[simp]
lemma FiberProductObj.isoMk_hom_fst {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
    {𝒴 : BasedCategory.{v₃, u₃} 𝒮} {𝒴' : BasedCategory.{v₄, u₄} 𝒮}
    {F : 𝒳 ⥤ᵇ 𝒴} {G : 𝒴' ⥤ᵇ 𝒴} {a b : FiberProductObj F G}
    (e₁ : a.fst ≅ b.fst) (e₂ : a.snd ≅ b.snd)
    (hl : IsHomLift 𝒴'.p (𝒳.p.map e₁.hom) e₂.hom)
    (w : F.map e₁.hom ≫ b.iso.hom = a.iso.hom ≫ G.map e₂.hom) :
    (FiberProductObj.isoMk e₁ e₂ hl w).hom.fst = e₁.hom :=
  rfl

@[simp]
lemma FiberProductObj.isoMk_hom_snd {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
    {𝒴 : BasedCategory.{v₃, u₃} 𝒮} {𝒴' : BasedCategory.{v₄, u₄} 𝒮}
    {F : 𝒳 ⥤ᵇ 𝒴} {G : 𝒴' ⥤ᵇ 𝒴} {a b : FiberProductObj F G}
    (e₁ : a.fst ≅ b.fst) (e₂ : a.snd ≅ b.snd)
    (hl : IsHomLift 𝒴'.p (𝒳.p.map e₁.hom) e₂.hom)
    (w : F.map e₁.hom ≫ b.iso.hom = a.iso.hom ≫ G.map e₂.hom) :
    (FiberProductObj.isoMk e₁ e₂ hl w).hom.snd = e₂.hom :=
  rfl

/-- The second component of a morphism in a fiber product lifts every base arrow
lifted by the morphism itself. -/
lemma FiberProductHom.isHomLift_snd {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
    {𝒴 : BasedCategory.{v₃, u₃} 𝒮} {𝒴' : BasedCategory.{v₄, u₄} 𝒮}
    {F : 𝒳 ⥤ᵇ 𝒴} {G : 𝒴' ⥤ᵇ 𝒴} {a b : FiberProductObj F G}
    (q : a ⟶ b) {R S : 𝒮} (f : R ⟶ S)
    (h : IsHomLift (fiberProduct F G).p f q) : IsHomLift 𝒴'.p f q.snd := by
  obtain ⟨⟩ := h
  exact q.isHomLift

/-- If two morphisms lift the same base arrow, the second lifts the image of the
first under its projection functor. -/
lemma isHomLift_map_of_common_lift {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
    {𝒴 : BasedCategory.{v₃, u₃} 𝒮} {a b : 𝒳.obj} {c d : 𝒴.obj}
    {R S : 𝒮} (f : R ⟶ S) (q₁ : a ⟶ b) (q₂ : c ⟶ d)
    (h₁ : IsHomLift 𝒳.p f q₁) (h₂ : IsHomLift 𝒴.p f q₂) :
    IsHomLift 𝒴.p (𝒳.p.map q₁) q₂ := by
  obtain ⟨⟩ := h₁
  exact h₂

/-- Isomorphic pairs induce isomorphic lifts into a product. -/
def prodLiftIso {𝒯 : BasedCategory.{v₄, u₄} 𝒮} {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
    {𝒴 : BasedCategory.{v₃, u₃} 𝒮} {a a' : 𝒯 ⥤ᵇ 𝒳} {b b' : 𝒯 ⥤ᵇ 𝒴}
    (η₁ : a ≅ a') (η₂ : b ≅ b') : prodLift a b ≅ prodLift a' b' :=
  BasedNatIso.mkNatIso
    (NatIso.ofComponents
      (fun t ↦ FiberProductObj.isoMk
        (((BasedNatTrans.forgetful 𝒯 𝒳).mapIso η₁).app t)
        (((BasedNatTrans.forgetful 𝒯 𝒴).mapIso η₂).app t)
        (by
          simp only [BasedNatTrans.forgetful_obj, Iso.app_hom, Functor.mapIso_hom,
            BasedNatTrans.forgetful_map]
          rw [IsHomLift.fac' 𝒳.p (𝟙 (𝒯.p.obj t)) (η₁.hom.toNatTrans.app t)]
          infer_instance)
        (by
          simp only [Iso.app_hom, Functor.mapIso_hom, BasedNatTrans.forgetful_map]
          haveI h₁ : IsHomLift 𝒳.p (𝟙 (𝒯.p.obj t)) (η₁.hom.toNatTrans.app t) :=
            η₁.hom.isHomLift' t
          haveI h₂ : IsHomLift 𝒴.p (𝟙 (𝒯.p.obj t)) (η₂.hom.toNatTrans.app t) :=
            η₂.hom.isHomLift' t
          haveI i₁ := base_isHomLift_comp (S := 𝒯.p.obj t)
            (T := 𝒳.p.obj ((prodLift a' b').obj t).fst)
            (𝒳.toBase.map (η₁.hom.toNatTrans.app t)) (((prodLift a' b').obj t).iso.hom)
          haveI i₂ := base_isHomLift_comp (S := 𝒳.p.obj ((prodLift a b).obj t).fst)
            (T := 𝒯.p.obj t)
            (((prodLift a b).obj t).iso.hom) (𝒴.toBase.map (η₂.hom.toNatTrans.app t))
          exact base_hom_ext (S := 𝒯.p.obj t)
            (T := 𝒳.p.obj ((prodLift a b).obj t).fst) _ _))
      (fun {t t'} φ ↦ by
        apply FiberProductHom.ext
        · exact η₁.hom.toNatTrans.naturality φ
        · exact η₂.hom.toNatTrans.naturality φ))
    (fun t ↦ FiberProductHom.isHomLift_of_fst _ (𝟙 (𝒯.p.obj t)) (η₁.hom.isHomLift' t))

/-- Functoriality of fiber products of based categories: a 2-commutative morphism
of cospans induces a morphism of their fiber products. -/
def fiberProductMap {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
    {𝒴 : BasedCategory.{v₃, u₃} 𝒮} {𝒴' : BasedCategory.{v₄, u₄} 𝒮}
    {𝒳₁ : BasedCategory.{v₅, u₅} 𝒮} {𝒴₁ : BasedCategory.{v₆, u₆} 𝒮}
    {𝒴₁' : BasedCategory.{v₇, u₇} 𝒮} {F : 𝒳 ⥤ᵇ 𝒴} {G : 𝒴' ⥤ᵇ 𝒴}
    {F₁ : 𝒳₁ ⥤ᵇ 𝒴₁} {G₁ : 𝒴₁' ⥤ᵇ 𝒴₁} (α : 𝒳 ⥤ᵇ 𝒳₁) (β : 𝒴 ⥤ᵇ 𝒴₁)
    (γ : 𝒴' ⥤ᵇ 𝒴₁') (τα : α.comp F₁ ≅ F.comp β)
    (τγ : γ.comp G₁ ≅ G.comp β) : fiberProduct F G ⥤ᵇ fiberProduct F₁ G₁ :=
  fiberProductLift ((fiberProductFst F G).comp α) ((fiberProductSnd F G).comp γ)
    (whiskerLeftIso (fiberProductFst F G) τα ≪≫
      whiskerRightIso (fiberProductIsoComm F G) β ≪≫
      (whiskerLeftIso (fiberProductSnd F G) τγ).symm)

@[simp]
lemma fiberProductMap_comp_fst {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
    {𝒴 : BasedCategory.{v₃, u₃} 𝒮} {𝒴' : BasedCategory.{v₄, u₄} 𝒮}
    {𝒳₁ : BasedCategory.{v₅, u₅} 𝒮} {𝒴₁ : BasedCategory.{v₆, u₆} 𝒮}
    {𝒴₁' : BasedCategory.{v₇, u₇} 𝒮} {F : 𝒳 ⥤ᵇ 𝒴} {G : 𝒴' ⥤ᵇ 𝒴}
    {F₁ : 𝒳₁ ⥤ᵇ 𝒴₁} {G₁ : 𝒴₁' ⥤ᵇ 𝒴₁} (α : 𝒳 ⥤ᵇ 𝒳₁)
    (β : 𝒴 ⥤ᵇ 𝒴₁) (γ : 𝒴' ⥤ᵇ 𝒴₁') (τα : α.comp F₁ ≅ F.comp β)
    (τγ : γ.comp G₁ ≅ G.comp β) :
    (fiberProductMap α β γ τα τγ).comp (fiberProductFst F₁ G₁) =
      (fiberProductFst F G).comp α :=
  fiberProductLift_comp_fst _ _ _

@[simp]
lemma fiberProductMap_comp_snd {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
    {𝒴 : BasedCategory.{v₃, u₃} 𝒮} {𝒴' : BasedCategory.{v₄, u₄} 𝒮}
    {𝒳₁ : BasedCategory.{v₅, u₅} 𝒮} {𝒴₁ : BasedCategory.{v₆, u₆} 𝒮}
    {𝒴₁' : BasedCategory.{v₇, u₇} 𝒮} {F : 𝒳 ⥤ᵇ 𝒴} {G : 𝒴' ⥤ᵇ 𝒴}
    {F₁ : 𝒳₁ ⥤ᵇ 𝒴₁} {G₁ : 𝒴₁' ⥤ᵇ 𝒴₁} (α : 𝒳 ⥤ᵇ 𝒳₁)
    (β : 𝒴 ⥤ᵇ 𝒴₁) (γ : 𝒴' ⥤ᵇ 𝒴₁') (τα : α.comp F₁ ≅ F.comp β)
    (τγ : γ.comp G₁ ≅ G.comp β) :
    (fiberProductMap α β γ τα τγ).comp (fiberProductSnd F₁ G₁) =
      (fiberProductSnd F G).comp γ :=
  fiberProductLift_comp_snd _ _ _

/-- The pair `(x,y')` underlying an object `(x,y',γ)` of a fiber product, regarded
as an object of the product over the base. -/
abbrev magicSquarePairObj {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
    {𝒴 : BasedCategory.{v₃, u₃} 𝒮} {𝒴' : BasedCategory.{v₄, u₄} 𝒮}
    (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴) (x : (fiberProduct F G).obj) :
    (prod 𝒳 𝒴').obj where
  fst := x.fst
  snd := x.snd
  over_eq := x.over_eq
  iso := eqToIso x.over_eq.symm
  isHomLift := IsHomLift.eqToHom_domain_lift_id x.over_eq.symm rfl

/-- The comparison isomorphism from `(F x,G y')` to the diagonal point `(F x,F x)`,
whose second component is `γ⁻¹`. -/
def magicSquareDiagIso {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
    {𝒴 : BasedCategory.{v₃, u₃} 𝒮} {𝒴' : BasedCategory.{v₄, u₄} 𝒮}
    (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴) (x : (fiberProduct F G).obj) :
    (prodMap F G).obj (magicSquarePairObj F G x) ≅ (diag 𝒴).obj (F.obj x.fst) := by
  let e₁ : ((prodMap F G).obj (magicSquarePairObj F G x)).fst ≅
      ((diag 𝒴).obj (F.obj x.fst)).fst := eqToIso (by rfl)
  let e₂ : ((prodMap F G).obj (magicSquarePairObj F G x)).snd ≅
      ((diag 𝒴).obj (F.obj x.fst)).snd := by
    exact x.iso.symm
  apply FiberProductObj.isoMk e₁ e₂
  · haveI he₁ : IsHomLift 𝒴.p (𝟙 (𝒴.p.obj (F.obj x.fst))) e₁.hom := by
      dsimp [e₁]
      exact IsHomLift.eqToHom_domain_lift_id (p := 𝒴.p) (by rfl) rfl
    haveI he₂ : IsHomLift 𝒴.p (𝟙 (𝒴.p.obj (F.obj x.fst))) e₂.hom := by
      dsimp [e₂]
      rw [F.w_obj]
      infer_instance
    apply IsHomLift.of_commSq 𝒴.p (𝒴.p.map e₁.hom) e₂.hom
      ((prodMap F G).obj (magicSquarePairObj F G x)).over_eq
      ((diag 𝒴).obj (F.obj x.fst)).over_eq
    constructor
    rw [IsHomLift.fac' 𝒴.p (𝟙 (𝒴.p.obj (F.obj x.fst))) e₁.hom,
      IsHomLift.fac' 𝒴.p (𝟙 (𝒴.p.obj (F.obj x.fst))) e₂.hom]
    simp
  · haveI he₁ : IsHomLift 𝒴.p (𝟙 (𝒴.p.obj (F.obj x.fst))) e₁.hom := by
      dsimp [e₁]
      exact IsHomLift.eqToHom_domain_lift_id (p := 𝒴.p) (by rfl) rfl
    haveI he₂ : IsHomLift 𝒴.p (𝟙 (𝒴.p.obj (F.obj x.fst))) e₂.hom := by
      dsimp [e₂]
      rw [F.w_obj]
      infer_instance
    haveI htarget : IsHomLift (base 𝒮).p (𝟙 (𝒴.p.obj (F.obj x.fst)))
        ((diag 𝒴).obj (F.obj x.fst)).iso.hom := by
      exact ((diag 𝒴).obj (F.obj x.fst)).isHomLift
    haveI hsource : IsHomLift (base 𝒮).p (𝟙 (𝒴.p.obj (F.obj x.fst)))
        ((prodMap F G).obj (magicSquarePairObj F G x)).iso.hom := by
      exact ((prodMap F G).obj (magicSquarePairObj F G x)).isHomLift
    haveI hleft := base_isHomLift_comp
      (S := 𝒴.p.obj (F.obj x.fst)) (T := 𝒴.p.obj (F.obj x.fst))
      (𝒴.toBase.map e₁.hom) (((diag 𝒴).obj (F.obj x.fst)).iso.hom)
    haveI hright := base_isHomLift_comp
      (S := 𝒴.p.obj (F.obj x.fst)) (T := 𝒴.p.obj (F.obj x.fst))
      (((prodMap F G).obj (magicSquarePairObj F G x)).iso.hom) (𝒴.toBase.map e₂.hom)
    exact base_hom_ext (S := 𝒴.p.obj (F.obj x.fst))
      (T := 𝒴.p.obj (F.obj x.fst)) _ _

@[simp]
lemma magicSquareDiagIso_hom_fst {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
    {𝒴 : BasedCategory.{v₃, u₃} 𝒮} {𝒴' : BasedCategory.{v₄, u₄} 𝒮}
    (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴) (x : (fiberProduct F G).obj) :
    (magicSquareDiagIso F G x).hom.fst = 𝟙 (F.obj x.fst) :=
  rfl

@[simp]
lemma magicSquareDiagIso_hom_snd {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
    {𝒴 : BasedCategory.{v₃, u₃} 𝒮} {𝒴' : BasedCategory.{v₄, u₄} 𝒮}
    (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴) (x : (fiberProduct F G).obj) :
    (magicSquareDiagIso F G x).hom.snd = x.iso.inv :=
  rfl

/-- The pair of component arrows underlying a morphism of a fiber product, regarded
as a morphism in the product over the base. -/
def magicSquarePairHom {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
    {𝒴 : BasedCategory.{v₃, u₃} 𝒮} {𝒴' : BasedCategory.{v₄, u₄} 𝒮}
    (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴) {x y : (fiberProduct F G).obj} (q : x ⟶ y) :
    magicSquarePairObj F G x ⟶ magicSquarePairObj F G y where
  fst := q.fst
  snd := q.snd
  isHomLift := q.isHomLift
  w := by
    haveI hfst : IsHomLift (base 𝒮).p (𝒳.p.map q.fst)
        (𝒳.toBase.map q.fst) := by infer_instance
    haveI hyiso : IsHomLift (base 𝒮).p (𝟙 (𝒳.p.obj y.fst))
        (magicSquarePairObj F G y).iso.hom := by
      exact (magicSquarePairObj F G y).isHomLift
    haveI hleft : IsHomLift (base 𝒮).p (𝒳.p.map q.fst)
        (𝒳.toBase.map q.fst ≫ (magicSquarePairObj F G y).iso.hom) := by
      infer_instance
    haveI hxiso : IsHomLift (base 𝒮).p (𝟙 (𝒳.p.obj x.fst))
        (magicSquarePairObj F G x).iso.hom := by
      exact (magicSquarePairObj F G x).isHomLift
    haveI hsnd : IsHomLift (base 𝒮).p (𝒳.p.map q.fst)
        (𝒴'.toBase.map q.snd) := by infer_instance
    haveI hright : IsHomLift (base 𝒮).p (𝒳.p.map q.fst)
        ((magicSquarePairObj F G x).iso.hom ≫ 𝒴'.toBase.map q.snd) := by
      infer_instance
    exact base_hom_ext_of_lift (𝒳.p.map q.fst) _ _

@[simp]
lemma magicSquarePairHom_fst {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
    {𝒴 : BasedCategory.{v₃, u₃} 𝒮} {𝒴' : BasedCategory.{v₄, u₄} 𝒮}
    (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴) {x y : (fiberProduct F G).obj} (q : x ⟶ y) :
    (magicSquarePairHom F G q).fst = q.fst :=
  rfl

@[simp]
lemma magicSquarePairHom_snd {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
    {𝒴 : BasedCategory.{v₃, u₃} 𝒮} {𝒴' : BasedCategory.{v₄, u₄} 𝒮}
    (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴) {x y : (fiberProduct F G).obj} (q : x ⟶ y) :
    (magicSquarePairHom F G q).snd = q.snd :=
  rfl

/-- The canonical comparison in the magic square. Its concrete definition makes the
two projections available definitionally for the full-faithfulness proof. -/
def fiberProductToProdMapDiag {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
    {𝒴 : BasedCategory.{v₃, u₃} 𝒮} {𝒴' : BasedCategory.{v₄, u₄} 𝒮}
    (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴) :
    fiberProduct F G ⥤ᵇ fiberProduct (prodMap F G) (diag 𝒴) where
  obj x :=
    { fst := magicSquarePairObj F G x
      snd := F.obj x.fst
      over_eq := F.w_obj x.fst
      iso := magicSquareDiagIso F G x
      isHomLift := by
        apply FiberProductHom.isHomLift_of_fst _
          (𝟙 ((prod 𝒳 𝒴').p.obj (magicSquarePairObj F G x)))
        rw [magicSquareDiagIso_hom_fst]
        exact IsHomLift.id (F.w_obj x.fst) }
  map {x y} q :=
    { fst := magicSquarePairHom F G q
      snd := F.map q.fst
      isHomLift := by
        change IsHomLift 𝒴.p (𝒳.p.map q.fst) (F.map q.fst)
        infer_instance
      w := by
        apply FiberProductHom.ext
        · change F.map q.fst ≫ 𝟙 _ = 𝟙 _ ≫ F.map q.fst
          simp
        · change G.map q.snd ≫ y.iso.inv = x.iso.inv ≫ F.map q.fst
          rw [← cancel_mono y.iso.hom, Category.assoc, Iso.inv_hom_id,
            Category.comp_id, Category.assoc, q.w, ← Category.assoc,
            Iso.inv_hom_id, Category.id_comp] }
  map_id x := by
    apply FiberProductHom.ext
    · apply FiberProductHom.ext <;> rfl
    · change F.map (𝟙 x.fst) = 𝟙 (F.obj x.fst)
      exact F.toFunctor.map_id x.fst
  map_comp q r := by
    apply FiberProductHom.ext
    · apply FiberProductHom.ext <;> rfl
    · change F.map (q.fst ≫ r.fst) = F.map q.fst ≫ F.map r.fst
      exact F.toFunctor.map_comp q.fst r.fst
  w := rfl

@[simp]
lemma fiberProductToProdMapDiag_obj_fst_fst
    {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    {𝒴' : BasedCategory.{v₄, u₄} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴)
    (x : (fiberProduct F G).obj) :
    ((fiberProductToProdMapDiag F G).obj x).fst.fst = x.fst :=
  rfl

@[simp]
lemma fiberProductToProdMapDiag_obj_fst_snd
    {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    {𝒴' : BasedCategory.{v₄, u₄} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴)
    (x : (fiberProduct F G).obj) :
    ((fiberProductToProdMapDiag F G).obj x).fst.snd = x.snd :=
  rfl

@[simp]
lemma fiberProductToProdMapDiag_obj_snd
    {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    {𝒴' : BasedCategory.{v₄, u₄} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴)
    (x : (fiberProduct F G).obj) :
    ((fiberProductToProdMapDiag F G).obj x).snd = F.obj x.fst :=
  rfl

@[simp]
lemma fiberProductToProdMapDiag_obj_iso_hom_fst
    {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    {𝒴' : BasedCategory.{v₄, u₄} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴)
    (x : (fiberProduct F G).obj) :
    ((fiberProductToProdMapDiag F G).obj x).iso.hom.fst = 𝟙 (F.obj x.fst) :=
  rfl

@[simp]
lemma fiberProductToProdMapDiag_obj_iso_hom_snd
    {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    {𝒴' : BasedCategory.{v₄, u₄} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴)
    (x : (fiberProduct F G).obj) :
    ((fiberProductToProdMapDiag F G).obj x).iso.hom.snd = x.iso.inv :=
  rfl

/-- The magic-square comparison is faithful. -/
lemma fiberProductToProdMapDiag_faithful
    {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    {𝒴' : BasedCategory.{v₄, u₄} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴) :
    (fiberProductToProdMapDiag F G).toFunctor.Faithful := by
  constructor
  intro a b f g h
  apply FiberProductHom.ext
  · exact congrArg (fun q ↦ q.fst.fst) h
  · exact congrArg (fun q ↦ q.fst.snd) h

/-- The magic-square comparison is full. -/
lemma fiberProductToProdMapDiag_full
    {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    {𝒴' : BasedCategory.{v₄, u₄} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴) :
    (fiberProductToProdMapDiag F G).toFunctor.Full := by
  constructor
  intro a b q
  let p : a ⟶ b :=
    { fst := q.fst.fst
      snd := q.fst.snd
      isHomLift := q.fst.isHomLift
      w := by
        have hw₁ := congrArg FiberProductHom.fst q.w
        have hw₂ := congrArg FiberProductHom.snd q.w
        simp only [FiberProductObj.comp_fst, FiberProductObj.comp_snd,
          prodMap_map_fst, prodMap_map_snd, diag_map_fst, diag_map_snd,
          fiberProductToProdMapDiag_obj_iso_hom_fst,
          fiberProductToProdMapDiag_obj_iso_hom_snd,
          fiberProductToProdMapDiag_obj_fst_fst,
          fiberProductToProdMapDiag_obj_fst_snd,
          fiberProductToProdMapDiag_obj_snd,
          Category.comp_id, Category.id_comp] at hw₁ hw₂
        have hw₁' : F.map q.fst.fst = q.snd := by
          calc
            F.map q.fst.fst = F.map q.fst.fst ≫ 𝟙 _ := (Category.comp_id _).symm
            _ = 𝟙 _ ≫ q.snd := hw₁
            _ = q.snd := Category.id_comp _
        apply (cancel_mono b.iso.inv).mp
        calc
          (F.map q.fst.fst ≫ b.iso.hom) ≫ b.iso.inv = F.map q.fst.fst := by simp
          _ = q.snd := hw₁'
          _ = (a.iso.hom ≫ G.map q.fst.snd) ≫ b.iso.inv := by
            rw [Category.assoc, hw₂, ← Category.assoc,
              Iso.hom_inv_id, Category.id_comp] }
  exact ⟨p, by
    apply FiberProductHom.ext
    · apply FiberProductHom.ext <;> rfl
    · change F.map p.fst = q.snd
      have hw₁ := congrArg FiberProductHom.fst q.w
      simp only [FiberProductObj.comp_fst, fiberProductLift_map_fst,
        prodMap_map_fst, diag_map_fst,
        fiberProductToProdMapDiag_obj_iso_hom_fst,
        fiberProductToProdMapDiag_obj_fst_fst,
        fiberProductToProdMapDiag_obj_snd,
        Category.comp_id, Category.id_comp] at hw₁
      have hw₁' : F.map q.fst.fst = q.snd := by
        calc
          F.map q.fst.fst = F.map q.fst.fst ≫ 𝟙 _ := (Category.comp_id _).symm
          _ = 𝟙 _ ≫ q.snd := hw₁
          _ = q.snd := Category.id_comp _
      simpa only [p] using hw₁'⟩

/-- The first component of the target comparison isomorphism. -/
abbrev magicSquareTargetFstIso
    {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    {𝒴' : BasedCategory.{v₄, u₄} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴)
    (q : (fiberProduct (prodMap F G) (diag 𝒴)).obj) : F.obj q.fst.fst ≅ q.snd :=
  (fiberProductFst 𝒴.toBase 𝒴.toBase).toFunctor.mapIso q.iso

/-- The second component of the target comparison isomorphism. -/
abbrev magicSquareTargetSndIso
    {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    {𝒴' : BasedCategory.{v₄, u₄} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴)
    (q : (fiberProduct (prodMap F G) (diag 𝒴)).obj) : G.obj q.fst.snd ≅ q.snd :=
  (fiberProductSnd 𝒴.toBase 𝒴.toBase).toFunctor.mapIso q.iso

@[simp]
lemma magicSquareTargetFstIso_hom
    {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    {𝒴' : BasedCategory.{v₄, u₄} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴)
    (q : (fiberProduct (prodMap F G) (diag 𝒴)).obj) :
    (magicSquareTargetFstIso F G q).hom = q.iso.hom.fst := rfl

@[simp]
lemma magicSquareTargetFstIso_inv
    {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    {𝒴' : BasedCategory.{v₄, u₄} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴)
    (q : (fiberProduct (prodMap F G) (diag 𝒴)).obj) :
    (magicSquareTargetFstIso F G q).inv = q.iso.inv.fst := rfl

@[simp]
lemma magicSquareTargetSndIso_hom
    {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    {𝒴' : BasedCategory.{v₄, u₄} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴)
    (q : (fiberProduct (prodMap F G) (diag 𝒴)).obj) :
    (magicSquareTargetSndIso F G q).hom = q.iso.hom.snd := rfl

@[simp]
lemma magicSquareTargetSndIso_inv
    {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    {𝒴' : BasedCategory.{v₄, u₄} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴)
    (q : (fiberProduct (prodMap F G) (diag 𝒴)).obj) :
    (magicSquareTargetSndIso F G q).inv = q.iso.inv.snd := rfl

/-- An explicit preimage of an object under the magic-square comparison. -/
abbrev magicSquarePreimageObj
    {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    {𝒴' : BasedCategory.{v₄, u₄} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴)
    (q : (fiberProduct (prodMap F G) (diag 𝒴)).obj) : (fiberProduct F G).obj where
  fst := q.fst.fst
  snd := q.fst.snd
  over_eq := q.fst.over_eq
  iso := magicSquareTargetFstIso F G q ≪≫ (magicSquareTargetSndIso F G q).symm
  isHomLift := by
    let e₁ := magicSquareTargetFstIso F G q
    let e₂ := magicSquareTargetSndIso F G q
    haveI he₁ : IsHomLift 𝒴.p (𝟙 ((prod 𝒳 𝒴').p.obj q.fst)) e₁.hom := by
      apply FiberProductHom.isHomLift_fst q.iso.hom
        (𝟙 ((prod 𝒳 𝒴').p.obj q.fst))
      exact q.isHomLift
    haveI he₂ : IsHomLift 𝒴.p (𝟙 ((prod 𝒳 𝒴').p.obj q.fst)) e₂.hom := by
      dsimp [e₂, magicSquareTargetSndIso]
      exact FiberProductHom.isHomLift_snd (F := 𝒴.toBase) (G := 𝒴.toBase)
        q.iso.hom (𝟙 (𝒳.p.obj q.fst.fst)) q.isHomLift
    haveI he₂inv : IsHomLift 𝒴.p (𝟙 ((prod 𝒳 𝒴').p.obj q.fst)) e₂.inv := by
      infer_instance
    change IsHomLift 𝒴.p (𝟙 ((prod 𝒳 𝒴').p.obj q.fst)) (e₁.hom ≫ e₂.inv)
    infer_instance

/-- The underlying pair of the explicit preimage is canonically isomorphic to the
pair in the given target object. -/
abbrev magicSquarePairIso
    {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    {𝒴' : BasedCategory.{v₄, u₄} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴)
    (q : (fiberProduct (prodMap F G) (diag 𝒴)).obj) :
    magicSquarePairObj F G (magicSquarePreimageObj F G q) ≅ q.fst := by
  let e₁ : (magicSquarePairObj F G (magicSquarePreimageObj F G q)).fst ≅
      q.fst.fst := eqToIso (by rfl)
  let e₂ : (magicSquarePairObj F G (magicSquarePreimageObj F G q)).snd ≅
      q.fst.snd := eqToIso (by rfl)
  apply FiberProductObj.isoMk e₁ e₂
  · dsimp [e₁, e₂]
    rw [𝒳.p.map_id]
    exact IsHomLift.id q.fst.over_eq
  · haveI he₁ : IsHomLift 𝒳.p (𝟙 (𝒳.p.obj q.fst.fst)) e₁.hom := by
      dsimp [e₁]
      exact IsHomLift.eqToHom_domain_lift_id (by rfl) rfl
    haveI he₂ : IsHomLift 𝒴'.p (𝟙 (𝒳.p.obj q.fst.fst)) e₂.hom := by
      dsimp [e₂]
      exact IsHomLift.eqToHom_domain_lift_id (by rfl) q.fst.over_eq
    haveI htarget : IsHomLift (base 𝒮).p (𝟙 (𝒳.p.obj q.fst.fst))
        q.fst.iso.hom := q.fst.isHomLift
    haveI hsource : IsHomLift (base 𝒮).p (𝟙 (𝒳.p.obj q.fst.fst))
        (magicSquarePairObj F G (magicSquarePreimageObj F G q)).iso.hom :=
      (magicSquarePairObj F G (magicSquarePreimageObj F G q)).isHomLift
    haveI hleft := base_isHomLift_comp
      (S := 𝒳.p.obj q.fst.fst) (T := 𝒳.p.obj q.fst.fst)
      (𝒳.toBase.map e₁.hom) q.fst.iso.hom
    haveI hright := base_isHomLift_comp
      (S := 𝒳.p.obj q.fst.fst) (T := 𝒳.p.obj q.fst.fst)
      (magicSquarePairObj F G (magicSquarePreimageObj F G q)).iso.hom
      (𝒴'.toBase.map e₂.hom)
    exact base_hom_ext
      (S := 𝒳.p.obj q.fst.fst) (T := 𝒳.p.obj q.fst.fst) _ _

@[simp]
lemma magicSquarePairIso_hom_fst
    {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    {𝒴' : BasedCategory.{v₄, u₄} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴)
    (q : (fiberProduct (prodMap F G) (diag 𝒴)).obj) :
    (magicSquarePairIso F G q).hom.fst = 𝟙 q.fst.fst := rfl

@[simp]
lemma magicSquarePairIso_hom_snd
    {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    {𝒴' : BasedCategory.{v₄, u₄} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴)
    (q : (fiberProduct (prodMap F G) (diag 𝒴)).obj) :
    (magicSquarePairIso F G q).hom.snd = 𝟙 q.fst.snd := rfl

@[simp]
lemma magicSquarePreimageObj_iso_inv
    {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    {𝒴' : BasedCategory.{v₄, u₄} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴)
    (q : (fiberProduct (prodMap F G) (diag 𝒴)).obj) :
    (magicSquarePreimageObj F G q).iso.inv =
      (magicSquareTargetSndIso F G q).hom ≫
        (magicSquareTargetFstIso F G q).inv := rfl

/-- The comparison sends its explicit preimage to an object isomorphic to the
original target object. -/
def magicSquarePreimageIso
    {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    {𝒴' : BasedCategory.{v₄, u₄} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴)
    (q : (fiberProduct (prodMap F G) (diag 𝒴)).obj) :
    (fiberProductToProdMapDiag F G).obj (magicSquarePreimageObj F G q) ≅ q := by
  let e₁ := magicSquarePairIso F G q
  let e₂ := magicSquareTargetFstIso F G q
  apply FiberProductObj.isoMk e₁ e₂
  · have hp : IsHomLift 𝒳.p (𝟙 (𝒳.p.obj q.fst.fst))
        (magicSquarePairIso F G q).hom.fst := by
      rw [magicSquarePairIso_hom_fst]
      exact IsHomLift.id rfl
    have hq := FiberProductHom.isHomLift_fst q.iso.hom
      (𝟙 ((prod 𝒳 𝒴').p.obj q.fst)) q.isHomLift
    exact isHomLift_map_of_common_lift
      (𝟙 (𝒳.p.obj q.fst.fst)) (magicSquarePairIso F G q).hom.fst
      q.iso.hom.fst hp hq
  · have hf : F.map (magicSquarePairIso F G q).hom.fst = 𝟙 (F.obj q.fst.fst) := by
      rw [magicSquarePairIso_hom_fst]
      exact F.toFunctor.map_id q.fst.fst
    have hg : G.map (magicSquarePairIso F G q).hom.snd = 𝟙 (G.obj q.fst.snd) := by
      rw [magicSquarePairIso_hom_snd]
      exact G.toFunctor.map_id q.fst.snd
    apply FiberProductHom.ext
    · simp only [FiberProductObj.comp_fst, prodMap_map_fst, diag_map_fst,
        fiberProductToProdMapDiag_obj_iso_hom_fst]
      rw [hf]
      dsimp only [e₂]
      rw [magicSquareTargetFstIso_hom]
    · simp only [FiberProductObj.comp_snd, prodMap_map_snd, diag_map_snd,
        fiberProductToProdMapDiag_obj_iso_hom_snd]
      dsimp only [e₂]
      have hrhs : (magicSquarePreimageObj F G q).iso.inv ≫
          (magicSquareTargetFstIso F G q).hom = q.iso.hom.snd := by
        rw [magicSquarePreimageObj_iso_inv, Category.assoc,
          (magicSquareTargetFstIso F G q).inv_hom_id, Category.comp_id,
          magicSquareTargetSndIso_hom]
      calc
        G.map (magicSquarePairIso F G q).hom.snd ≫ q.iso.hom.snd =
            𝟙 (G.obj q.fst.snd) ≫ q.iso.hom.snd :=
          congrArg (fun k ↦ k ≫ q.iso.hom.snd) hg
        _ = q.iso.hom.snd := Category.id_comp _
        _ = (magicSquarePreimageObj F G q).iso.inv ≫
            (magicSquareTargetFstIso F G q).hom := hrhs.symm

/-- The magic-square comparison is essentially surjective. -/
lemma fiberProductToProdMapDiag_essSurj
    {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    {𝒴' : BasedCategory.{v₄, u₄} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴) :
    (fiberProductToProdMapDiag F G).toFunctor.EssSurj := by
  constructor
  intro q
  exact ⟨magicSquarePreimageObj F G q, ⟨magicSquarePreimageIso F G q⟩⟩

lemma diag_faithful
    {𝒳 : BasedCategory.{v₂, u₂} 𝒮} [𝒳.p.IsFiberedInGroupoids] :
    (diag 𝒳).toFunctor.Faithful := by
  constructor
  intro a b φ ψ h
  exact congrArg FiberProductHom.fst h

lemma diag_full_of_projection_faithful
    {𝒳 : BasedCategory.{v₂, u₂} 𝒮} [𝒳.p.IsFiberedInGroupoids]
    [𝒳.p.Faithful] : (diag 𝒳).toFunctor.Full := by
  constructor
  intro a b q
  have hp : 𝒳.p.map q.fst = 𝒳.p.map q.snd :=
    IsHomLift.eq_of_isHomLift 𝒳.p (𝒳.p.map q.fst) q.snd
  have hfg : q.fst = q.snd := 𝒳.p.map_injective hp
  exact ⟨q.fst, by
    apply FiberProductHom.ext
    · rfl
    · exact hfg⟩

lemma projection_faithful_of_diag_full
    {𝒳 : BasedCategory.{v₂, u₂} 𝒮} [𝒳.p.IsFiberedInGroupoids]
    [(diag 𝒳).toFunctor.Full] : 𝒳.p.Faithful := by
  constructor
  intro a b φ ψ h
  let q : (diag 𝒳).obj a ⟶ (diag 𝒳).obj b :=
    { fst := φ
      snd := ψ
      isHomLift := h ▸ IsHomLift.map (p := 𝒳.p) ψ
      w := by
        change 𝒳.p.map φ ≫ 𝟙 _ = 𝟙 _ ≫ 𝒳.p.map ψ
        simpa using h }
  obtain ⟨k, hk⟩ := Functor.Full.map_surjective q
  have hφ := congrArg FiberProductHom.fst hk
  have hψ := congrArg FiberProductHom.snd hk
  exact hφ.symm.trans hψ

/-- The diagonal of a based category is fully faithful exactly when its
projection to the base is faithful. -/
theorem diag_isMonomorphism_iff_projection_faithful
    {𝒳 : BasedCategory.{v₂, u₂} 𝒮} [𝒳.p.IsFiberedInGroupoids] :
    ((diag 𝒳).toFunctor.Full ∧ (diag 𝒳).toFunctor.Faithful) ↔
      𝒳.p.Faithful := by
  constructor
  · rintro ⟨hfull, -⟩
    letI := hfull
    exact projection_faithful_of_diag_full (𝒳 := 𝒳)
  · intro hp
    letI := hp
    exact ⟨diag_full_of_projection_faithful (𝒳 := 𝒳),
      diag_faithful (𝒳 := 𝒳)⟩


variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]

/-- The composition of two morphisms lying over identities lies over the first
identity. -/
lemma isHomLift_id_comp {𝒳 : Type u₂} [Category.{v₂} 𝒳] (p : 𝒳 ⥤ 𝒮) {S T : 𝒮}
    {a b c : 𝒳} (φ : a ⟶ b) (ψ : b ⟶ c) (h₁ : IsHomLift p (𝟙 S) φ)
    (h₂ : IsHomLift p (𝟙 T) ψ) : IsHomLift p (𝟙 S) (φ ≫ ψ) := by
  haveI := h₁
  haveI := h₂
  have h : S = T := ((IsHomLift.codomain_eq p (𝟙 S) φ).symm.trans
    (IsHomLift.domain_eq p (𝟙 T) ψ))
  subst h
  infer_instance

variable {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
  {𝒴' : BasedCategory.{v₄, u₄} 𝒮} {F : 𝒳 ⥤ᵇ 𝒴} {G : 𝒴' ⥤ᵇ 𝒴}

/-- The first components of an isomorphism in a fiber product of based categories form
an isomorphism. -/
@[simps]
def FiberProductObj.isoFst {a b : FiberProductObj F G} (e : a ≅ b) : a.fst ≅ b.fst where
  hom := e.hom.fst
  inv := e.inv.fst
  hom_inv_id := congrArg FiberProductHom.fst e.hom_inv_id
  inv_hom_id := congrArg FiberProductHom.fst e.inv_hom_id

/-- The second components of an isomorphism in a fiber product of based categories form
an isomorphism. -/
@[simps]
def FiberProductObj.isoSnd {a b : FiberProductObj F G} (e : a ≅ b) : a.snd ≅ b.snd where
  hom := e.hom.snd
  inv := e.inv.snd
  hom_inv_id := congrArg FiberProductHom.snd e.hom_inv_id
  inv_hom_id := congrArg FiberProductHom.snd e.inv_hom_id

/-- The automorphism attached to an object of the inertia stack `𝒳 ×_{𝒳 × 𝒳} 𝒳`: the
composite `γ₂ ∘ γ₁⁻¹` of its two comparison components. -/
abbrev inAut (o : FiberProductObj (diag 𝒳) (diag 𝒳)) : o.fst ≅ o.fst :=
  FiberProductObj.isoSnd o.iso ≪≫ (FiberProductObj.isoFst o.iso).symm

lemma inAut_isHomLift (o : FiberProductObj (diag 𝒳) (diag 𝒳)) :
    IsHomLift 𝒳.p (𝟙 (𝒳.p.obj o.fst)) (inAut o).hom := by
  haveI h₃ : IsHomLift (prod 𝒳 𝒳).p (𝟙 (𝒳.p.obj o.fst)) o.iso.hom := o.isHomLift
  haveI h₄ : IsHomLift (prod 𝒳 𝒳).p (𝟙 (𝒳.p.obj o.fst)) o.iso.inv :=
    IsHomLift.lift_id_inv (prod 𝒳 𝒳).p (𝒳.p.obj o.fst) o.iso
  haveI h₅ : IsHomLift 𝒳.p (𝟙 (𝒳.p.obj o.fst)) o.iso.hom.snd :=
    FiberProductHom.isHomLift_snd o.iso.hom (𝟙 (𝒳.p.obj o.fst)) h₃
  haveI h₆ : IsHomLift 𝒳.p (𝟙 (𝒳.p.obj o.fst)) o.iso.inv.fst :=
    FiberProductHom.isHomLift_fst o.iso.inv (𝟙 (𝒳.p.obj o.fst)) h₄
  exact isHomLift_id_comp 𝒳.p o.iso.hom.snd o.iso.inv.fst h₅ h₆


section Symmetry

/-- The symmetry of the fiber product: the canonical morphism `𝒳 ×_𝒴 𝒴' ⥤ᵇ 𝒴' ×_𝒴 𝒳`
exchanging the two factors, obtained from the universal property applied to the two
projections and to the inverse of the 2-commutativity isomorphism. -/
def fiberProductSymm {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    {𝒴' : BasedCategory.{v₄, u₄} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴) :
    fiberProduct F G ⥤ᵇ fiberProduct G F :=
  fiberProductLift (fiberProductSnd F G) (fiberProductFst F G)
    (fiberProductIsoComm F G).symm

/-- The symmetry of the fiber product exchanges the two projections: composing it with the
first projection of `𝒴' ×_𝒴 𝒳` gives the second projection of `𝒳 ×_𝒴 𝒴'`. -/
@[simp]
lemma fiberProductSymm_comp_fst {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
    {𝒴 : BasedCategory.{v₃, u₃} 𝒮} {𝒴' : BasedCategory.{v₄, u₄} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴)
    (G : 𝒴' ⥤ᵇ 𝒴) :
    (fiberProductSymm F G).comp (fiberProductFst G F) = fiberProductSnd F G :=
  fiberProductLift_comp_fst _ _ _

/-- The symmetry of the fiber product exchanges the two projections: composing it with the
second projection of `𝒴' ×_𝒴 𝒳` gives the first projection of `𝒳 ×_𝒴 𝒴'`. -/
@[simp]
lemma fiberProductSymm_comp_snd {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
    {𝒴 : BasedCategory.{v₃, u₃} 𝒮} {𝒴' : BasedCategory.{v₄, u₄} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴)
    (G : 𝒴' ⥤ᵇ 𝒴) :
    (fiberProductSymm F G).comp (fiberProductSnd G F) = fiberProductFst F G :=
  fiberProductLift_comp_snd _ _ _

/-- The symmetry of the fiber product, as an equivalence of the underlying categories: its
inverse is the symmetry in the other direction, and both composites are the identity
functor on the nose. -/
def fiberProductSymmEquivalence {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
    {𝒴 : BasedCategory.{v₃, u₃} 𝒮} {𝒴' : BasedCategory.{v₄, u₄} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴)
    (G : 𝒴' ⥤ᵇ 𝒴) :
    (fiberProduct F G).obj ≌ (fiberProduct G F).obj where
  functor := (fiberProductSymm F G).toFunctor
  inverse := (fiberProductSymm G F).toFunctor
  unitIso := Iso.refl _
  counitIso := Iso.refl _

instance instIsEquivalenceFiberProductSymm {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
    {𝒴 : BasedCategory.{v₃, u₃} 𝒮} {𝒴' : BasedCategory.{v₄, u₄} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴)
    (G : 𝒴' ⥤ᵇ 𝒴) :
    (fiberProductSymm F G).toFunctor.IsEquivalence :=
  (fiberProductSymmEquivalence F G).isEquivalence_functor

end Symmetry

section Pasting

variable {𝒲 : BasedCategory.{v₅, u₅} 𝒮} {𝒱 : BasedCategory.{v₄, u₄} 𝒮}
  {𝒴 : BasedCategory.{v₃, u₃} 𝒮} {𝒯 : BasedCategory.{v₆, u₆} 𝒮}

variable (E : 𝒲 ⥤ᵇ 𝒱) (g : 𝒱 ⥤ᵇ 𝒴) (h : 𝒯 ⥤ᵇ 𝒴)

/-- The 2-isomorphism of the pasted square: the outer square of

```
𝒲 ×_𝒱 (𝒱 ×_𝒴 𝒯) ⟶ 𝒱 ×_𝒴 𝒯 ⟶ 𝒯
       |                |         |
       v                v         v
       𝒲       ⟶        𝒱    ⟶    𝒴
```

is 2-commutative, being the horizontal paste of the two 2-commutative squares. -/
def pasteIso :
    (fiberProductFst E (fiberProductFst g h)).comp (E.comp g) ≅
      ((fiberProductSnd E (fiberProductFst g h)).comp (fiberProductSnd g h)).comp h :=
  (BasedCategory.isoWhiskerRight (fiberProductIsoComm E (fiberProductFst g h)) g).trans
    (BasedCategory.isoWhiskerLeft (fiberProductSnd E (fiberProductFst g h))
      (fiberProductIsoComm g h))

/-- **Pasting law for 2-fiber products of prestacks** (the comparison morphism): the
morphism `𝒲 ×_𝒱 (𝒱 ×_𝒴 𝒯) ⥤ᵇ 𝒲 ×_𝒴 𝒯` induced by the outer square of the pasted
diagram. It is an equivalence (`isEquivalence_pasteFwd`). -/
def pasteFwd : fiberProduct E (fiberProductFst g h) ⥤ᵇ fiberProduct (E.comp g) h :=
  fiberProductLift (fiberProductFst E (fiberProductFst g h))
    ((fiberProductSnd E (fiberProductFst g h)).comp (fiberProductSnd g h))
    (pasteIso E g h)

@[simp]
lemma pasteFwd_comp_fst :
    (pasteFwd E g h).comp (fiberProductFst (E.comp g) h) =
      fiberProductFst E (fiberProductFst g h) :=
  fiberProductLift_comp_fst _ _ _

@[simp]
lemma pasteFwd_comp_snd :
    (pasteFwd E g h).comp (fiberProductSnd (E.comp g) h) =
      (fiberProductSnd E (fiberProductFst g h)).comp (fiberProductSnd g h) :=
  fiberProductLift_comp_snd _ _ _


lemma pasteFwd_obj (a : FiberProductObj E (fiberProductFst g h)) :
    (pasteFwd E g h).obj a =
      { fst := a.fst, snd := a.snd.snd,
        over_eq := a.snd.over_eq.trans a.over_eq,
        iso := (g.mapIso a.iso).trans a.snd.iso,
        isHomLift := ((pasteFwd E g h).obj a).isHomLift } :=
  rfl

@[simp]
lemma pasteFwd_obj_iso_hom (x : FiberProductObj E (fiberProductFst g h)) :
    ((pasteFwd E g h).obj x).iso.hom = g.map x.iso.hom ≫ x.snd.iso.hom := by
  simp [pasteFwd, pasteIso, BasedCategory.isoWhiskerRight,
    BasedCategory.isoWhiskerLeft, fiberProductIsoComm, fiberProductLift,
    BasedNatIso.mkNatIso]

instance : (pasteFwd E g h).toFunctor.EssSurj where
  mem_essImage b := by
    refine ⟨{ fst := b.fst
              snd := { fst := E.obj b.fst, snd := b.snd
                       over_eq := b.over_eq.trans (E.w_obj b.fst).symm
                       iso := b.iso
                       isHomLift := (E.w_obj b.fst) ▸ b.isHomLift }
              over_eq := E.w_obj b.fst
              iso := Iso.refl _
              isHomLift := IsHomLift.id (E.w_obj b.fst) }, ?_⟩
    refine ⟨FiberProductObj.isoMk (F := E.comp g) (G := h) (Iso.refl _) (Iso.refl _) ?_ ?_⟩
    · show IsHomLift 𝒯.p (𝒲.p.map (𝟙 b.fst)) (𝟙 b.snd)
      rw [𝒲.p.map_id]
      exact IsHomLift.id b.over_eq
    · show (E.comp g).map (𝟙 b.fst) ≫ b.iso.hom = _ ≫ h.map (𝟙 b.snd)
      simp [pasteFwd, pasteIso, BasedCategory.isoWhiskerRight,
        BasedCategory.isoWhiskerLeft, fiberProductIsoComm, fiberProductLift,
        BasedNatIso.mkNatIso]
      rw [show g.map (𝟙 (E.obj b.fst)) = 𝟙 (g.obj (E.obj b.fst)) from
        g.toFunctor.map_id _]
      exact (Category.id_comp _).symm


instance : (pasteFwd E g h).toFunctor.Faithful where
  map_injective {a b} φ ψ hφψ := by
    have h1 : φ.fst = ψ.fst :=
      congrArg (fun (t : (pasteFwd E g h).obj a ⟶ (pasteFwd E g h).obj b) =>
        FiberProductHom.fst t) hφψ
    have h2 : φ.snd.snd = ψ.snd.snd :=
      congrArg (fun (t : (pasteFwd E g h).obj a ⟶ (pasteFwd E g h).obj b) =>
        FiberProductHom.snd t) hφψ
    have key : ∀ (θ : a ⟶ b), θ.snd.fst = a.iso.inv ≫ E.map θ.fst ≫ b.iso.hom := by
      intro θ
      have hw : E.map θ.fst ≫ b.iso.hom = a.iso.hom ≫ θ.snd.fst := θ.w
      have h3 : a.iso.inv ≫ E.map θ.fst ≫ b.iso.hom = a.iso.inv ≫ a.iso.hom ≫ θ.snd.fst := by
        rw [hw]
      rw [h3, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    refine FiberProductHom.ext h1 ?_
    refine FiberProductHom.ext ?_ h2
    rw [key φ, key ψ, h1]


section Full

variable {E g h}
variable {a b : FiberProductObj E (fiberProductFst g h)}
  (θ : (pasteFwd E g h).obj a ⟶ (pasteFwd E g h).obj b)

/-- The middle component of the morphism upstairs reconstructed from a morphism
downstairs: it is forced by the compatibility condition
`FiberProductHom.w`, which is why the comparison is fully faithful. -/
abbrev pasteMid : a.snd.fst ⟶ b.snd.fst :=
  a.iso.inv ≫ E.map θ.fst ≫ b.iso.hom

lemma pasteMid_isHomLift : IsHomLift 𝒱.p (𝒲.p.map θ.fst) (pasteMid θ) := by
  have h1 : IsHomLift 𝒱.p (𝟙 (𝒲.p.obj a.fst)) a.iso.inv := inferInstance
  have h2 : IsHomLift 𝒱.p (𝒲.p.map θ.fst) (E.map θ.fst) :=
    E.preserves_isHomLift _ _
  have h3 : IsHomLift 𝒱.p (𝟙 (𝒲.p.obj b.fst)) b.iso.hom := b.isHomLift
  have hc : IsHomLift 𝒱.p (𝟙 (𝒲.p.obj a.fst) ≫ 𝒲.p.map θ.fst ≫ 𝟙 (𝒲.p.obj b.fst))
      (a.iso.inv ≫ E.map θ.fst ≫ b.iso.hom) := inferInstance
  have heq : (𝟙 (𝒲.p.obj a.fst) ≫ 𝒲.p.map θ.fst ≫ 𝟙 (𝒲.p.obj b.fst)) =
      𝒲.p.map θ.fst := by
    rw [Category.id_comp]
    exact Category.comp_id _
  rwa [heq] at hc


/-- The morphism upstairs reconstructed from a morphism downstairs; this is the inverse
of the action of `pasteFwd` on morphisms, and gives fullness. -/
def pasteLift : a ⟶ b where
  fst := θ.fst
  snd :=
    { fst := pasteMid θ
      snd := θ.snd
      isHomLift := by
        have hm := pasteMid_isHomLift θ
        rw [IsHomLift.fac' 𝒱.p (𝒲.p.map θ.fst) (pasteMid θ)]
        have ht := θ.isHomLift
        infer_instance
      w := by
        have hw : (E.comp g).map θ.fst ≫ ((pasteFwd E g h).obj b).iso.hom =
            ((pasteFwd E g h).obj a).iso.hom ≫ h.map θ.snd := θ.w
        rw [pasteFwd_obj_iso_hom, pasteFwd_obj_iso_hom] at hw
        show g.map (a.iso.inv ≫ E.map θ.fst ≫ b.iso.hom) ≫ b.snd.iso.hom =
          a.snd.iso.hom ≫ h.map θ.snd
        rw [g.toFunctor.map_comp, g.toFunctor.map_comp, Category.assoc, Category.assoc]
        calc g.map a.iso.inv ≫ g.map (E.map θ.fst) ≫ g.map b.iso.hom ≫ b.snd.iso.hom
            = g.map a.iso.inv ≫ ((g.map a.iso.hom ≫ a.snd.iso.hom) ≫ h.map θ.snd) := by
              congr 1
          _ = a.snd.iso.hom ≫ h.map θ.snd := by
              rw [Category.assoc, ← Category.assoc (g.map a.iso.inv),
                ← g.toFunctor.map_comp, Iso.inv_hom_id, g.toFunctor.map_id,
                Category.id_comp] }
  isHomLift := by
    refine IsHomLift.of_fac' _ _ _ a.over_eq b.over_eq ?_
    have hm := pasteMid_isHomLift θ
    exact IsHomLift.fac' 𝒱.p (𝒲.p.map θ.fst) (pasteMid θ)
  w := by
    show E.map θ.fst ≫ b.iso.hom = a.iso.hom ≫ pasteMid θ
    rw [show pasteMid θ = a.iso.inv ≫ E.map θ.fst ≫ b.iso.hom from rfl,
      ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

instance : (pasteFwd E g h).toFunctor.Full where
  map_surjective θ := ⟨pasteLift θ, rfl⟩

end Full


/-- **Pasting law for 2-fiber products of prestacks**: the comparison morphism
`𝒲 ×_𝒱 (𝒱 ×_𝒴 𝒯) ⥤ᵇ 𝒲 ×_𝒴 𝒯` is an equivalence. -/
instance isEquivalence_pasteFwd : (pasteFwd E g h).toFunctor.IsEquivalence where

end Pasting

end CategoryTheory.BasedCategory
