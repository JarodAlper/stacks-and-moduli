module

public import StacksAndModuli.API.PseudofunctorStack
public import Mathlib.AlgebraicGeometry.Sites.SheafQuasiCompact
public import Mathlib.CategoryTheory.Sites.Descent.Precoverage

/-!
# Composition and collapse of pseudofunctor descent data

This file proves effective-descent transitivity for a singleton morphism followed by a
covering family. Given `q : T ⟶ S`, a covering family `g i : X i ⟶ T`, and descent data
for the composites `g i ≫ q`, effectiveness along `g` glues the component objects and the
comparison morphisms into descent data for `q`. The resulting pullback functor on descent
data is an equivalence.

The final scheme-level theorem applies this construction to the Zariski cover of a finite
coproduct by its summands. It identifies descent along a finite family with descent along
the single morphism from its disjoint union.

Main declarations:
- `CategoryTheory.Pseudofunctor.isStackFor_iff_of_pullFunctor_isEquivalence`;
- `CategoryTheory.Pseudofunctor.DescentComposition.pullFunctorIsEquivalence`;
- `CategoryTheory.Pseudofunctor.DescentComposition.isStackFor_singleton_iff_composite`;
- `AlgebraicGeometry.Scheme.Cover.isStackFor_sigma_iff`;
- `AlgebraicGeometry.isStackFor_propQCCover_of_affine_singletons`.
-/

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

universe t t' v' v u' u

namespace CategoryTheory.Pseudofunctor

open LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
  (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
  {S : C} {I : Type t} {X : I → C} (f : ∀ i, X i ⟶ S)
  {I' : Type t'} {X' : I' → C} (f' : ∀ i, X' i ⟶ S)

lemma isStackFor_iff_of_pullFunctor_isEquivalence
    (α : I' → I) (p' : ∀ j, X' j ⟶ X (α j))
    (w : ∀ j, p' j ≫ f (α j) = f' j)
    [(DescentData.pullFunctor F (f := f) (f' := f') (α := α) (p := 𝟙 S) (p' := p')
      (fun j ↦ by simpa using w j)).IsEquivalence] :
    F.IsStackFor (Presieve.ofArrows X f) ↔
      F.IsStackFor (Presieve.ofArrows X' f') := by
  rw [isStackFor_ofArrows_iff, isStackFor_ofArrows_iff]
  let w' : ∀ j, p' j ≫ f (α j) = f' j ≫ 𝟙 S := fun j ↦ by simpa using w j
  let H := DescentData.pullFunctor F (f := f) (f' := f') (α := α)
    (p := 𝟙 S) (p' := p') w'
  let e : F.toDescentData f ⋙ H ≅ F.toDescentData f' :=
    DescentData.toDescentDataCompPullFunctorIso F w' ≪≫
      Functor.isoWhiskerRight (Cat.Hom.toNatIso (F.mapId _)) _ ≪≫
        Functor.leftUnitor _
  constructor
  · intro h
    letI : (F.toDescentData f).IsEquivalence := h
    rw [← Functor.isEquivalence_iff_of_iso e]
    infer_instance
  · intro h
    letI : (F.toDescentData f').IsEquivalence := h
    rw [← Functor.isEquivalence_iff_of_iso e] at h
    exact Functor.isEquivalence_of_comp_right _ H

end CategoryTheory.Pseudofunctor

namespace CategoryTheory.Pseudofunctor

open LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
  {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
  {I : Type t} {X : I → C} {T S : C} (g : ∀ i, X i ⟶ T) (q : T ⟶ S)

namespace DescentComposition

lemma mapComp'_hom_app_heq
    {A B D : LocallyDiscrete Cᵒᵖ} {f f' : A ⟶ B} {h h' : B ⟶ D}
    {fh fh' : A ⟶ D} (ef : f = f') (eh : h = h') (efh : fh = fh')
    (p : f ≫ h = fh) (p' : f' ≫ h' = fh') (M : F.obj A) :
    HEq ((F.mapComp' f h fh p).hom.toNatTrans.app M)
      ((F.mapComp' f' h' fh' p').hom.toNatTrans.app M) := by
  subst f'
  subst h'
  subst fh'
  rfl

lemma mapComp'_inv_app_heq
    {A B D : LocallyDiscrete Cᵒᵖ} {f f' : A ⟶ B} {h h' : B ⟶ D}
    {fh fh' : A ⟶ D} (ef : f = f') (eh : h = h') (efh : fh = fh')
    (p : f ≫ h = fh) (p' : f' ≫ h' = fh') (M : F.obj A) :
    HEq ((F.mapComp' f h fh p).inv.toNatTrans.app M)
      ((F.mapComp' f' h' fh' p').inv.toNatTrans.app M) := by
  subst f'
  subst h'
  subst fh'
  rfl

lemma descentHom_heq {S₀ : C} {I₀ : Type t} {X₀ : I₀ → C}
    {f₀ : ∀ i, X₀ i ⟶ S₀} (D : F.DescentData f₀)
    {Y : C} {r r' : Y ⟶ S₀} (hr : r = r') {i₁ i₂ : I₀}
    (a : Y ⟶ X₀ i₁) (b : Y ⟶ X₀ i₂)
    (ha : a ≫ f₀ i₁ = r) (hb : b ≫ f₀ i₂ = r)
    (ha' : a ≫ f₀ i₁ = r') (hb' : b ≫ f₀ i₂ = r') :
    HEq (D.hom r a b ha hb) (D.hom r' a b ha' hb') := by
  subst r'
  rfl

/-- Restrict descent data for the composites `g i ≫ q` to descent data for `g`. -/
def restrict (D : F.DescentData (fun i ↦ g i ≫ q)) : F.DescentData g where
  obj i := D.obj i
  hom Y r i₁ i₂ a b ha hb :=
    D.hom (r ≫ q) a b (by rw [← Category.assoc, ha]) (by rw [← Category.assoc, hb])
  pullHom_hom Y' Y k r r' hr i₁ i₂ a b ha hb ka kb hka hkb := by
    apply D.pullHom_hom k (r ≫ q) (r' ≫ q) (by rw [reassoc_of% hr])
      a b (by rw [← Category.assoc, ha]) (by rw [← Category.assoc, hb]) ka kb hka hkb
  hom_self Y r i a ha := D.hom_self (r ≫ q) a (by rw [← Category.assoc, ha])
  hom_comp Y r i₁ i₂ i₃ a b c ha hb hc :=
    D.hom_comp (r ≫ q) a b c (by rw [← Category.assoc, ha])
      (by rw [← Category.assoc, hb]) (by rw [← Category.assoc, hc])

set_option backward.isDefEq.respectTransparency false in
/-- The choice-dependent core of the local comparison induced by composite descent data. -/
def localMorCore (D : F.DescentData (fun i ↦ g i ≫ q))
    (M : F.obj (.mk (op T))) (e : (F.toDescentData g).obj M ≅ restrict g q D)
    {Y : C} (r : Y ⟶ S) (f₁ f₂ : Y ⟶ T)
    (hf₁ : f₁ ≫ q = r) (hf₂ : f₂ ≫ q = r)
    {Z : C} (h : Z ⟶ Y)
    {i j : I} (a : Z ⟶ X i) (b : Z ⟶ X j)
    (ha : a ≫ g i = h ≫ f₁) (hb : b ≫ g j = h ≫ f₂) :
    (F.map (h ≫ f₁).op.toLoc).toFunctor.obj M ⟶
      (F.map (h ≫ f₂).op.toLoc).toFunctor.obj M :=
  (F.mapComp' (g i).op.toLoc a.op.toLoc (h ≫ f₁).op.toLoc
      (by simp [← ha])).hom.toNatTrans.app M ≫
    (F.map a.op.toLoc).toFunctor.map (e.hom.hom i) ≫
    D.hom (h ≫ r) a b
      (by rw [← Category.assoc, ha, Category.assoc, hf₁])
      (by rw [← Category.assoc, hb, Category.assoc, hf₂]) ≫
    (F.map b.op.toLoc).toFunctor.map (e.inv.hom j) ≫
    (F.mapComp' (g j).op.toLoc b.op.toLoc (h ≫ f₂).op.toLoc
      (by simp [← hb])).inv.toNatTrans.app M

set_option backward.isDefEq.respectTransparency false in
/-- The local comparison induced by composite descent data and a gluing of its
restriction along `g`, expressed as a section of the morphism presheaf. -/
def localMor (D : F.DescentData (fun i ↦ g i ≫ q))
    (M : F.obj (.mk (op T))) (e : (F.toDescentData g).obj M ≅ restrict g q D)
    {Y : C} (r : Y ⟶ S) (f₁ f₂ : Y ⟶ T)
    (hf₁ : f₁ ≫ q = r) (hf₂ : f₂ ≫ q = r)
    {Z : C} (h : Z ⟶ Y)
    {i j : I} (a : Z ⟶ X i) (b : Z ⟶ X j)
    (ha : a ≫ g i = h ≫ f₁) (hb : b ≫ g j = h ≫ f₂) :
    (F.presheafHom ((F.map f₁.op.toLoc).toFunctor.obj M)
      ((F.map f₂.op.toLoc).toFunctor.obj M)).obj (op (Over.mk h)) :=
  (F.mapComp' f₁.op.toLoc h.op.toLoc (h ≫ f₁).op.toLoc (by grind)).inv.toNatTrans.app M ≫
    localMorCore g q D M e r f₁ f₂ hf₁ hf₂ h a b ha hb ≫
    (F.mapComp' f₂.op.toLoc h.op.toLoc (h ≫ f₂).op.toLoc (by grind)).hom.toNatTrans.app M

set_option backward.isDefEq.respectTransparency false in
lemma localMorCore_unique (D : F.DescentData (fun i ↦ g i ≫ q))
    (M : F.obj (.mk (op T))) (e : (F.toDescentData g).obj M ≅ restrict g q D)
    {Y : C} (r : Y ⟶ S) (f₁ f₂ : Y ⟶ T)
    (hf₁ : f₁ ≫ q = r) (hf₂ : f₂ ≫ q = r)
    {Z : C} (h : Z ⟶ Y)
    {i j i' j' : I} (a : Z ⟶ X i) (b : Z ⟶ X j)
    (a' : Z ⟶ X i') (b' : Z ⟶ X j')
    (ha : a ≫ g i = h ≫ f₁) (hb : b ≫ g j = h ≫ f₂)
    (ha' : a' ≫ g i' = h ≫ f₁) (hb' : b' ≫ g j' = h ≫ f₂) :
    localMorCore g q D M e r f₁ f₂ hf₁ hf₂ h a b ha hb =
      localMorCore g q D M e r f₁ f₂ hf₁ hf₂ h a' b' ha' hb' := by
  have hleft := e.hom.comm (h ≫ f₁) a a' ha ha'
  have hright := e.inv.comm (h ≫ f₂) b' b hb' hb
  dsimp [restrict] at hleft hright
  simp only [Category.assoc, hf₁] at hleft
  simp only [Category.assoc, hf₂] at hright
  have hD : D.hom (h ≫ r) a b
      (by rw [← Category.assoc, ha, Category.assoc, hf₁])
      (by rw [← Category.assoc, hb, Category.assoc, hf₂]) =
      D.hom (h ≫ r) a a'
        (by rw [← Category.assoc, ha, Category.assoc, hf₁])
        (by rw [← Category.assoc, ha', Category.assoc, hf₁]) ≫
      D.hom (h ≫ r) a' b'
        (by rw [← Category.assoc, ha', Category.assoc, hf₁])
        (by rw [← Category.assoc, hb', Category.assoc, hf₂]) ≫
      D.hom (h ≫ r) b' b
        (by rw [← Category.assoc, hb', Category.assoc, hf₂])
        (by rw [← Category.assoc, hb, Category.assoc, hf₂]) := by
    rw [D.hom_comp (h ≫ r) a' b' b, D.hom_comp (h ≫ r) a a' b]
  dsimp [localMorCore]
  rw [hD]
  simp only [Category.assoc]
  rw [reassoc_of% hleft, ← reassoc_of% hright]
  simp

lemma localMor_unique (D : F.DescentData (fun i ↦ g i ≫ q))
    (M : F.obj (.mk (op T))) (e : (F.toDescentData g).obj M ≅ restrict g q D)
    {Y : C} (r : Y ⟶ S) (f₁ f₂ : Y ⟶ T)
    (hf₁ : f₁ ≫ q = r) (hf₂ : f₂ ≫ q = r)
    {Z : C} (h : Z ⟶ Y)
    {i j i' j' : I} (a : Z ⟶ X i) (b : Z ⟶ X j)
    (a' : Z ⟶ X i') (b' : Z ⟶ X j')
    (ha : a ≫ g i = h ≫ f₁) (hb : b ≫ g j = h ≫ f₂)
    (ha' : a' ≫ g i' = h ≫ f₁) (hb' : b' ≫ g j' = h ≫ f₂) :
    localMor g q D M e r f₁ f₂ hf₁ hf₂ h a b ha hb =
      localMor g q D M e r f₁ f₂ hf₁ hf₂ h a' b' ha' hb' := by
  dsimp only [localMor]
  rw [localMorCore_unique g q D M e r f₁ f₂ hf₁ hf₂ h a b a' b' ha hb ha' hb']

set_option backward.isDefEq.respectTransparency false in
lemma localMor_precomp (D : F.DescentData (fun i ↦ g i ≫ q))
    (M : F.obj (.mk (op T))) (e : (F.toDescentData g).obj M ≅ restrict g q D)
    {Y : C} (r : Y ⟶ S) (f₁ f₂ : Y ⟶ T)
    (hf₁ : f₁ ≫ q = r) (hf₂ : f₂ ≫ q = r)
    {Z : C} (h : Z ⟶ Y)
    {i j : I} (a : Z ⟶ X i) (b : Z ⟶ X j)
    (ha : a ≫ g i = h ≫ f₁) (hb : b ≫ g j = h ≫ f₂)
    {Z' : C} (k : Z' ⟶ Z) (h' : Z' ⟶ Y)
    (a' : Z' ⟶ X i) (b' : Z' ⟶ X j)
    (hk : k ≫ h = h') (hka : k ≫ a = a') (hkb : k ≫ b = b') :
    localMor g q D M e r f₁ f₂ hf₁ hf₂ h' a' b'
        (by rw [← hka, Category.assoc, ha, ← Category.assoc, hk])
        (by rw [← hkb, Category.assoc, hb, ← Category.assoc, hk]) =
      (F.presheafHom ((F.map f₁.op.toLoc).toFunctor.obj M)
        ((F.map f₂.op.toLoc).toFunctor.obj M)).map (Over.homMk k).op
          (localMor g q D M e r f₁ f₂ hf₁ hf₂ h a b ha hb) := by
  dsimp [localMor, localMorCore, Pseudofunctor.presheafHom, pullHom]
  rw [← D.pullHom_hom k (h ≫ r) (h' ≫ r) (by rw [← hk, Category.assoc])
    a b (by rw [← Category.assoc, ha, Category.assoc, hf₁])
      (by rw [← Category.assoc, hb, Category.assoc, hf₂])
    a' b' hka hkb]
  simp only [Functor.map_comp, Category.assoc]
  dsimp [pullHom]
  simp only [Functor.map_comp, Category.assoc]
  have hnat₁ := F.mapComp'_hom_naturality a.op.toLoc k.op.toLoc a'.op.toLoc
    (by simp [← hka]) (e.hom.hom i)
  have hnat₂ := F.mapComp'_inv_naturality b.op.toLoc k.op.toLoc b'.op.toLoc
    (by simp [← hkb]) (e.inv.hom j)
  dsimp [restrict] at hnat₁ hnat₂
  rw [reassoc_of% hnat₁, ← reassoc_of% hnat₂]
  rw [F.mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom_app_assoc
      (g i).op.toLoc a.op.toLoc k.op.toLoc
      (f₁.op.toLoc ≫ h.op.toLoc) a'.op.toLoc
      (f₁.op.toLoc ≫ h'.op.toLoc) (by grind) (by grind) (by grind),
    F.mapComp'₀₁₃_inv_comp_mapComp'₀₂₃_hom_app_assoc
      f₁.op.toLoc h.op.toLoc k.op.toLoc
      (f₁.op.toLoc ≫ h.op.toLoc) h'.op.toLoc
      (f₁.op.toLoc ≫ h'.op.toLoc) (by grind) (by grind) (by grind),
    ← F.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app_assoc
      (g j).op.toLoc b.op.toLoc k.op.toLoc
      (f₂.op.toLoc ≫ h.op.toLoc) b'.op.toLoc
      (f₂.op.toLoc ≫ h'.op.toLoc) (by grind) (by grind) (by grind),
    F.mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app
      f₂.op.toLoc h.op.toLoc k.op.toLoc
      (f₂.op.toLoc ≫ h.op.toLoc) h'.op.toLoc
      (f₂.op.toLoc ≫ h'.op.toLoc) (by grind) (by grind) (by grind)]

variable {J : GrothendieckTopology C}

/-- The common local refinement on which two lifts to `T` both factor through `g`. -/
abbrev localSieve {Y : C} (f₁ f₂ : Y ⟶ T) : Sieve (Over.mk (𝟙 Y)) :=
  (Sieve.overEquiv (Over.mk (𝟙 Y))).symm
    (Sieve.pullback f₁ (Sieve.ofArrows X g) ⊓
      Sieve.pullback f₂ (Sieve.ofArrows X g))

lemma localSieve_mem (hg : Sieve.ofArrows X g ∈ J T)
    {Y : C} (f₁ f₂ : Y ⟶ T) : localSieve g f₁ f₂ ∈ J.over Y _ := by
  rw [J.mem_over_iff, OrderIso.apply_symm_apply]
  exact J.intersection_covering (J.pullback_stable f₁ hg) (J.pullback_stable f₂ hg)

namespace localSieve

variable {Y Z : C} {f₁ f₂ : Y ⟶ T} {h : Z ⟶ Y}
  (hh : localSieve g f₁ f₂ (Over.homMk h : Over.mk h ⟶ Over.mk (𝟙 Y)))

include hh in
lemma exists_left : ∃ (i : I) (a : Z ⟶ X i), a ≫ g i = h ≫ f₁ := by
  obtain ⟨⟨_, a, _, ⟨i⟩, ha⟩, -⟩ := hh
  exact ⟨i, a, ha⟩

include hh in
lemma exists_right : ∃ (j : I) (b : Z ⟶ X j), b ≫ g j = h ≫ f₂ := by
  obtain ⟨-, ⟨_, b, _, ⟨j⟩, hb⟩⟩ := hh
  exact ⟨j, b, hb⟩

noncomputable def leftIdx : I := (exists_left g hh).choose

noncomputable def leftHom : Z ⟶ X (leftIdx g hh) := (exists_left g hh).choose_spec.choose

lemma left_fac : leftHom g hh ≫ g (leftIdx g hh) = h ≫ f₁ :=
  (exists_left g hh).choose_spec.choose_spec

noncomputable def rightIdx : I := (exists_right g hh).choose

noncomputable def rightHom : Z ⟶ X (rightIdx g hh) :=
  (exists_right g hh).choose_spec.choose

lemma right_fac : rightHom g hh ≫ g (rightIdx g hh) = h ≫ f₂ :=
  (exists_right g hh).choose_spec.choose_spec

end localSieve

set_option backward.isDefEq.respectTransparency.types false in
/-- The compatible local comparisons on the common refinement sieve. -/
noncomputable def localFamily (D : F.DescentData (fun i ↦ g i ≫ q))
    (M : F.obj (.mk (op T))) (e : (F.toDescentData g).obj M ≅ restrict g q D)
    {Y : C} (r : Y ⟶ S) (f₁ f₂ : Y ⟶ T)
    (hf₁ : f₁ ≫ q = r) (hf₂ : f₂ ≫ q = r) :
    Presieve.FamilyOfElements
      (F.presheafHom ((F.map f₁.op.toLoc).toFunctor.obj M)
        ((F.map f₂.op.toLoc).toFunctor.obj M))
      (localSieve g f₁ f₂).arrows :=
  fun Z h hh ↦
    let hh' : localSieve g f₁ f₂
        (Over.homMk Z.hom : Over.mk Z.hom ⟶ Over.mk (𝟙 Y)) := by
      convert! hh
      ext
      simpa using (Over.w h).symm
    localMor g q D M e r f₁ f₂ hf₁ hf₂ Z.hom
      (localSieve.leftHom g hh') (localSieve.rightHom g hh')
      (localSieve.left_fac g hh') (localSieve.right_fac g hh')

set_option backward.isDefEq.respectTransparency.types false in
lemma localFamily_eq (D : F.DescentData (fun i ↦ g i ≫ q))
    (M : F.obj (.mk (op T))) (e : (F.toDescentData g).obj M ≅ restrict g q D)
    {Y : C} (r : Y ⟶ S) (f₁ f₂ : Y ⟶ T)
    (hf₁ : f₁ ≫ q = r) (hf₂ : f₂ ≫ q = r)
    {Z : Over Y} (h : Z ⟶ Over.mk (𝟙 Y))
    (hh : (localSieve g f₁ f₂).arrows h)
    {i j : I} (a : Z.left ⟶ X i) (b : Z.left ⟶ X j)
    (ha : a ≫ g i = Z.hom ≫ f₁) (hb : b ≫ g j = Z.hom ≫ f₂) :
    localFamily g q D M e r f₁ f₂ hf₁ hf₂ h hh =
      localMor g q D M e r f₁ f₂ hf₁ hf₂ Z.hom a b ha hb := by
  apply localMor_unique

set_option backward.isDefEq.respectTransparency false in
lemma localFamily_compatible (D : F.DescentData (fun i ↦ g i ≫ q))
    (M : F.obj (.mk (op T))) (e : (F.toDescentData g).obj M ≅ restrict g q D)
    {Y : C} (r : Y ⟶ S) (f₁ f₂ : Y ⟶ T)
    (hf₁ : f₁ ≫ q = r) (hf₂ : f₂ ≫ q = r) :
    (localFamily g q D M e r f₁ f₂ hf₁ hf₂).Compatible := by
  intro Y₁ Y₂ Z h₁ h₂ k₁ k₂ hh₁ hh₂ fac
  have hk₁' : k₁ = (Over.homMk Y₁.hom (by simp) : Y₁ ⟶ Over.mk (𝟙 Y)) := by
    ext
    simpa using Over.w k₁
  subst k₁
  obtain rfl : k₂ = (Over.homMk Y₂.hom (by simp) : Y₂ ⟶ Over.mk (𝟙 Y)) := by
    ext
    simpa using Over.w k₂
  obtain ⟨h₁, hk₁, rfl⟩ := Over.homMk_surjective h₁
  obtain ⟨h₂, hk₂, rfl⟩ := Over.homMk_surjective h₂
  dsimp at *
  rw [localFamily_eq g q D M e r f₁ f₂ hf₁ hf₂ _ hh₁
      (localSieve.leftHom g hh₁) (localSieve.rightHom g hh₁)
      (localSieve.left_fac g hh₁) (localSieve.right_fac g hh₁),
    localFamily_eq g q D M e r f₁ f₂ hf₁ hf₂ _ hh₂
      (localSieve.leftHom g hh₂) (localSieve.rightHom g hh₂)
      (localSieve.left_fac g hh₂) (localSieve.right_fac g hh₂)]
  have hp₁ := localMor_precomp g q D M e r f₁ f₂ hf₁ hf₂ Y₁.hom
    (localSieve.leftHom g hh₁) (localSieve.rightHom g hh₁)
    (localSieve.left_fac g hh₁) (localSieve.right_fac g hh₁)
    h₁ Z.hom (h₁ ≫ localSieve.leftHom g hh₁)
    (h₁ ≫ localSieve.rightHom g hh₁) hk₁ rfl rfl
  have hp₂ := localMor_precomp g q D M e r f₁ f₂ hf₁ hf₂ Y₂.hom
    (localSieve.leftHom g hh₂) (localSieve.rightHom g hh₂)
    (localSieve.left_fac g hh₂) (localSieve.right_fac g hh₂)
    h₂ Z.hom (h₂ ≫ localSieve.leftHom g hh₂)
    (h₂ ≫ localSieve.rightHom g hh₂) hk₂ rfl rfl
  dsimp [Pseudofunctor.presheafHom] at hp₁ hp₂
  rw [← hp₁, ← hp₂]
  apply localMor_unique

lemma mem_localSieve {Y Z : C} (f₁ f₂ : Y ⟶ T) (h : Z ⟶ Y)
    {i j : I} (a : Z ⟶ X i) (b : Z ⟶ X j)
    (ha : a ≫ g i = h ≫ f₁) (hb : b ≫ g j = h ≫ f₂) :
    localSieve g f₁ f₂ (Over.homMk h : Over.mk h ⟶ Over.mk (𝟙 Y)) :=
  ⟨⟨_, a, _, ⟨i⟩, ha⟩, ⟨_, b, _, ⟨j⟩, hb⟩⟩

variable [F.IsPrestack J]

set_option backward.isDefEq.respectTransparency.types false in
/-- The comparison between two pullbacks of the glued object, obtained by sheaf gluing. -/
noncomputable def gluedHom (hg : Sieve.ofArrows X g ∈ J T)
    (D : F.DescentData (fun i ↦ g i ≫ q))
    (M : F.obj (.mk (op T))) (e : (F.toDescentData g).obj M ≅ restrict g q D)
    {Y : C} (r : Y ⟶ S) (f₁ f₂ : Y ⟶ T)
    (hf₁ : f₁ ≫ q = r) (hf₂ : f₂ ≫ q = r) :
    (F.map f₁.op.toLoc).toFunctor.obj M ⟶ (F.map f₂.op.toLoc).toFunctor.obj M :=
  F.presheafHomObjHomEquiv.symm
    (Presieve.IsSheafFor.amalgamate
      (((isSheaf_iff_isSheaf_of_type _ _).1
        (IsPrestack.isSheaf J ((F.map f₁.op.toLoc).toFunctor.obj M)
          ((F.map f₂.op.toLoc).toFunctor.obj M))).isSheafFor _
            (by simpa using localSieve_mem g hg f₁ f₂)) _
        (localFamily_compatible g q D M e r f₁ f₂ hf₁ hf₂))

set_option backward.isDefEq.respectTransparency false in
lemma map_gluedHom (hg : Sieve.ofArrows X g ∈ J T)
    (D : F.DescentData (fun i ↦ g i ≫ q))
    (M : F.obj (.mk (op T))) (e : (F.toDescentData g).obj M ≅ restrict g q D)
    {Y : C} (r : Y ⟶ S) (f₁ f₂ : Y ⟶ T)
    (hf₁ : f₁ ≫ q = r) (hf₂ : f₂ ≫ q = r)
    {Z : C} (h : Z ⟶ Y) {i j : I} (a : Z ⟶ X i) (b : Z ⟶ X j)
    (ha : a ≫ g i = h ≫ f₁) (hb : b ≫ g j = h ≫ f₂) :
    (F.map h.op.toLoc).toFunctor.map
      (gluedHom g q hg D M e r f₁ f₂ hf₁ hf₂) =
        localMor g q D M e r f₁ f₂ hf₁ hf₂ h a b ha hb := by
  let s := Presieve.IsSheafFor.amalgamate
    (((isSheaf_iff_isSheaf_of_type _ _).1
      (IsPrestack.isSheaf J ((F.map f₁.op.toLoc).toFunctor.obj M)
        ((F.map f₂.op.toLoc).toFunctor.obj M))).isSheafFor _
          (by simpa using localSieve_mem g hg f₁ f₂)) _
      (localFamily_compatible g q D M e r f₁ f₂ hf₁ hf₂)
  have hs : (localFamily g q D M e r f₁ f₂ hf₁ hf₂).IsAmalgamation s :=
    Presieve.IsSheafFor.isAmalgamation
      (((isSheaf_iff_isSheaf_of_type _ _).1
        (IsPrestack.isSheaf J ((F.map f₁.op.toLoc).toFunctor.obj M)
          ((F.map f₂.op.toLoc).toFunctor.obj M))).isSheafFor _
            (by simpa using localSieve_mem g hg f₁ f₂))
      (localFamily_compatible g q D M e r f₁ f₂ hf₁ hf₂)
  simpa [s, gluedHom, localFamily_eq g q D M e r f₁ f₂ hf₁ hf₂
      (Over.homMk h (by simp) : Over.mk h ⟶ Over.mk (𝟙 Y))
      (mem_localSieve g f₁ f₂ h a b ha hb) a b ha hb,
    presheafHomObjHomEquiv, pullHom, mapComp'_id_comp_hom_app,
    mapComp'_id_comp_inv_app] using
      hs (Over.homMk h (by simp) : Over.mk h ⟶ Over.mk (𝟙 Y))
        (mem_localSieve g f₁ f₂ h a b ha hb)

set_option backward.isDefEq.respectTransparency false in
lemma localMorCore_self (D : F.DescentData (fun i ↦ g i ≫ q))
    (M : F.obj (.mk (op T))) (e : (F.toDescentData g).obj M ≅ restrict g q D)
    {Y : C} (r : Y ⟶ S) (f : Y ⟶ T) (hf : f ≫ q = r)
    {Z : C} (h : Z ⟶ Y) {i : I} (a : Z ⟶ X i)
    (ha : a ≫ g i = h ≫ f) :
    localMorCore g q D M e r f f hf hf h a a ha ha = 𝟙 _ := by
  let ei : ((F.toDescentData g).obj M).obj i ≅ (restrict g q D).obj i :=
    { hom := e.hom.hom i
      inv := e.inv.hom i
      hom_inv_id := congr_fun (congr_arg DescentData.Hom.hom e.hom_inv_id) i
      inv_hom_id := congr_fun (congr_arg DescentData.Hom.hom e.inv_hom_id) i }
  dsimp [localMorCore]
  rw [D.hom_self (h ≫ r) a
    (by rw [← Category.assoc, ha, Category.assoc, hf])]
  let B := F.mapComp' (g i).op.toLoc a.op.toLoc
    (f.op.toLoc ≫ h.op.toLoc) (by grind)
  change B.hom.toNatTrans.app M ≫
      (F.map a.op.toLoc).toFunctor.map (e.hom.hom i) ≫ 𝟙 _ ≫
      (F.map a.op.toLoc).toFunctor.map (e.inv.hom i) ≫
      B.inv.toNatTrans.app M = 𝟙 _
  have hea := ((F.map a.op.toLoc).toFunctor.mapIso ei).hom_inv_id
  dsimp [ei] at hea
  rw [Category.id_comp, reassoc_of% hea]
  simp

set_option backward.isDefEq.respectTransparency false in
lemma localMorCore_comp (D : F.DescentData (fun i ↦ g i ≫ q))
    (M : F.obj (.mk (op T))) (e : (F.toDescentData g).obj M ≅ restrict g q D)
    {Y : C} (r : Y ⟶ S) (f₁ f₂ f₃ : Y ⟶ T)
    (hf₁ : f₁ ≫ q = r) (hf₂ : f₂ ≫ q = r) (hf₃ : f₃ ≫ q = r)
    {Z : C} (h : Z ⟶ Y) {i j k : I}
    (a : Z ⟶ X i) (b : Z ⟶ X j) (c : Z ⟶ X k)
    (ha : a ≫ g i = h ≫ f₁) (hb : b ≫ g j = h ≫ f₂)
    (hc : c ≫ g k = h ≫ f₃) :
    localMorCore g q D M e r f₁ f₂ hf₁ hf₂ h a b ha hb ≫
      localMorCore g q D M e r f₂ f₃ hf₂ hf₃ h b c hb hc =
        localMorCore g q D M e r f₁ f₃ hf₁ hf₃ h a c ha hc := by
  let ej : ((F.toDescentData g).obj M).obj j ≅ (restrict g q D).obj j :=
    { hom := e.hom.hom j
      inv := e.inv.hom j
      hom_inv_id := congr_fun (congr_arg DescentData.Hom.hom e.hom_inv_id) j
      inv_hom_id := congr_fun (congr_arg DescentData.Hom.hom e.inv_hom_id) j }
  dsimp [localMorCore]
  simp only [Category.assoc, Cat.Hom.inv_hom_id_toNatTrans_app_assoc]
  have heb := ((F.map b.op.toLoc).toFunctor.mapIso ej).inv_hom_id
  dsimp [ej] at heb
  rw [reassoc_of% heb]
  have hD := D.hom_comp (h ≫ r) a b c
    (by rw [← Category.assoc, ha, Category.assoc, hf₁])
    (by rw [← Category.assoc, hb, Category.assoc, hf₂])
    (by rw [← Category.assoc, hc, Category.assoc, hf₃])
  rw [reassoc_of% hD]

set_option backward.isDefEq.respectTransparency false in
lemma localMor_self (D : F.DescentData (fun i ↦ g i ≫ q))
    (M : F.obj (.mk (op T))) (e : (F.toDescentData g).obj M ≅ restrict g q D)
    {Y : C} (r : Y ⟶ S) (f : Y ⟶ T) (hf : f ≫ q = r)
    {Z : C} (h : Z ⟶ Y) {i : I} (a : Z ⟶ X i)
    (ha : a ≫ g i = h ≫ f) :
    localMor g q D M e r f f hf hf h a a ha ha = 𝟙 _ := by
  dsimp only [localMor]
  rw [localMorCore_self g q D M e r f hf h a ha]
  simp

set_option backward.isDefEq.respectTransparency false in
lemma localMor_comp (D : F.DescentData (fun i ↦ g i ≫ q))
    (M : F.obj (.mk (op T))) (e : (F.toDescentData g).obj M ≅ restrict g q D)
    {Y : C} (r : Y ⟶ S) (f₁ f₂ f₃ : Y ⟶ T)
    (hf₁ : f₁ ≫ q = r) (hf₂ : f₂ ≫ q = r) (hf₃ : f₃ ≫ q = r)
    {Z : C} (h : Z ⟶ Y) {i j k : I}
    (a : Z ⟶ X i) (b : Z ⟶ X j) (c : Z ⟶ X k)
    (ha : a ≫ g i = h ≫ f₁) (hb : b ≫ g j = h ≫ f₂)
    (hc : c ≫ g k = h ≫ f₃) :
    localMor g q D M e r f₁ f₂ hf₁ hf₂ h a b ha hb ≫
      localMor g q D M e r f₂ f₃ hf₂ hf₃ h b c hb hc =
        localMor g q D M e r f₁ f₃ hf₁ hf₃ h a c ha hc := by
  dsimp only [localMor]
  simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc]
  have hc' := localMorCore_comp g q D M e r f₁ f₂ f₃
    hf₁ hf₂ hf₃ h a b c ha hb hc
  rw [reassoc_of% hc']

set_option backward.isDefEq.respectTransparency false in
lemma hom_ext_of_sieve {Y : C} (R : Sieve (Over.mk (𝟙 Y))) (hR : R ∈ J.over Y _)
    {A B : F.obj (.mk (op Y))} {u v : A ⟶ B}
    (huv : ∀ {Z : C} (h : Z ⟶ Y),
      R (Over.homMk h : Over.mk h ⟶ Over.mk (𝟙 Y)) →
        (F.map h.op.toLoc).toFunctor.map u = (F.map h.op.toLoc).toFunctor.map v) :
    u = v := by
  refine F.presheafHomObjHomEquiv.injective ?_
  refine (((isSheaf_iff_isSheaf_of_type _ _).1
    (IsPrestack.isSheaf J A B)).isSeparated _ hR).ext ?_
  rintro Z h hh
  obtain rfl : h = (Over.homMk Z.hom (by simp) : Z ⟶ Over.mk (𝟙 Y)) := by
    ext
    simpa using Over.w h
  have hmap := huv Z.hom hh
  dsimp [presheafHomObjHomEquiv, Pseudofunctor.presheafHom, pullHom]
  simp only [Functor.map_comp, Category.assoc]
  rw [hmap]

set_option backward.isDefEq.respectTransparency false in
lemma hom_ext_of_map_eq (hg : Sieve.ofArrows X g ∈ J T)
    {Y : C} (f₁ f₂ : Y ⟶ T) (M : F.obj (.mk (op T)))
    {u v : (F.map f₁.op.toLoc).toFunctor.obj M ⟶
      (F.map f₂.op.toLoc).toFunctor.obj M}
    (huv : ∀ {Z : C} (h : Z ⟶ Y) {i j : I} (a : Z ⟶ X i) (b : Z ⟶ X j)
      (_ : a ≫ g i = h ≫ f₁) (_ : b ≫ g j = h ≫ f₂),
      (F.map h.op.toLoc).toFunctor.map u = (F.map h.op.toLoc).toFunctor.map v) :
    u = v := by
  apply hom_ext_of_sieve (J := J) (localSieve g f₁ f₂) (localSieve_mem g hg f₁ f₂)
  intro Z h hh
  obtain ⟨⟨_, a, _, ⟨i⟩, ha⟩, ⟨_, b, _, ⟨j⟩, hb⟩⟩ := hh
  exact huv h a b ha hb

/-- A common local refinement on which three lifts to `T` factor through `g`. -/
abbrev localSieve₃ {Y : C} (f₁ f₂ f₃ : Y ⟶ T) : Sieve (Over.mk (𝟙 Y)) :=
  (Sieve.overEquiv (Over.mk (𝟙 Y))).symm
    ((Sieve.pullback f₁ (Sieve.ofArrows X g) ⊓
      Sieve.pullback f₂ (Sieve.ofArrows X g)) ⊓
        Sieve.pullback f₃ (Sieve.ofArrows X g))

lemma localSieve₃_mem (hg : Sieve.ofArrows X g ∈ J T)
    {Y : C} (f₁ f₂ f₃ : Y ⟶ T) : localSieve₃ g f₁ f₂ f₃ ∈ J.over Y _ := by
  rw [J.mem_over_iff, OrderIso.apply_symm_apply]
  exact J.intersection_covering
    (J.intersection_covering (J.pullback_stable f₁ hg) (J.pullback_stable f₂ hg))
    (J.pullback_stable f₃ hg)

set_option backward.isDefEq.respectTransparency false in
lemma gluedHom_self (hg : Sieve.ofArrows X g ∈ J T)
    (D : F.DescentData (fun i ↦ g i ≫ q))
    (M : F.obj (.mk (op T))) (e : (F.toDescentData g).obj M ≅ restrict g q D)
    {Y : C} (r : Y ⟶ S) (f : Y ⟶ T) (hf : f ≫ q = r) :
    gluedHom g q hg D M e r f f hf hf = 𝟙 _ := by
  apply hom_ext_of_map_eq g hg f f M
  intro Z h i j a b ha hb
  rw [map_gluedHom g q hg D M e r f f hf hf h a b ha hb, Functor.map_id]
  rw [localMor_unique g q D M e r f f hf hf h a b a a ha hb ha ha]
  exact localMor_self g q D M e r f hf h a ha

set_option backward.isDefEq.respectTransparency false in
lemma gluedHom_comp (hg : Sieve.ofArrows X g ∈ J T)
    (D : F.DescentData (fun i ↦ g i ≫ q))
    (M : F.obj (.mk (op T))) (e : (F.toDescentData g).obj M ≅ restrict g q D)
    {Y : C} (r : Y ⟶ S) (f₁ f₂ f₃ : Y ⟶ T)
    (hf₁ : f₁ ≫ q = r) (hf₂ : f₂ ≫ q = r) (hf₃ : f₃ ≫ q = r) :
    gluedHom g q hg D M e r f₁ f₂ hf₁ hf₂ ≫
      gluedHom g q hg D M e r f₂ f₃ hf₂ hf₃ =
        gluedHom g q hg D M e r f₁ f₃ hf₁ hf₃ := by
  apply hom_ext_of_sieve (J := J) (localSieve₃ g f₁ f₂ f₃)
    (localSieve₃_mem g hg f₁ f₂ f₃)
  intro Z h hh
  obtain ⟨⟨⟨_, a, _, ⟨i⟩, ha⟩, ⟨_, b, _, ⟨j⟩, hb⟩⟩,
    ⟨_, c, _, ⟨k⟩, hc⟩⟩ := hh
  rw [Functor.map_comp,
    map_gluedHom g q hg D M e r f₁ f₂ hf₁ hf₂ h a b ha hb,
    map_gluedHom g q hg D M e r f₂ f₃ hf₂ hf₃ h b c hb hc,
    map_gluedHom g q hg D M e r f₁ f₃ hf₁ hf₃ h a c ha hc,
    localMor_comp g q D M e r f₁ f₂ f₃ hf₁ hf₂ hf₃ h a b c ha hb hc]

set_option backward.isDefEq.respectTransparency false in
lemma pullHom_gluedHom (hg : Sieve.ofArrows X g ∈ J T)
    (D : F.DescentData (fun i ↦ g i ≫ q))
    (M : F.obj (.mk (op T))) (e : (F.toDescentData g).obj M ≅ restrict g q D)
    {Y' Y : C} (k : Y' ⟶ Y) (r : Y ⟶ S) (r' : Y' ⟶ S) (hr : k ≫ r = r')
    (f₁ f₂ : Y ⟶ T) (hf₁ : f₁ ≫ q = r) (hf₂ : f₂ ≫ q = r)
    (f₁' f₂' : Y' ⟶ T) (hk₁ : k ≫ f₁ = f₁') (hk₂ : k ≫ f₂ = f₂') :
    pullHom (gluedHom g q hg D M e r f₁ f₂ hf₁ hf₂) k f₁' f₂' hk₁ hk₂ =
      gluedHom g q hg D M e r' f₁' f₂'
        (by rw [← hk₁, Category.assoc, hf₁, hr])
        (by rw [← hk₂, Category.assoc, hf₂, hr]) := by
  subst f₁'
  subst f₂'
  subst r'
  apply hom_ext_of_map_eq g hg (k ≫ f₁) (k ≫ f₂) M
  intro Z h i j a b ha hb
  rw [map_gluedHom g q hg D M e (k ≫ r) (k ≫ f₁) (k ≫ f₂)
    (by rw [Category.assoc, hf₁])
    (by rw [Category.assoc, hf₂]) h a b ha hb]
  dsimp [pullHom]
  simp only [Functor.map_comp, Category.assoc]
  rw [← F.mapComp'_naturality_1 k.op.toLoc h.op.toLoc (h ≫ k).op.toLoc
    (by grind) (gluedHom g q hg D M e r f₁ f₂ hf₁ hf₂)]
  rw [map_gluedHom g q hg D M e r f₁ f₂ hf₁ hf₂ (h ≫ k) a b
    (by rw [ha, ← Category.assoc])
    (by rw [hb, ← Category.assoc])]
  dsimp [localMor, localMorCore]
  simp only [Category.assoc]
  rw [
    ← F.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app_assoc
      f₁.op.toLoc k.op.toLoc h.op.toLoc
      (k ≫ f₁).op.toLoc (k.op.toLoc ≫ h.op.toLoc)
      (f₁.op.toLoc ≫ k.op.toLoc ≫ h.op.toLoc) (by simp) rfl (by simp),
    ← F.mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight_app_assoc
      f₂.op.toLoc k.op.toLoc h.op.toLoc
      (k ≫ f₂).op.toLoc (k.op.toLoc ≫ h.op.toLoc)
      (f₂.op.toLoc ≫ k.op.toLoc ≫ h.op.toLoc) (by simp) rfl (by simp)]
  have hfk₁ : f₁.op.toLoc ≫ k.op.toLoc = (k ≫ f₁).op.toLoc := by simp
  have hfk₂ : f₂.op.toLoc ≫ k.op.toLoc = (k ≫ f₂).op.toLoc := by simp
  have hcancel₁ :
      (F.mapComp' f₁.op.toLoc k.op.toLoc (f₁.op.toLoc ≫ k.op.toLoc) rfl).hom.toNatTrans.app M ≫
        (F.mapComp' f₁.op.toLoc k.op.toLoc (k ≫ f₁).op.toLoc hfk₁).inv.toNatTrans.app M =
          𝟙 _ := by
    exact Cat.Hom.hom_inv_id_toNatTrans_app
      (F.mapComp' f₁.op.toLoc k.op.toLoc (k ≫ f₁).op.toLoc hfk₁) M
  have hcancel₂ :
      (F.mapComp' f₂.op.toLoc k.op.toLoc (k ≫ f₂).op.toLoc hfk₂).hom.toNatTrans.app M ≫
        (F.mapComp' f₂.op.toLoc k.op.toLoc (f₂.op.toLoc ≫ k.op.toLoc) rfl).inv.toNatTrans.app M =
          𝟙 _ := by
    exact Cat.Hom.hom_inv_id_toNatTrans_app
      (F.mapComp' f₂.op.toLoc k.op.toLoc (k ≫ f₂).op.toLoc hfk₂) M
  rw [← Functor.map_comp, ← Functor.map_comp_assoc]
  rw [hcancel₁, hcancel₂, Functor.map_id]
  rw [Functor.map_id]
  simp only [Category.id_comp, Category.comp_id]
  have H₁ := mapComp'_inv_app_heq (F := F)
    (f := (k ≫ f₁).op.toLoc) (f' := f₁.op.toLoc ≫ k.op.toLoc)
    (h := h.op.toLoc) (h' := h.op.toLoc)
    (fh := f₁.op.toLoc ≫ k.op.toLoc ≫ h.op.toLoc)
    (fh' := (f₁.op.toLoc ≫ k.op.toLoc) ≫ h.op.toLoc)
    hfk₁.symm rfl (Category.assoc _ _ _).symm
    (by
      calc
        (k ≫ f₁).op.toLoc ≫ h.op.toLoc =
            (f₁.op.toLoc ≫ k.op.toLoc) ≫ h.op.toLoc :=
          congrArg (fun z ↦ z ≫ h.op.toLoc) hfk₁.symm
        _ = _ := Category.assoc _ _ _)
    rfl M
  have hga : (g i).op.toLoc ≫ a.op.toLoc =
      f₁.op.toLoc ≫ k.op.toLoc ≫ h.op.toLoc := by
    simpa only [op_comp, Quiver.Hom.comp_toLoc, Category.assoc] using
      congrArg (fun z ↦ z.op.toLoc) ha
  have H₂ := mapComp'_hom_app_heq (F := F)
    (f := (g i).op.toLoc) (f' := (g i).op.toLoc)
    (h := a.op.toLoc) (h' := a.op.toLoc)
    (fh := f₁.op.toLoc ≫ k.op.toLoc ≫ h.op.toLoc)
    (fh' := (f₁.op.toLoc ≫ k.op.toLoc) ≫ h.op.toLoc)
    rfl rfl (Category.assoc _ _ _).symm
    hga (hga.trans (Category.assoc _ _ _).symm) M
  have hgb : (g j).op.toLoc ≫ b.op.toLoc =
      f₂.op.toLoc ≫ k.op.toLoc ≫ h.op.toLoc := by
    simpa only [op_comp, Quiver.Hom.comp_toLoc, Category.assoc] using
      congrArg (fun z ↦ z.op.toLoc) hb
  have H₃ := mapComp'_inv_app_heq (F := F)
    (f := (g j).op.toLoc) (f' := (g j).op.toLoc)
    (h := b.op.toLoc) (h' := b.op.toLoc)
    (fh := f₂.op.toLoc ≫ k.op.toLoc ≫ h.op.toLoc)
    (fh' := (f₂.op.toLoc ≫ k.op.toLoc) ≫ h.op.toLoc)
    rfl rfl (Category.assoc _ _ _).symm
    hgb (hgb.trans (Category.assoc _ _ _).symm) M
  have H₄ := mapComp'_hom_app_heq (F := F)
    (f := (k ≫ f₂).op.toLoc) (f' := f₂.op.toLoc ≫ k.op.toLoc)
    (h := h.op.toLoc) (h' := h.op.toLoc)
    (fh := f₂.op.toLoc ≫ k.op.toLoc ≫ h.op.toLoc)
    (fh' := (f₂.op.toLoc ≫ k.op.toLoc) ≫ h.op.toLoc)
    hfk₂.symm rfl (Category.assoc _ _ _).symm
    (by
      calc
        (k ≫ f₂).op.toLoc ≫ h.op.toLoc =
            (f₂.op.toLoc ≫ k.op.toLoc) ≫ h.op.toLoc :=
          congrArg (fun z ↦ z ≫ h.op.toLoc) hfk₂.symm
        _ = _ := Category.assoc _ _ _)
    rfl M
  have Ecomp₁ :
      (F.map (k ≫ f₁).op.toLoc ≫ F.map h.op.toLoc).toFunctor.obj M =
        (F.map (f₁.op.toLoc ≫ k.op.toLoc) ≫ F.map h.op.toLoc).toFunctor.obj M :=
    congrArg (fun z ↦ (F.map z ≫ F.map h.op.toLoc).toFunctor.obj M) hfk₁.symm
  have Eassoc₁ :
      (F.map (f₁.op.toLoc ≫ k.op.toLoc ≫ h.op.toLoc)).toFunctor.obj M =
        (F.map ((f₁.op.toLoc ≫ k.op.toLoc) ≫ h.op.toLoc)).toFunctor.obj M := by
    rw [Category.assoc]
  have Eassoc₂ :
      (F.map (f₂.op.toLoc ≫ k.op.toLoc ≫ h.op.toLoc)).toFunctor.obj M =
        (F.map ((f₂.op.toLoc ≫ k.op.toLoc) ≫ h.op.toLoc)).toFunctor.obj M := by
    rw [Category.assoc]
  have Ecomp₂ :
      (F.map (k ≫ f₂).op.toLoc ≫ F.map h.op.toLoc).toFunctor.obj M =
        (F.map (f₂.op.toLoc ≫ k.op.toLoc) ≫ F.map h.op.toLoc).toFunctor.obj M :=
    congrArg (fun z ↦ (F.map z ≫ F.map h.op.toLoc).toFunctor.obj M) hfk₂.symm
  let K := (F.map a.op.toLoc).toFunctor.map (e.hom.hom i) ≫
    D.hom (h ≫ k ≫ r) a b
      (by rw [← Category.assoc a (g i) q, ha,
        ← Category.assoc h k f₁, Category.assoc (h ≫ k) f₁ q,
        hf₁, Category.assoc h k r])
      (by rw [← Category.assoc b (g j) q, hb,
        ← Category.assoc h k f₂, Category.assoc (h ≫ k) f₂ q,
        hf₂, Category.assoc h k r]) ≫
    (F.map b.op.toLoc).toFunctor.map (e.inv.hom j)
  have H₂K := heq_comp Eassoc₁ rfl rfl H₂ (HEq.rfl : K ≍ K)
  have H₃₄ := heq_comp rfl Eassoc₂ Ecomp₂ H₃ H₄
  have Htail := heq_comp Eassoc₁ rfl Ecomp₂ H₂K H₃₄
  exact eq_of_heq (heq_comp Ecomp₁ Eassoc₁ Ecomp₂ H₁
    (by simpa only [K, Category.assoc] using Htail))

/-- The singleton descent datum obtained by gluing the restriction of composite
descent data along the covering family `g`. -/
noncomputable def singletonDatum (hg : Sieve.ofArrows X g ∈ J T)
    (D : F.DescentData (fun i ↦ g i ≫ q))
    (M : F.obj (.mk (op T))) (e : (F.toDescentData g).obj M ≅ restrict g q D) :
    F.DescentData (fun _ : Unit ↦ q) where
  obj _ := M
  hom Y r _ _ f₁ f₂ hf₁ hf₂ :=
    gluedHom g q hg D M e r f₁ f₂ hf₁ hf₂
  pullHom_hom Y' Y k r r' hr _ _ f₁ f₂ hf₁ hf₂ f₁' f₂' hk₁ hk₂ :=
    pullHom_gluedHom g q hg D M e k r r' hr f₁ f₂ hf₁ hf₂ f₁' f₂' hk₁ hk₂
  hom_self Y r _ f hf := gluedHom_self g q hg D M e r f hf
  hom_comp Y r _ _ _ f₁ f₂ f₃ hf₁ hf₂ hf₃ :=
    gluedHom_comp g q hg D M e r f₁ f₂ f₃ hf₁ hf₂ hf₃

noncomputable def singletonPullbackIso (hg : Sieve.ofArrows X g ∈ J T)
    (D : F.DescentData (fun i ↦ g i ≫ q))
    (M : F.obj (.mk (op T))) (e : (F.toDescentData g).obj M ≅ restrict g q D) :
    (DescentData.pullFunctor F (f := fun _ : Unit ↦ q) (p := 𝟙 S)
      (f' := fun i ↦ g i ≫ q) (α := fun _ ↦ ()) (p' := g) (fun i ↦ by simp)).obj
        (singletonDatum g q hg D M e) ≅ D :=
  DescentData.isoMk
    (fun i ↦
      { hom := e.hom.hom i
        inv := e.inv.hom i
        hom_inv_id := congr_fun (congr_arg DescentData.Hom.hom e.hom_inv_id) i
        inv_hom_id := congr_fun (congr_arg DescentData.Hom.hom e.inv_hom_id) i })
    (by
      intro Y r i₁ i₂ a b ha hb
      let w : ∀ i, g i ≫ q = (g i ≫ q) ≫ 𝟙 S := fun i ↦ by simp
      dsimp only [DescentData.pullFunctor, DescentData.pullFunctorObj]
      rw [DescentData.pullFunctorObjHom_eq _ _
        (a ≫ g i₁ ≫ q) a b r (a ≫ g i₁) (b ≫ g i₂)
        (by simp [Category.assoc]) (by rw [hb, ha])
        (by simpa using ha) rfl rfl]
      dsimp only [singletonDatum]
      have hfa : (a ≫ g i₁) ≫ q = r := by simpa only [Category.assoc] using ha
      have hfb : (b ≫ g i₂) ≫ q = r := by simpa only [Category.assoc] using hb
      let G := gluedHom g q hg D M e r (a ≫ g i₁) (b ≫ g i₂) hfa hfb
      have hm := map_gluedHom g q hg D M e r (a ≫ g i₁) (b ≫ g i₂)
        hfa hfb (𝟙 Y) a b (by simp) (by simp)
      have hp := map_eq_pullHom (F := F) G (𝟙 Y)
        (a ≫ g i₁) (b ≫ g i₂) (by simp) (by simp)
      rw [pullHom_id] at hp
      have hG : G =
          (F.mapComp' (a ≫ g i₁).op.toLoc (𝟙 Y).op.toLoc
            (a ≫ g i₁).op.toLoc (by simp)).hom.toNatTrans.app M ≫
          (F.map (𝟙 Y).op.toLoc).toFunctor.map G ≫
          (F.mapComp' (b ≫ g i₂).op.toLoc (𝟙 Y).op.toLoc
            (b ≫ g i₂).op.toLoc (by simp)).inv.toNatTrans.app M := by
        rw [hp]
        simp
      dsimp only [G] at hG hm
      rw [hG]
      rw [hm]
      dsimp [localMor, localMorCore]
      simp only [Category.assoc, Cat.Hom.inv_hom_id_toNatTrans_app_assoc,
        Cat.Hom.hom_inv_id_toNatTrans_app_assoc]
      let idY : LocallyDiscrete.mk (op Y) ⟶ LocallyDiscrete.mk (op Y) := 𝟙 _
      let c₁ := (g i₁).op.toLoc ≫ a.op.toLoc
      let A₁ := F.mapComp' (g i₁).op.toLoc a.op.toLoc c₁ rfl
      let B₁ := F.mapComp' c₁ idY c₁ (Category.comp_id c₁)
      let C₁ := F.mapComp' c₁ idY (c₁ ≫ idY) rfl
      let D₁ := F.mapComp' (g i₁).op.toLoc a.op.toLoc (c₁ ≫ idY)
        (Category.comp_id c₁).symm
      have hc₁ : c₁ ≫ idY = c₁ := Category.comp_id c₁
      have EC₁ : (F.map (c₁ ≫ idY)).toFunctor.obj M =
          (F.map c₁).toFunctor.obj M :=
        congrArg (fun z ↦ (F.map z).toFunctor.obj M) hc₁
      have HC₁ := mapComp'_inv_app_heq (F := F)
        (f := c₁) (f' := c₁) (h := idY) (h' := idY)
        (fh := c₁ ≫ idY) (fh' := c₁) rfl rfl hc₁ rfl hc₁ M
      have HD₁ := mapComp'_hom_app_heq (F := F)
        (f := (g i₁).op.toLoc) (f' := (g i₁).op.toLoc)
        (h := a.op.toLoc) (h' := a.op.toLoc)
        (fh := c₁ ≫ idY) (fh' := c₁) rfl rfl hc₁ hc₁.symm rfl M
      let P₁ := A₁.inv.toNatTrans.app M ≫ B₁.hom.toNatTrans.app M
      let R₁ := C₁.inv.toNatTrans.app M ≫ D₁.hom.toNatTrans.app M
      let R₁' := B₁.inv.toNatTrans.app M ≫ A₁.hom.toNatTrans.app M
      have HR₁ : R₁ ≍ R₁' := heq_comp rfl EC₁ rfl HC₁ HD₁
      have HPR₁ : P₁ ≫ R₁ ≍ P₁ ≫ R₁' :=
        heq_comp rfl rfl rfl HEq.rfl HR₁
      have hleft : P₁ ≫ R₁ = 𝟙 _ := by
        rw [eq_of_heq HPR₁]
        dsimp [P₁, R₁', A₁, B₁]
        simp
      have hleft' :
          A₁.inv.toNatTrans.app M ≫ B₁.hom.toNatTrans.app M ≫
            C₁.inv.toNatTrans.app M ≫ D₁.hom.toNatTrans.app M = 𝟙 _ := by
        simpa only [P₁, R₁, Category.assoc] using hleft
      let c₂ := (g i₂).op.toLoc ≫ b.op.toLoc
      let A₂ := F.mapComp' (g i₂).op.toLoc b.op.toLoc c₂ rfl
      let B₂ := F.mapComp' c₂ idY c₂ (Category.comp_id c₂)
      let C₂ := F.mapComp' c₂ idY (c₂ ≫ idY) rfl
      let D₂ := F.mapComp' (g i₂).op.toLoc b.op.toLoc (c₂ ≫ idY)
        (Category.comp_id c₂).symm
      have hc₂ : c₂ ≫ idY = c₂ := Category.comp_id c₂
      have EC₂ : (F.map (c₂ ≫ idY)).toFunctor.obj M =
          (F.map c₂).toFunctor.obj M :=
        congrArg (fun z ↦ (F.map z).toFunctor.obj M) hc₂
      have HD₂ := mapComp'_inv_app_heq (F := F)
        (f := (g i₂).op.toLoc) (f' := (g i₂).op.toLoc)
        (h := b.op.toLoc) (h' := b.op.toLoc)
        (fh := c₂ ≫ idY) (fh' := c₂) rfl rfl hc₂ hc₂.symm rfl M
      have HC₂ := mapComp'_hom_app_heq (F := F)
        (f := c₂) (f' := c₂) (h := idY) (h' := idY)
        (fh := c₂ ≫ idY) (fh' := c₂) rfl rfl hc₂ rfl hc₂ M
      let P₂ := D₂.inv.toNatTrans.app M ≫ C₂.hom.toNatTrans.app M
      let P₂' := A₂.inv.toNatTrans.app M ≫ B₂.hom.toNatTrans.app M
      let R₂ := B₂.inv.toNatTrans.app M ≫ A₂.hom.toNatTrans.app M
      have HP₂ : P₂ ≍ P₂' := heq_comp rfl EC₂ rfl HD₂ HC₂
      have HPR₂ : P₂ ≫ R₂ ≍ P₂' ≫ R₂ :=
        heq_comp rfl rfl rfl HP₂ HEq.rfl
      have hright : P₂ ≫ R₂ = 𝟙 _ := by
        rw [eq_of_heq HPR₂]
        dsimp [P₂', R₂, A₂, B₂]
        simp
      have hright' :
          D₂.inv.toNatTrans.app M ≫ C₂.hom.toNatTrans.app M ≫
            B₂.inv.toNatTrans.app M ≫ A₂.hom.toNatTrans.app M = 𝟙 _ := by
        simpa only [P₂, R₂, Category.assoc] using hright
      dsimp [A₁, B₁, C₁, D₁, c₁, idY] at hleft'
      dsimp [A₂, B₂, C₂, D₂, c₂, idY] at hright'
      rw [reassoc_of% hleft', reassoc_of% hright']
      let ei₂ : ((F.toDescentData g).obj M).obj i₂ ≅ (restrict g q D).obj i₂ :=
        { hom := e.hom.hom i₂
          inv := e.inv.hom i₂
          hom_inv_id := congr_fun (congr_arg DescentData.Hom.hom e.hom_inv_id) i₂
          inv_hom_id := congr_fun (congr_arg DescentData.Hom.hom e.inv_hom_id) i₂ }
      have hei₂ := ((F.map b.op.toLoc).toFunctor.mapIso ei₂).inv_hom_id
      dsimp [ei₂] at hei₂
      rw [hei₂]
      have hDr := descentHom_heq (F := F) D (Category.id_comp r) a b
        (by simpa only [Category.id_comp] using ha)
        (by simpa only [Category.id_comp] using hb) ha hb
      rw [eq_of_heq hDr]
      exact (congrArg
        (fun z ↦ (F.map a.op.toLoc).toFunctor.map (e.hom.hom i₁) ≫ z)
        (Category.comp_id (D.hom r a b ha hb))).symm)

/-- Pulling singleton descent data along a covering family is an equivalence when
descent is effective for that family and the composite family is covering. -/
theorem pullFunctorIsEquivalence
    (hg : Sieve.ofArrows X g ∈ J T)
    (hcomp : Sieve.ofArrows X (fun i ↦ g i ≫ q) ∈ J S)
    [(F.toDescentData g).IsEquivalence] :
    (DescentData.pullFunctor F (f := fun _ : Unit ↦ q) (p := 𝟙 S)
      (f' := fun i ↦ g i ≫ q) (α := fun _ ↦ ()) (p' := g)
      (fun i ↦ by simp)).IsEquivalence := by
  let H := DescentData.pullFunctor F (f := fun _ : Unit ↦ q) (p := 𝟙 S)
    (f' := fun i ↦ g i ≫ q) (α := fun _ ↦ ()) (p' := g) (fun i ↦ by simp)
  let hff := DescentData.fullyFaithfulPullFunctor F
    (f := fun _ : Unit ↦ q) (f' := fun i ↦ g i ≫ q)
    (α := fun _ ↦ ()) (p' := g) (fun i ↦ by simp) hcomp
  letI : H.Full := hff.full
  letI : H.Faithful := hff.faithful
  letI : H.EssSurj := ⟨fun D ↦ by
    obtain ⟨M, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
      (F := F.toDescentData g) (restrict g q D)
    exact ⟨singletonDatum g q hg D M e, ⟨singletonPullbackIso g q hg D M e⟩⟩⟩
  exact { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }

/-- If descent is effective along `g`, then descent for a singleton `q` is
equivalent to descent for the composite family `g i ≫ q`. -/
lemma isStackFor_singleton_iff_composite
    (hg : Sieve.ofArrows X g ∈ J T)
    (hcomp : Sieve.ofArrows X (fun i ↦ g i ≫ q) ∈ J S)
    (hstackg : F.IsStackFor (Presieve.ofArrows X g)) :
    F.IsStackFor (Presieve.ofArrows (fun _ : Unit ↦ T) (fun _ ↦ q)) ↔
      F.IsStackFor (Presieve.ofArrows X (fun i ↦ g i ≫ q)) := by
  rw [isStackFor_ofArrows_iff] at hstackg
  letI : (F.toDescentData g).IsEquivalence := hstackg
  letI : (DescentData.pullFunctor F (f := fun _ : Unit ↦ q) (p := 𝟙 S)
      (f' := fun i ↦ g i ≫ q) (α := fun _ ↦ ()) (p' := g)
      (fun i ↦ by simp)).IsEquivalence :=
    pullFunctorIsEquivalence (F := F) (J := J) g q hg hcomp
  exact isStackFor_iff_of_pullFunctor_isEquivalence F
    (fun _ : Unit ↦ q) (fun i ↦ g i ≫ q) (fun _ ↦ ()) g (fun i ↦ by simp)

end DescentComposition

end CategoryTheory.Pseudofunctor

namespace AlgebraicGeometry.Scheme.Cover

open CategoryTheory Limits

universe v₁ v₂ u₁ u₂

variable {K : GrothendieckTopology Scheme.{u₁}}
  (F : Pseudofunctor (LocallyDiscrete Scheme.{u₁}ᵒᵖ) Cat.{v₂, u₂})
  [F.IsPrestack K] [F.IsStack Scheme.zariskiTopology]

/-- For a small family of scheme morphisms, descent along the family is equivalent
to descent along the morphism from the disjoint union. -/
lemma isStackFor_sigma_iff (hK : Scheme.zariskiTopology ≤ K)
    {P : MorphismProperty Scheme.{u₁}} [IsZariskiLocalAtSource P]
    {S : Scheme.{u₁}} (𝒰 : S.Cover.{u₁} (Scheme.precoverage P))
    (h𝒰 : Sieve.ofArrows 𝒰.X 𝒰.f ∈ K S) :
    F.IsStackFor (Presieve.ofArrows 𝒰.sigma.X 𝒰.sigma.f) ↔
      F.IsStackFor (Presieve.ofArrows 𝒰.X 𝒰.f) := by
  let g : ∀ i, 𝒰.X i ⟶ (∐ 𝒰.X) := Sigma.ι 𝒰.X
  let q : (∐ 𝒰.X) ⟶ S := Sigma.desc 𝒰.f
  have hgzar : Sieve.ofArrows 𝒰.X g ∈ Scheme.zariskiTopology (∐ 𝒰.X) := by
    dsimp [g]
    have h := (AlgebraicGeometry.sigmaOpenCover 𝒰.X).mem_grothendieckTopology
    change Sieve.ofArrows 𝒰.X (Sigma.ι 𝒰.X) ∈
      Scheme.zariskiTopology (∐ 𝒰.X) at h
    exact h
  have hgK : Sieve.ofArrows 𝒰.X g ∈ K (∐ 𝒰.X) := hK _ hgzar
  have hstackg : F.IsStackFor (Presieve.ofArrows 𝒰.X g) :=
    F.isStackFor _ (by simpa using hgzar)
  have h := CategoryTheory.Pseudofunctor.DescentComposition.isStackFor_singleton_iff_composite
    (F := F) (J := K) g q hgK (by simpa [g, q] using h𝒰) hstackg
  simpa [g, q, Presieve.ofArrows_of_unique] using h

end AlgebraicGeometry.Scheme.Cover

namespace AlgebraicGeometry

open CategoryTheory Limits Scheme

universe v₁ v₂ u₁ u₂

variable {P : MorphismProperty Scheme.{u₁}} [P.IsMultiplicative]
  [IsZariskiLocalAtSource P]

/-- If a pseudofunctor is already a Zariski stack, descent for surjective `P`-morphisms
between affine schemes implies descent for every `P`-quasi-compact covering family of an
affine scheme.  The proof takes a finite affine refinement, collapses it to the morphism
from its disjoint union, and transports descent across the refinement. -/
lemma isStackFor_propQCCover_of_affine_singletons
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u₁}ᵒᵖ) Cat.{v₂, u₂})
    [F.IsPrestack (Scheme.propQCTopology P)] [F.IsStack Scheme.zariskiTopology]
    (hsingle : ∀ {R S : CommRingCat.{u₁}} (f : R ⟶ S),
      P (Spec.map f) → Surjective (Spec.map f) →
        F.IsStackFor (.singleton (Spec.map f)))
    {R : CommRingCat.{u₁}} (𝒰 : (Spec R).Cover.{u₁} (Scheme.propQCPrecoverage P)) :
    F.IsStackFor 𝒰.presieve₀ := by
  obtain ⟨𝒱, h𝒱𝒰, hfin, _⟩ := QuasiCompactCover.exists_hom 𝒰.forgetQc
  letI : Finite 𝒱.I₀ := hfin
  have h𝒱mem : Sieve.ofArrows 𝒱.cover.X 𝒱.cover.f ∈
      Scheme.propQCTopology P (Spec R) :=
    Scheme.Cover.mem_propQCTopology 𝒱.cover
  have h𝒱stack : F.IsStackFor 𝒱.cover.presieve₀ := by
    apply (Scheme.Cover.isStackFor_sigma_iff F
      Scheme.zariskiTopology_le_propQCTopology 𝒱.cover h𝒱mem).mp
    rw [Presieve.ofArrows_of_unique]
    letI (i : 𝒱.cover.I₀) : IsAffine (𝒱.cover.X i) := by
      change IsAffine (Spec (𝒱.X i))
      infer_instance
    letI : IsAffine (𝒱.cover.sigma.X default) := by
      change IsAffine (∐ fun i : 𝒱.I₀ ↦ Spec (𝒱.X i))
      infer_instance
    let q := 𝒱.cover.sigma.f default
    let f : Spec _ ⟶ Spec R := (𝒱.cover.sigma.X default).isoSpec.inv ≫ q
    obtain ⟨φ, hφ⟩ := Spec.map_surjective f
    have hfP : P (Spec.map φ) := by
      rw [hφ]
      exact IsZariskiLocalAtSource.comp (𝒱.cover.sigma.map_prop default)
        (𝒱.cover.sigma.X default).isoSpec.inv
    have hfSurj : Surjective (Spec.map φ) := by
      rw [hφ]
      dsimp only [f]
      letI : Surjective q := by
        dsimp only [q, Scheme.Cover.sigma_f]
        exact inferInstanceAs <| Surjective (Sigma.desc 𝒱.cover.f)
      infer_instance
    have hfstack := hsingle φ hfP hfSurj
    apply (Pseudofunctor.IsStackFor_generate_iff F (.singleton q)).mp
    have hfstack' :=
      (Pseudofunctor.IsStackFor_generate_iff F (.singleton (Spec.map φ))).mpr hfstack
    have hfcover : Sieve.generate (Presieve.singleton (Spec.map φ)) ∈
        Scheme.propQCTopology P (Spec R) := by
      letI : Surjective (Spec.map φ) := hfSurj
      letI : QuasiCompact (Spec.map φ) := by infer_instance
      exact Scheme.Hom.generate_singleton_mem_propQCTopology (Spec.map φ) hfP
    apply Pseudofunctor.IsStackFor.of_le' F hfstack' hfcover
    rw [Sieve.generate_le_iff]
    rintro _ _ ⟨⟩
    rw [hφ]
    have hq : (Sieve.generate (Presieve.singleton q)) q :=
      (Sieve.le_generate (Presieve.singleton q)) _ q (Presieve.singleton_self q)
    exact (Sieve.generate (Presieve.singleton q)).downward_closed
      hq (𝒱.cover.sigma.X default).isoSpec.inv
  apply (Pseudofunctor.IsStackFor_generate_iff F 𝒰.presieve₀).mp
  have h𝒱stack' :=
    (Pseudofunctor.IsStackFor_generate_iff F 𝒱.cover.presieve₀).mpr h𝒱stack
  apply Pseudofunctor.IsStackFor.of_le' F h𝒱stack' h𝒱mem
  exact h𝒱𝒰.sieve₀_le_sieve₀

end AlgebraicGeometry
