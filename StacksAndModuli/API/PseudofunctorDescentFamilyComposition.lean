module

public import StacksAndModuli.API.PseudofunctorDescentComposition

/-!
# Composition of families of pseudofunctor descent data

This file proves transitivity of effective descent for a covering family followed,
over every member of that family, by another covering family.  It complements
`PseudofunctorDescentComposition`, whose main construction treats a single outer
morphism.
-/

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite

universe t t' v' v u' u

namespace CategoryTheory.Pseudofunctor

open LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
  {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
  {A : Type t'} {B : A → Type t} {T : A → C} {S : C}
  {X : ∀ a, B a → C}
  (g : ∀ a i, X a i ⟶ T a) (q : ∀ a, T a ⟶ S)

namespace DescentFamilyComposition

open DescentComposition

/-- Restrict descent data for all composites `g a i ≫ q a` to the inner family
over one fixed outer index `a`. -/
def restrict (D : F.DescentData
    (fun k : Σ a, B a ↦ g k.1 k.2 ≫ q k.1)) (a : A) :
    F.DescentData (g a) where
  obj i := D.obj ⟨a, i⟩
  hom Y r i₁ i₂ f₁ f₂ hf₁ hf₂ :=
    D.hom (i₁ := ⟨a, i₁⟩) (i₂ := ⟨a, i₂⟩) (r ≫ q a) f₁ f₂
      (by rw [← Category.assoc, hf₁]) (by rw [← Category.assoc, hf₂])
  pullHom_hom Y' Y k r r' hr i₁ i₂ f₁ f₂ hf₁ hf₂ f₁' f₂' hk₁ hk₂ := by
    apply D.pullHom_hom (i₁ := ⟨a, i₁⟩) (i₂ := ⟨a, i₂⟩)
      k (r ≫ q a) (r' ≫ q a) (by rw [reassoc_of% hr])
      f₁ f₂ (by rw [← Category.assoc, hf₁]) (by rw [← Category.assoc, hf₂])
      f₁' f₂' hk₁ hk₂
  hom_self Y r i f hf :=
    D.hom_self (i := ⟨a, i⟩) (r ≫ q a) f (by rw [← Category.assoc, hf])
  hom_comp Y r i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ :=
    D.hom_comp (i₁ := ⟨a, i₁⟩) (i₂ := ⟨a, i₂⟩) (i₃ := ⟨a, i₃⟩)
      (r ≫ q a) f₁ f₂ f₃
      (by rw [← Category.assoc, hf₁]) (by rw [← Category.assoc, hf₂])
      (by rw [← Category.assoc, hf₃])

set_option backward.isDefEq.respectTransparency false in
/-- The choice-dependent comparison between pullbacks of two inner gluings. -/
def localMorCore (D : F.DescentData
    (fun k : Σ a, B a ↦ g k.1 k.2 ≫ q k.1))
    {a₁ a₂ : A} (M₁ : F.obj (.mk (op (T a₁))))
    (M₂ : F.obj (.mk (op (T a₂))))
    (e₁ : (F.toDescentData (g a₁)).obj M₁ ≅ restrict g q D a₁)
    (e₂ : (F.toDescentData (g a₂)).obj M₂ ≅ restrict g q D a₂)
    {Y : C} (r : Y ⟶ S) (f₁ : Y ⟶ T a₁) (f₂ : Y ⟶ T a₂)
    (hf₁ : f₁ ≫ q a₁ = r) (hf₂ : f₂ ≫ q a₂ = r)
    {Z : C} (h : Z ⟶ Y)
    {i : B a₁} {j : B a₂} (b₁ : Z ⟶ X a₁ i) (b₂ : Z ⟶ X a₂ j)
    (hb₁ : b₁ ≫ g a₁ i = h ≫ f₁) (hb₂ : b₂ ≫ g a₂ j = h ≫ f₂) :
    (F.map (h ≫ f₁).op.toLoc).toFunctor.obj M₁ ⟶
      (F.map (h ≫ f₂).op.toLoc).toFunctor.obj M₂ :=
  (F.mapComp' (g a₁ i).op.toLoc b₁.op.toLoc (h ≫ f₁).op.toLoc
      (by simp [← hb₁])).hom.toNatTrans.app M₁ ≫
    (F.map b₁.op.toLoc).toFunctor.map (e₁.hom.hom i) ≫
    D.hom (i₁ := ⟨a₁, i⟩) (i₂ := ⟨a₂, j⟩) (h ≫ r) b₁ b₂
      (by rw [← Category.assoc, hb₁, Category.assoc, hf₁])
      (by rw [← Category.assoc, hb₂, Category.assoc, hf₂]) ≫
    (F.map b₂.op.toLoc).toFunctor.map (e₂.inv.hom j) ≫
    (F.mapComp' (g a₂ j).op.toLoc b₂.op.toLoc (h ≫ f₂).op.toLoc
      (by simp [← hb₂])).inv.toNatTrans.app M₂

set_option backward.isDefEq.respectTransparency false in
/-- The local comparison, expressed as a section of the morphism presheaf. -/
def localMor (D : F.DescentData
    (fun k : Σ a, B a ↦ g k.1 k.2 ≫ q k.1))
    {a₁ a₂ : A} (M₁ : F.obj (.mk (op (T a₁))))
    (M₂ : F.obj (.mk (op (T a₂))))
    (e₁ : (F.toDescentData (g a₁)).obj M₁ ≅ restrict g q D a₁)
    (e₂ : (F.toDescentData (g a₂)).obj M₂ ≅ restrict g q D a₂)
    {Y : C} (r : Y ⟶ S) (f₁ : Y ⟶ T a₁) (f₂ : Y ⟶ T a₂)
    (hf₁ : f₁ ≫ q a₁ = r) (hf₂ : f₂ ≫ q a₂ = r)
    {Z : C} (h : Z ⟶ Y)
    {i : B a₁} {j : B a₂} (b₁ : Z ⟶ X a₁ i) (b₂ : Z ⟶ X a₂ j)
    (hb₁ : b₁ ≫ g a₁ i = h ≫ f₁) (hb₂ : b₂ ≫ g a₂ j = h ≫ f₂) :
    (F.presheafHom ((F.map f₁.op.toLoc).toFunctor.obj M₁)
      ((F.map f₂.op.toLoc).toFunctor.obj M₂)).obj (op (Over.mk h)) :=
  (F.mapComp' f₁.op.toLoc h.op.toLoc (h ≫ f₁).op.toLoc (by grind)).inv.toNatTrans.app M₁ ≫
    localMorCore g q D M₁ M₂ e₁ e₂ r f₁ f₂ hf₁ hf₂ h b₁ b₂ hb₁ hb₂ ≫
    (F.mapComp' f₂.op.toLoc h.op.toLoc (h ≫ f₂).op.toLoc (by grind)).hom.toNatTrans.app M₂

set_option backward.isDefEq.respectTransparency false in
lemma localMorCore_unique (D : F.DescentData
    (fun k : Σ a, B a ↦ g k.1 k.2 ≫ q k.1))
    {a₁ a₂ : A} (M₁ : F.obj (.mk (op (T a₁))))
    (M₂ : F.obj (.mk (op (T a₂))))
    (e₁ : (F.toDescentData (g a₁)).obj M₁ ≅ restrict g q D a₁)
    (e₂ : (F.toDescentData (g a₂)).obj M₂ ≅ restrict g q D a₂)
    {Y : C} (r : Y ⟶ S) (f₁ : Y ⟶ T a₁) (f₂ : Y ⟶ T a₂)
    (hf₁ : f₁ ≫ q a₁ = r) (hf₂ : f₂ ≫ q a₂ = r)
    {Z : C} (h : Z ⟶ Y)
    {i i' : B a₁} {j j' : B a₂}
    (b₁ : Z ⟶ X a₁ i) (b₂ : Z ⟶ X a₂ j)
    (b₁' : Z ⟶ X a₁ i') (b₂' : Z ⟶ X a₂ j')
    (hb₁ : b₁ ≫ g a₁ i = h ≫ f₁) (hb₂ : b₂ ≫ g a₂ j = h ≫ f₂)
    (hb₁' : b₁' ≫ g a₁ i' = h ≫ f₁)
    (hb₂' : b₂' ≫ g a₂ j' = h ≫ f₂) :
    localMorCore g q D M₁ M₂ e₁ e₂ r f₁ f₂ hf₁ hf₂ h b₁ b₂ hb₁ hb₂ =
      localMorCore g q D M₁ M₂ e₁ e₂ r f₁ f₂ hf₁ hf₂ h b₁' b₂' hb₁' hb₂' := by
  have hleft := e₁.hom.comm (h ≫ f₁) b₁ b₁' hb₁ hb₁'
  have hright := e₂.inv.comm (h ≫ f₂) b₂' b₂ hb₂' hb₂
  dsimp [restrict] at hleft hright
  simp only [Category.assoc, hf₁] at hleft
  simp only [Category.assoc, hf₂] at hright
  have hD : D.hom (i₁ := ⟨a₁, i⟩) (i₂ := ⟨a₂, j⟩) (h ≫ r) b₁ b₂
      (by rw [← Category.assoc, hb₁, Category.assoc, hf₁])
      (by rw [← Category.assoc, hb₂, Category.assoc, hf₂]) =
      D.hom (i₁ := ⟨a₁, i⟩) (i₂ := ⟨a₁, i'⟩) (h ≫ r) b₁ b₁'
        (by rw [← Category.assoc, hb₁, Category.assoc, hf₁])
        (by rw [← Category.assoc, hb₁', Category.assoc, hf₁]) ≫
      D.hom (i₁ := ⟨a₁, i'⟩) (i₂ := ⟨a₂, j'⟩) (h ≫ r) b₁' b₂'
        (by rw [← Category.assoc, hb₁', Category.assoc, hf₁])
        (by rw [← Category.assoc, hb₂', Category.assoc, hf₂]) ≫
      D.hom (i₁ := ⟨a₂, j'⟩) (i₂ := ⟨a₂, j⟩) (h ≫ r) b₂' b₂
        (by rw [← Category.assoc, hb₂', Category.assoc, hf₂])
        (by rw [← Category.assoc, hb₂, Category.assoc, hf₂]) := by
    rw [D.hom_comp (i₁ := ⟨a₁, i'⟩) (i₂ := ⟨a₂, j'⟩)
        (i₃ := ⟨a₂, j⟩) (h ≫ r) b₁' b₂' b₂,
      D.hom_comp (i₁ := ⟨a₁, i⟩) (i₂ := ⟨a₁, i'⟩)
        (i₃ := ⟨a₂, j⟩) (h ≫ r) b₁ b₁' b₂]
  dsimp [localMorCore]
  rw [hD]
  simp only [Category.assoc]
  rw [reassoc_of% hleft, ← reassoc_of% hright]
  simp

lemma localMor_unique (D : F.DescentData
    (fun k : Σ a, B a ↦ g k.1 k.2 ≫ q k.1))
    {a₁ a₂ : A} (M₁ : F.obj (.mk (op (T a₁))))
    (M₂ : F.obj (.mk (op (T a₂))))
    (e₁ : (F.toDescentData (g a₁)).obj M₁ ≅ restrict g q D a₁)
    (e₂ : (F.toDescentData (g a₂)).obj M₂ ≅ restrict g q D a₂)
    {Y : C} (r : Y ⟶ S) (f₁ : Y ⟶ T a₁) (f₂ : Y ⟶ T a₂)
    (hf₁ : f₁ ≫ q a₁ = r) (hf₂ : f₂ ≫ q a₂ = r)
    {Z : C} (h : Z ⟶ Y)
    {i i' : B a₁} {j j' : B a₂}
    (b₁ : Z ⟶ X a₁ i) (b₂ : Z ⟶ X a₂ j)
    (b₁' : Z ⟶ X a₁ i') (b₂' : Z ⟶ X a₂ j')
    (hb₁ : b₁ ≫ g a₁ i = h ≫ f₁) (hb₂ : b₂ ≫ g a₂ j = h ≫ f₂)
    (hb₁' : b₁' ≫ g a₁ i' = h ≫ f₁)
    (hb₂' : b₂' ≫ g a₂ j' = h ≫ f₂) :
    localMor g q D M₁ M₂ e₁ e₂ r f₁ f₂ hf₁ hf₂ h b₁ b₂ hb₁ hb₂ =
      localMor g q D M₁ M₂ e₁ e₂ r f₁ f₂ hf₁ hf₂ h b₁' b₂' hb₁' hb₂' := by
  dsimp only [localMor]
  rw [localMorCore_unique g q D M₁ M₂ e₁ e₂ r f₁ f₂ hf₁ hf₂ h
    b₁ b₂ b₁' b₂' hb₁ hb₂ hb₁' hb₂']

set_option backward.isDefEq.respectTransparency false in
lemma localMor_precomp (D : F.DescentData
    (fun k : Σ a, B a ↦ g k.1 k.2 ≫ q k.1))
    {a₁ a₂ : A} (M₁ : F.obj (.mk (op (T a₁))))
    (M₂ : F.obj (.mk (op (T a₂))))
    (e₁ : (F.toDescentData (g a₁)).obj M₁ ≅ restrict g q D a₁)
    (e₂ : (F.toDescentData (g a₂)).obj M₂ ≅ restrict g q D a₂)
    {Y : C} (r : Y ⟶ S) (f₁ : Y ⟶ T a₁) (f₂ : Y ⟶ T a₂)
    (hf₁ : f₁ ≫ q a₁ = r) (hf₂ : f₂ ≫ q a₂ = r)
    {Z : C} (h : Z ⟶ Y)
    {i : B a₁} {j : B a₂} (b₁ : Z ⟶ X a₁ i) (b₂ : Z ⟶ X a₂ j)
    (hb₁ : b₁ ≫ g a₁ i = h ≫ f₁) (hb₂ : b₂ ≫ g a₂ j = h ≫ f₂)
    {Z' : C} (k : Z' ⟶ Z) (h' : Z' ⟶ Y)
    (b₁' : Z' ⟶ X a₁ i) (b₂' : Z' ⟶ X a₂ j)
    (hk : k ≫ h = h') (hkb₁ : k ≫ b₁ = b₁') (hkb₂ : k ≫ b₂ = b₂') :
    localMor g q D M₁ M₂ e₁ e₂ r f₁ f₂ hf₁ hf₂ h' b₁' b₂'
        (by rw [← hkb₁, Category.assoc, hb₁, ← Category.assoc, hk])
        (by rw [← hkb₂, Category.assoc, hb₂, ← Category.assoc, hk]) =
      (F.presheafHom ((F.map f₁.op.toLoc).toFunctor.obj M₁)
        ((F.map f₂.op.toLoc).toFunctor.obj M₂)).map (Over.homMk k).op
          (localMor g q D M₁ M₂ e₁ e₂ r f₁ f₂ hf₁ hf₂ h b₁ b₂ hb₁ hb₂) := by
  dsimp [localMor, localMorCore, Pseudofunctor.presheafHom, pullHom]
  rw [← D.pullHom_hom (i₁ := ⟨a₁, i⟩) (i₂ := ⟨a₂, j⟩)
    k (h ≫ r) (h' ≫ r) (by rw [← hk, Category.assoc])
    b₁ b₂ (by rw [← Category.assoc, hb₁, Category.assoc, hf₁])
      (by rw [← Category.assoc, hb₂, Category.assoc, hf₂])
    b₁' b₂' hkb₁ hkb₂]
  simp only [Functor.map_comp, Category.assoc]
  dsimp [pullHom]
  simp only [Functor.map_comp, Category.assoc]
  have hnat₁ := F.mapComp'_hom_naturality b₁.op.toLoc k.op.toLoc b₁'.op.toLoc
    (by simp [← hkb₁]) (e₁.hom.hom i)
  have hnat₂ := F.mapComp'_inv_naturality b₂.op.toLoc k.op.toLoc b₂'.op.toLoc
    (by simp [← hkb₂]) (e₂.inv.hom j)
  dsimp [restrict] at hnat₁ hnat₂
  rw [reassoc_of% hnat₁, ← reassoc_of% hnat₂]
  rw [F.mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom_app_assoc
      (g a₁ i).op.toLoc b₁.op.toLoc k.op.toLoc
      (f₁.op.toLoc ≫ h.op.toLoc) b₁'.op.toLoc
      (f₁.op.toLoc ≫ h'.op.toLoc) (by grind) (by grind) (by grind),
    F.mapComp'₀₁₃_inv_comp_mapComp'₀₂₃_hom_app_assoc
      f₁.op.toLoc h.op.toLoc k.op.toLoc
      (f₁.op.toLoc ≫ h.op.toLoc) h'.op.toLoc
      (f₁.op.toLoc ≫ h'.op.toLoc) (by grind) (by grind) (by grind),
    ← F.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app_assoc
      (g a₂ j).op.toLoc b₂.op.toLoc k.op.toLoc
      (f₂.op.toLoc ≫ h.op.toLoc) b₂'.op.toLoc
      (f₂.op.toLoc ≫ h'.op.toLoc) (by grind) (by grind) (by grind),
    F.mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app
      f₂.op.toLoc h.op.toLoc k.op.toLoc
      (f₂.op.toLoc ≫ h.op.toLoc) h'.op.toLoc
      (f₂.op.toLoc ≫ h'.op.toLoc) (by grind) (by grind) (by grind)]

variable {J : GrothendieckTopology C}

/-- The common local refinement on which lifts to two different outer members
factor through their respective inner covering families. -/
abbrev localSieve {a₁ a₂ : A} {Y : C}
    (f₁ : Y ⟶ T a₁) (f₂ : Y ⟶ T a₂) : Sieve (Over.mk (𝟙 Y)) :=
  (Sieve.overEquiv (Over.mk (𝟙 Y))).symm
    (Sieve.pullback f₁ (Sieve.ofArrows (X a₁) (g a₁)) ⊓
      Sieve.pullback f₂ (Sieve.ofArrows (X a₂) (g a₂)))

lemma localSieve_mem
    (hg : ∀ a, Sieve.ofArrows (X a) (g a) ∈ J (T a))
    {a₁ a₂ : A} {Y : C} (f₁ : Y ⟶ T a₁) (f₂ : Y ⟶ T a₂) :
    localSieve g f₁ f₂ ∈ J.over Y _ := by
  rw [J.mem_over_iff, OrderIso.apply_symm_apply]
  exact J.intersection_covering
    (J.pullback_stable f₁ (hg a₁)) (J.pullback_stable f₂ (hg a₂))

namespace localSieve

variable {a₁ a₂ : A} {Y Z : C} {f₁ : Y ⟶ T a₁} {f₂ : Y ⟶ T a₂} {h : Z ⟶ Y}
  (hh : localSieve g f₁ f₂ (Over.homMk h : Over.mk h ⟶ Over.mk (𝟙 Y)))

include hh in
lemma exists_left : ∃ (i : B a₁) (b : Z ⟶ X a₁ i), b ≫ g a₁ i = h ≫ f₁ := by
  obtain ⟨⟨_, b, _, ⟨i⟩, hb⟩, -⟩ := hh
  exact ⟨i, b, hb⟩

include hh in
lemma exists_right : ∃ (j : B a₂) (b : Z ⟶ X a₂ j), b ≫ g a₂ j = h ≫ f₂ := by
  obtain ⟨-, ⟨_, b, _, ⟨j⟩, hb⟩⟩ := hh
  exact ⟨j, b, hb⟩

noncomputable def leftIdx : B a₁ := (exists_left g hh).choose

noncomputable def leftHom : Z ⟶ X a₁ (leftIdx g hh) :=
  (exists_left g hh).choose_spec.choose

lemma left_fac : leftHom g hh ≫ g a₁ (leftIdx g hh) = h ≫ f₁ :=
  (exists_left g hh).choose_spec.choose_spec

noncomputable def rightIdx : B a₂ := (exists_right g hh).choose

noncomputable def rightHom : Z ⟶ X a₂ (rightIdx g hh) :=
  (exists_right g hh).choose_spec.choose

lemma right_fac : rightHom g hh ≫ g a₂ (rightIdx g hh) = h ≫ f₂ :=
  (exists_right g hh).choose_spec.choose_spec

end localSieve

set_option backward.isDefEq.respectTransparency.types false in
/-- The compatible family of local comparisons on the common refinement sieve. -/
noncomputable def localFamily (D : F.DescentData
    (fun k : Σ a, B a ↦ g k.1 k.2 ≫ q k.1))
    {a₁ a₂ : A} (M₁ : F.obj (.mk (op (T a₁))))
    (M₂ : F.obj (.mk (op (T a₂))))
    (e₁ : (F.toDescentData (g a₁)).obj M₁ ≅ restrict g q D a₁)
    (e₂ : (F.toDescentData (g a₂)).obj M₂ ≅ restrict g q D a₂)
    {Y : C} (r : Y ⟶ S) (f₁ : Y ⟶ T a₁) (f₂ : Y ⟶ T a₂)
    (hf₁ : f₁ ≫ q a₁ = r) (hf₂ : f₂ ≫ q a₂ = r) :
    Presieve.FamilyOfElements
      (F.presheafHom ((F.map f₁.op.toLoc).toFunctor.obj M₁)
        ((F.map f₂.op.toLoc).toFunctor.obj M₂))
      (localSieve g f₁ f₂).arrows :=
  fun Z h hh ↦
    let hh' : localSieve g f₁ f₂
        (Over.homMk Z.hom : Over.mk Z.hom ⟶ Over.mk (𝟙 Y)) := by
      convert! hh
      ext
      simpa using (Over.w h).symm
    localMor g q D M₁ M₂ e₁ e₂ r f₁ f₂ hf₁ hf₂ Z.hom
      (localSieve.leftHom g hh') (localSieve.rightHom g hh')
      (localSieve.left_fac g hh') (localSieve.right_fac g hh')

set_option backward.isDefEq.respectTransparency false in
lemma localFamily_eq (D : F.DescentData
    (fun k : Σ a, B a ↦ g k.1 k.2 ≫ q k.1))
    {a₁ a₂ : A} (M₁ : F.obj (.mk (op (T a₁))))
    (M₂ : F.obj (.mk (op (T a₂))))
    (e₁ : (F.toDescentData (g a₁)).obj M₁ ≅ restrict g q D a₁)
    (e₂ : (F.toDescentData (g a₂)).obj M₂ ≅ restrict g q D a₂)
    {Y : C} (r : Y ⟶ S) (f₁ : Y ⟶ T a₁) (f₂ : Y ⟶ T a₂)
    (hf₁ : f₁ ≫ q a₁ = r) (hf₂ : f₂ ≫ q a₂ = r)
    {Z : Over Y} (h : Z ⟶ Over.mk (𝟙 Y))
    (hh : (localSieve g f₁ f₂).arrows h)
    {i : B a₁} {j : B a₂} (b₁ : Z.left ⟶ X a₁ i) (b₂ : Z.left ⟶ X a₂ j)
    (hb₁ : b₁ ≫ g a₁ i = Z.hom ≫ f₁) (hb₂ : b₂ ≫ g a₂ j = Z.hom ≫ f₂) :
    localFamily g q D M₁ M₂ e₁ e₂ r f₁ f₂ hf₁ hf₂ h hh =
      localMor g q D M₁ M₂ e₁ e₂ r f₁ f₂ hf₁ hf₂ Z.hom b₁ b₂ hb₁ hb₂ := by
  apply localMor_unique

set_option backward.isDefEq.respectTransparency false in
lemma localFamily_compatible (D : F.DescentData
    (fun k : Σ a, B a ↦ g k.1 k.2 ≫ q k.1))
    {a₁ a₂ : A} (M₁ : F.obj (.mk (op (T a₁))))
    (M₂ : F.obj (.mk (op (T a₂))))
    (e₁ : (F.toDescentData (g a₁)).obj M₁ ≅ restrict g q D a₁)
    (e₂ : (F.toDescentData (g a₂)).obj M₂ ≅ restrict g q D a₂)
    {Y : C} (r : Y ⟶ S) (f₁ : Y ⟶ T a₁) (f₂ : Y ⟶ T a₂)
    (hf₁ : f₁ ≫ q a₁ = r) (hf₂ : f₂ ≫ q a₂ = r) :
    (localFamily g q D M₁ M₂ e₁ e₂ r f₁ f₂ hf₁ hf₂).Compatible := by
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
  rw [localFamily_eq g q D M₁ M₂ e₁ e₂ r f₁ f₂ hf₁ hf₂ _ hh₁
      (localSieve.leftHom g hh₁) (localSieve.rightHom g hh₁)
      (localSieve.left_fac g hh₁) (localSieve.right_fac g hh₁),
    localFamily_eq g q D M₁ M₂ e₁ e₂ r f₁ f₂ hf₁ hf₂ _ hh₂
      (localSieve.leftHom g hh₂) (localSieve.rightHom g hh₂)
      (localSieve.left_fac g hh₂) (localSieve.right_fac g hh₂)]
  have hp₁ := localMor_precomp g q D M₁ M₂ e₁ e₂ r f₁ f₂ hf₁ hf₂ Y₁.hom
    (localSieve.leftHom g hh₁) (localSieve.rightHom g hh₁)
    (localSieve.left_fac g hh₁) (localSieve.right_fac g hh₁)
    h₁ Z.hom (h₁ ≫ localSieve.leftHom g hh₁)
    (h₁ ≫ localSieve.rightHom g hh₁) hk₁ rfl rfl
  have hp₂ := localMor_precomp g q D M₁ M₂ e₁ e₂ r f₁ f₂ hf₁ hf₂ Y₂.hom
    (localSieve.leftHom g hh₂) (localSieve.rightHom g hh₂)
    (localSieve.left_fac g hh₂) (localSieve.right_fac g hh₂)
    h₂ Z.hom (h₂ ≫ localSieve.leftHom g hh₂)
    (h₂ ≫ localSieve.rightHom g hh₂) hk₂ rfl rfl
  dsimp [Pseudofunctor.presheafHom] at hp₁ hp₂
  rw [← hp₁, ← hp₂]
  apply localMor_unique

lemma mem_localSieve {a₁ a₂ : A} {Y Z : C}
    (f₁ : Y ⟶ T a₁) (f₂ : Y ⟶ T a₂) (h : Z ⟶ Y)
    {i : B a₁} {j : B a₂} (b₁ : Z ⟶ X a₁ i) (b₂ : Z ⟶ X a₂ j)
    (hb₁ : b₁ ≫ g a₁ i = h ≫ f₁) (hb₂ : b₂ ≫ g a₂ j = h ≫ f₂) :
    localSieve g f₁ f₂ (Over.homMk h : Over.mk h ⟶ Over.mk (𝟙 Y)) :=
  ⟨⟨_, b₁, _, ⟨i⟩, hb₁⟩, ⟨_, b₂, _, ⟨j⟩, hb₂⟩⟩

variable [F.IsPrestack J]

set_option backward.isDefEq.respectTransparency.types false in
/-- The comparison between pullbacks of two inner glued objects, obtained by
sheaf gluing on their common refinement. -/
noncomputable def gluedHom
    (hg : ∀ a, Sieve.ofArrows (X a) (g a) ∈ J (T a))
    (D : F.DescentData (fun k : Σ a, B a ↦ g k.1 k.2 ≫ q k.1))
    {a₁ a₂ : A} (M₁ : F.obj (.mk (op (T a₁))))
    (M₂ : F.obj (.mk (op (T a₂))))
    (e₁ : (F.toDescentData (g a₁)).obj M₁ ≅ restrict g q D a₁)
    (e₂ : (F.toDescentData (g a₂)).obj M₂ ≅ restrict g q D a₂)
    {Y : C} (r : Y ⟶ S) (f₁ : Y ⟶ T a₁) (f₂ : Y ⟶ T a₂)
    (hf₁ : f₁ ≫ q a₁ = r) (hf₂ : f₂ ≫ q a₂ = r) :
    (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      (F.map f₂.op.toLoc).toFunctor.obj M₂ :=
  F.presheafHomObjHomEquiv.symm
    (Presieve.IsSheafFor.amalgamate
      (((isSheaf_iff_isSheaf_of_type _ _).1
        (IsPrestack.isSheaf J ((F.map f₁.op.toLoc).toFunctor.obj M₁)
          ((F.map f₂.op.toLoc).toFunctor.obj M₂))).isSheafFor _
            (by simpa using localSieve_mem g hg f₁ f₂)) _
        (localFamily_compatible g q D M₁ M₂ e₁ e₂ r f₁ f₂ hf₁ hf₂))

set_option backward.isDefEq.respectTransparency false in
lemma map_gluedHom
    (hg : ∀ a, Sieve.ofArrows (X a) (g a) ∈ J (T a))
    (D : F.DescentData (fun k : Σ a, B a ↦ g k.1 k.2 ≫ q k.1))
    {a₁ a₂ : A} (M₁ : F.obj (.mk (op (T a₁))))
    (M₂ : F.obj (.mk (op (T a₂))))
    (e₁ : (F.toDescentData (g a₁)).obj M₁ ≅ restrict g q D a₁)
    (e₂ : (F.toDescentData (g a₂)).obj M₂ ≅ restrict g q D a₂)
    {Y : C} (r : Y ⟶ S) (f₁ : Y ⟶ T a₁) (f₂ : Y ⟶ T a₂)
    (hf₁ : f₁ ≫ q a₁ = r) (hf₂ : f₂ ≫ q a₂ = r)
    {Z : C} (h : Z ⟶ Y)
    {i : B a₁} {j : B a₂} (b₁ : Z ⟶ X a₁ i) (b₂ : Z ⟶ X a₂ j)
    (hb₁ : b₁ ≫ g a₁ i = h ≫ f₁) (hb₂ : b₂ ≫ g a₂ j = h ≫ f₂) :
    (F.map h.op.toLoc).toFunctor.map
      (gluedHom g q hg D M₁ M₂ e₁ e₂ r f₁ f₂ hf₁ hf₂) =
        localMor g q D M₁ M₂ e₁ e₂ r f₁ f₂ hf₁ hf₂ h b₁ b₂ hb₁ hb₂ := by
  let s := Presieve.IsSheafFor.amalgamate
    (((isSheaf_iff_isSheaf_of_type _ _).1
      (IsPrestack.isSheaf J ((F.map f₁.op.toLoc).toFunctor.obj M₁)
        ((F.map f₂.op.toLoc).toFunctor.obj M₂))).isSheafFor _
          (by simpa using localSieve_mem g hg f₁ f₂)) _
      (localFamily_compatible g q D M₁ M₂ e₁ e₂ r f₁ f₂ hf₁ hf₂)
  have hs : (localFamily g q D M₁ M₂ e₁ e₂ r f₁ f₂ hf₁ hf₂).IsAmalgamation s :=
    Presieve.IsSheafFor.isAmalgamation
      (((isSheaf_iff_isSheaf_of_type _ _).1
        (IsPrestack.isSheaf J ((F.map f₁.op.toLoc).toFunctor.obj M₁)
          ((F.map f₂.op.toLoc).toFunctor.obj M₂))).isSheafFor _
            (by simpa using localSieve_mem g hg f₁ f₂))
      (localFamily_compatible g q D M₁ M₂ e₁ e₂ r f₁ f₂ hf₁ hf₂)
  simpa [s, gluedHom,
    localFamily_eq g q D M₁ M₂ e₁ e₂ r f₁ f₂ hf₁ hf₂
      (Over.homMk h (by simp) : Over.mk h ⟶ Over.mk (𝟙 Y))
      (mem_localSieve g f₁ f₂ h b₁ b₂ hb₁ hb₂) b₁ b₂ hb₁ hb₂,
    presheafHomObjHomEquiv, pullHom, mapComp'_id_comp_hom_app,
    mapComp'_id_comp_inv_app] using
      hs (Over.homMk h (by simp) : Over.mk h ⟶ Over.mk (𝟙 Y))
        (mem_localSieve g f₁ f₂ h b₁ b₂ hb₁ hb₂)

set_option backward.isDefEq.respectTransparency false in
lemma localMorCore_self
    (D : F.DescentData (fun k : Σ a, B a ↦ g k.1 k.2 ≫ q k.1))
    {a : A} (M : F.obj (.mk (op (T a))))
    (e : (F.toDescentData (g a)).obj M ≅ restrict g q D a)
    {Y : C} (r : Y ⟶ S) (f : Y ⟶ T a) (hf : f ≫ q a = r)
    {Z : C} (h : Z ⟶ Y) {i : B a} (b : Z ⟶ X a i)
    (hb : b ≫ g a i = h ≫ f) :
    localMorCore g q D M M e e r f f hf hf h b b hb hb = 𝟙 _ := by
  let ei : ((F.toDescentData (g a)).obj M).obj i ≅ (restrict g q D a).obj i :=
    { hom := e.hom.hom i
      inv := e.inv.hom i
      hom_inv_id := congr_fun (congr_arg DescentData.Hom.hom e.hom_inv_id) i
      inv_hom_id := congr_fun (congr_arg DescentData.Hom.hom e.inv_hom_id) i }
  dsimp [localMorCore]
  rw [D.hom_self (i := ⟨a, i⟩) (h ≫ r) b
    (by rw [← Category.assoc, hb, Category.assoc, hf])]
  let K := F.mapComp' (g a i).op.toLoc b.op.toLoc
    (f.op.toLoc ≫ h.op.toLoc) (by grind)
  change K.hom.toNatTrans.app M ≫
      (F.map b.op.toLoc).toFunctor.map (e.hom.hom i) ≫ 𝟙 _ ≫
      (F.map b.op.toLoc).toFunctor.map (e.inv.hom i) ≫
      K.inv.toNatTrans.app M = 𝟙 _
  have heb := ((F.map b.op.toLoc).toFunctor.mapIso ei).hom_inv_id
  dsimp [ei] at heb
  rw [Category.id_comp, reassoc_of% heb]
  simp

set_option backward.isDefEq.respectTransparency false in
lemma localMorCore_comp
    (D : F.DescentData (fun k : Σ a, B a ↦ g k.1 k.2 ≫ q k.1))
    {a₁ a₂ a₃ : A}
    (M₁ : F.obj (.mk (op (T a₁)))) (M₂ : F.obj (.mk (op (T a₂))))
    (M₃ : F.obj (.mk (op (T a₃))))
    (e₁ : (F.toDescentData (g a₁)).obj M₁ ≅ restrict g q D a₁)
    (e₂ : (F.toDescentData (g a₂)).obj M₂ ≅ restrict g q D a₂)
    (e₃ : (F.toDescentData (g a₃)).obj M₃ ≅ restrict g q D a₃)
    {Y : C} (r : Y ⟶ S) (f₁ : Y ⟶ T a₁) (f₂ : Y ⟶ T a₂)
    (f₃ : Y ⟶ T a₃) (hf₁ : f₁ ≫ q a₁ = r) (hf₂ : f₂ ≫ q a₂ = r)
    (hf₃ : f₃ ≫ q a₃ = r) {Z : C} (h : Z ⟶ Y)
    {i : B a₁} {j : B a₂} {k : B a₃}
    (b₁ : Z ⟶ X a₁ i) (b₂ : Z ⟶ X a₂ j) (b₃ : Z ⟶ X a₃ k)
    (hb₁ : b₁ ≫ g a₁ i = h ≫ f₁) (hb₂ : b₂ ≫ g a₂ j = h ≫ f₂)
    (hb₃ : b₃ ≫ g a₃ k = h ≫ f₃) :
    localMorCore g q D M₁ M₂ e₁ e₂ r f₁ f₂ hf₁ hf₂ h b₁ b₂ hb₁ hb₂ ≫
      localMorCore g q D M₂ M₃ e₂ e₃ r f₂ f₃ hf₂ hf₃ h b₂ b₃ hb₂ hb₃ =
        localMorCore g q D M₁ M₃ e₁ e₃ r f₁ f₃ hf₁ hf₃ h b₁ b₃ hb₁ hb₃ := by
  let ej : ((F.toDescentData (g a₂)).obj M₂).obj j ≅ (restrict g q D a₂).obj j :=
    { hom := e₂.hom.hom j
      inv := e₂.inv.hom j
      hom_inv_id := congr_fun (congr_arg DescentData.Hom.hom e₂.hom_inv_id) j
      inv_hom_id := congr_fun (congr_arg DescentData.Hom.hom e₂.inv_hom_id) j }
  dsimp [localMorCore]
  simp only [Category.assoc, Cat.Hom.inv_hom_id_toNatTrans_app_assoc]
  have heb := ((F.map b₂.op.toLoc).toFunctor.mapIso ej).inv_hom_id
  dsimp [ej] at heb
  rw [reassoc_of% heb]
  have hD := D.hom_comp (i₁ := ⟨a₁, i⟩) (i₂ := ⟨a₂, j⟩) (i₃ := ⟨a₃, k⟩)
    (h ≫ r) b₁ b₂ b₃
    (by rw [← Category.assoc, hb₁, Category.assoc, hf₁])
    (by rw [← Category.assoc, hb₂, Category.assoc, hf₂])
    (by rw [← Category.assoc, hb₃, Category.assoc, hf₃])
  rw [reassoc_of% hD]

set_option backward.isDefEq.respectTransparency false in
lemma localMor_self
    (D : F.DescentData (fun k : Σ a, B a ↦ g k.1 k.2 ≫ q k.1))
    {a : A} (M : F.obj (.mk (op (T a))))
    (e : (F.toDescentData (g a)).obj M ≅ restrict g q D a)
    {Y : C} (r : Y ⟶ S) (f : Y ⟶ T a) (hf : f ≫ q a = r)
    {Z : C} (h : Z ⟶ Y) {i : B a} (b : Z ⟶ X a i)
    (hb : b ≫ g a i = h ≫ f) :
    localMor g q D M M e e r f f hf hf h b b hb hb = 𝟙 _ := by
  dsimp only [localMor]
  rw [localMorCore_self g q D M e r f hf h b hb]
  simp

set_option backward.isDefEq.respectTransparency false in
lemma localMor_comp
    (D : F.DescentData (fun k : Σ a, B a ↦ g k.1 k.2 ≫ q k.1))
    {a₁ a₂ a₃ : A}
    (M₁ : F.obj (.mk (op (T a₁)))) (M₂ : F.obj (.mk (op (T a₂))))
    (M₃ : F.obj (.mk (op (T a₃))))
    (e₁ : (F.toDescentData (g a₁)).obj M₁ ≅ restrict g q D a₁)
    (e₂ : (F.toDescentData (g a₂)).obj M₂ ≅ restrict g q D a₂)
    (e₃ : (F.toDescentData (g a₃)).obj M₃ ≅ restrict g q D a₃)
    {Y : C} (r : Y ⟶ S) (f₁ : Y ⟶ T a₁) (f₂ : Y ⟶ T a₂)
    (f₃ : Y ⟶ T a₃) (hf₁ : f₁ ≫ q a₁ = r) (hf₂ : f₂ ≫ q a₂ = r)
    (hf₃ : f₃ ≫ q a₃ = r) {Z : C} (h : Z ⟶ Y)
    {i : B a₁} {j : B a₂} {k : B a₃}
    (b₁ : Z ⟶ X a₁ i) (b₂ : Z ⟶ X a₂ j) (b₃ : Z ⟶ X a₃ k)
    (hb₁ : b₁ ≫ g a₁ i = h ≫ f₁) (hb₂ : b₂ ≫ g a₂ j = h ≫ f₂)
    (hb₃ : b₃ ≫ g a₃ k = h ≫ f₃) :
    localMor g q D M₁ M₂ e₁ e₂ r f₁ f₂ hf₁ hf₂ h b₁ b₂ hb₁ hb₂ ≫
      localMor g q D M₂ M₃ e₂ e₃ r f₂ f₃ hf₂ hf₃ h b₂ b₃ hb₂ hb₃ =
        localMor g q D M₁ M₃ e₁ e₃ r f₁ f₃ hf₁ hf₃ h b₁ b₃ hb₁ hb₃ := by
  dsimp only [localMor]
  simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc]
  have hc := localMorCore_comp g q D M₁ M₂ M₃ e₁ e₂ e₃ r f₁ f₂ f₃
    hf₁ hf₂ hf₃ h b₁ b₂ b₃ hb₁ hb₂ hb₃
  rw [reassoc_of% hc]

set_option backward.isDefEq.respectTransparency false in
lemma hom_ext_of_sieve {Y : C} (R : Sieve (Over.mk (𝟙 Y))) (hR : R ∈ J.over Y _)
    {M N : F.obj (.mk (op Y))} {u v : M ⟶ N}
    (huv : ∀ {Z : C} (h : Z ⟶ Y),
      R (Over.homMk h : Over.mk h ⟶ Over.mk (𝟙 Y)) →
        (F.map h.op.toLoc).toFunctor.map u = (F.map h.op.toLoc).toFunctor.map v) :
    u = v := by
  refine F.presheafHomObjHomEquiv.injective ?_
  refine (((isSheaf_iff_isSheaf_of_type _ _).1
    (IsPrestack.isSheaf J M N)).isSeparated _ hR).ext ?_
  rintro Z h hh
  obtain rfl : h = (Over.homMk Z.hom (by simp) : Z ⟶ Over.mk (𝟙 Y)) := by
    ext
    simpa using Over.w h
  have hmap := huv Z.hom hh
  dsimp [presheafHomObjHomEquiv, Pseudofunctor.presheafHom, pullHom]
  simp only [Functor.map_comp, Category.assoc]
  rw [hmap]

set_option backward.isDefEq.respectTransparency false in
lemma hom_ext_of_map_eq
    (hg : ∀ a, Sieve.ofArrows (X a) (g a) ∈ J (T a))
    {a₁ a₂ : A} {Y : C} (f₁ : Y ⟶ T a₁) (f₂ : Y ⟶ T a₂)
    (M₁ : F.obj (.mk (op (T a₁)))) (M₂ : F.obj (.mk (op (T a₂))))
    {u v : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      (F.map f₂.op.toLoc).toFunctor.obj M₂}
    (huv : ∀ {Z : C} (h : Z ⟶ Y) {i : B a₁} {j : B a₂}
      (b₁ : Z ⟶ X a₁ i) (b₂ : Z ⟶ X a₂ j)
      (_ : b₁ ≫ g a₁ i = h ≫ f₁) (_ : b₂ ≫ g a₂ j = h ≫ f₂),
      (F.map h.op.toLoc).toFunctor.map u = (F.map h.op.toLoc).toFunctor.map v) :
    u = v := by
  apply hom_ext_of_sieve (J := J) (localSieve g f₁ f₂)
    (localSieve_mem g hg f₁ f₂)
  intro Z h hh
  obtain ⟨⟨_, b₁, _, ⟨i⟩, hb₁⟩, ⟨_, b₂, _, ⟨j⟩, hb₂⟩⟩ := hh
  exact huv h b₁ b₂ hb₁ hb₂

/-- A common local refinement on which three lifts through potentially different
outer members factor through their respective inner covers. -/
abbrev localSieve₃ {a₁ a₂ a₃ : A} {Y : C}
    (f₁ : Y ⟶ T a₁) (f₂ : Y ⟶ T a₂) (f₃ : Y ⟶ T a₃) :
    Sieve (Over.mk (𝟙 Y)) :=
  (Sieve.overEquiv (Over.mk (𝟙 Y))).symm
    ((Sieve.pullback f₁ (Sieve.ofArrows (X a₁) (g a₁)) ⊓
      Sieve.pullback f₂ (Sieve.ofArrows (X a₂) (g a₂))) ⊓
        Sieve.pullback f₃ (Sieve.ofArrows (X a₃) (g a₃)))

lemma localSieve₃_mem
    (hg : ∀ a, Sieve.ofArrows (X a) (g a) ∈ J (T a))
    {a₁ a₂ a₃ : A} {Y : C}
    (f₁ : Y ⟶ T a₁) (f₂ : Y ⟶ T a₂) (f₃ : Y ⟶ T a₃) :
    localSieve₃ g f₁ f₂ f₃ ∈ J.over Y _ := by
  rw [J.mem_over_iff, OrderIso.apply_symm_apply]
  exact J.intersection_covering
    (J.intersection_covering
      (J.pullback_stable f₁ (hg a₁)) (J.pullback_stable f₂ (hg a₂)))
    (J.pullback_stable f₃ (hg a₃))

set_option backward.isDefEq.respectTransparency false in
lemma gluedHom_self
    (hg : ∀ a, Sieve.ofArrows (X a) (g a) ∈ J (T a))
    (D : F.DescentData (fun k : Σ a, B a ↦ g k.1 k.2 ≫ q k.1))
    {a : A} (M : F.obj (.mk (op (T a))))
    (e : (F.toDescentData (g a)).obj M ≅ restrict g q D a)
    {Y : C} (r : Y ⟶ S) (f : Y ⟶ T a) (hf : f ≫ q a = r) :
    gluedHom g q hg D M M e e r f f hf hf = 𝟙 _ := by
  apply hom_ext_of_map_eq g hg f f M M
  intro Z h i j b₁ b₂ hb₁ hb₂
  rw [map_gluedHom g q hg D M M e e r f f hf hf h b₁ b₂ hb₁ hb₂,
    Functor.map_id]
  rw [localMor_unique g q D M M e e r f f hf hf h b₁ b₂ b₁ b₁
    hb₁ hb₂ hb₁ hb₁]
  exact localMor_self g q D M e r f hf h b₁ hb₁

set_option backward.isDefEq.respectTransparency false in
lemma gluedHom_comp
    (hg : ∀ a, Sieve.ofArrows (X a) (g a) ∈ J (T a))
    (D : F.DescentData (fun k : Σ a, B a ↦ g k.1 k.2 ≫ q k.1))
    {a₁ a₂ a₃ : A}
    (M₁ : F.obj (.mk (op (T a₁)))) (M₂ : F.obj (.mk (op (T a₂))))
    (M₃ : F.obj (.mk (op (T a₃))))
    (e₁ : (F.toDescentData (g a₁)).obj M₁ ≅ restrict g q D a₁)
    (e₂ : (F.toDescentData (g a₂)).obj M₂ ≅ restrict g q D a₂)
    (e₃ : (F.toDescentData (g a₃)).obj M₃ ≅ restrict g q D a₃)
    {Y : C} (r : Y ⟶ S) (f₁ : Y ⟶ T a₁) (f₂ : Y ⟶ T a₂)
    (f₃ : Y ⟶ T a₃) (hf₁ : f₁ ≫ q a₁ = r) (hf₂ : f₂ ≫ q a₂ = r)
    (hf₃ : f₃ ≫ q a₃ = r) :
    gluedHom g q hg D M₁ M₂ e₁ e₂ r f₁ f₂ hf₁ hf₂ ≫
      gluedHom g q hg D M₂ M₃ e₂ e₃ r f₂ f₃ hf₂ hf₃ =
        gluedHom g q hg D M₁ M₃ e₁ e₃ r f₁ f₃ hf₁ hf₃ := by
  apply hom_ext_of_sieve (J := J) (localSieve₃ g f₁ f₂ f₃)
    (localSieve₃_mem g hg f₁ f₂ f₃)
  intro Z h hh
  obtain ⟨⟨⟨_, b₁, _, ⟨i⟩, hb₁⟩, ⟨_, b₂, _, ⟨j⟩, hb₂⟩⟩,
    ⟨_, b₃, _, ⟨k⟩, hb₃⟩⟩ := hh
  rw [Functor.map_comp,
    map_gluedHom g q hg D M₁ M₂ e₁ e₂ r f₁ f₂ hf₁ hf₂ h b₁ b₂ hb₁ hb₂,
    map_gluedHom g q hg D M₂ M₃ e₂ e₃ r f₂ f₃ hf₂ hf₃ h b₂ b₃ hb₂ hb₃,
    map_gluedHom g q hg D M₁ M₃ e₁ e₃ r f₁ f₃ hf₁ hf₃ h b₁ b₃ hb₁ hb₃,
    localMor_comp g q D M₁ M₂ M₃ e₁ e₂ e₃ r f₁ f₂ f₃
      hf₁ hf₂ hf₃ h b₁ b₂ b₃ hb₁ hb₂ hb₃]

set_option backward.isDefEq.respectTransparency false in
lemma pullHom_gluedHom
    (hg : ∀ a, Sieve.ofArrows (X a) (g a) ∈ J (T a))
    (D : F.DescentData (fun z : Σ a, B a ↦ g z.1 z.2 ≫ q z.1))
    {a₁ a₂ : A} (M₁ : F.obj (.mk (op (T a₁))))
    (M₂ : F.obj (.mk (op (T a₂))))
    (e₁ : (F.toDescentData (g a₁)).obj M₁ ≅ restrict g q D a₁)
    (e₂ : (F.toDescentData (g a₂)).obj M₂ ≅ restrict g q D a₂)
    {Y' Y : C} (k : Y' ⟶ Y) (r : Y ⟶ S) (r' : Y' ⟶ S) (hr : k ≫ r = r')
    (f₁ : Y ⟶ T a₁) (f₂ : Y ⟶ T a₂)
    (hf₁ : f₁ ≫ q a₁ = r) (hf₂ : f₂ ≫ q a₂ = r)
    (f₁' : Y' ⟶ T a₁) (f₂' : Y' ⟶ T a₂)
    (hk₁ : k ≫ f₁ = f₁') (hk₂ : k ≫ f₂ = f₂') :
    pullHom (gluedHom g q hg D M₁ M₂ e₁ e₂ r f₁ f₂ hf₁ hf₂)
        k f₁' f₂' hk₁ hk₂ =
      gluedHom g q hg D M₁ M₂ e₁ e₂ r' f₁' f₂'
        (by rw [← hk₁, Category.assoc, hf₁, hr])
        (by rw [← hk₂, Category.assoc, hf₂, hr]) := by
  subst f₁'
  subst f₂'
  subst r'
  apply hom_ext_of_map_eq g hg (k ≫ f₁) (k ≫ f₂) M₁ M₂
  intro Z h i j b₁ b₂ hb₁ hb₂
  rw [map_gluedHom g q hg D M₁ M₂ e₁ e₂ (k ≫ r) (k ≫ f₁) (k ≫ f₂)
    (by rw [Category.assoc, hf₁]) (by rw [Category.assoc, hf₂])
    h b₁ b₂ hb₁ hb₂]
  dsimp [pullHom]
  simp only [Functor.map_comp, Category.assoc]
  rw [← F.mapComp'_naturality_1 k.op.toLoc h.op.toLoc (h ≫ k).op.toLoc
    (by grind) (gluedHom g q hg D M₁ M₂ e₁ e₂ r f₁ f₂ hf₁ hf₂)]
  rw [map_gluedHom g q hg D M₁ M₂ e₁ e₂ r f₁ f₂ hf₁ hf₂
    (h ≫ k) b₁ b₂ (by rw [hb₁, ← Category.assoc])
    (by rw [hb₂, ← Category.assoc])]
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
      (F.mapComp' f₁.op.toLoc k.op.toLoc (f₁.op.toLoc ≫ k.op.toLoc) rfl).hom.toNatTrans.app M₁ ≫
        (F.mapComp' f₁.op.toLoc k.op.toLoc (k ≫ f₁).op.toLoc hfk₁).inv.toNatTrans.app M₁ =
          𝟙 _ := by
    exact Cat.Hom.hom_inv_id_toNatTrans_app
      (F.mapComp' f₁.op.toLoc k.op.toLoc (k ≫ f₁).op.toLoc hfk₁) M₁
  have hcancel₂ :
      (F.mapComp' f₂.op.toLoc k.op.toLoc (k ≫ f₂).op.toLoc hfk₂).hom.toNatTrans.app M₂ ≫
        (F.mapComp' f₂.op.toLoc k.op.toLoc (f₂.op.toLoc ≫ k.op.toLoc) rfl).inv.toNatTrans.app M₂ =
          𝟙 _ := by
    exact Cat.Hom.hom_inv_id_toNatTrans_app
      (F.mapComp' f₂.op.toLoc k.op.toLoc (k ≫ f₂).op.toLoc hfk₂) M₂
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
    rfl M₁
  have hgb₁ : (g a₁ i).op.toLoc ≫ b₁.op.toLoc =
      f₁.op.toLoc ≫ k.op.toLoc ≫ h.op.toLoc := by
    simpa only [op_comp, Quiver.Hom.comp_toLoc, Category.assoc] using
      congrArg (fun z ↦ z.op.toLoc) hb₁
  have H₂ := mapComp'_hom_app_heq (F := F)
    (f := (g a₁ i).op.toLoc) (f' := (g a₁ i).op.toLoc)
    (h := b₁.op.toLoc) (h' := b₁.op.toLoc)
    (fh := f₁.op.toLoc ≫ k.op.toLoc ≫ h.op.toLoc)
    (fh' := (f₁.op.toLoc ≫ k.op.toLoc) ≫ h.op.toLoc)
    rfl rfl (Category.assoc _ _ _).symm
    hgb₁ (hgb₁.trans (Category.assoc _ _ _).symm) M₁
  have hgb₂ : (g a₂ j).op.toLoc ≫ b₂.op.toLoc =
      f₂.op.toLoc ≫ k.op.toLoc ≫ h.op.toLoc := by
    simpa only [op_comp, Quiver.Hom.comp_toLoc, Category.assoc] using
      congrArg (fun z ↦ z.op.toLoc) hb₂
  have H₃ := mapComp'_inv_app_heq (F := F)
    (f := (g a₂ j).op.toLoc) (f' := (g a₂ j).op.toLoc)
    (h := b₂.op.toLoc) (h' := b₂.op.toLoc)
    (fh := f₂.op.toLoc ≫ k.op.toLoc ≫ h.op.toLoc)
    (fh' := (f₂.op.toLoc ≫ k.op.toLoc) ≫ h.op.toLoc)
    rfl rfl (Category.assoc _ _ _).symm
    hgb₂ (hgb₂.trans (Category.assoc _ _ _).symm) M₂
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
    rfl M₂
  have Ecomp₁ :
      (F.map (k ≫ f₁).op.toLoc ≫ F.map h.op.toLoc).toFunctor.obj M₁ =
        (F.map (f₁.op.toLoc ≫ k.op.toLoc) ≫ F.map h.op.toLoc).toFunctor.obj M₁ :=
    congrArg (fun z ↦ (F.map z ≫ F.map h.op.toLoc).toFunctor.obj M₁) hfk₁.symm
  have Eassoc₁ :
      (F.map (f₁.op.toLoc ≫ k.op.toLoc ≫ h.op.toLoc)).toFunctor.obj M₁ =
        (F.map ((f₁.op.toLoc ≫ k.op.toLoc) ≫ h.op.toLoc)).toFunctor.obj M₁ := by
    rw [Category.assoc]
  have Eassoc₂ :
      (F.map (f₂.op.toLoc ≫ k.op.toLoc ≫ h.op.toLoc)).toFunctor.obj M₂ =
        (F.map ((f₂.op.toLoc ≫ k.op.toLoc) ≫ h.op.toLoc)).toFunctor.obj M₂ := by
    rw [Category.assoc]
  have Ecomp₂ :
      (F.map (k ≫ f₂).op.toLoc ≫ F.map h.op.toLoc).toFunctor.obj M₂ =
        (F.map (f₂.op.toLoc ≫ k.op.toLoc) ≫ F.map h.op.toLoc).toFunctor.obj M₂ :=
    congrArg (fun z ↦ (F.map z ≫ F.map h.op.toLoc).toFunctor.obj M₂) hfk₂.symm
  let L := (F.map b₁.op.toLoc).toFunctor.map (e₁.hom.hom i) ≫
    D.hom (i₁ := ⟨a₁, i⟩) (i₂ := ⟨a₂, j⟩) (h ≫ k ≫ r) b₁ b₂
      (by rw [← Category.assoc b₁ (g a₁ i) (q a₁), hb₁,
        ← Category.assoc h k f₁, Category.assoc (h ≫ k) f₁ (q a₁),
        hf₁, Category.assoc h k r])
      (by rw [← Category.assoc b₂ (g a₂ j) (q a₂), hb₂,
        ← Category.assoc h k f₂, Category.assoc (h ≫ k) f₂ (q a₂),
        hf₂, Category.assoc h k r]) ≫
    (F.map b₂.op.toLoc).toFunctor.map (e₂.inv.hom j)
  have H₂L := heq_comp Eassoc₁ rfl rfl H₂ (HEq.rfl : L ≍ L)
  have H₃₄ := heq_comp rfl Eassoc₂ Ecomp₂ H₃ H₄
  have Htail := heq_comp Eassoc₁ rfl Ecomp₂ H₂L H₃₄
  exact eq_of_heq (heq_comp Ecomp₁ Eassoc₁ Ecomp₂ H₁
    (by simpa only [L, Category.assoc] using Htail))

/-- The outer descent datum obtained by gluing the restriction of composite
descent data along every inner covering family. -/
noncomputable def outerDatum
    (hg : ∀ a, Sieve.ofArrows (X a) (g a) ∈ J (T a))
    (D : F.DescentData (fun z : Σ a, B a ↦ g z.1 z.2 ≫ q z.1))
    (M : ∀ a, F.obj (.mk (op (T a))))
    (e : ∀ a, (F.toDescentData (g a)).obj (M a) ≅ restrict g q D a) :
    F.DescentData q where
  obj a := M a
  hom Y r a₁ a₂ f₁ f₂ hf₁ hf₂ :=
    gluedHom g q hg D (M a₁) (M a₂) (e a₁) (e a₂) r f₁ f₂ hf₁ hf₂
  pullHom_hom Y' Y k r r' hr a₁ a₂ f₁ f₂ hf₁ hf₂ f₁' f₂' hk₁ hk₂ :=
    pullHom_gluedHom g q hg D (M a₁) (M a₂) (e a₁) (e a₂)
      k r r' hr f₁ f₂ hf₁ hf₂ f₁' f₂' hk₁ hk₂
  hom_self Y r a f hf := gluedHom_self g q hg D (M a) (e a) r f hf
  hom_comp Y r a₁ a₂ a₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ :=
    gluedHom_comp g q hg D (M a₁) (M a₂) (M a₃) (e a₁) (e a₂) (e a₃)
      r f₁ f₂ f₃ hf₁ hf₂ hf₃

/-- Pulling the glued outer datum back to the fully composed family recovers the
original composite descent datum. -/
noncomputable def outerPullbackIso
    (hg : ∀ a, Sieve.ofArrows (X a) (g a) ∈ J (T a))
    (D : F.DescentData (fun z : Σ a, B a ↦ g z.1 z.2 ≫ q z.1))
    (M : ∀ a, F.obj (.mk (op (T a))))
    (e : ∀ a, (F.toDescentData (g a)).obj (M a) ≅ restrict g q D a) :
    (DescentData.pullFunctor F (f := q) (p := 𝟙 S)
      (f' := fun z : Σ a, B a ↦ g z.1 z.2 ≫ q z.1) (p' := fun z ↦ g z.1 z.2)
      (fun z ↦ by simp)).obj (outerDatum g q hg D M e) ≅ D :=
  DescentData.isoMk
    (fun z ↦
      { hom := (e z.1).hom.hom z.2
        inv := (e z.1).inv.hom z.2
        hom_inv_id := congr_fun (congr_arg DescentData.Hom.hom (e z.1).hom_inv_id) z.2
        inv_hom_id := congr_fun (congr_arg DescentData.Hom.hom (e z.1).inv_hom_id) z.2 })
    (by
      intro Y r z₁ z₂ b₁ b₂ hb₁ hb₂
      let w : ∀ z : Σ a, B a, g z.1 z.2 ≫ q z.1 =
          (g z.1 z.2 ≫ q z.1) ≫ 𝟙 S := fun z ↦ by simp
      dsimp only [DescentData.pullFunctor, DescentData.pullFunctorObj]
      rw [DescentData.pullFunctorObjHom_eq
        (f := q) (f' := fun z : Σ a, B a ↦ g z.1 z.2 ≫ q z.1)
        (α := fun z : Σ a, B a ↦ z.1) (p := 𝟙 S) (p' := fun z ↦ g z.1 z.2)
        (w := w) (outerDatum g q hg D M e)
        (b₁ ≫ g z₁.1 z₁.2 ≫ q z₁.1) b₁ b₂ r
        (b₁ ≫ g z₁.1 z₁.2) (b₂ ≫ g z₂.1 z₂.2)
        (by simp [Category.assoc]) (by rw [hb₂, hb₁])
        (by simpa using hb₁) rfl rfl]
      dsimp only [outerDatum]
      have hf₁ : (b₁ ≫ g z₁.1 z₁.2) ≫ q z₁.1 = r := by
        simpa only [Category.assoc] using hb₁
      have hf₂ : (b₂ ≫ g z₂.1 z₂.2) ≫ q z₂.1 = r := by
        simpa only [Category.assoc] using hb₂
      let G := gluedHom g q hg D (M z₁.1) (M z₂.1) (e z₁.1) (e z₂.1) r
        (b₁ ≫ g z₁.1 z₁.2) (b₂ ≫ g z₂.1 z₂.2) hf₁ hf₂
      have hm := map_gluedHom g q hg D (M z₁.1) (M z₂.1) (e z₁.1) (e z₂.1) r
        (b₁ ≫ g z₁.1 z₁.2) (b₂ ≫ g z₂.1 z₂.2) hf₁ hf₂
        (𝟙 Y) b₁ b₂ (by simp) (by simp)
      have hp := map_eq_pullHom (F := F) G (𝟙 Y)
        (b₁ ≫ g z₁.1 z₁.2) (b₂ ≫ g z₂.1 z₂.2) (by simp) (by simp)
      rw [pullHom_id] at hp
      have hG : G =
          (F.mapComp' (b₁ ≫ g z₁.1 z₁.2).op.toLoc (𝟙 Y).op.toLoc
            (b₁ ≫ g z₁.1 z₁.2).op.toLoc (by simp)).hom.toNatTrans.app (M z₁.1) ≫
          (F.map (𝟙 Y).op.toLoc).toFunctor.map G ≫
          (F.mapComp' (b₂ ≫ g z₂.1 z₂.2).op.toLoc (𝟙 Y).op.toLoc
            (b₂ ≫ g z₂.1 z₂.2).op.toLoc (by simp)).inv.toNatTrans.app (M z₂.1) := by
        rw [hp]
        simp
      dsimp only [G] at hG hm
      rw [hG, hm]
      dsimp [localMor, localMorCore]
      simp only [Category.assoc, Cat.Hom.inv_hom_id_toNatTrans_app_assoc,
        Cat.Hom.hom_inv_id_toNatTrans_app_assoc]
      let idY : LocallyDiscrete.mk (op Y) ⟶ LocallyDiscrete.mk (op Y) := 𝟙 _
      let c₁ := (g z₁.1 z₁.2).op.toLoc ≫ b₁.op.toLoc
      let A₁ := F.mapComp' (g z₁.1 z₁.2).op.toLoc b₁.op.toLoc c₁ rfl
      let B₁ := F.mapComp' c₁ idY c₁ (Category.comp_id c₁)
      let C₁ := F.mapComp' c₁ idY (c₁ ≫ idY) rfl
      let D₁ := F.mapComp' (g z₁.1 z₁.2).op.toLoc b₁.op.toLoc (c₁ ≫ idY)
        (Category.comp_id c₁).symm
      have hc₁ : c₁ ≫ idY = c₁ := Category.comp_id c₁
      have EC₁ : (F.map (c₁ ≫ idY)).toFunctor.obj (M z₁.1) =
          (F.map c₁).toFunctor.obj (M z₁.1) :=
        congrArg (fun z ↦ (F.map z).toFunctor.obj (M z₁.1)) hc₁
      have HC₁ := mapComp'_inv_app_heq (F := F)
        (f := c₁) (f' := c₁) (h := idY) (h' := idY)
        (fh := c₁ ≫ idY) (fh' := c₁) rfl rfl hc₁ rfl hc₁ (M z₁.1)
      have HD₁ := mapComp'_hom_app_heq (F := F)
        (f := (g z₁.1 z₁.2).op.toLoc) (f' := (g z₁.1 z₁.2).op.toLoc)
        (h := b₁.op.toLoc) (h' := b₁.op.toLoc)
        (fh := c₁ ≫ idY) (fh' := c₁) rfl rfl hc₁ hc₁.symm rfl (M z₁.1)
      let P₁ := A₁.inv.toNatTrans.app (M z₁.1) ≫ B₁.hom.toNatTrans.app (M z₁.1)
      let R₁ := C₁.inv.toNatTrans.app (M z₁.1) ≫ D₁.hom.toNatTrans.app (M z₁.1)
      let R₁' := B₁.inv.toNatTrans.app (M z₁.1) ≫ A₁.hom.toNatTrans.app (M z₁.1)
      have HR₁ : R₁ ≍ R₁' := heq_comp rfl EC₁ rfl HC₁ HD₁
      have HPR₁ : P₁ ≫ R₁ ≍ P₁ ≫ R₁' :=
        heq_comp rfl rfl rfl HEq.rfl HR₁
      have hleft : P₁ ≫ R₁ = 𝟙 _ := by
        rw [eq_of_heq HPR₁]
        dsimp [P₁, R₁', A₁, B₁]
        simp
      have hleft' :
          A₁.inv.toNatTrans.app (M z₁.1) ≫ B₁.hom.toNatTrans.app (M z₁.1) ≫
            C₁.inv.toNatTrans.app (M z₁.1) ≫ D₁.hom.toNatTrans.app (M z₁.1) = 𝟙 _ := by
        simpa only [P₁, R₁, Category.assoc] using hleft
      let c₂ := (g z₂.1 z₂.2).op.toLoc ≫ b₂.op.toLoc
      let A₂ := F.mapComp' (g z₂.1 z₂.2).op.toLoc b₂.op.toLoc c₂ rfl
      let B₂ := F.mapComp' c₂ idY c₂ (Category.comp_id c₂)
      let C₂ := F.mapComp' c₂ idY (c₂ ≫ idY) rfl
      let D₂ := F.mapComp' (g z₂.1 z₂.2).op.toLoc b₂.op.toLoc (c₂ ≫ idY)
        (Category.comp_id c₂).symm
      have hc₂ : c₂ ≫ idY = c₂ := Category.comp_id c₂
      have EC₂ : (F.map (c₂ ≫ idY)).toFunctor.obj (M z₂.1) =
          (F.map c₂).toFunctor.obj (M z₂.1) :=
        congrArg (fun z ↦ (F.map z).toFunctor.obj (M z₂.1)) hc₂
      have HD₂ := mapComp'_inv_app_heq (F := F)
        (f := (g z₂.1 z₂.2).op.toLoc) (f' := (g z₂.1 z₂.2).op.toLoc)
        (h := b₂.op.toLoc) (h' := b₂.op.toLoc)
        (fh := c₂ ≫ idY) (fh' := c₂) rfl rfl hc₂ hc₂.symm rfl (M z₂.1)
      have HC₂ := mapComp'_hom_app_heq (F := F)
        (f := c₂) (f' := c₂) (h := idY) (h' := idY)
        (fh := c₂ ≫ idY) (fh' := c₂) rfl rfl hc₂ rfl hc₂ (M z₂.1)
      let P₂ := D₂.inv.toNatTrans.app (M z₂.1) ≫ C₂.hom.toNatTrans.app (M z₂.1)
      let P₂' := A₂.inv.toNatTrans.app (M z₂.1) ≫ B₂.hom.toNatTrans.app (M z₂.1)
      let R₂ := B₂.inv.toNatTrans.app (M z₂.1) ≫ A₂.hom.toNatTrans.app (M z₂.1)
      have HP₂ : P₂ ≍ P₂' := heq_comp rfl EC₂ rfl HD₂ HC₂
      have HPR₂ : P₂ ≫ R₂ ≍ P₂' ≫ R₂ :=
        heq_comp rfl rfl rfl HP₂ HEq.rfl
      have hright : P₂ ≫ R₂ = 𝟙 _ := by
        rw [eq_of_heq HPR₂]
        dsimp [P₂', R₂, A₂, B₂]
        simp
      have hright' :
          D₂.inv.toNatTrans.app (M z₂.1) ≫ C₂.hom.toNatTrans.app (M z₂.1) ≫
            B₂.inv.toNatTrans.app (M z₂.1) ≫ A₂.hom.toNatTrans.app (M z₂.1) = 𝟙 _ := by
        simpa only [P₂, R₂, Category.assoc] using hright
      dsimp [A₁, B₁, C₁, D₁, c₁, idY] at hleft'
      dsimp [A₂, B₂, C₂, D₂, c₂, idY] at hright'
      rw [reassoc_of% hleft', reassoc_of% hright']
      let ei₂ : ((F.toDescentData (g z₂.1)).obj (M z₂.1)).obj z₂.2 ≅
          (restrict g q D z₂.1).obj z₂.2 :=
        { hom := (e z₂.1).hom.hom z₂.2
          inv := (e z₂.1).inv.hom z₂.2
          hom_inv_id := congr_fun (congr_arg DescentData.Hom.hom (e z₂.1).hom_inv_id) z₂.2
          inv_hom_id := congr_fun (congr_arg DescentData.Hom.hom (e z₂.1).inv_hom_id) z₂.2 }
      have hei₂ := ((F.map b₂.op.toLoc).toFunctor.mapIso ei₂).inv_hom_id
      dsimp [ei₂] at hei₂
      rw [hei₂]
      have hDr := descentHom_heq (F := F) D (i₁ := z₁) (i₂ := z₂)
        (Category.id_comp r) b₁ b₂
        (by simpa only [Category.id_comp] using hb₁)
        (by simpa only [Category.id_comp] using hb₂) hb₁ hb₂
      rw [eq_of_heq hDr]
      exact (congrArg
        (fun z ↦ (F.map b₁.op.toLoc).toFunctor.map ((e z₁.1).hom.hom z₁.2) ≫ z)
        (Category.comp_id (D.hom (i₁ := z₁) (i₂ := z₂) r b₁ b₂ hb₁ hb₂))).symm)

/-- Pulling outer descent data to the fully composed family is an equivalence when
descent is effective for every inner family and the composite family is covering. -/
theorem pullFunctorIsEquivalence
    (hg : ∀ a, Sieve.ofArrows (X a) (g a) ∈ J (T a))
    (hcomp : Sieve.ofArrows (fun z : Σ a, B a ↦ X z.1 z.2)
      (fun z ↦ g z.1 z.2 ≫ q z.1) ∈ J S)
    (hinner : ∀ a, (F.toDescentData (g a)).IsEquivalence) :
    (DescentData.pullFunctor F (f := q) (p := 𝟙 S)
      (f' := fun z : Σ a, B a ↦ g z.1 z.2 ≫ q z.1) (p' := fun z ↦ g z.1 z.2)
      (fun z ↦ by simp)).IsEquivalence := by
  let H := DescentData.pullFunctor F (f := q) (p := 𝟙 S)
    (f' := fun z : Σ a, B a ↦ g z.1 z.2 ≫ q z.1) (p' := fun z ↦ g z.1 z.2)
    (fun z ↦ by simp)
  let hff := DescentData.fullyFaithfulPullFunctor F
    (f := q) (f' := fun z : Σ a, B a ↦ g z.1 z.2 ≫ q z.1)
    (α := fun z ↦ z.1) (p' := fun z ↦ g z.1 z.2) (fun z ↦ by simp) hcomp
  letI : H.Full := hff.full
  letI : H.Faithful := hff.faithful
  letI (a : A) : (F.toDescentData (g a)).IsEquivalence := hinner a
  letI : H.EssSurj := ⟨fun D ↦ by
    let M : ∀ a, F.obj (.mk (op (T a))) := fun a ↦
      (F.toDescentData (g a)).objPreimage (restrict g q D a)
    let e : ∀ a, (F.toDescentData (g a)).obj (M a) ≅ restrict g q D a := fun a ↦
      (F.toDescentData (g a)).objObjPreimageIso (restrict g q D a)
    exact ⟨outerDatum g q hg D M e, ⟨outerPullbackIso g q hg D M e⟩⟩⟩
  exact { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }

/-- Effective descent is transitive for an outer covering family and a covering
family on each outer member. -/
lemma isStackFor_family_iff_composite
    (hg : ∀ a, Sieve.ofArrows (X a) (g a) ∈ J (T a))
    (hcomp : Sieve.ofArrows (fun z : Σ a, B a ↦ X z.1 z.2)
      (fun z ↦ g z.1 z.2 ≫ q z.1) ∈ J S)
    (hinner : ∀ a, F.IsStackFor (Presieve.ofArrows (X a) (g a))) :
    F.IsStackFor (Presieve.ofArrows T q) ↔
      F.IsStackFor (Presieve.ofArrows (fun z : Σ a, B a ↦ X z.1 z.2)
        (fun z ↦ g z.1 z.2 ≫ q z.1)) := by
  have heq (a : A) : (F.toDescentData (g a)).IsEquivalence := by
    rw [← isStackFor_ofArrows_iff]
    exact hinner a
  letI : (DescentData.pullFunctor F (f := q) (p := 𝟙 S)
      (f' := fun z : Σ a, B a ↦ g z.1 z.2 ≫ q z.1) (p' := fun z ↦ g z.1 z.2)
      (fun z ↦ by simp)).IsEquivalence :=
    pullFunctorIsEquivalence g q hg hcomp heq
  exact isStackFor_iff_of_pullFunctor_isEquivalence F q
    (fun z : Σ a, B a ↦ g z.1 z.2 ≫ q z.1) (fun z ↦ z.1)
    (fun z ↦ g z.1 z.2) (fun z ↦ by simp)

end DescentFamilyComposition

end CategoryTheory.Pseudofunctor

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ v₂ u₁ u₂

variable {P : MorphismProperty Scheme.{u₁}} [P.IsMultiplicative]
  [P.IsStableUnderBaseChange]
  [IsZariskiLocalAtSource P]

/-- A Zariski stack satisfying effective descent for surjective `P`-morphisms
between affine schemes satisfies descent for every `P`-quasi-compact cover. -/
lemma isStackFor_propQCCover_of_affine_singletons_global
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u₁}ᵒᵖ) Cat.{v₂, u₂})
    [F.IsPrestack (Scheme.propQCTopology P)] [F.IsStack Scheme.zariskiTopology]
    (hsingle : ∀ {R S : CommRingCat.{u₁}} (f : R ⟶ S),
      P (Spec.map f) → Surjective (Spec.map f) →
        F.IsStackFor (.singleton (Spec.map f)))
    {S : Scheme.{u₁}} (𝒰 : S.Cover.{u₁} (Scheme.propQCPrecoverage P)) :
    F.IsStackFor 𝒰.presieve₀ := by
  let 𝒜 : S.Cover (Scheme.propQCPrecoverage P) :=
    S.affineCover.weaken Scheme.zariskiPrecoverage_le_propQCPrecoverage
  let 𝒱 (a : 𝒜.I₀) : (𝒜.X a).Cover (Scheme.propQCPrecoverage P) :=
    𝒰.pullback₁ (𝒜.f a)
  have hg (a : 𝒜.I₀) :
      Sieve.ofArrows (𝒱 a).X (𝒱 a).f ∈ Scheme.propQCTopology P (𝒜.X a) := by
    exact Precoverage.generate_mem_toGrothendieck (𝒱 a).mem₀
  have hinner (a : 𝒜.I₀) : F.IsStackFor (𝒱 a).presieve₀ := by
    dsimp [𝒱, 𝒜]
    exact AlgebraicGeometry.isStackFor_propQCCover_of_affine_singletons F hsingle (𝒱 a)
  have hcomp : Sieve.ofArrows
      (fun z : Σ a, (𝒱 a).I₀ ↦ (𝒱 z.1).X z.2)
      (fun z ↦ (𝒱 z.1).f z.2 ≫ 𝒜.f z.1) ∈ Scheme.propQCTopology P S := by
    exact Precoverage.generate_mem_toGrothendieck (𝒜.bind 𝒱).mem₀
  have houter : F.IsStackFor 𝒜.presieve₀ := by
    apply F.isStackFor (J := Scheme.zariskiTopology)
    simpa [𝒜] using S.affineCover.mem_grothendieckTopology
  have hcomposite : F.IsStackFor (Presieve.ofArrows
      (fun z : Σ a, (𝒱 a).I₀ ↦ (𝒱 z.1).X z.2)
      (fun z ↦ (𝒱 z.1).f z.2 ≫ 𝒜.f z.1)) :=
    (Pseudofunctor.DescentFamilyComposition.isStackFor_family_iff_composite
      (F := F) (J := Scheme.propQCTopology P)
      (fun a i ↦ (𝒱 a).f i) (fun a ↦ 𝒜.f a) hg hcomp hinner).mp houter
  have hrefines : Presieve.ofArrows
      (fun z : Σ a, (𝒱 a).I₀ ↦ (𝒱 z.1).X z.2)
      (fun z ↦ (𝒱 z.1).f z.2 ≫ 𝒜.f z.1) ≤
        (Sieve.generate 𝒰.presieve₀).arrows := by
    rintro Z f ⟨z⟩
    dsimp [𝒱] at z ⊢
    refine ⟨𝒰.X z.2, pullback.snd (𝒜.f z.1) (𝒰.f z.2), 𝒰.f z.2, ⟨z.2⟩, ?_⟩
    exact pullback.condition.symm
  have hgenerated : F.IsStackFor (Sieve.generate 𝒰.presieve₀).arrows :=
    Pseudofunctor.IsStackFor.of_le (F := F) hcomposite hcomp hrefines
  exact (F.IsStackFor_generate_iff 𝒰.presieve₀).mp hgenerated

/-- A Zariski stack that is already a prestack for the `P`-quasi-compact topology is a
stack for that topology as soon as effective descent holds for every surjective
`P`-morphism between affine schemes. -/
lemma isStack_propQCTopology_of_affine_singletons
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u₁}ᵒᵖ) Cat.{v₂, u₂})
    [F.IsPrestack (Scheme.propQCTopology P)] [F.IsStack Scheme.zariskiTopology]
    (hsingle : ∀ {R S : CommRingCat.{u₁}} (f : R ⟶ S),
      P (Spec.map f) → Surjective (Spec.map f) →
        F.IsStackFor (.singleton (Spec.map f))) :
    F.IsStack (Scheme.propQCTopology P) := by
  apply Pseudofunctor.IsStack.of_precoverage
  intro S R hR
  obtain ⟨𝒰, rfl⟩ :=
    (Precoverage.mem_iff_exists_zeroHypercover (J := Scheme.propQCPrecoverage P)).mp hR
  let 𝒱 := 𝒰.restrictIndexOfSmall.{u₁}
  have h𝒱 : F.IsStackFor 𝒱.presieve₀ :=
    isStackFor_propQCCover_of_affine_singletons_global F hsingle 𝒱
  apply Pseudofunctor.IsStackFor.of_le (F := F) h𝒱
    (Precoverage.generate_mem_toGrothendieck 𝒱.mem₀)
  rintro X f ⟨i⟩
  exact ⟨Precoverage.ZeroHypercover.Small.restrictFun 𝒰 i⟩

/-- Assuming morphism descent for the `P`-quasi-compact topology, the full stack
condition is equivalent to the Zariski stack condition together with effective descent
for surjective `P`-morphisms between affine schemes. -/
lemma isStack_propQCTopology_iff_of_isPrestack
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u₁}ᵒᵖ) Cat.{v₂, u₂})
    [F.IsPrestack (Scheme.propQCTopology P)] :
    F.IsStack (Scheme.propQCTopology P) ↔
      F.IsStack Scheme.zariskiTopology ∧
        ∀ {R S : CommRingCat.{u₁}} (f : R ⟶ S),
          P (Spec.map f) → Surjective (Spec.map f) →
            F.IsStackFor (.singleton (Spec.map f)) := by
  constructor
  · intro h
    letI : F.IsStack (Scheme.propQCTopology P) := h
    refine ⟨Pseudofunctor.IsStack.of_le
      (Scheme.zariskiTopology_le_propQCTopology (P := P)), ?_⟩
    intro R S f hf hs
    letI : Surjective (Spec.map f) := hs
    letI : QuasiCompact (Spec.map f) := by infer_instance
    exact F.isStackFor (.singleton (Spec.map f))
      (Scheme.Hom.generate_singleton_mem_propQCTopology (Spec.map f) hf)
  · rintro ⟨hzar, hsingle⟩
    letI : F.IsStack Scheme.zariskiTopology := hzar
    exact isStack_propQCTopology_of_affine_singletons (P := P) F hsingle

end AlgebraicGeometry
