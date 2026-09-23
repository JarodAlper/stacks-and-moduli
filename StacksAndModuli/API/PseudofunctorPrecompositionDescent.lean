module

public import StacksAndModuli.API.PseudofunctorDescentComposition
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime

/-!
# Descent after precomposition by a pullback-preserving functor

This file supplies the coherence bridge needed when a pseudofunctor is precomposed
with an ordinary functor.  It identifies the composite pseudofunctor's flexible
composition maps with the corresponding maps after applying the ordinary functor,
and maps chosen pullback diagrams along a functor that preserves them.
-/

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

universe t vC uC vD uD vE uE

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

/-- Use the ambient category's specified pullback as a chosen pullback. -/
noncomputable def Limits.ChosenPullback.ofHasPullback {X₁ X₂ S : C}
    (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S) [HasPullback f₁ f₂] :
    ChosenPullback f₁ f₂ where
  pullback := CategoryTheory.Limits.pullback f₁ f₂
  p₁ := CategoryTheory.Limits.pullback.fst f₁ f₂
  p₂ := CategoryTheory.Limits.pullback.snd f₁ f₂
  condition := CategoryTheory.Limits.pullback.condition
  isLimit := CategoryTheory.Limits.pullbackIsPullback f₁ f₂

/-- Build a chosen triple pullback from specified pairwise pullbacks and the
ambient pullback of the two adjacent pairwise pullbacks over their middle object. -/
noncomputable def Limits.ChosenPullback₃.ofHasPullback
    {X₁ X₂ X₃ S : C} {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S} {f₃ : X₃ ⟶ S}
    (sq₁₂ : ChosenPullback f₁ f₂) (sq₂₃ : ChosenPullback f₂ f₃)
    (sq₁₃ : ChosenPullback f₁ f₃) [HasPullback sq₁₂.p₂ sq₂₃.p₁] :
    ChosenPullback₃ sq₁₂ sq₂₃ sq₁₃ := by
  let cp := Limits.ChosenPullback.ofHasPullback sq₁₂.p₂ sq₂₃.p₁
  refine { chosenPullback := cp, l := ?_ }
  apply Classical.choice
  apply ChosenPullback.LiftStruct.nonempty
  · rw [Category.assoc, sq₁₂.hp₁, Category.assoc, sq₂₃.hp₂,
      ← sq₁₂.hp₂, ← sq₂₃.hp₁, ← Category.assoc, cp.condition,
      Category.assoc]
  · rw [Category.assoc, sq₁₂.hp₁]

/-- Map a chosen pullback along a functor, given a proof that its square remains
a pullback. -/
noncomputable def Limits.ChosenPullback.map (H : C ⥤ D) {X₁ X₂ S : C}
    {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S} (sq : ChosenPullback f₁ f₂)
    (hsq : IsPullback (H.map sq.p₁) (H.map sq.p₂) (H.map f₁) (H.map f₂)) :
    ChosenPullback (H.map f₁) (H.map f₂) where
  pullback := H.obj sq.pullback
  p₁ := H.map sq.p₁
  p₂ := H.map sq.p₂
  condition := hsq.w
  isLimit := hsq.isLimit

variable (H : C ⥤ D)
variable {X₁ X₂ X₃ S : C}
variable {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S} {f₃ : X₃ ⟶ S}
variable {sq₁₂ : ChosenPullback f₁ f₂} {sq₂₃ : ChosenPullback f₂ f₃}
variable {sq₁₃ : ChosenPullback f₁ f₃}

/-- Map a chosen triple pullback along a functor, using pullback proofs for its
constituent squares. -/
noncomputable def Limits.ChosenPullback₃.map
    (sq₃ : ChosenPullback₃ sq₁₂ sq₂₃ sq₁₃)
    (h₁₂ : IsPullback (H.map sq₁₂.p₁) (H.map sq₁₂.p₂)
      (H.map f₁) (H.map f₂))
    (h₂₃ : IsPullback (H.map sq₂₃.p₁) (H.map sq₂₃.p₂)
      (H.map f₂) (H.map f₃))
    (h₁₃ : IsPullback (H.map sq₁₃.p₁) (H.map sq₁₃.p₂)
      (H.map f₁) (H.map f₃))
    (hwide : IsPullback (H.map sq₃.p₁₂) (H.map sq₃.p₂₃)
      (H.map sq₁₂.p₂) (H.map sq₂₃.p₁)) :
    ChosenPullback₃ (sq₁₂.map H h₁₂) (sq₂₃.map H h₂₃)
      (sq₁₃.map H h₁₃) where
  chosenPullback := {
    pullback := H.obj sq₃.pullback
    p₁ := H.map sq₃.p₁₂
    p₂ := H.map sq₃.p₂₃
    condition := hwide.w
    isLimit := hwide.isLimit }
  l := {
    f := H.map sq₃.p₁₃
    f_p₁ := by
      change H.map sq₃.p₁₃ ≫ H.map sq₁₃.p₁ =
        H.map sq₃.p₁₂ ≫ H.map sq₁₂.p₁
      rw [← H.map_comp, ← H.map_comp, sq₃.p₁₃_p₁, sq₃.p₁₂_p₁]
    f_p₂ := by
      change H.map sq₃.p₁₃ ≫ H.map sq₁₃.p₂ =
        H.map sq₃.p₂₃ ≫ H.map sq₂₃.p₂
      rw [← H.map_comp, ← H.map_comp, sq₃.p₁₃_p₃, sq₃.p₂₃_p₃]
    f_p := by
      change H.map sq₃.p₁₃ ≫ (H.map sq₁₃.p₁ ≫ H.map f₁) =
        H.map sq₃.p₁₂ ≫ (H.map sq₁₂.p₁ ≫ H.map f₁)
      simp only [← Category.assoc, ← H.map_comp]
      rw [sq₃.p₁₃_p₁, sq₃.p₁₂_p₁] }

namespace Pseudofunctor

variable (H : C ⥤ D)
variable (G : Pseudofunctor (LocallyDiscrete Dᵒᵖ) Cat.{vE, uE})

/-- The flexible composition isomorphism of a pseudofunctor precomposed by an
ordinary functor is the flexible composition isomorphism after applying that
functor. -/
lemma comp_mapComp'_eq {X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ X) (h : Z ⟶ Y)
    (w : g ≫ f = h) :
    (Pseudofunctor.comp H.op.toPseudofunctor G).mapComp'
      f.op.toLoc g.op.toLoc h.op.toLoc (by simpa using congrArg (fun q => q.op.toLoc) w) =
      G.mapComp' (H.map f).op.toLoc (H.map g).op.toLoc (H.map h).op.toLoc
        (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, ← H.map_comp, w]) := by
  subst h
  let e₁ := (Pseudofunctor.comp H.op.toPseudofunctor G).mapComp'
    f.op.toLoc g.op.toLoc (g ≫ f).op.toLoc (by simp)
  let e₂ := G.mapComp' (H.map f).op.toLoc (H.map g).op.toLoc
    (H.map (g ≫ f)).op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, ← H.map_comp])
  change e₁ = e₂
  have hH : H.op.toPseudofunctor.mapComp f.op.toLoc g.op.toLoc =
      eqToIso (by
        change (H.map (g ≫ f)).op.toLoc =
          (H.map f).op.toLoc ≫ (H.map g).op.toLoc
        rw [← Quiver.Hom.comp_toLoc, ← op_comp, ← H.map_comp]) := by
    ext
    rfl
  ext q
  change G.obj (.mk (op (H.obj Y))) at q
  simp only [e₁, e₂, Pseudofunctor.mapComp', Pseudofunctor.comp_mapComp,
    hH, PrelaxFunctor.map₂Iso_eqToIso]
  simp only [Iso.trans_hom, Cat.Hom₂.comp_app]
  simp only [eqToIso.hom, Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app]
  simp
  change eqToHom _ ≫ (G.mapComp (H.map f).op.toLoc
    (H.map g).op.toLoc).hom.toNatTrans.app q = _
  rfl

/-- Pulling a morphism after precomposition agrees with pulling it after applying
the ordinary functor. -/
lemma comp_pullHom_eq {X₁ X₂ P Y : C} (a₁ : P ⟶ X₁) (a₂ : P ⟶ X₂)
    (p : Y ⟶ P) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)
    (hp₁ : p ≫ a₁ = f₁) (hp₂ : p ≫ a₂ = f₂)
    (M₁ : G.obj (.mk (op (H.obj X₁)))) (M₂ : G.obj (.mk (op (H.obj X₂))))
    (φ : (G.map (H.map a₁).op.toLoc).toFunctor.obj M₁ ⟶
      (G.map (H.map a₂).op.toLoc).toFunctor.obj M₂) :
    LocallyDiscreteOpToCat.pullHom
      (F := Pseudofunctor.comp H.op.toPseudofunctor G)
      φ p f₁ f₂ hp₁ hp₂ =
      LocallyDiscreteOpToCat.pullHom (F := G) φ (H.map p) (H.map f₁) (H.map f₂)
        (by rw [← H.map_comp, hp₁]) (by rw [← H.map_comp, hp₂]) := by
  dsimp only [LocallyDiscreteOpToCat.pullHom]
  rw [comp_mapComp'_eq H G a₁ p f₁ hp₁,
    comp_mapComp'_eq H G a₂ p f₂ hp₂]
  rfl

/-- `pullHom` is heterogeneous-equal after replacing its two target arrows by
equal arrows. -/
lemma pullHom_heq_of_eq {E : Type uC} [Category.{vC} E]
    (F : Pseudofunctor (LocallyDiscrete Eᵒᵖ) Cat.{vE, uE})
    {X₁ X₂ P Y : E} (a₁ : P ⟶ X₁) (a₂ : P ⟶ X₂)
    (M₁ : F.obj (.mk (op X₁))) (M₂ : F.obj (.mk (op X₂)))
    (φ : (F.map a₁.op.toLoc).toFunctor.obj M₁ ⟶
      (F.map a₂.op.toLoc).toFunctor.obj M₂)
    (p : Y ⟶ P) {f₁ f₁' : Y ⟶ X₁} {f₂ f₂' : Y ⟶ X₂}
    (ef₁ : f₁ = f₁') (ef₂ : f₂ = f₂')
    (hp₁ : p ≫ a₁ = f₁) (hp₂ : p ≫ a₂ = f₂)
    (hp₁' : p ≫ a₁ = f₁') (hp₂' : p ≫ a₂ = f₂') :
    HEq (LocallyDiscreteOpToCat.pullHom (F := F) φ p f₁ f₂ hp₁ hp₂)
      (LocallyDiscreteOpToCat.pullHom (F := F) φ p f₁' f₂' hp₁' hp₂') := by
  subst f₁'
  subst f₂'
  rfl

variable {I : Type t} {S : C} {X : I → C} {f : ∀ i, X i ⟶ S}
variable (sq : ∀ i j, ChosenPullback (f i) (f j))
variable (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))
variable (hsq : ∀ i j, IsPullback (H.map (sq i j).p₁) (H.map (sq i j).p₂)
  (H.map (f i)) (H.map (f j)))
variable (hwide : ∀ i j k, IsPullback (H.map (sq₃ i j k).p₁₂)
  (H.map (sq₃ i j k).p₂₃) (H.map (sq i j).p₂) (H.map (sq j k).p₁))

/-- The chosen pullback family obtained by mapping a chosen family through a functor
that preserves each displayed pullback square. -/
noncomputable abbrev mappedChosenPullback (i j : I) :
    ChosenPullback (H.map (f i)) (H.map (f j)) :=
  (sq i j).map H (hsq i j)

/-- The chosen triple-pullback family obtained by mapping a chosen family through a
functor that preserves the pairwise and wide pullback squares. -/
noncomputable abbrev mappedChosenPullback₃ (i j k : I) :
    ChosenPullback₃ (mappedChosenPullback H sq hsq i j)
      (mappedChosenPullback H sq hsq j k) (mappedChosenPullback H sq hsq i k) :=
  (sq₃ i j k).map H (hsq i j) (hsq j k) (hsq i k) (hwide i j k)

/-- Map chosen-pullback descent data for a precomposed pseudofunctor to descent data
for the original pseudofunctor over the mapped pullback diagrams. -/
noncomputable def DescentData'.mapPrecomp
    (A : (Pseudofunctor.comp H.op.toPseudofunctor G).DescentData' sq sq₃) :
    G.DescentData' (mappedChosenPullback H sq hsq)
      (mappedChosenPullback₃ H sq sq₃ hsq hwide) := by
  let homD : ∀ i j, (G.map (H.map (sq i j).p₁).op.toLoc).toFunctor.obj (A.obj i) ⟶
      (G.map (H.map (sq i j).p₂).op.toLoc).toFunctor.obj (A.obj j) :=
    fun i j ↦ A.hom i j
  refine ⟨A.obj, homD, ?_, ?_⟩
  · intro i
    let p := (sq i i).isPullback.lift (𝟙 (X i)) (𝟙 (X i)) (by simp)
    have hp₁ : p ≫ (sq i i).p₁ = 𝟙 (X i) := by
      dsimp [p]
      simp
    have hp₂ : p ≫ (sq i i).p₂ = 𝟙 (X i) := by
      dsimp [p]
      simp
    have hp₁' : H.map p ≫ H.map (sq i i).p₁ = 𝟙 (H.obj (X i)) := by
      rw [← H.map_comp, hp₁, H.map_id]
    have hp₂' : H.map p ≫ H.map (sq i i).p₂ = 𝟙 (H.obj (X i)) := by
      rw [← H.map_comp, hp₂, H.map_id]
    have hT := DescentData'.pullHom'_eq_pullHom
      (F := G) (f := fun a ↦ H.map (f a))
      (sq := mappedChosenPullback H sq hsq) (hom := homD)
      (q := H.map (f i)) (i₁ := i) (i₂ := i)
      (f₁ := 𝟙 (H.obj (X i))) (f₂ := 𝟙 (H.obj (X i))) (p := H.map p)
      (hf₁ := by simp) (hf₂ := by simp) (hp₁ := hp₁') (hp₂ := hp₂')
    have hSource := A.pullHom'_hom_self i
    have hS := DescentData'.pullHom'_eq_pullHom
      (F := Pseudofunctor.comp H.op.toPseudofunctor G) (f := f) (sq := sq)
      (hom := A.hom) (q := f i) (i₁ := i) (i₂ := i)
      (f₁ := 𝟙 (X i)) (f₂ := 𝟙 (X i)) (p := p)
      (hf₁ := by simp) (hf₂ := by simp) (hp₁ := hp₁) (hp₂ := hp₂)
    have h₀ := pullHom_heq_of_eq G (H.map (sq i i).p₁) (H.map (sq i i).p₂)
      (A.obj i) (A.obj i) (homD i i) (H.map p)
      (H.map_id (X i)) (H.map_id (X i))
      (by rw [← H.map_comp, hp₁]) (by rw [← H.map_comp, hp₂]) hp₁' hp₂'
    have hc := comp_pullHom_eq H G (sq i i).p₁ (sq i i).p₂ p
      (𝟙 (X i)) (𝟙 (X i)) hp₁ hp₂ (A.obj i) (A.obj i) (A.hom i i)
    have E :
        ((Pseudofunctor.comp H.op.toPseudofunctor G).map
          (𝟙 (X i)).op.toLoc).toFunctor.obj (A.obj i) =
        (G.map (𝟙 (H.obj (X i))).op.toLoc).toFunctor.obj (A.obj i) := by
      change (G.map (H.map (𝟙 (X i))).op.toLoc).toFunctor.obj (A.obj i) = _
      rw [H.map_id]
    have hId : HEq
        (𝟙 (((Pseudofunctor.comp H.op.toPseudofunctor G).map
          (𝟙 (X i)).op.toLoc).toFunctor.obj (A.obj i)))
        (𝟙 ((G.map (𝟙 (H.obj (X i))).op.toLoc).toFunctor.obj (A.obj i))) := by
      exact (eqToHom_heq_id_dom _ _ E).symm.trans (eqToHom_heq_id_cod _ _ E)
    exact eq_of_heq ((heq_of_eq hT).trans (h₀.symm.trans
      ((heq_of_eq hc).symm.trans ((heq_of_eq hS).symm.trans
        ((heq_of_eq hSource).trans hId)))))
  · intro i j k
    have hp₁ : (mappedChosenPullback₃ H sq sq₃ hsq hwide i j k).p₁ =
        H.map (sq₃ i j k).p₁ := by
      change H.map (sq₃ i j k).p₁₂ ≫ H.map (sq i j).p₁ = _
      rw [← H.map_comp, (sq₃ i j k).p₁₂_p₁]
    have hp₂ : (mappedChosenPullback₃ H sq sq₃ hsq hwide i j k).p₂ =
        H.map (sq₃ i j k).p₂ := by
      change H.map (sq₃ i j k).p₁₂ ≫ H.map (sq i j).p₂ = _
      rw [← H.map_comp, (sq₃ i j k).p₁₂_p₂]
    have hp₃ : (mappedChosenPullback₃ H sq sq₃ hsq hwide i j k).p₃ =
        H.map (sq₃ i j k).p₃ := by
      change H.map (sq₃ i j k).p₂₃ ≫ H.map (sq j k).p₂ = _
      rw [← H.map_comp, (sq₃ i j k).p₂₃_p₃]
    have hp₁₂ : (mappedChosenPullback₃ H sq sq₃ hsq hwide i j k).p₁₂ =
        H.map (sq₃ i j k).p₁₂ := rfl
    have hp₂₃ : (mappedChosenPullback₃ H sq sq₃ hsq hwide i j k).p₂₃ =
        H.map (sq₃ i j k).p₂₃ := rfl
    have hp₁₃ : (mappedChosenPullback₃ H sq sq₃ hsq hwide i j k).p₁₃ =
        H.map (sq₃ i j k).p₁₃ := rfl
    rw [DescentData'.pullHom'₁₂_eq_pullHom_of_chosenPullback₃,
      DescentData'.pullHom'₂₃_eq_pullHom_of_chosenPullback₃,
      DescentData'.pullHom'₁₃_eq_pullHom_of_chosenPullback₃]
    have h := A.pullHom'_hom_comp i j k
    rw [DescentData'.pullHom'₁₂_eq_pullHom_of_chosenPullback₃,
      DescentData'.pullHom'₂₃_eq_pullHom_of_chosenPullback₃,
      DescentData'.pullHom'₁₃_eq_pullHom_of_chosenPullback₃] at h
    let T₁₂ := LocallyDiscreteOpToCat.pullHom (F := G) (homD i j)
      (H.map (sq₃ i j k).p₁₂) (mappedChosenPullback₃ H sq sq₃ hsq hwide i j k).p₁
      (mappedChosenPullback₃ H sq sq₃ hsq hwide i j k).p₂
      (by rw [hp₁, ← H.map_comp, (sq₃ i j k).p₁₂_p₁])
      (by rw [hp₂, ← H.map_comp, (sq₃ i j k).p₁₂_p₂])
    let T₂₃ := LocallyDiscreteOpToCat.pullHom (F := G) (homD j k)
      (H.map (sq₃ i j k).p₂₃) (mappedChosenPullback₃ H sq sq₃ hsq hwide i j k).p₂
      (mappedChosenPullback₃ H sq sq₃ hsq hwide i j k).p₃
      (by rw [hp₂, ← H.map_comp, (sq₃ i j k).p₂₃_p₂])
      (by rw [hp₃, ← H.map_comp, (sq₃ i j k).p₂₃_p₃])
    let T₁₃ := LocallyDiscreteOpToCat.pullHom (F := G) (homD i k)
      (H.map (sq₃ i j k).p₁₃) (mappedChosenPullback₃ H sq sq₃ hsq hwide i j k).p₁
      (mappedChosenPullback₃ H sq sq₃ hsq hwide i j k).p₃
      (by rw [hp₁, ← H.map_comp, (sq₃ i j k).p₁₃_p₁])
      (by rw [hp₃, ← H.map_comp, (sq₃ i j k).p₁₃_p₃])
    let S₁₂ := LocallyDiscreteOpToCat.pullHom
      (F := Pseudofunctor.comp H.op.toPseudofunctor G) (A.hom i j)
      (sq₃ i j k).p₁₂ (sq₃ i j k).p₁ (sq₃ i j k).p₂
    let S₂₃ := LocallyDiscreteOpToCat.pullHom
      (F := Pseudofunctor.comp H.op.toPseudofunctor G) (A.hom j k)
      (sq₃ i j k).p₂₃ (sq₃ i j k).p₂ (sq₃ i j k).p₃
    let S₁₃ := LocallyDiscreteOpToCat.pullHom
      (F := Pseudofunctor.comp H.op.toPseudofunctor G) (A.hom i k)
      (sq₃ i j k).p₁₃ (sq₃ i j k).p₁ (sq₃ i j k).p₃
    change T₁₂ ≫ T₂₃ = T₁₃
    change S₁₂ ≫ S₂₃ = S₁₃ at h
    have H₁₂ : T₁₂ ≍ S₁₂ := by
      have h₀ := pullHom_heq_of_eq G (H.map (sq i j).p₁) (H.map (sq i j).p₂)
        (A.obj i) (A.obj j) (homD i j) (H.map (sq₃ i j k).p₁₂)
        hp₁.symm hp₂.symm
        (by rw [← H.map_comp, (sq₃ i j k).p₁₂_p₁])
        (by rw [← H.map_comp, (sq₃ i j k).p₁₂_p₂])
        (by rw [hp₁, ← H.map_comp, (sq₃ i j k).p₁₂_p₁])
        (by rw [hp₂, ← H.map_comp, (sq₃ i j k).p₁₂_p₂])
      exact h₀.symm.trans ((comp_pullHom_eq H G (sq i j).p₁ (sq i j).p₂
        (sq₃ i j k).p₁₂ (sq₃ i j k).p₁ (sq₃ i j k).p₂
        (sq₃ i j k).p₁₂_p₁ (sq₃ i j k).p₁₂_p₂
        (A.obj i) (A.obj j) (A.hom i j)).symm |> heq_of_eq)
    have H₂₃ : T₂₃ ≍ S₂₃ := by
      have h₀ := pullHom_heq_of_eq G (H.map (sq j k).p₁) (H.map (sq j k).p₂)
        (A.obj j) (A.obj k) (homD j k) (H.map (sq₃ i j k).p₂₃)
        hp₂.symm hp₃.symm
        (by rw [← H.map_comp, (sq₃ i j k).p₂₃_p₂])
        (by rw [← H.map_comp, (sq₃ i j k).p₂₃_p₃])
        (by rw [hp₂, ← H.map_comp, (sq₃ i j k).p₂₃_p₂])
        (by rw [hp₃, ← H.map_comp, (sq₃ i j k).p₂₃_p₃])
      exact h₀.symm.trans ((comp_pullHom_eq H G (sq j k).p₁ (sq j k).p₂
        (sq₃ i j k).p₂₃ (sq₃ i j k).p₂ (sq₃ i j k).p₃
        (sq₃ i j k).p₂₃_p₂ (sq₃ i j k).p₂₃_p₃
        (A.obj j) (A.obj k) (A.hom j k)).symm |> heq_of_eq)
    have H₁₃ : T₁₃ ≍ S₁₃ := by
      have h₀ := pullHom_heq_of_eq G (H.map (sq i k).p₁) (H.map (sq i k).p₂)
        (A.obj i) (A.obj k) (homD i k) (H.map (sq₃ i j k).p₁₃)
        hp₁.symm hp₃.symm
        (by rw [← H.map_comp, (sq₃ i j k).p₁₃_p₁])
        (by rw [← H.map_comp, (sq₃ i j k).p₁₃_p₃])
        (by rw [hp₁, ← H.map_comp, (sq₃ i j k).p₁₃_p₁])
        (by rw [hp₃, ← H.map_comp, (sq₃ i j k).p₁₃_p₃])
      exact h₀.symm.trans ((comp_pullHom_eq H G (sq i k).p₁ (sq i k).p₂
        (sq₃ i j k).p₁₃ (sq₃ i j k).p₁ (sq₃ i j k).p₃
        (sq₃ i j k).p₁₃_p₁ (sq₃ i j k).p₁₃_p₃
        (A.obj i) (A.obj k) (A.hom i k)).symm |> heq_of_eq)
    have E₁ : (G.map (mappedChosenPullback₃ H sq sq₃ hsq hwide i j k).p₁.op.toLoc).toFunctor.obj
        (A.obj i) =
        ((Pseudofunctor.comp H.op.toPseudofunctor G).map
          (sq₃ i j k).p₁.op.toLoc).toFunctor.obj (A.obj i) := by
      rw [hp₁]
      rfl
    have E₂ : (G.map (mappedChosenPullback₃ H sq sq₃ hsq hwide i j k).p₂.op.toLoc).toFunctor.obj
        (A.obj j) =
        ((Pseudofunctor.comp H.op.toPseudofunctor G).map
          (sq₃ i j k).p₂.op.toLoc).toFunctor.obj (A.obj j) := by
      rw [hp₂]
      rfl
    have E₃ : (G.map (mappedChosenPullback₃ H sq sq₃ hsq hwide i j k).p₃.op.toLoc).toFunctor.obj
        (A.obj k) =
        ((Pseudofunctor.comp H.op.toPseudofunctor G).map
          (sq₃ i j k).p₃.op.toLoc).toFunctor.obj (A.obj k) := by
      rw [hp₃]
      rfl
    exact eq_of_heq ((heq_comp E₁ E₂ E₃ H₁₂ H₂₃).trans
      ((heq_of_eq h).trans H₁₃.symm))

/-- Functorially map chosen-pullback descent data for a precomposed pseudofunctor
to descent data for the original pseudofunctor over the mapped diagrams. -/
noncomputable def descentDataMapPrecompFunctor :
    (Pseudofunctor.comp H.op.toPseudofunctor G).DescentData' sq sq₃ ⥤
      G.DescentData' (mappedChosenPullback H sq hsq)
        (mappedChosenPullback₃ H sq sq₃ hsq hwide) where
  obj A := A.mapPrecomp H G sq sq₃ hsq hwide
  map φ :=
    { hom := φ.hom
      comm := φ.comm }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Mapping chosen-pullback descent data through precomposition is fully faithful:
the component morphisms and their compatibility equations are unchanged. -/
noncomputable def descentDataMapPrecompFullyFaithful :
    (descentDataMapPrecompFunctor H G sq sq₃ hsq hwide).FullyFaithful where
  preimage φ :=
    { hom := φ.hom
      comm := φ.comm }
  map_preimage _ := rfl
  preimage_map _ := rfl

end Pseudofunctor

end CategoryTheory
