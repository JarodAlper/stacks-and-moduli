module

public import StacksAndModuli.API.AlgebraicSpaceAtlasComposition
public import StacksAndModuli.API.OverBasedYonedaEquivalence
public import StacksAndModuli.API.PresheafOverComparison
public import StacksAndModuli.API.RepresentableWithEquivalence

/-!
# Base change of scheme charts of stack fibers

Supporting material for §4.3 of *Stacks and Moduli*, corresponding to no labelled result
of the book and to no Stacks Project tag.

A chart `Sch/U → 𝒳 ×_𝒴 Sch/T` may be pulled back along a scheme morphism `S → T`.
Although the chart is only assumed representable by algebraic spaces, the particular
base change along the structural map to `T` has scheme source: it is represented by
`U ×_T S`.  The declarations below package this observation together with the comparison
to the canonical fiber `𝒳 ×_𝒴 Sch/S`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Limits
open CategoryTheory.BasedCategory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ u

namespace AlgebraicGeometry.BasedFunctor

variable {Xcat : BasedCategory.{v₂, u₂} Scheme.{u}}
  {Ycat : BasedCategory.{v₃, u₃} Scheme.{u}}
  {Ycat' : BasedCategory.{v₄, u₄} Scheme.{u}}

/-- Postcomposing by an equivalence of target prestacks preserves representability with
a morphism property. -/
theorem RepresentableWith.comp_target_isEquivalence
    {P : MorphismProperty Scheme.{u}} {F : Xcat ⥤ᵇ Ycat}
    (hF : RepresentableWith P F) (E : Ycat ⥤ᵇ Ycat')
    [Xcat.p.IsFiberedInGroupoids] [Ycat.p.IsFiberedInGroupoids]
    [Ycat'.p.IsFiberedInGroupoids] [E.toFunctor.IsEquivalence] :
    RepresentableWith P (F.comp E) := by
  classical
  refine ⟨?_, ?_⟩
  · intro S g
    obtain ⟨L, ⟨α⟩, ⟨β⟩⟩ :=
      CategoryTheory.BasedFunctor.exists_inverse_of_toFunctor E
    let η : (g.comp L).comp E ≅ g :=
      (eqToIso (CategoryTheory.BasedFunctor.comp_assoc g L E)).trans
        ((isoWhiskerLeft g β).trans
          (eqToIso (CategoryTheory.BasedFunctor.comp_id g)))
    let K₀ := fiberProductPostcomp F (g.comp L) E
    let K₁ := fiberProductMapRightIso (F.comp E) η
    let K := K₀.comp K₁
    let _ : K₀.toFunctor.IsEquivalence :=
      isEquivalence_fiberProductPostcomp F (g.comp L) E
    let _ : K₁.toFunctor.IsEquivalence :=
      isEquivalence_fiberProductMapRightIso (F.comp E) η
    have hK : K.toFunctor.IsEquivalence := by
      change (K₀.toFunctor ⋙ K₁.toFunctor).IsEquivalence
      exact Functor.isEquivalence_trans K₀.toFunctor K₁.toFunctor
    obtain ⟨A, hA, R, hR⟩ := hF.1 S (g.comp L)
    exact ⟨A, hA, R.comp K,
      Functor.isEquivalence_trans R.toFunctor K.toFunctor⟩
  · intro S g A hA R hR U q hq
    obtain ⟨L, ⟨α⟩, ⟨β⟩⟩ :=
      CategoryTheory.BasedFunctor.exists_inverse_of_toFunctor E
    let η : (g.comp L).comp E ≅ g :=
      (eqToIso (CategoryTheory.BasedFunctor.comp_assoc g L E)).trans
        ((isoWhiskerLeft g β).trans
          (eqToIso (CategoryTheory.BasedFunctor.comp_id g)))
    let K₀ := fiberProductPostcomp F (g.comp L) E
    let K₁ := fiberProductMapRightIso (F.comp E) η
    let K := K₀.comp K₁
    let _ : K₀.toFunctor.IsEquivalence :=
      isEquivalence_fiberProductPostcomp F (g.comp L) E
    let _ : K₁.toFunctor.IsEquivalence :=
      isEquivalence_fiberProductMapRightIso (F.comp E) η
    have hK : K.toFunctor.IsEquivalence := by
      change (K₀.toFunctor ⋙ K₁.toFunctor).IsEquivalence
      exact Functor.isEquivalence_trans K₀.toFunctor K₁.toFunctor
    let _ : K.toFunctor.IsEquivalence := hK
    obtain ⟨J, ⟨γ⟩, ⟨δ⟩⟩ :=
      CategoryTheory.BasedFunctor.exists_inverse_of_toFunctor K
    have hJ : J.toFunctor.IsEquivalence :=
      Functor.IsEquivalence.mk' K.toFunctor
        ((BasedNatTrans.forgetful _ _).mapIso δ).symm
        ((BasedNatTrans.forgetful _ _).mapIso γ)
    have hP := hF.2 S (g.comp L) A hA (R.comp J)
      (Functor.isEquivalence_trans R.toFunctor J.toFunctor) U q hq
    have hK_snd : K.comp
        (CategoryTheory.BasedCategory.fiberProductSnd (F.comp E) g) =
        CategoryTheory.BasedCategory.fiberProductSnd F (g.comp L) := by
      rfl
    let eproj : J.comp
        (CategoryTheory.BasedCategory.fiberProductSnd F (g.comp L)) ≅
        CategoryTheory.BasedCategory.fiberProductSnd (F.comp E) g := by
      rw [← hK_snd, ← CategoryTheory.BasedFunctor.comp_assoc]
      exact (isoWhiskerRight δ
        (CategoryTheory.BasedCategory.fiberProductSnd (F.comp E) g)).trans
        (eqToIso (CategoryTheory.BasedFunctor.id_comp _))
    let eprojR := isoWhiskerLeft R eproj
    let chart := (overBasedToOfPresheafYoneda U).comp (ofPresheaf.map q)
    let echart := isoWhiskerLeft chart eprojR
    change P (chart.comp (R.comp (J.comp
      (CategoryTheory.BasedCategory.fiberProductSnd F (g.comp L))))).overHom at hP
    change P (chart.comp (R.comp
      (CategoryTheory.BasedCategory.fiberProductSnd (F.comp E) g))).overHom
    exact (CategoryTheory.BasedFunctor.overHom_eq_of_iso echart) ▸ hP

variable {S T : Scheme.{u}}

/-- The underlying scheme map of the gluing isomorphism in a fiber product of two
representable-prestack maps is the canonical equality transport. -/
lemma FiberProductObj.overBasedMaps_iso_hom_left {U : Scheme.{u}}
    {f : U ⟶ T} {p : S ⟶ T}
    (a : FiberProductObj (overBased.map f) (overBased.map p)) :
    a.iso.hom.left = eqToHom a.over_eq.symm := by
  let _ := a.isHomLift
  have h := IsHomLift.fac' (overBased T).p
    (𝟙 ((overBased U).p.obj a.fst)) a.iso.hom
  simpa using h

/-- The canonical gluing isomorphism attached to a morphism into an ordinary
scheme pullback. -/
noncomputable def overBasedPullbackLiftIso {U : Scheme.{u}}
    (f : U ⟶ T) (p : S ⟶ T) (w : Over (pullback f p)) :
    (overBased.map f).obj
        (Over.mk (w.hom ≫ pullback.fst f p)) ≅
      (overBased.map p).obj
        (Over.mk (w.hom ≫ pullback.snd f p)) :=
  Over.isoMk (Iso.refl _) (by
    dsimp [overBased.map]
    simpa only [Category.id_comp, Category.assoc] using
      congrArg (fun k ↦ w.hom ≫ k)
        (pullback.condition (f := f) (g := p)).symm)

/-- The canonical equivalence from the representable prestack of an ordinary scheme
pullback to the corresponding 2-fiber product of representable prestacks. -/
noncomputable def overBasedPullbackLift {U : Scheme.{u}}
    (f : U ⟶ T) (p : S ⟶ T) :
    overBased (pullback f p) ⥤ᵇ
      fiberProduct (overBased.map f) (overBased.map p) where
  obj w :=
    { fst := Over.mk (w.hom ≫ pullback.fst f p)
      snd := Over.mk (w.hom ≫ pullback.snd f p)
      over_eq := rfl
      iso := overBasedPullbackLiftIso f p w
      isHomLift := IsHomLift.of_fac' _ _ _ rfl rfl
        (by simp [overBasedPullbackLiftIso]) }
  map {w w'} t :=
    { fst := Over.homMk t.left (by
        change t.left ≫ (w'.hom ≫ pullback.fst f p) =
          w.hom ≫ pullback.fst f p
        rw [← Category.assoc, Over.w t])
      snd := Over.homMk t.left (by
        change t.left ≫ (w'.hom ≫ pullback.snd f p) =
          w.hom ≫ pullback.snd f p
        rw [← Category.assoc, Over.w t])
      isHomLift := IsHomLift.of_fac' _ _ _ rfl rfl (by simp)
      w := by
        apply Over.OverMorphism.ext
        simp [overBasedPullbackLiftIso, overBased.map] }
  map_id w := by
    apply FiberProductHom.ext <;> apply Over.OverMorphism.ext <;> simp
  map_comp t t' := by
    apply FiberProductHom.ext <;> apply Over.OverMorphism.ext <;> simp
  w := rfl

/-- The morphism into the ordinary scheme pullback classified by an object of the
2-fiber product of representable prestacks. -/
noncomputable def overBasedPullbackLeftMap {U : Scheme.{u}}
    (f : U ⟶ T) (p : S ⟶ T)
    (a : FiberProductObj (overBased.map f) (overBased.map p)) :
    a.fst.left ⟶ pullback f p :=
  pullback.lift a.fst.hom
    (eqToHom a.over_eq.symm ≫ a.snd.hom) (by
      have hw := Over.w a.iso.hom
      rw [FiberProductObj.overBasedMaps_iso_hom_left a] at hw
      simpa only [overBased.map, Over.map_obj_left, Over.map_obj_hom,
        Category.assoc] using hw.symm)

@[reassoc]
lemma overBasedPullbackLeftMap_fst {U : Scheme.{u}}
    (f : U ⟶ T) (p : S ⟶ T)
    (a : FiberProductObj (overBased.map f) (overBased.map p)) :
    overBasedPullbackLeftMap f p a ≫ pullback.fst f p = a.fst.hom :=
  pullback.lift_fst _ _ _

@[reassoc]
lemma overBasedPullbackLeftMap_snd {U : Scheme.{u}}
    (f : U ⟶ T) (p : S ⟶ T)
    (a : FiberProductObj (overBased.map f) (overBased.map p)) :
    overBasedPullbackLeftMap f p a ≫ pullback.snd f p =
      eqToHom a.over_eq.symm ≫ a.snd.hom :=
  pullback.lift_snd _ _ _

/-- The canonical pullback comparison is faithful. -/
theorem overBasedPullbackLift_faithful {U : Scheme.{u}}
    (f : U ⟶ T) (p : S ⟶ T) :
    (overBasedPullbackLift f p).toFunctor.Faithful where
  map_injective {_ _} q r h := by
    apply Over.OverMorphism.ext
    exact congrArg (fun k ↦ k.fst.left) h

/-- The canonical pullback comparison is full. -/
theorem overBasedPullbackLift_full {U : Scheme.{u}}
    (f : U ⟶ T) (p : S ⟶ T) :
    (overBasedPullbackLift f p).toFunctor.Full where
  map_surjective {a b} q := by
    let _ := q.isHomLift
    have hsnd : q.snd.left = q.fst.left := by
      have h := IsHomLift.fac' (overBased S).p
        ((overBased U).p.map q.fst) q.snd
      simpa using h
    have hfst := Over.w q.fst
    have hsndw := Over.w q.snd
    change q.fst.left ≫ (b.hom ≫ pullback.fst f p) =
      a.hom ≫ pullback.fst f p at hfst
    change q.snd.left ≫ (b.hom ≫ pullback.snd f p) =
      a.hom ≫ pullback.snd f p at hsndw
    let r : a ⟶ b := Over.homMk q.fst.left (by
      apply pullback.hom_ext
      · simpa only [Category.assoc] using hfst
      · rw [← hsnd]
        simpa only [Category.assoc] using hsndw)
    refine ⟨r, ?_⟩
    apply FiberProductHom.ext
    · apply Over.OverMorphism.ext
      rfl
    · apply Over.OverMorphism.ext
      exact hsnd.symm

/-- The canonical pullback comparison is essentially surjective. -/
theorem overBasedPullbackLift_essSurj {U : Scheme.{u}}
    (f : U ⟶ T) (p : S ⟶ T) :
    (overBasedPullbackLift f p).toFunctor.EssSurj := by
  constructor
  intro a
  let w : Over (pullback f p) := Over.mk (overBasedPullbackLeftMap f p a)
  let e₁ : ((overBasedPullbackLift f p).obj w).fst ≅ a.fst :=
    Over.isoMk (Iso.refl _) (by
      simpa [overBasedPullbackLift, w] using
        (overBasedPullbackLeftMap_fst f p a).symm)
  let e₂ : ((overBasedPullbackLift f p).obj w).snd ≅ a.snd :=
    Over.isoMk (eqToIso a.over_eq.symm) (by
      simpa [overBasedPullbackLift, w] using
        (overBasedPullbackLeftMap_snd f p a).symm)
  refine ⟨w, ⟨?_⟩⟩
  apply FiberProductObj.isoMk e₁ e₂
  · let R : Scheme.{u} := a.fst.left
    have h₁left : IsHomLift (Functor.id Scheme) (𝟙 R) e₁.hom.left := by
      dsimp [e₁]
      exact IsHomLift.id rfl
    have h₁ := over_isHomLift_of_left (𝟙 R) e₁.hom h₁left
    have h₂left : IsHomLift (Functor.id Scheme) (𝟙 R) e₂.hom.left := by
      apply IsHomLift.of_fac' (Functor.id Scheme) (𝟙 R) e₂.hom.left
        rfl a.over_eq
      simp [e₂, R]
    have h₂ := over_isHomLift_of_left (𝟙 R) e₂.hom h₂left
    exact isHomLift_map_of_common_lift (𝟙 R) e₁.hom e₂.hom h₁ h₂
  · apply Over.OverMorphism.ext
    change e₁.hom.left ≫ a.iso.hom.left =
      ((overBasedPullbackLift f p).obj w).iso.hom.left ≫ e₂.hom.left
    rw [show e₁.hom.left = 𝟙 w.left by rfl,
      show e₂.hom.left = eqToHom a.over_eq.symm by rfl,
      show ((overBasedPullbackLift f p).obj w).iso.hom.left = 𝟙 w.left by rfl]
    rw [FiberProductObj.overBasedMaps_iso_hom_left a]

/-- The canonical comparison from the representable prestack of a scheme pullback
to the 2-fiber product is an equivalence. -/
theorem isEquivalence_overBasedPullbackLift {U : Scheme.{u}}
    (f : U ⟶ T) (p : S ⟶ T) :
    (overBasedPullbackLift f p).toFunctor.IsEquivalence :=
  ⟨overBasedPullbackLift_faithful f p,
    overBasedPullbackLift_full f p,
    overBasedPullbackLift_essSurj f p⟩

/-- The second projection of the canonical pullback comparison is the ordinary
scheme-pullback projection. -/
theorem overBasedPullbackLift_comp_snd {U : Scheme.{u}}
    (f : U ⟶ T) (p : S ⟶ T) :
    (overBasedPullbackLift f p).comp
        (CategoryTheory.BasedCategory.fiberProductSnd
          (overBased.map f) (overBased.map p)) =
      overBased.map (pullback.snd f p) := by
  apply CategoryTheory.BasedFunctor.ext_of_toFunctor_eq
  rfl

/-- The canonical isomorphism from a morphism between representable prestacks to the
representable-prestack morphism classified by its underlying scheme map. -/
noncomputable def overBasedMapIso {U : Scheme.{u}}
    (H : overBased U ⥤ᵇ overBased T) :
    H ≅ overBased.map H.overHom :=
  Classical.choice (CategoryTheory.BasedFunctor.nonempty_iso_overBased_map H)

/-- The representable prestack of the ordinary pullback of the scheme map classified
by `H` is equivalent to the corresponding prestack fiber product. -/
noncomputable def overBasedFiberPullbackEquivalence {U : Scheme.{u}}
    (H : overBased U ⥤ᵇ overBased T) (p : S ⟶ T) :
    overBased (pullback H.overHom p) ⥤ᵇ
      fiberProduct H (overBased.map p) :=
  (overBasedPullbackLift H.overHom p).comp
    (fiberProductMapLeftIso (overBasedMapIso H).symm (overBased.map p))

/-- The comparison from the representable prestack of an ordinary pullback to the
corresponding fiber product is an equivalence. -/
theorem isEquivalence_overBasedFiberPullbackEquivalence {U : Scheme.{u}}
    (H : overBased U ⥤ᵇ overBased T) (p : S ⟶ T) :
    (overBasedFiberPullbackEquivalence H p).toFunctor.IsEquivalence := by
  let _ : (overBasedPullbackLift H.overHom p).toFunctor.IsEquivalence :=
    isEquivalence_overBasedPullbackLift H.overHom p
  let _ : (fiberProductMapLeftIso (overBasedMapIso H).symm
      (overBased.map p)).toFunctor.IsEquivalence :=
    isEquivalence_fiberProductMapLeftIso
      (overBasedMapIso H).symm (overBased.map p)
  exact Functor.isEquivalence_trans
    (overBasedPullbackLift H.overHom p).toFunctor
    (fiberProductMapLeftIso (overBasedMapIso H).symm (overBased.map p)).toFunctor

/-- The structural projection of the representable-prestack pullback comparison is
the ordinary scheme-pullback projection. -/
theorem overBasedFiberPullbackEquivalence_comp_snd {U : Scheme.{u}}
    (H : overBased U ⥤ᵇ overBased T) (p : S ⟶ T) :
    (overBasedFiberPullbackEquivalence H p).comp
        (CategoryTheory.BasedCategory.fiberProductSnd H (overBased.map p)) =
      overBased.map (pullback.snd H.overHom p) := by
  rw [show overBasedFiberPullbackEquivalence H p =
      (overBasedPullbackLift H.overHom p).comp
        (fiberProductMapLeftIso (overBasedMapIso H).symm (overBased.map p)) from rfl,
    CategoryTheory.BasedFunctor.comp_assoc]
  have hsnd :
      (fiberProductMapLeftIso (overBasedMapIso H).symm (overBased.map p)).comp
          (CategoryTheory.BasedCategory.fiberProductSnd H (overBased.map p)) =
        CategoryTheory.BasedCategory.fiberProductSnd
          (overBased.map H.overHom) (overBased.map p) := by
    apply CategoryTheory.BasedFunctor.ext_of_toFunctor_eq
    rfl
  rw [hsnd, overBasedPullbackLift_comp_snd]

/-- A scheme presentation of a stack fiber pulls back to a scheme presentation over
an arbitrary scheme morphism.  Its structural map is the ordinary pullback of the
structural map of the original presentation. -/
theorem RepresentableWith.exists_baseChange_presentation
    {P : MorphismProperty Scheme.{u}}
    {F : Xcat ⥤ᵇ Ycat} {U : Scheme.{u}} {g : overBased T ⥤ᵇ Ycat}
    {q : overBased U ⥤ᵇ fiberProduct F g}
    [Xcat.p.IsFiberedInGroupoids] [Ycat.p.IsFiberedInGroupoids]
    (hq : RepresentableWith P q) (p : S ⟶ T) :
    ∃ q' : overBased
        (pullback (q.comp (CategoryTheory.BasedCategory.fiberProductSnd F g)).overHom p) ⥤ᵇ
          fiberProduct F ((overBased.map p).comp g),
      RepresentableWith P q' ∧
        (q'.comp (CategoryTheory.BasedCategory.fiberProductSnd F
          ((overBased.map p).comp g))).overHom =
          pullback.snd
            (q.comp (CategoryTheory.BasedCategory.fiberProductSnd F g)).overHom p := by
  let H := q.comp (CategoryTheory.BasedCategory.fiberProductSnd F g)
  let h := overBased.map p
  let K := pasteFwd q
    (CategoryTheory.BasedCategory.fiberProductSnd F g) h
  let _ : K.toFunctor.IsEquivalence := inferInstance
  obtain ⟨L, ⟨α⟩, ⟨β⟩⟩ :=
    CategoryTheory.BasedFunctor.exists_inverse_of_toFunctor K
  have hL : L.toFunctor.IsEquivalence :=
    Functor.IsEquivalence.mk' K.toFunctor
      ((BasedNatTrans.forgetful _ _).mapIso β).symm
      ((BasedNatTrans.forgetful _ _).mapIso α)
  let _ : L.toFunctor.IsEquivalence := hL
  let L₀ := overBasedFiberPullbackEquivalence H p
  let _ : L₀.toFunctor.IsEquivalence :=
    isEquivalence_overBasedFiberPullbackEquivalence H p
  let π₀ := CategoryTheory.BasedCategory.fiberProductSnd H h
  let π₁ := CategoryTheory.BasedCategory.fiberProductSnd
    (CategoryTheory.BasedCategory.fiberProductSnd F g) h
  let L₂ := CategoryTheory.BasedCategory.fiberProductSnd q
    (CategoryTheory.BasedCategory.fiberProductFst
      (CategoryTheory.BasedCategory.fiberProductSnd F g) h)
  let L₃ := CategoryTheory.BasedCategory.fiberProductAssoc F g h
  let _ : L₃.toFunctor.IsEquivalence := by
    dsimp only [L₃]
    exact CategoryTheory.BasedCategory.isEquivalence_fiberProductAssoc F g h
  let q' := ((L₀.comp L).comp L₂).comp L₃
  have hL₀L : (L₀.comp L).toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans L₀.toFunctor L.toFunctor
  let _ : (L₀.comp L).toFunctor.IsEquivalence := hL₀L
  have hL₂ : RepresentableWith P L₂ :=
    hq.fiberProductSnd
      (CategoryTheory.BasedCategory.fiberProductFst
        (CategoryTheory.BasedCategory.fiberProductSnd F g) h)
  have hq'₀ : RepresentableWith P ((L₀.comp L).comp L₂) :=
    hL₂.comp_source_isEquivalence (L₀.comp L)
  have hq' : RepresentableWith P q' :=
    hq'₀.comp_target_isEquivalence L₃
  refine ⟨q', hq', ?_⟩
  let π := CategoryTheory.BasedCategory.fiberProductSnd F (h.comp g)
  let ηL : L.comp (L₂.comp π₁) ≅ π₀ := by
    simpa only [L₂, π₁, π₀, H, K,
      CategoryTheory.BasedFunctor.comp_assoc,
      CategoryTheory.BasedCategory.pasteFwd_comp_snd,
      CategoryTheory.BasedFunctor.id_comp] using
      CategoryTheory.BasedCategory.isoWhiskerRight β π₀
  let ηq : q'.comp π ≅ L₀.comp π₀ := by
    simpa only [q', π, L₃, CategoryTheory.BasedFunctor.comp_assoc,
      CategoryTheory.BasedCategory.fiberProductAssoc_comp_snd] using
      CategoryTheory.BasedCategory.isoWhiskerLeft L₀ ηL
  have hproj : L₀.comp π₀ =
      overBased.map (pullback.snd H.overHom p) := by
    simpa only [L₀, π₀, h] using
      overBasedFiberPullbackEquivalence_comp_snd H p
  let η : q'.comp π ≅ overBased.map (pullback.snd H.overHom p) :=
    ηq.trans (eqToIso hproj)
  have hover := CategoryTheory.BasedFunctor.overHom_eq_of_iso η
  simpa only [q', π, h, H,
    CategoryTheory.BasedFunctor.overHom_map] using hover

/-- A morphism between representable prestacks is relatively representable with every
base-change-stable property satisfied by the scheme morphism it classifies. -/
theorem relativelyRepresentableWith_of_overHom
    {P : MorphismProperty Scheme.{u}} [P.RespectsIso] [P.IsStableUnderBaseChange]
    (H : overBased S ⥤ᵇ overBased T) (hH : P H.overHom) :
    H.RelativelyRepresentableWith P := by
  let f := H.overHom
  have hpresheaf : P.presheaf (yoneda.map f) := MorphismProperty.relative_map hH
  have h₀ := relativelyRepresentableWith_ofPresheaf_map hpresheaf
  have h₁ := h₀.comp_of_isEquivalence (overBasedToOfPresheafYoneda S)
  have h₂ := h₁.comp_target_isEquivalence (ofPresheafYonedaToOverBased T)
  have hnat :
      (overBasedToOfPresheafYoneda S).comp (ofPresheaf.map (yoneda.map f)) =
        (overBased.map f).comp (overBasedToOfPresheafYoneda T) :=
    overBasedToOfPresheafYoneda_comp_map f
  let e₀ :
      ((overBasedToOfPresheafYoneda S).comp (ofPresheaf.map (yoneda.map f))).comp
          (ofPresheafYonedaToOverBased T) ≅
        overBased.map f :=
    (eqToIso (congrArg (·.comp (ofPresheafYonedaToOverBased T)) hnat)).trans
      ((isoWhiskerLeft (overBased.map f) (overBasedYonedaCounitIso T)).trans
        (eqToIso (CategoryTheory.BasedFunctor.comp_id (overBased.map f))))
  have hmap : (overBased.map f).RelativelyRepresentableWith P := h₂.of_iso e₀
  obtain ⟨e⟩ := CategoryTheory.BasedFunctor.nonempty_iso_overBased_map H
  exact hmap.of_iso e.symm

end AlgebraicGeometry.BasedFunctor
