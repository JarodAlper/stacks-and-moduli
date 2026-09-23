module

public import StacksAndModuli.API.AlgebraicSpaceAtlasComposition
public import StacksAndModuli.API.FiberProductPresentationRepresentable
public import StacksAndModuli.API.OverPresheafTotalPrestack
public import StacksAndModuli.API.PrestackComponents
public import StacksAndModuli.API.PresheafPrestackSmall
public import StacksAndModuli.API.RepresentableSourceFaithful

/-!
# Algebraic-space sources of representable morphisms

This file proves that a representable morphism of prestacks into an algebraic space has
source represented by an algebraic space.  The presheaf-level argument first observes
that a map whose every pullback along a representable presheaf is a sheaf has sheaf source
when its target is a sheaf.  It then composes an algebraic-space atlas of the target with
an atlas of its pullback.  For a universe-polymorphic prestack source, representability
makes the source projection faithful; a small code for its fiberwise connected components
then permits shrinking the component presheaf to the scheme universe and applying the
presheaf-level result.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Limits Opposite ConcreteCategory
open CategoryTheory.BasedCategory

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
  {X Y Z : Cᵒᵖ ⥤ Type v} {f : X ⟶ Z} {g : Y ⟶ Z} {S : C}

/-- Taking the Yoneda element of a pullback lift and then projecting to the first
factor recovers the first input. -/
lemma yonedaEquiv_pullback_lift_fst (a : yoneda.obj S ⟶ X)
    (b : yoneda.obj S ⟶ Y) (h : a ≫ f = b ≫ g) :
    (Limits.pullback.fst f g).app (op S)
        (yonedaEquiv (Limits.pullback.lift a b h)) = yonedaEquiv a :=
  (yonedaEquiv_comp (Limits.pullback.lift a b h)
    (Limits.pullback.fst f g)).symm.trans
      (congrArg yonedaEquiv (Limits.pullback.lift_fst a b h))

/-- Taking the Yoneda element of a pullback lift and then projecting to the second
factor recovers the second input. -/
lemma yonedaEquiv_pullback_lift_snd (a : yoneda.obj S ⟶ X)
    (b : yoneda.obj S ⟶ Y) (h : a ≫ f = b ≫ g) :
    (Limits.pullback.snd f g).app (op S)
        (yonedaEquiv (Limits.pullback.lift a b h)) = yonedaEquiv b :=
  (yonedaEquiv_comp (Limits.pullback.lift a b h)
    (Limits.pullback.snd f g)).symm.trans
      (congrArg yonedaEquiv (Limits.pullback.lift_snd a b h))

/-- The morphism classified by the Yoneda element of a pullback lift has the expected
first projection. -/
lemma yonedaEquiv_symm_pullback_lift_fst (a : yoneda.obj S ⟶ X)
    (b : yoneda.obj S ⟶ Y) (h : a ≫ f = b ≫ g) :
    yonedaEquiv.symm (yonedaEquiv (Limits.pullback.lift a b h)) ≫
        Limits.pullback.fst f g = a :=
  congrArg (fun k ↦ k ≫ Limits.pullback.fst f g)
      (Equiv.symm_apply_apply yonedaEquiv _)
    |>.trans (Limits.pullback.lift_fst a b h)

/-- The morphism classified by the Yoneda element of a pullback lift has the expected
second projection. -/
lemma yonedaEquiv_symm_pullback_lift_snd (a : yoneda.obj S ⟶ X)
    (b : yoneda.obj S ⟶ Y) (h : a ≫ f = b ≫ g) :
    yonedaEquiv.symm (yonedaEquiv (Limits.pullback.lift a b h)) ≫
        Limits.pullback.snd f g = b :=
  congrArg (fun k ↦ k ≫ Limits.pullback.snd f g)
      (Equiv.symm_apply_apply yonedaEquiv _)
    |>.trans (Limits.pullback.lift_snd a b h)

end CategoryTheory

namespace CategoryTheory.Presieve

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- If the target of a map of presheaves is a sheaf and every pullback along a
representable presheaf is a sheaf, then its source is a sheaf. -/
theorem IsSheaf.source_of_isSheaf_pullback
    {X Y : Cᵒᵖ ⥤ Type v} (f : X ⟶ Y) (hY : IsSheaf J Y)
    (hPullback : ∀ (S : C) (y : yoneda.obj S ⟶ Y),
      IsSheaf J (Limits.pullback f y)) :
    IsSheaf J X := by
  intro S R hR x hx
  let xy : R.arrows.FamilyOfElements Y := x.map f
  have hxy : xy.Compatible := hx.map f
  obtain ⟨y, hy, hyUnique⟩ := hY R hR xy hxy
  let g : yoneda.obj S ⟶ Y := yonedaEquiv.symm y
  let P : Cᵒᵖ ⥤ Type v := Limits.pullback f g
  let z : R.arrows.FamilyOfElements P := fun T p hp ↦
    yonedaEquiv (Limits.pullback.lift (yonedaEquiv.symm (x p hp))
      (yoneda.map p) (by
        apply yonedaEquiv.injective
        rw [yonedaEquiv_comp, yonedaEquiv_comp,
          Equiv.apply_symm_apply, yonedaEquiv_yoneda_map]
        exact (hy p hp).symm))
  have hz : z.Compatible := by
    dsimp only [z]
    intro T₁ T₂ W p₁ p₂ q₁ q₂ hp₁ hp₂ hq
    apply yonedaEquiv.symm.injective
    rw [yonedaEquiv_symm_map, yonedaEquiv_symm_map]
    apply Limits.pullback.hom_ext
    · simp only [Category.assoc]
      calc
        yoneda.map p₁ ≫
            (yonedaEquiv.symm
              (yonedaEquiv (Limits.pullback.lift
                (yonedaEquiv.symm (x q₁ hp₁)) (yoneda.map q₁) _)) ≫
              Limits.pullback.fst f g) =
            yoneda.map p₁ ≫ yonedaEquiv.symm (x q₁ hp₁) := by
              apply congrArg (yoneda.map p₁ ≫ ·)
              exact yonedaEquiv_symm_pullback_lift_fst _ _ _
        _ = yonedaEquiv.symm (X.map p₁.op (x q₁ hp₁)) :=
          (yonedaEquiv_symm_map p₁.op (x q₁ hp₁)).symm
        _ = yonedaEquiv.symm (X.map p₂.op (x q₂ hp₂)) :=
          congrArg yonedaEquiv.symm (hx p₁ p₂ hp₁ hp₂ hq)
        _ = yoneda.map p₂ ≫ yonedaEquiv.symm (x q₂ hp₂) :=
          yonedaEquiv_symm_map p₂.op (x q₂ hp₂)
        _ = yoneda.map p₂ ≫
            (yonedaEquiv.symm
              (yonedaEquiv (Limits.pullback.lift
                (yonedaEquiv.symm (x q₂ hp₂)) (yoneda.map q₂) _)) ≫
              Limits.pullback.fst f g) := by
              apply congrArg (yoneda.map p₂ ≫ ·)
              exact (yonedaEquiv_symm_pullback_lift_fst _ _ _).symm
    · simp only [Category.assoc]
      calc
        yoneda.map p₁ ≫
            (yonedaEquiv.symm
              (yonedaEquiv (Limits.pullback.lift
                (yonedaEquiv.symm (x q₁ hp₁)) (yoneda.map q₁) _)) ≫
              Limits.pullback.snd f g) =
            yoneda.map p₁ ≫ yoneda.map q₁ := by
              apply congrArg (yoneda.map p₁ ≫ ·)
              exact yonedaEquiv_symm_pullback_lift_snd _ _ _
        _ = yoneda.map (p₁ ≫ q₁) := (yoneda.map_comp _ _).symm
        _ = yoneda.map (p₂ ≫ q₂) := congrArg yoneda.map hq
        _ = yoneda.map p₂ ≫ yoneda.map q₂ := yoneda.map_comp _ _
        _ = yoneda.map p₂ ≫
            (yonedaEquiv.symm
              (yonedaEquiv (Limits.pullback.lift
                (yonedaEquiv.symm (x q₂ hp₂)) (yoneda.map q₂) _)) ≫
              Limits.pullback.snd f g) := by
              apply congrArg (yoneda.map p₂ ≫ ·)
              exact (yonedaEquiv_symm_pullback_lift_snd _ _ _).symm
  obtain ⟨t, ht, htUnique⟩ := hPullback S g R hR z hz
  let a : X.obj (op S) := (Limits.pullback.fst f g).app (op S) t
  refine ⟨a, ?_, ?_⟩
  · intro T p hp
    change X.map p.op ((Limits.pullback.fst f g).app (op S) t) = x p hp
    rw [← NatTrans.naturality_apply]
    have h := congrArg
      (fun w ↦ (Limits.pullback.fst f g).app (op T) w) (ht p hp)
    have hzfst : (Limits.pullback.fst f g).app (op T) (z p hp) = x p hp := by
      dsimp only [z]
      exact (yonedaEquiv_pullback_lift_fst _ _ _).trans
        (Equiv.apply_symm_apply yonedaEquiv _)
    exact h.trans hzfst
  · intro a' ha'
    have hfa : f.app (op S) a' = y := by
      apply hyUnique
      intro T p hp
      rw [← NatTrans.naturality_apply, ha' p hp]
      rfl
    let t' : P.obj (op S) := yonedaEquiv
      (Limits.pullback.lift (yonedaEquiv.symm a') (yoneda.map (𝟙 S)) (by
        apply yonedaEquiv.injective
        rw [yonedaEquiv_comp, yonedaEquiv_comp,
          Equiv.apply_symm_apply, yonedaEquiv_yoneda_map]
        simpa [g] using hfa))
    have ht' : z.IsAmalgamation t' := by
      intro T p hp
      apply yonedaEquiv.symm.injective
      rw [yonedaEquiv_symm_map]
      apply Limits.pullback.hom_ext
      · simp only [Category.assoc]
        calc
          yoneda.map p ≫ (yonedaEquiv.symm t' ≫
              Limits.pullback.fst f g) =
              yoneda.map p ≫ yonedaEquiv.symm a' := by
                apply congrArg (yoneda.map p ≫ ·)
                dsimp only [t']
                exact yonedaEquiv_symm_pullback_lift_fst _ _ _
          _ = yonedaEquiv.symm (X.map p.op a') :=
            (yonedaEquiv_symm_map p.op a').symm
          _ = yonedaEquiv.symm (x p hp) := congrArg yonedaEquiv.symm (ha' p hp)
          _ = yonedaEquiv.symm (z p hp) ≫ Limits.pullback.fst f g := by
            dsimp only [z]
            exact (yonedaEquiv_symm_pullback_lift_fst _ _ _).symm
      · simp only [Category.assoc]
        calc
          yoneda.map p ≫ (yonedaEquiv.symm t' ≫
              Limits.pullback.snd f g) =
              yoneda.map p ≫ yoneda.map (𝟙 S) := by
                apply congrArg (yoneda.map p ≫ ·)
                dsimp only [t']
                exact yonedaEquiv_symm_pullback_lift_snd _ _ _
          _ = yoneda.map p := by simp
          _ = yonedaEquiv.symm (z p hp) ≫ Limits.pullback.snd f g := by
            dsimp only [z]
            exact (yonedaEquiv_symm_pullback_lift_snd _ _ _).symm
    have htt : t' = t := htUnique t' ht'
    have hfst := congrArg
      (fun w ↦ (Limits.pullback.fst f g).app (op S) w) htt
    have hfst' : (Limits.pullback.fst f g).app (op S) t' = a' := by
      dsimp only [t']
      exact (yonedaEquiv_pullback_lift_fst _ _ _).trans
        (Equiv.apply_symm_apply yonedaEquiv _)
    exact hfst'.symm.trans hfst

end CategoryTheory.Presieve

namespace AlgebraicGeometry

universe v₂ u₂

/-- The canonical morphism from a representable prestack to a presheaf prestack
classifies the presheaf point from which it was constructed. -/
lemma BasedFunctor.ofPresheafHom_overBasedToOfPresheafYoneda_comp_map
    {Y : Scheme.{u}ᵒᵖ ⥤ Type u} {S : Scheme.{u}}
    (g : yoneda.obj S ⟶ Y) :
    BasedFunctor.ofPresheafHom
      ((overBasedToOfPresheafYoneda S).comp (ofPresheaf.map g)) = g := by
  rfl

/-- A scheme-valued base change of a representable map of presheaf prestacks is an
algebraic space. -/
theorem IsAlgebraicSpace.pullback_of_representableMap
    {X Y : Scheme.{u}ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hf : BasedFunctor.Representable (ofPresheaf.map f))
    {S : Scheme.{u}} (g : yoneda.obj S ⟶ Y) :
    IsAlgebraicSpace (Limits.pullback f g) := by
  let G := (overBasedToOfPresheafYoneda S).comp (ofPresheaf.map g)
  obtain ⟨A, hA, E, hE⟩ := hf S G
  let _ : IsAlgebraicSpace A := hA
  let _ : E.toFunctor.IsEquivalence := hE
  let P := ofPresheafPullback (φ := f) G
  let L : ofPresheaf P ⥤ᵇ fiberProduct (ofPresheaf.map f) G :=
    ofPresheafPullbackLift G
  let _ : L.toFunctor.IsEquivalence := by
    dsimp only [L]
    exact isEquivalence_ofPresheafPullbackLift G
  let e : P ≅ A := ofPresheaf.comparisonIso E L
  have hP : IsAlgebraicSpace P := IsAlgebraicSpace.of_iso e.symm
  change IsAlgebraicSpace P
  exact hP

/-- A representable map of presheaf prestacks into an algebraic space has algebraic-space
source. -/
theorem IsAlgebraicSpace.source_of_representableMap
    {X Y : Scheme.{u}ᵒᵖ ⥤ Type u} [IsAlgebraicSpace Y]
    (f : X ⟶ Y) (hf : BasedFunctor.Representable (ofPresheaf.map f)) :
    IsAlgebraicSpace X := by
  refine ⟨?_, ?_⟩
  · exact Presieve.IsSheaf.source_of_isSheaf_pullback f
      IsAlgebraicSpace.isSheaf
      (fun _ g ↦ by
        let _ : IsAlgebraicSpace (Limits.pullback f g) :=
          IsAlgebraicSpace.pullback_of_representableMap f hf g
        exact IsAlgebraicSpace.isSheaf)
  · obtain ⟨U, q, hq⟩ := IsAlgebraicSpace.exists_presentation (X := Y)
    let P := Limits.pullback f q
    let _ : IsAlgebraicSpace P :=
      IsAlgebraicSpace.pullback_of_representableMap f hf q
    obtain ⟨V, r, hr⟩ := IsAlgebraicSpace.exists_presentation (X := P)
    refine ⟨V, r ≫ Limits.pullback.fst f q, ?_⟩
    let Q : MorphismProperty Scheme.{u} := @Surjective ⊓ @Etale
    have hfst : Q.presheaf (Limits.pullback.fst f q) :=
      (MorphismProperty.relative_isStableUnderBaseChange Q).of_isPullback
        (IsPullback.of_hasPullback f q).flip hq
    exact MorphismProperty.comp_mem _ _ _ hr hfst

namespace BasedFunctor.Representable

variable {Xcat : BasedCategory.{v₂, u₂} Scheme.{u}} [Xcat.p.IsFiberedInGroupoids]
  {Y : Scheme.{u}ᵒᵖ ⥤ Type u} {F : Xcat ⥤ᵇ ofPresheaf Y}

/-- The scheme-valued point of the target used to test a representable morphism over a
fixed target section. -/
noncomputable def sourceFiberTest (S : Scheme.{u})
    (y : Y.obj (op S)) : overBased S ⥤ᵇ ofPresheaf Y :=
  twoYonedaPullback S (ofPresheafFiberObj Y S y)

/-- An algebraic space representing the base change of a representable morphism along
one target-fiber object. -/
noncomputable def sourceFiberSpace (hF : BasedFunctor.Representable F)
    (S : Scheme.{u}) (y : Y.obj (op S)) :
    Scheme.{u}ᵒᵖ ⥤ Type u :=
  Classical.choose (hF S (sourceFiberTest S y))

omit [Xcat.p.IsFiberedInGroupoids] in
/-- The chosen source fiber space is an algebraic space. -/
lemma sourceFiberSpace_isAlgebraicSpace (hF : BasedFunctor.Representable F)
    (S : Scheme.{u}) (y : Y.obj (op S)) :
    IsAlgebraicSpace (sourceFiberSpace hF S y) :=
  (Classical.choose_spec (hF S (sourceFiberTest S y))).1

/-- The chosen equivalence from the algebraic-space fiber to the prestack fiber
product. -/
noncomputable def sourceFiberRepresentation (hF : BasedFunctor.Representable F)
    (S : Scheme.{u}) (y : Y.obj (op S)) :
    ofPresheaf (sourceFiberSpace hF S y) ⥤ᵇ
      fiberProduct F (sourceFiberTest S y) :=
  Classical.choose (Classical.choose_spec
    (hF S (sourceFiberTest S y))).2

omit [Xcat.p.IsFiberedInGroupoids] in
/-- The chosen source-fiber representation is an equivalence. -/
lemma sourceFiberRepresentation_isEquivalence
    (hF : BasedFunctor.Representable F) (S : Scheme.{u})
    (y : Y.obj (op S)) :
    (sourceFiberRepresentation hF S y).toFunctor.IsEquivalence :=
  Classical.choose_spec (Classical.choose_spec
    (hF S (sourceFiberTest S y))).2

/-- A small type of codes for the connected components of the source fiber. -/
noncomputable def sourceComponentCode (hF : BasedFunctor.Representable F)
    (S : Scheme.{u}) : Type u :=
  Σ y : Y.obj (op S), (sourceFiberSpace hF S y).obj (op S)

/-- The source-fiber object decoded from a target-fiber object and a point of its
algebraic-space base change. -/
noncomputable def sourceComponentCodeFiberObj (hF : BasedFunctor.Representable F)
    (S : Scheme.{u}) (c : sourceComponentCode hF S) : Xcat.p.Fiber S :=
  let E := sourceFiberRepresentation hF S c.1
  let d : (ofPresheaf (sourceFiberSpace hF S c.1)).obj :=
    CostructuredArrow.mk (yonedaEquiv.symm c.2)
  ⟨(E.obj d).fst, E.w_obj d⟩

/-- Decode a small source-component code to a connected component of the source
fiber. -/
noncomputable def sourceComponentCodeToComponent
    (hF : BasedFunctor.Representable F) (S : Scheme.{u}) :
    sourceComponentCode hF S →
      CategoryTheory.ConnectedComponents (Xcat.p.Fiber S) :=
  fun c ↦ CategoryTheory.ConnectedComponents.mk
    (sourceComponentCodeFiberObj hF S c)

/-- Every connected component of a source fiber is represented by a small code. -/
theorem sourceComponentCodeToComponent_surjective
    (hF : BasedFunctor.Representable F) (S : Scheme.{u}) :
    Function.Surjective (sourceComponentCodeToComponent hF S) := by
  intro j
  let a : Xcat.p.Fiber S := componentRepresentative (𝒳 := Xcat) j
  obtain ⟨y, hy⟩ := ofPresheafFiberObj_surjective Y S ((F.onFiber S).obj a)
  let G := sourceFiberTest (Y := Y) S y
  let t : Over S := Over.mk (𝟙 S)
  let π : G.obj t ⟶ (ofPresheafFiberObj Y S y).1 :=
    IsPreFibered.pullbackMap (ofPresheafFiberObj Y S y).2 (𝟙 S)
  let hπ : IsHomLift (ofPresheaf Y).p (𝟙 S) π := inferInstance
  let hπIso : IsIso π :=
    IsFiberedInGroupoids.isIso_of_isHomLift_isIso
      (p := (ofPresheaf Y).p) (𝟙 S) π
  let e₀ : F.obj a.1 ≅ (ofPresheafFiberObj Y S y).1 :=
    Fiber.fiberInclusion.mapIso (eqToIso hy).symm
  let e : F.obj a.1 ≅ G.obj t := e₀ ≪≫ (asIso π).symm
  have heS : IsHomLift (ofPresheaf Y).p (𝟙 S) e.hom := by
    have he₀ : IsHomLift (ofPresheaf Y).p (𝟙 S) e₀.hom := by
      dsimp only [e₀]
      exact (eqToIso hy).symm.hom.2
    have hπinv : IsHomLift (ofPresheaf Y).p (𝟙 S) (asIso π).symm.hom := by
      change IsHomLift (ofPresheaf Y).p (𝟙 S) (inv π)
      infer_instance
    simpa only [e, Iso.trans_hom, Category.id_comp] using
      IsHomLift.comp (ofPresheaf Y).p (𝟙 S) (𝟙 S) e₀.hom (asIso π).symm.hom
  have he : IsHomLift (ofPresheaf Y).p (𝟙 (Xcat.p.obj a.1)) e.hom := by
    rw [a.2]
    exact heS
  let B : FiberProductObj F G :=
    { fst := a.1
      snd := t
      over_eq := a.2.symm
      iso := e
      isHomLift := he }
  let E := sourceFiberRepresentation hF S y
  let _ : E.toFunctor.IsEquivalence :=
    sourceFiberRepresentation_isEquivalence hF S y
  let d := ofPresheaf.ptObj E B a.2.symm
  let z : (sourceFiberSpace hF S y).obj (op S) := yonedaEquiv d.hom
  let c : sourceComponentCode hF S := ⟨y, z⟩
  let α : E.obj d ≅ B := ofPresheaf.ptObjIso E B a.2.symm
  have hαlift : IsHomLift Xcat.p (𝟙 S) α.hom.fst := by
    apply IsHomLift.of_fac' Xcat.p (𝟙 S) α.hom.fst (E.w_obj d) a.2
    change (fiberProduct F G).p.map α.hom = _
    rw [ofPresheaf.ptObjIso_base]
    simp
  let φ : (Xcat.p.Fiber S) := ⟨(E.obj d).fst, E.w_obj d⟩
  let q : φ ⟶ a := ⟨α.hom.fst, hαlift⟩
  have hdecode : sourceComponentCodeFiberObj hF S c = φ := by
    apply Subtype.ext
    change (E.obj (CostructuredArrow.mk (yonedaEquiv.symm (yonedaEquiv d.hom)))).fst =
      (E.obj d).fst
    rw [yonedaEquiv.symm_apply_apply, ← CostructuredArrow.eq_mk d]
  refine ⟨c, ?_⟩
  change CategoryTheory.ConnectedComponents.mk
      (sourceComponentCodeFiberObj hF S c) = j
  rw [hdecode]
  calc
    CategoryTheory.ConnectedComponents.mk φ =
        CategoryTheory.ConnectedComponents.mk a :=
      Quotient.sound' (Zigzag.of_hom q)
    _ = j := componentRepresentative_component j

end BasedFunctor.Representable

/-- The source of a representable morphism of prestacks into an algebraic space is
represented by an algebraic space. -/
theorem BasedFunctor.Representable.exists_source_isAlgebraicSpace
    {Xcat : BasedCategory.{v₂, u₂} Scheme.{u}} [Xcat.p.IsFiberedInGroupoids]
    {Y : Scheme.{u}ᵒᵖ ⥤ Type u} [IsAlgebraicSpace Y]
    {F : Xcat ⥤ᵇ ofPresheaf Y} (hF : BasedFunctor.Representable F) :
    ∃ X : Scheme.{u}ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace X ∧ Xcat.IsRepresentedByPresheaf X := by
  let hp : Xcat.p.Faithful := hF.source_projection_faithful
  let _ : Xcat.p.Faithful := hp
  let C := fiberComponents (𝒳 := Xcat)
  have hsmall : FunctorToTypes.Small.{u} C := by
    intro S
    exact small_of_surjective
      (BasedFunctor.Representable.sourceComponentCodeToComponent_surjective
        hF S.unop)
  let _ : FunctorToTypes.Small.{u} C := hsmall
  let X := FunctorToTypes.shrink.{u} C
  let E : ofPresheaf X ⥤ᵇ Xcat :=
    { toFunctor :=
        (CategoryOfElements.costructuredArrowYonedaEquivalence X).inverse ⋙
          (shrinkElementsComparison C).toFunctor ⋙
          (componentPrestackComparison (𝒳 := Xcat)).toFunctor
      w := by
        rw [Functor.assoc, Functor.assoc,
          (componentPrestackComparison (𝒳 := Xcat)).w,
          (shrinkElementsComparison C).w]
        rfl }
  have hE : E.toFunctor.IsEquivalence := by
    have h₁ :=
      (CategoryOfElements.costructuredArrowYonedaEquivalence X).isEquivalence_inverse
    have h₂ := isEquivalence_shrinkElementsComparison C
    have h₃ := isEquivalence_componentPrestackComparison (𝒳 := Xcat)
    have h₁₂ :
        ((CategoryOfElements.costructuredArrowYonedaEquivalence X).inverse ⋙
          (shrinkElementsComparison C).toFunctor).IsEquivalence :=
      Functor.isEquivalence_trans _ _
    exact Functor.isEquivalence_trans _ _
  let _ : E.toFunctor.IsEquivalence := hE
  let H := E.comp F
  have hH : BasedFunctor.Representable H := hF.comp_source_isEquivalence E
  let f := ofPresheafMapOfBasedFunctor H
  let η := ofPresheafMapOfBasedFunctorIso H
  have hf : BasedFunctor.Representable (ofPresheaf.map f) :=
    hH.of_iso η.symm
  have hX : IsAlgebraicSpace X :=
    IsAlgebraicSpace.source_of_representableMap f hf
  exact ⟨X, hX, E, hE⟩

end AlgebraicGeometry
