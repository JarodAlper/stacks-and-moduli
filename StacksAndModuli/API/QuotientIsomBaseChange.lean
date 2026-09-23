module

public import StacksAndModuli.«Section4.4-Equivalence-Relations».«part4.4.3-quotient-stacks-of-groupoids»
public import StacksAndModuli.API.OfPresheafPairFiberProduct

/-!
# Isom prestacks of quotient-stack points through the relation

For a groupoid of presheaves `s, t : R ⇉ U` with quotient prestack `[U/R]^pre` and a
local stackification `i : [U/R]^pre ⟶ 𝒳`, two `T`-points `a₀ b₀ : Mor(-, T) ⟶ U` induce
`T`-points of the quotient stack, and their Isom prestack — the 2-fiber product of the
induced morphisms `Sch/T ⟶ 𝒳` — is represented by the presheaf

`pointRelation a₀ b₀ = (Mor(-,T) ×_{a₀, U, s} R) ×_{t ∘ pr₂, U, b₀} Mor(-,T)`,

the base change of the relation along the two points.  This is the base-changed form of
`isRepresentedByPresheaf_fiberProduct_quotientPresentation_comp` and the geometric input
for descent arguments about the diagonal of `[U/R]` (Lemma 4.3.14 of *Stacks and
Moduli*).
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Limits Opposite AlgebraicGeometry CategoryTheory.BasedCategory

universe v₂ u₂ u

namespace AlgebraicGeometry.PresheafGroupoid

variable {𝒢 : PresheafGroupoid.{u}} {𝒳st : BasedCategory.{v₂, u₂} Scheme.{u}}
  {i : 𝒢.quotientPrestack ⥤ᵇ 𝒳st}

variable {T : Scheme.{u}} (a₀ b₀ : yoneda.obj T ⟶ 𝒢.U)

/-- The base change of the relation presheaf of a groupoid along two `T`-points of its
object presheaf: sections over `W` are triples `(x, r, y)` of two `W`-points of `T` and
a relation `r ∈ R(W)` with `s r = a₀ x` and `t r = b₀ y`. -/
noncomputable abbrev pointRelation : Scheme.{u}ᵒᵖ ⥤ Type u :=
  Presheaf.fiberProduct
    (Presheaf.fiberProduct.snd a₀ 𝒢.s ≫ 𝒢.t) b₀

variable (𝒢) in
/-- The `T`-point of the quotient prestack induced by a point `a₀ : Mor(-, T) ⟶ U`. -/
noncomputable abbrev objectPoint (a₀ : yoneda.obj T ⟶ 𝒢.U) :
    overBased T ⥤ᵇ ofPresheaf 𝒢.U :=
  (overBasedToOfPresheafYoneda T).comp (ofPresheaf.map a₀)

/-- The first `T`-point extracted from a section of the base-changed relation. -/
noncomputable abbrev pointRelation.x {W : Scheme.{u}}
    (w : yoneda.obj W ⟶ pointRelation (𝒢 := 𝒢) a₀ b₀) : W ⟶ T :=
  Yoneda.fullyFaithful.preimage
    (w ≫ Presheaf.fiberProduct.fst _ b₀ ≫ Presheaf.fiberProduct.fst a₀ 𝒢.s)

/-- The relation extracted from a section of the base-changed relation. -/
noncomputable abbrev pointRelation.r {W : Scheme.{u}}
    (w : yoneda.obj W ⟶ pointRelation (𝒢 := 𝒢) a₀ b₀) : yoneda.obj W ⟶ 𝒢.R :=
  w ≫ Presheaf.fiberProduct.fst _ b₀ ≫ Presheaf.fiberProduct.snd a₀ 𝒢.s

/-- The second `T`-point extracted from a section of the base-changed relation. -/
noncomputable abbrev pointRelation.y {W : Scheme.{u}}
    (w : yoneda.obj W ⟶ pointRelation (𝒢 := 𝒢) a₀ b₀) : W ⟶ T :=
  Yoneda.fullyFaithful.preimage (w ≫ Presheaf.fiberProduct.snd _ b₀)

lemma pointRelation.x_spec {W : Scheme.{u}}
    (w : yoneda.obj W ⟶ pointRelation (𝒢 := 𝒢) a₀ b₀) :
    yoneda.map (pointRelation.x a₀ b₀ w) =
      w ≫ Presheaf.fiberProduct.fst _ b₀ ≫ Presheaf.fiberProduct.fst a₀ 𝒢.s :=
  Yoneda.fullyFaithful.map_preimage _

lemma pointRelation.y_spec {W : Scheme.{u}}
    (w : yoneda.obj W ⟶ pointRelation (𝒢 := 𝒢) a₀ b₀) :
    yoneda.map (pointRelation.y a₀ b₀ w) = w ≫ Presheaf.fiberProduct.snd _ b₀ :=
  Yoneda.fullyFaithful.map_preimage _

/-- The source equation of the extracted relation. -/
lemma pointRelation.s_eq {W : Scheme.{u}}
    (w : yoneda.obj W ⟶ pointRelation (𝒢 := 𝒢) a₀ b₀) :
    pointRelation.r a₀ b₀ w ≫ 𝒢.s = yoneda.map (pointRelation.x a₀ b₀ w) ≫ a₀ := by
  rw [pointRelation.x_spec]
  have h := Presheaf.fiberProduct.condition a₀ 𝒢.s
  rw [pointRelation.r, Category.assoc, Category.assoc, ← h]
  rfl

/-- The target equation of the extracted relation. -/
lemma pointRelation.t_eq {W : Scheme.{u}}
    (w : yoneda.obj W ⟶ pointRelation (𝒢 := 𝒢) a₀ b₀) :
    pointRelation.r a₀ b₀ w ≫ 𝒢.t = yoneda.map (pointRelation.y a₀ b₀ w) ≫ b₀ := by
  rw [pointRelation.y_spec]
  have h := Presheaf.fiberProduct.condition
    (Presheaf.fiberProduct.snd a₀ 𝒢.s ≫ 𝒢.t) b₀
  have h' := congrArg (fun k ↦ w ≫ k) h
  simpa [pointRelation.r, Category.assoc] using h'

section Comparison

variable (i)

/-- The arrow of the quotient prestack attached to a section of the base-changed
relation: the relation component relates the two induced points of the object
presheaf. -/
noncomputable def pointRelationHom {W : Scheme.{u}}
    (w : yoneda.obj W ⟶ pointRelation (𝒢 := 𝒢) a₀ b₀) :
    (𝒢.quotientPresentation.obj
        ((objectPoint 𝒢 a₀).obj (Over.mk (pointRelation.x a₀ b₀ w))) ⟶
      𝒢.quotientPresentation.obj
        ((objectPoint 𝒢 b₀).obj (Over.mk (pointRelation.y a₀ b₀ w)))) where
  hom := 𝟙 W
  rel := yonedaEquiv (pointRelation.r a₀ b₀ w)
  s_rel := by
    change 𝒢.s.app (op W) (yonedaEquiv (pointRelation.r a₀ b₀ w)) =
      yonedaEquiv (yoneda.map (pointRelation.x a₀ b₀ w) ≫ a₀)
    rw [← yonedaEquiv_comp, pointRelation.s_eq]
  t_rel := by
    change 𝒢.t.app (op W) (yonedaEquiv (pointRelation.r a₀ b₀ w)) =
      𝒢.U.map (𝟙 W).op (yonedaEquiv (yoneda.map (pointRelation.y a₀ b₀ w) ≫ b₀))
    rw [← yonedaEquiv_comp, pointRelation.t_eq]
    simp

/-- The attached arrow lies over the identity. -/
lemma pointRelationHom_isHomLift {W : Scheme.{u}}
    (w : yoneda.obj W ⟶ pointRelation (𝒢 := 𝒢) a₀ b₀) :
    𝒢.quotientProj.IsHomLift (𝟙 W) (pointRelationHom a₀ b₀ w) :=
  IsHomLift.of_fac 𝒢.quotientProj (𝟙 W) (pointRelationHom a₀ b₀ w) rfl rfl (by
    simp [pointRelationHom])

/-- The attached arrow, made invertible by the groupoid structure. -/
noncomputable def pointRelationIso {W : Scheme.{u}}
    (w : yoneda.obj W ⟶ pointRelation (𝒢 := 𝒢) a₀ b₀) :
    𝒢.quotientPresentation.obj
        ((objectPoint 𝒢 a₀).obj (Over.mk (pointRelation.x a₀ b₀ w))) ≅
      𝒢.quotientPresentation.obj
        ((objectPoint 𝒢 b₀).obj (Over.mk (pointRelation.y a₀ b₀ w))) := by
  let f := pointRelationHom a₀ b₀ w
  let _ : 𝒢.quotientProj.IsHomLift (𝟙 W) f := pointRelationHom_isHomLift a₀ b₀ w
  let _ : IsIso f :=
    Functor.IsFiberedInGroupoids.isIso_of_isHomLift_id
      (p := 𝒢.quotientProj) (S := W) f
  exact asIso f

/-- The comparison from the prestack of the base-changed relation to the Isom prestack
of the two induced quotient-stack points. -/
noncomputable def pointRelationComparison :
    ofPresheaf (pointRelation (𝒢 := 𝒢) a₀ b₀) ⥤ᵇ
      fiberProduct
        ((objectPoint 𝒢 a₀).comp (𝒢.quotientPresentation.comp i))
        ((objectPoint 𝒢 b₀).comp (𝒢.quotientPresentation.comp i)) where
  obj d :=
    { fst := Over.mk (pointRelation.x a₀ b₀ d.hom)
      snd := Over.mk (pointRelation.y a₀ b₀ d.hom)
      over_eq := rfl
      iso := i.toFunctor.mapIso (pointRelationIso a₀ b₀ d.hom)
      isHomLift := by
        change 𝒳st.p.IsHomLift (𝟙 d.left) (i.map (pointRelationIso a₀ b₀ d.hom).hom)
        have h : 𝒢.quotientProj.IsHomLift (𝟙 d.left)
            (pointRelationIso a₀ b₀ d.hom).hom := by
          change 𝒢.quotientProj.IsHomLift (𝟙 d.left) (pointRelationHom a₀ b₀ d.hom)
          exact pointRelationHom_isHomLift a₀ b₀ d.hom
        let _ := h
        exact i.preserves_isHomLift _ _ }
  map {d e} q :=
    { fst := Over.homMk q.left (by
        change q.left ≫ pointRelation.x a₀ b₀ e.hom = pointRelation.x a₀ b₀ d.hom
        apply yoneda.map_injective
        rw [yoneda.map_comp, pointRelation.x_spec a₀ b₀ e.hom,
          pointRelation.x_spec a₀ b₀ d.hom, ← CostructuredArrow.w q]
        simp only [Category.assoc])
      snd := Over.homMk q.left (by
        change q.left ≫ pointRelation.y a₀ b₀ e.hom = pointRelation.y a₀ b₀ d.hom
        apply yoneda.map_injective
        rw [yoneda.map_comp, pointRelation.y_spec a₀ b₀ e.hom,
          pointRelation.y_spec a₀ b₀ d.hom, ← CostructuredArrow.w q]
        simp only [Category.assoc])
      isHomLift := by
        apply IsHomLift.of_fac' (Over.forget T) _ _ rfl rfl
        rfl
      w := by
        change i.map _ ≫ i.map (pointRelationIso a₀ b₀ e.hom).hom =
          i.map (pointRelationIso a₀ b₀ d.hom).hom ≫ i.map _
        rw [← i.toFunctor.map_comp, ← i.toFunctor.map_comp]
        apply congrArg i.map
        apply QuotientHom.ext
        · change q.left ≫ 𝟙 e.left = 𝟙 d.left ≫ q.left
          simp
        · have hq : 𝒢.R.map q.left.op (yonedaEquiv (pointRelation.r a₀ b₀ e.hom)) =
              yonedaEquiv (pointRelation.r a₀ b₀ d.hom) := by
            rw [yonedaEquiv_naturality]
            apply congrArg yonedaEquiv
            rw [pointRelation.r, pointRelation.r, ← Category.assoc,
              CostructuredArrow.w q]
          change
            𝒢.comp (𝒢.R.map q.left.op (yonedaEquiv (pointRelation.r a₀ b₀ e.hom)))
                (𝒢.e.app _ _) _ =
              𝒢.comp (𝒢.R.map (𝟙 d.left).op (𝒢.e.app _ _))
                (yonedaEquiv (pointRelation.r a₀ b₀ d.hom)) _
          simpa only [PresheafGroupoid.map_e_app, Functor.map_id_apply,
            PresheafGroupoid.comp_e_app, PresheafGroupoid.e_app_comp] using hq }
  map_id d := by
    apply FiberProductHom.ext
    · apply Over.OverMorphism.ext
      rfl
    · apply Over.OverMorphism.ext
      rfl
  map_comp q r := by
    apply FiberProductHom.ext <;> (apply Over.OverMorphism.ext; rfl)
  w := rfl

/-- Two sections of the base-changed relation agree as soon as their three components
agree. -/
lemma pointRelation.section_ext {W : Scheme.{u}}
    {w w' : yoneda.obj W ⟶ pointRelation (𝒢 := 𝒢) a₀ b₀}
    (hx : pointRelation.x a₀ b₀ w = pointRelation.x a₀ b₀ w')
    (hr : pointRelation.r a₀ b₀ w = pointRelation.r a₀ b₀ w')
    (hy : pointRelation.y a₀ b₀ w = pointRelation.y a₀ b₀ w') : w = w' := by
  have hx' := (pointRelation.x_spec a₀ b₀ w).symm.trans
    ((congrArg yoneda.map hx).trans (pointRelation.x_spec a₀ b₀ w'))
  have hy' := (pointRelation.y_spec a₀ b₀ w).symm.trans
    ((congrArg yoneda.map hy).trans (pointRelation.y_spec a₀ b₀ w'))
  refine Presheaf.fiberProduct.hom_ext _ b₀ ?_ ?_
  · refine Presheaf.fiberProduct.hom_ext a₀ 𝒢.s ?_ ?_
    · simpa [Category.assoc] using hx'
    · simpa [pointRelation.r, Category.assoc] using hr
  · simpa [Category.assoc] using hy'

/-- The comparison is faithful. -/
lemma pointRelationComparison_faithful :
    (pointRelationComparison i a₀ b₀).toFunctor.Faithful := by
  constructor
  intro d e q q' h
  apply CostructuredArrow.hom_ext
  have h₁ := congrArg (fun k ↦ CommaMorphism.left (FiberProductHom.fst k)) h
  exact h₁

/-- The comparison is full. -/
lemma pointRelationComparison_full
    (hi : BasedFunctor.IsLocalStackification (J := Scheme.etaleTopology) i) :
    (pointRelationComparison i a₀ b₀).toFunctor.Full := by
  constructor
  intro d e k
  let f₁ : d.left ⟶ e.left := (FiberProductHom.fst k).left
  -- the second component lies over the same scheme morphism
  have hf₂ : (FiberProductHom.snd k).left = f₁ := by
    have := k.isHomLift
    have h := IsHomLift.fac' (overBased T).p
      ((overBased T).p.map (FiberProductHom.fst k)) (FiberProductHom.snd k)
    simpa using h
  -- the x- and y-components are compatible
  have hxw : f₁ ≫ pointRelation.x a₀ b₀ e.hom = pointRelation.x a₀ b₀ d.hom :=
    Over.w (FiberProductHom.fst k)
  have hyw : f₁ ≫ pointRelation.y a₀ b₀ e.hom = pointRelation.y a₀ b₀ d.hom := by
    have h : (FiberProductHom.snd k).left ≫ pointRelation.y a₀ b₀ e.hom =
        pointRelation.y a₀ b₀ d.hom := Over.w (FiberProductHom.snd k)
    rwa [hf₂] at h
  -- the relation components are compatible, by faithfulness of the stackification map
  have hrel : 𝒢.R.map f₁.op (yonedaEquiv (pointRelation.r a₀ b₀ e.hom)) =
      yonedaEquiv (pointRelation.r a₀ b₀ d.hom) := by
    have hw := FiberProductHom.w k
    let _ : i.toFunctor.Faithful := hi.faithful
    have hw' :
        𝒢.quotientPresentation.map ((objectPoint 𝒢 a₀).map (FiberProductHom.fst k)) ≫
            (pointRelationIso a₀ b₀ e.hom).hom =
          (pointRelationIso a₀ b₀ d.hom).hom ≫
            𝒢.quotientPresentation.map
              ((objectPoint 𝒢 b₀).map (FiberProductHom.snd k)) := by
      apply i.toFunctor.map_injective
      rw [i.toFunctor.map_comp, i.toFunctor.map_comp]
      exact hw
    have hrelEq := congrArg QuotientHom.rel hw'
    change 𝒢.comp (𝒢.R.map f₁.op (yonedaEquiv (pointRelation.r a₀ b₀ e.hom)))
        (𝒢.e.app _ _) _ =
      𝒢.comp (𝒢.R.map (𝟙 d.left).op (𝒢.e.app _ _))
        (yonedaEquiv (pointRelation.r a₀ b₀ d.hom)) _ at hrelEq
    simpa only [PresheafGroupoid.map_e_app, Functor.map_id_apply,
      PresheafGroupoid.comp_e_app, PresheafGroupoid.e_app_comp] using hrelEq
  have hrw : yoneda.map f₁ ≫ pointRelation.r a₀ b₀ e.hom =
      pointRelation.r a₀ b₀ d.hom := by
    apply yonedaEquiv.injective
    rw [← hrel, ← yonedaEquiv_naturality]
  -- assemble the morphism of sections
  refine ⟨CostructuredArrow.homMk f₁ ?_, ?_⟩
  · apply pointRelation.section_ext a₀ b₀
    · change pointRelation.x a₀ b₀ (yoneda.map f₁ ≫ e.hom) =
        pointRelation.x a₀ b₀ d.hom
      rw [← hxw]
      apply yoneda.map_injective
      rw [pointRelation.x_spec, yoneda.map_comp, pointRelation.x_spec]
      simp [Category.assoc]
    · change pointRelation.r a₀ b₀ (yoneda.map f₁ ≫ e.hom) =
        pointRelation.r a₀ b₀ d.hom
      rw [← hrw]
      rw [pointRelation.r, pointRelation.r]
      simp [Category.assoc]
    · change pointRelation.y a₀ b₀ (yoneda.map f₁ ≫ e.hom) =
        pointRelation.y a₀ b₀ d.hom
      rw [← hyw]
      apply yoneda.map_injective
      rw [pointRelation.y_spec, yoneda.map_comp, pointRelation.y_spec]
      simp [Category.assoc]
  · apply FiberProductHom.ext
    · apply Over.OverMorphism.ext
      rfl
    · apply Over.OverMorphism.ext
      exact hf₂.symm

/-- The universal pairing into an explicit presheaf fiber product. -/
noncomputable def _root_.CategoryTheory.Presheaf.fiberProduct.lift'
    {F G G' Z : Scheme.{u}ᵒᵖ ⥤ Type u} {α : F ⟶ G} {β : G' ⟶ G}
    (p : Z ⟶ F) (q : Z ⟶ G') (h : p ≫ α = q ≫ β) :
    Z ⟶ Presheaf.fiberProduct α β :=
  Limits.PullbackCone.IsLimit.lift (Presheaf.fiberProduct.isLimit α β) p q h

@[simp]
lemma _root_.CategoryTheory.Presheaf.fiberProduct.lift'_fst
    {F G G' Z : Scheme.{u}ᵒᵖ ⥤ Type u} {α : F ⟶ G} {β : G' ⟶ G}
    (p : Z ⟶ F) (q : Z ⟶ G') (h : p ≫ α = q ≫ β) :
    Presheaf.fiberProduct.lift' p q h ≫ Presheaf.fiberProduct.fst α β = p :=
  Limits.PullbackCone.IsLimit.lift_fst (Presheaf.fiberProduct.isLimit α β) p q h

@[simp]
lemma _root_.CategoryTheory.Presheaf.fiberProduct.lift'_snd
    {F G G' Z : Scheme.{u}ᵒᵖ ⥤ Type u} {α : F ⟶ G} {β : G' ⟶ G}
    (p : Z ⟶ F) (q : Z ⟶ G') (h : p ≫ α = q ≫ β) :
    Presheaf.fiberProduct.lift' p q h ≫ Presheaf.fiberProduct.snd α β = q :=
  Limits.PullbackCone.IsLimit.lift_snd (Presheaf.fiberProduct.isLimit α β) p q h

/-- The section of the base-changed relation attached to an object of the Isom
prestack of the two induced quotient-stack points. -/
noncomputable def isomObjSection
    (c : FiberProductObj
      ((objectPoint 𝒢 a₀).comp (𝒢.quotientPresentation.comp i))
      ((objectPoint 𝒢 b₀).comp (𝒢.quotientPresentation.comp i)))
    (φ : 𝒢.quotientPresentation.obj ((objectPoint 𝒢 a₀).obj c.fst) ⟶
      𝒢.quotientPresentation.obj ((objectPoint 𝒢 b₀).obj c.snd))
    (hφhom : φ.hom = eqToHom c.over_eq.symm) :
    yoneda.obj c.fst.left ⟶ pointRelation (𝒢 := 𝒢) a₀ b₀ := by
  refine Presheaf.fiberProduct.lift'
    (Presheaf.fiberProduct.lift' (yoneda.map c.fst.hom)
      ((yonedaEquiv.symm φ.rel : yoneda.obj c.fst.left ⟶ 𝒢.R)) ?_)
    (yoneda.map (eqToHom c.over_eq.symm ≫ c.snd.hom)) ?_
  · -- the source equation
    apply yonedaEquiv.injective
    conv_rhs => rw [yonedaEquiv_comp]
    rw [Equiv.apply_symm_apply]
    exact φ.s_rel.symm
  · -- the target equation
    rw [← Category.assoc, Presheaf.fiberProduct.lift'_snd]
    apply yonedaEquiv.injective
    conv_lhs => rw [yonedaEquiv_comp]
    rw [Equiv.apply_symm_apply]
    change 𝒢.t.app (op (𝒢.quotientPresentation.obj
      ((objectPoint 𝒢 a₀).obj c.fst)).base) φ.rel = _
    rw [φ.t_rel]
    change 𝒢.U.map φ.hom.op (yonedaEquiv (yoneda.map c.snd.hom ≫ b₀)) = _
    rw [yonedaEquiv_naturality, hφhom, yoneda.map_comp, Category.assoc]
    rfl

lemma isomObjSection_x
    (c : FiberProductObj
      ((objectPoint 𝒢 a₀).comp (𝒢.quotientPresentation.comp i))
      ((objectPoint 𝒢 b₀).comp (𝒢.quotientPresentation.comp i)))
    (φ : 𝒢.quotientPresentation.obj ((objectPoint 𝒢 a₀).obj c.fst) ⟶
      𝒢.quotientPresentation.obj ((objectPoint 𝒢 b₀).obj c.snd))
    (hφhom : φ.hom = eqToHom c.over_eq.symm) :
    pointRelation.x a₀ b₀ (isomObjSection i a₀ b₀ c φ hφhom) = c.fst.hom := by
  apply yoneda.map_injective
  rw [pointRelation.x_spec, isomObjSection]
  rw [← Category.assoc, Presheaf.fiberProduct.lift'_fst,
    Presheaf.fiberProduct.lift'_fst]

lemma isomObjSection_y
    (c : FiberProductObj
      ((objectPoint 𝒢 a₀).comp (𝒢.quotientPresentation.comp i))
      ((objectPoint 𝒢 b₀).comp (𝒢.quotientPresentation.comp i)))
    (φ : 𝒢.quotientPresentation.obj ((objectPoint 𝒢 a₀).obj c.fst) ⟶
      𝒢.quotientPresentation.obj ((objectPoint 𝒢 b₀).obj c.snd))
    (hφhom : φ.hom = eqToHom c.over_eq.symm) :
    pointRelation.y a₀ b₀ (isomObjSection i a₀ b₀ c φ hφhom) =
      eqToHom c.over_eq.symm ≫ c.snd.hom := by
  apply yoneda.map_injective
  rw [pointRelation.y_spec, isomObjSection]
  simp

lemma isomObjSection_r
    (c : FiberProductObj
      ((objectPoint 𝒢 a₀).comp (𝒢.quotientPresentation.comp i))
      ((objectPoint 𝒢 b₀).comp (𝒢.quotientPresentation.comp i)))
    (φ : 𝒢.quotientPresentation.obj ((objectPoint 𝒢 a₀).obj c.fst) ⟶
      𝒢.quotientPresentation.obj ((objectPoint 𝒢 b₀).obj c.snd))
    (hφhom : φ.hom = eqToHom c.over_eq.symm) :
    pointRelation.r a₀ b₀ (isomObjSection i a₀ b₀ c φ hφhom) =
      yonedaEquiv.symm φ.rel := by
  rw [pointRelation.r, isomObjSection]
  rw [← Category.assoc, Presheaf.fiberProduct.lift'_fst,
    Presheaf.fiberProduct.lift'_snd]
  rfl

/-- The comparison is essentially surjective: every object of the Isom prestack of two
induced quotient-stack points comes from a section of the base-changed relation, by
lifting its comparison isomorphism through the fully faithful stackification map. -/
lemma pointRelationComparison_essSurj
    (hi : BasedFunctor.IsLocalStackification (J := Scheme.etaleTopology) i) :
    (pointRelationComparison i a₀ b₀).toFunctor.EssSurj := by
  constructor
  intro c
  let _ : i.toFunctor.Full := hi.full
  let _ : i.toFunctor.Faithful := hi.faithful
  obtain ⟨φ, hφ⟩ := i.toFunctor.map_surjective c.iso.hom
  have hlift : 𝒳st.p.IsHomLift (𝟙 c.fst.left) (i.map φ) := by
    rw [hφ]
    exact c.isHomLift
  have hφhom : φ.hom = eqToHom c.over_eq.symm := by
    have hcomp : (i.toFunctor ⋙ 𝒳st.p).IsHomLift (𝟙 c.fst.left) φ :=
      IsHomLift.of_fac' _ _ _
        (IsHomLift.domain_eq 𝒳st.p (𝟙 c.fst.left) (i.map φ))
        (IsHomLift.codomain_eq 𝒳st.p (𝟙 c.fst.left) (i.map φ))
        (IsHomLift.fac' 𝒳st.p (𝟙 c.fst.left) (i.map φ))
    have hq : 𝒢.quotientPrestack.p.IsHomLift (𝟙 c.fst.left) φ := i.w ▸ hcomp
    have hfac := IsHomLift.fac' 𝒢.quotientPrestack.p (𝟙 c.fst.left) φ
    change φ.hom = _ at hfac
    rw [hfac]
    simp
  refine ⟨CostructuredArrow.mk (isomObjSection i a₀ b₀ c φ hφhom), ⟨?_⟩⟩
  refine FiberProductObj.isoMk
    (Over.isoMk (Iso.refl c.fst.left) (by
      change 𝟙 c.fst.left ≫ c.fst.hom =
        pointRelation.x a₀ b₀ (isomObjSection i a₀ b₀ c φ hφhom)
      rw [Category.id_comp, isomObjSection_x]))
    (Over.isoMk (eqToIso c.over_eq.symm) (by
      change eqToHom c.over_eq.symm ≫ c.snd.hom =
        pointRelation.y a₀ b₀ (isomObjSection i a₀ b₀ c φ hφhom)
      rw [isomObjSection_y]))
    (by
      apply IsHomLift.of_fac' (Over.forget T) _ _ rfl c.over_eq
      change eqToHom c.over_eq.symm = 𝟙 c.fst.left ≫ eqToHom c.over_eq.symm
      rw [Category.id_comp])
    (by
      change i.map _ ≫ c.iso.hom = i.map (pointRelationIso a₀ b₀ _).hom ≫ i.map _
      rw [← hφ, ← i.toFunctor.map_comp, ← i.toFunctor.map_comp]
      apply congrArg i.map
      apply QuotientHom.ext
      · change 𝟙 c.fst.left ≫ φ.hom = 𝟙 c.fst.left ≫ eqToHom c.over_eq.symm
        rw [hφhom]
      · have hrel : yonedaEquiv (pointRelation.r a₀ b₀
            (isomObjSection i a₀ b₀ c φ hφhom)) = φ.rel := by
          rw [isomObjSection_r]
          exact Equiv.apply_symm_apply _ _
        change 𝒢.comp (𝒢.R.map (𝟙 c.fst.left).op φ.rel) (𝒢.e.app _ _) _ =
          𝒢.comp (𝒢.R.map (𝟙 c.fst.left).op (𝒢.e.app _ _))
            (yonedaEquiv (pointRelation.r a₀ b₀ (isomObjSection i a₀ b₀ c φ hφhom))) _
        simp only [hrel]
        simp only [PresheafGroupoid.map_e_app, Functor.map_id_apply,
          PresheafGroupoid.comp_e_app, PresheafGroupoid.e_app_comp]
        simp)

/-- The comparison is an equivalence. -/
theorem isEquivalence_pointRelationComparison
    (hi : BasedFunctor.IsLocalStackification (J := Scheme.etaleTopology) i) :
    (pointRelationComparison i a₀ b₀).toFunctor.IsEquivalence :=
  { faithful := pointRelationComparison_faithful i a₀ b₀
    full := pointRelationComparison_full i a₀ b₀ hi
    essSurj := pointRelationComparison_essSurj i a₀ b₀ hi }

/-- The Isom prestack of two induced `T`-points of a quotient stack is represented by
the base change of the relation along the two points. -/
theorem isRepresentedByPresheaf_fiberProduct_objectPoints
    (hi : BasedFunctor.IsLocalStackification (J := Scheme.etaleTopology) i) :
    (fiberProduct
        ((objectPoint 𝒢 a₀).comp (𝒢.quotientPresentation.comp i))
        ((objectPoint 𝒢 b₀).comp
          (𝒢.quotientPresentation.comp i))).IsRepresentedByPresheaf
      (pointRelation (𝒢 := 𝒢) a₀ b₀) :=
  ⟨pointRelationComparison i a₀ b₀, isEquivalence_pointRelationComparison i a₀ b₀ hi⟩

end Comparison

end AlgebraicGeometry.PresheafGroupoid
