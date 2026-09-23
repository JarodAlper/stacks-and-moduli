module

public import StacksAndModuli.«Section3.3-Presheaves-and-Sheaves».«part3.3.4-fiber-products»
public import StacksAndModuli.API.PresheafFiberProduct
public import StacksAndModuli.API.PresheafPrestackHom
public import StacksAndModuli.API.RepresentableWithCharts
public import StacksAndModuli.API.RelativelyRepresentableSourceEquivalence
public import StacksAndModuli.API.FiberProductPostcomp
public import StacksAndModuli.API.ModuleFlatteningImmersion
public import StacksAndModuli.API.RelativeDiagonalBaseChange
public import StacksAndModuli.API.PresheafPrestackHom

/-!
# Fiber products of prestacks of presheaves over a common presheaf target

For two morphisms of presheaves `φ φ' : X ⟶ Y`, the 2-fiber product of the induced
morphisms of associated prestacks `ofPresheaf.map φ` and `ofPresheaf.map φ'` is again a
prestack of presheaves: it is equivalent to the prestack associated to the explicit
presheaf fiber product `X ×_Y X` of Equation 3.3.13. The equivalence is constructed in
the projection direction (`ofPresheafPairFiberProductProj`), following the convention of
`StacksAndModuli/API/PresheafFiberProduct.lean` that based functors are never inverted.

Combined with the presheaf-level relative diagonal `Presheaf.fiberProduct.diagLift`, this
identifies the relative diagonal of `ofPresheaf.map φ` with the morphism of prestacks
induced by a presheaf map, and transfers relative representability accordingly:

- `CategoryTheory.Presheaf.fiberProduct.diagLift`: the relative diagonal
  `X ⟶ X ×_Y X` of a presheaf map, with its projection identities;
- `CategoryTheory.Functor.relativelyRepresentable.of_comp_mono`: relative
  representability may be cancelled from a composition with a monomorphism;
- `CategoryTheory.Presheaf.fiberProduct.relativelyRepresentable_diagLift`: if the
  absolute diagonal of `X` is relatively representable, so is the relative diagonal of
  any presheaf map out of `X`;
- `CategoryTheory.BasedCategory.ofPresheafPairFiberProductProj` and
  `isEquivalence_ofPresheafPairFiberProductProj`: the equivalence
  `ofPresheaf X ×_{ofPresheaf Y} ofPresheaf X ≌ ofPresheaf (X ×_Y X)`;
- `CategoryTheory.BasedCategory.ofPresheafMapDiagCompProjIso`: under that equivalence
  the relative diagonal of `ofPresheaf.map φ` is the prestack morphism of `diagLift φ`;
- `CategoryTheory.BasedFunctor.relativelyRepresentableWith_top_diag_ofPresheaf_map` and
  `relativelyRepresentableWith_top_diag_of_target_overBased`: the resulting relative
  representability of the relative diagonal of a morphism of prestacks out of
  `ofPresheaf X`, for `X` with relatively representable diagonal.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Limits Opposite ConcreteCategory

universe w v u u₁ u₂ v₁ v₂

namespace CategoryTheory.Presheaf.fiberProduct

variable {𝒮 : Type u} [Category.{v} 𝒮] {X X' Y : 𝒮ᵒᵖ ⥤ Type w}
  (φ : X ⟶ Y) (φ' : X' ⟶ Y)

/-- Two morphisms into an explicit presheaf fiber product agree as soon as their
compositions with the two projections agree. -/
lemma hom_ext {Z : 𝒮ᵒᵖ ⥤ Type w} {w₁ w₂ : Z ⟶ Presheaf.fiberProduct φ φ'}
    (h₁ : w₁ ≫ fst φ φ' = w₂ ≫ fst φ φ')
    (h₂ : w₁ ≫ snd φ φ' = w₂ ≫ snd φ φ') : w₁ = w₂ := by
  ext S z
  refine Subtype.ext (Prod.ext ?_ ?_)
  · exact ConcreteCategory.congr_hom (congr_app h₁ S) z
  · exact ConcreteCategory.congr_hom (congr_app h₂ S) z

/-- The relative diagonal of a presheaf map `φ : X ⟶ Y`, valued in the explicit
presheaf fiber product `X ×_Y X`. -/
@[simps]
def diagLift : X ⟶ Presheaf.fiberProduct φ φ where
  app _ := ↾fun x ↦ ⟨⟨x, x⟩, rfl⟩
  naturality _ _ _ := rfl

@[simp]
lemma diagLift_fst : diagLift φ ≫ fst φ φ = 𝟙 X := rfl

@[simp]
lemma diagLift_snd : diagLift φ ≫ snd φ φ = 𝟙 X := rfl

/-- The comparison from the explicit presheaf fiber product to the categorical binary
product, given by the pair of projections. -/
noncomputable def toProd : Presheaf.fiberProduct φ φ' ⟶ X ⨯ X' :=
  prod.lift (fst φ φ') (snd φ φ')

instance mono_toProd : Mono (toProd φ φ') := by
  constructor
  intro Z a b hab
  have h₁ : a ≫ fst φ φ' = b ≫ fst φ φ' := by
    have := congrArg (fun k ↦ k ≫ prod.fst) hab
    simpa [toProd] using this
  have h₂ : a ≫ snd φ φ' = b ≫ snd φ φ' := by
    have := congrArg (fun k ↦ k ≫ prod.snd) hab
    simpa [toProd] using this
  exact hom_ext φ φ' h₁ h₂

/-- The relative diagonal followed by the comparison to the categorical product is the
absolute diagonal. -/
lemma diagLift_comp_toProd : diagLift φ ≫ toProd φ φ = Limits.diag X := by
  apply prod.hom_ext
  · rw [Category.assoc, toProd, prod.lift_fst, diagLift_fst, prod.lift_fst]
  · rw [Category.assoc, toProd, prod.lift_snd, diagLift_snd, prod.lift_snd]

end CategoryTheory.Presheaf.fiberProduct

namespace CategoryTheory.Functor.relativelyRepresentable

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {F : C ⥤ D}

/-- Relative representability may be cancelled from a composition with a
monomorphism. -/
theorem of_comp_mono {A B B' : D} {f : A ⟶ B} (g : B ⟶ B') [Mono g]
    (h : F.relativelyRepresentable (f ≫ g)) : F.relativelyRepresentable f := by
  intro a q
  obtain ⟨b, snd, fst, hpb⟩ := h (q ≫ g)
  exact ⟨b, snd, fst, IsPullback.of_comp_mono g hpb⟩

end CategoryTheory.Functor.relativelyRepresentable

namespace CategoryTheory.Presheaf.fiberProduct

variable {𝒮 : Type u} [Category.{v} 𝒮] {X Y : 𝒮ᵒᵖ ⥤ Type v} (φ : X ⟶ Y)

/-- If the absolute diagonal of a presheaf is relatively representable, then so is the
relative diagonal of every presheaf map out of it. -/
theorem relativelyRepresentable_diagLift
    (hdiag : yoneda.relativelyRepresentable (Limits.diag X)) :
    yoneda.relativelyRepresentable (diagLift φ) := by
  have h : yoneda.relativelyRepresentable (diagLift φ ≫ toProd φ φ) := by
    rw [diagLift_comp_toProd]
    exact hdiag
  exact Functor.relativelyRepresentable.of_comp_mono (toProd φ φ) h

end CategoryTheory.Presheaf.fiberProduct

namespace CategoryTheory.BasedCategory

variable {𝒮 : Type u} [Category.{v} 𝒮] {X X' Y : 𝒮ᵒᵖ ⥤ Type v}
  (φ : X ⟶ Y) (φ' : X' ⟶ Y)

/-- The two classified points underlying an object of the fiber product of two
prestack morphisms of presheaves satisfy the fiber-product equation, after
transporting the second point to the base of the first along the comparison
isomorphism. -/
lemma FiberProductObj.ofPresheafPair_w
    (a : FiberProductObj (ofPresheaf.map φ) (ofPresheaf.map φ')) :
    a.fst.hom ≫ φ = (yoneda.map a.iso.hom.left ≫ a.snd.hom) ≫ φ' := by
  have h := CostructuredArrow.w a.iso.hom
  dsimp [ofPresheaf.map] at h
  rw [Category.assoc]
  exact h.symm

/-- The morphism to the explicit presheaf fiber product classified by an object of the
fiber product of two prestack morphisms of presheaves. -/
noncomputable def FiberProductObj.pairHom
    (a : FiberProductObj (ofPresheaf.map φ) (ofPresheaf.map φ')) :
    yoneda.obj a.fst.left ⟶ Presheaf.fiberProduct φ φ' where
  app T := ↾fun t ↦
    ⟨⟨a.fst.hom.app T t, (yoneda.map a.iso.hom.left ≫ a.snd.hom).app T t⟩, by
      have h := ConcreteCategory.congr_hom
        (congr_app (FiberProductObj.ofPresheafPair_w φ φ' a) T) t
      simpa using h⟩
  naturality T T' f := by
    ext t
    refine Subtype.ext (Prod.ext ?_ ?_)
    · have h := ConcreteCategory.congr_hom (a.fst.hom.naturality f) t
      simpa using h
    · have h := ConcreteCategory.congr_hom
        ((yoneda.map a.iso.hom.left ≫ a.snd.hom).naturality f) t
      simpa using h

@[simp]
lemma FiberProductObj.pairHom_fst
    (a : FiberProductObj (ofPresheaf.map φ) (ofPresheaf.map φ')) :
    a.pairHom φ φ' ≫ Presheaf.fiberProduct.fst φ φ' = a.fst.hom :=
  rfl

@[simp]
lemma FiberProductObj.pairHom_snd
    (a : FiberProductObj (ofPresheaf.map φ) (ofPresheaf.map φ')) :
    a.pairHom φ φ' ≫ Presheaf.fiberProduct.snd φ φ' =
      yoneda.map a.iso.hom.left ≫ a.snd.hom :=
  rfl

/-- The component identity underlying the compatibility field of a morphism in the
fiber product of two prestack morphisms of presheaves. -/
lemma FiberProductHom.ofPresheafPair_left_w
    {a b : FiberProductObj (ofPresheaf.map φ) (ofPresheaf.map φ')} (q : a ⟶ b) :
    (FiberProductHom.fst q).left ≫ b.iso.hom.left =
      a.iso.hom.left ≫ (FiberProductHom.snd q).left := by
  have h := congrArg CommaMorphism.left q.w
  simpa [ofPresheaf.map] using h

/-- The projection from the fiber product of the prestack morphisms of two presheaf
maps to the prestack of the explicit presheaf fiber product. -/
noncomputable def ofPresheafPairFiberProductProj :
    fiberProduct (ofPresheaf.map φ) (ofPresheaf.map φ') ⥤ᵇ
      ofPresheaf (Presheaf.fiberProduct φ φ') where
  obj a := CostructuredArrow.mk (a.pairHom φ φ')
  map {a b} q := CostructuredArrow.homMk (FiberProductHom.fst q).left (by
    change yoneda.map (FiberProductHom.fst q).left ≫ b.pairHom φ φ' = a.pairHom φ φ'
    refine Presheaf.fiberProduct.hom_ext φ φ' ?_ ?_
    · rw [Category.assoc, FiberProductObj.pairHom_fst, FiberProductObj.pairHom_fst]
      exact CostructuredArrow.w (FiberProductHom.fst q)
    · rw [Category.assoc, FiberProductObj.pairHom_snd, FiberProductObj.pairHom_snd]
      calc
        yoneda.map (FiberProductHom.fst q).left ≫
            yoneda.map b.iso.hom.left ≫ b.snd.hom =
          yoneda.map ((FiberProductHom.fst q).left ≫ b.iso.hom.left) ≫
            b.snd.hom := by
            rw [yoneda.map_comp, Category.assoc]
        _ = yoneda.map (a.iso.hom.left ≫ (FiberProductHom.snd q).left) ≫
            b.snd.hom := by
            rw [FiberProductHom.ofPresheafPair_left_w φ φ' q]
        _ = yoneda.map a.iso.hom.left ≫
            yoneda.map (FiberProductHom.snd q).left ≫ b.snd.hom := by
            rw [yoneda.map_comp, Category.assoc]
        _ = yoneda.map a.iso.hom.left ≫ a.snd.hom := by
            rw [CostructuredArrow.w (FiberProductHom.snd q)])
  map_id a := by
    apply CostructuredArrow.hom_ext
    rfl
  map_comp q r := by
    apply CostructuredArrow.hom_ext
    rfl
  w := rfl

@[simp]
lemma ofPresheafPairFiberProductProj_obj
    (a : FiberProductObj (ofPresheaf.map φ) (ofPresheaf.map φ')) :
    (ofPresheafPairFiberProductProj φ φ').obj a =
      CostructuredArrow.mk (a.pairHom φ φ') :=
  rfl

@[simp]
lemma ofPresheafPairFiberProductProj_map_left
    {a b : FiberProductObj (ofPresheaf.map φ) (ofPresheaf.map φ')} (q : a ⟶ b) :
    ((ofPresheafPairFiberProductProj φ φ').map q).left =
      (FiberProductHom.fst q).left :=
  rfl

/-- The comparison isomorphism of an object of the fiber product of two prestack
morphisms of presheaves acts on bases by the transport of the common-base equality. -/
lemma FiberProductObj.ofPresheafPair_iso_hom_left
    (a : FiberProductObj (ofPresheaf.map φ) (ofPresheaf.map φ')) :
    a.iso.hom.left = eqToHom a.over_eq.symm := by
  have := a.isHomLift
  have h := IsHomLift.fac' (ofPresheaf Y).p
    (𝟙 ((ofPresheaf X).p.obj a.fst)) a.iso.hom
  simpa using h

/-- The projection to the prestack of the explicit presheaf fiber product is
faithful. -/
lemma ofPresheafPairFiberProductProj_faithful :
    (ofPresheafPairFiberProductProj φ φ').toFunctor.Faithful := by
  constructor
  intro a b q q' h
  have hfst : (FiberProductHom.fst q).left = (FiberProductHom.fst q').left := by
    have := congrArg CommaMorphism.left h
    simpa using this
  have := q.isHomLift
  have := q'.isHomLift
  have hq := IsHomLift.fac' (ofPresheaf X').p
    ((ofPresheaf X).p.map (FiberProductHom.fst q)) (FiberProductHom.snd q)
  have hq' := IsHomLift.fac' (ofPresheaf X').p
    ((ofPresheaf X).p.map (FiberProductHom.fst q')) (FiberProductHom.snd q')
  refine FiberProductHom.ext ?_ ?_
  · exact CostructuredArrow.hom_ext _ _ hfst
  · apply CostructuredArrow.hom_ext
    have hsnd : (FiberProductHom.snd q).left = (FiberProductHom.snd q').left := by
      change (ofPresheaf X').p.map (FiberProductHom.snd q) =
        (ofPresheaf X').p.map (FiberProductHom.snd q')
      rw [hq, hq']
      change eqToHom _ ≫ (FiberProductHom.fst q).left ≫ eqToHom _ =
        eqToHom _ ≫ (FiberProductHom.fst q').left ≫ eqToHom _
      rw [hfst]
    exact hsnd

/-- The projection to the prestack of the explicit presheaf fiber product is full. -/
lemma ofPresheafPairFiberProductProj_full :
    (ofPresheafPairFiberProductProj φ φ').toFunctor.Full := by
  constructor
  intro a b k
  have hkfst : yoneda.map k.left ≫ b.fst.hom = a.fst.hom := by
    have h := CostructuredArrow.w k
    have h₁ := congrArg (fun z ↦ z ≫ Presheaf.fiberProduct.fst φ φ') h
    simpa using h₁
  have hksnd : yoneda.map k.left ≫ yoneda.map b.iso.hom.left ≫ b.snd.hom =
      yoneda.map a.iso.hom.left ≫ a.snd.hom := by
    have h := CostructuredArrow.w k
    have h₂ := congrArg (fun z ↦ z ≫ Presheaf.fiberProduct.snd φ φ') h
    simpa using h₂
  have hsndTriangle :
      yoneda.map (eqToHom a.over_eq ≫ k.left ≫ eqToHom b.over_eq.symm) ≫
        b.snd.hom = a.snd.hom := by
    rw [FiberProductObj.ofPresheafPair_iso_hom_left,
      FiberProductObj.ofPresheafPair_iso_hom_left] at hksnd
    simp only [eqToHom_map] at hksnd
    simp only [yoneda.map_comp, eqToHom_map, Category.assoc]
    rw [hksnd]
    simp
  let qsnd : a.snd ⟶ b.snd :=
    CostructuredArrow.homMk (eqToHom a.over_eq ≫ k.left ≫ eqToHom b.over_eq.symm)
      hsndTriangle
  have hlift : IsHomLift (ofPresheaf X').p k.left qsnd := by
    apply IsHomLift.of_fac' (ofPresheaf X').p k.left qsnd a.over_eq b.over_eq
    rfl
  let q : a ⟶ b :=
    { fst := CostructuredArrow.homMk k.left hkfst
      snd := qsnd
      isHomLift := hlift
      w := by
        apply CostructuredArrow.hom_ext
        change k.left ≫ b.iso.hom.left = a.iso.hom.left ≫ (qsnd).left
        rw [FiberProductObj.ofPresheafPair_iso_hom_left,
          FiberProductObj.ofPresheafPair_iso_hom_left]
        change k.left ≫ eqToHom b.over_eq.symm =
          eqToHom a.over_eq.symm ≫ eqToHom a.over_eq ≫ k.left ≫
            eqToHom b.over_eq.symm
        rw [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] }
  refine ⟨q, ?_⟩
  apply CostructuredArrow.hom_ext
  rfl

/-- The projection to the prestack of the explicit presheaf fiber product is
essentially surjective. -/
lemma ofPresheafPairFiberProductProj_essSurj :
    (ofPresheafPairFiberProductProj φ φ').toFunctor.EssSurj := by
  constructor
  intro d
  have hcond : (d.hom ≫ Presheaf.fiberProduct.fst φ φ') ≫ φ =
      (d.hom ≫ Presheaf.fiberProduct.snd φ φ') ≫ φ' := by
    rw [Category.assoc, Category.assoc, Presheaf.fiberProduct.condition]
  let a : FiberProductObj (ofPresheaf.map φ) (ofPresheaf.map φ') :=
    { fst := CostructuredArrow.mk (d.hom ≫ Presheaf.fiberProduct.fst φ φ')
      snd := CostructuredArrow.mk (d.hom ≫ Presheaf.fiberProduct.snd φ φ')
      over_eq := rfl
      iso := CostructuredArrow.isoMk (Iso.refl d.left) (by
        change yoneda.map (𝟙 d.left) ≫
          ((d.hom ≫ Presheaf.fiberProduct.snd φ φ') ≫ φ') =
          (d.hom ≫ Presheaf.fiberProduct.fst φ φ') ≫ φ
        rw [yoneda.map_id, Category.id_comp, hcond])
      isHomLift := by
        apply IsHomLift.of_fac' (ofPresheaf Y).p (𝟙 d.left) _ rfl rfl
        change (𝟙 d.left : _) = eqToHom rfl ≫ 𝟙 d.left ≫ eqToHom rfl
        simp }
  refine ⟨a, ⟨?_⟩⟩
  have hpair : a.pairHom φ φ' = d.hom := by
    refine Presheaf.fiberProduct.hom_ext φ φ' ?_ ?_
    · rw [FiberProductObj.pairHom_fst]
      rfl
    · rw [FiberProductObj.pairHom_snd]
      change yoneda.map (𝟙 d.left) ≫
        (d.hom ≫ Presheaf.fiberProduct.snd φ φ') =
        d.hom ≫ Presheaf.fiberProduct.snd φ φ'
      rw [yoneda.map_id, Category.id_comp]
  exact CostructuredArrow.isoMk (Iso.refl d.left) (by
    change yoneda.map (𝟙 d.left) ≫ d.hom = a.pairHom φ φ'
    rw [yoneda.map_id, Category.id_comp, hpair])

/-- The fiber product of the prestack morphisms of two presheaf maps is equivalent, by
the canonical projection, to the prestack of their explicit presheaf fiber product. -/
theorem isEquivalence_ofPresheafPairFiberProductProj :
    (ofPresheafPairFiberProductProj φ φ').toFunctor.IsEquivalence :=
  { faithful := ofPresheafPairFiberProductProj_faithful φ φ'
    full := ofPresheafPairFiberProductProj_full φ φ'
    essSurj := ofPresheafPairFiberProductProj_essSurj φ φ' }

end CategoryTheory.BasedCategory

namespace CategoryTheory.BasedCategory

section OfPresheafDiagCompat

variable {𝒮 : Type u} [Category.{v} 𝒮] {X Y : 𝒮ᵒᵖ ⥤ Type v} (φ : X ⟶ Y)

/-- Under the pair projection, the relative diagonal of the prestack morphism of a
presheaf map is the prestack morphism of its presheaf-level relative diagonal. -/
noncomputable def ofPresheafMapDiagCompProjIso :
    ofPresheaf.map (Presheaf.fiberProduct.diagLift φ) ≅
      (ofPresheaf.map φ).diag.comp (ofPresheafPairFiberProductProj φ φ) :=
  BasedNatIso.mkNatIso
    (NatIso.ofComponents
      (fun d ↦ CostructuredArrow.isoMk (Iso.refl d.left) (by
        change yoneda.map (𝟙 d.left) ≫
          ((ofPresheaf.map φ).diag.obj d).pairHom φ φ =
          d.hom ≫ Presheaf.fiberProduct.diagLift φ
        rw [yoneda.map_id, Category.id_comp]
        refine Presheaf.fiberProduct.hom_ext φ φ ?_ ?_
        · rw [FiberProductObj.pairHom_fst, Category.assoc]
          change d.hom = d.hom ≫ Presheaf.fiberProduct.diagLift φ ≫
            Presheaf.fiberProduct.fst φ φ
          rw [Presheaf.fiberProduct.diagLift_fst, Category.comp_id]
        · rw [FiberProductObj.pairHom_snd, Category.assoc]
          change yoneda.map (𝟙 d.left) ≫ d.hom = d.hom ≫
            Presheaf.fiberProduct.diagLift φ ≫ Presheaf.fiberProduct.snd φ φ
          rw [yoneda.map_id, Category.id_comp,
            Presheaf.fiberProduct.diagLift_snd, Category.comp_id]))
      (fun {d e} q ↦ by
        apply CostructuredArrow.hom_ext
        change q.left ≫ 𝟙 e.left = 𝟙 d.left ≫ q.left
        simp))
    (fun d ↦ by
      apply IsHomLift.of_fac'
        (ofPresheaf (Presheaf.fiberProduct φ φ)).p (𝟙 d.left) _ rfl rfl
      change (𝟙 d.left : _) = eqToHom rfl ≫ 𝟙 d.left ≫ eqToHom rfl
      simp)

end OfPresheafDiagCompat

section DiagPostcomp

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
  {𝒴 : BasedCategory.{v, u} 𝒮} {𝒴₂ : BasedCategory.{w, u₂} 𝒮}

/-- The relative diagonal of a composition with a second morphism is the relative
diagonal of the first morphism followed by the canonical comparison of squares. -/
noncomputable def diagCompPostcompIso (M : 𝒳 ⥤ᵇ 𝒴) (E : 𝒴 ⥤ᵇ 𝒴₂) :
    (M.comp E).diag ≅ M.diag.comp (fiberProductPostcomp M M E) :=
  BasedNatIso.mkNatIso
    (NatIso.ofComponents
      (fun x ↦ FiberProductObj.isoMk (Iso.refl x) (Iso.refl x)
        (by
          change 𝒳.p.IsHomLift (𝒳.p.map (𝟙 x)) (𝟙 x)
          exact IsHomLift.map (p := 𝒳.p) (𝟙 x))
        (by
          change E.map (M.map (𝟙 x)) ≫ E.map (𝟙 (M.obj x)) =
            𝟙 (E.obj (M.obj x)) ≫ E.map (M.map (𝟙 x))
          simp))
      (fun {x y} q ↦ by
        apply FiberProductHom.ext
        · change q ≫ 𝟙 y = 𝟙 x ≫ q
          simp
        · change q ≫ 𝟙 y = 𝟙 x ≫ q
          simp))
    (fun x ↦ by
      apply IsHomLift.of_fac'
        (fiberProduct (M.comp E) (M.comp E)).p (𝟙 (𝒳.p.obj x)) _ rfl rfl
      change 𝒳.p.map (𝟙 x) = eqToHom rfl ≫ 𝟙 (𝒳.p.obj x) ≫ eqToHom rfl
      simp)

end DiagPostcomp

end CategoryTheory.BasedCategory

namespace CategoryTheory.BasedFunctor

open CategoryTheory.BasedCategory

variable {𝒮 : Type u} [Category.{v} 𝒮]

/-- Relative representability with the trivial property is relative
representability. -/
lemma relativelyRepresentableWith_top_iff
    {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₁, u₁} 𝒮} {F : 𝒳 ⥤ᵇ 𝒴} :
    F.RelativelyRepresentableWith (⊤ : MorphismProperty 𝒮) ↔
      F.RelativelyRepresentable :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun _ _ _ _ _ ↦ trivial⟩⟩

/-- The prestack morphism of a relatively representable presheaf map is relatively
representable. -/
theorem relativelyRepresentableWith_top_ofPresheaf_map
    {X Y : 𝒮ᵒᵖ ⥤ Type v} {φ : X ⟶ Y} (hφ : yoneda.relativelyRepresentable φ) :
    (ofPresheaf.map φ).RelativelyRepresentableWith (⊤ : MorphismProperty 𝒮) := by
  refine ⟨fun S g ↦ ?_, fun _ _ _ _ _ ↦ trivial⟩
  exact ⟨hφ.pullback g.ofPresheafHom,
    isRepresentedBy_fiberProduct_ofPresheafMap g hφ⟩

/-- If the absolute diagonal of a presheaf is relatively representable, then the
relative diagonal of the prestack morphism of any presheaf map out of it is relatively
representable. -/
theorem relativelyRepresentableWith_top_diag_ofPresheaf_map
    {X Y : 𝒮ᵒᵖ ⥤ Type v} (φ : X ⟶ Y)
    (hdiag : yoneda.relativelyRepresentable (Limits.diag X)) :
    (ofPresheaf.map φ).diag.RelativelyRepresentableWith
      (⊤ : MorphismProperty 𝒮) := by
  have h₁ : (ofPresheaf.map
      (Presheaf.fiberProduct.diagLift φ)).RelativelyRepresentableWith
      (⊤ : MorphismProperty 𝒮) :=
    relativelyRepresentableWith_top_ofPresheaf_map
      (Presheaf.fiberProduct.relativelyRepresentable_diagLift φ hdiag)
  have h₂ := h₁.of_iso (ofPresheafMapDiagCompProjIso φ)
  exact h₂.of_comp_target_isEquivalence
    (isEquivalence_ofPresheafPairFiberProductProj φ φ)

/-- If the absolute diagonal of a presheaf is relatively representable, then the
relative diagonal of any morphism of prestacks from its associated prestack to a
representable prestack is relatively representable. -/
theorem relativelyRepresentableWith_top_diag_of_target_overBased
    {X : 𝒮ᵒᵖ ⥤ Type v} {T : 𝒮} (M : ofPresheaf X ⥤ᵇ overBased T)
    (hdiag : yoneda.relativelyRepresentable (Limits.diag X)) :
    M.diag.RelativelyRepresentableWith (⊤ : MorphismProperty 𝒮) := by
  let ρ := overBasedToOfPresheafYoneda T
  have hψ := relativelyRepresentableWith_top_diag_ofPresheaf_map
    (ofPresheafMapOfBasedFunctor (M.comp ρ)) hdiag
  have hM' : (M.comp ρ).diag.RelativelyRepresentableWith
      (⊤ : MorphismProperty 𝒮) :=
    hψ.diag_of_iso (ofPresheafMapOfBasedFunctorIso (M.comp ρ))
  have hpost := hM'.of_iso (diagCompPostcompIso M ρ)
  exact hpost.of_comp_target_isEquivalence
    (isEquivalence_fiberProductPostcomp M M ρ)

end CategoryTheory.BasedFunctor
