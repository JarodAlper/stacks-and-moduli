module

public import StacksAndModuli.API.PrestackProducts

/-!
# The fiber product of a prestack with itself along the identity

For any morphism of prestacks, a fiber product taken along the identity of its target is
equivalent to its source, in both directions and over the base. Both orders of the two
fiber-product legs are covered.

This is the base case of relative representability: it is what makes the identity morphism
of a prestack representable, hence what exhibits a prestack as an open substack of itself.
It is not formal — Construction 3.4.33 builds the fiber product from explicit triples
`(x, y', γ : F(x) ≅ G(y'))`, so both the projection and its inverse have to be written out
and their `IsHomLift` obligations discharged by hand.

## Main definitions

* `CategoryTheory.BasedCategory.fiberProductIdInv`: the inverse `𝒴' ⥤ᵇ 𝒳 ×_𝒳 𝒴'` of the
  second projection, `y' ↦ (G(y'), y', refl)`.
* `CategoryTheory.BasedCategory.fiberProductFstIdInv`: the inverse with the identity as
  the second fiber-product leg.

## Main results

* `CategoryTheory.BasedCategory.isEquivalence_fiberProductSnd_id` and
  `…isEquivalence_fiberProductIdInv`: both are equivalences of categories.
* `CategoryTheory.BasedCategory.isEquivalence_fiberProductFst_id` and
  `…isEquivalence_fiberProductFstIdInv`: the corresponding equivalences with the
  identity as the second leg.
* `CategoryTheory.BasedCategory.FiberProductHom.fst_eq_of_id`: a morphism of `𝒳 ×_𝒳 𝒴'` is
  determined by its second component.
-/

@[expose] public section

namespace CategoryTheory.BasedCategory

open CategoryTheory _root_.CategoryTheory.Functor

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
  {𝒴' : BasedCategory.{v₃, u₃} 𝒮}


variable (G : 𝒴' ⥤ᵇ 𝒳)

/-- A morphism of `𝒳 ×_𝒳 𝒴'` is determined by its second component: the first is
recovered from it through the two comparison isomorphisms. -/
lemma FiberProductHom.fst_eq_of_id {a b : FiberProductObj (BasedFunctor.id 𝒳) G}
    (φ : FiberProductHom a b) :
    φ.fst = (a.iso.hom ≫ G.map φ.snd) ≫ b.iso.inv :=
  (Iso.eq_comp_inv b.iso).mpr φ.w

/-- The first component built from a morphism `g` of `𝒴'` lies over `𝒴'.p.map g`. -/
lemma isHomLift_fstOfSnd {a b : FiberProductObj (BasedFunctor.id 𝒳) G} (g : a.snd ⟶ b.snd) :
    𝒳.p.IsHomLift (𝒴'.p.map g) ((a.iso.hom ≫ G.map g) ≫ b.iso.inv) := by
  have h1 : 𝒳.p.IsHomLift (𝟙 (𝒳.p.obj a.fst)) a.iso.hom := a.isHomLift
  have h2 : 𝒳.p.IsHomLift (𝒴'.p.map g) (G.map g) :=
    BasedFunctor.preserves_isHomLift G (𝒴'.p.map g) g
  have h3 : 𝒳.p.IsHomLift (𝒴'.p.map g) (a.iso.hom ≫ G.map g) :=
    IsHomLift.comp_lift_id_left' 𝒳.p (𝒳.p.obj a.fst) a.iso.hom (𝒴'.p.map g) (G.map g)
  have h4 : 𝒳.p.IsHomLift (𝟙 (𝒳.p.obj b.fst)) b.iso.inv :=
    IsHomLift.lift_id_inv 𝒳.p (𝒳.p.obj b.fst) b.iso
  exact IsHomLift.comp_lift_id_right' 𝒳.p (𝒴'.p.map g) (a.iso.hom ≫ G.map g)
    (𝒳.p.obj b.fst) b.iso.inv

instance instFaithfulFiberProductSndId :
    (fiberProductSnd (BasedFunctor.id 𝒳) G).toFunctor.Faithful where
  map_injective {a b} φ ψ h := by
    have hsnd : φ.snd = ψ.snd := h
    apply FiberProductHom.ext
    · rw [FiberProductHom.fst_eq_of_id G φ, FiberProductHom.fst_eq_of_id G ψ, hsnd]
    · exact hsnd

instance instFullFiberProductSndId :
    (fiberProductSnd (BasedFunctor.id 𝒳) G).toFunctor.Full where
  map_surjective {a b} g :=
    ⟨⟨(a.iso.hom ≫ G.map g) ≫ b.iso.inv, g,
      isHomLift_map_of_common_lift (𝒴'.p.map g) _ g (isHomLift_fstOfSnd G g) inferInstance,
      (Iso.eq_comp_inv b.iso).mp rfl⟩, rfl⟩

instance instEssSurjFiberProductSndId :
    (fiberProductSnd (BasedFunctor.id 𝒳) G).toFunctor.EssSurj where
  mem_essImage b :=
    ⟨⟨G.obj b, b, (G.w_obj b).symm, Iso.refl _,
      inferInstanceAs (𝒳.p.IsHomLift (𝟙 (𝒳.p.obj (G.obj b))) (𝟙 (G.obj b)))⟩, ⟨Iso.refl b⟩⟩

/-- **The second projection of `𝒳 ×_𝒳 𝒴'` is an equivalence.** -/
lemma isEquivalence_fiberProductSnd_id :
    (fiberProductSnd (BasedFunctor.id 𝒳) G).toFunctor.IsEquivalence :=
  ⟨instFaithfulFiberProductSndId G, instFullFiberProductSndId G, instEssSurjFiberProductSndId G⟩



/-- The inverse of the second projection `𝒳 ×_𝒳 𝒴' → 𝒴'`. -/
def fiberProductIdInv : 𝒴' ⥤ᵇ fiberProduct (BasedFunctor.id 𝒳) G where
  toFunctor :=
    { obj := fun b =>
        { fst := G.obj b
          snd := b
          over_eq := (G.w_obj b).symm
          iso := Iso.refl _
          isHomLift := inferInstanceAs (𝒳.p.IsHomLift (𝟙 (𝒳.p.obj (G.obj b))) (𝟙 (G.obj b))) }
      map := fun {a b} f =>
        { fst := G.map f
          snd := f
          isHomLift := isHomLift_map_of_common_lift (𝒴'.p.map f) (G.map f) f
            (BasedFunctor.preserves_isHomLift G (𝒴'.p.map f) f) inferInstance
          w := by
            change G.map f ≫ 𝟙 (G.obj b) = 𝟙 (G.obj a) ≫ G.map f
            rw [Category.comp_id, Category.id_comp] }
      map_id := fun b => FiberProductHom.ext (by simp) (by simp)
      map_comp := fun f g => FiberProductHom.ext (by simp) (by simp) }
  w := G.w

instance instFaithfulFiberProductIdInv : (fiberProductIdInv G).toFunctor.Faithful where
  map_injective {_ _} _ _ h := congrArg FiberProductHom.snd h

instance instFullFiberProductIdInv : (fiberProductIdInv G).toFunctor.Full where
  map_surjective {a b} φ := by
    refine ⟨φ.snd, ?_⟩
    refine FiberProductHom.ext ?_ rfl
    change G.map φ.snd = φ.fst
    have hw : φ.fst ≫ 𝟙 (((fiberProductIdInv G).obj b).fst) =
        𝟙 (G.obj a) ≫ G.map φ.snd := φ.w
    have h1 : φ.fst = G.map φ.snd := by
      rw [← Category.comp_id φ.fst, ← Category.id_comp (G.map φ.snd)]
      exact hw
    exact h1.symm

instance instEssSurjFiberProductIdInv : (fiberProductIdInv G).toFunctor.EssSurj where
  mem_essImage a := by
    refine ⟨a.snd, ⟨?_⟩⟩
    refine
      { hom :=
          { fst := a.iso.inv
            snd := 𝟙 a.snd
            isHomLift := isHomLift_map_of_common_lift (𝟙 (𝒳.p.obj a.fst)) a.iso.inv (𝟙 a.snd)
              (IsHomLift.lift_id_inv 𝒳.p (𝒳.p.obj a.fst) a.iso) (IsHomLift.id a.over_eq)
            w := by
              change a.iso.inv ≫ a.iso.hom = 𝟙 (G.obj a.snd) ≫ G.map (𝟙 a.snd)
              simp }
        inv :=
          { fst := a.iso.hom
            snd := 𝟙 a.snd
            isHomLift := isHomLift_map_of_common_lift (𝟙 (𝒳.p.obj a.fst)) a.iso.hom (𝟙 a.snd)
              a.isHomLift (IsHomLift.id a.over_eq)
            w := by
              change a.iso.hom ≫ 𝟙 (G.obj a.snd) = a.iso.hom ≫ G.map (𝟙 a.snd)
              simp }
        hom_inv_id := ?_
        inv_hom_id := ?_ }
    · exact FiberProductHom.ext a.iso.inv_hom_id (Category.comp_id _)
    · exact FiberProductHom.ext a.iso.hom_inv_id (Category.comp_id _)

/-- The inverse of the second projection is an equivalence of categories. -/
lemma isEquivalence_fiberProductIdInv :
    (fiberProductIdInv G).toFunctor.IsEquivalence :=
  ⟨instFaithfulFiberProductIdInv G, instFullFiberProductIdInv G, instEssSurjFiberProductIdInv G⟩


section IdentitySecondLeg

variable {𝒳' : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
  (F : 𝒳' ⥤ᵇ 𝒴)

/-- The second component built from a morphism in the first factor of
`𝒳' ×_𝒴 𝒴` lies over the image of that morphism in the base. -/
lemma isHomLift_sndOfFst_id {a b : FiberProductObj F (BasedFunctor.id 𝒴)}
    (f : a.fst ⟶ b.fst) :
    𝒴.p.IsHomLift (𝒳'.p.map f) ((a.iso.inv ≫ F.map f) ≫ b.iso.hom) := by
  have h₁ : 𝒴.p.IsHomLift (𝒳'.p.map f) (F.map f) :=
    BasedFunctor.preserves_isHomLift F (𝒳'.p.map f) f
  have h₂ : 𝒴.p.IsHomLift (𝒳'.p.map f) (a.iso.inv ≫ F.map f) :=
    IsHomLift.comp_lift_id_left' 𝒴.p (𝒳'.p.obj a.fst) a.iso.inv
      (𝒳'.p.map f) (F.map f)
  exact IsHomLift.comp_lift_id_right' 𝒴.p (𝒳'.p.map f)
    (a.iso.inv ≫ F.map f) (𝒳'.p.obj b.fst) b.iso.hom

instance instFaithfulFiberProductFstId :
    (fiberProductFst F (BasedFunctor.id 𝒴)).toFunctor.Faithful where
  map_injective {a b} φ ψ h := by
    have hfst : φ.fst = ψ.fst := h
    apply FiberProductHom.ext
    · exact hfst
    · apply (cancel_epi a.iso.hom).mp
      have hφ : a.iso.hom ≫ φ.snd = F.map φ.fst ≫ b.iso.hom := by
        simpa only [BasedFunctor.id, Functor.id_obj, Functor.id_map] using φ.w.symm
      have hψ : a.iso.hom ≫ ψ.snd = F.map ψ.fst ≫ b.iso.hom := by
        simpa only [BasedFunctor.id, Functor.id_obj, Functor.id_map] using ψ.w.symm
      rw [hφ, hψ, hfst]

instance instFullFiberProductFstId :
    (fiberProductFst F (BasedFunctor.id 𝒴)).toFunctor.Full where
  map_surjective {a b} f :=
    ⟨⟨f, (a.iso.inv ≫ F.map f) ≫ b.iso.hom,
      isHomLift_map_of_common_lift (𝒳'.p.map f) f _ inferInstance
        (isHomLift_sndOfFst_id F f),
      by
        change F.map f ≫ b.iso.hom = a.iso.hom ≫ ((a.iso.inv ≫ F.map f) ≫ b.iso.hom)
        simp⟩, rfl⟩

instance instEssSurjFiberProductFstId :
    (fiberProductFst F (BasedFunctor.id 𝒴)).toFunctor.EssSurj where
  mem_essImage a :=
    ⟨⟨a, F.obj a, F.w_obj a, Iso.refl _,
      inferInstanceAs (𝒴.p.IsHomLift (CategoryStruct.id (𝒳'.p.obj a))
        (CategoryStruct.id (F.obj a)))⟩,
      ⟨Iso.refl a⟩⟩

/-- **The first projection of `𝒳' ×_𝒴 𝒴` is an equivalence.** -/
lemma isEquivalence_fiberProductFst_id :
    (fiberProductFst F (BasedFunctor.id 𝒴)).toFunctor.IsEquivalence :=
  ⟨instFaithfulFiberProductFstId F, instFullFiberProductFstId F,
    instEssSurjFiberProductFstId F⟩

/-- The canonical inverse of the first projection `𝒳' ×_𝒴 𝒴 → 𝒳'`. -/
def fiberProductFstIdInv : 𝒳' ⥤ᵇ fiberProduct F (BasedFunctor.id 𝒴) :=
  fiberProductLift (BasedFunctor.id 𝒳') F
    (eqToIso ((BasedFunctor.id_comp F).trans (BasedFunctor.comp_id F).symm))

@[simp]
lemma fiberProductFstIdInv_comp_fst :
    (fiberProductFstIdInv F).comp (fiberProductFst F (BasedFunctor.id 𝒴)) =
      BasedFunctor.id 𝒳' :=
  fiberProductLift_comp_fst _ _ _

@[simp]
lemma fiberProductFstIdInv_comp_snd :
    (fiberProductFstIdInv F).comp (fiberProductSnd F (BasedFunctor.id 𝒴)) = F :=
  fiberProductLift_comp_snd _ _ _

/-- The canonical inverse of the first projection is an equivalence of categories. -/
lemma isEquivalence_fiberProductFstIdInv :
    (fiberProductFstIdInv F).toFunctor.IsEquivalence :=
  letI : (fiberProductFst F (BasedFunctor.id 𝒴)).toFunctor.IsEquivalence :=
    isEquivalence_fiberProductFst_id F
  haveI : ((fiberProductFstIdInv F).comp
      (fiberProductFst F (BasedFunctor.id 𝒴))).toFunctor.IsEquivalence := by
    rw [fiberProductFstIdInv_comp_fst]
    exact Functor.isEquivalence_refl
  haveI : ((fiberProductFstIdInv F).toFunctor ⋙
      (fiberProductFst F (BasedFunctor.id 𝒴)).toFunctor).IsEquivalence := by
    change ((fiberProductFstIdInv F).comp
      (fiberProductFst F (BasedFunctor.id 𝒴))).toFunctor.IsEquivalence
    infer_instance
  Functor.isEquivalence_of_comp_right (fiberProductFstIdInv F).toFunctor
    (fiberProductFst F (BasedFunctor.id 𝒴)).toFunctor

end IdentitySecondLeg

end CategoryTheory.BasedCategory
