module

public import StacksAndModuli.API.PresheafPrestack
public import Mathlib.CategoryTheory.ConnectedComponents

/-!
# Connected-component presentations of prestacks

Supporting API for reindexing fiber categories, assembling their connected components
into a presheaf, and presenting a category fibered in groupoids with faithful
projection as the category of elements of that presheaf.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Opposite

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.BasedCategory

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]
  {𝒳 : BasedCategory.{v₂, u₂} 𝒮} [𝒳.p.IsFiberedInGroupoids]
  {S : 𝒮}

/-- The chosen cartesian pullback of an object `a ∈ 𝒳(S)` along an arrow
`f : T → S`, regarded as an object of the fiber category `𝒳(T)`. -/
noncomputable def pullbackFiberObj (a : 𝒳.p.Fiber S) (f : Over S) :
    𝒳.p.Fiber f.left :=
  Fiber.mk (IsPreFibered.pullbackObj_proj a.2 f.hom)

@[simp]
lemma pullbackFiberObj_val (a : 𝒳.p.Fiber S) (f : Over S) :
    Fiber.fiberInclusion.obj (pullbackFiberObj a f) =
      IsPreFibered.pullbackObj a.2 f.hom :=
  rfl

/-- Reindex a vertical morphism between two objects of a fiber along a base
arrow, using the chosen strongly-cartesian pullbacks. -/
noncomputable def fiberPullbackMap {R S : 𝒮} (f : R ⟶ S)
    {a b : 𝒳.p.Fiber S} (φ : a ⟶ b) :
    pullbackFiberObj a (Over.mk f) ⟶ pullbackFiberObj b (Over.mk f) := by
  let u := IsStronglyCartesian.map 𝒳.p f
    (IsPreFibered.pullbackMap b.2 f) (Category.id_comp f).symm
    (IsPreFibered.pullbackMap a.2 f ≫ Fiber.fiberInclusion.map φ)
  have hu : IsHomLift 𝒳.p (𝟙 R) u :=
    IsStronglyCartesian.map_isHomLift 𝒳.p f
      (IsPreFibered.pullbackMap b.2 f) (Category.id_comp f).symm
      (IsPreFibered.pullbackMap a.2 f ≫ Fiber.fiberInclusion.map φ)
  exact Fiber.homMk 𝒳.p R u

@[reassoc]
lemma fiberPullbackMap_fac {R S : 𝒮} (f : R ⟶ S)
    {a b : 𝒳.p.Fiber S} (φ : a ⟶ b) :
    Fiber.fiberInclusion.map (fiberPullbackMap f φ) ≫
        IsPreFibered.pullbackMap b.2 f =
      IsPreFibered.pullbackMap a.2 f ≫ Fiber.fiberInclusion.map φ := by
  change IsStronglyCartesian.map 𝒳.p f
      (IsPreFibered.pullbackMap b.2 f) (Category.id_comp f).symm
      (IsPreFibered.pullbackMap a.2 f ≫ Fiber.fiberInclusion.map φ) ≫
        IsPreFibered.pullbackMap b.2 f = _
  exact IsStronglyCartesian.fac 𝒳.p f
    (IsPreFibered.pullbackMap b.2 f) (Category.id_comp f).symm
    (IsPreFibered.pullbackMap a.2 f ≫ Fiber.fiberInclusion.map φ)

/-- The reindexing functor between fiber categories induced by a base arrow. -/
noncomputable def fiberPullbackFunctor {R S : 𝒮} (f : R ⟶ S) :
    𝒳.p.Fiber S ⥤ 𝒳.p.Fiber R where
  obj a := pullbackFiberObj a (Over.mk f)
  map φ := fiberPullbackMap f φ
  map_id a := by
    apply Fiber.hom_ext
    apply IsStronglyCartesian.ext 𝒳.p f
      (IsPreFibered.pullbackMap a.2 f) (𝟙 R)
    rw [fiberPullbackMap_fac]
    change IsPreFibered.pullbackMap a.2 f ≫ 𝟙 a.1 =
      𝟙 _ ≫ IsPreFibered.pullbackMap a.2 f
    simp
  map_comp φ ψ := by
    apply Fiber.hom_ext
    apply IsStronglyCartesian.ext 𝒳.p f
      (IsPreFibered.pullbackMap _ f) (𝟙 R)
    rw [Functor.map_comp, fiberPullbackMap_fac, Category.assoc,
      fiberPullbackMap_fac, ← Category.assoc, fiberPullbackMap_fac,
      Functor.map_comp]
    exact (Category.assoc _ _ _).symm

/-- The presheaf sending a base object to the connected components of the
corresponding fiber category. -/
noncomputable def fiberComponents : 𝒮ᵒᵖ ⥤ Type u₂ where
  obj S := ConnectedComponents (𝒳.p.Fiber S.unop)
  map {R S} f := ↾fun j ↦
    (fiberPullbackFunctor (𝒳 := 𝒳) f.unop).mapConnectedComponents j
  map_id S := by
    ext j
    induction j using Quotient.inductionOn' with
    | _ a =>
      apply Quotient.sound'
      let φ : (fiberPullbackFunctor (𝒳 := 𝒳) (𝟙 S.unop)).obj a ⟶ a :=
        ⟨IsPreFibered.pullbackMap a.2 (𝟙 S.unop), inferInstance⟩
      exact Zigzag.of_hom φ
  map_comp {R S T} f g := by
    ext j
    induction j using Quotient.inductionOn' with
    | _ a =>
      apply Quotient.sound'
      let e := IsFibered.pullbackPullbackIso a.2 f.unop g.unop
      have he : IsHomLift 𝒳.p (𝟙 T.unop) e.hom := by
        dsimp [e, IsFibered.pullbackPullbackIso]
        infer_instance
      let φ : (fiberPullbackFunctor (𝒳 := 𝒳) (g.unop ≫ f.unop)).obj a ⟶
          (fiberPullbackFunctor (𝒳 := 𝒳) g.unop).obj
            ((fiberPullbackFunctor (𝒳 := 𝒳) f.unop).obj a) := ⟨e.hom, he⟩
      exact Zigzag.of_hom φ

lemma nonempty_hom_of_zigzag {J : Type u₂} [Category.{v₂} J]
    [IsGroupoid J] {a b : J} (h : Zigzag a b) : Nonempty (a ⟶ b) := by
  induction h with
  | refl => exact ⟨𝟙 _⟩
  | tail h hz ih =>
    obtain ⟨φ⟩ := ih
    rcases hz with ⟨⟨ψ⟩⟩ | ⟨⟨ψ⟩⟩
    · exact ⟨φ ≫ ψ⟩
    · exact ⟨φ ≫ inv ψ⟩

noncomputable def componentRepresentative {S : 𝒮}
    (j : ConnectedComponents (𝒳.p.Fiber S)) : 𝒳.p.Fiber S :=
  (default : j.Component).obj

lemma componentRepresentative_component {S : 𝒮}
    (j : ConnectedComponents (𝒳.p.Fiber S)) :
    ConnectedComponents.mk (componentRepresentative (𝒳 := 𝒳) j) = j :=
  (default : j.Component).property

noncomputable def fiberHomOfComponentsEq {S : 𝒮} {a b : 𝒳.p.Fiber S}
    (h : ConnectedComponents.mk a = ConnectedComponents.mk b) : a ⟶ b :=
  Classical.choice (nonempty_hom_of_zigzag (Quotient.exact' h))

lemma hom_ext_of_faithful_of_isHomLift (p : 𝒳.obj ⥤ 𝒮) [p.Faithful]
    {R S : 𝒮} (f : R ⟶ S) {a b : 𝒳.obj} (φ ψ : a ⟶ b)
    [IsHomLift p f φ] [IsHomLift p f ψ] : φ = ψ := by
  apply p.map_injective
  rw [IsHomLift.fac' p f φ, IsHomLift.fac' p f ψ]

/-- The category-of-elements prestack of the connected-component presheaf. -/
noncomputable abbrev componentPrestack : BasedCategory.{v₁, max u₁ u₂} 𝒮 :=
  elementsPrestack (fiberComponents (𝒳 := 𝒳))

noncomputable abbrev componentPrestackBase
    (x : (componentPrestack (𝒳 := 𝒳)).obj) : 𝒮 :=
  x.unop.1.unop

noncomputable abbrev componentPrestackComponent
    (x : (componentPrestack (𝒳 := 𝒳)).obj) :
    ConnectedComponents (𝒳.p.Fiber (componentPrestackBase x)) :=
  x.unop.2

noncomputable abbrev componentPrestackFiberObj
    (x : (componentPrestack (𝒳 := 𝒳)).obj) :
    𝒳.p.Fiber (componentPrestackBase x) :=
  componentRepresentative (componentPrestackComponent x)

noncomputable abbrev componentPrestackObj
    (x : (componentPrestack (𝒳 := 𝒳)).obj) : 𝒳.obj :=
  (componentPrestackFiberObj x).1

lemma componentPrestackMap_components
    {x y : (componentPrestack (𝒳 := 𝒳)).obj} (q : x ⟶ y) :
    ConnectedComponents.mk (componentPrestackFiberObj x) =
      ConnectedComponents.mk
        ((fiberPullbackFunctor (𝒳 := 𝒳) q.unop.val.unop).obj
          (componentPrestackFiberObj y)) := by
  have h := CategoryOfElements.map_snd q.unop
  change (fiberComponents (𝒳 := 𝒳)).map q.unop.val
      (componentPrestackComponent y) = componentPrestackComponent x at h
  calc
    ConnectedComponents.mk (componentPrestackFiberObj x) =
        componentPrestackComponent x :=
      componentRepresentative_component (componentPrestackComponent x)
    _ = (fiberComponents (𝒳 := 𝒳)).map q.unop.val
        (componentPrestackComponent y) := h.symm
    _ = (fiberComponents (𝒳 := 𝒳)).map q.unop.val
        (ConnectedComponents.mk (componentPrestackFiberObj y)) := by
      rw [componentRepresentative_component (componentPrestackComponent y)]
    _ = ConnectedComponents.mk
        ((fiberPullbackFunctor (𝒳 := 𝒳) q.unop.val.unop).obj
          (componentPrestackFiberObj y)) := rfl

noncomputable def componentPrestackMap
    {x y : (componentPrestack (𝒳 := 𝒳)).obj} (q : x ⟶ y) :
    componentPrestackObj x ⟶ componentPrestackObj y :=
  Fiber.fiberInclusion.map
      (fiberHomOfComponentsEq (componentPrestackMap_components q)) ≫
    IsPreFibered.pullbackMap (componentPrestackFiberObj y).2 q.unop.val.unop

instance componentPrestackMap_isHomLift
    {x y : (componentPrestack (𝒳 := 𝒳)).obj} (q : x ⟶ y) :
    IsHomLift 𝒳.p q.unop.val.unop (componentPrestackMap q) := by
  dsimp only [componentPrestackMap]
  infer_instance

/-- For a category fibered in groupoids with faithful projection, choose one
representative in every connected component of every fiber to obtain a based
functor from the component prestack to the original based category. -/
noncomputable def componentPrestackComparison [𝒳.p.Faithful] :
    componentPrestack (𝒳 := 𝒳) ⥤ᵇ 𝒳 where
  obj x := componentPrestackObj x
  map q := componentPrestackMap q
  map_id x := by
    letI hmap : IsHomLift 𝒳.p (𝟙 (componentPrestackBase x))
        (componentPrestackMap (𝟙 x)) := by
      simpa using componentPrestackMap_isHomLift (𝒳 := 𝒳) (𝟙 x)
    letI hid : IsHomLift 𝒳.p (𝟙 (componentPrestackBase x))
        (𝟙 (componentPrestackObj x)) :=
      IsHomLift.id (componentPrestackFiberObj x).2
    exact hom_ext_of_faithful_of_isHomLift 𝒳.p
      (𝟙 (componentPrestackBase x)) _ _
  map_comp {x y z} q r := by
    let f := q.unop.val.unop
    let g := r.unop.val.unop
    letI hcomp : IsHomLift 𝒳.p (f ≫ g) (componentPrestackMap (q ≫ r)) := by
      simpa [f, g] using componentPrestackMap_isHomLift (𝒳 := 𝒳) (q ≫ r)
    letI hq : IsHomLift 𝒳.p f (componentPrestackMap q) :=
      componentPrestackMap_isHomLift q
    letI hr : IsHomLift 𝒳.p g (componentPrestackMap r) :=
      componentPrestackMap_isHomLift r
    letI hqr : IsHomLift 𝒳.p (f ≫ g)
        (componentPrestackMap q ≫ componentPrestackMap r) :=
      IsHomLift.comp 𝒳.p f g _ _
    exact hom_ext_of_faithful_of_isHomLift 𝒳.p (f ≫ g) _ _
  w := by
    refine Functor.ext_of_iso
      (NatIso.ofComponents
        (fun x ↦ eqToIso (componentPrestackFiberObj x).2) ?_)
      (fun x ↦ (componentPrestackFiberObj x).2)
    intro x y q
    have h := IsHomLift.fac' 𝒳.p q.unop.val.unop (componentPrestackMap q)
    simp only [Functor.comp_map, h]
    simp

lemma componentPrestackComparison_faithful [𝒳.p.Faithful] :
    (componentPrestackComparison (𝒳 := 𝒳)).toFunctor.Faithful := by
  haveI : (componentPrestack (𝒳 := 𝒳)).p.Faithful := inferInstance
  exact (componentPrestackComparison (𝒳 := 𝒳)).w.faithful_of_comp

noncomputable def componentPrestackPreimageMap [𝒳.p.Faithful]
    {x y : (componentPrestack (𝒳 := 𝒳)).obj}
    (φ : (componentPrestackComparison (𝒳 := 𝒳)).obj x ⟶
      (componentPrestackComparison (𝒳 := 𝒳)).obj y) : x ⟶ y := by
  let f : componentPrestackBase x ⟶ componentPrestackBase y :=
    eqToHom (componentPrestackFiberObj x).2.symm ≫ 𝒳.p.map φ ≫
      eqToHom (componentPrestackFiberObj y).2
  have hφ : IsHomLift 𝒳.p f φ := by
    apply IsHomLift.of_fac 𝒳.p f φ
      (componentPrestackFiberObj x).2 (componentPrestackFiberObj y).2
    rfl
  let ψ : componentPrestackFiberObj x ⟶
      (fiberPullbackFunctor (𝒳 := 𝒳) f).obj (componentPrestackFiberObj y) := by
    let u := IsStronglyCartesian.map 𝒳.p f
      (IsPreFibered.pullbackMap (componentPrestackFiberObj y).2 f)
      (Category.id_comp f).symm φ
    have hu : IsHomLift 𝒳.p (𝟙 (componentPrestackBase x)) u :=
      IsStronglyCartesian.map_isHomLift 𝒳.p f
        (IsPreFibered.pullbackMap (componentPrestackFiberObj y).2 f)
        (Category.id_comp f).symm φ
    exact ⟨u, hu⟩
  have hcomponents : (fiberComponents (𝒳 := 𝒳)).map f.op
      (componentPrestackComponent y) = componentPrestackComponent x := by
    calc
      (fiberComponents (𝒳 := 𝒳)).map f.op
          (componentPrestackComponent y) =
        (fiberComponents (𝒳 := 𝒳)).map f.op
          (ConnectedComponents.mk (componentPrestackFiberObj y)) := by
            rw [componentRepresentative_component (componentPrestackComponent y)]
      _ = ConnectedComponents.mk
          ((fiberPullbackFunctor (𝒳 := 𝒳) f).obj
            (componentPrestackFiberObj y)) := rfl
      _ = ConnectedComponents.mk (componentPrestackFiberObj x) :=
        Quotient.sound' (Zigzag.of_inv ψ)
      _ = componentPrestackComponent x :=
        componentRepresentative_component (componentPrestackComponent x)
  exact (CategoryOfElements.homMk _ _ f.op hcomponents).op

lemma componentPrestackPreimageMap_image [𝒳.p.Faithful]
    {x y : (componentPrestack (𝒳 := 𝒳)).obj}
    (φ : (componentPrestackComparison (𝒳 := 𝒳)).obj x ⟶
      (componentPrestackComparison (𝒳 := 𝒳)).obj y) :
    (componentPrestackComparison (𝒳 := 𝒳)).map
      (componentPrestackPreimageMap φ) = φ := by
  change componentPrestackMap (componentPrestackPreimageMap φ) = φ
  let f : componentPrestackBase x ⟶ componentPrestackBase y :=
    eqToHom (componentPrestackFiberObj x).2.symm ≫ 𝒳.p.map φ ≫
      eqToHom (componentPrestackFiberObj y).2
  letI hφ : IsHomLift 𝒳.p f φ := by
    apply IsHomLift.of_fac 𝒳.p f φ
      (componentPrestackFiberObj x).2 (componentPrestackFiberObj y).2
    rfl
  letI hmap : IsHomLift 𝒳.p f
      (componentPrestackMap (componentPrestackPreimageMap φ)) := by
    simpa [componentPrestackPreimageMap, f] using
      componentPrestackMap_isHomLift (𝒳 := 𝒳)
        (componentPrestackPreimageMap φ)
  exact hom_ext_of_faithful_of_isHomLift 𝒳.p f _ _

lemma componentPrestackComparison_full [𝒳.p.Faithful] :
    (componentPrestackComparison (𝒳 := 𝒳)).toFunctor.Full := by
  constructor
  intro x y φ
  exact ⟨componentPrestackPreimageMap φ,
    componentPrestackPreimageMap_image φ⟩

lemma componentPrestackComparison_essSurj [𝒳.p.Faithful] :
    (componentPrestackComparison (𝒳 := 𝒳)).toFunctor.EssSurj := by
  constructor
  intro a
  let aFiber : 𝒳.p.Fiber (𝒳.p.obj a) := Fiber.mk rfl
  let j : ConnectedComponents (𝒳.p.Fiber (𝒳.p.obj a)) :=
    ConnectedComponents.mk aFiber
  let x : (componentPrestack (𝒳 := 𝒳)).obj := op ⟨op (𝒳.p.obj a), j⟩
  have hcomp : ConnectedComponents.mk (componentPrestackFiberObj x) =
      ConnectedComponents.mk aFiber := by
    exact componentRepresentative_component j
  let e : componentPrestackFiberObj x ≅ aFiber :=
    asIso (fiberHomOfComponentsEq hcomp)
  exact ⟨x, ⟨Fiber.fiberInclusion.mapIso e⟩⟩

/-- A category fibered in groupoids with faithful projection is equivalent to
the category of elements of its presheaf of fiberwise connected components. -/
theorem isEquivalence_componentPrestackComparison [𝒳.p.Faithful] :
    (componentPrestackComparison (𝒳 := 𝒳)).toFunctor.IsEquivalence := by
  letI := componentPrestackComparison_faithful (𝒳 := 𝒳)
  letI := componentPrestackComparison_full (𝒳 := 𝒳)
  letI := componentPrestackComparison_essSurj (𝒳 := 𝒳)
  exact { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }

/-- A based category equivalent to a category-of-elements prestack has faithful
projection to the base. -/
lemma projection_faithful_of_equivalence_from_elements
    {F : 𝒮ᵒᵖ ⥤ Type u₂} (E : elementsPrestack F ⥤ᵇ 𝒳)
    [E.toFunctor.IsEquivalence] : 𝒳.p.Faithful := by
  haveI : (elementsPrestack F).p.Faithful := inferInstance
  apply 𝒳.p.faithful_of_comp_essSurj E.toFunctor
  intro x y φ ψ h
  obtain ⟨φ', hφ⟩ := E.toFunctor.map_surjective φ
  obtain ⟨ψ', hψ⟩ := E.toFunctor.map_surjective ψ
  rw [← hφ, ← hψ]
  apply congrArg E.toFunctor.map
  apply (elementsPrestack F).p.map_injective
  have hwφ := Functor.congr_hom E.w φ'
  have hwψ := Functor.congr_hom E.w ψ'
  simp only [Functor.comp_map] at hwφ hwψ
  rw [hφ] at hwφ
  rw [hψ] at hwψ
  rw [hwφ, hwψ] at h
  simpa only [cancel_epi, cancel_mono] using h

omit [𝒳.p.IsFiberedInGroupoids] in
/-- A based category equivalent to the costructured-arrow prestack of a presheaf
has faithful projection to the base. -/
lemma projection_faithful_of_equivalence_from_ofPresheaf
    {F : 𝒮ᵒᵖ ⥤ Type v₁} (E : ofPresheaf F ⥤ᵇ 𝒳)
    [E.toFunctor.IsEquivalence] : 𝒳.p.Faithful := by
  let _ : (ofPresheaf F).p.Faithful := inferInstance
  apply 𝒳.p.faithful_of_comp_essSurj E.toFunctor
  intro x y phi psi h
  obtain ⟨phi', hphi⟩ := E.toFunctor.map_surjective phi
  obtain ⟨psi', hpsi⟩ := E.toFunctor.map_surjective psi
  rw [← hphi, ← hpsi]
  apply congrArg E.toFunctor.map
  apply (ofPresheaf F).p.map_injective
  have hwphi := Functor.congr_hom E.w phi'
  have hwpsi := Functor.congr_hom E.w psi'
  simp only [Functor.comp_map] at hwphi hwpsi
  rw [hphi] at hwphi
  rw [hpsi] at hwpsi
  rw [hwphi, hwpsi] at h
  simpa only [cancel_epi, cancel_mono] using h

/-- A category fibered in groupoids is equivalent over its base to the category of
elements of a set-valued presheaf exactly when its projection is faithful. -/
theorem isEquivalentToPresheaf_iff_projection_faithful :
    IsEquivalentToPresheaf (𝒳 := 𝒳) ↔ 𝒳.p.Faithful := by
  constructor
  · rintro ⟨F, E, hE⟩
    letI := hE
    exact projection_faithful_of_equivalence_from_elements E
  · intro hp
    letI := hp
    exact ⟨fiberComponents (𝒳 := 𝒳),
      componentPrestackComparison (𝒳 := 𝒳),
      isEquivalence_componentPrestackComparison (𝒳 := 𝒳)⟩


end CategoryTheory.BasedCategory
