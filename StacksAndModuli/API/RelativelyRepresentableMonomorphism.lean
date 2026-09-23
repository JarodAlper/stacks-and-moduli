module

public import StacksAndModuli.«Section4.1-Definitions».«part4.1.1-representable-morphisms-and-algebraic-spaces»

/-!
# Relatively representable monomorphisms are fully faithful

A relatively representable morphism between categories fibered in groupoids is faithful.
If every morphism representing one of its base changes is a monomorphism, the morphism is
also full. Thus relative representability by monomorphisms implies full faithfulness.

The proofs test morphisms against the two-Yoneda morphism defined by their codomain. A
representation of the resulting fiber product identifies its second projection, up to a
based natural isomorphism, with postcomposition by the representing morphism. Faithfulness
then follows from the faithful projection of an over-category, while fullness follows by
cancelling the representing monomorphism.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor

universe v v₂ u₂ v₃ u₃ u

namespace CategoryTheory.BasedFunctor

open CategoryTheory.BasedCategory

variable {𝒰 : Type u} [Category.{v} 𝒰]

/-- A relatively representable morphism between categories fibered in groupoids is
faithful. -/
theorem RelativelyRepresentable.toFunctor_faithful
    {𝒳 : BasedCategory.{v₂, u₂} 𝒰}
    {𝒴 : BasedCategory.{v₃, u₃} 𝒰}
    [𝒳.p.IsFiberedInGroupoids] [𝒴.p.IsFiberedInGroupoids]
    {F : BasedFunctor 𝒳 𝒴} (hF : F.RelativelyRepresentable) :
    F.toFunctor.Faithful := by
  constructor
  intro a b φ ψ hFmap
  have hbase : 𝒳.p.map φ = 𝒳.p.map ψ := by
    have hφ := Functor.congr_hom F.w φ
    have hψ := Functor.congr_hom F.w ψ
    simp only [Functor.comp_map] at hφ hψ
    have hm := congrArg 𝒴.p.map hFmap
    rw [hφ, hψ] at hm
    simpa only [cancel_epi, cancel_mono] using hm
  let S : 𝒰 := 𝒳.p.obj b
  let y : 𝒴.p.Fiber S := ⟨F.obj b, F.w_obj b⟩
  let g : BasedFunctor (overBased S) 𝒴 := twoYonedaPullback S y
  let t : Over S := Over.mk (𝟙 S)
  let π : g.obj t ⟶ F.obj b := IsPreFibered.pullbackMap y.2 (𝟙 S)
  let hπIso : IsIso π :=
    IsFiberedInGroupoids.isIso_of_isHomLift_isIso (p := 𝒴.p) (𝟙 S) π
  let e : F.obj b ≅ g.obj t := (asIso π).symm
  have he : IsHomLift 𝒴.p (𝟙 S) e.hom := by
    change IsHomLift 𝒴.p (𝟙 S) (inv π)
    infer_instance
  let B : FiberProductObj F g :=
    { fst := b
      snd := t
      over_eq := rfl
      iso := e
      isHomLift := he }
  let s : Over S := Over.mk (𝒳.p.map φ)
  let q : s ⟶ t := Over.homMk (𝒳.p.map φ)
  have hq : IsHomLift (overBased S).p (𝒳.p.map φ) q := by
    exact IsHomLift.of_fac' (overBased S).p (𝒳.p.map φ) q rfl rfl
      (by simp [q, s, t])
  have hcomp : IsHomLift 𝒴.p (𝒳.p.map φ) (F.map φ ≫ e.hom) := by
    exact IsHomLift.comp_lift_id_right' 𝒴.p (𝒳.p.map φ) (F.map φ) S e.hom
  let ea : F.obj a ≅ g.obj s :=
    IsCartesian.domainUniqueUpToIso 𝒴.p (𝒳.p.map φ) (g.map q)
      (F.map φ ≫ e.hom)
  have hea : IsHomLift 𝒴.p (𝟙 (𝒳.p.obj a)) ea.hom := by
    exact IsCartesian.domainUniqueUpToIso_inv_isHomLift 𝒴.p (𝒳.p.map φ)
      (g.map q) (F.map φ ≫ e.hom)
  let A : FiberProductObj F g :=
    { fst := a
      snd := s
      over_eq := rfl
      iso := ea
      isHomLift := hea }
  let mφ : A ⟶ B :=
    { fst := φ
      snd := q
      isHomLift := hq
      w := by
        change F.map φ ≫ e.hom = ea.hom ≫ g.map q
        exact (IsCartesian.fac 𝒴.p (𝒳.p.map φ) (g.map q)
          (F.map φ ≫ e.hom)).symm }
  let mψ : A ⟶ B :=
    { fst := ψ
      snd := q
      isHomLift := by rw [← hbase]; exact hq
      w := by
        change F.map ψ ≫ e.hom = ea.hom ≫ g.map q
        rw [← hFmap]
        exact (IsCartesian.fac 𝒴.p (𝒳.p.map φ) (g.map q)
          (F.map φ ≫ e.hom)).symm }
  obtain ⟨P, E, hE⟩ := hF S g
  let hE' : E.toFunctor.IsEquivalence := hE
  let _ : (fiberProduct F g).p.Faithful := by
    apply (fiberProduct F g).p.faithful_of_comp_essSurj E.toFunctor
    intro x z f f' hf
    obtain ⟨α, hα⟩ := E.toFunctor.map_surjective f
    obtain ⟨β, hβ⟩ := E.toFunctor.map_surjective f'
    rw [← hα, ← hβ]
    apply congrArg E.toFunctor.map
    apply (overBased P).p.map_injective
    have hwα := Functor.congr_hom E.w α
    have hwβ := Functor.congr_hom E.w β
    simp only [Functor.comp_map] at hwα hwβ
    rw [hα] at hwα
    rw [hβ] at hwβ
    rw [hwα, hwβ] at hf
    simpa only [cancel_epi, cancel_mono] using hf
  have hm : mφ = mψ := by
    apply (fiberProduct F g).p.map_injective
    exact hbase
  exact congrArg FiberProductHom.fst hm

/-- A morphism between categories fibered in groupoids that is relatively representable
by monomorphisms is full. -/
theorem RelativelyRepresentableWith.toFunctor_full_of_monomorphisms
    {𝒳 : BasedCategory.{v₂, u₂} 𝒰}
    {𝒴 : BasedCategory.{v₃, u₃} 𝒰}
    [𝒳.p.IsFiberedInGroupoids] [𝒴.p.IsFiberedInGroupoids]
    {F : BasedFunctor 𝒳 𝒴}
    (hF : F.RelativelyRepresentableWith (MorphismProperty.monomorphisms 𝒰)) :
    F.toFunctor.Full := by
  constructor
  intro a b θ
  let f : 𝒳.p.obj a ⟶ 𝒳.p.obj b :=
    eqToHom (F.w_obj a).symm ≫ 𝒴.p.map θ ≫ eqToHom (F.w_obj b)
  have hθ : IsHomLift 𝒴.p f θ :=
    IsHomLift.of_fac 𝒴.p f θ (F.w_obj a) (F.w_obj b) rfl
  let S : 𝒰 := 𝒳.p.obj b
  let y : 𝒴.p.Fiber S := ⟨F.obj b, F.w_obj b⟩
  let g : BasedFunctor (overBased S) 𝒴 := twoYonedaPullback S y
  let t : Over S := Over.mk (𝟙 S)
  let π : g.obj t ⟶ F.obj b := IsPreFibered.pullbackMap y.2 (𝟙 S)
  let hπIso : IsIso π :=
    IsFiberedInGroupoids.isIso_of_isHomLift_isIso (p := 𝒴.p) (𝟙 S) π
  let e : F.obj b ≅ g.obj t := (asIso π).symm
  have he : IsHomLift 𝒴.p (𝟙 S) e.hom := by
    change IsHomLift 𝒴.p (𝟙 S) (inv π)
    infer_instance
  let B : FiberProductObj F g :=
    { fst := b
      snd := t
      over_eq := rfl
      iso := e
      isHomLift := he }
  let s : Over S := Over.mk f
  let q : s ⟶ t := Over.homMk f
  have hq : IsHomLift (overBased S).p f q := by
    exact IsHomLift.of_fac' (overBased S).p f q rfl rfl
      (by simp [q, s, t])
  have hcomp : IsHomLift 𝒴.p f (θ ≫ e.hom) := by
    exact IsHomLift.comp_lift_id_right' 𝒴.p f θ S e.hom
  let ea : F.obj a ≅ g.obj s :=
    IsCartesian.domainUniqueUpToIso 𝒴.p f (g.map q) (θ ≫ e.hom)
  have hea : IsHomLift 𝒴.p (𝟙 (𝒳.p.obj a)) ea.hom := by
    exact IsCartesian.domainUniqueUpToIso_inv_isHomLift 𝒴.p f
      (g.map q) (θ ≫ e.hom)
  let A : FiberProductObj F g :=
    { fst := a
      snd := s
      over_eq := rfl
      iso := ea
      isHomLift := hea }
  obtain ⟨P, E, hE⟩ := hF.1 S g
  let _ : E.toFunctor.IsEquivalence := hE
  let H : BasedFunctor (overBased P) (overBased S) :=
    E.comp (BasedCategory.fiberProductSnd F g)
  let p : P ⟶ S := H.overHom
  let _ : Mono p := hF.2 S g P E hE
  let mapFull : (overBased.map p).toFunctor.Full := by
    constructor
    intro X Y k
    refine ⟨Over.homMk k.left ?_, ?_⟩
    · apply (cancel_mono p).mp
      rw [Category.assoc]
      exact k.w
    · exact Over.OverMorphism.ext rfl
  let _ : (overBased.map p).toFunctor.Full := mapFull
  obtain ⟨α⟩ := nonempty_iso_overBased_map H
  let β : (overBased.map p).toFunctor ≅ H.toFunctor :=
    (BasedNatTrans.forgetful (overBased P) (overBased S)).mapIso α.symm
  let hHfull : H.toFunctor.Full := Functor.Full.of_iso β
  let _ : H.toFunctor.Full := hHfull
  let hsndFull : (BasedCategory.fiberProductSnd F g).toFunctor.Full := by
    apply Functor.full_of_comp_essSurj
      (BasedCategory.fiberProductSnd F g).toFunctor E.toFunctor
    intro X Y k
    obtain ⟨m, hm⟩ := H.toFunctor.map_surjective k
    exact ⟨E.map m, hm⟩
  let _ : (BasedCategory.fiberProductSnd F g).toFunctor.Full := hsndFull
  obtain ⟨m, hm⟩ :=
    (BasedCategory.fiberProductSnd F g).toFunctor.map_surjective (X := A) (Y := B) q
  have hm' : m.snd = q := by
    simpa only [BasedCategory.fiberProductSnd_map] using hm
  refine ⟨m.fst, ?_⟩
  rw [← cancel_mono e.hom]
  calc
    F.map m.fst ≫ e.hom = ea.hom ≫ g.map m.snd := m.w
    _ = ea.hom ≫ g.map q := by rw [hm']
    _ = θ ≫ e.hom :=
      IsCartesian.fac 𝒴.p f (g.map q) (θ ≫ e.hom)

end CategoryTheory.BasedFunctor
