module

public import StacksAndModuli.«Section4.1-Definitions».«part4.1.2-deligne-mumford-and-algebraic-stacks»

/-!
# Faithfulness of the source of a representable morphism

A representable morphism of prestacks into a category fibered in sets has source fibered
in sets.  The proof tests representability on the scheme-valued point determined by the
common codomain of two arrows.  The resulting base change is an algebraic space, whose
projection is faithful, and detects equality of the two arrows.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor

universe v₂ u₂ v₃ u₃ u

namespace AlgebraicGeometry.BasedFunctor.Representable

open CategoryTheory.BasedCategory

/-- If a representable morphism of prestacks has target fibered in sets, then its source
is fibered in sets. -/
theorem source_projection_faithful
    {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}}
    {𝒴 : BasedCategory.{v₃, u₃} Scheme.{u}}
    [𝒳.p.IsFiberedInGroupoids] [𝒴.p.IsFiberedInGroupoids]
    {F : BasedFunctor 𝒳 𝒴} (hF : AlgebraicGeometry.BasedFunctor.Representable F)
    [𝒴.p.Faithful] : 𝒳.p.Faithful := by
  constructor
  intro a b φ ψ hbase
  have hFmap : F.map φ = F.map ψ := by
    apply 𝒴.p.map_injective
    have hφ := Functor.congr_hom F.w φ
    have hψ := Functor.congr_hom F.w ψ
    simp only [Functor.comp_map] at hφ hψ
    rw [hφ, hψ, hbase]
  let S : Scheme.{u} := 𝒳.p.obj b
  let y : 𝒴.p.Fiber S := ⟨F.obj b, F.w_obj b⟩
  let g : BasedFunctor (overBased S) 𝒴 := twoYonedaPullback S y
  let t : Over S := Over.mk (𝟙 S)
  let π : g.obj t ⟶ F.obj b := IsPreFibered.pullbackMap y.2 (𝟙 S)
  let hπ : IsHomLift 𝒴.p (𝟙 S) π := inferInstance
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
  have hFφ : IsHomLift 𝒴.p (𝒳.p.map φ) (F.map φ) :=
    BasedFunctor.preserves_isHomLift F (𝒳.p.map φ) φ
  have hcomp : IsHomLift 𝒴.p (𝒳.p.map φ) (F.map φ ≫ e.hom) := by
    exact IsHomLift.comp_lift_id_right' 𝒴.p (𝒳.p.map φ) (F.map φ) S e.hom
  have hqCart : IsCartesian 𝒴.p (𝒳.p.map φ) (g.map q) := inferInstance
  have hcompCart : IsCartesian 𝒴.p (𝒳.p.map φ) (F.map φ ≫ e.hom) := inferInstance
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
      isHomLift := by
        rw [← hbase]
        exact hq
      w := by
        change F.map ψ ≫ e.hom = ea.hom ≫ g.map q
        rw [← hFmap]
        exact (IsCartesian.fac 𝒴.p (𝒳.p.map φ) (g.map q)
          (F.map φ ≫ e.hom)).symm }
  obtain ⟨P, hP, E, hE⟩ := hF S g
  let hE' : E.toFunctor.IsEquivalence := hE
  let hPullbackFaithful : (fiberProduct F g).p.Faithful := by
    apply (fiberProduct F g).p.faithful_of_comp_essSurj E.toFunctor
    intro x z f f' hf
    obtain ⟨α, hα⟩ := E.toFunctor.map_surjective f
    obtain ⟨β, hβ⟩ := E.toFunctor.map_surjective f'
    rw [← hα, ← hβ]
    apply congrArg E.toFunctor.map
    apply (ofPresheaf P).p.map_injective
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

end AlgebraicGeometry.BasedFunctor.Representable
