module

public import StacksAndModuli.API.IsomPresheafStack
public import StacksAndModuli.«Section3.3-Presheaves-and-Sheaves».«part3.3.2-single-map-and-schemes-are-sheaves»

/-!
# Gluing stack morphisms over scheme coproducts

The morphism sheaf of an étale stack sends a coproduct of schemes to the product of
its component values.  Combining this with cartesian lifts glues componentwise arrows
to a single arrow over the morphism induced by the coproduct universal property.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Functor Limits Opposite

universe v₂ u₂ u

namespace CategoryTheory.BasedCategory

open AlgebraicGeometry

variable {X : BasedCategory.{v₂, u₂} Scheme.{u}}
  [IsStack Scheme.etaleTopology X]

/-- The morphism sheaf of a stack sends a scheme coproduct to the product of its
component values. -/
theorem bijective_sigma_isomPresheaf
    {ι : Type u} (U : ι → Scheme.{u})
    (a b : X.p.Fiber (∐ U)) :
    Function.Bijective fun
      (φ : (isomPresheaf a b).obj (op (Over.mk (𝟙 (∐ U))))) (j : ι) ↦
        (isomPresheaf a b).map
          (Over.homMk (Sigma.ι U j) : Over.mk (Sigma.ι U j) ⟶
            Over.mk (𝟙 (∐ U))).op φ := by
  let terminal : Over (∐ U) := Over.mk (𝟙 (∐ U))
  let V : ι → Over (∐ U) := fun j ↦ Over.mk (Sigma.ι U j)
  let inc : ∀ j, V j ⟶ terminal := fun j ↦ Over.homMk (Sigma.ι U j)
  have hcover : Presieve.IsSheafFor (isomPresheaf a b)
      (Presieve.ofArrows V inc) := by
    apply ((isSheaf_iff_isSheaf_of_type
      (Scheme.etaleTopology.over (∐ U)) (isomPresheaf a b)).mp
      (isomPresheaf_isSheaf a b)).isSheafFor (Presieve.ofArrows V inc)
    rw [GrothendieckTopology.mem_over_iff]
    change Sieve.overEquiv terminal (Sieve.ofArrows V inc) ∈
      Scheme.etaleTopology terminal.left
    rw [Sieve.overEquiv_ofArrows]
    apply Scheme.zariskiTopology_le_etaleTopology
    have h := (sigmaOpenCover U).mem_grothendieckTopology
    change Sieve.ofArrows U (Sigma.ι U) ∈
      Scheme.zariskiTopology (∐ U) at h
    simpa [V, inc, terminal] using h
  have hall : ∀ x : (j : ι) → (isomPresheaf a b).obj (op (V j)),
      Presieve.Arrows.Compatible (isomPresheaf a b) inc x := by
    intro x i j Z gi gj hcomm
    by_cases hij : i = j
    · subst j
      have : gi = gj := by
        apply (cancel_mono (inc i)).mp
        exact hcomm
      subst gj
      rfl
    · let _ : IsEmpty Z.left :=
        isEmpty_of_commSq_sigmaι_of_ne
          (g := U) (i := i) (j := j)
          (Z := Z.left) (a := gi.left) (b := gj.left)
          ⟨congrArg Over.Hom.left hcomm⟩ hij
      let ht := Presieve.isTerminal_of_isSheafFor_empty_presieve Z
        (isomPresheaf a b) (by
          rw [Presieve.ofArrows_of_isEmpty]
          apply ((isSheaf_iff_isSheaf_of_type
            (Scheme.etaleTopology.over (∐ U)) (isomPresheaf a b)).mp
            (isomPresheaf_isSheaf a b)).isSheafFor ⊥
          rw [GrothendieckTopology.mem_over_iff]
          apply Scheme.zariskiTopology_le_etaleTopology
          simpa using
            (Scheme.bot_mem_grothendieckTopology
              (P := @AlgebraicGeometry.IsOpenImmersion) Z.left))
      exact ConcreteCategory.congr_hom
        (ht.hom_ext
          (↾fun _ : PUnit ↦ (isomPresheaf a b).map gi.op (x i))
          (↾fun _ : PUnit ↦ (isomPresheaf a b).map gj.op (x j)))
        PUnit.unit
  have hglue := (Presieve.isSheafFor_arrows_iff
    (isomPresheaf a b) inc).mp hcover
  constructor
  · intro φ ψ hφψ
    obtain ⟨t, ht, huniq⟩ := hglue
      (fun j ↦ (isomPresheaf a b).map (inc j).op φ) (hall _)
    exact (huniq φ fun _ ↦ rfl).trans
      (huniq ψ fun j ↦ (congrFun hφψ j).symm).symm
  · intro x
    obtain ⟨t, ht, -⟩ := hglue x (hall x)
    exact ⟨t, funext ht⟩

/-- Componentwise arrows from a coproduct cocone to a fixed target glue to an
arrow over the map induced from the coproduct. -/
theorem exists_homLift_sigmaDesc
    {ι : Type u} (U : ι → Scheme.{u}) {T : Scheme.{u}}
    (f : ∀ j, U j ⟶ T)
    {a y : X.obj} {z : ι → X.obj}
    (ha : X.p.obj a = ∐ U) (hy : X.p.obj y = T)
    (η : ∀ j, z j ⟶ a) (θ : ∀ j, z j ⟶ y)
    [hη : ∀ j, IsHomLift X.p (Sigma.ι U j) (η j)]
    [hθ : ∀ j, IsHomLift X.p (f j) (θ j)] :
    ∃ q : a ⟶ y, IsHomLift X.p (Limits.Sigma.desc f) q := by
  classical
  let aFib : X.p.Fiber (∐ U) := Fiber.mk ha
  let yFib : X.p.Fiber T := Fiber.mk hy
  let p : (∐ U) ⟶ T := Limits.Sigma.desc f
  let bFib : X.p.Fiber (∐ U) :=
    Fiber.mk (IsPreFibered.pullbackObj_proj yFib.2 p)
  let β : bFib.1 ⟶ y := IsPreFibered.pullbackMap yFib.2 p
  haveI hβCart : IsCartesian X.p p β := by
    dsimp [β, bFib]
    exact IsPreFibered.pullbackMap.IsCartesian yFib.2 p
  haveI hβ : IsHomLift X.p p β := by
    exact IsCartesian.toIsHomLift
  let δ : ∀ j, z j ⟶ bFib.1 := fun j ↦
    IsStronglyCartesian.map X.p p β
      (show f j = Sigma.ι U j ≫ p by simp [p]) (θ j)
  haveI hδ : ∀ j, IsHomLift X.p (Sigma.ι U j) (δ j) := fun j ↦ by
    dsimp [δ]
    infer_instance
  let localMorph : ∀ j,
      (isomPresheaf aFib bFib).obj (op (Over.mk (Sigma.ι U j))) := fun j ↦ by
    let πa := IsPreFibered.pullbackMap aFib.2 (Sigma.ι U j)
    haveI hπaCart : IsCartesian X.p (Sigma.ι U j) πa := by
      dsimp [πa]
      exact IsPreFibered.pullbackMap.IsCartesian aFib.2 (Sigma.ι U j)
    haveI hπa : IsHomLift X.p (Sigma.ι U j) πa :=
      IsCartesian.toIsHomLift
    have hηStrong : IsStronglyCartesian X.p (Sigma.ι U j) (η j) :=
      inferInstance
    let toZ := @IsStronglyCartesian.map _ _ _ _ X.p _ _ _ _
      (Sigma.ι U j) (η j) hηStrong _ _ _ _
      (show Sigma.ι U j = (𝟙 (U j)) ≫ Sigma.ι U j by simp) πa hπa
    haveI htoZ : IsHomLift X.p (𝟙 (U j)) toZ := by
      dsimp [toZ]
      exact @IsStronglyCartesian.map_isHomLift _ _ _ _ X.p _ _ _ _
        (Sigma.ι U j) (η j) hηStrong _ _ _ _
        (show Sigma.ι U j = (𝟙 (U j)) ≫ Sigma.ι U j by simp) πa hπa
    let toB := toZ ≫ δ j
    haveI htoB : IsHomLift X.p (Sigma.ι U j) toB := by
      dsimp [toB]
      have h := @IsHomLift.comp _ _ _ _ X.p _ _ _ _ _ _
        (𝟙 (U j)) (Sigma.ι U j) toZ (δ j) htoZ (hδ j)
      simpa using h
    let πb := IsPreFibered.pullbackMap bFib.2 (Sigma.ι U j)
    haveI hπbCart : IsCartesian X.p (Sigma.ι U j) πb := by
      dsimp [πb]
      exact IsPreFibered.pullbackMap.IsCartesian bFib.2 (Sigma.ι U j)
    haveI hπb : IsHomLift X.p (Sigma.ι U j) πb :=
      IsCartesian.toIsHomLift
    have hπbStrong : IsStronglyCartesian X.p (Sigma.ι U j) πb :=
      inferInstance
    let ψ := @IsStronglyCartesian.map _ _ _ _ X.p _ _ _ _
      (Sigma.ι U j) πb hπbStrong _ _ _ _
      (show Sigma.ι U j = (𝟙 (U j)) ≫ Sigma.ι U j by simp) toB htoB
    haveI hψ : IsHomLift X.p (𝟙 (U j)) ψ := by
      dsimp [ψ]
      exact @IsStronglyCartesian.map_isHomLift _ _ _ _ X.p _ _ _ _
        (Sigma.ι U j) πb hπbStrong _ _ _ _
        (show Sigma.ι U j = (𝟙 (U j)) ≫ Sigma.ι U j by simp) toB htoB
    exact Fiber.homMk X.p (U j) ψ
  obtain ⟨Φ, -⟩ :=
    (bijective_sigma_isomPresheaf U aFib bFib).2 localMorph
  let πb := IsPreFibered.pullbackMap bFib.2 (𝟙 (∐ U))
  haveI hπbCart : IsCartesian X.p (𝟙 (∐ U)) πb := by
    dsimp [πb]
    exact IsPreFibered.pullbackMap.IsCartesian bFib.2 (𝟙 (∐ U))
  haveI hπb : IsHomLift X.p (𝟙 (∐ U)) πb := IsCartesian.toIsHomLift
  haveI hidA : IsHomLift X.p (𝟙 (∐ U)) (𝟙 a) := IsHomLift.id ha
  let πa := IsPreFibered.pullbackMap aFib.2 (𝟙 (∐ U))
  haveI hπaCart : IsCartesian X.p (𝟙 (∐ U)) πa := by
    dsimp [πa]
    exact IsPreFibered.pullbackMap.IsCartesian aFib.2 (𝟙 (∐ U))
  haveI hπa : IsHomLift X.p (𝟙 (∐ U)) πa := IsCartesian.toIsHomLift
  have hπaStrong : IsStronglyCartesian X.p (𝟙 (∐ U)) πa := inferInstance
  let toPullbackA := @IsStronglyCartesian.map _ _ _ _ X.p _ _ _ _
    (𝟙 (∐ U)) πa hπaStrong _ _ _ _
    (show (𝟙 (∐ U)) = (𝟙 (∐ U)) ≫ (𝟙 (∐ U)) by simp) (𝟙 a) hidA
  haveI htoPullbackA : IsHomLift X.p (𝟙 (∐ U)) toPullbackA := by
    dsimp [toPullbackA]
    exact @IsStronglyCartesian.map_isHomLift _ _ _ _ X.p _ _ _ _
      (𝟙 (∐ U)) πa hπaStrong _ _ _ _
      (show (𝟙 (∐ U)) = (𝟙 (∐ U)) ≫ (𝟙 (∐ U)) by simp) (𝟙 a) hidA
  haveI hΦLift : IsHomLift X.p (𝟙 (∐ U))
      (Fiber.fiberInclusion.map Φ) := Φ.2
  let φ : a ⟶ bFib.1 :=
    (toPullbackA ≫ Fiber.fiberInclusion.map Φ) ≫ πb
  haveI hφ : IsHomLift X.p (𝟙 (∐ U)) φ := by
    dsimp [φ]
    have h₁ : IsHomLift X.p (𝟙 (∐ U))
        (toPullbackA ≫ Fiber.fiberInclusion.map Φ) :=
      @IsHomLift.comp_of_lift_id _ _ _ _ X.p (∐ U) _ _ _
        toPullbackA (Fiber.fiberInclusion.map Φ) htoPullbackA hΦLift
    exact @IsHomLift.comp_of_lift_id _ _ _ _ X.p (∐ U) _ _ _
      (toPullbackA ≫ Fiber.fiberInclusion.map Φ) πb h₁ hπb
  refine ⟨φ ≫ β, ?_⟩
  have hq := IsHomLift.comp X.p (𝟙 (∐ U)) p φ β
  simpa [p] using hq

end CategoryTheory.BasedCategory
