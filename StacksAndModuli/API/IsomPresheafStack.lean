module

public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.6-isom-presheaves»
public import StacksAndModuli.«Section3.5-Stacks».«part3.5.1-the-definition»

/-!
# Isomorphism sheaves of stacks

Supporting API showing that the explicit presheaf of morphisms between two objects of a
stack is a sheaf on the corresponding over-site.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Opposite

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.BasedCategory

variable {SBase : Type u₁} [Category.{v₁} SBase]
  {J : GrothendieckTopology SBase}
  {𝒳 : BasedCategory.{v₂, u₂} SBase} [IsStack J 𝒳]
  {S : SBase}

/-- The explicit presheaf of morphisms between two objects of a stack fiber is a sheaf
on the corresponding over-site. -/
theorem isomPresheaf_isSheaf (a b : 𝒳.p.Fiber S) :
    Presheaf.IsSheaf (J.over S) (isomPresheaf a b) := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro f R hR x hx
  let Q : Sieve f.left := Sieve.overEquiv f R
  have hQ : Q ∈ J f.left := (GrothendieckTopology.mem_over_iff J R).mp hR
  let H : Q.arrows.category ⥤ Over S :=
    ObjectProperty.ι (fun T : Over f.left ↦ Q T.hom) ⋙ Over.map f.hom
  let qHom : ∀ q : Q.arrows.category, H.obj q ⟶ f :=
    fun q ↦ Over.homMk q.obj.hom
  let D : Q.arrows.category ⥤ 𝒳.obj := H ⋙ (twoYonedaPullback S a).toFunctor
  let η : ∀ q : Q.arrows.category, D.obj q ⟶
      Fiber.fiberInclusion.obj (pullbackFiberObj a f) :=
    fun q ↦ twoYonedaPullbackMap S a (qHom q)
  have hDmap : ∀ {q r : Q.arrows.category} (k : q ⟶ r),
      IsHomLift 𝒳.p k.hom.left (D.map k) := by
    intro q r k
    change IsHomLift 𝒳.p (H.map k).left
      ((twoYonedaPullback S a).map (H.map k))
    infer_instance
  have hηlift : ∀ q : Q.arrows.category,
      IsHomLift 𝒳.p q.obj.hom (η q) := by
    intro q
    simpa [η, qHom, H] using twoYonedaPullbackMap_isHomLift S a (qHom q)
  have hηnat : ∀ {q r : Q.arrows.category} (k : q ⟶ r),
      D.map k ≫ η r = η q := by
    intro q r k
    have hk : H.map k ≫ qHom r = qHom q := by
      ext
      simpa [H, qHom] using Over.w k.hom
    change (twoYonedaPullback S a).map (H.map k) ≫
      (twoYonedaPullback S a).map (qHom r) =
        (twoYonedaPullback S a).map (qHom q)
    rw [← (twoYonedaPullback S a).toFunctor.map_comp, hk]
  let rMem : ∀ q : Q.arrows.category, R (qHom q) := fun q ↦
    (Sieve.overEquiv_iff R q.obj.hom).mp q.property
  let localHom : ∀ q : Q.arrows.category,
      pullbackFiberObj a (H.obj q) ⟶ pullbackFiberObj b (H.obj q) :=
    fun q ↦ x (qHom q) (rMem q)
  let θ : ∀ q : Q.arrows.category, D.obj q ⟶
      Fiber.fiberInclusion.obj (pullbackFiberObj b f) :=
    fun q ↦ Fiber.fiberInclusion.map (localHom q) ≫
      twoYonedaPullbackMap S b (qHom q)
  have hθlift : ∀ q : Q.arrows.category,
      IsHomLift 𝒳.p q.obj.hom (θ q) := by
    intro q
    letI := (localHom q).2
    simpa [θ, qHom, H] using
      (inferInstance : IsHomLift 𝒳.p
        ((𝟙 (H.obj q).left) ≫ (qHom q).left)
        (Fiber.fiberInclusion.map (localHom q) ≫
          twoYonedaPullbackMap S b (qHom q)))
  have hlocal : ∀ {q r : Q.arrows.category} (k : q ⟶ r),
      isomRestriction a b (H.map k) (localHom r) = localHom q := by
    intro q r k
    have hk : H.map k ≫ qHom r = qHom q := by
      ext
      simpa [H, qHom] using Over.w k.hom
    have hxc := hx.to_sieveCompatible (qHom r) (H.map k) (rMem r)
    change x (H.map k ≫ qHom r) _ =
      isomRestriction a b (H.map k) (localHom r) at hxc
    have hsame := hx (𝟙 (H.obj q)) (𝟙 (H.obj q))
      (R.downward_closed (rMem r) (H.map k)) (rMem q) (by simpa using hk)
    calc
      isomRestriction a b (H.map k) (localHom r) =
          x (H.map k ≫ qHom r) _ := hxc.symm
      _ = x (qHom q) (rMem q) := by simpa using hsame
      _ = localHom q := rfl
  have hθnat : ∀ {q r : Q.arrows.category} (k : q ⟶ r),
      D.map k ≫ θ r = θ q := by
    intro q r k
    have hb : twoYonedaPullbackMap S b (H.map k) ≫
        twoYonedaPullbackMap S b (qHom r) =
          twoYonedaPullbackMap S b (qHom q) := by
      have hb' := (twoYonedaPullback S b).toFunctor.map_comp (H.map k) (qHom r)
      change twoYonedaPullbackMap S b (H.map k ≫ qHom r) =
        twoYonedaPullbackMap S b (H.map k) ≫
          twoYonedaPullbackMap S b (qHom r) at hb'
      have hk : H.map k ≫ qHom r = qHom q := by
        ext
        simpa [H, qHom] using Over.w k.hom
      rw [hk] at hb'
      exact hb'.symm
    change twoYonedaPullbackMap S a (H.map k) ≫
        (Fiber.fiberInclusion.map (localHom r) ≫
          twoYonedaPullbackMap S b (qHom r)) =
      Fiber.fiberInclusion.map (localHom q) ≫
        twoYonedaPullbackMap S b (qHom q)
    rw [← Category.assoc, ← isomRestriction_fac a b (H.map k) (localHom r),
      Category.assoc, hb, hlocal k]
  obtain ⟨Φ, hΦ, huniq⟩ :=
    Functor.IsStack.existsUnique_gluing_hom_of_cocone hQ D
      (pullbackFiberObj a f).2 (pullbackFiberObj b f).2
      η hηlift hDmap hηnat θ hθlift hθnat
  letI : IsHomLift 𝒳.p (𝟙 f.left) Φ := hΦ.1
  let φ : pullbackFiberObj a f ⟶ pullbackFiberObj b f := Fiber.homMk 𝒳.p f.left Φ
  refine ⟨φ, ?_, ?_⟩
  · intro T k hk
    let Uc : Over S := Over.mk (k.left ≫ f.hom)
    let kc : Uc ⟶ f := Over.homMk k.left
    let d : Uc ⟶ T := Over.homMk (𝟙 T.left) (by
      dsimp [Uc]
      simpa using (Over.w k).symm)
    have hdk : d ≫ k = kc := by
      ext
      change 𝟙 T.left ≫ k.left = k.left
      simp
    have hkc : R kc := by
      have h := R.downward_closed hk d
      rw [hdk] at h
      exact h
    let hkQ : Q k.left := (Sieve.overEquiv_iff R k.left).mpr hkc
    let q := Q.arrows.categoryMk k.left hkQ
    let e : T ⟶ H.obj q := Over.homMk (𝟙 T.left) (by
      dsimp [H, q]
      simpa using Over.w k)
    have he : e ≫ qHom q = k := by
      ext
      rw [Over.comp_left]
      change 𝟙 T.left ≫ q.obj.hom = k.left
      simp [q]
    letI hqLift : IsHomLift 𝒳.p k.left (twoYonedaPullbackMap S b (qHom q)) := by
      simpa [q, qHom, H] using twoYonedaPullbackMap_isHomLift S b (qHom q)
    letI : IsStronglyCartesian 𝒳.p k.left (twoYonedaPullbackMap S b (qHom q)) :=
      Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift 𝒳.p k.left _
    have hcan : (isomPresheaf a b).map (qHom q).op φ =
        x (qHom q) (rMem q) := by
      apply Fiber.hom_ext
      change Fiber.fiberInclusion.map (isomRestriction a b (qHom q) φ) =
        Fiber.fiberInclusion.map (x (qHom q) (rMem q))
      apply IsStronglyCartesian.ext 𝒳.p k.left
        (twoYonedaPullbackMap S b (qHom q)) (𝟙 T.left)
      rw [isomRestriction_fac]
      change twoYonedaPullbackMap S a (qHom q) ≫ Φ =
        Fiber.fiberInclusion.map (x (qHom q) (rMem q)) ≫
          twoYonedaPullbackMap S b (qHom q)
      exact (hΦ.2 hkQ).symm
    have hcomp : (isomPresheaf a b).map k.op φ =
        (isomPresheaf a b).map e.op ((isomPresheaf a b).map (qHom q).op φ) := by
      rw [← he]
      simp
    have hsc := hx.to_sieveCompatible (qHom q) e (rMem q)
    have hsame := hx (𝟙 T) (𝟙 T)
      (R.downward_closed (rMem q) e) hk (by simpa using he)
    have hmatch : (isomPresheaf a b).map e.op (x (qHom q) (rMem q)) =
        x k hk := by
      calc
        (isomPresheaf a b).map e.op (x (qHom q) (rMem q)) =
            x (e ≫ qHom q) _ := hsc.symm
        _ = x k hk := by simpa using hsame
    exact hcomp.trans ((congrArg ((isomPresheaf a b).map e.op) hcan).trans hmatch)
  · intro ψ hψ
    apply Fiber.hom_ext
    apply huniq (Fiber.fiberInclusion.map ψ)
    refine ⟨ψ.2, ?_⟩
    intro T k hkQ
    let q := Q.arrows.categoryMk k hkQ
    change Fiber.fiberInclusion.map (x (qHom q) (rMem q)) ≫
        twoYonedaPullbackMap S b (qHom q) =
      twoYonedaPullbackMap S a (qHom q) ≫ Fiber.fiberInclusion.map ψ
    rw [← isomRestriction_fac]
    have hres := hψ (qHom q) (rMem q)
    change isomRestriction a b (qHom q) ψ =
      x (qHom q) (rMem q) at hres
    exact congrArg (fun z ↦ Fiber.fiberInclusion.map z ≫
      twoYonedaPullbackMap S b (qHom q)) hres.symm

/-- The sheaf of morphisms between two objects of a stack fiber, bundled as a sheaf
on the corresponding over-site. -/
noncomputable def isomSheaf (a b : 𝒳.p.Fiber S) : Sheaf (J.over S) (Type v₂) where
  obj := isomPresheaf a b
  property := isomPresheaf_isSheaf a b

end CategoryTheory.BasedCategory
