module

public import StacksAndModuli.API.PseudofunctorPrecompositionDescent

/-!
# Equivalence of descent data after pullback-preserving precomposition

For a functor preserving the chosen pairwise and triple pullbacks of a family,
this file constructs the inverse to the functor that maps descent data for a
precomposed pseudofunctor to descent data over the mapped family.  Consequently,
the two chosen-pullback descent categories are equivalent.

Main declaration:
- `CategoryTheory.Pseudofunctor.descentDataPrecompEquivalence`.
-/

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

universe t vC uC vD uD vE uE

namespace CategoryTheory.Pseudofunctor

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable (H : C ⥤ D)
variable (G : Pseudofunctor (LocallyDiscrete Dᵒᵖ) Cat.{vE, uE})
variable {I : Type t} {S : C} {X : I → C} {f : ∀ i, X i ⟶ S}
variable (sq : ∀ i j, ChosenPullback (f i) (f j))
variable (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))
variable (hsq : ∀ i j, IsPullback (H.map (sq i j).p₁) (H.map (sq i j).p₂)
  (H.map (f i)) (H.map (f j)))
variable (hwide : ∀ i j k, IsPullback (H.map (sq₃ i j k).p₁₂)
  (H.map (sq₃ i j k).p₂₃) (H.map (sq i j).p₂) (H.map (sq j k).p₁))

/-- Recover descent data for a precomposed pseudofunctor from descent data over
the image of the chosen pullback diagrams. -/
noncomputable def DescentData'.unmapPrecomp
    (A : G.DescentData' (mappedChosenPullback H sq hsq)
      (mappedChosenPullback₃ H sq sq₃ hsq hwide)) :
    (Pseudofunctor.comp H.op.toPseudofunctor G).DescentData' sq sq₃ := by
  let homD : ∀ i j,
      ((Pseudofunctor.comp H.op.toPseudofunctor G).map
        (sq i j).p₁.op.toLoc).toFunctor.obj (A.obj i) ⟶
      ((Pseudofunctor.comp H.op.toPseudofunctor G).map
        (sq i j).p₂.op.toLoc).toFunctor.obj (A.obj j) :=
    fun i j ↦ A.hom i j
  refine ⟨A.obj, homD, ?_, ?_⟩
  · intro i
    let p := (sq i i).isPullback.lift (𝟙 (X i)) (𝟙 (X i)) (by simp)
    have hp₁ : p ≫ (sq i i).p₁ = 𝟙 (X i) := by
      dsimp [p]
      simp
    have hp₂ : p ≫ (sq i i).p₂ = 𝟙 (X i) := by
      dsimp [p]
      simp
    have hp₁' : H.map p ≫ H.map (sq i i).p₁ = 𝟙 (H.obj (X i)) := by
      rw [← H.map_comp, hp₁, H.map_id]
    have hp₂' : H.map p ≫ H.map (sq i i).p₂ = 𝟙 (H.obj (X i)) := by
      rw [← H.map_comp, hp₂, H.map_id]
    have hT := DescentData'.pullHom'_eq_pullHom
      (F := G) (f := fun a ↦ H.map (f a))
      (sq := mappedChosenPullback H sq hsq) (hom := A.hom)
      (q := H.map (f i)) (i₁ := i) (i₂ := i)
      (f₁ := 𝟙 (H.obj (X i))) (f₂ := 𝟙 (H.obj (X i))) (p := H.map p)
      (hf₁ := by simp) (hf₂ := by simp) (hp₁ := hp₁') (hp₂ := hp₂')
    have hTarget := A.pullHom'_hom_self i
    have hS := DescentData'.pullHom'_eq_pullHom
      (F := Pseudofunctor.comp H.op.toPseudofunctor G) (f := f) (sq := sq)
      (hom := homD) (q := f i) (i₁ := i) (i₂ := i)
      (f₁ := 𝟙 (X i)) (f₂ := 𝟙 (X i)) (p := p)
      (hf₁ := by simp) (hf₂ := by simp) (hp₁ := hp₁) (hp₂ := hp₂)
    have h₀ := pullHom_heq_of_eq G (H.map (sq i i).p₁) (H.map (sq i i).p₂)
      (A.obj i) (A.obj i) (A.hom i i) (H.map p)
      (H.map_id (X i)) (H.map_id (X i))
      (by rw [← H.map_comp, hp₁]) (by rw [← H.map_comp, hp₂]) hp₁' hp₂'
    have hc := comp_pullHom_eq H G (sq i i).p₁ (sq i i).p₂ p
      (𝟙 (X i)) (𝟙 (X i)) hp₁ hp₂ (A.obj i) (A.obj i) (homD i i)
    have E :
        ((Pseudofunctor.comp H.op.toPseudofunctor G).map
          (𝟙 (X i)).op.toLoc).toFunctor.obj (A.obj i) =
        (G.map (𝟙 (H.obj (X i))).op.toLoc).toFunctor.obj (A.obj i) := by
      change (G.map (H.map (𝟙 (X i))).op.toLoc).toFunctor.obj (A.obj i) = _
      rw [H.map_id]
    have hId : HEq
        (𝟙 (((Pseudofunctor.comp H.op.toPseudofunctor G).map
          (𝟙 (X i)).op.toLoc).toFunctor.obj (A.obj i)))
        (𝟙 ((G.map (𝟙 (H.obj (X i))).op.toLoc).toFunctor.obj (A.obj i))) := by
      exact (eqToHom_heq_id_dom _ _ E).symm.trans (eqToHom_heq_id_cod _ _ E)
    exact eq_of_heq ((heq_of_eq hS).trans ((heq_of_eq hc).trans
      (h₀.trans ((heq_of_eq hT).symm.trans
        ((heq_of_eq hTarget).trans hId.symm)))))
  · intro i j k
    have hp₁ : (mappedChosenPullback₃ H sq sq₃ hsq hwide i j k).p₁ =
        H.map (sq₃ i j k).p₁ := by
      change H.map (sq₃ i j k).p₁₂ ≫ H.map (sq i j).p₁ = _
      rw [← H.map_comp, (sq₃ i j k).p₁₂_p₁]
    have hp₂ : (mappedChosenPullback₃ H sq sq₃ hsq hwide i j k).p₂ =
        H.map (sq₃ i j k).p₂ := by
      change H.map (sq₃ i j k).p₁₂ ≫ H.map (sq i j).p₂ = _
      rw [← H.map_comp, (sq₃ i j k).p₁₂_p₂]
    have hp₃ : (mappedChosenPullback₃ H sq sq₃ hsq hwide i j k).p₃ =
        H.map (sq₃ i j k).p₃ := by
      change H.map (sq₃ i j k).p₂₃ ≫ H.map (sq j k).p₂ = _
      rw [← H.map_comp, (sq₃ i j k).p₂₃_p₃]
    rw [DescentData'.pullHom'₁₂_eq_pullHom_of_chosenPullback₃,
      DescentData'.pullHom'₂₃_eq_pullHom_of_chosenPullback₃,
      DescentData'.pullHom'₁₃_eq_pullHom_of_chosenPullback₃]
    have h := A.pullHom'_hom_comp i j k
    rw [DescentData'.pullHom'₁₂_eq_pullHom_of_chosenPullback₃,
      DescentData'.pullHom'₂₃_eq_pullHom_of_chosenPullback₃,
      DescentData'.pullHom'₁₃_eq_pullHom_of_chosenPullback₃] at h
    let T₁₂ := LocallyDiscreteOpToCat.pullHom (F := G) (A.hom i j)
      (H.map (sq₃ i j k).p₁₂) (mappedChosenPullback₃ H sq sq₃ hsq hwide i j k).p₁
      (mappedChosenPullback₃ H sq sq₃ hsq hwide i j k).p₂
      (by
        change H.map (sq₃ i j k).p₁₂ ≫ H.map (sq i j).p₁ = _
        rw [hp₁, ← H.map_comp, (sq₃ i j k).p₁₂_p₁])
      (by
        change H.map (sq₃ i j k).p₁₂ ≫ H.map (sq i j).p₂ = _
        rw [hp₂, ← H.map_comp, (sq₃ i j k).p₁₂_p₂])
    let T₂₃ := LocallyDiscreteOpToCat.pullHom (F := G) (A.hom j k)
      (H.map (sq₃ i j k).p₂₃) (mappedChosenPullback₃ H sq sq₃ hsq hwide i j k).p₂
      (mappedChosenPullback₃ H sq sq₃ hsq hwide i j k).p₃
      (by
        change H.map (sq₃ i j k).p₂₃ ≫ H.map (sq j k).p₁ = _
        rw [hp₂, ← H.map_comp, (sq₃ i j k).p₂₃_p₂])
      (by
        change H.map (sq₃ i j k).p₂₃ ≫ H.map (sq j k).p₂ = _
        rw [hp₃, ← H.map_comp, (sq₃ i j k).p₂₃_p₃])
    let T₁₃ := LocallyDiscreteOpToCat.pullHom (F := G) (A.hom i k)
      (H.map (sq₃ i j k).p₁₃) (mappedChosenPullback₃ H sq sq₃ hsq hwide i j k).p₁
      (mappedChosenPullback₃ H sq sq₃ hsq hwide i j k).p₃
      (by
        change H.map (sq₃ i j k).p₁₃ ≫ H.map (sq i k).p₁ = _
        rw [hp₁, ← H.map_comp, (sq₃ i j k).p₁₃_p₁])
      (by
        change H.map (sq₃ i j k).p₁₃ ≫ H.map (sq i k).p₂ = _
        rw [hp₃, ← H.map_comp, (sq₃ i j k).p₁₃_p₃])
    let S₁₂ := LocallyDiscreteOpToCat.pullHom
      (F := Pseudofunctor.comp H.op.toPseudofunctor G) (homD i j)
      (sq₃ i j k).p₁₂ (sq₃ i j k).p₁ (sq₃ i j k).p₂
    let S₂₃ := LocallyDiscreteOpToCat.pullHom
      (F := Pseudofunctor.comp H.op.toPseudofunctor G) (homD j k)
      (sq₃ i j k).p₂₃ (sq₃ i j k).p₂ (sq₃ i j k).p₃
    let S₁₃ := LocallyDiscreteOpToCat.pullHom
      (F := Pseudofunctor.comp H.op.toPseudofunctor G) (homD i k)
      (sq₃ i j k).p₁₃ (sq₃ i j k).p₁ (sq₃ i j k).p₃
    change S₁₂ ≫ S₂₃ = S₁₃
    change T₁₂ ≫ T₂₃ = T₁₃ at h
    have H₁₂ : T₁₂ ≍ S₁₂ := by
      have h₀ := pullHom_heq_of_eq G (H.map (sq i j).p₁) (H.map (sq i j).p₂)
        (A.obj i) (A.obj j) (A.hom i j) (H.map (sq₃ i j k).p₁₂)
        hp₁.symm hp₂.symm
        (by rw [← H.map_comp, (sq₃ i j k).p₁₂_p₁])
        (by rw [← H.map_comp, (sq₃ i j k).p₁₂_p₂])
        (by rw [hp₁, ← H.map_comp, (sq₃ i j k).p₁₂_p₁])
        (by rw [hp₂, ← H.map_comp, (sq₃ i j k).p₁₂_p₂])
      exact h₀.symm.trans ((comp_pullHom_eq H G (sq i j).p₁ (sq i j).p₂
        (sq₃ i j k).p₁₂ (sq₃ i j k).p₁ (sq₃ i j k).p₂
        (sq₃ i j k).p₁₂_p₁ (sq₃ i j k).p₁₂_p₂
        (A.obj i) (A.obj j) (homD i j)).symm |> heq_of_eq)
    have H₂₃ : T₂₃ ≍ S₂₃ := by
      have h₀ := pullHom_heq_of_eq G (H.map (sq j k).p₁) (H.map (sq j k).p₂)
        (A.obj j) (A.obj k) (A.hom j k) (H.map (sq₃ i j k).p₂₃)
        hp₂.symm hp₃.symm
        (by rw [← H.map_comp, (sq₃ i j k).p₂₃_p₂])
        (by rw [← H.map_comp, (sq₃ i j k).p₂₃_p₃])
        (by rw [hp₂, ← H.map_comp, (sq₃ i j k).p₂₃_p₂])
        (by rw [hp₃, ← H.map_comp, (sq₃ i j k).p₂₃_p₃])
      exact h₀.symm.trans ((comp_pullHom_eq H G (sq j k).p₁ (sq j k).p₂
        (sq₃ i j k).p₂₃ (sq₃ i j k).p₂ (sq₃ i j k).p₃
        (sq₃ i j k).p₂₃_p₂ (sq₃ i j k).p₂₃_p₃
        (A.obj j) (A.obj k) (homD j k)).symm |> heq_of_eq)
    have H₁₃ : T₁₃ ≍ S₁₃ := by
      have h₀ := pullHom_heq_of_eq G (H.map (sq i k).p₁) (H.map (sq i k).p₂)
        (A.obj i) (A.obj k) (A.hom i k) (H.map (sq₃ i j k).p₁₃)
        hp₁.symm hp₃.symm
        (by rw [← H.map_comp, (sq₃ i j k).p₁₃_p₁])
        (by rw [← H.map_comp, (sq₃ i j k).p₁₃_p₃])
        (by rw [hp₁, ← H.map_comp, (sq₃ i j k).p₁₃_p₁])
        (by rw [hp₃, ← H.map_comp, (sq₃ i j k).p₁₃_p₃])
      exact h₀.symm.trans ((comp_pullHom_eq H G (sq i k).p₁ (sq i k).p₂
        (sq₃ i j k).p₁₃ (sq₃ i j k).p₁ (sq₃ i j k).p₃
        (sq₃ i j k).p₁₃_p₁ (sq₃ i j k).p₁₃_p₃
        (A.obj i) (A.obj k) (homD i k)).symm |> heq_of_eq)
    have E₁ : (G.map (mappedChosenPullback₃ H sq sq₃ hsq hwide i j k).p₁.op.toLoc).toFunctor.obj
        (A.obj i) =
        ((Pseudofunctor.comp H.op.toPseudofunctor G).map
          (sq₃ i j k).p₁.op.toLoc).toFunctor.obj (A.obj i) := by
      rw [hp₁]
      rfl
    have E₂ : (G.map (mappedChosenPullback₃ H sq sq₃ hsq hwide i j k).p₂.op.toLoc).toFunctor.obj
        (A.obj j) =
        ((Pseudofunctor.comp H.op.toPseudofunctor G).map
          (sq₃ i j k).p₂.op.toLoc).toFunctor.obj (A.obj j) := by
      rw [hp₂]
      rfl
    have E₃ : (G.map (mappedChosenPullback₃ H sq sq₃ hsq hwide i j k).p₃.op.toLoc).toFunctor.obj
        (A.obj k) =
        ((Pseudofunctor.comp H.op.toPseudofunctor G).map
          (sq₃ i j k).p₃.op.toLoc).toFunctor.obj (A.obj k) := by
      rw [hp₃]
      rfl
    exact eq_of_heq ((heq_comp E₁ E₂ E₃ H₁₂ H₂₃).symm.trans
      ((heq_of_eq h).trans H₁₃))

/-- Functorially recover descent data for the precomposed pseudofunctor. -/
noncomputable def descentDataUnmapPrecompFunctor :
    G.DescentData' (mappedChosenPullback H sq hsq)
        (mappedChosenPullback₃ H sq sq₃ hsq hwide) ⥤
      (Pseudofunctor.comp H.op.toPseudofunctor G).DescentData' sq sq₃ where
  obj A := A.unmapPrecomp H G sq sq₃ hsq hwide
  map φ :=
    { hom := φ.hom
      comm := φ.comm }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Chosen-pullback descent data for a precomposed pseudofunctor are equivalent
to descent data for the original pseudofunctor over the mapped diagrams. -/
noncomputable def descentDataPrecompEquivalence :
    (Pseudofunctor.comp H.op.toPseudofunctor G).DescentData' sq sq₃ ≌
      G.DescentData' (mappedChosenPullback H sq hsq)
        (mappedChosenPullback₃ H sq sq₃ hsq hwide) where
  functor := descentDataMapPrecompFunctor H G sq sq₃ hsq hwide
  inverse := descentDataUnmapPrecompFunctor H G sq sq₃ hsq hwide
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)

/-- The canonical descent functor for a precomposed pseudofunctor, converted to
chosen pullbacks and then mapped to the image diagrams. -/
noncomputable def precompToMappedDescentData' :
    (Pseudofunctor.comp H.op.toPseudofunctor G).obj (.mk (op S)) ⥤
      G.DescentData' (mappedChosenPullback H sq hsq)
        (mappedChosenPullback₃ H sq sq₃ hsq hwide) :=
  (Pseudofunctor.comp H.op.toPseudofunctor G).toDescentData f ⋙
    DescentData'.fromDescentDataFunctor
      (Pseudofunctor.comp H.op.toPseudofunctor G) sq sq₃ ⋙
    descentDataMapPrecompFunctor H G sq sq₃ hsq hwide

/-- The canonical descent functor for the original pseudofunctor over the mapped
family, expressed using the mapped chosen pullbacks. -/
noncomputable def toMappedDescentData' :
    G.obj (.mk (op (H.obj S))) ⥤
      G.DescentData' (mappedChosenPullback H sq hsq)
        (mappedChosenPullback₃ H sq sq₃ hsq hwide) :=
  G.toDescentData (fun i ↦ H.map (f i)) ⋙
    DescentData'.fromDescentDataFunctor G
      (mappedChosenPullback H sq hsq)
      (mappedChosenPullback₃ H sq sq₃ hsq hwide)

/-- The canonical descent functor commutes, up to natural isomorphism, with
precomposition by a functor preserving the chosen pullback diagrams. -/
noncomputable def precompToMappedDescentDataIso :
    precompToMappedDescentData' H G sq sq₃ hsq hwide ≅
      toMappedDescentData' H G sq sq₃ hsq hwide :=
  NatIso.ofComponents (fun M ↦
    DescentData'.isoMk (fun _ ↦ Iso.refl _) (fun i j ↦ by
      change G.obj (.mk (op (H.obj S))) at M
      dsimp [precompToMappedDescentData', toMappedDescentData',
        descentDataMapPrecompFunctor, DescentData'.mapPrecomp,
        DescentData'.fromDescentDataFunctor, DescentData'.ofDescentData,
        DescentData.ofObj]
      simp only [Functor.map_id, Category.id_comp, Category.comp_id]
      rw [comp_mapComp'_eq H G (f i) (sq i j).p₁ (sq i j).p (sq i j).hp₁,
        comp_mapComp'_eq H G (f j) (sq i j).p₂ (sq i j).p (sq i j).hp₂]
      have ep : (mappedChosenPullback H sq hsq i j).p = H.map (sq i j).p := by
        change H.map (sq i j).p₁ ≫ H.map (f i) = H.map (sq i j).p
        rw [← H.map_comp, (sq i j).hp₁]
      have ep₁ : (mappedChosenPullback H sq hsq i j).p₁ = H.map (sq i j).p₁ := rfl
      have ep₂ : (mappedChosenPullback H sq hsq i j).p₂ = H.map (sq i j).p₂ := rfl
      have hli : (mappedChosenPullback H sq hsq i j).p₁ ≫ H.map (f i) =
          (mappedChosenPullback H sq hsq i j).p := rfl
      have hri : H.map (sq i j).p₁ ≫ H.map (f i) = H.map (sq i j).p := by
        rw [← H.map_comp, (sq i j).hp₁]
      have hlj : (mappedChosenPullback H sq hsq i j).p₂ ≫ H.map (f j) =
          (mappedChosenPullback H sq hsq i j).p := by
        exact (mappedChosenPullback H sq hsq i j).condition.symm
      have hrj : H.map (sq i j).p₂ ≫ H.map (f j) = H.map (sq i j).p := by
        rw [← H.map_comp, (sq i j).hp₂]
      have H₁ := DescentComposition.mapComp'_inv_app_heq (F := G)
        (f := (H.map (f i)).op.toLoc) (f' := (H.map (f i)).op.toLoc)
        (h := (mappedChosenPullback H sq hsq i j).p₁.op.toLoc)
        (h' := (H.map (sq i j).p₁).op.toLoc)
        (fh := (mappedChosenPullback H sq hsq i j).p.op.toLoc)
        (fh' := (H.map (sq i j).p).op.toLoc)
        rfl (congrArg (fun q ↦ q.op.toLoc) ep₁) (congrArg (fun q ↦ q.op.toLoc) ep)
        (by simpa only [← Quiver.Hom.comp_toLoc, ← op_comp] using
          congrArg (fun q ↦ q.op.toLoc) hli)
        (by simpa only [← Quiver.Hom.comp_toLoc, ← op_comp] using
          congrArg (fun q ↦ q.op.toLoc) hri) M
      have H₂ := DescentComposition.mapComp'_hom_app_heq (F := G)
        (f := (H.map (f j)).op.toLoc) (f' := (H.map (f j)).op.toLoc)
        (h := (mappedChosenPullback H sq hsq i j).p₂.op.toLoc)
        (h' := (H.map (sq i j).p₂).op.toLoc)
        (fh := (mappedChosenPullback H sq hsq i j).p.op.toLoc)
        (fh' := (H.map (sq i j).p).op.toLoc)
        rfl (congrArg (fun q ↦ q.op.toLoc) ep₂) (congrArg (fun q ↦ q.op.toLoc) ep)
        (by simpa only [← Quiver.Hom.comp_toLoc, ← op_comp] using
          congrArg (fun q ↦ q.op.toLoc) hlj)
        (by simpa only [← Quiver.Hom.comp_toLoc, ← op_comp] using
          congrArg (fun q ↦ q.op.toLoc) hrj) M
      apply eq_of_heq
      apply heq_comp
      · change (G.map (mappedChosenPullback H sq hsq i j).p₁.op.toLoc).toFunctor.obj
          ((G.map (H.map (f i)).op.toLoc).toFunctor.obj M) =
          (G.map (H.map (sq i j).p₁).op.toLoc).toFunctor.obj
            ((G.map (H.map (f i)).op.toLoc).toFunctor.obj M)
        rw [ep₁]
      · change (G.map (mappedChosenPullback H sq hsq i j).p.op.toLoc).toFunctor.obj M =
          (G.map (H.map (sq i j).p).op.toLoc).toFunctor.obj M
        rw [ep]
      · change (G.map (mappedChosenPullback H sq hsq i j).p₂.op.toLoc).toFunctor.obj
          ((G.map (H.map (f j)).op.toLoc).toFunctor.obj M) =
          (G.map (H.map (sq i j).p₂).op.toLoc).toFunctor.obj
            ((G.map (H.map (f j)).op.toLoc).toFunctor.obj M)
        rw [ep₂]
      · exact H₁
      · exact H₂))

/-- A pseudofunctor has effective descent for a family whenever the original
pseudofunctor has effective descent for its image and the precomposition functor
preserves the chosen pairwise and triple pullback diagrams. -/
theorem isStackFor_precomp_of_preservesChosenPullbacks
    (sq : ∀ i j, ChosenPullback (f i) (f j))
    (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))
    (hsq : ∀ i j, IsPullback (H.map (sq i j).p₁) (H.map (sq i j).p₂)
      (H.map (f i)) (H.map (f j)))
    (hwide : ∀ i j k, IsPullback (H.map (sq₃ i j k).p₁₂)
      (H.map (sq₃ i j k).p₂₃) (H.map (sq i j).p₂) (H.map (sq j k).p₁))
    (hG : G.IsStackFor
      (Presieve.ofArrows (fun i ↦ H.obj (X i)) (fun i ↦ H.map (f i)))) :
    (Pseudofunctor.comp H.op.toPseudofunctor G).IsStackFor
      (Presieve.ofArrows X f) := by
  rw [isStackFor_ofArrows_iff] at hG ⊢
  letI : (G.toDescentData (fun i ↦ H.map (f i))).IsEquivalence := hG
  letI : (DescentData'.fromDescentDataFunctor G
      (mappedChosenPullback H sq hsq)
      (mappedChosenPullback₃ H sq sq₃ hsq hwide)).IsEquivalence :=
    (DescentData'.descentDataEquivalence G
      (mappedChosenPullback H sq hsq)
      (mappedChosenPullback₃ H sq sq₃ hsq hwide)).symm.isEquivalence_functor
  letI : (DescentData'.fromDescentDataFunctor
      (Pseudofunctor.comp H.op.toPseudofunctor G) sq sq₃).IsEquivalence :=
    (DescentData'.descentDataEquivalence
      (Pseudofunctor.comp H.op.toPseudofunctor G) sq sq₃).symm.isEquivalence_functor
  letI : (descentDataMapPrecompFunctor H G sq sq₃ hsq hwide).IsEquivalence :=
    (descentDataPrecompEquivalence H G sq sq₃ hsq hwide).isEquivalence_functor
  haveI : (toMappedDescentData' H G sq sq₃ hsq hwide).IsEquivalence := by
    dsimp only [toMappedDescentData']
    infer_instance
  haveI : (precompToMappedDescentData' H G sq sq₃ hsq hwide).IsEquivalence :=
    Functor.isEquivalence_of_iso
      (precompToMappedDescentDataIso H G sq sq₃ hsq hwide).symm
  haveI hExpanded :
      (((Pseudofunctor.comp H.op.toPseudofunctor G).toDescentData f ⋙
        DescentData'.fromDescentDataFunctor
          (Pseudofunctor.comp H.op.toPseudofunctor G) sq sq₃) ⋙
        descentDataMapPrecompFunctor H G sq sq₃ hsq hwide).IsEquivalence := by
    change (precompToMappedDescentData' H G sq sq₃ hsq hwide).IsEquivalence
    infer_instance
  haveI hFirst :
      ((Pseudofunctor.comp H.op.toPseudofunctor G).toDescentData f ⋙
        DescentData'.fromDescentDataFunctor
          (Pseudofunctor.comp H.op.toPseudofunctor G) sq sq₃).IsEquivalence := by
    apply Functor.isEquivalence_of_comp_right _
      (descentDataMapPrecompFunctor H G sq sq₃ hsq hwide)
  exact Functor.isEquivalence_of_comp_right _
    (DescentData'.fromDescentDataFunctor
      (Pseudofunctor.comp H.op.toPseudofunctor G) sq sq₃)

/-- Effective descent transfers from a precomposed pseudofunctor back to the
original pseudofunctor over the image family, when the precomposition functor
preserves the chosen pairwise and triple pullback diagrams.  Converse direction
of `isStackFor_precomp_of_preservesChosenPullbacks`. -/
theorem isStackFor_of_precomp_of_preservesChosenPullbacks
    (sq : ∀ i j, ChosenPullback (f i) (f j))
    (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))
    (hsq : ∀ i j, IsPullback (H.map (sq i j).p₁) (H.map (sq i j).p₂)
      (H.map (f i)) (H.map (f j)))
    (hwide : ∀ i j k, IsPullback (H.map (sq₃ i j k).p₁₂)
      (H.map (sq₃ i j k).p₂₃) (H.map (sq i j).p₂) (H.map (sq j k).p₁))
    (hpre : (Pseudofunctor.comp H.op.toPseudofunctor G).IsStackFor
      (Presieve.ofArrows X f)) :
    G.IsStackFor
      (Presieve.ofArrows (fun i ↦ H.obj (X i)) (fun i ↦ H.map (f i))) := by
  rw [isStackFor_ofArrows_iff] at hpre ⊢
  let _ : ((Pseudofunctor.comp H.op.toPseudofunctor G).toDescentData f).IsEquivalence :=
    hpre
  let _ : (DescentData'.fromDescentDataFunctor
      (Pseudofunctor.comp H.op.toPseudofunctor G) sq sq₃).IsEquivalence :=
    (DescentData'.descentDataEquivalence
      (Pseudofunctor.comp H.op.toPseudofunctor G) sq sq₃).symm.isEquivalence_functor
  let _ : (descentDataMapPrecompFunctor H G sq sq₃ hsq hwide).IsEquivalence :=
    (descentDataPrecompEquivalence H G sq sq₃ hsq hwide).isEquivalence_functor
  have _ : (precompToMappedDescentData' H G sq sq₃ hsq hwide).IsEquivalence := by
    dsimp only [precompToMappedDescentData']
    infer_instance
  have _ : (toMappedDescentData' H G sq sq₃ hsq hwide).IsEquivalence :=
    Functor.isEquivalence_of_iso (precompToMappedDescentDataIso H G sq sq₃ hsq hwide)
  let _ : (DescentData'.fromDescentDataFunctor G
      (mappedChosenPullback H sq hsq)
      (mappedChosenPullback₃ H sq sq₃ hsq hwide)).IsEquivalence :=
    (DescentData'.descentDataEquivalence G
      (mappedChosenPullback H sq hsq)
      (mappedChosenPullback₃ H sq sq₃ hsq hwide)).symm.isEquivalence_functor
  have hFirst : (G.toDescentData (fun i ↦ H.map (f i)) ⋙
      DescentData'.fromDescentDataFunctor G
        (mappedChosenPullback H sq hsq)
        (mappedChosenPullback₃ H sq sq₃ hsq hwide)).IsEquivalence := by
    change (toMappedDescentData' H G sq sq₃ hsq hwide).IsEquivalence
    infer_instance
  exact Functor.isEquivalence_of_comp_right _
    (DescentData'.fromDescentDataFunctor G
      (mappedChosenPullback H sq hsq)
      (mappedChosenPullback₃ H sq sq₃ hsq hwide))

/-- Precomposition by a pullback-preserving, cover-preserving functor carries a
stack on the target site to a stack on the source site. -/
theorem isStack_precomp_of_coverPreserving
    {C : Type uC} [Category.{vC} C] [HasPullbacks C]
    {D : Type uD} [Category.{vD} D]
    (H : C ⥤ D) [PreservesLimitsOfShape WalkingCospan H]
    (G : Pseudofunctor (LocallyDiscrete Dᵒᵖ) Cat.{vE, uE})
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (hH : CoverPreserving J K H) [G.IsStack K] :
    (Pseudofunctor.comp H.op.toPseudofunctor G).IsStack J := by
  apply Pseudofunctor.IsStack.of_isStackFor
  intro S R hR
  let I := R.arrows.category
  let X : I → C := fun i ↦ i.obj.left
  let f : ∀ i, X i ⟶ S := fun i ↦ i.obj.hom
  let sq : ∀ i j, ChosenPullback (f i) (f j) :=
    fun i j ↦ Limits.ChosenPullback.ofHasPullback (f i) (f j)
  let sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k) :=
    fun i j k ↦ Limits.ChosenPullback₃.ofHasPullback (sq i j) (sq j k) (sq i k)
  refine ((Pseudofunctor.comp H.op.toPseudofunctor G).isStackFor_iff_of_sieve_eq
    (R := R.arrows) (R' := Presieve.ofArrows X f) ?_).mpr ?_
  · simpa only [X, f, Sieve.generate_sieve] using (Sieve.ofArrows_category R).symm
  apply isStackFor_precomp_of_preservesChosenPullbacks H G sq sq₃
  · intro i j
    exact H.map_isPullback (sq i j).isPullback
  · intro i j k
    exact H.map_isPullback (sq₃ i j k).chosenPullback.isPullback
  ·
    have hpush := hH.cover_preserve hR
    have himage : Sieve.ofArrows (fun i ↦ H.obj (X i)) (fun i ↦ H.map (f i))
        ∈ K (H.obj S) := by
      rw [← Sieve.functorPushforward_ofArrows H]
      change Sieve.functorPushforward H
        (Sieve.ofArrows (fun i : R.arrows.category ↦ i.obj.left)
          (fun i ↦ i.obj.hom)) ∈ K (H.obj S)
      rw [Sieve.ofArrows_category R]
      exact hpush
    exact Pseudofunctor.isStackFor (J := K) G _ himage

end CategoryTheory.Pseudofunctor
