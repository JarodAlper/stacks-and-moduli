module

public import StacksAndModuli.«Section2.2-Grassmannian».«part2.2.2-projectivity-of-the-grassmannian»
public import Mathlib.CategoryTheory.Sites.Hypercover.SheafOfTypes
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import Mathlib.AlgebraicGeometry.Sites.Small
public import StacksAndModuli.API.OpenCoverQuotient
public import StacksAndModuli.API.RestrictPullbackPentagon
public import StacksAndModuli.API.RepresentableByTransport
public import StacksAndModuli.API.OverPullbackSquare

/-!
# Relative Grassmannians

This module formalizes the third subsection, Section 2.2.3 ("Relative version", label
`sec:relative-grassmannian`), of Section 2.2 (Projectivity of the Grassmannian) of
Chapter 2 of *Stacks and Moduli* — the
proof of the representability part of Theorem 2.1.1
(`thm:grassmannian-projective-relative`). It develops representability by gluing over a
Zariski cover of the base and applies it to the Grassmannian of a vector bundle.

Main book results:
- `AlgebraicGeometry.Scheme.exists_grassmannianOverFunctor_representableBy`:
  **Theorem 2.1.1** (`thm:grassmannian-projective-relative`), simultaneously packaging
  representability and strong projectivity of the relative Grassmannian.
- `AlgebraicGeometry.Scheme.isRelativelyVeryAmple_exteriorPower_universalQuotient`:
  **Corollary 2.2.15** (`cor:grassmannian-very-ample`).
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false


section ThmGrassmannianProjectiveRelative

open CategoryTheory Limits Opposite Functor.relativelyRepresentable

universe u w

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u})
variable (F : (Over S)ᵒᵖ ⥤ Type (max u w)) {I : Type u} {X : I → Over S}
variable (f : (i : I) → uliftYoneda.{w}.obj (X i) ⟶ F)

/-- The property of being an open immersion for a morphism in the slice over `S`. -/
abbrev isOpenImmersionOver : MorphismProperty (Over S) :=
  fun _ _ g ↦ IsOpenImmersion g.left

instance : (isOpenImmersionOver S).IsMultiplicative where
  id_mem X := by
    dsimp [isOpenImmersionOver]
    infer_instance
  comp_mem f g hf hg := by
    dsimp [isOpenImmersionOver] at hf hg ⊢
    letI : IsOpenImmersion f.left := hf
    letI : IsOpenImmersion g.left := hg
    infer_instance

instance : (isOpenImmersionOver S).RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition (by
    intro X Y f hf
    letI : IsIso f := hf
    dsimp [isOpenImmersionOver]
    infer_instance)

namespace RelativeRepresentability

variable {C D : Type*} [Category C] [Category D] (P : MorphismProperty C)
  {H : C ⥤ D} [H.Full] [H.Faithful] {X : C} {G : D} {a : H.obj X ⟶ G}

/-- In a self-pullback of a relatively representable morphism whose represented
base changes are monomorphisms, the two projections agree.  Unlike Mathlib's
`MorphismProperty.fst'_self_eq_snd`, this formulation is not specialized to the
small Yoneda embedding and therefore also applies to `uliftYoneda`. -/
lemma fst'_self_eq_snd (hP : P ≤ MorphismProperty.monomorphisms C)
    (ha : P.relative H a) : ha.rep.fst' a = ha.rep.snd a := by
  have hdiag : H.map (𝟙 X) ≫ a = H.map (𝟙 X) ≫ a := rfl
  let d := ha.rep.lift' (𝟙 X) (𝟙 X) hdiag
  have hd₁ : d ≫ ha.rep.fst' a = 𝟙 X := ha.rep.lift'_fst _ _ hdiag
  have hd₂ : d ≫ ha.rep.snd a = 𝟙 X := ha.rep.lift'_snd _ _ hdiag
  have hsnd : Mono (ha.rep.snd a) := by
    have hp : P (ha.rep.snd a) :=
      ha.property (g := a) _ _ (ha.rep.isPullback' a)
    exact hP _ hp
  have hsd : ha.rep.snd a ≫ d = 𝟙 _ := by
    rw [← cancel_mono (ha.rep.snd a)]
    simp only [Category.assoc, hd₂, Category.id_comp, Category.comp_id]
  haveI : IsIso d := ⟨⟨ha.rep.snd a, hd₂, hsd⟩⟩
  rw [← cancel_epi d, hd₁, hd₂]

/-- The first projection in the same self-pullback is an isomorphism.  This
universe-polymorphic variant is used by the large-presheaf gluing construction. -/
lemma isIso_fst'_self (hP : P ≤ MorphismProperty.monomorphisms C)
    (ha : P.relative H a) : IsIso (ha.rep.fst' a) := by
  rw [fst'_self_eq_snd P hP ha]
  have hdiag : H.map (𝟙 X) ≫ a = H.map (𝟙 X) ≫ a := rfl
  let d := ha.rep.lift' (𝟙 X) (𝟙 X) hdiag
  have hd₂ : d ≫ ha.rep.snd a = 𝟙 X := ha.rep.lift'_snd _ _ hdiag
  have hsnd : Mono (ha.rep.snd a) := by
    have hp : P (ha.rep.snd a) :=
      ha.property (g := a) _ _ (ha.rep.isPullback' a)
    exact hP _ hp
  have hsd : ha.rep.snd a ≫ d = 𝟙 _ := by
    rw [← cancel_mono (ha.rep.snd a)]
    simp only [Category.assoc, hd₂, Category.id_comp, Category.comp_id]
  exact ⟨⟨d, hsd, hd₂⟩⟩

end RelativeRepresentability

namespace OverLocalRepresentability

variable {S F f}
  (hf : ∀ i, (isOpenImmersionOver S).relative uliftYoneda.{w} (f i))

/-- The gluing datum in the slice category associated to a family of representable open
subfunctors of a presheaf on schemes over `S`. -/
noncomputable def overGlueData : CategoryTheory.GlueData (Over S) where
  J := I
  U := X
  V := fun (i, j) ↦ (hf i).rep.pullback (f j)
  f i j := (hf i).rep.fst' (f j)
  f_mono i j := by
    have h := (hf j).property _ _ _ ((hf i).rep.isPullback' (f j)).flip
    letI : IsOpenImmersion ((hf i).rep.fst' (f j)).left := h
    exact Over.mono_of_mono_left _
  f_id i := by
    let P := isOpenImmersionOver S
    have hP : P ≤ MorphismProperty.monomorphisms (Over S) := by
      intro A B g hg
      letI : IsOpenImmersion g.left := hg
      exact Over.mono_of_mono_left g
    exact RelativeRepresentability.isIso_fst'_self P hP (hf i)
  t i j := (hf i).rep.symmetry (hf j).rep
  t_id i := by
    let P := isOpenImmersionOver S
    have hP : P ≤ MorphismProperty.monomorphisms (Over S) := by
      intro A B g hg
      letI : IsOpenImmersion g.left := hg
      exact Over.mono_of_mono_left g
    apply (hf i).rep.hom_ext'
    · rw [symmetry_fst, RelativeRepresentability.fst'_self_eq_snd P hP (hf i)]
      simp
    · rw [symmetry_snd, RelativeRepresentability.fst'_self_eq_snd P hP (hf i)]
      simp
  t' i j k := (hf j).rep.lift₃ (f k) (f i)
    (pullback₃.p₂ (hf i).rep (f j) (f k))
    (pullback₃.p₃ (hf i).rep (f j) (f k))
    (pullback₃.p₁ (hf i).rep (f j) (f k))
    (by simp) (by simp)
  t_fac i j k := by
    apply (hf j).rep.hom_ext' <;> simp
  cocycle i j k := by
    apply pullback₃.hom_ext <;> simp

/-- The scheme gluing datum obtained by forgetting the structure morphisms in the
slice-category gluing datum. -/
noncomputable def glueData : Scheme.GlueData where
  toGlueData := (OverLocalRepresentability.overGlueData (f := f) hf).mapGlueData
    (Over.forget S)
  f_open i j := by
    exact (hf j).property _ _ _ ((hf i).rep.isPullback' (f j)).flip

/-- The structure morphism from the glued scheme to `S`, obtained by descending the
structure morphisms of the local representatives. -/
noncomputable def gluedHom : (glueData hf).glued ⟶ S :=
  (glueData hf).openCover.glueMorphisms (fun i : I ↦ (X i).hom) (fun i j ↦ by
    change pullback.fst ((glueData hf).ι i) ((glueData hf).ι j) ≫ (X i).hom =
      pullback.snd ((glueData hf).ι i) ((glueData hf).ι j) ≫ (X j).hom
    let D := glueData hf
    let l : pullback (D.ι i) (D.ι j) ⟶ D.V (i, j) :=
      (D.vPullbackConeIsLimit i j).lift (pullback.cone _ _)
    have hl₁ : l ≫ D.f i j = pullback.fst (D.ι i) (D.ι j) :=
      (D.vPullbackConeIsLimit i j).fac (pullback.cone _ _) WalkingCospan.left
    have hl₂ : l ≫ D.t i j ≫ D.f j i = pullback.snd (D.ι i) (D.ι j) :=
      (D.vPullbackConeIsLimit i j).fac (pullback.cone _ _) WalkingCospan.right
    rw [← hl₁, ← hl₂, Category.assoc, Category.assoc]
    change l ≫ ((hf i).rep.fst' (f j)).left ≫ (X i).hom =
      l ≫ ((hf i).rep.symmetry (hf j).rep).left ≫
        ((hf j).rep.fst' (f i)).left ≫ (X j).hom
    simp only [Over.w])

/-- Each local representative maps to the glued scheme over `S`. -/
lemma toGlued_comp_gluedHom (i : I) :
    (glueData hf).ι i ≫ gluedHom hf = (X i).hom := by
  exact (glueData hf).openCover.ι_glueMorphisms _ _ i

/-- The object over `S` obtained by gluing the local representatives. -/
noncomputable def gluedOver : Over S := Over.mk (gluedHom hf)

/-- The open immersion from a local representative to the glued object, as a morphism
over `S`. -/
noncomputable def toGlued (i : I) : X i ⟶ gluedOver hf :=
  Over.homMk ((glueData hf).ι i) (toGlued_comp_gluedHom hf i)

instance (i : I) : IsOpenImmersion (toGlued hf i).left := by
  change IsOpenImmersion ((glueData hf).ι i)
  infer_instance

/-- The `i`th chart, equipped with the structure morphism induced from the glued scheme. -/
noncomputable def chartOver (i : I) : Over S :=
  Over.mk ((glueData hf).ι i ≫ gluedHom hf)

/-- The canonical identification of the original relative chart with the chart carrying
the structure morphism induced from the gluing construction. -/
noncomputable def chartIso (i : I) : X i ≅ chartOver hf i :=
  Over.isoMk (Iso.refl _) (by simpa [chartOver] using toGlued_comp_gluedHom hf i)

/-- The inclusion of a chart into the glued relative scheme. -/
noncomputable def chartMap (i : I) : chartOver hf i ⟶ gluedOver hf :=
  Over.homMk ((glueData hf).ι i) rfl

/-- The overlap of two charts, with its structure morphism inherited from the first chart. -/
noncomputable def overlapOver (i j : I) : Over S :=
  Over.mk ((glueData hf).f i j ≫ (glueData hf).ι i ≫ gluedHom hf)

/-- The first projection from a chart overlap. -/
noncomputable def overlapFst (i j : I) : overlapOver hf i j ⟶ chartOver hf i :=
  Over.homMk ((glueData hf).f i j) rfl

/-- The second projection from a chart overlap. -/
noncomputable def overlapSnd (i j : I) : overlapOver hf i j ⟶ chartOver hf j :=
  Over.homMk ((glueData hf).t i j ≫ (glueData hf).f j i) (by
    dsimp [overlapOver, chartOver]
    simpa only [Category.assoc] using
      congrArg (fun q ↦ q ≫ gluedHom hf) ((glueData hf).glue_condition i j))

/-- The overlap used by the scheme gluing agrees with the original pullback in the slice. -/
noncomputable def overlapIso (i j : I) :
    overlapOver hf i j ≅ (overGlueData hf).V (i, j) :=
  Over.isoMk (Iso.refl _) (by
    change ((overGlueData hf).V (i, j)).hom =
      (glueData hf).f i j ≫ (glueData hf).ι i ≫ gluedHom hf
    have hdf : (glueData hf).f i j = ((overGlueData hf).f i j).left := rfl
    rw [hdf]
    have hι : (glueData hf).ι i ≫ gluedHom hf = (X i).hom :=
      toGlued_comp_gluedHom hf i
    calc
      _ = ((overGlueData hf).f i j).left ≫ (X i).hom :=
        (Over.w ((overGlueData hf).f i j)).symm
      _ = ((overGlueData hf).f i j).left ≫
          ((glueData hf).ι i ≫ gluedHom hf) := by rw [hι]
      _ = ((overGlueData hf).f i j).left ≫ (glueData hf).ι i ≫ gluedHom hf :=
        (Category.assoc _ _ _).symm)

@[reassoc]
lemma overlapIso_hom_fst (i j : I) :
    (overlapIso hf i j).hom ≫ (overGlueData hf).f i j =
      overlapFst hf i j ≫ (chartIso hf i).inv := by
  ext
  rfl

@[reassoc]
lemma overlapIso_hom_snd (i j : I) :
    (overlapIso hf i j).hom ≫ (overGlueData hf).t i j ≫
      (overGlueData hf).f j i = overlapSnd hf i j ≫ (chartIso hf j).inv := by
  ext
  rfl

@[reassoc]
lemma overlap_fst_chartIso_hom (i j : I) :
    (overGlueData hf).f i j ≫ (chartIso hf i).hom =
      (overlapIso hf i j).inv ≫ overlapFst hf i j := by
  rw [← cancel_epi (overlapIso hf i j).hom]
  rw [overlapIso_hom_fst_assoc, Iso.hom_inv_id_assoc]
  simpa only [Category.comp_id] using
    overlapFst hf i j ≫= (chartIso hf i).inv_hom_id

@[reassoc]
lemma overlap_snd_chartIso_hom (i j : I) :
    (overGlueData hf).t i j ≫ (overGlueData hf).f j i ≫ (chartIso hf j).hom =
      (overlapIso hf i j).inv ≫ overlapSnd hf i j := by
  rw [← cancel_epi (overlapIso hf i j).hom]
  rw [overlapIso_hom_snd_assoc, Iso.hom_inv_id_assoc]
  simpa only [Category.comp_id] using
    overlapSnd hf i j ≫= (chartIso hf j).inv_hom_id

/-- The one-hypercover of the glued object in the relative Zariski site. -/
noncomputable def oneHypercover :
    (Scheme.zariskiTopology.over S).OneHypercover (gluedOver hf) where
  I₀ := I
  X := chartOver hf
  f := chartMap hf
  I₁ _ _ := PUnit
  Y i j _ := overlapOver hf i j
  p₁ i j _ := overlapFst hf i j
  p₂ i j _ := overlapSnd hf i j
  w i j _ := by
    ext
    dsimp [overlapFst, overlapSnd, chartMap]
    exact ((glueData hf).glue_condition i j).symm
  mem₀ := by
    rw [GrothendieckTopology.mem_over_iff]
    refine Scheme.zariskiTopology.superset_covering ?_
      (glueData hf).openCover.mem_grothendieckTopology
    rw [Sieve.generate_le_iff]
    rintro W g ⟨i⟩
    rw [Sieve.overEquiv_iff]
    exact ⟨chartOver hf i, Over.homMk (𝟙 _) rfl, chartMap hf i, ⟨i⟩, by ext; rfl⟩
  mem₁ i j W p₁ p₂ fac := by
    refine (Scheme.zariskiTopology.over S).superset_covering (fun T g _ ↦ ?_)
      ((Scheme.zariskiTopology.over S).top_mem W)
    have fac₀ := congrArg Over.Hom.left fac
    dsimp [chartMap] at fac₀
    have fac₀' : g.left ≫ p₁.left ≫ (glueData hf).ι i =
        g.left ≫ p₂.left ≫ (glueData hf).ι j := g.left ≫= fac₀
    have fac' : (g.left ≫ p₁.left) ≫ (glueData hf).ι i =
        (g.left ≫ p₂.left) ≫ (glueData hf).ι j := by
      simpa only [Category.assoc] using fac₀'
    have ⟨φ, h₁, h₂⟩ := PullbackCone.IsLimit.lift' ((glueData hf).vPullbackConeIsLimit i j)
      (g.left ≫ p₁.left) (g.left ≫ p₂.left) fac'
    change φ ≫ (overlapFst hf i j).left = g.left ≫ p₁.left at h₁
    let h : T ⟶ overlapOver hf i j := Over.homMk φ (by
      change φ ≫ (overlapFst hf i j).left ≫ (chartOver hf i).hom = T.hom
      rw [← Category.assoc, h₁]
      exact Over.w (g ≫ p₁))
    exact ⟨⟨⟩, h, by ext; exact h₁.symm, by ext; exact h₂.symm⟩

section

variable (G : Sheaf (Scheme.zariskiTopology.over S) (Type (max u w)))
  (s : ∀ i, G.obj.obj (op (chartOver hf i)))
  (hs : ∀ i j, G.obj.map (overlapFst hf i j).op (s i) =
    G.obj.map (overlapSnd hf i j).op (s j))

/-- Glue compatible sections on the relative representatives. -/
noncomputable def sheafValGluedMk : G.obj.obj (op (gluedOver hf)) :=
  Multifork.IsLimit.sectionsEquiv ((oneHypercover hf).isLimitMultifork G)
    { val := fun i ↦ s i
      property := by rintro ⟨⟨i, j⟩, ⟨⟩⟩; exact hs i j }

@[simp]
lemma sheafValGluedMk_val (i : I) :
    G.obj.map (chartMap hf i).op (sheafValGluedMk hf G s hs) = s i :=
  Multifork.IsLimit.sectionsEquiv_apply_val ((oneHypercover hf).isLimitMultifork G) _ _

end

section SheafRepresentability

variable (G : Sheaf (Scheme.zariskiTopology.over S) (Type (max u w)))
  (g : (i : I) → uliftYoneda.{w}.obj (X i) ⟶ G.1)
  (hg : ∀ i, (isOpenImmersionOver S).relative uliftYoneda.{w} (g i))

/-- The local map to the sheaf, transported to the chart used by the gluing construction. -/
noncomputable def chartToSheaf (i : I) :
    uliftYoneda.{w}.obj (chartOver hg i) ⟶ G.1 :=
  uliftYoneda.map (chartIso hg i).inv ≫ g i

lemma chartToSheaf_overlap (i j : I) :
    uliftYoneda.map (overlapFst hg i j) ≫ chartToSheaf G g hg i =
      uliftYoneda.map (overlapSnd hg i j) ≫ chartToSheaf G g hg j := by
  apply uliftYonedaEquiv.injective
  simp only [chartToSheaf, uliftYonedaEquiv_comp,
    uliftYonedaEquiv_uliftYoneda_map]
  change (g i).app _ ⟨overlapFst hg i j ≫ (chartIso hg i).inv⟩ =
    (g j).app _ ⟨overlapSnd hg i j ≫ (chartIso hg j).inv⟩
  rw [← overlapIso_hom_fst hg i j, ← overlapIso_hom_snd hg i j]
  have hfst : (overGlueData hg).f i j = (hg i).rep.fst' (g j) := rfl
  have hsnd : (overGlueData hg).t i j ≫ (overGlueData hg).f j i =
      (hg i).rep.snd (g j) := by
    change (hg i).rep.symmetry (hg j).rep ≫ (hg j).rep.fst' (g i) =
      (hg i).rep.snd (g j)
    exact (hg i).rep.symmetry_fst (hg j).rep
  rw [hfst, hsnd]
  change (g i).app (op (overlapOver hg i j))
      ⟨(overlapIso hg i j).hom ≫ (hg i).rep.fst' (g j)⟩ =
    (g j).app (op (overlapOver hg i j))
      ⟨(overlapIso hg i j).hom ≫ (hg i).rep.snd (g j)⟩
  have hw := congrArg
    (fun q ↦ q.app (op (overlapOver hg i j)) ⟨(overlapIso hg i j).hom⟩)
    ((hg i).rep.isPullback' (g j)).w
  change (g i).app (op (overlapOver hg i j))
      ⟨(overlapIso hg i j).hom ≫ (hg i).rep.fst' (g j)⟩ =
    (g j).app (op (overlapOver hg i j))
      ⟨(overlapIso hg i j).hom ≫ (hg i).rep.snd (g j)⟩ at hw
  exact hw

/-- The map from the relative scheme obtained by gluing to the sheaf. -/
noncomputable def yonedaGluedToSheaf :
    (Scheme.zariskiTopology.over S).uliftYoneda.{w}.obj (gluedOver hg) ⟶ G :=
  ⟨uliftYonedaEquiv.symm (sheafValGluedMk hg G
    (fun i ↦ uliftYonedaEquiv (chartToSheaf G g hg i)) (by
      intro i j
      apply uliftYonedaEquiv.symm.injective
      change uliftYonedaEquiv.symm
          (G.1.map (overlapFst hg i j).op
            (uliftYonedaEquiv (chartToSheaf G g hg i))) =
        uliftYonedaEquiv.symm
          (G.1.map (overlapSnd hg i j).op
            (uliftYonedaEquiv (chartToSheaf G g hg j)))
      have hfop : (overlapFst hg i j).op.unop = overlapFst hg i j := rfl
      have hsop : (overlapSnd hg i j).op.unop = overlapSnd hg i j := rfl
      calc
        _ = uliftYoneda.map (overlapFst hg i j) ≫
              uliftYonedaEquiv.symm
                (uliftYonedaEquiv (chartToSheaf G g hg i)) := by
          simpa only [hfop] using
            (uliftYonedaEquiv_symm_map (F := G.1) (overlapFst hg i j).op
              (uliftYonedaEquiv (chartToSheaf G g hg i)))
        _ = uliftYoneda.map (overlapFst hg i j) ≫
              chartToSheaf G g hg i := by
          rw [Equiv.symm_apply_apply]
        _ = uliftYoneda.map (overlapSnd hg i j) ≫
              chartToSheaf G g hg j := chartToSheaf_overlap G g hg i j
        _ = uliftYoneda.map (overlapSnd hg i j) ≫
              uliftYonedaEquiv.symm
                (uliftYonedaEquiv (chartToSheaf G g hg j)) := by
          rw [Equiv.symm_apply_apply]
        _ = _ := by
          simpa only [hsop] using
            (uliftYonedaEquiv_symm_map (F := G.1) (overlapSnd hg i j).op
              (uliftYonedaEquiv (chartToSheaf G g hg j))).symm))⟩

@[reassoc (attr := simp)]
lemma yoneda_chartMap_yonedaGluedToSheaf (i : I) :
    uliftYoneda.map (chartMap hg i) ≫ (yonedaGluedToSheaf G g hg).hom =
      chartToSheaf G g hg i := by
  apply uliftYonedaEquiv.injective
  rw [uliftYonedaEquiv_comp, uliftYonedaEquiv_uliftYoneda_map]
  change G.obj.map (chartMap hg i).op
      (sheafValGluedMk hg G (fun i ↦ uliftYonedaEquiv (chartToSheaf G g hg i)) _) =
    uliftYonedaEquiv (chartToSheaf G g hg i)
  exact sheafValGluedMk_val hg G _ _ i

lemma chartIso_hom_chartMap (i : I) :
    (chartIso hg i).hom ≫ chartMap hg i = toGlued hg i := by
  ext
  rfl

@[reassoc (attr := simp)]
lemma yoneda_toGlued_yonedaGluedToSheaf (i : I) :
    uliftYoneda.map (toGlued hg i) ≫ (yonedaGluedToSheaf G g hg).hom = g i := by
  rw [← chartIso_hom_chartMap G g hg i, uliftYoneda.map_comp, Category.assoc,
    yoneda_chartMap_yonedaGluedToSheaf, chartToSheaf,
    ← uliftYoneda.map_comp_assoc]
  simp

@[simp]
lemma yonedaGluedToSheaf_app_chartMap {i : I} :
    dsimp% (yonedaGluedToSheaf G g hg).hom.app _ ⟨chartMap hg i⟩ =
      uliftYonedaEquiv (chartToSheaf G g hg i) := by
  have h := congrArg
    (fun q ↦ q.app (op (chartOver hg i)) ⟨𝟙 (chartOver hg i)⟩)
    (yoneda_chartMap_yonedaGluedToSheaf G g hg i)
  have h' : (yonedaGluedToSheaf G g hg).hom.app
      (op (chartOver hg i)) ⟨chartMap hg i⟩ =
      (chartToSheaf G g hg i).app (op (chartOver hg i)) ⟨𝟙 _⟩ := by
    exact h
  exact h'.trans
    (CategoryTheory.uliftYonedaEquiv_apply (chartToSheaf G g hg i)).symm

instance [Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over S) (Sigma.desc g)] :
    Sheaf.IsLocallySurjective (yonedaGluedToSheaf G g hg) :=
  Presheaf.isLocallySurjective_of_isLocallySurjective_fac _
    (show Sigma.desc (fun i ↦ uliftYoneda.map (toGlued hg i)) ≫
      (yonedaGluedToSheaf G g hg).hom = Sigma.desc g by cat_disch)

lemma comp_toGlued_eq {U : Over S} {i j : I} (a : U ⟶ X i) (b : U ⟶ X j)
    (h : uliftYoneda.map a ≫ g i = uliftYoneda.map b ≫ g j) :
    a ≫ toGlued hg i = b ≫ toGlued hg j := by
  let l := (hg i).rep.lift' a b h
  let m : U ⟶ overlapOver hg i j := l ≫ (overlapIso hg i j).inv
  have ha : l ≫ (overGlueData hg).f i j = a := by
    exact (hg i).rep.lift'_fst a b h
  have hb : l ≫ (overGlueData hg).t i j ≫ (overGlueData hg).f j i = b := by
    have hsnd : (overGlueData hg).t i j ≫ (overGlueData hg).f j i =
        (hg i).rep.snd (g j) := by
      change (hg i).rep.symmetry (hg j).rep ≫ (hg j).rep.fst' (g i) =
        (hg i).rep.snd (g j)
      exact (hg i).rep.symmetry_fst (hg j).rep
    calc
      _ = l ≫ ((overGlueData hg).t i j ≫ (overGlueData hg).f j i) :=
        Category.assoc _ _ _
      _ = l ≫ (hg i).rep.snd (g j) := by rw [hsnd]
      _ = b := (hg i).rep.lift'_snd a b h
  calc
    a ≫ toGlued hg i = m ≫ overlapFst hg i j ≫ chartMap hg i := by
      rw [← ha, ← chartIso_hom_chartMap G g hg i]
      simp only [m, Category.assoc, overlap_fst_chartIso_hom_assoc]
    _ = m ≫ overlapSnd hg i j ≫ chartMap hg j := by
      have hw := m ≫= (oneHypercover hg).w (i₁ := i) (i₂ := j) PUnit.unit
      change m ≫ overlapFst hg i j ≫ chartMap hg i =
        m ≫ overlapSnd hg i j ≫ chartMap hg j at hw
      exact hw
    _ = b ≫ toGlued hg j := by
      rw [← hb, ← chartIso_hom_chartMap G g hg j]
      simp only [m, Category.assoc, overlap_snd_chartIso_hom_assoc]

@[simp]
lemma yonedaGluedToSheaf_app_comp {V U : Over S} (γ : V ⟶ U)
    (α : U ⟶ gluedOver hg) :
    dsimp% (yonedaGluedToSheaf G g hg).hom.app (op V) ⟨γ ≫ α⟩ =
      G.obj.map γ.op ((yonedaGluedToSheaf G g hg).hom.app (op U) ⟨α⟩) :=
  ConcreteCategory.congr_hom
    ((yonedaGluedToSheaf G g hg).hom.naturality γ.op) ⟨α⟩

instance : Sheaf.IsLocallyInjective (yonedaGluedToSheaf G g hg) where
  equalizerSieve_mem := by
    rintro ⟨U⟩ ⟨α⟩ ⟨β⟩ h
    replace h : (yonedaGluedToSheaf G g hg).hom.app _ ⟨α⟩ =
        (yonedaGluedToSheaf G g hg).hom.app _ ⟨β⟩ := h
    have mem := (oneHypercover hg).mem₀
    refine (Scheme.zariskiTopology.over S).superset_covering (fun V γ hγ ↦ ?_)
      ((Scheme.zariskiTopology.over S).intersection_covering
        ((Scheme.zariskiTopology.over S).pullback_stable α mem)
        ((Scheme.zariskiTopology.over S).pullback_stable β mem))
    obtain ⟨⟨W₁, a, _, ⟨i⟩, fac₁⟩, ⟨W₂, b, _, ⟨j⟩, fac₂⟩⟩ := hγ
    change I at i j
    change V ⟶ chartOver hg i at a
    change V ⟶ chartOver hg j at b
    apply ULift.ext
    change γ ≫ α = γ ≫ β
    replace h : (yonedaGluedToSheaf G g hg).hom.app _ ⟨γ ≫ α⟩ =
        (yonedaGluedToSheaf G g hg).hom.app _ ⟨γ ≫ β⟩ := by
      dsimp at h
      simp [h]
    rw [← fac₁, ← fac₂] at h ⊢
    have hfi : (oneHypercover hg).f i = chartMap hg i := rfl
    have hfj : (oneHypercover hg).f j = chartMap hg j := rfl
    rw [hfi, hfj] at ⊢
    have h' : G.obj.map a.op
        ((yonedaGluedToSheaf G g hg).hom.app _ ⟨chartMap hg i⟩) =
      G.obj.map b.op ((yonedaGluedToSheaf G g hg).hom.app _ ⟨chartMap hg j⟩) := by
      calc
        _ = (yonedaGluedToSheaf G g hg).hom.app _ ⟨a ≫ chartMap hg i⟩ :=
          (yonedaGluedToSheaf_app_comp G g hg a (chartMap hg i)).symm
        _ = (yonedaGluedToSheaf G g hg).hom.app _ ⟨b ≫ chartMap hg j⟩ := h
        _ = _ := yonedaGluedToSheaf_app_comp G g hg b (chartMap hg j)
    have hi := yonedaGluedToSheaf_app_chartMap G g hg (i := i)
    have hj := yonedaGluedToSheaf_app_chartMap G g hg (i := j)
    have h'' : G.obj.map a.op (uliftYonedaEquiv (chartToSheaf G g hg i)) =
        G.obj.map b.op (uliftYonedaEquiv (chartToSheaf G g hg j)) := by
      calc
        _ = G.obj.map a.op
            ((yonedaGluedToSheaf G g hg).hom.app _ ⟨chartMap hg i⟩) :=
          congrArg (G.obj.map a.op) hi.symm
        _ = G.obj.map b.op
            ((yonedaGluedToSheaf G g hg).hom.app _ ⟨chartMap hg j⟩) := h'
        _ = _ := congrArg (G.obj.map b.op) hj
    have hab : uliftYoneda.map (a ≫ (chartIso hg i).inv) ≫ g i =
        uliftYoneda.map (b ≫ (chartIso hg j).inv) ≫ g j := by
      have h''' := congrArg uliftYonedaEquiv.symm h''
      rw [uliftYonedaEquiv_symm_map, uliftYonedaEquiv_symm_map] at h'''
      have haop : a.op.unop = a := rfl
      have hbop : b.op.unop = b := rfl
      simpa only [chartToSheaf, Equiv.symm_apply_apply, uliftYoneda.map_comp,
        haop, hbop, Category.assoc] using h'''
    have eq := comp_toGlued_eq G g hg (a ≫ (chartIso hg i).inv)
      (b ≫ (chartIso hg j).inv) hab
    change a ≫ chartMap hg i = b ≫ chartMap hg j
    simpa only [Category.assoc, ← chartIso_hom_chartMap G g hg,
      Iso.inv_hom_id_assoc] using eq

variable [Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over S) (Sigma.desc g)]

instance : IsIso (yonedaGluedToSheaf G g hg) := by
  rw [← Sheaf.isLocallyBijective_iff_isIso (yonedaGluedToSheaf G g hg)]
  constructor <;> infer_instance

/-- The natural isomorphism representing a relative sheaf from a jointly surjective
family of representable open subfunctors. -/
noncomputable def yonedaIsoSheaf :
    (Scheme.zariskiTopology.over S).uliftYoneda.{w}.obj (gluedOver hg) ≅ G :=
  asIso (yonedaGluedToSheaf G g hg)

/-- A relative Zariski sheaf covered by representable open subfunctors is represented
by their glued object over the base. -/
noncomputable def representableBy : G.1.RepresentableBy (gluedOver hg) :=
  (Functor.RepresentableBy.equivUliftYonedaIso G.1 (gluedOver hg)).symm
    ((sheafToPresheaf _ _).mapIso (yonedaIsoSheaf G g hg))

include g hg in
/-- A relative Zariski sheaf admitting a jointly surjective family of representable
open subfunctors is representable. -/
theorem isRepresentable : G.1.IsRepresentable :=
  ⟨gluedOver hg, ⟨representableBy G g hg⟩⟩

end SheafRepresentability

end OverLocalRepresentability

namespace BaseRestrictionChart

variable {U S : Scheme.{u}} (j : U ⟶ S)
  (H : (Over U)ᵒᵖ ⥤ Type (u + 1)) (F : (Over S)ᵒᵖ ⥤ Type (u + 1))
  (P : Over U) (R : H.RepresentableBy P)
  (e : H ≅ (Over.map j).op ⋙ F)

/-- A representative over an open part of the base, regarded as an object over the
original base. -/
noncomputable def object : Over S := (Over.map j).obj P

/-- The universal local point transported to the global functor. -/
noncomputable def point : F.obj (op (object j P)) :=
  e.hom.app (op P) (R.homEquiv (𝟙 P))

/-- The map from a represented restriction chart to the global functor. -/
noncomputable def map : uliftYoneda.{u + 1}.obj (object j P) ⟶ F :=
  uliftYonedaEquiv.symm (point j H F P R e)

/-- The base change to `U` of a test object over `S`, regarded again as an object over
`S`.  This is the object which represents the inverse image of a restriction chart. -/
noncomputable def pullbackObject (T : Over S) : Over S :=
  (Over.map j).obj ((Over.pullback j).obj T)

/-- The projection from the base-changed test object to the original test object. -/
noncomputable def pullbackSnd (T : Over S) : pullbackObject j T ⟶ T :=
  (Over.mapPullbackAdj j).counit.app T

instance [IsOpenImmersion j] (T : Over S) :
    IsOpenImmersion (pullbackSnd j T).left := by
  change IsOpenImmersion (pullback.fst T.hom j)
  infer_instance

/-- A global point restricted to the pullback test object and transported back through
the chosen local comparison. -/
noncomputable def restrictedPoint (T : Over S) (z : F.obj (op T)) :
    H.obj (op ((Over.pullback j).obj T)) :=
  e.inv.app _ (F.map (pullbackSnd j T).op z)

/-- The unique morphism from the pulled-back test object to the local representative
classified by the restricted point. -/
noncomputable def lift (T : Over S) (z : F.obj (op T)) :
    (Over.pullback j).obj T ⟶ P :=
  R.homEquiv.symm
    (restrictedPoint (j := j) (H := H) (F := F) (e := e) T z)

/-- The first map in the canonical square representing the inverse image of a
restriction chart. -/
noncomputable def pullbackFst (T : Over S) (z : F.obj (op T)) :
    uliftYoneda.{u + 1}.obj (pullbackObject j T) ⟶
      uliftYoneda.{u + 1}.obj (object j P) :=
  uliftYoneda.map ((Over.map j).map
    (lift (j := j) (H := H) (F := F) (P := P) (R := R) (e := e) T z))

/-- The canonical inverse-image square commutes. -/
lemma pullback_square_w (T : Over S) (z : F.obj (op T)) :
    pullbackFst j H F P R e T z ≫ map j H F P R e =
      uliftYoneda.map (pullbackSnd j T) ≫ uliftYonedaEquiv.symm z := by
  apply uliftYonedaEquiv.injective
  rw [uliftYonedaEquiv_comp]
  simp only [pullbackFst, uliftYonedaEquiv_uliftYoneda_map, map,
    uliftYonedaEquiv_symm_apply_app]
  change F.map ((Over.map j).map
      (lift (j := j) (H := H) (F := F) (P := P) (R := R) (e := e) T z)).op
      (point j H F P R e) = F.map (pullbackSnd j T).op z
  rw [point]
  have hn := e.hom.naturality
    (lift (j := j) (H := H) (F := F) (P := P) (R := R) (e := e) T z).op
  have hnapp := ConcreteCategory.congr_hom hn (R.homEquiv (𝟙 P))
  rw [← ConcreteCategory.comp_apply]
  change (e.hom.app (op P) ≫ ((Over.map j).op ⋙ F).map
      (lift (j := j) (H := H) (F := F) (P := P) (R := R) (e := e) T z).op)
      (R.homEquiv (𝟙 P)) = _
  rw [← hnapp]
  rw [ConcreteCategory.comp_apply]
  rw [← R.homEquiv_comp]
  simp only [Category.comp_id, lift, Equiv.apply_symm_apply, restrictedPoint]
  rw [← ConcreteCategory.comp_apply]
  exact ConcreteCategory.congr_hom (e.inv_hom_id_app _) _

/-- The canonical cone over the inverse-image cospan of a restriction chart. -/
noncomputable def pullbackCone (T : Over S) (z : F.obj (op T)) :
    PullbackCone (map j H F P R e) (uliftYonedaEquiv.{u + 1}.symm z) :=
  PullbackCone.mk (pullbackFst j H F P R e T z)
    (uliftYoneda.map (pullbackSnd j T)) (pullback_square_w j H F P R e T z)

/-- A test object mapping to the global chart, equipped with the induced structure
morphism to the open base `U`. -/
noncomputable def factorObject {W : Over S} (L : W ⟶ object j P) : Over U :=
  Over.mk (L.left ≫ P.hom)

/-- Factoring through the chart identifies the original test object with the result of
forgetting its induced `U`-structure. -/
noncomputable def factorIso {W : Over S} (L : W ⟶ object j P) :
    W ≅ (Over.map j).obj (factorObject j P L) :=
  Over.isoMk (Iso.refl _) (by
    change (L.left ≫ P.hom) ≫ j = W.hom
    calc
      _ = L.left ≫ (object j P).hom := rfl
      _ = W.hom := Over.w L)

/-- The map to the local representative underlying a factorization through the global
chart. -/
noncomputable def factorToRepresentative {W : Over S} (L : W ⟶ object j P) :
    factorObject j P L ⟶ P :=
  Over.homMk L.left rfl

@[reassoc (attr := simp)]
lemma factorIso_hom_map_factorToRepresentative {W : Over S}
    (L : W ⟶ object j P) :
    (factorIso j P L).hom ≫ (Over.map j).map (factorToRepresentative j P L) = L := by
  ext
  rfl

/-- A map from a factored test object to a global test object, expressed with domain in
the image of `Over.map j`. -/
noncomputable def factorToTest {W T : Over S} (L : W ⟶ object j P) (a : W ⟶ T) :
    (Over.map j).obj (factorObject j P L) ⟶ T :=
  (factorIso j P L).inv ≫ a

@[reassoc (attr := simp)]
lemma factorIso_hom_factorToTest {W T : Over S}
    (L : W ⟶ object j P) (a : W ⟶ T) :
    (factorIso j P L).hom ≫ factorToTest j P L a = a := by
  simp [factorToTest]

/-- The adjoint lift from a factored test object to the pullback of the global test
object along `j`. -/
noncomputable def factorLift {W T : Over S} (L : W ⟶ object j P) (a : W ⟶ T) :
    factorObject j P L ⟶ (Over.pullback j).obj T :=
  (Over.mapPullbackAdj j).homEquiv (factorObject j P L) T
    (factorToTest j P L a)

@[reassoc (attr := simp)]
lemma map_factorLift_counit {W T : Over S} (L : W ⟶ object j P) (a : W ⟶ T) :
    (Over.map j).map (factorLift j P L a) ≫ (Over.mapPullbackAdj j).counit.app T =
      factorToTest j P L a := by
  dsimp [factorLift]
  rw [← (Over.mapPullbackAdj j).homEquiv_counit]
  exact Equiv.symm_apply_apply _ _

/-- The induced global morphism to the canonical inverse-image object. -/
noncomputable def globalFactorLift {W T : Over S} (L : W ⟶ object j P) (a : W ⟶ T) :
    W ⟶ pullbackObject j T :=
  (factorIso j P L).hom ≫ (Over.map j).map (factorLift j P L a)

@[reassoc (attr := simp)]
lemma globalFactorLift_pullbackSnd {W T : Over S} (L : W ⟶ object j P) (a : W ⟶ T) :
    globalFactorLift j P L a ≫ pullbackSnd j T = a := by
  dsimp [globalFactorLift, pullbackSnd, pullbackObject, factorLift, factorToTest]
  rw [Category.assoc, ← (Over.mapPullbackAdj j).homEquiv_counit]
  simp

lemma globalFactorLift_unique [IsOpenImmersion j] {W T : Over S}
    (L : W ⟶ object j P) (a : W ⟶ T) (b : W ⟶ pullbackObject j T)
    (hb : b ≫ pullbackSnd j T = a) : b = globalFactorLift j P L a := by
  letI : Mono (pullbackSnd j T) := Over.mono_of_mono_left _
  rw [← cancel_mono (pullbackSnd j T), hb, globalFactorLift_pullbackSnd]

/-- A restriction chart is pointwise injective when the base map is an open
immersion. -/
lemma map_app_injective [IsOpenImmersion j] (W : Over S) :
    Function.Injective ((map j H F P R e).app (op W)) := by
  rintro ⟨L₁⟩ ⟨L₂⟩ hL
  apply ULift.ext
  have hj : Mono j := by infer_instance
  have hbase : L₁.left ≫ P.hom = L₂.left ≫ P.hom := by
    rw [← cancel_mono j]
    calc
      (L₁.left ≫ P.hom) ≫ j = L₁.left ≫ (object j P).hom := rfl
      _ = L₂.left ≫ (object j P).hom := (Over.w L₁).trans (Over.w L₂).symm
      _ = (L₂.left ≫ P.hom) ≫ j := rfl
  let l₁ : factorObject j P L₁ ⟶ P := factorToRepresentative j P L₁
  let l₂ : factorObject j P L₁ ⟶ P := Over.homMk L₂.left hbase.symm
  have hmap₁ : (factorIso j P L₁).inv ≫ L₁ = (Over.map j).map l₁ := by
    rw [← cancel_epi (factorIso j P L₁).hom]
    exact (factorIso_hom_map_factorToRepresentative j P L₁).symm
  have hmap₂ : (factorIso j P L₁).inv ≫ L₂ = (Over.map j).map l₂ := by
    rw [← cancel_epi (factorIso j P L₁).hom]
    ext
    rfl
  have hLK := by
    change F.map L₁.op (point j H F P R e) =
      F.map L₂.op (point j H F P R e) at hL
    have h := congrArg (F.map (factorIso j P L₁).inv.op) hL
    simp only [← Functor.map_comp_apply, ← op_comp, hmap₁, hmap₂] at h
    exact h
  have hl : l₁ = l₂ := by
    apply R.homEquiv.injective
    apply (ConcreteCategory.bijective_of_isIso
      (e.hom.app (op (factorObject j P L₁)))).injective
    have hn₁ := e.hom.naturality l₁.op
    have hn₂ := e.hom.naturality l₂.op
    have he₁ : e.hom.app (op (factorObject j P L₁)) (R.homEquiv l₁) =
        F.map ((Over.map j).map l₁).op (point j H F P R e) := by
      calc
        _ = e.hom.app (op (factorObject j P L₁))
            (H.map l₁.op (R.homEquiv (𝟙 P))) := by
          rw [← R.homEquiv_comp]
          simp
        _ = (H.map l₁.op ≫ e.hom.app (op (factorObject j P L₁)))
            (R.homEquiv (𝟙 P)) := rfl
        _ = (e.hom.app (op P) ≫ ((Over.map j).op ⋙ F).map l₁.op)
            (R.homEquiv (𝟙 P)) := ConcreteCategory.congr_hom hn₁ _
        _ = _ := rfl
    have he₂ : e.hom.app (op (factorObject j P L₁)) (R.homEquiv l₂) =
        F.map ((Over.map j).map l₂).op (point j H F P R e) := by
      calc
        _ = e.hom.app (op (factorObject j P L₁))
            (H.map l₂.op (R.homEquiv (𝟙 P))) := by
          rw [← R.homEquiv_comp]
          simp
        _ = (H.map l₂.op ≫ e.hom.app (op (factorObject j P L₁)))
            (R.homEquiv (𝟙 P)) := rfl
        _ = (e.hom.app (op P) ≫ ((Over.map j).op ⋙ F).map l₂.op)
            (R.homEquiv (𝟙 P)) := ConcreteCategory.congr_hom hn₂ _
        _ = _ := rfl
    exact he₁.trans (hLK.trans he₂.symm)
  have hLL : L₁ = L₂ := by
    have hleft : L₁.left = L₂.left := by
      change l₁.left = l₂.left
      exact congrArg (fun q ↦ q.left) hl
    exact CommaMorphism.ext hleft (by simp)
  exact hLL

instance [IsOpenImmersion j] : Mono (map j H F P R e) := by
  rw [NatTrans.mono_iff_mono_app]
  intro W
  rw [mono_iff_injective]
  exact map_app_injective j H F P R e (unop W)

/-- The canonical lift also has the prescribed first projection whenever the two
given legs form a commutative cone. -/
lemma globalFactorLift_pullbackFst [IsOpenImmersion j] {W T : Over S}
    (z : F.obj (op T)) (L : W ⟶ object j P) (a : W ⟶ T)
    (h : (map j H F P R e).app (op W) ⟨L⟩ =
      (uliftYonedaEquiv.{u + 1}.symm z).app (op W) ⟨a⟩) :
    globalFactorLift j P L a ≫
        (Over.map j).map (lift (j := j) (H := H) (F := F) (P := P)
          (R := R) (e := e) T z) = L := by
  apply ULift.up_injective
  apply (map_app_injective j H F P R e W)
  have hw := congrArg
    (fun q ↦ q.app (op W) ⟨globalFactorLift j P L a⟩)
    (pullback_square_w j H F P R e T z)
  change (map j H F P R e).app (op W)
      ⟨globalFactorLift j P L a ≫ (Over.map j).map
        (lift (j := j) (H := H) (F := F) (P := P)
          (R := R) (e := e) T z)⟩ =
    (map j H F P R e).app (op W) ⟨L⟩
  calc
    _ = (uliftYonedaEquiv.{u + 1}.symm z).app (op W)
        ⟨globalFactorLift j P L a ≫ pullbackSnd j T⟩ := hw
    _ = (uliftYonedaEquiv.{u + 1}.symm z).app (op W) ⟨a⟩ := by
      rw [globalFactorLift_pullbackSnd]
    _ = _ := h.symm

/-- The canonical square represents the inverse image of a base-restriction chart. -/
lemma isPullback [IsOpenImmersion j] (T : Over S) (z : F.obj (op T)) :
    IsPullback (pullbackFst j H F P R e T z)
      (uliftYoneda.map (pullbackSnd j T)) (map j H F P R e)
      (uliftYonedaEquiv.{u + 1}.symm z) := by
  apply IsPullback.of_forall_isPullback_app
  intro W
  rw [Types.isPullback_iff]
  refine ⟨congrArg (·.app W) (pullback_square_w j H F P R e T z), ?_, ?_⟩
  · intro a b hab
    apply ULift.ext
    letI : Mono (pullbackSnd j T) := Over.mono_of_mono_left _
    rw [← cancel_mono (pullbackSnd j T)]
    exact congrArg ULift.down hab.2
  · rintro ⟨L⟩ ⟨a⟩ h
    refine ⟨⟨globalFactorLift j P L a⟩, ?_, ?_⟩
    · apply ULift.ext
      exact globalFactorLift_pullbackFst j H F P R e z L a h
    · apply ULift.ext
      exact globalFactorLift_pullbackSnd j P L a

/-- A represented restriction along an open immersion of bases is a representable
open subfunctor of the global functor. -/
theorem isOpenImmersion [IsOpenImmersion j] :
    (isOpenImmersionOver S).relative uliftYoneda.{u + 1}
      (map j H F P R e) := by
  apply MorphismProperty.relative.of_exists
  intro T z
  let z₀ : F.obj (op T) := uliftYonedaEquiv z
  refine ⟨pullbackObject j T, pullbackFst j H F P R e T z₀,
    pullbackSnd j T, ?_, ?_⟩
  · simpa only [z₀, Equiv.symm_apply_apply] using
      isPullback j H F P R e T z₀
  exact inferInstance

end BaseRestrictionChart

end AlgebraicGeometry.Scheme

end ThmGrassmannianProjectiveRelative

section ThmGrassmannianProjectiveRelative

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The quotient obtained by descending compatible kernels is quasicoherent when its
local cokernel models are quasicoherent. -/
lemma openCoverQuotientSheaf_isQuasicoherent
    (𝒰 : Scheme.OpenCover.{u} X) (M : X.Modules)
    (K : ∀ i, (𝒰.X i).Modules)
    (k : ∀ i, K i ⟶ (restrictFunctor (𝒰.f i)).obj M)
    [∀ i, Mono (k i)]
    (hcompat : OpenCoverSubmoduleCompatible 𝒰 M K k)
    [hqc : ∀ i, (cokernel (k i)).IsQuasicoherent] :
    (openCoverQuotientSheaf 𝒰 M k).IsQuasicoherent := by
  let _ (i : 𝒰.I₀) : ((restrictFunctor (𝒰.f i)).obj
      (openCoverQuotientSheaf 𝒰 M k)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (𝒰.X i).ringCatSheaf).prop_of_iso
      (openCoverQuotientRestrictIso 𝒰 M k hcompat i).symm (hqc i)
  exact isQuasicoherent_of_openCover_restrict _ 𝒰

/-- The quotient obtained by descending compatible kernels has fixed locally free rank
when its local cokernel models have that rank. -/
lemma openCoverQuotientSheaf_isProjectiveOfRank {q : ℕ}
    (𝒰 : Scheme.OpenCover.{u} X) (M : X.Modules)
    (K : ∀ i, (𝒰.X i).Modules)
    (k : ∀ i, K i ⟶ (restrictFunctor (𝒰.f i)).obj M)
    [∀ i, Mono (k i)]
    (hcompat : OpenCoverSubmoduleCompatible 𝒰 M K k)
    (hrank : ∀ i, IsProjectiveOfRank q (cokernel (k i))) :
    IsProjectiveOfRank q (openCoverQuotientSheaf 𝒰 M k) := by
  apply IsProjectiveOfRank.of_openCover_restrict 𝒰
  intro i
  exact (hrank i).of_iso
    (openCoverQuotientRestrictIso 𝒰 M k hcompat i).symm

namespace PullbackQuotient

variable {S : Scheme.{u}} {q : ℕ} {V : S.Modules} (T : Over S)

/-- The ambient comparison from the canonical pullback on a local object to the
literal restriction of the pullback on the covered object. -/
noncomputable def normalizedAmbientIso {T' : Over S} (g : T' ⟶ T)
    [IsOpenImmersion g.left] :
    (Modules.pullback T'.hom).obj V ≅
      (restrictFunctor g.left).obj ((Modules.pullback T.hom).obj V) :=
  pullbackComparison V g ≪≫ (restrictFunctorIsoPullback g.left).symm.app _

instance overCompLeft_isOpenImmersion {T' T'' : Over S} (g : T' ⟶ T)
    (g' : T'' ⟶ T') [IsOpenImmersion g.left] [IsOpenImmersion g'.left] :
    IsOpenImmersion (g' ≫ g).left := by
  change IsOpenImmersion (g'.left ≫ g.left)
  infer_instance

/-- The normalized ambient comparison is coherent under composition of open
immersions. -/
lemma normalizedAmbientIso_comp {T' T'' : Over S} (g : T' ⟶ T) (g' : T'' ⟶ T')
    [IsOpenImmersion g.left] [IsOpenImmersion g'.left] :
    (normalizedAmbientIso T' g').hom ≫
        (restrictFunctor g'.left).map (normalizedAmbientIso T g).hom =
      (normalizedAmbientIso T (g' ≫ g)).hom ≫
        (restrictFunctorComp g'.left g.left).hom.app
          ((Modules.pullback T.hom).obj V) := by
  dsimp [normalizedAmbientIso]
  simp only [Category.assoc, Functor.map_comp]
  rw [← (restrictFunctorIsoPullback g'.left).inv.naturality_assoc]
  rw [Modules.restrictFunctorIsoPullback_comp_inv_app]
  rw [← Category.assoc, ← Category.assoc]
  rw [comparison_comp_coherence]

/-- The normalized ambient comparison is invariant under equality of morphisms in
the slice, after transporting literal restriction along the induced equality of
underlying scheme morphisms. -/
lemma normalizedAmbientIso_congr {T' : Over S} (g h : T' ⟶ T)
    [IsOpenImmersion g.left] [IsOpenImmersion h.left] (e : g = h) :
    (normalizedAmbientIso (V := V) T g).hom ≫
        (restrictFunctorCongr (congrArg CommaMorphism.left e)).hom.app
          ((Modules.pullback T.hom).obj V) =
      (normalizedAmbientIso T h).hom := by
  subst h
  have hc : (restrictFunctorCongr
      (congrArg CommaMorphism.left (rfl : g = g))).hom.app
        ((Modules.pullback T.hom).obj V) = 𝟙 _ := by
    ext U x
    simp only [restrictFunctorCongr_hom_app_app, eqToHom_refl, op_id]
    change (((Modules.pullback T.hom).obj V).presheaf.map (𝟙 _)) x = x
    rw [((Modules.pullback T.hom).obj V).presheaf.map_id]
    rfl
  rw [hc, Category.comp_id]

/-- The kernel inclusion of a quotient on a member of an open cover, normalized so
that its ambient object is the literal restriction of the global pulled-back sheaf. -/
noncomputable def normalizedKernelι {T' : Over S} (g : T' ⟶ T)
    [IsOpenImmersion g.left] (x : PullbackQuotient q V T') :
    kernel x.π ⟶ (restrictFunctor g.left).obj ((Modules.pullback T.hom).obj V) :=
  kernel.ι x.π ≫ (normalizedAmbientIso T g).hom

instance normalizedKernelι_mono {T' : Over S} (g : T' ⟶ T)
    [IsOpenImmersion g.left] (x : PullbackQuotient q V T') :
    Mono (normalizedKernelι T g x) := by
  dsimp [normalizedKernelι]
  infer_instance

/-- Normalizing the ambient object transports the local quotient's kernel range by
the corresponding ambient isomorphism. -/
lemma range_normalizedKernelι {T' : Over S} (g : T' ⟶ T)
    [IsOpenImmersion g.left] (x : PullbackQuotient q V T') :
    PresheafOfModules.Submodule.range (normalizedKernelι T g x).val =
      x.kernelRangeSubmodule.mapIso
        ((SheafOfModules.forget T'.left.ringCatSheaf).mapIso
          (normalizedAmbientIso T g)) := by
  exact PresheafOfModules.Submodule.range_comp_iso (kernel.ι x.π).val
    ((SheafOfModules.forget T'.left.ringCatSheaf).mapIso
      (normalizedAmbientIso T g))

/-- For an open immersion, pull back a quotient using literal restriction for its
target sheaf. This presentation is equivalent to `PullbackQuotient.pullback` but is
better suited to comparing kernels sectionwise. -/
noncomputable def restrictPullback {T' : Over S} (g : T' ⟶ T)
    [IsOpenImmersion g.left] (x : PullbackQuotient q V T) :
    PullbackQuotient q V T' where
  Q := (restrictFunctor g.left).obj x.Q
  isQuasicoherent := by
    letI : x.Q.IsQuasicoherent := x.isQuasicoherent
    infer_instance
  isProjectiveOfRank := by
    letI : x.Q.IsQuasicoherent := x.isQuasicoherent
    exact (x.isProjectiveOfRank.pullback g.left).of_iso
      ((restrictFunctorIsoPullback g.left).app x.Q).symm
  π := (normalizedAmbientIso T g).hom ≫ (restrictFunctor g.left).map x.π
  epi := by
    letI : Epi x.π := x.epi
    infer_instance

/-- The restriction-normalized pullback represents the same quotient class as the
standard pseudofunctorial pullback. -/
lemma restrictPullback_r_pullback {T' : Over S} (g : T' ⟶ T)
    [IsOpenImmersion g.left] (x : PullbackQuotient q V T) :
    (PullbackQuotient.setoid q V T').r (restrictPullback T g x) (x.pullback g) := by
  refine ⟨(restrictFunctorIsoPullback g.left).app x.Q, ?_⟩
  dsimp [restrictPullback, PullbackQuotient.pullback, normalizedAmbientIso]
  rw [Category.assoc, (restrictFunctorIsoPullback g.left).hom.naturality]
  simp

/-- Equivalent standard and restriction-normalized pullbacks have the same kernel
range in their common canonical ambient sheaf. -/
lemma kernelRangeSubmodule_restrictPullback_eq_pullback {T' : Over S}
    (g : T' ⟶ T) [IsOpenImmersion g.left] (x : PullbackQuotient q V T) :
    (restrictPullback T g x).kernelRangeSubmodule =
      (x.pullback g).kernelRangeSubmodule := by
  have hq : Quotient.mk'' (restrictPullback T g x) = Quotient.mk'' (x.pullback g) :=
    Quotient.sound (restrictPullback_r_pullback T g x)
  exact congrArg (kernelRangeSubmoduleQuotient (q := q) (V := V)) hq

/-- After transporting its ambient object back to literal restriction, the kernel
range of a restriction-normalized pullback is the restriction of the original kernel
inclusion. -/
lemma kernelRangeSubmodule_restrictPullback_mapIso {T' : Over S}
    (g : T' ⟶ T) [IsOpenImmersion g.left] (x : PullbackQuotient q V T) :
    (restrictPullback T g x).kernelRangeSubmodule.mapIso
        ((SheafOfModules.forget T'.left.ringCatSheaf).mapIso
          (normalizedAmbientIso T g)) =
      PresheafOfModules.Submodule.range
        ((restrictFunctor g.left).map (kernel.ι x.π)).val := by
  let F := restrictFunctor g.left
  haveI := Scheme.Modules.restrictFunctor_preservesKernel g.left x.π
  let eK : F.obj (kernel x.π) ≅ kernel (F.map x.π) :=
    PreservesKernel.iso F x.π
  have heK : eK.hom ≫ kernel.ι (F.map x.π) = F.map (kernel.ι x.π) := by
    dsimp [eK]
    simp
  calc
    (restrictPullback T g x).kernelRangeSubmodule.mapIso
        ((SheafOfModules.forget T'.left.ringCatSheaf).mapIso
          (normalizedAmbientIso T g)) =
      PresheafOfModules.Submodule.range (kernel.ι (F.map x.π)).val :=
        SheafOfModules.kernelRange_comp_iso (F.map x.π) (normalizedAmbientIso T g)
    _ = PresheafOfModules.Submodule.range
        ((restrictFunctor g.left).map (kernel.ι x.π)).val :=
      (PresheafOfModules.Submodule.range_eq_of_iso
        (F.map (kernel.ι x.π)).val (kernel.ι (F.map x.π)).val
        ((SheafOfModules.forget T'.left.ringCatSheaf).mapIso eK)
        (congrArg SheafOfModules.Hom.val heK)).symm

/-- Restricting a normalized kernel along a second open immersion has the same
pointwise range as normalizing the kernel of the pulled-back quotient along the
composite, after the coherent comparison from composite to iterated restriction. -/
lemma range_restrict_normalizedKernelι {T' T'' : Over S} (g : T' ⟶ T)
    (g' : T'' ⟶ T') [IsOpenImmersion g.left] [IsOpenImmersion g'.left]
    (x : PullbackQuotient q V T') :
    PresheafOfModules.Submodule.range
        ((restrictFunctor g'.left).map (normalizedKernelι T g x)).val =
      PresheafOfModules.Submodule.range
        (normalizedKernelι T (g' ≫ g) (x.pullback g') ≫
          (restrictFunctorComp g'.left g.left).hom.app
            ((Modules.pullback T.hom).obj V)).val := by
  let F := restrictFunctor g'.left
  let eA' := (SheafOfModules.forget T''.left.ringCatSheaf).mapIso
    (normalizedAmbientIso (V := V) T' g')
  let eFA := (SheafOfModules.forget T''.left.ringCatSheaf).mapIso
    (F.mapIso (normalizedAmbientIso (V := V) T g))
  let eA := (SheafOfModules.forget T''.left.ringCatSheaf).mapIso
    (normalizedAmbientIso (V := V) T (g' ≫ g))
  let eC := (SheafOfModules.forget T''.left.ringCatSheaf).mapIso
    ((restrictFunctorComp g'.left g.left).app
      ((Modules.pullback T.hom).obj V))
  change _ = PresheafOfModules.Submodule.range
    ((normalizedKernelι T (g' ≫ g) (x.pullback g')).val ≫ eC.hom)
  have hE : eA'.trans eFA = eA.trans eC := by
    apply Iso.ext
    exact congrArg SheafOfModules.Hom.val
      (normalizedAmbientIso_comp T g g')
  have hm : (F.map (normalizedKernelι T g x)).val =
      (F.map (kernel.ι x.π)).val ≫ eFA.hom := by
    dsimp [normalizedKernelι, F, eFA]
    rw [Functor.map_comp]
    rfl
  have hnorm : PresheafOfModules.Submodule.range
      ((normalizedKernelι T (g' ≫ g) (x.pullback g')).val ≫ eC.hom) =
      ((x.pullback g').kernelRangeSubmodule.mapIso eA).mapIso eC := by
    calc
      _ = (PresheafOfModules.Submodule.range
          (normalizedKernelι T (g' ≫ g) (x.pullback g')).val).mapIso eC :=
        PresheafOfModules.Submodule.range_comp_iso _ _
      _ = _ := congrArg (fun N ↦ N.mapIso eC)
        (range_normalizedKernelι T (g' ≫ g) (x.pullback g'))
  calc
    _ = (PresheafOfModules.Submodule.range
          (F.map (kernel.ι x.π)).val).mapIso eFA := by
      change PresheafOfModules.Submodule.range
        (F.map (normalizedKernelι T g x)).val = _
      rw [hm]
      exact PresheafOfModules.Submodule.range_comp_iso _ _
    _ = ((restrictPullback T' g' x).kernelRangeSubmodule.mapIso eA').mapIso eFA :=
      congrArg (fun N ↦ N.mapIso eFA)
        (kernelRangeSubmodule_restrictPullback_mapIso T' g' x).symm
    _ = (restrictPullback T' g' x).kernelRangeSubmodule.mapIso (eA'.trans eFA) :=
      PresheafOfModules.Submodule.mapIso_trans _ _ _
    _ = (restrictPullback T' g' x).kernelRangeSubmodule.mapIso (eA.trans eC) :=
      congrArg _ hE
    _ = ((restrictPullback T' g' x).kernelRangeSubmodule.mapIso eA).mapIso eC :=
      (PresheafOfModules.Submodule.mapIso_trans _ _ _).symm
    _ = ((x.pullback g').kernelRangeSubmodule.mapIso eA).mapIso eC :=
      congrArg (fun N ↦ (N.mapIso eA).mapIso eC)
        (kernelRangeSubmodule_restrictPullback_eq_pullback T' g' x)
    _ = _ := hnorm.symm

/-- The cokernel of the normalized local kernel inclusion is canonically the original
local quotient sheaf. -/
noncomputable def normalizedKernelCokernelIso {T' : Over S} (g : T' ⟶ T)
    [IsOpenImmersion g.left] (x : PullbackQuotient q V T') :
    cokernel (normalizedKernelι T g x) ≅ x.Q := by
  letI : Epi x.π := x.epi
  exact cokernel.mapIso (f := normalizedKernelι T g x) (kernel.ι x.π)
      (Iso.refl _) (normalizedAmbientIso T g).symm (by
        dsimp [normalizedKernelι]
        simp) ≪≫
    cokernelKernelIsoOfEpi x.π

/-- The normalized-kernel cokernel isomorphism identifies its cokernel projection
with the original quotient map after undoing ambient normalization. -/
@[reassoc]
lemma cokernel_π_comp_normalizedKernelCokernelIso_hom {T' : Over S}
    (g : T' ⟶ T) [IsOpenImmersion g.left] (x : PullbackQuotient q V T') :
    cokernel.π (normalizedKernelι T g x) ≫
      (normalizedKernelCokernelIso T g x).hom =
    (normalizedAmbientIso T g).inv ≫ x.π := by
  dsimp [normalizedKernelCokernelIso]
  rw [cokernel.mapIso_hom, ← Category.assoc, cokernel.π_desc]
  rw [Category.assoc, cokernel_π_comp_cokernelKernelIsoOfEpi_hom, Iso.symm_hom]

/-- The cokernel of a normalized local kernel remains quasicoherent. -/
lemma normalizedKernelCokernel_isQuasicoherent {T' : Over S} (g : T' ⟶ T)
    [IsOpenImmersion g.left] (x : PullbackQuotient q V T') :
    (cokernel (normalizedKernelι T g x)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent T'.left.ringCatSheaf).prop_of_iso
    (normalizedKernelCokernelIso T g x).symm x.isQuasicoherent

/-- The cokernel of a normalized local kernel has the rank of the original quotient. -/
lemma normalizedKernelCokernel_isProjectiveOfRank {T' : Over S} (g : T' ⟶ T)
    [IsOpenImmersion g.left] (x : PullbackQuotient q V T') :
    IsProjectiveOfRank q (cokernel (normalizedKernelι T g x)) :=
  x.isProjectiveOfRank.of_iso (normalizedKernelCokernelIso T g x).symm

/-- Effective open-cover descent constructor for a relative quotient: compatible local
kernels in the restrictions of the pulled-back ambient sheaf determine a global
quasicoherent rank-`q` quotient. -/
noncomputable def ofOpenCoverKernels
    (𝒰 : Scheme.OpenCover.{u} T.left)
    (K : ∀ i, (𝒰.X i).Modules)
    (k : ∀ i, K i ⟶ (restrictFunctor (𝒰.f i)).obj
      ((Modules.pullback T.hom).obj V))
    [∀ i, Mono (k i)]
    (hcompat : OpenCoverSubmoduleCompatible 𝒰 ((Modules.pullback T.hom).obj V) K k)
    [hqc : ∀ i, (cokernel (k i)).IsQuasicoherent]
    (hrank : ∀ i, IsProjectiveOfRank q (cokernel (k i))) :
    PullbackQuotient q V T where
  Q := openCoverQuotientSheaf 𝒰 ((Modules.pullback T.hom).obj V) k
  isQuasicoherent :=
    openCoverQuotientSheaf_isQuasicoherent 𝒰 ((Modules.pullback T.hom).obj V) K k hcompat
  isProjectiveOfRank :=
    openCoverQuotientSheaf_isProjectiveOfRank 𝒰 ((Modules.pullback T.hom).obj V) K k
      hcompat hrank
  π := openCoverQuotientMap 𝒰 ((Modules.pullback T.hom).obj V) k
  epi := by infer_instance

end PullbackQuotient

end AlgebraicGeometry.Scheme.Modules

end ThmGrassmannianProjectiveRelative

section ThmGrassmannianProjectiveRelative

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} (T : Over S) (𝒰 : Scheme.OpenCover.{u} T.left)

/-- A member of an open cover of the source of `T`, equipped with its induced map to
the fixed base scheme. -/
noncomputable def openCoverObjectOver (i : 𝒰.I₀) : Over S :=
  Over.mk (𝒰.f i ≫ T.hom)

/-- The morphism over the base from a member of an open cover to the covered object. -/
noncomputable def openCoverMapOver (i : 𝒰.I₀) : openCoverObjectOver T 𝒰 i ⟶ T :=
  Over.homMk (𝒰.f i) rfl

@[simp]
lemma openCoverMapOver_left (i : 𝒰.I₀) :
    (openCoverMapOver T 𝒰 i).left = 𝒰.f i := rfl

instance openCoverMapOver_isOpenImmersion (i : 𝒰.I₀) :
    IsOpenImmersion (openCoverMapOver T 𝒰 i).left := by
  change IsOpenImmersion (𝒰.f i)
  infer_instance

/-- The part of the `j`th cover member lying over an open `W` of the covered scheme. -/
noncomputable def openCoverOverlapObjectOver (j : 𝒰.I₀) (W : T.left.Opens) : Over S :=
  Over.mk ((𝒰.f j ⁻¹ᵁ W).ι ≫ 𝒰.f j ≫ T.hom)

/-- The overlap object maps canonically to the `j`th cover member. -/
noncomputable def openCoverOverlapToRight (j : 𝒰.I₀) (W : T.left.Opens) :
    openCoverOverlapObjectOver T 𝒰 j W ⟶ openCoverObjectOver T 𝒰 j :=
  Over.homMk ((𝒰.f j ⁻¹ᵁ W).ι) rfl

instance openCoverOverlapToRight_isOpenImmersion (j : 𝒰.I₀) (W : T.left.Opens) :
    IsOpenImmersion (openCoverOverlapToRight T 𝒰 j W).left := by
  change IsOpenImmersion ((𝒰.f j ⁻¹ᵁ W).ι)
  infer_instance

/-- If `W` is contained in the range of the `i`th cover member, the overlap cut out in
the `j`th member maps canonically to the `i`th member as well. -/
noncomputable def openCoverOverlapToLeft (i j : 𝒰.I₀) (W : T.left.Opens)
    (hW : W ≤ (𝒰.f i).opensRange) :
    openCoverOverlapObjectOver T 𝒰 j W ⟶ openCoverObjectOver T 𝒰 i := by
  dsimp [openCoverOverlapObjectOver, openCoverObjectOver]
  refine Over.homMk
    (IsOpenImmersion.lift (𝒰.f i) ((𝒰.f j ⁻¹ᵁ W).ι ≫ 𝒰.f j) (by
      rintro x ⟨y, rfl⟩
      apply hW
      exact y.property)) ?_
  change _ ≫ (𝒰.f i ≫ T.hom) =
    (((𝒰.f j ⁻¹ᵁ W).ι ≫ 𝒰.f j) ≫ T.hom)
  rw [← Category.assoc, IsOpenImmersion.lift_fac]

instance openCoverOverlapToLeft_isOpenImmersion (i j : 𝒰.I₀) (W : T.left.Opens)
    (hW : W ≤ (𝒰.f i).opensRange) :
    IsOpenImmersion (openCoverOverlapToLeft T 𝒰 i j W hW).left := by
  change IsOpenImmersion (IsOpenImmersion.lift (𝒰.f i)
    ((𝒰.f j ⁻¹ᵁ W).ι ≫ 𝒰.f j) (by
      rintro x ⟨y, rfl⟩
      apply hW
      exact y.property))
  infer_instance

/-- Both overlap morphisms have the same composite to the covered object. -/
lemma openCoverOverlap_maps_equal (i j : 𝒰.I₀) (W : T.left.Opens)
    (hW : W ≤ (𝒰.f i).opensRange) :
    openCoverOverlapToLeft T 𝒰 i j W hW ≫ openCoverMapOver T 𝒰 i =
      openCoverOverlapToRight T 𝒰 j W ≫ openCoverMapOver T 𝒰 j := by
  dsimp [openCoverOverlapToLeft, openCoverOverlapToRight,
    openCoverMapOver, openCoverObjectOver, openCoverOverlapObjectOver]
  ext
  exact IsOpenImmersion.lift_fac _ _ _

/-- The image of the canonical overlap in the left chart lies over the chosen open
of the covered scheme. -/
lemma openCoverOverlapToLeft_image_top_le_preimage (i j : 𝒰.I₀)
    (W : T.left.Opens) (hW : W ≤ (𝒰.f i).opensRange) :
    (openCoverOverlapToLeft T 𝒰 i j W hW).left ''ᵁ
        (⊤ : (openCoverOverlapObjectOver T 𝒰 j W).left.Opens) ≤
      (openCoverMapOver T 𝒰 i).left ⁻¹ᵁ W := by
  let gᵢ := openCoverOverlapToLeft T 𝒰 i j W hW
  let gⱼ := openCoverOverlapToRight T 𝒰 j W
  let fᵢ := openCoverMapOver T 𝒰 i
  let fⱼ := openCoverMapOver T 𝒰 j
  rintro y ⟨a, -, rfl⟩
  change fᵢ.left.base (gᵢ.left.base a) ∈ W
  have he := congrArg (fun k ↦ k.left.base a)
    (openCoverOverlap_maps_equal T 𝒰 i j W hW)
  change fᵢ.left.base (gᵢ.left.base a) =
    fⱼ.left.base (gⱼ.left.base a) at he
  rw [he]
  dsimp [fⱼ, gⱼ, openCoverOverlapToRight, openCoverMapOver,
    openCoverOverlapObjectOver, openCoverObjectOver]
  exact a.property

/-- The top open of the canonical overlap has image exactly the inverse image of
the chosen open in the right chart. -/
lemma openCoverOverlapToRight_image_top (j : 𝒰.I₀) (W : T.left.Opens) :
    (openCoverOverlapToRight T 𝒰 j W).left ''ᵁ
        (⊤ : (openCoverOverlapObjectOver T 𝒰 j W).left.Opens) =
      (openCoverMapOver T 𝒰 j).left ⁻¹ᵁ W := by
  dsimp [openCoverOverlapToRight, openCoverMapOver,
    openCoverOverlapObjectOver, openCoverObjectOver]
  exact Scheme.Opens.ι_image_top _

/-- The two iterated literal restrictions of a module to a canonical overlap are
canonically isomorphic. -/
noncomputable def openCoverOverlapRestrictionIso (M : T.left.Modules)
    (i j : 𝒰.I₀) (W : T.left.Opens) (hW : W ≤ (𝒰.f i).opensRange) :
    (Modules.restrictFunctor (openCoverOverlapToLeft T 𝒰 i j W hW).left).obj
        ((Modules.restrictFunctor (𝒰.f i)).obj M) ≅
      (Modules.restrictFunctor (openCoverOverlapToRight T 𝒰 j W).left).obj
        ((Modules.restrictFunctor (𝒰.f j)).obj M) := by
  let gᵢ := openCoverOverlapToLeft T 𝒰 i j W hW
  let gⱼ := openCoverOverlapToRight T 𝒰 j W
  let fᵢ := openCoverMapOver T 𝒰 i
  let fⱼ := openCoverMapOver T 𝒰 j
  have hcomp : gᵢ.left ≫ fᵢ.left = gⱼ.left ≫ fⱼ.left := by
    exact congrArg CommaMorphism.left
      (openCoverOverlap_maps_equal T 𝒰 i j W hW)
  exact ((Modules.restrictFunctorComp gᵢ.left fᵢ.left).app M).symm ≪≫
    (Modules.restrictFunctorCongr hcomp).app M ≪≫
      (Modules.restrictFunctorComp gⱼ.left fⱼ.left).app M

/-- The component of the canonical overlap restriction isomorphism is the
composite of the two restriction-coherence maps and equality transport. -/
lemma openCoverOverlapRestrictionIso_hom_app (M : T.left.Modules)
    (i j : 𝒰.I₀) (W : T.left.Opens) (hW : W ≤ (𝒰.f i).opensRange)
    (U : (openCoverOverlapObjectOver T 𝒰 j W).left.Opens) :
    (openCoverOverlapRestrictionIso T 𝒰 M i j W hW).hom.app U =
      ((Modules.restrictFunctorComp
        (openCoverOverlapToLeft T 𝒰 i j W hW).left
        (openCoverMapOver T 𝒰 i).left).inv.app M).app U ≫
      ((Modules.restrictFunctorCongr (congrArg CommaMorphism.left
        (openCoverOverlap_maps_equal T 𝒰 i j W hW))).hom.app M).app U ≫
      ((Modules.restrictFunctorComp
        (openCoverOverlapToRight T 𝒰 j W).left
        (openCoverMapOver T 𝒰 j).left).hom.app M).app U := rfl

/-- The canonical overlap comparison carries the restriction of a global section
through the left chart to the same restriction through the right chart. -/
lemma openCoverOverlapRestrictionIso_hom_app_restrict (M : T.left.Modules)
    (i j : 𝒰.I₀) (W : T.left.Opens) (hW : W ≤ (𝒰.f i).opensRange)
    (s : M.presheaf.obj (Opposite.op W)) :
    let O := openCoverOverlapObjectOver T 𝒰 j W
    let fᵢ := openCoverMapOver T 𝒰 i
    let fⱼ := openCoverMapOver T 𝒰 j
    let E := openCoverOverlapRestrictionIso T 𝒰 M i j W hW
    (((Modules.restrictFunctor fⱼ.left).obj M).presheaf.map
      (eqToHom (openCoverOverlapToRight_image_top T 𝒰 j W).symm).op
      (E.hom.app (⊤ : O.left.Opens)
      (((Modules.restrictFunctor fᵢ.left).obj M).presheaf.map
          (homOfLE (openCoverOverlapToLeft_image_top_le_preimage
            T 𝒰 i j W hW)).op
          (M.presheaf.map (homOfLE (fᵢ.left.image_preimage_le W)).op s)))) =
      M.presheaf.map (homOfLE (fⱼ.left.image_preimage_le W)).op s := by
  dsimp only
  rw [openCoverOverlapRestrictionIso_hom_app T 𝒰 M i j W hW]
  simp only [Modules.restrictFunctorComp_inv_app_app,
    Modules.restrictFunctorComp_hom_app_app,
    Modules.restrictFunctorCongr_hom_app_app, Modules.restrict_map]
  change M.presheaf.map _ (M.presheaf.map _ (M.presheaf.map _
    (M.presheaf.map _ (M.presheaf.map _ (M.presheaf.map _ s))))) =
      M.presheaf.map _ s
  rw [← M.presheaf.map_comp_apply, ← M.presheaf.map_comp_apply,
    ← M.presheaf.map_comp_apply, ← M.presheaf.map_comp_apply,
    ← M.presheaf.map_comp_apply]
  rfl

/-- Composing the left chart's coherence isomorphism with the canonical overlap
comparison cancels that coherence and leaves equality transport followed by the
right chart's coherence isomorphism. -/
lemma restrictFunctorComp_trans_openCoverOverlapRestrictionIso
    (M : T.left.Modules) (i j : 𝒰.I₀) (W : T.left.Opens)
    (hW : W ≤ (𝒰.f i).opensRange) :
    ((Modules.restrictFunctorComp
      (openCoverOverlapToLeft T 𝒰 i j W hW).left
      (openCoverMapOver T 𝒰 i).left).app M).trans
        (openCoverOverlapRestrictionIso T 𝒰 M i j W hW) =
      ((Modules.restrictFunctorCongr (congrArg CommaMorphism.left
        (openCoverOverlap_maps_equal T 𝒰 i j W hW))).app M).trans
        ((Modules.restrictFunctorComp
          (openCoverOverlapToRight T 𝒰 j W).left
          (openCoverMapOver T 𝒰 j).left).app M) := by
  apply Iso.ext
  let C := Modules.restrictFunctorComp
    (openCoverOverlapToLeft T 𝒰 i j W hW).left
    (openCoverMapOver T 𝒰 i).left
  let D := Modules.restrictFunctorComp
    (openCoverOverlapToRight T 𝒰 j W).left
    (openCoverMapOver T 𝒰 j).left
  let R := Modules.restrictFunctorCongr (congrArg CommaMorphism.left
    (openCoverOverlap_maps_equal T 𝒰 i j W hW))
  change C.hom.app M ≫ C.inv.app M ≫ R.hom.app M ≫ D.hom.app M =
    R.hom.app M ≫ D.hom.app M
  rw [C.hom_inv_id_app_assoc]

/-- Normalization along the left composite followed by the canonical overlap
comparison agrees with normalization along the right composite. -/
lemma normalizedAmbientIso_trans_openCoverOverlapRestrictionIso
    (V : S.Modules) (i j : 𝒰.I₀) (W : T.left.Opens)
    (hW : W ≤ (𝒰.f i).opensRange) :
    ((Modules.PullbackQuotient.normalizedAmbientIso (V := V) T
      (openCoverOverlapToLeft T 𝒰 i j W hW ≫ openCoverMapOver T 𝒰 i)).trans
        ((Modules.restrictFunctorComp
          (openCoverOverlapToLeft T 𝒰 i j W hW).left
          (openCoverMapOver T 𝒰 i).left).app
            ((Modules.pullback T.hom).obj V))).trans
      (openCoverOverlapRestrictionIso T 𝒰 ((Modules.pullback T.hom).obj V)
        i j W hW) =
    (Modules.PullbackQuotient.normalizedAmbientIso (V := V) T
      (openCoverOverlapToRight T 𝒰 j W ≫ openCoverMapOver T 𝒰 j)).trans
        ((Modules.restrictFunctorComp
          (openCoverOverlapToRight T 𝒰 j W).left
          (openCoverMapOver T 𝒰 j).left).app
            ((Modules.pullback T.hom).obj V)) := by
  let gᵢ := openCoverOverlapToLeft T 𝒰 i j W hW
  let gⱼ := openCoverOverlapToRight T 𝒰 j W
  let fᵢ := openCoverMapOver T 𝒰 i
  let fⱼ := openCoverMapOver T 𝒰 j
  let Cᵢ := Modules.restrictFunctorComp gᵢ.left fᵢ.left
  let Cⱼ := Modules.restrictFunctorComp gⱼ.left fⱼ.left
  let Aᵢ := Modules.PullbackQuotient.normalizedAmbientIso (V := V) T (gᵢ ≫ fᵢ)
  let Aⱼ := Modules.PullbackQuotient.normalizedAmbientIso (V := V) T (gⱼ ≫ fⱼ)
  let E := openCoverOverlapRestrictionIso T 𝒰 ((Modules.pullback T.hom).obj V)
    i j W hW
  let R := Modules.restrictFunctorCongr (congrArg CommaMorphism.left
    (openCoverOverlap_maps_equal T 𝒰 i j W hW))
  have hAR : Aᵢ.trans (R.app ((Modules.pullback T.hom).obj V)) = Aⱼ := by
    apply Iso.ext
    exact Modules.PullbackQuotient.normalizedAmbientIso_congr T
      (gᵢ ≫ fᵢ) (gⱼ ≫ fⱼ)
        (openCoverOverlap_maps_equal T 𝒰 i j W hW)
  have hcancel : (Cᵢ.app ((Modules.pullback T.hom).obj V)).trans E =
      (R.app ((Modules.pullback T.hom).obj V)).trans
        (Cⱼ.app ((Modules.pullback T.hom).obj V)) :=
    restrictFunctorComp_trans_openCoverOverlapRestrictionIso
      T 𝒰 ((Modules.pullback T.hom).obj V) i j W hW
  have h1 := Iso.trans_assoc Aᵢ (Cᵢ.app ((Modules.pullback T.hom).obj V)) E
  have h2 : Aᵢ.trans ((Cᵢ.app ((Modules.pullback T.hom).obj V)).trans E) =
      Aᵢ.trans ((R.app ((Modules.pullback T.hom).obj V)).trans
        (Cⱼ.app ((Modules.pullback T.hom).obj V))) :=
    congrArg (fun z : _ ≅ _ ↦ Aᵢ.trans z) hcancel
  have h3 := (Iso.trans_assoc Aᵢ (R.app ((Modules.pullback T.hom).obj V))
    (Cⱼ.app ((Modules.pullback T.hom).obj V))).symm
  have h4 : (Aᵢ.trans (R.app ((Modules.pullback T.hom).obj V))).trans
      (Cⱼ.app ((Modules.pullback T.hom).obj V)) =
      Aⱼ.trans (Cⱼ.app ((Modules.pullback T.hom).obj V)) :=
    congrArg (fun z : _ ≅ _ ↦ z.trans
      (Cⱼ.app ((Modules.pullback T.hom).obj V))) hAR
  exact h1.trans (h2.trans (h3.trans h4))

/-- Equal kernel ranges of quotient pullbacks to a canonical overlap give equal
ranges for the literal restrictions of the two normalized kernel inclusions, after
transport by the canonical overlap ambient isomorphism. -/
lemma normalizedKernelRange_overlap {q : ℕ} (V : S.Modules)
    (x : ∀ i, Modules.PullbackQuotient q V (openCoverObjectOver T 𝒰 i))
    (i j : 𝒰.I₀) (W : T.left.Opens) (hW : W ≤ (𝒰.f i).opensRange)
    (hker : ((x i).pullback (openCoverOverlapToLeft T 𝒰 i j W hW)).kernelRangeSubmodule =
      ((x j).pullback (openCoverOverlapToRight T 𝒰 j W)).kernelRangeSubmodule) :
    (PresheafOfModules.Submodule.range
      ((Modules.restrictFunctor (openCoverOverlapToLeft T 𝒰 i j W hW).left).map
        (Modules.PullbackQuotient.normalizedKernelι T (openCoverMapOver T 𝒰 i)
          (x i))).val).mapIso
        ((SheafOfModules.forget
          (openCoverOverlapObjectOver T 𝒰 j W).left.ringCatSheaf).mapIso
          (openCoverOverlapRestrictionIso T 𝒰 ((Modules.pullback T.hom).obj V)
            i j W hW)) =
      PresheafOfModules.Submodule.range
        ((Modules.restrictFunctor (openCoverOverlapToRight T 𝒰 j W).left).map
          (Modules.PullbackQuotient.normalizedKernelι T (openCoverMapOver T 𝒰 j)
            (x j))).val := by
  let O := openCoverOverlapObjectOver T 𝒰 j W
  let gᵢ := openCoverOverlapToLeft T 𝒰 i j W hW
  let gⱼ := openCoverOverlapToRight T 𝒰 j W
  let fᵢ := openCoverMapOver T 𝒰 i
  let fⱼ := openCoverMapOver T 𝒰 j
  let Cᵢ := Modules.restrictFunctorComp gᵢ.left fᵢ.left
  let Cⱼ := Modules.restrictFunctorComp gⱼ.left fⱼ.left
  let Aᵢ := Modules.PullbackQuotient.normalizedAmbientIso (V := V) T (gᵢ ≫ fᵢ)
  let Aⱼ := Modules.PullbackQuotient.normalizedAmbientIso (V := V) T (gⱼ ≫ fⱼ)
  let E := openCoverOverlapRestrictionIso T 𝒰 ((Modules.pullback T.hom).obj V) i j W hW
  let F := SheafOfModules.forget O.left.ringCatSheaf
  let aᵢ := F.mapIso Aᵢ
  let aⱼ := F.mapIso Aⱼ
  let cᵢ := F.mapIso (Cᵢ.app ((Modules.pullback T.hom).obj V))
  let cⱼ := F.mapIso (Cⱼ.app ((Modules.pullback T.hom).obj V))
  let e := F.mapIso E
  let Nᵢ := ((x i).pullback gᵢ).kernelRangeSubmodule
  let Nⱼ := ((x j).pullback gⱼ).kernelRangeSubmodule
  have hN : Nᵢ = Nⱼ := hker
  have hIso : (aᵢ.trans cᵢ).trans e = aⱼ.trans cⱼ := by
    apply Iso.ext
    exact congrArg SheafOfModules.Hom.val (Iso.ext_iff.mp
      (normalizedAmbientIso_trans_openCoverOverlapRestrictionIso T 𝒰 V i j W hW))
  have htransport : Nᵢ.mapIso ((aᵢ.trans cᵢ).trans e) =
      Nⱼ.mapIso (aⱼ.trans cⱼ) := by
    exact (congrArg (fun z : _ ≅ _ ↦ Nᵢ.mapIso z) hIso).trans
      (congrArg (fun N ↦ N.mapIso (aⱼ.trans cⱼ)) hN)
  have hrᵢ := Modules.PullbackQuotient.range_restrict_normalizedKernelι
    T fᵢ gᵢ (x i)
  have hrⱼ := Modules.PullbackQuotient.range_restrict_normalizedKernelι
    T fⱼ gⱼ (x j)
  have hnᵢ := Modules.PullbackQuotient.range_normalizedKernelι
    T (gᵢ ≫ fᵢ) ((x i).pullback gᵢ)
  have hnⱼ := Modules.PullbackQuotient.range_normalizedKernelι
    T (gⱼ ≫ fⱼ) ((x j).pullback gⱼ)
  have hcᵢ := PresheafOfModules.Submodule.range_comp_iso
    (Modules.PullbackQuotient.normalizedKernelι T (gᵢ ≫ fᵢ)
      ((x i).pullback gᵢ)).val cᵢ
  have hcⱼ := PresheafOfModules.Submodule.range_comp_iso
    (Modules.PullbackQuotient.normalizedKernelι T (gⱼ ≫ fⱼ)
      ((x j).pullback gⱼ)).val cⱼ
  have hmᵢ := PresheafOfModules.Submodule.mapIso_trans Nᵢ aᵢ cᵢ
  have hmᵢ' := PresheafOfModules.Submodule.mapIso_trans Nᵢ (aᵢ.trans cᵢ) e
  have hmⱼ := PresheafOfModules.Submodule.mapIso_trans Nⱼ aⱼ cⱼ
  have hleft : (PresheafOfModules.Submodule.range
      ((Modules.restrictFunctor gᵢ.left).map
        (Modules.PullbackQuotient.normalizedKernelι T fᵢ (x i))).val).mapIso e =
      Nᵢ.mapIso ((aᵢ.trans cᵢ).trans e) := by
    calc
      _ = (PresheafOfModules.Submodule.range
          (Modules.PullbackQuotient.normalizedKernelι T (gᵢ ≫ fᵢ)
            ((x i).pullback gᵢ) ≫ Cᵢ.hom.app
              ((Modules.pullback T.hom).obj V)).val).mapIso e :=
        congrArg (fun N ↦ N.mapIso e) hrᵢ
      _ = ((PresheafOfModules.Submodule.range
          (Modules.PullbackQuotient.normalizedKernelι T (gᵢ ≫ fᵢ)
            ((x i).pullback gᵢ)).val).mapIso cᵢ).mapIso e :=
        congrArg (fun N ↦ N.mapIso e) hcᵢ
      _ = ((Nᵢ.mapIso aᵢ).mapIso cᵢ).mapIso e :=
        congrArg (fun N ↦ (N.mapIso cᵢ).mapIso e) hnᵢ
      _ = (Nᵢ.mapIso (aᵢ.trans cᵢ)).mapIso e :=
        congrArg (fun N ↦ N.mapIso e) hmᵢ
      _ = Nᵢ.mapIso ((aᵢ.trans cᵢ).trans e) := hmᵢ'
  have hright : Nⱼ.mapIso (aⱼ.trans cⱼ) =
      PresheafOfModules.Submodule.range
        ((Modules.restrictFunctor gⱼ.left).map
          (Modules.PullbackQuotient.normalizedKernelι T fⱼ (x j))).val := by
    have hj2 : (Nⱼ.mapIso aⱼ).mapIso cⱼ =
        (PresheafOfModules.Submodule.range
          (Modules.PullbackQuotient.normalizedKernelι T (gⱼ ≫ fⱼ)
            ((x j).pullback gⱼ)).val).mapIso cⱼ :=
      congrArg (fun N ↦ N.mapIso cⱼ) hnⱼ.symm
    have hj3 : (PresheafOfModules.Submodule.range
        (Modules.PullbackQuotient.normalizedKernelι T (gⱼ ≫ fⱼ)
          ((x j).pullback gⱼ)).val).mapIso cⱼ =
        PresheafOfModules.Submodule.range
          (Modules.PullbackQuotient.normalizedKernelι T (gⱼ ≫ fⱼ)
            ((x j).pullback gⱼ) ≫ Cⱼ.hom.app
              ((Modules.pullback T.hom).obj V)).val := hcⱼ.symm
    exact hmⱼ.symm.trans (hj2.trans (hj3.trans hrⱼ.symm))
  exact hleft.trans (htransport.trans hright)

/-- A compatible family of relative Grassmannian points has equal pullbacks to every
canonical overlap object cut out by an open of the covered scheme. -/
lemma grassmannianCompatibleFamily_overlap {q : ℕ} (V : S.Modules)
    (z : ∀ i, (Modules.grassmannianOverFunctor q V).obj
      (Opposite.op (openCoverObjectOver T 𝒰 i)))
    (hz : Presieve.Arrows.Compatible (Modules.grassmannianOverFunctor q V)
      (fun i ↦ openCoverMapOver T 𝒰 i) z)
    (i j : 𝒰.I₀) (W : T.left.Opens) (hW : W ≤ (𝒰.f i).opensRange) :
    (Modules.grassmannianOverFunctor q V).map
        (openCoverOverlapToLeft T 𝒰 i j W hW).op (z i) =
      (Modules.grassmannianOverFunctor q V).map
        (openCoverOverlapToRight T 𝒰 j W).op (z j) :=
  hz i j (openCoverOverlapObjectOver T 𝒰 j W)
    (openCoverOverlapToLeft T 𝒰 i j W hW)
    (openCoverOverlapToRight T 𝒰 j W)
    (openCoverOverlap_maps_equal T 𝒰 i j W hW)

/-- After choosing quotient presentations for a compatible family, the kernels of
their pullbacks to a canonical overlap have equal pointwise ranges. -/
lemma grassmannianCompatibleFamily_rep_kernelRange_overlap {q : ℕ} (V : S.Modules)
    (z : ∀ i, (Modules.grassmannianOverFunctor q V).obj
      (Opposite.op (openCoverObjectOver T 𝒰 i)))
    (hz : Presieve.Arrows.Compatible (Modules.grassmannianOverFunctor q V)
      (fun i ↦ openCoverMapOver T 𝒰 i) z)
    (x : ∀ i, Modules.PullbackQuotient q V (openCoverObjectOver T 𝒰 i))
    (hx : ∀ i, Quotient.mk'' (x i) = z i)
    (i j : 𝒰.I₀) (W : T.left.Opens) (hW : W ≤ (𝒰.f i).opensRange) :
    ((x i).pullback (openCoverOverlapToLeft T 𝒰 i j W hW)).kernelRangeSubmodule =
      ((x j).pullback (openCoverOverlapToRight T 𝒰 j W)).kernelRangeSubmodule := by
  have hover := grassmannianCompatibleFamily_overlap T 𝒰 V z hz i j W hW
  rw [← hx i, ← hx j] at hover
  apply congrArg (Modules.PullbackQuotient.kernelRangeSubmoduleQuotient
    (q := q) (V := V)) at hover
  exact hover

/-- The normalized local kernels attached to representatives of a compatible family
have equal literal restricted ranges on every canonical overlap, after transport by
the canonical overlap ambient isomorphism. -/
lemma grassmannianCompatibleFamily_normalizedKernelRange_overlap {q : ℕ}
    (V : S.Modules)
    (z : ∀ i, (Modules.grassmannianOverFunctor q V).obj
      (Opposite.op (openCoverObjectOver T 𝒰 i)))
    (hz : Presieve.Arrows.Compatible (Modules.grassmannianOverFunctor q V)
      (fun i ↦ openCoverMapOver T 𝒰 i) z)
    (x : ∀ i, Modules.PullbackQuotient q V (openCoverObjectOver T 𝒰 i))
    (hx : ∀ i, Quotient.mk'' (x i) = z i)
    (i j : 𝒰.I₀) (W : T.left.Opens) (hW : W ≤ (𝒰.f i).opensRange) :
    (PresheafOfModules.Submodule.range
      ((Modules.restrictFunctor (openCoverOverlapToLeft T 𝒰 i j W hW).left).map
        (Modules.PullbackQuotient.normalizedKernelι T (openCoverMapOver T 𝒰 i)
          (x i))).val).mapIso
        ((SheafOfModules.forget
          (openCoverOverlapObjectOver T 𝒰 j W).left.ringCatSheaf).mapIso
          (openCoverOverlapRestrictionIso T 𝒰 ((Modules.pullback T.hom).obj V)
            i j W hW)) =
      PresheafOfModules.Submodule.range
        ((Modules.restrictFunctor (openCoverOverlapToRight T 𝒰 j W).left).map
          (Modules.PullbackQuotient.normalizedKernelι T (openCoverMapOver T 𝒰 j)
            (x j))).val :=
  normalizedKernelRange_overlap T 𝒰 V x i j W hW
    (grassmannianCompatibleFamily_rep_kernelRange_overlap T 𝒰 V z hz x hx i j W hW)

set_option maxSynthPendingDepth 10 in
/-- The normalized kernels of representatives of a compatible relative
Grassmannian family satisfy effective open-cover compatibility. -/
lemma grassmannianCompatibleFamily_normalizedKernels_compatible {q : ℕ}
    (V : S.Modules)
    (z : ∀ i, (Modules.grassmannianOverFunctor q V).obj
      (Opposite.op (openCoverObjectOver T 𝒰 i)))
    (hz : Presieve.Arrows.Compatible (Modules.grassmannianOverFunctor q V)
      (fun i ↦ openCoverMapOver T 𝒰 i) z)
    (x : ∀ i, Modules.PullbackQuotient q V (openCoverObjectOver T 𝒰 i))
    (hx : ∀ i, Quotient.mk'' (x i) = z i)
    [∀ i, Mono (Modules.PullbackQuotient.normalizedKernelι T
      (openCoverMapOver T 𝒰 i) (x i))] :
    Modules.OpenCoverSubmoduleCompatible 𝒰 ((Modules.pullback T.hom).obj V)
      (fun i ↦ kernel (x i).π)
      (fun i ↦ Modules.PullbackQuotient.normalizedKernelι T
        (openCoverMapOver T 𝒰 i) (x i)) := by
  apply Modules.openCoverSubmoduleCompatible_of_openSubmoduleCondition_le_on_ranges
  intro i j W hW s hs
  obtain ⟨t, ht⟩ := (Modules.mem_openSubmoduleCondition_iff
    (𝒰.f i) ((Modules.pullback T.hom).obj V)
      (Modules.PullbackQuotient.normalizedKernelι T
        (openCoverMapOver T 𝒰 i) (x i)) W s).1 hs
  apply (Modules.mem_openSubmoduleCondition_iff
    (𝒰.f j) ((Modules.pullback T.hom).obj V)
      (Modules.PullbackQuotient.normalizedKernelι T
        (openCoverMapOver T 𝒰 j) (x j)) W s).2
  let gᵢ := openCoverOverlapToLeft T 𝒰 i j W hW
  let gⱼ := openCoverOverlapToRight T 𝒰 j W
  let fᵢ := openCoverMapOver T 𝒰 i
  let fⱼ := openCoverMapOver T 𝒰 j
  let Kᵢ := kernel (x i).π
  let Kⱼ := kernel (x j).π
  let M := (Modules.pullback T.hom).obj V
  let kᵢ := Modules.PullbackQuotient.normalizedKernelι T fᵢ (x i)
  let kⱼ := Modules.PullbackQuotient.normalizedKernelι T fⱼ (x j)
  change kᵢ.app (fᵢ.left ⁻¹ᵁ W) t =
    M.presheaf.map (homOfLE (fᵢ.left.image_preimage_le W)).op s at ht
  have htopᵢ : gᵢ.left ''ᵁ
      (⊤ : (openCoverOverlapObjectOver T 𝒰 j W).left.Opens) ≤ fᵢ.left ⁻¹ᵁ W :=
    openCoverOverlapToLeft_image_top_le_preimage T 𝒰 i j W hW
  let t' := Kᵢ.presheaf.map (homOfLE htopᵢ).op t
  let E := (SheafOfModules.forget
    (openCoverOverlapObjectOver T 𝒰 j W).left.ringCatSheaf).mapIso
    (openCoverOverlapRestrictionIso T 𝒰 M i j W hW)
  let a := (((Modules.restrictFunctor gᵢ.left).map kᵢ).val.app
    (Opposite.op (⊤ : (openCoverOverlapObjectOver T 𝒰 j W).left.Opens))) t'
  have ha0 : a ∈ (PresheafOfModules.Submodule.range
      ((Modules.restrictFunctor gᵢ.left).map kᵢ).val).obj
        (Opposite.op (⊤ : (openCoverOverlapObjectOver T 𝒰 j W).left.Opens)) := ⟨t', rfl⟩
  have ha : E.hom.app (Opposite.op
      (⊤ : (openCoverOverlapObjectOver T 𝒰 j W).left.Opens)) a ∈
      ((PresheafOfModules.Submodule.range
        ((Modules.restrictFunctor gᵢ.left).map kᵢ).val).mapIso E).obj
          (Opposite.op (⊤ : (openCoverOverlapObjectOver T 𝒰 j W).left.Opens)) :=
    PresheafOfModules.Submodule.hom_mem_mapIso _ E _ a ha0
  have hrange := grassmannianCompatibleFamily_normalizedKernelRange_overlap
    T 𝒰 V z hz x hx i j W hW
  change (PresheafOfModules.Submodule.range
      ((Modules.restrictFunctor gᵢ.left).map kᵢ).val).mapIso E =
    PresheafOfModules.Submodule.range
      ((Modules.restrictFunctor gⱼ.left).map kⱼ).val at hrange
  have ha' := PresheafOfModules.Submodule.mem_of_eq hrange ha
  obtain ⟨r', hr'⟩ := (PresheafOfModules.Submodule.mem_range_iff
    ((Modules.restrictFunctor gⱼ.left).map kⱼ).val
      (Opposite.op (⊤ : (openCoverOverlapObjectOver T 𝒰 j W).left.Opens)) _).1 ha'
  change Kⱼ.presheaf.obj (Opposite.op (gⱼ.left ''ᵁ
    (⊤ : (openCoverOverlapObjectOver T 𝒰 j W).left.Opens))) at r'
  change (((Modules.restrictFunctor gⱼ.left).map kⱼ).app
      (⊤ : (openCoverOverlapObjectOver T 𝒰 j W).left.Opens) r') =
    E.hom.app (Opposite.op
      (⊤ : (openCoverOverlapObjectOver T 𝒰 j W).left.Opens)) a at hr'
  have htopⱼ : gⱼ.left ''ᵁ
      (⊤ : (openCoverOverlapObjectOver T 𝒰 j W).left.Opens) = fⱼ.left ⁻¹ᵁ W :=
    openCoverOverlapToRight_image_top T 𝒰 j W
  let r := Kⱼ.presheaf.map (eqToHom htopⱼ.symm).op r'
  refine ⟨r, ?_⟩
  change kⱼ.app (fⱼ.left ⁻¹ᵁ W)
      (Kⱼ.presheaf.map (eqToHom htopⱼ.symm).op r') = _
  have hnatⱼ := PresheafOfModules.naturality_apply kⱼ.val
    (eqToHom htopⱼ.symm).op r'
  change kⱼ.app (fⱼ.left ⁻¹ᵁ W)
      (Kⱼ.presheaf.map (eqToHom htopⱼ.symm).op r') =
    ((Modules.restrictFunctor fⱼ.left).obj M).presheaf.map
      (eqToHom htopⱼ.symm).op
      (((Modules.restrictFunctor gⱼ.left).map kⱼ).app
        (⊤ : (openCoverOverlapObjectOver T 𝒰 j W).left.Opens) r') at hnatⱼ
  rw [hnatⱼ]
  change ((Modules.restrictFunctor fⱼ.left).obj M).presheaf.map
      (eqToHom htopⱼ.symm).op
      (((Modules.restrictFunctor gⱼ.left).map kⱼ).app
        (⊤ : (openCoverOverlapObjectOver T 𝒰 j W).left.Opens) r') = _
  rw [hr']
  have hnat := PresheafOfModules.naturality_apply kᵢ.val
    (homOfLE htopᵢ).op t
  change (((Modules.restrictFunctor gᵢ.left).map kᵢ).app
      (⊤ : (openCoverOverlapObjectOver T 𝒰 j W).left.Opens) t') =
    ((Modules.restrictFunctor fᵢ.left).obj M).presheaf.map
      (homOfLE htopᵢ).op (kᵢ.app (fᵢ.left ⁻¹ᵁ W) t) at hnat
  rw [show a = ((Modules.restrictFunctor fᵢ.left).obj M).presheaf.map
      (homOfLE htopᵢ).op (kᵢ.app (fᵢ.left ⁻¹ᵁ W) t) from hnat]
  rw [ht]
  dsimp only [M, fᵢ, fⱼ, E, htopᵢ, htopⱼ]
  rw [show htopᵢ = openCoverOverlapToLeft_image_top_le_preimage
    T 𝒰 i j W hW from Subsingleton.elim _ _]
  erw [Modules.forget_mapIso_hom_app_apply]
  rw [openCoverOverlapRestrictionIso_hom_app T 𝒰
    ((Modules.pullback T.hom).obj V) i j W hW]
  simp only [Modules.restrictFunctorComp_inv_app_app,
    Modules.restrictFunctorComp_hom_app_app,
    Modules.restrictFunctorCongr_hom_app_app, Modules.restrict_map]
  let P := ((Modules.pullback T.hom).obj V).presheaf
  change P.map _ (P.map _ (P.map _ (P.map _ (P.map _ (P.map _ s))))) = P.map _ s
  rw [← P.map_comp_apply, ← P.map_comp_apply, ← P.map_comp_apply,
    ← P.map_comp_apply]
  change P.map _ (P.map _ s) = P.map _ s
  erw [← P.map_comp_apply]
  rfl

/-- The global quotient obtained by descending the normalized kernels of a
compatible family of relative Grassmannian points. -/
noncomputable def grassmannianCompatibleFamilyAmalgamation {q : ℕ}
    (V : S.Modules)
    (z : ∀ i, (Modules.grassmannianOverFunctor q V).obj
      (Opposite.op (openCoverObjectOver T 𝒰 i)))
    (hz : Presieve.Arrows.Compatible (Modules.grassmannianOverFunctor q V)
      (fun i ↦ openCoverMapOver T 𝒰 i) z)
    (x : ∀ i, Modules.PullbackQuotient q V (openCoverObjectOver T 𝒰 i))
    (hx : ∀ i, Quotient.mk'' (x i) = z i) :
    Modules.PullbackQuotient q V T := by
  let k (i : 𝒰.I₀) := Modules.PullbackQuotient.normalizedKernelι T
    (openCoverMapOver T 𝒰 i) (x i)
  letI (i : 𝒰.I₀) : Mono (k i) := by
    dsimp only [k]
    infer_instance
  letI (i : 𝒰.I₀) : (cokernel (k i)).IsQuasicoherent := by
    dsimp only [k]
    exact Modules.PullbackQuotient.normalizedKernelCokernel_isQuasicoherent
      T (openCoverMapOver T 𝒰 i) (x i)
  exact Modules.PullbackQuotient.ofOpenCoverKernels T 𝒰
    (fun i ↦ kernel (x i).π) k
    (grassmannianCompatibleFamily_normalizedKernels_compatible
      T 𝒰 V z hz x hx)
    (fun i ↦ by
      dsimp only [k]
      exact Modules.PullbackQuotient.normalizedKernelCokernel_isProjectiveOfRank
        T (openCoverMapOver T 𝒰 i) (x i))

set_option backward.isDefEq.respectTransparency.types false in
/-- Restricting the descended quotient to a cover member recovers the chosen local
quotient presentation. -/
lemma grassmannianCompatibleFamilyAmalgamation_restrictPullback_r {q : ℕ}
    (V : S.Modules)
    (z : ∀ i, (Modules.grassmannianOverFunctor q V).obj
      (Opposite.op (openCoverObjectOver T 𝒰 i)))
    (hz : Presieve.Arrows.Compatible (Modules.grassmannianOverFunctor q V)
      (fun i ↦ openCoverMapOver T 𝒰 i) z)
    (x : ∀ i, Modules.PullbackQuotient q V (openCoverObjectOver T 𝒰 i))
    (hx : ∀ i, Quotient.mk'' (x i) = z i) (i : 𝒰.I₀) :
    (Modules.PullbackQuotient.setoid q V (openCoverObjectOver T 𝒰 i)).r
      (Modules.PullbackQuotient.restrictPullback T (openCoverMapOver T 𝒰 i)
        (grassmannianCompatibleFamilyAmalgamation T 𝒰 V z hz x hx))
      (x i) := by
  let f := openCoverMapOver T 𝒰 i
  let M := (Modules.pullback T.hom).obj V
  let K (j : 𝒰.I₀) := kernel (x j).π
  let k (j : 𝒰.I₀) := Modules.PullbackQuotient.normalizedKernelι T
    (openCoverMapOver T 𝒰 j) (x j)
  let hcompat := grassmannianCompatibleFamily_normalizedKernels_compatible
    T 𝒰 V z hz x hx
  let hmono : ∀ j, Mono (k j) := fun j ↦ by
    dsimp only [k]
    infer_instance
  let e := @Modules.openCoverQuotientRestrictIso _ 𝒰 M K k hmono hcompat i ≪≫
    Modules.PullbackQuotient.normalizedKernelCokernelIso T f (x i)
  refine ⟨e, ?_⟩
  change (Modules.PullbackQuotient.normalizedAmbientIso T f).hom ≫
      (Modules.restrictFunctor f.left).map
        (@Modules.openCoverQuotientMap _ 𝒰 M K k hmono) ≫ e.hom = (x i).π
  dsimp only [e]
  rw [Iso.trans_hom]
  have hnorm : cokernel.π (k i) ≫
      (Modules.PullbackQuotient.normalizedKernelCokernelIso T f (x i)).hom =
    (Modules.PullbackQuotient.normalizedAmbientIso T f).inv ≫ (x i).π := by
    exact Modules.PullbackQuotient.cokernel_π_comp_normalizedKernelCokernelIso_hom
      T f (x i)
  have hlocal := @Modules.restrict_openCoverQuotientMap_comp_iso_assoc _
    𝒰 M K k hmono hcompat i _
      (Modules.PullbackQuotient.normalizedKernelCokernelIso T f (x i)).hom
  erw [hlocal]
  erw [hnorm]
  simp

/-- The descended quotient restricts to every member of the original compatible
family of relative Grassmannian points. -/
lemma grassmannianCompatibleFamilyAmalgamation_restrict {q : ℕ}
    (V : S.Modules)
    (z : ∀ i, (Modules.grassmannianOverFunctor q V).obj
      (Opposite.op (openCoverObjectOver T 𝒰 i)))
    (hz : Presieve.Arrows.Compatible (Modules.grassmannianOverFunctor q V)
      (fun i ↦ openCoverMapOver T 𝒰 i) z)
    (x : ∀ i, Modules.PullbackQuotient q V (openCoverObjectOver T 𝒰 i))
    (hx : ∀ i, Quotient.mk'' (x i) = z i) (i : 𝒰.I₀) :
    (Modules.grassmannianOverFunctor q V).map
      (openCoverMapOver T 𝒰 i).op
      (Quotient.mk'' (grassmannianCompatibleFamilyAmalgamation T 𝒰 V z hz x hx)) =
        z i := by
  rw [← hx i]
  apply Quotient.sound
  exact (Modules.PullbackQuotient.setoid q V
    (openCoverObjectOver T 𝒰 i)).trans
    ((Modules.PullbackQuotient.setoid q V
      (openCoverObjectOver T 𝒰 i)).symm
      (Modules.PullbackQuotient.restrictPullback_r_pullback T
        (openCoverMapOver T 𝒰 i)
        (grassmannianCompatibleFamilyAmalgamation T 𝒰 V z hz x hx)))
    (grassmannianCompatibleFamilyAmalgamation_restrictPullback_r
      T 𝒰 V z hz x hx i)

/-- Equality of pulled-back quotient kernels on one chart gives equality of the
literal restrictions of their global kernel ranges. -/
lemma restrictedKernelRange_eq_of_pullbackKernelRange_eq {q : ℕ} (V : S.Modules)
    (x y : Modules.PullbackQuotient q V T) (i : 𝒰.I₀)
    (h : (x.pullback (openCoverMapOver T 𝒰 i)).kernelRangeSubmodule =
      (y.pullback (openCoverMapOver T 𝒰 i)).kernelRangeSubmodule) :
      PresheafOfModules.Submodule.range
          ((Modules.restrictFunctor (𝒰.f i)).map (kernel.ι x.π)).val =
        PresheafOfModules.Submodule.range
          ((Modules.restrictFunctor (𝒰.f i)).map (kernel.ι y.π)).val := by
  rw [← Modules.PullbackQuotient.kernelRangeSubmodule_restrictPullback_eq_pullback,
    ← Modules.PullbackQuotient.kernelRangeSubmodule_restrictPullback_eq_pullback] at h
  change PresheafOfModules.Submodule.range
      ((Modules.restrictFunctor (openCoverMapOver T 𝒰 i).left).map
        (kernel.ι x.π)).val = _
  let e := (SheafOfModules.forget (𝒰.X i).ringCatSheaf).mapIso
    (Modules.PullbackQuotient.normalizedAmbientIso (V := V) T
      (openCoverMapOver T 𝒰 i))
  calc
    _ = (Modules.PullbackQuotient.restrictPullback T
        (openCoverMapOver T 𝒰 i) x).kernelRangeSubmodule.mapIso e :=
      (Modules.PullbackQuotient.kernelRangeSubmodule_restrictPullback_mapIso
        T (openCoverMapOver T 𝒰 i) x).symm
    _ = (Modules.PullbackQuotient.restrictPullback T
        (openCoverMapOver T 𝒰 i) y).kernelRangeSubmodule.mapIso e :=
      congrArg (fun N ↦ N.mapIso e) h
    _ = _ := Modules.PullbackQuotient.kernelRangeSubmodule_restrictPullback_mapIso
      T (openCoverMapOver T 𝒰 i) y

/-- Global quotient kernels are determined by their pullbacks to an open cover. -/
lemma kernelRange_eq_of_openCover_pullbackKernelRange_eq {q : ℕ} (V : S.Modules)
    (x y : Modules.PullbackQuotient q V T)
    (h : ∀ i, (x.pullback (openCoverMapOver T 𝒰 i)).kernelRangeSubmodule =
      (y.pullback (openCoverMapOver T 𝒰 i)).kernelRangeSubmodule) :
    x.kernelRangeSubmodule = y.kernelRangeSubmodule := by
  exact Modules.range_eq_of_openCover_restrict_range_eq 𝒰
    ((Modules.pullback T.hom).obj V) (kernel x.π) (kernel y.π)
    (kernel.ι x.π) (kernel.ι y.π)
    (fun i ↦ restrictedKernelRange_eq_of_pullbackKernelRange_eq
      T 𝒰 V x y i (h i))

/-- Two relative Grassmannian points which agree on every member of an open cover
are equal. This is the separatedness half of effective Zariski descent for quotient
presentations. -/
lemma grassmannianOverFunctor_eq_of_openCover_restrict {q : ℕ} (V : S.Modules)
    (z z' : (Modules.grassmannianOverFunctor q V).obj (Opposite.op T))
    (h : ∀ i, (Modules.grassmannianOverFunctor q V).map
      (openCoverMapOver T 𝒰 i).op z =
        (Modules.grassmannianOverFunctor q V).map
          (openCoverMapOver T 𝒰 i).op z') : z = z' := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep z
  obtain ⟨y, rfl⟩ := Quotient.exists_rep z'
  apply Modules.PullbackQuotient.kernelRangeSubmoduleQuotient_injective
  apply kernelRange_eq_of_openCover_pullbackKernelRange_eq T 𝒰 V x y
  intro i
  exact congrArg (Modules.PullbackQuotient.kernelRangeSubmoduleQuotient
    (q := q) (V := V)) (h i)

/-- API lemma for Theorem 2.1.1 (the Zariski descent
input): the relative Grassmannian functor is a sheaf for the Zariski topology on schemes
over the base. -/
theorem isSheaf_grassmannianOverFunctor {q : ℕ} (V : S.Modules) :
    Presieve.IsSheaf (Scheme.zariskiTopology.over S)
      (Modules.grassmannianOverFunctor q V) := by
  rw [Scheme.zariskiTopology_eq]
  change Presieve.IsSheaf
    (((precoverage @IsOpenImmersion).toPretopology).toGrothendieck.over S)
      (Modules.grassmannianOverFunctor q V)
  rw [Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck,
    over_toGrothendieck_eq_toGrothendieck_comap_forget]
  apply (Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange_of_small
    (Modules.grassmannianOverFunctor q V)).2
  intro T E
  rw [Presieve.isSheafFor_arrows_iff]
  intro z hz
  let 𝒰 : T.left.OpenCover := E.map (Over.forget S) le_rfl
  let c (i : E.I₀) : openCoverObjectOver T 𝒰 i ≅ E.X i :=
    Over.isoMk (Iso.refl _) (by
      change (E.X i).hom = (E.f i).left ≫ T.hom
      exact (Over.w (E.f i)).symm)
  let z' (i : 𝒰.I₀) :=
    (Modules.grassmannianOverFunctor q V).map (c i).hom.op (z i)
  have hz' : Presieve.Arrows.Compatible (Modules.grassmannianOverFunctor q V)
      (fun i ↦ openCoverMapOver T 𝒰 i) z' := by
    intro i j W gi gj hij
    have hci : (c i).hom ≫ E.f i = openCoverMapOver T 𝒰 i := by
      ext
      rfl
    have hcj : (c j).hom ≫ E.f j = openCoverMapOver T 𝒰 j := by
      ext
      rfl
    have h := hz i j W (gi ≫ (c i).hom) (gj ≫ (c j).hom) (by
      simp only [Category.assoc, hci, hcj, hij])
    simpa only [z', op_comp, Functor.map_comp, Function.comp_apply,
      ConcreteCategory.comp_apply] using h
  choose x hx using fun i ↦ Quotient.exists_rep (z' i)
  let t : (Modules.grassmannianOverFunctor q V).obj (Opposite.op T) :=
    Quotient.mk'' (grassmannianCompatibleFamilyAmalgamation T 𝒰 V z' hz' x hx)
  refine ⟨t, ?_, ?_⟩
  · intro i
    have ht := grassmannianCompatibleFamilyAmalgamation_restrict T 𝒰
      V z' hz' x hx i
    change (Modules.grassmannianOverFunctor q V).map (E.f i).op t = z i
    apply injective_of_mono
      ((Modules.grassmannianOverFunctor q V).map (c i).hom.op)
    have hci : (c i).hom ≫ E.f i = openCoverMapOver T 𝒰 i := by
      ext
      rfl
    simpa only [← Functor.map_comp_apply, ← op_comp, hci] using ht
  · intro t' ht'
    apply grassmannianOverFunctor_eq_of_openCover_restrict T 𝒰 V t' t
    intro i
    have hi := ht' i
    have ht := grassmannianCompatibleFamilyAmalgamation_restrict T 𝒰
      V z' hz' x hx i
    have h := (congrArg
      ((Modules.grassmannianOverFunctor q V).map (c i).hom.op) hi).trans ht.symm
    simpa only [← Functor.map_comp_apply, ← op_comp, z', show
      (c i).hom ≫ E.f i = openCoverMapOver T 𝒰 i by ext; rfl] using h

end AlgebraicGeometry.Scheme

end ThmGrassmannianProjectiveRelative

section ThmGrassmannianProjectiveRelative

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} (V : S.Modules) [V.IsQuasicoherent]
  {n : ℕ} (hV : Modules.IsProjectiveOfRank n V) (q : ℕ)

/-- The representative of the free Grassmannian over the coordinate neighborhood of
`x`, regarded as a scheme over the original base. -/
noncomputable def grassmannianCoordinateChart (x : S) : Over S :=
  (Over.map (hV.coordinateBasicOpenAffine x).1.ι).obj
    (grassmannianOverRepresentation
      (hV.coordinateBasicOpenAffine x).1.toScheme q n)

/-- The universal point on a coordinate Grassmannian chart, transported through the
chosen trivialization to a quotient of the original vector bundle. -/
noncomputable def grassmannianCoordinateChartPoint (x : S) :
    (Modules.grassmannianOverFunctor q V).obj
      (op (grassmannianCoordinateChart V hV q x)) :=
    (hV.coordinateBasicOpenGrassmannianRestrictionIso q x).hom.app
    (op (grassmannianOverRepresentation
      (hV.coordinateBasicOpenAffine x).1.toScheme q n))
    ((freeGrassmannianRepresentableBy
      (hV.coordinateBasicOpenAffine x).1.toScheme q n).homEquiv (𝟙 _))

/-- The natural map from a coordinate Grassmannian chart to the relative
Grassmannian functor of `V`. -/
noncomputable def grassmannianCoordinateChartMap (x : S) :
    uliftYoneda.{u + 1}.obj (grassmannianCoordinateChart V hV q x) ⟶
      Modules.grassmannianOverFunctor q V :=
  uliftYonedaEquiv.symm (grassmannianCoordinateChartPoint V hV q x)

/-- Every coordinate trivialization of a vector bundle gives a representable open
subfunctor of its relative Grassmannian. -/
theorem grassmannianCoordinateChartMap_isOpenImmersion (x : S) :
    (isOpenImmersionOver S).relative uliftYoneda.{u + 1}
      (grassmannianCoordinateChartMap V hV q x) := by
  let U := (hV.coordinateBasicOpenAffine x).1.toScheme
  let j : U ⟶ S := (hV.coordinateBasicOpenAffine x).1.ι
  let H := Modules.grassmannianOverFunctor q
    (SheafOfModules.free (R := U.ringCatSheaf) (ULift.{u} (Fin n)))
  let P := grassmannianOverRepresentation U q n
  let R := freeGrassmannianRepresentableBy U q n
  let e := hV.coordinateBasicOpenGrassmannianRestrictionIso q x
  simpa only [grassmannianCoordinateChartMap, grassmannianCoordinateChartPoint,
    grassmannianCoordinateChart, BaseRestrictionChart.map,
    BaseRestrictionChart.point, BaseRestrictionChart.object, U, j, H, P, R, e] using
    BaseRestrictionChart.isOpenImmersion j H
      (Modules.grassmannianOverFunctor q V) P R e

/-- The coproduct map from all coordinate-trivialization charts. -/
noncomputable def grassmannianCoordinateChartCoverMap :
    (∐ fun x : S ↦
      uliftYoneda.{u + 1}.obj (grassmannianCoordinateChart V hV q x)) ⟶
        Modules.grassmannianOverFunctor q V :=
  Limits.Sigma.desc (fun x : S ↦ grassmannianCoordinateChartMap V hV q x)

/-- The coordinate-trivialization charts jointly cover the relative Grassmannian. -/
theorem grassmannianCoordinateChartMap_isLocallySurjective :
    Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over S)
      (grassmannianCoordinateChartCoverMap V (hV := hV) (q := q)) := by
  constructor
  intro T z
  rw [GrothendieckTopology.mem_over_iff]
  let 𝒰 := hV.coordinateBasicOpenCover.pullback₁ T.hom
  refine Scheme.zariskiTopology.superset_covering ?_
    (Precoverage.generate_mem_toGrothendieck 𝒰.mem₀)
  rw [Sieve.generate_le_iff]
  rintro W γ ⟨x⟩
  rw [Sieve.overEquiv_iff]
  let U := (hV.coordinateBasicOpenAffine x).1.toScheme
  let j : U ⟶ S := (hV.coordinateBasicOpenAffine x).1.ι
  let H := Modules.grassmannianOverFunctor q
    (SheafOfModules.free (R := U.ringCatSheaf) (ULift.{u} (Fin n)))
  let P := grassmannianOverRepresentation U q n
  let R := freeGrassmannianRepresentableBy U q n
  let e := hV.coordinateBasicOpenGrassmannianRestrictionIso q x
  let Q := BaseRestrictionChart.pullbackObject j T
  let k := BaseRestrictionChart.lift j H
    (Modules.grassmannianOverFunctor q V) P R e T z
  let Q₀ : Over S := Over.mk (𝒰.f x ≫ T.hom)
  let c : Q₀ ≅ Q := Over.isoMk (Iso.refl _) (by
    dsimp only [Iso.refl_hom]
    rw [Category.id_comp]
    change Limits.pullback.snd T.hom j ≫ j = 𝒰.f x ≫ T.hom
    exact (Limits.pullback.condition (f := T.hom) (g := j)).symm)
  let t := (Limits.Sigma.ι (fun x : S ↦
      uliftYoneda.{u + 1}.obj (grassmannianCoordinateChart V hV q x)) x).app
      (op Q₀) ⟨c.hom ≫ (Over.map j).map k⟩
  refine ⟨t, ?_⟩
  have hw := congrArg
    (fun p ↦ p.app (op Q₀) ⟨c.hom⟩)
    (BaseRestrictionChart.pullback_square_w j H
      (Modules.grassmannianOverFunctor q V) P R e T z)
  have hc : c.hom ≫ BaseRestrictionChart.pullbackSnd j T =
      (Over.homMk (𝒰.f x) : Q₀ ⟶ T) := by
    ext
    rfl
  have hk :
      (BaseRestrictionChart.pullbackFst j H
        (Modules.grassmannianOverFunctor q V) P R e T z).app (op Q₀) ⟨c.hom⟩ =
        ⟨c.hom ≫ (Over.map j).map k⟩ := rfl
  have hs :
      (uliftYoneda.{u + 1}.map (BaseRestrictionChart.pullbackSnd j T)).app
        (op Q₀) ⟨c.hom⟩ = ⟨c.hom ≫ BaseRestrictionChart.pullbackSnd j T⟩ := rfl
  have hz :
      (uliftYonedaEquiv.{u + 1}.symm z).app (op Q₀)
        ⟨c.hom ≫ BaseRestrictionChart.pullbackSnd j T⟩ =
      (Modules.grassmannianOverFunctor q V).map
        (c.hom ≫ BaseRestrictionChart.pullbackSnd j T).op z := rfl
  have ht :
      (grassmannianCoordinateChartCoverMap V (hV := hV) (q := q)).app (op Q₀) t =
        (grassmannianCoordinateChartMap V hV q x).app (op Q₀)
          ⟨c.hom ≫ (Over.map j).map k⟩ := by
    change ((Limits.Sigma.ι (fun x : S ↦
      uliftYoneda.{u + 1}.obj (grassmannianCoordinateChart V hV q x)) x ≫
        Limits.Sigma.desc (fun x : S ↦
          grassmannianCoordinateChartMap V hV q x)).app (op Q₀))
            ⟨c.hom ≫ (Over.map j).map k⟩ = _
    rw [Limits.Sigma.ι_desc]
  rw [ht]
  rw [NatTrans.comp_app_apply, NatTrans.comp_app_apply, hk, hs, hz] at hw
  simpa only [NatTrans.comp_app_apply,
    ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk, Category.assoc, hc, uliftYoneda,
    uliftYonedaEquiv_symm_apply_app,
    Q₀, Q, j, H, P, R, e,
    grassmannianCoordinateChartCoverMap,
    grassmannianCoordinateChartMap, grassmannianCoordinateChartPoint,
    grassmannianCoordinateChart, BaseRestrictionChart.map,
    BaseRestrictionChart.point, BaseRestrictionChart.object] using hw

/-- The absolute Grassmannian, viewed on schemes over a fixed base, is a sheaf for the
induced Zariski topology. -/
theorem isSheaf_grassmannianFunctorOver (q n : ℕ) :
    Presieve.IsSheaf (Scheme.zariskiTopology.over S)
      (Modules.grassmannianFunctorOver S q n) := by
  have h : Presieve.IsSheaf (Scheme.zariskiTopology.over S)
      ((Over.forget S).op ⋙ grassmannianFunctor q n) :=
    (Over.forget S).op_comp_isSheaf_of_isSheaf_type
      (J := Scheme.zariskiTopology.over S) (K := Scheme.zariskiTopology)
      (isSheaf_grassmannianFunctor q n)
  change Presieve.IsSheaf (Scheme.zariskiTopology.over S)
    (((Over.forget S).op ⋙ grassmannianFunctor q n) ⋙ uliftFunctor.{u + 1})
  exact Presieve.isSheaf_comp_uliftFunctor
    (J := Scheme.zariskiTopology.over S) h

/-- The relative Grassmannian of a canonical finite free sheaf is a Zariski sheaf. -/
theorem isSheaf_freeGrassmannianOver (q n : ℕ) :
    Presieve.IsSheaf (Scheme.zariskiTopology.over S)
      (Modules.grassmannianOverFunctor q
        (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n)))) := by
  exact Presieve.isSheaf_iso (Scheme.zariskiTopology.over S)
    (Modules.freeGrassmannianIsoGrassmannianFunctorOver
      (S := S) (n := n) q).symm
    (isSheaf_grassmannianFunctorOver (S := S) q n)

/-- API lemma for Theorem 2.1.1 (representability
criterion): a relative Grassmannian is representable once effective Zariski descent for
its quotient presentations has supplied the sheaf condition.  All geometric inputs to the
gluing theorem—the represented coordinate charts, their openness, and joint local
surjectivity—are discharged here. -/
theorem grassmannianOverFunctor_isRepresentable_of_isSheaf
    (hV : Modules.IsProjectiveOfRank n V)
    (hF : Presieve.IsSheaf (Scheme.zariskiTopology.over S)
      (Modules.grassmannianOverFunctor q V)) :
    (Modules.grassmannianOverFunctor q V).IsRepresentable := by
  let G : Sheaf (Scheme.zariskiTopology.over S) (Type (u + 1)) :=
    ⟨Modules.grassmannianOverFunctor q V,
      (isSheaf_iff_isSheaf_of_type _ _).2 hF⟩
  let g := fun x : S ↦ grassmannianCoordinateChartMap V hV q x
  have hg : ∀ x, (isOpenImmersionOver S).relative uliftYoneda.{u + 1} (g x) := by
    intro x
    exact grassmannianCoordinateChartMap_isOpenImmersion V hV q x
  letI : Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over S)
      (Limits.Sigma.desc g) :=
    grassmannianCoordinateChartMap_isLocallySurjective V hV q
  exact OverLocalRepresentability.isRepresentable G g hg

/-- API lemma for Theorem 2.1.1 (representability part):
the relative Grassmannian `Gr(q, V)` of a finite locally free sheaf `V` on a scheme `S`
is representable by a scheme over `S`. The projectivity part is stated in part 2.2.2 as
`exists_grassmannianOverFunctor_representableBy`. -/
theorem grassmannianOverFunctor_isRepresentable
    (hV : Modules.IsProjectiveOfRank n V) :
    (Modules.grassmannianOverFunctor q V).IsRepresentable :=
  grassmannianOverFunctor_isRepresentable_of_isSheaf V q hV
    (isSheaf_grassmannianOverFunctor (q := q) V)

/-- Background definition for Theorem 2.1.1 (the representing scheme):
a chosen scheme over `S` representing the relative Grassmannian of `V`.

This packages the representability theorem into an object that can be used by the
global Plücker and universal-quotient constructions. -/
noncomputable def grassmannianOverRepresentationOfProjective
    (hV : Modules.IsProjectiveOfRank n V) : Over S := by
  letI : (Modules.grassmannianOverFunctor q V).IsRepresentable :=
    grassmannianOverFunctor_isRepresentable V q hV
  exact (Modules.grassmannianOverFunctor q V).reprX

/-- Background definition for Theorem 2.1.1 (the representing
equivalence): the chosen relative Grassmannian scheme represents its quotient functor. -/
noncomputable def grassmannianOverRepresentableByOfProjective
    (hV : Modules.IsProjectiveOfRank n V) :
    (Modules.grassmannianOverFunctor q V).RepresentableBy
      (grassmannianOverRepresentationOfProjective V q hV) := by
  letI : (Modules.grassmannianOverFunctor q V).IsRepresentable :=
    grassmannianOverFunctor_isRepresentable V q hV
  exact (Modules.grassmannianOverFunctor q V).representableBy

/-- Kernel-model form of the relative representability criterion.  It suffices to
embed the relative Grassmannian into a Zariski sheaf so that membership in the image is
local; the image criterion supplies the sheaf condition and the coordinate charts then
give the representing scheme. -/
theorem grassmannianOverFunctor_isRepresentable_of_mono_of_range_local
    (hV : Modules.IsProjectiveOfRank n V)
    (K : (Over S)ᵒᵖ ⥤ Type (u + 1))
    (η : Modules.grassmannianOverFunctor q V ⟶ K) [Mono η]
    (hK : Presieve.IsSheaf (Scheme.zariskiTopology.over S) K)
    (hlocal : ∀ (T : (Over S)ᵒᵖ) (s : K.obj T),
      (Subfunctor.range η).sieveOfSection s ∈
          (Scheme.zariskiTopology.over S) (unop T) →
        s ∈ (Subfunctor.range η).obj T) :
    (Modules.grassmannianOverFunctor q V).IsRepresentable := by
  apply grassmannianOverFunctor_isRepresentable_of_isSheaf V q hV
  exact Presieve.isSheaf_of_mono_of_range_local η hK hlocal


section PluckerBaseChange

variable {U : Scheme.{u}} (j : U ⟶ S)

/-- **Base change of a Grassmannian representative**: the fiber product `P ×_S U`
represents the relative Grassmannian of the restricted bundle `V|_U`, by the
adjunction `Over.map j ⊣ Over.pullback j` and the base-change comparison of relative
Grassmannian functors. -/
noncomputable def grassmannianRepresentableByPullback {P : Over S}
    (repr : (Modules.grassmannianOverFunctor q V).RepresentableBy P) :
    (Modules.grassmannianOverFunctor q
      ((Modules.pullback j).obj V)).RepresentableBy ((Over.pullback j).obj P) :=
  ((Over.mapPullbackAdj j).compRepresentableBy repr).ofIso
    (Modules.grassmannianOverFunctorPullbackIso j q V).symm

/-- The comparison identifying the Grassmannian of the exterior power of the restricted
bundle with the restriction of the Grassmannian of `⋀^q V`: it is the exterior-power
pullback comparison followed by base change of the ambient sheaf. -/
noncomputable def grassmannianExteriorPowerRestrictIso :
    Modules.grassmannianOverFunctor 1
        (Modules.exteriorPower ((Modules.pullback j).obj V) q) ≅
      (Over.map j).op ⋙
        Modules.grassmannianOverFunctor 1 (Modules.exteriorPower V q) :=
  Modules.grassmannianOverFunctorIsoOfIso 1
      (Modules.pullbackExteriorPowerIso j V hV q).symm ≪≫
    Modules.grassmannianOverFunctorPullbackIso j 1 (Modules.exteriorPower V q)

/-- Base change of a representative of `Gr(1, ⋀^q V)` represents `Gr(1, ⋀^q (V|_U))`. -/
noncomputable def grassmannianRepresentableByPullbackExteriorPower {P' : Over S}
    (repr' : (Modules.grassmannianOverFunctor 1
      (Modules.exteriorPower V q)).RepresentableBy P') :
    (Modules.grassmannianOverFunctor 1
      (Modules.exteriorPower ((Modules.pullback j).obj V) q)).RepresentableBy
        ((Over.pullback j).obj P') :=
  ((Over.mapPullbackAdj j).compRepresentableBy repr').ofIso
    (grassmannianExteriorPowerRestrictIso V hV q j).symm

/-- The Plücker transformation of the restricted bundle is the restriction of the
Plücker transformation of `V`, in the direction of the comparison isomorphisms. -/
lemma grassmannianExteriorPowerRestrictIso_hom_app_plucker (T : Over U)
    (x : (Modules.grassmannianOverFunctor q
      ((Modules.pullback j).obj V)).obj (op T)) :
    (grassmannianExteriorPowerRestrictIso V hV q j).hom.app (op T)
        ((Modules.pluckerTransformation q
          ((Modules.pullback j).obj V)).app (op T) x) =
      (Modules.pluckerTransformation q V).app (op ((Over.map j).obj T))
        ((Modules.grassmannianOverFunctorPullbackIso j q V).hom.app (op T) x) :=
  Modules.pluckerTransformation_rebase_app hV j T x

/-- The same compatibility, read in the direction of the inverse comparisons. -/
lemma grassmannianExteriorPowerRestrictIso_inv_app_plucker (T : Over U)
    (y : (Modules.grassmannianOverFunctor q V).obj (op ((Over.map j).obj T))) :
    (grassmannianExteriorPowerRestrictIso V hV q j).inv.app (op T)
        ((Modules.pluckerTransformation q V).app
          (op ((Over.map j).obj T)) y) =
      (Modules.pluckerTransformation q ((Modules.pullback j).obj V)).app (op T)
        ((Modules.grassmannianOverFunctorPullbackIso j q V).inv.app (op T) y) := by
  apply ((grassmannianExteriorPowerRestrictIso V hV q j).app (op T)).toEquiv.injective
  simp only [Iso.toEquiv_fun, Iso.app_hom,
    grassmannianExteriorPowerRestrictIso_hom_app_plucker,
    CategoryTheory.Iso.inv_hom_id_app_apply]

/-- **The Plücker morphism commutes with base change of the base scheme**: restricting
the Plücker morphism of representing schemes to an open part `U` of the base is the
Plücker morphism of the restricted bundle. -/
lemma pluckerMorphismOfRepr_pullback {P P' : Over S}
    (repr : (Modules.grassmannianOverFunctor q V).RepresentableBy P)
    (repr' : (Modules.grassmannianOverFunctor 1
      (Modules.exteriorPower V q)).RepresentableBy P') :
    (Over.pullback j).map (Modules.pluckerMorphismOfRepr V repr repr') =
      Modules.pluckerMorphismOfRepr ((Modules.pullback j).obj V)
        (grassmannianRepresentableByPullback V q j repr)
        (grassmannianRepresentableByPullbackExteriorPower V hV q j repr') := by
  apply Modules.pluckerMorphismOfRepr_unique
  intro T t
  dsimp only [grassmannianRepresentableByPullbackExteriorPower,
    grassmannianRepresentableByPullback, Functor.RepresentableBy.ofIso,
    Adjunction.compRepresentableBy]
  simp only [Equiv.trans_apply]
  rw [(Over.mapPullbackAdj j).homEquiv_naturality_right_symm,
    Modules.pluckerMorphismOfRepr_homEquiv]
  exact grassmannianExteriorPowerRestrictIso_inv_app_plucker V hV q j T _

end PluckerBaseChange

section FreeExteriorPower


/-- The `Finsupp`/`Pi` identification of the standard finite free module sends the standard
basis vector to the standard basis vector. -/
lemma uliftFinFinsuppEquivPi_single {R : Type u} [CommRing R] (n : ℕ) (k : Fin n) :
    Modules.FreeQuotient.uliftFinFinsuppEquivPi (R := R) n
        (Finsupp.single (ULift.up k) (1 : R)) = Pi.single k 1 := by
  classical
  rw [Modules.FreeQuotient.uliftFinFinsuppEquivPi, LinearEquiv.trans_apply,
    Finsupp.mapDomain.coe_linearEquiv, Finsupp.mapDomain_single]
  exact Finsupp.linearEquivFunOnFinite_single (R := R) (M := R) (Fin n) k 1

lemma uliftFinFinsuppEquivPi_symm_single {R : Type u} [CommRing R] (n : ℕ) (k : Fin n) :
    (Modules.FreeQuotient.uliftFinFinsuppEquivPi (R := R) n).symm (Pi.single k 1) =
      Finsupp.single (ULift.up k) (1 : R) := by
  apply (Modules.FreeQuotient.uliftFinFinsuppEquivPi (R := R) n).injective
  rw [LinearEquiv.apply_symm_apply, uliftFinFinsuppEquivPi_single]

/-- The exterior power of a finite free module in the `Finsupp` model, identified with
the finite free module indexed by `q`-element subsets through the Plücker basis
`exteriorPowerPiEquiv`. -/
noncomputable def freeExteriorPowerModuleEquiv (R : Type u) [CommRing R] (q m : ℕ) :
    (⋀[R]^q (ULift.{u} (Fin m) →₀ R)) ≃ₗ[R] (ULift.{u} (Fin (m.choose q)) →₀ R) :=
  ((Modules.FreeQuotient.uliftFinFinsuppEquivPi m).exteriorPower q).trans
    ((exteriorPowerPiEquiv R q m).symm.trans
      (Modules.FreeQuotient.uliftFinFinsuppEquivPi (m.choose q)).symm)


section FreeGenerators

/-- The standard global generator of a finite free sheaf attached to an index. -/
noncomputable def freeGenSection (X : Scheme.{u}) {I : Type u} (i : I) :
    Γ(SheafOfModules.free (R := X.ringCatSheaf) I, (⊤ : X.Opens)) :=
  Scheme.Modules.Hom.app
    (M := (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (N := (SheafOfModules.free (R := X.ringCatSheaf) I : X.Modules))
    (SheafOfModules.ιFree i) (⊤ : X.Opens) (1 : Γ(X, (⊤ : X.Opens)))

/-- On an affine scheme the standard generator is the image of the standard basis vector
under the global-sections identification. -/
lemma freeModuleSpecΓIso_single (R : CommRingCat.{u}) {I : Type u} (i : I) :
    (AlgebraicGeometry.freeModuleSpecΓIso (R := R) I).hom (Finsupp.single i (1 : R)) =
      freeGenSection (Spec R) i := by
  have h := DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp
    (AlgebraicGeometry.lsingle_comp_freeModuleSpecΓIso_hom (R := R) I i)) (1 : R)
  have h1 : (show Γ(Spec R, (⊤ : (Spec R).Opens)) from
        (AlgebraicGeometry.unitModuleSpecΓIso R).hom (1 : R)) =
      (1 : Γ(Spec R, (⊤ : (Spec R).Opens))) := by
    rw [AlgebraicGeometry.unitModuleSpecΓIso_hom_one]
    exact map_one _
  exact h.trans (congrArg (fun z ↦ Scheme.Modules.Hom.app
    (M := (SheafOfModules.unit (Spec R).ringCatSheaf : (Spec R).Modules))
    (N := (SheafOfModules.free (R := (Spec R).ringCatSheaf) I : (Spec R).Modules))
    (SheafOfModules.ιFree i) (⊤ : (Spec R).Opens) z) h1)


/-- Naturality of the pullback–pushforward unit on sections: the pullback of a morphism
carries unit sections to unit sections. -/
lemma unit_app_naturality {X Y : Scheme.{u}} (f : X ⟶ Y) {V W : Y.Modules} (ψ : V ⟶ W)
    (U : Y.Opens) (s : Γ(V, U)) :
    (Modules.Hom.app ((Modules.pullback f).map ψ) (f ⁻¹ᵁ U))
        ((((Modules.pullbackPushforwardAdjunction f).unit.app V).app U) s) =
      (((Modules.pullbackPushforwardAdjunction f).unit.app W).app U)
        (Modules.Hom.app ψ U s) := by
  have h := congrArg (fun (k : V ⟶ (Modules.pushforward f).obj
      ((Modules.pullback f).obj W)) ↦ (k.app U) s)
    ((Modules.pullbackPushforwardAdjunction f).unit.naturality ψ)
  exact h.symm

/-- Naturality of the pullback–pushforward unit on global sections. -/
lemma unit_app_naturality_top {X Y : Scheme.{u}} (f : X ⟶ Y) {V W : Y.Modules}
    (ψ : V ⟶ W) (s : Γ(V, (⊤ : Y.Opens))) :
    (Modules.Hom.app ((Modules.pullback f).map ψ) (⊤ : X.Opens))
        ((((Modules.pullbackPushforwardAdjunction f).unit.app V).app (⊤ : Y.Opens)) s) =
      (((Modules.pullbackPushforwardAdjunction f).unit.app W).app (⊤ : Y.Opens))
        (Modules.Hom.app ψ (⊤ : Y.Opens) s) :=
  unit_app_naturality f ψ ⊤ s

/-- The canonical comparison from the pullback of the structure sheaf sends the unit
section to the unit section. -/
lemma pullbackObjUnitToUnit_unit_one {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Modules.Hom.app (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
        (⊤ : X.Opens))
      ((((Modules.pullbackPushforwardAdjunction f).unit.app
        (SheafOfModules.unit Y.ringCatSheaf)).app (⊤ : Y.Opens))
        (1 : Γ(Y, (⊤ : Y.Opens)))) = (1 : Γ(X, (⊤ : X.Opens))) := by
  have htr := (Modules.pullbackPushforwardAdjunction f).homEquiv_unit
    (X := SheafOfModules.unit Y.ringCatSheaf)
    (Y := (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (f := SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
  have hmath : (Modules.pullbackPushforwardAdjunction f).homEquiv
        (SheafOfModules.unit Y.ringCatSheaf) (SheafOfModules.unit X.ringCatSheaf)
        (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  rw [hmath] at htr
  have happ := congrArg (fun (k : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶
      (Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) ↦
    Scheme.Modules.Hom.app
      (M := (SheafOfModules.unit Y.ringCatSheaf : Y.Modules))
      (N := (Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))
      k (⊤ : Y.Opens)
      (show Γ((SheafOfModules.unit Y.ringCatSheaf : Y.Modules), (⊤ : Y.Opens)) from
        (1 : Γ(Y, (⊤ : Y.Opens))))) htr
  refine Eq.trans happ.symm ?_
  refine Eq.trans (SheafOfModules.unitToPushforwardObjUnit_val_app_apply
    f.toRingCatSheafHom (X := Opposite.op (⊤ : Y.Opens))
    (show Γ(Y, (⊤ : Y.Opens)) from 1)) ?_
  exact map_one ((f.toRingCatSheafHom.hom.app (Opposite.op (⊤ : Y.Opens))).hom)

/-- The pullback comparison of free sheaves carries the standard generator to the unit
section of the standard generator. -/
lemma pullbackFreeIso_inv_freeGenSection {X Y : Scheme.{u}} (f : X ⟶ Y) (I : Type u)
    (i : I) :
    (Modules.Hom.app (Modules.pullbackFreeIso f I).inv (⊤ : X.Opens))
        (freeGenSection X i) =
      (((Modules.pullbackPushforwardAdjunction f).unit.app
        (SheafOfModules.free (R := Y.ringCatSheaf) I)).app (⊤ : Y.Opens))
        (freeGenSection Y i) := by
  have hM := SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom
    (φ := f.toRingCatSheafHom) (I := I) i
  have happ := congrArg (fun (k : ((Modules.pullback f).obj
      (SheafOfModules.unit Y.ringCatSheaf) : X.Modules) ⟶
      (SheafOfModules.free (R := X.ringCatSheaf) I : X.Modules)) ↦
    Scheme.Modules.Hom.app
      (M := ((Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) : X.Modules))
      (N := (SheafOfModules.free (R := X.ringCatSheaf) I : X.Modules))
      k (⊤ : X.Opens)
      ((((Modules.pullbackPushforwardAdjunction f).unit.app
        (SheafOfModules.unit Y.ringCatSheaf)).app (⊤ : Y.Opens))
        (show Γ((SheafOfModules.unit Y.ringCatSheaf : Y.Modules), (⊤ : Y.Opens)) from
          (1 : Γ(Y, (⊤ : Y.Opens)))))) hM
  have hnat := unit_app_naturality f
    (show (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶
      (SheafOfModules.free (R := Y.ringCatSheaf) I : Y.Modules) from
      SheafOfModules.ιFree i) (⊤ : Y.Opens)
    (show Γ((SheafOfModules.unit Y.ringCatSheaf : Y.Modules), (⊤ : Y.Opens)) from
      (1 : Γ(Y, (⊤ : Y.Opens))))
  have h1 : (Modules.Hom.app (Modules.pullbackFreeIso f I).hom (⊤ : X.Opens))
      ((((Modules.pullbackPushforwardAdjunction f).unit.app
        (SheafOfModules.free (R := Y.ringCatSheaf) I)).app (⊤ : Y.Opens))
        (freeGenSection Y i)) = freeGenSection X i := by
    refine Eq.trans (congrArg
      (Modules.Hom.app (Modules.pullbackFreeIso f I).hom (⊤ : X.Opens)) hnat.symm) ?_
    refine Eq.trans happ ?_
    exact congrArg (Scheme.Modules.Hom.app
      (M := (SheafOfModules.unit X.ringCatSheaf : X.Modules))
      (N := (SheafOfModules.free (R := X.ringCatSheaf) I : X.Modules))
      (SheafOfModules.ιFree i) (⊤ : X.Opens))
      (pullbackObjUnitToUnit_unit_one f)
  have hcancel : ∀ z : Γ((Modules.pullback f).obj
        (SheafOfModules.free (R := Y.ringCatSheaf) I), (⊤ : X.Opens)),
      (Modules.Hom.app (Modules.pullbackFreeIso f I).inv (⊤ : X.Opens))
        ((Modules.Hom.app (Modules.pullbackFreeIso f I).hom (⊤ : X.Opens)) z) = z := by
    intro z
    have := congrArg (fun (k : (Modules.pullback f).obj
        (SheafOfModules.free (R := Y.ringCatSheaf) I) ⟶
        (Modules.pullback f).obj (SheafOfModules.free (R := Y.ringCatSheaf) I)) ↦
      (Modules.Hom.app k (⊤ : X.Opens)) z)
      (Modules.pullbackFreeIso f I).hom_inv_id
    exact this
  exact ((hcancel _).symm.trans (congrArg
    (Modules.Hom.app (Modules.pullbackFreeIso f I).inv (⊤ : X.Opens)) h1)).symm


/-- The pullback comparison of free sheaves carries the unit section of a standard
generator back to the standard generator. -/
lemma pullbackFreeIso_hom_unit_freeGenSection {X Y : Scheme.{u}} (f : X ⟶ Y) (I : Type u)
    (i : I) :
    (Modules.Hom.app (Modules.pullbackFreeIso f I).hom (⊤ : X.Opens))
        ((((Modules.pullbackPushforwardAdjunction f).unit.app
          (SheafOfModules.free (R := Y.ringCatSheaf) I)).app (⊤ : Y.Opens))
          (freeGenSection Y i)) = freeGenSection X i := by
  rw [← pullbackFreeIso_inv_freeGenSection]
  have hc := congrArg (fun (k : (SheafOfModules.free (R := X.ringCatSheaf) I : X.Modules) ⟶
      (SheafOfModules.free (R := X.ringCatSheaf) I : X.Modules)) ↦
    (Modules.Hom.app k (⊤ : X.Opens)) (freeGenSection X i))
    (Modules.pullbackFreeIso f I).inv_hom_id
  exact hc


/-- A section of a presheaf of modules on a space is determined by its value on the whole
space. -/
lemma sections_ext_top {X : Scheme.{u}} {M : X.Modules}
    (s t : M.val.sections)
    (h : s.1 (Opposite.op (⊤ : X.Opens)) = t.1 (Opposite.op (⊤ : X.Opens))) : s = t := by
  refine _root_.PresheafOfModules.sections_ext s t (fun U ↦ ?_)
  have hs := _root_.PresheafOfModules.sections_property s
    (X := Opposite.op (⊤ : X.Opens)) (Y := U) (homOfLE le_top).op
  have ht := _root_.PresheafOfModules.sections_property t
    (X := Opposite.op (⊤ : X.Opens)) (Y := U) (homOfLE le_top).op
  rw [← hs, ← ht, h]

/-- **Morphisms out of a free sheaf are determined by the images of the standard
generators.** -/
lemma free_hom_ext {X : Scheme.{u}} {I : Type u} {M : X.Modules}
    (φ ψ : (SheafOfModules.free (R := X.ringCatSheaf) I : X.Modules) ⟶ M)
    (h : ∀ i, Modules.Hom.app φ (⊤ : X.Opens) (freeGenSection X i) =
        Modules.Hom.app ψ (⊤ : X.Opens) (freeGenSection X i)) : φ = ψ := by
  apply (SheafOfModules.freeHomEquiv M).injective
  funext i
  rw [SheafOfModules.freeHomEquiv_apply, SheafOfModules.freeHomEquiv_apply]
  exact sections_ext_top _ _ (h i)

end FreeGenerators

/-- The inverse of the exterior power of a linear equivalence, on a wedge. -/
lemma _root_.LinearEquiv.exteriorPower_symm_apply_ιMulti {R : Type u} [CommRing R]
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (k : ℕ) (v : Fin k → N) :
    (e.exteriorPower k).symm (exteriorPower.ιMulti R k v) =
      exteriorPower.ιMulti R k (fun j ↦ e.symm (v j)) := by
  apply (e.exteriorPower k).injective
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.exteriorPower_apply_ιMulti]
  exact congrArg (exteriorPower.ιMulti R k)
    (funext fun j ↦ (e.apply_symm_apply (v j)).symm)

/-- **The Plücker basis identification on standard basis vectors**: the module-level
identification `⋀^q R^m ≅ R^{C(m,q)}` sends the basis vector indexed by a `q`-element
subset to the wedge of the corresponding standard basis vectors. -/
lemma freeExteriorPowerModuleEquiv_symm_single (R : Type u) [CommRing R] (q m : ℕ)
    (s : Set.powersetCard (Fin m) q) :
    (freeExteriorPowerModuleEquiv R q m).symm
        (Finsupp.single (ULift.up (powersetCardEquivFin q m s)) 1) =
      exteriorPower.ιMulti R q
        (fun j ↦ Finsupp.single
          (ULift.up (Set.powersetCard.ofFinEmbEquiv.symm s j)) (1 : R)) := by
  rw [freeExteriorPowerModuleEquiv]
  simp only [LinearEquiv.trans_symm, LinearEquiv.symm_symm, LinearEquiv.trans_apply]
  rw [uliftFinFinsuppEquivPi_single, exteriorPowerPiEquiv_apply_single]
  rw [show exteriorPower.ιMulti_family R q (Pi.basisFun R (Fin m)) s =
      exteriorPower.ιMulti R q
        (fun j ↦ Pi.basisFun R (Fin m) (Set.powersetCard.ofFinEmbEquiv.symm s j)) from rfl,
    LinearEquiv.exteriorPower_symm_apply_ιMulti]
  refine congrArg (exteriorPower.ιMulti R q) (funext fun j ↦ ?_)
  rw [Pi.basisFun_apply]
  exact uliftFinFinsuppEquivPi_symm_single m _

/-- **The exterior power of a finite free sheaf on an affine scheme is finite free**: on
`Spec R` the comparison runs through the tilde model, where it is the Plücker basis
identification `⋀^q R^m ≅ R^{C(m,q)}`. -/
noncomputable def freeExteriorPowerSpecIso (R : CommRingCat.{u}) (q m : ℕ) :
    Modules.exteriorPower
        (SheafOfModules.free (R := (Spec R).ringCatSheaf) (ULift.{u} (Fin m))) q ≅
      SheafOfModules.free (R := (Spec R).ringCatSheaf) (ULift.{u} (Fin (m.choose q))) :=
  Modules.exteriorPowerIso
      (AlgebraicGeometry.tildeFinsupp (R := R) (ULift.{u} (Fin m))).symm q ≪≫
    (AlgebraicGeometry.exteriorPowerTildeIso
      (ModuleCat.of R (ULift.{u} (Fin m) →₀ R)) q).symm ≪≫
    (AlgebraicGeometry.tilde.functor R).mapIso
      (freeExteriorPowerModuleEquiv R q m).toModuleIso ≪≫
    AlgebraicGeometry.tildeFinsupp (R := R) (ULift.{u} (Fin (m.choose q)))


/-- Global sections of a morphism of sheaves of modules on an affine scheme are its
sections over the top open. -/
lemma moduleSpecΓFunctor_map_apply {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    (ψ : M ⟶ N) (x : Γ(M, (⊤ : (Spec R).Opens))) :
    (moduleSpecΓFunctor.map ψ).hom x = (Modules.Hom.app ψ (⊤ : (Spec R).Opens)) x := rfl

set_option maxHeartbeats 3200000 in
/-- **The Plücker identification of a free sheaf on standard generators**: over an affine
scheme the inverse of `freeExteriorPowerSpecIso` sends the standard generator indexed by a
`q`-element subset to the wedge of the corresponding standard generators. -/
lemma freeExteriorPowerSpecIso_inv_generator (R : CommRingCat.{u}) (q m : ℕ)
    (s : Set.powersetCard (Fin m) q) :
    (Modules.Hom.app (freeExteriorPowerSpecIso R q m).inv (⊤ : (Spec R).Opens))
        (freeGenSection (Spec R) (ULift.up (powersetCardEquivFin q m s))) =
      ((Modules.toExteriorPower (SheafOfModules.free (R := (Spec R).ringCatSheaf)
            (ULift.{u} (Fin m))) q).app (Opposite.op (⊤ : (Spec R).Opens))).hom
        (exteriorPower.ιMulti Γ(Spec R, (⊤ : (Spec R).Opens)) q
          (fun j ↦ freeGenSection (Spec R)
            (ULift.up (Set.powersetCard.ofFinEmbEquiv.symm s j)))) := by
  have hD : (Modules.Hom.app
        (AlgebraicGeometry.tildeFinsupp (R := R)
          (ULift.{u} (Fin (m.choose q)))).inv (⊤ : (Spec R).Opens))
      (freeGenSection (Spec R) (ULift.up (powersetCardEquivFin q m s))) =
      (AlgebraicGeometry.tilde.toTildeΓNatIso.hom.app
        (ModuleCat.of R (ULift.{u} (Fin (m.choose q)) →₀ R))).hom
        (Finsupp.single (ULift.up (powersetCardEquivFin q m s)) 1) := by
    rw [← freeModuleSpecΓIso_single]
    have h1 : (AlgebraicGeometry.freeModuleSpecΓIso (R := R)
          (ULift.{u} (Fin (m.choose q)))).hom ≫
        moduleSpecΓFunctor.map (AlgebraicGeometry.tildeFinsupp
          (R := R) (ULift.{u} (Fin (m.choose q)))).inv =
        AlgebraicGeometry.tilde.toTildeΓNatIso.hom.app
          (ModuleCat.of R (ULift.{u} (Fin (m.choose q)) →₀ R)) := by
      rw [AlgebraicGeometry.freeModuleSpecΓIso]
      simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc,
        ← Functor.map_comp, Iso.hom_inv_id, Functor.map_id, Category.comp_id]
      rfl
    exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp h1) _
  have hC : ∀ x : (ULift.{u} (Fin (m.choose q)) →₀ R),
      (Modules.Hom.app ((AlgebraicGeometry.tilde.functor R).map
          (freeExteriorPowerModuleEquiv R q m).toModuleIso.inv) (⊤ : (Spec R).Opens))
        ((AlgebraicGeometry.tilde.toTildeΓNatIso.hom.app
          (ModuleCat.of R (ULift.{u} (Fin (m.choose q)) →₀ R))).hom x) =
      (AlgebraicGeometry.tilde.toTildeΓNatIso.hom.app
        (ModuleCat.of R (⋀[R]^q (ULift.{u} (Fin m) →₀ R) :
          Submodule R (ExteriorAlgebra R (ULift.{u} (Fin m) →₀ R))))).hom
        ((freeExteriorPowerModuleEquiv R q m).symm x) := by
    intro x
    have hn := AlgebraicGeometry.tilde.toTildeΓNatIso.hom.naturality
      (freeExteriorPowerModuleEquiv R q m).toModuleIso.inv
    exact (DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp hn) x).symm
  have hgen : ∀ j : Fin m,
      (Modules.Hom.app (AlgebraicGeometry.tildeFinsupp (R := R)
          (ULift.{u} (Fin m))).hom (⊤ : (Spec R).Opens))
        ((AlgebraicGeometry.tilde.toTildeΓNatIso.hom.app
          (ModuleCat.of R (ULift.{u} (Fin m) →₀ R))).hom
          (Finsupp.single (ULift.up j) (1 : R))) =
        freeGenSection (Spec R) (ULift.up j) := by
    intro j
    rw [← freeModuleSpecΓIso_single]
    rfl
  have hsplit : (Modules.Hom.app (freeExteriorPowerSpecIso R q m).inv
        (⊤ : (Spec R).Opens))
      (freeGenSection (Spec R) (ULift.up (powersetCardEquivFin q m s))) =
      (Modules.Hom.app (Modules.exteriorPowerMap
          (AlgebraicGeometry.tildeFinsupp (R := R) (ULift.{u} (Fin m))).hom q)
          (⊤ : (Spec R).Opens))
        ((Modules.Hom.app (AlgebraicGeometry.exteriorPowerTildeIso
            (ModuleCat.of R (ULift.{u} (Fin m) →₀ R)) q).hom (⊤ : (Spec R).Opens))
          ((Modules.Hom.app ((AlgebraicGeometry.tilde.functor R).map
              (freeExteriorPowerModuleEquiv R q m).toModuleIso.inv)
              (⊤ : (Spec R).Opens))
            ((Modules.Hom.app (AlgebraicGeometry.tildeFinsupp (R := R)
                (ULift.{u} (Fin (m.choose q)))).inv (⊤ : (Spec R).Opens))
              (freeGenSection (Spec R)
                (ULift.up (powersetCardEquivFin q m s)))))) := rfl
  rw [hsplit, hD, hC, freeExteriorPowerModuleEquiv_symm_single]
  have hB : ∀ w : (⋀[R]^q (ULift.{u} (Fin m) →₀ R) :
        Submodule R (ExteriorAlgebra R (ULift.{u} (Fin m) →₀ R))),
      (Modules.Hom.app (AlgebraicGeometry.exteriorPowerTildeIso
          (ModuleCat.of R (ULift.{u} (Fin m) →₀ R)) q).hom (⊤ : (Spec R).Opens))
        ((AlgebraicGeometry.tilde.toTildeΓNatIso.hom.app
          (ModuleCat.of R (⋀[R]^q (ULift.{u} (Fin m) →₀ R) :
            Submodule R (ExteriorAlgebra R (ULift.{u} (Fin m) →₀ R))))).hom w) =
      AlgebraicGeometry.exteriorPowerTildeΓEquiv
        (ModuleCat.of R (ULift.{u} (Fin m) →₀ R)) q w := fun _ ↦ rfl
  rw [hB, AlgebraicGeometry.exteriorPowerTildeΓEquiv_ιMulti]
  refine Eq.trans (Scheme.Modules.exteriorPowerMap_app_unit_ιMulti
    (AlgebraicGeometry.tildeFinsupp (R := R) (ULift.{u} (Fin m))).hom q
    (⊤ : (Spec R).Opens)
    (fun i ↦ show Γ(AlgebraicGeometry.tilde
        (ModuleCat.of R (ULift.{u} (Fin m) →₀ R)), (⊤ : (Spec R).Opens)) from
      AlgebraicGeometry.tilde.toOpen
        (ModuleCat.of R (ULift.{u} (Fin m) →₀ R)) ⊤
        (Finsupp.single (ULift.up (Set.powersetCard.ofFinEmbEquiv.symm s i)) 1))) ?_
  exact congrArg _ (congrArg (exteriorPower.ιMulti Γ(Spec R, (⊤ : (Spec R).Opens)) q)
    (funext fun j ↦ hgen _))

/-- **The exterior power of a finite free sheaf is finite free**, on an arbitrary scheme:
base change the affine case along the structure morphism to `Spec ℤ`, using that the
exterior-power pullback comparison is an isomorphism for vector bundles. -/
noncomputable def freeExteriorPowerIso (X : Scheme.{u}) (q m : ℕ) :
    Modules.exteriorPower
        (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m))) q ≅
      SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin (m.choose q))) :=
  let f : X ⟶ Spec (CommRingCat.of (ULift.{u} ℤ)) := specULiftZIsTerminal.from X
  let E : (Spec (CommRingCat.of (ULift.{u} ℤ))).Modules :=
    SheafOfModules.free (R := (Spec (CommRingCat.of (ULift.{u} ℤ))).ringCatSheaf)
      (ULift.{u} (Fin m))
  haveI : E.IsQuasicoherent := by dsimp only [E]; infer_instance
  haveI hE : Modules.IsProjectiveOfRank m E :=
    Modules.free_isProjectiveOfRank _ m
  Modules.exteriorPowerIso (Modules.pullbackFreeIso f (ULift.{u} (Fin m))).symm q ≪≫
    (Modules.pullbackExteriorPowerIso f E hE q).symm ≪≫
    (Modules.pullback f).mapIso (freeExteriorPowerSpecIso _ q m) ≪≫
    Modules.pullbackFreeIso f (ULift.{u} (Fin (m.choose q)))


/-- Global-sections form of the pullback comparison on unit wedges. -/
lemma pullbackExteriorPower_app_unit_top {T S : Scheme.{u}} (f : T ⟶ S) (V : S.Modules)
    (q : ℕ) (w : (⋀[Γ(S, (⊤ : S.Opens))]^q Γ(V, (⊤ : S.Opens)) :
      Submodule Γ(S, (⊤ : S.Opens))
        (ExteriorAlgebra Γ(S, (⊤ : S.Opens)) Γ(V, (⊤ : S.Opens))))) :
    (Modules.Hom.app (AlgebraicGeometry.pullbackExteriorPower f V q) (⊤ : T.Opens))
        ((((Modules.pullbackPushforwardAdjunction f).unit.app
          (Modules.exteriorPower V q)).app (⊤ : S.Opens))
          (((Modules.toExteriorPower V q).app
            (Opposite.op (⊤ : S.Opens))).hom w)) =
      AlgebraicGeometry.pullbackWedgeApp f V q (⊤ : S.Opens) w :=
  AlgebraicGeometry.pullbackExteriorPower_app_unit f V q (⊤ : S.Opens) w

/-- Global-sections form of the pullback wedge comparison on a wedge of sections. -/
lemma pullbackWedgeApp_ιMulti_top {T S : Scheme.{u}} (f : T ⟶ S) (V : S.Modules) (q : ℕ)
    (v : Fin q → Γ(V, (⊤ : S.Opens))) :
    AlgebraicGeometry.pullbackWedgeApp f V q (⊤ : S.Opens)
        (exteriorPower.ιMulti Γ(S, (⊤ : S.Opens)) q v) =
      ((Modules.toExteriorPower ((Modules.pullback f).obj V) q).app
        (Opposite.op (⊤ : T.Opens))).hom
        (exteriorPower.ιMulti Γ(T, (⊤ : T.Opens)) q
          (fun i ↦ show Γ((Modules.pullback f).obj V, (⊤ : T.Opens)) from
            (((Modules.pullbackPushforwardAdjunction f).unit.app V).app
              (⊤ : S.Opens)) (v i))) :=
  AlgebraicGeometry.pullbackWedgeApp_ιMulti f V q (⊤ : S.Opens) v

set_option maxHeartbeats 3200000 in
/-- **The Plücker identification of a free sheaf on standard generators**: on an arbitrary
scheme the inverse of `freeExteriorPowerIso` sends the standard generator indexed by a
`q`-element subset `s` to the wedge of the standard generators indexed by the elements of
`s`.  This is the affine computation `freeExteriorPowerSpecIso_inv_generator` transported
along the structure morphism to `Spec ℤ`, using that standard generators and unit wedges
are compatible with pullback. -/
lemma freeExteriorPowerIso_inv_generator (X : Scheme.{u}) (q m : ℕ)
    (s : Set.powersetCard (Fin m) q) :
    (Modules.Hom.app (freeExteriorPowerIso X q m).inv (⊤ : X.Opens))
        (freeGenSection X (ULift.up (powersetCardEquivFin q m s))) =
      ((Modules.toExteriorPower (SheafOfModules.free (R := X.ringCatSheaf)
            (ULift.{u} (Fin m))) q).app (Opposite.op (⊤ : X.Opens))).hom
        (exteriorPower.ιMulti Γ(X, (⊤ : X.Opens)) q
          (fun j ↦ freeGenSection X
            (ULift.up (Set.powersetCard.ofFinEmbEquiv.symm s j)))) := by
  set Z := Spec (CommRingCat.of (ULift.{u} ℤ)) with hZ
  set f : X ⟶ Z := specULiftZIsTerminal.from X with hf
  set E : Z.Modules := SheafOfModules.free (R := Z.ringCatSheaf) (ULift.{u} (Fin m))
    with hE
  have hsplit : (Modules.Hom.app (freeExteriorPowerIso X q m).inv (⊤ : X.Opens))
        (freeGenSection X (ULift.up (powersetCardEquivFin q m s))) =
      (Modules.Hom.app (Modules.exteriorPowerMap
          (Modules.pullbackFreeIso f (ULift.{u} (Fin m))).hom q) (⊤ : X.Opens))
        ((Modules.Hom.app (AlgebraicGeometry.pullbackExteriorPower f E q) (⊤ : X.Opens))
          ((Modules.Hom.app ((Modules.pullback f).map
              (freeExteriorPowerSpecIso (CommRingCat.of (ULift.{u} ℤ)) q m).inv)
              (⊤ : X.Opens))
            ((Modules.Hom.app (Modules.pullbackFreeIso f
                (ULift.{u} (Fin (m.choose q)))).inv (⊤ : X.Opens))
              (freeGenSection X
                (ULift.up (powersetCardEquivFin q m s)))))) := rfl
  rw [hsplit, pullbackFreeIso_inv_freeGenSection,
    unit_app_naturality_top f
      (freeExteriorPowerSpecIso (CommRingCat.of (ULift.{u} ℤ)) q m).inv,
    freeExteriorPowerSpecIso_inv_generator,
    pullbackExteriorPower_app_unit_top f E q]
  refine Eq.trans (congrArg (Modules.Hom.app (Modules.exteriorPowerMap
      (Modules.pullbackFreeIso f (ULift.{u} (Fin m))).hom q) (⊤ : X.Opens))
    (pullbackWedgeApp_ιMulti_top f E q
      (fun j ↦ freeGenSection Z
        (ULift.up (Set.powersetCard.ofFinEmbEquiv.symm s j))))) ?_
  refine Eq.trans (Scheme.Modules.exteriorPowerMap_app_unit_ιMulti
    (Modules.pullbackFreeIso f (ULift.{u} (Fin m))).hom q (⊤ : X.Opens) _) ?_
  exact congrArg _ (congrArg (exteriorPower.ιMulti Γ(X, (⊤ : X.Opens)) q)
    (funext fun j ↦ pullbackFreeIso_hom_unit_freeGenSection f _ _))


set_option maxHeartbeats 3200000 in
/-- **The identification `⋀^q O^{⊕m} ≅ O^{⊕C(m,q)}` is compatible with base change**: the
pullback of the identification of `X` along `g : T ⟶ X`, read through the free-sheaf and
exterior-power pullback comparisons, is the identification of `T`.  Both sides are
morphisms out of a free sheaf, so it suffices to compare them on standard generators. -/
lemma pullback_freeExteriorPowerIso_inv {X T : Scheme.{u}} (g : T ⟶ X) (q m : ℕ) :
    (Modules.pullbackFreeIso g (ULift.{u} (Fin (m.choose q)))).inv ≫
        (Modules.pullback g).map (freeExteriorPowerIso X q m).inv ≫
        AlgebraicGeometry.pullbackExteriorPower g
          (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m))) q =
      (freeExteriorPowerIso T q m).inv ≫
        Modules.exteriorPowerMap
          (Modules.pullbackFreeIso g (ULift.{u} (Fin m))).inv q := by
  refine free_hom_ext _ _ (fun J ↦ ?_)
  obtain ⟨s, rfl⟩ : ∃ s : Set.powersetCard (Fin m) q,
      ULift.up (powersetCardEquivFin q m s) = J :=
    ⟨(powersetCardEquivFin q m).symm J.down, by simp⟩
  have hL : (Modules.Hom.app ((Modules.pullbackFreeIso g
          (ULift.{u} (Fin (m.choose q)))).inv ≫
        (Modules.pullback g).map (freeExteriorPowerIso X q m).inv ≫
        AlgebraicGeometry.pullbackExteriorPower g
          (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m))) q)
        (⊤ : T.Opens))
      (freeGenSection T (ULift.up (powersetCardEquivFin q m s))) =
      (Modules.Hom.app (AlgebraicGeometry.pullbackExteriorPower g
          (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m))) q)
          (⊤ : T.Opens))
        ((Modules.Hom.app ((Modules.pullback g).map
            (freeExteriorPowerIso X q m).inv) (⊤ : T.Opens))
          ((Modules.Hom.app (Modules.pullbackFreeIso g
              (ULift.{u} (Fin (m.choose q)))).inv (⊤ : T.Opens))
            (freeGenSection T (ULift.up (powersetCardEquivFin q m s))))) := rfl
  have hR : (Modules.Hom.app ((freeExteriorPowerIso T q m).inv ≫
        Modules.exteriorPowerMap
          (Modules.pullbackFreeIso g (ULift.{u} (Fin m))).inv q) (⊤ : T.Opens))
      (freeGenSection T (ULift.up (powersetCardEquivFin q m s))) =
      (Modules.Hom.app (Modules.exteriorPowerMap
          (Modules.pullbackFreeIso g (ULift.{u} (Fin m))).inv q) (⊤ : T.Opens))
        ((Modules.Hom.app (freeExteriorPowerIso T q m).inv (⊤ : T.Opens))
          (freeGenSection T (ULift.up (powersetCardEquivFin q m s)))) := rfl
  rw [hL, hR, pullbackFreeIso_inv_freeGenSection,
    unit_app_naturality_top g (freeExteriorPowerIso X q m).inv,
    freeExteriorPowerIso_inv_generator, freeExteriorPowerIso_inv_generator,
    pullbackExteriorPower_app_unit_top g
      (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m))) q]
  refine Eq.trans (pullbackWedgeApp_ιMulti_top g
    (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m))) q
    (fun j ↦ freeGenSection X
      (ULift.up (Set.powersetCard.ofFinEmbEquiv.symm s j)))) ?_
  refine Eq.trans ?_ (Scheme.Modules.exteriorPowerMap_app_unit_ιMulti
    (Modules.pullbackFreeIso g (ULift.{u} (Fin m))).inv q (⊤ : T.Opens) _).symm
  exact congrArg _ (congrArg (exteriorPower.ιMulti Γ(T, (⊤ : T.Opens)) q)
    (funext fun j ↦ (pullbackFreeIso_inv_freeGenSection g _ _).symm))


/-- The coordinate identification of the global sections of a finite free sheaf on an
affine scheme. -/
noncomputable def freeSectionsPiEquiv (R : CommRingCat.{u}) (N : ℕ) :
    (Fin N → R) ≃ₗ[R] moduleSpecΓFunctor.obj
      (SheafOfModules.free (R := (Spec R).ringCatSheaf) (ULift.{u} (Fin N))) :=
  (Modules.FreeQuotient.uliftFinFinsuppEquivPi (R := R) N).symm.trans
    (AlgebraicGeometry.freeModuleSpecΓIso (R := R) (ULift.{u} (Fin N))).toLinearEquiv

@[simp]
lemma freeSectionsPiEquiv_single (R : CommRingCat.{u}) (N : ℕ) (k : Fin N) :
    freeSectionsPiEquiv R N (Pi.single k 1) =
      freeGenSection (Spec R) (ULift.up k) := by
  rw [freeSectionsPiEquiv, LinearEquiv.trans_apply, uliftFinFinsuppEquivPi_symm_single]
  exact freeModuleSpecΓIso_single R (ULift.up k)

set_option maxHeartbeats 6400000 in
/-- **The Plücker identification on global sections**: on an affine scheme the inverse of
`freeExteriorPowerIso` is, in coordinates, the Plücker basis identification
`exteriorPowerPiEquiv` followed by the comparison `⋀^q Γ(O^{⊕m}) ≅ Γ(⋀^q O^{⊕m})`. -/
lemma freeExteriorPowerIso_inv_sections (R : CommRingCat.{u}) (q m : ℕ) :
    (moduleSpecΓFunctor.map (freeExteriorPowerIso (Spec R) q m).inv).hom ∘ₗ
        (freeSectionsPiEquiv R (m.choose q)).toLinearMap =
      (AlgebraicGeometry.exteriorPowerΓMapₗ
          (SheafOfModules.free (R := (Spec R).ringCatSheaf) (ULift.{u} (Fin m))) q) ∘ₗ
        ((exteriorPower.map q (freeSectionsPiEquiv R m).toLinearMap) ∘ₗ
          (exteriorPowerPiEquiv R q m).toLinearMap) := by
  apply (Pi.basisFun R (Fin (m.choose q))).ext
  intro J
  set s : Set.powersetCard (Fin m) q := (powersetCardEquivFin q m).symm J with hs
  have hJ : powersetCardEquivFin q m s = J := by
    rw [hs, Equiv.apply_symm_apply]
  rw [Pi.basisFun_apply]
  show (moduleSpecΓFunctor.map (freeExteriorPowerIso (Spec R) q m).inv).hom
      (freeSectionsPiEquiv R (m.choose q) (Pi.single J 1)) = _
  rw [freeSectionsPiEquiv_single, ← hJ, moduleSpecΓFunctor_map_apply,
    freeExteriorPowerIso_inv_generator]
  show _ = AlgebraicGeometry.exteriorPowerΓMapₗ _ q
    ((exteriorPower.map q (freeSectionsPiEquiv R m).toLinearMap)
      (exteriorPowerPiEquiv R q m (Pi.single (powersetCardEquivFin q m s) 1)))
  rw [exteriorPowerPiEquiv_apply_single,
    show exteriorPower.ιMulti_family R q (Pi.basisFun R (Fin m)) s =
      exteriorPower.ιMulti R q
        (fun j ↦ Pi.basisFun R (Fin m) (Set.powersetCard.ofFinEmbEquiv.symm s j)) from rfl,
    exteriorPower.map_apply_ιMulti, AlgebraicGeometry.exteriorPowerΓMapₗ_apply,
    AlgebraicGeometry.exteriorPowerΓMap_ιMulti]
  refine congrArg _ (congrArg
    (exteriorPower.ιMulti Γ(Spec R, (⊤ : (Spec R).Opens)) q) (funext fun j ↦ ?_))
  show _ = freeSectionsPiEquiv R m (Pi.basisFun R (Fin m)
    (Set.powersetCard.ofFinEmbEquiv.symm s j))
  rw [Pi.basisFun_apply, freeSectionsPiEquiv_single]

end FreeExteriorPower


section FreeQuotientPlucker

/-- **The Plücker quotient of a strict free quotient**: the top exterior power of a
rank-`q` quotient of `O^{⊕m}`, presented as a line-bundle quotient of `O^{⊕C(m,q)}`
through the identification `freeExteriorPowerIso`. -/
noncomputable def freeQuotientPlucker {W : Scheme.{u}} {q m : ℕ}
    (y : Modules.FreeQuotient q (ULift.{u} (Fin m)) W) :
    Modules.FreeQuotient 1 (ULift.{u} (Fin (m.choose q))) W where
  Q := Modules.exteriorPower y.Q q
  isQuasicoherent := by
    haveI := y.isQuasicoherent
    infer_instance
  isProjectiveOfRank := by
    haveI := y.isQuasicoherent
    have h := Modules.isProjectiveOfRank_exteriorPower y.Q y.isProjectiveOfRank q
    rwa [Nat.choose_self] at h
  π := (freeExteriorPowerIso W q m).inv ≫ Modules.exteriorPowerMap y.π q
  epi := by
    haveI := y.isQuasicoherent
    haveI := y.epi
    haveI : IsIso (freeExteriorPowerIso W q m).inv := inferInstance
    haveI : Epi (Modules.exteriorPowerMap y.π q) :=
      Modules.epi_exteriorPowerMap y.π q
    exact epi_comp _ _


set_option maxHeartbeats 1600000 in
/-- **Normalizing the Plücker quotient**: the Plücker quotient of a relative quotient of a
free sheaf, transported to the free model `O^{⊕C(m,q)}` and normalized to a strict free
quotient on the test scheme, is the Plücker quotient of the normalization. -/
lemma toFreeQuotient_plucker {S : Scheme.{u}} {q m : ℕ} {T : Over S}
    (x : Modules.PullbackQuotient q
      (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin m))) T) :
    (Modules.FreeQuotient.setoid 1 (ULift.{u} (Fin (m.choose q))) T.left).r
      ((Modules.PullbackQuotient.mapAmbientIso (freeExteriorPowerIso S q m)
        x.plucker).toFreeQuotient)
      (freeQuotientPlucker x.toFreeQuotient) := by
  haveI := x.isQuasicoherent
  refine ⟨Iso.refl _, ?_⟩
  show _ ≫ 𝟙 _ = _
  rw [Category.comp_id]
  show (Modules.pullbackFreeIso T.hom (ULift.{u} (Fin (m.choose q)))).inv ≫
      ((Modules.pullback T.hom).map (freeExteriorPowerIso S q m).inv ≫
        (AlgebraicGeometry.pullbackExteriorPower T.hom
            (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin m))) q ≫
          Modules.exteriorPowerMap x.π q)) =
    (freeExteriorPowerIso T.left q m).inv ≫
      Modules.exteriorPowerMap
        ((Modules.pullbackFreeIso T.hom (ULift.{u} (Fin m))).inv ≫ x.π) q
  rw [Modules.exteriorPowerMap_comp]
  calc (Modules.pullbackFreeIso T.hom (ULift.{u} (Fin (m.choose q)))).inv ≫
        ((Modules.pullback T.hom).map (freeExteriorPowerIso S q m).inv ≫
          (AlgebraicGeometry.pullbackExteriorPower T.hom
              (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin m))) q ≫
            Modules.exteriorPowerMap x.π q))
      = ((Modules.pullbackFreeIso T.hom (ULift.{u} (Fin (m.choose q)))).inv ≫
          (Modules.pullback T.hom).map (freeExteriorPowerIso S q m).inv ≫
          AlgebraicGeometry.pullbackExteriorPower T.hom
            (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin m))) q) ≫
        Modules.exteriorPowerMap x.π q := by
        simp only [Category.assoc]
    _ = ((freeExteriorPowerIso T.left q m).inv ≫
          Modules.exteriorPowerMap
            (Modules.pullbackFreeIso T.hom (ULift.{u} (Fin m))).inv q) ≫
        Modules.exteriorPowerMap x.π q := by
        rw [pullback_freeExteriorPowerIso_inv T.hom q m]
    _ = (freeExteriorPowerIso T.left q m).inv ≫
        Modules.exteriorPowerMap
          (Modules.pullbackFreeIso T.hom (ULift.{u} (Fin m))).inv q ≫
        Modules.exteriorPowerMap x.π q := by
        simp only [Category.assoc]


set_option maxHeartbeats 1600000 in
/-- **The Plücker quotient of a strict free quotient commutes with base change.** -/
lemma freeQuotientPlucker_pullback {W W' : Scheme.{u}} (g : W' ⟶ W) {q m : ℕ}
    (y : Modules.FreeQuotient q (ULift.{u} (Fin m)) W) :
    (Modules.FreeQuotient.setoid 1 (ULift.{u} (Fin (m.choose q))) W').r
      ((freeQuotientPlucker y).pullback g)
      (freeQuotientPlucker (y.pullback g)) := by
  haveI := y.isQuasicoherent
  refine ⟨Modules.pullbackExteriorPowerIso g y.Q y.isProjectiveOfRank q, ?_⟩
  show ((Modules.pullbackFreeIso g (ULift.{u} (Fin (m.choose q)))).inv ≫
      (Modules.pullback g).map ((freeExteriorPowerIso W q m).inv ≫
        Modules.exteriorPowerMap y.π q)) ≫
      AlgebraicGeometry.pullbackExteriorPower g y.Q q =
    (freeExteriorPowerIso W' q m).inv ≫
      Modules.exteriorPowerMap
        ((Modules.pullbackFreeIso g (ULift.{u} (Fin m))).inv ≫
          (Modules.pullback g).map y.π) q
  rw [Functor.map_comp, Modules.exteriorPowerMap_comp]
  calc ((Modules.pullbackFreeIso g (ULift.{u} (Fin (m.choose q)))).inv ≫
        ((Modules.pullback g).map (freeExteriorPowerIso W q m).inv ≫
          (Modules.pullback g).map (Modules.exteriorPowerMap y.π q))) ≫
        AlgebraicGeometry.pullbackExteriorPower g y.Q q
      = (Modules.pullbackFreeIso g (ULift.{u} (Fin (m.choose q)))).inv ≫
        (Modules.pullback g).map (freeExteriorPowerIso W q m).inv ≫
        ((Modules.pullback g).map (Modules.exteriorPowerMap y.π q) ≫
          AlgebraicGeometry.pullbackExteriorPower g y.Q q) := by
        simp only [Category.assoc]
    _ = (Modules.pullbackFreeIso g (ULift.{u} (Fin (m.choose q)))).inv ≫
        (Modules.pullback g).map (freeExteriorPowerIso W q m).inv ≫
        (AlgebraicGeometry.pullbackExteriorPower g
            (SheafOfModules.free (R := W.ringCatSheaf) (ULift.{u} (Fin m))) q ≫
          Modules.exteriorPowerMap ((Modules.pullback g).map y.π) q) := by
        rw [← AlgebraicGeometry.pullbackExteriorPower_naturality g
          (SheafOfModules.free (R := W.ringCatSheaf) (ULift.{u} (Fin m))) q y.π]
    _ = ((Modules.pullbackFreeIso g (ULift.{u} (Fin (m.choose q)))).inv ≫
        (Modules.pullback g).map (freeExteriorPowerIso W q m).inv ≫
        AlgebraicGeometry.pullbackExteriorPower g
          (SheafOfModules.free (R := W.ringCatSheaf) (ULift.{u} (Fin m))) q) ≫
          Modules.exteriorPowerMap ((Modules.pullback g).map y.π) q := by
        simp only [Category.assoc]
    _ = ((freeExteriorPowerIso W' q m).inv ≫
        Modules.exteriorPowerMap
          (Modules.pullbackFreeIso g (ULift.{u} (Fin m))).inv q) ≫
        Modules.exteriorPowerMap ((Modules.pullback g).map y.π) q := by
        rw [pullback_freeExteriorPowerIso_inv g q m]
    _ = _ := by simp only [Category.assoc]



set_option maxHeartbeats 3200000 in
/-- **The kernel of the Plücker quotient, on an affine spectrum**: in coordinates it is
the Plücker kernel of the kernel of the given presentation. -/
lemma freeQuotientPlucker_kernelSubmodule {R : CommRingCat.{u}} {q m : ℕ}
    (z : Modules.FreeQuotient q (ULift.{u} (Fin m)) (Spec R)) :
    (freeQuotientPlucker z).kernelSubmodule =
      LinearMap.ker (pluckerLinearMap R q m z.kernelSubmodule) := by
  haveI := z.isQuasicoherent
  -- the module map of the Plücker quotient, in coordinates
  have hmap : (freeQuotientPlucker z).moduleMapPi =
      (AlgebraicGeometry.exteriorPowerΓMapₗ z.Q q).comp
        ((exteriorPower.map q z.moduleMapPi).comp
          (exteriorPowerPiEquiv R q m).toLinearMap) := by
    have h1 : (freeQuotientPlucker z).moduleMapPi =
        (moduleSpecΓFunctor.map (Modules.exteriorPowerMap z.π q)).hom.comp
          ((moduleSpecΓFunctor.map (freeExteriorPowerIso (Spec R) q m).inv).hom.comp
            (freeSectionsPiEquiv R (m.choose q)).toLinearMap) := by
      rw [Modules.FreeQuotient.moduleMapPi, Modules.FreeQuotient.moduleMap]
      rfl
    rw [h1, freeExteriorPowerIso_inv_sections]
    apply LinearMap.ext
    intro x
    show (moduleSpecΓFunctor.map (Modules.exteriorPowerMap z.π q)).hom
        (AlgebraicGeometry.exteriorPowerΓMapₗ _ q
          ((exteriorPower.map q (freeSectionsPiEquiv R m).toLinearMap)
            (exteriorPowerPiEquiv R q m x))) = _
    show _ = AlgebraicGeometry.exteriorPowerΓMapₗ z.Q q
      ((exteriorPower.map q z.moduleMapPi) (exteriorPowerPiEquiv R q m x))
    rw [AlgebraicGeometry.exteriorPowerΓMapₗ_apply,
      AlgebraicGeometry.exteriorPowerΓMapₗ_apply, moduleSpecΓFunctor_map_apply,
      AlgebraicGeometry.exteriorPowerΓMap_naturality]
    refine congrArg _ ?_
    rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
    rfl
  rw [Modules.FreeQuotient.kernelSubmodule, hmap]
  have hinj : Function.Injective (AlgebraicGeometry.exteriorPowerΓMapₗ z.Q q) :=
    (AlgebraicGeometry.bijective_exteriorPowerΓMap z.Q q).1
  rw [LinearMap.ker_comp_of_ker_eq_bot _
    (LinearMap.ker_eq_bot_of_injective hinj)]
  exact ker_exteriorPower_map_comp_exteriorPowerPiEquiv R q m z.moduleMapPi
    z.moduleMapPi_surjective


/-- On an affine spectrum the glued kernel datum is the intrinsic affine kernel datum. -/
lemma kernelData_eq_affineKernelData {n q : ℕ} {R : CommRingCat.{u}}
    (x : Modules.FreeQuotient q (ULift.{u} (Fin n)) (Spec R)) :
    x.kernelData = x.affineKernelData := by
  rw [Modules.FreeQuotient.kernelData_eq_affineKernelDataOfIsAffine,
    Modules.FreeQuotient.affineKernelDataOfIsAffine, Scheme.isoSpec_Spec_inv,
    Scheme.isoSpec_Spec_hom, Modules.FreeQuotient.affineKernelData_comap_specMap]
  refine Modules.FreeQuotient.affineKernelData_eq_of_r ?_
  refine (Modules.FreeQuotient.setoid q (ULift.{u} (Fin n)) (Spec R)).trans
    (Modules.FreeQuotient.pullback_comp_r (Spec.map (Scheme.ΓSpecIso R).hom)
      (Spec.map (Scheme.ΓSpecIso R).inv) x) ?_
  have hcomp : Spec.map (Scheme.ΓSpecIso R).hom ≫ Spec.map (Scheme.ΓSpecIso R).inv =
      𝟙 (Spec R) := by
    rw [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
  rw [hcomp]
  exact Modules.FreeQuotient.pullback_id_r x


/-- The kernel of a strict free quotient on an affine spectrum, as a point of the
kernel-model Grassmannian of the coordinate module. -/
noncomputable def kernelGrassmannian {R : CommRingCat.{u}} {q m : ℕ}
    (z : Modules.FreeQuotient q (ULift.{u} (Fin m)) (Spec R)) :
    Module.Grassmannian R (Fin m → R) q := by
  letI e : Γ(Spec R, (⊤ : (Spec R).Opens)) ≃+* R :=
    (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
  letI : Algebra Γ(Spec R, (⊤ : (Spec R).Opens)) R :=
    (e : Γ(Spec R, (⊤ : (Spec R).Opens)) →+* R).toAlgebra
  letI : RingHomInvPair (e : Γ(Spec R, (⊤ : (Spec R).Opens)) →+* R)
      (e.symm : R →+* Γ(Spec R, (⊤ : (Spec R).Opens))) := RingHomInvPair.of_ringEquiv e
  letI : RingHomInvPair (e.symm : R →+* Γ(Spec R, (⊤ : (Spec R).Opens)))
      (e : Γ(Spec R, (⊤ : (Spec R).Opens)) →+* R) := RingHomInvPair.of_ringEquiv_symm e
  have hsub : z.kernelData.submodule ⟨⊤, isAffineOpen_top _⟩ =
      z.intrinsicKernelSubmodule := by
    rw [kernelData_eq_affineKernelData, Modules.FreeQuotient.affineKernelData,
      SubmoduleSheafData.ofAffineSubmodule_submodule_top]
  have hK := z.kernelData_quotientProjectiveOfRank
  have hproj : Module.Projective Γ(Spec R, (⊤ : (Spec R).Opens))
      ((Fin m → Γ(Spec R, (⊤ : (Spec R).Opens))) ⧸ z.intrinsicKernelSubmodule) := by
    rw [← hsub]
    exact hK.projective_affine ⟨⊤, isAffineOpen_top _⟩
  have hrank : ∀ p : PrimeSpectrum Γ(Spec R, (⊤ : (Spec R).Opens)),
      Module.rankAtStalk
        ((Fin m → Γ(Spec R, (⊤ : (Spec R).Opens))) ⧸ z.intrinsicKernelSubmodule) p = q := by
    intro p
    rw [← hsub]
    exact hK.rankAtStalk_affine ⟨⊤, isAffineOpen_top _⟩ p
  have hfin : Module.Finite Γ(Spec R, (⊤ : (Spec R).Opens))
      ((Fin m → Γ(Spec R, (⊤ : (Spec R).Opens))) ⧸ z.intrinsicKernelSubmodule) :=
    Module.Finite.of_surjective _ (Submodule.mkQ_surjective _)
  have htransport := Module.finite_projective_rankAtStalk_of_semilinearEquiv
    e rfl z.intrinsicKernelQuotientSemilinearEquiv hfin hproj hrank
  exact
    { toSubmodule := z.kernelSubmodule
      finite_quotient := htransport.1
      projective_quotient := htransport.2.1
      rankAtStalk_eq := htransport.2.2 }

@[simp]
lemma kernelGrassmannian_toSubmodule {R : CommRingCat.{u}} {q m : ℕ}
    (z : Modules.FreeQuotient q (ULift.{u} (Fin m)) (Spec R)) :
    (kernelGrassmannian z).toSubmodule = z.kernelSubmodule := rfl


set_option maxHeartbeats 1600000 in
/-- **The kernel of the Plücker quotient is the Plücker datum** (affine spectrum): on
`Spec R` the kernel datum of the Plücker quotient of a strict free quotient is the Plücker
datum of its kernel. -/
lemma freeQuotientPlucker_kernelData_spec {R : CommRingCat.{u}} {q m : ℕ}
    (z : Modules.FreeQuotient q (ULift.{u} (Fin m)) (Spec R)) :
    (freeQuotientPlucker z).kernelData =
      z.kernelData.pluckerData q z.kernelData_quotientProjectiveOfRank := by
  letI e : R ≃+* Γ(Spec R, (⊤ : (Spec R).Opens)) :=
    (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv
  letI : Algebra R Γ(Spec R, (⊤ : (Spec R).Opens)) :=
    (e : R →+* Γ(Spec R, (⊤ : (Spec R).Opens))).toAlgebra
  have hsub : z.kernelData.submodule ⟨⊤, isAffineOpen_top _⟩ =
      z.kernelSubmodule.mapPiRingEquiv e := by
    rw [kernelData_eq_affineKernelData, Modules.FreeQuotient.affineKernelData,
      SubmoduleSheafData.ofAffineSubmodule_submodule_top]
    rfl
  rw [kernelData_eq_affineKernelData, Modules.FreeQuotient.affineKernelData,
    SubmoduleSheafData.pluckerData_eq_affinePluckerOfQuotientProjectiveOfRank,
    SubmoduleSheafData.affinePluckerOfQuotientProjectiveOfRank,
    SubmoduleSheafData.affinePlucker]
  refine congrArg SubmoduleSheafData.ofAffineSubmodule ?_
  rw [Module.Grassmannian.plucker_toSubmodule,
    SubmoduleSheafData.grassmannianTop_toSubmodule, hsub,
    Modules.FreeQuotient.intrinsicKernelSubmodule,
    freeQuotientPlucker_kernelSubmodule]
  exact pluckerLinearMap_ker_mapPiRingEquiv m e (fun _ ↦ rfl) (kernelGrassmannian z)

/-- **The kernel of the Plücker quotient is the Plücker datum**: the kernel datum of the
Plücker quotient of a strict free quotient is the Plücker datum of its kernel.  Both sides
are compatible with base change, so this is local and follows from the affine case. -/
lemma freeQuotientPlucker_kernelData {W : Scheme.{u}} {q m : ℕ}
    (y : Modules.FreeQuotient q (ULift.{u} (Fin m)) W) :
    (freeQuotientPlucker y).kernelData =
      y.kernelData.pluckerData q y.kernelData_quotientProjectiveOfRank := by
  apply SubmoduleSheafData.eq_of_comap_eq_openCover W.affineCover
  intro i
  have hL : (freeQuotientPlucker y).kernelData.comap (W.affineCover.f i) =
      (freeQuotientPlucker (y.pullback (W.affineCover.f i))).kernelData := by
    rw [Modules.FreeQuotient.kernelData_comap]
    exact Modules.FreeQuotient.kernelData_eq_of_r
      (freeQuotientPlucker_pullback (W.affineCover.f i) y)
  have hR : (y.kernelData.pluckerData q
        y.kernelData_quotientProjectiveOfRank).comap (W.affineCover.f i) =
      (y.pullback (W.affineCover.f i)).kernelData.pluckerData q
        (y.pullback (W.affineCover.f i)).kernelData_quotientProjectiveOfRank := by
    rw [SubmoduleSheafData.pluckerData_comap]
    congr 1
    exact Modules.FreeQuotient.kernelData_comap y (W.affineCover.f i)
  rw [hL, hR]
  exact freeQuotientPlucker_kernelData_spec _

end FreeQuotientPlucker

section FreePlucker

variable (X : Scheme.{u})

/-- The relative Plücker morphism of part 2.2.2, as a morphism of schemes over the
base. -/
noncomputable def pluckerOverMorphismOver (q m : ℕ) :
    grassmannianOverRepresentation X q m ⟶
      grassmannianOverRepresentation X 1 (m.choose q) :=
  Over.homMk (pluckerOverMorphism X q m) (pluckerOverMorphism_fst X q m)

/-- The universal point classified by a map into the base-changed absolute Grassmannian,
read in the absolute Grassmannian functor. -/
lemma freeGrassmannianRepresentableBy_homEquiv (q m : ℕ) (T : Over X)
    (t : T ⟶ grassmannianOverRepresentation X q m) :
    Modules.freeGrassmannianEquiv q T
        ((freeGrassmannianRepresentableBy X q m).homEquiv t) =
      (grassmannianGluedRepresentation q m).homEquiv
        (t.left ≫ CategoryTheory.Limits.pullback.snd (specULiftZIsTerminal.from X)
          (specULiftZIsTerminal.from (grassmannianGlueData q m).glued)) := by
  exact Equiv.apply_symm_apply _ _

/-- **The comparison of the abstract and the concrete Plücker morphism in the free case**:
under the identification of the free relative Grassmannian with the absolute Grassmannian
functor (`Modules.freeGrassmannianEquiv`) and the identification `⋀^q O^{⊕m} ≅ O^{⊕C(m,q)}`
(`freeExteriorPowerIso`), the exterior-power Plücker transformation is the concrete
Plücker morphism `pluckerMorphism` of part 2.2.2.

Both sides are computed from the kernel datum of the induced quotient, so this reduces to
`freeQuotientPlucker_kernelData`: the kernel datum of the Plücker quotient is the Plücker
datum of the kernel.  That in turn is local, and on an affine spectrum it is the module
identity `ker (⋀^q φ ∘ exteriorPowerPiEquiv) = ker (pluckerLinearMap)`
(`ker_exteriorPower_map_comp_exteriorPowerPiEquiv` of part 2.2.2), because the section map
of the Plücker quotient factors as `exteriorPowerΓMap ∘ ⋀^q(moduleMapPi) ∘
exteriorPowerPiEquiv` (`freeExteriorPowerIso_inv_sections` and
`AlgebraicGeometry.exteriorPowerΓMap_naturality`). -/
theorem freeGrassmannianEquiv_pluckerTransformation (q m : ℕ) (T : Over X)
    (z : (Modules.grassmannianOverFunctor q
      (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m)))).obj (op T)) :
    Modules.freeGrassmannianEquiv (n := m.choose q) 1 T
        ((Modules.grassmannianOverFunctorIsoOfIso 1
            (freeExteriorPowerIso X q m)).hom.app (op T)
          ((Modules.pluckerTransformation q
            (SheafOfModules.free (R := X.ringCatSheaf)
              (ULift.{u} (Fin m)))).app (op T) z)) =
      (pluckerMorphism q m).app (op T.left) (Modules.freeGrassmannianEquiv q T z) := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep z
  apply Subtype.ext
  show (Modules.PullbackQuotient.mapAmbientIso (freeExteriorPowerIso X q m)
      (Modules.PullbackQuotient.plucker x)).toFreeQuotient.kernelData = _
  rw [Modules.FreeQuotient.kernelData_eq_of_r (toFreeQuotient_plucker x),
    freeQuotientPlucker_kernelData]
  rfl

set_option maxHeartbeats 1600000 in
/-- The Plücker morphism between the standard representatives of the free relative
Grassmannians is the relative Plücker morphism of part 2.2.2. -/
lemma pluckerMorphismOfRepr_free_eq (q m : ℕ) :
    Modules.pluckerMorphismOfRepr
        (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m)))
        (freeGrassmannianRepresentableBy X q m)
        ((freeGrassmannianRepresentableBy X 1 (m.choose q)).ofIso
          (Modules.grassmannianOverFunctorIsoOfIso 1
            (freeExteriorPowerIso X q m)).symm) =
      pluckerOverMorphismOver X q m := by
  symm
  apply Modules.pluckerMorphismOfRepr_unique
  intro T t
  apply ((Modules.grassmannianOverFunctorIsoOfIso 1
    (freeExteriorPowerIso X q m)).app (op T)).toEquiv.injective
  apply (Modules.freeGrassmannianEquiv (n := m.choose q) 1 T).injective
  simp only [Iso.toEquiv_fun, Iso.app_hom, Functor.RepresentableBy.ofIso,
    Equiv.trans_apply, Iso.app_inv, Iso.symm_hom,
    CategoryTheory.Iso.inv_hom_id_app_apply,
    freeGrassmannianEquiv_pluckerTransformation,
    freeGrassmannianRepresentableBy_homEquiv]
  have key : ∀ (Z : Scheme.{u}) (g : Z ⟶ (grassmannianGlueData q m).glued),
      (grassmannianGluedRepresentation 1 (m.choose q)).homEquiv
          (g ≫ pluckerGluedSchemeMorphism q m) =
        (pluckerMorphism q m).app (op Z)
          ((grassmannianGluedRepresentation q m).homEquiv g) := by
    intro Z g
    rw [(grassmannianGluedRepresentation 1 (m.choose q)).homEquiv_comp,
      show (grassmannianGluedRepresentation 1 (m.choose q)).homEquiv
            (pluckerGluedSchemeMorphism q m) =
          (pluckerMorphism q m).app (op (grassmannianGlueData q m).glued)
            ((grassmannianGluedRepresentation q m).homEquiv
              (𝟙 (grassmannianGlueData q m).glued)) from Equiv.apply_symm_apply _ _,
      ← (pluckerMorphism q m).naturality_apply]
    congr 1
    rw [← (grassmannianGluedRepresentation q m).homEquiv_comp, Category.comp_id]
  have hleft : (pluckerOverMorphismOver X q m).left = pluckerOverMorphism X q m := rfl
  rw [Over.comp_left, hleft, Category.assoc, pluckerOverMorphism_snd,
    ← Category.assoc, key]

end FreePlucker

/-- API lemma for Theorem 2.1.1 (the closed-immersion
property of the Plücker morphism, free case): for the canonical free bundle `O^{⊕m}` on
`U`, the Plücker morphism between representing schemes of `Gr(q, O^{⊕m})` and of
`Gr(1, ⋀^q O^{⊕m})` is a closed immersion.

This is the book's computation with the standard charts of the Grassmannian, carried out
in part 2.2.2 for the kernel-encoded functors: `pluckerGluedSchemeMorphism` is a closed
immersion (`isClosedImmersion_pluckerGluedSchemeMorphism`), hence so is its base change
`pluckerOverMorphism U q m` to `U`.  The two models are matched by
`pluckerMorphismOfRepr_free_eq`, through the identification `⋀^q O^{⊕m} ≅ O^{⊕C(m,q)}`
(`freeExteriorPowerIso`) and the comparison of Plücker transformations
`freeGrassmannianEquiv_pluckerTransformation` (the one outstanding obligation). -/
theorem isClosedImmersion_pluckerMorphismOfRepr_free (U : Scheme.{u}) (q m : ℕ)
    {P P' : Over U}
    (repr : (Modules.grassmannianOverFunctor q
      (SheafOfModules.free (R := U.ringCatSheaf)
        (ULift.{u} (Fin m)))).RepresentableBy P)
    (repr' : (Modules.grassmannianOverFunctor 1
      (Modules.exteriorPower (SheafOfModules.free (R := U.ringCatSheaf)
        (ULift.{u} (Fin m))) q)).RepresentableBy P') :
    IsClosedImmersion (Modules.pluckerMorphismOfRepr
      (SheafOfModules.free (R := U.ringCatSheaf) (ULift.{u} (Fin m)))
      repr repr').left := by
  refine Modules.isClosedImmersion_pluckerMorphismOfRepr_congr _
    (freeGrassmannianRepresentableBy U q m)
    ((freeGrassmannianRepresentableBy U 1 (m.choose q)).ofIso
      (Modules.grassmannianOverFunctorIsoOfIso 1
        (freeExteriorPowerIso U q m)).symm) repr repr' ?_
  rw [pluckerMorphismOfRepr_free_eq U q m]
  exact isClosedImmersion_pluckerOverMorphism U q m

/-- API lemma for Theorem 2.1.1 (the closed-immersion
property of the Plücker morphism): the Plücker morphism between representing schemes of
`Gr(q, V)` and of `Gr(1, ⋀^q V)` is a closed immersion.

Following the book, the statement is local on the base: over a coordinate neighborhood
`U ⊆ S` trivializing `V`, the Plücker morphism is the base change of the Plücker morphism
of the free bundle (`pluckerMorphismOfRepr_pullback` and
`Modules.pluckerMorphismOfRepr_ambient`), which is a closed immersion by the free case;
and closed immersions are local at the target. -/
theorem isClosedImmersion_pluckerMorphismOfRepr
    (hV : Modules.IsProjectiveOfRank n V) {P P' : Over S}
    (repr : (Modules.grassmannianOverFunctor q V).RepresentableBy P)
    (repr' : (Modules.grassmannianOverFunctor 1
      (Modules.exteriorPower V q)).RepresentableBy P') :
    IsClosedImmersion (Modules.pluckerMorphismOfRepr V repr repr').left := by
  refine IsZariskiLocalAtTarget.of_openCover
    (hV.coordinateBasicOpenCover.pullback₁ P'.hom) ?_
  intro x
  set j : (hV.coordinateBasicOpenAffine x).1.toScheme ⟶ S :=
    (hV.coordinateBasicOpenAffine x).1.ι with hj
  have hsq := CategoryTheory.Over.isPullback_pullback_map_left j
    (Modules.pluckerMorphismOfRepr V repr repr')
  have hci : IsClosedImmersion
      ((Over.pullback j).map (Modules.pluckerMorphismOfRepr V repr repr')).left := by
    rw [pluckerMorphismOfRepr_pullback V hV q j repr repr',
      Modules.pluckerMorphismOfRepr_ambient
        (hV.coordinateBasicOpenAffinePullbackFreeIso x)]
    exact isClosedImmersion_pluckerMorphismOfRepr_free _ q n _ _
  rw [← hsq.isoPullback_hom_snd] at hci
  exact (MorphismProperty.cancel_left_of_respectsIso
    (@IsClosedImmersion : MorphismProperty Scheme.{u}) _ _).mp hci

/-- **Theorem 2.1.1** (`thm:grassmannian-projective-relative`): for a quasi-coherent
vector bundle `V` of rank `n` on a scheme `S`, the relative Grassmannian functor
`Gr(q, V)` is representable by a scheme strongly projective over `S`.

Representability is `grassmannianOverFunctor_isRepresentable` above; strong projectivity
is `Modules.isStronglyProjective_of_representableBy` of part 2.2.2, applied to the
representing schemes of `Gr(q, V)` and of `Gr(1, ⋀^q V)` (the latter is a vector bundle of
rank `C(n, q)` by `Modules.isProjectiveOfRank_exteriorPower`), through the
closed-immersion property of the Plücker morphism. -/
theorem exists_grassmannianOverFunctor_representableBy
    (hV : Modules.IsProjectiveOfRank n V) :
    ∃ P : Over S, Nonempty ((Modules.grassmannianOverFunctor q V).RepresentableBy P) ∧
      IsStronglyProjective P.hom := by
  letI : (Modules.grassmannianOverFunctor q V).IsRepresentable :=
    grassmannianOverFunctor_isRepresentable V q hV
  letI : (Modules.grassmannianOverFunctor 1
      (Modules.exteriorPower V q)).IsRepresentable :=
    grassmannianOverFunctor_isRepresentable (Modules.exteriorPower V q) 1
      (Modules.isProjectiveOfRank_exteriorPower V hV q)
  refine ⟨(Modules.grassmannianOverFunctor q V).reprX,
    ⟨(Modules.grassmannianOverFunctor q V).representableBy⟩, ?_⟩
  exact Modules.isStronglyProjective_of_representableBy V hV
    (Modules.grassmannianOverFunctor q V).representableBy
    (Modules.grassmannianOverFunctor 1 (Modules.exteriorPower V q)).representableBy
    (isClosedImmersion_pluckerMorphismOfRepr V q hV _ _)

end AlgebraicGeometry.Scheme

end ThmGrassmannianProjectiveRelative

section CorGrassmannianVeryAmple

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme

/-- **Relatively very ample** (Stacks Project tag `01VL`, in the rendering used by
Corollary 2.2.15): a sheaf of modules `L` on `X` is relatively very ample for
`f : X ⟶ S` if there is a finite locally free quasi-coherent sheaf `E` on `S`, a scheme
`P` over `S` representing the projective bundle `ℙ(E) = Gr(1, E)`, and an immersion of `X`
into `P` over `S` along which the universal line-bundle quotient of `ℙ(E)` pulls back to
`L`.

The book cites the Stacks Project for the notion; since this development has no
`Proj`-model of `ℙ(E)` with its twisting sheaf `O(1)`, the universal quotient of the
functor `Gr(1, E)` plays the role of `O(1)`, which is the same thing (see the section
COMMENTARY). -/
def IsRelativelyVeryAmple {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules) : Prop :=
  ∃ (E : S.Modules) (_ : E.IsQuasicoherent) (_ : Modules.IsFiniteLocallyFree E)
    (P : Over S) (repr : (Modules.grassmannianOverFunctor 1 E).RepresentableBy P)
    (t : Over.mk f ⟶ P) (_ : IsImmersion t.left)
    (x : Modules.PullbackQuotient 1 E (Over.mk f)),
    Quotient.mk (Modules.PullbackQuotient.setoid 1 E (Over.mk f)) x =
      repr.homEquiv t ∧ Nonempty (x.Q ≅ L)

/-- **Corollary 2.2.15** (`cor:grassmannian-very-ample`): the determinant `⋀^q Q_univ` of
the universal quotient on a representing scheme of `Gr(q, V)` is a line bundle which is
relatively very ample over `S`.

It is a line bundle by `Modules.isProjectiveOfRank_exteriorPower` (rank `C(q, q) = 1`),
and the Plücker embedding `Modules.pluckerMorphismOfRepr` is the required immersion: it is
a closed immersion (`isClosedImmersion_pluckerMorphismOfRepr`) and by its defining property
(`Modules.pluckerMorphismOfRepr_homEquiv`) the universal quotient of `Gr(1, ⋀^q V)` pulls
back along it to the Plücker quotient `⋀^q Q_univ`. -/
theorem isRelativelyVeryAmple_exteriorPower_universalQuotient {S : Scheme.{u}} {q n : ℕ}
    (V : S.Modules) [V.IsQuasicoherent] (hV : Modules.IsProjectiveOfRank n V)
    {P : Over S} (repr : (Modules.grassmannianOverFunctor q V).RepresentableBy P)
    (x : Modules.PullbackQuotient q V P)
    (hx : Quotient.mk (Modules.PullbackQuotient.setoid q V P) x =
      repr.homEquiv (𝟙 P)) :
    IsRelativelyVeryAmple P.hom (Modules.exteriorPower x.Q q) := by
  haveI := x.isQuasicoherent
  letI : (Modules.grassmannianOverFunctor 1
      (Modules.exteriorPower V q)).IsRepresentable :=
    grassmannianOverFunctor_isRepresentable (Modules.exteriorPower V q) 1
      (Modules.isProjectiveOfRank_exteriorPower V hV q)
  let P' := (Modules.grassmannianOverFunctor 1 (Modules.exteriorPower V q)).reprX
  let repr' := (Modules.grassmannianOverFunctor 1
    (Modules.exteriorPower V q)).representableBy
  haveI hci : IsClosedImmersion
      (Modules.pluckerMorphismOfRepr V repr repr').left :=
    isClosedImmersion_pluckerMorphismOfRepr V q hV repr repr'
  refine ⟨Modules.exteriorPower V q, inferInstance,
    (Modules.isProjectiveOfRank_exteriorPower V hV q).isFiniteLocallyFree,
    P', repr', Modules.pluckerMorphismOfRepr V repr repr', inferInstance,
    x.plucker, ?_, ⟨Iso.refl _⟩⟩
  rw [show (Modules.pluckerMorphismOfRepr V repr repr' :
      Over.mk P.hom ⟶ P') = 𝟙 P ≫ Modules.pluckerMorphismOfRepr V repr repr' from
    (Category.id_comp _).symm]
  refine Eq.trans ?_ (Modules.pluckerMorphismOfRepr_homEquiv V repr repr' (𝟙 P)).symm
  rw [← hx]
  rfl

end AlgebraicGeometry.Scheme

end CorGrassmannianVeryAmple
