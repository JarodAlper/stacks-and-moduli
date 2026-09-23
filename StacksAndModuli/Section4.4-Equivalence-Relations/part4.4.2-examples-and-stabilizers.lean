module

public import StacksAndModuli.«Section4.4-Equivalence-Relations».«part4.4.1-groupoids-and-equivalence-relations»
public import StacksAndModuli.«Section3.3-Presheaves-and-Sheaves».«part3.3.4-fiber-products»
public import StacksAndModuli.API.PresheafFiberProductYoneda

/-!
# Examples of groupoids, stabilizers and orbits

This module formalizes **Example 4.4.3** (`ex:groupoid-projections`), **Definition 4.4.7**
(`def:stabilizer-and-orbits-of-groupoids`) and the surrounding unlabelled examples,
remarks and exercises of §4.4 (Equivalence relations and groupoids) of *Stacks and
Moduli*, section label
`subsec:equivalence-relations`.

Main results:
- `AlgebraicGeometry.PresheafGroupoid.ofAction`: the action groupoid
  `p₂, σ : G ×_S U ⇉ U` of a group scheme `G → S` acting on a scheme `U` over `S`, with
  `AlgebraicGeometry.PresheafGroupoid.ofAction_isEtale` and `.ofAction_isSmooth`;
- `AlgebraicGeometry.PresheafGroupoid.stabilizer`: the stabilizer group presheaf of a
  field-valued point of a groupoid of presheaves;
- `AlgebraicGeometry.groupoidOrbit`: the orbit of a point of `U` under a groupoid of
  schemes `s, t : R ⇉ U`, as a set of points.

**Example 4.4.4** (`ex:equivalence-relation-bug-eyed-cover`, the bug-eyed cover), the
unlabelled example "Groupoids induced from presentations", and **Exercise 4.4.6**
(`exer:projections-in-simplicial-group-action`) are not formalized; their section blocks
hold comments recording what is deferred and why (completeness state: see this folder's
STATUS.md).
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section ExGroupoidProjections

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.PresheafGroupoid

variable {S G U₀ : Scheme.{u}} (πG : G ⟶ S) (πU : U₀ ⟶ S) (m : pullback πG πG ⟶ G)
  (eG : S ⟶ G) (ι : G ⟶ G) (σ : pullback πG πU ⟶ U₀)

variable (hm : m ≫ πG = pullback.fst πG πG ≫ πG) (heG : eG ≫ πG = 𝟙 S)
  (hι : ι ≫ πG = πG) (hσ : σ ≫ πU = pullback.snd πG πU ≫ πU)

variable (hm_assoc : ∀ {T : Scheme.{u}} (g₁ g₂ g₃ : T ⟶ G) (h₁₂ : g₁ ≫ πG = g₂ ≫ πG)
    (h₂₃ : g₂ ≫ πG = g₃ ≫ πG) (h₁ : (pullback.lift g₁ g₂ h₁₂ ≫ m) ≫ πG = g₃ ≫ πG)
    (h₂ : g₁ ≫ πG = (pullback.lift g₂ g₃ h₂₃ ≫ m) ≫ πG),
    pullback.lift (pullback.lift g₁ g₂ h₁₂ ≫ m) g₃ h₁ ≫ m =
      pullback.lift g₁ (pullback.lift g₂ g₃ h₂₃ ≫ m) h₂ ≫ m)

variable (hm_one_mul : ∀ {T : Scheme.{u}} (g : T ⟶ G)
    (h : (g ≫ πG ≫ eG) ≫ πG = g ≫ πG), pullback.lift (g ≫ πG ≫ eG) g h ≫ m = g)

variable (hm_mul_one : ∀ {T : Scheme.{u}} (g : T ⟶ G)
    (h : g ≫ πG = (g ≫ πG ≫ eG) ≫ πG), pullback.lift g (g ≫ πG ≫ eG) h ≫ m = g)

variable (hm_inv_mul : ∀ {T : Scheme.{u}} (g : T ⟶ G) (h : (g ≫ ι) ≫ πG = g ≫ πG),
    pullback.lift (g ≫ ι) g h ≫ m = g ≫ πG ≫ eG)

variable (hm_mul_inv : ∀ {T : Scheme.{u}} (g : T ⟶ G) (h : g ≫ πG = (g ≫ ι) ≫ πG),
    pullback.lift g (g ≫ ι) h ≫ m = g ≫ πG ≫ eG)

variable (hσ_mul : ∀ {T : Scheme.{u}} (g' g : T ⟶ G) (u : T ⟶ U₀)
    (hg : g' ≫ πG = g ≫ πG) (hu : g ≫ πG = u ≫ πU)
    (h₁ : (pullback.lift g' g hg ≫ m) ≫ πG = u ≫ πU)
    (h₂ : g' ≫ πG = (pullback.lift g u hu ≫ σ) ≫ πU),
    pullback.lift (pullback.lift g' g hg ≫ m) u h₁ ≫ σ =
      pullback.lift g' (pullback.lift g u hu ≫ σ) h₂ ≫ σ)

variable (hσ_one : ∀ {T : Scheme.{u}} (u : T ⟶ U₀)
    (h : (u ≫ πU ≫ eG) ≫ πG = u ≫ πU), pullback.lift (u ≫ πU ≫ eG) u h ≫ σ = u)

/-- **Example 4.4.3** (`ex:groupoid-projections`) (the action groupoid): let `G → S` be a
group scheme with multiplication `m`, identity `e_G` and inverse `ι`, acting on a scheme
`U` over `S` via `σ : G ×_S U → U` (all hypotheses stated on `T`-points). The associated
groupoid of presheaves
`p₂, σ : G ×_S U ⇉ U` has as relations the pairs `(g, u)`, regarded as `u → g·u`, with
source `p₂(g, u) = u`, target `σ(g, u) = g·u`, composition `((g', u'), (g, u)) ↦ (g'g, u)`
(where `u' = g·u`), identity `u ↦ (e_G, u)` and inverse `(g, u) ↦ (g⁻¹, g·u)`. The special
case `U = S` (with the trivial action) gives the groupoid `G ⇉ S` with both arrows the
structure morphism. -/
noncomputable def ofAction : PresheafGroupoid.{u} where
  U := yoneda.obj U₀
  R := Presheaf.fiberProduct (yoneda.map πG) (yoneda.map πU)
  s := Presheaf.fiberProduct.snd (yoneda.map πG) (yoneda.map πU)
  t :=
    { app := fun T ↦ ↾fun x ↦ pullback.lift x.1.1 x.1.2 x.2 ≫ σ
      naturality := fun {T T'} f ↦ by
        ext x
        change pullback.lift (f.unop ≫ x.1.1) (f.unop ≫ x.1.2) _ ≫ σ =
          f.unop ≫ pullback.lift x.1.1 x.1.2 x.2 ≫ σ
        rw [← Category.assoc]
        congr 1
        apply pullback.hom_ext <;> simp }
  comp {T} x y h :=
    ⟨⟨pullback.lift x.1.1 y.1.1 (by
        have hx : x.1.1 ≫ πG = x.1.2 ≫ πU := x.2
        have hy : y.1.1 ≫ πG = y.1.2 ≫ πU := y.2
        have h' : x.1.2 = pullback.lift y.1.1 y.1.2 hy ≫ σ := h
        rw [hx, h', Category.assoc, hσ, pullback.lift_snd_assoc, ← hy]) ≫ m, y.1.2⟩, by
      have hx : x.1.1 ≫ πG = x.1.2 ≫ πU := x.2
      have hy : y.1.1 ≫ πG = y.1.2 ≫ πU := y.2
      have h' : x.1.2 = pullback.lift y.1.1 y.1.2 hy ≫ σ := h
      change (pullback.lift x.1.1 y.1.1 _ ≫ m) ≫ πG = y.1.2 ≫ πU
      rw [Category.assoc, hm, pullback.lift_fst_assoc, hx, h', Category.assoc, hσ,
        pullback.lift_snd_assoc, ← hy]⟩
  s_comp {T} x y h := rfl
  t_comp {T} x y h := by
    have h' : x.1.2 = pullback.lift y.1.1 y.1.2 y.2 ≫ σ := h
    change pullback.lift (pullback.lift x.1.1 y.1.1 _ ≫ m) y.1.2 _ ≫ σ =
      pullback.lift x.1.1 x.1.2 x.2 ≫ σ
    rw [hσ_mul x.1.1 y.1.1 y.1.2 _ y.2 _
      (by rw [show x.1.1 ≫ πG = x.1.2 ≫ πU from x.2, h'])]
    simp only [h']
  comp_naturality {T T'} f x y h h' := by
    refine Subtype.ext (Prod.ext ?_ rfl)
    change f.unop ≫ pullback.lift x.1.1 y.1.1 _ ≫ m =
      pullback.lift (f.unop ≫ x.1.1) (f.unop ≫ y.1.1) _ ≫ m
    rw [← Category.assoc]
    congr 1
    apply pullback.hom_ext <;> simp
  comp_assoc {T} x y z hxy hyz h₁ h₂ := by
    refine Subtype.ext (Prod.ext ?_ rfl)
    exact hm_assoc x.1.1 y.1.1 z.1.1 _ _ _ _
  e :=
    { app := fun T ↦ ↾fun u ↦ ⟨⟨u ≫ πU ≫ eG, u⟩, by
        change (u ≫ πU ≫ eG) ≫ πG = u ≫ πU
        simp only [Category.assoc, heG, Category.comp_id]⟩
      naturality := fun {T T'} f ↦ by
        ext u
        exact Subtype.ext (Prod.ext (by simp) rfl) }
  e_s := by
    ext T u
    rfl
  e_t := by
    ext T u
    exact hσ_one u _
  comp_e {T} x h := by
    refine Subtype.ext (Prod.ext ?_ rfl)
    have hx : x.1.2 ≫ πU = x.1.1 ≫ πG := x.2.symm
    change pullback.lift x.1.1 (x.1.2 ≫ πU ≫ eG) _ ≫ m = x.1.1
    simp only [← Category.assoc, hx]
    simp only [Category.assoc]
    exact hm_mul_one x.1.1 _
  e_comp {T} x h := by
    refine Subtype.ext (Prod.ext ?_ rfl)
    have hx : x.1.2 ≫ πU = x.1.1 ≫ πG := x.2.symm
    have hσe : σ ≫ πU ≫ eG = pullback.snd πG πU ≫ πU ≫ eG := by
      rw [← Category.assoc, hσ, Category.assoc]
    change pullback.lift ((pullback.lift x.1.1 x.1.2 x.2 ≫ σ) ≫ πU ≫ eG) x.1.1 _ ≫ m =
      x.1.1
    simp only [Category.assoc, hσe, pullback.lift_snd_assoc]
    simp only [← Category.assoc, hx]
    simp only [Category.assoc]
    exact hm_one_mul x.1.1 _
  inv :=
    { app := fun T ↦ ↾fun x ↦ ⟨⟨x.1.1 ≫ ι, pullback.lift x.1.1 x.1.2 x.2 ≫ σ⟩, by
        change (x.1.1 ≫ ι) ≫ πG = (pullback.lift x.1.1 x.1.2 x.2 ≫ σ) ≫ πU
        rw [Category.assoc, hι, Category.assoc, hσ, pullback.lift_snd_assoc]
        exact x.2⟩
      naturality := fun {T T'} f ↦ by
        ext x
        refine Subtype.ext (Prod.ext (by simp) ?_)
        change pullback.lift (f.unop ≫ x.1.1) (f.unop ≫ x.1.2) _ ≫ σ =
          f.unop ≫ pullback.lift x.1.1 x.1.2 x.2 ≫ σ
        rw [← Category.assoc]
        congr 1
        apply pullback.hom_ext <;> simp }
  inv_s := by
    ext T x
    rfl
  inv_t := by
    ext T x
    have hx : x.1.1 ≫ πG = x.1.2 ≫ πU := x.2
    have hg : (x.1.1 ≫ ι) ≫ πG = x.1.1 ≫ πG := by rw [Category.assoc, hι]
    change pullback.lift (x.1.1 ≫ ι) (pullback.lift x.1.1 x.1.2 x.2 ≫ σ) _ ≫ σ = x.1.2
    rw [← hσ_mul (x.1.1 ≫ ι) x.1.1 x.1.2 hg x.2
      (by rw [Category.assoc, hm, pullback.lift_fst_assoc, hg, hx])
      (by rw [hg, hx, Category.assoc, hσ, pullback.lift_snd_assoc])]
    simp only [hm_inv_mul]
    simp only [← Category.assoc, hx]
    simp only [Category.assoc]
    exact hσ_one x.1.2 _
  inv_comp {T} x h := by
    refine Subtype.ext (Prod.ext ?_ rfl)
    have hx : x.1.1 ≫ πG = x.1.2 ≫ πU := x.2
    change pullback.lift (x.1.1 ≫ ι) x.1.1 _ ≫ m = x.1.2 ≫ πU ≫ eG
    rw [hm_inv_mul x.1.1 _]
    simp only [← Category.assoc, hx]
  comp_inv {T} x h := by
    refine Subtype.ext (Prod.ext ?_ rfl)
    have hx : x.1.1 ≫ πG = x.1.2 ≫ πU := x.2
    have hσe : σ ≫ πU ≫ eG = pullback.snd πG πU ≫ πU ≫ eG := by
      rw [← Category.assoc, hσ, Category.assoc]
    change pullback.lift x.1.1 (x.1.1 ≫ ι) _ ≫ m =
      (pullback.lift x.1.1 x.1.2 x.2 ≫ σ) ≫ πU ≫ eG
    rw [hm_mul_inv x.1.1 _]
    simp only [Category.assoc, hσe, pullback.lift_snd_assoc]
    simp only [← Category.assoc, hx]

/-- Background construction used with Example 4.4.3 (the action map): the combined map
`(t, s) : G ×_S U → U ×_S U`, `(g, u) ↦ (g·u, u)`, of the action groupoid. It is the
morphism whose unramifiedness (resp. being a monomorphism) characterizes `[U/G]` as a
Deligne–Mumford stack (resp. as an algebraic space) in Corollary 4.6.8
(Corollary 4.6.8). -/
noncomputable def actionMap : pullback πG πU ⟶ pullback πU πU :=
  pullback.lift σ (pullback.snd πG πU) hσ

@[reassoc (attr := simp)]
lemma actionMap_comp_fst : actionMap πG πU σ hσ ≫ pullback.fst πU πU = σ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma actionMap_comp_snd :
    actionMap πG πU σ hσ ≫ pullback.snd πU πU = pullback.snd πG πU :=
  pullback.lift_snd _ _ _

/-- API lemma for action groupoids (free actions): the action groupoid of a
*free* action is an equivalence relation. Freeness is stated on `T`-points, as everywhere
else in this block: if two elements `g, g'` of `G(T)` over the same point of `S` move a
point `u` of `U(T)` to the same place, they are equal. Then a relation `(g, u)` is
determined by its source `u` and target `g·u`, which is exactly
`PresheafGroupoid.IsEquivalenceRelation`. -/
lemma ofAction_isEquivalenceRelation
    (hfree : ∀ {T : Scheme.{u}} (g g' : T ⟶ G) (u : T ⟶ U₀) (h : g ≫ πG = u ≫ πU)
      (h' : g' ≫ πG = u ≫ πU),
      pullback.lift g u h ≫ σ = pullback.lift g' u h' ≫ σ → g = g') :
    (ofAction πG πU m eG ι σ hm heG hι hσ hm_assoc hm_one_mul hm_mul_one hm_inv_mul
      hm_mul_inv hσ_mul hσ_one).IsEquivalenceRelation := by
  intro T x y hs ht
  obtain ⟨⟨gx, ux⟩, hx⟩ := x
  obtain ⟨⟨gy, uy⟩, hy⟩ := y
  have hu : ux = uy := hs
  subst hu
  exact Subtype.ext (Prod.ext (hfree gx gy ux hx hy ht) rfl)

/-- Helper construction for Example 4.4.3 (the shearing automorphism): the
automorphism `(g, u) ↦ (g, g·u)` of `G ×_S U`, with inverse `(g, u) ↦ (g, g⁻¹·u)`. It is
what turns the target of the action groupoid into its source, and so transports the
étaleness (resp. smoothness) of `π_G` from one to the other. -/
noncomputable def shear :
    Presheaf.fiberProduct (yoneda.map πG) (yoneda.map πU) ≅
      Presheaf.fiberProduct (yoneda.map πG) (yoneda.map πU) := by
  refine NatIso.ofComponents (fun T => Equiv.toIso
    { toFun := fun x => ⟨⟨x.1.1, pullback.lift x.1.1 x.1.2 x.2 ≫ σ⟩, ?_⟩
      invFun := fun x => ⟨⟨x.1.1, pullback.lift (x.1.1 ≫ ι) x.1.2 ?_ ≫ σ⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }) ?_
  · have hx : x.1.1 ≫ πG = x.1.2 ≫ πU := x.2
    change x.1.1 ≫ πG = (pullback.lift x.1.1 x.1.2 x.2 ≫ σ) ≫ πU
    rw [Category.assoc, hσ, pullback.lift_snd_assoc]
    exact hx
  · have hx : x.1.1 ≫ πG = x.1.2 ≫ πU := x.2
    change (x.1.1 ≫ ι) ≫ πG = x.1.2 ≫ πU
    rw [Category.assoc, hι]
    exact hx
  · have hx : x.1.1 ≫ πG = x.1.2 ≫ πU := x.2
    change x.1.1 ≫ πG = (pullback.lift (x.1.1 ≫ ι) x.1.2 _ ≫ σ) ≫ πU
    rw [Category.assoc, hσ, pullback.lift_snd_assoc]
    exact hx
  · intro x
    refine Subtype.ext (Prod.ext rfl ?_)
    have hx : x.1.1 ≫ πG = x.1.2 ≫ πU := x.2
    have hg : (x.1.1 ≫ ι) ≫ πG = x.1.1 ≫ πG := by rw [Category.assoc, hι]
    change pullback.lift (x.1.1 ≫ ι) (pullback.lift x.1.1 x.1.2 x.2 ≫ σ) _ ≫ σ = x.1.2
    rw [← hσ_mul (x.1.1 ≫ ι) x.1.1 x.1.2 hg x.2
      (by rw [Category.assoc, hm, pullback.lift_fst_assoc, hg, hx])
      (by rw [hg, hx, Category.assoc, hσ, pullback.lift_snd_assoc])]
    simp only [hm_inv_mul]
    simp only [← Category.assoc, hx]
    simp only [Category.assoc]
    exact hσ_one x.1.2 _
  · intro x
    refine Subtype.ext (Prod.ext rfl ?_)
    have hx : x.1.1 ≫ πG = x.1.2 ≫ πU := x.2
    have hg : x.1.1 ≫ πG = (x.1.1 ≫ ι) ≫ πG := by rw [Category.assoc, hι]
    change pullback.lift x.1.1 (pullback.lift (x.1.1 ≫ ι) x.1.2 _ ≫ σ) _ ≫ σ = x.1.2
    rw [← hσ_mul x.1.1 (x.1.1 ≫ ι) x.1.2 hg (by rw [Category.assoc, hι]; exact hx)
      (by rw [Category.assoc, hm, pullback.lift_fst_assoc, hx])
      (by rw [hx, Category.assoc, hσ, pullback.lift_snd_assoc])]
    simp only [hm_mul_inv]
    simp only [← Category.assoc, hx]
    simp only [Category.assoc]
    exact hσ_one x.1.2 _
  · intro T T' f
    ext x
    refine Subtype.ext (Prod.ext rfl ?_)
    change pullback.lift (f.unop ≫ x.1.1) (f.unop ≫ x.1.2) _ ≫ σ =
      f.unop ≫ pullback.lift x.1.1 x.1.2 x.2 ≫ σ
    rw [← Category.assoc]
    congr 1
    apply pullback.hom_ext <;> simp

/-- Helper lemma for Example 4.4.3: the target of the action groupoid is the
source precomposed with the shearing automorphism. -/
lemma t_eq_shear_comp_snd :
    (ofAction πG πU m eG ι σ hm heG hι hσ hm_assoc hm_one_mul hm_mul_one hm_inv_mul
      hm_mul_inv hσ_mul hσ_one).t =
      (shear πG πU m eG ι σ hm hι hσ hm_inv_mul hm_mul_inv hσ_mul hσ_one).hom ≫
        Presheaf.fiberProduct.snd (yoneda.map πG) (yoneda.map πU) := by
  ext T x
  rfl

/-- **Example 4.4.3** (`ex:groupoid-projections`) (étale case): the action groupoid of an
étale group scheme is an étale groupoid: the source `p₂` is a base change of
`π_G : G → S`, and the target `σ` differs from it by the shearing automorphism
`(g, u) ↦ (g, g·u)` of `G ×_S U`. -/
lemma ofAction_isEtale [Etale πG] :
    (ofAction πG πU m eG ι σ hm heG hι hσ hm_assoc hm_one_mul hm_mul_one hm_inv_mul
      hm_mul_inv hσ_mul hσ_one).IsEtale := by
  have hs : MorphismProperty.presheaf (@Etale : MorphismProperty Scheme.{u})
      (Presheaf.fiberProduct.snd (yoneda.map πG) (yoneda.map πU)) := by
    have h1 : Etale (pullback.snd πG πU) := MorphismProperty.pullback_snd _ _ inferInstance
    have h2 : MorphismProperty.presheaf (@Etale : MorphismProperty Scheme.{u})
        (yoneda.map (pullback.snd πG πU)) := MorphismProperty.presheaf_yoneda_map h1
    rw [← Presheaf.fiberProductYonedaIso_hom_comp_snd πG πU] at h2
    exact (MorphismProperty.cancel_left_of_respectsIso
      (MorphismProperty.presheaf (@Etale : MorphismProperty Scheme.{u}))
      (Presheaf.fiberProductYonedaIso πG πU).hom _).mp h2
  refine ⟨hs, ?_⟩
  rw [t_eq_shear_comp_snd]
  exact (MorphismProperty.cancel_left_of_respectsIso
    (MorphismProperty.presheaf (@Etale : MorphismProperty Scheme.{u}))
    (shear πG πU m eG ι σ hm hι hσ hm_inv_mul hm_mul_inv hσ_mul hσ_one).hom _).mpr hs

/-- **Example 4.4.3** (`ex:groupoid-projections`) (smooth case): the action groupoid of a
smooth group scheme is a smooth groupoid. -/
lemma ofAction_isSmooth [Smooth πG] :
    (ofAction πG πU m eG ι σ hm heG hι hσ hm_assoc hm_one_mul hm_mul_one hm_inv_mul
      hm_mul_inv hσ_mul hσ_one).IsSmooth := by
  have hs : MorphismProperty.presheaf (@Smooth : MorphismProperty Scheme.{u})
      (Presheaf.fiberProduct.snd (yoneda.map πG) (yoneda.map πU)) := by
    have h1 : Smooth (pullback.snd πG πU) := MorphismProperty.pullback_snd _ _ inferInstance
    have h2 : MorphismProperty.presheaf (@Smooth : MorphismProperty Scheme.{u})
        (yoneda.map (pullback.snd πG πU)) := MorphismProperty.presheaf_yoneda_map h1
    rw [← Presheaf.fiberProductYonedaIso_hom_comp_snd πG πU] at h2
    exact (MorphismProperty.cancel_left_of_respectsIso
      (MorphismProperty.presheaf (@Smooth : MorphismProperty Scheme.{u}))
      (Presheaf.fiberProductYonedaIso πG πU).hom _).mp h2
  refine ⟨hs, ?_⟩
  rw [t_eq_shear_comp_snd]
  exact (MorphismProperty.cancel_left_of_respectsIso
    (MorphismProperty.presheaf (@Smooth : MorphismProperty Scheme.{u}))
    (shear πG πU m eG ι σ hm hι hσ hm_inv_mul hm_mul_inv hσ_mul hσ_one).hom _).mpr hs

/-- API lemma for the action groupoid of Example 4.4.3 (affine source): if the group scheme
`G → S` is affine, then the source `G ×_S U → U` of its action groupoid is representable
by affine morphisms. -/
lemma ofAction_s_isAffine [IsAffineHom πG] :
    MorphismProperty.presheaf (@IsAffineHom : MorphismProperty Scheme.{u})
      (ofAction πG πU m eG ι σ hm heG hι hσ hm_assoc hm_one_mul hm_mul_one hm_inv_mul
        hm_mul_inv hσ_mul hσ_one).s := by
  have h1 : IsAffineHom (pullback.snd πG πU) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have h2 : MorphismProperty.presheaf (@IsAffineHom : MorphismProperty Scheme.{u})
      (yoneda.map (pullback.snd πG πU)) := MorphismProperty.presheaf_yoneda_map h1
  rw [← Presheaf.fiberProductYonedaIso_hom_comp_snd πG πU] at h2
  exact (MorphismProperty.cancel_left_of_respectsIso
    (MorphismProperty.presheaf (@IsAffineHom : MorphismProperty Scheme.{u}))
    (Presheaf.fiberProductYonedaIso πG πU).hom _).mp h2

/-- API lemma for the action groupoid of Example 4.4.3 (affine target): if the group scheme
`G → S` is affine, then the target of its action groupoid is representable by affine
morphisms, since it differs from the source by the shearing automorphism. -/
lemma ofAction_t_isAffine [IsAffineHom πG] :
    MorphismProperty.presheaf (@IsAffineHom : MorphismProperty Scheme.{u})
      (ofAction πG πU m eG ι σ hm heG hι hσ hm_assoc hm_one_mul hm_mul_one hm_inv_mul
        hm_mul_inv hσ_mul hσ_one).t := by
  rw [t_eq_shear_comp_snd]
  exact (MorphismProperty.cancel_left_of_respectsIso
    (MorphismProperty.presheaf (@IsAffineHom : MorphismProperty Scheme.{u}))
    (shear πG πU m eG ι σ hm hι hσ hm_inv_mul hm_mul_inv hσ_mul hσ_one).hom _).mpr
      (ofAction_s_isAffine πG πU m eG ι σ hm heG hι hσ hm_assoc hm_one_mul hm_mul_one
        hm_inv_mul hm_mul_inv hσ_mul hσ_one)

/-- The associativity axiom of an action, for the trivial action of `G → S` on `S` itself:
both sides project to the second factor. -/
lemma trivialAction_hσ_mul : ∀ {T : Scheme.{u}} (g' g : T ⟶ G) (u : T ⟶ S)
    (hg : g' ≫ πG = g ≫ πG) (hu : g ≫ πG = u ≫ 𝟙 S)
    (h₁ : (pullback.lift g' g hg ≫ m) ≫ πG = u ≫ 𝟙 S)
    (h₂ : g' ≫ πG = (pullback.lift g u hu ≫ pullback.snd πG (𝟙 S)) ≫ 𝟙 S),
    pullback.lift (pullback.lift g' g hg ≫ m) u h₁ ≫ pullback.snd πG (𝟙 S) =
      pullback.lift g' (pullback.lift g u hu ≫ pullback.snd πG (𝟙 S)) h₂ ≫
        pullback.snd πG (𝟙 S) := by
  intro T g' g u hg hu h₁ h₂
  simp

/-- The unit axiom of an action, for the trivial action of `G → S` on `S` itself. -/
lemma trivialAction_hσ_one : ∀ {T : Scheme.{u}} (u : T ⟶ S)
    (h : (u ≫ (𝟙 S) ≫ eG) ≫ πG = u ≫ 𝟙 S),
    pullback.lift (u ≫ (𝟙 S) ≫ eG) u h ≫ pullback.snd πG (𝟙 S) = u := by
  intro T u h
  simp

/-- **Example 4.4.3** (`ex:groupoid-projections`) (the special case `U = S`): the trivial
action of a group scheme `G → S` on `S` gives the groupoid `G ⇉ S` with both arrows the
structure morphism `π_G`. Its quotient stack is the classifying stack `BG`. -/
noncomputable abbrev ofGroup : PresheafGroupoid.{u} :=
  ofAction πG (𝟙 S) m eG ι (pullback.snd πG (𝟙 S)) hm heG hι rfl hm_assoc hm_one_mul
    hm_mul_one hm_inv_mul hm_mul_inv (trivialAction_hσ_mul πG m) (trivialAction_hσ_one πG eG)

/-- Supporting specialization of Example 4.4.3 (smooth case, `U = S`): the groupoid
`G ⇉ S` of a smooth group scheme is smooth. -/
lemma ofGroup_isSmooth [Smooth πG] :
    (ofGroup πG m eG ι hm heG hι hm_assoc hm_one_mul hm_mul_one hm_inv_mul
      hm_mul_inv).IsSmooth :=
  ofAction_isSmooth _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

end AlgebraicGeometry.PresheafGroupoid

end ExGroupoidProjections

section ExEquivalenceRelationBugEyedCover

/- Unformalized Example 4.4.4: the étale equivalence relation
`p₂, σ : R ⇉ 𝔸¹` obtained from the action of `ℤ/2` on `𝔸¹` by
`x ↦ -x` after removing the non-identity point of the stabilizer of the origin,
`R = (ℤ/2 × 𝔸¹) ∖ {(-1, 0)}`, requires the constant group scheme `ℤ/2` over a field, its
action on `𝔸¹`, and the explicit open complement of a point — concrete algebraic geometry
that is not yet available in StacksAndModuli. It is deferred together with the computation that
the quotient `𝔸¹/R` is an algebraic space which is not a scheme (Example 4.9.2,
`ex:bug-eyed-cover`, §4.9). -/

end ExEquivalenceRelationBugEyedCover

section ExGroupoidsFromPresentations

/- **Subsection 4.4** (`subsec:equivalence-relations`) (the unlabelled example "Groupoids
induced from presentations"): for a Deligne–Mumford (resp. algebraic) stack `𝒳` with an
étale (resp. smooth) presentation `p : U → 𝒳` representable by schemes, the fiber product
`R = U ×_𝒳 U` with the two projections is an étale (resp. smooth) groupoid `R ⇉ U` of
algebraic spaces, and an equivalence relation when `𝒳` is an algebraic space. This
groupoid is not constructed as an `AlgebraicGeometry.PresheafGroupoid` here: turning the
prestack fiber product
`U ×_𝒳 U` (available as `CategoryTheory.BasedCategory.fiberProduct`, §3.4.5) into a
strictly functorial presheaf of relations requires a cleavage — a noncomputable choice of
pullbacks in `𝒳` — and heavy transport of the comparison isomorphisms. The mathematical
content is recorded where it is used: the fiber-product description of `R` for quotient
groupoids is
`AlgebraicGeometry.PresheafGroupoid.isRepresentedByPresheaf_fiberProduct_of_isStackification`
(part 4.4.3), and the reconstruction `𝒳 ≅ [U/R]` is the unlabelled exercise
`AlgebraicGeometry.PresheafGroupoid.exists_isStackification_quotientPrestack_of_presentation`
(part 4.4.4), stated by quantifying over groupoids with `R = U ×_𝒳 U`. Morita equivalence
of the groupoids induced by different presentations is explicitly not used in the book and
is not formalized. -/

end ExGroupoidsFromPresentations

section ExerProjectionsInSimplicialGroupAction

/- Unformalized Exercise 4.4.6: the identifications
`U ×_{[U/G]} ⋯ ×_{[U/G]} U ≅ Gⁿ⁻¹ ×_S U` of the iterated fiber products
of a quotient stack presentation with the Čech nerve of the group action, together with
the description of the projection maps, require iterated fiber products of prestacks and
the quotient stack `[U/G]` machinery of Appendix B/§3.4, which are themselves deferred in
§3.4 (Example 3.4.26, `ex:quotient-stack-presentation`) and §4.1 (see those folders'
STATUS.md). Cf. Stacks Project 06FI, 0234 for the simplicial picture. -/

end ExerProjectionsInSimplicialGroupAction

section DefStabilizerAndOrbitsOfGroupoids

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

/-- **Definition 4.4.7** (`def:stabilizer-and-orbits-of-groupoids`) (the stabilizer): let
`R ⇉ U` be a groupoid of presheaves on `Sch` (in practice a smooth groupoid of algebraic
spaces) and let `x ∈ U(Spec K)` be a field-valued point. The *stabilizer* `G_x` of `x`
(the *automorphism group* of `x`) is the fiber product of `(s, t) : R → U × U` with
`(x, x) : Spec K → U × U`: its `T`-points are the pairs of a relation `r ∈ R(T)` and a
morphism `φ : T → Spec K` with `s(r) = φ*(x) = t(r)`. It is a presheaf of groups over
`Spec K` (the group structure is induced by the groupoid composition). -/
noncomputable def PresheafGroupoid.stabilizer (𝒢 : PresheafGroupoid.{u}) {K : Type u} [Field K]
    (x : 𝒢.U.obj (op (Spec (CommRingCat.of K)))) : Scheme.{u}ᵒᵖ ⥤ Type u where
  obj T := {p : 𝒢.R.obj T × ((unop T) ⟶ Spec (CommRingCat.of K)) //
    𝒢.s.app T p.1 = 𝒢.U.map p.2.op x ∧ 𝒢.t.app T p.1 = 𝒢.U.map p.2.op x}
  map {T T'} f := ↾fun p ↦ ⟨⟨𝒢.R.map f p.1.1, f.unop ≫ p.1.2⟩, by
    constructor
    · rw [PresheafGroupoid.s_app_map, p.2.1, op_comp, Functor.map_comp_apply]
      rfl
    · rw [PresheafGroupoid.t_app_map, p.2.2, op_comp, Functor.map_comp_apply]
      rfl⟩
  map_id T := by
    ext p
    · simp
    · simp
  map_comp {T T' T''} f g := by
    ext p
    · simp
    · simp

/-- **Definition 4.4.7** (`def:stabilizer-and-orbits-of-groupoids`) (the orbit): let
`s, t : R ⇉ U` be a groupoid of schemes and let `x` be a point of `U`. The *orbit* of `x`
is the set of points `s(t⁻¹(x)) ⊆ U`: the points related to `x` by a point of `R`. -/
def groupoidOrbit {R₀ U₀ : Scheme.{u}} (s t : R₀ ⟶ U₀) (x : U₀) : Set U₀ :=
  s.base '' (t.base ⁻¹' {x})

/- **Subsection 4.4** (`subsec:equivalence-relations`) (the unlabelled remark following
Definition 4.4.7): if the groupoid `R ⇉ U` arises from a smooth presentation `U → 𝒳` of
an algebraic stack, the stabilizer of `x ∈ U(K)` is identified with the stabilizer
(automorphism group, cf. Definition 4.2.5, `def:stabilizers`, §4.2) of its image in
`𝒳(K)`, and the orbit of `x` is the set of points of `U` whose image in `𝒳` is isomorphic
to the image of `x`. This identification is not formalized here, as the groupoid induced
by a presentation is itself deferred (see the section `ExGroupoidsFromPresentations`
above). -/

end AlgebraicGeometry

end DefStabilizerAndOrbitsOfGroupoids

section ExerIdentityInverseUnique

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.PresheafGroupoid

variable (𝒢 : PresheafGroupoid.{u})

/-- API theorem from the unnumbered exercise following
Definition 4.4.7, uniqueness of the identity): the identity of a groupoid of presheaves is
uniquely determined by the source, target and composition: any section `e'` of the source
satisfying the left unit law is equal to the identity `e`. -/
theorem e_unique (e' : 𝒢.U ⟶ 𝒢.R) (he_s : e' ≫ 𝒢.s = 𝟙 𝒢.U)
    (he_comp : ∀ {T : Scheme.{u}ᵒᵖ} (x : 𝒢.R.obj T)
      (h : 𝒢.s.app T (e'.app T (𝒢.t.app T x)) = 𝒢.t.app T x),
      𝒢.comp (e'.app T (𝒢.t.app T x)) x h = x) :
    e' = 𝒢.e := by
  ext T a
  have hs : ∀ b : 𝒢.U.obj T, 𝒢.s.app T (e'.app T b) = b := fun b ↦ by
    rw [← NatTrans.comp_app_apply, he_s, NatTrans.id_app, types_id_apply]
  -- the left unit law of `e'` applied to the identity relation `e(a)`
  have h1 := he_comp (𝒢.e.app T a) (by rw [hs])
  simp only [PresheafGroupoid.t_app_e_app] at h1
  -- the right unit law of `e` applied to `e'(a)`
  have h2 : 𝒢.comp (e'.app T a) (𝒢.e.app T a) (by rw [hs, PresheafGroupoid.t_app_e_app]) =
      e'.app T a := 𝒢.comp_e_app _ _ _
  exact h2.symm.trans h1

/-- API theorem from the unnumbered exercise following
Definition 4.4.7, uniqueness of the inverse): the inverse of a groupoid of presheaves is
uniquely determined by the source, target, composition and identity: any `inv'` with
`s ∘ inv' = t` satisfying the left inverse law is equal to the inverse `inv`. -/
theorem inv_unique (inv' : 𝒢.R ⟶ 𝒢.R) (hinv_s : inv' ≫ 𝒢.s = 𝒢.t)
    (hinv_comp : ∀ {T : Scheme.{u}ᵒᵖ} (x : 𝒢.R.obj T)
      (h : 𝒢.s.app T (inv'.app T x) = 𝒢.t.app T x),
      𝒢.comp (inv'.app T x) x h = 𝒢.e.app T (𝒢.s.app T x)) :
    inv' = 𝒢.inv := by
  ext T x
  have hs : 𝒢.s.app T (inv'.app T x) = 𝒢.t.app T x := by
    rw [← NatTrans.comp_app_apply, hinv_s]
  -- `inv' x ∘ (x ∘ inv x) = inv' x` since `x ∘ inv x = e(t x)`
  have h1 : 𝒢.comp (inv'.app T x) (𝒢.comp x (𝒢.inv.app T x) (by simp))
      (by rw [hs]; simp) = inv'.app T x := by
    simp only [𝒢.comp_inv]
    exact 𝒢.comp_e_app _ _ _
  -- reassociating, the same composition is `(inv' x ∘ x) ∘ inv x = e(s x) ∘ inv x = inv x`
  have h2 : 𝒢.comp (inv'.app T x) (𝒢.comp x (𝒢.inv.app T x) (by simp))
      (by rw [hs]; simp) = 𝒢.inv.app T x := by
    rw [← 𝒢.comp_assoc (inv'.app T x) x (𝒢.inv.app T x) hs (by simp)
      (by simp) (by rw [hs]; simp)]
    simp only [hinv_comp]
    exact 𝒢.e_app_comp _ _ _
  exact h1.symm.trans h2

end AlgebraicGeometry.PresheafGroupoid

end ExerIdentityInverseUnique
