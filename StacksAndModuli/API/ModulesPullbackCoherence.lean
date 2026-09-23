module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Tactic.CategoryTheory.Slice

/-!
# Coherence for iterated module pullbacks over pasted squares

Supporting API with no Stacks Project counterpart.

The structural isomorphisms `Modules.pullbackComp` and `Modules.pullbackCongr` make
`Modules.pullback` a pseudofunctor on schemes; Mathlib records the associativity and
unitality coherences as whole-natural-transformation identities
(`Modules.pseudofunctor_associativity` and friends).  Applications — the Quot and
Grassmannian functors of Chapter 2 — need *component-level* consequences: that two
composites of structural cells realizing the same identification of iterated pullbacks
agree.  This file provides them, in the substitution-friendly style of
`PullbackQuotient.cocycle_aux` (part2.1.2): scheme morphisms are free variables and the
defining equalities are hypotheses, so instantiation at concrete pullback squares is by
`exact`.

The main result `pullback_theta_coherence` treats the theta-shaped diagram arising when
a relative-Grassmannian datum on a base-changed test object is compared with the base
change of the datum: two commuting squares over a common base glued along their
projections.  `pullback_theta_coherence_iso` is the same statement with an ambient
identification `u : V ≅ (pullback pi).obj M` carried along.

Main declarations:
- `Modules.pullbackCongr_hom_app`, `Modules.pullbackCongr_inv_app`;
- `Modules.pullbackComp_assoc_inv_hom_app` (component-level associativity);
- `Modules.pullback_theta_coherence`, `Modules.pullback_theta_coherence_iso`.
-/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {W X Y Z : Scheme.{u}}

/-- The component of a `pullbackCongr` cell is an equality-transport morphism. -/
lemma pullbackCongr_hom_app {f g : X ⟶ Y} (h : f = g) (M : Y.Modules) :
    (pullbackCongr h).hom.app M = eqToHom (by rw [h]) := by
  subst h
  simp [pullbackCongr]

/-- The component of an inverse `pullbackCongr` cell is an equality-transport
morphism. -/
lemma pullbackCongr_inv_app {f g : X ⟶ Y} (h : f = g) (M : Y.Modules) :
    (pullbackCongr h).inv.app M = eqToHom (by rw [h]) := by
  subst h
  simp [pullbackCongr]

/-- Component-level associativity of the pullback-composition cells: decomposing a
pullback along `f ≫ (g ≫ h)` in two stages and reassociating agrees with the
decomposition along `(f ≫ g) ≫ h`. -/
@[reassoc]
lemma pullbackComp_assoc_inv_hom_app (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (M : Z.Modules) :
    (pullbackComp f (g ≫ h)).inv.app M ≫
      (pullback f).map ((pullbackComp g h).inv.app M) ≫
        (pullbackComp f g).hom.app ((pullback h).obj M) =
    (pullbackCongr (Category.assoc f g h).symm).hom.app M ≫
      (pullbackComp (f ≫ g) h).inv.app M := by
  have hassoc := NatTrans.congr_app
    (pseudofunctor_associativity (f := f) (g := g) (h := h)) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, eqToHom_app] at hassoc
  rw [pullbackCongr_hom_app, ← cancel_mono ((pullbackComp (f ≫ g) h).hom.app M)]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  exact hassoc

/-- Rearranged associativity: peeling one stage off the composite pullback from the
left. -/
@[reassoc]
lemma pullbackComp_inv_app_map_inv_app (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (M : Z.Modules) :
    (pullbackComp f (g ≫ h)).inv.app M ≫
      (pullback f).map ((pullbackComp g h).inv.app M) =
    (pullbackCongr (Category.assoc f g h).symm).hom.app M ≫
      (pullbackComp (f ≫ g) h).inv.app M ≫
        (pullbackComp f g).inv.app ((pullback h).obj M) := by
  rw [← cancel_mono ((pullbackComp f g).hom.app ((pullback h).obj M))]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  exact pullbackComp_assoc_inv_hom_app f g h M

/-- Rearranged associativity: recomposing one stage of the composite pullback from the
left. -/
@[reassoc]
lemma pullbackComp_inv_app_map_hom_app (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (M : Z.Modules) :
    (pullbackComp f g).inv.app ((pullback h).obj M) ≫
      (pullback f).map ((pullbackComp g h).hom.app M) =
    (pullbackComp (f ≫ g) h).hom.app M ≫
      (pullbackCongr (Category.assoc f g h)).hom.app M ≫
        (pullbackComp f (g ≫ h)).inv.app M := by
  have hassoc := NatTrans.congr_app
    (pseudofunctor_associativity (f := f) (g := g) (h := h)) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, eqToHom_app] at hassoc
  rw [← cancel_epi ((pullbackComp f g).hom.app ((pullback h).obj M)),
    ← cancel_mono ((pullbackComp f (g ≫ h)).hom.app M)]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app,
    Category.comp_id]
  rw [← cancel_epi ((pullback f).map ((pullbackComp g h).inv.app M)),
    ← cancel_epi ((pullbackComp f (g ≫ h)).inv.app M)]
  slice_rhs 1 4 => rw [hassoc]
  slice_lhs 2 3 => rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id]
  simp only [pullbackCongr_hom_app, Category.id_comp, Iso.inv_hom_id_app,
    eqToHom_refl, Category.comp_id]

/-- A `pullbackCongr` cell on the inner factor commutes with the composition cell. -/
@[reassoc]
lemma pullbackComp_inv_app_map_pullbackCongr_hom {f : W ⟶ X} {a b : X ⟶ Y}
    (h : a = b) (M : Y.Modules) :
    (pullbackComp f a).inv.app M ≫
      (pullback f).map ((pullbackCongr h).hom.app M) =
    (pullbackCongr (congrArg (f ≫ ·) h)).hom.app M ≫
      (pullbackComp f b).inv.app M := by
  subst h
  simp [pullbackCongr]

/-- A `pullbackCongr` cell on the outer factor commutes with the composition cell. -/
@[reassoc]
lemma pullbackComp_inv_app_pullbackCongr_hom {a b : W ⟶ X} {t : X ⟶ Y}
    (h : a = b) (M : Y.Modules) :
    (pullbackComp a t).inv.app M ≫
      (pullbackCongr h).hom.app ((pullback t).obj M) =
    (pullbackCongr (congrArg (· ≫ t) h)).hom.app M ≫
      (pullbackComp b t).inv.app M := by
  subst h
  simp [pullbackCongr]

/-- A reflexive `pullbackCongr` cell is the identity; composing with it does
nothing.  Stated in composition form so it can be used by `rw` mid-chain. -/
lemma pullbackCongr_refl_inv_app_comp {a : X ⟶ Y} (h : a = a) (M : Y.Modules)
    {Q : X.Modules} (x : (pullback a).obj M ⟶ Q) :
    (pullbackCongr h).inv.app M ≫ x = x :=
  Category.id_comp x

/-- The functorial image of a reflexive `pullbackCongr` cell is the identity;
composing with it does nothing. -/
lemma map_pullbackCongr_refl_inv_app_comp {q : W ⟶ X} {a : X ⟶ Y} (h : a = a)
    (M : Y.Modules) {Q : W.Modules}
    (x : (pullback q).obj ((pullback a).obj M) ⟶ Q) :
    (pullback q).map ((pullbackCongr h).inv.app M) ≫ x = x := by
  have hcell : (pullback q).map ((pullbackCongr h).inv.app M) = 𝟙 _ :=
    (congrArg (pullback q).map
      (rfl : (pullbackCongr h).inv.app M = 𝟙 _)).trans ((pullback q).map_id _)
  rw [hcell]
  exact Category.id_comp x

section Theta

variable {P' T' Tl PP P B : Scheme.{u}}

/-- Coherence over a theta-shaped diagram: two commuting squares over a common base
`B`, glued along their projections.  The left square is the base-changed test object
(`snd' ≫ pi = fst' ≫ t'` with `t' = gl ≫ t`), the right square the original one
(`snd ≫ pi = fst ≫ t`), and `G` compares them (`fst' ≫ gl = G ≫ fst`,
`G ≫ snd = snd'`).  The two canonical structural composites from
`(pullback snd').obj ((pullback pi).obj M)` to
`(pullback G).obj ((pullback fst).obj ((pullback t).obj M))` agree. -/
lemma pullback_theta_coherence
    (snd' : P' ⟶ PP) (pi : PP ⟶ B) (fst' : P' ⟶ T') (t' : T' ⟶ B)
    (gl : T' ⟶ Tl) (t : Tl ⟶ B) (G : P' ⟶ P) (fst : P ⟶ Tl) (snd : P ⟶ PP)
    (h₁ : snd' ≫ pi = fst' ≫ t') (hgl : gl ≫ t = t')
    (h₃ : fst' ≫ gl = G ≫ fst) (h₄ : G ≫ snd = snd')
    (h₅ : snd ≫ pi = fst ≫ t) (M : B.Modules) :
    (pullbackComp snd' pi).hom.app M ≫
      (pullbackCongr h₁).hom.app M ≫
      (pullbackComp fst' t').inv.app M ≫
      (pullback fst').map ((pullbackCongr hgl).inv.app M) ≫
      (pullback fst').map ((pullbackComp gl t).inv.app M) ≫
      (pullbackComp fst' gl).hom.app ((pullback t).obj M) ≫
      (pullbackCongr h₃).hom.app ((pullback t).obj M) ≫
      (pullbackComp G fst).inv.app ((pullback t).obj M) =
    (pullbackCongr h₄).inv.app ((pullback pi).obj M) ≫
      (pullbackComp G snd).inv.app ((pullback pi).obj M) ≫
      (pullback G).map ((pullbackComp snd pi).hom.app M) ≫
      (pullback G).map ((pullbackCongr h₅).hom.app M) ≫
      (pullback G).map ((pullbackComp fst t).inv.app M) := by
  subst hgl h₄
  rw [map_pullbackCongr_refl_inv_app_comp]
  rw [pullbackCongr_refl_inv_app_comp]
  rw [pullbackComp_assoc_inv_hom_app_assoc fst' gl t M]
  rw [pullbackComp_inv_app_pullbackCongr_hom_assoc h₃ M]
  rw [pullbackComp_inv_app_map_hom_app_assoc G snd pi M]
  rw [pullbackComp_inv_app_map_pullbackCongr_hom_assoc h₅ M]
  rw [pullbackComp_inv_app_map_inv_app G fst t M]
  simp only [pullbackCongr_hom_app, eqToHom_trans_assoc]

/-- The theta coherence with an ambient identification `u : V ≅ (pullback pi).obj M`
carried along, in the exact shape produced by comparing base-changed relative
Grassmannian data. -/
lemma pullback_theta_coherence_iso
    (snd' : P' ⟶ PP) (pi : PP ⟶ B) (fst' : P' ⟶ T') (t' : T' ⟶ B)
    (gl : T' ⟶ Tl) (t : Tl ⟶ B) (G : P' ⟶ P) (fst : P ⟶ Tl) (snd : P ⟶ PP)
    (h₁ : snd' ≫ pi = fst' ≫ t') (hgl : gl ≫ t = t')
    (h₃ : fst' ≫ gl = G ≫ fst) (h₄ : G ≫ snd = snd')
    (h₅ : snd ≫ pi = fst ≫ t) (M : B.Modules)
    {V : PP.Modules} (u : V ≅ (pullback pi).obj M) :
    (pullback snd').map u.hom ≫
      (pullbackComp snd' pi).hom.app M ≫
      (pullbackCongr h₁).hom.app M ≫
      (pullbackComp fst' t').inv.app M ≫
      (pullback fst').map ((pullbackCongr hgl).inv.app M) ≫
      (pullback fst').map ((pullbackComp gl t).inv.app M) ≫
      (pullbackComp fst' gl).hom.app ((pullback t).obj M) ≫
      (pullbackCongr h₃).hom.app ((pullback t).obj M) ≫
      (pullbackComp G fst).inv.app ((pullback t).obj M) =
    (pullbackCongr h₄).inv.app V ≫
      (pullbackComp G snd).inv.app V ≫
      (pullback G).map ((pullback snd).map u.hom) ≫
      (pullback G).map ((pullbackComp snd pi).hom.app M) ≫
      (pullback G).map ((pullbackCongr h₅).hom.app M) ≫
      (pullback G).map ((pullbackComp fst t).inv.app M) := by
  have hnat₁ : (pullbackCongr h₄).inv.app V ≫
      (pullback (G ≫ snd)).map u.hom =
      (pullback snd').map u.hom ≫
        (pullbackCongr h₄).inv.app ((pullback pi).obj M) :=
    ((pullbackCongr h₄).inv.naturality u.hom).symm
  have hnat₂ : (pullbackComp G snd).inv.app V ≫
      (pullback G).map ((pullback snd).map u.hom) =
      (pullback (G ≫ snd)).map u.hom ≫
        (pullbackComp G snd).inv.app ((pullback pi).obj M) :=
    ((pullbackComp G snd).inv.naturality u.hom).symm
  slice_rhs 2 3 => rw [hnat₂]
  slice_rhs 1 2 => rw [hnat₁]
  simp only [Category.assoc]
  congr 1
  exact pullback_theta_coherence snd' pi fst' t' gl t G fst snd h₁ hgl h₃ h₄ h₅ M

end Theta

section InversePair

variable {X Y : Scheme.{u}}

/-- Left-unitality at a component: the functorial image of the inverse identity cell
factors through the composition cell for `f ≫ 𝟙`. -/
lemma pullbackId_inv_app_map (f : X ⟶ Y) (M : Y.Modules) :
    (pullback f).map ((pullbackId Y).inv.app M) =
    (pullbackCongr (Category.comp_id f).symm).hom.app M ≫
      (pullbackComp f (𝟙 Y)).inv.app M := by
  have hlu := NatTrans.congr_app (pseudofunctor_left_unitality (f := f)) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, eqToHom_app] at hlu
  have hlu' : (pullbackComp f (𝟙 Y)).inv.app M ≫
      (pullback f).map ((pullbackId Y).hom.app M) = eqToHom (by simp) :=
    ((congrArg (fun t => (pullbackComp f (𝟙 Y)).inv.app M ≫ t)
      (Category.comp_id
        ((pullback f).map ((pullbackId Y).hom.app M)))).symm).trans hlu
  rw [pullbackCongr_hom_app,
    ← cancel_mono ((pullback f).map ((pullbackId Y).hom.app M))]
  rw [show (pullback f).map ((pullbackId Y).inv.app M) ≫
      (pullback f).map ((pullbackId Y).hom.app M) = 𝟙 _ from by
    rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app]
    exact (pullback f).map_id _]
  rw [Category.assoc, hlu']
  simp

/-- Right-unitality at a component: the outer identity cell factors through the
composition cell for `𝟙 ≫ f`. -/
lemma pullbackId_hom_app_comp (f : X ⟶ Y) (M : Y.Modules) :
    (pullbackId X).hom.app ((pullback f).obj M) =
    (pullbackComp (𝟙 X) f).hom.app M ≫
      (pullbackCongr (Category.id_comp f)).hom.app M := by
  have hru := NatTrans.congr_app (pseudofunctor_right_unitality (f := f)) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, eqToHom_app] at hru
  have hru' : (pullbackComp (𝟙 X) f).inv.app M ≫
      (pullbackId X).hom.app ((pullback f).obj M) = eqToHom (by simp) :=
    ((congrArg (fun t => (pullbackComp (𝟙 X) f).inv.app M ≫ t)
      (Category.comp_id
        ((pullbackId X).hom.app ((pullback f).obj M)))).symm).trans hru
  rw [pullbackCongr_hom_app, ← cancel_epi ((pullbackComp (𝟙 X) f).inv.app M),
    hru', ← Category.assoc, Iso.inv_hom_id_app]
  simp

variable {f : X ⟶ Y} {g : Y ⟶ X}

/-- For a pair of mutually inverse scheme morphisms, the composite of the two
pullback functors is structurally the identity: the unit of the induced adjoint
equivalence of module categories. -/
noncomputable def pullbackInverseUnit (hgf : g ≫ f = 𝟙 Y) :
    𝟭 Y.Modules ≅ pullback f ⋙ pullback g :=
  (pullbackComp g f ≪≫ pullbackCongr hgf ≪≫ pullbackId Y).symm

/-- For a pair of mutually inverse scheme morphisms, the composite of the two
pullback functors is structurally the identity: the counit of the induced adjoint
equivalence of module categories. -/
noncomputable def pullbackInverseCounit (hfg : f ≫ g = 𝟙 X) :
    pullback g ⋙ pullback f ≅ 𝟭 X.Modules :=
  pullbackComp f g ≪≫ pullbackCongr hfg ≪≫ pullbackId X

/-- The triangle identity for the structural unit and counit of the pullback
equivalence induced by a pair of mutually inverse scheme morphisms. -/
lemma pullbackInverse_triangle (hgf : g ≫ f = 𝟙 Y) (hfg : f ≫ g = 𝟙 X)
    (M : Y.Modules) :
    (pullback f).map ((pullbackInverseUnit hgf).hom.app M) ≫
      (pullbackInverseCounit hfg).hom.app ((pullback f).obj M) =
    𝟙 ((pullback f).obj M) := by
  simp only [pullbackInverseUnit, pullbackInverseCounit, Iso.trans_hom,
    Iso.symm_hom, Iso.trans_inv, NatTrans.comp_app,
    CategoryTheory.Functor.map_comp, Category.assoc]
  rw [pullbackId_inv_app_map f M]
  rw [show (pullback f).map ((pullbackCongr hgf).inv.app M) =
      (pullback f).map ((pullbackCongr hgf.symm).hom.app M) from by
    rw [pullbackCongr_inv_app, pullbackCongr_hom_app]]
  simp only [Category.assoc]
  rw [pullbackComp_inv_app_map_pullbackCongr_hom_assoc hgf.symm M]
  rw [pullbackComp_inv_app_map_inv_app_assoc f g f M]
  rw [pullbackId_hom_app_comp f M]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [pullbackComp_inv_app_pullbackCongr_hom_assoc hfg M]
  simp only [Iso.inv_hom_id_app_assoc, pullbackCongr_hom_app, eqToHom_trans]
  exact eqToHom_refl ((pullback f).obj M) _

end InversePair

end AlgebraicGeometry.Scheme.Modules

end
