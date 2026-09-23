module

public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.2a-action-quotient-prestacks»
public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.3-morphisms-of-prestacks»
public import StacksAndModuli.API.PrestackComponents

/-!
# Free action quotients

This module formalizes Exercise 3.4.20
(`exer:quotient-stack-of-free-action`). For a natural action of a group-valued
presheaf `G` on a set-valued presheaf `U`, the action graph
`(g, u) ↦ (g • u, u)` is a monomorphism exactly when the action-quotient prestack
`[U/G]^pre` is equivalent over the base to a set-valued presheaf.

For a smooth affine group object acting on an `S`-scheme `U`, it also proves the
parallel assertion for the principal-bundle quotient stack `[U/G]`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section ExerQuotientStackOfFreeAction

open CategoryTheory Functor Opposite

universe w v u

namespace CategoryTheory.PresheafAction

variable {C : Type u} [Category.{v} C] (A : PresheafAction.{w} C)

/-- Background definition for Exercise 3.4.20 (the implicit
action map): the component over `T` of the action graph `(σ, p₂)`, given by
`(g, x) ↦ (g • x, x)`. The compatibility `PresheafAction.map_smul` is exactly
the naturality of these component maps. -/
def actionGraph (T : Cᵒᵖ) :
    A.G.obj T × A.U.obj T → A.U.obj T × A.U.obj T := by
  letI := A.action T
  exact fun z ↦ (z.1 • z.2, z.2)

@[simp]
lemma actionGraph_app_apply (T : Cᵒᵖ)
    (z : A.G.obj T × A.U.obj T) :
    A.actionGraph T z =
      (letI := A.action T; (z.1 • z.2, z.2)) :=
  rfl

/-- The pointwise action graphs commute with restriction; hence they are the
components of the book's morphism of presheaves `(σ, p₂)`. -/
lemma actionGraph_naturality {T T' : Cᵒᵖ} (f : T ⟶ T')
    (z : A.G.obj T × A.U.obj T) :
    (A.U.map f (A.actionGraph T z).1,
        A.U.map f (A.actionGraph T z).2) =
      A.actionGraph T' (A.G.map f z.1, A.U.map f z.2) := by
  rw [actionGraph_app_apply, actionGraph_app_apply]
  exact Prod.ext (A.map_smul f z.1 z.2) rfl

/-- Background definition for Exercise 3.4.20 (the implicit
definition): the action is free when every component of its action graph
`(σ, p₂)` is injective. This is the pointwise characterization of a
monomorphism of set-valued presheaves. -/
abbrev IsFree : Prop :=
  ∀ T : Cᵒᵖ, Function.Injective (A.actionGraph T)

/-- A free action has faithful action-quotient projection. -/
lemma quotientProj_faithful_of_isFree (hA : A.IsFree) :
    A.quotientProj.Faithful := by
  constructor
  intro x y f g hbase
  change f.base = g.base at hbase
  apply QuotientHom.ext
  · exact hbase
  · letI := A.action (op x.base)
    have hleft : A.U.map f.base.op y.point =
        A.U.map g.base.op y.point := by
      rw [hbase]
    have hsmul : f.gauge • x.point = g.gauge • x.point :=
      f.relation.symm.trans (hleft.trans g.relation)
    have hpairs :
        A.actionGraph (op x.base) (f.gauge, x.point) =
          A.actionGraph (op x.base) (g.gauge, x.point) := by
      exact Prod.ext hsmul rfl
    exact congrArg (fun p ↦ p.1) (hA (op x.base) hpairs)

/-- Faithfulness of the action-quotient projection forces the action to be free. -/
lemma isFree_of_quotientProj_faithful [A.quotientProj.Faithful] : A.IsFree := by
  intro T z z' hzz'
  rcases z with ⟨g, x⟩
  rcases z' with ⟨h, y⟩
  letI := A.action T
  change (g • x, x) = (h • y, y) at hzz'
  have hxy : x = y := congrArg (fun p ↦ p.2) hzz'
  subst y
  have hsmul : g • x = h • x := congrArg (fun p ↦ p.1) hzz'
  let source : A.QuotientObj :=
    { base := T.unop
      point := x }
  let target : A.QuotientObj :=
    { base := T.unop
      point := g • x }
  let phi : A.QuotientHom source target :=
    { base := 𝟙 T.unop
      gauge := g
      relation := by
        change A.U.map (𝟙 T) (g • x) = g • x
        simpa using congrArg (fun q ↦ q (g • x)) (A.U.map_id T) }
  let psi : A.QuotientHom source target :=
    { base := 𝟙 T.unop
      gauge := h
      relation := by
        calc
          A.U.map (𝟙 T) (g • x) = g • x := by
            simpa using congrArg (fun q ↦ q (g • x)) (A.U.map_id T)
          _ = h • x := hsmul }
  have hphiPsi : phi = psi := by
    apply A.quotientProj.map_injective
    rfl
  exact Prod.ext (congrArg QuotientHom.gauge hphiPsi) rfl

/-- The action-quotient projection is faithful exactly for a free action. -/
theorem quotientProj_faithful_iff_isFree :
    A.quotientProj.Faithful ↔ A.IsFree := by
  constructor
  · intro h
    letI := h
    exact A.isFree_of_quotientProj_faithful
  · exact A.quotientProj_faithful_of_isFree

/-- **Exercise 3.4.20** (`exer:quotient-stack-of-free-action`)
(quotient-prestack assertion): `G` acts freely on `U` if and only if the
action-quotient prestack `[U/G]^pre` is equivalent to a set-valued presheaf. -/
theorem quotientPrestack_isEquivalentToPresheaf_iff_isFree :
    BasedCategory.IsEquivalentToPresheaf (𝒳 := A.quotientPrestack) ↔ A.IsFree := by
  letI : (A.quotientPrestack).p.IsFiberedInGroupoids := by
    change A.quotientProj.IsFiberedInGroupoids
    infer_instance
  rw [BasedCategory.isEquivalentToPresheaf_iff_projection_faithful
    (𝒳 := A.quotientPrestack)]
  change A.quotientProj.Faithful ↔ A.IsFree
  exact A.quotientProj_faithful_iff_isFree

end CategoryTheory.PresheafAction

end ExerQuotientStackOfFreeAction

section ExerQuotientStackOfFreeAction

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open scoped CategoryTheory.Obj CategoryTheory.ModObj

universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} (G U : Over S) [GrpObj G]
  [Smooth G.hom] [IsAffineHom G.hom] [ModObj G U]

/-- Helper lemma used in the proof of Exercise 3.4.20 (quotient-stack
direction): if `[U/G] → Sch/S` is faithful, then the action graph
`(σ,p₂) : G ×ₛ U → U ×ₛ U` is a monomorphism. -/
lemma actionGraph_mono_of_quotientStack_projection_faithful
    [(actionQuotientPrestack G U).p.Faithful] :
    Mono (ModObj.leftSMul G U) := by
  constructor
  intro Z a b hab
  have hsnd : a ≫ snd G U = b ≫ snd G U := by
    simpa only [Category.assoc, ModObj.leftSMul_snd] using
      congrArg (fun q ↦ q ≫ snd U U) hab
  let m : Z ⟶ G := a ≫ fst G U
  let n : Z ⟶ G := b ≫ fst G U
  let u : Z ⟶ U := a ≫ snd G U
  have hmu : m • u = n • u := by
    change lift m u ≫ γ[G, U] = lift n u ≫ γ[G, U]
    have ha : lift m u = a := by
      apply CartesianMonoidalCategory.hom_ext
      · simp [m]
      · simp [u]
    have hb : lift n u = b := by
      apply CartesianMonoidalCategory.hom_ext
      · simp [n]
      · simpa [u] using hsnd
    rw [ha, hb]
    simpa only [Category.assoc, ModObj.leftSMul_fst] using
      congrArg (fun q ↦ q ≫ fst U U) hab
  let v : Z ⟶ U := m • u
  let phi := ActionQuotientHom.trivialGaugeOfEq (G := G) v m u rfl
  let psi := ActionQuotientHom.trivialGaugeOfEq (G := G) v n u hmu.symm
  have hphiPsi : phi = psi := by
    apply (actionQuotientPrestack G U).p.map_injective
    change (𝟙 Z : Z ⟶ Z) = 𝟙 Z
    rfl
  have hmn : m = n := by
    apply GlobalPrincipalBundle.trivialRightTranslate_injective (G := G) (T := Z)
    exact congrArg (fun q ↦ q.carrier.total) hphiPsi
  apply CartesianMonoidalCategory.hom_ext
  · exact hmn
  · exact hsnd

/-- Helper lemma used in the proof of Exercise 3.4.20 (quotient-stack
direction): a free action makes the projection `[U/G] → Sch/S` faithful. -/
lemma quotientStack_projection_faithful_of_actionGraph_mono
    [Mono (ModObj.leftSMul G U)] :
    (actionQuotientPrestack G U).p.Faithful := by
  constructor
  intro x y f g hbase
  change ActionQuotientObj G U at x y
  change ActionQuotientHom G U x y at f g
  change f.carrier.base = g.carrier.base at hbase
  have hp : f.carrier.total ≫ y.carrier.bundle.p =
      g.carrier.total ≫ y.carrier.bundle.p := by
    calc
      f.carrier.total ≫ y.carrier.bundle.p =
          x.carrier.bundle.p ≫ f.carrier.base := f.carrier.isPullback.w
      _ = x.carrier.bundle.p ≫ g.carrier.base := by rw [hbase]
      _ = g.carrier.total ≫ y.carrier.bundle.p := g.carrier.isPullback.w.symm
  let d : x.carrier.bundle.P ⟶ G :=
    GlobalPrincipalBundle.torsorDifference y.carrier.bundle
      f.carrier.total g.carrier.total hp
  have hdsmul : d • g.carrier.total = f.carrier.total :=
    GlobalPrincipalBundle.torsorDifference_smul y.carrier.bundle
      f.carrier.total g.carrier.total hp
  letI : IsModHom G y.map := y.equivariant
  have hdmap : d • x.map = x.map := by
    calc
      d • x.map = d • (g.carrier.total ≫ y.map) := by
        rw [g.map_naturality]
      _ = (d • g.carrier.total) ≫ y.map := by
        rw [IsModHom.map_smul]
      _ = f.carrier.total ≫ y.map := by rw [hdsmul]
      _ = x.map := f.map_naturality
  have hgraph : lift d x.map ≫ ModObj.leftSMul G U =
      lift (1 : x.carrier.bundle.P ⟶ G) x.map ≫
        ModObj.leftSMul G U := by
    rw [ModObj.lift_leftSMul, ModObj.lift_leftSMul]
    rw [hdmap, one_smul]
  have hlift : lift d x.map =
      lift (1 : x.carrier.bundle.P ⟶ G) x.map := by
    apply (cancel_mono (ModObj.leftSMul G U)).mp
    exact hgraph
  have hd : d = (1 : x.carrier.bundle.P ⟶ G) := by
    simpa only [lift_fst] using congrArg
      (fun q ↦ q ≫ fst G U) hlift
  apply ActionQuotientHom.ext
  apply ClassifyingHom.ext
  · exact hbase
  · calc
      f.carrier.total = d • g.carrier.total := hdsmul.symm
      _ = (1 : x.carrier.bundle.P ⟶ G) • g.carrier.total := by rw [hd]
      _ = g.carrier.total := by simp

/-- **Exercise 3.4.20** (`exer:quotient-stack-of-free-action`) (quotient-stack
assertion): a smooth affine group object `G` acts freely on `U`—equivalently,
the action graph `(σ,p₂) : G ×ₛ U → U ×ₛ U` is a monomorphism—if and only if
the quotient stack `[U/G]` is equivalent to a presheaf. -/
theorem quotientStack_isEquivalentToPresheaf_iff_actionGraph_mono :
    BasedCategory.IsEquivalentToPresheaf (𝒳 := quotientStack G U) ↔
      Mono (ModObj.leftSMul G U) := by
  letI : (quotientStack G U).p.IsFiberedInGroupoids := inferInstance
  rw [BasedCategory.isEquivalentToPresheaf_iff_projection_faithful]
  constructor
  · intro h
    letI := h
    exact actionGraph_mono_of_quotientStack_projection_faithful G U
  · intro h
    letI := h
    exact quotientStack_projection_faithful_of_actionGraph_mono G U

end AlgebraicGeometry.Scheme

end ExerQuotientStackOfFreeAction
