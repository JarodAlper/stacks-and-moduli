module

public import StacksAndModuli.API.ModPullback
public import StacksAndModuli.Util.FpqcCover
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Square
public import Mathlib.CategoryTheory.Monoidal.Grp

/-!
# Principal bundles for a fixed group object

Let `G` be a group object of a cartesian category, acting on `P`, and let
`p : P ⟶ T` be invariant.  The torsor map is `(g, x) ↦ (g • x, x)` from
`G × P` to `P ×ₜ P`.  This file proves directly that its being an isomorphism
is stable under pullback of `p` while the acting group remains fixed.

For schemes over a fixed base `S`, `GlobalPrincipalBundle G T` packages this
construction together with the fppf hypotheses.  This is the form used by the
classifying and quotient prestacks: `G`, `P`, and `T` all live in `Scheme/S`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open scoped CategoryTheory.Obj CategoryTheory.ModObj

universe v u

namespace CategoryTheory.ModObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory.{v} C]
  [HasPullbacks C]
variable {G P T T' : C} [GrpObj G]
variable [ModObj G P]

/-- The torsor map `(g, x) ↦ (g • x, x)` associated to an invariant map
`p : P ⟶ T`. -/
noncomputable def torsorMap (p : P ⟶ T)
    (hp : γ[G, P] ≫ p = snd G P ≫ p) : G ⊗ P ⟶ pullback p p :=
  pullback.lift γ[G, P] (snd G P) hp

/-- The natural `G`-action on the pullback of an invariant map `p` along an
arbitrary map `f`. -/
@[instance_reducible]
noncomputable def pullbackTorsorAction (p : P ⟶ T) (f : T' ⟶ T)
    (hp : γ[G, P] ≫ p = snd G P ≫ p) :
    ModObj G (pullback p f) := by
  letI : ModObj G T := ModObj.trivialAction G T
  letI : ModObj G T' := ModObj.trivialAction G T'
  letI : IsModHom G p := by
    constructor
    rw [hp]
    change snd G P ≫ p = (G ◁ p) ≫ snd G T
    simp
  letI : IsModHom G f := ModObj.isModHom_trivialAction G f
  exact ModObj.pullbackAction G p f

/-- The projection of the pulled-back action is invariant. -/
lemma pullbackTorsorAction_invariant (p : P ⟶ T) (f : T' ⟶ T)
    (hp : γ[G, P] ≫ p = snd G P ≫ p) :
    letI := pullbackTorsorAction p f hp
    γ[G, pullback p f] ≫ pullback.snd p f =
      snd G (pullback p f) ≫ pullback.snd p f := by
  change pullback.lift
      ((G ◁ pullback.fst p f) ≫ γ[G, P])
      ((G ◁ pullback.snd p f) ≫ snd G T') _ ≫ pullback.snd p f = _
  rw [pullback.lift_snd]
  simp

/-- The map from the pair space of a pulled-back object to the original pair
space. -/
noncomputable def pullbackPairMap (p : P ⟶ T) (f : T' ⟶ T) :
    pullback (pullback.snd p f) (pullback.snd p f) ⟶ pullback p p :=
  pullback.lift
    (pullback.fst _ _ ≫ pullback.fst p f)
    (pullback.snd _ _ ≫ pullback.fst p f)
    (by
      calc
        (pullback.fst _ _ ≫ pullback.fst p f) ≫ p =
            pullback.fst _ _ ≫ (pullback.snd p f ≫ f) := by
          rw [Category.assoc, pullback.condition]
        _ = (pullback.fst _ _ ≫ pullback.snd p f) ≫ f :=
          (Category.assoc _ _ _).symm
        _ = (pullback.snd _ _ ≫ pullback.snd p f) ≫ f := by
          rw [pullback.condition]
        _ = pullback.snd _ _ ≫ (pullback.snd p f ≫ f) :=
          Category.assoc _ _ _
        _ = (pullback.snd _ _ ≫ pullback.fst p f) ≫ p := by
          rw [Category.assoc, pullback.condition])

@[reassoc (attr := simp)]
lemma torsorMap_fst (p : P ⟶ T) (hp : γ[G, P] ≫ p = snd G P ≫ p) :
    torsorMap p hp ≫ pullback.fst p p = γ[G, P] :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma torsorMap_snd (p : P ⟶ T) (hp : γ[G, P] ≫ p = snd G P ≫ p) :
    torsorMap p hp ≫ pullback.snd p p = snd G P :=
  pullback.lift_snd _ _ _

lemma pullbackTorsor_square (p : P ⟶ T) (f : T' ⟶ T)
    (hp : γ[G, P] ≫ p = snd G P ≫ p) :
    letI := pullbackTorsorAction p f hp
    torsorMap (pullback.snd p f) (pullbackTorsorAction_invariant p f hp) ≫
      pullbackPairMap p f = (G ◁ pullback.fst p f) ≫ torsorMap p hp := by
  letI := pullbackTorsorAction p f hp
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackPairMap, pullback.lift_fst]
    rw [torsorMap_fst_assoc]
    change pullback.lift
        ((G ◁ pullback.fst p f) ≫ γ[G, P])
        ((G ◁ pullback.snd p f) ≫ snd G T') _ ≫ pullback.fst p f = _
    rw [pullback.lift_fst]
    simp [Category.assoc]
  · simp [Category.assoc, torsorMap, pullbackPairMap]

/-- An explicit inverse to the torsor map after pullback. -/
noncomputable def pullbackTorsorInv (p : P ⟶ T) (f : T' ⟶ T)
    (hp : γ[G, P] ≫ p = snd G P ≫ p)
    [IsIso (torsorMap p hp)] :
    pullback (pullback.snd p f) (pullback.snd p f) ⟶
      G ⊗ pullback p f :=
  lift
    (pullbackPairMap p f ≫ inv (torsorMap p hp) ≫ fst G P)
    (pullback.snd _ _)

lemma pullbackTorsorInv_map (p : P ⟶ T) (f : T' ⟶ T)
    (hp : γ[G, P] ≫ p = snd G P ≫ p)
    [IsIso (torsorMap p hp)] :
    pullbackTorsorInv p f hp ≫ (G ◁ pullback.fst p f) =
      pullbackPairMap p f ≫ inv (torsorMap p hp) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [pullbackTorsorInv]
  · simp [pullbackTorsorInv]
    have hi : inv (torsorMap p hp) ≫ snd G P = pullback.snd p p := by
      rw [← torsorMap_snd p hp]
      simp
    rw [hi]
    simp [pullbackPairMap]

lemma pullbackTorsor_hom_inv (p : P ⟶ T) (f : T' ⟶ T)
    (hp : γ[G, P] ≫ p = snd G P ≫ p)
    [IsIso (torsorMap p hp)] :
    letI := pullbackTorsorAction p f hp
    torsorMap (pullback.snd p f) (pullbackTorsorAction_invariant p f hp) ≫
      pullbackTorsorInv p f hp = 𝟙 _ := by
  letI := pullbackTorsorAction p f hp
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, pullbackTorsorInv, lift_fst]
    rw [← Category.assoc, pullbackTorsor_square p f hp]
    simp
  · simp [Category.assoc, pullbackTorsorInv, torsorMap]

lemma pullbackTorsor_inv_hom (p : P ⟶ T) (f : T' ⟶ T)
    (hp : γ[G, P] ≫ p = snd G P ≫ p)
    [IsIso (torsorMap p hp)] :
    letI := pullbackTorsorAction p f hp
    pullbackTorsorInv p f hp ≫
      torsorMap (pullback.snd p f) (pullbackTorsorAction_invariant p f hp) =
        𝟙 _ := by
  letI := pullbackTorsorAction p f hp
  apply pullback.hom_ext
  · rw [Category.assoc, torsorMap_fst]
    apply pullback.hom_ext
    · have hact : γ[G, pullback p f] ≫ pullback.fst p f =
          (G ◁ pullback.fst p f) ≫ γ[G, P] := by
        change pullback.lift
            ((G ◁ pullback.fst p f) ≫ γ[G, P])
            ((G ◁ pullback.snd p f) ≫ snd G T') _ ≫ pullback.fst p f = _
        rw [pullback.lift_fst]
      rw [Category.assoc, hact]
      rw [← Category.assoc, pullbackTorsorInv_map p f hp]
      have hi : inv (torsorMap p hp) ≫ γ[G, P] = pullback.fst p p := by
        rw [← torsorMap_fst p hp]
        simp
      rw [Category.assoc, hi]
      simp [pullbackPairMap]
    · rw [Category.assoc, pullbackTorsorAction_invariant p f hp]
      simp [pullbackTorsorInv]
      exact (pullback.condition : pullback.fst (pullback.snd p f)
        (pullback.snd p f) ≫ pullback.snd p f = _).symm
  · simp [Category.assoc, pullbackTorsorInv, torsorMap]

/-- Pulling back an invariant action preserves the torsor isomorphism. -/
lemma isIso_pullbackTorsorMap (p : P ⟶ T) (f : T' ⟶ T)
    (hp : γ[G, P] ≫ p = snd G P ≫ p)
    [IsIso (torsorMap p hp)] :
    letI := pullbackTorsorAction p f hp
    IsIso (torsorMap (pullback.snd p f)
      (pullbackTorsorAction_invariant p f hp)) := by
  letI := pullbackTorsorAction p f hp
  exact ⟨⟨pullbackTorsorInv p f hp,
    pullbackTorsor_hom_inv p f hp,
    pullbackTorsor_inv_hom p f hp⟩⟩

/-! ## The universal regular torsor -/

variable (G)

/-- The regular action of a group object is simply transitive. -/
lemma isIso_regularLeftSMul :
    letI := ModObj.regular G
    IsIso (ModObj.leftSMul G G) := by
  letI := ModObj.regular G
  rw [ModObj.isIso_leftSMul_iff]
  intro Z x y
  refine ⟨y * x⁻¹, ?_, ?_⟩
  · change (y * x⁻¹) * x = y
    simp
  · intro m hm
    change m * x = y at hm
    apply mul_right_cancel (b := x)
    simpa [hm]

/-- The regular action is invariant over the terminal object. -/
lemma regular_invariant_toUnit :
    letI := ModObj.regular G
    γ[G, G] ≫ toUnit G = snd G G ≫ toUnit G := by
  letI := ModObj.regular G
  apply toUnit_unique

/-- The cartesian product is the pullback of the two maps to the terminal
object. -/
lemma tensorToUnit_isPullback (X Y : C) :
    IsPullback (fst X Y) (snd X Y) (toUnit X) (toUnit Y) :=
  IsPullback.of_is_product'
    (tensorProductIsBinaryProduct X Y)
    CartesianMonoidalCategory.isTerminalTensorUnit

/-- The canonical comparison from the cartesian tensor product to the
pullback over the terminal object. -/
noncomputable def tensorIsoPullbackToUnit (X Y : C) :
    X ⊗ Y ≅ pullback (toUnit X) (toUnit Y) :=
  (tensorToUnit_isPullback X Y).isoPullback

/-- For the regular action, the torsor map over the terminal object is the
usual map `(g, h) ↦ (gh, h)`, followed by the canonical product comparison. -/
lemma torsorMap_toUnit_eq :
    letI := ModObj.regular G
    torsorMap (toUnit G) (regular_invariant_toUnit G) =
      leftSMul G G ≫ (tensorIsoPullbackToUnit G G).hom := by
  letI := ModObj.regular G
  apply pullback.hom_ext
  · rw [torsorMap_fst]
    simp only [Category.assoc, tensorIsoPullbackToUnit,
      IsPullback.isoPullback_hom_fst, leftSMul_fst]
  · rw [torsorMap_snd]
    simp only [Category.assoc, tensorIsoPullbackToUnit,
      IsPullback.isoPullback_hom_snd, leftSMul_snd]

/-- The regular action makes a group object into a torsor over the terminal
object. -/
lemma isIso_torsorMap_toUnit :
    letI := ModObj.regular G
    IsIso (torsorMap (toUnit G) (regular_invariant_toUnit G)) := by
  letI := ModObj.regular G
  rw [torsorMap_toUnit_eq G]
  letI := isIso_regularLeftSMul G
  infer_instance

end CategoryTheory.ModObj

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} (G : Over S) [GrpObj G]

/-- A principal bundle over an `S`-scheme `T` for a fixed group object `G` of
`Scheme/S`.  The projection and action both live over `S`. -/
structure GlobalPrincipalBundle (T : Over S) where
  /-- The total space over `S`. -/
  P : Over S
  /-- The bundle projection. -/
  p : P ⟶ T
  /-- The action of the fixed group `G`. -/
  [action : ModObj G P]
  /-- The projection is invariant under the action. -/
  invariant : γ[G, P] ≫ p = snd G P ≫ p
  /-- The underlying projection of schemes is flat. -/
  [flat : Flat p.left]
  /-- The underlying projection of schemes is surjective. -/
  [surjective : Surjective p.left]
  /-- The underlying projection is locally of finite presentation. -/
  [locallyOfFinitePresentation : LocallyOfFinitePresentation p.left]
  /-- The underlying projection is smooth. -/
  [smooth : Smooth p.left]
  /-- The action is simply transitive in every fiber. -/
  [torsor : IsIso (ModObj.torsorMap p invariant)]

attribute [instance] GlobalPrincipalBundle.action GlobalPrincipalBundle.flat
  GlobalPrincipalBundle.surjective
  GlobalPrincipalBundle.locallyOfFinitePresentation GlobalPrincipalBundle.smooth
  GlobalPrincipalBundle.torsor

namespace GlobalPrincipalBundle

variable {G} {T T' : Over S}

/-- The structure morphism of a group object over a scheme is surjective: its
unit is a section. -/
lemma groupHom_surjective (G : Over S) [GrpObj G] : Surjective G.hom := by
  constructor
  intro x
  refine ⟨(η[G]).left x, ?_⟩
  have h := congrArg (fun k : S ⟶ S ↦ (Scheme.forget.map k) x) (η[G]).w
  exact h

/-- The group itself, with its regular action, is the universal principal
bundle over the terminal `S`-scheme. -/
noncomputable def universal (G : Over S) [GrpObj G] [Smooth G.hom]
    [IsAffineHom G.hom] : GlobalPrincipalBundle G (𝟙_ (Over S)) where
  P := G
  p := toUnit G
  action := ModObj.regular G
  invariant := ModObj.regular_invariant_toUnit G
  flat := by
    change Flat G.hom
    infer_instance
  surjective := by
    change Surjective G.hom
    exact groupHom_surjective G
  locallyOfFinitePresentation := by
    change LocallyOfFinitePresentation G.hom
    infer_instance
  smooth := by
    change Smooth G.hom
    infer_instance
  torsor := ModObj.isIso_torsorMap_toUnit G

/-- The projection of a global principal bundle is an fpqc cover. -/
lemma isFpqcCover (B : GlobalPrincipalBundle G T) : IsFpqcCover B.p.left :=
  IsFpqcCover.of_fppf B.p.left

/-- Pull back a principal bundle while keeping the group over `S` fixed. -/
noncomputable def pullback (B : GlobalPrincipalBundle G T) (f : T' ⟶ T) :
    GlobalPrincipalBundle G T' where
  P := Limits.pullback B.p f
  p := Limits.pullback.snd B.p f
  action := ModObj.pullbackTorsorAction B.p f B.invariant
  invariant := ModObj.pullbackTorsorAction_invariant B.p f B.invariant
  flat := by
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      ((IsPullback.of_hasPullback B.p f).map (Over.forget S))
      (inferInstance : Flat B.p.left)
  surjective := by
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      ((IsPullback.of_hasPullback B.p f).map (Over.forget S))
      (inferInstance : Surjective B.p.left)
  locallyOfFinitePresentation := by
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      ((IsPullback.of_hasPullback B.p f).map (Over.forget S))
      (inferInstance : LocallyOfFinitePresentation B.p.left)
  smooth := by
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      ((IsPullback.of_hasPullback B.p f).map (Over.forget S))
      (inferInstance : Smooth B.p.left)
  torsor := ModObj.isIso_pullbackTorsorMap B.p f B.invariant

/-- The trivial principal bundle `G ×_S T ⟶ T`, obtained by pulling the
universal regular torsor back from the terminal `S`-scheme. -/
noncomputable def trivial (G : Over S) [GrpObj G] [Smooth G.hom]
    [IsAffineHom G.hom] (T : Over S) : GlobalPrincipalBundle G T :=
  (universal G).pullback (toUnit T)

variable (G) (T)

/-- The first projection from the total space of the trivial principal bundle. -/
noncomputable def trivialFst [Smooth G.hom] [IsAffineHom G.hom] :
    (trivial G T).P ⟶ G :=
  Limits.pullback.fst (toUnit G) (toUnit T)

/-- The bundle projection from the total space of the trivial principal bundle. -/
noncomputable def trivialSnd [Smooth G.hom] [IsAffineHom G.hom] :
    (trivial G T).P ⟶ T :=
  Limits.pullback.snd (toUnit G) (toUnit T)

/-- Maps into the total space of a trivial principal bundle are determined by
their group and base coordinates. -/
lemma trivial_hom_ext [Smooth G.hom] [IsAffineHom G.hom] {Q : Over S}
    (f g : Q ⟶ (trivial G T).P)
    (hfst : f ≫ trivialFst G T = g ≫ trivialFst G T)
    (hsnd : f ≫ trivialSnd G T = g ≫ trivialSnd G T) : f = g := by
  apply Limits.pullback.hom_ext
  · exact hfst
  · exact hsnd

/-- The first projection of a trivial torsor intertwines its action with the
regular action on `G`. -/
lemma trivialFst_smul [Smooth G.hom] [IsAffineHom G.hom] :
    γ[G, (trivial G T).P] ≫ trivialFst G T =
      (G ◁ trivialFst G T) ≫ μ[G] := by
  change Limits.pullback.lift
      ((G ◁ Limits.pullback.fst (toUnit G) (toUnit T)) ≫ μ[G])
      ((G ◁ Limits.pullback.snd (toUnit G) (toUnit T)) ≫ snd G T) _ ≫
        Limits.pullback.fst (toUnit G) (toUnit T) = _
  rw [Limits.pullback.lift_fst]
  rfl

/-- The second projection of a trivial torsor is invariant. -/
lemma trivialSnd_invariant [Smooth G.hom] [IsAffineHom G.hom] :
    γ[G, (trivial G T).P] ≫ trivialSnd G T =
      snd G (trivial G T).P ≫ trivialSnd G T := by
  exact (trivial G T).invariant

variable [ModObj G T]

/-- The canonical equivariant map from the trivial torsor to an acted-on object,
`(g,t) ↦ g • t`. -/
noncomputable def trivialActionMap [Smooth G.hom] [IsAffineHom G.hom] :
    (trivial G T).P ⟶ T :=
  trivialFst G T • trivialSnd G T

/-- The canonical map `(g,t) ↦ g • t` from the trivial torsor is equivariant. -/
lemma trivialActionMap_equivariant [Smooth G.hom] [IsAffineHom G.hom] :
    IsModHom G (trivialActionMap G T) := by
  constructor
  change γ[G, (trivial G T).P] ≫
      (trivialFst G T • trivialSnd G T) = _
  rw [ModObj.comp_smul]
  rw [trivialFst_smul, trivialSnd_invariant]
  have hwhisk : G ◁ (trivialFst G T • trivialSnd G T) =
      lift (fst G (trivial G T).P)
        (snd G (trivial G T).P ≫
          (trivialFst G T • trivialSnd G T)) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · simp
  dsimp only [trivialActionMap]
  change _ = (G ◁ (trivialFst G T • trivialSnd G T)) ≫ γ[G, T]
  rw [hwhisk]
  change (((G ◁ trivialFst G T) ≫ μ[G]) •
      (snd G (trivial G T).P ≫ trivialSnd G T)) =
    (fst G (trivial G T).P) •
      (snd G (trivial G T).P ≫
        (trivialFst G T • trivialSnd G T))
  rw [ModObj.comp_smul]
  rw [← mul_smul]
  congr 1

end GlobalPrincipalBundle

namespace GlobalPrincipalBundle

variable {G T U : Over S} [GrpObj G]

/-- In a cartesian category, whiskering a map into a group object on the left
and then multiplying is pointwise multiplication by the first coordinate. -/
lemma whiskerLeft_mul {P : Over S} (q : P ⟶ G) :
    (G ◁ q) ≫ μ[G] =
      fst G P * (snd G P ≫ q) := by
  change (G ◁ q) ≫ μ[G] =
    lift (fst G P) (snd G P ≫ q) ≫ μ[G]
  congr 1

/-! ### Translations of a trivial torsor -/

/-- The unit section of the trivial torsor. -/
noncomputable def trivialSection [Smooth G.hom] [IsAffineHom G.hom] :
    T ⟶ (trivial G T).P :=
  pullback.lift (toUnit T ≫ η[G]) (𝟙 T) (by apply toUnit_unique)

@[reassoc (attr := simp)]
lemma trivialSection_fst [Smooth G.hom] [IsAffineHom G.hom] :
    trivialSection (G := G) (T := T) ≫ trivialFst G T =
      toUnit T ≫ η[G] :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma trivialSection_snd [Smooth G.hom] [IsAffineHom G.hom] :
    trivialSection (G := G) (T := T) ≫ trivialSnd G T = 𝟙 T :=
  pullback.lift_snd _ _ _

/-- Right translation of the trivial torsor by a section `m : T → G`. -/
noncomputable def trivialRightTranslate [Smooth G.hom] [IsAffineHom G.hom]
    (m : T ⟶ G) : (trivial G T).P ⟶ (trivial G T).P :=
  pullback.lift
    (trivialFst G T * (trivialSnd G T ≫ m))
    (trivialSnd G T)
    (by apply toUnit_unique)

@[reassoc (attr := simp)]
lemma trivialRightTranslate_fst [Smooth G.hom] [IsAffineHom G.hom]
    (m : T ⟶ G) :
    trivialRightTranslate (G := G) m ≫ trivialFst G T =
      trivialFst G T * (trivialSnd G T ≫ m) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma trivialRightTranslate_snd [Smooth G.hom] [IsAffineHom G.hom]
    (m : T ⟶ G) :
    trivialRightTranslate (G := G) m ≫ trivialSnd G T = trivialSnd G T :=
  pullback.lift_snd _ _ _

lemma trivialRightTranslate_comp [Smooth G.hom] [IsAffineHom G.hom]
    (m n : T ⟶ G) :
    trivialRightTranslate (G := G) m ≫ trivialRightTranslate (G := G) n =
      trivialRightTranslate (G := G) (m * n) := by
  apply pullback.hom_ext
  · change (trivialRightTranslate (G := G) m ≫ trivialRightTranslate (G := G) n) ≫
      trivialFst G T = trivialRightTranslate (G := G) (m * n) ≫ trivialFst G T
    rw [Category.assoc, trivialRightTranslate_fst]
    rw [MonObj.comp_mul]
    simp only [trivialRightTranslate_fst, trivialRightTranslate_snd_assoc]
    rw [MonObj.comp_mul]
    exact mul_assoc _ _ _
  · change (trivialRightTranslate (G := G) m ≫ trivialRightTranslate (G := G) n) ≫
      trivialSnd G T = trivialRightTranslate (G := G) (m * n) ≫ trivialSnd G T
    rw [Category.assoc, trivialRightTranslate_snd, trivialRightTranslate_snd,
      trivialRightTranslate_snd]

lemma trivialRightTranslate_one [Smooth G.hom] [IsAffineHom G.hom] :
    trivialRightTranslate (G := G) (1 : T ⟶ G) = 𝟙 _ := by
  apply pullback.hom_ext
  · change trivialRightTranslate (G := G) (1 : T ⟶ G) ≫ trivialFst G T =
      𝟙 _ ≫ trivialFst G T
    rw [trivialRightTranslate_fst]
    simp
  · change trivialRightTranslate (G := G) (1 : T ⟶ G) ≫ trivialSnd G T =
      𝟙 _ ≫ trivialSnd G T
    rw [trivialRightTranslate_snd]
    simp

/-- Right translations of a trivial torsor are isomorphisms. -/
noncomputable instance (m : T ⟶ G) [Smooth G.hom] [IsAffineHom G.hom] :
    IsIso (trivialRightTranslate (G := G) m) := by
  refine ⟨⟨trivialRightTranslate (G := G) m⁻¹, ?_, ?_⟩⟩
  · rw [trivialRightTranslate_comp, mul_inv_cancel, trivialRightTranslate_one]
  · rw [trivialRightTranslate_comp, inv_mul_cancel, trivialRightTranslate_one]

/-- Right translation on a trivial torsor commutes with the left `G`-action. -/
lemma trivialRightTranslate_equivariant [Smooth G.hom] [IsAffineHom G.hom]
    (m : T ⟶ G) : IsModHom G (trivialRightTranslate (G := G) m) := by
  constructor
  apply pullback.hom_ext
  · change (γ[G, (trivial G T).P] ≫ trivialRightTranslate (G := G) m) ≫
      trivialFst G T = ((G ◁ trivialRightTranslate (G := G) m) ≫
        γ[G, (trivial G T).P]) ≫ trivialFst G T
    rw [Category.assoc, trivialRightTranslate_fst]
    rw [MonObj.comp_mul, trivialFst_smul]
    rw [← Category.assoc, trivialSnd_invariant, Category.assoc]
    rw [Category.assoc, trivialFst_smul]
    have hwhisk :
        (G ◁ trivialRightTranslate (G := G) m) ≫ (G ◁ trivialFst G T) =
          G ◁ (trivialRightTranslate (G := G) m ≫ trivialFst G T) :=
      (MonoidalLeftAction.actionHomRight_comp G
        (trivialRightTranslate (G := G) m) (trivialFst G T)).symm
    slice_rhs 1 2 => exact hwhisk
    rw [trivialRightTranslate_fst]
    rw [whiskerLeft_mul, whiskerLeft_mul]
    rw [MonObj.comp_mul]
    change ((fst G (trivial G T).P *
        (snd G (trivial G T).P ≫ trivialFst G T)) *
          (snd G (trivial G T).P ≫ trivialSnd G T ≫ m)) =
      fst G (trivial G T).P *
        ((snd G (trivial G T).P ≫ trivialFst G T) *
          (snd G (trivial G T).P ≫ trivialSnd G T ≫ m))
    exact mul_assoc _ _ _
  · change (γ[G, (trivial G T).P] ≫ trivialRightTranslate (G := G) m) ≫
      trivialSnd G T = ((G ◁ trivialRightTranslate (G := G) m) ≫
        γ[G, (trivial G T).P]) ≫ trivialSnd G T
    simp only [Category.assoc, trivialRightTranslate_snd]
    rw [trivialSnd_invariant]
    simp

/-- Distinct group-valued sections induce distinct right translations of a
trivial torsor. -/
lemma trivialRightTranslate_injective [Smooth G.hom] [IsAffineHom G.hom] :
    Function.Injective (trivialRightTranslate (G := G) (T := T)) := by
  intro m n hmn
  have h := congrArg (fun q ↦
      trivialSection (G := G) (T := T) ≫ q ≫ trivialFst G T) hmn
  have h' : (1 : T ⟶ G) * m = (1 : T ⟶ G) * n := by
    change (toUnit T ≫ η[G]) * m = (toUnit T ≫ η[G]) * n
    simpa only [Category.assoc, trivialRightTranslate_fst,
      MonObj.comp_mul, trivialSection_fst,
      trivialSection_snd_assoc, MonObj.comp_one,
      Category.id_comp] using h
  simpa using h'

variable [ModObj G U]

/-- The `G`-equivariant map from the trivial torsor over `T` associated to a
map `u : T → U`, given by `(g,t) ↦ g • u(t)`. -/
noncomputable def trivialActionMapTo [Smooth G.hom] [IsAffineHom G.hom]
    (u : T ⟶ U) : (trivial G T).P ⟶ U :=
  trivialFst G T • (trivialSnd G T ≫ u)

lemma trivialActionMapTo_equivariant [Smooth G.hom] [IsAffineHom G.hom]
    (u : T ⟶ U) : IsModHom G (trivialActionMapTo (G := G) u) := by
  constructor
  change γ[G, (trivial G T).P] ≫
      (trivialFst G T • (trivialSnd G T ≫ u)) = _
  rw [ModObj.comp_smul]
  rw [trivialFst_smul]
  rw [← Category.assoc, trivialSnd_invariant, Category.assoc]
  have hwhisk : G ◁ (trivialFst G T • (trivialSnd G T ≫ u)) =
      lift (fst G (trivial G T).P)
        (snd G (trivial G T).P ≫
          (trivialFst G T • (trivialSnd G T ≫ u))) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  change _ = (G ◁ (trivialFst G T • (trivialSnd G T ≫ u))) ≫ γ[G, U]
  rw [hwhisk]
  change (((G ◁ trivialFst G T) ≫ μ[G]) •
      (snd G (trivial G T).P ≫ trivialSnd G T ≫ u)) =
    (fst G (trivial G T).P) •
      (snd G (trivial G T).P ≫
        (trivialFst G T • (trivialSnd G T ≫ u)))
  rw [ModObj.comp_smul]
  rw [← mul_smul]
  congr 1

/-- Evaluating the equivariant map associated to a point at the unit section
recovers that point. -/
@[reassoc (attr := simp)]
lemma trivialSection_actionMapTo [Smooth G.hom] [IsAffineHom G.hom]
    (u : T ⟶ U) :
    trivialSection (G := G) (T := T) ≫
      trivialActionMapTo (G := G) u = u := by
  simp only [trivialActionMapTo, ModObj.comp_smul, trivialSection_fst,
    trivialSection_snd_assoc]
  exact one_smul (T ⟶ G) u

/-- Forming the equivariant map from a point commutes with an equivariant map
of acted-on objects. -/
lemma trivialActionMapTo_comp [Smooth G.hom] [IsAffineHom G.hom]
    {V : Over S} [ModObj G V] (u : T ⟶ U) (q : U ⟶ V) [IsModHom G q] :
    trivialActionMapTo (G := G) u ≫ q =
      trivialActionMapTo (G := G) (u ≫ q) := by
  rw [trivialActionMapTo, IsModHom.map_smul]
  simp only [trivialActionMapTo, Category.assoc]

/-- Acting on the unit section gives the identity of the trivial torsor. -/
lemma trivialActionMapTo_trivialSection [Smooth G.hom] [IsAffineHom G.hom] :
    trivialActionMapTo (G := G) (trivialSection (G := G) (T := T)) = 𝟙 _ := by
  apply trivial_hom_ext
  · letI : ModObj G G := ModObj.regular G
    letI : IsModHom G (trivialFst G T) := by
      constructor
      exact trivialFst_smul G T
    rw [trivialActionMapTo_comp, trivialSection_fst]
    simp only [trivialActionMapTo]
    change trivialFst G T * ((trivialSnd G T ≫ toUnit T) ≫ η[G]) = _
    have hto : trivialSnd G T ≫ toUnit T = toUnit ((trivial G T).P) :=
      toUnit_unique _ _
    rw [hto]
    change trivialFst G T * (1 : (trivial G T).P ⟶ G) = trivialFst G T
    exact _root_.mul_one _
  · letI : ModObj G T := ModObj.trivialAction G T
    letI : IsModHom G (trivialSnd G T) := by
      constructor
      change γ[G, (trivial G T).P] ≫ trivialSnd G T =
        (G ◁ trivialSnd G T) ≫ snd G T
      rw [trivialSnd_invariant]
      simp
    rw [trivialActionMapTo_comp, trivialSection_snd]
    simp only [Category.id_comp, trivialActionMapTo, CategoryTheory.Hom.smul_def]
    change lift _ _ ≫ snd G T = _
    simp

/-- An equivariant map out of a trivial torsor is uniquely determined by its
value on the unit section. -/
lemma trivialActionMapTo_section_comp [Smooth G.hom] [IsAffineHom G.hom]
    (q : (trivial G T).P ⟶ U) [IsModHom G q] :
    trivialActionMapTo (G := G)
      (trivialSection (G := G) (T := T) ≫ q) = q := by
  rw [← trivialActionMapTo_comp, trivialActionMapTo_trivialSection,
    Category.id_comp]

lemma trivialRightTranslate_actionMap [Smooth G.hom] [IsAffineHom G.hom]
    (m : T ⟶ G) (u : T ⟶ U) :
    trivialRightTranslate (G := G) m ≫ trivialActionMapTo (G := G) u =
      trivialActionMapTo (G := G) (m • u) := by
  simp only [trivialActionMapTo]
  rw [ModObj.comp_smul, trivialRightTranslate_fst]
  rw [← Category.assoc, trivialRightTranslate_snd]
  rw [ModObj.comp_smul]
  rw [mul_smul]

/-- Torsor coordinates: the unique group-valued difference between two maps
into a principal bundle lying over the same base map. -/
noncomputable def torsorDifference (B : GlobalPrincipalBundle G T)
    {Q : Over S} (f g : Q ⟶ B.P) (h : f ≫ B.p = g ≫ B.p) : Q ⟶ G :=
  Limits.pullback.lift f g h ≫ inv (ModObj.torsorMap B.p B.invariant) ≫
    fst G B.P

lemma torsorDifference_smul (B : GlobalPrincipalBundle G T)
    {Q : Over S} (f g : Q ⟶ B.P) (h : f ≫ B.p = g ≫ B.p) :
    torsorDifference B f g h • g = f := by
  let pair : Q ⟶ Limits.pullback B.p B.p := Limits.pullback.lift f g h
  have hinvSnd : inv (ModObj.torsorMap B.p B.invariant) ≫ snd G B.P =
      Limits.pullback.snd B.p B.p := by
    rw [← ModObj.torsorMap_snd B.p B.invariant]
    simp
  have hinvFst : inv (ModObj.torsorMap B.p B.invariant) ≫ γ[G, B.P] =
      Limits.pullback.fst B.p B.p := by
    rw [← ModObj.torsorMap_fst B.p B.invariant]
    simp
  have hsnd : pair ≫ inv (ModObj.torsorMap B.p B.invariant) ≫
      snd G B.P = g := by
    rw [hinvSnd]
    exact Limits.pullback.lift_snd _ _ _
  have hlift : lift (torsorDifference B f g h) g =
      pair ≫ inv (ModObj.torsorMap B.p B.invariant) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [torsorDifference, pair, Category.assoc]
    · simpa only [lift_snd, Category.assoc] using hsnd.symm
  rw [CategoryTheory.Hom.smul_def, hlift]
  rw [Category.assoc, hinvFst]
  exact Limits.pullback.lift_fst _ _ _

/-- Torsor coordinates are characterized by the equation carrying the second
point to the first. -/
lemma torsorDifference_eq (B : GlobalPrincipalBundle G T)
    {Q : Over S} (f g : Q ⟶ B.P) (h : f ≫ B.p = g ≫ B.p)
    (m : Q ⟶ G) (hm : m • g = f) :
    torsorDifference B f g h = m := by
  let pair : Q ⟶ Limits.pullback B.p B.p := Limits.pullback.lift f g h
  change lift m g ≫ γ[G, B.P] = f at hm
  have hpair : lift m g ≫ ModObj.torsorMap B.p B.invariant = pair := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, ModObj.torsorMap_fst]
      simpa [pair] using hm
    · simp [pair]
  simp only [torsorDifference]
  change pair ≫ inv (ModObj.torsorMap B.p B.invariant) ≫ fst G B.P = m
  rw [← hpair, Category.assoc, IsIso.hom_inv_id_assoc]
  simp

/-- The action on a principal bundle is free on morphisms: two group-valued
maps carrying the same point to the same point are equal. -/
lemma smul_left_cancel (B : GlobalPrincipalBundle G T) {Q : Over S}
    (g : Q ⟶ B.P) (m n : Q ⟶ G) (h : m • g = n • g) : m = n := by
  have hlift : lift m g = lift n g := by
    rw [← cancel_mono (ModObj.torsorMap B.p B.invariant)]
    apply Limits.pullback.hom_ext
    · simp only [Category.assoc, ModObj.torsorMap_fst]
      exact h
    · simp
  have hfst := congrArg (fun q ↦ q ≫ fst G B.P) hlift
  simpa using hfst

end GlobalPrincipalBundle

end AlgebraicGeometry.Scheme
