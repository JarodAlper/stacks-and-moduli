module

public import StacksAndModuli.API.PrincipalBundleInduction

/-!
# The unit of principal-bundle induction

This file proves equivariance of the canonical map from a principal
`H`-bundle to its extension of structure group along a homomorphism
`H ⟶ G`.  The proof compares the two pullbacks of the canonical chart to
`H ⊗ P`; the torsor-coordinate cocycle identifies their transition gauges.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
  CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
  CategoryTheory.MonObj
open scoped CategoryTheory.Obj CategoryTheory.ModObj

universe u

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.Scheme.PrincipalBundleInduction

variable {S : Scheme.{u}} {H G T : Over S} [GrpObj H] [GrpObj G]
  (phi : H ⟶ G) [IsMonHom phi]
  (B : GlobalPrincipalBundle H T)

/-! ### The two action charts -/

/-- The pullback of the bundle cover along the projection `H ⊗ P ⟶ P`. -/
noncomputable abbrev unitActionCoverObj : (coverSieve B).arrows.category :=
  (coverSieve B).arrows.categoryMk (snd H B.P ≫ B.p)
    ⟨snd H B.P, rfl⟩

/-- The projection from the action chart to the original bundle. -/
noncomputable abbrev unitActionProjection :
    (unitActionCoverObj B).obj.left ⟶ B.P :=
  snd H B.P

/-- The action map from the action chart to the original bundle. -/
noncomputable abbrev unitActionMap :
    (unitActionCoverObj B).obj.left ⟶ B.P :=
  γ[H, B.P]

/-- The projection `H ⊗ P ⟶ P` defines a map from the action chart to the
canonical chart over `P`. -/
noncomputable abbrev unitActionCoverSnd :
    unitActionCoverObj B ⟶ selfCoverObj B :=
  ObjectProperty.homMk (Over.homMk (unitActionProjection B) rfl)

/-- The action `H ⊗ P ⟶ P` defines the second map from the action chart to
the canonical chart over `P`. -/
noncomputable abbrev unitActionCoverAction :
    unitActionCoverObj B ⟶ selfCoverObj B :=
  ObjectProperty.homMk (Over.homMk (unitActionMap B) B.invariant)

/-- The universal group coordinate on the action chart. -/
noncomputable abbrev unitActionCoordinate :
    (unitActionCoverObj B).obj.left ⟶ H :=
  fst H B.P

@[simp]
lemma unitActionCoverSnd_left :
    (unitActionCoverSnd B).hom.left = unitActionProjection B :=
  rfl

@[simp]
lemma unitActionCoverAction_left :
    (unitActionCoverAction B).hom.left = unitActionMap B :=
  rfl

/-- Every chosen local section defines a morphism from its chart to the
canonical chart over the total space of the bundle. -/
noncomputable abbrev unitSectionHom
    (q : (coverSieve B).arrows.category) : q ⟶ selfCoverObj B :=
  ObjectProperty.homMk
    (Over.homMk (localSection B q) (localSection_fac B q))

@[simp]
lemma unitSectionHom_left (q : (coverSieve B).arrows.category) :
    (unitSectionHom B q).hom.left = localSection B q :=
  rfl

/-! ### The torsor-coordinate identity -/

/-- The two transition gauges from the action chart to the canonical chart
give the same canonical point after accounting for the universal `H`-action.
This is the raw `H`-valued identity before applying `H ⟶ G`. -/
lemma unitGauge_transition_raw :
    let s := localSection B (selfCoverObj B)
    let t := localSection B (unitActionCoverObj B)
    let d₀ := B.torsorDifference s (CategoryStruct.id B.P) (by
      dsimp only [s]
      exact (localSection_fac B (selfCoverObj B)).trans
        (Category.id_comp B.p).symm)
    let a := unitActionMap B
    let p := unitActionProjection B
    let h := unitActionCoordinate B
    let dA := B.torsorDifference t (a ≫ s)
      (localSection_transition_eq B (unitActionCoverAction B))
    let dS := B.torsorDifference t (p ≫ s)
      (localSection_transition_eq B (unitActionCoverSnd B))
    (a ≫ d₀)⁻¹ * dA⁻¹ =
      (h * (p ≫ d₀)⁻¹) * dS⁻¹ := by
  dsimp only
  let s := localSection B (selfCoverObj B)
  let t := localSection B (unitActionCoverObj B)
  let a : (unitActionCoverObj B).obj.left ⟶ B.P :=
    unitActionMap B
  let p : (unitActionCoverObj B).obj.left ⟶ B.P :=
    unitActionProjection B
  let h : (unitActionCoverObj B).obj.left ⟶ H :=
    unitActionCoordinate B
  have hs : s ≫ B.p = (CategoryStruct.id B.P) ≫ B.p := by
    dsimp only [s]
    simpa only [Over.mk_hom, Category.id_comp] using
      localSection_fac B (selfCoverObj B)
  have htaS : t ≫ B.p = (a ≫ s) ≫ B.p := by
    dsimp only [t, a]
    exact localSection_transition_eq B (unitActionCoverAction B)
  have htpS : t ≫ B.p = (p ≫ s) ≫ B.p := by
    dsimp only [t, p]
    exact localSection_transition_eq B (unitActionCoverSnd B)
  have hta : t ≫ B.p = a ≫ B.p := by
    calc
      t ≫ B.p = (a ≫ s) ≫ B.p := htaS
      _ = a ≫ (s ≫ B.p) := Category.assoc _ _ _
      _ = a ≫ ((CategoryStruct.id B.P) ≫ B.p) :=
        congrArg (fun q ↦ a ≫ q) hs
      _ = a ≫ B.p := by rw [Category.id_comp]
  have htp : t ≫ B.p = p ≫ B.p := by
    calc
      t ≫ B.p = (p ≫ s) ≫ B.p := htpS
      _ = p ≫ (s ≫ B.p) := Category.assoc _ _ _
      _ = p ≫ ((CategoryStruct.id B.P) ≫ B.p) :=
        congrArg (fun q ↦ p ≫ q) hs
      _ = p ≫ B.p := by rw [Category.id_comp]
  let d₀ := B.torsorDifference s (CategoryStruct.id B.P) hs
  let dA := B.torsorDifference t (a ≫ s) htaS
  let dS := B.torsorDifference t (p ≫ s) htpS
  let rA := B.torsorDifference t a hta
  let rS := B.torsorDifference t p htp
  have hdA : dA * (a ≫ d₀) = rA := by
    have hpre := B.torsorDifference_precomp a s
      (CategoryStruct.id B.P) hs
    have hmul := B.torsorDifference_mul t (a ≫ s) a
      htaS
      (by simpa only [Category.assoc, Category.comp_id, Category.id_comp] using
        congrArg (fun q ↦ a ≫ q) hs)
    dsimp only [dA, d₀, rA]
    rw [← hpre]
    simpa only [Category.comp_id] using hmul
  have hdS : dS * (p ≫ d₀) = rS := by
    have hpre := B.torsorDifference_precomp p s
      (CategoryStruct.id B.P) hs
    have hmul := B.torsorDifference_mul t (p ≫ s) p
      htpS
      (by simpa only [Category.assoc, Category.comp_id, Category.id_comp] using
        congrArg (fun q ↦ p ≫ q) hs)
    dsimp only [dS, d₀, rS]
    rw [← hpre]
    simpa only [Category.comp_id] using hmul
  have hr : rA * h = rS := by
    symm
    apply B.torsorDifference_eq
    calc
      (rA * h) • p = rA • (h • p) := mul_smul rA h p
      _ = rA • a := by
        congr 1
        dsimp only [h, p, a, unitActionCoordinate, unitActionProjection,
          unitActionMap]
        rw [CategoryTheory.Hom.smul_def, lift_fst_snd, Category.id_comp]
      _ = t := B.torsorDifference_smul t a hta
  have hri : h⁻¹ * rA⁻¹ = rS⁻¹ := by
    simpa only [_root_.mul_inv_rev] using congrArg (fun q ↦ q⁻¹) hr
  change (a ≫ d₀)⁻¹ * dA⁻¹ =
    (h * (p ≫ d₀)⁻¹) * dS⁻¹
  calc
    (a ≫ d₀)⁻¹ * dA⁻¹ =
        (dA * (a ≫ d₀))⁻¹ := (_root_.mul_inv_rev _ _).symm
    _ = rA⁻¹ := congrArg (fun q ↦ q⁻¹) hdA
    _ = h * rS⁻¹ := by
      calc
        rA⁻¹ = 1 * rA⁻¹ := (_root_.one_mul _).symm
        _ = (h * h⁻¹) * rA⁻¹ := by rw [mul_inv_cancel]
        _ = h * (h⁻¹ * rA⁻¹) := _root_.mul_assoc _ _ _
        _ = h * rS⁻¹ := congrArg (fun q ↦ h * q) hri
    _ = h * ((dS * (p ≫ d₀))⁻¹) := by rw [hdS]
    _ = h * ((p ≫ d₀)⁻¹ * dS⁻¹) := by
      rw [_root_.mul_inv_rev]
    _ = (h * (p ≫ d₀)⁻¹) * dS⁻¹ :=
      (_root_.mul_assoc _ _ _).symm

/-- Applying the structure-group homomorphism to the torsor-coordinate
identity gives the corresponding identity between local induction gauges. -/
lemma unitGauge_transition :
    (unitActionMap B ≫ unitGauge phi B) *
        (transitionGauge phi B (unitActionCoverAction B))⁻¹ =
      ((unitActionCoordinate B ≫ phi) *
          (unitActionProjection B ≫ unitGauge phi B)) *
        (transitionGauge phi B (unitActionCoverSnd B))⁻¹ := by
  have h := congrArg (fun q ↦ q ≫ phi) (unitGauge_transition_raw B)
  simpa only [unitGauge, transitionGauge, MonObj.mul_comp, GrpObj.inv_comp,
    GrpObj.comp_inv, Category.assoc, unitActionCoverAction_left,
    unitActionCoverSnd_left] using h

/-- Along a chosen local section, the transition to the canonical chart is
the pullback of the unit gauge. -/
lemma transitionGauge_unitSectionHom
    (q : (coverSieve B).arrows.category) :
    transitionGauge phi B (unitSectionHom B q) =
      localSection B q ≫ unitGauge phi B := by
  let s := localSection B q
  let s₀ := localSection B (selfCoverObj B)
  have hs₀ : s₀ ≫ B.p = (CategoryStruct.id B.P) ≫ B.p := by
    dsimp only [s₀]
    exact (localSection_fac B (selfCoverObj B)).trans
      (Category.id_comp B.p).symm
  let d₀ := B.torsorDifference s₀ (CategoryStruct.id B.P) hs₀
  let d := B.torsorDifference s (s ≫ s₀)
    (localSection_transition_eq B (unitSectionHom B q))
  have hpre := B.torsorDifference_precomp s s₀
    (CategoryStruct.id B.P) hs₀
  have hmul := B.torsorDifference_mul s (s ≫ s₀) s
    (localSection_transition_eq B (unitSectionHom B q))
    (by simpa only [Category.assoc, Category.comp_id, Category.id_comp] using
      congrArg (fun z ↦ s ≫ z) hs₀)
  have hd : d = (s ≫ d₀)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    dsimp only [d, d₀]
    rw [← hpre]
    simpa only [Category.comp_id, GlobalPrincipalBundle.torsorDifference_self]
      using hmul
  change d ≫ phi = s ≫ (d₀ ≫ phi)⁻¹
  rw [hd, GrpObj.inv_comp]
  exact (GrpObj.comp_inv s (d₀ ≫ phi)).symm

variable [Smooth G.hom] [IsAffineHom G.hom]

/-- The point with identity group coordinate is the unit section of a
trivial principal bundle. -/
lemma trivialPoint_one_eq_trivialSection {Z : Over S} :
    GlobalPrincipalBundle.trivialPoint (G := G) (1 : Z ⟶ G) =
      GlobalPrincipalBundle.trivialSection (G := G) (T := Z) := by
  apply GlobalPrincipalBundle.trivial_hom_ext
  · simp [CategoryTheory.Hom.one_def]
  · simp

/-- A point whose coordinate has been corrected by the inverse transition
gauge maps to the prescribed point in the canonical chart. -/
lemma transitionAdjustedPoint_comp_localHom
    {q : (coverSieve B).arrows.category}
    (k : q ⟶ selfCoverObj B) (m : q.obj.left ⟶ G) :
    GlobalPrincipalBundle.trivialPoint
        (m * (transitionGauge phi B k)⁻¹) ≫
          (localHom phi B k).total =
      GlobalPrincipalBundle.trivialPoint m ≫
        GlobalPrincipalBundle.trivialBaseMap (G := G) k.hom.left := by
  apply GlobalPrincipalBundle.trivial_hom_ext
  · simp only [localHom_total, Category.assoc,
      GlobalPrincipalBundle.trivialBaseMap_fst,
      GlobalPrincipalBundle.trivialRightTranslate_fst,
      MonObj.comp_mul, GlobalPrincipalBundle.trivialPoint_fst,
      GlobalPrincipalBundle.trivialPoint_snd_assoc, Category.id_comp]
    rw [_root_.mul_assoc, inv_mul_cancel, _root_.mul_one]
  · simp only [localHom_total, Category.assoc,
      GlobalPrincipalBundle.trivialBaseMap_snd,
      GlobalPrincipalBundle.trivialRightTranslate_snd_assoc,
      GlobalPrincipalBundle.trivialPoint_snd_assoc, Category.id_comp]

/-- A point of a trivial bundle commutes with change of its base. -/
lemma trivialPoint_comp_trivialBaseMap {Z : Over S}
    (f : Z ⟶ B.P) (m : B.P ⟶ G) :
    GlobalPrincipalBundle.trivialPoint (f ≫ m) ≫
        GlobalPrincipalBundle.trivialBaseMap (G := G) f =
      f ≫ GlobalPrincipalBundle.trivialPoint m := by
  apply GlobalPrincipalBundle.trivial_hom_ext
  · simp
  · simp [Category.assoc]

/-- Multiplying the group coordinate of a point of a trivial bundle is its
left `G`-action. -/
lemma trivialPoint_mul_comp_trivialBaseMap {Z : Over S}
    (f : Z ⟶ B.P) (h : Z ⟶ G) (m : B.P ⟶ G) :
    GlobalPrincipalBundle.trivialPoint (h * (f ≫ m)) ≫
        GlobalPrincipalBundle.trivialBaseMap (G := G) f =
      h • (f ≫ GlobalPrincipalBundle.trivialPoint m) := by
  apply GlobalPrincipalBundle.trivial_hom_ext
  · letI : ModObj G G := ModObj.regular G
    letI : IsModHom G (GlobalPrincipalBundle.trivialFst G B.P) :=
      ⟨GlobalPrincipalBundle.trivialFst_smul G B.P⟩
    rw [IsModHom.map_smul]
    simp only [Category.assoc,
      GlobalPrincipalBundle.trivialBaseMap_fst,
      GlobalPrincipalBundle.trivialPoint_fst]
    change h * (f ≫ m) = h * (f ≫ m)
    rfl
  · change
      (GlobalPrincipalBundle.trivialPoint (h * (f ≫ m)) ≫
          GlobalPrincipalBundle.trivialBaseMap (G := G) f) ≫
            GlobalPrincipalBundle.trivialSnd G B.P =
        (h • (f ≫ GlobalPrincipalBundle.trivialPoint m)) ≫
          GlobalPrincipalBundle.trivialSnd G B.P
    simp only [Category.assoc, GlobalPrincipalBundle.trivialBaseMap_snd,
      GlobalPrincipalBundle.trivialPoint_snd_assoc, Category.id_comp]
    symm
    change (lift h (f ≫ GlobalPrincipalBundle.trivialPoint m) ≫
      γ[G, (GlobalPrincipalBundle.trivial G B.P).P]) ≫
        GlobalPrincipalBundle.trivialSnd G B.P = f
    rw [Category.assoc,
      GlobalPrincipalBundle.trivialSnd_invariant]
    rw [← Category.assoc, lift_snd, Category.assoc,
      GlobalPrincipalBundle.trivialPoint_snd, Category.comp_id]

/-! ### Equivariance of the unit -/

/-- The canonical map from a principal `H`-bundle to its induced
`G`-bundle intertwines the universal `H`-action with the restricted
`G`-action. -/
lemma unit_action (C : Cocone phi B) :
    unitActionMap B ≫ unit phi B C =
      (unitActionCoordinate B ≫ phi) •
        (unitActionProjection B ≫ unit phi B C) := by
  let q := unitActionCoverObj B
  let q₀ := selfCoverObj B
  let kA : q ⟶ q₀ := unitActionCoverAction B
  let kS : q ⟶ q₀ := unitActionCoverSnd B
  let a : q.obj.left ⟶ B.P := unitActionMap B
  let p : q.obj.left ⟶ B.P := unitActionProjection B
  let h : q.obj.left ⟶ G := unitActionCoordinate B ≫ phi
  let u : B.P ⟶ G := unitGauge phi B
  let mA : q.obj.left ⟶ G := a ≫ u
  let mS : q.obj.left ⟶ G := h * (p ≫ u)
  let zA : q.obj.left ⟶ ((localFunctor phi B).obj q).bundle.P :=
    GlobalPrincipalBundle.trivialPoint
      (mA * (transitionGauge phi B kA)⁻¹)
  let zS : q.obj.left ⟶ ((localFunctor phi B).obj q).bundle.P :=
    GlobalPrincipalBundle.trivialPoint
      (mS * (transitionGauge phi B kS)⁻¹)
  have hz : zA = zS := by
    apply congrArg GlobalPrincipalBundle.trivialPoint
    simpa only [q, kA, kS, a, p, h, u, mA, mS] using
      unitGauge_transition phi B
  have hA : zA ≫ (localHom phi B kA).total =
      a ≫ unitLocal phi B := by
    calc
      zA ≫ (localHom phi B kA).total =
          GlobalPrincipalBundle.trivialPoint mA ≫
            GlobalPrincipalBundle.trivialBaseMap (G := G) kA.hom.left := by
              simpa only [zA] using
                transitionAdjustedPoint_comp_localHom phi B kA mA
      _ = a ≫ GlobalPrincipalBundle.trivialPoint u := by
        simpa only [mA, a, kA, unitActionCoverAction_left] using
          trivialPoint_comp_trivialBaseMap (G := G) B a u
      _ = a ≫ unitLocal phi B := rfl
  have hS : zS ≫ (localHom phi B kS).total =
      h • (p ≫ unitLocal phi B) := by
    calc
      zS ≫ (localHom phi B kS).total =
          GlobalPrincipalBundle.trivialPoint mS ≫
            GlobalPrincipalBundle.trivialBaseMap (G := G) kS.hom.left := by
              simpa only [zS] using
                transitionAdjustedPoint_comp_localHom phi B kS mS
      _ = h • (p ≫ GlobalPrincipalBundle.trivialPoint u) := by
        simpa only [mS, p, h, kS, unitActionCoverSnd_left] using
          trivialPoint_mul_comp_trivialBaseMap (G := G) B p h u
      _ = h • (p ≫ unitLocal phi B) := rfl
  have hnatA : (localHom phi B kA).total ≫ (C.comparison q₀).total =
      (C.comparison q).total := by
    exact congrArg ClassifyingHom.total (C.comparison_naturality kA)
  have hnatS : (localHom phi B kS).total ≫ (C.comparison q₀).total =
      (C.comparison q).total := by
    exact congrArg ClassifyingHom.total (C.comparison_naturality kS)
  letI : IsModHom G (C.comparison q₀).total :=
    (C.comparison q₀).equivariant
  change a ≫ (unitLocal phi B ≫ (C.comparison q₀).total) =
    h • (p ≫ (unitLocal phi B ≫ (C.comparison q₀).total))
  calc
    a ≫ (unitLocal phi B ≫ (C.comparison q₀).total) =
        (zA ≫ (localHom phi B kA).total) ≫
          (C.comparison q₀).total := by
            rw [← Category.assoc, hA]
    _ = zA ≫ (C.comparison q).total := by
      rw [Category.assoc, hnatA]
    _ = zS ≫ (C.comparison q).total := by rw [hz]
    _ = (zS ≫ (localHom phi B kS).total) ≫
        (C.comparison q₀).total := by rw [Category.assoc, hnatS]
    _ = (h • (p ≫ unitLocal phi B)) ≫
        (C.comparison q₀).total := by rw [hS]
    _ = h • ((p ≫ unitLocal phi B) ≫
        (C.comparison q₀).total) :=
      IsModHom.map_smul (C.comparison q₀).total h
        (p ≫ unitLocal phi B)
    _ = h • (p ≫
        (unitLocal phi B ≫ (C.comparison q₀).total)) := by
      rw [Category.assoc]

/-- Pointwise form of equivariance of the induction unit. -/
lemma unit_smul (C : Cocone phi B) {Z : Over S}
    (r : Z ⟶ H) (x : Z ⟶ B.P) :
    (r • x) ≫ unit phi B C =
      (r ≫ phi) • (x ≫ unit phi B C) := by
  have h := congrArg (fun f ↦ lift r x ≫ f) (unit_action phi B C)
  have hr : lift r x ≫ unitActionCoordinate B = r := by
    change lift r x ≫ fst H B.P = r
    exact lift_fst _ _
  have hx : lift r x ≫ unitActionProjection B = x := by
    change lift r x ≫ snd H B.P = x
    exact lift_snd _ _
  rw [ModObj.comp_smul] at h
  have hrphi : lift r x ≫ (unitActionCoordinate B ≫ phi) = r ≫ phi := by
    rw [← Category.assoc, hr]
  have hxunit : lift r x ≫
      (unitActionProjection B ≫ unit phi B C) = x ≫ unit phi B C := by
    rw [← Category.assoc, hx]
  rw [hrphi, hxunit] at h
  change (lift r x ≫ γ[H, B.P]) ≫ unit phi B C = _
  exact (Category.assoc _ _ _).trans (by
    simpa only [unitActionMap] using h)

/-- In every local chart, the chosen section followed by the induction unit
is the unit section followed by the chart comparison. -/
lemma trivialSection_comp_comparison (C : Cocone phi B)
    (q : (coverSieve B).arrows.category) :
    GlobalPrincipalBundle.trivialSection (G := G) (T := q.obj.left) ≫
        (C.comparison q).total =
      localSection B q ≫ unit phi B C := by
  let k : q ⟶ selfCoverObj B := unitSectionHom B q
  let m : q.obj.left ⟶ G := localSection B q ≫ unitGauge phi B
  have hm : transitionGauge phi B k = m := by
    simpa only [k, m] using transitionGauge_unitSectionHom phi B q
  have hpoint : GlobalPrincipalBundle.trivialSection
        (G := G) (T := q.obj.left) ≫ (localHom phi B k).total =
      localSection B q ≫ unitLocal phi B := by
    have hlocal := transitionAdjustedPoint_comp_localHom phi B k m
    have hcoord : m * (transitionGauge phi B k)⁻¹ = 1 := by
      rw [hm, mul_inv_cancel]
    rw [hcoord, trivialPoint_one_eq_trivialSection] at hlocal
    calc
      GlobalPrincipalBundle.trivialSection (G := G) (T := q.obj.left) ≫
          (localHom phi B k).total =
        GlobalPrincipalBundle.trivialPoint m ≫
          GlobalPrincipalBundle.trivialBaseMap (G := G) k.hom.left := hlocal
      _ = localSection B q ≫
          GlobalPrincipalBundle.trivialPoint (unitGauge phi B) := by
        apply GlobalPrincipalBundle.trivial_hom_ext
        · simp only [Category.assoc,
            GlobalPrincipalBundle.trivialBaseMap_fst,
            GlobalPrincipalBundle.trivialPoint_fst, m]
          change localSection B q ≫ unitGauge phi B =
            localSection B q ≫
              (GlobalPrincipalBundle.trivialPoint (unitGauge phi B) ≫
                GlobalPrincipalBundle.trivialFst G B.P)
          rw [GlobalPrincipalBundle.trivialPoint_fst]
        · simp only [Category.assoc,
            GlobalPrincipalBundle.trivialBaseMap_snd,
            GlobalPrincipalBundle.trivialPoint_snd_assoc,
            Category.id_comp, k, unitSectionHom_left]
          change localSection B q =
            localSection B q ≫
              (GlobalPrincipalBundle.trivialPoint (unitGauge phi B) ≫
                GlobalPrincipalBundle.trivialSnd G B.P)
          rw [GlobalPrincipalBundle.trivialPoint_snd, Category.comp_id]
      _ = localSection B q ≫ unitLocal phi B := rfl
  have hnat : (localHom phi B k).total ≫
      (C.comparison (selfCoverObj B)).total = (C.comparison q).total :=
    congrArg ClassifyingHom.total (C.comparison_naturality k)
  calc
    GlobalPrincipalBundle.trivialSection (G := G) (T := q.obj.left) ≫
        (C.comparison q).total =
      GlobalPrincipalBundle.trivialSection (G := G) (T := q.obj.left) ≫
        ((localHom phi B k).total ≫
          (C.comparison (selfCoverObj B)).total) := by rw [hnat]
    _ = (GlobalPrincipalBundle.trivialSection (G := G) (T := q.obj.left) ≫
        (localHom phi B k).total) ≫
          (C.comparison (selfCoverObj B)).total :=
      (Category.assoc _ _ _).symm
    _ = (localSection B q ≫ unitLocal phi B) ≫
        (C.comparison (selfCoverObj B)).total := by rw [hpoint]
    _ = localSection B q ≫ unit phi B C := by
      rw [unit, Category.assoc]


end AlgebraicGeometry.Scheme.PrincipalBundleInduction
