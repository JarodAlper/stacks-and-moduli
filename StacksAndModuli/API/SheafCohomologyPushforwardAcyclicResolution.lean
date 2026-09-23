module

public import StacksAndModuli.API.ExtAdjunction
public import StacksAndModuli.API.SheafCohomologyPushforwardDegreeZero

/-!
# Pushforward cohomology from a flasque resolution

The canonical comparison

`H¹(T, g_* F) ⟶ H¹(S, F)`

does not require pushforward to be exact on every abelian sheaf.  It is enough to
place `F` in a short exact sequence with flasque middle term and to know that
pushforward preserves this one sequence.  This is the form applicable to affine
pushforward on quasicoherent module sheaves.

The proof factors the canonical map through the counit Ext comparison and applies
the four lemma to the two long exact sequences.  We first record the corresponding
naturality of the counit comparison under the weaker, sequencewise exactness
hypothesis.

## Main results

* `CategoryTheory.Adjunction.extAddHomInv_postcomp_extClass_of_map_shortExact`:
  compatibility with a connecting class when the right adjoint preserves the
  specified short exact sequence.
* `TopCat.Sheaf.pushforwardCohomologyMap_one_bijective_of_shortExact`:
  the canonical degree-one pushforward comparison obtained from a flasque short
  exact resolution.
* `AlgebraicGeometry.Scheme.Modules.pushforwardCohomologyMap_one_bijective_of_shortExact`:
  the corresponding statement for a short exact sequence of scheme modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace

universe w vC vD uC uD

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

namespace CategoryTheory.Adjunction

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
variable [Abelian C] [Abelian D] [HasExt.{w} C] [HasExt.{w} D]
variable {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
variable [L.Additive] [R.Additive]
variable [PreservesFiniteLimits L] [PreservesFiniteColimits L]

/-- The counit Ext comparison commutes with a connecting class whenever the
particular short exact sequence, rather than every short exact sequence, is
preserved by the right adjoint. -/
lemma extAddHomInv_postcomp_extClass_of_map_shortExact
    (X : C) {S : ShortComplex D} (hS : S.ShortExact)
    (hRS : (S.map R).ShortExact) (n : ℕ)
    (x : Ext X (R.obj S.X₃) n) :
    adj.extAddHomInv X S.X₁ (n + 1)
        (x.comp hRS.extClass rfl) =
      (adj.extAddHomInv X S.X₃ n x).comp hS.extClass rfl := by
  simp only [extAddHomInv_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_extClass]
  rw [Ext.comp_assoc_of_second_deg_zero]
  let τ : (S.map R).map L ⟶ S :=
    { τ₁ := adj.counit.app S.X₁
      τ₂ := adj.counit.app S.X₂
      τ₃ := adj.counit.app S.X₃
      comm₁₂ := by exact (adj.counit.naturality S.f).symm
      comm₂₃ := by exact (adj.counit.naturality S.g).symm }
  let hRSL : ((S.map R).map L).ShortExact := hRS.map_of_exact L
  have hn := ShortComplex.ShortExact.extClass_naturality hRSL hS τ
  calc
    ((x.mapExactFunctor L).comp hRSL.extClass rfl).comp
          (Ext.mk₀ (adj.counit.app S.X₁)) (add_zero (n + 1)) =
      (x.mapExactFunctor L).comp
        (hRSL.extClass.comp
          (Ext.mk₀ (adj.counit.app S.X₁)) (add_zero 1)) rfl :=
      Ext.comp_assoc_of_third_deg_zero _ _ _ _
    _ = (x.mapExactFunctor L).comp
        ((Ext.mk₀ (adj.counit.app S.X₃)).comp hS.extClass
          (zero_add 1)) rfl :=
      congrArg (fun q ↦ (x.mapExactFunctor L).comp q rfl) hn

end CategoryTheory.Adjunction

namespace TopCat.Sheaf

variable {S T : TopCat.{w}} (g : S ⟶ T)

/-- The canonical pushforward comparison factored through the counit Ext
comparison, before identifying it with `pushforwardCohomologyMap`. -/
noncomputable def pushforwardCohomologyMapAdjunction
    (F : Sheaf AddCommGrpCat.{w} S) (n : ℕ) :
    CategoryTheory.Sheaf.H ((pushforward AddCommGrpCat.{w} g).obj F) n →+
      CategoryTheory.Sheaf.H F n := by
  let L := pullback AddCommGrpCat.{w} g
  let R := pushforward AddCommGrpCat.{w} g
  let adj := pullbackPushforwardAdjunction AddCommGrpCat.{w} g
  let c := (pullbackConstantAddCommGrpIso g).app
    (AddCommGrpCat.of (ULift ℤ))
  let Cℤ := (constantSheaf (Opens.grothendieckTopology T)
    AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ))
  let _ : L.Additive := pullback_additive_addCommGrp g
  let _ : R.Additive := adj.right_adjoint_additive
  let _ : PreservesFiniteLimits L :=
    pullback_preservesFiniteLimits_addCommGrp g
  exact ((Ext.mk₀ c.inv).precomp F (zero_add n)).comp
    (adj.extAddHomInv Cℤ F n)

/-- The adjunction factorization is the repository's canonical pushforward
cohomology map. -/
lemma pushforwardCohomologyMapAdjunction_apply
    (F : Sheaf AddCommGrpCat.{w} S) (n : ℕ)
    (x : CategoryTheory.Sheaf.H
      ((pushforward AddCommGrpCat.{w} g).obj F) n) :
    pushforwardCohomologyMapAdjunction g F n x =
      pushforwardCohomologyMap g F n x := by
  let L := pullback AddCommGrpCat.{w} g
  let R := pushforward AddCommGrpCat.{w} g
  let adj := pullbackPushforwardAdjunction AddCommGrpCat.{w} g
  let c := (pullbackConstantAddCommGrpIso g).app
    (AddCommGrpCat.of (ULift ℤ))
  let ε := adj.counit.app F
  let _ : L.Additive := pullback_additive_addCommGrp g
  let _ : R.Additive := adj.right_adjoint_additive
  let _ : PreservesFiniteLimits L :=
    pullback_preservesFiniteLimits_addCommGrp g
  change (Ext.mk₀ c.inv).comp
      ((x.mapExactFunctor L).comp (Ext.mk₀ ε) (add_zero n)) (zero_add n) =
    ((Ext.mk₀ c.inv).comp (x.mapExactFunctor L) (zero_add n)).comp
      (Ext.mk₀ ε) (add_zero n)
  exact (Ext.comp_assoc (Ext.mk₀ c.inv) (x.mapExactFunctor L)
    (Ext.mk₀ ε) (zero_add n) (add_zero n) (by omega)).symm

/-- The adjunction factorization of the pushforward cohomology map is natural
in the coefficient sheaf. -/
lemma pushforwardCohomologyMapAdjunction_naturality
    {F G : Sheaf AddCommGrpCat.{w} S} (f : F ⟶ G) (n : ℕ)
    (x : CategoryTheory.Sheaf.H
      ((pushforward AddCommGrpCat.{w} g).obj F) n) :
    pushforwardCohomologyMapAdjunction g G n
        (CategoryTheory.Sheaf.H.map
          ((pushforward AddCommGrpCat.{w} g).map f) n x) =
      CategoryTheory.Sheaf.H.map f n
        (pushforwardCohomologyMapAdjunction g F n x) := by
  let L := pullback AddCommGrpCat.{w} g
  let R := pushforward AddCommGrpCat.{w} g
  let adj := pullbackPushforwardAdjunction AddCommGrpCat.{w} g
  let c := (pullbackConstantAddCommGrpIso g).app
    (AddCommGrpCat.of (ULift ℤ))
  let Cℤ := (constantSheaf (Opens.grothendieckTopology T)
    AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ))
  let _ : L.Additive := pullback_additive_addCommGrp g
  let _ : R.Additive := adj.right_adjoint_additive
  let _ : PreservesFiniteLimits L :=
    pullback_preservesFiniteLimits_addCommGrp g
  change (Ext.mk₀ c.inv).comp
      (adj.extAddHomInv Cℤ G n
        (x.comp (Ext.mk₀ (R.map f)) (add_zero n))) (zero_add n) =
    ((Ext.mk₀ c.inv).comp (adj.extAddHomInv Cℤ F n x)
      (zero_add n)).comp (Ext.mk₀ f) (add_zero n)
  rw [adj.extAddHomInv_postcomp_mk₀]
  exact (Ext.comp_assoc (Ext.mk₀ c.inv)
    (adj.extAddHomInv Cℤ F n x) (Ext.mk₀ f)
    (zero_add n) (add_zero n) (by omega)).symm

/-- The adjunction factorization intertwines the connecting maps of a short
exact sequence and its pushforward. -/
lemma pushforwardCohomologyMapAdjunction_delta
    {Q : ShortComplex (Sheaf AddCommGrpCat.{w} S)}
    (hQ : Q.ShortExact)
    (hRQ : (Q.map (pushforward AddCommGrpCat.{w} g)).ShortExact)
    (x : CategoryTheory.Sheaf.H
      ((pushforward AddCommGrpCat.{w} g).obj Q.X₃) 0) :
    pushforwardCohomologyMapAdjunction g Q.X₁ 1
        (x.comp hRQ.extClass rfl) =
      (pushforwardCohomologyMapAdjunction g Q.X₃ 0 x).comp
        hQ.extClass rfl := by
  let L := pullback AddCommGrpCat.{w} g
  let R := pushforward AddCommGrpCat.{w} g
  let adj := pullbackPushforwardAdjunction AddCommGrpCat.{w} g
  let c := (pullbackConstantAddCommGrpIso g).app
    (AddCommGrpCat.of (ULift ℤ))
  let Cℤ := (constantSheaf (Opens.grothendieckTopology T)
    AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ))
  let _ : L.Additive := pullback_additive_addCommGrp g
  let _ : R.Additive := adj.right_adjoint_additive
  let _ : PreservesFiniteLimits L :=
    pullback_preservesFiniteLimits_addCommGrp g
  change (Ext.mk₀ c.inv).comp
      (adj.extAddHomInv Cℤ Q.X₁ 1
        (x.comp hRQ.extClass rfl)) (zero_add 1) =
    ((Ext.mk₀ c.inv).comp (adj.extAddHomInv Cℤ Q.X₃ 0 x)
      (zero_add 0)).comp hQ.extClass rfl
  rw [adj.extAddHomInv_postcomp_extClass_of_map_shortExact Cℤ hQ hRQ]
  exact (Ext.comp_assoc (Ext.mk₀ c.inv)
    (adj.extAddHomInv Cℤ Q.X₃ 0 x) hQ.extClass
    (zero_add 0) rfl (by omega)).symm

/-- A flasque middle term in a short exact resolution suffices for the
degree-one canonical pushforward comparison, provided pushforward preserves
that particular short exact sequence. -/
theorem pushforwardCohomologyMap_one_bijective_of_shortExact
    {Q : ShortComplex (Sheaf AddCommGrpCat.{w} S)}
    (hQ : Q.ShortExact)
    (hRQ : (Q.map (pushforward AddCommGrpCat.{w} g)).ShortExact)
    [Q.X₂.IsFlasque] :
    Function.Bijective (pushforwardCohomologyMap g Q.X₁ 1) := by
  let R := pushforward AddCommGrpCat.{w} g
  let CℤT := (constantSheaf (Opens.grothendieckTopology T)
    AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ))
  let CℤS := (constantSheaf (Opens.grothendieckTopology S)
    AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ))
  let _ : (R.obj Q.X₂).IsFlasque := by infer_instance
  let _ : Subsingleton (CategoryTheory.Sheaf.H Q.X₂ 1) :=
    subsingleton_H_of_isFlasque 0 Q.X₂
  let _ : Subsingleton (CategoryTheory.Sheaf.H (R.obj Q.X₂) 1) :=
    subsingleton_H_of_isFlasque 0 (R.obj Q.X₂)
  let _ : Subsingleton (Ext CℤT (Q.map R).X₂ (0 + 1)) := by
    change Subsingleton (CategoryTheory.Sheaf.H (R.obj Q.X₂) 1)
    infer_instance
  let _ : Subsingleton (Ext CℤS Q.X₂ (0 + 1)) := by
    change Subsingleton (CategoryTheory.Sheaf.H Q.X₂ 1)
    infer_instance
  have hcmp₂ : Function.Bijective
      (pushforwardCohomologyMapAdjunction g Q.X₂ 0) := by
    rw [funext (pushforwardCohomologyMapAdjunction_apply g Q.X₂ 0)]
    exact pushforwardCohomologyMap_zero_bijective g Q.X₂
  have hcmp₃ : Function.Bijective
      (pushforwardCohomologyMapAdjunction g Q.X₃ 0) := by
    rw [funext (pushforwardCohomologyMapAdjunction_apply g Q.X₃ 0)]
    exact pushforwardCohomologyMap_zero_bijective g Q.X₃
  have hcmp₁ : Function.Bijective
      (pushforwardCohomologyMapAdjunction g Q.X₁ 1) :=
    AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact
      (CategoryTheory.Sheaf.H.map (R.map Q.g) 0)
      (hRQ.extClass.postcomp CℤT rfl)
      (CategoryTheory.Sheaf.H.map Q.g 0)
      (hQ.extClass.postcomp CℤS rfl)
      (pushforwardCohomologyMapAdjunction g Q.X₂ 0)
      (pushforwardCohomologyMapAdjunction g Q.X₃ 0)
      (pushforwardCohomologyMapAdjunction g Q.X₁ 1)
      (by
        ext x
        exact (pushforwardCohomologyMapAdjunction_naturality
          g Q.g 0 x).symm)
      (by
        ext x
        exact (pushforwardCohomologyMapAdjunction_delta
          g hQ hRQ x).symm)
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' CℤT hRQ 0 1 rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' CℤS hQ 0 1 rfl))
      hcmp₂.surjective hcmp₃
      (fun x₁ ↦ Ext.covariant_sequence_exact₁ CℤT hRQ x₁
        (by subsingleton) rfl)
      (fun x₁ ↦ Ext.covariant_sequence_exact₁ CℤS hQ x₁
        (by subsingleton) rfl)
  rw [← funext (pushforwardCohomologyMapAdjunction_apply g Q.X₁ 1)]
  exact hcmp₁

end TopCat.Sheaf

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{w}} (f : X ⟶ Y)

/-- The module-sheaf form of the flasque-resolution comparison: if a short exact
sequence of modules remains short exact after pushforward and its middle term is
flasque as an abelian sheaf, then the canonical degree-one pushforward cohomology
map for its left term is bijective. -/
theorem pushforwardCohomologyMap_one_bijective_of_shortExact
    {Q : ShortComplex X.Modules} (hQ : Q.ShortExact)
    (hRQ : (Q.map (pushforward f)).ShortExact)
    [TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj Q.X₂)] :
    Function.Bijective (pushforwardCohomologyMap f Q.X₁ 1) := by
  let _ : (SheafOfModules.toSheaf X.ringCatSheaf).Additive := by
    infer_instance
  let _ : (TopCat.Sheaf.pushforward AddCommGrpCat.{w} f.base).Additive :=
    (TopCat.Sheaf.pullbackPushforwardAdjunction
      AddCommGrpCat.{w} f.base).right_adjoint_additive
  let Q' := Q.map (SheafOfModules.toSheaf X.ringCatSheaf)
  have hQ' : Q'.ShortExact := by
    dsimp [Q']
    exact shortExact_map_toSheaf hQ
  have hRQ' :
      (Q'.map (TopCat.Sheaf.pushforward AddCommGrpCat.{w} f.base)).ShortExact := by
    have h := shortExact_map_toSheaf hRQ
    change (Q'.map
      (TopCat.Sheaf.pushforward AddCommGrpCat.{w} f.base)).ShortExact at h
    exact h
  let _ : TopCat.Sheaf.IsFlasque Q'.X₂ := by
    change TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj Q.X₂)
    infer_instance
  have h := TopCat.Sheaf.pushforwardCohomologyMap_one_bijective_of_shortExact
    f.base hQ' hRQ'
  change Function.Bijective
    (TopCat.Sheaf.pushforwardCohomologyMap f.base
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj Q.X₁) 1)
  change Function.Bijective
    (TopCat.Sheaf.pushforwardCohomologyMap f.base
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj Q.X₁) 1) at h
  exact h

end AlgebraicGeometry.Scheme.Modules
