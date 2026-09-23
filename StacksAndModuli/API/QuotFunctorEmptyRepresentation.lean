module

public import StacksAndModuli.«Section2.1-Intro».«part2.1.3-projective-space-and-hilbert-quot-functors»
public import StacksAndModuli.API.AffinePushforwardQuasicoherent
public import StacksAndModuli.API.OpenCoverModuleMorphismZero
public import StacksAndModuli.API.ProjectiveTwistBaseChange

/-!
# Empty representatives for fixed-polynomial Quot functors

This low-dependency module records the generic empty branch of Quot
representability.  It is independent of the projective-zero classification: if a
fixed-polynomial Quot functor has no points on nonempty test schemes, then the
empty scheme represents it and is projective over the base.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme

private lemma Modules.subsingleton_sections_bot_for_emptyQuot
    {X : Scheme.{u}} (N : X.Modules) :
    Subsingleton Γ(N, ⊥) := by
  refine ⟨fun a b ↦ ?_⟩
  apply (Modules.abSheaf N).eq_of_locally_eq' (fun i : PEmpty.{u + 1} ↦ ⊥) ⊥
    (fun _ ↦ homOfLE le_rfl) ?_ a b (fun i ↦ i.elim)
  intro x hx
  exact absurd hx (by simp)

private lemma Modules.isZero_of_isEmpty_for_emptyQuot
    {X : Scheme.{u}} [IsEmpty X] (M : X.Modules) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  apply Modules.hom_ext _ _ fun U ↦ ?_
  have hU : U = ⊥ := Subsingleton.elim _ _
  subst U
  letI : Subsingleton Γ(M, ⊥) :=
    Modules.subsingleton_sections_bot_for_emptyQuot M
  ext x
  exact Subsingleton.elim _ _

private lemma Modules.flatOver_of_isEmpty_for_emptyQuot
    {X Y : Scheme.{u}} [IsEmpty X] (M : X.Modules) (f : X ⟶ Y) :
    M.FlatOver f := by
  intro U V h
  letI := Module.compHom Γ(M, U.1)
    ((X.presheaf.map (homOfLE h).op).hom.comp (f.app V.1).hom)
  have hU : U.1 = ⊥ := Subsingleton.elim _ _
  letI : Subsingleton Γ(M, U.1) :=
    hU.symm ▸ Modules.subsingleton_sections_bot_for_emptyQuot M
  exact Module.Flat.of_free

private noncomputable def emptyQuotientPullbackDataForEmptyRepresentation
    {n : ℕ} {S : Scheme.{u}}
    (F : (projectiveSpaceOver n S).Modules) (T : Over S)
    [IsEmpty T.left] :
    Modules.QuotientPullbackData F (projectiveSpaceOverπ n S) T := by
  let W := ((Over.pullback (projectiveSpaceOverπ n S)).obj T).left
  letI : IsEmpty W :=
    (pullback.fst T.hom (projectiveSpaceOverπ n S)).base.hom.1.isEmpty
  let Q : W.Modules := SheafOfModules.unit W.ringCatSheaf
  exact
    { Q := Q
      isQuasicoherent := Modules.unit_isQuasicoherent W
      isFinitePresentation :=
        Modules.unit_isFinitePresentation_of_globalPresentation W
      flatOver := Modules.flatOver_of_isEmpty_for_emptyQuot Q _
      π := 0
      epi := (Modules.isZero_of_isEmpty_for_emptyQuot Q).epi 0 }

private lemma emptyQuotientPullbackDataForEmptyRepresentation_hasHilbertPolynomial
    {n : ℕ} {S : Scheme.{u}}
    (F : (projectiveSpaceOver n S).Modules) (P : Polynomial ℚ)
    (T : Over S) [IsEmpty T.left] :
    (emptyQuotientPullbackDataForEmptyRepresentation F T).HasFiberwiseHilbertPolynomial P := by
  intro K hK s
  letI : Field K := hK.toField
  letI : IsEmpty (Spec K) := s.base.hom.1.isEmpty
  exact isEmptyElim (Classical.arbitrary (Spec K))

private noncomputable def emptyQuotFunctorPPointForEmptyRepresentation
    {n : ℕ} {S : Scheme.{u}}
    (F : (projectiveSpaceOver n S).Modules) (P : Polynomial ℚ)
    (T : Over S) [IsEmpty T.left] :
    (quotFunctorP F P).obj (op T) :=
  ⟨Quotient.mk _ (emptyQuotientPullbackDataForEmptyRepresentation F T),
    emptyQuotientPullbackDataForEmptyRepresentation F T,
    rfl,
    emptyQuotientPullbackDataForEmptyRepresentation_hasHilbertPolynomial F P T⟩

private lemma quotientPullbackData_r_of_isEmpty_for_emptyQuot
    {X S : Scheme.{u}} {F : X.Modules} {f : X ⟶ S}
    (T : Over S) [IsEmpty T.left]
    (x y : Modules.QuotientPullbackData F f T) :
    (Modules.QuotientPullbackData.setoid F f T).r x y := by
  let W := ((Over.pullback f).obj T).left
  letI : IsEmpty W := (pullback.fst T.hom f).base.hom.1.isEmpty
  let hx : IsZero x.Q := Modules.isZero_of_isEmpty_for_emptyQuot x.Q
  let hy : IsZero y.Q := Modules.isZero_of_isEmpty_for_emptyQuot y.Q
  refine ⟨hx.isoZero ≪≫ hy.isoZero.symm, ?_⟩
  exact hy.eq_of_tgt _ _

private lemma quotFunctorP_subsingleton_of_isEmpty_for_emptyQuot
    {n : ℕ} {S : Scheme.{u}}
    (F : (projectiveSpaceOver n S).Modules) (P : Polynomial ℚ)
    (T : Over S) [IsEmpty T.left] :
    Subsingleton ((quotFunctorP F P).obj (op T)) := by
  constructor
  intro x y
  apply Subtype.ext
  obtain ⟨a, ha⟩ := Quotient.exists_rep x.1
  obtain ⟨b, hb⟩ := Quotient.exists_rep y.1
  rw [← ha, ← hb]
  exact Quotient.sound
    (quotientPullbackData_r_of_isEmpty_for_emptyQuot T a b)

private noncomputable def emptyOverForEmptyQuot (S : Scheme.{u}) : Over S :=
  Over.mk (Scheme.emptyTo S)

private instance emptyOverForEmptyQuot_isEmpty (S : Scheme.{u}) :
    IsEmpty (emptyOverForEmptyQuot S).left := by
  dsimp [emptyOverForEmptyQuot]
  infer_instance

private noncomputable def emptyOverToQuotFunctorPForEmptyRepresentation
    {n : ℕ} {S : Scheme.{u}}
    (F : (projectiveSpaceOver n S).Modules) (P : Polynomial ℚ)
    {T : Over S} (g : T ⟶ emptyOverForEmptyQuot S) :
    (quotFunctorP F P).obj (op T) := by
  letI : IsEmpty T.left := g.left.base.hom.1.isEmpty
  exact emptyQuotFunctorPPointForEmptyRepresentation F P T

private noncomputable def quotFunctorPToEmptyOverForEmptyRepresentation
    {n : ℕ} {S : Scheme.{u}}
    (F : (projectiveSpaceOver n S).Modules) (P : Polynomial ℚ)
    (hempty : ∀ T : Over S, Nonempty T.left →
      IsEmpty ((quotFunctorP F P).obj (op T)))
    {T : Over S} (z : (quotFunctorP F P).obj (op T)) :
    T ⟶ emptyOverForEmptyQuot S := by
  have hne : ¬ Nonempty T.left := by
    intro hT
    letI : IsEmpty ((quotFunctorP F P).obj (op T)) := hempty T hT
    exact isEmptyElim z
  letI : IsEmpty T.left := not_nonempty_iff.mp hne
  let hT : IsInitial T.left := isInitialOfIsEmpty
  exact Over.homMk (hT.to (emptyOverForEmptyQuot S).left) (hT.hom_ext _ _)

private noncomputable def emptyOverQuotFunctorPEquivForEmptyRepresentation
    {n : ℕ} {S : Scheme.{u}}
    (F : (projectiveSpaceOver n S).Modules) (P : Polynomial ℚ)
    (hempty : ∀ T : Over S, Nonempty T.left →
      IsEmpty ((quotFunctorP F P).obj (op T)))
    (T : Over S) :
    (T ⟶ emptyOverForEmptyQuot S) ≃ (quotFunctorP F P).obj (op T) where
  toFun := emptyOverToQuotFunctorPForEmptyRepresentation F P
  invFun := quotFunctorPToEmptyOverForEmptyRepresentation F P hempty
  left_inv g := by
    letI : IsEmpty T.left := g.left.base.hom.1.isEmpty
    apply Over.OverMorphism.ext
    exact isInitialOfIsEmpty.hom_ext _ _
  right_inv z := by
    let g := quotFunctorPToEmptyOverForEmptyRepresentation F P hempty z
    letI : IsEmpty T.left := g.left.base.hom.1.isEmpty
    exact (quotFunctorP_subsingleton_of_isEmpty_for_emptyQuot F P T).elim _ _

private noncomputable def quotFunctorPRepresentableByEmptyForEmptyRepresentation
    {n : ℕ} {S : Scheme.{u}}
    (F : (projectiveSpaceOver n S).Modules) (P : Polynomial ℚ)
    (hempty : ∀ T : Over S, Nonempty T.left →
      IsEmpty ((quotFunctorP F P).obj (op T))) :
    (quotFunctorP F P).RepresentableBy (emptyOverForEmptyQuot S) where
  homEquiv := emptyOverQuotFunctorPEquivForEmptyRepresentation F P hempty _
  homEquiv_comp {X X'} f g := by
    letI : IsEmpty X.left := (f ≫ g).left.base.hom.1.isEmpty
    exact (quotFunctorP_subsingleton_of_isEmpty_for_emptyQuot F P X).elim _ _

private theorem emptyOverForEmptyQuot_isHProjective (S : Scheme.{u}) :
    IsHProjective (emptyOverForEmptyQuot S).hom := by
  refine ⟨0, Scheme.emptyTo (projectiveSpaceOver 0 S), inferInstance, ?_⟩
  exact Scheme.empty_ext _ _

/-- A fixed-polynomial Quot functor with no points on nonempty test schemes is
represented by an H-projective empty scheme. -/
theorem exists_quotFunctorP_representableBy_isHProjective_of_emptyOnNonempty
    {n : ℕ} {S : Scheme.{u}}
    (F : (projectiveSpaceOver n S).Modules) (P : Polynomial ℚ)
    (hempty : ∀ T : Over S, Nonempty T.left →
      IsEmpty ((quotFunctorP F P).obj (op T))) :
    ∃ Q : Over S, Nonempty ((quotFunctorP F P).RepresentableBy Q) ∧
      IsHProjective Q.hom :=
  ⟨emptyOverForEmptyQuot S,
    ⟨quotFunctorPRepresentableByEmptyForEmptyRepresentation F P hempty⟩,
    emptyOverForEmptyQuot_isHProjective S⟩

end AlgebraicGeometry.Scheme

end

end
