module

public import StacksAndModuli.API.StrictQuotientLocalCharts

/-!
# The strict Quot atlas for a zero ambient sheaf

If the ambient sheaf is a zero object, every epimorphic quotient of its pullback is a
zero object.  Hence the strict kernel model of the Quot functor is terminal.  This file
constructs the resulting one-chart strict Quot atlas explicitly; it is a boundary case
of the bounded local-chart input needed for the general Quot representability theorem.

Main declarations:
- `AlgebraicGeometry.Scheme.Modules.QuotientPullbackData.zero`;
- `AlgebraicGeometry.Scheme.strictQuotFunctorTerminalIsoOfIsZero`;
- `AlgebraicGeometry.Scheme.strictQuotientChartAtlasOfIsZero`;
- `AlgebraicGeometry.Scheme.exists_quotientRepresentableBy_of_isZero`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme

namespace Modules.QuotientPullbackData

variable {X S : Scheme.{u}} (F : X.Modules) (f : X ⟶ S) (T : Over S)

/-- The zero quotient is a flat, finitely presented quotient of any ambient sheaf. -/
noncomputable def zero : QuotientPullbackData F f T := by
  let W := ((Over.pullback f).obj T).left
  let I := ULift.{u} PEmpty
  let Q : W.Modules := SheafOfModules.free (R := W.ringCatSheaf) I
  have hQ : IsZero Q := by
    dsimp only [Q]
    rw [IsZero.iff_id_eq_zero]
    apply Cofan.IsColimit.hom_ext
      (SheafOfModules.isColimitFreeCofan (R := W.ringCatSheaf) I)
    intro i
    exact isEmptyElim i
  let P := Modules.freePresentation (X := W) I
  exact
    { Q := Q
      isQuasicoherent := P.isQuasicoherent
      isFinitePresentation := Modules.isFinitePresentation_of_globalPresentation P
      flatOver := by
        intro U V h
        letI := Module.compHom Γ(Q, U.1)
          ((W.presheaf.map (homOfLE h).op).hom.comp
            ((pullback.fst T.hom f).app V.1).hom)
        letI : Subsingleton Γ(Q, U.1) := by
          constructor
          intro a b
          have hid : (𝟙 Q : Q ⟶ Q) = 0 := hQ.eq_of_src _ _
          have ha : a = 0 := by
            calc
              a = ((𝟙 Q : Q ⟶ Q).app U.1).hom a := by simp
              _ = ((0 : Q ⟶ Q).app U.1).hom a := by rw [hid]
              _ = 0 := by simp
          have hb : b = 0 := by
            calc
              b = ((𝟙 Q : Q ⟶ Q).app U.1).hom b := by simp
              _ = ((0 : Q ⟶ Q).app U.1).hom b := by rw [hid]
              _ = 0 := by simp
          exact ha.trans hb.symm
        exact Module.Flat.of_free
      π := 0
      epi := hQ.epi _ }

end Modules.QuotientPullbackData

namespace Modules.StrictQuotientKernelData

variable {X S : Scheme.{u}} (F : X.Modules) (f : X ⟶ S) (T : Over S)

/-- The strict kernel point defined by the zero quotient. -/
noncomputable def zero : StrictQuotientKernelData F f T :=
  ofQuotient (QuotientPullbackData.zero F f T)

/-- If the ambient sheaf is zero, every strict quotient kernel is the kernel of the
zero quotient. -/
theorem eq_zero_of_isZero (hF : IsZero F) (K : StrictQuotientKernelData F f T) :
    K = zero F f T := by
  let z := QuotientPullbackData.zero F f T
  let hsource : IsZero
      ((Modules.pullback ((Over.pullback f).obj T).hom).obj F) :=
    (Modules.pullback ((Over.pullback f).obj T).hom).map_isZero hF
  letI : Epi K.witness.π := K.witness.epi
  letI : Epi z.π := z.epi
  let htarget : IsZero K.witness.Q := IsZero.of_epi K.witness.π hsource
  let hzero : IsZero z.Q := IsZero.of_epi z.π hsource
  let e : K.witness.Q ≅ z.Q := IsZero.iso htarget hzero
  have hr : (QuotientPullbackData.setoid F f T).r K.witness
      z := by
    refine ⟨e, ?_⟩
    exact hzero.eq_of_tgt _ _
  apply Subtype.ext
  exact K.kernelData_witness.symm.trans
    (QuotientPullbackData.kernelData_eq_of_r hr)

/-- Strict Quot kernels form a subsingleton when the ambient sheaf is zero. -/
theorem subsingleton_of_isZero (hF : IsZero F) :
    Subsingleton (StrictQuotientKernelData F f T) :=
  ⟨fun K L ↦ (eq_zero_of_isZero F f T hF K).trans
    (eq_zero_of_isZero F f T hF L).symm⟩

end Modules.StrictQuotientKernelData

/-- The strict Quot functor of a zero ambient sheaf is represented by the terminal
object of the over-category. -/
noncomputable def strictQuotFunctorTerminalIsoOfIsZero
    {X S : Scheme.{u}} (F : X.Modules) (f : X ⟶ S) (hF : IsZero F) :
    uliftYoneda.{0}.obj (Over.mk (𝟙 S)) ≅ strictQuotFunctor F f := by
  let point : (strictQuotFunctor F f).obj (op (Over.mk (𝟙 S))) :=
    Modules.StrictQuotientKernelData.zero F f (Over.mk (𝟙 S))
  let α : uliftYoneda.{0}.obj (Over.mk (𝟙 S)) ⟶ strictQuotFunctor F f :=
    uliftYonedaEquiv.symm point
  have hα : IsIso α := by
    letI (T : (Over S)ᵒᵖ) : IsIso (α.app T) := by
      rw [isIso_iff_bijective]
      constructor
      · intro a b _
        apply ULift.ext
        apply Over.OverMorphism.ext
        simpa using (Over.w a.down).trans (Over.w b.down).symm
      · intro K
        refine ⟨ULift.up (Over.homMk (unop T).hom), ?_⟩
        exact @Subsingleton.elim
          (Modules.StrictQuotientKernelData F f (unop T))
          (Modules.StrictQuotientKernelData.subsingleton_of_isZero F f (unop T) hF) _ _
    exact NatIso.isIso_of_isIso_app α
  exact asIso α

/-- A natural isomorphism of presheaves is relatively representable by open immersions. -/
theorem relative_over_isOpenImmersion_of_isIso
    {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} (g : F ⟶ G) [IsIso g] :
    (isOpenImmersionOver S).relative uliftYoneda.{0} g := by
  apply MorphismProperty.relative.of_exists
  intro T h
  refine ⟨T, h ≫ inv g, 𝟙 T, ?_, ?_⟩
  · exact IsPullback.of_vert_isIso ⟨by simp⟩
  · change IsOpenImmersion (𝟙 T.left)
    infer_instance

/-- The one-chart strict Quot atlas for a zero ambient sheaf. -/
noncomputable def strictQuotientChartAtlasOfIsZero
    {X S : Scheme.{u}} (F : X.Modules) (f : X ⟶ S) (hF : IsZero F) :
    StrictQuotientChartAtlas F f where
  I := PUnit
  chart _ := Over.mk (𝟙 S)
  map _ := (strictQuotFunctorTerminalIsoOfIsZero F f hF).hom
  isOpen _ := relative_over_isOpenImmersion_of_isIso _
  locallySurjective := by
    apply Presheaf.isLocallySurjective_of_surjective
    intro T K
    refine ⟨(Limits.Sigma.ι
      (fun _ : PUnit ↦ uliftYoneda.{0}.obj (Over.mk (𝟙 S))) PUnit.unit).app T
      (ULift.up (Over.homMk (unop T).hom)), ?_⟩
    exact @Subsingleton.elim
      (Modules.StrictQuotientKernelData F f (unop T))
      (Modules.StrictQuotientKernelData.subsingleton_of_isZero F f (unop T) hF) _ _
  locallyOfFiniteType _ := by
    change LocallyOfFiniteType (𝟙 S)
    infer_instance

/-- The strict Quot functor of a zero ambient sheaf admits the local chart atlas required
by the general gluing theorem. -/
theorem nonempty_strictQuotientChartAtlas_of_isZero
    {X S : Scheme.{u}} (F : X.Modules) (f : X ⟶ S) (hF : IsZero F) :
    Nonempty (StrictQuotientChartAtlas F f) :=
  ⟨strictQuotientChartAtlasOfIsZero F f hF⟩

/-- A zero ambient sheaf has a locally finite-type Quot representative.  The explicit
terminal model makes a quasicoherence hypothesis on the ambient sheaf unnecessary. -/
theorem exists_quotientRepresentableBy_of_isZero
    {X S : Scheme.{u}} (F : X.Modules) (f : X ⟶ S) (hF : IsZero F) :
    ∃ Q : Over S,
      Nonempty ((quotFunctor F f).RepresentableBy Q) ∧ LocallyOfFiniteType Q.hom :=
  (quotFunctor_exists_representableBy_iff_strictQuotFunctor
    F f (fun Q ↦ LocallyOfFiniteType Q.hom)).2 <| by
      refine ⟨Over.mk (𝟙 S), ⟨?_⟩, ?_⟩
      · exact (Functor.RepresentableBy.equivUliftYonedaIso
          (strictQuotFunctor F f) (Over.mk (𝟙 S))).symm
            (strictQuotFunctorTerminalIsoOfIsZero F f hF)
      · change LocallyOfFiniteType (𝟙 S)
        infer_instance

end AlgebraicGeometry.Scheme

end
