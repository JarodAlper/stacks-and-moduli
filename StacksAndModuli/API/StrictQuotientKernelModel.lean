module

public import StacksAndModuli.API.EpiKernelClassification
public import StacksAndModuli.API.OpenCoverQuotient
public import StacksAndModuli.API.PresheafSubmoduleRange
public import StacksAndModuli.«Section2.1-Intro».«part2.1.3-projective-space-and-hilbert-quot-functors»

/-!
# A universe-small kernel model for the Quot functor

The usual Quot functor records a quotient sheaf up to compatible isomorphism, so its
values lie one universe above the schemes on which it is evaluated.  This file replaces
each isomorphism class by the sectionwise range of the kernel inclusion.  Such ranges are
restriction-stable submodules of the pulled-back source sheaf and form a type in the same
universe as the test scheme.

The small model remembers, as a proposition, that its kernel is realised by a flat,
finitely presented, quasicoherent quotient.  Choosing a realisation defines pullback;
classification of epimorphisms by their kernels proves that the result is independent of
the choice.  The resulting functor becomes naturally isomorphic to the usual Quot functor
after `ULift`.

Main declarations:
- `AlgebraicGeometry.Scheme.Modules.QuotientPullbackData.kernelData`;
- `AlgebraicGeometry.Scheme.Modules.StrictQuotientKernelData`;
- `AlgebraicGeometry.Scheme.strictQuotFunctor`;
- `AlgebraicGeometry.Scheme.strictQuotientKernelNatIso`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme

namespace Modules.QuotientPullbackData

variable {X S : Scheme.{u}} {F : X.Modules} {f : X ⟶ S}
variable {T T' : Over S}

/-- Equal morphisms of sheaves of modules have equal sectionwise kernel ranges. -/
lemma kernelRange_eq_of_eq {Y : Scheme.{u}} {M Q : Y.Modules}
    {p q : M ⟶ Q} (h : p = q) :
    PresheafOfModules.Submodule.range (kernel.ι p).val =
      PresheafOfModules.Submodule.range (kernel.ι q).val := by
  subst q
  rfl

/-- The universe-small kernel of a Quot datum, recorded as the sectionwise range of
the kernel inclusion into the pulled-back source sheaf. -/
noncomputable def kernelData (x : QuotientPullbackData F f T) :
    ((Modules.pullback ((Over.pullback f).obj T).hom).obj F).val.Submodule :=
  PresheafOfModules.Submodule.range (kernel.ι x.π).val

/-- Equivalent quotient presentations have equal strict kernel data. -/
lemma kernelData_eq_of_r {x y : QuotientPullbackData F f T}
    (h : (QuotientPullbackData.setoid F f T).r x y) :
    x.kernelData = y.kernelData := by
  obtain ⟨e, he⟩ := h
  dsimp only [kernelData]
  have htransport :
      PresheafOfModules.Submodule.range (kernel.ι (x.π ≫ e.hom)).val =
        PresheafOfModules.Submodule.range (kernel.ι y.π).val :=
    kernelRange_eq_of_eq he
  exact (SheafOfModules.kernelRange_comp_isIso x.π e).symm.trans htransport

/-- Quotient presentations with equal strict kernel data are equivalent. -/
lemma r_of_kernelData_eq {x y : QuotientPullbackData F f T}
    (h : x.kernelData = y.kernelData) :
    (QuotientPullbackData.setoid F f T).r x y := by
  let M := (Modules.pullback ((Over.pullback f).obj T).hom).obj F
  let _ : Mono (kernel.ι x.π).val := Modules.val_mono_of_mono _
  let _ : Mono (kernel.ι y.π).val := Modules.val_mono_of_mono _
  let _ : Epi x.π := x.epi
  let _ : Epi y.π := y.epi
  let e : kernel x.π ≅ kernel y.π :=
    M.isoOfRangeEq (kernel.ι x.π) (kernel.ι y.π) h
  apply CategoryTheory.Abelian.exists_iso_comp_eq_of_kernelSubobject_eq x.π y.π
  exact Subobject.mk_eq_mk_of_comm _ _ e
    (SheafOfModules.isoOfRangeEq_hom_comp M
      (kernel.ι x.π) (kernel.ι y.π) h)

/-- Compatible isomorphism of Quot data is exactly equality of their strict kernels. -/
lemma kernelData_eq_iff_r {x y : QuotientPullbackData F f T} :
    x.kernelData = y.kernelData ↔
      (QuotientPullbackData.setoid F f T).r x y :=
  ⟨r_of_kernelData_eq, kernelData_eq_of_r⟩

end Modules.QuotientPullbackData

namespace Modules

variable {X S : Scheme.{u}} (F : X.Modules) (f : X ⟶ S)

/-- A universe-small point of Quot: a sectionwise kernel in the pulled-back source
which is realised by a quasicoherent, finitely presented quotient flat over the test
scheme.  Realisability is proposition-valued, so the type remains in universe `u`. -/
def StrictQuotientKernelData (T : Over S) : Type u :=
  {K : ((Modules.pullback ((Over.pullback f).obj T).hom).obj F).val.Submodule //
    ∃ x : QuotientPullbackData F f T, x.kernelData = K}

namespace StrictQuotientKernelData

variable {F f} {T T' : Over S}

/-- A chosen quotient presentation realising strict kernel data. -/
noncomputable def witness (K : StrictQuotientKernelData F f T) :
    QuotientPullbackData F f T :=
  K.property.choose

/-- The chosen presentation has the prescribed kernel. -/
@[simp]
lemma kernelData_witness (K : StrictQuotientKernelData F f T) :
    K.witness.kernelData = K.1 :=
  K.property.choose_spec

/-- The strict kernel attached to a quotient presentation. -/
noncomputable def ofQuotient (x : QuotientPullbackData F f T) :
    StrictQuotientKernelData F f T :=
  ⟨x.kernelData, x, rfl⟩

@[simp]
lemma ofQuotient_val (x : QuotientPullbackData F f T) :
    (ofQuotient x).1 = x.kernelData :=
  rfl

/-- Pull back strict kernel data by choosing a presentation, pulling it back, and
then forgetting back to its kernel.  Kernel classification makes this choice-free. -/
noncomputable def pullback (g : T' ⟶ T) (K : StrictQuotientKernelData F f T) :
    StrictQuotientKernelData F f T' :=
  ofQuotient (K.witness.pullback g)

/-- Pullback of strict kernel data is independent of the chosen realising quotient. -/
lemma pullback_eq_of_kernelData_eq (g : T' ⟶ T)
    (K : StrictQuotientKernelData F f T) (x : QuotientPullbackData F f T)
    (hx : x.kernelData = K.1) :
    K.pullback g = ofQuotient (x.pullback g) := by
  apply Subtype.ext
  apply Modules.QuotientPullbackData.kernelData_eq_of_r
  apply Modules.QuotientPullbackData.pullback_r
  exact Modules.QuotientPullbackData.r_of_kernelData_eq
    (K.kernelData_witness.trans hx.symm)

/-- Pulling strict kernel data back along an identity does nothing. -/
@[simp]
lemma pullback_id (K : StrictQuotientKernelData F f T) :
    K.pullback (𝟙 T) = K := by
  apply Subtype.ext
  exact (Modules.QuotientPullbackData.kernelData_eq_of_r
    (Modules.QuotientPullbackData.pullback_id_r K.witness)).trans
      K.kernelData_witness

/-- Pullback of strict kernel data is strictly functorial. -/
lemma pullback_comp (g : T' ⟶ T) {T'' : Over S} (g' : T'' ⟶ T')
    (K : StrictQuotientKernelData F f T) :
    (K.pullback g).pullback g' = K.pullback (g' ≫ g) := by
  apply Subtype.ext
  have hchosen :
      (QuotientPullbackData.setoid F f T').r
        (K.pullback g).witness (K.witness.pullback g) :=
    QuotientPullbackData.r_of_kernelData_eq
      ((K.pullback g).kernelData_witness.trans rfl)
  have hpull := QuotientPullbackData.pullback_r (g := g') hchosen
  have hcomp := QuotientPullbackData.pullback_comp_r g g' K.witness
  exact QuotientPullbackData.kernelData_eq_of_r
    ((QuotientPullbackData.setoid F f _).trans hpull hcomp)

/-- Strict kernels, lifted by one universe, are equivalent to isomorphism classes of
Quot data on each test scheme. -/
noncomputable def quotientEquiv :
    ULift.{u + 1} (StrictQuotientKernelData F f T) ≃
      Quotient (QuotientPullbackData.setoid F f T) where
  toFun K := Quotient.mk _ K.down.witness
  invFun := Quotient.lift (fun x ↦ ULift.up (ofQuotient x)) (by
    intro x y h
    apply ULift.ext
    exact Subtype.ext (QuotientPullbackData.kernelData_eq_of_r h))
  left_inv K := by
    obtain ⟨K⟩ := K
    apply ULift.ext
    exact Subtype.ext K.kernelData_witness
  right_inv q := by
    refine Quotient.inductionOn q (fun x ↦ ?_)
    apply Quotient.sound
    exact QuotientPullbackData.r_of_kernelData_eq
      (ofQuotient x).kernelData_witness

end StrictQuotientKernelData

end Modules

/-- The universe-small strict-kernel version of the Quot functor. -/
noncomputable def strictQuotFunctor {X S : Scheme.{u}} (F : X.Modules) (f : X ⟶ S) :
    CategoryTheory.Functor (Over S)ᵒᵖ (Type u) where
  obj T := Modules.StrictQuotientKernelData F f (unop T)
  map g := ↾fun K ↦ Modules.StrictQuotientKernelData.pullback
    (F := F) (f := f) g.unop K
  map_id T := by
    refine ConcreteCategory.hom_ext _ _ fun K ↦ ?_
    exact Modules.StrictQuotientKernelData.pullback_id K
  map_comp g g' := by
    refine ConcreteCategory.hom_ext _ _ fun K ↦ ?_
    exact (Modules.StrictQuotientKernelData.pullback_comp g.unop g'.unop K).symm

/-- After lifting values by one universe, the strict-kernel functor is naturally
isomorphic to the usual isomorphism-class Quot functor. -/
noncomputable def strictQuotientKernelNatIso {X S : Scheme.{u}}
    (F : X.Modules) (f : X ⟶ S) :
    strictQuotFunctor F f ⋙ uliftFunctor.{u + 1, u} ≅ quotFunctor F f :=
  NatIso.ofComponents
    (fun T ↦ (Modules.StrictQuotientKernelData.quotientEquiv
      (F := F) (f := f) (T := unop T)).toIso)
    (by
      intro T T' g
      ext K
      obtain ⟨K⟩ := K
      apply Quotient.sound
      exact Modules.QuotientPullbackData.r_of_kernelData_eq
        (Modules.StrictQuotientKernelData.kernelData_witness (K.pullback g.unop)))

/-- The strict and isomorphism-class Quot functors satisfy exactly the same relative
Zariski sheaf condition.  The strict side is the one to use with universe-small local
representability theorems. -/
theorem strictQuotFunctor_isSheaf_iff_quotFunctor_isSheaf
    {X S : Scheme.{u}} (F : X.Modules) (f : X ⟶ S) :
    Presieve.IsSheaf (Scheme.zariskiTopology.over S) (strictQuotFunctor F f) ↔
      Presieve.IsSheaf (Scheme.zariskiTopology.over S) (quotFunctor F f) := by
  constructor
  · intro h
    exact Presieve.isSheaf_iso (Scheme.zariskiTopology.over S)
      (strictQuotientKernelNatIso F f)
      ((Presieve.isSheaf_comp_uliftFunctor_iff
        (J := Scheme.zariskiTopology.over S)).mpr h)
  · intro h
    exact (Presieve.isSheaf_comp_uliftFunctor_iff
      (J := Scheme.zariskiTopology.over S)).mp
        (Presieve.isSheaf_iso (Scheme.zariskiTopology.over S)
          (strictQuotientKernelNatIso F f).symm h)

/-- Bundle the strict Quot functor as a relative-Zariski sheaf once effective descent
has supplied its remaining sheaf condition. -/
noncomputable def strictQuotFunctorSheaf {X S : Scheme.{u}}
    (F : X.Modules) (f : X ⟶ S)
    (h : Presieve.IsSheaf (Scheme.zariskiTopology.over S) (strictQuotFunctor F f)) :
    Sheaf (Scheme.zariskiTopology.over S) (Type u) :=
  ⟨strictQuotFunctor F f, (isSheaf_iff_isSheaf_of_type _ _).2 h⟩

/-- Representability of the usual Quot functor by a fixed scheme is equivalent to
representability of its universe-small strict-kernel model. -/
theorem quotFunctor_representableBy_iff_strictQuotFunctor_representableBy
    {X S : Scheme.{u}} (F : X.Modules) (f : X ⟶ S) (Q : Over S) :
    Nonempty ((quotFunctor F f).RepresentableBy Q) ↔
      Nonempty ((strictQuotFunctor F f).RepresentableBy Q) := by
  constructor
  · rintro ⟨h⟩
    exact ⟨Functor.representableByUliftFunctorEquiv
      (h.ofIso (strictQuotientKernelNatIso F f).symm)⟩
  · rintro ⟨h⟩
    exact ⟨((Functor.representableByUliftFunctorEquiv).symm h).ofIso
      (strictQuotientKernelNatIso F f)⟩

/-- Any additional property of the representing object may be carried unchanged
through the strict-kernel comparison.  Thus local chart and gluing arguments for Quot
may be performed entirely on the universe-small functor. -/
theorem quotFunctor_exists_representableBy_iff_strictQuotFunctor
    {X S : Scheme.{u}} (F : X.Modules) (f : X ⟶ S) (P : Over S → Prop) :
    (∃ Q : Over S, Nonempty ((quotFunctor F f).RepresentableBy Q) ∧ P Q) ↔
      ∃ Q : Over S, Nonempty ((strictQuotFunctor F f).RepresentableBy Q) ∧ P Q := by
  constructor
  · rintro ⟨Q, hQ, hP⟩
    exact ⟨Q, (quotFunctor_representableBy_iff_strictQuotFunctor_representableBy
      F f Q).mp hQ, hP⟩
  · rintro ⟨Q, hQ, hP⟩
    exact ⟨Q, (quotFunctor_representableBy_iff_strictQuotFunctor_representableBy
      F f Q).mpr hQ, hP⟩

end AlgebraicGeometry.Scheme

end
