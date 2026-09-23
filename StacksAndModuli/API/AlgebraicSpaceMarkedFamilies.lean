module

public import StacksAndModuli.API.MarkedGeometricFiberProperty
public import StacksAndModuli.«Section4.8-Properness».«part4.8.1-definitions»
public import StacksAndModuli.«Section6.3-Stable».«part6.3.1-definition»

/-!
# Marked families with algebraic-space total space

This file packages a morphism from an algebraic space to a scheme together with an
indexed family of sections.  It also provides a scheme presentation of each geometric
fibre and transports the sections to that presentation.  The construction is the
reusable algebraic-space infrastructure needed for Definition 6.3.20 of *Stacks and
Moduli*.

The total algebraic space is represented by its functor of points.  For a geometric
point `Spec K ⟶ S`, its fibre is the pullback presheaf.  A
`PresentedGeometricFiber` records a scheme representing that presheaf.  Yoneda full
faithfulness then recovers both the structure morphism to `Spec K` and its induced
marked sections, so fibre predicates can use the ordinary scheme API.

## Main declarations

* `AlgebraicGeometry.MarkedAlgebraicSpaceOver`;
* `AlgebraicGeometry.MarkedAlgebraicSpaceOver.reindex`;
* `AlgebraicGeometry.MarkedAlgebraicSpaceOver.PresentedGeometricFiber`;
* `AlgebraicGeometry.MarkedAlgebraicSpaceOver.PresentedGeometricFiber.reindex`;
* `AlgebraicGeometry.MarkedAlgebraicSpaceOver.PresentedGeometricFiber.marking`;
* `AlgebraicGeometry.MarkedAlgebraicSpaceOver.PresentedGeometricFiber.isoOver`;
* `AlgebraicGeometry.MarkedAlgebraicSpaceOver.HasPresentedGeometricFibers`;
* `AlgebraicGeometry.MarkedAlgebraicSpaceOver.HasPresentedGeometricFibers.prop`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.BasedCategory

universe w v u

namespace AlgebraicGeometry

/-- A morphism from an algebraic space to a scheme, equipped with an indexed family of
sections.  This is only the raw data: geometric and finiteness conditions are imposed by
separate predicates. -/
structure MarkedAlgebraicSpaceOver (I : Type v) (S : Scheme.{u}) where
  /-- The functor of points of the total algebraic space. -/
  total : Scheme.{u}ᵒᵖ ⥤ Type u
  /-- The total functor is an algebraic space. -/
  isAlgebraicSpace : IsAlgebraicSpace total
  /-- The structure morphism to the base scheme. -/
  hom : total ⟶ yoneda.obj S
  /-- The indexed sections of the structure morphism. -/
  mark : I → (yoneda.obj S ⟶ total)
  /-- Each marking is a section. -/
  mark_fac : ∀ i, mark i ≫ hom = 𝟙 _

/-- A morphism from an algebraic space to a scheme with `n` ordered sections. -/
abbrev NMarkedAlgebraicSpaceOver (n : ℕ) (S : Scheme.{u}) :=
  MarkedAlgebraicSpaceOver (Fin n) S

namespace MarkedAlgebraicSpaceOver

variable {I : Type v} {S : Scheme.{u}} (F : MarkedAlgebraicSpaceOver I S)

instance : IsAlgebraicSpace F.total := F.isAlgebraicSpace

/-- Reindex the markings of an algebraic-space family along an arbitrary map of index
types. The total algebraic space and its structure morphism are unchanged. -/
def reindex {J : Type w} (e : J → I) : MarkedAlgebraicSpaceOver J S where
  total := F.total
  isAlgebraicSpace := F.isAlgebraicSpace
  hom := F.hom
  mark := F.mark ∘ e
  mark_fac := fun j ↦ F.mark_fac (e j)

@[simp]
theorem reindex_total {J : Type w} (e : J → I) : (F.reindex e).total = F.total :=
  rfl

@[simp]
theorem reindex_hom {J : Type w} (e : J → I) : (F.reindex e).hom = F.hom :=
  rfl

@[simp]
theorem reindex_mark {J : Type w} (e : J → I) (j : J) :
    (F.reindex e).mark j = F.mark (e j) :=
  rfl

/-- Reindexing along an equivalence and then along its inverse recovers the original
marked algebraic-space family. -/
theorem reindex_symm {J : Type w} (e : J ≃ I) :
    (F.reindex e).reindex e.symm = F := by
  cases F
  simp [reindex, Function.comp_def]

/-- The morphism of prestacks associated with the structure morphism of a marked
algebraic space over a scheme. -/
def toBaseFunctor : ofPresheaf F.total ⥤ᵇ ofPresheaf (yoneda.obj S) :=
  ofPresheaf.map F.hom

/-- The presheaf-theoretic fibre over a field-valued point of the base. -/
abbrev fiberPresheaf (K : Type u) [Field K]
    (s : Spec (CommRingCat.of K) ⟶ S) : Scheme.{u}ᵒᵖ ⥤ Type u :=
  pullback F.hom (yoneda.map s)

/-- A fibre of an algebraic space over a field-valued point is again an algebraic
space. -/
instance fiberPresheaf_isAlgebraicSpace (K : Type u) [Field K]
    (s : Spec (CommRingCat.of K) ⟶ S) : IsAlgebraicSpace (F.fiberPresheaf K s) :=
  IsAlgebraicSpace.pullback F.hom (yoneda.map s)

/-- The marking induced on a presheaf-theoretic field-valued fibre. -/
def fiberMark (K : Type u) [Field K]
    (s : Spec (CommRingCat.of K) ⟶ S) (i : I) :
    yoneda.obj (Spec (CommRingCat.of K)) ⟶ F.fiberPresheaf K s :=
  pullback.lift (yoneda.map s ≫ F.mark i) (𝟙 _) (by simp [F.mark_fac])

/-- A scheme presentation of a geometric fibre of a marked algebraic-space morphism.

The structure map and markings on `scheme` are recovered canonically from `iso` by
Yoneda full faithfulness. -/
structure PresentedGeometricFiber (K : Type u) [Field K]
    (s : Spec (CommRingCat.of K) ⟶ S) where
  /-- A scheme representing the geometric fibre. -/
  scheme : Scheme.{u}
  /-- Its functor of points is the presheaf pullback defining the fibre. -/
  iso : yoneda.obj scheme ≅ F.fiberPresheaf K s

namespace PresentedGeometricFiber

variable {F} {K : Type u} [Field K]
  {s : Spec (CommRingCat.of K) ⟶ S}

/-- Regard a presentation of a geometric fibre as a presentation of the same family
after reindexing its markings. -/
def reindex (P : F.PresentedGeometricFiber K s) {J : Type w} (e : J → I) :
    (F.reindex e).PresentedGeometricFiber K s where
  scheme := P.scheme
  iso := P.iso

/-- The structure morphism from a presented fibre to the spectrum of its field. -/
def toBase (P : F.PresentedGeometricFiber K s) :
    P.scheme ⟶ Spec (CommRingCat.of K) :=
  yoneda.preimage (P.iso.hom ≫ pullback.snd F.hom (yoneda.map s))

@[simp]
theorem reindex_toBase (P : F.PresentedGeometricFiber K s)
    {J : Type w} (e : J → I) : (P.reindex e).toBase = P.toBase :=
  rfl

/-- Yoneda sends the recovered structure morphism to the second pullback projection. -/
@[simp]
theorem yoneda_map_toBase (P : F.PresentedGeometricFiber K s) :
    yoneda.map P.toBase =
      P.iso.hom ≫ pullback.snd F.hom (yoneda.map s) := by
  simp [toBase]

/-- The scheme morphism underlying the `i`-th marking of a presented fibre. -/
def markingHom (P : F.PresentedGeometricFiber K s) (i : I) :
    Spec (CommRingCat.of K) ⟶ P.scheme :=
  yoneda.preimage (F.fiberMark K s i ≫ P.iso.inv)

/-- The recovered marking agrees with the canonical marking on the pullback presheaf. -/
@[reassoc]
theorem yoneda_map_markingHom_comp_iso
    (P : F.PresentedGeometricFiber K s) (i : I) :
    yoneda.map (P.markingHom i) ≫ P.iso.hom = F.fiberMark K s i := by
  simp [markingHom, Category.assoc]

/-- The canonical scheme isomorphism between two presentations of the same
presheaf-theoretic geometric fibre. -/
def schemeIso (P Q : F.PresentedGeometricFiber K s) : P.scheme ≅ Q.scheme :=
  Yoneda.fullyFaithful.preimageIso (P.iso ≪≫ Q.iso.symm)

/-- Yoneda identifies the canonical comparison of presentations with the comparison
induced by their representing isomorphisms. -/
@[simp]
theorem yoneda_map_schemeIso_hom (P Q : F.PresentedGeometricFiber K s) :
    yoneda.map (P.schemeIso Q).hom = P.iso.hom ≫ Q.iso.inv := by
  simp [schemeIso]

/-- The canonical comparison between two presentations commutes with their structure
morphisms to the residue field. -/
theorem schemeIso_hom_toBase (P Q : F.PresentedGeometricFiber K s) :
    (P.schemeIso Q).hom ≫ Q.toBase = P.toBase := by
  apply yoneda.map_injective
  simp [Category.assoc]

/-- Two scheme presentations of the same geometric fibre are canonically isomorphic
over the residue field. -/
def isoOver (P Q : F.PresentedGeometricFiber K s) :
    Over.mk P.toBase ≅ Over.mk Q.toBase :=
  Over.isoMk (P.schemeIso Q) (P.schemeIso_hom_toBase Q)

/-- The recovered marking is a section of the recovered structure morphism. -/
theorem markingHom_fac (P : F.PresentedGeometricFiber K s) (i : I) :
    P.markingHom i ≫ P.toBase = 𝟙 _ := by
  apply yoneda.map_injective
  simp only [markingHom, toBase, Functor.map_comp, yoneda.map_preimage]
  rw [Category.assoc, P.iso.inv_hom_id_assoc]
  simp only [fiberMark, pullback.lift_snd]
  simp

/-- The `i`-th marking of a presented geometric fibre, bundled as a section over its
field. -/
def marking (P : F.PresentedGeometricFiber K s) (i : I) :
    @Scheme.SectionOver P.scheme (Spec (CommRingCat.of K)) ⟨P.toBase⟩ :=
  Over.homMk (P.markingHom i) (P.markingHom_fac i)

@[simp]
theorem reindex_marking (P : F.PresentedGeometricFiber K s)
    {J : Type w} (e : J → I) (j : J) :
    (P.reindex e).marking j = P.marking (e j) :=
  rfl

/-- The canonical isomorphism between two presentations carries every recovered
marking to the corresponding marking. -/
@[reassoc]
theorem marking_comp_isoOver_hom
    (P Q : F.PresentedGeometricFiber K s) (i : I) :
    P.marking i ≫ (P.isoOver Q).hom = Q.marking i := by
  apply CostructuredArrow.hom_ext
  change P.markingHom i ≫ (P.schemeIso Q).hom = Q.markingHom i
  apply yoneda.map_injective
  simp [markingHom, Category.assoc]

end PresentedGeometricFiber

/-- Every geometric fibre admits a scheme presentation satisfying the marked
geometric-fibre predicate `Q`.

The existential presentation is the precise bridge from an algebraic-space fibre to the
scheme-level curve predicates.  For isomorphism-invariant predicates its truth is
independent of the chosen presentation. -/
def HasPresentedGeometricFibers
    (Q : MarkedGeometricFiberPredicate.{v, u} I) : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ S),
      ∃ P : F.PresentedGeometricFiber K s,
        @Q K _ _ P.scheme ⟨P.toBase⟩ P.marking

/-- An isomorphism-invariant predicate required on one presentation of every
geometric fibre holds on every presentation. -/
theorem HasPresentedGeometricFibers.prop
    {Q : MarkedGeometricFiberPredicate.{v, u} I}
    [Q.IsClosedUnderIsomorphisms]
    (h : F.HasPresentedGeometricFibers Q)
    {K : Type u} [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ S)
    (P : F.PresentedGeometricFiber K s) :
    @Q K _ _ P.scheme ⟨P.toBase⟩ P.marking := by
  obtain ⟨W, hW⟩ := h K s
  let _ : W.scheme.Over (Spec (CommRingCat.of K)) := ⟨W.toBase⟩
  let _ : P.scheme.Over (Spec (CommRingCat.of K)) := ⟨P.toBase⟩
  exact Q.prop_of_iso (W.isoOver P) (W.marking_comp_isoOver_hom P) hW

/-- A pointwise implication of marked geometric-fibre predicates induces an implication
between their presented-fibre conditions. -/
theorem HasPresentedGeometricFibers.mono
    {Q R : MarkedGeometricFiberPredicate.{v, u} I}
    (hQR : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (Z : Scheme.{u}) [Z.Over (Spec (CommRingCat.of K))]
      (p : I → Z.SectionOver (Spec (CommRingCat.of K))), Q K Z p → R K Z p)
    (hQ : F.HasPresentedGeometricFibers Q) :
    F.HasPresentedGeometricFibers R := by
  intro K _ _ s
  obtain ⟨P, hP⟩ := hQ K s
  let _ : P.scheme.Over (Spec (CommRingCat.of K)) := ⟨P.toBase⟩
  exact ⟨P, hQR K P.scheme P.marking hP⟩

/-- Reindex a presented geometric-fibre condition. The new predicate may differ from
the old one, provided it follows pointwise after precomposing the marking family. -/
theorem HasPresentedGeometricFibers.reindex
    {J : Type w} (e : J → I)
    {Q : MarkedGeometricFiberPredicate.{v, u} I}
    {R : MarkedGeometricFiberPredicate.{w, u} J}
    (hQR : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (Z : Scheme.{u}) [Z.Over (Spec (CommRingCat.of K))]
      (p : I → Z.SectionOver (Spec (CommRingCat.of K))),
        Q K Z p → R K Z (p ∘ e))
    (hQ : F.HasPresentedGeometricFibers Q) :
    (F.reindex e).HasPresentedGeometricFibers R := by
  intro K _ _ s
  obtain ⟨P, hP⟩ := hQ K s
  let P' := P.reindex e
  let _ : P.scheme.Over (Spec (CommRingCat.of K)) := ⟨P.toBase⟩
  refine ⟨P', ?_⟩
  change R K P.scheme (P.reindex e).marking
  have hmark : (P.reindex e).marking = P.marking ∘ e := by
    funext j
    rfl
  rw [hmark]
  exact hQR K P.scheme P.marking hP

/-- Two isomorphism-invariant conditions which hold on presented geometric fibres can
be imposed simultaneously on a common presentation. -/
theorem HasPresentedGeometricFibers.inf
    {Q R : MarkedGeometricFiberPredicate.{v, u} I}
    [Q.IsClosedUnderIsomorphisms] [R.IsClosedUnderIsomorphisms]
    (hQ : F.HasPresentedGeometricFibers Q)
    (hR : F.HasPresentedGeometricFibers R) :
    F.HasPresentedGeometricFibers (Q.inf R) := by
  intro K _ _ s
  obtain ⟨P, hP⟩ := hQ K s
  exact ⟨P, hP, HasPresentedGeometricFibers.prop F hR s P⟩

end MarkedAlgebraicSpaceOver

end AlgebraicGeometry
