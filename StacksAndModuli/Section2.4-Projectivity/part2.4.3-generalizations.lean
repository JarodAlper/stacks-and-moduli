module

public import StacksAndModuli.«Section2.2-Grassmannian».«part2.2.4-projective-space-comparison»
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Projectivity notions and generalizations

This module corresponds to the subsection **Subsection 2.4.4** (Generalizations,
`subsec:generalizations-hilbert-quot`) of §2.4 (Projectivity of Hilb and Quot) of
Chapter 2 of *Stacks and Moduli*,
section label `sec:representability-of-hilb-quot`.

The book distinguishes three notions of projectivity for a morphism `X → S`, in
increasing generality: **H-projective** (closed immersion into `ℙ^n_S`; defined in
part2.1.3 as `AlgebraicGeometry.IsHProjective`), **strongly projective** (closed
immersion into `ℙ(E)` for a vector bundle `E` on `S`; defined in part2.1.2 as
`AlgebraicGeometry.IsStronglyProjective`), and **projective** in the sense of EGA (closed
immersion into `ℙ(E)` for a finite type quasi-coherent sheaf `E`; Stacks 01W8). This
module defines the third notion and states the implications between them.

The remaining items of this subsection and of §2.4 — `exer:flag-schemes`, the parts
(a)–(e) of `exer:quot-generalization1`, the strongly-quasi-projective exercise, the
Artin-axioms remark, and the Chow-variety material of `subsec:chow-schemes` — are not
yet formalized; see this folder's STATUS.md.

Exercise 2.4.13 (`exer:scheme-of-morphisms`) is false as printed: already for
`X = Y = ℙ¹` over a field, positive-degree endomorphisms form nonproper open loci in
projective spaces of pairs of binary forms.  This module formalizes its morphism functor
but makes no projectivity assertion; see the high-confidence `[erratum]` in this folder's
COMMENTARY.md.

Main results:
- `AlgebraicGeometry.IsEGAProjective`: EGA-projectivity of a morphism of schemes
  (`subsec:generalizations-hilbert-quot`).
- `AlgebraicGeometry.IsStronglyProjective.isEGAProjective`,
  `AlgebraicGeometry.IsHProjective.isStronglyProjective`: the implications between the
  three notions (statements; the second proof is deferred).
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section ExerQuotGeneralization1

open CategoryTheory AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Background definition for Subsection 2.4.4 (the implicit
definition of EGA-projectivity): a morphism of schemes `f : X ⟶ S` is **projective in
the sense of EGA** if there is a finite type quasi-coherent sheaf of modules `E` on
`S`, a scheme `P` over `S` representing the projective bundle `ℙ(E) = Gr(1, E)`, and a
factorization of `f` through a closed immersion `X ⟶ P`. This is the most general of
the three notions of projectivity discussed in the book (EGA II.5.5; Stacks Project
tag 01W8). On the rendering of `ℙ(E)` via representability of the rank-one
Grassmannian functor, see the `[decision]` entry in this folder's COMMENTARY.md. -/
def IsEGAProjective {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ (E : S.Modules) (_ : E.IsQuasicoherent) (_ : E.IsFiniteType)
    (P : Over S) (_ : (Modules.grassmannianOverFunctor 1 E).RepresentableBy P)
    (ι : X ⟶ P.left), IsClosedImmersion ι ∧ ι ≫ P.hom = f

/-- API lemma for Subsection 2.4.4 (the implication
strongly projective ⇒ EGA-projective): a strongly projective morphism is projective in
the sense of EGA (a finite locally free sheaf is quasi-coherent of finite type). -/
theorem IsStronglyProjective.isEGAProjective {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : IsStronglyProjective f) : IsEGAProjective f := by
  obtain ⟨E, hqc, hfl, P, hrep, ι, hι, hcomp⟩ := hf
  letI : E.IsQuasicoherent := hqc
  exact ⟨E, hqc, hfl.isFiniteType, P, hrep, ι, hι, hcomp⟩

/-- API lemma for Subsection 2.4.4 (the implication
H-projective ⇒ strongly projective, conditional form): an H-projective morphism is
strongly projective (`ℙ^n_S = ℙ(O_S^{⊕(n+1)})` is the projective bundle of the trivial
bundle) — granted the added hypothesis that relative projective space represents the
rank-one Grassmannian functor of the free sheaf in every dimension. The unconditional
statement is `IsHProjective.isStronglyProjective` below. -/
theorem IsHProjective.isStronglyProjective_of_freeGrassmannianRepresentableBy
    {X S : Scheme.{u}} {f : X ⟶ S} (hf : IsHProjective f)
    (hrep : ∀ n : ℕ,
      (Modules.grassmannianOverFunctor 1
        (SheafOfModules.free (R := S.ringCatSheaf)
          (ULift.{u} (Fin (n + 1))))).RepresentableBy
        (Over.mk (Scheme.projectiveSpaceOverπ n S))) :
    IsStronglyProjective f := by
  obtain ⟨n, ι, hι, hcomp⟩ := hf
  let E : S.Modules :=
    SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin (n + 1)))
  letI : E.IsLocallyFree := inferInstance
  have hqc : E.IsQuasicoherent := inferInstance
  have hfl : Modules.IsFiniteLocallyFree E :=
    Modules.free_isFiniteLocallyFree S (n + 1)
  exact ⟨E, hqc, hfl, Over.mk (Scheme.projectiveSpaceOverπ n S), hrep n,
    ι, hι, hcomp⟩

/-- Relative projective space over `S` is the base change of the glued rank-one
Grassmannian, through the comparison isomorphism
`Proj.projectiveSpaceToRankOneGrassmannian` of part2.2.4. -/
noncomputable def Scheme.projectiveSpaceOverIsoGrassmannianOverRepresentation
    (n : ℕ) (S : Scheme.{u}) :
    Over.mk (Scheme.projectiveSpaceOverπ n S) ≅
      Scheme.grassmannianOverRepresentation S 1 (n + 1) := by
  refine Over.isoMk (asIso (Limits.pullback.map
    (specULiftZIsTerminal.from S)
    (specULiftZIsTerminal.from (Scheme.projectiveSpace n))
    (specULiftZIsTerminal.from S)
    (specULiftZIsTerminal.from (Scheme.grassmannianGlueData.{u} 1 (n + 1)).glued)
    (𝟙 S) (ProjectiveSpectrum.Proj.projectiveSpaceToRankOneGrassmannian.{u} n)
    (𝟙 (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (specULiftZIsTerminal.hom_ext _ _)
    (specULiftZIsTerminal.hom_ext _ _))) ?_
  show Limits.pullback.map
      (specULiftZIsTerminal.from S)
      (specULiftZIsTerminal.from (Scheme.projectiveSpace n))
      (specULiftZIsTerminal.from S)
      (specULiftZIsTerminal.from (Scheme.grassmannianGlueData.{u} 1 (n + 1)).glued)
      (𝟙 S) (ProjectiveSpectrum.Proj.projectiveSpaceToRankOneGrassmannian.{u} n)
      (𝟙 (Spec (CommRingCat.of (ULift.{u} ℤ))))
      (specULiftZIsTerminal.hom_ext _ _)
      (specULiftZIsTerminal.hom_ext _ _) ≫
      Limits.pullback.fst (specULiftZIsTerminal.from S)
        (specULiftZIsTerminal.from
          (Scheme.grassmannianGlueData.{u} 1 (n + 1)).glued) =
    Scheme.projectiveSpaceOverπ n S
  rw [Limits.pullback.lift_fst, Category.comp_id]
  rfl

/-- API lemma for Subsection 2.4.4 (the implication
H-projective ⇒ strongly projective): an H-projective morphism is strongly projective.
Follows formally from
`IsHProjective.isStronglyProjective_of_freeGrassmannianRepresentableBy`: by the
comparison of part2.2.4, `ℙⁿ_S` is the base change of the glued rank-one Grassmannian
and hence represents the rank-one Grassmannian functor of the trivial bundle in every
dimension. -/
theorem IsHProjective.isStronglyProjective {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : IsHProjective f) : IsStronglyProjective f := by
  refine hf.isStronglyProjective_of_freeGrassmannianRepresentableBy (fun n ↦ ?_)
  exact (Scheme.freeGrassmannianRepresentableBy S 1 (n + 1)).ofIsoObj
    (Scheme.projectiveSpaceOverIsoGrassmannianOverRepresentation n S)

end AlgebraicGeometry

end ExerQuotGeneralization1

section ExerSchemeOfMorphisms

open CategoryTheory AlgebraicGeometry Limits

universe u

/-- Background definition for Exercise 2.4.13 (the implicit definition of the
functor): the **functor of morphisms** `Mor_S(X,Y)`, sending an `S`-scheme `T` to the set
of `T`-morphisms `X_T → Y_T`.

It is rendered here as `T ↦ Hom_{Over S}(X ×_S T, Y)`, the internal hom of the slice
category. That is the book's functor: by the adjunction
`Over.map T.hom ⊣ Over.pullback T.hom` (`Over.mapPullbackAdj`),
`Hom_{Over S}((Over.map T.hom).obj (X_T), Y) ≃ Hom_{Over T}(X_T, Y_T) = Mor_T(X_T, Y_T)`,
and `(Over.map T.hom).obj (X_T)` is the product `X ×_S T` in `Over S`. Rendering it this
way makes the base-change functoriality of `T ↦ Mor_T(X_T, Y_T)` — a pile of pullback
coherence otherwise — literally the functoriality of `yoneda`. The pointwise comparison
with the book's spelling is not itself formalized; see this folder's COMMENTARY.md. -/
noncomputable def AlgebraicGeometry.Scheme.morFunctor {S : Scheme.{u}} (X Y : Over S) :
    (Over S)ᵒᵖ ⥤ Type u :=
  (Limits.prod.functor.obj X).op ⋙ yoneda.obj Y

/-- The points of `Mor_S(X,Y)` over `T` are the `S`-morphisms `X ×_S T → Y`. -/
@[simp]
theorem AlgebraicGeometry.Scheme.morFunctor_obj {S : Scheme.{u}} (X Y T : Over S) :
    (Scheme.morFunctor X Y).obj (.op T) = (X ⨯ T ⟶ Y) :=
  rfl

/- Deferred Exercise 2.4.13 (high-confidence erratum): the
printed projectivity conclusion is false. For `X = Y = ℙ¹` over a field, the locus of
degree-`d > 0` endomorphisms is the open subset of the projective space of pairs of
degree-`d` binary forms on which the resultant is nonzero; it is not proper. Allowing all
degrees also makes the full morphism functor an infinite union of such loci.

The graph construction therefore gives an open locus in suitable Hilbert schemes, not a
closed projective subscheme. Standard corrected conclusions assert representability by a
scheme locally of finite type (with fixed graph-Hilbert-polynomial pieces
quasi-projective), under suitable hypotheses. The easy, faithful part of the exercise—the
definition of `morFunctor` and its points—is formalized above; no false theorem is asserted.
-/

end ExerSchemeOfMorphisms

#min_imports
