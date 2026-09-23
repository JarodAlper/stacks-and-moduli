module

public import StacksAndModuli.API.ProjectiveFlatteningUniversalFamily
public import StacksAndModuli.API.RepresentableByTransport

/-!
# Base change of projective flattening loci

The fixed-Hilbert-polynomial flattening condition commutes with arbitrary base
change.  This file records that fact as a natural isomorphism of functors and
uses the slice adjunction `Over.map f ⊣ Over.pullback f` to transport a
representing immersion.

The resulting `ProjectiveFlatteningLocusWitness` is deliberately weaker than
`ProjectiveFlatteningHasFiniteRankPresentation`: it remembers the represented
flattening locus and its immersion into the base, but not a particular list of
finite module rank conditions.  Unlike the latter presentation, this geometric
witness has a formal arbitrary-base-change operation.

Main declarations:

* `projectiveFamilyAtBaseChangeIso`;
* `projectiveFlatteningFunctorBaseChangeIso`;
* `ProjectiveFlatteningLocusWitness` and its `baseChange` operation;
* `projectiveFlatteningFunctorIsoOfSheafIso` and
  `ProjectiveFlatteningLocusWitness.ofSheafIso`;
* `ProjectiveFlatteningLocusWitness.baseChangeOfIso`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

variable {T T' : Scheme.{u}} (n : ℕ)
variable (Q : (Scheme.projectiveSpaceOver n T).Modules)

/-- Pulling a projective family first to `T'` and then to a test scheme over
`T'` agrees with pulling it directly from `T`. -/
noncomputable def projectiveFamilyAtBaseChangeIso
    (f : T' ⟶ T) (A : Over T') :
    projectiveFamilyAt n
        ((Scheme.Modules.pullback (Scheme.projectiveSpaceOverMap n f)).obj Q) A ≅
      projectiveFamilyAt n Q ((Over.map f).obj A) := by
  let g : (Over.map f).obj A ⟶ Over.mk f := Over.homMk A.hom rfl
  exact projectiveFamilyPullbackIso n Q g

variable [Q.IsQuasicoherent] (P : Polynomial ℚ)

/-- The flat, fixed-Hilbert-polynomial condition for a base-changed projective
family is the restriction of the original flattening functor along
`Over.map f`. -/
noncomputable def projectiveFlatteningFunctorBaseChangeIso
    (f : T' ⟶ T) :
    projectiveFlatteningFunctor n
        ((Scheme.Modules.pullback (Scheme.projectiveSpaceOverMap n f)).obj Q) (P := P) ≅
      (Over.map f).op ⋙ projectiveFlatteningFunctor n Q (P := P) where
  hom :=
    { app := fun A ↦ ↾fun h ↦ by
        let e := projectiveFamilyAtBaseChangeIso n Q f A.unop
        exact ⟨⟨
          FlatOver.of_iso e h.down.down.1,
          Scheme.HasFiberwiseHilbertPolynomial.of_iso e h.down.down.2
        ⟩⟩
      naturality := by
        intro A B g
        apply ConcreteCategory.hom_ext
        intro x
        exact (projectiveFlatteningFunctor_subsingleton n Q P
          ((Over.map f).op.obj B)).elim _ _ }
  inv :=
    { app := fun A ↦ ↾fun h ↦ by
        let e := projectiveFamilyAtBaseChangeIso n Q f A.unop
        exact ⟨⟨
          FlatOver.of_iso e.symm h.down.down.1,
          Scheme.HasFiberwiseHilbertPolynomial.of_iso e.symm h.down.down.2
        ⟩⟩
      naturality := by
        intro A B g
        apply ConcreteCategory.hom_ext
        intro x
        exact (projectiveFlatteningFunctor_subsingleton n
          ((Scheme.Modules.pullback (Scheme.projectiveSpaceOverMap n f)).obj Q) P B).elim _ _ }
  hom_inv_id := by
    ext A x
    exact (projectiveFlatteningFunctor_subsingleton n
      ((Scheme.Modules.pullback (Scheme.projectiveSpaceOverMap n f)).obj Q) P A).elim _ _
  inv_hom_id := by
    ext A x
    exact (projectiveFlatteningFunctor_subsingleton n Q P
      ((Over.map f).op.obj A)).elim _ _

/-- A represented projective flattening locus together with the fact that its
structure map is an immersion.  This is the geometric output of a finite-rank
presentation, separated from the chosen finite list presenting it. -/
structure ProjectiveFlatteningLocusWitness where
  /-- The scheme over the base representing the flattening condition. -/
  representative : Over T
  /-- The representation of the flat, fixed-Hilbert-polynomial functor. -/
  representableBy :
    (projectiveFlatteningFunctor n Q (P := P)).RepresentableBy representative
  /-- The flattening locus is immersed in the base. -/
  representative_hom_isImmersion : IsImmersion representative.hom

namespace ProjectiveFlatteningLocusWitness

/-- A finite-rank presentation gives its represented immersed flattening
locus. -/
noncomputable def ofFiniteRankPresentation
    (h : ProjectiveFlatteningHasFiniteRankPresentation n Q (P := P)) :
    ProjectiveFlatteningLocusWitness n Q P where
  representative := projectiveFlatteningRepresentative n Q (P := P) h
  representableBy := projectiveFlatteningRepresentableBy n Q (P := P) h
  representative_hom_isImmersion :=
    projectiveFlatteningRepresentative_hom_isImmersion n Q (P := P) h

/-- A represented immersed projective flattening locus pulls back along an
arbitrary morphism of base schemes. -/
noncomputable def baseChange
    (D : ProjectiveFlatteningLocusWitness n Q P)
    (f : T' ⟶ T) :
    ProjectiveFlatteningLocusWitness n
      ((Scheme.Modules.pullback (Scheme.projectiveSpaceOverMap n f)).obj Q) P where
  representative := (Over.pullback f).obj D.representative
  representableBy :=
    ((Over.mapPullbackAdj f).compRepresentableBy D.representableBy).ofIso
      (projectiveFlatteningFunctorBaseChangeIso n Q P f).symm
  representative_hom_isImmersion := by
    letI : IsImmersion D.representative.hom :=
      D.representative_hom_isImmersion
    dsimp only [Over.pullback_obj_hom]
    infer_instance

end ProjectiveFlatteningLocusWitness

/-- Projective flattening functors are invariant under an isomorphism of the
underlying projective families. -/
noncomputable def projectiveFlatteningFunctorIsoOfSheafIso
    {Q' : (Scheme.projectiveSpaceOver n T).Modules} [Q'.IsQuasicoherent]
    (e : Q ≅ Q') :
    projectiveFlatteningFunctor n Q (P := P) ≅
      projectiveFlatteningFunctor n Q' (P := P) where
  hom :=
    { app := fun A ↦ ↾fun h ↦ by
        let eA := (Scheme.Modules.pullback
          (Scheme.projectiveSpaceOverMap n A.unop.hom)).mapIso e
        exact ⟨⟨
          FlatOver.of_iso eA h.down.down.1,
          Scheme.HasFiberwiseHilbertPolynomial.of_iso eA h.down.down.2
        ⟩⟩
      naturality := by
        intro A B g
        apply ConcreteCategory.hom_ext
        intro x
        exact (projectiveFlatteningFunctor_subsingleton n Q' P B).elim _ _ }
  inv :=
    { app := fun A ↦ ↾fun h ↦ by
        let eA := (Scheme.Modules.pullback
          (Scheme.projectiveSpaceOverMap n A.unop.hom)).mapIso e
        exact ⟨⟨
          FlatOver.of_iso eA.symm h.down.down.1,
          Scheme.HasFiberwiseHilbertPolynomial.of_iso eA.symm h.down.down.2
        ⟩⟩
      naturality := by
        intro A B g
        apply ConcreteCategory.hom_ext
        intro x
        exact (projectiveFlatteningFunctor_subsingleton n Q P B).elim _ _ }
  hom_inv_id := by
    ext A x
    exact (projectiveFlatteningFunctor_subsingleton n Q P A).elim _ _
  inv_hom_id := by
    ext A x
    exact (projectiveFlatteningFunctor_subsingleton n Q' P A).elim _ _

namespace ProjectiveFlatteningLocusWitness

/-- Transport a represented immersed projective flattening locus across an
isomorphism of projective families. -/
noncomputable def ofSheafIso
    (D : ProjectiveFlatteningLocusWitness n Q P)
    {Q' : (Scheme.projectiveSpaceOver n T).Modules} [Q'.IsQuasicoherent]
    (e : Q ≅ Q') : ProjectiveFlatteningLocusWitness n Q' P where
  representative := D.representative
  representableBy := D.representableBy.ofIso
    (projectiveFlatteningFunctorIsoOfSheafIso n Q P e)
  representative_hom_isImmersion := D.representative_hom_isImmersion

/-- Pull back a represented immersed projective flattening locus and then
transport it across an isomorphism with the desired projective family. -/
noncomputable def baseChangeOfIso
    (D : ProjectiveFlatteningLocusWitness n Q P)
    {T' : Scheme.{u}} (f : T' ⟶ T)
    {Q' : (Scheme.projectiveSpaceOver n T').Modules} [Q'.IsQuasicoherent]
    (e : (Scheme.Modules.pullback
      (Scheme.projectiveSpaceOverMap n f)).obj Q ≅ Q') :
    ProjectiveFlatteningLocusWitness n Q' P :=
  ofSheafIso n
    ((Scheme.Modules.pullback
      (Scheme.projectiveSpaceOverMap n f)).obj Q) P
    ((baseChange n Q P D f) :
      ProjectiveFlatteningLocusWitness n
        ((Scheme.Modules.pullback
          (Scheme.projectiveSpaceOverMap n f)).obj Q) P)
    e

end ProjectiveFlatteningLocusWitness

end AlgebraicGeometry.Scheme.Modules

end

end
