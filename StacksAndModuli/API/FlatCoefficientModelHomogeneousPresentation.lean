module

public import StacksAndModuli.API.FlatCoefficientModelGradedCechBridge
public import StacksAndModuli.API.ProjectiveGradedHomogeneousMatrix
public import StacksAndModuli.API.ProjectiveGradedTotalCoker
public import StacksAndModuli.API.ProjectiveGradedTwistedFreeTotal

/-!
# Homogeneous presentations of flat coefficient models

An ordinary `FlatCoefficientModel` remembers a descended polynomial relation matrix, but
forgets the grading from which that matrix came.  This file isolates the exact extra data
needed to restore the grading: a morphism of graded modules whose total range becomes the
range of the descended matrix, together with the graded comparison after coefficient base
change.

The total-module comparison is then automatic.  It is the composite of
`GradedModule.Total.cokerLinearEquiv` with transport of a quotient along the chosen total
equivalence.  Consequently homogeneous presentation data produces the
`NoetherianFlatPolynomialModel.HasGradedRealization` input used by the noetherian Čech
model API.

Main declarations:

* `FlatCoefficientModel.HomogeneousCokernelPresentation`;
* `FlatCoefficientModel.BasedHomogeneousPresentation`;
* `FlatCoefficientModel.ShiftedFreeHomogeneousPresentation`;
* `FlatCoefficientModel.ShiftedFreeHomogeneousPresentation.ofHomogeneousMatrix`;
* `FlatCoefficientModel.HomogeneousCokernelPresentation.modelTotalEquiv`;
* `FlatCoefficientModel.HomogeneousCokernelPresentation.toHasGradedRealization`;
* `FlatCoefficientModel.HomogeneousCokernelPresentation.exists_eventual_noetherianCechModel`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u v w

namespace Module.FinitePresentation.PolynomialModel.FlatCoefficientModel

open CategoryTheory
open AlgebraicGeometry.ProjectiveSpace

variable {R : Type w} {A : Type u} [CommRing R] [IsNoetherianRing R]
variable [CommRing A] [Algebra R A] {n : ℕ}
variable (M : GradedModule A n)
variable {D : PolynomialModel A (Fin (n + 1)) M.Total}
variable (E : FlatCoefficientModel (R := R) D)

/-- Homogeneous cokernel data realizing the relation matrix of a flat coefficient model.

The `relationRange` field is deliberately stated at the level used by the ordinary matrix
cokernel: changing the relation source or its basis does not change the presented module.
The `baseChangeIso` field is the remaining genuinely graded compatibility datum.  It cannot
be recovered from the ordinary polynomial-module base-change equivalence, since an
ungraded equivalence of total modules need not preserve homogeneous pieces or variable
actions degree by degree. -/
structure HomogeneousCokernelPresentation where
  /-- The graded source of homogeneous relations. -/
  relations : GradedModule E.coefficientRing n
  /-- The graded module of generators. -/
  generators : GradedModule E.coefficientRing n
  /-- The homogeneous relation morphism. -/
  relation : relations ⟶ generators
  /-- A polynomial-linear basis comparison for the total generator module. -/
  generatorTotalEquiv :
    generators.Total ≃ₗ[MvPolynomial (Fin (n + 1)) E.coefficientRing]
      (Fin D.generators → MvPolynomial (Fin (n + 1)) E.coefficientRing)
  /-- Under the generator comparison, homogeneous relations span exactly the descended
  matrix relations. -/
  relationRange :
    (LinearMap.range (GradedModule.Total.map relation)).map
        generatorTotalEquiv.toLinearMap =
      LinearMap.range (Matrix.toLin' E.relation)
  /-- After coefficient change, the degreewise cokernel is the original graded module. -/
  baseChangeIso : Nonempty ((GradedModule.coker relation).baseChange A ≅ M)

/-- A homogeneous presentation equipped with polynomial bases on the total source and
target.

This is the exact matrix-level boundary for grading the relation matrix of a flat
coefficient model.  Finite sums of shifted free modules fit here by supplying their total
basis equivalences; the one equation `totalRelation` then records both homogeneity and the
chosen source and target shifts. -/
structure BasedHomogeneousPresentation where
  /-- The graded source of homogeneous relations. -/
  relations : GradedModule E.coefficientRing n
  /-- The graded module of generators. -/
  generators : GradedModule E.coefficientRing n
  /-- The homogeneous relation morphism. -/
  relation : relations ⟶ generators
  /-- A polynomial basis of the total relation module. -/
  relationTotalEquiv :
    relations.Total ≃ₗ[MvPolynomial (Fin (n + 1)) E.coefficientRing]
      (Fin D.relations → MvPolynomial (Fin (n + 1)) E.coefficientRing)
  /-- A polynomial basis of the total generator module. -/
  generatorTotalEquiv :
    generators.Total ≃ₗ[MvPolynomial (Fin (n + 1)) E.coefficientRing]
      (Fin D.generators → MvPolynomial (Fin (n + 1)) E.coefficientRing)
  /-- In the chosen total bases, the homogeneous map is the descended relation matrix. -/
  totalRelation :
    generatorTotalEquiv.toLinearMap.comp (GradedModule.Total.map relation) =
      (Matrix.toLin' E.relation).comp relationTotalEquiv.toLinearMap
  /-- After coefficient change, the degreewise cokernel is the original graded module. -/
  baseChangeIso : Nonempty ((GradedModule.coker relation).baseChange A ≅ M)

namespace BasedHomogeneousPresentation

omit [IsNoetherianRing R] in
/-- Conjugacy of the total relation map with the descended matrix implies equality of their
relation submodules. -/
lemma relationRange (H : BasedHomogeneousPresentation M E) :
    (LinearMap.range (GradedModule.Total.map H.relation)).map
        H.generatorTotalEquiv.toLinearMap =
      LinearMap.range (Matrix.toLin' E.relation) := by
  rw [← LinearMap.range_comp, H.totalRelation]
  apply LinearMap.range_comp_of_range_eq_top
  exact LinearEquiv.range _

/-- Forgetting the basis of the relation source retains the homogeneous cokernel
presentation. -/
noncomputable def toHomogeneousCokernelPresentation
    (H : BasedHomogeneousPresentation M E) :
    HomogeneousCokernelPresentation M E where
  relations := H.relations
  generators := H.generators
  relation := H.relation
  generatorTotalEquiv := H.generatorTotalEquiv
  relationRange := H.relationRange
  baseChangeIso := H.baseChangeIso

end BasedHomogeneousPresentation

/-- Shifted-free homogeneous presentation data for the relation matrix of a flat coefficient
model.

The two shifts use the convention of `GradedModule.Total.shiftedFree`: its basis vectors
have degrees equal to the negatives of the recorded shifts.  The `totalRelation` equation
is the concrete compatibility one obtains by descending homogeneous matrix entries. -/
structure ShiftedFreeHomogeneousPresentation where
  /-- The common shift of the relation basis. -/
  relationShift : ℤ
  /-- The common shift of the generator basis. -/
  generatorShift : ℤ
  /-- The descended homogeneous map between the shifted-free modules. -/
  relation :
    GradedModule.Total.shiftedFree E.coefficientRing n D.relations relationShift ⟶
      GradedModule.Total.shiftedFree E.coefficientRing n D.generators generatorShift
  /-- In the standard total bases, the homogeneous map is the descended relation matrix. -/
  totalRelation :
    (GradedModule.Total.shiftedFreeLinearEquiv
        (R := E.coefficientRing) (n := n) generatorShift).symm.toLinearMap.comp
        (GradedModule.Total.map relation) =
      (Matrix.toLin' E.relation).comp
        (GradedModule.Total.shiftedFreeLinearEquiv
          (R := E.coefficientRing) (n := n) relationShift).symm.toLinearMap
  /-- After coefficient change, the degreewise cokernel is the original graded module. -/
  baseChangeIso : Nonempty ((GradedModule.coker relation).baseChange A ≅ M)

namespace ShiftedFreeHomogeneousPresentation

/-- A uniformly homogeneous relation matrix, together with the genuinely graded
base-change comparison for its cokernel, gives a shifted-free homogeneous presentation.

The graded morphism and its total-map conjugacy are constructed automatically from the
matrix; callers need not supply either piece of bookkeeping. -/
noncomputable def ofHomogeneousMatrix
    (degree : ℕ)
    (hhomogeneous : ∀ i j,
      E.relation i j ∈ GradedModule.polySubmodule E.coefficientRing n degree)
    (hbaseChange : Nonempty
      ((GradedModule.coker
        (GradedModule.Total.homogeneousMatrixHom E.relation hhomogeneous)).baseChange A ≅
          M)) :
    ShiftedFreeHomogeneousPresentation M E where
  relationShift := -(degree : ℤ)
  generatorShift := 0
  relation := GradedModule.Total.homogeneousMatrixHom E.relation hhomogeneous
  totalRelation :=
    GradedModule.Total.homogeneousMatrixHom_totalRelation E.relation hhomogeneous
  baseChangeIso := hbaseChange

omit [IsNoetherianRing R] in
/-- The concrete shifted-free compatibility equation implies equality of the two ordinary
relation submodules. -/
lemma relationRange (H : ShiftedFreeHomogeneousPresentation M E) :
    (LinearMap.range (GradedModule.Total.map H.relation)).map
        (GradedModule.Total.shiftedFreeLinearEquiv
          (R := E.coefficientRing) (n := n) H.generatorShift).symm.toLinearMap =
      LinearMap.range (Matrix.toLin' E.relation) := by
  rw [← LinearMap.range_comp, H.totalRelation]
  apply LinearMap.range_comp_of_range_eq_top
  exact LinearEquiv.range _

/-- The canonical total bases turn a shifted-free presentation into a based homogeneous
presentation. -/
noncomputable def toBasedHomogeneousPresentation
    (H : ShiftedFreeHomogeneousPresentation M E) :
    BasedHomogeneousPresentation M E where
  relations := GradedModule.Total.shiftedFree E.coefficientRing n D.relations H.relationShift
  generators :=
    GradedModule.Total.shiftedFree E.coefficientRing n D.generators H.generatorShift
  relation := H.relation
  relationTotalEquiv :=
    (GradedModule.Total.shiftedFreeLinearEquiv
      (R := E.coefficientRing) (n := n) H.relationShift).symm
  generatorTotalEquiv :=
    (GradedModule.Total.shiftedFreeLinearEquiv
      (R := E.coefficientRing) (n := n) H.generatorShift).symm
  totalRelation := H.totalRelation
  baseChangeIso := H.baseChangeIso

/-- Forgetting the explicit shifted-free bases retains precisely a homogeneous cokernel
presentation. -/
noncomputable def toHomogeneousCokernelPresentation
    (H : ShiftedFreeHomogeneousPresentation M E) :
    HomogeneousCokernelPresentation M E :=
  H.toBasedHomogeneousPresentation.toHomogeneousCokernelPresentation

end ShiftedFreeHomogeneousPresentation

namespace HomogeneousCokernelPresentation

/-- Quotient transport identifies the ordinary cokernel of the homogeneous total relation
map with the polynomial-matrix cokernel in the flat coefficient model. -/
noncomputable def quotientEquiv
    (H : HomogeneousCokernelPresentation M E) :
    (H.generators.Total ⧸ LinearMap.range (GradedModule.Total.map H.relation))
      ≃ₗ[MvPolynomial (Fin (n + 1)) E.coefficientRing] E.modelModule :=
  Submodule.Quotient.equiv _ _ H.generatorTotalEquiv H.relationRange

/-- A homogeneous cokernel presentation supplies the missing compatible grading on the
ordinary polynomial-matrix cokernel. -/
noncomputable def modelTotalEquiv
    (H : HomogeneousCokernelPresentation M E) :
    (GradedModule.coker H.relation).Total
      ≃ₗ[MvPolynomial (Fin (n + 1)) E.coefficientRing] E.modelModule :=
  (GradedModule.Total.cokerLinearEquiv H.relation).symm.trans H.quotientEquiv

/-- Homogeneous cokernel presentation data turns a flat coefficient model into a
noetherian flat polynomial model with a compatible graded realization. -/
theorem toHasGradedRealization
    (H : HomogeneousCokernelPresentation M E) :
    (E.toNoetherianFlatPolynomialModel (R := R)).HasGradedRealization M := by
  letI : IsNoetherianRing E.coefficientRing := E.coefficientRing_isNoetherian
  change ∃ N : GradedModule E.coefficientRing n,
    Nonempty
      (N.Total ≃ₗ[MvPolynomial (Fin (n + 1)) E.coefficientRing] E.modelModule) ∧
    Nonempty (N.baseChange A ≅ M)
  refine ⟨GradedModule.coker H.relation, ⟨⟨H.modelTotalEquiv⟩, ?_⟩⟩
  exact H.baseChangeIso

/-- Once the descended presentation is homogeneous, relative Serre vanishing supplies
all sufficiently large noetherian Čech models.  The bound may depend on the model. -/
theorem exists_eventual_noetherianCechModel
    (H : HomogeneousCokernelPresentation M E) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
      Nonempty (GradedModule.NoetherianCechModel M d) := by
  letI : IsNoetherianRing E.coefficientRing := E.coefficientRing_isNoetherian
  exact H.toHasGradedRealization.exists_eventual_noetherianCechModel

end HomogeneousCokernelPresentation

namespace BasedHomogeneousPresentation

/-- A based homogeneous presentation supplies a compatible grading on the flat coefficient
model. -/
theorem toHasGradedRealization
    (H : BasedHomogeneousPresentation M E) :
    (E.toNoetherianFlatPolynomialModel (R := R)).HasGradedRealization M :=
  H.toHomogeneousCokernelPresentation.toHasGradedRealization

/-- A based homogeneous presentation supplies noetherian Čech models in every sufficiently
large twist. -/
theorem exists_eventual_noetherianCechModel
    (H : BasedHomogeneousPresentation M E) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
      Nonempty (GradedModule.NoetherianCechModel M d) :=
  H.toHomogeneousCokernelPresentation.exists_eventual_noetherianCechModel

end BasedHomogeneousPresentation

namespace ShiftedFreeHomogeneousPresentation

/-- Shifted-free homogeneous presentation data supplies a compatible grading on the flat
coefficient model. -/
theorem toHasGradedRealization
    (H : ShiftedFreeHomogeneousPresentation M E) :
    (E.toNoetherianFlatPolynomialModel (R := R)).HasGradedRealization M :=
  H.toHomogeneousCokernelPresentation.toHasGradedRealization

/-- Shifted-free homogeneous presentation data supplies noetherian Čech models in every
sufficiently large twist. -/
theorem exists_eventual_noetherianCechModel
    (H : ShiftedFreeHomogeneousPresentation M E) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
      Nonempty (GradedModule.NoetherianCechModel M d) :=
  H.toHomogeneousCokernelPresentation.exists_eventual_noetherianCechModel

end ShiftedFreeHomogeneousPresentation

end Module.FinitePresentation.PolynomialModel.FlatCoefficientModel

end

end
