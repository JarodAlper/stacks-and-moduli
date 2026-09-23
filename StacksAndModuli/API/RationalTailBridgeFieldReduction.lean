module

public import StacksAndModuli.API.FiniteEtaleRankTwo
public import StacksAndModuli.API.FiniteSeparableSplitNodeLift
public import StacksAndModuli.API.GenusZeroCurveClassificationReduction
public import StacksAndModuli.API.ProperIntegralGlobalSections
public import StacksAndModuli.API.SplitNodeResidueField
public import StacksAndModuli.API.SmoothStalkReduced
public import StacksAndModuli.API.SurjectiveOnStalksResidueField
public import StacksAndModuli.«Section6.3-Stable».«part6.3.4-rational-tails-and-bridges»

/-!
# Field-theoretic reductions for rational tails and bridges

This file develops reusable consequences of
`AlgebraicGeometry.Scheme.SmoothGenusZeroSubcurveOver`.  Smoothness and irreducibility
make the subcurve integral; a closed immersion into a proper ambient curve makes it
proper.  Its global constants are consequently a finite field extension of the ground
field.

For a rational tail, the defining bijective evaluation map is promoted to a ring
equivalence, and to an algebra equivalence for the canonical algebra structure it induces
on the residue field.  This transfers finite-dimensionality and separability.  For the
degree-two case of a rational bridge, the remaining algebraic hypothesis is isolated
exactly as étaleness of the intersection algebra; under that hypothesis the algebra is
either a separable quadratic field or the split algebra.

## Main results

* `SmoothGenusZeroSubcurveOver.curve_isIntegral`;
* `SmoothGenusZeroSubcurveOver.curve_isProper`;
* `SmoothGenusZeroSubcurveOver.globalSections_isField_of_ambient_isProper`;
* `SmoothGenusZeroSubcurveOver.globalSections_finiteDimensional_of_ambient_isProper`;
* `SmoothGenusZeroSubcurveOver.
  globalSections_isSeparable_of_ambient_isProper_of_perfectField`;
* `SmoothGenusZeroSubcurveOver.globalSectionsResidueFieldAlgEquiv`;
* `SmoothGenusZeroSubcurveOver.IsRationalTail.exists_globalSectionsResidueFieldRingEquiv`;
* `SmoothGenusZeroSubcurveOver.IsRationalTail.
  exists_finiteSeparable_residueField_of_perfectField`;
* `SmoothGenusZeroSubcurveOver.globalSectionsAlgEquiv_of_splitNodeAt`;
* `SmoothGenusZeroSubcurveOver.
  globalSections_finiteSeparable_of_finiteSeparableSplitNodeLiftAt`;
* `SmoothGenusZeroSubcurveOver.IsRationalTail.
  exists_globalSectionsAlgEquiv_of_attaching_splitNode`;
* `SmoothGenusZeroSubcurveOver.IsRationalBridge.
  intersectionDegree_eq_two_of_containsNoMarkedPoints`;
* `SmoothGenusZeroSubcurveOver.intersection_isQuadraticOrSplit_of_degree_two`;
* `SmoothGenusZeroSubcurveOver.projectiveLineIso_of_pointedClassification`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Scheme

namespace SmoothGenusZeroSubcurveOver

variable {k : Type u} [Field k] {C : Scheme.{u}}
  [C.Over (Spec (CommRingCat.of k))]

/-- A smooth genus-zero subcurve is reduced. -/
theorem curve_isReduced (E : SmoothGenusZeroSubcurveOver k C) :
    IsReduced E.curve.left := by
  let _ : Smooth E.curve.hom := E.smooth
  exact isReduced_of_smooth_toSpec_field E.curve.hom

/-- A smooth irreducible genus-zero subcurve is integral. -/
theorem curve_isIntegral (E : SmoothGenusZeroSubcurveOver k C) :
    IsIntegral E.curve.left := by
  let _ : Smooth E.curve.hom := E.smooth
  let _ : IrreducibleSpace E.curve.left := E.irreducible
  exact isIntegral_of_smooth_toSpec_field_of_irreducible E.curve.hom

/-- A closed subcurve of a proper scheme over the ground field is proper. -/
theorem curve_isProper (E : SmoothGenusZeroSubcurveOver k C)
    [IsProper (C ↘ Spec (CommRingCat.of k))] :
    IsProper E.curve.hom := by
  let _ : IsClosedImmersion E.ι.left := E.isClosedImmersion
  have h : IsProper (E.ι.left ≫ (C ↘ Spec (CommRingCat.of k))) := by
    infer_instance
  have hw : E.ι.left ≫ (C ↘ Spec (CommRingCat.of k)) = E.curve.hom :=
    E.ι.w
  rw [hw] at h
  exact h

/-- The global constants of a smooth genus-zero subcurve of a proper ambient scheme
form a field. -/
theorem globalSections_isField_of_ambient_isProper
    (E : SmoothGenusZeroSubcurveOver k C)
    [IsProper (C ↘ Spec (CommRingCat.of k))] :
    IsField Γ(E.curve.left, ⊤) := by
  let _ : IsIntegral E.curve.left := E.curve_isIntegral
  let _ : IsProper (E.curve.left ↘ Spec (CommRingCat.of k)) :=
    E.curve_isProper
  exact Scheme.isField_globalSections k E.curve.left

/-- The global constants of a smooth genus-zero subcurve of a proper ambient scheme
are finite-dimensional over the ground field. -/
theorem globalSections_finiteDimensional_of_ambient_isProper
    (E : SmoothGenusZeroSubcurveOver k C)
    [IsProper (C ↘ Spec (CommRingCat.of k))] :
    FiniteDimensional k Γ(E.curve.left, ⊤) := by
  let _ : IsIntegral E.curve.left := E.curve_isIntegral
  let _ : IsProper (E.curve.left ↘ Spec (CommRingCat.of k)) :=
    E.curve_isProper
  exact finiteDimensional_globalSections_of_isIntegral_of_proper k E.curve.left

/-- Over a perfect ground field, the global constants of a smooth genus-zero
subcurve in a proper ambient scheme form a finite separable field extension. -/
theorem globalSections_isSeparable_of_ambient_isProper_of_perfectField
    (E : SmoothGenusZeroSubcurveOver k C) [PerfectField k]
    [IsProper (C ↘ Spec (CommRingCat.of k))] :
    letI : Field Γ(E.curve.left, ⊤) :=
      E.globalSections_isField_of_ambient_isProper.toField
    Algebra.IsSeparable k Γ(E.curve.left, ⊤) := by
  let _ : Field Γ(E.curve.left, ⊤) :=
    E.globalSections_isField_of_ambient_isProper.toField
  let _ : FiniteDimensional k Γ(E.curve.left, ⊤) :=
    E.globalSections_finiteDimensional_of_ambient_isProper
  infer_instance

/-- The canonical `k`-algebra structure on `κ(x)` obtained by evaluating global
functions after applying the structural map `k → Γ(E, 𝒪_E)`. -/
@[instance_reducible]
noncomputable def residueFieldAlgebra (E : SmoothGenusZeroSubcurveOver k C)
    (x : E.curve.left) : Algebra k (E.curve.left.residueField x) :=
  ((E.globalSectionsToResidueField x).comp
    (algebraMap k Γ(E.curve.left, ⊤))).toAlgebra

/-- For the evaluation-induced algebra structure on `κ(x)`, its algebra map is the
composite `k → Γ(E, 𝒪_E) → κ(x)`. -/
@[simp]
theorem algebraMap_residueFieldAlgebra
    (E : SmoothGenusZeroSubcurveOver k C) (x : E.curve.left) (a : k) :
    @algebraMap k (E.curve.left.residueField x) _ _
      (E.residueFieldAlgebra x) a =
        E.globalSectionsToResidueField x
          (algebraMap k Γ(E.curve.left, ⊤) a) :=
  rfl

/-- Evaluation at `x` as an algebra homomorphism for any `k`-algebra structure on
`κ(x)` compatible with evaluation of structural constants. -/
noncomputable def globalSectionsToResidueFieldAlgHomOfCompatible
    (E : SmoothGenusZeroSubcurveOver k C) (x : E.curve.left)
    [Algebra k (E.curve.left.residueField x)]
    (hcompat : ∀ a : k,
      E.globalSectionsToResidueField x
          (algebraMap k Γ(E.curve.left, ⊤) a) =
        algebraMap k (E.curve.left.residueField x) a) :
    Γ(E.curve.left, ⊤) →ₐ[k] E.curve.left.residueField x :=
  { E.globalSectionsToResidueField x with
    commutes' := hcompat }

/-- The compatible algebra homomorphism has global evaluation as its underlying
function. -/
@[simp]
theorem globalSectionsToResidueFieldAlgHomOfCompatible_apply
    (E : SmoothGenusZeroSubcurveOver k C) (x : E.curve.left)
    [Algebra k (E.curve.left.residueField x)]
    (hcompat : ∀ a : k,
      E.globalSectionsToResidueField x
          (algebraMap k Γ(E.curve.left, ⊤) a) =
        algebraMap k (E.curve.left.residueField x) a)
    (f : Γ(E.curve.left, ⊤)) :
    E.globalSectionsToResidueFieldAlgHomOfCompatible x hcompat f =
      E.globalSectionsToResidueField x f :=
  rfl

/-- A bijective evaluation map compatible with chosen `k`-algebra structures is an
equivalence of `k`-algebras. -/
noncomputable def globalSectionsResidueFieldAlgEquivOfCompatible
    (E : SmoothGenusZeroSubcurveOver k C) (x : E.curve.left)
    [Algebra k (E.curve.left.residueField x)]
    (hcompat : ∀ a : k,
      E.globalSectionsToResidueField x
          (algebraMap k Γ(E.curve.left, ⊤) a) =
        algebraMap k (E.curve.left.residueField x) a)
    (h : Function.Bijective (E.globalSectionsToResidueField x)) :
    Γ(E.curve.left, ⊤) ≃ₐ[k] E.curve.left.residueField x :=
  AlgEquiv.ofBijective
    (E.globalSectionsToResidueFieldAlgHomOfCompatible x hcompat) h

/-- The compatible algebra equivalence has global evaluation as its underlying
function. -/
@[simp]
theorem globalSectionsResidueFieldAlgEquivOfCompatible_apply
    (E : SmoothGenusZeroSubcurveOver k C) (x : E.curve.left)
    [Algebra k (E.curve.left.residueField x)]
    (hcompat : ∀ a : k,
      E.globalSectionsToResidueField x
          (algebraMap k Γ(E.curve.left, ⊤) a) =
        algebraMap k (E.curve.left.residueField x) a)
    (h : Function.Bijective (E.globalSectionsToResidueField x))
    (f : Γ(E.curve.left, ⊤)) :
    E.globalSectionsResidueFieldAlgEquivOfCompatible x hcompat h f =
      E.globalSectionsToResidueField x f :=
  rfl

/-- Evaluation at `x` as an algebra homomorphism, using its canonical induced
`k`-algebra structure on the residue field. -/
noncomputable def globalSectionsToResidueFieldAlgHom
    (E : SmoothGenusZeroSubcurveOver k C) (x : E.curve.left) :
    letI := E.residueFieldAlgebra x
    Γ(E.curve.left, ⊤) →ₐ[k] E.curve.left.residueField x := by
  letI := E.residueFieldAlgebra x
  exact
    { E.globalSectionsToResidueField x with
      commutes' := fun _ ↦ rfl }

/-- A bijective global evaluation map is canonically an equivalence of rings. -/
noncomputable def globalSectionsResidueFieldRingEquiv
    (E : SmoothGenusZeroSubcurveOver k C) (x : E.curve.left)
    (h : Function.Bijective (E.globalSectionsToResidueField x)) :
    Γ(E.curve.left, ⊤) ≃+* E.curve.left.residueField x :=
  RingEquiv.ofBijective (E.globalSectionsToResidueField x) h

/-- The ring equivalence obtained from a bijective evaluation has evaluation as its
underlying function. -/
@[simp]
theorem globalSectionsResidueFieldRingEquiv_apply
    (E : SmoothGenusZeroSubcurveOver k C) (x : E.curve.left)
    (h : Function.Bijective (E.globalSectionsToResidueField x))
    (f : Γ(E.curve.left, ⊤)) :
    E.globalSectionsResidueFieldRingEquiv x h f =
      E.globalSectionsToResidueField x f :=
  rfl

/-- A bijective global evaluation map is canonically an equivalence of `k`-algebras
for the evaluation-induced algebra structure on the residue field. -/
noncomputable def globalSectionsResidueFieldAlgEquiv
    (E : SmoothGenusZeroSubcurveOver k C) (x : E.curve.left)
    (h : Function.Bijective (E.globalSectionsToResidueField x)) :
    letI := E.residueFieldAlgebra x
    Γ(E.curve.left, ⊤) ≃ₐ[k] E.curve.left.residueField x := by
  letI := E.residueFieldAlgebra x
  exact AlgEquiv.ofBijective (E.globalSectionsToResidueFieldAlgHom x) h

/-- The algebra equivalence obtained from a bijective evaluation has the original
evaluation map as its underlying function. -/
@[simp]
theorem globalSectionsResidueFieldAlgEquiv_apply
    (E : SmoothGenusZeroSubcurveOver k C) (x : E.curve.left)
    (h : Function.Bijective (E.globalSectionsToResidueField x))
    (a : Γ(E.curve.left, ⊤)) :
    letI := E.residueFieldAlgebra x
    E.globalSectionsResidueFieldAlgEquiv x h a =
      E.globalSectionsToResidueField x a := by
  rfl

/-- Finite-dimensionality transfers across a bijective evaluation compatible with
chosen `k`-algebra structures. -/
theorem residueField_finiteDimensional_of_bijective_of_compatible
    (E : SmoothGenusZeroSubcurveOver k C) (x : E.curve.left)
    [Algebra k (E.curve.left.residueField x)]
    (hcompat : ∀ a : k,
      E.globalSectionsToResidueField x
          (algebraMap k Γ(E.curve.left, ⊤) a) =
        algebraMap k (E.curve.left.residueField x) a)
    (h : Function.Bijective (E.globalSectionsToResidueField x))
    [FiniteDimensional k Γ(E.curve.left, ⊤)] :
    FiniteDimensional k (E.curve.left.residueField x) :=
  Module.Finite.equiv
    (E.globalSectionsResidueFieldAlgEquivOfCompatible x hcompat h).toLinearEquiv

/-- Separability transfers across a bijective evaluation compatible with chosen
`k`-algebra structures. -/
theorem residueField_isSeparable_of_bijective_of_compatible
    (E : SmoothGenusZeroSubcurveOver k C) (x : E.curve.left)
    [Algebra k (E.curve.left.residueField x)]
    (hcompat : ∀ a : k,
      E.globalSectionsToResidueField x
          (algebraMap k Γ(E.curve.left, ⊤) a) =
        algebraMap k (E.curve.left.residueField x) a)
    (h : Function.Bijective (E.globalSectionsToResidueField x))
    [Algebra.IsSeparable k Γ(E.curve.left, ⊤)] :
    Algebra.IsSeparable k (E.curve.left.residueField x) :=
  AlgEquiv.Algebra.isSeparable
    (E.globalSectionsResidueFieldAlgEquivOfCompatible x hcompat h)

/-- A rational tail supplies a point at which global evaluation is a ring
equivalence, together with the defining reduced-intersection and marking conditions. -/
theorem IsRationalTail.exists_globalSectionsResidueFieldRingEquiv {I : Type v}
    (E : SmoothGenusZeroSubcurveOver k C)
    (p : I → C.SectionOver (Spec (CommRingCat.of k)))
    (h : E.IsRationalTail p) :
    ∃ x : E.curve.left,
      E.IsSingleReducedIntersectionAt x ∧
        E.ContainsNoMarkedPoints p ∧
          Nonempty (Γ(E.curve.left, ⊤) ≃+* E.curve.left.residueField x) := by
  obtain ⟨x, hx, heval, hmarks⟩ := h.2
  exact ⟨x, hx, hmarks, ⟨E.globalSectionsResidueFieldRingEquiv x heval⟩⟩

/-- A rational tail supplies an algebra equivalence between its global constants and
the residue field at its attaching point, using the canonical evaluation-induced
algebra structure. -/
theorem IsRationalTail.exists_globalSectionsResidueFieldAlgEquiv {I : Type v}
    (E : SmoothGenusZeroSubcurveOver k C)
    (p : I → C.SectionOver (Spec (CommRingCat.of k)))
    (h : E.IsRationalTail p) :
    ∃ x : E.curve.left,
      E.IsSingleReducedIntersectionAt x ∧
        E.ContainsNoMarkedPoints p ∧
          letI := E.residueFieldAlgebra x
          Nonempty
            (Γ(E.curve.left, ⊤) ≃ₐ[k] E.curve.left.residueField x) := by
  obtain ⟨x, hx, heval, hmarks⟩ := h.2
  refine ⟨x, hx, hmarks, ?_⟩
  exact ⟨E.globalSectionsResidueFieldAlgEquiv x heval⟩

/-- A bijective evaluation transfers finite-dimensionality from global constants to
the residue field, for the canonical evaluation-induced algebra structure. -/
theorem residueField_finiteDimensional_of_bijective
    (E : SmoothGenusZeroSubcurveOver k C) (x : E.curve.left)
    (h : Function.Bijective (E.globalSectionsToResidueField x))
    [FiniteDimensional k Γ(E.curve.left, ⊤)] :
    letI := E.residueFieldAlgebra x
    FiniteDimensional k (E.curve.left.residueField x) := by
  let _ := E.residueFieldAlgebra x
  exact Module.Finite.equiv (E.globalSectionsResidueFieldAlgEquiv x h).toLinearEquiv

/-- A bijective evaluation transfers separability from global constants to the
residue field, for the canonical evaluation-induced algebra structure. -/
theorem residueField_isSeparable_of_bijective
    (E : SmoothGenusZeroSubcurveOver k C) (x : E.curve.left)
    (h : Function.Bijective (E.globalSectionsToResidueField x))
    [Algebra.IsSeparable k Γ(E.curve.left, ⊤)] :
    letI := E.residueFieldAlgebra x
    Algebra.IsSeparable k (E.curve.left.residueField x) := by
  let _ := E.residueFieldAlgebra x
  exact AlgEquiv.Algebra.isSeparable
    (E.globalSectionsResidueFieldAlgEquiv x h)

/-- In a proper ambient scheme, a rational tail has a finite residue-field extension
at its attaching point, for the evaluation-induced `k`-algebra structure. -/
theorem IsRationalTail.exists_finiteDimensional_residueField {I : Type v}
    (E : SmoothGenusZeroSubcurveOver k C)
    (p : I → C.SectionOver (Spec (CommRingCat.of k)))
    [IsProper (C ↘ Spec (CommRingCat.of k))]
    (h : E.IsRationalTail p) :
    ∃ x : E.curve.left,
      E.IsSingleReducedIntersectionAt x ∧
        E.ContainsNoMarkedPoints p ∧
          letI := E.residueFieldAlgebra x
          FiniteDimensional k (E.curve.left.residueField x) := by
  let _ : FiniteDimensional k Γ(E.curve.left, ⊤) :=
    E.globalSections_finiteDimensional_of_ambient_isProper
  obtain ⟨x, hx, heval, hmarks⟩ := h.2
  refine ⟨x, hx, hmarks, ?_⟩
  exact E.residueField_finiteDimensional_of_bijective x heval

/-- In a proper ambient scheme over a perfect field, the attaching residue field of
a rational tail is a finite separable extension of the ground field, for the
evaluation-induced algebra structure. -/
theorem IsRationalTail.exists_finiteSeparable_residueField_of_perfectField
    {I : Type v} (E : SmoothGenusZeroSubcurveOver k C)
    (p : I → C.SectionOver (Spec (CommRingCat.of k))) [PerfectField k]
    [IsProper (C ↘ Spec (CommRingCat.of k))]
    (h : E.IsRationalTail p) :
    ∃ x : E.curve.left,
      E.IsSingleReducedIntersectionAt x ∧
        E.ContainsNoMarkedPoints p ∧
          letI := E.residueFieldAlgebra x
          FiniteDimensional k (E.curve.left.residueField x) ∧
            Algebra.IsSeparable k (E.curve.left.residueField x) := by
  let _ : FiniteDimensional k Γ(E.curve.left, ⊤) :=
    E.globalSections_finiteDimensional_of_ambient_isProper
  obtain ⟨x, hx, heval, hmarks⟩ := h.2
  refine ⟨x, hx, hmarks, ?_⟩
  let _ := E.residueFieldAlgebra x
  let _ : FiniteDimensional k (E.curve.left.residueField x) :=
    E.residueField_finiteDimensional_of_bijective x heval
  exact ⟨inferInstance, inferInstance⟩

/-- The residue-field map of the closed immersion of a smooth genus-zero subcurve,
bundled as an equivalence of algebras over the ground field. -/
noncomputable def ambientResidueFieldAlgEquiv
    (E : SmoothGenusZeroSubcurveOver k C) (x : E.curve.left) :
    letI := _root_.AlgebraicGeometry.Scheme.residueFieldAlgebra
      (C ↘ Spec (CommRingCat.of k)) (E.ι.left x)
    letI := _root_.AlgebraicGeometry.Scheme.residueFieldAlgebra E.curve.hom x
    C.residueField (E.ι.left x) ≃ₐ[k] E.curve.left.residueField x := by
  let _ : IsClosedImmersion E.ι.left := E.isClosedImmersion
  let _ := _root_.AlgebraicGeometry.Scheme.residueFieldAlgebra
    (C ↘ Spec (CommRingCat.of k)) (E.ι.left x)
  let _ := _root_.AlgebraicGeometry.Scheme.residueFieldAlgebra E.curve.hom x
  have hresidue : Function.Bijective
      (E.ι.left.residueFieldMapAlgHomOfCompEq
        (C ↘ Spec (CommRingCat.of k)) E.curve.hom E.ι.w x) := by
    let hclosed := E.ι.left.residueFieldMap_bijective_of_isClosedImmersion x
    constructor
    · intro a b hab
      apply hclosed.1
      exact
        (E.ι.left.residueFieldMapAlgHomOfCompEq_apply
            (C ↘ Spec (CommRingCat.of k)) E.curve.hom E.ι.w x a).symm.trans
          (hab.trans
            (E.ι.left.residueFieldMapAlgHomOfCompEq_apply
              (C ↘ Spec (CommRingCat.of k)) E.curve.hom E.ι.w x b))
    · intro b
      obtain ⟨a, ha⟩ := hclosed.2 b
      refine ⟨a, ?_⟩
      exact
        (E.ι.left.residueFieldMapAlgHomOfCompEq_apply
          (C ↘ Spec (CommRingCat.of k)) E.curve.hom E.ι.w x a).trans ha
  exact AlgEquiv.ofBijective
    (E.ι.left.residueFieldMapAlgHomOfCompEq
      (C ↘ Spec (CommRingCat.of k)) E.curve.hom E.ι.w x)
    hresidue

/-- If evaluation at `x` is bijective and the image of `x` admits a split-node lift
after a finite separable extension, then the global constants of the subcurve are a
finite separable algebra over the ground field. -/
theorem globalSections_finiteSeparable_of_finiteSeparableSplitNodeLiftAt
    (E : SmoothGenusZeroSubcurveOver k C)
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k))]
    (x : E.curve.left)
    (heval : Function.Bijective (E.globalSectionsToResidueField x))
    (hnode : C.HasFiniteSeparableSplitNodeLiftAt k (E.ι.left x)) :
    FiniteDimensional k Γ(E.curve.left, ⊤) ∧
      Algebra.IsSeparable k Γ(E.curve.left, ⊤) := by
  let _ := _root_.AlgebraicGeometry.Scheme.residueFieldAlgebra
    (C ↘ Spec (CommRingCat.of k)) (E.ι.left x)
  let _ := _root_.AlgebraicGeometry.Scheme.residueFieldAlgebra E.curve.hom x
  let _ : FiniteDimensional k (C.residueField (E.ι.left x)) :=
    hnode.residueField_finiteDimensional
  let _ : Algebra.IsSeparable k (C.residueField (E.ι.left x)) :=
    hnode.residueField_isSeparable
  let e : C.residueField (E.ι.left x) ≃ₐ[k] Γ(E.curve.left, ⊤) :=
    (E.ambientResidueFieldAlgEquiv x).trans
      (E.globalSectionsResidueFieldAlgEquivOfCompatible
        x (fun _ ↦ rfl) heval).symm
  exact ⟨Module.Finite.equiv e.toLinearEquiv,
    AlgEquiv.Algebra.isSeparable e⟩

/-- A rational tail whose attaching point admits a finite-separable split-node lift
has finite separable global constants over the ground field. -/
theorem IsRationalTail.globalSections_finiteSeparable_of_attachingNodeLift
    {I : Type v} (E : SmoothGenusZeroSubcurveOver k C)
    (p : I → C.SectionOver (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k))]
    (h : E.IsRationalTail p)
    (hnode : ∀ x, E.IsSingleReducedIntersectionAt x →
      C.HasFiniteSeparableSplitNodeLiftAt k (E.ι.left x)) :
    FiniteDimensional k Γ(E.curve.left, ⊤) ∧
      Algebra.IsSeparable k Γ(E.curve.left, ⊤) := by
  obtain ⟨x, hx, heval, -⟩ := h.2
  exact E.globalSections_finiteSeparable_of_finiteSeparableSplitNodeLiftAt
    x heval (hnode x hx)

/-- If evaluation at `x` is bijective and the image of `x` in the ambient scheme is a
split node, then the global constants of the subcurve are canonically equivalent to the
ground field. The comparison uses that a closed immersion induces an isomorphism on
residue fields. -/
theorem globalSectionsAlgEquiv_of_splitNodeAt
    (E : SmoothGenusZeroSubcurveOver k C) [IsLocallyNoetherian C]
    (x : E.curve.left)
    (heval : Function.Bijective (E.globalSectionsToResidueField x))
    (hnode : C.IsSplitNodeAt k (E.ι.left x)) :
    Nonempty (Γ(E.curve.left, ⊤) ≃ₐ[k] k) := by
  let _ := _root_.AlgebraicGeometry.Scheme.residueFieldAlgebra
    (C ↘ Spec (CommRingCat.of k)) (E.ι.left x)
  let _ := _root_.AlgebraicGeometry.Scheme.residueFieldAlgebra E.curve.hom x
  let eResidue := E.ambientResidueFieldAlgEquiv x
  let eEvaluation : Γ(E.curve.left, ⊤) ≃ₐ[k]
      E.curve.left.residueField x :=
    E.globalSectionsResidueFieldAlgEquivOfCompatible x (fun _ ↦ rfl) heval
  exact ⟨eEvaluation.trans (eResidue.symm.trans hnode.residueFieldAlgEquiv)⟩

/-- A rational tail whose attaching point maps to a split node has global constants
equal to the ground field as a `k`-algebra. -/
theorem IsRationalTail.exists_globalSectionsAlgEquiv_of_attaching_splitNode
    {I : Type v} (E : SmoothGenusZeroSubcurveOver k C)
    (p : I → C.SectionOver (Spec (CommRingCat.of k)))
    [IsLocallyNoetherian C] (h : E.IsRationalTail p)
    (hnode : ∀ x, E.IsSingleReducedIntersectionAt x →
      C.IsSplitNodeAt k (E.ι.left x)) :
    ∃ x : E.curve.left,
      E.IsSingleReducedIntersectionAt x ∧
        E.ContainsNoMarkedPoints p ∧
          Nonempty (Γ(E.curve.left, ⊤) ≃ₐ[k] k) := by
  obtain ⟨x, hx, heval, hmarks⟩ := h.2
  exact ⟨x, hx, hmarks,
    E.globalSectionsAlgEquiv_of_splitNodeAt x heval (hnode x hx)⟩

/-- An unmarked rational bridge lies in the degree-two alternative of the
rational-bridge definition. -/
theorem IsRationalBridge.intersectionDegree_eq_two_of_containsNoMarkedPoints
    {I : Type v} {E : SmoothGenusZeroSubcurveOver k C}
    {p : I → C.SectionOver (Spec (CommRingCat.of k))}
    (hbridge : E.IsRationalBridge p) (hmarks : E.ContainsNoMarkedPoints p) :
    E.intersectionDegree = 2 := by
  rcases hbridge.2 with hdegree | ⟨j, hmark, _⟩
  · exact hdegree.1
  · exact (hmarks j hmark).elim

/-- The degree-two intersection algebra of a rational-bridge candidate is either a
separable quadratic field or the split algebra, provided it is étale over the global
constants field.  Étaleness is the exact algebraic hypothesis not contained in the
definition of `intersectionDegree`. -/
theorem intersection_isQuadraticOrSplit_of_degree_two
    (E : SmoothGenusZeroSubcurveOver k C) {K : Type u} [Field K]
    (e : Γ(E.curve.left, ⊤) ≃+* K)
    (hEtale :
      letI : Algebra K Γ(E.intersection, ⊤) :=
        ((E.intersectionGlobalSectionsMap.comp e.symm.toRingHom)).toAlgebra
      Algebra.Etale K Γ(E.intersection, ⊤))
    (hdegree : E.intersectionDegree = 2) :
    letI : Algebra K Γ(E.intersection, ⊤) :=
      ((E.intersectionGlobalSectionsMap.comp e.symm.toRingHom)).toAlgebra
    (∃ (L : Type u) (_ : Field L) (_ : Algebra K L)
        (_ : Algebra.IsSeparable K L)
        (_ : Algebra.IsQuadraticExtension K L),
        Nonempty (Γ(E.intersection, ⊤) ≃ₐ[K] L)) ∨
      Nonempty (Γ(E.intersection, ⊤) ≃ₐ[K] K × K) := by
  let _ : Algebra K Γ(E.intersection, ⊤) :=
    ((E.intersectionGlobalSectionsMap.comp e.symm.toRingHom)).toAlgebra
  let _ : Algebra.Etale K Γ(E.intersection, ⊤) := hEtale
  let _ : Algebra Γ(E.curve.left, ⊤) Γ(E.intersection, ⊤) :=
    E.intersectionGlobalSectionsMap.toAlgebra
  apply Algebra.Etale.exists_quadratic_algEquiv_or_prod_of_finrank_eq_two
  have hfinrank :
      Module.finrank Γ(E.curve.left, ⊤) Γ(E.intersection, ⊤) = 2 := by
    exact hdegree
  rw [← hfinrank]
  symm
  apply Algebra.finrank_eq_of_equiv_equiv e (RingEquiv.refl _)
  ext a
  simp [RingHom.algebraMap_toAlgebra]

/-- For an actual rational bridge which is not in the marked-tail alternative, the
degree-two intersection algebra is either a separable quadratic field or the split
algebra, provided it is étale after identifying the global constants with a field `K`. -/
theorem IsRationalBridge.intersection_isQuadraticOrSplit_of_not_markedTail
    {I : Type v} (E : SmoothGenusZeroSubcurveOver k C)
    (p : I → C.SectionOver (Spec (CommRingCat.of k)))
    (hbridge : E.IsRationalBridge p)
    (hnotMarkedTail : ¬ ∃ j : I,
      E.ContainsMarkedPoint (p j) ∧ E.IsRationalTail (deleteMarking p j))
    {K : Type u} [Field K] (e : Γ(E.curve.left, ⊤) ≃+* K)
    (hEtale :
      letI : Algebra K Γ(E.intersection, ⊤) :=
        ((E.intersectionGlobalSectionsMap.comp e.symm.toRingHom)).toAlgebra
      Algebra.Etale K Γ(E.intersection, ⊤)) :
    letI : Algebra K Γ(E.intersection, ⊤) :=
      ((E.intersectionGlobalSectionsMap.comp e.symm.toRingHom)).toAlgebra
    (∃ (L : Type u) (_ : Field L) (_ : Algebra K L)
        (_ : Algebra.IsSeparable K L)
        (_ : Algebra.IsQuadraticExtension K L),
        Nonempty (Γ(E.intersection, ⊤) ≃ₐ[K] L)) ∨
      Nonempty (Γ(E.intersection, ⊤) ≃ₐ[K] K × K) := by
  exact E.intersection_isQuadraticOrSplit_of_degree_two e hEtale
    ((hbridge.2.resolve_right hnotMarkedTail).1)

/-- For an unmarked rational bridge, the intersection algebra is either a separable
quadratic field or the split algebra, provided it is étale after identifying the
global constants with a field `K`. -/
theorem IsRationalBridge.intersection_isQuadraticOrSplit_of_containsNoMarkedPoints
    {I : Type v} (E : SmoothGenusZeroSubcurveOver k C)
    (p : I → C.SectionOver (Spec (CommRingCat.of k)))
    (hbridge : E.IsRationalBridge p) (hmarks : E.ContainsNoMarkedPoints p)
    {K : Type u} [Field K] (e : Γ(E.curve.left, ⊤) ≃+* K)
    (hEtale :
      letI : Algebra K Γ(E.intersection, ⊤) :=
        ((E.intersectionGlobalSectionsMap.comp e.symm.toRingHom)).toAlgebra
      Algebra.Etale K Γ(E.intersection, ⊤)) :
    letI : Algebra K Γ(E.intersection, ⊤) :=
      ((E.intersectionGlobalSectionsMap.comp e.symm.toRingHom)).toAlgebra
    (∃ (L : Type u) (_ : Field L) (_ : Algebra K L)
        (_ : Algebra.IsSeparable K L)
        (_ : Algebra.IsQuadraticExtension K L),
        Nonempty (Γ(E.intersection, ⊤) ≃ₐ[K] L)) ∨
      Nonempty (Γ(E.intersection, ⊤) ≃ₐ[K] K × K) := by
  exact E.intersection_isQuadraticOrSplit_of_degree_two e hEtale
    (hbridge.intersectionDegree_eq_two_of_containsNoMarkedPoints hmarks)

/-- The pointed genus-zero classification identifies the subcurve with the projective
line once properness, geometric integrality, and a rational point are supplied.

No smoothness or geometric integrality over the field of global constants is asserted:
the theorem stays over the original ground field `k`. -/
theorem projectiveLineIso_of_pointedClassification
    (E : SmoothGenusZeroSubcurveOver k C)
    [IsProper (C ↘ Spec (CommRingCat.of k))]
    [GeometricallyIntegral
      (E.curve.left ↘ Spec (CommRingCat.of k))]
    (H : HasPointedSmoothGenusZeroClassification k)
    (s : Spec (CommRingCat.of k) ⟶ E.curve.left)
    (hs : s ≫ E.curve.hom = 𝟙 _) :
    Nonempty (projectiveLineAsOver k ≅
      E.curve.left.asOver (Spec (CommRingCat.of k))) := by
  let _ : IsCurveOver k E.curve.left := E.isCurveOver
  let _ : IsProper (E.curve.left ↘ Spec (CommRingCat.of k)) :=
    E.curve_isProper
  let _ : Smooth (E.curve.left ↘ Spec (CommRingCat.of k)) := E.smooth
  exact H E.curve.left E.genus_eq_zero ⟨s, hs⟩

/-- Over an algebraically closed ground field, the pointed genus-zero classification
identifies the subcurve with the projective line once geometric integrality over that
same ground field is supplied.  A rational point is then automatic from smoothness.

This deliberately makes no claim about smoothness or geometric integrality after
changing the base to the field of global constants. -/
theorem projectiveLineIso_of_pointedClassification_of_isAlgClosed
    (E : SmoothGenusZeroSubcurveOver k C) [IsAlgClosed k]
    [IsProper (C ↘ Spec (CommRingCat.of k))]
    [GeometricallyIntegral
      (E.curve.left ↘ Spec (CommRingCat.of k))]
    (H : HasPointedSmoothGenusZeroClassification k) :
    Nonempty (projectiveLineAsOver k ≅
      E.curve.left.asOver (Spec (CommRingCat.of k))) := by
  let _ : IsCurveOver k E.curve.left := E.isCurveOver
  let _ : IsProper (E.curve.left ↘ Spec (CommRingCat.of k)) :=
    E.curve_isProper
  let _ : Smooth (E.curve.left ↘ Spec (CommRingCat.of k)) := E.smooth
  exact H.projectiveLineIso_of_genusOver_eq_zero
    E.curve.left E.genus_eq_zero

end SmoothGenusZeroSubcurveOver

end AlgebraicGeometry.Scheme

end
