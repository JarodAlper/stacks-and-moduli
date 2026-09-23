module

public import StacksAndModuli.API.StableCurveModuli
public import StacksAndModuli.«Section6.5-Stable-Reduction»


@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.BasedCategory

universe v₁ u₁ v₂ u₂ u

namespace AlgebraicGeometry.Mgbar

section DefCurve

/-!
## Curves and genus

Fix a field `k`. A curve over `k` is a finite-type scheme of dimension one;
it need not be smooth, connected, or proper. The library calls this
`Scheme.IsCurveOver k C` (Definition 6.1.1).

For a proper connected nodal curve over an algebraically closed field, the genus
is the dimension of `H¹(C, 𝒪_C)`. This also equals its arithmetic genus.
Cohomology, rather than the genus of the normalization, counts the contribution
from cycles in the dual graph of a singular curve.
-/

variable (k : Type u) [Field k]
variable (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))]

local notation "H¹(" C ")" => Scheme.Modules.H (Scheme.structureModule C) 1

/-- The cohomological definition of genus over the chosen ground field. -/
theorem genus_eq : Scheme.genusOver k C = Module.finrank k H¹(C) :=
  Scheme.genusOver_def k C

end DefCurve

section DefStableCurves

/-!
## Stability

Now let `k` be algebraically closed. A stable curve is proper, connected, and
nodal, with finitely many automorphisms over `k` — the finite-automorphism form of
Definition 6.3.2, equivalent to the book's combinatorial definition by Proposition 6.3.5.
A node is an ordinary double point: its completed local ring has the form
`k⟦x,y⟧/(xy)`. Stability rules out components with too few attaching points:
a rational component needs at least three, and a genus-one component at least
one. The following interface packages stability together with a specified genus.
-/

variable (k : Type u) [Field k] [IsAlgClosed k]
variable (g : ℕ) (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))]

/-- Unpack exactly what it means for `C` to be stable of genus `g`. -/
theorem stable_iff :
    Scheme.IsStableCurveOfGenusOver k g C ↔
      Scheme.IsNodalCurveOver k C ∧
      IsProper (C ↘ Spec (CommRingCat.of k)) ∧
      ConnectedSpace C ∧ Scheme.genusOver k C = g ∧
      Finite (C.AutOver (Spec (CommRingCat.of k))) :=
  Scheme.isStableCurveOfGenusOver_iff k g C

end DefStableCurves

section DefFamilyOfStableCurves

/-!
## Families

A family over a scheme `S` varies a stable curve with the point of `S`.
`StableCurveFamily g S` means a proper, flat, finitely presented family whose
geometric fibres are stable curves of genus `g` (Definition 6.3.20).
Flatness is the condition that makes this a family without jumps in its
algebraic structure. The total space is allowed to be an algebraic space,
as in the book; it is not required to be a scheme.

To inspect a fibre, take a geometric point `s : Spec k ⟶ S` with `k`
algebraically closed. The API chooses a scheme presentation of that fibre.
This presentation is sufficient to discuss its stability and genus.
-/

variable {g : ℕ} {S : Scheme.{u}} (F : StableCurveFamily g S)
variable {k : Type u} [Field k] [IsAlgClosed k]
variable (s : Spec (CommRingCat.of k) ⟶ S)

/-- Every geometric fibre of the family is stable. -/
theorem fibre_stable : Scheme.IsStableCurveOfGenusOver k g (F.geometricFiber s) :=
  F.geometricFiber_stable s

/-- The same genus `g` occurs at every geometric point. -/
theorem fibre_genus : Scheme.genusOver k (F.geometricFiber s) = g :=
  F.geometricFiber_genus s

end DefFamilyOfStableCurves

section DefPrestack

/-!
## Prestacks

A *prestack* over a category `𝒮` — in standard terminology a category fibered in
groupoids — is a category `𝒳` together with a functor `𝒳 ⥤ 𝒮` in which pullbacks exist
and satisfy the usual universal property (Definition 3.4.1). Mathlib's
`CategoryTheory.BasedCategory` is the data of such a functor, and
`CategoryTheory.Functor.IsFiberedInGroupoids` is the condition on it.

The library keeps the two apart: it states every result about a based category carrying
the condition as a typeclass instance, so the condition never appears in a type. Here we
bundle them, so that the moduli category of the next section can carry the word in its
type. That is a presentational choice local to this file — what the library results
quoted below actually consume is the underlying based category, supplied by the coercion.
-/

set_option linter.checkUnivs false in
/-- Background definition for this example: a prestack over `𝒮`, bundled — a based
category over `𝒮` together with the condition that its projection is fibered in
groupoids. The library's own rendering of Definition 3.4.1 is the unbundled one: the class
`CategoryTheory.Functor.IsFiberedInGroupoids` on the projection of a
`CategoryTheory.BasedCategory`. -/
abbrev Prestack (𝒮 : Type u₁) [Category.{v₁} 𝒮] :=
  {𝒳 : BasedCategory.{v₂, u₂} 𝒮 // 𝒳.p.IsFiberedInGroupoids}

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]

/-- The based category underlying a prestack is fibered in groupoids. As an instance, this
is what lets a prestack be passed — through the coercion — to the library's results, which
take a based category carrying the condition. -/
instance (𝒳 : Prestack.{v₁, u₁, v₂, u₂} 𝒮) :
    (𝒳 : BasedCategory.{v₂, u₂} 𝒮).p.IsFiberedInGroupoids :=
  𝒳.2

/-- The objects of a prestack are those of the underlying based category. This restores
`𝒳.obj`, which the bundling would otherwise displace to `𝒳.1.obj`. -/
abbrev Prestack.obj (𝒳 : Prestack.{v₁, u₁, v₂, u₂} 𝒮) : Type u₂ := 𝒳.1.obj

/-- The projection of a prestack to its base. This restores `𝒳.p`. -/
abbrev Prestack.p (𝒳 : Prestack.{v₁, u₁, v₂, u₂} 𝒮) : 𝒳.obj ⥤ 𝒮 := 𝒳.1.p

end DefPrestack


/- From here on, `FiniteType`, `IsSeparated`, `UniversallyClosed` and `IsProper` are the
absolute notions for a stack over schemes — the corresponding property of its structure
morphism to `Sch = Sch/Spec ℤ` — rather than Mathlib's classes for morphisms of schemes. -/
export AlgebraicGeometry.BasedCategory (FiniteType IsSeparated UniversallyClosed IsProper)

/-- Background definition for this example: an algebraic stack `𝒳` is *smooth* over
`Spec ℤ` if it admits a smooth presentation by a scheme `U` — a surjective, smooth,
representable morphism `U → 𝒳` — with `U` itself smooth over `Spec ℤ`. Smoothness is
smooth-local on the source in the sense of Definition 4.3.2, so this is the smoothness over
`Spec ℤ` of Theorem 6.4.16. The condition is stated for any based category over schemes,
but it is meant for algebraic stacks. -/
def IsSmooth (𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}) : Prop :=
  ∃ (U : Scheme.{u}) (F : overBased U ⥤ᵇ 𝒳),
    BasedFunctor.RepresentableWith (@Surjective ⊓ @Smooth : MorphismProperty Scheme.{u}) F ∧
      Smooth (specULiftZIsTerminal.{u}.from U)


section ThmMgIsProper

/-!
## The moduli stack

Write `𝓜̄_g` for the moduli category of stable curves of genus `g`, the book's
`\overline{\mathcal M}_g`. An object consists of a base scheme `S` and a family over `S`.
An arrow consists of a map of bases and a cartesian square of families.
Thus arrows over the identity of `S` are isomorphisms of families.
This retains automorphisms, which a set of isomorphism classes would forget.

The projection to schemes remembers the base. Since `Spec ℤ` is the final scheme, a
stack over schemes is the same thing as a stack over `Spec ℤ`, and every property below —
finite type, separated, universally closed, proper — is understood over `Spec ℤ`, as in
the book.
-/

local notation:max "𝓜̄_" g:max => moduliOfStableCurves g

variable (g : ℕ)

/-- **Deligne–Mumford's landmark theorem.** For `g ≥ 2`, the moduli stack `𝓜̄_g` of
stable curves of genus `g` is a smooth, proper Deligne–Mumford stack over `Spec ℤ`
(the unpointed case of Theorems 6.4.16 and 6.5.23).

The proof is admitted here. -/
theorem deligneMumfordTheorem (hg : g ≥ 2) :
    IsDeligneMumfordStack 𝓜̄_g ∧ IsSmooth 𝓜̄_g ∧ IsProper 𝓜̄_g := by
  sorry


end ThmMgIsProper

end AlgebraicGeometry.Mgbar

end
