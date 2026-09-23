module

public import StacksAndModuli.API.GlobalSectionsField
public import StacksAndModuli.API.FlasqueVanishing
public import StacksAndModuli.API.SheafCohomologySchemeIso
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension

/-!
# Curves and their genus

This module follows the subsection "Curves" of §6.1 (Review of smooth curves) of
*Stacks and Moduli*, section label
`sec:smooth-curves`.

The material is needed long before Chapter 6: the moduli prestack `ℳ_g` of
Example 3.4.10 (`ex:moduli-prestack-of-smooth-curves`) is cut out of the prestack of
families of smooth curves by a condition on the genus of the geometric fibres, and the
Algebraicity of `ℳ_g` (Theorem 4.1.17, `thm:mg-is-algebraic`) is stated for it.

## Main definition

- `AlgebraicGeometry.Scheme.IsCurveOver`: **Definition 6.1.1** — a curve over a field.

## Supporting API

- `AlgebraicGeometry.Scheme.genus`: the genus of a proper curve, read intrinsically as
  `dim_{Γ(C, 𝒪_C)} H¹(C, 𝒪_C)`. This is the form the moduli problem needs, because it is a
  property of the scheme `C` alone and therefore transports along the base change defining
  a geometric fibre.
- `AlgebraicGeometry.Scheme.genusOver`: the genus over a fixed base field,
  `h¹(C, 𝒪_C) = dim_k H¹(C, 𝒪_C)` — the book's `\h^1(C, \oh_C)`.
- `AlgebraicGeometry.Scheme.eulerCharStructure`, `AlgebraicGeometry.Scheme.arithmeticGenus`:
  `χ(C, 𝒪_C)` and the book's `g(C) = 1 - χ(C, 𝒪_C)`. The Euler characteristic is
  `Scheme.Modules.eulerChar` of the structure sheaf; it is additive on short exact
  sequences (`StacksAndModuli/API/SheafCohomologyModuleLES.lean`), which is the induction step of
  Riemann–Roch.

- `AlgebraicGeometry.Scheme.genusOver_eq_genus`: the two readings of the genus agree
  whenever `Γ(C, 𝒪_C) = k`, which is the case for a proper geometrically connected
  geometrically reduced curve.
- `AlgebraicGeometry.Scheme.arithmeticGenus_eq_genusOver`: the book's `1 - χ(C, 𝒪_C)`
  equals `h¹(C, 𝒪_C)` when `Γ(C, 𝒪_C) = k`.
- `AlgebraicGeometry.Scheme.genusOver_eq_genus_of_isAlgClosed` and
  `…arithmeticGenus_eq_genus_of_isAlgClosed`: all three readings agree for an integral
  curve proper over an algebraically closed field — the case of a geometric fibre.
- `AlgebraicGeometry.Scheme.genus_eq_zero_of_subsingleton`: the genus of a nonempty scheme
  with one point — such as `Spec k` — is `0`. This is the end-to-end check that the
  definition computes.

The general facts about `Γ(X, 𝒪_X)` that these rest on — that it is a field, integral over
`k`, and equal to `k` over an algebraically closed field — carry no book label and live in
`StacksAndModuli/API/GlobalSectionsField.lean`.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

section DefCurve

/-- **Definition 6.1.1** (`def:curve`): a *curve over a field `k`* is a one-dimensional
scheme `C` of finite type over `k`.

"Of finite type" is spelled as Mathlib does, as the conjunction of `QuasiCompact` and
`LocallyOfFiniteType` for the structure morphism; "one-dimensional" is the Krull dimension
of the underlying topological space, which is the notion §4.5 uses. -/
class IsCurveOver (k : Type u) [Field k] (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))] : Prop where
  quasiCompact : QuasiCompact (C ↘ Spec (CommRingCat.of k))
  locallyOfFiniteType : LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k))
  topologicalKrullDim_eq : topologicalKrullDim C = 1

attribute [instance] IsCurveOver.quasiCompact IsCurveOver.locallyOfFiniteType

/-- API lemma for Definition 6.1.1, unfolded. -/
lemma isCurveOver_iff (k : Type u) [Field k] (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))] :
    IsCurveOver k C ↔ QuasiCompact (C ↘ Spec (CommRingCat.of k)) ∧
      LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k)) ∧ topologicalKrullDim C = 1 :=
  ⟨fun h ↦ ⟨h.1, h.2, h.3⟩, fun h ↦ ⟨h.1, h.2.1, h.2.2⟩⟩

/-- Curves over a field are preserved by isomorphisms over that field. -/
theorem IsCurveOver.isoOver {k : Type u} [Field k]
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [Y.Over (Spec (CommRingCat.of k))] (h : IsCurveOver k X)
    (e : X.asOver (Spec (CommRingCat.of k)) ≅
      Y.asOver (Spec (CommRingCat.of k))) :
    IsCurveOver k Y := by
  let E : X ≅ Y := (Over.forget (Spec (CommRingCat.of k))).mapIso e
  let _ : IsCurveOver k X := h
  have he : E.inv ≫ (X ↘ Spec (CommRingCat.of k)) =
      Y ↘ Spec (CommRingCat.of k) := e.inv.w
  constructor
  · rw [← he]
    infer_instance
  · rw [← he]
    infer_instance
  · have hdim : topologicalKrullDim X = topologicalKrullDim Y :=
      IsHomeomorph.topologicalKrullDim_eq E.hom.homeomorph
        E.hom.homeomorph.isHomeomorph
    exact hdim.symm.trans h.topologicalKrullDim_eq

/-- **§6.1, "Curves"** (unlabelled, following Definition 6.1.1): the *genus* of a proper curve,
read intrinsically as `dim_{Γ(C, 𝒪_C)} H¹(C, 𝒪_C)`.

The book writes `g(C) = 1 - χ(C, 𝒪_C)`, "which is equal to `h¹(C, 𝒪_C)` if `C` is
geometrically connected and reduced". The reading taken here as *the* definition is the
second one, with the scalars taken to be the ring of global sections rather than a base
field; the three readings are compared in `arithmeticGenus_eq_genusOver` and
`genusOver_eq_genus`, whose common hypothesis `Γ(C, 𝒪_C) = k` holds exactly in the
situation where the book asserts the identification.

Taking the scalars to be `Γ(C, 𝒪_C)` makes the genus an invariant of the scheme `C` alone,
with no base field in the notation. That is what the moduli problem needs: `ℳ_g` is cut
out by a condition on *geometric fibres*, and a geometric fibre is produced by a base
change that does not remember a preferred field of definition. See the COMMENTARY entry for
Definition 6.1.1. -/
noncomputable def genus (C : Scheme.{u}) : ℕ :=
  Module.finrank Γ(C, ⊤) (Modules.H (structureModule C) 1)

lemma genus_def (C : Scheme.{u}) :
    C.genus = Module.finrank Γ(C, ⊤) (Modules.H (structureModule C) 1) := rfl

/-- **§6.1, "Curves"** (unlabelled, following Definition 6.1.1): `h¹(C, 𝒪_C)`, the genus of a
proper curve over a fixed base field `k`, as the book writes it. -/
noncomputable def genusOver (k : Type u) [Field k] (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))] : ℕ :=
  Modules.h k (structureModule C) 1

lemma genusOver_def (k : Type u) [Field k] (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))] :
    genusOver k C = Module.finrank k (Modules.H (structureModule C) 1) := rfl

/-- The genus over a field is preserved by an isomorphism over that field. -/
theorem genusOver_eq_of_isoOver (k : Type u) [Field k]
    {C D : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    [D.Over (Spec (CommRingCat.of k))]
    (e : C.asOver (Spec (CommRingCat.of k)) ≅
      D.asOver (Spec (CommRingCat.of k))) :
    genusOver k C = genusOver k D := by
  rw [genusOver_def, genusOver_def]
  exact Modules.h_structureModule_eq_of_overIso k e 1

/-- The intrinsic genus is preserved by an isomorphism of schemes. -/
theorem genus_eq_of_iso {C D : Scheme.{u}} (e : C ≅ D) : C.genus = D.genus := by
  simp only [genus_def, Module.finrank]
  congr 1
  refine rank_eq_of_equiv_equiv e.inv.appTop
    (structureCohomologyAddEquivOfIso e 1)
    (ConcreteCategory.bijective_of_isIso _) ?_
  intro r x
  have hr : e.hom.appTop (e.inv.appTop r) = r := by
    change (e.inv.appTop ≫ e.hom.appTop) r = r
    rw [← Scheme.Hom.comp_appTop, e.hom_inv_id, Scheme.Hom.id_appTop]
    rfl
  calc
    structureCohomologyAddEquivOfIso e 1 (r • x) =
        structureCohomologyAddEquivOfIso e 1
          (e.hom.appTop (e.inv.appTop r) • x) := by rw [hr]
    _ = e.inv.appTop r • structureCohomologyAddEquivOfIso e 1 x :=
      structureCohomologyAddEquivOfIso_smul e 1 (e.inv.appTop r) x

/-- **§6.1, "Curves"** (unlabelled): the Euler characteristic `χ(C, 𝒪_C)` of a proper
curve over `k`.

Only `h⁰` and `h¹` occur: on a curve `Hⁱ(C, 𝒪_C) = 0` for `i ≥ 2` by Grothendieck
vanishing, which is not available in Mathlib, so the alternating sum is *defined* by its
two possibly nonzero terms rather than derived. See the COMMENTARY entry for
Definition 6.1.1. -/
noncomputable def eulerCharStructure (k : Type u) [Field k] (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))] : ℤ :=
  Modules.eulerChar k (structureModule C)

lemma eulerCharStructure_def (k : Type u) [Field k] (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))] :
    eulerCharStructure k C =
      (Modules.h k (structureModule C) 0 : ℤ) - (Modules.h k (structureModule C) 1 : ℤ) :=
  rfl

/-- **§6.1, "Curves"** (unlabelled, following Definition 6.1.1): the *arithmetic genus*
`g(C) = 1 - χ(C, 𝒪_C)` of a proper curve over `k`, exactly as the book defines it. -/
noncomputable def arithmeticGenus (k : Type u) [Field k] (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))] : ℤ :=
  1 - eulerCharStructure k C

/-- `H¹(C, 𝒪_C) = 0` for a scheme with at most one point — in particular for `Spec k`.
Cohomology on a one-point space vanishes in positive degrees, because every sheaf there is
flasque (`StacksAndModuli/API/FlasqueVanishing.lean`). -/
lemma subsingleton_H_one_structureModule_of_subsingleton (C : Scheme.{u}) [Subsingleton C] :
    Subsingleton (Modules.H (structureModule C) 1) :=
  Modules.subsingleton_H_of_subsingleton (structureModule C) 0

/-- **The genus of a nonempty scheme with at most one point is zero**, e.g.
`Scheme.genus (Spec k) = 0` for a field `k`.

This is the end-to-end check that `Scheme.genus` computes a real value: it needs the
`Γ(C, 𝒪_C)`-module structure on `H¹`, the vanishing of `H¹` on a one-point space, and the
convention for `Module.finrank` of a subsingleton.

The nontriviality of `Γ(C, 𝒪_C)` — that is, `C ≠ ∅` — is a real hypothesis, not noise:
`Module.finrank` over the *zero* ring is `1` by Mathlib's convention, so the empty scheme
comes out with genus `1`. See this folder's COMMENTARY.md. -/
lemma genus_eq_zero_of_subsingleton (C : Scheme.{u}) [Subsingleton C]
    [Nontrivial Γ(C, ⊤)] : C.genus = 0 := by
  haveI := subsingleton_H_one_structureModule_of_subsingleton C
  rw [genus_def]
  exact Module.finrank_zero_of_subsingleton

/-- **The two readings of the genus agree.** If `Γ(C, 𝒪_C) = k` — the structure map from
`k` is bijective — then the intrinsic genus `dim_{Γ(C,𝒪_C)} H¹(C, 𝒪_C)` is the book's
`h¹(C, 𝒪_C) = dim_k H¹(C, 𝒪_C)`.

The proof is a rank comparison across the ring isomorphism, not a tower law: `k` acts on
`H¹(C, 𝒪_C)` *through* `Γ(C, 𝒪_C)` by construction
(`Scheme.Modules.base_smul_eq_globalSections_smul`), so Mathlib's `rank_eq_of_equiv_equiv`
applies with the identity additive equivalence. In particular no field structure on
`Γ(C, 𝒪_C)` is needed. -/
theorem genusOver_eq_genus (k : Type u) [Field k] (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))]
    (hb : Function.Bijective (C.baseRingHom (CommRingCat.of k))) :
    genusOver k C = C.genus := by
  simp only [genusOver_def, genus_def, Module.finrank]
  congr 1
  exact rank_eq_of_equiv_equiv (C.baseRingHom (CommRingCat.of k)) (AddEquiv.refl _) hb
    (fun a x ↦ Modules.base_smul_eq_globalSections_smul _ 1 a x)

/-- **The book's definition of the genus, `g(C) = 1 - χ(C, 𝒪_C)`, is `h¹(C, 𝒪_C)`** as
soon as `Γ(C, 𝒪_C) = k`: then `h⁰(C, 𝒪_C) = 1`. -/
theorem arithmeticGenus_eq_genusOver (k : Type u) [Field k] (C : Scheme.{u})
    [C.Over (Spec (CommRingCat.of k))]
    (hb : Function.Bijective (C.baseRingHom (CommRingCat.of k))) :
    arithmeticGenus k C = (genusOver k C : ℤ) := by
  have h0 : Modules.h k (structureModule C) 0 = 1 := by
    rw [Modules.h_structureModule_zero, finrank_globalSections_eq_one k C hb]
  simp [arithmeticGenus, eulerCharStructure_def, h0, genusOver]

/-- **The genus of an integral proper curve over an algebraically closed field.** The
intrinsic genus `dim_{Γ(C,𝒪_C)} H¹(C, 𝒪_C)` used to define `ℳ_g` is the book's
`h¹(C, 𝒪_C) = dim_k H¹(C, 𝒪_C)`. -/
theorem genusOver_eq_genus_of_isAlgClosed (k : Type u) [Field k] [IsAlgClosed k]
    (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))] [IsIntegral C]
    [UniversallyClosed (C ↘ Spec (CommRingCat.of k))] :
    genusOver k C = C.genus :=
  genusOver_eq_genus k C (bijective_baseRingHom_of_isAlgClosed k C)

/-- **The book's `g(C) = 1 - χ(C, 𝒪_C)` computes the intrinsic genus** for an integral
proper curve over an algebraically closed field. -/
theorem arithmeticGenus_eq_genus_of_isAlgClosed (k : Type u) [Field k] [IsAlgClosed k]
    (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))] [IsIntegral C]
    [UniversallyClosed (C ↘ Spec (CommRingCat.of k))] :
    arithmeticGenus k C = (C.genus : ℤ) := by
  rw [arithmeticGenus_eq_genusOver k C (bijective_baseRingHom_of_isAlgClosed k C),
    genusOver_eq_genus_of_isAlgClosed k C]

end DefCurve

end AlgebraicGeometry.Scheme
