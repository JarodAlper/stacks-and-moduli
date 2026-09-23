module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.Grp.AB
public import StacksAndModuli.API.ExtModuleOfRingHom
public import StacksAndModuli.API.GlobalSectionsOverBase

/-!
# The module structure on the cohomology of an `𝒪_X`-module

Mathlib defines `Hⁿ(X, F) = Sheaf.H F n` for an *abelian* sheaf `F` on a site, as an `Ext`
group out of the constant sheaf `ℤ`; it is therefore only an abelian group. But the
cohomology of a sheaf of `𝒪_X`-modules on a scheme `X` carries much more: multiplication by
a global section of `𝒪_X` is an endomorphism of `F` as an abelian sheaf, so `Hⁿ(X, F)` is a
module over `Γ(X, 𝒪_X)`, hence over any ring mapping to it — in particular over `k`
whenever `X` is a `k`-scheme. For `X` a proper curve over a field `k` this is what makes
`h¹(C, 𝒪_C) = dim_k H¹(C, 𝒪_C)`, and so the genus, meaningful.

The construction is elementary: `Γ(X, ⊤) →+* End F` in abelian sheaves (multiply sections
by the restriction of a global section — naturality is
`AlgebraicGeometry.Scheme.Modules.map_comp_smul`), followed by
`CategoryTheory.Abelian.Ext.moduleOfRingHom`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.smulNatTrans`, `…smulSheafHom`: multiplication by a
  global section of `𝒪_X`, on the underlying abelian sheaf of an `𝒪_X`-module.
* `AlgebraicGeometry.Scheme.Modules.smulEnd`: the ring homomorphism
  `Γ(X, ⊤) →+* End ((SheafOfModules.toSheaf _).obj F)` assembling those.
* `AlgebraicGeometry.Scheme.Modules.H`: `Hⁿ(X, F)` for `F` an `𝒪_X`-module.
* `AlgebraicGeometry.Scheme.baseRingHom`: the ring map `R →+* Γ(X, ⊤)` attached to a
  structure morphism `X ⟶ Spec R`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.instModuleGlobalSectionsH`: `Hⁿ(X, F)` is a
  `Γ(X, ⊤)`-module.
* `AlgebraicGeometry.Scheme.Modules.instModuleH`: `Hⁿ(X, F)` is a `k`-module for a scheme
  over `Spec k`; for `k` a field this is the vector space structure used to define
  `h⁰`, `h¹` and the genus.
* `AlgebraicGeometry.Scheme.Modules.HZeroLinearEquiv`: `H⁰(X, F) ≅ Γ(F, X)` as
  `Γ(X, 𝒪_X)`-modules, and `…HZeroStructureLinearEquiv` its `k`-linear form for `F = 𝒪_X`,
  giving `h⁰(X, 𝒪_X) = dim_k Γ(X, 𝒪_X)` (`…h_structureModule_zero`).
* `AlgebraicGeometry.Scheme.Modules.HMap`, `…HLinearEquivOfIso`: linear functoriality of
  `Hⁿ` in the coefficient module, and `…h_eq_of_iso` in dimensions.

## Upstream

The scheme-level construction follows the file `AlgebraicGeometry/AlgebraicCycle/
CohmologyModule.lean` of Mathlib PR
[#41621](https://github.com/leanprover-community/mathlib4/pull/41621) (Raphael Douglas
Giles), simplified: the naturality of scalar multiplication is already in Mathlib as
`Scheme.Modules.map_comp_smul`, and the action is factored through `Γ(X, ⊤)` rather than
being defined separately for every base ring.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open CategoryTheory Abelian Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace Scheme

variable {X : Scheme.{u}}

/-- The ring homomorphism `R →+* Γ(X, 𝒪_X)` induced by the structure morphism of an
`R`-scheme, via the `Γ`–`Spec` adjunction.

This is `AlgebraicGeometry.Scheme.Modules.baseRingHom` of
`StacksAndModuli/API/GlobalSectionsOverBase.lean` taken at the structure morphism `X ↘ Spec R`,
and unbundled to a `RingHom`. Because the structure morphism is recorded in the instance
graph by `X.Over (Spec R)`, the induced algebra and module structures *can* be instances
here, which is what makes `Module.finrank k (Hⁿ(X, F))` elaborate. -/
noncomputable def baseRingHom (X : Scheme.{u}) (R : CommRingCat.{u}) [X.Over (Spec R)] :
    R →+* Γ(X, ⊤) :=
  (Scheme.Modules.baseRingHom (X ↘ Spec R)).hom

lemma baseRingHom_eq (X : Scheme.{u}) (R : CommRingCat.{u}) [X.Over (Spec R)] :
    X.baseRingHom R = ((Scheme.ΓSpecIso R).inv ≫ (X ↘ Spec R).appTop).hom := rfl

/-- The global sections of a `k`-scheme form a `k`-algebra.

Definitionally `AlgebraicGeometry.Scheme.Modules.globalSectionsAlgebra (X ↘ Spec R)`, so
no diamond arises with the `letI`-installed structure of
`StacksAndModuli/API/GlobalSectionsOverBase.lean`. -/
noncomputable instance instAlgebraGlobalSections {k : Type u} [CommRing k]
    [X.Over (Spec (CommRingCat.of k))] : Algebra k Γ(X, ⊤) :=
  Scheme.Modules.globalSectionsAlgebra (X ↘ Spec (CommRingCat.of k))

lemma algebraMap_globalSections_eq {k : Type u} [CommRing k]
    [X.Over (Spec (CommRingCat.of k))] :
    algebraMap k Γ(X, ⊤) = X.baseRingHom (CommRingCat.of k) := rfl

namespace Modules

variable (F : X.Modules)

/-- Restriction of global sections of `𝒪_X` to an open `U`, as a ring homomorphism. -/
noncomputable def restrictTop (X : Scheme.{u}) (U : X.Opens) : Γ(X, ⊤) →+* Γ(X, U) :=
  (X.presheaf.map (Opens.leTop U).op).hom

@[simp]
lemma restrictTop_apply (X : Scheme.{u}) (U : X.Opens) (r : Γ(X, ⊤)) :
    restrictTop X U r = X.presheaf.map (Opens.leTop U).op r := rfl

@[simp]
lemma restrictTop_top (X : Scheme.{u}) (r : Γ(X, ⊤)) : restrictTop X ⊤ r = r := by
  rw [restrictTop_apply, show (Opens.leTop (⊤ : X.Opens)).op = 𝟙 _ from rfl,
    X.presheaf.map_id]
  rfl

/-- Multiplication by a global section `r : Γ(X, 𝒪_X)`, as an endomorphism of the underlying
abelian presheaf of an `𝒪_X`-module `F`: on an open `U` it is multiplication by `r|_U`. -/
noncomputable def smulNatTrans (r : Γ(X, ⊤)) :
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj F).obj ⟶
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj F).obj where
  app U := F.smul (restrictTop X U.unop r)
  naturality U V i := by
    have key : restrictTop X V.unop r =
        X.presheaf.map i.unop.op (restrictTop X U.unop r) := by
      rw [restrictTop_apply, restrictTop_apply, ← ConcreteCategory.comp_apply,
        ← X.presheaf.map_comp, ← op_comp]
      rfl
    rw [key]
    exact (F.map_comp_smul i.unop (restrictTop X U.unop r)).symm

@[simp]
lemma smulNatTrans_app (r : Γ(X, ⊤)) (U : (Opens X)ᵒᵖ) :
    (smulNatTrans F r).app U = F.smul (restrictTop X U.unop r) := rfl

/-- Multiplication by a global section `r : Γ(X, 𝒪_X)`, as an endomorphism of the underlying
abelian sheaf of an `𝒪_X`-module `F`. -/
noncomputable def smulSheafHom (r : Γ(X, ⊤)) :
    End ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) :=
  Sheaf.homEquiv.symm (smulNatTrans F r)

@[simp]
lemma smulSheafHom_hom (r : Γ(X, ⊤)) : (smulSheafHom F r).hom = smulNatTrans F r := rfl

@[simp]
lemma smulSheafHom_app (r : Γ(X, ⊤)) (U : (Opens X)ᵒᵖ) :
    (smulSheafHom F r).hom.app U = F.smul (restrictTop X U.unop r) := rfl

/-- Two endomorphisms of the underlying abelian sheaf of an `𝒪_X`-module agree as soon as
they agree on sections over every open. -/
lemma sheafHom_ext {f g : End ((SheafOfModules.toSheaf X.ringCatSheaf).obj F)}
    (h : ∀ U : (Opens X)ᵒᵖ, f.hom.app U = g.hom.app U) : f = g :=
  Sheaf.homEquiv.injective (NatTrans.ext (funext h))

/-- Multiplication by a global section of `𝒪_X`, read on sections over one open, is the
composite of restriction with the `Γ(X, U)`-action on `Γ(F, U)`; both are ring
homomorphisms. -/
noncomputable def smulEndOver (U : X.Opens) : Γ(X, ⊤) →+* End Γ(F, U) :=
  (F.smul).comp (restrictTop X U)

@[simp]
lemma smulEndOver_apply (U : X.Opens) (r : Γ(X, ⊤)) :
    smulEndOver F U r = F.smul (restrictTop X U r) := rfl

/-- **The scalars acting on cohomology.** Multiplication by global sections of `𝒪_X` is a
ring homomorphism from `Γ(X, 𝒪_X)` to the endomorphism ring of the underlying abelian sheaf
of an `𝒪_X`-module `F`. This is the input to
`CategoryTheory.Abelian.Ext.moduleOfRingHom` that makes `Hⁿ(X, F)` a
`Γ(X, 𝒪_X)`-module. -/
noncomputable def smulEnd :
    Γ(X, ⊤) →+* End ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) where
  toFun := smulSheafHom F
  map_one' := sheafHom_ext F fun U ↦ (smulEndOver F U.unop).map_one
  map_mul' r s := sheafHom_ext F fun U ↦ (smulEndOver F U.unop).map_mul r s
  map_zero' := sheafHom_ext F fun U ↦ (smulEndOver F U.unop).map_zero
  map_add' r s := sheafHom_ext F fun U ↦ (smulEndOver F U.unop).map_add r s

@[simp]
lemma smulEnd_apply (r : Γ(X, ⊤)) : smulEnd F r = smulSheafHom F r := rfl

/-- Morphisms of `𝒪_X`-modules commute with multiplication by a global section of `𝒪_X`:
they are `𝒪_X`-linear. This is what makes the induced maps on cohomology linear. -/
lemma smulSheafHom_comp {F G : X.Modules} (φ : F ⟶ G) (r : Γ(X, ⊤)) :
    smulSheafHom F r ≫ (SheafOfModules.toSheaf X.ringCatSheaf).map φ =
      (SheafOfModules.toSheaf X.ringCatSheaf).map φ ≫ smulSheafHom G r := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U ↦ ?_))
  refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
  exact φ.app_smul (restrictTop X U.unop r) x

/-- `Hⁿ(X, F)`: the `n`-th cohomology group of an `𝒪_X`-module `F`, defined as the
cohomology of the underlying abelian sheaf. It is a `Γ(X, 𝒪_X)`-module, and a `k`-vector
space when `X` is a scheme over a field `k`. -/
noncomputable abbrev H (F : X.Modules) (n : ℕ) : Type u :=
  ((SheafOfModules.toSheaf X.ringCatSheaf).obj F).H n

/-- The cohomology of an `𝒪_X`-module is a module over the ring of global sections of
`𝒪_X`. -/
noncomputable instance instModuleGlobalSectionsH (n : ℕ) : Module Γ(X, ⊤) (H F n) :=
  Ext.moduleOfRingHom (smulEnd F) n

lemma smul_def (n : ℕ) (r : Γ(X, ⊤)) (x : H F n) :
    r • x = x.comp (Ext.mk₀ (smulSheafHom F r)) (add_zero n) := rfl

variable {F} in
/-- **Functoriality of cohomology, linearly.** A morphism `φ : F ⟶ G` of `𝒪_X`-modules
induces a `Γ(X, 𝒪_X)`-linear map `Hⁿ(X, F) → Hⁿ(X, G)`. Mathlib supplies the underlying
additive map (`CategoryTheory.Sheaf.H.map`); the content added here is its linearity, which
is the `𝒪_X`-linearity of `φ` (`smulSheafHom_comp`). -/
noncomputable def HMap {G : X.Modules} (φ : F ⟶ G) (n : ℕ) : H F n →ₗ[Γ(X, ⊤)] H G n where
  toFun := Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) n
  map_add' x y := (Sheaf.H.map _ n).map_add x y
  map_smul' r x := by
    simp only [RingHom.id_apply, smul_def, Sheaf.H.map_apply,
      Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, smulSheafHom_comp]

variable {F} in
@[simp]
lemma HMap_apply {G : X.Modules} (φ : F ⟶ G) (n : ℕ) (x : H F n) :
    HMap φ n x = Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) n x := rfl

variable {F} in
/-- An isomorphism of `𝒪_X`-modules induces a `Γ(X, 𝒪_X)`-linear isomorphism on
cohomology. -/
noncomputable def HLinearEquivOfIso {G : X.Modules} (e : F ≅ G) (n : ℕ) :
    H F n ≃ₗ[Γ(X, ⊤)] H G n where
  __ := HMap e.hom n
  invFun := HMap e.inv n
  left_inv x := by
    change Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map e.inv) n
        (Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map e.hom) n x) = x
    rw [← Sheaf.H.map_comp_apply, ← CategoryTheory.Functor.map_comp, e.hom_inv_id,
      CategoryTheory.Functor.map_id, Sheaf.H.map_id_apply]
  right_inv x := by
    change Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map e.hom) n
        (Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map e.inv) n x) = x
    rw [← Sheaf.H.map_comp_apply, ← CategoryTheory.Functor.map_comp, e.inv_hom_id,
      CategoryTheory.Functor.map_id, Sheaf.H.map_id_apply]

/-- **`H⁰` is global sections, linearly.** For an `𝒪_X`-module `F` the degree-zero
cohomology `H⁰(X, F)` is `Γ(F, X)`. Mathlib supplies the additive isomorphism
(`CategoryTheory.Sheaf.H.equiv₀`, taken at the terminal open `⊤`); what is added here is
that it is linear over `Γ(X, 𝒪_X)`. -/
noncomputable def HZeroLinearEquiv : H F 0 ≃ₗ[Γ(X, ⊤)] Γ(F, ⊤) :=
  AddEquiv.toLinearEquiv
    (Sheaf.H.equiv₀ ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) Limits.isTerminalTop)
    (fun r x ↦ by
      refine (Sheaf.H.equiv₀_naturality (f := smulSheafHom F r)
        (hT := (Limits.isTerminalTop : Limits.IsTerminal (⊤ : X.Opens))) x).symm.trans ?_
      rw [smulSheafHom_app, restrictTop_top]
      exact F.smul_apply r _)

/-- The cohomology of an `𝒪_X`-module on a scheme over `Spec R` is an `R`-module: `R` acts
through the structure map `R → Γ(X, 𝒪_X)`.

This is the unbundled form; the instance used in practice is `instModuleH`, whose scalars
are a bare type. -/
@[instance_reducible]
noncomputable def moduleOfBase (R : CommRingCat.{u}) [X.Over (Spec R)] (n : ℕ) :
    Module R (H F n) :=
  Ext.moduleOfRingHom ((smulEnd F).comp (X.baseRingHom R)) n

/-- **The vector space structure on cohomology.** For a scheme `X` over `Spec k` and an
`𝒪_X`-module `F`, the cohomology `Hⁿ(X, F)` is a `k`-module — a `k`-vector space when `k`
is a field. This is what gives `hⁿ(X, F) = dim_k Hⁿ(X, F)`, and hence the genus of a proper
curve, a meaning. -/
noncomputable instance instModuleH {k : Type u} [CommRing k]
    [X.Over (Spec (CommRingCat.of k))] (n : ℕ) : Module k (H F n) :=
  Ext.moduleOfRingHom ((smulEnd F).comp (X.baseRingHom (CommRingCat.of k))) n

lemma base_smul_def {k : Type u} [CommRing k] [X.Over (Spec (CommRingCat.of k))] (n : ℕ)
    (a : k) (x : H F n) :
    a • x = x.comp (Ext.mk₀ (smulSheafHom F (X.baseRingHom (CommRingCat.of k) a)))
      (add_zero n) := rfl

/-- The scalars of the base ring act on cohomology through the structure map
`k → Γ(X, 𝒪_X)`. -/
lemma base_smul_eq_globalSections_smul {k : Type u} [CommRing k]
    [X.Over (Spec (CommRingCat.of k))] (n : ℕ) (a : k) (x : H F n) :
    a • x = (X.baseRingHom (CommRingCat.of k) a) • x := rfl

instance instIsScalarTowerH {k : Type u} [CommRing k] [X.Over (Spec (CommRingCat.of k))]
    (n : ℕ) : IsScalarTower k Γ(X, ⊤) (H F n) where
  smul_assoc a r x :=
    (congrArg (· • x) (Algebra.smul_def a r)).trans (mul_smul _ r x)

/-- `hⁿ(X, F)`, the dimension over the base field `k` of the `n`-th cohomology of an
`𝒪_X`-module `F` on a `k`-scheme `X`. It is `0` when the cohomology is infinite
dimensional, following the `Module.finrank` convention. -/
noncomputable def h (k : Type u) [Field k] [X.Over (Spec (CommRingCat.of k))]
    (F : X.Modules) (n : ℕ) : ℕ :=
  Module.finrank k (H F n)

lemma h_def (k : Type u) [Field k] [X.Over (Spec (CommRingCat.of k))] (F : X.Modules)
    (n : ℕ) : h k F n = Module.finrank k (H F n) := rfl

/-- `χ(X, F) = h⁰(X, F) - h¹(X, F)`, the Euler characteristic of an `𝒪_X`-module on a
`k`-scheme in the two-term range.

On a curve `Hⁱ(X, F) = 0` for `i ≥ 2` by Grothendieck vanishing, so this is the full
alternating sum; Grothendieck vanishing is not available in Mathlib, so the two terms that
can be nonzero are taken as the definition. -/
noncomputable def eulerChar (k : Type u) [Field k] [X.Over (Spec (CommRingCat.of k))]
    (F : X.Modules) : ℤ :=
  (h k F 0 : ℤ) - (h k F 1 : ℤ)

lemma eulerChar_def (k : Type u) [Field k] [X.Over (Spec (CommRingCat.of k))]
    (F : X.Modules) : eulerChar k F = (h k F 0 : ℤ) - (h k F 1 : ℤ) := rfl

/-- Isomorphic `𝒪_X`-modules have the same cohomology dimensions. -/
lemma h_eq_of_iso (k : Type u) [Field k] [X.Over (Spec (CommRingCat.of k))]
    {F G : X.Modules} (e : F ≅ G) (n : ℕ) : h k F n = h k G n :=
  (LinearEquiv.restrictScalars k (HLinearEquivOfIso e n)).finrank_eq

/-- Finite dimensionality of cohomology transfers along an isomorphism of `𝒪_X`-modules. -/
lemma finiteDimensional_H_of_iso (k : Type u) [Field k] [X.Over (Spec (CommRingCat.of k))]
    {F G : X.Modules} (e : F ≅ G) (n : ℕ) [FiniteDimensional k (H F n)] :
    FiniteDimensional k (H G n) :=
  Module.Finite.equiv (LinearEquiv.restrictScalars k (HLinearEquivOfIso e n))

/-- Isomorphic `𝒪_X`-modules have the same Euler characteristic. -/
lemma eulerChar_eq_of_iso (k : Type u) [Field k] [X.Over (Spec (CommRingCat.of k))]
    {F G : X.Modules} (e : F ≅ G) : eulerChar k F = eulerChar k G := by
  rw [eulerChar_def, eulerChar_def, h_eq_of_iso k e 0, h_eq_of_iso k e 1]

/-- Vanishing cohomology has dimension zero.

Deliberately not a `simp` lemma: the hypothesis is a typeclass that `simp` would have to
discharge by instance search on every `h`, which times out. -/
lemma h_eq_zero_of_subsingleton (k : Type u) [Field k] [X.Over (Spec (CommRingCat.of k))]
    (F : X.Modules) (n : ℕ) (hs : Subsingleton (H F n)) : h k F n = 0 := by
  letI := hs
  rw [h_def, Module.finrank_zero_of_subsingleton]

/-- With the `k`-module structure on global sections installed from
`StacksAndModuli/API/GlobalSectionsOverBase.lean`, `k` acts on `Γ(F, ⊤)` through `Γ(X, 𝒪_X)`. -/
lemma isScalarTower_globalSections (k : Type u) [CommRing k]
    [X.Over (Spec (CommRingCat.of k))] (F : X.Modules) :
    letI := Scheme.Modules.globalSectionsModule (X ↘ Spec (CommRingCat.of k)) F
    IsScalarTower k Γ(X, ⊤) Γ(F, ⊤) :=
  letI := Scheme.Modules.globalSectionsModule (X ↘ Spec (CommRingCat.of k)) F
  { smul_assoc a r x := (congrArg (· • x) (Algebra.smul_def a r)).trans (mul_smul _ r x) }

/-- **`h⁰(X, F) = dim_k Γ(F, X)`**, for an arbitrary `𝒪_X`-module on a `k`-scheme. The
`k`-module structure on the right is the one `GlobalSectionsOverBase` installs from the
structure morphism; `h_structureModule_zero` is the case `F = 𝒪_X`, where it is available
as an instance. -/
lemma h_zero_eq_finrank_globalSections (k : Type u) [Field k]
    [X.Over (Spec (CommRingCat.of k))] (F : X.Modules) :
    letI := Scheme.Modules.globalSectionsModule (X ↘ Spec (CommRingCat.of k)) F
    h k F 0 = Module.finrank k Γ(F, ⊤) :=
  letI := Scheme.Modules.globalSectionsModule (X ↘ Spec (CommRingCat.of k)) F
  letI := isScalarTower_globalSections k F
  (LinearEquiv.restrictScalars k (HZeroLinearEquiv F)).finrank_eq

end Modules

variable (X) in
/-- The structure sheaf `𝒪_X` regarded as an `𝒪_X`-module. -/
noncomputable abbrev structureModule : X.Modules := SheafOfModules.unit X.ringCatSheaf

namespace Modules

/-- The sections of `𝒪_X` viewed as an `𝒪_X`-module are the sections of the structure
sheaf. -/
noncomputable def structureModuleSectionsEquiv (X : Scheme.{u}) (U : X.Opens) :
    Γ(structureModule X, U) ≃ₗ[Γ(X, U)] Γ(X, U) :=
  LinearEquiv.refl _ _

/-- **`H⁰(X, 𝒪_X) = Γ(X, 𝒪_X)` as `k`-vector spaces**, for a scheme `X` over `Spec k`.
Together with `Scheme.Modules.h` this computes `h⁰(X, 𝒪_X) = dim_k Γ(X, 𝒪_X)`; for a
proper, geometrically connected, geometrically reduced `X` the right-hand side is `1`. -/
noncomputable def HZeroStructureLinearEquiv (X : Scheme.{u}) (k : Type u) [CommRing k]
    [X.Over (Spec (CommRingCat.of k))] :
    H (structureModule X) 0 ≃ₗ[k] Γ(X, ⊤) :=
  LinearEquiv.restrictScalars k
    (HZeroLinearEquiv (structureModule X) ≪≫ₗ structureModuleSectionsEquiv X ⊤)

/-- `h⁰(X, 𝒪_X)` is the dimension of the ring of global sections over the base field. -/
lemma h_structureModule_zero (X : Scheme.{u}) (k : Type u) [Field k]
    [X.Over (Spec (CommRingCat.of k))] :
    h k (structureModule X) 0 = Module.finrank k Γ(X, ⊤) :=
  (HZeroStructureLinearEquiv X k).finrank_eq

end Modules

end Scheme

end AlgebraicGeometry
