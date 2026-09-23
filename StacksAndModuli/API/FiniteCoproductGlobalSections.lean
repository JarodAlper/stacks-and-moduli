module

public import StacksAndModuli.API.GlobalSectionsField
public import StacksAndModuli.API.SheafCohomologyPushforwardZero
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Global sections of indexed coproducts of schemes

Restriction to the coproduct inclusions identifies the global functions on an indexed
coproduct of schemes with the product of the global-function rings of its components.  No
finiteness assumption is needed for this ring equivalence.  For a finite family of schemes
over a field, it yields the expected dimension formula whenever every component has only
constant global functions.

The inverse restriction map is constructed geometrically.  The component maps to the
spectrum of the product ring assemble to a map from the coproduct; its map on global
sections glues a family of componentwise functions.  The coproduct open cover proves that
restriction is injective.

## Main results

* `AlgebraicGeometry.Scheme.sigmaGlobalSectionsRingEquiv`: global functions on an indexed
  coproduct are the product of the component global-function rings.
* `AlgebraicGeometry.Scheme.sigmaGlobalSectionsLinearEquiv`: the corresponding linear
  equivalence for schemes over a common base ring.
* `AlgebraicGeometry.Scheme.finrank_globalSections_sigma_eq_card`: if every component has
  global-function ring equal to the base field, the dimension is the number of components.
* `AlgebraicGeometry.Scheme.Modules.h_zero_pushforward_structureModule_sigma_eq_card`: the
  degree-zero pushforward-cohomology form used for normalization maps.
-/

@[expose] public section

-- These options are load-bearing throughout the library.

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {ι : Type u} (X : ι → Scheme.{u})

/-- Restriction of global functions to every component of an indexed coproduct. -/
noncomputable def sigmaAppTop :
    Γ(∐ X, ⊤) →+* (∀ i, Γ(X i, ⊤)) :=
  RingHom.pi fun i ↦ (Sigma.ι X i).appTop.hom

/-- The component of `sigmaAppTop` is restriction along the corresponding coproduct
inclusion. -/
@[simp]
lemma sigmaAppTop_apply (s : Γ(∐ X, ⊤)) (i : ι) :
    sigmaAppTop X s i = (Sigma.ι X i).appTop.hom s :=
  rfl

/-- The coproduct map to the spectrum of the product of the component global-function
rings. -/
noncomputable def sigmaToSpecPiGlobalSections :
    (∐ X) ⟶ Spec (.of (∀ i, Γ(X i, ⊤))) :=
  Sigma.desc fun i ↦ (X i).toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun i ↦ Γ(X i, ⊤)) i))

/-- Gluing componentwise global functions, obtained from the preceding map on global
sections. -/
noncomputable def piGlobalSectionsToSigma :
    (∀ i, Γ(X i, ⊤)) →+* Γ(∐ X, ⊤) :=
  ((Scheme.ΓSpecIso (.of (∀ i, Γ(X i, ⊤)))).inv ≫
    (sigmaToSpecPiGlobalSections X).appTop).hom

/-- Restricting a glued family of global functions recovers that family. -/
lemma sigmaAppTop_piGlobalSectionsToSigma (s : ∀ i, Γ(X i, ⊤)) :
    sigmaAppTop X (piGlobalSectionsToSigma X s) = s := by
  ext i
  change (Sigma.ι X i).appTop.hom
    (((Scheme.ΓSpecIso (.of (∀ i, Γ(X i, ⊤)))).inv ≫
      (sigmaToSpecPiGlobalSections X).appTop).hom s) = s i
  rw [← CommRingCat.comp_apply, Category.assoc, ← Scheme.Hom.comp_appTop]
  rw [show Sigma.ι X i ≫ sigmaToSpecPiGlobalSections X =
      (X i).toSpecΓ ≫
        Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun i ↦ Γ(X i, ⊤)) i)) by
      simp [sigmaToSpecPiGlobalSections]]
  simp only [Scheme.Hom.comp_app, TopologicalSpace.Opens.map_top,
    Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  rfl

/-- Restriction of global functions to all coproduct components is injective. -/
lemma sigmaAppTop_injective : Function.Injective (sigmaAppTop X) := by
  intro s t h
  apply (sigmaOpenCover X).ext_elem
  intro i
  exact congr_fun h i

/-- Global functions on an indexed coproduct restrict bijectively to families of global
functions on its components. -/
theorem sigmaAppTop_bijective : Function.Bijective (sigmaAppTop X) :=
  ⟨sigmaAppTop_injective X, fun s ↦
    ⟨piGlobalSectionsToSigma X s, sigmaAppTop_piGlobalSectionsToSigma X s⟩⟩

/-- Gluing the restrictions of a global function recovers that function. -/
@[simp]
lemma piGlobalSectionsToSigma_sigmaAppTop (s : Γ(∐ X, ⊤)) :
    piGlobalSectionsToSigma X (sigmaAppTop X s) = s := by
  apply sigmaAppTop_injective X
  rw [sigmaAppTop_piGlobalSectionsToSigma]

/-- The ring of global functions on an indexed coproduct is the product of the rings of
global functions on its components. -/
noncomputable def sigmaGlobalSectionsRingEquiv :
    Γ(∐ X, ⊤) ≃+* (∀ i, Γ(X i, ⊤)) :=
  RingEquiv.ofBijective (sigmaAppTop X) (sigmaAppTop_bijective X)

/-- The global-sections ring equivalence is restriction to the coproduct components. -/
@[simp]
lemma sigmaGlobalSectionsRingEquiv_apply (s : Γ(∐ X, ⊤)) :
    sigmaGlobalSectionsRingEquiv X s = sigmaAppTop X s :=
  rfl

/-- The structure morphism on a coproduct of schemes over a common base. -/
noncomputable def sigmaStructureMap (k : Type u) [CommRing k]
    [∀ i, (X i).Over (Spec (CommRingCat.of k))] :
    (∐ X) ⟶ Spec (CommRingCat.of k) :=
  Sigma.desc fun i ↦ X i ↘ Spec (CommRingCat.of k)

/-- Each coproduct inclusion respects the canonical structure morphism. -/
@[reassoc (attr := simp)]
lemma sigmaι_sigmaStructureMap (k : Type u) [CommRing k]
    [∀ i, (X i).Over (Spec (CommRingCat.of k))] (i : ι) :
    Sigma.ι X i ≫ sigmaStructureMap X k = X i ↘ Spec (CommRingCat.of k) :=
  Sigma.ι_desc _ _

/-- The canonical scheme-over-a-base structure on a coproduct of schemes over that base. -/
@[instance_reducible]
noncomputable def sigmaOver (k : Type u) [CommRing k]
    [∀ i, (X i).Over (Spec (CommRingCat.of k))] :
    (∐ X).Over (Spec (CommRingCat.of k)) :=
  ⟨sigmaStructureMap X k⟩

/-- The global-sections equivalence for a coproduct of schemes over a common base is linear
over the base ring. -/
noncomputable def sigmaGlobalSectionsLinearEquiv
    (k : Type u) [CommRing k]
    [∀ i, (X i).Over (Spec (CommRingCat.of k))] :
    letI := sigmaOver X k
    Γ(∐ X, ⊤) ≃ₗ[k] (∀ i, Γ(X i, ⊤)) := by
  letI := sigmaOver X k
  refine LinearEquiv.ofBijective
    { toFun := sigmaAppTop X
      map_add' := map_add (sigmaAppTop X)
      map_smul' := fun r s ↦ ?_ }
    (sigmaAppTop_bijective X)
  ext i
  change (Sigma.ι X i).appTop.hom
      ((Scheme.Modules.baseRingHom (sigmaStructureMap X k)).hom r * s) =
    (Scheme.Modules.baseRingHom (X i ↘ Spec (CommRingCat.of k))).hom r *
      (Sigma.ι X i).appTop.hom s
  rw [map_mul]
  congr 1
  change ((Scheme.Modules.baseRingHom (sigmaStructureMap X k) ≫
    (Sigma.ι X i).appTop).hom) r = _
  rw [Scheme.Modules.baseRingHom_comp_appTop, sigmaι_sigmaStructureMap]

/-- If every component has global-function ring equal to the base field, global functions
on their coproduct are linearly equivalent to one copy of the field per component. -/
noncomputable def sigmaGlobalSectionsLinearEquivBase
    (k : Type u) [Field k]
    [∀ i, (X i).Over (Spec (CommRingCat.of k))]
    (hb : ∀ i, Function.Bijective
      ((X i).baseRingHom (CommRingCat.of k))) :
    letI := sigmaOver X k
    Γ(∐ X, ⊤) ≃ₗ[k] (ι → k) := by
  letI := sigmaOver X k
  exact (sigmaGlobalSectionsLinearEquiv X k).trans <|
    LinearEquiv.piCongrRight fun i ↦
      (LinearEquiv.ofBijective (Algebra.linearMap k Γ(X i, ⊤)) (hb i)).symm

/-- If every component's base-ring map is bijective, the dimension of the global functions
on a finite coproduct is the number of components. -/
theorem finrank_globalSections_sigma_eq_card
    (k : Type u) [Field k] [Fintype ι]
    [∀ i, (X i).Over (Spec (CommRingCat.of k))]
    (hb : ∀ i, Function.Bijective
      ((X i).baseRingHom (CommRingCat.of k))) :
    letI := sigmaOver X k
    Module.finrank k Γ(∐ X, ⊤) = Fintype.card ι := by
  let _ := sigmaOver X k
  exact (sigmaGlobalSectionsLinearEquivBase X k hb).finrank_eq.trans
    (Module.finrank_pi k)

/-- A finite coproduct of integral schemes universally closed over an algebraically closed
field has one independent global constant on each component. -/
theorem finrank_globalSections_sigma_eq_card_of_isIntegral
    (k : Type u) [Field k] [IsAlgClosed k] [Fintype ι]
    [∀ i, (X i).Over (Spec (CommRingCat.of k))]
    [∀ i, IsIntegral (X i)]
    [∀ i, UniversallyClosed (X i ↘ Spec (CommRingCat.of k))] :
    letI := sigmaOver X k
    Module.finrank k Γ(∐ X, ⊤) = Fintype.card ι :=
  finrank_globalSections_sigma_eq_card X k fun i ↦
    bijective_baseRingHom_of_isAlgClosed k (X i)

/-- A finite coproduct of connected reduced schemes universally closed over an algebraically
closed field has one independent global constant on each component. -/
theorem finrank_globalSections_sigma_eq_card_of_isReduced_of_connected
    (k : Type u) [Field k] [IsAlgClosed k] [Fintype ι]
    [∀ i, (X i).Over (Spec (CommRingCat.of k))]
    [∀ i, IsReduced (X i)] [∀ i, ConnectedSpace (X i)]
    [∀ i, UniversallyClosed (X i ↘ Spec (CommRingCat.of k))] :
    letI := sigmaOver X k
    Module.finrank k Γ(∐ X, ⊤) = Fintype.card ι :=
  finrank_globalSections_sigma_eq_card X k fun i ↦
    bijective_baseRingHom_of_isAlgClosed_of_isReduced_of_connected k (X i)

/-- The degree-zero structure-sheaf cohomology of a finite coproduct has dimension equal to
the number of components when every component has only constant global functions. -/
lemma Modules.h_structureModule_sigma_zero_eq_card
    (k : Type u) [Field k] [Fintype ι]
    [∀ i, (X i).Over (Spec (CommRingCat.of k))]
    (hb : ∀ i, Function.Bijective
      ((X i).baseRingHom (CommRingCat.of k))) :
    letI := sigmaOver X k
    Modules.h k (structureModule (∐ X)) 0 = Fintype.card ι := by
  let _ := sigmaOver X k
  rw [Modules.h_structureModule_zero]
  exact finrank_globalSections_sigma_eq_card X k hb

/-- The degree-zero structure-sheaf cohomology of a finite coproduct of integral schemes
universally closed over an algebraically closed field counts its components. -/
lemma Modules.h_structureModule_sigma_zero_eq_card_of_isIntegral
    (k : Type u) [Field k] [IsAlgClosed k] [Fintype ι]
    [∀ i, (X i).Over (Spec (CommRingCat.of k))]
    [∀ i, IsIntegral (X i)]
    [∀ i, UniversallyClosed (X i ↘ Spec (CommRingCat.of k))] :
    letI := sigmaOver X k
    Modules.h k (structureModule (∐ X)) 0 = Fintype.card ι :=
  Modules.h_structureModule_sigma_zero_eq_card X k fun i ↦
    bijective_baseRingHom_of_isAlgClosed k (X i)

/-- Degree-zero cohomology of the pushforward of the structure sheaf from a finite coproduct
counts the components when every component has only constant global functions. -/
lemma Modules.h_zero_pushforward_structureModule_sigma_eq_card
    (k : Type u) [Field k] [Fintype ι]
    [∀ i, (X i).Over (Spec (CommRingCat.of k))]
    {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k))]
    (f : (∐ X) ⟶ Y)
    (hf : f ≫ (Y ↘ Spec (CommRingCat.of k)) = sigmaStructureMap X k)
    (hb : ∀ i, Function.Bijective
      ((X i).baseRingHom (CommRingCat.of k))) :
    letI := sigmaOver X k
    Modules.h k ((Modules.pushforward f).obj (structureModule (∐ X))) 0 =
      Fintype.card ι := by
  let _ := sigmaOver X k
  rw [Modules.h_zero_pushforward_eq_finrank_globalSections k f hf]
  exact finrank_globalSections_sigma_eq_card X k hb

/-- Degree-zero cohomology of the pushforward of the structure sheaf from a finite coproduct
of integral schemes universally closed over an algebraically closed field counts its
components. -/
lemma Modules.h_zero_pushforward_structureModule_sigma_eq_card_of_isIntegral
    (k : Type u) [Field k] [IsAlgClosed k] [Fintype ι]
    [∀ i, (X i).Over (Spec (CommRingCat.of k))]
    [∀ i, IsIntegral (X i)]
    [∀ i, UniversallyClosed (X i ↘ Spec (CommRingCat.of k))]
    {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k))]
    (f : (∐ X) ⟶ Y)
    (hf : f ≫ (Y ↘ Spec (CommRingCat.of k)) = sigmaStructureMap X k) :
    letI := sigmaOver X k
    Modules.h k ((Modules.pushforward f).obj (structureModule (∐ X))) 0 =
      Fintype.card ι :=
  Modules.h_zero_pushforward_structureModule_sigma_eq_card X k f hf fun i ↦
    bijective_baseRingHom_of_isAlgClosed k (X i)

end AlgebraicGeometry.Scheme

end
