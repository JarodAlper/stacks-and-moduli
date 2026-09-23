module

public import StacksAndModuli.API.NodalBranches
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.Ideal.GoingDown

/-!
# Components incident to formal branches

This file constructs the canonical irreducible component of a scheme incident to a formal
branch at one of its points.  The construction has two algebraic steps.  A minimal prime of
the completed local ring contracts to a minimal prime of the local ring because completion
is flat, and a local-ring minimal prime contracts through an affine-neighbourhood localization
to a minimal prime of the affine coordinate ring.  The corresponding generic point then closes
up to an irreducible component of the ambient scheme.

No assertion is made that distinct formal branches give distinct components: at a self-node,
the two branches are incident to the same component.

## Main definitions

* `AlgebraicGeometry.Scheme.stalkBranchComponent`: the component incident to a minimal prime
  of a stalk.
* `AlgebraicGeometry.Scheme.formalBranchComponent`: the component incident to a formal branch.
* `AlgebraicGeometry.Scheme.SplitNodeBranches.toComponent`: the flag-to-vertex map for the
  prospective dual graph of a nodal curve.

## Main results

* `Ideal.mem_minimalPrimes_under_of_flat`: contraction along a flat ring map preserves
  minimality of a prime minimal over zero.
* `Topology.IsOpenEmbedding.closure_singleton_mem_irreducibleComponents`: a component generic
  point of an open subspace remains a component generic point in the ambient space.
* `AlgebraicGeometry.Scheme.formalBranchComponent_mem`: the branch point lies on its incident
  component.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open TopologicalSpace

universe u v

namespace Ideal

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- A minimal prime contracts to a minimal prime along a flat ring map. -/
lemma mem_minimalPrimes_under_of_flat [Module.Flat R S] (Q : Ideal S)
    (hQ : Q ∈ minimalPrimes S) : Q.under R ∈ minimalPrimes R := by
  let _ : Q.IsPrime := hQ.isPrime
  refine ⟨⟨Ideal.IsPrime.under R Q, bot_le⟩, ?_⟩
  intro p hp hpQ
  let _ : p.IsPrime := hp.1
  obtain ⟨P, hPQ, hP, hPp⟩ :=
    Q.exists_ideal_le_liesOver_of_le (p := p) (q := Q.under R) hpQ
  have hPQeq : P = Q := le_antisymm hPQ (hQ.2 ⟨hP, bot_le⟩ hPQ)
  exact le_of_eq ((congrArg (fun J : Ideal S ↦ J.under R) hPQeq.symm).trans hPp.over.symm)

end Ideal

namespace Topology.IsOpenEmbedding

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- If `y` is the generic point of an irreducible component of an open subspace, then its
image is the generic point of an irreducible component of the ambient space. -/
lemma closure_singleton_mem_irreducibleComponents {f : X → Y} (hf : IsOpenEmbedding f)
    (y : X) (hy : closure ({y} : Set X) ∈ irreducibleComponents X) :
    closure ({f y} : Set Y) ∈ irreducibleComponents Y := by
  refine ⟨isIrreducible_singleton.closure, fun Z hZ hsub ↦ ?_⟩
  have hyZ : y ∈ f ⁻¹' Z := hsub (subset_closure (Set.mem_singleton (f y)))
  have hpre_irred : IsIrreducible (f ⁻¹' Z) :=
    hZ.preimage hf ⟨f y, hyZ, y, rfl⟩
  have hpre_closure_irred : IsIrreducible (closure (f ⁻¹' Z)) := hpre_irred.closure
  have hy_le : closure ({y} : Set X) ⊆ closure (f ⁻¹' Z) :=
    closure_mono (Set.singleton_subset_iff.mpr hyZ)
  have hclosure_le : closure (f ⁻¹' Z) ⊆ closure ({y} : Set X) :=
    hy.2 hpre_closure_irred hy_le
  have hinter_nonempty : (Z ∩ Set.range f).Nonempty := ⟨f y, hyZ, y, rfl⟩
  refine (subset_closure_inter_of_isPreirreducible_of_isOpen hZ.isPreirreducible
    hf.isOpen_range hinter_nonempty).trans ?_
  refine closure_minimal ?_ isClosed_closure
  rintro z ⟨hzZ, x, rfl⟩
  simpa only [Set.image_singleton] using image_closure_subset_closure_image hf.continuous
    ⟨x, hclosure_le (subset_closure hzZ), rfl⟩

end Topology.IsOpenEmbedding

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (x : X)

/-- The point of the local spectrum determined by a minimal prime of the stalk. -/
def stalkBranchPoint (p : minimalPrimes (X.presheaf.stalk x)) :
    Spec (X.presheaf.stalk x) :=
  ⟨p.1, p.2.isPrime⟩

/-- The canonical affine neighbourhood used to assign a stalk branch to an ambient
irreducible component. -/
noncomputable abbrev branchAffineOpen : X.Opens :=
  (X.affineCover.f (X.affineCover.idx x)).opensRange

/-- Contraction of a stalk minimal prime to the coordinate ring of the canonical affine
neighbourhood. -/
noncomputable def stalkBranchContraction (p : minimalPrimes (X.presheaf.stalk x)) :
    minimalPrimes Γ(X, X.branchAffineOpen x) := by
  let U := X.branchAffineOpen x
  let hU : IsAffineOpen U := isAffineOpen_opensRange (X.affineCover.f (X.affineCover.idx x))
  let hxU : x ∈ U := X.affineCover.covers x
  let _ : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    (X.presheaf.germ U x hxU).hom.toAlgebra
  let _ := hU.isLocalization_stalk ⟨x, hxU⟩
  let q : Ideal Γ(X, U) := p.1.under Γ(X, U)
  have hq : q ∈ minimalPrimes Γ(X, U) := by
    have hp : p.1 ∈ ((⊥ : Ideal Γ(X, U)).map
        (algebraMap Γ(X, U) (X.presheaf.stalk x))).minimalPrimes := by
      simpa only [Ideal.map_bot] using p.2
    rw [IsLocalization.minimalPrimes_map
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl (X.presheaf.stalk x)
        (⊥ : Ideal Γ(X, U))] at hp
    exact hp
  exact ⟨q, hq⟩

/-- The contracted stalk branch is the ideal-theoretic contraction along the germ map of
the canonical affine neighbourhood. -/
@[simp]
lemma stalkBranchContraction_val (p : minimalPrimes (X.presheaf.stalk x)) :
    (X.stalkBranchContraction x p : Ideal Γ(X, X.branchAffineOpen x)) =
      p.1.comap (X.presheaf.germ (X.branchAffineOpen x) x (X.affineCover.covers x)).hom :=
  rfl

/-- The canonical point of the affine-neighbourhood spectrum determined by a minimal prime
of the stalk. -/
noncomputable def stalkBranchGenericPoint (p : minimalPrimes (X.presheaf.stalk x)) :
    Spec Γ(X, X.branchAffineOpen x) :=
  ⟨(X.stalkBranchContraction x p).1, (X.stalkBranchContraction x p).2.isPrime⟩

/-- The ideal of the generic point associated to a stalk branch is its contraction to the
canonical affine neighbourhood. -/
@[simp]
lemma stalkBranchGenericPoint_asIdeal (p : minimalPrimes (X.presheaf.stalk x)) :
    (X.stalkBranchGenericPoint x p).asIdeal = X.stalkBranchContraction x p :=
  rfl

/-- Mapping a stalk branch point to the scheme agrees with first contracting it to the
canonical affine neighbourhood and then using that open immersion. -/
lemma fromSpecStalk_stalkBranchPoint_eq (p : minimalPrimes (X.presheaf.stalk x)) :
    X.fromSpecStalk x (X.stalkBranchPoint x p) =
      let U := X.branchAffineOpen x
      let hU : IsAffineOpen U :=
        isAffineOpen_opensRange (X.affineCover.f (X.affineCover.idx x))
      hU.fromSpec (X.stalkBranchGenericPoint x p) := by
  let U := X.branchAffineOpen x
  let hU : IsAffineOpen U := isAffineOpen_opensRange (X.affineCover.f (X.affineCover.idx x))
  let hxU : x ∈ U := X.affineCover.covers x
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU]
  change hU.fromSpec (Spec.map (X.presheaf.germ U x hxU) (X.stalkBranchPoint x p)) =
    hU.fromSpec (X.stalkBranchGenericPoint x p)
  congr 1

/-- The irreducible component incident to a minimal prime of the stalk at `x`. -/
noncomputable def stalkBranchComponent (p : minimalPrimes (X.presheaf.stalk x)) :
    irreducibleComponents X := by
  let U := X.branchAffineOpen x
  let hU : IsAffineOpen U := isAffineOpen_opensRange (X.affineCover.f (X.affineCover.idx x))
  let y := X.stalkBranchGenericPoint x p
  refine ⟨closure ({X.fromSpecStalk x (X.stalkBranchPoint x p)} : Set X), ?_⟩
  rw [X.fromSpecStalk_stalkBranchPoint_eq x p]
  apply hU.fromSpec.isOpenEmbedding.closure_singleton_mem_irreducibleComponents
  change closure ({y} : Set (PrimeSpectrum Γ(X, U))) ∈
    irreducibleComponents (PrimeSpectrum Γ(X, U))
  rw [← PrimeSpectrum.vanishingIdeal_mem_minimalPrimes,
    PrimeSpectrum.vanishingIdeal_singleton]
  exact (X.stalkBranchContraction x p).2

/-- The underlying set of the component assigned to a stalk branch is the closure of the
image of its local generic point. -/
@[simp]
lemma stalkBranchComponent_val (p : minimalPrimes (X.presheaf.stalk x)) :
    (X.stalkBranchComponent x p).1 =
      closure ({X.fromSpecStalk x (X.stalkBranchPoint x p)} : Set X) :=
  rfl

/-- The point `x` lies on the irreducible component incident to every stalk branch at `x`. -/
lemma stalkBranchComponent_mem (p : minimalPrimes (X.presheaf.stalk x)) :
    x ∈ (X.stalkBranchComponent x p).1 := by
  change x ∈ closure ({X.fromSpecStalk x (X.stalkBranchPoint x p)} : Set X)
  have hspec := IsLocalRing.specializes_closedPoint (X.stalkBranchPoint x p)
  have hspec' := hspec.map (X.fromSpecStalk x).continuous
  rw [Scheme.fromSpecStalk_closedPoint] at hspec'
  exact hspec'.mem_closure

/-- A formal branch contracts from the completed local ring to a minimal prime of the
ordinary local ring. -/
noncomputable def FormalBranchesAt.toStalkBranch
    [IsNoetherianRing (X.presheaf.stalk x)]
    (b : X.FormalBranchesAt x) :
    minimalPrimes (X.presheaf.stalk x) := by
  letI : Module.Flat (X.presheaf.stalk x) (X.completedLocalRing x) := inferInstance
  exact ⟨b.1.under (X.presheaf.stalk x),
    Ideal.mem_minimalPrimes_under_of_flat b.1 b.2⟩

/-- A formal branch contracts along the canonical map from the stalk to its completion. -/
@[simp]
lemma FormalBranchesAt.toStalkBranch_val [IsNoetherianRing (X.presheaf.stalk x)]
    (b : X.FormalBranchesAt x) :
    (b.toStalkBranch : Ideal (X.presheaf.stalk x)) =
      b.1.comap (X.toCompletedLocalRing x) :=
  rfl

/-- The irreducible component of `X` incident to a formal branch at `x`. -/
noncomputable def formalBranchComponent [IsNoetherianRing (X.presheaf.stalk x)]
    (b : X.FormalBranchesAt x) :
    irreducibleComponents X :=
  X.stalkBranchComponent x b.toStalkBranch

/-- The component assigned to a formal branch is the closure of the image of its contracted
local generic point. -/
@[simp]
lemma formalBranchComponent_val [IsNoetherianRing (X.presheaf.stalk x)]
    (b : X.FormalBranchesAt x) :
    (X.formalBranchComponent x b).1 =
      closure ({X.fromSpecStalk x (X.stalkBranchPoint x b.toStalkBranch)} : Set X) :=
  rfl

/-- The underlying point of a formal branch lies on its incident irreducible component. -/
lemma formalBranchComponent_mem [IsNoetherianRing (X.presheaf.stalk x)]
    (b : X.FormalBranchesAt x) :
    x ∈ (X.formalBranchComponent x b).1 :=
  X.stalkBranchComponent_mem x b.toStalkBranch

/-- The component incident to a global split-node branch.  For the dual graph of a nodal
curve, this is the map from flags to vertices. -/
noncomputable def SplitNodeBranches.toComponent {k : Type u} [Field k]
    [X.Over (Spec (CommRingCat.of k))] [IsLocallyNoetherian X]
    (b : X.SplitNodeBranches k) : irreducibleComponents X :=
  X.formalBranchComponent b.1.1 b.2

/-- The split node underlying a branch lies on the component assigned to that branch. -/
lemma SplitNodeBranches.node_mem_toComponent {k : Type u} [Field k]
    [X.Over (Spec (CommRingCat.of k))] [IsLocallyNoetherian X]
    (b : X.SplitNodeBranches k) : b.1.1 ∈ b.toComponent.1 :=
  X.formalBranchComponent_mem b.1.1 b.2

end AlgebraicGeometry.Scheme
