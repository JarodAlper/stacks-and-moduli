module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Topology.Category.TopCat.GrothendieckTopology

/-!
# Grothendieck topologies and sites: definitions and first examples

This module formalizes the subsection *Definitions and first examples* (unlabelled) of
§3.2 (Grothendieck topologies and sites) of *Stacks and Moduli*,
section label `sec:sites`. It covers the definition of a
Grothendieck topology and a site (`D:site`), the site of open subsets of a topological space
with the small Zariski site of a scheme (`ex:topological-space-grothendeick-topology`), and
the small étale site of a scheme (`ex:small-etale-site-scheme`).

All of this material is already available in Mathlib, so this file consists of `example`
declarations recalling the corresponding Mathlib declarations.

Main results:
- `CategoryTheory.Pretopology` and `CategoryTheory.GrothendieckTopology` for the
  covering-family and sieve formulations of a site (`D:site`);
- `TopologicalSpace.Opens.grothendieckTopology` for the site of a topological space
  (`ex:topological-space-grothendeick-topology`);
- `AlgebraicGeometry.Scheme.smallEtaleTopology` for the small étale site
  (`ex:small-etale-site-scheme`).

-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section DSite

open CategoryTheory Limits

/- **Definition 3.2.1** (`D:site`): Let $\cS$ be a category with fiber products. A
*Grothendieck topology* on $\cS$ (in the covering-families form of the book, called a
*pretopology* in Mathlib and SGA 4) assigns to each object $X$ a set of *coverings*
$\{X_i \to X\}_{i \in I}$ such that: (1) isomorphisms are coverings; (2) the base change of a
covering along any morphism $Y \to X$ is a covering of $Y$; (3) a covering of $X$ composed
with coverings of each of its members is a covering of $X$. A *site* is a category equipped
with a Grothendieck topology.

In Mathlib, coverings of $X$ are `Presieve`s on $X$: an indexed family `{Xᵢ → X}` is rendered
as the presieve `Presieve.ofArrows X f`. -/
example (𝒮 : Type*) [Category 𝒮] [HasPullbacks 𝒮] := Pretopology 𝒮

/- API projection from Definition 3.2.1 (axiom (1), identity): if $X' \to X$ is an isomorphism,
then $(X' \to X) \in \Cov(X)$. -/
example {𝒮 : Type*} [Category 𝒮] [HasPullbacks 𝒮] (K : Pretopology 𝒮) {X X' : 𝒮}
    (f : X' ⟶ X) [IsIso f] :
    Presieve.singleton f ∈ K X :=
  K.has_isos f

/- API projection from Definition 3.2.1 (axiom (2), restriction): if $\{X_i \to X\} \in \Cov(X)$
and $Y \to X$ is a morphism, then the fiber products $X_i \times_X Y$ exist and
$\{X_i \times_X Y \to Y\} \in \Cov(Y)$. -/
example {𝒮 : Type*} [Category 𝒮] [HasPullbacks 𝒮] (K : Pretopology 𝒮) {X Y : 𝒮}
    (f : Y ⟶ X) (R : Presieve X) (hR : R ∈ K X) :
    Presieve.pullbackArrows f R ∈ K Y :=
  K.pullbacks f R hR

/- API projection from Definition 3.2.1 (axiom (3), composition): if $\{X_i \to X\} \in \Cov(X)$
and $\{X_{ij} \to X_i\} \in \Cov(X_i)$ for each $i$, then the family of composites
$\{X_{ij} \to X_i \to X\}$ belongs to $\Cov(X)$. In Mathlib the composed family is the
presieve `R.bind Ti`. -/
example {𝒮 : Type*} [Category 𝒮] [HasPullbacks 𝒮] (K : Pretopology 𝒮) {X : 𝒮}
    (R : Presieve X) (Ti : ∀ ⦃Y⦄ (f : Y ⟶ X), R f → Presieve Y) (hR : R ∈ K X)
    (hTi : ∀ ⦃Y⦄ (f : Y ⟶ X) (H : R f), Ti f H ∈ K Y) :
    R.bind Ti ∈ K X :=
  K.transitive R Ti hR hTi

/- Background definition for Definition 3.2.1 (the `Precoverage` data): Mathlib also isolates the raw
data of the definition: a `Precoverage` assigns to each object a set of covering presieves,
with no axioms. The three site axioms are then available as the typeclasses
`Precoverage.HasIsos`, `Precoverage.IsStableUnderBaseChange` (together with
`Precoverage.HasPullbacks` for the existence of the fiber products), and
`Precoverage.IsStableUnderComposition`. This variant does not require the ambient category to
have all pullbacks, exactly as in the book, where only fiber products along coverings are
required to exist. -/
example (𝒮 : Type*) [Category 𝒮] := Precoverage 𝒮

/- API projection from Definition 3.2.1 (the existence clause in axiom (2) for
precoverages): every covering presieve has pullbacks along every morphism. Unlike the
`Pretopology` rendering above, this asks only for the pullbacks that occur in the book's
restriction axiom. -/
example {𝒮 : Type*} [Category 𝒮] (J : Precoverage 𝒮) [J.HasPullbacks]
    {X Y : 𝒮} {R : Presieve Y} (f : X ⟶ Y) (hR : R ∈ J Y) :
    R.HasPullbacks f :=
  J.hasPullbacks_of_mem f hR

/- API projection from Definition 3.2.1 (axiom (1) for precoverages). -/
example {𝒮 : Type*} [Category 𝒮] (J : Precoverage 𝒮) [J.HasIsos] {X X' : 𝒮} (f : X' ⟶ X)
    [IsIso f] :
    Presieve.singleton f ∈ J X :=
  Precoverage.mem_coverings_of_isIso f

/- API projection from Definition 3.2.1 (axiom (2) for precoverages), stated for indexed families
`{Xᵢ → X}` exactly as in the book: given a covering `{Xᵢ → X}`, a morphism `g : Y ⟶ X`, and
fiber products `Pᵢ = Xᵢ ×_X Y`, the family `{Pᵢ → Y}` is a covering of `Y`. -/
example {𝒮 : Type*} [Category 𝒮] (J : Precoverage 𝒮) [J.IsStableUnderBaseChange]
    {ι : Type*} {X : 𝒮} {Xi : ι → 𝒮} (f : ∀ i, Xi i ⟶ X)
    (hf : Presieve.ofArrows Xi f ∈ J X) {Y : 𝒮} (g : Y ⟶ X)
    {P : ι → 𝒮} (p₁ : ∀ i, P i ⟶ Y) (p₂ : ∀ i, P i ⟶ Xi i)
    (h : ∀ i, IsPullback (p₁ i) (p₂ i) g (f i)) :
    Presieve.ofArrows P p₁ ∈ J Y :=
  Precoverage.mem_coverings_of_isPullback f hf g p₁ p₂ h

/- API projection from Definition 3.2.1 (axiom (3) for precoverages), stated for indexed families
exactly as in the book: given a covering `{Xᵢ → X}` and coverings `{Y i j → Xᵢ}` for each
`i`, the family of composites `{Y i j → Xᵢ → X}` indexed by pairs `(i, j)` is a covering of
`X`. -/
example {𝒮 : Type*} [Category 𝒮] (J : Precoverage 𝒮) [J.IsStableUnderComposition]
    {ι : Type*} {X : 𝒮} {Xi : ι → 𝒮} (f : ∀ i, Xi i ⟶ X)
    (hf : Presieve.ofArrows Xi f ∈ J X) {σ : ι → Type*} {Y : ∀ i, σ i → 𝒮}
    (g : ∀ i j, Y i j ⟶ Xi i) (hg : ∀ i, Presieve.ofArrows (Y i) (g i) ∈ J (Xi i)) :
    Presieve.ofArrows (fun p : Σ i, σ i ↦ Y p.1 p.2) (fun p ↦ g p.1 p.2 ≫ f p.1) ∈ J X :=
  Precoverage.comp_mem_coverings f hf g hg

/- **Definition 3.2.1** (`D:site`) (the sieve-theoretic variant): the sieve-theoretic notion
of Grothendieck topology of SGA 4 (mentioned in the historical remarks of the book) is
Mathlib's `GrothendieckTopology`; a pretopology generates one via
`Pretopology.toGrothendieck`. Mathlib states the sheaf and stack conditions with respect to a
`GrothendieckTopology`, and a "site" is a category equipped with one. -/
example (𝒮 : Type*) [Category 𝒮] := GrothendieckTopology 𝒮

/- API construction associated to Definition 3.2.1 (the topology generated by a pretopology). -/
example {𝒮 : Type*} [Category 𝒮] [HasPullbacks 𝒮] (K : Pretopology 𝒮) :
    GrothendieckTopology 𝒮 :=
  K.toGrothendieck

end DSite

section ExTopologicalSpaceGrothendeickTopology

open CategoryTheory TopologicalSpace AlgebraicGeometry

/- **Example 3.2.3** (`ex:topological-space-grothendeick-topology`) (the category of opens):
for a topological space $X$, the category $\Op(X)$ of open sets $U \subseteq X$, with a
unique morphism $U \to V$ if and only if $U \subseteq V$. -/
example (X : Type*) [TopologicalSpace X] : Category (Opens X) :=
  inferInstance

/- A morphism $U \to V$ in $\Op(X)$ is an inclusion $U \subseteq V$. -/
example {X : Type*} [TopologicalSpace X] {U V : Opens X} (h : U ≤ V) : U ⟶ V :=
  homOfLE h

/- A morphism $U \to V$ exists if and only if $U \subseteq V$. -/
example {X : Type*} [TopologicalSpace X] {U V : Opens X} :
    Nonempty (U ⟶ V) ↔ U ≤ V :=
  ⟨fun ⟨f⟩ ↦ leOfHom f, fun h ↦ ⟨homOfLE h⟩⟩

/- There is at most one morphism between two opens. -/
example {X : Type*} [TopologicalSpace X] {U V : Opens X} :
    Subsingleton (U ⟶ V) :=
  inferInstance

/- **Example 3.2.3** (`ex:topological-space-grothendeick-topology`): the Grothendieck
topology on $\Op(X)$: a covering of $U$ is a collection of open subsets $\{U_i\}$ with
$U = \bigcup_i U_i$; Mathlib directly defines the generated sieve-theoretic topology, in
which a sieve covers $U$ when its members jointly contain every point of $U$. -/
example (X : Type*) [TopologicalSpace X] : GrothendieckTopology (Opens X) :=
  Opens.grothendieckTopology X

/- **Example 3.2.3** (`ex:topological-space-grothendeick-topology`) (the covering-families
form): the corresponding pretopology, whose coverings of `U` are the families of opens whose
union is `U`. -/
example (X : Type*) [TopologicalSpace X] : Pretopology (Opens X) :=
  Opens.pretopology X

/- **Example 3.2.3** (`ex:topological-space-grothendeick-topology`) (description of the
covering families): a family of opens `Vᵢ ⊆ U` is a covering in the topological pretopology
exactly when their union is `U`. -/
example {X : Type*} [TopologicalSpace X] {U : Opens X} {ι : Type*}
    {V : ι → Opens X} (f : ∀ i, V i ⟶ U) :
    Presieve.ofArrows V f ∈ Opens.pretopology X U ↔ iSup V = U := by
  change
    (∀ x ∈ U, ∃ (W : Opens X) (g : W ⟶ U), Presieve.ofArrows V f g ∧ x ∈ W) ↔ _
  constructor
  · intro h
    apply le_antisymm
    · exact iSup_le fun i ↦ leOfHom (f i)
    · intro x hx
      obtain ⟨W, g, hg, hxW⟩ := h x hx
      exact le_iSup V hg.idx (by simpa [hg.obj_idx] using hxW)
  · intro h x hx
    have hx' : x ∈ iSup V := h.symm.le hx
    rw [Opens.mem_iSup] at hx'
    obtain ⟨i, hxi⟩ := hx'
    exact ⟨V i, f i, Presieve.ofArrows.mk i, hxi⟩

/- The pretopology generates the Grothendieck topology. -/
example (X : Type*) [TopologicalSpace X] :
    (Opens.pretopology X).toGrothendieck = Opens.grothendieckTopology X :=
  Opens.pretopology_toGrothendieck X

/- **Example 3.2.3** (`ex:topological-space-grothendeick-topology`) (the small Zariski site):
the small Zariski site $X_{\Zar}$ of a scheme $X$: the site of open subsets of the underlying
topological space of $X$. -/
example (X : Scheme) : GrothendieckTopology (Opens X) :=
  Opens.grothendieckTopology X

end ExTopologicalSpaceGrothendeickTopology

section ExSmallEtaleSiteScheme

open CategoryTheory AlgebraicGeometry

universe u

/- **Example 3.2.4** (`ex:small-etale-site-scheme`) (the underlying category): the underlying
category of the small étale site of a scheme $X$: schemes étale over $X$, where a morphism
$(U \to X) \to (V \to X)$ is an $X$-morphism $U \to V$. -/
example (X : Scheme.{u}) := X.Etale

/- An étale morphism `U ⟶ X` determines an object of the small étale site. -/
example {X U : Scheme.{u}} (f : U ⟶ X) [Etale f] : X.Etale :=
  Scheme.Etale.mk f

/- **Example 3.2.4** (`ex:small-etale-site-scheme`) (the parenthetical "which is necessarily
étale"): a morphism between schemes étale over $X$ is automatically étale. -/
example {X U V : Scheme.{u}} (f : U ⟶ X) (g : V ⟶ X) [Etale f] [Etale g] (h : U ⟶ V)
    (w : h ≫ g = f) : Etale h :=
  MorphismProperty.of_postcomp (W := @Etale) (W' := @Etale) h g inferInstance
    (by rw [w]; infer_instance)

/- **Example 3.2.4** (`ex:small-etale-site-scheme`): the small étale site of a scheme $X$:
coverings are jointly surjective families of morphisms in $X_{\et}$. -/
example (X : Scheme.{u}) : GrothendieckTopology X.Etale :=
  X.smallEtaleTopology

/- The pretopology generating the small étale site. -/
example (X : Scheme.{u}) : Pretopology X.Etale :=
  X.smallEtalePretopology

/- **Example 3.2.4** (`ex:small-etale-site-scheme`) (description of the coverings): a family
of morphisms in $X_{\et}$ is a covering for the small étale topology if and only if it is
jointly surjective. -/
example {X : Scheme.{u}} {W : X.Etale} {ι : Type u} {Z : ι → X.Etale} (f : ∀ i, Z i ⟶ W) :
    Sieve.ofArrows Z f ∈ X.smallEtaleTopology W ↔ ⋃ i, Set.range (f i).left = Set.univ :=
  Scheme.ofArrows_mem_smallEtaleTopology_iff f

end ExSmallEtaleSiteScheme
