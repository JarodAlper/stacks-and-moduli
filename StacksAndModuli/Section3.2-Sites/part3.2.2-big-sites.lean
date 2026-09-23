module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.Topology.Category.TopCat.GrothendieckTopology

/-!
# Big sites

This module formalizes the examples of big sites of the subsection *Big sites*
(Subsection 3.2.2, `subsec:big-sites`) of §3.2 (Grothendieck topologies and sites) of
*Stacks and Moduli*: the big étale site
(`ex:big-etale-site`), the big topological and big Zariski sites (`ex:big-zariski-site`),
and the big fppf and fpqc sites (`ex:big-fppf-site`).

All of this material is already available in Mathlib, so this file consists of `example`
declarations recalling the corresponding Mathlib declarations.

Main results:
- `AlgebraicGeometry.Scheme.etaleTopology` for the big étale site (`ex:big-etale-site`);
- `TopCat.grothendieckTopology` for the big topological site and
  `AlgebraicGeometry.Scheme.zariskiTopology` for the big Zariski site
  (`ex:big-zariski-site`);
- `AlgebraicGeometry.Scheme.fppfTopology` for the big fppf site and
  `AlgebraicGeometry.Scheme.fpqcTopology` for the big fpqc site (`ex:big-fppf-site`).

The restricted sites, the lisse-étale site, and the big affine sites of the same subsection
are formalized in `part3.2.3-restricted-and-affine-sites`. Per-label completeness is tracked
in this folder's STATUS.md.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section ExBigEtaleSite

open CategoryTheory AlgebraicGeometry

universe u

/- **Example 3.2.5** (`ex:big-etale-site`): the big étale site $\Sch_{\et}$: the category of
schemes, where a covering of a scheme $U$ is a jointly surjective collection of étale
morphisms $\{U_i \to U\}$. -/
example : Precoverage Scheme.{u} :=
  Scheme.etalePrecoverage

/- **Example 3.2.5** (`ex:big-etale-site`) (description of the coverings): a family
`{Uᵢ → U}` is an étale covering exactly when every map is étale and the family is jointly
surjective. -/
example {S : Scheme.{u}} {ι : Type*} {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ S) :
    Presieve.ofArrows X f ∈ Scheme.etalePrecoverage S ↔
      (∀ s : S, ∃ i, s ∈ Set.range (f i)) ∧ ∀ i, Etale (f i) :=
  Scheme.ofArrows_mem_precoverage_iff (P := @Etale)

/- **Example 3.2.5** (`ex:big-etale-site`) (pretopology and sieve-theoretic forms): the étale
pretopology and the (sieve-theoretic) étale topology on the category of schemes. -/
example : Pretopology Scheme.{u} :=
  Scheme.etalePretopology

example : GrothendieckTopology Scheme.{u} :=
  Scheme.etaleTopology

end ExBigEtaleSite

section ExBigZariskiSite

open CategoryTheory AlgebraicGeometry

universe u

/- Result of the unlabelled "Big topological site" example in Subsection 3.2.2
site"): the big topological site: the category $\Top$ of topological spaces, where a
covering of $U$ is a jointly surjective collection of open embeddings
$\{U_i \hookrightarrow U\}$. -/
example : Precoverage TopCat.{u} :=
  TopCat.precoverage

/- Result of the unlabelled "Big topological site" example in Subsection 3.2.2
site", description of the coverings): a family of maps of topological spaces is a covering
exactly when its members are open embeddings and their images jointly cover the target. -/
example {X : TopCat.{u}} {ι : Type*} {Y : ι → TopCat.{u}} (f : ∀ i, Y i ⟶ X) :
    Presieve.ofArrows Y f ∈ TopCat.precoverage X ↔
      (∀ x, ∃ i, x ∈ Set.range (f i)) ∧ ∀ i, Topology.IsOpenEmbedding (f i) := by
  rw [TopCat.precoverage]
  change
    (Presieve.ofArrows Y f ∈
        Types.jointlySurjectivePrecoverage.comap (forget TopCat) X ∧
      Presieve.ofArrows Y f ∈ TopCat.isOpenEmbedding.precoverage X) ↔ _
  simp only [Presieve.ofArrows_mem_comap_jointlySurjectivePrecoverage_iff,
    MorphismProperty.ofArrows_mem_precoverage, TopCat.isOpenEmbedding_iff]
  constructor <;> rintro ⟨h, hP⟩ <;> refine ⟨?_, hP⟩
  · intro x
    obtain ⟨i, y, hy⟩ := h x
    exact ⟨i, y, hy⟩
  · intro x
    obtain ⟨i, y, hy⟩ := h x
    exact ⟨i, y, hy⟩

example : GrothendieckTopology TopCat.{u} :=
  TopCat.grothendieckTopology

/- **Example 3.2.7** (`ex:big-zariski-site`): the big Zariski site $\Sch_{\Zar}$: replacing
étale morphisms in the big étale site by open immersions. -/
example : Precoverage Scheme.{u} :=
  Scheme.zariskiPrecoverage

/- **Example 3.2.7** (`ex:big-zariski-site`) (description of the coverings): a family
`{Uᵢ → U}` is a Zariski covering exactly when every map is an open immersion and the
family is jointly surjective. -/
example {S : Scheme.{u}} {ι : Type*} {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ S) :
    Presieve.ofArrows X f ∈ Scheme.zariskiPrecoverage S ↔
      (∀ s : S, ∃ i, s ∈ Set.range (f i)) ∧ ∀ i, IsOpenImmersion (f i) :=
  Scheme.ofArrows_mem_precoverage_iff (P := @IsOpenImmersion)

example : Pretopology Scheme.{u} :=
  Scheme.zariskiPretopology

example : GrothendieckTopology Scheme.{u} :=
  Scheme.zariskiTopology

/- Zariski coverings are étale coverings. -/
example : Scheme.zariskiTopology.{u} ≤ Scheme.etaleTopology :=
  Scheme.zariskiTopology_le_etaleTopology

end ExBigZariskiSite

section ExBigFppfSite

open CategoryTheory AlgebraicGeometry

universe u

/- **Example 3.2.8** (`ex:big-fppf-site`): the big fppf site $\Sch_{\fppf}$: a covering of
$U$ is a jointly surjective collection of flat morphisms locally of finite presentation
$\{U_i \to U\}$; equivalently a collection with $\coprod_i U_i \to U$ fppf, i.e. surjective,
flat, and locally of finite presentation. -/
example : Precoverage Scheme.{u} :=
  Scheme.fppfPrecoverage

/- **Example 3.2.8** (`ex:big-fppf-site`) (description of the coverings): a family
`{Uᵢ → U}` is an fppf covering exactly when it is jointly surjective and every map is
flat and locally of finite presentation. -/
example {S : Scheme.{u}} {ι : Type*} {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ S) :
    Presieve.ofArrows X f ∈ Scheme.fppfPrecoverage S ↔
      (∀ s : S, ∃ i, s ∈ Set.range (f i)) ∧
        ∀ i, Flat (f i) ∧ LocallyOfFinitePresentation (f i) := by
  rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
  rfl

example : GrothendieckTopology Scheme.{u} :=
  Scheme.fppfTopology

/- **Example 3.2.8** (`ex:big-fppf-site`) (singleton coverings): a single surjective, flat
morphism which is locally of finite presentation (i.e. an fppf morphism) is an fppf
covering. -/
example {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f]
    [LocallyOfFinitePresentation f] :
    Presieve.singleton f ∈ Scheme.fppfPrecoverage Y :=
  f.singleton_mem_fppfPrecoverage

/- Result of the unlabelled "Big fpqc site" example in Subsection 3.2.2: the
big fpqc site: a covering of $U$ is a jointly surjective collection of flat morphisms
$\{U_i \to U\}$ subject to the quasi-compactness condition characterizing fpqc families (each
quasi-compact open of $U$ is the image of a quasi-compact open of $\coprod_i U_i$). -/
example : Precoverage Scheme.{u} :=
  Scheme.fpqcPrecoverage

/- Result of the unlabelled "Big fpqc site" example in Subsection 3.2.2
description of the coverings): an indexed family is an fpqc covering exactly when it is a
quasi-compact cover, is jointly surjective, and all of its maps are flat. The
`QuasiCompactCover` condition is Mathlib's family-wise formulation of the book's condition
on quasi-compact subsets of the target. -/
example {S : Scheme.{u}} (E : PreZeroHypercover.{u} S) :
    E.presieve₀ ∈ Scheme.fpqcPrecoverage S ↔
      QuasiCompactCover E ∧
        ((∀ s : S, ∃ i, s ∈ Set.range (E.f i)) ∧ ∀ i, Flat (E.f i)) := by
  rw [Scheme.fpqcPrecoverage]
  change
    (E.presieve₀ ∈ Scheme.qcPrecoverage S ∧
      E.presieve₀ ∈ Scheme.precoverage @Flat S) ↔ _
  rw [Scheme.presieve₀_mem_qcPrecoverage_iff,
    Scheme.presieve₀_mem_precoverage_iff]

example : GrothendieckTopology Scheme.{u} :=
  Scheme.fpqcTopology

/- Result of the unlabelled "Big fpqc site" example in Subsection 3.2.2
singleton coverings): a single surjective, flat, quasi-compact morphism is an fpqc
covering. -/
example {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f] [QuasiCompact f] :
    Presieve.singleton f ∈ Scheme.fpqcPrecoverage Y :=
  f.singleton_mem_fpqcPrecoverage

/- Every fppf covering is an fpqc covering. -/
example : Scheme.fppfTopology.{u} ≤ Scheme.fpqcTopology :=
  Scheme.fppfTopology_le_fpqcTopology

end ExBigFppfSite
