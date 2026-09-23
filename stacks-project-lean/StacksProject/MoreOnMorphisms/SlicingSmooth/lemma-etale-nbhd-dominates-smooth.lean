module

public import StacksProject.API.EtaleNeighborhood
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty

/-!
# Smooth morphisms admit étale-local sections

Stacks Project §`055S` (`more-morphisms-section-etale-over-smooth`, Slicing smooth morphisms)
of `more-morphisms.tex`, tags **055U** and **055V**.

- **055U** `more-morphisms-lemma-etale-nbhd-dominates-smooth`, which carries the Stacks Project
  slogan *"Smooth morphisms admit étale local sections"*:
  > Let `f : X → S` be a smooth morphism of schemes and `s ∈ S` a point in the image of `f`.
  > Then there exists an étale neighbourhood `(S', s') → (S, s)` and an `S`-morphism `S' → X`.

  (Reference: EGA IV, Corollaire 17.16.3 (ii).)

- **055V** `more-morphisms-lemma-etale-dominates-smooth`:
  > Let `S` be a scheme and `𝒰 = {S_i → S}` a smooth covering of `S`. Then there exists an
  > étale covering `𝒱 = {T_j → S}` which refines `𝒰`.

This is what §3.3 needs in order to prove that a surjective smooth morphism is an epimorphism of
sheaves on the big étale site: 055V is the formal covering-refinement step, and 055U is the
geometric input it rests on.

Mathlib has none of this: searching for a section-existence result for smooth morphisms turns up
nothing. It does have the two ingredients the Stacks proof uses —
`Mathlib/RingTheory/Smooth/StandardSmooth.lean` (smooth is Zariski-locally standard smooth) and
a good étale-neighbourhood API (`Algebra.exists_etale_of_isEtaleAt`,
`AlgebraicGeometry.exists_etale_isCompl_of_quasiFiniteAt`).

**Proof route (Stacks Project).** By slicing: `057G`
(`more-morphisms-lemma-slice-smooth`) says that if `f` is smooth at `x`, `x` is a closed point
of its fibre `X_s`, and `κ(s) ⊆ κ(x)` is separable, then there is an immersion `Z → X` through
`x` with `Z → S` étale and `Z_s = {x}`. That is proved by induction on the relative dimension,
slicing by elements of `m_x` (`057C`, `057D`, `057F`), using
`varieties-lemma-smooth-separable-closed-points-dense` to arrange the separability. 055U follows
by taking `Z` as the étale neighbourhood, and 055V by applying 055U at every point.

**Formal proof route.** `StacksProject.API.EtaleNeighborhood` instead proves the affine-target
case from a rational point on a separably closed geometric fibre, spreads its finite coordinate
data to a standard étale algebra, and clears the remaining denominators with one principal
localization. The theorem below chooses a `Spec` open neighbourhood of the target point,
base-changes the smooth morphism to it, applies that affine result, and composes the resulting
étale neighbourhood back into the original target.
-/

@[expose] public section

namespace AlgebraicGeometry.Scheme.Hom

open CategoryTheory Limits

universe u

variable {X Y : Scheme.{u}}

/-- A morphism **has étale-local sections** when, étale-locally on the target, it admits a
section. This is the conclusion of Stacks 055U. -/
def HasEtaleLocalSections (f : X ⟶ Y) : Prop :=
  ∀ y : Y, ∃ (Y' : Scheme.{u}) (p : Y' ⟶ Y) (_ : Etale p) (_ : y ∈ Set.range p.base)
    (s : Y' ⟶ X), s ≫ f = p

/-- **Stacks 055U** (`more-morphisms-lemma-etale-nbhd-dominates-smooth`), slogan: *smooth
morphisms admit étale local sections*: if `y` lies in the image of a smooth morphism
`f : X ⟶ Y`, then an étale neighbourhood of `y` admits a lift to `X`. -/
@[stacks 055U]
theorem exists_etaleNeighborhood_of_smooth (f : X ⟶ Y) [Smooth f]
    (y : Y) (hy : y ∈ Set.range f.base) :
    ∃ (Y' : Scheme.{u}) (p : Y' ⟶ Y) (_ : Etale p) (_ : y ∈ Set.range p.base)
      (s : Y' ⟶ X), s ≫ f = p := by
  obtain ⟨A, j, hj, y', hy'⟩ := Scheme.exists_Spec_apply_eq y
  obtain ⟨x, hx⟩ := hy
  obtain ⟨z, -, hzsnd⟩ :=
    Scheme.Pullback.exists_preimage_pullback x y' (hx.trans hy'.symm)
  have hyRange : y' ∈ Set.range (pullback.snd f j) := ⟨z, hzsnd⟩
  obtain ⟨Y', p, hp, hyp, s, hs⟩ :=
    StacksProject.exists_etaleNeighborhood_of_smooth_toSpec
      (pullback.snd f j) y' hyRange
  refine ⟨Y', p ≫ j, inferInstance, ?_, s ≫ pullback.fst f j, ?_⟩
  · obtain ⟨z', hz'⟩ := hyp
    refine ⟨z', ?_⟩
    change j (p z') = y
    rw [hz', hy']
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hs]

/-- **Stacks 055U** (`more-morphisms-lemma-etale-nbhd-dominates-smooth`) (surjective
reformulation): a smooth surjection has étale-local sections at every target point. -/
@[stacks 055U "surjective reformulation"]
theorem hasEtaleLocalSections_of_smooth' (f : X ⟶ Y) [Smooth f] [Surjective f] :
    HasEtaleLocalSections f := fun y ↦
  exists_etaleNeighborhood_of_smooth f y (f.surjective y)

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Hom

open CategoryTheory

/-- **Stacks 055V** (`more-morphisms-lemma-etale-dominates-smooth`), in the form needed to show
that a smooth surjection is an epimorphism on the big étale site: a surjective morphism with
étale-local sections is refined by an étale covering sieve.

Proof route: for each `y : Y` take the étale neighbourhood `p : Y' → Y` and section
`s : Y' → X` supplied by `HasEtaleLocalSections`. The family of all such `p` is jointly
surjective (by surjectivity of `f`) and étale, hence generates a covering sieve for
`Scheme.etaleTopology`. Each `p = s ≫ f` factors through `f`, so the sieve it generates is
contained in `Sieve.generate (Presieve.singleton f)`. -/
@[stacks 055V]
theorem exists_etale_sieve_le_of_hasEtaleLocalSections {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Surjective f] (h : HasEtaleLocalSections f) :
    ∃ R : Sieve Y, R ∈ Scheme.etaleTopology Y ∧
      R ≤ Sieve.generate (Presieve.singleton f) := by
  choose Y' p hp hy s hs using h
  refine ⟨Sieve.generate (Presieve.ofArrows Y' p), ?_, ?_⟩
  · refine Precoverage.generate_mem_toGrothendieck ?_
    exact (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).mpr
      ⟨fun y ↦ ⟨y, hy y⟩, fun y ↦ hp y⟩
  · rw [Sieve.generate_le_iff]
    rintro Z g ⟨y⟩
    exact ⟨X, s y, f, ⟨⟩, hs y⟩

end AlgebraicGeometry.Scheme.Hom
