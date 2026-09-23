module

public import StacksAndModuli.API.RelativeFibreFlatCokernel
public import StacksAndModuli.API.RelativeFlatSpreadingInterface

/-!
# Relative flat loci as relative-fibre exactness loci

For an exact two-step presentation by finite modules with projective final term, the locus
where the concrete cokernel is flat over the coefficient ring is exactly the locus where
the two presentation maps are exact on the localized relative fibre.  Consequently openness
of either locus is equivalent to openness of the other.

This is the formal bridge between the exactness-locus input of Stacks Project tag 00RB and
the relative flat-locus conclusion of tag 00RC.  It does not assert openness: after this
identification, the remaining input is precisely the determinantal openness theorem for the
relative-fibre exactness locus.

Main declarations:

* `LinearMap.relativeFibreExactLocus_eq_flatOverLocus_coker_of_exact`;
* `LinearMap.hasOpenRelativeFibreExactLocus_iff_hasOpenFlatOverLocus_coker_of_exact`;
* `LinearMap.HasOpenRelativeFibreExactLocus.hasOpenFlatOverLocus_of_exact`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u v

namespace LinearMap

/-- For an exact finite presentation with projective final term, the relative-fibre
exactness locus equals the relative flat locus of the concrete cokernel. -/
theorem relativeFibreExactLocus_eq_flatOverLocus_coker_of_exact
    {R : Type u} {S L K F : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    [AddCommGroup L] [Module S L]
    [AddCommGroup K] [Module S K] [Module.Finite S K]
    [AddCommGroup F] [Module S F] [Module.Finite S F]
    [Module.Projective S F]
    (f : L →ₗ[S] K) (g : K →ₗ[S] F)
    (hexact : Function.Exact f g) :
    letI : Module R (F ⧸ LinearMap.range g) :=
      Module.compHom (F ⧸ LinearMap.range g) (algebraMap R S)
    letI : IsScalarTower R S (F ⧸ LinearMap.range g) :=
      IsScalarTower.of_compHom R S (F ⧸ LinearMap.range g)
    relativeFibreExactLocus (R := R) f g =
      Module.FinitePresentation.flatOverLocus
        (R := R) (S := S) (M := F ⧸ LinearMap.range g) := by
  letI : Module R (F ⧸ LinearMap.range g) :=
    Module.compHom (F ⧸ LinearMap.range g) (algebraMap R S)
  letI : IsScalarTower R S (F ⧸ LinearMap.range g) :=
    IsScalarTower.of_compHom R S (F ⧸ LinearMap.range g)
  ext q
  exact Module.Flat.isRelativeFibreExactAt_iff_localizedTensorCoker_flat_of_exact
    q f g hexact

/-- Under the same finite-presentation hypotheses, openness of the relative-fibre
exactness locus is equivalent to openness of the relative flat locus of the cokernel. -/
theorem hasOpenRelativeFibreExactLocus_iff_hasOpenFlatOverLocus_coker_of_exact
    {R : Type u} {S L K F : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    [AddCommGroup L] [Module S L]
    [AddCommGroup K] [Module S K] [Module.Finite S K]
    [AddCommGroup F] [Module S F] [Module.Finite S F]
    [Module.Projective S F]
    (f : L →ₗ[S] K) (g : K →ₗ[S] F)
    (hexact : Function.Exact f g) :
    letI : Module R (F ⧸ LinearMap.range g) :=
      Module.compHom (F ⧸ LinearMap.range g) (algebraMap R S)
    letI : IsScalarTower R S (F ⧸ LinearMap.range g) :=
      IsScalarTower.of_compHom R S (F ⧸ LinearMap.range g)
    HasOpenRelativeFibreExactLocus (R := R) f g ↔
      Module.FinitePresentation.HasOpenFlatOverLocus
        (R := R) (S := S) (M := F ⧸ LinearMap.range g) := by
  letI : Module R (F ⧸ LinearMap.range g) :=
    Module.compHom (F ⧸ LinearMap.range g) (algebraMap R S)
  letI : IsScalarTower R S (F ⧸ LinearMap.range g) :=
    IsScalarTower.of_compHom R S (F ⧸ LinearMap.range g)
  change IsOpen (relativeFibreExactLocus (R := R) f g) ↔
    IsOpen (Module.FinitePresentation.flatOverLocus
      (R := R) (S := S) (M := F ⧸ LinearMap.range g))
  rw [relativeFibreExactLocus_eq_flatOverLocus_coker_of_exact f g hexact]

namespace HasOpenRelativeFibreExactLocus

/-- Openness of a relative-fibre exactness locus gives openness of the corresponding
relative flat locus. -/
theorem hasOpenFlatOverLocus_of_exact
    {R : Type u} {S L K F : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    [AddCommGroup L] [Module S L]
    [AddCommGroup K] [Module S K] [Module.Finite S K]
    [AddCommGroup F] [Module S F] [Module.Finite S F]
    [Module.Projective S F]
    {f : L →ₗ[S] K} {g : K →ₗ[S] F}
    (hopen : HasOpenRelativeFibreExactLocus (R := R) f g)
    (hexact : Function.Exact f g) :
    letI : Module R (F ⧸ LinearMap.range g) :=
      Module.compHom (F ⧸ LinearMap.range g) (algebraMap R S)
    letI : IsScalarTower R S (F ⧸ LinearMap.range g) :=
      IsScalarTower.of_compHom R S (F ⧸ LinearMap.range g)
    Module.FinitePresentation.HasOpenFlatOverLocus
      (R := R) (S := S) (M := F ⧸ LinearMap.range g) :=
  (hasOpenRelativeFibreExactLocus_iff_hasOpenFlatOverLocus_coker_of_exact
    f g hexact).mp hopen

end HasOpenRelativeFibreExactLocus

end LinearMap

end

end
