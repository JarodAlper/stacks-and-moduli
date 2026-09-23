module

public import StacksAndModuli.API.RelativeDifferentialsAffineComparison

/-!
# Relative differentials on affine charts

For a scheme morphism `f : X ⟶ Y`, affine opens `V ⊆ X` and `U ⊆ Y`, and an inclusion
`V ⊆ f⁻¹(U)`, there are two sheaves of relative differentials on
`Spec Γ(X, V)`:

* the affine-coordinate transport of the global sheaf `Ω_{X/Y}`;
* the relative differential sheaf of the coordinate morphism
  `Spec Γ(X, V) ⟶ Spec Γ(Y, U)`.

This file packages their expected identification as an explicit compatibility predicate.
It also proves that finite local freeness, including fixed rank, transports from the
coordinate morphism back to the restriction of the global sheaf.  Constructing the
canonical comparison and proving it invertible remain separate geometric obligations.

Main declarations:

* `Hom.AffineRelativeDifferentialsCompatible`;
* `relativeDifferentials_pullback_isFiniteLocallyFree_of_affineCompatibility`;
* `relativeDifferentials_pullback_isProjectiveOfRank_of_affineCompatibility`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

namespace Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The affine-chart compatibility expected of the global relative differential sheaf.

It says that after restricting `Ω_{X/Y}` to the affine open `V` and transporting it to
`Spec Γ(X, V)`, the result is isomorphic to the relative differential sheaf of the
coordinate map induced by `f`.  The use of `Nonempty` records only the property needed for
invariant geometric conclusions; a future canonical comparison can refine this interface. -/
def AffineRelativeDifferentialsCompatible
    (U : Y.affineOpens) (V : X.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U.1) : Prop :=
  Nonempty
    (Modules.affineCoordinateSheaf f.relativeDifferentials V ≅
      (Spec.map (f.appLE U.1 V.1 e)).relativeDifferentials)

end Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- On a standard-smooth affine chart, affine compatibility and the two affine
comparison obligations imply finite local freeness of the restriction of the global
relative differential sheaf. -/
lemma relativeDifferentials_pullback_isFiniteLocallyFree_of_affineCompatibility
    (U : Y.affineOpens) (V : X.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U.1)
    (hφ : (f.appLE U.1 V.1 e).hom.IsStandardSmooth)
    (hCompat : f.AffineRelativeDifferentialsCompatible U V e)
    (hGlobal : IsIso
      (affineGlobalRelativeDerivation (f.appLE U.1 V.1 e)).desc)
    (hTarget : IsLocalizing
      (modulesSpecToSheaf.obj
        (Spec.map (f.appLE U.1 V.1 e)).relativeDifferentials)) :
    Modules.IsFiniteLocallyFree
      ((Modules.pullback V.1.ι).obj f.relativeDifferentials) := by
  let φ := f.appLE U.1 V.1 e
  have hChart : Modules.IsFiniteLocallyFree
      (Spec.map φ).relativeDifferentials :=
    relativeDifferentials_isFiniteLocallyFree_of_affineCompatibility
      φ hφ hGlobal hTarget
  obtain ⟨c⟩ := hCompat
  have hCoordinate : Modules.IsFiniteLocallyFree
      (Modules.affineCoordinateSheaf f.relativeDifferentials V) :=
    hChart.of_iso c.symm
  have hBack := hCoordinate.pullback_of_isIso V.2.isoSpec.hom
  let M := (Modules.pullback V.1.ι).obj f.relativeDifferentials
  let cBack :
      (Modules.pullback V.2.isoSpec.hom).obj
          (Modules.affineCoordinateSheaf f.relativeDifferentials V) ≅ M :=
    (Modules.pullbackComp V.2.isoSpec.hom V.2.isoSpec.inv).app M ≪≫
      (Modules.pullbackCongr V.2.isoSpec.hom_inv_id).app M ≪≫
      (Modules.pullbackId _).app M
  exact hBack.of_iso cBack

/-- On a standard-smooth affine chart of relative dimension `n`, affine compatibility
and the two affine comparison obligations imply that the restriction of the global
relative differential sheaf is finite locally free of rank `n`. -/
lemma relativeDifferentials_pullback_isProjectiveOfRank_of_affineCompatibility
    (n : ℕ) (U : Y.affineOpens) (V : X.affineOpens)
    (e : V.1 ≤ f ⁻¹ᵁ U.1) [Nontrivial Γ(X, V.1)]
    (hφ : (f.appLE U.1 V.1 e).hom.IsStandardSmoothOfRelativeDimension n)
    (hCompat : f.AffineRelativeDifferentialsCompatible U V e)
    (hGlobal : IsIso
      (affineGlobalRelativeDerivation (f.appLE U.1 V.1 e)).desc)
    (hTarget : IsLocalizing
      (modulesSpecToSheaf.obj
        (Spec.map (f.appLE U.1 V.1 e)).relativeDifferentials)) :
    Modules.IsProjectiveOfRank n
      ((Modules.pullback V.1.ι).obj f.relativeDifferentials) := by
  let φ := f.appLE U.1 V.1 e
  have hChart : Modules.IsProjectiveOfRank n
      (Spec.map φ).relativeDifferentials :=
    relativeDifferentials_isProjectiveOfRank_of_affineCompatibility
      n φ hφ hGlobal hTarget
  obtain ⟨c⟩ := hCompat
  have hCoordinate : Modules.IsProjectiveOfRank n
      (Modules.affineCoordinateSheaf f.relativeDifferentials V) :=
    hChart.of_iso c.symm
  have hBack := hCoordinate.pullback_of_isIso V.2.isoSpec.hom
  let M := (Modules.pullback V.1.ι).obj f.relativeDifferentials
  let cBack :
      (Modules.pullback V.2.isoSpec.hom).obj
          (Modules.affineCoordinateSheaf f.relativeDifferentials V) ≅ M :=
    (Modules.pullbackComp V.2.isoSpec.hom V.2.isoSpec.inv).app M ≪≫
      (Modules.pullbackCongr V.2.isoSpec.hom_inv_id).app M ≪≫
      (Modules.pullbackId _).app M
  exact hBack.of_iso cBack

end AlgebraicGeometry.Scheme
