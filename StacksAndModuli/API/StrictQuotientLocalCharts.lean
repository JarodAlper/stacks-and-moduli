module

public import StacksAndModuli.API.QuotFunctorZariskiDescent

/-!
# Local chart criterion for the Quot functor

This file packages the geometric input needed after effective Zariski descent for the
Quot functor.  A strict Quot chart atlas consists of a small family of schemes over the
base whose maps to the universe-small strict-kernel model are relatively representable
open immersions and jointly Zariski-locally surjective.  If the chart schemes are locally
of finite type over the base, the gluing construction for representable open subfunctors
produces a locally finite-type representative of both the strict and isomorphism-class
Quot functors.

Main declarations:
- `AlgebraicGeometry.Scheme.StrictQuotientChartAtlas`;
- `AlgebraicGeometry.Scheme.StrictQuotientChartAtlas.strictRepresentableBy`;
- `AlgebraicGeometry.Scheme.StrictQuotientChartAtlas.exists_quotientRepresentableBy`;
- `AlgebraicGeometry.Scheme.exists_strictQuotientRepresentableBy_of_chartAtlas`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme

variable {X S : Scheme.{u}} (F : X.Modules) (f : X ⟶ S)

/-- A small atlas of representable open subfunctors of the strict Quot functor.

The auxiliary universe of `uliftYoneda` is `0`, so its values and the strict-kernel
model both lie in `Type u`. -/
structure StrictQuotientChartAtlas where
  /-- Index type of the chart family. -/
  I : Type u
  /-- The scheme representing each chart, regarded over the base. -/
  chart : I → Over S
  /-- The map from each represented chart to the strict Quot functor. -/
  map : (i : I) → uliftYoneda.{0}.obj (chart i) ⟶ strictQuotFunctor F f
  /-- Every chart map is relatively representable by open immersions. -/
  isOpen : ∀ i, (isOpenImmersionOver S).relative uliftYoneda.{0} (map i)
  /-- The chart maps are jointly Zariski-locally surjective. -/
  locallySurjective : Presheaf.IsLocallySurjective
    (Scheme.zariskiTopology.over S) (Limits.Sigma.desc map)
  /-- Every chart is locally of finite type over the base. -/
  locallyOfFiniteType : ∀ i, LocallyOfFiniteType (chart i).hom

namespace StrictQuotientChartAtlas

variable {F f} (A : StrictQuotientChartAtlas F f)

/-- The strict Quot functor bundled as a relative Zariski sheaf. -/
noncomputable def sheaf [F.IsQuasicoherent] :
    Sheaf (Scheme.zariskiTopology.over S) (Type u) :=
  strictQuotFunctorSheaf F f
    (Modules.QuotientOpenDescent.isSheaf_strictQuotFunctor (F := F) (f := f))

/-- The scheme over the base obtained by gluing the strict Quot charts. -/
noncomputable def glued [F.IsQuasicoherent] : Over S :=
  OverLocalRepresentability.gluedOver (A.isOpen)

/-- The glued scheme represents the strict Quot functor. -/
noncomputable def strictRepresentableBy [F.IsQuasicoherent] :
    (strictQuotFunctor F f).RepresentableBy A.glued := by
  let G := sheaf (F := F) (f := f)
  let g : (i : A.I) → uliftYoneda.{0}.obj (A.chart i) ⟶ G.1 := A.map
  letI : Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over S)
      (Limits.Sigma.desc g) := by
    exact A.locallySurjective
  exact OverLocalRepresentability.representableBy G g A.isOpen

/-- The glued representative is locally of finite type over the base. -/
theorem glued_locallyOfFiniteType [F.IsQuasicoherent] :
    LocallyOfFiniteType A.glued.hom := by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFiniteType)
    (OverLocalRepresentability.glueData A.isOpen).openCover]
  intro i
  change LocallyOfFiniteType
    ((OverLocalRepresentability.glueData A.isOpen).ι i ≫
      OverLocalRepresentability.gluedHom A.isOpen)
  rw [OverLocalRepresentability.toGlued_comp_gluedHom A.isOpen i]
  exact A.locallyOfFiniteType i

include A in
/-- A strict Quot chart atlas produces a locally finite-type representative of the
universe-small strict-kernel functor. -/
theorem exists_strictRepresentableBy [F.IsQuasicoherent] :
    ∃ Q : Over S,
      Nonempty ((strictQuotFunctor F f).RepresentableBy Q) ∧
        LocallyOfFiniteType Q.hom :=
  ⟨glued A, ⟨strictRepresentableBy A⟩, glued_locallyOfFiniteType A⟩

include A in
/-- A strict Quot chart atlas produces a locally finite-type representative of the usual
isomorphism-class Quot functor. -/
theorem exists_quotientRepresentableBy [F.IsQuasicoherent] :
    ∃ Q : Over S,
      Nonempty ((quotFunctor F f).RepresentableBy Q) ∧
        LocallyOfFiniteType Q.hom := by
  rw [quotFunctor_exists_representableBy_iff_strictQuotFunctor
    (F := F) (f := f) (P := fun Q ↦ LocallyOfFiniteType Q.hom)]
  exact exists_strictRepresentableBy A

end StrictQuotientChartAtlas

/-- Existence of the bounded local-chart input is sufficient for a locally finite-type
representative of the strict Quot functor.  For projective space, constructing this
`Nonempty` atlas is the geometric boundedness/Grassmannian-chart obligation left after
Zariski sheafness. -/
theorem exists_strictQuotientRepresentableBy_of_chartAtlas {F : X.Modules} {f : X ⟶ S}
    [F.IsQuasicoherent] (hA : Nonempty (StrictQuotientChartAtlas F f)) :
    ∃ Q : Over S,
      Nonempty ((strictQuotFunctor F f).RepresentableBy Q) ∧
        LocallyOfFiniteType Q.hom := by
  obtain ⟨A⟩ := hA
  exact A.exists_strictRepresentableBy

/-- Transport the representative obtained from a strict Quot chart atlas to the usual
isomorphism-class Quot functor. -/
theorem exists_quotientRepresentableBy_of_chartAtlas {F : X.Modules} {f : X ⟶ S}
    [F.IsQuasicoherent] (hA : Nonempty (StrictQuotientChartAtlas F f)) :
    ∃ Q : Over S,
      Nonempty ((quotFunctor F f).RepresentableBy Q) ∧
        LocallyOfFiniteType Q.hom := by
  obtain ⟨A⟩ := hA
  exact A.exists_quotientRepresentableBy

end AlgebraicGeometry.Scheme

end
