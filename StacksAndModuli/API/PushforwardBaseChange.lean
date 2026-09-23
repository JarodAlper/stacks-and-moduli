module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# The base-change comparison map for pushforward of sheaves of modules

For a commutative square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

there is a canonical comparison map `g^* f_* F ⟶ f'_* g'^* F`, and "the formation of `f_* F`
commutes with base change" means that this map is an isomorphism.  The statement occurs
throughout §A.6 of *Stacks and Moduli* — in Grauert's Theorem, in both versions of Cohomology
and Base Change, and in Proposition 6.1.16 for `π_*(Ω^{⊗ k})` — and the map itself is absent
from Mathlib and from the rest of this library.

It is the mate, in the sense of `CategoryTheory.mateEquiv`, of the canonical isomorphism
`g^* ⋙ f'^* ≅ f^* ⋙ g'^*` between the two ways of pulling back around the square; that
isomorphism is `pullbackSquareIso`, assembled from `Scheme.Modules.pullbackComp` and
`Scheme.Modules.pullbackCongr`.  Nothing here assumes the square is cartesian: the comparison
map exists for any commutative square, and cartesianness (with flatness or properness
hypotheses) is what makes it an isomorphism.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.pullbackSquareIso`: `g^* ⋙ f'^* ≅ f^* ⋙ g'^*`.
* `AlgebraicGeometry.Scheme.Modules.pushforwardBaseChange`: the comparison
  `f_* ⋙ g^* ⟶ g'^* ⋙ f'_*`.
* `AlgebraicGeometry.Scheme.Modules.PushforwardCommutesWithBaseChange`: the property that
  the comparison map is an isomorphism for every base change of `f`.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X X' Y Y' : Scheme.{u}}

/-- The canonical isomorphism between the two ways of pulling back around a commutative
square `g' ≫ f = f' ≫ g`: `g^* ⋙ f'^* ≅ f^* ⋙ g'^*`. -/
noncomputable def pullbackSquareIso {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (w : g' ≫ f = f' ≫ g) :
    pullback g ⋙ pullback f' ≅ pullback f ⋙ pullback g' :=
  pullbackComp f' g ≪≫ (pullbackCongr w).symm ≪≫ (pullbackComp g' f).symm

/-- The **base-change comparison map** `g^* f_* F ⟶ f'_* g'^* F` attached to a commutative
square `g' ≫ f = f' ≫ g`, as the mate of `pullbackSquareIso`. -/
noncomputable def pushforwardBaseChange {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} (w : g' ≫ f = f' ≫ g) :
    pushforward f ⋙ pullback g ⟶ pullback g' ⋙ pushforward f' :=
  (mateEquiv (pullbackPushforwardAdjunction f) (pullbackPushforwardAdjunction f')
    (TwoSquare.mk _ _ _ _ (pullbackSquareIso w).hom)).natTrans

/-- **The formation of `f_* F` commutes with base change**: for every cartesian square over
`f`, the comparison map `g^* f_* F ⟶ f'_* g'^* F` is an isomorphism.

Stated for a fixed `F`, since that is how §A.6 uses it: it is `π_*(Ω^{⊗ k})`, not `π_*`
itself, whose formation is asserted to commute with base change. -/
def PushforwardCommutesWithBaseChange {f : X ⟶ Y} (F : X.Modules) : Prop :=
  ∀ (Y' X' : Scheme.{u}) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h : IsPullback g' f' f g),
    IsIso ((pushforwardBaseChange (f := f) (g := g) (f' := f') (g' := g')
      h.w).app F)

end AlgebraicGeometry.Scheme.Modules
