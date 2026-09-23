module

public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Reindexing a finite product of monomial bases

The twisted-free Grassmannian construction repeatedly identifies one finite index
type of cardinal `r * c` with a product of an ambient summand and a monomial index.
Keeping this elementary equivalence in a dependency-free module lets both the
fixed-degree reconstruction and the eventual package use the same choice.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The canonical finite reindexing of a product basis by one finite type. -/
noncomputable def twistedFreeMonomialIndexEquiv (r c : ℕ) :
    ULift.{u} (Fin (r * c)) ≃ ULift.{u} (Fin r) × Fin c :=
  Equiv.ulift.trans <|
    finProdFinEquiv.symm.trans <|
      Equiv.prodCongr Equiv.ulift.symm (Equiv.refl _)

end AlgebraicGeometry.Scheme

end

end
