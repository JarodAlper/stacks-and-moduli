module

public import StacksAndModuli.API.ProjectiveSpaceTwistMultiplication
public import StacksAndModuli.API.ProjectiveSpaceTwistZero
public import StacksAndModuli.API.SchemeModulesTensorQuasicoherent
public import StacksAndModuli.API.SchemeModulesTensorLocallyFree
public import StacksAndModuli.API.SchemeModulesTensorSymmetry

/-!
# Cancelling opposite twists on relative projective space

For a natural degree `d`, symmetry puts `O(-d)` on the left and the existing relative
twist-multiplication isomorphism identifies `O(-d) ⊗ O(d)` with `O`.  A chosen tensor
associator then cancels the two twists in `(F ⊗ O(d)) ⊗ O(-d)`.

The final declaration applies this cancellation to the pullback--pushforward counit.  It
is the untwisted evaluation map needed by Quot-to-Grassmannian reconstruction.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

/-- For a natural degree `d`, the relative twists `O(d)` and `O(-d)` cancel. -/
noncomputable def projectiveSpaceOverTwist_cancelIso_nat
    (n : ℕ) (S : Scheme.{u}) (d : ℕ) :
    Modules.tensor
        (projectiveSpaceOverTwist n S (d : ℤ))
        (projectiveSpaceOverTwist n S (-(d : ℤ))) ≅
      SheafOfModules.unit (projectiveSpaceOver n S).ringCatSheaf :=
  Modules.tensorCommIso
      (projectiveSpaceOverTwist n S (d : ℤ))
      (projectiveSpaceOverTwist n S (-(d : ℤ))) ≪≫
    projectiveSpaceOverTwist_addIso_nat n S (-(d : ℤ)) d ≪≫
    eqToIso (congrArg (projectiveSpaceOverTwist n S) (by omega)) ≪≫
    projectiveSpaceOverTwistZeroIso n S

/-- Twisting a module by `d` and then by `-d` recovers the original module. -/
noncomputable def projectiveSpaceOverTwistModule_cancelIso_nat
    (n : ℕ) (S : Scheme.{u})
    (F : (projectiveSpaceOver n S).Modules) (d : ℕ) :
    Modules.tensor
        (projectiveSpaceOverTwistModule F (d : ℤ))
        (projectiveSpaceOverTwist n S (-(d : ℤ))) ≅ F :=
  Modules.tensorAssocIso F
      (projectiveSpaceOverTwist n S (d : ℤ))
      (projectiveSpaceOverTwist n S (-(d : ℤ))) ≪≫
    Modules.tensorRightIso F (projectiveSpaceOverTwist_cancelIso_nat n S d) ≪≫
    Modules.tensorUnitIso F

/-- Cancelling a positive projective twist against its negative is natural in the
module sheaf. -/
@[reassoc]
lemma projectiveSpaceOverTwistModule_cancelIso_nat_hom_naturality
    (n : ℕ) (S : Scheme.{u}) {F F' : (projectiveSpaceOver n S).Modules}
    (f : F ⟶ F') (d : ℕ) :
    Modules.tensorMapLeft
          (Modules.tensorMapLeft f (projectiveSpaceOverTwist n S (d : ℤ)))
          (projectiveSpaceOverTwist n S (-(d : ℤ))) ≫
        (projectiveSpaceOverTwistModule_cancelIso_nat n S F' d).hom =
      (projectiveSpaceOverTwistModule_cancelIso_nat n S F d).hom ≫ f := by
  let Od := projectiveSpaceOverTwist n S (d : ℤ)
  let Dm := projectiveSpaceOverTwist n S (-(d : ℤ))
  let c := projectiveSpaceOverTwist_cancelIso_nat n S d
  change Modules.tensorMapLeft (Modules.tensorMapLeft f Od) Dm ≫
        (Modules.tensorAssocIso F' Od Dm).hom ≫
        Modules.tensorMapRight F' c.hom ≫ (Modules.tensorUnitIso F').hom =
      (Modules.tensorAssocIso F Od Dm).hom ≫
        Modules.tensorMapRight F c.hom ≫ (Modules.tensorUnitIso F).hom ≫ f
  calc
    Modules.tensorMapLeft (Modules.tensorMapLeft f Od) Dm ≫
          (Modules.tensorAssocIso F' Od Dm).hom ≫
          Modules.tensorMapRight F' c.hom ≫ (Modules.tensorUnitIso F').hom =
        ((Modules.tensorAssocIso F Od Dm).hom ≫
          Modules.tensorMapLeft f (Modules.tensor Od Dm)) ≫
          Modules.tensorMapRight F' c.hom ≫ (Modules.tensorUnitIso F').hom :=
      congrArg
        (fun k ↦ k ≫ Modules.tensorMapRight F' c.hom ≫
          (Modules.tensorUnitIso F').hom)
        (Modules.tensorAssocIso_hom_naturality_left f Od Dm)
    _ = (Modules.tensorAssocIso F Od Dm).hom ≫
        (Modules.tensorMapLeft f (Modules.tensor Od Dm) ≫
          Modules.tensorMapRight F' c.hom) ≫ (Modules.tensorUnitIso F').hom := by
      simp only [Category.assoc]
    _ = (Modules.tensorAssocIso F Od Dm).hom ≫
        (Modules.tensorMapRight F c.hom ≫
          Modules.tensorMapLeft f (SheafOfModules.unit
            (projectiveSpaceOver n S).ringCatSheaf)) ≫
          (Modules.tensorUnitIso F').hom :=
      congrArg
        (fun k ↦ (Modules.tensorAssocIso F Od Dm).hom ≫ k ≫
          (Modules.tensorUnitIso F').hom)
        (Modules.tensorMap_exchange f c.hom).symm
    _ = (Modules.tensorAssocIso F Od Dm).hom ≫ Modules.tensorMapRight F c.hom ≫
        (Modules.tensorMapLeft f (SheafOfModules.unit
            (projectiveSpaceOver n S).ringCatSheaf) ≫
          (Modules.tensorUnitIso F').hom) := by
      simp only [Category.assoc]
    _ = (Modules.tensorAssocIso F Od Dm).hom ≫ Modules.tensorMapRight F c.hom ≫
        ((Modules.tensorUnitIso F).hom ≫ f) :=
      congrArg
        (fun k ↦ (Modules.tensorAssocIso F Od Dm).hom ≫
          Modules.tensorMapRight F c.hom ≫ k)
        (Modules.tensorUnitIso_naturality f)
    _ = _ := rfl

/-- The pullback--pushforward evaluation of `F(d)`, followed by cancellation of `d` and
`-d`, as an untwisted map to `F`. -/
noncomputable def projectiveSpaceOverUntwistedEvaluation
    (n : ℕ) (S : Scheme.{u})
    (F : (projectiveSpaceOver n S).Modules) (d : ℕ) :
    Modules.tensor
        ((Modules.pullback (projectiveSpaceOverπ n S)).obj
          ((Modules.pushforward (projectiveSpaceOverπ n S)).obj
            (projectiveSpaceOverTwistModule F (d : ℤ))))
        (projectiveSpaceOverTwist n S (-(d : ℤ))) ⟶ F :=
  Modules.tensorMapLeft
      ((Modules.pullbackPushforwardAdjunction
        (projectiveSpaceOverπ n S)).counit.app
          (projectiveSpaceOverTwistModule F (d : ℤ)))
      (projectiveSpaceOverTwist n S (-(d : ℤ))) ≫
    (projectiveSpaceOverTwistModule_cancelIso_nat n S F d).hom

end AlgebraicGeometry.Scheme

end

end
