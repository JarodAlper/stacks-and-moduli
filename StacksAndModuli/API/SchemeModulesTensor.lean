module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import StacksAndModuli.API.PresheafModuleLocalEquivalenceTensor

/-!
# Tensor product of sheaves of modules on a scheme

Mathlib has a monoidal structure on *presheaves* of modules over a presheaf of commutative
rings (`PresheafOfModules.monoidalCategory`) and a sheafification functor
`PresheafOfModules.sheafification`, but no tensor product of *sheaves* of modules. This
file supplies the tensor product `F ⊗ G` on `X.Modules` for a scheme `X`, as the
sheafification of the presheaf-level tensor product, together with functoriality in each
variable.

The tensor product is what gives meaning to the Serre twist `F(d) = F ⊗ 𝒪(d)` of a sheaf on
`Proj`, and hence to Castelnuovo–Mumford regularity.

## Implementation note

`X.PresheafOfModules` unfolds to `PresheafOfModules X.ringCatSheaf.obj`, while Mathlib's
monoidal instance is stated for `PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)`. The
two are definitionally equal but their discrimination keys differ, so typeclass search does
not find the instance at the `X.PresheafOfModules` spelling. `instMonoidalPresheafOfModules`
below restates it (cf. the "Discrimination-key mismatch on instance search" entry of the
root INSIGHTS.md).

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.instMonoidalPresheafOfModules`: the monoidal structure
  on `X.PresheafOfModules`, at the spelling typeclass search can use.
* `AlgebraicGeometry.Scheme.Modules.sheafification`: sheafification of presheaves of
  modules on a scheme.
* `AlgebraicGeometry.Scheme.Modules.tensor`: the tensor product `F ⊗ G` of two sheaves of
  modules on a scheme.
* `AlgebraicGeometry.Scheme.Modules.tensorPower`: the tensor powers `F^{⊗ k}`.
* `AlgebraicGeometry.Scheme.Modules.tensorMapLeft`, `tensorMapRight`: functoriality of the
  tensor product in each variable, with `tensorLeftIso` and `tensorRightIso` transporting
  along isomorphisms.
* `AlgebraicGeometry.Scheme.Modules.nonempty_tensorAssoc`: associativity, obtained by
  localizing the presheaf associator.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace Opposite MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u})

/-- The monoidal structure on presheaves of modules over a scheme, restated at the
`X.PresheafOfModules` spelling so that typeclass search finds it. -/
noncomputable instance instMonoidalPresheafOfModules :
    MonoidalCategory (X.PresheafOfModules) :=
  inferInstanceAs (MonoidalCategory
    (_root_.PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat)))

/-- Sheafification of presheaves of modules on a scheme. -/
noncomputable def sheafification : X.PresheafOfModules ⥤ X.Modules :=
  _root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)

variable {X}

/-- The tensor product `F ⊗ G` of two sheaves of modules on a scheme: the sheafification of
the tensor product of the underlying presheaves of modules. -/
noncomputable def tensor (F G : X.Modules) : X.Modules :=
  (sheafification X).obj (MonoidalCategoryStruct.tensorObj (C := X.PresheafOfModules)
    F.val G.val)

@[inherit_doc] scoped infixl:70 " ⊗ₘ " => tensor

/-- The `k`-th tensor power `F^{⊗ k}` of a sheaf of modules on a scheme, with
`F^{⊗ 0} = 𝒪_X` and `F^{⊗ (k+1)} = F^{⊗ k} ⊗ F`.

This is what gives meaning to the pluricanonical sheaves `Ω_{𝒞/S}^{⊗ k}` of a family of
curves (Proposition 6.1.16) and to the Serre twists of a sheaf on `Proj`. -/
noncomputable def tensorPower (F : X.Modules) : ℕ → X.Modules
  | 0 => SheafOfModules.unit X.ringCatSheaf
  | (k + 1) => tensorPower F k ⊗ₘ F

@[simp] lemma tensorPower_zero (F : X.Modules) :
    tensorPower F 0 = SheafOfModules.unit X.ringCatSheaf := rfl

@[simp] lemma tensorPower_succ (F : X.Modules) (k : ℕ) :
    tensorPower F (k + 1) = tensorPower F k ⊗ₘ F := rfl

/-- Functoriality of the tensor product in the left variable. -/
noncomputable def tensorMapLeft {F F' : X.Modules} (φ : F ⟶ F') (G : X.Modules) :
    F ⊗ₘ G ⟶ F' ⊗ₘ G :=
  (sheafification X).map (MonoidalCategoryStruct.whiskerRight (C := X.PresheafOfModules)
    ((SheafOfModules.forget _).map φ) G.val)

/-- Functoriality of the tensor product in the right variable. -/
noncomputable def tensorMapRight (F : X.Modules) {G G' : X.Modules} (ψ : G ⟶ G') :
    F ⊗ₘ G ⟶ F ⊗ₘ G' :=
  (sheafification X).map (MonoidalCategoryStruct.whiskerLeft (C := X.PresheafOfModules)
    F.val ((SheafOfModules.forget _).map ψ))

@[simp]
theorem tensorMapLeft_id (F G : X.Modules) : tensorMapLeft (𝟙 F) G = 𝟙 (F ⊗ₘ G) := by
  show (sheafification X).map (MonoidalCategoryStruct.whiskerRight
    (C := X.PresheafOfModules) (𝟙 F.val) G.val) = _
  rw [MonoidalCategory.id_whiskerRight, CategoryTheory.Functor.map_id]
  rfl

@[simp]
theorem tensorMapRight_id (F G : X.Modules) : tensorMapRight F (𝟙 G) = 𝟙 (F ⊗ₘ G) := by
  show (sheafification X).map (MonoidalCategoryStruct.whiskerLeft
    (C := X.PresheafOfModules) F.val (𝟙 G.val)) = _
  rw [MonoidalCategory.whiskerLeft_id, CategoryTheory.Functor.map_id]
  rfl

@[simp]
theorem tensorMapLeft_comp {F F' F'' : X.Modules} (φ : F ⟶ F') (φ' : F' ⟶ F'')
    (G : X.Modules) :
    tensorMapLeft (φ ≫ φ') G = tensorMapLeft φ G ≫ tensorMapLeft φ' G := by
  show (sheafification X).map (MonoidalCategoryStruct.whiskerRight
    (C := X.PresheafOfModules) (φ.val ≫ φ'.val) G.val) = _
  rw [MonoidalCategory.comp_whiskerRight, CategoryTheory.Functor.map_comp]
  rfl

@[simp]
theorem tensorMapRight_comp (F : X.Modules) {G G' G'' : X.Modules} (ψ : G ⟶ G')
    (ψ' : G' ⟶ G'') :
    tensorMapRight F (ψ ≫ ψ') = tensorMapRight F ψ ≫ tensorMapRight F ψ' := by
  show (sheafification X).map (MonoidalCategoryStruct.whiskerLeft
    (C := X.PresheafOfModules) F.val (ψ.val ≫ ψ'.val)) = _
  rw [MonoidalCategory.whiskerLeft_comp, CategoryTheory.Functor.map_comp]
  rfl

/-- Transporting the tensor product along an isomorphism in the right variable. -/
noncomputable def tensorRightIso (F : X.Modules) {G G' : X.Modules} (e : G ≅ G') :
    F ⊗ₘ G ≅ F ⊗ₘ G' where
  hom := tensorMapRight F e.hom
  inv := tensorMapRight F e.inv
  hom_inv_id := by rw [← tensorMapRight_comp, e.hom_inv_id, tensorMapRight_id]
  inv_hom_id := by rw [← tensorMapRight_comp, e.inv_hom_id, tensorMapRight_id]

/-- Transporting the tensor product along an isomorphism in the left variable. -/
noncomputable def tensorLeftIso {F F' : X.Modules} (e : F ≅ F') (G : X.Modules) :
    F ⊗ₘ G ≅ F' ⊗ₘ G where
  hom := tensorMapLeft e.hom G
  inv := tensorMapLeft e.inv G
  hom_inv_id := by rw [← tensorMapLeft_comp, e.hom_inv_id, tensorMapLeft_id]
  inv_hom_id := by rw [← tensorMapLeft_comp, e.inv_hom_id, tensorMapLeft_id]

/-- The local equivalences of module presheaves used in the sheafification
localization. -/
private abbrev localEquivalences (X : Scheme.{u}) :
    MorphismProperty X.PresheafOfModules :=
  (Opens.grothendieckTopology X).W.inverseImage
    (_root_.PresheafOfModules.toPresheaf X.ringCatSheaf.obj)

-- The monoidality theorem is stated using `X.presheaf`, whereas the localization
-- below is stated using the definitionally equal `X.ringCatSheaf.obj`. Restate
-- the instance at the latter spelling so typeclass search sees it.
private noncomputable instance localEquivalences_isMonoidal (X : Scheme.{u}) :
    (localEquivalences X).IsMonoidal := by
  exact _root_.PresheafOfModules.localEquivalencesIsMonoidal X.presheaf

-- As above, expose Mathlib's module-sheafification localization instance at the
-- scheme-specific abbreviations used in this file.
private noncomputable instance sheafification_isLocalization (X : Scheme.{u}) :
    (sheafification X).IsLocalization (localEquivalences X) :=
  inferInstanceAs ((_root_.PresheafOfModules.sheafification
    (𝟙 X.ringCatSheaf.obj)).IsLocalization
      ((Opens.grothendieckTopology X).W.inverseImage
        (_root_.PresheafOfModules.toPresheaf X.ringCatSheaf.obj)))

/-- The tensor product of sheaves of modules on a scheme is associative.

The two sheafification units are local equivalences. Since local equivalences are
stable under tensoring, sheafification turns their left and right whiskerings into
isomorphisms. These isomorphisms join the sheaf tensors to the image of the presheaf
associator and give the required zigzag. -/
theorem nonempty_tensorAssoc (F G H : X.Modules) :
    Nonempty ((F ⊗ₘ G) ⊗ₘ H ≅ F ⊗ₘ (G ⊗ₘ H)) := by
  let adj := _root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  let uFG := adj.unit.app (F.val ⊗ G.val)
  let uGH := adj.unit.app (G.val ⊗ H.val)
  have huFG : localEquivalences X uFG := by
    change (Opens.grothendieckTopology X).W
      ((_root_.PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map uFG)
    simpa [uFG, adj] using
      (Opens.grothendieckTopology X).W_toSheafify
        (MonoidalCategoryStruct.tensorObj
          (C := X.PresheafOfModules) F.val G.val).presheaf
  have huGH : localEquivalences X uGH := by
    change (Opens.grothendieckTopology X).W
      ((_root_.PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map uGH)
    simpa [uGH, adj] using
      (Opens.grothendieckTopology X).W_toSheafify
        (MonoidalCategoryStruct.tensorObj
          (C := X.PresheafOfModules) G.val H.val).presheaf
  have huFGH : localEquivalences X (uFG ▷ H.val) :=
    (localEquivalences X).whiskerRight_mem uFG huFG H.val
  have hFuGH : localEquivalences X (F.val ◁ uGH) :=
    (localEquivalences X).whiskerLeft_mem F.val uGH huGH
  exact ⟨
    (Localization.isoOfHom (sheafification X) (localEquivalences X)
      (uFG ▷ H.val) huFGH).symm ≪≫
    (sheafification X).mapIso (α_ F.val G.val H.val) ≪≫
    Localization.isoOfHom (sheafification X) (localEquivalences X)
      (F.val ◁ uGH) hFuGH
  ⟩

end AlgebraicGeometry.Scheme.Modules
