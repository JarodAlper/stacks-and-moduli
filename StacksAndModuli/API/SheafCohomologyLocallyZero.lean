module

public import StacksAndModuli.API.InjectiveSheafFlasque
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Topology.Sheaves.Abelian

/-!
# The cohomology presheaf of an abelian sheaf is locally zero

Supporting API with no Stacks Project counterpart.

For an abelian sheaf `F` on a topological space and `n ≥ 1`, every cohomology class over an
open `U` dies after restricting to a small enough neighbourhood of any point of `U`. Equivalently,
the presheaf `U ↦ Hⁿ(U, F)` has zero sheafification.

This is the input to **Cartan's criterion** — that Čech cohomology with respect to a basis of
acyclics computes derived cohomology — which is what turns the algebraic Čech vanishing of
`StacksAndModuli/API/AffineCechCoeffSystem.lean` into the vanishing of derived cohomology of a
quasi-coherent sheaf on an affine scheme. See `PLAN-hilbert-quot.md`.

The proof is the classical dimension shift. Embed `F` in an injective sheaf `I` with quotient
`Q`. Since `Extⁱ(-, I) = 0` for `i ≥ 1`, the covariant `Ext` long exact sequence writes every
class in `Hⁿ⁺¹(U, F)` as `x₃ ∘ extClass` for some `x₃ ∈ Hⁿ(U, Q)`. In degree `n = 0` the class
`x₃` is a section of `Q` over `U`, which lifts locally to `I` because `I ⟶ Q` is an epimorphism
of sheaves, hence locally surjective; the lift kills the class because
`mk₀ g ∘ extClass = 0`. In higher degrees the induction hypothesis applies to `Q`.

Main declaration:
- `CategoryTheory.Sheaf.exists_isOpen_comp_freeAtMap_eq_zero`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace CategoryTheory.Sheaf

variable {X : TopCat.{u}}

/-- The short exact sequence embedding an abelian sheaf into an injective one. -/
noncomputable abbrev injSES (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (by simp)

lemma injSES_shortExact (F : TopCat.Sheaf AddCommGrpCat.{u} X) : (injSES F).ShortExact where
  exact := ShortComplex.exact_cokernel _
  mono_f := Injective.ι_mono F
  epi_g := coequalizer.π_epi

/-- **The cohomology presheaf is locally zero in positive degrees.** -/
theorem exists_le_comp_freeAtMap_eq_zero :
    ∀ (n : ℕ) (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U : Opens X)
      (α : Ext (freeAt (Opens.grothendieckTopology X) U) F (n + 1)) (x : X), x ∈ U →
      ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧
        (Ext.mk₀ (freeAtMap (Opens.grothendieckTopology X) (homOfLE hVU))).comp α
          (zero_add (n + 1)) = 0 := by
  intro n
  induction n with
  | zero =>
      intro F U α x hx
      set J := Opens.grothendieckTopology X with hJ
      set S := injSES F with hSdef
      have hS : S.ShortExact := injSES_shortExact F
      have hxI : α.comp (Ext.mk₀ S.f) (add_zero 1) = 0 := Ext.eq_zero_of_injective _
      obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ (freeAt J U) hS α hxI rfl
      -- `x₃` is a section of `S.X₃` over `U`; lift it locally through the epimorphism `S.g`
      set s := freeYonedaEquiv J U S.X₃ (Ext.addEquiv₀ x₃) with hs
      have hepi : TopCat.Presheaf.IsLocallySurjective S.g.hom :=
        (TopCat.Sheaf.isLocallySurjective_iff_epi S.g).mpr hS.epi_g
      obtain ⟨V, hVU, ⟨t, ht⟩, hxV⟩ :=
        (TopCat.Presheaf.isLocallySurjective_iff S.g.hom).mp hepi U s x hx
      refine ⟨V, hVU, hxV, ?_⟩
      set y := (freeYonedaEquiv J V S.X₂).symm t with hy
      have hkey : y ≫ S.g = freeAtMap J (homOfLE hVU) ≫ Ext.addEquiv₀ x₃ := by
        refine (freeYonedaEquiv J V S.X₃).injective ?_
        rw [freeYonedaEquiv_naturality_sheaf, freeYonedaEquiv_naturality]
        rw [hy, Equiv.apply_symm_apply]
        exact ht
      have hx₃eq : x₃ = Ext.mk₀ (Ext.addEquiv₀ x₃) := (Ext.mk₀_addEquiv₀_apply x₃).symm
      rw [← hx₃, ← Ext.comp_assoc _ _ _ (zero_add 0) (zero_add 1) (by omega), hx₃eq,
        Ext.mk₀_comp_mk₀, ← hkey, ← Ext.mk₀_comp_mk₀,
        Ext.comp_assoc _ _ _ (add_zero 0) (zero_add 1) (by omega), hS.comp_extClass]
      simp
  | succ n ih =>
      intro F U α x hx
      set J := Opens.grothendieckTopology X with hJ
      set S := injSES F with hSdef
      have hS : S.ShortExact := injSES_shortExact F
      have hxI : α.comp (Ext.mk₀ S.f) (add_zero (n + 2)) = 0 := Ext.eq_zero_of_injective _
      obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ (freeAt J U) hS α hxI rfl
      obtain ⟨V, hVU, hxV, hzero⟩ := ih S.X₃ U x₃ x hx
      refine ⟨V, hVU, hxV, ?_⟩
      rw [← hx₃, ← Ext.comp_assoc _ _ _ (zero_add (n + 1)) rfl (by omega), hzero]
      simp

/-! ## `H¹` as a cokernel of sections -/

variable (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U : Opens X)

/-- The class in `H¹(U, F)` attached to a section of the injective quotient over `U`. -/
noncomputable def h1OfSection
    (q : ((injSES F).X₃.obj.obj (op U) : Type u)) :
    Ext (freeAt (Opens.grothendieckTopology X) U) F 1 :=
  (Ext.mk₀ ((freeYonedaEquiv (Opens.grothendieckTopology X) U (injSES F).X₃).symm q)).comp
    (injSES_shortExact F).extClass (zero_add 1)

/-- **Every degree-one class comes from a section of the injective quotient.** -/
theorem surjective_h1OfSection : Function.Surjective (h1OfSection F U) := by
  intro α
  have hxI : α.comp (Ext.mk₀ (injSES F).f) (add_zero 1) = 0 := Ext.eq_zero_of_injective _
  obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ _ (injSES_shortExact F) α hxI rfl
  refine ⟨freeYonedaEquiv (Opens.grothendieckTopology X) U (injSES F).X₃
    (Ext.addEquiv₀ x₃), ?_⟩
  rw [h1OfSection, Equiv.symm_apply_apply, Ext.mk₀_addEquiv₀_apply, hx₃]

/-- **A degree-one class vanishes exactly when its section lifts to the injective.** -/
theorem h1OfSection_eq_zero_iff (q : ((injSES F).X₃.obj.obj (op U) : Type u)) :
    h1OfSection F U q = 0 ↔
      ∃ t : ((injSES F).X₂.obj.obj (op U) : Type u),
        ((injSES F).g).hom.app (op U) t = q := by
  constructor
  · intro h
    obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ _ (injSES_shortExact F)
      (Ext.mk₀ ((freeYonedaEquiv (Opens.grothendieckTopology X) U (injSES F).X₃).symm q))
      rfl h
    have heq : (Ext.addEquiv₀ x₂) ≫ (injSES F).g
        = (freeYonedaEquiv (Opens.grothendieckTopology X) U (injSES F).X₃).symm q := by
      apply (Ext.mk₀_bijective _ _).injective
      rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_addEquiv₀_apply]
      exact hx₂
    refine ⟨freeYonedaEquiv (Opens.grothendieckTopology X) U (injSES F).X₂
      (Ext.addEquiv₀ x₂), ?_⟩
    rw [← freeYonedaEquiv_naturality_sheaf, heq, Equiv.apply_symm_apply]
  · rintro ⟨t, rfl⟩
    have hfac : (freeYonedaEquiv (Opens.grothendieckTopology X) U (injSES F).X₃).symm
        (((injSES F).g).hom.app (op U) t)
        = (freeYonedaEquiv (Opens.grothendieckTopology X) U (injSES F).X₂).symm t
          ≫ (injSES F).g := by
      refine (freeYonedaEquiv (Opens.grothendieckTopology X) U (injSES F).X₃).injective ?_
      rw [Equiv.apply_symm_apply, freeYonedaEquiv_naturality_sheaf,
        Equiv.apply_symm_apply]
    rw [h1OfSection, hfac, ← Ext.mk₀_comp_mk₀,
      Ext.comp_assoc _ _ _ (add_zero 0) (zero_add 1) (by omega),
      (injSES_shortExact F).comp_extClass]
    simp

/-! ## Gluing local lifts -/

/-- **Compatible local lifts through the injective quotient glue.** If a section `q` of the
quotient over `U` admits lifts over an open cover of `U` which already agree on the overlaps,
then it lifts over `U`.

Together with `h1OfSection_eq_zero_iff` and `surjective_h1OfSection` this is the `H¹` half of
Cartan's criterion: to kill `H¹(U, F)` one takes arbitrary local lifts, whose differences form a
Čech `1`-cocycle for `F`, and corrects them by a coboundary — which is exactly what
`Ȟ¹(𝒰, F) = 0` provides. -/
theorem exists_lift_of_compatible {ι : Type*} (V : ι → Opens X)
    (hVU : ∀ i, V i ≤ U) (hcover : U ≤ iSup V)
    (q : ((injSES F).X₃.obj.obj (op U) : Type u))
    (s : ∀ i, ((injSES F).X₂.obj.obj (op (V i)) : Type u))
    (hs : ∀ i, ((injSES F).g).hom.app (op (V i)) (s i)
      = (injSES F).X₃.obj.map (homOfLE (hVU i)).op q)
    (hcompat : TopCat.Presheaf.IsCompatible (injSES F).X₂.val V s) :
    ∃ w : ((injSES F).X₂.obj.obj (op U) : Type u),
      ((injSES F).g).hom.app (op U) w = q := by
  obtain ⟨w, hw, -⟩ := (injSES F).X₂.existsUnique_gluing' V U (fun i => homOfLE (hVU i))
    hcover s hcompat
  refine ⟨w, ?_⟩
  refine (injSES F).X₃.eq_of_locally_eq' V U (fun i => homOfLE (hVU i)) hcover _ _ fun i => ?_
  rw [← ConcreteCategory.comp_apply, ← NatTrans.naturality, ConcreteCategory.comp_apply,
    hw i, hs i]

/-- **If `H¹(V, F)` vanishes, every section of the injective quotient over `V` lifts.**  This
is the form in which acyclicity on the members of a cover feeds the `H¹` half of Cartan's
criterion: for an affine open of a scheme and a quasicoherent `F` the hypothesis is
`AlgebraicGeometry.Scheme.Modules.subsingleton_HPrime_of_isAffineOpen`. -/
theorem exists_lift_of_subsingleton_HPrime_one
    (h : Subsingleton (Ext (freeAt (Opens.grothendieckTopology X) U) F 1))
    (q : ((injSES F).X₃.obj.obj (op U) : Type u)) :
    ∃ t : ((injSES F).X₂.obj.obj (op U) : Type u),
      ((injSES F).g).hom.app (op U) t = q :=
  (h1OfSection_eq_zero_iff F U q).mp (@Subsingleton.elim _ h _ 0)

/-- **Correcting local lifts by a Čech coboundary makes them compatible.** If the pairwise
differences of local lifts of `q` are the coboundary of a family `t` of sections of `F`, then
subtracting `t` produces lifts that agree on the overlaps. -/
theorem exists_compatible_lifts_of_coboundary {ι : Type*} (V : ι → Opens X)
    (hVU : ∀ i, V i ≤ U)
    (q : ((injSES F).X₃.obj.obj (op U) : Type u))
    (s : ∀ i, ((injSES F).X₂.obj.obj (op (V i)) : Type u))
    (hs : ∀ i, ((injSES F).g).hom.app (op (V i)) (s i)
      = (injSES F).X₃.obj.map (homOfLE (hVU i)).op q)
    (t : ∀ i, (F.obj.obj (op (V i)) : Type u))
    (ht : ∀ i j,
      (injSES F).X₂.obj.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (s i)
          - (injSES F).X₂.obj.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (s j)
        = ((injSES F).f).hom.app (op (V i ⊓ V j))
            (F.obj.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (t i)
              - F.obj.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (t j))) :
    ∃ s' : ∀ i, ((injSES F).X₂.obj.obj (op (V i)) : Type u),
      (∀ i, ((injSES F).g).hom.app (op (V i)) (s' i)
        = (injSES F).X₃.obj.map (homOfLE (hVU i)).op q) ∧
      TopCat.Presheaf.IsCompatible (injSES F).X₂.val V s' := by
  refine ⟨fun i => s i - ((injSES F).f).hom.app (op (V i)) (t i), fun i => ?_, fun i j => ?_⟩
  · have h0 : ∀ u : ((injSES F).X₁.obj.obj (op (V i)) : Type u),
        ((injSES F).g).hom.app (op (V i)) (((injSES F).f).hom.app (op (V i)) u) = 0 := by
      intro u
      have h2 : ((Injective.ι F ≫ cokernel.π (Injective.ι F)).hom.app (op (V i))) u = 0 := by
        rw [cokernel.condition]
        rfl
      exact h2
    rw [map_sub, hs i, h0, sub_zero]
  · have hnat : ∀ (W : Opens X) (hW : W ≤ V i) (u : (F.obj.obj (op (V i)) : Type u)),
        (injSES F).X₂.obj.map (homOfLE hW).op (((injSES F).f).hom.app (op (V i)) u)
          = ((injSES F).f).hom.app (op W) (F.obj.map (homOfLE hW).op u) := by
      intro W hW u
      rw [← ConcreteCategory.comp_apply, ← NatTrans.naturality, ConcreteCategory.comp_apply]
    have hnat' : ∀ (W : Opens X) (hW : W ≤ V j) (u : (F.obj.obj (op (V j)) : Type u)),
        (injSES F).X₂.obj.map (homOfLE hW).op (((injSES F).f).hom.app (op (V j)) u)
          = ((injSES F).f).hom.app (op W) (F.obj.map (homOfLE hW).op u) := by
      intro W hW u
      rw [← ConcreteCategory.comp_apply, ← NatTrans.naturality, ConcreteCategory.comp_apply]
    have h := ht i j
    show (injSES F).X₂.obj.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op
        (s i - ((injSES F).f).hom.app (op (V i)) (t i))
      = (injSES F).X₂.obj.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op
        (s j - ((injSES F).f).hom.app (op (V j)) (t j))
    rw [map_sub, map_sub, hnat _ inf_le_left, hnat' _ inf_le_right,
      sub_eq_sub_iff_sub_eq_sub, ← map_sub]
    exact h

/-- **`H¹` vanishes on an open where every section of the injective quotient lifts compatibly on
some cover.** -/
theorem subsingleton_HPrime_one_of_forall_exists_compatible_lifts
    (H : ∀ q : ((injSES F).X₃.obj.obj (op U) : Type u),
      ∃ (ι : Type u) (V : ι → Opens X) (hVU : ∀ i, V i ≤ U) (_ : U ≤ iSup V)
        (s : ∀ i, ((injSES F).X₂.obj.obj (op (V i)) : Type u)),
        (∀ i, ((injSES F).g).hom.app (op (V i)) (s i)
          = (injSES F).X₃.obj.map (homOfLE (hVU i)).op q) ∧
        TopCat.Presheaf.IsCompatible (injSES F).X₂.val V s) :
    Subsingleton (Ext (freeAt (Opens.grothendieckTopology X) U) F 1) := by
  refine subsingleton_of_forall_eq 0 fun α => ?_
  obtain ⟨q, rfl⟩ := surjective_h1OfSection F U α
  obtain ⟨ι, V, hVU, hcover, s, hs, hcompat⟩ := H q
  exact (h1OfSection_eq_zero_iff F U q).mpr
    (exists_lift_of_compatible F U V hVU hcover q s hs hcompat)

/-- **The `H¹` half of Cartan's criterion.** `H¹(U, F)` vanishes as soon as every section of the
injective quotient over `U` admits local lifts on some open cover whose difference cocycle is a
Čech coboundary with values in `F`.

Arbitrary local lifts always exist, because `I ⟶ Q` is an epimorphism of sheaves; so the only
real hypothesis is that the resulting `1`-cocycle is a coboundary, i.e. `Ȟ¹(𝒰, F) = 0`. For
`X = Spec R` and the cover by the distinguished opens `D(f i)` that is
`LocalizedModule.exact_coeffDₗ_cechCoeffSystem`. -/
theorem subsingleton_HPrime_one_of_forall_coboundary
    (H : ∀ q : ((injSES F).X₃.obj.obj (op U) : Type u),
      ∃ (ι : Type u) (V : ι → Opens X) (hVU : ∀ i, V i ≤ U) (_ : U ≤ iSup V)
        (s : ∀ i, ((injSES F).X₂.obj.obj (op (V i)) : Type u))
        (t : ∀ i, (F.obj.obj (op (V i)) : Type u)),
        (∀ i, ((injSES F).g).hom.app (op (V i)) (s i)
          = (injSES F).X₃.obj.map (homOfLE (hVU i)).op q) ∧
        (∀ i j,
          (injSES F).X₂.obj.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (s i)
              - (injSES F).X₂.obj.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (s j)
            = ((injSES F).f).hom.app (op (V i ⊓ V j))
                (F.obj.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (t i)
                  - F.obj.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (t j)))) :
    Subsingleton (Ext (freeAt (Opens.grothendieckTopology X) U) F 1) := by
  refine subsingleton_HPrime_one_of_forall_exists_compatible_lifts F U fun q => ?_
  obtain ⟨ι, V, hVU, hcover, s, t, hs, ht⟩ := H q
  obtain ⟨s', hs', hcompat⟩ :=
    exists_compatible_lifts_of_coboundary F U V hVU q s hs t ht
  exact ⟨ι, V, hVU, hcover, s', hs', hcompat⟩

/-- **The `H¹` half of Cartan's criterion, with the local lifts supplied by acyclicity.**

If every member of a cover of `U` is `F`-acyclic in degree one, arbitrary local lifts exist,
and the only remaining hypothesis is that the resulting Čech `1`-cocycle is a coboundary —
that is, `Ȟ¹(𝒰, F) = 0`.

For `X` a scheme, `𝒰` a cover of `U` by affine opens and `F` quasicoherent, the acyclicity
hypothesis is `AlgebraicGeometry.Scheme.Modules.subsingleton_HPrime_of_isAffineOpen`. -/
theorem subsingleton_HPrime_one_of_acyclic_cover
    {ι : Type u} (V : ι → Opens X) (hVU : ∀ i, V i ≤ U) (hcover : U ≤ iSup V)
    (hacyc : ∀ i, Subsingleton (Ext (freeAt (Opens.grothendieckTopology X) (V i)) F 1))
    (hcech : ∀ (q : ((injSES F).X₃.obj.obj (op U) : Type u))
        (s : ∀ i, ((injSES F).X₂.obj.obj (op (V i)) : Type u)),
        (∀ i, ((injSES F).g).hom.app (op (V i)) (s i)
          = (injSES F).X₃.obj.map (homOfLE (hVU i)).op q) →
        ∃ t : ∀ i, (F.obj.obj (op (V i)) : Type u), ∀ i j,
          (injSES F).X₂.obj.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (s i)
              - (injSES F).X₂.obj.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (s j)
            = ((injSES F).f).hom.app (op (V i ⊓ V j))
                (F.obj.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (t i)
                  - F.obj.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (t j))) :
    Subsingleton (Ext (freeAt (Opens.grothendieckTopology X) U) F 1) := by
  refine subsingleton_HPrime_one_of_forall_coboundary F U fun q => ?_
  choose s hs using fun i => exists_lift_of_subsingleton_HPrime_one F (V i) (hacyc i)
    ((injSES F).X₃.obj.map (homOfLE (hVU i)).op q)
  obtain ⟨t, ht⟩ := hcech q s hs
  exact ⟨ι, V, hVU, hcover, s, t, hs, ht⟩

end CategoryTheory.Sheaf

end
