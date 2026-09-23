module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import StacksAndModuli.API.CokernelEpiComp
public import StacksAndModuli.API.OpenCoverModuleMorphismZero
public import StacksAndModuli.API.PresheafSubmoduleRange

/-!
# Descending a quotient of a sheaf of modules along an open cover

Supporting API with no Stacks Project counterpart (the Lean-side effectivity of
Zariski descent for quotient presentations, consumed by §2.2.3's relative
Grassmannian).

Given a sheaf of modules `M` on a scheme `X`, an open cover `𝒰`, and for each index a
monomorphism `k i : K i ⟶ M|_{U i}` of sheaves of modules, we define the sections of
`M` that locally come from the `K i` (`openSubmoduleCondition`), glue them to a
restriction-stable sectionwise submodule of `M`, and, under the compatibility of the
local ranges on overlaps, will construct the descended quotient together with its
comparison to the local cokernels.

Main declarations (first layer):
- `Modules.openSubmoduleCondition`: the sections of `M` over `W` whose restriction to
  `f''(f⁻¹W)` lies in the range of `k`;
- `Modules.mem_openSubmoduleCondition_iff`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X U : Scheme.{u}}

/-- The restriction-stable family of submodules of `M` singling out the sections whose
restriction to the image of `f` comes from `K` through `k`. Over an open `W ⊆ X`, a
section `s ∈ Γ(M, W)` satisfies the condition when some `t ∈ Γ(K, f⁻¹W)` maps to the
restriction of `s` under `k`. -/
noncomputable def openSubmoduleCondition (f : U ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) {K : U.Modules} (k : K ⟶ (restrictFunctor f).obj M) :
    M.val.Submodule where
  obj W :=
    { carrier := { s : Γ(M, W.unop) | ∃ t : Γ(K, f ⁻¹ᵁ W.unop),
        (k.app (f ⁻¹ᵁ W.unop)).hom t =
          (M.presheaf.map (homOfLE (f.image_preimage_le W.unop)).op).hom s }
      add_mem' := by
        rintro s₁ s₂ ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩
        exact ⟨t₁ + t₂, by rw [map_add, map_add, ht₁, ht₂]⟩
      zero_mem' := ⟨0, by rw [map_zero, map_zero]⟩
      smul_mem' := by
        rintro r s ⟨t, ht⟩
        refine ⟨((f.appIso (f ⁻¹ᵁ W.unop)).hom
          ((X.presheaf.map (homOfLE (f.image_preimage_le W.unop)).op).hom r)) • t, ?_⟩
        rw [Hom.app_smul, ht, Modules.map_smul]
        change ((f.appIso (f ⁻¹ᵁ W.unop)).inv ((f.appIso (f ⁻¹ᵁ W.unop)).hom
            ((X.presheaf.map (homOfLE (f.image_preimage_le W.unop)).op).hom r))) •
            ((M.presheaf.map (homOfLE (f.image_preimage_le W.unop)).op).hom s) = _
        rw [Iso.hom_inv_id_apply] }
  map {W W'} ρ := by
    intro s hs
    obtain ⟨t, ht⟩ := hs
    refine Submodule.mem_comap.mpr
      ⟨(K.presheaf.map (homOfLE
        (Scheme.Hom.preimage_mono f (leOfHom ρ.unop))).op).hom t, ?_⟩
    have hnat := CategoryTheory.congr_fun (k.mapPresheaf.naturality
      (homOfLE (Scheme.Hom.preimage_mono f (leOfHom ρ.unop))).op) t
    dsimp at hnat
    change (k.app (f ⁻¹ᵁ W'.unop)).hom
        ((K.presheaf.map (homOfLE
          (Scheme.Hom.preimage_mono f (leOfHom ρ.unop))).op).hom t) =
      (M.presheaf.map (homOfLE (f.image_preimage_le W'.unop)).op).hom
        ((M.presheaf.map ρ).hom s)
    rw [hnat, ht]
    have hcomp₁ : M.presheaf.map ρ ≫
        M.presheaf.map (homOfLE (f.image_preimage_le W'.unop)).op =
        M.presheaf.map (homOfLE (f.image_preimage_le W.unop)).op ≫
          ((restrictFunctor f).obj M).presheaf.map
            (homOfLE (Scheme.Hom.preimage_mono f (leOfHom ρ.unop))).op := by
      rw [restrict_map, ← Functor.map_comp, ← Functor.map_comp]
      congr 1
    have h2 := CategoryTheory.congr_fun hcomp₁ s
    exact h2.symm

lemma mem_openSubmoduleCondition_iff (f : U ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) {K : U.Modules} (k : K ⟶ (restrictFunctor f).obj M)
    (W : X.Opens) (s : Γ(M, W)) :
    s ∈ (openSubmoduleCondition f M k).obj (Opposite.op W) ↔
      ∃ t : Γ(K, f ⁻¹ᵁ W), (k.app (f ⁻¹ᵁ W)).hom t =
        (M.presheaf.map (homOfLE (f.image_preimage_le W)).op).hom s :=
  Iff.rfl

/-- Over the image of a chart open, the condition is exactly membership in the range
of `k` at that open: the preimage-transport is absorbed. -/
lemma mem_openSubmoduleCondition_image_iff (f : U ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) {K : U.Modules} (k : K ⟶ (restrictFunctor f).obj M)
    (V : U.Opens) (s : Γ(M, f ''ᵁ V)) :
    s ∈ (openSubmoduleCondition f M k).obj (Opposite.op (f ''ᵁ V)) ↔
      ∃ t : Γ(K, V), (k.app V).hom t = s := by
  rw [mem_openSubmoduleCondition_iff]
  have hnat : ∀ {V₁ V₂ : U.Opens} (ρ : Opposite.op V₁ ⟶ Opposite.op V₂)
      (x : Γ(K, V₁)),
      ((k.app V₂).hom) (((K.presheaf.map ρ).hom) x) =
        ((((restrictFunctor f).obj M).presheaf.map ρ).hom) ((k.app V₁).hom x) :=
    fun ρ x ↦ CategoryTheory.congr_fun (k.mapPresheaf.naturality ρ) x
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨(K.presheaf.map (homOfLE (f.preimage_image_eq V).ge).op).hom t, ?_⟩
    rw [hnat, ht]
    have hid : M.presheaf.map
        (homOfLE (f.image_preimage_le (f ''ᵁ V))).op ≫
        ((restrictFunctor f).obj M).presheaf.map
          (homOfLE (f.preimage_image_eq V).ge).op = 𝟙 _ := by
      rw [restrict_map, ← Functor.map_comp,
        show (homOfLE (f.image_preimage_le (f ''ᵁ V))).op ≫
            (f.opensFunctor.map (homOfLE (f.preimage_image_eq V).ge)).op = 𝟙 _ from
          Subsingleton.elim _ _, CategoryTheory.Functor.map_id]
    exact CategoryTheory.congr_fun hid s
  · rintro ⟨t, rfl⟩
    refine ⟨(K.presheaf.map (homOfLE (f.preimage_image_eq V).le).op).hom t, ?_⟩
    rw [hnat]
    have hsame : ((restrictFunctor f).obj M).presheaf.map
        (homOfLE (f.preimage_image_eq V).le).op =
        M.presheaf.map (homOfLE (f.image_preimage_le (f ''ᵁ V))).op := by
      rw [restrict_map]
      congr 1
    exact CategoryTheory.congr_fun hsame ((k.app V).hom t)

/-- The glued kernel of an open-cover family of local submodule inclusions: the
sections of `M` which on each chart come from the corresponding local kernel. -/
noncomputable def openCoverSubmodule (𝒰 : Scheme.OpenCover.{u} X) (M : X.Modules)
    {K : ∀ i, (𝒰.X i).Modules}
    (k : ∀ i, K i ⟶ (restrictFunctor (𝒰.f i)).obj M) :
    M.val.Submodule :=
  ⨅ i, openSubmoduleCondition (𝒰.f i) M (k i)

lemma mem_openCoverSubmodule_iff (𝒰 : Scheme.OpenCover.{u} X) (M : X.Modules)
    {K : ∀ i, (𝒰.X i).Modules}
    (k : ∀ i, K i ⟶ (restrictFunctor (𝒰.f i)).obj M) (W : X.Opens) (s : Γ(M, W)) :
    s ∈ (openCoverSubmodule 𝒰 M k).obj (Opposite.op W) ↔
      ∀ i, s ∈ (openSubmoduleCondition (𝒰.f i) M (k i)).obj (Opposite.op W) := by
  rw [openCoverSubmodule, iInf, PresheafOfModules.Submodule.sInf_obj]
  simp only [Submodule.mem_iInf]
  constructor
  · intro h i
    exact h _ ⟨i, rfl⟩
  · rintro h N ⟨i, rfl⟩
    exact h i

/-- The underlying presheaf morphism of a monomorphism of `𝒪ₓ`-modules is a
monomorphism. -/
lemma val_mono_of_mono {Y : Scheme.{u}} {A B : Y.Modules} (φ : A ⟶ B) [Mono φ] :
    Mono φ.val :=
  Functor.map_mono (SheafOfModules.forget Y.ringCatSheaf) φ

/-- A monomorphism of `𝒪ₓ`-modules is sectionwise injective. -/
lemma app_injective_of_mono {Y : Scheme.{u}} {A B : Y.Modules} (φ : A ⟶ B) [Mono φ]
    (V : Y.Opens) : Function.Injective (φ.app V).hom := by
  have := val_mono_of_mono φ
  exact PresheafOfModules.injective_of_mono φ.val (Opposite.op V)

/-- Applying the forgetful functor's image of an isomorphism of `𝒪ₓ`-modules is
applying the isomorphism. -/
lemma forget_mapIso_hom_app_apply {Y : Scheme.{u}} {A B : Y.Modules} (e : A ≅ B)
    (V : Y.Opens) (x : Γ(A, V)) :
    (((SheafOfModules.forget Y.ringCatSheaf).mapIso e).hom.app
      (Opposite.op V)) x = (e.hom.app V).hom x := rfl

/-- The glued kernel of a family of monomorphic local inclusions over an open cover is
a subsheaf of `M`: sections satisfying all chart conditions glue, because the
witnesses glue in each `K i` (a sheaf) and are unique (each `k i` is a monomorphism).
This is the kernel object of the descended quotient. -/
noncomputable def openCoverKernelSheaf (𝒰 : Scheme.OpenCover.{u} X) (M : X.Modules)
    {K : ∀ i, (𝒰.X i).Modules}
    (k : ∀ i, K i ⟶ (restrictFunctor (𝒰.f i)).obj M) [∀ i, Mono (k i)] :
    X.Modules where
  val := (openCoverSubmodule 𝒰 M k).toPresheafOfModules
  isSheaf := by
    change TopCat.Presheaf.IsSheaf _
    rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
    intro ι W sf hcompat
    -- the underlying `M`-sections of the family
    have hval : ∀ {V V' : (TopologicalSpace.Opens ↥X)ᵒᵖ} (ρ : V ⟶ V')
        (x : ToType ((openCoverSubmodule 𝒰 M k).toPresheafOfModules.presheaf.obj V)),
        (((openCoverSubmodule 𝒰 M k).toPresheafOfModules.presheaf.map ρ) x).val =
          (M.presheaf.map ρ) x.val := by
      intro V V' ρ x
      exact PresheafOfModules.Submodule.toPresheafOfModules_map_apply
        (openCoverSubmodule 𝒰 M k) ρ x
    let msf : ∀ i, ToType (M.presheaf.obj (Opposite.op (W i))) := fun i ↦ (sf i).1
    have hmcompat : TopCat.Presheaf.IsCompatible M.presheaf W msf := by
      intro i i'
      have h1 := congrArg Subtype.val (hcompat i i')
      exact (hval _ (sf i)).symm.trans (h1.trans (hval _ (sf i')))
    obtain ⟨s, hs, huniq⟩ := (abSheaf M).existsUnique_gluing W msf hmcompat
    have hmem : s ∈ (openCoverSubmodule 𝒰 M k).obj (Opposite.op (iSup W)) := by
      rw [mem_openCoverSubmodule_iff]
      intro j
      rw [mem_openSubmoduleCondition_iff]
      -- witnesses over each piece of the cover
      have hwit : ∀ i, ∃ t : Γ(K j, (𝒰.f j) ⁻¹ᵁ W i),
          ((k j).app ((𝒰.f j) ⁻¹ᵁ W i)).hom t =
            (M.presheaf.map
              (homOfLE ((𝒰.f j).image_preimage_le (W i))).op).hom (msf i) := by
        intro i
        have h2 := (sf i).2
        rw [mem_openCoverSubmodule_iff] at h2
        exact (mem_openSubmoduleCondition_iff _ M (k j) (W i) (msf i)).mp (h2 j)
      choose tj htj using hwit
      -- the witnesses agree on overlaps because `k j` is sectionwise injective
      have htcompat : TopCat.Presheaf.IsCompatible (K j).presheaf
          (fun i ↦ (𝒰.f j) ⁻¹ᵁ (W i)) tj := by
        intro i i'
        apply app_injective_of_mono (k j)
        beta_reduce
        have hnat : ∀ (a : ι) (ρ : Opposite.op ((𝒰.f j) ⁻¹ᵁ W a) ⟶
              Opposite.op ((𝒰.f j) ⁻¹ᵁ W i ⊓ (𝒰.f j) ⁻¹ᵁ W i'))
            (x : Γ(K j, (𝒰.f j) ⁻¹ᵁ W a)),
            ((k j).app _).hom (((K j).presheaf.map ρ).hom x) =
              (((restrictFunctor (𝒰.f j)).obj M).presheaf.map ρ).hom
                (((k j).app _).hom x) := fun a ρ x ↦
          CategoryTheory.congr_fun ((k j).mapPresheaf.naturality ρ) x
        rw [hnat i _ (tj i), hnat i' _ (tj i'), htj i, htj i']
        have hcanon : ((𝒰.f j) ''ᵁ ((𝒰.f j) ⁻¹ᵁ W i ⊓ (𝒰.f j) ⁻¹ᵁ W i')) ≤
            W i ⊓ W i' :=
          le_inf ((Scheme.Hom.image_mono _ inf_le_left).trans
              ((𝒰.f j).image_preimage_le (W i)))
            ((Scheme.Hom.image_mono _ inf_le_right).trans
              ((𝒰.f j).image_preimage_le (W i')))
        have hside : ∀ (a : ι) (ρ : Opposite.op ((𝒰.f j) ⁻¹ᵁ W a) ⟶
              Opposite.op ((𝒰.f j) ⁻¹ᵁ W i ⊓ (𝒰.f j) ⁻¹ᵁ W i'))
            (σ : Opposite.op (W a) ⟶ Opposite.op (W i ⊓ W i')),
            M.presheaf.map (homOfLE ((𝒰.f j).image_preimage_le (W a))).op ≫
              ((restrictFunctor (𝒰.f j)).obj M).presheaf.map ρ =
            M.presheaf.map σ ≫ M.presheaf.map (homOfLE hcanon).op := by
          intro a ρ σ
          rw [show ρ = ρ.unop.op from rfl, restrict_map, ← Functor.map_comp,
            ← Functor.map_comp]
          congr 1
        have h5 := CategoryTheory.congr_fun (hside i
          (TopologicalSpace.Opens.infLELeft _ _).op
          (TopologicalSpace.Opens.infLELeft _ _).op) (msf i)
        have h6 := CategoryTheory.congr_fun (hside i'
          (TopologicalSpace.Opens.infLERight _ _).op
          (TopologicalSpace.Opens.infLERight _ _).op) (msf i')
        refine h5.trans (Eq.trans ?_ h6.symm)
        exact congrArg _ (hmcompat i i')
      obtain ⟨t₀, ht₀, -⟩ := (abSheaf (K j)).existsUnique_gluing'
        (fun i ↦ (𝒰.f j) ⁻¹ᵁ (W i)) ((𝒰.f j) ⁻¹ᵁ (iSup W))
        (fun i ↦ homOfLE (Scheme.Hom.preimage_mono _ (le_iSup W i)))
        (by
          intro x hx
          obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
            (show (𝒰.f j).base x ∈ iSup W from hx)
          exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩)
        tj htcompat
      refine ⟨t₀, ?_⟩
      -- both sides are sections of the restricted sheaf agreeing on a cover
      apply (abSheaf ((restrictFunctor (𝒰.f j)).obj M)).eq_of_locally_eq'
        (fun i ↦ (𝒰.f j) ⁻¹ᵁ (W i)) ((𝒰.f j) ⁻¹ᵁ (iSup W))
        (fun i ↦ homOfLE (Scheme.Hom.preimage_mono _ (le_iSup W i)))
        (by
          intro x hx
          obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
            (show (𝒰.f j).base x ∈ iSup W from hx)
          exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩)
      intro i
      have hnat2 : (((restrictFunctor (𝒰.f j)).obj M).presheaf.map
          (homOfLE (Scheme.Hom.preimage_mono (𝒰.f j) (le_iSup W i))).op).hom
            (((k j).app _).hom t₀) =
          ((k j).app _).hom (((K j).presheaf.map
            (homOfLE (Scheme.Hom.preimage_mono (𝒰.f j) (le_iSup W i))).op).hom t₀) :=
        (CategoryTheory.congr_fun ((k j).mapPresheaf.naturality
          (homOfLE (Scheme.Hom.preimage_mono (𝒰.f j) (le_iSup W i))).op) t₀).symm
      rw [hnat2, ht₀ i, htj i]
      -- restriction of the glued section
      have hfuse2 : (M.presheaf.map
            (homOfLE ((𝒰.f j).image_preimage_le (iSup W))).op ≫
          ((restrictFunctor (𝒰.f j)).obj M).presheaf.map
            (homOfLE (Scheme.Hom.preimage_mono (𝒰.f j) (le_iSup W i))).op) =
          (M.presheaf.map (homOfLE (le_iSup W i)).op ≫
            M.presheaf.map (homOfLE ((𝒰.f j).image_preimage_le (W i))).op) := by
        rw [restrict_map, ← Functor.map_comp, ← Functor.map_comp]
        congr 1
      have h7 := CategoryTheory.congr_fun hfuse2 s
      refine Eq.trans ?_ h7.symm
      exact (congrArg _ (hs i)).symm
    refine ⟨⟨s, hmem⟩, ?_, ?_⟩
    · intro i
      exact Subtype.ext ((hval _ ⟨s, hmem⟩).trans (hs i))
    · intro y hy
      apply Subtype.ext
      exact huniq y.1 fun i ↦
        (hval _ y).symm.trans (congrArg Subtype.val (hy i))

/-- The inclusion of the glued kernel into the ambient sheaf. -/
noncomputable def openCoverKernelι (𝒰 : Scheme.OpenCover.{u} X) (M : X.Modules)
    {K : ∀ i, (𝒰.X i).Modules}
    (k : ∀ i, K i ⟶ (restrictFunctor (𝒰.f i)).obj M) [∀ i, Mono (k i)] :
    openCoverKernelSheaf 𝒰 M k ⟶ M :=
  ⟨(openCoverSubmodule 𝒰 M k).ι⟩

instance openCoverKernelι_mono (𝒰 : Scheme.OpenCover.{u} X) (M : X.Modules)
    {K : ∀ i, (𝒰.X i).Modules}
    (k : ∀ i, K i ⟶ (restrictFunctor (𝒰.f i)).obj M) [∀ i, Mono (k i)] :
    Mono (openCoverKernelι 𝒰 M k) := by
  have hval : Mono (openCoverKernelι 𝒰 M k).val :=
    inferInstanceAs (Mono (openCoverSubmodule 𝒰 M k).ι)
  exact Functor.mono_of_mono_map (SheafOfModules.forget X.ringCatSheaf) hval

/-- The quotient of `M` by the glued kernel of an open-cover family of local
inclusions. This is the sheaf that descends the local cokernels. -/
noncomputable def openCoverQuotientSheaf (𝒰 : Scheme.OpenCover.{u} X) (M : X.Modules)
    {K : ∀ i, (𝒰.X i).Modules}
    (k : ∀ i, K i ⟶ (restrictFunctor (𝒰.f i)).obj M) [∀ i, Mono (k i)] :
    X.Modules :=
  cokernel (openCoverKernelι 𝒰 M k)

/-- The projection onto the descended quotient. -/
noncomputable def openCoverQuotientMap (𝒰 : Scheme.OpenCover.{u} X) (M : X.Modules)
    {K : ∀ i, (𝒰.X i).Modules}
    (k : ∀ i, K i ⟶ (restrictFunctor (𝒰.f i)).obj M) [∀ i, Mono (k i)] :
    M ⟶ openCoverQuotientSheaf 𝒰 M k :=
  cokernel.π (openCoverKernelι 𝒰 M k)

instance openCoverQuotientMap_epi (𝒰 : Scheme.OpenCover.{u} X) (M : X.Modules)
    {K : ∀ i, (𝒰.X i).Modules}
    (k : ∀ i, K i ⟶ (restrictFunctor (𝒰.f i)).obj M) [∀ i, Mono (k i)] :
    Epi (openCoverQuotientMap 𝒰 M k) :=
  inferInstanceAs (Epi (cokernel.π _))

/-- Effectivity of an open-cover family of local kernel inclusions: restricting the
glued kernel back to each chart recovers exactly the local kernel, as sectionwise
ranges inside the restricted ambient sheaf. -/
def OpenCoverSubmoduleCompatible (𝒰 : Scheme.OpenCover.{u} X) (M : X.Modules)
    (K : ∀ i, (𝒰.X i).Modules)
    (k : ∀ i, K i ⟶ (restrictFunctor (𝒰.f i)).obj M) [∀ i, Mono (k i)] : Prop :=
  ∀ i, PresheafOfModules.Submodule.range
      ((restrictFunctor (𝒰.f i)).map (openCoverKernelι 𝒰 M k)).val =
    PresheafOfModules.Submodule.range (k i).val

instance restrict_openCoverKernelι_val_mono (𝒰 : Scheme.OpenCover.{u} X)
    (M : X.Modules) {K : ∀ i, (𝒰.X i).Modules}
    (k : ∀ i, K i ⟶ (restrictFunctor (𝒰.f i)).obj M) [∀ i, Mono (k i)] (i : 𝒰.I₀) :
    Mono ((restrictFunctor (𝒰.f i)).map (openCoverKernelι 𝒰 M k)).val := by
  apply PresheafOfModules.mono_of_injective
  intro V
  exact fun a b h ↦ Subtype.ext h

/-- Under effectivity, restricting the glued kernel to a chart recovers the local
kernel, compatibly with the inclusions into the restricted ambient sheaf. -/
noncomputable def openCoverKernelRestrictIso (𝒰 : Scheme.OpenCover.{u} X)
    (M : X.Modules) {K : ∀ i, (𝒰.X i).Modules}
    (k : ∀ i, K i ⟶ (restrictFunctor (𝒰.f i)).obj M) [∀ i, Mono (k i)]
    (hcompat : OpenCoverSubmoduleCompatible 𝒰 M K k) (i : 𝒰.I₀) :
    (restrictFunctor (𝒰.f i)).obj (openCoverKernelSheaf 𝒰 M k) ≅ K i :=
  haveI : Mono (k i).val := val_mono_of_mono (k i)
  ((restrictFunctor (𝒰.f i)).obj M).isoOfRangeEq
    ((restrictFunctor (𝒰.f i)).map (openCoverKernelι 𝒰 M k)) (k i) (hcompat i)

@[reassoc (attr := simp)]
lemma openCoverKernelRestrictIso_hom_comp (𝒰 : Scheme.OpenCover.{u} X)
    (M : X.Modules) {K : ∀ i, (𝒰.X i).Modules}
    (k : ∀ i, K i ⟶ (restrictFunctor (𝒰.f i)).obj M) [∀ i, Mono (k i)]
    (hcompat : OpenCoverSubmoduleCompatible 𝒰 M K k) (i : 𝒰.I₀) :
    (openCoverKernelRestrictIso 𝒰 M k hcompat i).hom ≫ k i =
      (restrictFunctor (𝒰.f i)).map (openCoverKernelι 𝒰 M k) := by
  have : Mono (k i).val := val_mono_of_mono (k i)
  exact SheafOfModules.isoOfRangeEq_hom_comp _ _ _ _

/-- Under effectivity, restricting the descended quotient to a chart recovers the
local cokernel model. -/
noncomputable def openCoverQuotientRestrictIso (𝒰 : Scheme.OpenCover.{u} X)
    (M : X.Modules) {K : ∀ i, (𝒰.X i).Modules}
    (k : ∀ i, K i ⟶ (restrictFunctor (𝒰.f i)).obj M) [∀ i, Mono (k i)]
    (hcompat : OpenCoverSubmoduleCompatible 𝒰 M K k) (i : 𝒰.I₀) :
    (restrictFunctor (𝒰.f i)).obj (openCoverQuotientSheaf 𝒰 M k) ≅
      cokernel (k i) :=
  (PreservesCokernel.iso (restrictFunctor (𝒰.f i)) (openCoverKernelι 𝒰 M k)) ≪≫
    cokernel.mapIso _ _ (openCoverKernelRestrictIso 𝒰 M k hcompat i) (Iso.refl _)
      (by
        rw [Iso.refl_hom, Category.comp_id]
        exact (openCoverKernelRestrictIso_hom_comp 𝒰 M k hcompat i).symm)

/-- Effectivity follows from the pairwise inclusion of the chart conditions over
opens inside each chart's range: restricting the glued kernel to chart `i` then has
exactly the sectionwise range of `k i`. -/
lemma openCoverSubmoduleCompatible_of_openSubmoduleCondition_le_on_ranges
    (𝒰 : Scheme.OpenCover.{u} X) (M : X.Modules)
    {K : ∀ i, (𝒰.X i).Modules}
    (k : ∀ i, K i ⟶ (restrictFunctor (𝒰.f i)).obj M) [∀ i, Mono (k i)]
    (hpair : ∀ i j (W : X.Opens), W ≤ (𝒰.f i).opensRange →
      ∀ s : Γ(M, W),
        s ∈ (openSubmoduleCondition (𝒰.f i) M (k i)).obj (Opposite.op W) →
        s ∈ (openSubmoduleCondition (𝒰.f j) M (k j)).obj (Opposite.op W)) :
    OpenCoverSubmoduleCompatible 𝒰 M K k := by
  intro i
  refine PresheafOfModules.Submodule.ext fun V ↦ ?_
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    have hy : (y.val : Γ(M, (𝒰.f i) ''ᵁ V.unop)) ∈
        (openCoverSubmodule 𝒰 M k).obj (Opposite.op ((𝒰.f i) ''ᵁ V.unop)) := y.2
    rw [mem_openCoverSubmodule_iff] at hy
    obtain ⟨t, ht⟩ := (mem_openSubmoduleCondition_image_iff (𝒰.f i) M (k i)
      V.unop y.val).mp (hy i)
    exact ⟨t, ht⟩
  · rintro x ⟨t, rfl⟩
    refine ⟨⟨(k i).app V.unop t, ?_⟩, rfl⟩
    rw [mem_openCoverSubmodule_iff]
    intro j
    refine hpair i j ((𝒰.f i) ''ᵁ V.unop) (Scheme.Hom.image_le_opensRange _ _) _ ?_
    exact (mem_openSubmoduleCondition_image_iff (𝒰.f i) M (k i) V.unop
      ((k i).app V.unop t)).mpr ⟨t, rfl⟩

/-- Membership in the sectionwise range of a monomorphism of sheaves of modules is a
local condition: a section whose restrictions to a cover lie in the range lies in the
range. -/
lemma mem_range_app_of_locally {Y : Scheme.{u}} {A M : Y.Modules} (b : A ⟶ M)
    [Mono b] {ι : Type u} (Wl : ι → Y.Opens) (V : Y.Opens) (hV : V ≤ iSup Wl)
    (hl : ∀ l, Wl l ≤ V) (s : Γ(M, V))
    (h : ∀ l, ∃ t, (b.app (Wl l)).hom t =
      (M.presheaf.map (homOfLE (hl l)).op).hom s) :
    ∃ t, (b.app V).hom t = s := by
  choose tl htl using h
  have hnat : ∀ {V₁ V₂ : Y.Opens} (ρ : Opposite.op V₁ ⟶ Opposite.op V₂)
      (x : Γ(A, V₁)),
      ((b.app V₂).hom) (((A.presheaf.map ρ).hom) x) =
        ((M.presheaf.map ρ).hom) ((b.app V₁).hom x) :=
    fun ρ x ↦ CategoryTheory.congr_fun (b.mapPresheaf.naturality ρ) x
  have hfuse : ∀ (l l' : ι) (ρ : Opposite.op (Wl l) ⟶
      Opposite.op (Wl l ⊓ Wl l')),
      M.presheaf.map (homOfLE (hl l)).op ≫ M.presheaf.map ρ =
        M.presheaf.map (homOfLE ((inf_le_left.trans (hl l)) :
          (Wl l ⊓ Wl l' : _) ≤ V)).op := by
    intro l l' ρ
    rw [← Functor.map_comp]
    congr 1
  have hcompat : TopCat.Presheaf.IsCompatible A.presheaf Wl tl := by
    intro l l'
    apply app_injective_of_mono b
    beta_reduce
    rw [hnat _ (tl l), hnat _ (tl l'), htl l, htl l']
    refine (CategoryTheory.congr_fun (hfuse l l' _) s).trans ?_
    have hfuse' : ∀ (ρ : Opposite.op (Wl l') ⟶
        Opposite.op (Wl l ⊓ Wl l')),
        M.presheaf.map (homOfLE (hl l')).op ≫ M.presheaf.map ρ =
          M.presheaf.map (homOfLE ((inf_le_left.trans (hl l)) :
            (Wl l ⊓ Wl l' : _) ≤ V)).op := by
      intro ρ
      rw [← Functor.map_comp]
      congr 1
    exact (CategoryTheory.congr_fun (hfuse' _) s).symm
  obtain ⟨t, ht, -⟩ := (abSheaf A).existsUnique_gluing' Wl V
    (fun l ↦ homOfLE (hl l)) hV tl hcompat
  refine ⟨t, ?_⟩
  apply (abSheaf M).eq_of_locally_eq' Wl V (fun l ↦ homOfLE (hl l)) hV
  intro l
  rw [show (((abSheaf M).1.map (homOfLE (hl l)).op).hom) ((b.app V).hom t) =
      ((b.app (Wl l)).hom) (((A.presheaf.map (homOfLE (hl l)).op).hom) t) from
    (hnat _ t).symm, ht l, htl l]

/-- Sectionwise ranges of monomorphisms into a common ambient sheaf are determined by
their restrictions to an open cover. -/
lemma range_eq_of_openCover_restrict_range_eq (𝒰 : Scheme.OpenCover.{u} X)
    (M : X.Modules) (A B : X.Modules) (a : A ⟶ M) (b : B ⟶ M)
    [Mono a] [Mono b]
    (h : ∀ i, PresheafOfModules.Submodule.range
        ((restrictFunctor (𝒰.f i)).map a).val =
      PresheafOfModules.Submodule.range ((restrictFunctor (𝒰.f i)).map b).val) :
    PresheafOfModules.Submodule.range a.val =
      PresheafOfModules.Submodule.range b.val := by
  have key : ∀ (A' B' : X.Modules) (a' : A' ⟶ M) (b' : B' ⟶ M), Mono a' → Mono b' →
      (∀ i, PresheafOfModules.Submodule.range
          ((restrictFunctor (𝒰.f i)).map a').val ≤
        PresheafOfModules.Submodule.range ((restrictFunctor (𝒰.f i)).map b').val) →
      PresheafOfModules.Submodule.range a'.val ≤
        PresheafOfModules.Submodule.range b'.val := by
    intro A' B' a' b' ha' hb' hle W x hx
    obtain ⟨y, rfl⟩ := hx
    -- cover `W.unop` by the chart pieces
    refine mem_range_app_of_locally b'
      (fun i ↦ (𝒰.f i) ''ᵁ ((𝒰.f i) ⁻¹ᵁ W.unop)) W.unop
      (by
        intro p hp
        obtain ⟨i, ⟨q, hq⟩⟩ := 𝒰.exists_eq p
        refine TopologicalSpace.Opens.mem_iSup.mpr ⟨i, ⟨q, ?_, hq⟩⟩
        change (𝒰.f i) q ∈ Opposite.unop W
        rw [hq]
        exact hp)
      (fun i ↦ Scheme.Hom.image_preimage_le _ _) _ ?_
    intro i
    -- the restriction of `a'(y)` lies in the range of the restricted `a'`
    have hmem : ((M.presheaf.map
        (homOfLE (Scheme.Hom.image_preimage_le (𝒰.f i) W.unop)).op).hom)
          ((a'.val.app W).hom y) ∈
        (PresheafOfModules.Submodule.range
          ((restrictFunctor (𝒰.f i)).map a').val).obj
            (Opposite.op ((𝒰.f i) ⁻¹ᵁ W.unop)) := by
      refine ⟨(A'.presheaf.map
        (homOfLE (Scheme.Hom.image_preimage_le (𝒰.f i) W.unop)).op).hom y, ?_⟩
      exact CategoryTheory.congr_fun (a'.mapPresheaf.naturality
        (homOfLE (Scheme.Hom.image_preimage_le (𝒰.f i) W.unop)).op) y
    have hmem2 := (hle i) _ hmem
    obtain ⟨t, ht⟩ := hmem2
    exact ⟨t, ht⟩
  exact le_antisymm
    (key A B a b ‹_› ‹_› fun i ↦ (h i).le)
    (key B A b a ‹_› ‹_› fun i ↦ (h i).ge)

/-- The descended quotient's projection restricts to the local cokernel projection
through the comparison isomorphism. -/
@[reassoc (attr := simp)]
lemma restrict_openCoverQuotientMap_comp_iso (𝒰 : Scheme.OpenCover.{u} X)
    (M : X.Modules) {K : ∀ i, (𝒰.X i).Modules}
    (k : ∀ i, K i ⟶ (restrictFunctor (𝒰.f i)).obj M) [∀ i, Mono (k i)]
    (hcompat : OpenCoverSubmoduleCompatible 𝒰 M K k) (i : 𝒰.I₀) :
    (restrictFunctor (𝒰.f i)).map (openCoverQuotientMap 𝒰 M k) ≫
      (openCoverQuotientRestrictIso 𝒰 M k hcompat i).hom = cokernel.π (k i) := by
  rw [openCoverQuotientRestrictIso, Iso.trans_hom, ← Category.assoc,
    show (restrictFunctor (𝒰.f i)).map (openCoverQuotientMap 𝒰 M k) ≫
        (PreservesCokernel.iso (restrictFunctor (𝒰.f i))
          (openCoverKernelι 𝒰 M k)).hom =
      cokernel.π ((restrictFunctor (𝒰.f i)).map (openCoverKernelι 𝒰 M k)) from
      PreservesCokernel.π_iso_hom _ _,
    cokernel.mapIso_hom, cokernel.π_desc]
  rw [Iso.refl_hom, Category.id_comp]

section Local

variable {X U : Scheme.{u}}

/-- A sectionwise submodule of a sheaf of modules is **local** when membership can be
checked on any family of opens covering the ambient open.  Ranges of monomorphisms
from sheaves and open-immersion saturation conditions are local; local submodules
agreeing on affine opens agree. -/
def PresheafSubmoduleIsLocal {M : X.Modules} (N : M.val.Submodule) : Prop :=
  ∀ {ι : Type u} (Wl : ι → X.Opens) (W : X.Opens), W ≤ iSup Wl → ∀ hl : ∀ l, Wl l ≤ W,
    ∀ s : Γ(M, W), (∀ l, (M.presheaf.map (homOfLE (hl l)).op).hom s ∈
      N.obj (Opposite.op (Wl l))) → s ∈ N.obj (Opposite.op W)

/-- The sectionwise range of a monomorphism of sheaves of modules is a local
submodule. -/
lemma presheafSubmoduleIsLocal_range {A M : X.Modules} (b : A ⟶ M) [Mono b] :
    PresheafSubmoduleIsLocal (PresheafOfModules.Submodule.range b.val) := by
  intro ι Wl W hW hl s h
  rw [PresheafOfModules.Submodule.mem_range_iff]
  exact mem_range_app_of_locally b Wl W hW hl s fun l ↦
    (PresheafOfModules.Submodule.mem_range_iff b.val (Opposite.op (Wl l)) _).mp (h l)

/-- Two local sectionwise submodules of a sheaf of modules which agree on all affine
opens agree. -/
lemma presheafSubmodule_eq_of_isLocal_of_affine {M : X.Modules}
    {N N' : M.val.Submodule} (hN : PresheafSubmoduleIsLocal N)
    (hN' : PresheafSubmoduleIsLocal N')
    (haff : ∀ V : X.affineOpens, N.obj (Opposite.op V.1) = N'.obj (Opposite.op V.1)) :
    N = N' := by
  have key : ∀ (A B : M.val.Submodule), PresheafSubmoduleIsLocal B →
      (∀ V : X.affineOpens, A.obj (Opposite.op V.1) = B.obj (Opposite.op V.1)) →
      ∀ W : X.Opens, A.obj (Opposite.op W) ≤ B.obj (Opposite.op W) := by
    intro A B hB hab W s hs
    refine hB (ι := {V : X.affineOpens // V.1 ≤ W}) (fun V ↦ V.1.1) W ?_
      (fun V ↦ V.2) s ?_
    · intro p hp
      obtain ⟨V, hVaff, hxV, hVW⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
        X.isBasis_affineOpens) hp
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hVaff⟩, hVW⟩, hxV⟩
    · intro V
      rw [← hab V.1]
      exact A.map _ hs
  refine PresheafOfModules.Submodule.ext fun W ↦ ?_
  refine le_antisymm (key N N' hN' haff W.unop) (key N' N hN (fun V ↦ (haff V).symm) W.unop)

/-- Membership in the open-immersion saturation condition is a local property: the
witnesses glue in the (sheaf) source of the monomorphism. -/
lemma presheafSubmoduleIsLocal_openSubmoduleCondition (f : U ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) {K : U.Modules} (k : K ⟶ (restrictFunctor f).obj M) [Mono k] :
    PresheafSubmoduleIsLocal (openSubmoduleCondition f M k) := by
  intro ι Wl W hW hl s h
  rw [mem_openSubmoduleCondition_iff]
  have hpre : (f ⁻¹ᵁ W) ≤ iSup fun l ↦ f ⁻¹ᵁ Wl l := by
    intro p hp
    obtain ⟨l, hpl⟩ := TopologicalSpace.Opens.mem_iSup.mp (hW hp)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨l, hpl⟩
  refine mem_range_app_of_locally k (fun l ↦ f ⁻¹ᵁ Wl l) (f ⁻¹ᵁ W) hpre
    (fun l ↦ Scheme.Hom.preimage_mono f (hl l))
    ((M.presheaf.map (homOfLE (f.image_preimage_le W)).op).hom s) ?_
  intro l
  obtain ⟨t, ht⟩ := (mem_openSubmoduleCondition_iff f M k (Wl l) _).mp (h l)
  refine ⟨t, ht.trans ?_⟩
  have hfuse : M.presheaf.map (homOfLE (hl l)).op ≫
      M.presheaf.map (homOfLE (f.image_preimage_le (Wl l))).op =
      M.presheaf.map (homOfLE (f.image_preimage_le W)).op ≫
        ((restrictFunctor f).obj M).presheaf.map
          (homOfLE (Scheme.Hom.preimage_mono f (hl l))).op := by
    rw [restrict_map, ← Functor.map_comp, ← Functor.map_comp]
    congr 1
  exact CategoryTheory.congr_fun hfuse s

/-- The open-immersion saturation condition only depends on the sectionwise range of
the local kernel inclusion. -/
lemma openSubmoduleCondition_eq_of_range_eq (f : U ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) {K K' : U.Modules} (k : K ⟶ (restrictFunctor f).obj M)
    (k' : K' ⟶ (restrictFunctor f).obj M)
    (h : PresheafOfModules.Submodule.range k.val =
      PresheafOfModules.Submodule.range k'.val) :
    openSubmoduleCondition f M k = openSubmoduleCondition f M k' := by
  refine PresheafOfModules.Submodule.ext fun W ↦ ?_
  ext s
  constructor
  · rintro ⟨t, ht⟩
    exact (PresheafOfModules.Submodule.mem_range_iff k'.val
      (Opposite.op (f ⁻¹ᵁ W.unop)) _).mp (PresheafOfModules.Submodule.mem_of_eq h
        ((PresheafOfModules.Submodule.mem_range_iff k.val _ _).mpr ⟨t, ht⟩))
  · rintro ⟨t, ht⟩
    exact (PresheafOfModules.Submodule.mem_range_iff k.val
      (Opposite.op (f ⁻¹ᵁ W.unop)) _).mp (PresheafOfModules.Submodule.mem_of_eq h.symm
        ((PresheafOfModules.Submodule.mem_range_iff k'.val _ _).mpr ⟨t, ht⟩))

/-- A local sectionwise submodule of a sheaf of modules is itself a sheaf of modules:
compatible families of sections glue in the ambient sheaf, and the glued section
satisfies the (local) membership condition. -/
noncomputable def localSubmoduleSheaf {M : X.Modules} (N : M.val.Submodule)
    (hN : PresheafSubmoduleIsLocal N) : X.Modules where
  val := N.toPresheafOfModules
  isSheaf := by
    change TopCat.Presheaf.IsSheaf _
    rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
    intro ι W sf hcompat
    have hval : ∀ {V V' : (TopologicalSpace.Opens ↥X)ᵒᵖ} (ρ : V ⟶ V')
        (x : ToType (N.toPresheafOfModules.presheaf.obj V)),
        ((N.toPresheafOfModules.presheaf.map ρ) x).val = (M.presheaf.map ρ) x.val :=
      fun ρ x ↦ PresheafOfModules.Submodule.toPresheafOfModules_map_apply N ρ x
    let msf : ∀ i, ToType (M.presheaf.obj (Opposite.op (W i))) := fun i ↦ (sf i).1
    have hmcompat : TopCat.Presheaf.IsCompatible M.presheaf W msf := by
      intro i i'
      have h1 := congrArg Subtype.val (hcompat i i')
      exact (hval _ (sf i)).symm.trans (h1.trans (hval _ (sf i')))
    obtain ⟨s, hs, huniq⟩ := (abSheaf M).existsUnique_gluing W msf hmcompat
    have hmem : s ∈ N.obj (Opposite.op (iSup W)) := by
      refine hN W (iSup W) le_rfl (fun i ↦ le_iSup W i) s ?_
      intro i
      rw [show (M.presheaf.map (homOfLE (le_iSup W i)).op).hom s = msf i from hs i]
      exact (sf i).2
    refine ⟨⟨s, hmem⟩, ?_, ?_⟩
    · intro i
      exact Subtype.ext ((hval _ ⟨s, hmem⟩).trans (hs i))
    · intro y hy
      apply Subtype.ext
      exact huniq y.1 fun i ↦ (hval _ y).symm.trans (congrArg Subtype.val (hy i))

/-- The inclusion of a local sectionwise submodule into the ambient sheaf. -/
noncomputable def localSubmoduleSheafι {M : X.Modules} (N : M.val.Submodule)
    (hN : PresheafSubmoduleIsLocal N) : localSubmoduleSheaf N hN ⟶ M :=
  ⟨N.ι⟩

instance localSubmoduleSheafι_mono {M : X.Modules} (N : M.val.Submodule)
    (hN : PresheafSubmoduleIsLocal N) : Mono (localSubmoduleSheafι N hN) := by
  have hval : Mono (localSubmoduleSheafι N hN).val := inferInstanceAs (Mono N.ι)
  exact Functor.mono_of_mono_map (SheafOfModules.forget X.ringCatSheaf) hval

/-- The sectionwise range of the inclusion of a local submodule sheaf is the
submodule itself. -/
lemma range_localSubmoduleSheafι {M : X.Modules} (N : M.val.Submodule)
    (hN : PresheafSubmoduleIsLocal N) :
    PresheafOfModules.Submodule.range (localSubmoduleSheafι N hN).val = N := by
  refine PresheafOfModules.Submodule.ext fun W ↦ ?_
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    exact y.2
  · intro x hx
    exact ⟨⟨x, hx⟩, rfl⟩

end Local

end AlgebraicGeometry.Scheme.Modules

namespace CategoryTheory.Presieve

open CategoryTheory

/-- A functor admitting a monomorphism into a sheaf of types with local image is
itself a sheaf: it is isomorphic to its range subfunctor, which is a sheaf by the
locality of the image. -/
theorem isSheaf_of_mono_of_range_local {C : Type*} [Category C]
    {J : GrothendieckTopology C} {F K : Cᵒᵖ ⥤ Type _} (η : F ⟶ K) [Mono η]
    (hK : Presieve.IsSheaf J K)
    (hlocal : ∀ (T : Cᵒᵖ) (s : K.obj T),
      (Subfunctor.range η).sieveOfSection s ∈ J (Opposite.unop T) →
        s ∈ (Subfunctor.range η).obj T) :
    Presieve.IsSheaf J F := by
  have hrange : Presieve.IsSheaf J (Subfunctor.range η).toFunctor :=
    ((Subfunctor.range η).isSheaf_iff hK).mpr hlocal
  have hm : Mono (Subfunctor.toRange η) := by
    have hfac : Subfunctor.toRange η ≫ (Subfunctor.range η).ι = η :=
      Subfunctor.toRange_ι η
    exact mono_of_mono_fac hfac
  have : IsIso (Subfunctor.toRange η) := isIso_of_mono_of_epi _
  exact Presieve.isSheaf_iso J (asIso (Subfunctor.toRange η)).symm hrange

end CategoryTheory.Presieve
