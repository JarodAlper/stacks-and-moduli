module

public import StacksAndModuli.API.ProjectiveSpaceZeroQuotRank
public import StacksAndModuli.API.ProjectiveSpaceZeroGrassmannianQuot
public import StacksAndModuli.API.ProjectiveSpaceZeroQuotProjectivity

/-!
# The Quot–Grassmannian isomorphism on projective zero-space

Supporting API with no Stacks Project counterpart.

On relative projective zero-space the fixed-polynomial Quot functor of the finite
twisted-free sheaf is naturally isomorphic to the relative Grassmannian of the free
rank-`r` sheaf: `Quot^{C q}(𝒪(-l)^{⊕r}/ℙ⁰ₛ/S) ≅ Gr(q, 𝒪ₛ^{⊕r})`.  The natural
transformation is the Grassmannian-to-Quot construction of
`API/ProjectiveSpaceZeroGrassmannianQuot.lean`; each component is bijective because
the first pullback projection of `T ×ₛ ℙ⁰ₛ` is an isomorphism, so pulling back along
it is an equivalence of module categories with structural unit and counit
(`Modules.pullbackInverseUnit`/`Counit`), and injectivity and surjectivity follow
from naturality together with the triangle identity
(`Modules.pullbackInverse_triangle`) and the unconditional rank theorem
(`isProjectiveOfRank_zeroNormalizedSheaf`).

Feeding the isomorphism into the twisted-free Quot projectivity endgame yields an
unconditional H-projective representative for the fixed-polynomial twisted-free Quot
functor on relative `ℙ⁰`.

Main declarations:
- `Modules.zeroGrassmannianToQuotP`, `Modules.zeroQuotPGrassmannianIso`;
- `Scheme.exists_quotFunctorP_zero_representableBy_isHProjective`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {S : Scheme.{u}} {l : ℤ} {r q : ℕ}

section InverseData

variable (T : Over S)

/-- In relative dimension zero, the first projection of the fibre product with
projective space is an isomorphism. -/
lemma zeroPullbackFst_isIso :
    IsIso (Limits.pullback.fst T.hom (Scheme.projectiveSpaceOverπ 0 S)) := by
  haveI : IsIso (Scheme.projectiveSpaceOverπ 0 S) := by
    rw [← Scheme.projectiveSpaceOverZeroIso_hom S]
    infer_instance
  infer_instance

/-- The explicit two-sided inverse of the first projection in relative dimension
zero, through the identifications `T ≅ ℙ⁰_T ≅ T ×ₛ ℙ⁰ₛ`. -/
def zeroFstSection :
    T.left ⟶ Limits.pullback T.hom (Scheme.projectiveSpaceOverπ 0 S) :=
  (Scheme.projectiveSpaceOverZeroIso T.left).inv ≫
    (Scheme.projectiveSpaceOverBaseChangeIso 0 T.hom).inv

lemma zeroFstSection_fst :
    zeroFstSection T ≫
      Limits.pullback.fst T.hom (Scheme.projectiveSpaceOverπ 0 S) = 𝟙 T.left := by
  rw [zeroFstSection, Category.assoc,
    Scheme.projectiveSpaceOverBaseChangeIso_inv_fst 0 T.hom,
    ← Scheme.projectiveSpaceOverZeroIso_hom T.left, Iso.inv_hom_id]

lemma fst_zeroFstSection :
    Limits.pullback.fst T.hom (Scheme.projectiveSpaceOverπ 0 S) ≫
      zeroFstSection T = 𝟙 _ := by
  haveI := zeroPullbackFst_isIso T
  rw [show zeroFstSection T =
      inv (Limits.pullback.fst T.hom (Scheme.projectiveSpaceOverπ 0 S)) from
    IsIso.eq_inv_of_inv_hom_id (zeroFstSection_fst T), IsIso.hom_inv_id]

end InverseData

namespace PullbackQuotient

variable {T : Over S}

/-- The Grassmannian-to-Quot construction reflects the equivalence relation: two
vector-bundle quotients with equivalent associated Quot presentations are
equivalent. -/
theorem toQuotientPullbackDataZero_reflects
    {x y : PullbackQuotient q (zeroFreeAmbient S r) T}
    (h : (QuotientPullbackData.setoid
      (Scheme.projectiveSpaceOverTwistedFree 0 S l r)
      (Scheme.projectiveSpaceOverπ 0 S) T).r
        (x.toQuotientPullbackDataZero (l := l))
        (y.toQuotientPullbackDataZero (l := l))) :
    (PullbackQuotient.setoid q (zeroFreeAmbient S r) T).r x y := by
  obtain ⟨e, he⟩ := h
  dsimp only [PullbackQuotient.toQuotientPullbackDataZero] at e he
  have he' : (Modules.pullback
      (Limits.pullback.fst T.hom (Scheme.projectiveSpaceOverπ 0 S))).map x.π ≫
        e.hom =
      (Modules.pullback
        (Limits.pullback.fst T.hom (Scheme.projectiveSpaceOverπ 0 S))).map y.π := by
    have h0 := he
    rw [Category.assoc] at h0
    exact (cancel_epi _).mp h0
  refine ⟨(pullbackInverseUnit (zeroFstSection_fst T)).app x.Q ≪≫
    (Modules.pullback (zeroFstSection T)).mapIso e ≪≫
    ((pullbackInverseUnit (zeroFstSection_fst T)).app y.Q).symm, ?_⟩
  have hn1 := (pullbackInverseUnit (zeroFstSection_fst T)).hom.naturality x.π
  have hn2 := (pullbackInverseUnit (zeroFstSection_fst T)).inv.naturality y.π
  simp only [Functor.id_map, Functor.comp_map] at hn1 hn2
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv,
    Functor.mapIso_hom]
  calc x.π ≫
      (pullbackInverseUnit (zeroFstSection_fst T)).hom.app x.Q ≫
      (Modules.pullback (zeroFstSection T)).map e.hom ≫
      (pullbackInverseUnit (zeroFstSection_fst T)).inv.app y.Q
      = ((pullbackInverseUnit (zeroFstSection_fst T)).hom.app
            ((Modules.pullback T.hom).obj (zeroFreeAmbient S r)) ≫
          (Modules.pullback (zeroFstSection T)).map
            ((Modules.pullback (Limits.pullback.fst T.hom
              (Scheme.projectiveSpaceOverπ 0 S))).map x.π)) ≫
        (Modules.pullback (zeroFstSection T)).map e.hom ≫
        (pullbackInverseUnit (zeroFstSection_fst T)).inv.app y.Q := by
        rw [← Category.assoc, hn1]
    _ = (pullbackInverseUnit (zeroFstSection_fst T)).hom.app
            ((Modules.pullback T.hom).obj (zeroFreeAmbient S r)) ≫
        (Modules.pullback (zeroFstSection T)).map
          ((Modules.pullback (Limits.pullback.fst T.hom
            (Scheme.projectiveSpaceOverπ 0 S))).map x.π ≫ e.hom) ≫
        (pullbackInverseUnit (zeroFstSection_fst T)).inv.app y.Q := by
        simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    _ = (pullbackInverseUnit (zeroFstSection_fst T)).hom.app
            ((Modules.pullback T.hom).obj (zeroFreeAmbient S r)) ≫
        (Modules.pullback (zeroFstSection T)).map
          ((Modules.pullback (Limits.pullback.fst T.hom
            (Scheme.projectiveSpaceOverπ 0 S))).map y.π) ≫
        (pullbackInverseUnit (zeroFstSection_fst T)).inv.app y.Q := by
        rw [he']
    _ = (pullbackInverseUnit (zeroFstSection_fst T)).hom.app
            ((Modules.pullback T.hom).obj (zeroFreeAmbient S r)) ≫
        (pullbackInverseUnit (zeroFstSection_fst T)).inv.app
            ((Modules.pullback T.hom).obj (zeroFreeAmbient S r)) ≫ y.π := by
        rw [hn2]
    _ = y.π := by
        rw [Iso.hom_inv_id_app_assoc]

/-- Preimage of a fixed-polynomial Quot presentation under the
Grassmannian-to-Quot construction: pull the quotient sheaf back along the inverse
of the first projection. -/
noncomputable def ofQuotientPullbackDataZero
    (a : QuotientPullbackData
      (Scheme.projectiveSpaceOverTwistedFree 0 S l r)
      (Scheme.projectiveSpaceOverπ 0 S) T)
    (hP : a.HasFiberwiseHilbertPolynomial (Polynomial.C (q : ℚ))) :
    PullbackQuotient q (zeroFreeAmbient S r) T where
  Q := (Modules.pullback (zeroFstSection T)).obj a.Q
  isQuasicoherent := by
    haveI := a.isQuasicoherent
    infer_instance
  isProjectiveOfRank := by
    have h1 := a.isProjectiveOfRank_zeroNormalizedSheaf q hP
    exact IsProjectiveOfRank.of_iso
      ((Modules.pullbackComp
        (Scheme.projectiveSpaceOverZeroIso T.left).inv
        (Scheme.projectiveSpaceOverBaseChangeIso 0 T.hom).inv).app a.Q) h1
  π := (pullbackInverseUnit (zeroFstSection_fst T)).hom.app
      ((Modules.pullback T.hom).obj (zeroFreeAmbient S r)) ≫
    (Modules.pullback (zeroFstSection T)).map
      ((toQuotientPullbackDataZeroAmbientIso
        (S := S) (T := T) (l := l) (r := r)).inv ≫ a.π)
  epi := by
    haveI : Epi a.π := a.epi
    haveI : Epi ((toQuotientPullbackDataZeroAmbientIso
        (S := S) (T := T) (l := l) (r := r)).inv ≫ a.π) := epi_comp _ _
    haveI : Epi ((Modules.pullback (zeroFstSection T)).map
        ((toQuotientPullbackDataZeroAmbientIso
          (S := S) (T := T) (l := l) (r := r)).inv ≫ a.π)) := inferInstance
    exact epi_comp _ _

/-- The preimage construction is a section of the Grassmannian-to-Quot map: its
associated Quot presentation is equivalent to the original one. -/
theorem toQuotientPullbackDataZero_ofQuotientPullbackDataZero
    (a : QuotientPullbackData
      (Scheme.projectiveSpaceOverTwistedFree 0 S l r)
      (Scheme.projectiveSpaceOverπ 0 S) T)
    (hP : a.HasFiberwiseHilbertPolynomial (Polynomial.C (q : ℚ))) :
    (QuotientPullbackData.setoid
      (Scheme.projectiveSpaceOverTwistedFree 0 S l r)
      (Scheme.projectiveSpaceOverπ 0 S) T).r
        ((ofQuotientPullbackDataZero a hP).toQuotientPullbackDataZero (l := l)) a := by
  refine ⟨(pullbackInverseCounit (fst_zeroFstSection T)).app a.Q, ?_⟩
  dsimp only [PullbackQuotient.toQuotientPullbackDataZero,
    ofQuotientPullbackDataZero]
  have hn1 := (pullbackInverseCounit (fst_zeroFstSection T)).hom.naturality a.π
  have hn2 := reassoc_of%
    ((pullbackInverseCounit (fst_zeroFstSection T)).hom.naturality
      (toQuotientPullbackDataZeroAmbientIso
        (S := S) (T := T) (l := l) (r := r)).inv)
  have htri := reassoc_of%
    (pullbackInverse_triangle (zeroFstSection_fst T) (fst_zeroFstSection T)
      ((Modules.pullback T.hom).obj (zeroFreeAmbient S r)))
  simp only [Functor.id_map, Functor.comp_map] at hn1 hn2
  simp only [Iso.app_hom, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [hn1, hn2, htri, Iso.hom_inv_id_assoc]

end PullbackQuotient

/-- The Grassmannian-to-Quot natural transformation on relative projective
zero-space, for the constant Hilbert polynomial `C q`. -/
noncomputable def zeroGrassmannianToQuotP (S : Scheme.{u}) (l : ℤ) (r q : ℕ) :
    Modules.grassmannianOverFunctor q
        (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin r))) ⟶
      Scheme.quotFunctorP (Scheme.projectiveSpaceOverTwistedFree 0 S l r)
        (Polynomial.C (q : ℚ)) where
  app T := ↾fun z ↦
    ⟨Quotient.map (fun x ↦ x.toQuotientPullbackDataZero (l := l))
      (fun _ _ h ↦ PullbackQuotient.toQuotientPullbackDataZero_r (l := l) h) z, by
      obtain ⟨x, rfl⟩ := Quotient.exists_rep z
      exact ⟨x.toQuotientPullbackDataZero (l := l), rfl,
        x.toQuotientPullbackDataZero_hasFiberwiseHilbertPolynomial (l := l)⟩⟩
  naturality T T' g := by
    refine ConcreteCategory.hom_ext _ _ fun z ↦ ?_
    obtain ⟨x, rfl⟩ := Quotient.exists_rep z
    refine Subtype.ext ?_
    change (Quotient.mk _
        ((PullbackQuotient.pullback g.unop x).toQuotientPullbackDataZero
          (l := l)) :
      Quotient (QuotientPullbackData.setoid _ _ _)) =
      Quotient.mk _
        (QuotientPullbackData.pullback g.unop
          (x.toQuotientPullbackDataZero (l := l)))
    exact Quotient.sound
      (PullbackQuotient.toQuotientPullbackDataZero_pullback_r
        (l := l) g.unop x)

/-- Each component of the Grassmannian-to-Quot transformation is bijective. -/
theorem zeroGrassmannianToQuotP_app_bijective (T : (Over S)ᵒᵖ) :
    Function.Bijective ((zeroGrassmannianToQuotP S l r q).app T) := by
  constructor
  · intro z w h
    obtain ⟨x, rfl⟩ := Quotient.exists_rep z
    obtain ⟨y, rfl⟩ := Quotient.exists_rep w
    have h1 : (Quotient.mk _ (x.toQuotientPullbackDataZero (l := l)) :
        Quotient (QuotientPullbackData.setoid _ _ _)) =
        Quotient.mk _ (y.toQuotientPullbackDataZero (l := l)) :=
      congrArg Subtype.val h
    exact Quotient.sound
      (PullbackQuotient.toQuotientPullbackDataZero_reflects (l := l)
        (Quotient.exact h1))
  · rintro ⟨z, a, ha, hPa⟩
    refine ⟨Quotient.mk _
      (PullbackQuotient.ofQuotientPullbackDataZero (l := l) a hPa), ?_⟩
    refine Subtype.ext ?_
    change Quotient.mk _
      ((PullbackQuotient.ofQuotientPullbackDataZero (l := l)
        a hPa).toQuotientPullbackDataZero (l := l)) = z
    rw [← ha]
    exact Quotient.sound
      (PullbackQuotient.toQuotientPullbackDataZero_ofQuotientPullbackDataZero
        a hPa)

/-- **The Quot–Grassmannian isomorphism on projective zero-space**: the
fixed-constant-polynomial Quot functor of the finite twisted-free sheaf is the
relative Grassmannian of the free rank-`r` sheaf. -/
noncomputable def zeroQuotPGrassmannianIso (S : Scheme.{u}) (l : ℤ) (r q : ℕ) :
    Scheme.quotFunctorP (Scheme.projectiveSpaceOverTwistedFree 0 S l r)
        (Polynomial.C (q : ℚ)) ≅
      Modules.grassmannianOverFunctor q
        (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin r))) := by
  haveI : ∀ T, IsIso ((zeroGrassmannianToQuotP S l r q).app T) := fun T ↦
    (CategoryTheory.isIso_iff_bijective _).mpr
      (zeroGrassmannianToQuotP_app_bijective T)
  haveI : IsIso (zeroGrassmannianToQuotP S l r q) :=
    NatIso.isIso_of_isIso_app _
  exact (asIso (zeroGrassmannianToQuotP S l r q)).symm

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

/-- Special-case API theorem for Theorem 2.1.3 (relative dimension zero):
for every scheme `S`, twist `l`, rank `r` and polynomial `P ∈ ℚ[z]`, the
fixed-polynomial Quot functor `Quot^P(𝒪(-l)^{⊕r}/ℙ⁰ₛ/S)` is representable by an
H-projective scheme over `S`.  No noetherian hypothesis is needed. -/
theorem exists_quotFunctorP_zero_representableBy_isHProjective
    (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ) :
    ∃ G : Over S,
      Nonempty ((quotFunctorP
        (projectiveSpaceOverTwistedFree 0 S l r) P).RepresentableBy G) ∧
      IsHProjective G.hom :=
  exists_quotFunctorP_zero_representableBy_isHProjective_of_grassmannianIso
    S l r P (fun q ↦ Modules.zeroQuotPGrassmannianIso S l r q)

end AlgebraicGeometry.Scheme

end
