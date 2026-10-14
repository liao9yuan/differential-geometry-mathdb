import Submission.DifferentialGeometry.Topology.SimplicialComplex.MaximalFace
import Submission.DifferentialGeometry.Topology.SimplicialComplex.OrderedMaps
import Submission.DifferentialGeometry.Topology.SimplicialSet.MaximalCell

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Simplicial _root_.Opposite

namespace DifferentialGeometry.Topology.SimplicialComplex
universe u
variable {ι : Type u} [LinearOrder ι]


@[reassoc (attr := simp)]
theorem orderedInclusion_ι {K L : PreAbstractSimplicialComplex ι} (h : K ≤ L) :
    orderedInclusion h ≫ (orderedNerveSubcomplex L).ι =
      (orderedNerveSubcomplex K).ι := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.orderedInclusion_ι then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.orderedInclusion_ι"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.orderedInclusion_ι ``Submission.DifferentialGeometry.Topology.SimplicialComplex.orderedInclusion_ι

variable (K : PreAbstractSimplicialComplex ι) (s : Finset ι) (hs : s ∈ K)
  {n : ℕ} (hn : s.card = n + 1)

theorem orderedFace_subcomplex_le_iff {m : SimplexCategoryᵒᵖ}
    (x : (orderedSimplicialSet K).obj m) :
    Subfunctor.ofSection (orderedSimplexOfFace K s hs hn).val ≤ Subfunctor.ofSection x ↔
      s ⊆ Finset.univ.image x.val.obj := by
  rw [Subfunctor.ofSection_le_iff, Subfunctor.ofSection_obj]
  constructor
  · rintro ⟨f, hf⟩ a ha
    have ha' : a ∈ Finset.univ.image (orderedSimplexOfFace K s hs hn).val.val.obj := by
      simpa only [vertices_orderedSimplexOfFace] using ha
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ha'
    refine Finset.mem_image.mpr ⟨f.unop.toOrderHom i, Finset.mem_univ _, ?_⟩
    have hv := congrArg (fun y ↦ y.val.obj i) hf
    exact hv.trans hi
  · intro hsub
    have hpre (i : Fin (n + 1)) : ∃ j : Fin (m.unop.len + 1),
        x.val.obj j = (s.orderEmbOfFin hn) i := by
      have hi : (s.orderEmbOfFin hn) i ∈ s := by
        have hi' : (s.orderEmbOfFin hn) i ∈ Finset.univ.image (s.orderEmbOfFin hn) :=
          Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
        simpa only [Finset.image_orderEmbOfFin_univ] using hi'
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (hsub hi)
      exact ⟨j, hj⟩
    let f : Fin (n + 1) → Fin (m.unop.len + 1) := fun i ↦ (hpre i).choose
    have hf (i : Fin (n + 1)) : x.val.obj (f i) = (s.orderEmbOfFin hn) i :=
      (hpre i).choose_spec
    have hfmono : StrictMono f := by
      intro i j hij
      by_contra h
      have hji := x.val.monotone (le_of_not_gt h)
      rw [hf, hf] at hji
      exact ((s.orderEmbOfFin hn).strictMono hij).not_ge hji
    let φ : ⦋n⦌ ⟶ m.unop := SimplexCategory.Hom.mk ⟨f, hfmono.monotone⟩
    refine ⟨φ.op, ?_⟩
    apply Subtype.ext
    apply nerve.ext_of_isThin
    funext i
    exact hf i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.orderedFace_subcomplex_le_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.orderedFace_subcomplex_le_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.orderedFace_subcomplex_le_iff ``Submission.DifferentialGeometry.Topology.SimplicialComplex.orderedFace_subcomplex_le_iff

def orderedFaceN : (orderedSimplicialSet K).N :=
  _root_.SSet.N.mk (orderedSimplexOfFace K s hs hn).val (orderedSimplexOfFace K s hs hn).prop

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.orderedFaceN then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.orderedFaceN"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.orderedFaceN ``Submission.DifferentialGeometry.Topology.SimplicialComplex.orderedFaceN


@[simp]
theorem orderedFaceN_dim : (orderedFaceN K s hs hn).dim = n := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.orderedFaceN_dim then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.orderedFaceN_dim"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.orderedFaceN_dim ``Submission.DifferentialGeometry.Topology.SimplicialComplex.orderedFaceN_dim

theorem orderedFaceN_le_iff (t : (orderedSimplicialSet K).N) :
    orderedFaceN K s hs hn ≤ t ↔ s ⊆ Finset.univ.image t.simplex.val.obj :=
  orderedFace_subcomplex_le_iff K s hs hn t.simplex

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.orderedFaceN_le_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.orderedFaceN_le_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.orderedFaceN_le_iff ``Submission.DifferentialGeometry.Topology.SimplicialComplex.orderedFaceN_le_iff


theorem isMax_orderedFaceN (hmax : IsMax (⟨s, hs⟩ : K.faces)) :
    IsMax (orderedFaceN K s hs hn) := by
  intro t hst
  have hst' := (orderedFaceN_le_iff K s hs hn t).mp hst
  have hts' : Finset.univ.image t.simplex.val.obj ⊆ s :=
    hmax (show (⟨s, hs⟩ : K.faces) ≤ ⟨_, t.simplex.prop⟩ from hst')
  let a : (orderedSimplicialSet K).nonDegenerate t.dim := ⟨t.simplex, t.nonDegenerate⟩
  have he := congrArg Subtype.val ((orderedNondegenerateFaceEquiv K t.dim).left_inv a)
  change (orderedSimplexOfFace K (Finset.univ.image t.simplex.val.obj) t.simplex.prop
    (card_vertices_nondegenerate K a)).val = t.simplex at he
  change Subfunctor.ofSection t.simplex ≤
    Subfunctor.ofSection (orderedSimplexOfFace K s hs hn).val
  rw [← he]
  apply (orderedFace_subcomplex_le_iff K _ t.simplex.prop
    (card_vertices_nondegenerate K a) (orderedSimplexOfFace K s hs hn).val).mpr
  simpa only [vertices_orderedSimplexOfFace] using hts'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.isMax_orderedFaceN then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.isMax_orderedFaceN"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.isMax_orderedFaceN ``Submission.DifferentialGeometry.Topology.SimplicialComplex.isMax_orderedFaceN

theorem mem_orderedFaceN_costar_iff {m : SimplexCategoryᵒᵖ}
    (x : (orderedSimplicialSet K).obj m) :
    x ∈ (DifferentialGeometry.SSet.costar (orderedFaceN K s hs hn)).obj m ↔
      ¬s ⊆ Finset.univ.image x.val.obj :=
  not_congr (orderedFace_subcomplex_le_iff K s hs hn x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.mem_orderedFaceN_costar_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.mem_orderedFaceN_costar_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.mem_orderedFaceN_costar_iff ``Submission.DifferentialGeometry.Topology.SimplicialComplex.mem_orderedFaceN_costar_iff

def orderedFaceCostarIso :
    orderedSimplicialSet (faceCostar K s) ≅ DifferentialGeometry.SSet.costar (orderedFaceN K s hs hn) :=
  NatIso.ofComponents (fun _ ↦ Equiv.toIso {
    toFun := fun x ↦ ⟨⟨x.val, x.prop.1⟩,
      (mem_orderedFaceN_costar_iff K s hs hn _).mpr x.prop.2⟩
    invFun := fun x ↦ ⟨x.val.val, x.val.prop,
      (mem_orderedFaceN_costar_iff K s hs hn x.val).mp x.prop⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl }) (fun _ ↦ rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.orderedFaceCostarIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.orderedFaceCostarIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.orderedFaceCostarIso ``Submission.DifferentialGeometry.Topology.SimplicialComplex.orderedFaceCostarIso


@[reassoc (attr := simp)]
theorem orderedFaceCostarIso_hom_inclusion :
    (orderedFaceCostarIso K s hs hn).hom ≫ (DifferentialGeometry.SSet.costar (orderedFaceN K s hs hn)).ι =
      orderedInclusion (faceCostar_le K s) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.orderedFaceCostarIso_hom_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.orderedFaceCostarIso_hom_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.orderedFaceCostarIso_hom_inclusion ``Submission.DifferentialGeometry.Topology.SimplicialComplex.orderedFaceCostarIso_hom_inclusion

def orderedFaceCellMap : (Δ[n] : _root_.SSet.{u}) ⟶ orderedSimplicialSet K :=
  DifferentialGeometry.SSet.nondegenerateCellMap (orderedFaceN K s hs hn)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.orderedFaceCellMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.orderedFaceCellMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.orderedFaceCellMap ``Submission.DifferentialGeometry.Topology.SimplicialComplex.orderedFaceCellMap

theorem orderedFaceCellMap_app {m : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) :
    ((orderedFaceCellMap K s hs hn).app (_root_.Opposite.op ⦋m⦌)
      (_root_.SSet.stdSimplex.objEquiv.symm f)).val.obj =
        fun i ↦ (s.orderEmbOfFin hn) (f.toOrderHom i) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.orderedFaceCellMap_app then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.orderedFaceCellMap_app"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.orderedFaceCellMap_app ``Submission.DifferentialGeometry.Topology.SimplicialComplex.orderedFaceCellMap_app


def orderedFaceAttachingMap : (_root_.SSet.boundary n : _root_.SSet.{u}) ⟶
    orderedSimplicialSet (faceCostar K s) :=
  DifferentialGeometry.SSet.costarAttachingMap (orderedFaceN K s hs hn) ≫ (orderedFaceCostarIso K s hs hn).inv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.orderedFaceAttachingMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.orderedFaceAttachingMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.orderedFaceAttachingMap ``Submission.DifferentialGeometry.Topology.SimplicialComplex.orderedFaceAttachingMap

@[reassoc (attr := simp)]
theorem orderedFaceAttachingMap_inclusion :
    orderedFaceAttachingMap K s hs hn ≫ orderedInclusion (faceCostar_le K s) =
      (_root_.SSet.boundary n).ι ≫ orderedFaceCellMap K s hs hn := by
  ext x
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.orderedFaceAttachingMap_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.orderedFaceAttachingMap_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.orderedFaceAttachingMap_inclusion ``Submission.DifferentialGeometry.Topology.SimplicialComplex.orderedFaceAttachingMap_inclusion

theorem orderedFaceAttachment_isPushout (hmax : IsMax (⟨s, hs⟩ : K.faces)) :
    _root_.CategoryTheory.IsPushout (_root_.SSet.boundary n).ι (orderedFaceAttachingMap K s hs hn)
      (orderedFaceCellMap K s hs hn) (orderedInclusion (faceCostar_le K s)) := by
  apply (DifferentialGeometry.SSet.costar_cell_isPushout (orderedFaceN K s hs hn)
    (isMax_orderedFaceN K s hs hn hmax)).of_iso'
    (Iso.refl _) (Iso.refl _) (orderedFaceCostarIso K s hs hn) (Iso.refl _)
  · change (𝟙 (_root_.SSet.boundary n : _root_.SSet)) ≫ (_root_.SSet.boundary n).ι =
      (_root_.SSet.boundary n).ι ≫ (𝟙 (Δ[n] : _root_.SSet))
    simp
  · ext x
    rfl
  · ext x
    rfl
  · simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.orderedFaceAttachment_isPushout then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.orderedFaceAttachment_isPushout"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.orderedFaceAttachment_isPushout ``Submission.DifferentialGeometry.Topology.SimplicialComplex.orderedFaceAttachment_isPushout

end DifferentialGeometry.Topology.SimplicialComplex
