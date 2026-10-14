import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapLocalOrientations
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapSmoothOverlap
import Submission.DifferentialGeometry.Topology.Manifold.OpenSubtypeDifferential

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Topology.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.E3 target :: scope.openDecls } }
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.IC target :: scope.openDecls } }
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ} {L : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph IC I ∞ (f i))
local notation "OverlapOrientationQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

def finiteCapOldOverlapOpens (b : ι × Bool) : _root_.TopologicalSpace.Opens OverlapOrientationQ :=
  finiteCapNeighborhoodOpens hL hδ f hf hdisj b ⊓ finiteCoreInteriorOpens hL hδ f hf hdisj

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOldOverlapOpens then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOldOverlapOpens"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOldOverlapOpens ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOldOverlapOpens

private theorem overlap_radial_mem (b : ι × Bool)
    (p : finiteCapOldOverlapOpens hL hδ f hf hdisj b) :
    let : ChartedSpace E3 OverlapOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    finiteCapRadialCoordinateMap I hdim hL hδ f hf hdisj hs b ⟨p.val, p.property.1⟩ ∈
      cuttingAnnulus L (precision b.1) := by
  let : ChartedSpace E3 OverlapOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  have hp : p.val ∈ (finiteCapOpenChart hL hδ f hf hdisj b).source := by
    rw [finiteCapOpenChart_source]
    exact p.property.1
  have hx : finiteCapOpenChart hL hδ f hf hdisj b p.val ∈
      finiteCapOpenChart hL hδ f hf hdisj b ''
        ((finiteCapOpenChart hL hδ f hf hdisj b).source ∩
          finiteCoreInterior hL hδ f (fun i => (hf i).injective) hdisj) :=
    ⟨p.val, ⟨hp, p.property.2⟩, rfl⟩
  rw [finiteCapOpenChart_interior_overlap_image hL hδ f hf hdisj b] at hx
  rw [finiteCapRadialCoordinateMap_eq_openChart]
  exact hx

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.overlap_radial_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.overlap_radial_mem target :: scope.openDecls } }

def finiteCapOldOverlapRadialMap (b : ι × Bool) :
    let : ChartedSpace E3 OverlapOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    finiteCapOldOverlapOpens hL hδ f hf hdisj b → cuttingAnnulus L (precision b.1) := by
  let : ChartedSpace E3 OverlapOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  exact fun p => ⟨finiteCapRadialCoordinateMap I hdim hL hδ f hf hdisj hs b ⟨p.val, p.property.1⟩,
    overlap_radial_mem I hdim hL hδ f hf hdisj hs b p⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOldOverlapRadialMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOldOverlapRadialMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOldOverlapRadialMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOldOverlapRadialMap

theorem finiteCapOldOverlapRadialMap_contMDiff (b : ι × Bool) :
    let : ChartedSpace E3 OverlapOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    ContMDiff (𝓡 3) (𝓡 3) ∞ (finiteCapOldOverlapRadialMap I hdim hL hδ f hf hdisj hs b) := by
  let : ChartedSpace E3 OverlapOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  apply (ContMDiff.subtypeVal_comp_iff (cuttingAnnulus L (precision b.1))
    (finiteCapOldOverlapRadialMap I hdim hL hδ f hf hdisj hs b)).mp
  exact (finiteCapRadialCoordinateMap_contMDiff I hdim hL hδ f hf hdisj hs b).comp
    (contMDiff_inclusion (I := 𝓡 3)
      (show finiteCapOldOverlapOpens hL hδ f hf hdisj b ≤ finiteCapNeighborhoodOpens hL hδ f hf hdisj b from inf_le_left))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOldOverlapRadialMap_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOldOverlapRadialMap_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOldOverlapRadialMap_contMDiff ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOldOverlapRadialMap_contMDiff

theorem finiteCapOldOverlapRadialMap_mfderiv_bijective (b : ι × Bool)
    (p : finiteCapOldOverlapOpens hL hδ f hf hdisj b) :
    let : ChartedSpace E3 OverlapOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    Bijective (mfderiv (𝓡 3) (𝓡 3) (finiteCapOldOverlapRadialMap I hdim hL hδ f hf hdisj hs b) p) := by
  let : ChartedSpace E3 OverlapOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let A := cuttingAnnulus L (precision b.1)
  let F := finiteCapOldOverlapRadialMap I hdim hL hδ f hf hdisj hs b
  have hinc : finiteCapOldOverlapOpens hL hδ f hf hdisj b ≤ finiteCapNeighborhoodOpens hL hδ f hf hdisj b := inf_le_left
  let j := Opens.inclusion hinc
  have hj : ContMDiff (𝓡 3) (𝓡 3) ∞ j := contMDiff_inclusion hinc
  have hbj : ∀ q, _root_.Function.Bijective (mfderiv (𝓡 3) (𝓡 3) j q) := by
    intro q
    rw [DifferentialGeometry.mfderiv_opens_incl]
    exact Function.bijective_id
  have hb : _root_.Function.Bijective (mfderiv (𝓡 3) (𝓡 3) ((Subtype.val : A → E3) ∘ F) p) :=
    bijective_mfderiv_comp (𝓡 3) (𝓡 3) (𝓡 3) j
      (finiteCapRadialCoordinateMap I hdim hL hδ f hf hdisj hs b) hj
      (finiteCapRadialCoordinateMap_contMDiff I hdim hL hδ f hf hdisj hs b) hbj
      (finiteCapRadialCoordinateMap_mfderiv_bijective I hdim hL hδ f hf hdisj hs b) p
  rw [mfderiv_comp_open_val (𝓡 3) (𝓡 3) A F
    (finiteCapOldOverlapRadialMap_contMDiff I hdim hL hδ f hf hdisj hs b) p] at hb
  exact hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOldOverlapRadialMap_mfderiv_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOldOverlapRadialMap_mfderiv_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOldOverlapRadialMap_mfderiv_bijective ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOldOverlapRadialMap_mfderiv_bijective

theorem finiteCapOldOverlap_old_coordinate (b : ι × Bool) :
    let : ChartedSpace E3 OverlapOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    (finiteOldAmbientCoordinateMap I hdim hL hδ f hf hdisj hs ∘
      Opens.inclusion (show finiteCapOldOverlapOpens hL hδ f hf hdisj b ≤
        finiteCoreInteriorOpens hL hδ f hf hdisj from inf_le_right)) =
      (f b.1 ∘ cuttingAnnulusCylinderMap hL (hδ b.1) b.2) ∘
        finiteCapOldOverlapRadialMap I hdim hL hδ f hf hdisj hs b := by
  let : ChartedSpace E3 OverlapOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  funext p
  let x := finiteCapOldOverlapRadialMap I hdim hL hδ f hf hdisj hs b p
  let c := finiteCapOpenChart hL hδ f hf hdisj b
  let pOld : finiteCoreInteriorOpens hL hδ f hf hdisj := ⟨p.val, p.property.2⟩
  have hp : p.val ∈ c.source := by
    rw [finiteCapOpenChart_source]
    exact p.property.1
  have hx : x.val = c p.val := finiteCapRadialCoordinateMap_eq_openChart I hdim hL hδ f hf hdisj hs b ⟨p.val, p.property.1⟩
  have hc : c.symm x.val = p.val := by
    rw [hx]
    exact c.left_inv hp
  have hAnn : finiteCoreInteriorMap hL hδ f (fun i => (hf i).injective) hdisj
      (finiteCapAnnulusOldMap hL hδ f hf hdisj b x) = p.val :=
    (finiteCapOpenChart_symm_annulus hL hδ f hf hdisj b x).symm.trans hc
  have hOld := finiteCoreInteriorDiffeomorph_symm_original I hdim hL hδ f hf hdisj hs pOld
  have he : (finiteCoreInteriorDiffeomorph I hdim hL hδ f hf hdisj hs).symm pOld =
      finiteCapAnnulusOldMap hL hδ f hf hdisj b x :=
    (isOpenEmbedding_finiteCoreInteriorMap hL hδ f hf hdisj).injective (hOld.trans hAnn.symm)
  exact congrArg Subtype.val he

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOldOverlap_old_coordinate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOldOverlap_old_coordinate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOldOverlap_old_coordinate ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOldOverlap_old_coordinate

theorem finiteCapOldOverlap_radial_mfderiv (b : ι × Bool)
    (p : finiteCapOldOverlapOpens hL hδ f hf hdisj b) :
    let : ChartedSpace E3 OverlapOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    mfderiv (𝓡 3) (𝓡 3) (finiteCapRadialCoordinateMap I hdim hL hδ f hf hdisj hs b)
      ⟨p.val, p.property.1⟩ =
    mfderiv (𝓡 3) (𝓡 3) (finiteCapOldOverlapRadialMap I hdim hL hδ f hf hdisj hs b) p := by
  let : ChartedSpace E3 OverlapOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let A := cuttingAnnulus L (precision b.1)
  let C := finiteCapRadialCoordinateMap I hdim hL hδ f hf hdisj hs b
  let r := finiteCapOldOverlapRadialMap I hdim hL hδ f hf hdisj hs b
  have hinc : finiteCapOldOverlapOpens hL hδ f hf hdisj b ≤
      finiteCapNeighborhoodOpens hL hδ f hf hdisj b := inf_le_left
  let j := Opens.inclusion hinc
  have hj : ContMDiff (𝓡 3) (𝓡 3) ∞ j := contMDiff_inclusion hinc
  have hC := finiteCapRadialCoordinateMap_contMDiff I hdim hL hδ f hf hdisj hs b
  have hr := finiteCapOldOverlapRadialMap_contMDiff I hdim hL hδ f hf hdisj hs b
  have h₁ := mfderiv_comp (f := j) (g := C) p
    (hC.mdifferentiable (by simp) (j p)) (hj.mdifferentiable (by simp) p)
  rw [DifferentialGeometry.mfderiv_opens_incl] at h₁
  have h₁' : (mfderiv (𝓡 3) (𝓡 3) (C ∘ j) p : E3 →L[ℝ] E3) =
      mfderiv (𝓡 3) (𝓡 3) C ⟨p.val, p.property.1⟩ := h₁
  have h₂ := mfderiv_comp_open_val (𝓡 3) (𝓡 3) A r hr p
  have h₂' : (mfderiv (𝓡 3) (𝓡 3) (C ∘ j) p : E3 →L[ℝ] E3) =
      mfderiv (𝓡 3) (𝓡 3) r p := h₂
  exact h₁'.symm.trans h₂'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOldOverlap_radial_mfderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOldOverlap_radial_mfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOldOverlap_radial_mfderiv ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOldOverlap_radial_mfderiv

theorem finiteCapOldOverlap_old_mfderiv (b : ι × Bool)
    (p : finiteCapOldOverlapOpens hL hδ f hf hdisj b) :
    let : ChartedSpace E3 OverlapOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    mfderiv (𝓡 3) I (finiteOldAmbientCoordinateMap I hdim hL hδ f hf hdisj hs)
      ⟨p.val, p.property.2⟩ =
      (mfderiv (𝓡 3) I (f b.1 ∘ cuttingAnnulusCylinderMap hL (hδ b.1) b.2)
        (finiteCapOldOverlapRadialMap I hdim hL hδ f hf hdisj hs b p)).comp
      (mfderiv (𝓡 3) (𝓡 3) (finiteCapOldOverlapRadialMap I hdim hL hδ f hf hdisj hs b) p) := by
  let : ChartedSpace E3 OverlapOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let σ := finiteOldAmbientCoordinateMap I hdim hL hδ f hf hdisj hs
  let F := f b.1 ∘ cuttingAnnulusCylinderMap hL (hδ b.1) b.2
  let r := finiteCapOldOverlapRadialMap I hdim hL hδ f hf hdisj hs b
  have hinc : finiteCapOldOverlapOpens hL hδ f hf hdisj b ≤
      finiteCoreInteriorOpens hL hδ f hf hdisj := inf_le_right
  let j := Opens.inclusion hinc
  have hj : ContMDiff (𝓡 3) (𝓡 3) ∞ j := contMDiff_inclusion hinc
  have hσ := finiteOldAmbientCoordinateMap_contMDiff I hdim hL hδ f hf hdisj hs
  have hr := finiteCapOldOverlapRadialMap_contMDiff I hdim hL hδ f hf hdisj hs b
  have hF : ContMDiff (𝓡 3) I ∞ F :=
    (finiteCapAnnulusAmbient_isLocalDiffeomorph (I := I) hL hδ f hs b).contMDiff
  have h₁ := mfderiv_comp (f := j) (g := σ) p
    (hσ.mdifferentiable (by simp) (j p)) (hj.mdifferentiable (by simp) p)
  rw [DifferentialGeometry.mfderiv_opens_incl] at h₁
  have h₁' : (mfderiv (𝓡 3) I (σ ∘ j) p : E3 →L[ℝ] E) =
      mfderiv (𝓡 3) I σ ⟨p.val, p.property.2⟩ := h₁
  have h₂ := mfderiv_comp (f := r) (g := F) p
    (hF.mdifferentiable (by simp) (r p)) (hr.mdifferentiable (by simp) p)
  have h₂' : (mfderiv (𝓡 3) I (F ∘ r) p : E3 →L[ℝ] E) =
      (mfderiv (𝓡 3) I F (r p)).comp (mfderiv (𝓡 3) (𝓡 3) r p) := h₂
  let D : (finiteCapOldOverlapOpens hL hδ f hf hdisj b → M) → (E3 →L[ℝ] E) :=
    fun g => mfderiv (𝓡 3) I g p
  have hd : (mfderiv (𝓡 3) I (σ ∘ j) p : E3 →L[ℝ] E) =
      mfderiv (𝓡 3) I (F ∘ r) p :=
    congrArg D (finiteCapOldOverlap_old_coordinate I hdim hL hδ f hf hdisj hs b)
  exact h₁'.symm.trans (hd.trans h₂')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOldOverlap_old_mfderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOldOverlap_old_mfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOldOverlap_old_mfderiv ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOldOverlap_old_mfderiv
end DifferentialGeometry.Topology.ThreeManifold.Surgery
