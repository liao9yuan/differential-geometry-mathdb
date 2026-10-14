import Submission.DifferentialGeometry.Topology.Manifold.SmoothOrientationComparison
import Submission.DifferentialGeometry.Topology.Manifold.SmoothOrientationPullback
import Submission.DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import Submission.DifferentialGeometry.Topology.Manifold.SmoothEmbeddingFromOpen
import Submission.DifferentialGeometry.Topology.Manifold.Attachment.RadialEmbedding
import Mathlib.Analysis.Normed.Module.Connected

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.Manifold.Attachment
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.E3 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.S2 target :: scope.openDecls } }
private abbrev IR := (𝓡 2).prod (𝓡∂ 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.IR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.IR target :: scope.openDecls } }
private abbrev Collar (B : ℝ) := S2 × _root_.Set.Ico (0 : ℝ) B

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.Collar
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.Collar target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Attachment.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }

def radialCollarOrientationMap (L B : ℝ) (q : Collar B) : E3 := (L + q.2.val) • q.1.val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.radialCollarOrientationMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.radialCollarOrientationMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.radialCollarOrientationMap ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.radialCollarOrientationMap

theorem radialCollarOrientationMap_isSmoothEmbedding {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    letI := halfClosedIntervalChartedSpace hB
    IsSmoothEmbedding IR (𝓡 3) ∞ (radialCollarOrientationMap L B) := by
  let := halfClosedIntervalChartedSpace hB
  exact isSmoothEmbedding_fromOpen IR (𝓡 3) _ (retainedRadialMap hL)
    (isSmoothEmbedding_retainedRadialMap hL hB)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.radialCollarOrientationMap_isSmoothEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.radialCollarOrientationMap_isSmoothEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.radialCollarOrientationMap_isSmoothEmbedding ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.radialCollarOrientationMap_isSmoothEmbedding

theorem radialCollarOrientationMap_mfderiv_bijective {L B : ℝ} (hL : 0 < L) (hB : 0 < B)
    (q : Collar B) :
    letI := halfClosedIntervalChartedSpace hB
    Bijective (mfderiv IR (𝓡 3) (radialCollarOrientationMap L B) q) := by
  let := halfClosedIntervalChartedSpace hB
  exact bijective_mfderiv_of_isImmersionAt IR (𝓡 3) _ q
    ((radialCollarOrientationMap_isSmoothEmbedding hL hB).isImmersion.isImmersionAt q) (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.radialCollarOrientationMap_mfderiv_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.radialCollarOrientationMap_mfderiv_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.radialCollarOrientationMap_mfderiv_bijective ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.radialCollarOrientationMap_mfderiv_bijective

def radialCollarSmoothOrientation {L B : ℝ} (hL : 0 < L) (hB : 0 < B)
    (o : Orientation ℝ E3 (Fin (Module.finrank ℝ E3))) :
    letI := halfClosedIntervalChartedSpace hB
    letI := halfClosedInterval_isManifold hB
    SmoothOrientation IR (Collar B) := by
  let := halfClosedIntervalChartedSpace hB
  let := halfClosedInterval_isManifold hB
  exact pullbackSmoothOrientation IR (𝓡 3) (radialCollarOrientationMap L B)
    (radialCollarOrientationMap_isSmoothEmbedding hL hB).contMDiff
    (radialCollarOrientationMap_mfderiv_bijective hL hB) (euclideanSmoothOrientation E3 o)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.radialCollarSmoothOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.radialCollarSmoothOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.radialCollarSmoothOrientation ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.radialCollarSmoothOrientation

theorem radialCollarSmoothOrientation_neg_apply {L B : ℝ} (hL : 0 < L) (hB : 0 < B)
    (o : Orientation ℝ E3 (Fin (Module.finrank ℝ E3))) (q : Collar B) :
    letI := halfClosedIntervalChartedSpace hB
    letI := halfClosedInterval_isManifold hB
    (radialCollarSmoothOrientation hL hB (-o)).val q =
      -(radialCollarSmoothOrientation hL hB o).val q := by
  let := halfClosedIntervalChartedSpace hB
  let := halfClosedInterval_isManifold hB
  exact tangentOrientationEquiv_neg
    (differentialEquivOfBijective IR (𝓡 3) (radialCollarOrientationMap L B)
      (radialCollarOrientationMap_mfderiv_bijective hL hB) q).symm.toLinearEquiv o

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.radialCollarSmoothOrientation_neg_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.radialCollarSmoothOrientation_neg_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.radialCollarSmoothOrientation_neg_apply ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.radialCollarSmoothOrientation_neg_apply

theorem exists_radialCollarSmoothOrientation {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    letI := halfClosedIntervalChartedSpace hB
    letI := halfClosedInterval_isManifold hB
    ∀ O : SmoothOrientation IR (Collar B),
      ∃ o : Orientation ℝ E3 (Fin (Module.finrank ℝ E3)),
        (o = (Module.finBasis ℝ E3).orientation ∨ o = -(Module.finBasis ℝ E3).orientation) ∧
        ∀ q : Collar B, (radialCollarSmoothOrientation hL hB o).val q = O.val q := by
  let := halfClosedIntervalChartedSpace hB
  let := halfClosedInterval_isManifold hB
  refine fun O => ?_
  let : ConnectedSpace S2 := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) (0 : E3) (by norm_num : (0 : ℝ) ≤ 1))
  let : PreconnectedSpace (_root_.Set.Ico (0 : ℝ) B) := Subtype.preconnectedSpace isPreconnected_Ico
  let o₀ : Orientation ℝ E3 (Fin (Module.finrank ℝ E3)) := (Module.finBasis ℝ E3).orientation
  let y : S2 := Classical.choice (NormedSpace.sphere_nonempty_rclike ℝ (E := E3) (r := (1 : ℝ)) zero_le_one)
  let q₀ : Collar B := (y, ⟨0, le_rfl, hB⟩)
  rcases smoothOrientation_eq_or_eq_neg IR O (radialCollarSmoothOrientation hL hB o₀) q₀ with h | h
  · exact ⟨o₀, Or.inl rfl, fun q => (h q).symm⟩
  · refine ⟨-o₀, Or.inr rfl, ?_⟩
    intro q
    rw [radialCollarSmoothOrientation_neg_apply]
    exact (h q).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.Attachment.exists_radialCollarSmoothOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.Attachment.exists_radialCollarSmoothOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.Attachment.exists_radialCollarSmoothOrientation ``Submission.DifferentialGeometry.Topology.Manifold.Attachment.exists_radialCollarSmoothOrientation
end DifferentialGeometry.Topology.Manifold.Attachment
