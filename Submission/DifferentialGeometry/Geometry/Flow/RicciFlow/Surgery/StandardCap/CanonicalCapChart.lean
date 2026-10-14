import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CanonicalStaticWindow
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CanonicalRetainedMetric
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SphericalTransitionBridge
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWitness
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCap
import Submission.DifferentialGeometry.Topology.Manifold.SmoothEmbeddingDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Submission.Set _root_.Function _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry.Neck
open _root_.Submission.DifferentialGeometry.Topology.Handle _root_.Submission.DifferentialGeometry.Topology.Manifold
open _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instChartedSpaceEuclideanHalfSpaceOfNatNatSubtypeThreeSpaceLeRealNormTransitionEnd : ChartedSpace (EuclideanHalfSpace 3)
    {x : ThreeSpace // ‖x‖ ≤ StandardCap.transitionEnd} :=
  closedBallChartedSpace StandardCap.transitionEnd_pos

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instChartedSpaceEuclideanHalfSpaceOfNatNatSubtypeThreeSpaceLeRealNormTransitionEnd
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instChartedSpaceEuclideanHalfSpaceOfNatNatSubtypeThreeSpaceLeRealNormTransitionEnd target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instIsManifoldRealEuclideanSpaceFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopSubtypeThreeSpaceLeNormTransitionEnd : IsManifold (𝓡∂ 3) ∞
    {x : ThreeSpace // ‖x‖ ≤ StandardCap.transitionEnd} :=
  closedBall_isManifold StandardCap.transitionEnd_pos

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instIsManifoldRealEuclideanSpaceFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopSubtypeThreeSpaceLeNormTransitionEnd
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instIsManifoldRealEuclideanSpaceFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopSubtypeThreeSpaceLeNormTransitionEnd target :: scope.openDecls } }

def standardCapCoreHomeomorph :
    standardCapClosedCore ≃ₜ {x : ThreeSpace // ‖x‖ ≤ StandardCap.transitionEnd} where
  toFun x := ⟨x.val, by
    simpa only [standardCapClosedCore, Metric.mem_closedBall, dist_zero_right,
      show standardCapL = StandardCap.transitionEnd from rfl] using x.property⟩
  invFun x := ⟨x.val, by
    simpa only [standardCapClosedCore, Metric.mem_closedBall, dist_zero_right,
      show standardCapL = StandardCap.transitionEnd from rfl] using x.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  continuous_toFun := continuous_subtype_val.subtype_mk (fun x => by
    simpa only [standardCapClosedCore, Metric.mem_closedBall, dist_zero_right,
      show standardCapL = StandardCap.transitionEnd from rfl] using x.property)
  continuous_invFun := continuous_subtype_val.subtype_mk (fun x => by
    simpa only [standardCapClosedCore, Metric.mem_closedBall, dist_zero_right,
      show standardCapL = StandardCap.transitionEnd from rfl] using x.property)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardCapCoreHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardCapCoreHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardCapCoreHomeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardCapCoreHomeomorph

@[instance_reducible] def standardCapCoreChartedSpace :
    ChartedSpace (EuclideanHalfSpace 3) standardCapClosedCore :=
  chartedSpaceOfHomeomorph standardCapCoreHomeomorph

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardCapCoreChartedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardCapCoreChartedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardCapCoreChartedSpace ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardCapCoreChartedSpace

theorem standardCapCore_isManifold :
    letI := standardCapCoreChartedSpace
    IsManifold (𝓡∂ 3) ∞ standardCapClosedCore :=
  isManifoldOfHomeomorph (𝓡∂ 3) standardCapCoreHomeomorph

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardCapCore_isManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardCapCore_isManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardCapCore_isManifold ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardCapCore_isManifold

def standardCapCoreDiffeomorph :
    letI := standardCapCoreChartedSpace
    standardCapClosedCore ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯
      {x : ThreeSpace // ‖x‖ ≤ StandardCap.transitionEnd} := by
  letI := standardCapCoreChartedSpace
  exact
    { toEquiv := standardCapCoreHomeomorph.toEquiv
      contMDiff_toFun := contMDiff_homeomorph_of_chartedSpaceOfHomeomorph
        standardCapCoreHomeomorph (𝓡∂ 3) ∞
      contMDiff_invFun := contMDiff_homeomorph_symm_of_chartedSpaceOfHomeomorph
        standardCapCoreHomeomorph (𝓡∂ 3) ∞ }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardCapCoreDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardCapCoreDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardCapCoreDiffeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardCapCoreDiffeomorph

theorem standardCapCore_induced :
    letI := standardCapCoreChartedSpace
    _root_.Manifold.IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
      (Subtype.val : standardCapClosedCore → ThreeSpace) := by
  let := standardCapCoreChartedSpace
  let := standardCapCore_isManifold
  exact isSmoothEmbedding_diffeomorph_precomp Subtype.val
    (isSmoothEmbedding_closedBall_inclusion StandardCap.transitionEnd_pos)
    standardCapCoreDiffeomorph

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardCapCore_induced then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardCapCore_induced"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardCapCore_induced ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardCapCore_induced

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.E3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instChartedSpaceEuclideanHalfSpaceOfNatNatSubtypeE3LeRealNormTransitionEnd : ChartedSpace (EuclideanHalfSpace 3)
    {x : E3 // ‖x‖ ≤ transitionEnd} := closedBallChartedSpace transitionEnd_pos

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instChartedSpaceEuclideanHalfSpaceOfNatNatSubtypeE3LeRealNormTransitionEnd
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instChartedSpaceEuclideanHalfSpaceOfNatNatSubtypeE3LeRealNormTransitionEnd target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instIsManifoldRealEuclideanSpaceFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopSubtypeE3LeNormTransitionEnd : IsManifold (𝓡∂ 3) ∞
    {x : E3 // ‖x‖ ≤ transitionEnd} := closedBall_isManifold transitionEnd_pos

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instIsManifoldRealEuclideanSpaceFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopSubtypeE3LeNormTransitionEnd
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instIsManifoldRealEuclideanSpaceFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopSubtypeE3LeNormTransitionEnd target :: scope.openDecls } }
private local instance quotientChartedSpace {B : ℝ} {hB : 0 < B} :
    ChartedSpace E3 (InsertionQuotient hB) := radialCapAttachmentChartedSpace transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientChartedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientChartedSpace target :: scope.openDecls } }
private local instance quotientIsManifold {B : ℝ} {hB : 0 < B} :
    IsManifold (𝓡 3) ∞ (InsertionQuotient hB) := radialCapAttachment_isManifold transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientIsManifold
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientIsManifold target :: scope.openDecls } }

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
  {d : normalizedDatum g x₀ δ k}
  {A : ℝ} {hA : 0 < A} {D : ℝ} {m : ℕ} {ε : ℝ}

namespace CanonicalStaticInsertionWitness

variable (w : CanonicalStaticInsertionWitness d A hA D m ε)

def capChart : C(standardCapClosedCore, InsertionQuotient (inv_pos.mpr d.precision_pos)) :=
  ⟨w.data.capMap ∘ standardCapCoreHomeomorph,
    w.properties.capMap_embedding.contMDiff.continuous.comp standardCapCoreHomeomorph.continuous⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.capChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.capChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.capChart ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.capChart

theorem capChart_smooth :
    letI := standardCapCoreChartedSpace
    IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ w.capChart := by
  let := standardCapCoreChartedSpace
  let := standardCapCore_isManifold
  exact isSmoothEmbedding_diffeomorph_precomp w.data.capMap w.properties.capMap_embedding
    standardCapCoreDiffeomorph

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.capChart_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.capChart_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.capChart_smooth ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.capChart_smooth

theorem capChart_range : _root_.Set.range w.capChart = _root_.Set.range w.data.capInclusion := by
  change _root_.Set.range (w.data.capMap ∘ standardCapCoreHomeomorph) = _root_.Set.range w.data.capInclusion
  rw [standardCapCoreHomeomorph.surjective.range_comp]
  exact w.properties.capMap_image

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.capChart_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.capChart_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.capChart_range ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.capChart_range

theorem capChart_boundary (y : Sphere 2)
    (hx : standardCapL • y.val ∈ standardCapClosedCore) :
    w.capChart ⟨standardCapL • y.val, hx⟩ =
      w.data.retainedInclusion (retainedBoundary (inv_pos.mpr d.precision_pos) y) := by
  exact w.properties.capMap_boundary y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.capChart_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.capChart_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.capChart_boundary ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.capChart_boundary

theorem capChart_tip (hx : (0 : ThreeSpace) ∈ standardCapClosedCore) :
    w.capChart ⟨0, hx⟩ = w.data.tip := by
  exact w.properties.capMap_tip

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.capChart_tip then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.capChart_tip"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.capChart_tip ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.capChart_tip

theorem windowMap_eq_capChart (x : ThreeSpace) (hx : ‖x‖ < D + 1)
    (hc : x ∈ standardCapClosedCore) :
    w.data.windowMap ⟨x, hx⟩ = w.capChart ⟨x, hc⟩ := by
  rw [w.properties.windowMap_eq]
  change modelWindowMap (inv_pos.mpr d.precision_pos) w.properties.window_fit ⟨x, hx⟩ =
    w.data.capMap (standardCapCoreHomeomorph ⟨x, hc⟩)
  rw [w.properties.capMap_eq, w.properties.capInclusion_eq]
  exact modelWindowMap_agrees_cap _ _ (standardCapCoreHomeomorph ⟨x, hc⟩) hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.windowMap_eq_capChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.windowMap_eq_capChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.windowMap_eq_capChart ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.windowMap_eq_capChart

end CanonicalStaticInsertionWitness
end DifferentialGeometry.PDE.RicciFlow.StandardCap
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat_1 : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instChartedSpaceEuclideanHalfSpaceOfNatNatSubtypeThreeSpaceLeRealNormTransitionEnd_1 : ChartedSpace (EuclideanHalfSpace 3)
    {x : ThreeSpace // ‖x‖ ≤ StandardCap.transitionEnd} :=
  closedBallChartedSpace StandardCap.transitionEnd_pos

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instChartedSpaceEuclideanHalfSpaceOfNatNatSubtypeThreeSpaceLeRealNormTransitionEnd_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instChartedSpaceEuclideanHalfSpaceOfNatNatSubtypeThreeSpaceLeRealNormTransitionEnd_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instIsManifoldRealEuclideanSpaceFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopSubtypeThreeSpaceLeNormTransitionEnd_1 : IsManifold (𝓡∂ 3) ∞
    {x : ThreeSpace // ‖x‖ ≤ StandardCap.transitionEnd} :=
  closedBall_isManifold StandardCap.transitionEnd_pos

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instIsManifoldRealEuclideanSpaceFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopSubtypeThreeSpaceLeNormTransitionEnd_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instIsManifoldRealEuclideanSpaceFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopSubtypeThreeSpaceLeNormTransitionEnd_1 target :: scope.openDecls } }
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold
attribute [local instance] threeBallChartedSpace threeBall_isManifold

def standardCapBallDiffeomorph :
    ThreeBall ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ {x : ThreeSpace // ‖x‖ ≤ StandardCap.transitionEnd} :=
  threeBallDiffeomorph.symm.trans
    (closedBallUnitDiffeomorph StandardCap.transitionEnd_pos).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardCapBallDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardCapBallDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardCapBallDiffeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardCapBallDiffeomorph

@[simp] theorem standardCapBallDiffeomorph_apply_val (x : ThreeBall) :
    (standardCapBallDiffeomorph x).val = StandardCap.transitionEnd • x.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardCapBallDiffeomorph_apply_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardCapBallDiffeomorph_apply_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardCapBallDiffeomorph_apply_val ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardCapBallDiffeomorph_apply_val

@[simp] theorem standardCapBallDiffeomorph_boundary (y : Sphere 2) :
    standardCapBallDiffeomorph (sphereToThreeBall y) =
      radialCapBoundary StandardCap.transitionEnd_pos y := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardCapBallDiffeomorph_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardCapBallDiffeomorph_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardCapBallDiffeomorph_boundary ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardCapBallDiffeomorph_boundary

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private abbrev E3Ball := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.E3Ball
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.E3Ball target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3BallHAddOfNat : Fact (Module.finrank ℝ E3Ball = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3BallHAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3BallHAddOfNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instChartedSpaceEuclideanHalfSpaceOfNatNatSubtypeE3BallLeRealNormTransitionEnd : ChartedSpace (EuclideanHalfSpace 3)
    {x : E3Ball // ‖x‖ ≤ transitionEnd} := closedBallChartedSpace transitionEnd_pos

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instChartedSpaceEuclideanHalfSpaceOfNatNatSubtypeE3BallLeRealNormTransitionEnd
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instChartedSpaceEuclideanHalfSpaceOfNatNatSubtypeE3BallLeRealNormTransitionEnd target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instIsManifoldRealEuclideanSpaceFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopSubtypeE3BallLeNormTransitionEnd : IsManifold (𝓡∂ 3) ∞
    {x : E3Ball // ‖x‖ ≤ transitionEnd} := closedBall_isManifold transitionEnd_pos

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instIsManifoldRealEuclideanSpaceFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopSubtypeE3BallLeNormTransitionEnd
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instIsManifoldRealEuclideanSpaceFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopSubtypeE3BallLeNormTransitionEnd target :: scope.openDecls } }
private local instance quotientBallChartedSpace {B : ℝ} {hB : 0 < B} :
    ChartedSpace E3Ball (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientBallChartedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientBallChartedSpace target :: scope.openDecls } }
private local instance quotientBallIsManifold {B : ℝ} {hB : 0 < B} :
    IsManifold (𝓡 3) ∞ (InsertionQuotient hB) := radialCapAttachment_isManifold transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientBallIsManifold
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientBallIsManifold target :: scope.openDecls } }
attribute [local instance] threeBallChartedSpace threeBall_isManifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
  {d : normalizedDatum g x₀ δ k}
  {A : ℝ} {hA : 0 < A} {D : ℝ} {m : ℕ} {ε : ℝ}

namespace CanonicalStaticInsertionWitness

variable (w : CanonicalStaticInsertionWitness d A hA D m ε)

def cap : C(ThreeBall, InsertionQuotient (inv_pos.mpr d.precision_pos)) :=
  ⟨w.data.capInclusion ∘ standardCapBallDiffeomorph,
    w.properties.cap_embedding.contMDiff.continuous.comp standardCapBallDiffeomorph.continuous⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.cap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.cap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.cap ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.cap

theorem cap_smooth : _root_.Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ w.cap :=
  isSmoothEmbedding_diffeomorph_precomp w.data.capInclusion w.properties.cap_embedding
    standardCapBallDiffeomorph

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.cap_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.cap_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.cap_smooth ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.cap_smooth

theorem cap_range : _root_.Set.range w.cap = _root_.Set.range w.data.capInclusion :=
  standardCapBallDiffeomorph.surjective.range_comp w.data.capInclusion

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.cap_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.cap_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.cap_range ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.cap_range

theorem cap_boundary (y : Sphere 2) :
    w.cap (sphereToThreeBall y) =
      w.retainedMap ⟨(y, 0), le_rfl, inv_pos.mpr d.precision_pos⟩ := by
  change w.data.capInclusion (standardCapBallDiffeomorph (sphereToThreeBall y)) = _
  rw [standardCapBallDiffeomorph_boundary]
  rw [← w.properties.capMap_eq]
  exact w.properties.capMap_boundary y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.cap_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.cap_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.cap_boundary ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.cap_boundary

theorem cap_tip_interior : ∃ x : ThreeBall, ‖x.val‖ < 1 ∧ w.cap x = w.data.tip := by
  let z : ThreeBall := ⟨0, by simp [ThreeBall]⟩
  refine ⟨z, by simp [z], ?_⟩
  rw [w.properties.tip_eq]
  apply congrArg w.data.capInclusion
  apply Subtype.ext
  simp [standardCapBallDiffeomorph_apply_val, z]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.cap_tip_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.cap_tip_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.cap_tip_interior ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.cap_tip_interior

theorem capChart_range_cap : _root_.Set.range w.capChart = _root_.Set.range w.cap :=
  w.capChart_range.trans w.cap_range.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.capChart_range_cap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.capChart_range_cap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.capChart_range_cap ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.capChart_range_cap

theorem exists_window_preimage_cap (w : CanonicalStaticInsertionWitness d A hA D m ε)
    (hD : transitionEnd < D + 1) (z : ThreeBall) :
    ∃ u : standardCapWindow D, ‖u.val‖ ≤ transitionEnd ∧ w.window u = w.cap z := by
  have hz : w.cap z ∈ _root_.Set.range w.cap := ⟨z, rfl⟩
  rw [← w.capChart_range_cap] at hz
  obtain ⟨x, hx⟩ := hz
  have hxnorm : ‖x.val‖ ≤ transitionEnd := by
    simpa only [standardCapClosedCore, Metric.mem_closedBall, dist_zero_right,
      standardCapL_eq_transitionEnd] using x.property
  refine ⟨⟨x.val, hxnorm.trans_lt hD⟩, hxnorm, ?_⟩
  exact (w.windowMap_eq_capChart x.val (hxnorm.trans_lt hD) x.property).trans hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.exists_window_preimage_cap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.exists_window_preimage_cap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.exists_window_preimage_cap ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.CanonicalStaticInsertionWitness.exists_window_preimage_cap

end CanonicalStaticInsertionWitness
end DifferentialGeometry.PDE.RicciFlow.StandardCap
