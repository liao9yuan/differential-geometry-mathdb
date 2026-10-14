import Submission.DifferentialGeometry.Geometry.Neck.PointwiseChart
import Submission.DifferentialGeometry.Geometry.Metric.BilinearPerturbation
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Flat
import Submission.DifferentialGeometry.Geometry.Metric.RoundCylinder

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.TopologicalSpace _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian
open _root_.Submission.DifferentialGeometry.Geometry.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal
namespace DifferentialGeometry.Geometry.Neck

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.E3 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.S2 target :: scope.openDecls } }
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.IC target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Neck.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Neck.instSigmaCompactSpaceSubtypeProdElemE3S2RealMemOpens (O : _root_.TopologicalSpace.Opens (S2 × ℝ)) : SigmaCompactSpace O :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen IC O.isOpen)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.instSigmaCompactSpaceSubtypeProdElemE3S2RealMemOpens
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.instSigmaCompactSpaceSubtypeProdElemE3S2RealMemOpens target :: scope.openDecls } }

theorem openCylinder_inv_le_bufferedCylinder (δ : ℝ) :
    openCylinder δ⁻¹ ≤ bufferedCylinder δ := by
  intro q hq
  change -δ⁻¹ < q.2 ∧ q.2 < δ⁻¹ at hq
  change -δ⁻¹ - 1 < q.2 ∧ q.2 < δ⁻¹ + 1
  constructor <;> linarith [hq.1, hq.2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.openCylinder_inv_le_bufferedCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.openCylinder_inv_le_bufferedCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.openCylinder_inv_le_bufferedCylinder ``Submission.DifferentialGeometry.Geometry.Neck.openCylinder_inv_le_bufferedCylinder

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

namespace normalizedDatum

variable {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}

def controlledMap (d : normalizedDatum g x₀ δ k) : openCylinder δ⁻¹ → M :=
  d.map ∘ Opens.inclusion (openCylinder_inv_le_bufferedCylinder δ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMap ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMap

theorem controlledMap_apply (d : normalizedDatum g x₀ δ k) (q : openCylinder δ⁻¹) :
    d.controlledMap q = d.map (Opens.inclusion (openCylinder_inv_le_bufferedCylinder δ) q) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMap_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMap_apply ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMap_apply

theorem controlledMap_smooth (d : normalizedDatum g x₀ δ k) :
    ContMDiff IC I ∞ d.controlledMap :=
  d.smooth.comp (contMDiff_inclusion (openCylinder_inv_le_bufferedCylinder δ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMap_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMap_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMap_smooth ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMap_smooth

theorem controlledMap_isOpenEmbedding (d : normalizedDatum g x₀ δ k) :
    _root_.Topology.IsOpenEmbedding d.controlledMap :=
  d.isOpenEmbedding_map.comp (Opens.isOpenEmbedding_of_le
    (openCylinder_inv_le_bufferedCylinder δ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMap_isOpenEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMap_isOpenEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMap_isOpenEmbedding ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMap_isOpenEmbedding

theorem controlledMap_mfderiv (d : normalizedDatum g x₀ δ k) (q : openCylinder δ⁻¹)
    (v : TangentSpace IC q) :
    mfderiv IC I d.controlledMap q v =
      mfderiv IC I d.map (Opens.inclusion (openCylinder_inv_le_bufferedCylinder δ) q) v := by
  have h := mfderiv_comp q
    (d.smooth.mdifferentiable (by decide) _)
    ((contMDiff_inclusion (I := IC) (n := ∞)
      (openCylinder_inv_le_bufferedCylinder δ)).mdifferentiable (by decide) q)
  have hv := congrArg (fun f => f v) h
  simpa only [controlledMap, mfderiv_opens_incl, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] using! hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMap_mfderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMap_mfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMap_mfderiv ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMap_mfderiv

def controlledMetric (d : normalizedDatum g x₀ δ k) :
    SmoothRiemannianMetric IC (openCylinder δ⁻¹) :=
  d.normalizedMetric.restrictOpenOfSubset (openCylinder_inv_le_bufferedCylinder δ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMetric ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMetric

theorem controlledMetric_inner (d : normalizedDatum g x₀ δ k) (q : openCylinder δ⁻¹)
    (v w : TangentSpace IC q) :
    d.controlledMetric.inner q v w = metricScalarAt g x₀ *
      g.inner (d.controlledMap q) (mfderiv IC I d.controlledMap q v)
        (mfderiv IC I d.controlledMap q w) := by
  rw [controlledMap_mfderiv, controlledMap_mfderiv]
  exact d.normalizedMetric_inner
    (Opens.inclusion (openCylinder_inv_le_bufferedCylinder δ) q) v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMetric_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMetric_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMetric_inner ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMetric_inner

private theorem metricDerivNorm_controlledMetric (d : normalizedDatum g x₀ δ k)
    (j : ℕ) (q : openCylinder δ⁻¹) :
    metricDerivNorm j d.controlledMetric
      ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (openCylinder δ⁻¹))
      ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (openCylinder δ⁻¹)) q =
      metricDerivNorm j d.normalizedMetric (referenceMetric δ) (referenceMetric δ)
        (Opens.inclusion (openCylinder_inv_le_bufferedCylinder δ) q) := by
  simpa only [controlledMetric, referenceMetric, SmoothRiemannianMetric.restrictOpen_flat]
    using! metricDerivNorm_flat (openCylinder_inv_le_bufferedCylinder δ)
      d.normalizedMetric (referenceMetric δ) (referenceMetric δ) j q

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.metricDerivNorm_controlledMetric
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.normalizedDatum.metricDerivNorm_controlledMetric target :: scope.openDecls } }

theorem controlledMetric_error_lt (d : normalizedDatum g x₀ δ k) :
    metricDerivENormSupOn _root_.Set.univ k d.controlledMetric
      ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (openCylinder δ⁻¹))
      ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (openCylinder δ⁻¹)) <
        ENNReal.ofReal δ := by
  apply lt_of_le_of_lt _ d.normalizedMetric_error_lt
  apply (metricDerivENormSupOn_le_iff _ _ _ _ _ _).mpr
  intro j hj q _
  rw [metricDerivNorm_controlledMetric]
  apply ofReal_metricDerivNorm_le_sup _ _ _ _ _ hj
  exact ⟨q.property.1.le, q.property.2.le⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMetric_error_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMetric_error_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMetric_error_lt ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMetric_error_lt

theorem controlledMetric_cylinder_lower (d : normalizedDatum g x₀ δ k) :
    0 < 1 - Real.sqrt δ ∧ ∀ (q : openCylinder δ⁻¹) (v : TangentSpace IC q),
      (1 - Real.sqrt δ) * (roundCylinderMetric (E := E3) (n := 2)).inner q.val v v ≤
        d.controlledMetric.inner q v v := by
  constructor
  · apply sub_pos.mpr
    exact (Real.sqrt_lt d.precision_pos.le zero_le_one).mpr
      (by simpa using d.precision_lt_one)
  · intro q v
    have hl := (inner_bounds_of_metricDerivENormSupOn_lt
      ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (openCylinder δ⁻¹))
      d.controlledMetric d.controlledMetric_error_lt (_root_.Set.mem_univ q) v).1
    change (1 - δ) * (roundCylinderMetric (E := E3) (n := 2)).inner q.val v v ≤ _ at hl
    apply le_trans _ hl
    apply mul_le_mul_of_nonneg_right _
      (metric_inner_self_nonneg (roundCylinderMetric (E := E3) (n := 2)) q.val v)
    linarith [Real.le_sqrt_self_iff.mpr d.precision_lt_one.le]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMetric_cylinder_lower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMetric_cylinder_lower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMetric_cylinder_lower ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.controlledMetric_cylinder_lower

end normalizedDatum
end DifferentialGeometry.Geometry.Neck
