import Submission.DifferentialGeometry.Geometry.Neck.InsertionChart
import Submission.DifferentialGeometry.Geometry.Measure.MetricComparison
import Submission.DifferentialGeometry.Geometry.Measure.LocalIsometry
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Scaling
import Submission.DifferentialGeometry.Topology.SigmaCompactOpen

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.ENNReal _root_.Topology _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Neck

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.E3 target :: scope.openDecls } }
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.IC target :: scope.openDecls } }
private instance _root_.Submission.DifferentialGeometry.Geometry.Neck.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }
private instance _root_.Submission.DifferentialGeometry.Geometry.Neck.instMeasurableSpaceSubtypeProdElemE3S2RealMemOpensOpenCylinder {B : ℝ} : MeasurableSpace (openCylinder B) := borel (openCylinder B)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.instMeasurableSpaceSubtypeProdElemE3S2RealMemOpensOpenCylinder
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.instMeasurableSpaceSubtypeProdElemE3S2RealMemOpensOpenCylinder target :: scope.openDecls } }
private instance _root_.Submission.DifferentialGeometry.Geometry.Neck.instBorelSpaceSubtypeProdElemE3S2RealMemOpensOpenCylinder {B : ℝ} : BorelSpace (openCylinder B) := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.instBorelSpaceSubtypeProdElemE3S2RealMemOpensOpenCylinder
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.instBorelSpaceSubtypeProdElemE3S2RealMemOpensOpenCylinder target :: scope.openDecls } }
private instance _root_.Submission.DifferentialGeometry.Geometry.Neck.instMeasurableSpaceSubtypeProdElemE3S2RealMemOpensBufferedCylinder {δ : ℝ} : MeasurableSpace (bufferedCylinder δ) := borel (bufferedCylinder δ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.instMeasurableSpaceSubtypeProdElemE3S2RealMemOpensBufferedCylinder
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.instMeasurableSpaceSubtypeProdElemE3S2RealMemOpensBufferedCylinder target :: scope.openDecls } }
private instance _root_.Submission.DifferentialGeometry.Geometry.Neck.instBorelSpaceSubtypeProdElemE3S2RealMemOpensBufferedCylinder {δ : ℝ} : BorelSpace (bufferedCylinder δ) := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.instBorelSpaceSubtypeProdElemE3S2RealMemOpensBufferedCylinder
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.instBorelSpaceSubtypeProdElemE3S2RealMemOpensBufferedCylinder target :: scope.openDecls } }
private instance _root_.Submission.DifferentialGeometry.Geometry.Neck.instSigmaCompactSpaceSubtypeProdElemE3S2RealMemOpensBufferedCylinder {δ : ℝ} : SigmaCompactSpace (bufferedCylinder δ) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen IC (bufferedCylinder δ).isOpen)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.instSigmaCompactSpaceSubtypeProdElemE3S2RealMemOpensBufferedCylinder
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.instSigmaCompactSpaceSubtypeProdElemE3S2RealMemOpensBufferedCylinder target :: scope.openDecls } }
private instance _root_.Submission.DifferentialGeometry.Geometry.Neck.instSigmaCompactSpaceSubtypeProdElemE3S2RealMemOpensOpenCylinder {B : ℝ} : SigmaCompactSpace (openCylinder B) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen IC (openCylinder B).isOpen)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.instSigmaCompactSpaceSubtypeProdElemE3S2RealMemOpensOpenCylinder
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.instSigmaCompactSpaceSubtypeProdElemE3S2RealMemOpensOpenCylinder target :: scope.openDecls } }

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Geometry.Neck.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Neck.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Neck.instMeasurableSpaceSubtypeMemOpens_differentialGeometry (U : _root_.TopologicalSpace.Opens M) : MeasurableSpace U := borel U

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.instMeasurableSpaceSubtypeMemOpens_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.instMeasurableSpaceSubtypeMemOpens_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Neck.instBorelSpaceSubtypeMemOpens_differentialGeometry (U : _root_.TopologicalSpace.Opens M) : BorelSpace U := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.instBorelSpaceSubtypeMemOpens_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.instBorelSpaceSubtypeMemOpens_differentialGeometry target :: scope.openDecls } }

namespace normalizedDatum

variable {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}

theorem volume_controlled_image_eq (d : normalizedDatum g x₀ δ k)
    {S : Set (openCylinder δ⁻¹)} (hS : MeasurableSet S) :
    riemannianVolumeMeasure I M g (d.controlledMap '' S) =
      ENNReal.ofReal (Real.sqrt (metricScalarAt g x₀)⁻¹) ^ 3 *
        riemannianVolumeMeasure IC (openCylinder δ⁻¹) d.controlledMetric S := by
  let h := scaleMetric (metricScalarAt g x₀)⁻¹ (inv_pos.mpr d.scalar_pos) d.controlledMetric
  have hm (q : openCylinder δ⁻¹) (v w : TangentSpace IC q) :
      h.inner q v w = g.inner (d.controlledMap q)
        (mfderiv IC I d.controlledMap q v) (mfderiv IC I d.controlledMap q w) := by
    change (metricScalarAt g x₀)⁻¹ * d.controlledMetric.inner q v w = _
    rw [d.controlledMetric_inner, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt d.scalar_pos), one_mul]
  have heq := DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_image_eq_of_injective_local_isometry
    h g d.controlledMap d.controlledMap_isLocalDiffeomorph d.controlledMap_isOpenEmbedding.injective hm hS
  rw [← heq, volume_scale_apply]
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = 3 := by simp
  rw [hdim]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.volume_controlled_image_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.volume_controlled_image_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.volume_controlled_image_eq ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.volume_controlled_image_eq

theorem volume_image_eq (d : normalizedDatum g x₀ δ k)
    {S : Set (bufferedCylinder δ)} (hS : MeasurableSet S) :
    riemannianVolumeMeasure I M g (d.map '' S) =
      ENNReal.ofReal (Real.sqrt (metricScalarAt g x₀)⁻¹) ^ 3 *
        riemannianVolumeMeasure IC (bufferedCylinder δ) d.normalizedMetric S := by
  let h := scaleMetric (metricScalarAt g x₀)⁻¹ (inv_pos.mpr d.scalar_pos) d.normalizedMetric
  have hm (q : bufferedCylinder δ) (v w : TangentSpace IC q) :
      h.inner q v w = g.inner (d.map q)
        (mfderiv IC I d.map q v) (mfderiv IC I d.map q w) := by
    change (metricScalarAt g x₀)⁻¹ * d.normalizedMetric.inner q v w = _
    rw [d.normalizedMetric_inner, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt d.scalar_pos), one_mul]
  have hlocal : IsLocalDiffeomorph IC I ∞ d.map :=
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv d.map d.smooth d.immersion
      (by rw [show Module.finrank ℝ E = 3 from Fact.out]; simp)
  have heq := DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_image_eq_of_injective_local_isometry
    h g d.map hlocal d.injective hm hS
  rw [← heq, volume_scale_apply]
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = 3 := by simp
  rw [hdim]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.volume_image_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.volume_image_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.volume_image_eq ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.volume_image_eq

private theorem sqrt_cube_eq_rpow (c : ℝ) (hc : 0 ≤ c) :
    ENNReal.ofReal (Real.sqrt c) ^ 3 = ENNReal.ofReal (c ^ (3 / 2 : ℝ)) := by
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _) 3]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hc]
  congr 1
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.sqrt_cube_eq_rpow
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.normalizedDatum.sqrt_cube_eq_rpow target :: scope.openDecls } }

theorem volume_controlled_image_ge (d : normalizedDatum g x₀ δ k)
    {S : Set (openCylinder δ⁻¹)} (hS : MeasurableSet S) :
    ENNReal.ofReal ((metricScalarAt g x₀) ^ (-3 / 2 : ℝ)) *
      ENNReal.ofReal ((1 - δ) ^ (3 / 2 : ℝ)) *
        riemannianVolumeMeasure IC (openCylinder δ⁻¹)
          ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (openCylinder δ⁻¹)) S ≤
      riemannianVolumeMeasure I M g (d.controlledMap '' S) := by
  let g₀ := (roundCylinderMetric (E := E3) (n := 2)).restrictOpen (openCylinder δ⁻¹)
  have hpos : 0 < 1 - δ := sub_pos.mpr d.precision_lt_one
  have hinner (q : openCylinder δ⁻¹) (_ : q ∈ S) (v : TangentSpace IC q) :
      (scaleMetric (1 - δ) hpos g₀).inner q v v ≤ 1 * d.controlledMetric.inner q v v := by
    rw [scaleMetric_inner, one_mul]
    exact (inner_bounds_of_metricDerivENormSupOn_lt g₀ d.controlledMetric
      d.controlledMetric_error_lt (_root_.Set.mem_univ q) v).1
  have hb := DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_apply_le_of_inner_le
    d.controlledMetric (scaleMetric (1 - δ) hpos g₀) zero_lt_one hS hinner
  rw [volume_scale_apply] at hb
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = 3 := by simp
  rw [hdim, sqrt_cube_eq_rpow (1 - δ) hpos.le] at hb
  simp only [one_pow, Real.sqrt_one, ENNReal.ofReal_one, one_mul] at hb
  rw [volume_controlled_image_eq d hS, sqrt_cube_eq_rpow _ (inv_nonneg.mpr d.scalar_pos.le)]
  have hscale : (metricScalarAt g x₀)⁻¹ ^ (3 / 2 : ℝ) =
      (metricScalarAt g x₀) ^ (-3 / 2 : ℝ) := by
    rw [← Real.rpow_neg_eq_inv_rpow]
    congr 1
    ring
  rw [hscale, mul_assoc]
  exact mul_le_mul' le_rfl hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.volume_controlled_image_ge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.volume_controlled_image_ge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.volume_controlled_image_ge ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.volume_controlled_image_ge


theorem volume_image_ge (d : normalizedDatum g x₀ δ k)
    {S : Set (bufferedCylinder δ)} (hS : MeasurableSet S) (hcontrol : S ⊆ controlledCylinder δ) :
    ENNReal.ofReal ((metricScalarAt g x₀) ^ (-3 / 2 : ℝ)) *
      ENNReal.ofReal ((1 - δ) ^ (3 / 2 : ℝ)) *
        riemannianVolumeMeasure IC (bufferedCylinder δ)
          ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (bufferedCylinder δ)) S ≤
      riemannianVolumeMeasure I M g (d.map '' S) := by
  let g₀ := (roundCylinderMetric (E := E3) (n := 2)).restrictOpen (bufferedCylinder δ)
  have hpos : 0 < 1 - δ := sub_pos.mpr d.precision_lt_one
  have hinner (q : bufferedCylinder δ) (hq : q ∈ S) (v : TangentSpace IC q) :
      (scaleMetric (1 - δ) hpos g₀).inner q v v ≤ 1 * d.normalizedMetric.inner q v v := by
    rw [scaleMetric_inner, one_mul]
    exact (inner_bounds_of_metricDerivENormSupOn_lt g₀ d.normalizedMetric
      d.normalizedMetric_error_lt (hcontrol hq) v).1
  have hb := DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_apply_le_of_inner_le
    d.normalizedMetric (scaleMetric (1 - δ) hpos g₀) zero_lt_one hS hinner
  rw [volume_scale_apply] at hb
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = 3 := by simp
  rw [hdim, sqrt_cube_eq_rpow (1 - δ) hpos.le] at hb
  simp only [one_pow, Real.sqrt_one, ENNReal.ofReal_one, one_mul] at hb
  rw [volume_image_eq d hS, sqrt_cube_eq_rpow _ (inv_nonneg.mpr d.scalar_pos.le)]
  have hscale : (metricScalarAt g x₀)⁻¹ ^ (3 / 2 : ℝ) =
      (metricScalarAt g x₀) ^ (-3 / 2 : ℝ) := by
    rw [← Real.rpow_neg_eq_inv_rpow]
    congr 1
    ring
  rw [hscale, mul_assoc]
  exact mul_le_mul' le_rfl hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.volume_image_ge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.volume_image_ge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.volume_image_ge ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.volume_image_ge

end normalizedDatum
end DifferentialGeometry.Geometry.Neck
