import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.Perturbation.DeTurckNonlinearity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


open _root_.Submission.DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff _root_.NNReal _root_.ENNReal _root_.Topology _root_.BigOperators
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckRicciRHS_symm
    (g_bg g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    deTurckRicciRHS (I := I) g_bg g x v w =
      deTurckRicciRHS (I := I) g_bg g x w v := by
  simp only [deTurckRicciRHS, add_apply,
    smul_apply, smul_eq_mul, lieDerivMetricClm_apply]
  rw [ricciTensor_symm (I := I) (smoothRiemannianMetricToInfty (I := I) g) x v w,
    DeTurck.lieDerivMetric_isPointwiseSymm (I := I)
      (smoothRiemannianMetricToInfty (I := I) g)
      (DeTurck.deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g)
        (smoothRiemannianMetricToInfty (I := I) g_bg)) x v w]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS_symm ``Submission.DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS_symm

noncomputable def deTurckRHSSectionBackground (g_bg g : SmoothRiemannianMetric I M) :
    DifferentialGeometry.Integral.L2.SmoothCcTensor g_bg 0 2 where
  toSection := (deTurckRHSSection (I := I) g_bg g).toSection
  hasCompactSupport := (deTurckRHSSection (I := I) g_bg g).hasCompactSupport

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.deTurckRHSSectionBackground then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.deTurckRHSSectionBackground"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.deTurckRHSSectionBackground ``Submission.DifferentialGeometry.PDE.RicciFlow.deTurckRHSSectionBackground

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] theorem deTurckRHSSectionBackground_toSection
    (g_bg g : SmoothRiemannianMetric I M) :
    (deTurckRHSSectionBackground (I := I) g_bg g).toSection =
      (deTurckRHSSection (I := I) g_bg g).toSection := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.deTurckRHSSectionBackground_toSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.deTurckRHSSectionBackground_toSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.deTurckRHSSectionBackground_toSection ``Submission.DifferentialGeometry.PDE.RicciFlow.deTurckRHSSectionBackground_toSection

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckRHSSectionBackground_eval
    (g_bg g : SmoothRiemannianMetric I M) (x : M) (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.eval
        ((deTurckRHSSectionBackground (I := I) g_bg g).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v =
      deTurckRicciRHS (I := I) g_bg g x (v 0) (v 1) :=
  deTurckRHSSection_eval (I := I) g_bg g x v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.deTurckRHSSectionBackground_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.deTurckRHSSectionBackground_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.deTurckRHSSectionBackground_eval ``Submission.DifferentialGeometry.PDE.RicciFlow.deTurckRHSSectionBackground_eval

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckRHSSection_ccTensorBilinSymm_eq_deTurckRicciRHS
    (g_bg g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g_bg (deTurckRHSSectionBackground (I := I) g_bg g) x v w =
      deTurckRicciRHS (I := I) g_bg g x v w := by
  rw [ccTensorBilinSymm_apply]
  rw [ccTensorBilin_apply, ccTensorBilin_apply]
  unfold ccTensorModel
  rw [ccTensorMultilinear_apply]
  change (1 / 2 : ℝ) *
    (Tensor0SSpace.eval
        ((deTurckRHSSectionBackground (I := I) g_bg g).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![v, w] +
      Tensor0SSpace.eval
        ((deTurckRHSSectionBackground (I := I) g_bg g).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![w, v]) = _
  rw [deTurckRHSSectionBackground_eval, deTurckRHSSectionBackground_eval]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [deTurckRicciRHS_symm (I := I) g_bg g x w v]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.deTurckRHSSection_ccTensorBilinSymm_eq_deTurckRicciRHS then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.deTurckRHSSection_ccTensorBilinSymm_eq_deTurckRicciRHS"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.deTurckRHSSection_ccTensorBilinSymm_eq_deTurckRicciRHS ``Submission.DifferentialGeometry.PDE.RicciFlow.deTurckRHSSection_ccTensorBilinSymm_eq_deTurckRicciRHS

end DifferentialGeometry.PDE.RicciFlow
