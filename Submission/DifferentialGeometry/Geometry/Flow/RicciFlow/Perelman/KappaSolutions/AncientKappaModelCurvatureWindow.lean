import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NormalizedKLimGeometry
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StandardHarnackLimit
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.GoodPointDerivatives

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle


theorem ancientKappa_modelCurvatureBoundNearBase (hdim : Module.finrank ℝ E = 3)
    {kappa : ℝ} (_hkappa : 0 < kappa) :
    ModelCurvatureBoundNearBase.{u, uE, uH} I kappa := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_normalized_klim_local_curvature_constants.{u, uE, uH} (I := I) hdim kappa
  refine ⟨Real.sqrt 3 * C 3, mul_nonneg (Real.sqrt_nonneg _) (hC 3).le, ?_⟩
  intro L hL hbase s hs y hy
  have hK : KLim kappa L := ancientKappaThree_toKLim L hL hdim
  have hb : L.S.scalar 0 L.basepoint = 1 := hbase
  have h := (hbound ancientTimeInterval L hK hb 3 y hy s hs.2).2
  calc L.rmNormSq (I := I) s y ≤ 3 * C 3 ^ 2 := h
    _ = (Real.sqrt 3 * C 3) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_modelCurvatureBoundNearBase then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_modelCurvatureBoundNearBase"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_modelCurvatureBoundNearBase ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_modelCurvatureBoundNearBase

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
