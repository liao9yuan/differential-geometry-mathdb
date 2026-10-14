import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.LocalFlowInjectivity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointLocalCurvature

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Set _root_.Submission.Set _root_.Filter
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem nonempty_poleEndpointRescaledFlowSeq_baseInjBound
    (hcar : D.carrier = _root_.Set.Iic 0) (hreg : D.regular = _root_.Set.Iio 0)
    (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
    (hsigma : ∀ i, 0 < tau i + b) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F)
    (hancient : ∀ i, IsAncientKappaSolution kappa
      ((poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i))
    (p : F.M) {A : ℝ}
    (hbase : ∀ i, redLength
      ((poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma).term i).S 0 p (q i) 1 ≤ A) :
    Nonempty (FlowScaleInjectivityBound (I := I)
      (poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma)) := by
  obtain ⟨C, hC, hlocal⟩ := exists_poleEndpointRescaledFlowSeq_local_curvature_bound
    F hcar hreg b hbmem tau q hsigma (fun _ => kappa) hancient p hbase 1 zero_le_one
  let Y := poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
  apply nonempty_flowScaleInjectivityBound_of_noncollapsed_unit_curvature Y
    (by change (0 : ℝ) ≤ 0; exact le_rfl) hF.kappa_pos hC
    (fun _ => hF.connected)
    (fun i => poleEndpointRescaledFlowSeq_noncollapsed F hcar hreg b hbmem
      tau q hsigma kappa hF.noncollapsed i)
    (fun i => poleEndpointRescaledFlowSeq_nonnegativeCurvatureOperator F hcar hreg b hbmem
      tau q hsigma hF.nonnegativeCurvatureOperator i le_rfl)
  intro i x hx
  apply hlocal i 0 le_rfl x
  convert hx.le using 1 <;> rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nonempty_poleEndpointRescaledFlowSeq_baseInjBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nonempty_poleEndpointRescaledFlowSeq_baseInjBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nonempty_poleEndpointRescaledFlowSeq_baseInjBound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.nonempty_poleEndpointRescaledFlowSeq_baseInjBound

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
