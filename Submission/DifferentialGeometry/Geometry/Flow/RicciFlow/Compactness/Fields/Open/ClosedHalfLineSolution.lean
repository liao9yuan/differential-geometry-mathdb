import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.HalfLine
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.TimeLipschitz

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow _root_.Submission.DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedFlowSeq.{u, uE, uH} (I := I)}
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}

private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instCompleteSpace_differentialGeometry_1 : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instCompleteSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instCompleteSpace_differentialGeometry_1 target :: scope.openDecls } }

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem HalfLineMetricConvergenceData.isSolutionOn
    (Phi : PointedCGHMaps X P subseq) {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcarrier : X.D.carrier = _root_.Set.Iic 0) (hregular : _root_.Set.Iio 0 ⊆ X.D.regular) :
    IsSolutionOn ({ base := { metric := co.gInf } } : SolutionOn (I := I) (M := P.M) X.D) := by
  apply HalfLineMetricConvergenceData.isSolutionOn_of_time_lipschitz
    Phi co hcarrier hregular
  intro n K hK p
  apply Eventually.of_forall
  intro k
  have hn : -(↑(n + 1) : ℝ) < 0 := neg_neg_of_pos (by positivity)
  have hslab : _root_.Set.Icc (-(↑(n + 1) : ℝ)) 0 ⊆ X.D.carrier := by
    rw [hcarrier]
    exact _root_.Set.Icc_subset_Iic_self
  have hreg : _root_.Set.Ico (-(↑(n + 1) : ℝ)) 0 ⊆ X.D.regular :=
    Ico_subset_Iio_self.trans hregular
  obtain ⟨L, _, hL⟩ := exists_metric_extension_time_lipschitz_constant_on_closed_interval
    Phi R bf hsrc htgt hn hslab hreg k K hK p
  refine ⟨L, ?_⟩
  intro s hs t ht q hq x hx
  exact hL s ⟨by push_cast; linarith [hs.1], hs.2⟩
    t ⟨by push_cast; linarith [ht.1], ht.2⟩ q hq x hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.isSolutionOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.isSolutionOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.isSolutionOn ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.isSolutionOn

end DifferentialGeometry.CheegerGromovCompactness
