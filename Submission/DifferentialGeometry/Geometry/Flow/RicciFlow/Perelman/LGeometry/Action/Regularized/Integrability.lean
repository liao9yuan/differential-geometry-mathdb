import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Chart.H1
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Chart.KineticEnergy
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Defs
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Compactness.Scalar
import Submission.DifferentialGeometry.Topology.Manifold.CurveChart.Subdivision
import Submission.DifferentialGeometry.Geometry.Metric.Comparison.CurveEnergy

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Bundle _root_.Submission.Bundle _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Topology

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

universe u uE uH

section

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [UniformSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
variable {D : RealTimeInterval}

theorem intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a b : Real) (hab : a ≤ b) (alpha : Real → M)
    (halpha : ContMDiffOn (modelWithCornersSelf Real Real) I 1 alpha (_root_.Set.Icc a b))
    (hreg : ∀ s ∈ _root_.Set.Icc a b, T - s ^ 2 ∈ D.regular) :
    IntervalIntegrable (lRegularizedLagrangian S T alpha) _root_.MeasureTheory.MeasureSpace.volume a b := by
  classical
  obtain ⟨t, ht0, htmono, ⟨m, hm⟩, hchart⟩ :=
    DifferentialGeometry.Geometry.exists_chart_subdivision (H := H) hab halpha.continuousOn
  have hseg (n : Nat) : (t n : Real) ≤ t (n + 1) :=
    htmono (Nat.le_succ n)
  have hkinPiece (n : Nat) : IntervalIntegrable
      (fun s ↦ (1 / 2 : Real) *
        (S.base.metric (T - s ^ 2)).inner (alpha s)
          (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s))
      volume (t n) (t (n + 1)) := by
    obtain ⟨p, hsrc⟩ := hchart n
    have hshift : _root_.Set.MapsTo (fun r : Real ↦ (t n : Real) + r)
        (_root_.Set.Icc (0 : Real) ((t (n + 1) : Real) - t n)) (_root_.Set.Icc a b) := by
      intro r hr
      exact ⟨by linarith [(t n).property.1, hr.1],
        by linarith [hr.2, (t (n + 1)).property.2]⟩
    have hshiftPiece : _root_.Set.MapsTo (fun r : Real ↦ (t n : Real) + r)
        (_root_.Set.Icc (0 : Real) ((t (n + 1) : Real) - t n))
        (_root_.Set.Icc (t n : Real) (t (n + 1) : Real)) := by
      intro r hr
      exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
    have hlocalMD : ContMDiffOn (modelWithCornersSelf Real Real) I 1
        (fun r : Real ↦ alpha ((t n : Real) + r))
        (_root_.Set.Icc (0 : Real) ((t (n + 1) : Real) - t n)) :=
      halpha.comp (contMDiff_const.add contMDiff_id).contMDiffOn hshift
    have hlocalSource : _root_.Set.MapsTo (fun r : Real ↦ alpha ((t n : Real) + r))
        (_root_.Set.Icc (0 : Real) ((t (n + 1) : Real) - t n))
        (chartAt H p).source :=
      hsrc.comp hshiftPiece
    let us : timeH1 E ((t (n + 1) : Real) - t n) :=
      chartTimeH1 I (sub_nonneg.mpr (hseg n)) p
        (fun r : Real ↦ alpha ((t n : Real) + r)) hlocalMD hlocalSource
    have hrep : _root_.Set.EqOn us.toFun
        (fun r ↦ extChartAt I p (alpha ((t n : Real) + r)))
        (_root_.Set.Icc (0 : Real) ((t (n + 1) : Real) - t n)) := by
      with_unfolding_all
        exact chartTimeH1_toFun I (sub_nonneg.mpr (hseg n)) p
          (fun r : Real ↦ alpha ((t n : Real) + r)) hlocalMD hlocalSource
    exact intervalIntegrable_lKinetic_of_chartH1 S hMet T alpha p (t n) (t (n + 1))
      (hseg n) us hsrc hrep fun s hs ↦
        hreg s ⟨(t n).property.1.trans hs.1,
          hs.2.trans (t (n + 1)).property.2⟩
  have hkin : IntervalIntegrable
      (fun s ↦ (1 / 2 : Real) *
        (S.base.metric (T - s ^ 2)).inner (alpha s)
          (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s))
      volume a b := by
    have ht0' : (t 0 : Real) = a := by
      simpa only using congrArg Subtype.val ht0
    have htm' : (t m : Real) = b := by
      simpa only using congrArg Subtype.val (hm m le_rfl)
    have hchain := IntervalIntegrable.trans_iterate
      (n := m) fun k _hk ↦ hkinPiece k
    simpa only [ht0', htm'] using hchain
  have hcarrier : ∀ s ∈ _root_.Set.uIcc a b, T - s ^ 2 ∈ D.carrier := by
    intro s hs
    exact D.regular_subset (hreg s (by simpa only [_root_.Set.uIcc_of_le hab] using hs))
  have hpot : IntervalIntegrable
      (fun s ↦ 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s))
      volume a b :=
    lScalar_int (I := I) S hSc T a b alpha hcarrier (by
      simpa only [_root_.Set.uIcc_of_le hab] using halpha.continuousOn)
  with_unfolding_all exact hkin.add hpot

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one

theorem intervalIntegrable_lRegularizedSpeedSq_of_contMDiffOn_one
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a b : Real) (hab : a ≤ b) (alpha : Real → M)
    (halpha : ContMDiffOn (modelWithCornersSelf Real Real) I 1 alpha (_root_.Set.Icc a b))
    (hreg : ∀ s ∈ _root_.Set.Icc a b, T - s ^ 2 ∈ D.regular) :
    IntervalIntegrable (lRegularizedSpeedSq S T alpha) _root_.MeasureTheory.MeasureSpace.volume a b := by
  have hLag := intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one
    (I := I) S hMet hSc T a b hab alpha halpha hreg
  have hcarrier : ∀ s ∈ _root_.Set.uIcc a b, T - s ^ 2 ∈ D.carrier := by
    intro s hs
    exact D.regular_subset (hreg s (by simpa only [_root_.Set.uIcc_of_le hab] using hs))
  have hpot : IntervalIntegrable
      (fun s ↦ 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s)) _root_.MeasureTheory.MeasureSpace.volume a b :=
    lScalar_int (I := I) S hSc T a b alpha hcarrier (by
      simpa only [_root_.Set.uIcc_of_le hab] using halpha.continuousOn)
  have hhalf : IntervalIntegrable
      (fun s ↦ (1 / 2 : Real) * lRegularizedSpeedSq S T alpha s) _root_.MeasureTheory.MeasureSpace.volume a b := by
    change IntervalIntegrable (fun s ↦ (1 / 2 : Real) *
      (S.base.metric (T - s ^ 2)).inner (alpha s)
        (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s)) _root_.MeasureTheory.MeasureSpace.volume a b
    rw [show (fun s ↦ (1 / 2 : Real) *
        (S.base.metric (T - s ^ 2)).inner (alpha s)
          (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s)) =
      (fun s ↦ lRegularizedLagrangian S T alpha s -
        2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s)) by
      funext s
      simp only [lRegularizedLagrangian]
      ring]
    exact hLag.sub hpot
  have htwice := hhalf.const_mul 2
  convert htwice using 1
  funext s
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.intervalIntegrable_lRegularizedSpeedSq_of_contMDiffOn_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.intervalIntegrable_lRegularizedSpeedSq_of_contMDiffOn_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.intervalIntegrable_lRegularizedSpeedSq_of_contMDiffOn_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.intervalIntegrable_lRegularizedSpeedSq_of_contMDiffOn_one

end

section

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem integrableOn_riemannianMetric_inner_lVelocity_self_of_contMDiff_one
    (g : SmoothRiemannianMetric I M) (alpha : Real → M)
    (halpha : ContMDiff (modelWithCornersSelf Real Real) I 1 alpha)
    (a b : Real) :
    _root_.MeasureTheory.IntegrableOn
      (fun s ↦ g.inner (alpha s) (lVelocity (I := I) alpha s)
        (lVelocity (I := I) alpha s)) (_root_.Set.Icc a b) :=
  Geometry.Riemannian.integrableOn_inner_mfderiv_self_of_contMDiffOn g halpha.contMDiffOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.integrableOn_riemannianMetric_inner_lVelocity_self_of_contMDiff_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.integrableOn_riemannianMetric_inner_lVelocity_self_of_contMDiff_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.integrableOn_riemannianMetric_inner_lVelocity_self_of_contMDiff_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.integrableOn_riemannianMetric_inner_lVelocity_self_of_contMDiff_one

end

end DifferentialGeometry.PDE.RicciFlow.Perelman
