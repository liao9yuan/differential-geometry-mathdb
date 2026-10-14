import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedLengthHeatTest
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.W.Potential.Viscosity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Geometry.Connection _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Entropy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData (I := I) ancientTimeInterval)
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem ancient_perelmanDensity_upper_test_in_chart
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p a : F.M)
    {z : ℝ × E} (hz : z ∈ _root_.Set.Ioi 0 ×ˢ (extChartAt I a).target)
    (phi : ℝ × E → ℝ) (hphi : ContDiffAt ℝ 2 phi z) :
    let u := fun w : ℝ × E => perelmanDensity (Module.finrank ℝ E) w.1
      (fun x => redLength F.S 0 p x w.1) ((extChartAt I a).symm w.2)
    IsLocalMax (fun w => u w - phi w) z →
      fderiv ℝ phi z (1, 0) -
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramOnE (F.S.base.metric (-z.1)) a i j z.2 *
            (fderiv ℝ (fderiv ℝ phi) z (0, chartModelBasis E i) (0, chartModelBasis E j) -
              ∑ k : Fin (Module.finrank ℝ E),
                chartChristoffel (F.S.base.metric (-z.1)) a i j k z.2 *
                  fderiv ℝ phi z (0, chartModelBasis E k))) +
        F.S.scalar (-z.1) ((extChartAt I a).symm z.2) * u z ≤ 0 := by
  let n := Module.finrank ℝ E
  let f := fun w : ℝ × E => redLength F.S 0 p ((extChartAt I a).symm w.2) w.1
  let A := fun i j => chartInvGramOnE (I := I) (F.S.base.metric (-z.1)) a i j z.2
  let B := fun i j k => chartChristoffel (I := I) (F.S.base.metric (-z.1)) a i j k z.2
  let d : E := ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, (A i j * B i j k) • chartModelBasis E k
  have htime : 0 < z.1 := hz.1
  have hD (P : (ℝ × E) →L[ℝ] ℝ) : P (1, d) = P (1, 0) +
      ∑ i : Fin n, ∑ j : Fin n, A i j * ∑ k : Fin n, B i j k * P (0, chartModelBasis E k) := by
    have heq : ((1 : ℝ), d) = (1, (0 : E)) + (0, d) := by ext <;> simp
    rw [heq, map_add]
    change P (1, 0) + P ((ContinuousLinearMap.inr ℝ ℝ E) d) = _
    simp only [d, map_sum, map_smul, smul_eq_mul, ContinuousLinearMap.inr_apply, Finset.mul_sum, mul_assoc]
  have hop (P : (ℝ × E) →L[ℝ] ℝ) (C : (ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] ℝ) :
      P (1, d) - (∑ i : Fin n, ∑ j : Fin n, A i j * C (0, chartModelBasis E i) (0, chartModelBasis E j)) =
        P (1, 0) - ∑ i : Fin n, ∑ j : Fin n, A i j *
          (C (0, chartModelBasis E i) (0, chartModelBasis E j) -
            ∑ k : Fin n, B i j k * P (0, chartModelBasis E k)) := by
    rw [hD]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  have hquad (P : (ℝ × E) →L[ℝ] ℝ) :
      (∑ i : Fin n, ∑ j : Fin n, A i j * P (0, chartModelBasis E i) * P (0, chartModelBasis E j)) =
        ∑ i : Fin n, ∑ j : Fin n, A i j * P (0, chartModelBasis E j) * P (0, chartModelBasis E i) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  dsimp only
  intro hmax
  have hh := perelmanDensity_upper_test_of_conjugate_heat_lower_test n f htime d
    (chartModelBasis E) A (F.S.scalar (-z.1) ((extChartAt I a).symm z.2))
    (fun psi hpsi hmin => ?_) phi hphi hmax
  · rw [hop] at hh
    exact hh
  · have hq : (extChartAt I a).symm z.2 ∈ (chartAt H a).source := by
      simpa only [extChartAt_source] using (extChartAt I a).map_target hz.2
    have he : extChartAt I a ((extChartAt I a).symm z.2) = z.2 :=
      (extChartAt I a).right_inv hz.2
    have hp : (z.1, extChartAt I a ((extChartAt I a).symm z.2)) = z := by
      rw [he]
    have h := ancient_redLength_conjugate_heat_lower_test_in_chart F hF htime p a
      ((extChartAt I a).symm z.2) hq psi (hp.symm ▸ hpsi) (hp.symm ▸ hmin)
    rw [hop, hquad]
    simpa only [he, Prod.eta] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_perelmanDensity_upper_test_in_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_perelmanDensity_upper_test_in_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_perelmanDensity_upper_test_in_chart ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_perelmanDensity_upper_test_in_chart

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
