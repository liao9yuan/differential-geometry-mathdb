import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCylinderLimitRicci
import Submission.DifferentialGeometry.Geometry.Metric.DistancePullback
import Submission.DifferentialGeometry.Geometry.Metric.Distance.Ball

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E3 target :: scope.openDecls } }

theorem PartialStandardSolution.riemannianEDistOf_le_initial
    (S : PartialStandardSolution) {t : ℝ} (ht : t ∈ S.domain) (x y : E3) :
    riemannianEDistOf (S.metric t) x y ≤ riemannianEDistOf StandardCap.metric x y := by
  have htime := (mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos t).mp ht
  have hslab : _root_.Set.Icc 0 t ⊆ S.domain :=
    (Icc_subset_lifetimeInterval_iff S.lifetime S.lifetime_pos t htime.1).mpr htime.2
  have hreg : _root_.Set.Ioo 0 t ⊆ (lifetimeInterval S.lifetime S.lifetime_pos).regular := by
    intro s hs
    exact (mem_lifetimeInterval_regular S.lifetime S.lifetime_pos s).mpr
      ⟨hs.1, (ENNReal.ofReal_le_ofReal hs.2.le).trans_lt htime.2⟩
  have hquad : ∀ z : E3, ∀ v : TangentSpace (𝓡 3) z,
      (S.metric t).inner z v v ≤ (1 : ℝ) * StandardCap.metric.inner z v v := by
    intro z v
    have hanti := Perelman.CanonicalNeighborhood.metric_inner_antitoneOn_of_ricci_nonnegative_interior
      S.toSolutionOn S.isSolutionOn hslab hreg (fun s hs z v => by
        change 0 ≤ metricRicciAt (S.metric s) z (vec2 v v)
        rw [metricRicciAt_apply_eq_ricciTensor]
        exact S.ricciTensor_nonnegative s (hslab ⟨hs.1.le, hs.2.le⟩) z v) z v
    have hh := hanti ⟨le_rfl, htime.1⟩ ⟨htime.1, le_rfl⟩ htime.1
    simpa only [PartialStandardSolution.toSolutionOn_metric, S.initial, one_mul] using hh
  have h := edistOf_le_of_quad StandardCap.metric (S.metric t) zero_lt_one hquad x y
  simpa only [Real.sqrt_one, ENNReal.ofReal_one, one_mul] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.riemannianEDistOf_le_initial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.riemannianEDistOf_le_initial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.riemannianEDistOf_le_initial ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.riemannianEDistOf_le_initial

theorem PartialStandardSolution.euclidean_ball_subset_riemannianBallOf
    (S : PartialStandardSolution) {t : ℝ} (ht : t ∈ S.domain) (p x : E3) {R : ℝ}
    (hx : ‖x‖ ≤ R) :
    Metric.ball p 1 ⊆ riemannianBallOf (S.metric t) x (R + ‖p‖ + 1) := by
  intro y hy
  have hdist : _root_.Dist.dist y p < 1 := hy
  have hxy : _root_.Dist.dist x y < R + ‖p‖ + 1 := by
    have htri := dist_triangle x p y
    have hxp : _root_.Dist.dist x p ≤ ‖x‖ + ‖p‖ := dist_le_norm_add_norm x p
    rw [dist_comm p y] at htri
    linarith
  have h := (S.riemannianEDistOf_le_initial ht x y).trans (StandardCap.edist_le_euclidean x y)
  exact h.trans_lt (by rw [edist_dist]; exact (ENNReal.ofReal_lt_ofReal_iff (by have hR : 0 ≤ R := (norm_nonneg x).trans hx; positivity : 0 < R + ‖p‖ + 1)).mpr hxy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.euclidean_ball_subset_riemannianBallOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.euclidean_ball_subset_riemannianBallOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.euclidean_ball_subset_riemannianBallOf ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.euclidean_ball_subset_riemannianBallOf

end DifferentialGeometry.PDE.RicciFlow
