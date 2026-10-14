import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SeamTransition
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SumLaws

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Set _root_.Metric _root_.Submission.Metric _root_.Manifold _root_.Submission.Manifold _root_.Filter
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology

namespace DifferentialGeometry.Topology
open _root_.Submission.DifferentialGeometry.Topology.ConnectedSumQuotient
open _root_.Submission.DifferentialGeometry.Topology.OrientationAssembly

universe u

noncomputable section

namespace OrientationAssembly

variable {M : ClosedOrientedManifold.{u} 3}

def ballChartTangentEquiv (c : BallChart 3 (𝓡 3) M.Carrier) {x : csModel}
    (hx : x ∈ c.chart.source) :
    TangentSpace 𝓘(ℝ, csModel) x ≃L[ℝ] TangentSpace (𝓡 3) (c.chart x) :=
  IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv
    (PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ c.chart hx) (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.OrientationAssembly.ballChartTangentEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.OrientationAssembly.ballChartTangentEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.OrientationAssembly.ballChartTangentEquiv ``Submission.DifferentialGeometry.Topology.OrientationAssembly.ballChartTangentEquiv

end OrientationAssembly

variable {M M' : ClosedOrientedManifold.{u} 3} (c' : OrientedBallChart M')
    (Φ : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ M'.Carrier)

theorem mem_source_pullback {x : csModel}
    (hx : x ∈ (BallChart.pullback c'.toBallChart Φ).chart.source) :
    x ∈ c'.toBallChart.chart.source := by
  have h := hx
  rw [BallChart.pullback, PartialDiffeomorph.trans_toPartialEquiv,
    OpenPartialHomeomorph.trans_source] at h
  exact h.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.mem_source_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.mem_source_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.mem_source_pullback ``Submission.DifferentialGeometry.Topology.mem_source_pullback

namespace OrientationAssembly

theorem ballChartTangentEquiv_pullback {x : csModel}
    (hx : x ∈ (BallChart.pullback c'.toBallChart Φ).chart.source)
    (hx' : x ∈ c'.toBallChart.chart.source) :
    (ballChartTangentEquiv (BallChart.pullback c'.toBallChart Φ) hx).toLinearEquiv =
      (chartTangentEquiv c' hx').toLinearEquiv.trans
        (((Φ.symm).mfderivToContinuousLinearEquiv (by simp)
          (c'.toBallChart.chart x)).toLinearEquiv) := by
  have hcomp := mfderiv_comp (x := x)
    (f := (fun y : csModel => c'.toBallChart.chart y))
    (g := (fun y : M'.Carrier => Φ.symm y))
    ((Φ.symm).mdifferentiable (by simp) (c'.toBallChart.chart x))
    (PartialDiffeomorph.mdifferentiableAt c'.toBallChart.chart (by simp) hx')
  apply LinearEquiv.ext
  intro v
  change (mfderiv (𝓡 3) (𝓡 3)
      (fun y : csModel => Φ.symm (c'.toBallChart.chart y)) x) v =
    (mfderiv (𝓡 3) (𝓡 3) (fun y : M'.Carrier => Φ.symm y) (c'.toBallChart.chart x))
      ((mfderiv (𝓡 3) (𝓡 3) (fun y : csModel => c'.toBallChart.chart y) x) v)
  erw [DFunLike.congr_fun hcomp v]
  rw [ContinuousLinearMap.comp_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.OrientationAssembly.ballChartTangentEquiv_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.OrientationAssembly.ballChartTangentEquiv_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.OrientationAssembly.ballChartTangentEquiv_pullback ``Submission.DifferentialGeometry.Topology.OrientationAssembly.ballChartTangentEquiv_pullback

theorem ballChart_pullback_preserves_orientation
    (hΦ : Φ.preservesOrientation M.orientation M'.orientation) :
    ∀ x, ∀ hx : x ∈ (BallChart.pullback c'.toBallChart Φ).chart.source,
      Orientation.map (Fin 3)
        (ballChartTangentEquiv (BallChart.pullback c'.toBallChart Φ) hx).toLinearEquiv
        (_root_.Submission.OrientationAssembly.stdOrientation x) =
      M.orientation.orientation ((BallChart.pullback c'.toBallChart Φ).chart x) := by
  intro x hx
  have hx' := mem_source_pullback c' Φ hx
  have hchain := ballChartTangentEquiv_pullback c' Φ hx hx'
  have hsymm := Diffeomorph.preservesOrientation_symm hΦ
  have step1 : Orientation.map (Fin 3)
        (ballChartTangentEquiv (BallChart.pullback c'.toBallChart Φ) hx).toLinearEquiv
        (_root_.Submission.OrientationAssembly.stdOrientation x)
      = Orientation.map (Fin 3)
          ((chartTangentEquiv c' hx').toLinearEquiv.trans
            (((Φ.symm).mfderivToContinuousLinearEquiv (by simp)
              (c'.toBallChart.chart x)).toLinearEquiv))
          (_root_.Submission.OrientationAssembly.stdOrientation x) := by
        rw [hchain]
        rfl
  have step2 : Orientation.map (Fin 3)
          ((chartTangentEquiv c' hx').toLinearEquiv.trans
            (((Φ.symm).mfderivToContinuousLinearEquiv (by simp)
              (c'.toBallChart.chart x)).toLinearEquiv))
          (_root_.Submission.OrientationAssembly.stdOrientation x)
      = Orientation.map (Fin 3)
          ((Φ.symm).mfderivToContinuousLinearEquiv (by simp)
            (c'.toBallChart.chart x)).toLinearEquiv
          (Orientation.map (Fin 3) (chartTangentEquiv c' hx').toLinearEquiv
            (_root_.Submission.OrientationAssembly.stdOrientation x)) := by
        rw [← _root_.Submission.OrientationAssembly.orientation_map_map_trans (R := ℝ)
          (chartTangentEquiv c' hx').toLinearEquiv
          ((Φ.symm).mfderivToContinuousLinearEquiv (by simp) (c'.toBallChart.chart x)).toLinearEquiv
          (_root_.Submission.OrientationAssembly.stdOrientation x)]
  have step3 : Orientation.map (Fin 3)
          ((Φ.symm).mfderivToContinuousLinearEquiv (by simp)
            (c'.toBallChart.chart x)).toLinearEquiv
          (Orientation.map (Fin 3) (chartTangentEquiv c' hx').toLinearEquiv
            (_root_.Submission.OrientationAssembly.stdOrientation x))
      = Orientation.map (Fin 3)
          ((Φ.symm).mfderivToContinuousLinearEquiv (by simp)
            (c'.toBallChart.chart x)).toLinearEquiv
          (M'.orientation.orientation (c'.toBallChart.chart x)) := by
        rw [← _root_.Submission.OrientationAssembly.orientation_eq_map_chartTangentEquiv c' hx']
  have step4 : Orientation.map (Fin 3)
          ((Φ.symm).mfderivToContinuousLinearEquiv (by simp)
            (c'.toBallChart.chart x)).toLinearEquiv
          (M'.orientation.orientation (c'.toBallChart.chart x))
      = M.orientation.orientation (Φ.symm (c'.toBallChart.chart x)) :=
        hsymm (c'.toBallChart.chart x)
  have step5 : M.orientation.orientation (Φ.symm (c'.toBallChart.chart x))
      = M.orientation.orientation ((BallChart.pullback c'.toBallChart Φ).chart x) := by
        rw [BallChart.pullback_apply]
  exact step1.trans (step2.trans (step3.trans (step4.trans step5)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.OrientationAssembly.ballChart_pullback_preserves_orientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.OrientationAssembly.ballChart_pullback_preserves_orientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.OrientationAssembly.ballChart_pullback_preserves_orientation ``Submission.DifferentialGeometry.Topology.OrientationAssembly.ballChart_pullback_preserves_orientation

end OrientationAssembly

theorem exists_orientedBallChart_pullback_of_preservesOrientation
    (hΦ : Φ.preservesOrientation M.orientation M'.orientation) :
    ∃ c : OrientedBallChart M,
      ∀ x ∈ Metric.closedBall (0 : csModel) 2,
        Φ (c.toBallChart.chart x) = c'.toBallChart.chart x :=
  ⟨{ toBallChart := BallChart.pullback c'.toBallChart Φ
     preserves_orientation :=
       OrientationAssembly.ballChart_pullback_preserves_orientation c' Φ hΦ },
    fun x _ => BallChart.map_pullback c'.toBallChart Φ x⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_orientedBallChart_pullback_of_preservesOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_orientedBallChart_pullback_of_preservesOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_orientedBallChart_pullback_of_preservesOrientation ``Submission.DifferentialGeometry.Topology.exists_orientedBallChart_pullback_of_preservesOrientation

theorem orientedBallChartPullback : OrientedBallChartPullback.{u} :=
  fun Φ c' hΦ => exists_orientedBallChart_pullback_of_preservesOrientation c' Φ hΦ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.orientedBallChartPullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.orientedBallChartPullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.orientedBallChartPullback ``Submission.DifferentialGeometry.Topology.orientedBallChartPullback

end

end DifferentialGeometry.Topology
