import Submission.DifferentialGeometry.Geometry.Comparison.CheegerGromovTaylor.InjectivityRadius.Basic
import Submission.DifferentialGeometry.Geometry.Comparison.Volume.Segment.Ball.EuclideanUpper
import Submission.DifferentialGeometry.Geometry.Exponential.Intrinsic.Framed.Coordinates
import Submission.DifferentialGeometry.Geometry.Exponential.Intrinsic.Framed.Jacobi

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Function _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Metric _root_.Set
open scoped _root_.ENNReal _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Variation
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [CompleteSpace E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (↑(⊤ : ℕ∞) : WithTop ℕ∞) M]
  [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] [ConnectedSpace M]

private local instance _root_.Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

theorem intrinsicInj_ge_vol
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) {K R r₀ s q : Real} {v : ENNReal}
    (hK : 0 < K) (hR : 0 < R)
    (hRpi : R ≤ Real.pi / Real.sqrt K)
    (hRmBall :
      ∀ y : M, y ∈ Metric.eball p (ENNReal.ofReal (3 * R / 4)) →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          y 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g y)) ≤ K)
    (hloc :
      IsLocalDiffeomorphOn (modelWithCornersSelf Real E) I
        (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (intrinsicFramedExp (I := I) g hEnorm p)
        (_root_.Metric.ball (0 : E) R))
    (hr₀ : 0 < r₀) (hs : 0 < s)
    (hfit : r₀ + 2 * s < R) (hquarter : r₀ < R / 4)
    (hq : 0 ≤ q)
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2)))
    (hvol : v ≤ riemannianVolumeMeasure (I := I) (M := M) g
      {y : M | _root_.Manifold.riemannianEDist I p y < ENNReal.ofReal s}) :
    ENNReal.ofReal (r₀ / 2) * v /
        (((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure
            (EuclideanSpace Real (Fin (Module.finrank Real E)))).toSphere Set.univ) *
          ENNReal.ofReal (hyperbolicRadialVolume q (Module.finrank Real E - 1) s) +
        (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).toSphere Set.univ *
          ENNReal.ofReal (hyperbolicRadialVolume q (Module.finrank Real E - 1) (r₀ + s)))
      ≤ intrinsicInjRadius (I := I) g hEnorm p := by
  classical
  let V : ENNReal :=
    riemannianVolumeMeasure (I := I) (M := M) g
      {y : M | _root_.Manifold.riemannianEDist I p y < ENNReal.ofReal s}
  let P : ENNReal := intrinsicPullVol (I := I) g hEnorm p (r₀ + s)
  let D : ENNReal :=
    ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure
        (EuclideanSpace Real (Fin (Module.finrank Real E)))).toSphere Set.univ) *
      ENNReal.ofReal (hyperbolicRadialVolume q (Module.finrank Real E - 1) s) +
    (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).toSphere Set.univ *
      ENNReal.ofReal (hyperbolicRadialVolume q (Module.finrank Real E - 1) (r₀ + s))
  have hRm :
      ∀ z : E, ‖z‖ < 3 * R / 4 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (intrinsicFramedExp (I := I) g hEnorm p z) 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K := by
    intro z hz
    exact hRmBall _ (intrinsicFrame_mem_eball (I := I) g hEnorm p hz)
  have hno : ∀ z, z ∈ _root_.Metric.ball (0 : E) (r₀ + s) → z ≠ 0 →
      ∀ t, t ∈ _root_.Set.Ioo (0 : Real) 1 →
        ¬ IsConjVec (I := I) g hEnorm p
          ((t • normalFrame (I := I) g p z : TangentSpace I p) : E) := by
    intro z hz hz0 t ht
    have htz : t • z ∈ _root_.Metric.ball (0 : E) R := by
      rw [Metric.mem_ball, dist_zero_right] at hz ⊢
      rw [norm_smul, Real.norm_of_nonneg ht.1.le]
      calc
        t * ‖z‖ < 1 * ‖z‖ :=
          mul_lt_mul_of_pos_right ht.2 (norm_pos_iff.mpr hz0)
        _ = ‖z‖ := one_mul _
        _ < r₀ + s := hz
        _ < R := by linarith
    have hraw := framedExp_not_conj (I := I) g hEnorm p (t • z)
      (hloc ⟨t • z, htz⟩)
    simpa only [map_smul] using hraw
  have hvolV : v ≤ V := by
    simpa only [V] using hvol
  have hV :
      V ≤ ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure
          (EuclideanSpace Real (Fin (Module.finrank Real E)))).toSphere Set.univ) *
        ENNReal.ofReal (hyperbolicRadialVolume q (Module.finrank Real E - 1) s) := by
    simpa only [V] using
      (segmentBall_vol_le_euclidean (I := I) g hEnorm p hq hs hRic)
  have hP :
      P ≤ (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).toSphere Set.univ *
        ENNReal.ofReal
          (hyperbolicRadialVolume q (Module.finrank Real E - 1) (r₀ + s)) := by
    simpa only [P] using
      (intrinsicPullVol_le_hyperbolic (I := I) g hEnorm p hq
        (add_pos hr₀ hs) hno hRic)
  have hDen : V + P ≤ D := by
    simpa only [D] using add_le_add hV hP
  have hcgt :
      ENNReal.ofReal (r₀ / 2) * V / (V + P) ≤
        intrinsicInjRadius (I := I) g hEnorm p := by
    simpa only [V, P] using
      (intrinsicInjRadius_ge_cheeger_gromov_taylor_on (I := I) (K := K) (R := R) (r₀ := r₀)
        (s := s) g hEnorm p hK hR hRpi hRm hloc hr₀ hfit hquarter)
  change ENNReal.ofReal (r₀ / 2) * v / D ≤
    intrinsicInjRadius (I := I) g hEnorm p
  exact
    (ENNReal.div_le_div
      (mul_le_mul_right hvolV (ENNReal.ofReal (r₀ / 2))) hDen).trans hcgt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.intrinsicInj_ge_vol then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.intrinsicInj_ge_vol"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.intrinsicInj_ge_vol ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.intrinsicInj_ge_vol

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
