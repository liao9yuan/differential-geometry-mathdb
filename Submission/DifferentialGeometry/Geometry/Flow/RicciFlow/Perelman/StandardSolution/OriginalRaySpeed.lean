import Submission.DifferentialGeometry.Analysis.Parabolic.Scaling.ScaledSpeed
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.FixedBallScalarGradient
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.SpeedBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.SmoothExtension
import Mathlib.Analysis.Complex.Exponential
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.ExponentialMap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow

def originalRaySpeedEpsilon (n : ℕ) : ℝ :=
  _root_.Min.min (1 / 100 : ℝ)
    (1 / (16 * (1 + 2 * fixedBallScalarGradientConstant n + 4 * (n : ℝ) ^ 2) ^ 2))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.originalRaySpeedEpsilon then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.originalRaySpeedEpsilon"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.originalRaySpeedEpsilon ``Submission.DifferentialGeometry.PDE.RicciFlow.originalRaySpeedEpsilon

theorem originalRaySpeedEpsilon_pos (n : ℕ) : 0 < originalRaySpeedEpsilon n := by
  have hA := fixedBallScalarGradientConstant_nonneg n
  unfold originalRaySpeedEpsilon
  apply lt_min
  · norm_num
  · positivity

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.originalRaySpeedEpsilon_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.originalRaySpeedEpsilon_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.originalRaySpeedEpsilon_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.originalRaySpeedEpsilon_pos

private theorem scaled_ray_derivative_bound
    (r A N q U G Q : ℝ) (hr : 0 < r) (hq : 0 ≤ q)
    (hG : |G| ≤ (A / r ^ 3) * Real.sqrt U)
    (hQ : |Q| ≤ (N / r ^ 2) * U) :
    |r * (4 * (r * q) ^ 2 * G - 4 * (r * q) * Q)| ≤
      4 * A * q ^ 2 * Real.sqrt U + 4 * N * q * U := by
  have hrs : 0 ≤ r * q := mul_nonneg hr.le hq
  have hraw : |4 * (r * q) ^ 2 * G - 4 * (r * q) * Q| ≤
      4 * (r * q) ^ 2 * |G| + 4 * (r * q) * |Q| := by
    apply (abs_sub _ _).trans_eq
    simp only [abs_mul, abs_of_nonneg hrs,
      abs_of_nonneg (sq_nonneg (r * q))]
    norm_num
  have hcoeff : 4 * (r * q) ^ 2 * |G| + 4 * (r * q) * |Q| ≤
      4 * (r * q) ^ 2 * ((A / r ^ 3) * Real.sqrt U) +
        4 * (r * q) * ((N / r ^ 2) * U) :=
    add_le_add (mul_le_mul_of_nonneg_left hG (by positivity))
      (mul_le_mul_of_nonneg_left hQ (by positivity))
  rw [abs_mul, abs_of_pos hr]
  calc
    _ ≤ r * (4 * (r * q) ^ 2 * ((A / r ^ 3) * Real.sqrt U) +
        4 * (r * q) * ((N / r ^ 2) * U)) :=
      mul_le_mul_of_nonneg_left (hraw.trans hcoeff) hr.le
    _ = _ := by field_simp [hr.ne']

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.scaled_ray_derivative_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.scaled_ray_derivative_bound target :: scope.openDecls } }

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

theorem lRegCurve_speedSq_le_of_local_bounds
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (p : M) (Z : TangentSpace I p)
    (r : ℝ) (hr : 0 < r) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon ≤ originalRaySpeedEpsilon (Module.finrank ℝ E))
    (b : ℝ) (hb : 0 < b) (hbscale : b ≤ Real.sqrt epsilon * r)
    (hdom : b ∈ lRegularizedDomain S T p Z)
    (hZ : Real.sqrt ((S.base.metric T).inner p Z Z) ≤
      1 / (10 * Real.sqrt epsilon))
    (hgrad : ∀ s ∈ _root_.Set.Icc (0 : ℝ) b,
      |(S.base.metric (T - s ^ 2)).inner (lRegularizedCurve S T p Z s)
        (gradientFun (I := I) (S.base.metric (T - s ^ 2))
          (S.scalar (T - s ^ 2)) (lRegularizedCurve S T p Z s))
        (lVelocity (I := I) (lRegularizedCurve S T p Z) s)| ≤
      (fixedBallScalarGradientConstant (Module.finrank ℝ E) / r ^ 3) *
        Real.sqrt (lRegularizedSpeedSq S T (lRegularizedCurve S T p Z) s))
    (hric : ∀ s ∈ _root_.Set.Icc (0 : ℝ) b,
      |S.ricciAt (T - s ^ 2) (lRegularizedCurve S T p Z s)
        (vec2 (lVelocity (I := I) (lRegularizedCurve S T p Z) s)
          (lVelocity (I := I) (lRegularizedCurve S T p Z) s))| ≤
      ((Module.finrank ℝ E : ℝ) ^ 2 / r ^ 2) *
        lRegularizedSpeedSq S T (lRegularizedCurve S T p Z) s) :
    ∀ s ∈ _root_.Set.Icc (0 : ℝ) b,
      lRegularizedSpeedSq S T (lRegularizedCurve S T p Z) s ≤ 1 / (15 * epsilon) := by
  let alpha : ℝ → M := lRegularizedCurve S T p Z
  let U : ℝ → ℝ := lRegularizedSpeedSq S T alpha
  let G : ℝ → ℝ := fun s ↦
    (S.base.metric (T - s ^ 2)).inner (alpha s)
      (gradientFun (I := I) (S.base.metric (T - s ^ 2))
        (S.scalar (T - s ^ 2)) (alpha s)) (lVelocity (I := I) alpha s)
  let Q : ℝ → ℝ := fun s ↦ S.ricciAt (T - s ^ 2) (alpha s)
    (vec2 (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s))
  let F : ℝ → ℝ := fun q ↦ U (r * q)
  let F' : ℝ → ℝ := fun q ↦ r * (4 * (r * q) ^ 2 * G (r * q) - 4 * (r * q) * Q (r * q))
  let L : ℝ := b / r
  have hL : 0 ≤ L := div_nonneg hb.le hr.le
  have hLscale : L ≤ Real.sqrt epsilon := (div_le_iff₀ hr).mpr hbscale
  have hclock (q : ℝ) (hq : q ∈ _root_.Set.Icc (0 : ℝ) L) : r * q ∈ _root_.Set.Icc (0 : ℝ) b := by
    refine ⟨mul_nonneg hr.le hq.1, ?_⟩
    have h := (le_div_iff₀ hr).mp hq.2
    simpa only [mul_comm] using h
  have hreg := lRegularizedCurve_isLRegularizedCurveOn S hS T p Z hb hdom
  have hF (q : ℝ) (_hq : q ∈ _root_.Set.Icc (0 : ℝ) L) : 0 ≤ F q :=
    lRegularizedSpeedSq_nonneg S T alpha (r * q)
  have hFderiv (q : ℝ) (hq : q ∈ _root_.Set.Icc (0 : ℝ) L) : HasDerivAt F (F' q) q := by
    have hUderiv := hasDerivAt_lRegularizedSpeedSq S hS T hreg
      (by simpa only [_root_.Set.uIcc_of_le hb.le] using hclock q hq)
    exact (hUderiv.comp q (hasDerivAt_const_mul r)).congr_deriv (mul_comm _ _)
  have hFbound (q : ℝ) (hq : q ∈ _root_.Set.Icc (0 : ℝ) L) :
      |F' q| ≤ 4 * fixedBallScalarGradientConstant (Module.finrank ℝ E) * q ^ 2 *
        Real.sqrt (F q) + 4 * (Module.finrank ℝ E : ℝ) ^ 2 * q * F q := by
    exact scaled_ray_derivative_bound r (fixedBallScalarGradientConstant (Module.finrank ℝ E))
      ((Module.finrank ℝ E : ℝ) ^ 2) q (F q) (G (r * q)) (Q (r * q)) hr hq.1
      (hgrad (r * q) (hclock q hq)) (hric (r * q) (hclock q hq))
  have hT : T ∈ D.regular := by
    have hzero := lRegularizedDomain_segment S T p Z hdom le_rfl hb.le
    simpa using lRegularizedDomain_regularity S T p Z hzero
  have hU0 : U 0 = 4 * (S.base.metric T).inner p Z Z := by
    dsimp only [U, alpha, lRegularizedSpeedSq]
    norm_num only [zero_pow, sub_zero]
    rw [lRegularizedCurve_zero, lRegularizedCurve_velocity_zero S hS T p Z hT]
    rw [((S.base.metric T).inner p).map_smul, smul_apply,
      ((S.base.metric T).inner p Z).map_smul]
    simp only [smul_eq_mul]
    ring
  have hZnonneg : 0 ≤ (S.base.metric T).inner p Z Z := by
    by_cases hzero : Z = 0
    · rw [hzero]
      simp
    · exact ((S.base.metric T).pos p Z hzero).le
  have hZsq : (S.base.metric T).inner p Z Z ≤ (1 / (10 * Real.sqrt epsilon)) ^ 2 := by
    rw [← Real.sq_sqrt hZnonneg]
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mpr hZ
  have hinit : F 0 ≤ 1 / (25 * epsilon) := by
    change U (r * 0) ≤ _
    rw [_root_.MulZeroClass.mul_zero, hU0]
    calc
      _ ≤ 4 * (1 / (10 * Real.sqrt epsilon)) ^ 2 :=
        mul_le_mul_of_nonneg_left hZsq (by norm_num)
      _ = _ := by
        rw [div_pow, mul_pow, Real.sq_sqrt hepsilon.le]
        field_simp [hepsilon.ne']
        ring
  have hspeed := DifferentialGeometry.Analysis.scaled_speed_bound (Module.finrank ℝ E)
    (fixedBallScalarGradientConstant (Module.finrank ℝ E))
    (fixedBallScalarGradientConstant_nonneg _) epsilon hepsilon hepsilonSmall
    F F' L hL hLscale hF hFderiv hFbound hinit
  intro s hs
  have hq : s / r ∈ _root_.Set.Icc (0 : ℝ) L :=
    ⟨div_nonneg hs.1 hr.le, div_le_div_of_nonneg_right hs.2 hr.le⟩
  have hcancel : r * (s / r) = s := by field_simp [hr.ne']
  simpa only [F, U, alpha, hcancel] using hspeed (s / r) hq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lRegCurve_speedSq_le_of_local_bounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lRegCurve_speedSq_le_of_local_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lRegCurve_speedSq_le_of_local_bounds ``Submission.DifferentialGeometry.PDE.RicciFlow.lRegCurve_speedSq_le_of_local_bounds

end DifferentialGeometry.PDE.RicciFlow

end
