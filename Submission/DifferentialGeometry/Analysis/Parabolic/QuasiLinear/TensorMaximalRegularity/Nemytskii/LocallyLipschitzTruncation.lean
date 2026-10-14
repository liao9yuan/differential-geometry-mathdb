import Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Nemytskii.SubcriticalSmallTime
import Submission.DifferentialGeometry.Analysis.Calculus.Retraction.Ball

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Calculus
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}
variable {a : ℝ} {T : ℝ}

section RecentreNormed

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

noncomputable def recenteredBallRetraction (c : X) (R : ℝ) (v : X) : X :=
  c + ballRetraction R (v - c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.recenteredBallRetraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.recenteredBallRetraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.recenteredBallRetraction ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.recenteredBallRetraction

theorem recenteredBallRetraction_lipschitzWith
    {R : ℝ} (hR : 0 ≤ R) (c : X) :
    LipschitzWith 2 (recenteredBallRetraction c R) := by
  have hshift : LipschitzWith 1 (fun v : X => v - c) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [NNReal.coe_one, one_mul, dist_sub_right]
  have hadd : LipschitzWith 1 (fun w : X => c + w) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [NNReal.coe_one, one_mul, dist_add_left]
  have hcomp :
      LipschitzWith (1 * (2 * 1))
        (fun v : X => c + ballRetraction R (v - c)) :=
    hadd.comp ((lipschitzWith_ballRetraction (X := X) hR).comp hshift)
  change LipschitzWith 2 (fun v : X => c + ballRetraction R (v - c))
  simpa only [one_mul, mul_one] using hcomp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.recenteredBallRetraction_lipschitzWith then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.recenteredBallRetraction_lipschitzWith"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.recenteredBallRetraction_lipschitzWith ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.recenteredBallRetraction_lipschitzWith

end RecentreNormed

section RecentreHilbert

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

theorem recenteredBallRetraction_lipschitzWith_one
    {R : ℝ} (hR : 0 ≤ R) (c : X) :
    LipschitzWith 1 (recenteredBallRetraction c R) := by
  have hshift : LipschitzWith 1 (fun v : X => v - c) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [NNReal.coe_one, one_mul, dist_sub_right]
  have hadd : LipschitzWith 1 (fun w : X => c + w) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [NNReal.coe_one, one_mul, dist_add_left]
  have hcomp :
      LipschitzWith (1 * (1 * 1))
        (fun v : X => c + ballRetraction R (v - c)) :=
    hadd.comp ((lipschitzWith_one_ballRetraction (X := X) hR).comp hshift)
  change LipschitzWith 1 (fun v : X => c + ballRetraction R (v - c))
  simpa only [one_mul, mul_one] using hcomp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.recenteredBallRetraction_lipschitzWith_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.recenteredBallRetraction_lipschitzWith_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.recenteredBallRetraction_lipschitzWith_one ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.recenteredBallRetraction_lipschitzWith_one

end RecentreHilbert

section RecentreNormed

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem recenteredBallRetraction_mapsTo {R : ℝ} (hR : 0 ≤ R) (c : X) :
    Set.MapsTo (recenteredBallRetraction c R) Set.univ (Metric.closedBall c R) := by
  intro v _
  rw [Metric.mem_closedBall, dist_eq_norm, recenteredBallRetraction,
    add_comm c _, add_sub_cancel_right]
  exact ballRetraction_mem_closedBall hR (v - c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.recenteredBallRetraction_mapsTo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.recenteredBallRetraction_mapsTo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.recenteredBallRetraction_mapsTo ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.recenteredBallRetraction_mapsTo

theorem recenteredBallRetraction_eq_self_of_mem {R : ℝ} {c v : X}
    (hv : v ∈ Metric.closedBall c R) :
    recenteredBallRetraction c R v = v := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hv
  rw [recenteredBallRetraction, ballRetraction_eq_self_of_mem hv, add_sub_cancel]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.recenteredBallRetraction_eq_self_of_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.recenteredBallRetraction_eq_self_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.recenteredBallRetraction_eq_self_of_mem ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.recenteredBallRetraction_eq_self_of_mem

end RecentreNormed

section Truncation

variable {N : TensorHs (I := I) (M := M) g r s (a + 1) →
    TensorHs (I := I) (M := M) g r s a}

def truncatedNonlin (N : TensorHs (I := I) (M := M) g r s (a + 1) →
      TensorHs (I := I) (M := M) g r s a)
    (u₀' : TensorHs (I := I) (M := M) g r s (a + 1)) (R : ℝ) :
    TensorHs (I := I) (M := M) g r s (a + 1) →
      TensorHs (I := I) (M := M) g r s a :=
  fun v => N (recenteredBallRetraction u₀' R v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.truncatedNonlin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.truncatedNonlin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.truncatedNonlin ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.truncatedNonlin

omit [NeZero (Module.finrank ℝ E)] in
theorem truncatedNonlin_eq_of_mem
    {u₀' : TensorHs (I := I) (M := M) g r s (a + 1)} {R : ℝ}
    {v : TensorHs (I := I) (M := M) g r s (a + 1)}
    (hv : v ∈ Metric.closedBall u₀' R) :
    truncatedNonlin (I := I) (M := M) N u₀' R v = N v := by
  rw [truncatedNonlin, recenteredBallRetraction_eq_self_of_mem hv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.truncatedNonlin_eq_of_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.truncatedNonlin_eq_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.truncatedNonlin_eq_of_mem ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.truncatedNonlin_eq_of_mem

omit [NeZero (Module.finrank ℝ E)] in
theorem truncatedNonlin_lipschitzWith {L_R : ℝ≥0}
    {u₀' : TensorHs (I := I) (M := M) g r s (a + 1)} {R : ℝ} (hR : 0 ≤ R)
    (hN : LipschitzOnWith L_R N (Metric.closedBall u₀' R)) :
    LipschitzWith L_R (truncatedNonlin (I := I) (M := M) N u₀' R) := by
  have hρ : LipschitzOnWith 1 (recenteredBallRetraction u₀' R) Set.univ :=
    lipschitzOnWith_univ.mpr
      (recenteredBallRetraction_lipschitzWith_one (X := _) hR u₀')
  have hmaps := recenteredBallRetraction_mapsTo (X := _) hR u₀'
  have hcomp : LipschitzOnWith (L_R * 1)
      (N ∘ recenteredBallRetraction u₀' R) Set.univ :=
    hN.comp hρ hmaps
  rw [mul_one] at hcomp
  have : LipschitzWith L_R (N ∘ recenteredBallRetraction u₀' R) :=
    lipschitzOnWith_univ.mp hcomp
  exact this

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.truncatedNonlin_lipschitzWith then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.truncatedNonlin_lipschitzWith"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.truncatedNonlin_lipschitzWith ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.truncatedNonlin_lipschitzWith

end Truncation

omit [NeZero (Module.finrank ℝ E)] in
theorem quasilinear_strong_existence_truncated_smallTime_ofCompact
    {N : TensorHs (I := I) (M := M) g r s (a + 1) →
      TensorHs (I := I) (M := M) g r s a}
    {L_R : ℝ≥0} {R : ℝ} (hR : 0 ≤ R)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : TensorHs (I := I) (M := M) g r s (a + 2))
    (hN : LipschitzOnWith L_R N (Metric.closedBall
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show (a + 1) ≤ a + 2 by linarith) u₀) R)) :
    ∃ T_R : ℝ, 0 < T_R ∧ ∀ {T : ℝ} (hT : 0 < T) (_hTR : T ≤ T_R),
      ∃ (u : MaximalRegularitySolutionSpace (I := I) (M := M) a T)
        (gforce : timeL2 (TensorHs (I := I) (M := M) g r s a) T),
        u = maximalRegularityDuhamelMap (I := I) (M := M) a hT u₀ gforce ∧
          gforce = nemytskiiHa1 (I := I) (M := M)
              (truncatedNonlin_lipschitzWith (I := I) (M := M) hR hN)
              (maximalRegularityDuhamelSolutionFieldHa1 (I := I) (M := M) a hT u₀ gforce) ∧
          TimeSobolev.timeH1.trace0 _ T u =
              tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
                (show a ≤ a + 2 by linarith) u₀ ∧
          TimeSobolev.timeH1.timeDeriv _ T u =
            timeScaleLaplacian (I := I) (M := M) a
                (maximalRegularityDuhamelSolutionField (I := I) (M := M) a hT u₀ gforce) +
              nemytskiiHa1 (I := I) (M := M)
                (truncatedNonlin_lipschitzWith (I := I) (M := M) hR hN)
                (maximalRegularityDuhamelSolutionFieldHa1 (I := I) (M := M) a hT u₀
                  gforce) :=
  quasilinear_strong_existence_smallTime (I := I) (M := M)
    (h_compact := h_compact) u₀
    (truncatedNonlin_lipschitzWith (I := I) (M := M) hR hN)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinear_strong_existence_truncated_smallTime_ofCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinear_strong_existence_truncated_smallTime_ofCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinear_strong_existence_truncated_smallTime_ofCompact ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.quasilinear_strong_existence_truncated_smallTime_ofCompact

omit [NeZero (Module.finrank ℝ E)] in
theorem nemytskiiHa1_truncated_eqOn_ball
    {N : TensorHs (I := I) (M := M) g r s (a + 1) →
      TensorHs (I := I) (M := M) g r s a}
    {L_R : ℝ≥0} {R : ℝ} (hR : 0 ≤ R)
    {u₀' : TensorHs (I := I) (M := M) g r s (a + 1)}
    (hN : LipschitzOnWith L_R N (Metric.closedBall u₀' R))
    (field : timeL2 (TensorHs (I := I) (M := M) g r s (a + 1)) T)
    (hball : ∀ᵐ t ∂(timeMeasure T), field t ∈ Metric.closedBall u₀' R) :
    nemytskiiHa1 (I := I) (M := M)
        (truncatedNonlin_lipschitzWith (I := I) (M := M) hR hN) field =ᵐ[timeMeasure T]
      fun t => N (field t) := by
  have hcoe := nemytskiiHa1_coeFn (I := I) (M := M)
    (truncatedNonlin_lipschitzWith (I := I) (M := M) hR hN) field
  filter_upwards [hcoe, hball] with t ht htmem
  rw [ht, truncatedNonlin_eq_of_mem (I := I) (M := M) htmem]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskiiHa1_truncated_eqOn_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskiiHa1_truncated_eqOn_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskiiHa1_truncated_eqOn_ball ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.nemytskiiHa1_truncated_eqOn_ball

omit [NeZero (Module.finrank ℝ E)] in
theorem de_simon_quasilinear_tensor_heat_short_time_existence_locally_lipschitz_of_compact_resolvent
    {N : TensorHs (I := I) (M := M) g r s (a + 1) →
      TensorHs (I := I) (M := M) g r s a}
    {L_R : ℝ≥0} {R : ℝ} (hR : 0 ≤ R)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : TensorHs (I := I) (M := M) g r s (a + 2))
    (hN : LipschitzOnWith L_R N (Metric.closedBall
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show (a + 1) ≤ a + 2 by linarith) u₀) R)) :
    ∃ T_R : ℝ, 0 < T_R ∧ ∀ {T : ℝ} (hT : 0 < T) (_hTR : T ≤ T_R)
        (gforce : timeL2 (TensorHs (I := I) (M := M) g r s a) T)
        (_hfix : gforce = nemytskiiHa1 (I := I) (M := M)
            (truncatedNonlin_lipschitzWith (I := I) (M := M) hR hN)
            (maximalRegularityDuhamelSolutionFieldHa1 (I := I) (M := M) a hT u₀ gforce))
        (_hstay : ∀ᵐ t ∂(timeMeasure T),
            maximalRegularityDuhamelSolutionFieldHa1 (I := I) (M := M) a hT u₀ gforce t ∈
              Metric.closedBall
                (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
                  (show (a + 1) ≤ a + 2 by linarith) u₀) R),
      ∃ u : MaximalRegularitySolutionSpace (I := I) (M := M) a T,
        u = maximalRegularityDuhamelMap (I := I) (M := M) a hT u₀ gforce ∧
          gforce =ᵐ[timeMeasure T]
            (fun t => N (maximalRegularityDuhamelSolutionFieldHa1 (I := I) (M := M)
              a hT u₀ gforce t)) ∧
          TimeSobolev.timeH1.trace0 _ T u =
              tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
                (show a ≤ a + 2 by linarith) u₀ ∧
          TimeSobolev.timeH1.timeDeriv _ T u =
            timeScaleLaplacian (I := I) (M := M) a
                (maximalRegularityDuhamelSolutionField (I := I) (M := M) a hT u₀ gforce) +
              nemytskiiHa1 (I := I) (M := M)
                (truncatedNonlin_lipschitzWith (I := I) (M := M) hR hN)
                (maximalRegularityDuhamelSolutionFieldHa1 (I := I) (M := M) a hT u₀
                  gforce) := by
  refine ⟨smallTimeHorizon L_R, smallTimeHorizon_pos L_R, ?_⟩
  intro T hT hTR gforce hfix hstay
  refine ⟨maximalRegularityDuhamelMap (I := I) (M := M) a hT u₀ gforce, rfl, ?_, ?_, ?_⟩
  · conv_lhs => rw [hfix]
    exact nemytskiiHa1_truncated_eqOn_ball (I := I) (M := M) hR hN
      (maximalRegularityDuhamelSolutionFieldHa1 (I := I) (M := M) a hT u₀ gforce) hstay
  · exact maximalRegularityDuhamelMap_trace0 (I := I) (M := M) (a := a) (T := T)
      hT u₀ gforce
  · rw [maximalRegularityDuhamelMap_timeDeriv_eq (I := I) (M := M)
      (h_compact := h_compact) (a := a) (T := T) hT u₀ gforce]
    exact congrArg₂ (· + ·) rfl hfix

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.de_simon_quasilinear_tensor_heat_short_time_existence_locally_lipschitz_of_compact_resolvent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.de_simon_quasilinear_tensor_heat_short_time_existence_locally_lipschitz_of_compact_resolvent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.de_simon_quasilinear_tensor_heat_short_time_existence_locally_lipschitz_of_compact_resolvent ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.de_simon_quasilinear_tensor_heat_short_time_existence_locally_lipschitz_of_compact_resolvent

end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry

end
