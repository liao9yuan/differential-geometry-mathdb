import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Parametric.LocalComposition
import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.OperatorField.Parametric.ScalarSmulJet
import Mathlib.Topology.Order.ProjIcc

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open scoped _root_.Manifold _root_.ContDiff _root_.NNReal
namespace DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Integral.L2

variable {ι : Type*}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℝ M]
  [IsManifold 𝓘(ℝ, ℝ) ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instNeZeroNatFinrankReal_differentialGeometry : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instNeZeroNatFinrankReal_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instNeZeroNatFinrankReal_differentialGeometry target :: scope.openDecls } }

@[simp] theorem scalarH1ToContinuous_one
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) M) :
    scalarH1ToContinuous g (ccTensorToHs g 0 1 (scalarCc g 1)) = 1 := by
  ext x
  simp only [scalarH1ToContinuous_apply_ccTensorToHs, scalar0_scalarCc,
    ContinuousMap.one_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.scalarH1ToContinuous_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.scalarH1ToContinuous_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.scalarH1ToContinuous_one ``Submission.DifferentialGeometry.Analysis.Spectral.scalarH1ToContinuous_one

def scalarH1TimeCoordinate
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) M) :
    ℝ × PiLp 2 (fun _ : ι => TensorHs g 0 0 1) →L[ℝ]
      PiLp 2 (fun _ : Option ι => TensorHs g 0 0 1) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Option ι => TensorHs g 0 0 1)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j => match j with
      | none => ((ContinuousLinearMap.id ℝ ℝ).smulRight
          (ccTensorToHs g 0 1 (scalarCc g 1))).comp (ContinuousLinearMap.fst ℝ ℝ _)
      | some i => (PiLp.proj 2 (fun _ : ι => TensorHs g 0 0 1) i).comp
        (ContinuousLinearMap.snd ℝ ℝ _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.scalarH1TimeCoordinate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.scalarH1TimeCoordinate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.scalarH1TimeCoordinate ``Submission.DifferentialGeometry.Analysis.Spectral.scalarH1TimeCoordinate

@[simp] theorem scalarH1TimeCoordinate_none
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) M)
    (p : ℝ × PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) :
    scalarH1TimeCoordinate g p _root_.Option.none = p.1 • ccTensorToHs g 0 1 (scalarCc g 1) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.scalarH1TimeCoordinate_none then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.scalarH1TimeCoordinate_none"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.scalarH1TimeCoordinate_none ``Submission.DifferentialGeometry.Analysis.Spectral.scalarH1TimeCoordinate_none

@[simp] theorem scalarH1TimeCoordinate_some
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) M)
    (p : ℝ × PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) (i : ι) :
    scalarH1TimeCoordinate g p (_root_.Option.some i) = p.2 i := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.scalarH1TimeCoordinate_some then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.scalarH1TimeCoordinate_some"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.scalarH1TimeCoordinate_some ``Submission.DifferentialGeometry.Analysis.Spectral.scalarH1TimeCoordinate_some

theorem scalarH1TimeCoordinate_eval_none [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) M)
    (p : ℝ × PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) (x : M) :
    scalarH1PiToContinuous g (scalarH1TimeCoordinate g p) x _root_.Option.none = p.1 := by
  simp only [scalarH1PiToContinuous_apply, scalarH1TimeCoordinate_none, map_smul,
    scalarH1ToContinuous_one, ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul, mul_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.scalarH1TimeCoordinate_eval_none then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.scalarH1TimeCoordinate_eval_none"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.scalarH1TimeCoordinate_eval_none ``Submission.DifferentialGeometry.Analysis.Spectral.scalarH1TimeCoordinate_eval_none

theorem scalarH1TimeCoordinate_eval_some [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) M)
    (p : ℝ × PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) (x : M) (i : ι) :
    scalarH1PiToContinuous g (scalarH1TimeCoordinate g p) x (_root_.Option.some i) =
      scalarH1ToContinuous g (p.2 i) x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.scalarH1TimeCoordinate_eval_some then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.scalarH1TimeCoordinate_eval_some"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.scalarH1TimeCoordinate_eval_some ``Submission.DifferentialGeometry.Analysis.Spectral.scalarH1TimeCoordinate_eval_some

end DifferentialGeometry.Analysis.Spectral

namespace DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {ι : Type*} [Fintype ι]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℝ M]
  [IsManifold 𝓘(ℝ, ℝ) ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
  [BoundarylessManifold 𝓘(ℝ, ℝ) M]
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instNeZeroNatFinrankReal_differentialGeometry_1 : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instNeZeroNatFinrankReal_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instNeZeroNatFinrankReal_differentialGeometry_1 target :: scope.openDecls } }

theorem exists_scalarH1_time_composition_on_ball
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) M)
    (F : (Option ι → ℝ) → ℝ) {U : Set (Option ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (t0 : ℝ) (u0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1))
    (hu0 : Set.range (scalarH1PiToContinuous g (scalarH1TimeCoordinate g (t0, u0))) ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ≥0,
      ∃ N : Metric.ball (t0, u0) δ → TensorHs g 0 0 1,
        LipschitzWith C N ∧
        (∀ p ∈ Metric.ball (t0, u0) δ,
          Set.range (scalarH1PiToContinuous g (scalarH1TimeCoordinate g p)) ⊆ U) ∧
        ∀ p x, scalarH1ToContinuous g (N p) x =
          F (fun j => match j with
            | none => p.1.1
            | some i => scalarH1ToContinuous g (p.1.2 i) x) := by
  obtain ⟨r, hr, C, N, hN, hRange, hNe, _⟩ := exists_scalarH1_composition_on_ball
    g F hF hU (scalarH1TimeCoordinate g (t0, u0)) hu0
  have hnear : ∀ᶠ p in nhds (t0, u0),
      scalarH1TimeCoordinate g p ∈ Metric.ball (scalarH1TimeCoordinate g (t0, u0)) r :=
    (scalarH1TimeCoordinate g).continuous.continuousAt.eventually
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
  obtain ⟨δ, hδ, hmap⟩ := Metric.eventually_nhds_iff.mp hnear
  let A : Metric.ball (t0, u0) δ →
      Metric.ball (scalarH1TimeCoordinate g (t0, u0)) r :=
    fun p => ⟨scalarH1TimeCoordinate g p, hmap p.2⟩
  have hA : LipschitzWith ‖scalarH1TimeCoordinate (ι := ι) g‖₊ A := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    change _root_.Dist.dist (scalarH1TimeCoordinate g p.1) (scalarH1TimeCoordinate g q.1) ≤
      ‖scalarH1TimeCoordinate (ι := ι) g‖ * _root_.Dist.dist p.1 q.1
    exact (scalarH1TimeCoordinate (ι := ι) g).dist_le_opNorm p.1 q.1
  refine ⟨δ, hδ, C * ‖scalarH1TimeCoordinate (ι := ι) g‖₊, fun p => N (A p),
    hN.comp hA, fun p hp => hRange _ (hmap hp), ?_⟩
  intro p x
  rw [hNe]
  congr 1
  funext j
  cases j with
  | none => exact scalarH1TimeCoordinate_eval_none g p.1 x
  | some i => exact scalarH1TimeCoordinate_eval_some g p.1 x i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.exists_scalarH1_time_composition_on_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.exists_scalarH1_time_composition_on_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.exists_scalarH1_time_composition_on_ball ``Submission.DifferentialGeometry.Analysis.Spectral.exists_scalarH1_time_composition_on_ball

end DifferentialGeometry.Analysis.Spectral

end


noncomputable section
open scoped _root_.Manifold _root_.ContDiff _root_.NNReal
namespace DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {ι : Type*} [Fintype ι]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℝ M]
  [IsManifold 𝓘(ℝ, ℝ) ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
  [BoundarylessManifold 𝓘(ℝ, ℝ) M]
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instNeZeroNatFinrankReal_differentialGeometry_2 : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instNeZeroNatFinrankReal_differentialGeometry_2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instNeZeroNatFinrankReal_differentialGeometry_2 target :: scope.openDecls } }

theorem exists_scalarH1_time_composition_on_symmetric_time_interval
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) M)
    (F : (Option ι → ℝ) → ℝ) {U : Set (Option ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (t₀ : ℝ) (u₀ : PiLp 2 (fun _ : ι => TensorHs g 0 0 1))
    (hu₀ : Set.range (scalarH1PiToContinuous g (scalarH1TimeCoordinate g (t₀, u₀))) ⊆ U) :
    ∃ R : ℝ, 0 < R ∧ ∃ C : ℝ≥0,
      ∃ N : ℝ → Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) R →
        TensorHs g 0 0 1,
      LipschitzWith C (fun p : ℝ × Metric.closedBall
        (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) R => N p.1 p.2) ∧
      (∀ t ∈ Set.Icc (-R) R,
        ∀ u ∈ Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) R,
        Set.range (scalarH1PiToContinuous g (scalarH1TimeCoordinate g (t₀ + t, u₀ + u))) ⊆ U) ∧
      ∀ t ∈ Set.Icc (-R) R, ∀ u x,
        scalarH1ToContinuous g (N t u) x = F (fun j => match j with
          | none => t₀ + t
          | some i => scalarH1ToContinuous g (u₀ i + u.1 i) x) := by
  obtain ⟨δ, hδ, C, N, hN, hRange, hNe⟩ :=
    exists_scalarH1_time_composition_on_ball g F hF hU t₀ u₀ hu₀
  let R := δ / 2
  have hR : 0 < R := half_pos hδ
  have hRR : -R ≤ R := by linarith
  let S := Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) R
  have hmap (p : ℝ × S) :
      (t₀ + (Set.projIcc (-R) R hRR p.1 : ℝ), u₀ + p.2.1) ∈
        Metric.ball (t₀, u₀) δ := by
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    constructor
    · have hc := (Set.projIcc (-R) R hRR p.1).2
      rw [Real.dist_eq, add_sub_cancel_left]
      exact (abs_le.mpr hc).trans_lt (half_lt_self hδ)
    · have hu := p.2.2
      rw [Metric.mem_closedBall, dist_zero_right] at hu
      rw [dist_eq_norm, add_sub_cancel_left]
      exact hu.trans_lt (half_lt_self hδ)
  let A : ℝ × S → Metric.ball (t₀, u₀) δ := fun p => ⟨_, hmap p⟩
  have hA : LipschitzWith 1 A := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    change _root_.Dist.dist (t₀ + (Set.projIcc (-R) R hRR p.1 : ℝ), u₀ + p.2.1)
      (t₀ + (Set.projIcc (-R) R hRR q.1 : ℝ), u₀ + q.2.1) ≤ (1 : ℝ) * _root_.Dist.dist p q
    rw [one_mul, Prod.dist_eq, Prod.dist_eq, dist_add_left, dist_add_left]
    apply max_le_max
    · simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq] using
        (LipschitzWith.projIcc hRR).dist_le_mul p.1 q.1
    · exact le_rfl
  refine ⟨R, hR, C, fun t u => N (A (t, u)), ?_, ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro p q
    exact (hN.dist_le_mul (A p) (A q)).trans
      (mul_le_mul_of_nonneg_left
        (by simpa only [NNReal.coe_one, one_mul] using hA.dist_le_mul p q) C.coe_nonneg)
  · intro t ht u hu
    have h := hRange _ (hmap (t, ⟨u, hu⟩))
    simpa only [Set.projIcc_of_mem hRR ht] using h
  · intro t ht u x
    rw [hNe]
    congr 1
    funext j
    cases j with
    | none =>
        change t₀ + (Set.projIcc (-R) R hRR t : ℝ) = t₀ + t
        rw [Set.projIcc_of_mem hRR ht]
    | some i => rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.exists_scalarH1_time_composition_on_symmetric_time_interval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.exists_scalarH1_time_composition_on_symmetric_time_interval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.exists_scalarH1_time_composition_on_symmetric_time_interval ``Submission.DifferentialGeometry.Analysis.Spectral.exists_scalarH1_time_composition_on_symmetric_time_interval


theorem exists_scalarH1_time_composition_on_closedBall
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) M)
    (F : (Option ι → ℝ) → ℝ) {U : Set (Option ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (t0 : ℝ) (u0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1))
    (hu0 : Set.range (scalarH1PiToContinuous g (scalarH1TimeCoordinate g (t0, u0))) ⊆ U) :
    ∃ R : ℝ, 0 < R ∧ ∃ C : ℝ≥0,
      ∃ N : ℝ → Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) R →
        TensorHs g 0 0 1,
      LipschitzWith C (fun p : ℝ × Metric.closedBall
        (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) R => N p.1 p.2) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) R,
        ∀ u ∈ Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) R,
        Set.range (scalarH1PiToContinuous g (scalarH1TimeCoordinate g (t0 + t, u0 + u))) ⊆ U) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) R, ∀ u x,
        scalarH1ToContinuous g (N t u) x = F (fun j => match j with
          | none => t0 + t
          | some i => scalarH1ToContinuous g (u0 i + u.1 i) x) := by
  obtain ⟨δ, hδ, C, N, hN, hRange, hNe⟩ := exists_scalarH1_time_composition_on_ball g F hF hU t0 u0 hu0
  let R := δ / 2
  have hR : 0 < R := half_pos hδ
  let S := Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) R
  have hmap (p : ℝ × S) :
      (t0 + (Set.projIcc 0 R hR.le p.1 : ℝ), u0 + p.2.1) ∈ Metric.ball (t0, u0) δ := by
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    constructor
    · have hc := (Set.projIcc 0 R hR.le p.1).2
      simp only [Real.dist_eq, add_sub_cancel_left, abs_of_nonneg hc.1]
      exact hc.2.trans_lt (half_lt_self hδ)
    · have hu := p.2.2
      rw [Metric.mem_closedBall, dist_zero_right] at hu
      rw [dist_eq_norm, add_sub_cancel_left]
      exact hu.trans_lt (half_lt_self hδ)
  let A : ℝ × S → Metric.ball (t0, u0) δ := fun p => ⟨_, hmap p⟩
  have hA : LipschitzWith 1 A := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    change _root_.Dist.dist (t0 + (Set.projIcc 0 R hR.le p.1 : ℝ), u0 + p.2.1)
      (t0 + (Set.projIcc 0 R hR.le q.1 : ℝ), u0 + q.2.1) ≤ (1 : ℝ) * _root_.Dist.dist p q
    rw [one_mul, Prod.dist_eq, Prod.dist_eq, dist_add_left, dist_add_left]
    apply max_le_max
    · simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq] using
        (LipschitzWith.projIcc hR.le).dist_le_mul p.1 q.1
    · exact le_rfl
  refine ⟨R, hR, C, fun t u => N (A (t,u)), ?_, ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro p q
    exact (hN.dist_le_mul (A p) (A q)).trans
      (mul_le_mul_of_nonneg_left (by simpa only [NNReal.coe_one, one_mul] using hA.dist_le_mul p q) C.coe_nonneg)
  · intro t ht u hu
    have h := hRange _ (hmap (t, ⟨u, hu⟩))
    simpa only [Set.projIcc_of_mem hR.le ht] using h
  · intro t ht u x
    rw [hNe]
    congr 1
    funext j
    cases j with
    | none =>
        change t0 + (Set.projIcc 0 R hR.le t : ℝ) = t0 + t
        rw [Set.projIcc_of_mem hR.le ht]
    | some i => rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.exists_scalarH1_time_composition_on_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.exists_scalarH1_time_composition_on_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.exists_scalarH1_time_composition_on_closedBall ``Submission.DifferentialGeometry.Analysis.Spectral.exists_scalarH1_time_composition_on_closedBall

end DifferentialGeometry.Analysis.Spectral
end
