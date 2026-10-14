import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Galerkin.ForcingSequence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Background.Solution.Pointwise

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Tensor.RSTensor
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral hiding TensorEigenIdx
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

theorem exists_galerkin_projected_forcing_sequence_background (g₀ g_bg : SmoothRiemannianMetric I M)
    (K : LowRegularityBoundParameters) {Rcap T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (solution : MaximalRegularitySolutionSpace (I := I) (M := M) ((1 : ℕ) : ℝ) T)
    (fLo : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hlo : IsBackgroundLowRegularitySolutionAt (I := I) (M := M) g₀ g_bg K hT hT1 solution fLo Rcap) :
    ∃ (fseq : ℕ → timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T),
      _root_.Filter.Tendsto fseq _root_.Filter.atTop (𝓝 fLo) ∧
      ∀ N : ℕ,
        timeL2EigenProj (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T N (fseq N) =
            fseq N ∧
          (∀ᵐ t ∂(timeMeasure T),
            maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
              (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
              (fseq N) t ∈
              lowerState (I := I) (M := M) g₀ 1 (lowRegularityStateRadius K.top K.slope K.outer K.realize)) ∧
          fseq N =ᵐ[timeMeasure T]
            (fun t => projNfun (I := I) (M := M) g₀ 1 N
              (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg
                K.threshold_lt K.top_nonneg K.slope_nonneg K.outer_pos K.realize_pos hlo.metric_realization)
              (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1
                  (lowRegularityStateRadius_pos K.top_nonneg K.slope_nonneg
                    K.outer_pos K.realize_pos).le)
                (maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
                  (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
                  (fseq N)) t)) ∧
          timeH1.trace0 _ T (maximalRegularityDuhamelMap (I := I) (M := M) ((1 : ℕ) : ℝ)
              hT (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
              (fseq N)) = 0 ∧
          timeH1.timeDeriv _ T (maximalRegularityDuhamelMap (I := I) (M := M) ((1 : ℕ) : ℝ)
              hT (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
              (fseq N)) =
            timeScaleLaplacian (I := I) (M := M) ((1 : ℕ) : ℝ)
                (maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
                  (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
                  (fseq N)) + fseq N ∧
          ‖fseq N‖ ≤ lowRegularityStateRadius K.top K.slope K.outer K.realize / 4 := by
  set R : ℝ := lowRegularityStateRadius K.top K.slope K.outer K.realize with hRdef
  have hRpos : 0 < R := lowRegularityStateRadius_pos
    K.top_nonneg K.slope_nonneg K.outer_pos K.realize_pos
  have hQnn : 0 ≤ lowRegularityOuterRadius K.top K.outer K.realize :=
    (lowRegularityOuterRadius_pos K.top_nonneg K.outer_pos K.realize_pos).le
  set Nfun := boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg
    K.threshold_lt K.top_nonneg K.slope_nonneg K.outer_pos K.realize_pos hlo.metric_realization
    with hNfundef
  set A : ℝ≥0 := Real.toNNReal (K.top * lowRegularityOuterRadius K.top K.outer K.realize / R) with hAdef
  set B : ℝ≥0 := Real.toNNReal K.base with hBdef
  set C : ℝ≥0 := Real.toNNReal K.slope with hCdef
  have hAarg : 0 ≤ K.top * lowRegularityOuterRadius K.top K.outer K.realize / R :=
    div_nonneg (mul_nonneg K.top_nonneg hQnn) hRpos.le
  have hAcoe : (A : ℝ) = K.top * lowRegularityOuterRadius K.top K.outer K.realize / R :=
    Real.coe_toNNReal _ hAarg
  have hBcoe : (B : ℝ) = K.base := Real.coe_toNNReal _ K.base_nonneg
  have hCcoe : (C : ℝ) = K.slope := Real.coe_toNNReal _ K.slope_nonneg
  have hAR : (A : ℝ) * R = K.top * lowRegularityOuterRadius K.top K.outer K.realize := by
    rw [hAcoe]
    exact div_mul_cancel₀ _ hRpos.ne'
  have hsmallA : (A : ℝ) * R ≤ 1 / 16 := by
    rw [hAR]; exact lowRegularityOuterRadius_small K.top_nonneg
  have hsmallC : (C : ℝ) * R ≤ 1 / 16 := by
    rw [hCcoe, hRdef]; exact lowRegularityStateRadius_small K.slope_nonneg
  have hsingle : ∀ u u' : lowerState (I := I) (M := M) g₀ 1 R,
      ‖Nfun u - Nfun u'‖ ≤
        (A : ℝ) * R *
            ‖(u : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) -
              (u' : _)‖ +
          (B : ℝ) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
              ((u : _) - (u' : _))‖ +
          (C : ℝ) *
              (‖(u : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))‖ +
                ‖(u' : TensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2))‖) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
              ((u : _) - (u' : _))‖ := by
    intro u u'
    rw [hAR, hBcoe, hCcoe]
    exact hlo.remainder_lipschitz u u'
  have hDnn : 0 ≤ K.zeroBd := le_trans (norm_nonneg _) hlo.remainder_zero_bound
  have hTB : T ≤ 1 / (64 * ((B : ℝ) + 1) ^ 2) := by
    rw [hBcoe]
    exact le_trans hlo.time_le_horizon (le_trans (min_le_right _ _) (min_le_left _ _))
  have hex : ∀ N : ℕ,
      ∃ gforce : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T,
        (timeL2EigenProj (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T N gforce =
            gforce ∧
          (∀ᵐ t ∂(timeMeasure T),
            maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
              (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
              gforce t ∈ lowerState (I := I) (M := M) g₀ 1 R) ∧
          gforce =ᵐ[timeMeasure T]
            (fun t => projNfun (I := I) (M := M) g₀ 1 N Nfun
              (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1 hRpos.le)
                (maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
                  (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
                  gforce) t)) ∧
          timeH1.trace0 _ T (maximalRegularityDuhamelMap (I := I) (M := M) ((1 : ℕ) : ℝ)
              hT (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
              gforce) = 0 ∧
          timeH1.timeDeriv _ T (maximalRegularityDuhamelMap (I := I) (M := M) ((1 : ℕ) : ℝ)
              hT (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
              gforce) =
            timeScaleLaplacian (I := I) (M := M) ((1 : ℕ) : ℝ)
                (maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
                  (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
                  gforce) + gforce ∧
          ‖gforce‖ ≤ R / 4) ∧
        ‖gforce - fLo‖ ≤
          2 * ‖timeL2EigenProj (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T N fLo -
            fLo‖ := by
    intro N
    obtain ⟨T₀, hT₀eq, _hT₀pos, hsol⟩ :=
      exists_tame_projected_partial_solution
        (I := I) (M := M) g₀ 1 hRpos N Nfun hlo.remainder_continuous A B C K.zeroBd
        hDnn hlo.remainder_zero_bound hsmallA hsmallC hsingle
    have hTT₀ : T ≤ T₀ := by
      rw [hT₀eq, hBcoe]
      exact hlo.time_le_horizon
    obtain ⟨u, gforce, hu, hstate, hgE, htr, hpde, hgball⟩ :=
      hsol hT hTT₀
    subst hu
    refine ⟨gforce, ⟨?_, hstate, hgE, htr, hpde, hgball⟩, ?_⟩
    · exact projForce_fixed (I := I) (M := M) g₀ 1 N gforce
        (fun t => aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1 hRpos.le)
          (maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
            (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) gforce) t)
        hgE
    · exact projFixTame_le_two (I := I) (M := M) g₀ 1 hRpos N hlo.remainder_continuous hsingle
        hsmallA hsmallC hT hT1 hTB fLo gforce hlo.forcing_norm_le_quarter_radius hgball hlo.forcing_ae_eq_remainder hgE
  choose fseq hpack hK using hex
  exact ⟨fseq, projFix_tendsto (I := I) (M := M) g₀ (K := 2) fLo fseq hK, hpack⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_galerkin_projected_forcing_sequence_background then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_galerkin_projected_forcing_sequence_background"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_galerkin_projected_forcing_sequence_background ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_galerkin_projected_forcing_sequence_background

theorem exists_galerkin_projected_forcing_sequence_with_mode_convergence_background (g₀ g_bg : SmoothRiemannianMetric I M)
    (K : LowRegularityBoundParameters) {Rcap T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (solution : MaximalRegularitySolutionSpace (I := I) (M := M) ((1 : ℕ) : ℝ) T)
    (fLo : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hlo : IsBackgroundLowRegularitySolutionAt (I := I) (M := M) g₀ g_bg K hT hT1 solution fLo Rcap) :
    ∃ (fseq : ℕ → timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T),
      _root_.Filter.Tendsto fseq _root_.Filter.atTop (𝓝 fLo) ∧
      (∀ (i : TensorEigenIdx (I := I) (M := M) g₀ 0 2), ∀ t ∈ Set.Icc (0 : ℝ) T,
        Tendsto (fun N => perModeConvolution (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) (fseq N) i) u) t) _root_.Filter.atTop
          (𝓝 (perModeConvolution (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) fLo i) u) t))) ∧
      ∀ N : ℕ,
        timeL2EigenProj (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T N (fseq N) =
            fseq N ∧
          (∀ᵐ t ∂(timeMeasure T),
            maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
              (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
              (fseq N) t ∈
              lowerState (I := I) (M := M) g₀ 1 (lowRegularityStateRadius K.top K.slope K.outer K.realize)) ∧
          fseq N =ᵐ[timeMeasure T]
            (fun t => projNfun (I := I) (M := M) g₀ 1 N
              (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg
                K.threshold_lt K.top_nonneg K.slope_nonneg K.outer_pos K.realize_pos hlo.metric_realization)
              (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1
                  (lowRegularityStateRadius_pos K.top_nonneg K.slope_nonneg
                    K.outer_pos K.realize_pos).le)
                (maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
                  (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
                  (fseq N)) t)) ∧
          timeH1.trace0 _ T (maximalRegularityDuhamelMap (I := I) (M := M) ((1 : ℕ) : ℝ)
              hT (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
              (fseq N)) = 0 ∧
          timeH1.timeDeriv _ T (maximalRegularityDuhamelMap (I := I) (M := M) ((1 : ℕ) : ℝ)
              hT (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
              (fseq N)) =
            timeScaleLaplacian (I := I) (M := M) ((1 : ℕ) : ℝ)
                (maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
                  (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
                  (fseq N)) + fseq N ∧
          ‖fseq N‖ ≤ lowRegularityStateRadius K.top K.slope K.outer K.realize / 4 := by
  obtain ⟨fseq, hconv, hpack⟩ :=
    exists_galerkin_projected_forcing_sequence_background (I := I) (M := M) g₀ g_bg K hT hT1 solution fLo hlo
  refine ⟨fseq, hconv, fun i t ht => ?_, hpack⟩
  have hmode : _root_.Filter.Tendsto (fun N => timeModeCoeff (I := I) (M := M) (fseq N) i)
      atTop (𝓝 (timeModeCoeff (I := I) (M := M) fLo i)) := by
    have hcl := ((tensorHsCoeffL (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (a := ((1 : ℕ) : ℝ)) i).compLpL 2 (timeMeasure T)).continuous.tendsto fLo
    exact Tendsto.congr' (Filter.Eventually.of_forall fun _ => rfl) (hcl.comp hconv)
  exact tendsto_perModeConvolution_of_tendsto_timeL2
    (TensorEigenIdx.lambda (I := I) (M := M) i)
    (tensor_lambda_nonneg (I := I) (M := M) i) hmode ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_galerkin_projected_forcing_sequence_with_mode_convergence_background then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_galerkin_projected_forcing_sequence_with_mode_convergence_background"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_galerkin_projected_forcing_sequence_with_mode_convergence_background ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_galerkin_projected_forcing_sequence_with_mode_convergence_background

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
