import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Bounds.Class
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.Galerkin.TameSolutionProjection
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.Regularity.Solution

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

theorem exists_galerkin_projected_forcing_sequence (g₀ : SmoothRiemannianMetric I M)
    {δ Ctop B0 B1 D ρ P Rcap T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (fLo : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hlo : IsLowRegularitySolutionAt (I := I) (M := M) (δ := δ) (Ctop := Ctop)
      (B0 := B0) (B1 := B1) (D := D) (ρ := ρ) (P := P)
      g₀ hT hT1 fLo Rcap) :
    ∃ (fseq : ℕ → timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T),
      _root_.Filter.Tendsto fseq _root_.Filter.atTop (𝓝 fLo) ∧
      ∀ N : ℕ,
        timeL2EigenProj (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T N (fseq N) =
            fseq N ∧
          (∀ᵐ t ∂(timeMeasure T),
            maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
              (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
              (fseq N) t ∈
              lowerState (I := I) (M := M) g₀ 1 (lowRegularityStateRadius Ctop B1 ρ P)) ∧
          fseq N =ᵐ[timeMeasure T]
            (fun t => projNfun (I := I) (M := M) g₀ 1 N
              (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀
                hlo.threshold_lt_one hlo.top_nonneg hlo.slope_nonneg hlo.outer_pos hlo.realize_pos hlo.metric_realization)
              (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1
                  (lowRegularityStateRadius_pos hlo.top_nonneg hlo.slope_nonneg hlo.outer_pos hlo.realize_pos).le)
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
          ‖fseq N‖ ≤ lowRegularityStateRadius Ctop B1 ρ P / 4 := by
  classical
  obtain ⟨hδ, hCtop, hB1, hρ, hP, hreal, hδ0, hδ3, hcore, hB0, hcont, htame,
    hzero, hTτ, hball, hforce, -⟩ := hlo
  set R : ℝ := lowRegularityStateRadius Ctop B1 ρ P with hRdef
  have hRpos : 0 < R := lowRegularityStateRadius_pos hCtop hB1 hρ hP
  have hQnn : 0 ≤ lowRegularityOuterRadius Ctop ρ P := (lowRegularityOuterRadius_pos hCtop hρ hP).le
  set Nfun := boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal
    with hNfundef
  set A : ℝ≥0 := Real.toNNReal (Ctop * lowRegularityOuterRadius Ctop ρ P / R) with hAdef
  set B : ℝ≥0 := Real.toNNReal B0 with hBdef
  set C : ℝ≥0 := Real.toNNReal B1 with hCdef
  have hAarg : 0 ≤ Ctop * lowRegularityOuterRadius Ctop ρ P / R :=
    div_nonneg (mul_nonneg hCtop hQnn) hRpos.le
  have hAcoe : (A : ℝ) = Ctop * lowRegularityOuterRadius Ctop ρ P / R :=
    Real.coe_toNNReal _ hAarg
  have hBcoe : (B : ℝ) = B0 := Real.coe_toNNReal _ hB0
  have hCcoe : (C : ℝ) = B1 := Real.coe_toNNReal _ hB1
  have hAR : (A : ℝ) * R = Ctop * lowRegularityOuterRadius Ctop ρ P := by
    rw [hAcoe]
    exact div_mul_cancel₀ _ hRpos.ne'
  have hsmallA : (A : ℝ) * R ≤ 1 / 16 := by
    rw [hAR]; exact lowRegularityOuterRadius_small hCtop
  have hsmallC : (C : ℝ) * R ≤ 1 / 16 := by
    rw [hCcoe, hRdef]; exact lowRegularityStateRadius_small hB1
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
    exact htame u u'
  have hDnn : 0 ≤ D := le_trans (norm_nonneg _) hzero
  have hTB : T ≤ 1 / (64 * ((B : ℝ) + 1) ^ 2) := by
    rw [hBcoe]
    exact le_trans hTτ (le_trans (min_le_right _ _) (min_le_left _ _))
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
        (I := I) (M := M) g₀ 1 hRpos N Nfun hcont A B C D
        hDnn hzero hsmallA hsmallC hsingle
    have hTT₀ : T ≤ T₀ := by
      rw [hT₀eq, hBcoe]
      exact hTτ
    obtain ⟨u, gforce, hu, hstate, hgE, htr, hpde, hgball⟩ :=
      hsol hT hTT₀
    subst hu
    refine ⟨gforce, ⟨?_, hstate, hgE, htr, hpde, hgball⟩, ?_⟩
    · exact projForce_fixed (I := I) (M := M) g₀ 1 N gforce
        (fun t => aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1 hRpos.le)
          (maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
            (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) gforce) t)
        hgE
    · exact projFixTame_le_two (I := I) (M := M) g₀ 1 hRpos N hcont hsingle
        hsmallA hsmallC hT hT1 hTB fLo gforce hball hgball hforce hgE
  choose fseq hpack hK using hex
  exact ⟨fseq, projFix_tendsto (I := I) (M := M) g₀ (K := 2) fLo fseq hK, hpack⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_galerkin_projected_forcing_sequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_galerkin_projected_forcing_sequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_galerkin_projected_forcing_sequence ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_galerkin_projected_forcing_sequence

theorem galerkin_projected_forcing_sequence_tendsto (g₀ : SmoothRiemannianMetric I M) {T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (fLo : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hlo : IsLowRegularitySolution (I := I) (M := M) g₀ hT fLo) :
    ∃ (δ Ctop B1 ρ P : ℝ) (hδ : δ < 1) (hCtop : 0 ≤ Ctop) (hB1 : 0 ≤ B1)
      (hρ : 0 < ρ) (hP : 0 < P)
      (hreal : ∀ S : Integral.L2.SmoothCcTensor g₀ 0 2,
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ P →
          MetricRealization.gFibreOpBound (I := I) (M := M) g₀
            (MetricRealization.ccTensorBilinSymm (I := I) g₀ S) δ)
      (_hδ0 : 0 ≤ δ) (_hδ3 : δ ≤ 1 / 3)
      (_hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g₀ hδ
        (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1) (ρ := ρ)
          hP.le hreal)))
      (B0 : ℝ) (_hB0 : 0 ≤ B0)
      (_hcont : Continuous
        (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal))
      (_htame : ∀ u v : lowerState (I := I) (M := M) g₀ 1
          (lowRegularityStateRadius Ctop B1 ρ P),
        ‖boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal u -
            boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal v‖ ≤
          Ctop * lowRegularityOuterRadius Ctop ρ P *
              ‖(u.1 : TensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2)) - v.1‖ +
            B0 *
              ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
                ((u.1 : TensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2)) - v.1)‖ +
            B1 *
                (‖(u.1 : TensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2))‖ +
                  ‖(v.1 : TensorHs (I := I) (M := M) g₀ 0 2
                    (((1 : ℕ) : ℝ) + 2))‖) *
              ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
                ((u.1 : TensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2)) - v.1)‖)
      (fseq : ℕ → timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T),
      _root_.Filter.Tendsto fseq _root_.Filter.atTop (𝓝 fLo) ∧
      ∀ N : ℕ,
        timeL2EigenProj (I := I) (M := M) g₀ ((1 : ℕ) : ℝ) T N (fseq N) =
            fseq N ∧
          (∀ᵐ t ∂(timeMeasure T),
            maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
              (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
              (fseq N) t ∈
              lowerState (I := I) (M := M) g₀ 1 (lowRegularityStateRadius Ctop B1 ρ P)) ∧
          fseq N =ᵐ[timeMeasure T]
            (fun t => projNfun (I := I) (M := M) g₀ 1 N
              (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal)
              (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1
                  (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le)
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
          ‖fseq N‖ ≤ lowRegularityStateRadius Ctop B1 ρ P / 4 := by
  obtain ⟨δ, Ctop, B0, B1, D, ρ, P, hδ, hCtop, hB1, hρ, hP, hreal, hδ0, hδ3,
    hcore, hB0, hcont, htame, hzero, hTτ, hball, hforce⟩ := hlo
  have hat : IsLowRegularitySolutionAt (I := I) (M := M) (δ := δ) (Ctop := Ctop)
      (B0 := B0) (B1 := B1) (D := D) (ρ := ρ) (P := P)
      g₀ hT hT1 fLo (lowRegularityStateRadius Ctop B1 ρ P) :=
    ⟨hδ, hCtop, hB1, hρ, hP, hreal, hδ0, hδ3, hcore, hB0, hcont, htame,
      hzero, hTτ, hball, hforce, le_rfl⟩
  obtain ⟨fseq, hconv, hpack⟩ :=
    exists_galerkin_projected_forcing_sequence (I := I) (M := M) g₀ hT hT1 fLo hat
  exact ⟨δ, Ctop, B1, ρ, P, hδ, hCtop, hB1, hρ, hP, hreal, hδ0, hδ3,
    hcore, B0, hB0, hcont, htame, fseq, hconv, hpack⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.galerkin_projected_forcing_sequence_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.galerkin_projected_forcing_sequence_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.galerkin_projected_forcing_sequence_tendsto ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.galerkin_projected_forcing_sequence_tendsto

theorem exists_galerkin_projected_forcing_sequence_with_mode_convergence (g₀ : SmoothRiemannianMetric I M)
    {δ Ctop B0 B1 D ρ P Rcap T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (fLo : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hlo : IsLowRegularitySolutionAt (I := I) (M := M) (δ := δ) (Ctop := Ctop)
      (B0 := B0) (B1 := B1) (D := D) (ρ := ρ) (P := P)
      g₀ hT hT1 fLo Rcap) :
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
              lowerState (I := I) (M := M) g₀ 1 (lowRegularityStateRadius Ctop B1 ρ P)) ∧
          fseq N =ᵐ[timeMeasure T]
            (fun t => projNfun (I := I) (M := M) g₀ 1 N
              (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀
                hlo.threshold_lt_one hlo.top_nonneg hlo.slope_nonneg hlo.outer_pos hlo.realize_pos hlo.metric_realization)
              (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1
                  (lowRegularityStateRadius_pos hlo.top_nonneg hlo.slope_nonneg hlo.outer_pos hlo.realize_pos).le)
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
          ‖fseq N‖ ≤ lowRegularityStateRadius Ctop B1 ρ P / 4 := by
  obtain ⟨fseq, hconv, hpack⟩ :=
    exists_galerkin_projected_forcing_sequence (I := I) (M := M) g₀ hT hT1 fLo hlo
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
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_galerkin_projected_forcing_sequence_with_mode_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_galerkin_projected_forcing_sequence_with_mode_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_galerkin_projected_forcing_sequence_with_mode_convergence ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_galerkin_projected_forcing_sequence_with_mode_convergence

theorem galerkin_projected_forcing_sequence_mode_tendsto (g₀ : SmoothRiemannianMetric I M) {T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (fLo : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hlo : IsLowRegularitySolution (I := I) (M := M) g₀ hT fLo) :
    ∃ (δ Ctop B1 ρ P : ℝ) (hδ : δ < 1) (hCtop : 0 ≤ Ctop) (hB1 : 0 ≤ B1)
      (hρ : 0 < ρ) (hP : 0 < P)
      (hreal : ∀ S : Integral.L2.SmoothCcTensor g₀ 0 2,
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ P →
          MetricRealization.gFibreOpBound (I := I) (M := M) g₀
            (MetricRealization.ccTensorBilinSymm (I := I) g₀ S) δ)
      (_hδ0 : 0 ≤ δ) (_hδ3 : δ ≤ 1 / 3)
      (_hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g₀ hδ
        (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1) (ρ := ρ)
          hP.le hreal)))
      (B0 : ℝ) (_hB0 : 0 ≤ B0)
      (_hcont : Continuous
        (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal))
      (_htame : ∀ u v : lowerState (I := I) (M := M) g₀ 1
          (lowRegularityStateRadius Ctop B1 ρ P),
        ‖boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal u -
            boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal v‖ ≤
          Ctop * lowRegularityOuterRadius Ctop ρ P *
              ‖(u.1 : TensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2)) - v.1‖ +
            B0 *
              ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
                ((u.1 : TensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2)) - v.1)‖ +
            B1 *
                (‖(u.1 : TensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2))‖ +
                  ‖(v.1 : TensorHs (I := I) (M := M) g₀ 0 2
                    (((1 : ℕ) : ℝ) + 2))‖) *
              ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
                ((u.1 : TensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2)) - v.1)‖)
      (fseq : ℕ → timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T),
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
              lowerState (I := I) (M := M) g₀ 1 (lowRegularityStateRadius Ctop B1 ρ P)) ∧
          fseq N =ᵐ[timeMeasure T]
            (fun t => projNfun (I := I) (M := M) g₀ 1 N
              (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal)
              (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1
                  (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le)
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
          ‖fseq N‖ ≤ lowRegularityStateRadius Ctop B1 ρ P / 4 := by
  obtain ⟨δ, Ctop, B1, ρ, P, hδ, hCtop, hB1, hρ, hP, hreal, hδ0, hδ3, hcore,
    B0, hB0, hcont, htame, fseq, hconv, hpack⟩ :=
    galerkin_projected_forcing_sequence_tendsto (I := I) (M := M) g₀ hT hT1 fLo hlo
  refine ⟨δ, Ctop, B1, ρ, P, hδ, hCtop, hB1, hρ, hP, hreal, hδ0, hδ3, hcore,
    B0, hB0, hcont, htame, fseq, hconv, fun i t ht => ?_, hpack⟩
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
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.galerkin_projected_forcing_sequence_mode_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.galerkin_projected_forcing_sequence_mode_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.galerkin_projected_forcing_sequence_mode_tendsto ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.galerkin_projected_forcing_sequence_mode_tendsto

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
