import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Existence.Quasilinear
import Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.StrongBackwardIdentification

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry.Analysis.Spectral

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

omit [BoundarylessManifold I M] in
theorem mixForce_unique
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {L : ℝ≥0}
    {Nfun : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) →
      TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)}
    (hLip : LipschitzWith L Nfun) {C₁ C₂ : ℝ≥0}
    (hsingle : ∀ (u u' : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)),
      ‖Nfun u - Nfun u'‖ ≤
        (C₁ : ℝ) * _root_.Max.max
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) u‖
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) u'‖ * ‖u - u'‖ +
          (C₂ : ℝ) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (u - u')‖)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hsmall :
      (C₁ : ℝ) * Real.sqrt (1 + T) * ρ * (1 + T) +
          (C₂ : ℝ) * (2 * Real.sqrt T) < 1)
    {force₁ force₂ : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T}
    (hball₁ : ‖force₁‖ ≤ ρ) (hball₂ : ‖force₂‖ ≤ ρ)
    (hfix₁ : force₁ = nemytskii (I := I) (M := M) hLip
      (maximalRegularityDuhamelSolutionField (I := I) (M := M) (a : ℝ) hT
        (0 : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) force₁))
    (hfix₂ : force₂ = nemytskii (I := I) (M := M) hLip
      (maximalRegularityDuhamelSolutionField (I := I) (M := M) (a : ℝ) hT
        (0 : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) force₂)) :
    force₁ = force₂ := by
  have hdist := nemytskiiMixedForcingMap_dist_le (I := I) (M := M)
    g₀ a hLip hsingle hT hT1 hρ force₁ force₂ hball₁ hball₂
  rw [nemytskiiMixedForcingMap_apply, nemytskiiMixedForcingMap_apply,
    ← hfix₁, ← hfix₂] at hdist
  by_contra hne
  have hnorm : 0 < ‖force₁ - force₂‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hgap : 0 <
      (1 - ((C₁ : ℝ) * Real.sqrt (1 + T) * ρ * (1 + T) +
        (C₂ : ℝ) * (2 * Real.sqrt T))) * ‖force₁ - force₂‖ :=
    mul_pos (sub_pos.mpr hsmall) hnorm
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.mixForce_unique then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.mixForce_unique"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.mixForce_unique ``Submission.DifferentialGeometry.Analysis.Spectral.mixForce_unique

omit [BoundarylessManifold I M] in
theorem deTurckStrong_unique
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {L : ℝ≥0}
    {Nfun : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) →
      TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)}
    (hLip : LipschitzWith L Nfun) {C₁ C₂ : ℝ≥0}
    (hsingle : ∀ (u u' : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)),
      ‖Nfun u - Nfun u'‖ ≤
        (C₁ : ℝ) * _root_.Max.max
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) u‖
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) u'‖ * ‖u - u'‖ +
          (C₂ : ℝ) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (u - u')‖)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hsmall :
      (C₁ : ℝ) * Real.sqrt (1 + T) * ρ * (1 + T) +
          (C₂ : ℝ) * (2 * Real.sqrt T) < 1)
    (force₁ force₂ : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (u₁ u₂ : timeH1 (TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (field₁ field₂ :
      timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) T)
    (htrace₁ : timeH1.trace0 _ T u₁ = 0)
    (htrace₂ : timeH1.trace0 _ T u₂ = 0)
    (hlink₁ :
      timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) field₁ =
        timeH1.toTimeL2 (TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T u₁)
    (hlink₂ :
      timeL2Inclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) field₂ =
        timeH1.toTimeL2 (TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T u₂)
    (heq₁ : timeH1.timeDeriv _ T u₁ =
      timeScaleLaplacian (I := I) (M := M) (a : ℝ) field₁ + force₁)
    (heq₂ : timeH1.timeDeriv _ T u₂ =
      timeScaleLaplacian (I := I) (M := M) (a : ℝ) field₂ + force₂)
    (hforce₁ : force₁ = nemytskii (I := I) (M := M) hLip field₁)
    (hforce₂ : force₂ = nemytskii (I := I) (M := M) hLip field₂)
    (hball₁ : ‖force₁‖ ≤ ρ) (hball₂ : ‖force₂‖ ≤ ρ) :
    force₁ = force₂ ∧ field₁ = field₂ ∧ u₁ = u₂ := by
  let u₀ : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) := 0
  have hcompact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
  have htrace₁' : timeH1.trace0 _ T u₁ =
      tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) u₀ := by
    simpa only [u₀, map_zero] using htrace₁
  have htrace₂' : timeH1.trace0 _ T u₂ =
      tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) u₀ := by
    simpa only [u₀, map_zero] using htrace₂
  have hfix₁ := strongNemy_fixed (I := I) (M := M) hT hcompact
    u₀ force₁ u₁ field₁ hLip htrace₁' hlink₁ heq₁ hforce₁
  have hfix₂ := strongNemy_fixed (I := I) (M := M) hT hcompact
    u₀ force₂ u₂ field₂ hLip htrace₂' hlink₂ heq₂ hforce₂
  have hforces : force₁ = force₂ :=
    mixForce_unique (I := I) (M := M) g₀ a hLip hsingle hT hT1 hρ hsmall
      hball₁ hball₂ hfix₁ hfix₂
  rcases strongPair_eq_duhamel (I := I) (M := M) hT hcompact
      u₀ force₁ u₁ field₁ htrace₁' hlink₁ heq₁ with ⟨hfield₁, hu₁⟩
  rcases strongPair_eq_duhamel (I := I) (M := M) hT hcompact
      u₀ force₂ u₂ field₂ htrace₂' hlink₂ heq₂ with ⟨hfield₂, hu₂⟩
  refine ⟨hforces, ?_, ?_⟩
  · calc
      field₁ = maximalRegularityDuhamelSolutionField (I := I) (M := M)
          (a : ℝ) hT u₀ force₁ := hfield₁
      _ = maximalRegularityDuhamelSolutionField (I := I) (M := M)
          (a : ℝ) hT u₀ force₂ := by rw [hforces]
      _ = field₂ := hfield₂.symm
  · calc
      u₁ = maximalRegularityDuhamelMap (I := I) (M := M)
          (a : ℝ) hT u₀ force₁ := hu₁
      _ = maximalRegularityDuhamelMap (I := I) (M := M)
          (a : ℝ) hT u₀ force₂ := by rw [hforces]
      _ = u₂ := hu₂.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.deTurckStrong_unique then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.deTurckStrong_unique"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.deTurckStrong_unique ``Submission.DifferentialGeometry.Analysis.Spectral.deTurckStrong_unique

end DifferentialGeometry.Analysis.Spectral

end
