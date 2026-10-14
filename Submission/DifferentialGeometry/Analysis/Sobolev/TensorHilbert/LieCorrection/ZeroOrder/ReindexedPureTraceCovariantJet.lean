import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CovariantJet.Naturality
import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.LieCorrection.ZeroOrder.MixedConnectionExpansion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Spectral

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem reindexedPureTrace_sub
    (g gT gU : SmoothRiemannianMetric I M) (p : ℕ)
    (σ : Equiv.Perm (Fin (p + 2))) :
    reindexedPureTrace (I := I) (M := M) g gT p σ -
      reindexedPureTrace (I := I) (M := M) g gU p σ =
      reindexCoefficientInputSlots (I := I) (M := M) g (p + 2) p
        (pureTrace (I := I) (M := M) g gT p -
          pureTrace (I := I) (M := M) g gU p) σ := by
  rw [reindexedPureTrace, reindexedPureTrace, ← reindexCoefficientInputSlots_sub]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.reindexedPureTrace_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.reindexedPureTrace_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.reindexedPureTrace_sub ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.reindexedPureTrace_sub

omit [NeZero (Module.finrank ℝ E)] in
theorem covariantJetNormSq_reindexedPureTrace
    (g gm : SmoothRiemannianMetric I M) (p m : ℕ)
    (σ : Equiv.Perm (Fin (p + 2))) :
    covariantJetNormSq (I := I) (M := M) g m
        (reindexedPureTrace (I := I) (M := M) g gm p σ) =
      covariantJetNormSq (I := I) (M := M) g m
        (pureTrace (I := I) (M := M) g gm p) := by
  rw [reindexedPureTrace, covariantJetNormSq_reindexCoefficientInputSlots]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.covariantJetNormSq_reindexedPureTrace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.covariantJetNormSq_reindexedPureTrace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.covariantJetNormSq_reindexedPureTrace ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.covariantJetNormSq_reindexedPureTrace

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
