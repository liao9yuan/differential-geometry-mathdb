import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CompactDoublePatch

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.E3 target :: scope.openDecls } }
private abbrev E4 := EuclideanSpace ℝ (Fin 4)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.E4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.E4 target :: scope.openDecls } }
private abbrev S3 := Metric.sphere (0 : E4) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.S3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.S3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE4HAddOfNat : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE4HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE4HAddOfNat target :: scope.openDecls } }

def compactDoubleCorePartialDiffeomorph (north : S3) (R : ℝ) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) E3 S3 ∞ := by
  let Φ := compactDoubleCapPartialDiffeomorph north R
  have hsrc : Metric.ball (0 : E3) (R - 2) ⊆ Φ.source := by
    change Metric.ball (0 : E3) (R - 2) ⊆ Metric.ball 0 (R + 1)
    exact Metric.ball_subset_ball (by linarith)
  exact PartialDiffeomorph.ofOpenPartialHomeomorphRestr
    Φ.toOpenPartialHomeomorph
    (Metric.ball 0 (R - 2)) Metric.isOpen_ball hsrc
    (Φ.contMDiffOn_toFun.mono hsrc)
    (Φ.contMDiffOn_invFun.mono (by
      rintro _ ⟨x, hx, rfl⟩
      exact Φ.map_source' (hsrc hx)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCorePartialDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCorePartialDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCorePartialDiffeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCorePartialDiffeomorph

theorem compactDoubleCorePartialDiffeomorph_apply
    (north : S3) (R : ℝ) (x : E3) :
    compactDoubleCorePartialDiffeomorph north R x =
      compactDoubleCapMap north R x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCorePartialDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCorePartialDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCorePartialDiffeomorph_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCorePartialDiffeomorph_apply

theorem compactDoubleCorePartialDiffeomorph_symm_apply
    (north : S3) (R : ℝ) (p : S3) :
    (compactDoubleCorePartialDiffeomorph north R).symm p =
      (compactDoubleCapPartialDiffeomorph north R).symm p := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCorePartialDiffeomorph_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCorePartialDiffeomorph_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCorePartialDiffeomorph_symm_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCorePartialDiffeomorph_symm_apply

theorem compactDoubleCorePartialDiffeomorph_source
    (north : S3) (R : ℝ) :
    (compactDoubleCorePartialDiffeomorph north R).source =
      Metric.ball 0 (R - 2) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCorePartialDiffeomorph_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCorePartialDiffeomorph_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCorePartialDiffeomorph_source ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCorePartialDiffeomorph_source

theorem compactDoubleCorePartialDiffeomorph_target
    (north : S3) (R : ℝ) :
    (compactDoubleCorePartialDiffeomorph north R).target =
      compactDoubleCapMap north R '' Metric.ball 0 (R - 2) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCorePartialDiffeomorph_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCorePartialDiffeomorph_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCorePartialDiffeomorph_target ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCorePartialDiffeomorph_target

theorem compactDoubleCorePartialDiffeomorph_mfderiv
    (north : S3) (R : ℝ) (x : E3) :
    mfderiv (𝓡 3) (𝓡 3) (compactDoubleCorePartialDiffeomorph north R) x =
      mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCorePartialDiffeomorph_mfderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCorePartialDiffeomorph_mfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCorePartialDiffeomorph_mfderiv ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCorePartialDiffeomorph_mfderiv

theorem compactDoubleCorePartialDiffeomorph_truncation_pullback
    (north : S3) (R : ℝ)
    (hR : _root_.Max.max transitionEnd 2 + 2 ≤ R)
    (g : SmoothRiemannianMetric (𝓡 3) E3)
    (x : E3)
    (hx : x ∈ (compactDoubleCorePartialDiffeomorph north R).source)
    (v w : E3) :
    (compactDoubleTruncationMetric north R hR g).inner
      (compactDoubleCorePartialDiffeomorph north R x)
      (mfderiv (𝓡 3) (𝓡 3)
        (compactDoubleCorePartialDiffeomorph north R) x v)
      (mfderiv (𝓡 3) (𝓡 3)
        (compactDoubleCorePartialDiffeomorph north R) x w) =
      g.inner x v w := by
  have hn : ‖x‖ < R - 2 := by
    simpa only [compactDoubleCorePartialDiffeomorph_source,
      Metric.mem_ball, dist_zero_right] using hx
  exact compactDoubleTruncationMetric_cap_pullback_core
    north R hR g x hn.le v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCorePartialDiffeomorph_truncation_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCorePartialDiffeomorph_truncation_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCorePartialDiffeomorph_truncation_pullback ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.compactDoubleCorePartialDiffeomorph_truncation_pullback

end DifferentialGeometry.PDE.RicciFlow.StandardCap
