import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardTerminalCoreLimits
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardClosedRestart
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCurvatureControl

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E3 target :: scope.openDecls } }
private abbrev E4 := EuclideanSpace ℝ (Fin 4)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E4 target :: scope.openDecls } }
private abbrev S3 := Metric.sphere (0 : E4) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.S3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.S3 target :: scope.openDecls } }

theorem standard_uniform_closed_restart_extension :
    ∃ α : ℝ, 0 < α ∧ ∃ τ : ℝ, 0 < τ ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ S : PartialStandardSolution, ∀ T : ℝ, 0 < T → T ≤ α →
        S.lifetime = ENNReal.ofReal T →
        ∃ G H : ℝ → SmoothRiemannianMetric (𝓡 3) E3,
        ∃ Q : PartialStandardSolution,
          (∀ t ∈ _root_.Set.Ico 0 T, G t = S.metric t) ∧ H 0 = G T ∧
          Q.metric = gluedFamily G H T ∧
          Q.lifetime = ENNReal.ofReal (T + τ) ∧ S.IsExtendedBy Q ∧
          S.lifetime < Q.lifetime ∧
          (∀ t ∈ _root_.Set.Icc 0 (T + τ), RiemannianMetricComplete (Q.metric t)) ∧
          ∀ t ∈ _root_.Set.Icc 0 (T + τ), ∀ x : E3,
            Real.sqrt (normSq0S (Q.metric t) x 4 (metricRm04 (Q.metric t) x)) ≤ K := by
  obtain ⟨α, hα, Λ, hΛ, C, L, D, A, hC, hL, hD, hA, ell, hell,
    τ, hτ, B, hB, ΛZ, hΛZ, CZ, LZ, hCZ, hLZ, hfamily⟩ :=
      standard_uniform_terminal_core_limits
  obtain ⟨β, hβ, KG, hKG, hcurv⟩ := standard_uniform_initial_curvature_control
  refine ⟨min α β, lt_min hα hβ, τ, hτ, _root_.Max.max 0 (_root_.Max.max KG (567 * B 0)),
    le_max_left _ _, ?_⟩
  intro S T hT hTα htime
  obtain ⟨G, hEq, hzero, hc, he, hCov, hLip, hj, hpde, hgram, hclosed,
    htrunc, hjets, hflows, hlimits⟩ :=
      hfamily S T hT (hTα.trans (min_le_left _ _)) htime.symm.le
  let north : S3 := ⟨EuclideanSpace.single 0 1, by simp⟩
  obtain ⟨Z, hZ, hZfields, bf, co, hbound, hcovTail, hinit, hcomplete,
    hjlim, hglim, hplim, hllim, hRm⟩ := hlimits north
  have hleft : ∀ t ∈ _root_.Set.Ico 0 T, ∀ x : E3,
      Real.sqrt (normSq0S (S.metric t) x 4 (metricRm04 (S.metric t) x)) ≤ KG := by
    intro t ht x
    have htl : ENNReal.ofReal t < S.lifetime := by
      rw [htime]
      exact (ENNReal.ofReal_lt_ofReal_iff hT).mpr ht.2
    exact hcurv S t ht.1 (ht.2.le.trans (hTα.trans (min_le_right _ _))) htl
      t ⟨ht.1, le_rfl⟩ x
  obtain ⟨Q, hQtime, hQmetric, hExt, hstrict, hQcomp, hQcurv⟩ :=
    S.exists_strict_extension_of_closed_restart T τ hT hτ htime G co.gInf
      hEq hzero hc hj hpde (hclosed T ⟨hT.le, le_rfl⟩)
      hinit hcomplete hjlim hplim KG (567 * B 0) hleft hRm
  exact ⟨G, co.gInf, Q, hEq, hinit, hQmetric, hQtime, hExt, hstrict, hQcomp, hQcurv⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.standard_uniform_closed_restart_extension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.standard_uniform_closed_restart_extension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.standard_uniform_closed_restart_extension ``Submission.DifferentialGeometry.PDE.RicciFlow.standard_uniform_closed_restart_extension
end DifferentialGeometry.PDE.RicciFlow
