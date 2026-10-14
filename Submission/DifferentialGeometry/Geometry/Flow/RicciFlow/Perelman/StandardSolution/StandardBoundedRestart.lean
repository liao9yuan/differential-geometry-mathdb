import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CapReferenceRestart
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardBoundedTerminal
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardClosedRestart

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

theorem standard_closed_restart_extension_of_curvature_bound
    (T K : ℝ) (hT : 0 < T) (hK : 0 ≤ K) :
    ∃ τ : ℝ, 0 < τ ∧ ∃ KR : ℝ, 0 ≤ KR ∧
      ∀ S : PartialStandardSolution, S.lifetime = ENNReal.ofReal T →
        (∀ t ∈ _root_.Set.Ico 0 T, ∀ x : E3,
          Real.sqrt (normSq0S (S.metric t) x 4 (metricRm04 (S.metric t) x)) ≤ K) →
        ∃ G H : ℝ → SmoothRiemannianMetric (𝓡 3) E3,
        ∃ Q : PartialStandardSolution,
          (∀ t ∈ _root_.Set.Ico 0 T, G t = S.metric t) ∧ H 0 = G T ∧
          Q.metric = gluedFamily G H T ∧
          Q.lifetime = ENNReal.ofReal (T + τ) ∧ S.IsExtendedBy Q ∧
          S.lifetime < Q.lifetime ∧
          (∀ t ∈ _root_.Set.Icc 0 (T + τ), RiemannianMetricComplete (Q.metric t)) ∧
          ∀ t ∈ _root_.Set.Icc 0 (T + τ), ∀ x : E3,
            Real.sqrt (normSq0S (Q.metric t) x 4 (metricRm04 (Q.metric t) x)) ≤ KR := by
  obtain ⟨Λ, hΛ, C, L, hC, hL, hfamily⟩ :=
    standard_smooth_terminal_families_of_curvature_bound T K hT hK
  let D : ℕ → ℝ := fun k => L k * T
  have hD (k : ℕ) : 0 ≤ D k := mul_nonneg (hL k) hT.le
  have hell : 0 < Λ⁻¹ := inv_pos.mpr (zero_lt_one.trans_le hΛ)
  obtain ⟨τ, hτ, B, hB, ΛZ, hΛZ, CZ, LZ, hCZ, hLZ, hrestart⟩ :=
    exists_uniform_complete_cap_reference_core_restarts Λ⁻¹ hell D hD
  refine ⟨τ, hτ, _root_.Max.max 0 (_root_.Max.max K (567 * B 0)), le_max_left _ _, ?_⟩
  intro S htime hRm
  obtain ⟨G, hEq, hzero, hc, he, hCov, hLip, hj, hpde, hgram, hclosed⟩ :=
    hfamily S htime.symm.le hRm
  have hlow (x : E3) (v : TangentSpace (𝓡 3) x) :
      Λ⁻¹ * DifferentialGeometry.PDE.RicciFlow.StandardCap.metric.inner x v v ≤ (G T).inner x v v :=
    ((he T ⟨hT.le, le_rfl⟩).2 x (_root_.Set.mem_univ x) v).1
  have hdiff (k : ℕ) (x : E3) :
      DifferentialGeometry.CheegerGromovCompactness.metricDerivNorm k (G T)
        DifferentialGeometry.PDE.RicciFlow.StandardCap.metric DifferentialGeometry.PDE.RicciFlow.StandardCap.metric x ≤ D k := by
    have hh := hLip k T ⟨hT.le, le_rfl⟩ 0 ⟨le_rfl, hT.le⟩ x
    simpa only [D, hzero, sub_zero, abs_of_nonneg hT.le] using hh
  let north : S3 := ⟨EuclideanSpace.single 0 1, by simp⟩
  obtain ⟨Z, hZ, hZfields, bf, co, hbound, hcovTail, hinit, hcomplete,
    hjlim, hglim, hplim, hllim, hcurv⟩ := hrestart (G T) hlow hdiff north
  obtain ⟨Q, hQtime, hQmetric, hExt, hstrict, hQcomp, hQcurv⟩ :=
    S.exists_strict_extension_of_closed_restart T τ hT hτ htime G co.gInf
      hEq hzero hc hj hpde (hclosed T ⟨hT.le, le_rfl⟩)
      hinit hcomplete hjlim hplim K (567 * B 0) hRm hcurv
  exact ⟨G, co.gInf, Q, hEq, hinit, hQmetric, hQtime, hExt, hstrict, hQcomp, hQcurv⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.standard_closed_restart_extension_of_curvature_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.standard_closed_restart_extension_of_curvature_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.standard_closed_restart_extension_of_curvature_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.standard_closed_restart_extension_of_curvature_bound
end DifferentialGeometry.PDE.RicciFlow
