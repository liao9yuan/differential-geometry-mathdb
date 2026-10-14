import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardFirstTimeJet
import Submission.DifferentialGeometry.Geometry.Curvature.RiemannRicciNorm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Filter _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E3 target :: scope.openDecls } }

section Maps

variable {τ : ℝ} {hτ : 0 < τ} {hlt : ENNReal.ofReal τ < uniformStandardLifetime}
  {S : ℕ → StandardSolution} {x : ℕ → E3}
  {P : PointedRiemannianManifold (𝓡 3)} {φ : ℕ → ℕ}
  (Φ : PointedCGHMaps (standardClosedPointedFlowSequence τ hτ hlt S x) P φ)

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instTopologicalSpaceMEuclideanSpaceRealFinOfNatNat : TopologicalSpace P.M := P.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instTopologicalSpaceMEuclideanSpaceRealFinOfNatNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instTopologicalSpaceMEuclideanSpaceRealFinOfNatNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instChartedSpaceE3MEuclideanSpaceRealFinOfNatNat : ChartedSpace E3 P.M := P.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instChartedSpaceE3MEuclideanSpaceRealFinOfNatNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instChartedSpaceE3MEuclideanSpaceRealFinOfNatNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instT2SpaceMEuclideanSpaceRealFinOfNatNat : T2Space P.M := P.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instT2SpaceMEuclideanSpaceRealFinOfNatNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instT2SpaceMEuclideanSpaceRealFinOfNatNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopM : IsManifold (𝓡 3) ∞ P.M := P.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopM target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instSigmaCompactSpaceMEuclideanSpaceRealFinOfNatNat : SigmaCompactSpace P.M := P.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instSigmaCompactSpaceMEuclideanSpaceRealFinOfNatNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instSigmaCompactSpaceMEuclideanSpaceRealFinOfNatNat target :: scope.openDecls } }

variable (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instTopologicalSpaceSourceDomainEuclideanSpaceRealFinOfNatNat (j : ℕ) : TopologicalSpace (SourceDomain Φ j) := sourceDomTop Φ j

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instTopologicalSpaceSourceDomainEuclideanSpaceRealFinOfNatNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instTopologicalSpaceSourceDomainEuclideanSpaceRealFinOfNatNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instChartedSpaceE3SourceDomainEuclideanSpaceRealFinOfNatNat (j : ℕ) : ChartedSpace E3 (SourceDomain Φ j) := sourceDomCharted Φ j

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instChartedSpaceE3SourceDomainEuclideanSpaceRealFinOfNatNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instChartedSpaceE3SourceDomainEuclideanSpaceRealFinOfNatNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instT2SpaceSourceDomainEuclideanSpaceRealFinOfNatNat (j : ℕ) : T2Space (SourceDomain Φ j) := sourceDomT2 Φ j

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instT2SpaceSourceDomainEuclideanSpaceRealFinOfNatNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instT2SpaceSourceDomainEuclideanSpaceRealFinOfNatNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopSourceDomain (j : ℕ) : IsManifold (𝓡 3) ∞ (SourceDomain Φ j) := sourceDomSmooth Φ j

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopSourceDomain
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopSourceDomain target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instSigmaCompactSpaceSourceDomainEuclideanSpaceRealFinOfNatNat (j : ℕ) : SigmaCompactSpace (SourceDomain Φ j) :=
  sourceDomSigmaOf Φ j (standardClosedPointedMaps_sourceSigma Φ j)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instSigmaCompactSpaceSourceDomainEuclideanSpaceRealFinOfNatNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instSigmaCompactSpaceSourceDomainEuclideanSpaceRealFinOfNatNat target :: scope.openDecls } }

theorem standard_closed_limit_curvature_bound
    (hinit : ∀ j, sourceMetric Φ hsrc htgt j 0 = sourceMetricRestriction Φ P.metric j)
    (bf : BumpFamily Φ) (co : FlowMetricConvergenceData Φ P.metric bf hsrc htgt 0 τ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ _root_.Set.Icc 0 τ, ∀ q : P.M,
      normSq0S (co.gInf t) q 4 (metricRm04 (co.gInf t) q) ≤ B := by
  obtain ⟨Λ, hΛ, _C, _L, _hC, _hL, hb⟩ := standard_closed_reference_bounds τ hτ hlt
  have hbounds := hb S x P φ Φ hsrc htgt hinit
  have hcLow : 0 < Λ⁻¹ := inv_pos.mpr (zero_lt_one.trans_le hΛ)
  have hbound : ∀ j t, t ∈ _root_.Set.Icc 0 τ → ∀ (y : SourceDomain Φ j)
      (v : TangentSpace (𝓡 3) y),
      Λ⁻¹ * P.metric.inner y.val v v ≤ (sourceMetric Φ hsrc htgt j t).inner y v v := by
    intro j t ht y v
    exact (((hbounds.1 j).1 t ht).2 y (_root_.Set.mem_univ y) v).1
  have hcovTail := covTail_of_bounds Φ P.metric bf hsrc htgt 0 τ (by
    intro a
    obtain ⟨Ca, hCa, hcov⟩ := hbounds.2.cov a
    exact ⟨Ca, hCa, fun j t ht y _ => hcov j t ht y⟩)
  obtain ⟨hlife, K, hK, hRm⟩ := uniformStandardLifetime_slab τ hτ.le hlt
  refine ⟨(567 * K) ^ 2, sq_nonneg _, ?_⟩
  intro t ht q
  have hconv := FlowMetricConvergenceData.ricNorm_convergence_at Φ P.metric bf hsrc htgt
    0 τ Λ⁻¹ hcLow hbound hcovTail co ht q
  have hRic : normSq0S (co.gInf t) q 2 (metricRicci (co.gInf t) q) ≤ (9 * K) ^ 2 := by
    apply le_of_tendsto hconv
    filter_upwards with k
    have h := ricTower_normSq_le (S ((φ ∘ co.φ) k)).val.toSolutionOn t 0
      (Φ.map (co.φ k) q)
    have hcurv := (Real.sqrt_le_iff.mp
      (hRm (S ((φ ∘ co.φ) k)) t ht (Φ.map (co.φ k) q))).2
    change ricciNorm (S ((φ ∘ co.φ) k)).val.toSolutionOn t (Φ.map (co.φ k) q) ≤
      (Module.finrank ℝ E3 : ℝ) ^ 4 *
        normSq0S ((S ((φ ∘ co.φ) k)).val.metric t) (Φ.map (co.φ k) q) 4
          (metricRm04 ((S ((φ ∘ co.φ) k)).val.metric t) (Φ.map (co.φ k) q)) at h
    norm_num only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat] at h
    change ricciNorm (S ((φ ∘ co.φ) k)).val.toSolutionOn t (Φ.map (co.φ k) q) ≤ _
    nlinarith
  have hRicRoot : Real.sqrt (normSq0S (co.gInf t) q 2 (metricRicci (co.gInf t) q)) ≤ 9 * K :=
    Real.sqrt_le_iff.mpr ⟨by positivity, hRic⟩
  have hR := sqrt_normSq_metricRm04_le_ricci_three (co.gInf t) q (by
    change Module.finrank ℝ E3 = 3
    simp)
  have hRRoot : Real.sqrt (normSq0S (co.gInf t) q 4 (metricRm04 (co.gInf t) q)) ≤ 567 * K := by
    nlinarith
  exact (Real.sqrt_le_iff.mp hRRoot).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.standard_closed_limit_curvature_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.standard_closed_limit_curvature_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.standard_closed_limit_curvature_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.standard_closed_limit_curvature_bound

end Maps
end DifferentialGeometry.PDE.RicciFlow
