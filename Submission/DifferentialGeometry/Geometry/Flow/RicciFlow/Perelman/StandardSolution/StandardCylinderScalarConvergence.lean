import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCylinderIdentification
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCylinderClosedLimit

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E3 target :: scope.openDecls } }
private abbrev Q := cylinderReferenceCopy.Q

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Q
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Q target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instTopologicalSpaceMEuclideanSpaceRealFinOfNatNatCylinderPointedReference : TopologicalSpace cylinderPointedReference.M := cylinderPointedReference.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instTopologicalSpaceMEuclideanSpaceRealFinOfNatNatCylinderPointedReference
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instTopologicalSpaceMEuclideanSpaceRealFinOfNatNatCylinderPointedReference target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instChartedSpaceE3MEuclideanSpaceRealFinOfNatNatCylinderPointedReference : ChartedSpace E3 cylinderPointedReference.M := cylinderPointedReference.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instChartedSpaceE3MEuclideanSpaceRealFinOfNatNatCylinderPointedReference
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instChartedSpaceE3MEuclideanSpaceRealFinOfNatNatCylinderPointedReference target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instT2SpaceMEuclideanSpaceRealFinOfNatNatCylinderPointedReference : T2Space cylinderPointedReference.M := cylinderPointedReference.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instT2SpaceMEuclideanSpaceRealFinOfNatNatCylinderPointedReference
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instT2SpaceMEuclideanSpaceRealFinOfNatNatCylinderPointedReference target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopMCylinderPointedReference : IsManifold (𝓡 3) ∞ cylinderPointedReference.M := cylinderPointedReference.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopMCylinderPointedReference
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopMCylinderPointedReference target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instSigmaCompactSpaceMEuclideanSpaceRealFinOfNatNatCylinderPointedReference : SigmaCompactSpace cylinderPointedReference.M := cylinderPointedReference.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instSigmaCompactSpaceMEuclideanSpaceRealFinOfNatNatCylinderPointedReference
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instSigmaCompactSpaceMEuclideanSpaceRealFinOfNatNatCylinderPointedReference target :: scope.openDecls } }

theorem exists_standard_scalar_cylinder_subsequence
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1)
    (hlt : ENNReal.ofReal τ < uniformStandardLifetime)
    (S : ℕ → StandardSolution) (x : ℕ → E3)
    (hescape : _root_.Filter.Tendsto (fun n => (riemannianEDistOf ((S n).val.metric 0) 0 (x n)).toReal)
      _root_.Filter.atTop _root_.Filter.atTop) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      _root_.Filter.Tendsto (fun n => metricScalarAt ((S (ψ n)).val.metric τ) (x (ψ n)))
        atTop (𝓝 ((1 - τ)⁻¹)) := by
  obtain ⟨φ, hφ, Φ, hcharts, bf, co, hinit, hmono, hcharts', hzero, hpull, hcomplete,
    hjets, hgram, hpde, hsolutions, hconverge, htime⟩ :=
      exists_standard_cylinder_closed_limit τ hτ hlt S x hescape
  let hsrc := standardClosedPointedMaps_sourceSigma Φ
  let htgt := standardClosedPointedMaps_targetSigma Φ
  let q : Q := cylinderPointedReference.basepoint
  have hid := standard_cylinder_closed_limit_eq_shrinking Φ hsrc htgt hinit bf co hzero hgram hpde
    τ ⟨hτ.le, le_rfl⟩ hτ1
  obtain ⟨Λ, hΛ, _C, _L, _hC, _hL, hb⟩ := standard_closed_reference_bounds τ hτ hlt
  have hbounds := hb S x cylinderPointedReference φ Φ hsrc htgt hinit
  have hcLow : 0 < Λ⁻¹ := inv_pos.mpr (zero_lt_one.trans_le hΛ)
  have hcovTail := covTail_of_bounds Φ cylinderReferenceMetric bf hsrc htgt 0 τ (by
    intro a
    obtain ⟨Ca, hCa, hcov⟩ := hbounds.2.cov a
    exact ⟨Ca, hCa, fun j t ht y _ => hcov j t ht y⟩)
  have hconv := FlowMetricConvergenceData.scalar_convergence_at Φ cylinderReferenceMetric bf hsrc htgt
    0 τ Λ⁻¹ hcLow (fun j t ht y v => (((hbounds.1 j).1 t ht).2 y (_root_.Set.mem_univ y) v).1)
    hcovTail co ⟨hτ.le, le_rfl⟩ q
  have hscalar : metricScalarAt (co.gInf τ) q = (1 - τ)⁻¹ := by
    have hh := congrArg (fun g => metricScalarAt g (cylinderReferenceCopy.equiv.symm q)) hid
    have hcross := metricScalar_cross (co.gInf τ) cylinderReferenceCopy.equiv (cylinderReferenceCopy.equiv.symm q)
    rw [hcross] at hh
    have he := cylinderReferenceCopy.equiv.apply_symm_apply q
    exact (congrArg (fun y : Q => metricScalarAt (co.gInf τ) y) he).symm.trans
      (hh.trans (shrinkingCylinderMetric_scalar hτ1 _))
  refine ⟨φ ∘ co.φ, hmono, ?_⟩
  rw [hscalar] at hconv
  apply hconv.congr'
  filter_upwards with n
  change metricScalarAt ((S ((φ ∘ co.φ) n)).val.metric τ) (Φ.map (co.φ n) q) = _
  have hpoint := Φ.basepoint_map (co.φ n)
  change Φ.map (co.φ n) q = x (φ (co.φ n)) at hpoint
  rw [hpoint]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.exists_standard_scalar_cylinder_subsequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.exists_standard_scalar_cylinder_subsequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.exists_standard_scalar_cylinder_subsequence ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_standard_scalar_cylinder_subsequence

end DifferentialGeometry.PDE.RicciFlow
