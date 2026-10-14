import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ClosedWindowMetricFields
import Submission.DifferentialGeometry.Analysis.Calculus.IteratedDerivative.WithinTower
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]
  {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance comparisonTimeComplete : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.comparisonTimeComplete
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.comparisonTimeComplete target :: scope.openDecls } }

theorem MetricComparisonOn.jet_contDiffOn_of_solutions
    {D₁ D₂ : RealTimeInterval}
    (S : SolutionOn (I := I) (M := N) D₁) (hS : IsSolutionOn S)
    (T : SolutionOn (I := I3) (M := M) D₂) (hT : IsSolutionOn T)
    {a₁ a₂ c b : ℝ} (ha₁ : a₁ < c) (ha₂ : a₂ < c) (hcb : c < b)
    (hSdomain : _root_.Set.Icc a₁ b ⊆ D₁.carrier) (hSregular : _root_.Set.Ioo a₁ b ⊆ D₁.regular)
    (hTdomain : _root_.Set.Icc a₂ b ⊆ D₂.carrier) (hTregular : _root_.Set.Ioo a₂ b ⊆ D₂.regular)
    {F : N → M} {U : Set N} {order : ℕ} {eps : ℝ}
    (C : MetricComparisonOn S.base.metric T.base.metric F U (_root_.Set.Icc c b) order eps)
    (q : ℕ) (y : N) (hy : y ∈ U) (v : Fin 2 → TangentSpace I y) :
    ContDiffOn ℝ ∞ (fun s => C.jet q s y v) (_root_.Set.Icc c b) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · let : Subsingleton E := hE
    let : Subsingleton (TangentSpace I y) := inferInstanceAs (Subsingleton E)
    have hz : (fun s => C.jet q s y v) = fun _ => 0 := by
      funext s
      exact (C.jet q s y).map_coord_zero 0 (Subsingleton.elim (v 0) 0)
    rw [hz]
    exact contDiffOn_const
  · let : Nontrivial E := hE
    let : NeZero (Module.finrank ℝ E) := ⟨ne_of_gt (Module.finrank_pos (R := ℝ) (M := E))⟩
    let w : Fin 2 → TangentSpace I3 (F y) := fun j => mfderiv I I3 F y (v j)
    have htarget := (tensor0SEvalCLM (I := I3) (x := F y) w).contDiff.comp_contDiffOn
      (metricTensor_contDiffOn_time T hT ha₂ hcb hTdomain hTregular (F y))
    have hsource := (tensor0SEvalCLM (I := I) (x := y) v).contDiff.comp_contDiffOn
      (metricTensor_contDiffOn_time S hS ha₁ hcb hSdomain hSregular y)
    have hzero : ContDiffOn ℝ ∞ (fun s => C.jet 0 s y v) (_root_.Set.Icc c b) := by
      apply (htarget.sub hsource).congr
      intro s _hs
      rw [C.jet_zero s y v, C.pullback_eq s y hy v]
      rfl
    intro s hs
    exact DifferentialGeometry.Analysis.contDiffWithinAt_derivWithin_tower
      (f := fun b r => C.jet b r y v) (uniqueDiffOn_Icc hcb) hs
      (hzero s hs) (fun b r hr => C.jet_succ b r hr y hy v) q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MetricComparisonOn.jet_contDiffOn_of_solutions then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MetricComparisonOn.jet_contDiffOn_of_solutions"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MetricComparisonOn.jet_contDiffOn_of_solutions ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MetricComparisonOn.jet_contDiffOn_of_solutions

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
