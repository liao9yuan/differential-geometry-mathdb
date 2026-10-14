import Submission.DifferentialGeometry.Geometry.Operator.Family.Gram.Smoothness
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalJointSpatialJets

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]
  {D : RealTimeInterval}

theorem solution_chartGramOp_spatial_fderiv_continuousOn_closed
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : _root_.Set.Icc a b ⊆ D.carrier) (hreg : _root_.Set.Ioo a b ⊆ D.regular) (p : M) :
    ContinuousOn (fun z : ℝ × E => fderiv ℝ
      (fun y : E => chartGramOp S.family p (z.1, y)) z.2)
      (_root_.Set.Icc c b ×ˢ (extChartAt I p).target) := by
  exact chartGramOp_spatial_fderiv_continuousOn S.family p (fun _ hz => hz.2)
    (solution_chartGram_jets_continuousOn_closed S hS hac hcb hslab hreg p 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.solution_chartGramOp_spatial_fderiv_continuousOn_closed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.solution_chartGramOp_spatial_fderiv_continuousOn_closed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.solution_chartGramOp_spatial_fderiv_continuousOn_closed ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.solution_chartGramOp_spatial_fderiv_continuousOn_closed

end DifferentialGeometry.PDE.RicciFlow.Perelman

end

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}

theorem solution_chartGramOp_spatial_fderiv_continuousOn_carrier
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b : ℝ} (hcarrier : D.carrier = _root_.Set.Iic b) (hregular : D.regular = _root_.Set.Iio b) (p : M) :
    ContinuousOn (fun z : ℝ × E => fderiv ℝ
      (fun y : E => chartGramOp S.family p (z.1, y)) z.2)
      (_root_.Set.Iic b ×ˢ (extChartAt I p).target) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  rintro ⟨t, x⟩ ⟨ht, hx⟩
  have ht1 : t - 1 < b := (sub_lt_self t (by norm_num : (0 : ℝ) < 1)).trans_le ht
  have hslab : _root_.Set.Icc (t - 2) b ⊆ D.carrier := by
    rw [hcarrier]
    exact fun _ hz => hz.2
  have hreg : _root_.Set.Ioo (t - 2) b ⊆ D.regular := by
    rw [hregular]
    exact fun _ hz => hz.2
  have hc := solution_chartGramOp_spatial_fderiv_continuousOn_closed S hS
    (a := t - 2) (c := t - 1) (b := b) (by linarith) ht1 hslab hreg p
  have hmem : (t, x) ∈ _root_.Set.Icc (t - 1) b ×ˢ (extChartAt I p).target :=
    ⟨⟨by linarith, ht⟩, hx⟩
  refine (hc (t, x) hmem).mono_of_mem_nhdsWithin ?_
  have htend : _root_.Filter.Tendsto (fun z : ℝ × E => z.1)
      (𝓝[_root_.Set.Iic b ×ˢ (extChartAt I p).target] (t, x)) (𝓝 t) :=
    continuous_fst.continuousAt.continuousWithinAt
  have hlow : ∀ᶠ z : ℝ × E in 𝓝[_root_.Set.Iic b ×ˢ (extChartAt I p).target] (t, x),
      t - 1 < z.1 := htend.eventually (Ioi_mem_nhds (by linarith))
  filter_upwards [hlow, self_mem_nhdsWithin] with z hz hzmem
  exact ⟨⟨hz.le, hzmem.1⟩, hzmem.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.solution_chartGramOp_spatial_fderiv_continuousOn_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.solution_chartGramOp_spatial_fderiv_continuousOn_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.solution_chartGramOp_spatial_fderiv_continuousOn_carrier ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.solution_chartGramOp_spatial_fderiv_continuousOn_carrier

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
