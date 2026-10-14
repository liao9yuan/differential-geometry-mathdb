import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem NormalizedSequence.regular_window_of_higher_good
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (i : ℕ)
    {s : ℝ} (hs : s ∈ _root_.Set.Icc (-X.depth i) 0) {y : (X.term i).M}
    (hq : 2 ≤ (X.term i).S.scalar s y)
    (W : WindowedModelWitness eps kappa (X.term i).S y s) :
    Ioo (s - (eps * (X.term i).S.scalar s y)⁻¹) s ⊆ (X.interval i).regular := by
  rw [X.regular_eq i]
  intro t ht
  have hinv : ((X.term i).S.scalar s y)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hdepth : (eps * (X.term i).S.scalar s y)⁻¹ ≤ X.depth i := by
    rw [mul_inv]
    calc
      eps⁻¹ * ((X.term i).S.scalar s y)⁻¹ ≤ eps⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hinv (inv_nonneg.mpr W.eps_pos.le)
      _ = modelDepth eps := by rw [mul_one]; rfl
      _ ≤ X.depth i := X.depth_buffer i
  exact ⟨by linarith [hs.1, ht.1], ht.2.trans_le hs.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NormalizedSequence.regular_window_of_higher_good then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NormalizedSequence.regular_window_of_higher_good"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NormalizedSequence.regular_window_of_higher_good ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.NormalizedSequence.regular_window_of_higher_good

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
