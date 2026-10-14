import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BackwardScalarBound
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BackwardContinuation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AncientExtension.Gluing

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter
open scoped _root_.Topology _root_.Submission.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem ancient_extension {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hkappa : 0 < kappa) (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X)
        (delta : ℝ) (hd : 0 < delta)
        (B : BackwardExtension L (RealTimeInterval.closed (-delta) 0 (by linarith))),
          Nonempty (AncientExtension B) := by
  have hmod := KappaSolutions.ancientKappa_modelCurvatureBoundNearBase
    (I := I3) (by simp [ThreeSpace]) hkappa
  obtain ⟨epsC, hepsC, hchain⟩ := exists_cofinal_backwardExtensions_of_scalar_bounds hmod hsigma hPhi
  obtain ⟨epsS, hepsS, hscalar⟩ :=
    exists_uniform_backward_scalar_bound_on_finite_horizon hkappa hsigma hPhi
  refine ⟨min epsC epsS, lt_min hepsC hepsS, ?_⟩
  intro eps heps hle X L delta hd B₀
  have ha₀ : -delta < 0 := neg_neg_of_pos hd
  obtain ⟨a, ha, B, _ha0, _hanti, hcofinal, _hB0, hagree,
      rho, _hrho, _hstep, _hagrees, hcompatible, q, hq, hsubseq, hnest⟩ :=
    hchain eps heps (hle.trans (min_le_left _ _)) X L (-delta) ha₀ B₀ (by
      intro T
      obtain ⟨C, hC⟩ := hscalar eps heps (hle.trans (min_le_right _ _)) X L T
      exact ⟨C, fun a ha B hTa _ _ _ => hC a ha hTa B⟩)
  exact exists_ancientExtension_of_cofinal_backwardExtensions B₀ hkappa _root_.Set.Icc_subset_Iic_self
    a ha B hcofinal hcompatible (fun n t ht _ => hagree n t ht) q hq hsubseq hnest

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ancient_extension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ancient_extension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ancient_extension ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.ancient_extension

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
