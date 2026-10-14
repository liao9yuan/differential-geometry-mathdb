import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornStructure
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalParabolicBallNesting

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  RealizedFiniteHorn.metric_space RealizedFiniteHorn.charted RealizedFiniteHorn.smooth
  RealizedFiniteHorn.sigmaCompact

theorem finite_horn_construction_of_boundedAtDistance {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hkappa : 0 < kappa) (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi)
    (hbd : ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, BoundedAtDistance X) :
    ∃ alphaMax collarMin : ℝ, 0 < alphaMax ∧ alphaMax < 1 / 11 ∧ 0 < collarMin ∧
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaMax → ∀ collar : ℝ, collarMin ≤ collar →
        ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            FiniteControlledRadius X → ∃ H : RealizedFiniteHorn X.toFlowSequence,
              H.horn.neck_precision = alpha ∧ collar ≤ H.horn.collar_depth := by
  let _ := hkappa
  let _ := hsigma
  let _ := hPhi
  obtain ⟨epsStar, hepsStar, hb⟩ := hbd
  refine ⟨1 / 20, 1, by norm_num, by norm_num, one_pos, ?_⟩
  intro alpha halpha halphaMax collar hcollar
  exact ⟨epsStar, hepsStar, fun eps heps hle X hradius =>
    (finiteControlledRadius_false_of_boundedAtDistance X (hb eps heps hle X) hradius).elim⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_construction_of_boundedAtDistance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_construction_of_boundedAtDistance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_construction_of_boundedAtDistance ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_construction_of_boundedAtDistance

theorem finite_horn_construction_of_rmBallBound_and_ricciTensorBound
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} {K : ℝ} (hkappa : 0 < kappa) (hsigma : 0 < sigma)
    (hPhi : AdmissiblePinchingFunction Phi) (hK : 0 ≤ K)
    (hrm : ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ ρ : ℝ, 0 < ρ →
        TerminalParabolicRmBallBound X (-(modelDepth eps)) ρ)
    (hric : ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ i : ℕ,
        ∀ s ∈ Set.Icc (-(modelDepth eps)) 0, ∀ x : (X.term i).M, ∀ v : TangentSpace I3 x,
          0 ≤ (X.term i).S.ricciAt s x (vec2 v v) ∧
            (X.term i).S.ricciAt s x (vec2 v v) ≤
              ((Module.finrank ℝ ThreeSpace : ℝ) - 1) * K *
                ((X.term i).S.base.metric s).inner x v v) :
    ∃ alphaMax collarMin : ℝ, 0 < alphaMax ∧ alphaMax < 1 / 11 ∧ 0 < collarMin ∧
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaMax → ∀ collar : ℝ, collarMin ≤ collar →
        ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            FiniteControlledRadius X → ∃ H : RealizedFiniteHorn X.toFlowSequence,
              H.horn.neck_precision = alpha ∧ collar ≤ H.horn.collar_depth :=
  finite_horn_construction_of_boundedAtDistance hkappa hsigma hPhi (by
    obtain ⟨epsStar, hepsStar, h⟩ :=
      bounded_curvature_at_distance_of_rmBallBound_and_ricciTensorBound hK hrm hric
    exact ⟨epsStar, hepsStar, fun eps heps hle X => (h eps heps hle X).1⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_construction_of_rmBallBound_and_ricciTensorBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_construction_of_rmBallBound_and_ricciTensorBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_construction_of_rmBallBound_and_ricciTensorBound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_construction_of_rmBallBound_and_ricciTensorBound

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
