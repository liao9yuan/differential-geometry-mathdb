import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

section normedSpaceCompatibility

attribute [-instance] InnerProductSpace.toNormedSpace

open _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

open _root_.Submission.DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

def lCost
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (x y : M) (tau : Real) : Real :=
  _root_.InfSet.sInf {r : Real | ∃ alpha : Real → M,
    ContMDiff (modelWithCornersSelf Real Real) I 1 alpha ∧
      alpha 0 = x ∧ alpha (Real.sqrt tau) = y ∧
      lLength S T (squareRootReparametrization alpha) 0 tau = r}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lCost then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lCost"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lCost ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lCost

end normedSpaceCompatibility

section

open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]
  {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}

def lRegularizedCostC1
    (S : SolutionOn (I := I) (M := M) D) (T a b : ℝ) (x y : M) : ℝ :=
  _root_.InfSet.sInf {r : ℝ | ∃ alpha : ℝ → M,
    ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 alpha ∧
      alpha a = x ∧ alpha b = y ∧ lRegularizedAction S T alpha a b = r}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedCostC1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedCostC1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedCostC1 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedCostC1

theorem lRegularizedCostC1_le_bdd
    (S : SolutionOn (I := I) (M := M) D) (T a b : ℝ) (x y : M)
    (hbdd : BddBelow {r : ℝ | ∃ alpha : ℝ → M,
      ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 alpha ∧
        alpha a = x ∧ alpha b = y ∧ lRegularizedAction S T alpha a b = r})
    (alpha : ℝ → M)
    (halpha : ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 alpha)
    (hxa : alpha a = x) (hyb : alpha b = y) :
    lRegularizedCostC1 S T a b x y ≤ lRegularizedAction S T alpha a b := by
  unfold lRegularizedCostC1
  exact csInf_le hbdd ⟨alpha, halpha, hxa, hyb, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedCostC1_le_bdd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedCostC1_le_bdd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedCostC1_le_bdd ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedCostC1_le_bdd

end

end DifferentialGeometry.PDE.RicciFlow.Perelman
