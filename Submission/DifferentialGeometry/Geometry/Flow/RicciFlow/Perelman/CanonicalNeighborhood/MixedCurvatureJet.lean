import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Norm
import Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree.Reconstruction.RiemannFromRicci
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetric

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}

structure MixedCurvatureJet (S : SolutionOn (I := I3) (M := M) D) where
  value : ∀ a : ℕ, ℕ → ℝ → Tensor0SField (I := I3) (M := M) (n := ∞) (a + 4)
  spatial : ∀ a t, value a 0 t = curvCovDeriv (I := I3) (S.base.metric t) a
  time : ∀ a b t, t ∈ D.carrier → ∀ x (v : Fin (a + 4) → TangentSpace I3 x),
    value a (b + 1) t x v = derivWithin (fun s => value a b s x v) (D.carrier ∩ Set.Iic t) t +
      ∑ j : Fin (a + 4), value a b t x (Function.update v j
        (ricciEndAt (S.base.metric t) (metricRicciAt (S.base.metric t) x) (v j)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MixedCurvatureJet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MixedCurvatureJet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MixedCurvatureJet ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MixedCurvatureJet

def MixedCurvatureJet.norm {S : SolutionOn (I := I3) (M := M) D}
    (J : MixedCurvatureJet S) (a b : ℕ) (t : ℝ) (x : M) : ℝ :=
  Real.sqrt (normSq0S (I := I3) (S.base.metric t) x (a + 4) (J.value a b t x))

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MixedCurvatureJet
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MixedCurvatureJet.norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MixedCurvatureJet.norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MixedCurvatureJet.norm ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MixedCurvatureJet.norm

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
