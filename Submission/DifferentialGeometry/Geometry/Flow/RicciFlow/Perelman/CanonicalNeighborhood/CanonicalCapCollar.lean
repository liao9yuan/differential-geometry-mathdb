import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalToleranceMonotone

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open scoped _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] {D : RealTimeInterval}
  {S : SolutionOn (I := I3) (M := M) D}
  {eps C1 C2 alpha : ℝ} {x : M} {t : ℝ}

def CanonicalWitness.capTubeHasNeckChart
    (K : CanonicalWitness S eps C1 C2 x t) (alpha : ℝ) : Prop :=
  ∀ (cap : LocalCap S eps x t K.domain.carrier)
    (depth : ∀ y ∈ cap.tube,
      10000 / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x y),
    K.alternative = CanonicalAlternative.cap cap depth →
      ∃ (v : M) (nk : StrongNeck S alpha v t), ∀ z, cap.tube_map z = nk.map z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.capTubeHasNeckChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.capTubeHasNeckChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.capTubeHasNeckChart ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.capTubeHasNeckChart

theorem CanonicalWitness.capTubeHasNeckChart.enlarge_constants
    {K : CanonicalWitness S eps C1 C2 x t}
    (h : K.capTubeHasNeckChart alpha) {C1' C2' : ℝ}
    (hC1 : C1 ≤ C1') (hC2 : C2 ≤ C2') :
    (K.enlarge_constants hC1 hC2).capTubeHasNeckChart alpha := by
  intro cap depth heq
  change K.alternative.mono_constant
    (zero_lt_one.trans_le K.one_le_comparison_constant) hC2 K.Q_pos.le =
      CanonicalAlternative.cap cap depth at heq
  cases halt : K.alternative with
  | neck data =>
    rw [halt] at heq
    cases heq
  | cap data deep =>
    rw [halt] at heq
    change CanonicalAlternative.cap data deep = CanonicalAlternative.cap cap depth at heq
    cases heq
    exact h _ _ halt
  | positive whole data sec =>
    rw [halt] at heq
    cases heq
  | round whole data =>
    rw [halt] at heq
    cases heq

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.capTubeHasNeckChart
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.capTubeHasNeckChart.enlarge_constants then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.capTubeHasNeckChart.enlarge_constants"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.capTubeHasNeckChart.enlarge_constants ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.capTubeHasNeckChart.enlarge_constants

theorem CanonicalWitness.capTubeHasNeckChart.mono_eps
    {K : CanonicalWitness S eps C1 C2 x t}
    (h : K.capTubeHasNeckChart alpha) {eps' : ℝ}
    (heps : eps ≤ eps') (hsmall : eps' < 1 / 11) :
    (K.mono_eps heps hsmall).capTubeHasNeckChart alpha := by
  intro cap depth heq
  change K.alternative.mono_eps K.eps_pos heps hsmall =
    CanonicalAlternative.cap cap depth at heq
  cases halt : K.alternative with
  | neck data =>
    rw [halt] at heq
    cases heq
  | cap data deep =>
    rw [halt] at heq
    change CanonicalAlternative.cap (data.mono_eps heps hsmall) deep =
      CanonicalAlternative.cap cap depth at heq
    cases heq
    exact h _ _ halt
  | positive whole data sec =>
    rw [halt] at heq
    cases heq
  | round whole data =>
    rw [halt] at heq
    cases heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.capTubeHasNeckChart.mono_eps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.capTubeHasNeckChart.mono_eps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.capTubeHasNeckChart.mono_eps ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.capTubeHasNeckChart.mono_eps

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
