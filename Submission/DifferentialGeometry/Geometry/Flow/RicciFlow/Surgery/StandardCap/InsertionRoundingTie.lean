import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InsertionMetric
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.RoundingJets
import Submission.DifferentialGeometry.Geometry.Metric.OpenEmbeddingPullback
import Submission.DifferentialGeometry.Geometry.Metric.Conformal.OfContDiff

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.TopologicalSpace _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Metric _root_.Submission.DifferentialGeometry.Topology.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.E3 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.S2 target :: scope.openDecls } }
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.IC target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }

private theorem collar_subset {A B : ℝ} (hAB : 2 * A < B) :
    insertionCylinder A B ≤ DifferentialGeometry.Geometry.Neck.openCylinder B := by
  intro q hq
  change -2 * A < q.2 ∧ q.2 < B at hq
  change -B < q.2 ∧ q.2 < B
  exact ⟨by linarith [hq.1], hq.2⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.collar_subset
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.collar_subset target :: scope.openDecls } }

theorem insertionMap_isLocalDiffeomorph {A B : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) :
    IsLocalDiffeomorph IC (𝓡 3) ∞ (insertionMap hA hAB) :=
  isLocalDiffeomorph_of_injective_mfderiv (insertionMap hA hAB)
    (contMDiff_insertionMap hA hAB) (insertionMap_mfderiv_injective hA hAB) (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionMap_isLocalDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionMap_isLocalDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionMap_isLocalDiffeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertionMap_isLocalDiffeomorph

def insertedPullbackMetric {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B)) :
    SmoothRiemannianMetric IC (insertionCylinder A B) :=
  pullbackMetricOfInjectiveLocalDiffeomorph (insertedMetric hA hAB hη h)
    (insertionMap hA hAB) (insertionMap_isLocalDiffeomorph hA hAB)
    (injective_insertionMap hA hAB)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedPullbackMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedPullbackMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedPullbackMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedPullbackMetric

theorem insertedPullbackMetric_inner {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B))
    (q : insertionCylinder A B) (v w : TangentSpace IC q) :
    (insertedPullbackMetric hA hAB hη h).inner q v w =
      (insertedMetric hA hAB hη h).inner (insertionMap hA hAB q)
        (mfderiv IC (𝓡 3) (insertionMap hA hAB) q v)
        (mfderiv IC (𝓡 3) (insertionMap hA hAB) q w) :=
  pullbackMetricOfInjectiveLocalDiffeomorph_inner _ _ _ _ _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedPullbackMetric_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedPullbackMetric_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedPullbackMetric_inner ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedPullbackMetric_inner

theorem insertedPullbackMetric_rounded_inner {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B))
    (q : insertionCylinder A B) (hq : -5 * A / 4 ≤ q.val.2)
    (v w : TangentSpace IC q) :
    (insertedPullbackMetric hA hAB hη h).inner q v w =
      Real.exp (2 * conformalFactor q.val.2) *
        (h.restrictOpenOfSubset (collar_subset hAB)).inner q v w := by
  have hc : insertionCutoff A q.val.2 = 1 := by
    apply Real.smoothTransition.one_of_one_le
    apply (le_div_iff₀ hA).mpr
    linarith
  rw [insertedPullbackMetric_inner, insertedMetric_interpolation, hc]
  simp only [one_mul, sub_self, _root_.MulZeroClass.zero_mul, add_zero]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedPullbackMetric_rounded_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedPullbackMetric_rounded_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedPullbackMetric_rounded_inner ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedPullbackMetric_rounded_inner

theorem insertedPullbackMetric_metricCovDeriv_at_height_zero {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B))
    (gRef : SmoothRiemannianMetric IC (insertionCylinder A B))
    (q : insertionCylinder A B) (hq : q.val.2 = 0) (m : ℕ) :
    metricCovDeriv (insertedPullbackMetric hA hAB hη h) gRef m q =
      metricCovDeriv (h.restrictOpenOfSubset (collar_subset hAB)) gRef m q := by
  let : SigmaCompactSpace (insertionCylinder A B) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen IC (insertionCylinder A B).isOpen)
  let W : _root_.TopologicalSpace.Opens (insertionCylinder A B) :=
    ⟨{y | -5 * A / 4 < y.val.2},
      isOpen_lt continuous_const (continuous_snd.comp continuous_subtype_val)⟩
  let : SigmaCompactSpace W := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen IC W.isOpen)
  let h₀ := h.restrictOpenOfSubset (collar_subset hAB)
  let r := conformalMetricOfContDiff h₀
    (fun y : insertionCylinder A B => conformalFactor y.val.2)
    (contDiff_conformalFactor.contMDiff.comp
      (contMDiff_snd.comp (contMDiff_subtype_val (I := IC) (U := insertionCylinder A B))))
  have hW : q ∈ W := by change -5 * A / 4 < q.val.2; rw [hq]; linarith
  have heq : ∀ y : insertionCylinder A B, y ∈ W →
      ∀ v w : TangentSpace IC y,
        (insertedPullbackMetric hA hAB hη h).inner y v w = r.inner y v w := by
    intro y hy v w
    rw [conformalMetricOfContDiff_inner]
    exact insertedPullbackMetric_rounded_inner hA hAB hη h y (show -5 * A / 4 ≤ y.val.2 from (show -5 * A / 4 < y.val.2 from hy).le) v w
  have hjet : metricCovDeriv (insertedPullbackMetric hA hAB hη h) gRef m q =
      metricCovDeriv r gRef m q := by
    ext slots
    exact metricCovDeriv_eq_of_eqOn _ _ gRef W heq m ⟨q, hW⟩ slots
  exact hjet.trans (metricCovDeriv_conformalFactor_eq_at_height_zero
    (insertionCylinder A B) h₀ gRef q hq m)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedPullbackMetric_metricCovDeriv_at_height_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedPullbackMetric_metricCovDeriv_at_height_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedPullbackMetric_metricCovDeriv_at_height_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.insertedPullbackMetric_metricCovDeriv_at_height_zero

end DifferentialGeometry.PDE.RicciFlow.StandardCap
