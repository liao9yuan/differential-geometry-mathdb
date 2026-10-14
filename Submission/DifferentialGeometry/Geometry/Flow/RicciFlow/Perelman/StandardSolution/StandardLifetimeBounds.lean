import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCylinderIdentification
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardUniformExistence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ShrinkingCylinder
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CylinderReferenceCopy
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCylinderClosedLimit
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ClosedMetricLipschitz

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.Submission.DifferentialGeometry.Geometry.Topology _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E3 target :: scope.openDecls } }
private abbrev Cylinder := Metric.sphere (0 : E3) 1 × ℝ

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Cylinder
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Cylinder target :: scope.openDecls } }
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IC target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }

theorem not_exists_continuous_metric_extension_shrinkingCylinder :
    ¬ ∃ g : ℝ → SmoothRiemannianMetric IC Cylinder,
      (∀ (x : Cylinder) (v w : TangentSpace IC x),
        ContinuousOn (fun t => (g t).inner x v w) (_root_.Set.Icc 0 1)) ∧
      ∀ t ∈ _root_.Set.Ico (0 : ℝ) 1, g t = shrinkingCylinderMetric (E := E3) t := by
  rintro ⟨g, hcont, heq⟩
  let x : Cylinder := (DifferentialGeometry.Geometry.Neck.spherePoint, 0)
  let v : TangentSpace IC x := (EuclideanSpace.single 0 1, 0)
  have hv : v ≠ 0 := by
    intro h
    have h' := congrArg (fun w : TangentSpace IC x => w.1 0) h
    change (1 : ℝ) = 0 at h'
    exact one_ne_zero h'
  let A := (roundMetric (E := E3) (n := 2)).inner x.1 v.1 v.1
  have he : _root_.Set.EqOn (fun t => (g t).inner x v v) (fun t => 2 * (1 - t) * A) (_root_.Set.Ico 0 1) := by
    intro t ht
    change (g t).inner x v v = 2 * (1 - t) * A
    rw [heq t ht, shrinkingCylinderMetric_inner ht.2]
    simp only [v, _root_.MulZeroClass.mul_zero, add_zero, A]
  have hg : ContinuousOn (fun t => (g t).inner x v v) (closure (_root_.Set.Ico (0 : ℝ) 1)) := by
    rw [closure_Ico (by norm_num : (0 : ℝ) ≠ 1)]
    exact hcont x v v
  have ha : ContinuousOn (fun t => 2 * (1 - t) * A) (closure (_root_.Set.Ico (0 : ℝ) 1)) := by
    fun_prop
  have hzero := he.of_subset_closure hg ha subset_closure Subset.rfl
  have hm : (1 : ℝ) ∈ closure (_root_.Set.Ico (0 : ℝ) 1) := by
    rw [closure_Ico (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨zero_le_one, le_rfl⟩
  have hz : (g 1).inner x v v = 0 := by simpa using hzero hm
  exact (ne_of_gt ((g 1).pos x v hv)) hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.not_exists_continuous_metric_extension_shrinkingCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.not_exists_continuous_metric_extension_shrinkingCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.not_exists_continuous_metric_extension_shrinkingCylinder ``Submission.DifferentialGeometry.PDE.RicciFlow.not_exists_continuous_metric_extension_shrinkingCylinder


private theorem metric_inner_continuousOn_of_gram
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (g : ℝ → SmoothRiemannianMetric I M) (A : Set ℝ)
    (hgram : ∀ (q : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) q p.2 i j)
        (A ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) q).baseSet))
    (x : M) (v w : TangentSpace I x) :
    ContinuousOn (fun t => (g t).inner x v w) A := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  exact (tensor0SEvalCLM (I := I) (vec2 v w)).continuous.comp_continuousOn
    (metricCovDeriv_contDiffOn_time g A hgram (g 0) 0 x).continuousOn

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.metric_inner_continuousOn_of_gram
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.metric_inner_continuousOn_of_gram target :: scope.openDecls } }

private theorem cylinderCopy_extension_impossible
    (g : ℝ → SmoothRiemannianMetric (𝓡 3) cylinderReferenceCopy.Q)
    (hcont : ∀ (x : cylinderReferenceCopy.Q) (v w : TangentSpace (𝓡 3) x),
      ContinuousOn (fun t => (g t).inner x v w) (_root_.Set.Icc 0 1))
    (heq : ∀ t ∈ _root_.Set.Ico (0 : ℝ) 1,
      Diffeomorph.pullbackMetricCross (g t) cylinderReferenceCopy.equiv =
        shrinkingCylinderMetric (E := E3) t) : False := by
  apply not_exists_continuous_metric_extension_shrinkingCylinder
  refine ⟨fun t => Diffeomorph.pullbackMetricCross (g t) cylinderReferenceCopy.equiv, ?_, heq⟩
  intro x v w
  simpa only [Diffeomorph.pullbackMetricCross_inner] using hcont (cylinderReferenceCopy.equiv x)
    (mfderiv IC (𝓡 3) cylinderReferenceCopy.equiv x v)
    (mfderiv IC (𝓡 3) cylinderReferenceCopy.equiv x w)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.cylinderCopy_extension_impossible
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.cylinderCopy_extension_impossible target :: scope.openDecls } }


theorem uniformStandardLifetime_le_one : uniformStandardLifetime ≤ 1 := by
  by_contra hnot
  obtain ⟨τ, hτ0, hτ1, hτLife⟩ :=
    ENNReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hnot)
  have honeτ : (1 : ℝ) < τ := ENNReal.one_lt_ofReal.mp hτ1
  have hτ : 0 < τ := zero_lt_one.trans honeτ
  obtain ⟨S₀⟩ := standard_solution_nonempty
  let S : ℕ → StandardSolution := fun _ => S₀
  let x : ℕ → E3 := fun n => EuclideanSpace.single 0 (n : ℝ)
  have hescape : _root_.Filter.Tendsto
      (fun n => (riemannianEDistOf ((S n).val.metric 0) 0 (x n)).toReal) _root_.Filter.atTop atTop := by
    have heq : (fun n => (riemannianEDistOf ((S n).val.metric 0) 0 (x n)).toReal) =
        fun n : ℕ => (n : ℝ) := by
      funext n
      rw [(S n).val.initial, StandardCap.distance_zero]
      simp only [x, EuclideanSpace.single, PiLp.norm_single, Real.norm_eq_abs]
      exact abs_of_nonneg (Nat.cast_nonneg n)
    rw [heq]
    exact tendsto_natCast_atTop_atTop
  obtain ⟨φ, hφ, Φ, hcharts, bf, co, hinit, hmono, hcharts', hzero, hpull, hcomplete,
    hjets, hgram, hpde, hsolutions, hconverge, htime⟩ :=
      exists_standard_cylinder_closed_limit τ hτ hτLife S x hescape
  have hid := standard_cylinder_closed_limit_eq_shrinking Φ
    (standardClosedPointedMaps_sourceSigma Φ) (standardClosedPointedMaps_targetSigma Φ)
    hinit bf co hzero hgram hpde
  let : TopologicalSpace cylinderPointedReference.M := cylinderPointedReference.topology
  let : ChartedSpace E3 cylinderPointedReference.M := cylinderPointedReference.charted
  let : T2Space cylinderPointedReference.M := cylinderPointedReference.t2
  let : IsManifold (𝓡 3) ∞ cylinderPointedReference.M := cylinderPointedReference.smooth
  let : SigmaCompactSpace cylinderPointedReference.M := cylinderPointedReference.sigmaCompact
  apply cylinderCopy_extension_impossible co.gInf
  · intro p v w
    exact (metric_inner_continuousOn_of_gram co.gInf (_root_.Set.Icc 0 τ) hgram p v w).mono
      (_root_.Set.Icc_subset_Icc_right honeτ.le)
  · intro t ht
    exact hid t ⟨ht.1, ht.2.le.trans honeτ.le⟩ ht.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.uniformStandardLifetime_le_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.uniformStandardLifetime_le_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.uniformStandardLifetime_le_one ``Submission.DifferentialGeometry.PDE.RicciFlow.uniformStandardLifetime_le_one

end DifferentialGeometry.PDE.RicciFlow
