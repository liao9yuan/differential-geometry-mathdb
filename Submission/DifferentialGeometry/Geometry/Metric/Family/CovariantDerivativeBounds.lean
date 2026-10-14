import Submission.DifferentialGeometry.Geometry.Metric.Family.ConnectionRegularity
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.ParametricComponents
import Submission.DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Inverse
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetric
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.Evaluation
import Submission.DifferentialGeometry.Geometry.Metric.Family.JointSmoothness
import Submission.DifferentialGeometry.Geometry.Metric.Family.ChartCurvature.MetricFamilySmoothOn
import Submission.DifferentialGeometry.Tensor.RSTensor.Coordinates.Field

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Filter _root_.Bundle _root_.Submission.Bundle _root_.Manifold
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators _root_.Topology

namespace DifferentialGeometry.Geometry.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [I.Boundaryless]

private theorem tensor_iterCov_components_contMDiffOn
    (g : ℝ → SmoothRiemannianMetric I M) (J : Set ℝ) (hJ : UniqueDiffOn ℝ J)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (g p.1) x₀ p.2 i j)
        (J ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet))
    {r : ℕ} (A : Tensor0SField (I := I) (M := M) ∞ r)
    (x₀ : M) (k : ℕ) (n : Fin (r + k) → CoordinateIdx (𝕜 := ℝ) E) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => iterCov (g p.1) r A k p.2
        (frameTuple (coordinateFrameAt (I := I) x₀) p.2 n))
      (J ×ˢ chartLeviCivitaGoodSet (I := I) x₀) := by
  have hsub : chartLeviCivitaGoodSet (I := I) x₀ ⊆ coordinateFrameSet (I := I) x₀ :=
    fun _ hx => chartLeviCivitaGoodSet_mem_baseSet hx
  have hbase : ∀ n : Fin r → CoordinateIdx (𝕜 := ℝ) E,
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => frameComp0S A (coordinateFrameAt (I := I) x₀) p.2 n)
        (J ×ˢ chartLeviCivitaGoodSet (I := I) x₀) := by
    intro n p hp
    have hx : p.2 ∈ coordinateFrameSet (I := I) x₀ :=
      chartLeviCivitaGoodSet_mem_baseSet hp.2
    have he := DifferentialGeometry.TensorMultilinear.contMDiffAt_section_apply
      (T := fun y : M => A y) (A.contMDiff p.2)
      (fun a : Fin r => coordinateFrameAt (I := I) x₀ (n a))
      (fun a => (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
        (coordinateFrameSet_open (I := I) x₀) hx (n a))
    exact (he.comp p contMDiffAt_snd).contMDiffWithinAt
  have hc := iterCovComp_joint_contMDiffOn J (chartLeviCivitaGoodSet (I := I) x₀)
    (chartLeviCivitaGoodSet_isOpen (I := I) x₀) (coordinateFrameAt (I := I) x₀)
    (fun i => ((coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffOn i).mono hsub)
    (fun t x => christoffelSymbolInFrame (leviCivitaConnectionOfMetric (g t))
      (coordinateFrameAt (I := I) x₀) (coordinateFrameAt_isLocalFrame_one (I := I) x₀) x)
    (fun _ => frameComp0S A (coordinateFrameAt (I := I) x₀))
    (fun i j l => connectionComponents_contMDiffOn g J hgram hJ x₀ i j l)
    hbase k n
  apply hc.congr
  intro p hp
  exact (iterCovComp_eq_iterCov (g p.1) A (coordinateFrameAt (I := I) x₀)
    (coordinateFrameAt_isLocalFrame_one (I := I) x₀) (coordinateFrameSet_open (I := I) x₀)
    k (hsub hp.2) n).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Tensor.tensor_iterCov_components_contMDiffOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Tensor.tensor_iterCov_components_contMDiffOn target :: scope.openDecls } }

private theorem tensor_iterCov_normSq_contMDiffOn
    (g : ℝ → SmoothRiemannianMetric I M) (J : Set ℝ) (hJ : UniqueDiffOn ℝ J)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (g p.1) x₀ p.2 i j)
        (J ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet))
    {r : ℕ} (A : Tensor0SField (I := I) (M := M) ∞ r) (k : ℕ) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => normSq0S (g p.1) p.2 (r + k)
        (iterCov (g p.1) r A k p.2))
      (J ×ˢ (_root_.Set.univ : Set M)) := by
  classical
  intro p hp
  let u := chartLeviCivitaGoodSet (I := I) p.2
  let frame := coordinateFrameAt (I := I) p.2
  let inv := fun q : ℝ × M => fun i j : CoordinateIdx (𝕜 := ℝ) E =>
    inverseMetricFlatModelInChartComponent (g q.1) p.2 i j (extChartAt I p.2 q.2)
  let comp := fun q : ℝ × M => fun n : Fin (r + k) → CoordinateIdx (𝕜 := ℝ) E =>
    iterCov (g q.1) r A k q.2
      (frameTuple frame q.2 n)
  have hs : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => ∑ ns : Fin (r + k) → CoordinateIdx (𝕜 := ℝ) E,
        ∑ ms : Fin (r + k) → CoordinateIdx (𝕜 := ℝ) E,
          (∏ i : Fin (r + k), inv q (ns i) (ms i)) * comp q ns * comp q ms) (J ×ˢ u) := by
    intro q hq
    refine ContMDiffWithinAt.sum fun ns _ => ContMDiffWithinAt.sum fun ms _ => ?_
    exact ((ContMDiffWithinAt.prod fun i _ =>
      inverseComponents_contMDiffOn g J hgram p.2 (ns i) (ms i) q hq).mul
        (tensor_iterCov_components_contMDiffOn g J hJ hgram A p.2 k ns q hq)).mul
        (tensor_iterCov_components_contMDiffOn g J hJ hgram A p.2 k ms q hq)
  have hn : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => normSq0S (g q.1) q.2 (r + k)
        (iterCov (g q.1) r A k q.2)) (J ×ˢ u) := by
    apply hs.congr
    intro q hq
    have hx := chartLeviCivitaGoodSet_mem_baseSet hq.2
    rw [normSq0S_eq_coord (g q.1) q.2 (r + k) (coordinateFrameAtBasis (I := I) p.2 hx)
      (inv q) (gInvBasisAt (g q.1) p.2 hx)]
    have hb (slots : Fin (r + k) → CoordinateIdx (𝕜 := ℝ) E) :
        (fun j => coordinateFrameAtBasis (I := I) p.2 hx (slots j)) = frameTuple frame q.2 slots := by
      funext j
      exact coordinateFrameAt_basis_apply (I := I) p.2 hx (slots j)
    simp only [coordInner0S, tensor0SComponent_apply, hb]
    rfl
  have hx : p.2 ∈ u := self_mem_chartLeviCivitaGoodSet (I := I) p.2
  apply (hn p ⟨hp.1, hx⟩).mono_of_mem_nhdsWithin
  have hu : {q : ℝ × M | q.2 ∈ u} ∈ 𝓝 p :=
    ((chartLeviCivitaGoodSet_isOpen (I := I) p.2).preimage continuous_snd).mem_nhds hx
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hu] with q hq hqu
  exact ⟨hq.1, hqu⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Tensor.tensor_iterCov_normSq_contMDiffOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Tensor.tensor_iterCov_normSq_contMDiffOn target :: scope.openDecls } }

theorem exists_pos_bound_iterCov_on_compact_time
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn (I := I) (M := M) D g)
    {r : ℕ} (A : Tensor0SField (I := I) (M := M) ∞ r) (k : ℕ)
    {K : Set ℝ} {L : Set M} (hK : IsCompact K) (hL : IsCompact L)
    (hKreg : K ⊆ D.regular) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ K, ∀ x ∈ L,
      Real.sqrt (normSq0S (g t) x (r + k)
        (iterCov (g t) r A k x)) ≤ C := by
  have hmetric : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ :
        _root_.Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (D.regular ×ˢ (Set.univ : Set M)) := by
    intro p hp
    exact (hg.metricCLMSmoothAt (D.regular_isOpen.mem_nhds hp.1)).contMDiffWithinAt
  have hgram := chartGramMatrix_joint_contMDiffOn g D.regular hmetric
  have hn := tensor_iterCov_normSq_contMDiffOn g D.regular D.regular_isOpen.uniqueDiffOn hgram A k
  have hc := hn.continuousOn.sqrt.mono (_root_.Set.prod_mono hKreg (_root_.Set.subset_univ L))
  obtain ⟨C, hC⟩ := (hK.prod hL).exists_bound_of_continuousOn hc
  refine ⟨max 1 C, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro t ht x hx
  have hh := hC (t, x) ⟨ht, hx⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at hh
  exact hh.trans (le_max_right _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Tensor.exists_pos_bound_iterCov_on_compact_time then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Tensor.exists_pos_bound_iterCov_on_compact_time"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Tensor.exists_pos_bound_iterCov_on_compact_time ``Submission.DifferentialGeometry.Geometry.Tensor.exists_pos_bound_iterCov_on_compact_time

theorem exists_pos_bound_iterCov_scalar_on_compact
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn (I := I) (M := M) D g)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (k : ℕ)
    {K : Set ℝ} {L : Set M} (hK : IsCompact K) (hL : IsCompact L)
    (hKreg : K ⊆ D.regular) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ K, ∀ x ∈ L,
      Real.sqrt (normSq0S (g t) x (0 + k)
        (iterCov (g t) 0 (Tensor0SField.fromScalarField ∞ f hf) k x)) ≤ C :=
  exists_pos_bound_iterCov_on_compact_time hg (Tensor0SField.fromScalarField ∞ f hf) k hK hL hKreg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Tensor.exists_pos_bound_iterCov_scalar_on_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Tensor.exists_pos_bound_iterCov_scalar_on_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Tensor.exists_pos_bound_iterCov_scalar_on_compact ``Submission.DifferentialGeometry.Geometry.Tensor.exists_pos_bound_iterCov_scalar_on_compact

end DifferentialGeometry.Geometry.Tensor
