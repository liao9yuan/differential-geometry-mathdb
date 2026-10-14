import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.IntrinsicTimeJetConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction
import Submission.DifferentialGeometry.Geometry.Metric.Construction.TensorBumpTimeJets
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Naturality.OpenTensorJets
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.Locality
import Submission.DifferentialGeometry.Analysis.Calculus.Cutoff.Compact

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates _root_.Submission.DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

private local instance openMetricJetsC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.openMetricJetsC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.openMetricJetsC1 target :: scope.openDecls } }
private local instance openMetricJetsC2 : IsManifold I 2 M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.openMetricJetsC2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.openMetricJetsC2 target :: scope.openDecls } }

theorem exists_metric_time_jets_extension_on_compact
    (U : TopologicalSpace.Opens M) {D : RealTimeInterval}
    (S : ℕ → SolutionOn (I := I) (M := U) D) (hS : ∀ n, IsSolutionOn (S n))
    (G : SolutionOn (I := I) (M := M) D) (hG : IsSolutionOn G)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hcarrier : D.carrier = _root_.Set.Icc a b) (hregular : _root_.Set.Ioo a b ⊆ D.regular)
    (R : SmoothRiemannianMetric I U)
    (hconv : ∀ K : Set U, IsCompact K → ∀ r : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ _root_.Set.Icc c b,
        metricDerivNormSupOn K r ((S n).base.metric t)
          ((G.base.metric t).restrictOpen U) R < epsilon)
    {K : Set M} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ B : ℕ → ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2,
    ∃ C : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2,
      (∀ n t x, ∀ hx : x ∈ K, ∀ v : Fin 2 → TangentSpace I x,
        B n 0 t x v = ((S n).base.metric t).inner ⟨x, hKU hx⟩ (v 0) (v 1)) ∧
      (∀ t, C 0 t = metricTensorField (G.base.metric t)) ∧
      (∀ n q t, t ∈ _root_.Set.Icc c b → ∀ x : M,
        HasDerivWithinAt (fun s => B n q s x) (B n (q + 1) t x) (_root_.Set.Icc c b) t) ∧
      (∀ q t, t ∈ _root_.Set.Icc c b → ∀ x : M,
        HasDerivWithinAt (fun s => C q s x) (C (q + 1) t x) (_root_.Set.Icc c b) t) ∧
      ∀ r q : ℕ, ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ,
        ∀ n ≥ N, ∀ t ∈ _root_.Set.Icc c b, ∀ x ∈ K,
          tensor02CovDerivNormWith r (B n q t - C q t)
            (G.base.metric t) (G.base.metric t) x ≤ epsilon := by
  classical
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  obtain ⟨C, hCzero, hC⟩ := exists_ordinary_metric_time_jets_on_closed_interval G hG
    hac hcb hcarrier hregular
  choose A hAzero hA using fun n => exists_ordinary_metric_time_jets_on_closed_interval
    (S n) (hS n) hac hcb hcarrier hregular
  obtain ⟨chi, hchi, _hcompact, hone, hsupp, _hrange⟩ :=
    DifferentialGeometry.Analysis.exists_mfd_bump (I := I) hK U.isOpen hKU
  choose B hBvalue _hBout hBderiv using fun n => exists_tensor_bump_time_tower U 2 (A n)
    chi hchi hsupp (_root_.Set.Icc c b) (fun q t ht x => (hA n q t ht x).2)
  let L := solutionOnRestrictOpen G U
  have hL : IsSolutionOn L := isSolutionOn_restrictOpen G hG U
  let C' : ℕ → ℝ → Tensor0SField (I := I) (M := U) (n := ∞) 2 :=
    fun q t => restrictOpen0S (I := I) 2 (V := U) (C q t)
  have hC'zero (t : ℝ) : C' 0 t = metricTensorField (L.base.metric t) := by
    ext x v
    change C 0 t (x : M) v = _
    rw [hCzero]
    rfl
  have hC'deriv (q : ℕ) (t : ℝ) (ht : t ∈ _root_.Set.Icc c b) (x : U) :
      HasDerivWithinAt (fun s => C' q s x) (C' (q + 1) t x) (_root_.Set.Icc c b) t := by
    let basis := Module.finBasis ℝ (TangentSpace I x)
    apply tensor0S_hasDerivWithinAt_of_components basis
    intro slots
    exact (tensor0SEvalCLM (I := I) (x := (x : M))
      (fun j => basis (slots j))).hasFDerivAt.comp_hasDerivWithinAt t (hC q t ht (x : M)).2
  have hK' : IsCompact ((Subtype.val : U → M) ⁻¹' K) :=
    Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hK
      (fun x hx => ⟨⟨x, hKU hx⟩, rfl⟩)
  refine ⟨B, C, ?_, hCzero, hBderiv, fun q t ht x => (hC q t ht x).2, ?_⟩
  · intro n t x hx v
    have hchi1 : chi x = 1 := hone.self_of_nhdsSet hx
    rw [hBvalue n 0 t x (hKU hx) v, hchi1, one_mul, hAzero]
    rfl
  · intro r q epsilon hepsilon
    obtain ⟨N, hN⟩ := metric_time_jet_errors_uniform_on_compacts_of_closed_interval
      S hS L hL hac hcb hcarrier hregular R hconv A C' hAzero hC'zero
      (fun n q t ht x => (hA n q t ht x).2) hC'deriv hK' r q epsilon hepsilon
    refine ⟨N, fun n hn t ht x hx => ?_⟩
    let xU : U := ⟨x, hKU hx⟩
    have heq : ∀ᶠ y in 𝓝 xU,
        restrictOpen0S (I := I) 2 (V := U) (B n q t - C q t) y = (A n q t - C' q t) y := by
      have hcM : ∀ᶠ y in 𝓝 x, chi y = 1 := hone.filter_mono (nhds_le_nhdsSet hx)
      have hc : ∀ᶠ y : U in 𝓝 xU, chi (y : M) = 1 :=
        (continuous_subtype_val.tendsto xU).eventually hcM
      filter_upwards [hc] with y hy
      apply ContinuousMultilinearMap.ext
      intro v
      change B n q t (y : M) v - C q t (y : M) v = A n q t y v - C q t (y : M) v
      rw [hBvalue n q t (y : M) y.property v, hy, one_mul]
    have hnorm := tensor02CovDerivNormWith_eq_of_eventuallyEq
      ((G.base.metric t).restrictOpen U) ((G.base.metric t).restrictOpen U)
      (restrictOpen0S (I := I) 2 (V := U) (B n q t - C q t)) (A n q t - C' q t) r xU heq
    rw [tensor02CovDerivNormWith_restrictOpen0S] at hnorm
    rw [hnorm]
    exact hN n hn t ht xU hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_metric_time_jets_extension_on_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_metric_time_jets_extension_on_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_metric_time_jets_extension_on_compact ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_metric_time_jets_extension_on_compact
end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
