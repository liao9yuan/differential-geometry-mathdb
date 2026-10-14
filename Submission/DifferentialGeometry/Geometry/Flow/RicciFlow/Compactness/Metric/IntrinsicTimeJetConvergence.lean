import Submission.DifferentialGeometry.Analysis.Calculus.IteratedDerivative.WithinTower
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.UniformTensorNorm
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CompactPointedChartControl
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Pullback
import Submission.DifferentialGeometry.Topology.Manifold.ModelWithCorners
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCrossConvergence
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Naturality.CrossTensorPullback

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

section InnerProductModel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private theorem metric_time_jet_errors_uniform_on_compacts_of_inner_product_space
    {D : RealTimeInterval}
    (S : ℕ → SolutionOn (I := I) (M := M) D) (hS : ∀ n, IsSolutionOn (S n))
    (S₀ : SolutionOn (I := I) (M := M) D) (hS₀ : IsSolutionOn S₀)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hcarrier : D.carrier = _root_.Set.Icc a b) (hregular : _root_.Set.Ioo a b ⊆ D.regular)
    (R : SmoothRiemannianMetric I M)
    (hconv : ∀ K : Set M, IsCompact K → ∀ r : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ _root_.Set.Icc c b,
        metricDerivNormSupOn K r ((S n).base.metric t) (S₀.base.metric t) R < epsilon)
    (B : ℕ → ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (C : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (hBzero : ∀ n s, B n 0 s = metricTensorField ((S n).base.metric s))
    (hCzero : ∀ s, C 0 s = metricTensorField (S₀.base.metric s))
    (hB : ∀ n q s, s ∈ _root_.Set.Icc c b → ∀ x : M,
      HasDerivWithinAt (fun t => B n q t x) (B n (q + 1) s x) (_root_.Set.Icc c b) s)
    (hC : ∀ q s, s ∈ _root_.Set.Icc c b → ∀ x : M,
      HasDerivWithinAt (fun t => C q t x) (C (q + 1) s x) (_root_.Set.Icc c b) s)
    {K : Set M} (hK : IsCompact K) (r q : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ _root_.Set.Icc c b, ∀ x ∈ K,
      tensor02CovDerivNormWith (I := I) r (B n q t - C q t)
        (S₀.base.metric t) (S₀.base.metric t) x ≤ ε := by
  let F : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2 :=
    fun n t => B n q t - C q t
  apply uniform_on_compact_of_restricted_chart_bounds (I := I) (⊤ : TopologicalSpace.Opens M)
    hK (fun _ _ => _root_.Set.mem_univ _)
    (fun n t x => tensor02CovDerivNormWith (I := I) r (F n t)
      (S₀.base.metric t) (S₀.base.metric t) x) (_root_.Set.Icc c b)
  intro p Q hQ hQt
  have hU := isOpen_extChartAt_target (I := I) p
  have hUt := extChartAt_opens_target_subset (I := I) (⊤ : TopologicalSpace.Opens M) p
  have hBactual (n q : ℕ) (t : ℝ) (ht : t ∈ _root_.Set.Icc c b) (x : M) :
      B n q t x = iteratedDerivWithin q (fun s => metricTensorField ((S n).base.metric s) x)
        (_root_.Set.Icc c b) t := by
    apply (DifferentialGeometry.Analysis.iteratedDerivWithin_eq_of_hasDerivWithinAt
      (uniqueDiffOn_Icc hcb) _ (fun k s => B n k s x)
      (fun k s hs => hB n k s hs x) _ q ht).symm
    intro s _hs
    simp only [hBzero]
  have hCactual (q : ℕ) (t : ℝ) (ht : t ∈ _root_.Set.Icc c b) (x : M) :
      C q t x = iteratedDerivWithin q (fun s => metricTensorField (S₀.base.metric s) x)
        (_root_.Set.Icc c b) t := by
    apply (DifferentialGeometry.Analysis.iteratedDerivWithin_eq_of_hasDerivWithinAt
      (uniqueDiffOn_Icc hcb) _ (fun k s => C k s x)
      (fun k s hs => hC k s hs x) _ q ht).symm
    intro s _hs
    simp only [hCzero]
  have hcoord (slots : Fin 2 → Fin (Module.finrank ℝ E))
      (Q' : Set E) (hQ' : IsCompact Q') (hQ't : Q' ⊆ (extChartAt I p).target)
      (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ _root_.Set.Icc c b, ∀ y ∈ Q',
        ‖iteratedFDeriv ℝ m (fun z => F n t ((extChartAt I (p : M)).symm z)
          (fun j => chartBasisVecFiber (I := I) (p : M) (slots j)
            ((extChartAt I (p : M)).symm z))) y‖ ≤ ε := by
    obtain ⟨N, hN⟩ := uniform_ordinary_metric_jets_of_metric_convergence_on_closed_interval
      S hS S₀ hS₀ hac hcb hcarrier hregular _root_.CompactIccSpace.isCompact_Icc Subset.rfl
      (p : M) hU hUt R hconv hQ' hQ't m q slots ε hε
    refine ⟨N, fun n hn t ht y hy => ?_⟩
    have hBc := tensor_field_chart_components_contDiffOn (B n q t) (p : M) hUt slots
    have hCc := tensor_field_chart_components_contDiffOn (C q t) (p : M) hUt slots
    have hsub := iteratedFDeriv_sub_apply (i := m)
      ((hBc.contDiffAt (hU.mem_nhds (hQ't hy))).of_le (by exact_mod_cast le_top))
      ((hCc.contDiffAt (hU.mem_nhds (hQ't hy))).of_le (by exact_mod_cast le_top))
    have hh := hN n hn t ht y hy
    simp_rw [← hBactual n q t ht, ← hCactual q t ht] at hh
    rw [← hsub] at hh
    exact hh
  exact uniform_tensor02_covariant_norm_on_compact_time_of_closed_interval S₀ hS₀
    hac hcb (by rw [hcarrier]) hregular _root_.CompactIccSpace.isCompact_Icc Subset.rfl
    F (p : M) hU hUt hcoord hQ hQt r

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metric_time_jet_errors_uniform_on_compacts_of_inner_product_space
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metric_time_jet_errors_uniform_on_compacts_of_inner_product_space target :: scope.openDecls } }

end InnerProductModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem metric_time_jet_errors_uniform_on_compacts_of_closed_interval {D : RealTimeInterval}
    (S : ℕ → SolutionOn (I := I) (M := M) D) (hS : ∀ n, IsSolutionOn (S n))
    (S₀ : SolutionOn (I := I) (M := M) D) (hS₀ : IsSolutionOn S₀)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hcarrier : D.carrier = _root_.Set.Icc a b) (hregular : _root_.Set.Ioo a b ⊆ D.regular)
    (R : SmoothRiemannianMetric I M)
    (hconv : ∀ K : Set M, IsCompact K → ∀ r : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ _root_.Set.Icc c b,
        metricDerivNormSupOn K r ((S n).base.metric t) (S₀.base.metric t) R < epsilon)
    (B : ℕ → ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (C : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (hBzero : ∀ n s, B n 0 s = metricTensorField ((S n).base.metric s))
    (hCzero : ∀ s, C 0 s = metricTensorField (S₀.base.metric s))
    (hB : ∀ n q s, s ∈ _root_.Set.Icc c b → ∀ x : M,
      HasDerivWithinAt (fun t => B n q t x) (B n (q + 1) s x) (_root_.Set.Icc c b) s)
    (hC : ∀ q s, s ∈ _root_.Set.Icc c b → ∀ x : M,
      HasDerivWithinAt (fun t => C q t x) (C (q + 1) s x) (_root_.Set.Icc c b) s)
    {K : Set M} (hK : IsCompact K) (r q : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ _root_.Set.Icc c b, ∀ x ∈ K,
      tensor02CovDerivNormWith (I := I) r (B n q t - C q t)
        (S₀.base.metric t) (S₀.base.metric t) x ≤ ε := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (Module.finBasis ℝ E).equivFun.toContinuousLinearEquiv.trans
      (EuclideanSpace.equiv (Fin (Module.finrank ℝ E)) ℝ).symm
  let J := I.transContinuousLinearEquiv e
  let Φ := ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I M e
  let U : ℕ → SolutionOn (I := J) (M := M) D := fun n => (S n).pullback Φ.symm
  let U₀ : SolutionOn (I := J) (M := M) D := S₀.pullback Φ.symm
  have hU : ∀ n, IsSolutionOn (U n) := fun n => (hS n).pullback (S n) Φ.symm
  have hU₀ : IsSolutionOn U₀ := hS₀.pullback S₀ Φ.symm
  let R' : SmoothRiemannianMetric J M := Diffeomorph.pullbackMetricCross R Φ.symm
  have hconv' : ∀ L : Set M, IsCompact L → ∀ r : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ _root_.Set.Icc c b,
        metricDerivNormSupOn L r ((U n).base.metric t) (U₀.base.metric t) R' < epsilon := by
    intro L hL r epsilon hepsilon
    obtain ⟨N, hN⟩ := hconv (Φ.symm '' L) (hL.image Φ.symm.continuous) r epsilon hepsilon
    refine ⟨N, fun n hn t ht => ?_⟩
    change metricDerivNormSupOn L r
      (Diffeomorph.pullbackMetricCross ((S n).base.metric t) Φ.symm)
      (Diffeomorph.pullbackMetricCross (S₀.base.metric t) Φ.symm)
      (Diffeomorph.pullbackMetricCross R Φ.symm) < epsilon
    rw [metricDerivNormSupOn_pullbackCross_image]
    exact hN n hn t ht
  let B' : ℕ → ℕ → ℝ → Tensor0SField (I := J) (M := M) (n := ∞) 2 :=
    fun n q t => pullbackTensor02FieldCross Φ.symm (B n q t)
  let C' : ℕ → ℝ → Tensor0SField (I := J) (M := M) (n := ∞) 2 :=
    fun q t => pullbackTensor02FieldCross Φ.symm (C q t)
  have hB'zero (n : ℕ) (s : ℝ) : B' n 0 s = metricTensorField ((U n).base.metric s) := by
    ext x v
    change pullbackTensor02FieldCross Φ.symm (B n 0 s) x v = _
    rw [hBzero, pullbackTensor02FieldCross_apply, metricTensorField_apply]
    exact (Diffeomorph.pullbackMetricCross_inner ((S n).base.metric s) Φ.symm x (v 0) (v 1)).symm
  have hC'zero (s : ℝ) : C' 0 s = metricTensorField (U₀.base.metric s) := by
    ext x v
    change pullbackTensor02FieldCross Φ.symm (C 0 s) x v = _
    rw [hCzero, pullbackTensor02FieldCross_apply, metricTensorField_apply]
    exact (Diffeomorph.pullbackMetricCross_inner (S₀.base.metric s) Φ.symm x (v 0) (v 1)).symm
  have hB' (n q : ℕ) (s : ℝ) (hs : s ∈ _root_.Set.Icc c b) (x : M) :
      HasDerivWithinAt (fun t => B' n q t x) (B' n (q + 1) s x) (_root_.Set.Icc c b) s :=
    hasDerivWithinAt_pullbackTensor02FieldCross Φ.symm (B n q) (B n (q + 1) s) x
      (hB n q s hs (Φ.symm x))
  have hC' (q : ℕ) (s : ℝ) (hs : s ∈ _root_.Set.Icc c b) (x : M) :
      HasDerivWithinAt (fun t => C' q t x) (C' (q + 1) s x) (_root_.Set.Icc c b) s :=
    hasDerivWithinAt_pullbackTensor02FieldCross Φ.symm (C q) (C (q + 1) s) x
      (hC q s hs (Φ.symm x))
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := metric_time_jet_errors_uniform_on_compacts_of_inner_product_space
    U hU U₀ hU₀ hac hcb hcarrier hregular R' hconv' B' C' hB'zero hC'zero hB' hC'
    (hK.image Φ.continuous) r q epsilon hepsilon
  refine ⟨N, fun n hn t ht x hx => ?_⟩
  have hnorm := tensor02CovDerivNormWith_pullbackCross
    (S₀.base.metric t) (S₀.base.metric t) Φ.symm (B' n q t - C' q t) (B n q t - C q t)
    (fun y v => by
      change pullbackTensor02FieldCross Φ.symm (B n q t) y v -
        pullbackTensor02FieldCross Φ.symm (C q t) y v = _
      rw [pullbackTensor02FieldCross_apply, pullbackTensor02FieldCross_apply]
      rfl) r (Φ x)
  have hbound := hN n hn t ht (Φ x) (_root_.Set.mem_image_of_mem _ hx)
  change tensor02CovDerivNormWith r (B' n q t - C' q t)
    (Diffeomorph.pullbackMetricCross (S₀.base.metric t) Φ.symm)
    (Diffeomorph.pullbackMetricCross (S₀.base.metric t) Φ.symm) (Φ x) ≤ epsilon at hbound
  rw [hnorm, Φ.symm_apply_apply] at hbound
  exact hbound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metric_time_jet_errors_uniform_on_compacts_of_closed_interval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metric_time_jet_errors_uniform_on_compacts_of_closed_interval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metric_time_jet_errors_uniform_on_compacts_of_closed_interval ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metric_time_jet_errors_uniform_on_compacts_of_closed_interval

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
