import Submission.DifferentialGeometry.Analysis.Integration.Measure.Chart.Density
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Jacobian.UniformConvergence
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.ContDiff _root_.Matrix.Norms.Elementwise _root_.Topology

namespace DifferentialGeometry.Integral.Measure

open _root_.Submission.DifferentialGeometry.Tensor.Coordinates _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Operator (chartGramOnE chartGramOnE_contDiffOn)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem tendstoUniformlyOn_chartDensity_of_metricDerivNorm
    {ι : Type*} {l : Filter ι}
    (g : ι → SmoothRiemannianMetric I M) (gInf R : SmoothRiemannianMetric I M)
    (alpha : M) {K : Set E} (hK : IsCompact K)
    (hKchart : K ⊆ (extChartAt I alpha).target)
    (hconv : TendstoUniformlyOn
      (fun k z => metricDerivNorm (I := I) 0 (g k) gInf R ((extChartAt I alpha).symm z))
      (fun _ => 0) l K) :
    TendstoUniformlyOn
      (fun k z => chartDensity (g k) alpha ((extChartAt I alpha).symm z))
      (fun z => chartDensity gInf alpha ((extChartAt I alpha).symm z)) l K := by
  classical
  let : CompleteSpace E := FiniteDimensional.complete Real E
  have hb : ∀ i : Fin (Module.finrank Real E), ∃ C : Real,
      ∀ z ∈ K, Real.sqrt (chartGramOnE R alpha i i z) ≤ C := by
    intro i
    obtain ⟨C, hC⟩ := hK.bddAbove_image
      ((Real.continuous_sqrt.comp_continuousOn (chartGramOnE_contDiffOn R alpha i i).continuousOn).mono hKchart)
    exact ⟨C, fun z hz => hC ⟨z, hz, rfl⟩⟩
  choose C hC using hb
  let A : Real := ∑ i, _root_.Max.max (C i) 0
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => le_max_right _ _
  have hAi (i : Fin (Module.finrank Real E)) : C i ≤ A :=
    (le_max_left _ _).trans
      (Finset.single_le_sum (fun j _ => le_max_right (C j) 0) (Finset.mem_univ i))
  let : UniformSpace
      (Matrix (Fin (Module.finrank Real E)) (Fin (Module.finrank Real E)) Real) :=
    PseudoMetricSpace.toUniformSpace
  let G : ι → K → Matrix (Fin (Module.finrank Real E)) (Fin (Module.finrank Real E)) Real :=
    fun k z => chartGramMatrix (g k) alpha ((extChartAt I alpha).symm z)
  let GInf : K → Matrix (Fin (Module.finrank Real E)) (Fin (Module.finrank Real E)) Real :=
    fun z => chartGramMatrix gInf alpha ((extChartAt I alpha).symm z)
  have hG : TendstoUniformly G GInf l := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have hden : 0 < A ^ 2 + 1 := by positivity
    have hδ : 0 < ε / (A ^ 2 + 1) := div_pos hε hden
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv (ε / (A ^ 2 + 1)) hδ] with k hk
    intro z
    apply (dist_pi_lt_iff hε).2
    intro i
    apply (dist_pi_lt_iff hε).2
    intro j
    let x := (extChartAt I alpha).symm (z : E)
    let v := chartBasisVecFiber (I := I) alpha i x
    let w := chartBasisVecFiber (I := I) alpha j x
    have hi : Real.sqrt (R.inner x v v) ≤ A := (hC i z z.2).trans (hAi i)
    have hj : Real.sqrt (R.inner x w w) ≤ A := (hC j z z.2).trans (hAi j)
    have hn : 0 ≤ metricDerivNorm (I := I) 0 (g k) gInf R x := Real.sqrt_nonneg _
    have hsmall : metricDerivNorm (I := I) 0 (g k) gInf R x < ε / (A ^ 2 + 1) := by
      simpa only [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hn, x] using hk z z.2
    have hbound := metricDifference_abs_le (g k) gInf R x v w
    have hbound' : |(g k).inner x v w - gInf.inner x v w| ≤
        A ^ 2 * metricDerivNorm (I := I) 0 (g k) gInf R x := by
      refine hbound.trans ?_
      calc
        _ ≤ metricDerivNorm (I := I) 0 (g k) gInf R x * A * A :=
          mul_le_mul (mul_le_mul_of_nonneg_left hi hn) hj
            (Real.sqrt_nonneg _) (mul_nonneg hn hA)
        _ = _ := by ring
    have hlt : A ^ 2 * metricDerivNorm (I := I) 0 (g k) gInf R x < ε := by
      calc
        _ ≤ A ^ 2 * (ε / (A ^ 2 + 1)) := mul_le_mul_of_nonneg_left hsmall.le (sq_nonneg A)
        _ < (A ^ 2 + 1) * (ε / (A ^ 2 + 1)) :=
          mul_lt_mul_of_pos_right (lt_add_one _) hδ
        _ = ε := mul_div_cancel₀ ε hden.ne'
    change _root_.Dist.dist (gInf.inner x v w) ((g k).inner x v w) < ε
    rw [Real.dist_eq, abs_sub_comm]
    exact hbound'.trans_lt hlt
  have hCont : ContinuousOn
      (fun z => chartGramMatrix gInf alpha ((extChartAt I alpha).symm z)) K := by
    apply continuousOn_pi.2
    intro i
    apply continuousOn_pi.2
    intro j
    exact (chartGramOnE_contDiffOn gInf alpha i j).continuousOn.mono hKchart
  have hbInf : Bornology.IsBounded (_root_.Set.range GInf) := by
    apply (hK.image_of_continuousOn hCont).isBounded.subset
    rintro A' ⟨z, rfl⟩
    exact ⟨z, z.2, rfl⟩
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  exact hG.sqrt_det hbInf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.tendstoUniformlyOn_chartDensity_of_metricDerivNorm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.tendstoUniformlyOn_chartDensity_of_metricDerivNorm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.tendstoUniformlyOn_chartDensity_of_metricDerivNorm ``Submission.DifferentialGeometry.Integral.Measure.tendstoUniformlyOn_chartDensity_of_metricDerivNorm

end DifferentialGeometry.Integral.Measure
