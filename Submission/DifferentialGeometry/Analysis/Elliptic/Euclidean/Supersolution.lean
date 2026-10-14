import Submission.DifferentialGeometry.Analysis.Elliptic.Euclidean.WeakFormulation
import Submission.DifferentialGeometry.External.DeGiorgi.WeakFormulation.ExistenceTheory
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Divergence
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.ClassicalDivergence
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Classical

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section
open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory

namespace DeGiorgi

variable {d : ℕ} [NeZero d]
local notation "V" => EuclideanSpace ℝ (Fin d)

theorem isSupersolution_of_hasWeakDiv_nonpos
    {Ω : Set V} (hΩ : IsOpen Ω) {A : EllipticCoeff d Ω} {u g : V → ℝ}
    (hu : MemW1pWitness 2 u Ω) (hg : _root_.MeasureTheory.MemLp g 2 (volume.restrict Ω))
    (hdiv : HasWeakDiv g (fun x => matMulE (A.a x) (hu.weakGrad x)) Ω)
    (hg0 : ∀ᵐ x ∂volume.restrict Ω, g x ≤ 0) : IsSupersolution A u := by
  have hweak := (bilinFormOfCoeff_eq_integral_iff_hasWeakDiv hΩ hu hg.neg).mpr
    (by simpa only [Pi.neg_apply, neg_neg] using hdiv)
  refine ⟨hu.memW1p, ?_⟩
  intro hw φ hφ0 hφ hφpos
  rw [bilinFormOfCoeff_eq_left hΩ A hw hu hφ, hweak φ hφ0 hφ]
  exact _root_.MeasureTheory.integral_nonneg_of_ae (hg0.mono fun x hx => mul_nonneg (neg_nonneg.mpr hx) (hφpos x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.isSupersolution_of_hasWeakDiv_nonpos then
    throwError "Refusing to shadow existing declaration DeGiorgi.isSupersolution_of_hasWeakDiv_nonpos"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.isSupersolution_of_hasWeakDiv_nonpos ``Submission.DeGiorgi.isSupersolution_of_hasWeakDiv_nonpos

end DeGiorgi

end

end

section

noncomputable section
open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.ContDiff _root_.ENNReal

namespace DeGiorgi
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} [NeZero d]
local notation "V" => EuclideanSpace ℝ (Fin d)

theorem isSupersolution_on_ball_of_divergence_nonpos
    {N : Set V} (hN : IsOpen N) {c : V} {R : ℝ} (hball : Metric.closedBall c R ⊆ N)
    (A : EllipticCoeff d (Metric.ball c R)) (a : V → Matrix (Fin d) (Fin d) ℝ)
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) N)
    (hAa : _root_.Set.EqOn A.a a (Metric.ball c R)) {u : V → ℝ} (hu : ContDiffOn ℝ 2 u N)
    (hdiv : ∀ x ∈ Metric.ball c R,
      (∑ i, fderiv ℝ (fun y => matMulE (a y) (smoothGradField u y) i) x
        (EuclideanSpace.single i 1)) ≤ 0) : IsSupersolution A u := by
  let F := fun x => matMulE (a x) (smoothGradField u x)
  let g := fun x => ∑ i, fderiv ℝ (fun y => F y i) x (EuclideanSpace.single i 1)
  have hF (i : Fin d) : ContDiffOn ℝ 1 (fun x => F x i) N := by
    change ContDiffOn ℝ 1 (fun x => ∑ j,
      a x i j * fderiv ℝ u x (EuclideanSpace.single j 1)) N
    apply ContDiffOn.sum
    intro j _
    exact (ha i j).mul ((hu.fderiv_of_isOpen hN (by norm_num)).clm_apply contDiffOn_const)
  have hgc : ContinuousOn g (Metric.closedBall c R) := by
    apply (continuousOn_finsetSum _ (fun i _ =>
      ((hF i).continuousOn_fderiv_of_isOpen hN le_rfl).clm_apply continuousOn_const)).mono hball
  have hgLp : _root_.MeasureTheory.MemLp g 2 (volume.restrict (Metric.ball c R)) := by
    let : _root_.MeasureTheory.IsFiniteMeasure (volume.restrict (Metric.ball c R)) :=
      isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    obtain ⟨C, hC⟩ := (_root_.ProperSpace.isCompact_closedBall c R).exists_bound_of_continuousOn hgc
    apply MemLp.of_bound
      ((hgc.mono Metric.ball_subset_closedBall).aestronglyMeasurable
        Metric.isOpen_ball.measurableSet) C
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    exact hC x (Metric.ball_subset_closedBall hx)
  obtain ⟨hw, hgrad⟩ := exists_memW1pWitness_of_contDiffOn_closedBall hN
    (hu.of_le (by norm_num)) hball 2
  have hdivF : HasWeakDiv g F (Metric.ball c R) := hasWeakDiv_of_contDiffOn Metric.isOpen_ball
    (fun i => (hF i).mono (Metric.ball_subset_closedBall.trans hball))
  have hflux : F =ᵐ[volume.restrict (Metric.ball c R)]
      (fun x => matMulE (A.a x) (hw.weakGrad x)) := by
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    have hgx : hw.weakGrad x = smoothGradField u x := by ext j; exact hgrad x j
    change matMulE (a x) (smoothGradField u x) = _
    rw [hAa hx, hgx]
  exact isSupersolution_of_hasWeakDiv_nonpos Metric.isOpen_ball hw hgLp
    (hdivF.congr_ae EventuallyEq.rfl hflux)
    ((_root_.MeasureTheory.ae_restrict_mem Metric.isOpen_ball.measurableSet).mono (fun x hx => hdiv x hx))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.isSupersolution_on_ball_of_divergence_nonpos then
    throwError "Refusing to shadow existing declaration DeGiorgi.isSupersolution_on_ball_of_divergence_nonpos"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.isSupersolution_on_ball_of_divergence_nonpos ``Submission.DeGiorgi.isSupersolution_on_ball_of_divergence_nonpos

end DeGiorgi

end

end
