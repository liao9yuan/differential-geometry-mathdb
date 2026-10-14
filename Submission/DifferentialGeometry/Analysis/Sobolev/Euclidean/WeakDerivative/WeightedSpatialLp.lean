import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.SpatialLp
import Submission.DifferentialGeometry.Analysis.Integration.Lp.ContinuousOn
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.BigOperators _root_.ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem memLp_weighted_spatial_fderiv_of_locallyLipschitzOn
    {a b : ℝ} {Ω : Set E} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    {u : ℝ × E → ℝ} (hu : LocallyLipschitzOn (_root_.Set.Icc a b ×ˢ closure Ω) u)
    {c : Fin d → ℝ × E → ℝ}
    (hc : ∀ i, ContinuousOn (c i) (_root_.Set.Icc a b ×ˢ closure Ω)) (p : ℝ≥0∞) :
    _root_.MeasureTheory.MemLp (fun q : ℝ × E => ∑ i, c i q *
      fderiv ℝ (fun x => u (q.1, x)) q.2 (EuclideanSpace.single i 1)) p
        ((volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)) := by
  apply _root_.MeasureTheory.memLp_finsetSum Finset.univ
  intro i _
  have hci : _root_.MeasureTheory.MemLp (c i) ∞
      ((volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)) := by
    rw [Measure.prod_restrict]
    exact (hc i).memLp_top_of_subset_isCompact (isCompact_Icc.prod hΩc)
      (measurableSet_Icc.prod hΩ.measurableSet) (_root_.Set.prod_mono Subset.rfl subset_closure)
  exact (memLp_spatial_fderiv_of_locallyLipschitzOn hΩ hΩc hu p i).mul' (r := p) hci

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.memLp_weighted_spatial_fderiv_of_locallyLipschitzOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.memLp_weighted_spatial_fderiv_of_locallyLipschitzOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.memLp_weighted_spatial_fderiv_of_locallyLipschitzOn ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.memLp_weighted_spatial_fderiv_of_locallyLipschitzOn

theorem integrable_weighted_fderiv_pairings_of_locallyLipschitzOn
    {a b : ℝ} {Ω : Set E} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    {u w : ℝ × E → ℝ} {A : ℝ × E → Fin d → Fin d → ℝ}
    (hu : LocallyLipschitzOn (_root_.Set.Icc a b ×ˢ closure Ω) u)
    (hw : ContinuousOn w (_root_.Set.Icc a b ×ˢ closure Ω))
    (hA : ∀ i j, ContinuousOn (fun q => A q i j) (_root_.Set.Icc a b ×ˢ closure Ω))
    {φ : ℝ × E → ℝ} (hφ : ContDiff ℝ 1 φ) :
    _root_.MeasureTheory.Integrable (fun q => w q * u q * fderiv ℝ φ q (1, 0))
      ((volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)) ∧
    ∀ j, _root_.MeasureTheory.Integrable (fun q =>
      (∑ i, w q * A q i j *
        fderiv ℝ (fun x => u (q.1, x)) q.2 (EuclideanSpace.single i 1)) *
          fderiv ℝ φ q (0, EuclideanSpace.single j 1))
      ((volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)) := by
  have htest (v : ℝ × E) : Continuous (fun q => fderiv ℝ φ q v) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  constructor
  · have hc : ContinuousOn (fun q => w q * u q * fderiv ℝ φ q (1, 0))
        (_root_.Set.Icc a b ×ˢ closure Ω) :=
      (hw.mul hu.continuousOn).mul (htest (1, 0)).continuousOn
    rw [Measure.prod_restrict]
    exact (hc.integrableOn_compact (isCompact_Icc.prod hΩc)).mono_set
      (_root_.Set.prod_mono Subset.rfl subset_closure)
  · intro j
    have hweighted : _root_.MeasureTheory.MemLp (fun q : ℝ × E => ∑ i, w q * A q i j *
        fderiv ℝ (fun x => u (q.1, x)) q.2 (EuclideanSpace.single i 1)) 1
        ((volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)) :=
      memLp_weighted_spatial_fderiv_of_locallyLipschitzOn hΩ hΩc hu
        (fun i => hw.mul (hA i j)) 1
    have htestMem : _root_.MeasureTheory.MemLp
        (fun q : ℝ × E => fderiv ℝ φ q (0, EuclideanSpace.single j 1)) ∞
        ((volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)) := by
      rw [Measure.prod_restrict]
      exact (htest (0, EuclideanSpace.single j 1)).continuousOn.memLp_top_of_subset_isCompact
        (isCompact_Icc.prod hΩc) (measurableSet_Icc.prod hΩ.measurableSet)
        (_root_.Set.prod_mono Subset.rfl subset_closure)
    exact memLp_one_iff_integrable.mp (htestMem.mul' (r := 1) hweighted)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.integrable_weighted_fderiv_pairings_of_locallyLipschitzOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.integrable_weighted_fderiv_pairings_of_locallyLipschitzOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.integrable_weighted_fderiv_pairings_of_locallyLipschitzOn ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.integrable_weighted_fderiv_pairings_of_locallyLipschitzOn

end DifferentialGeometry.Analysis.Sobolev.Euclidean
