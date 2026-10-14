import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Variation
import Submission.DifferentialGeometry.Analysis.Integration.Lp.QuadraticBounds
import Submission.DifferentialGeometry.Analysis.Calculus.Variation.Quadratic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Submission.DifferentialGeometry.Analysis.Integration.Lp.Bilinear
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.DirichletEnergy.Locality
import Mathlib.Topology.MetricSpace.Thickening

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section
open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Topology _root_.ENNReal _root_.ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

section Measurability

private theorem aestronglyMeasurable_clm_apply
    {α X Y : Type*} [MeasurableSpace α] [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {μ : _root_.MeasureTheory.Measure α}
    {f : α → X →L[ℝ] Y} {u : α → X}
    (hf : _root_.MeasureTheory.AEStronglyMeasurable f μ) (hu : _root_.MeasureTheory.AEStronglyMeasurable u μ) :
    AEStronglyMeasurable (fun x => f x (u x)) μ :=
  (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable (hf.prodMk hu)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.aestronglyMeasurable_clm_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.aestronglyMeasurable_clm_apply target :: scope.openDecls } }

private theorem aestronglyMeasurable_comp_of_continuousOn
    {α X Y : Type*} [MeasurableSpace α] [NormedAddCommGroup X]
    [MeasurableSpace X] [BorelSpace X] [NormedAddCommGroup Y]
    [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    {μ : _root_.MeasureTheory.Measure α} {f : X → Y} {V : Set X} (hV : MeasurableSet V)
    (hf : ContinuousOn f V) {u : α → X} (hu : _root_.MeasureTheory.AEStronglyMeasurable u μ)
    (huV : ∀ᵐ x ∂μ, u x ∈ V) : _root_.MeasureTheory.AEStronglyMeasurable (fun x => f (u x)) μ := by
  classical
  have hm : Measurable (V.piecewise f (fun _ => 0)) :=
    hf.measurable_piecewise continuousOn_const hV
  exact (hm.comp_aemeasurable hu.aemeasurable).aestronglyMeasurable.congr
    (huV.mono fun x hx => Set.piecewise_eq_of_mem V f (fun _ => 0) hx)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.aestronglyMeasurable_comp_of_continuousOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.aestronglyMeasurable_comp_of_continuousOn target :: scope.openDecls } }

end Measurability

section Integral

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
local instance metricFormNormedAdd : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.metricFormNormedAdd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.metricFormNormedAdd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.metricFormNormedAdd ``Submission.DifferentialGeometry.Analysis.Sobolev.metricFormNormedAdd
local instance metricFormNormedSpace : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.metricFormNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.metricFormNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.metricFormNormedSpace ``Submission.DifferentialGeometry.Analysis.Sobolev.metricFormNormedSpace
local instance metricDerivNormedAdd : NormedAddCommGroup (F →L[ℝ] (F →L[ℝ] F →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.metricDerivNormedAdd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.metricDerivNormedAdd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.metricDerivNormedAdd ``Submission.DifferentialGeometry.Analysis.Sobolev.metricDerivNormedAdd
local instance metricDerivNormedSpace : NormedSpace ℝ (F →L[ℝ] (F →L[ℝ] F →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.metricDerivNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.metricDerivNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.metricDerivNormedSpace ``Submission.DifferentialGeometry.Analysis.Sobolev.metricDerivNormedSpace

private theorem hasDerivAt_integral_metric_energy
    {α ι : Type*} [MeasurableSpace α] [Fintype ι] {μ : _root_.MeasureTheory.Measure α}
    {u φ : α → F} (hu : _root_.MeasureTheory.AEStronglyMeasurable u μ) (hφm : _root_.MeasureTheory.AEStronglyMeasurable φ μ)
    {v w : ι → α → F} (hv : ∀ j, _root_.MeasureTheory.MemLp (v j) 2 μ) (hw : ∀ j, _root_.MeasureTheory.MemLp (w j) 2 μ)
    {A : F → F →L[ℝ] F →L[ℝ] ℝ} {V K : Set F}
    (hV : IsOpen V) (hA : ContDiffOn ℝ 1 A V) (hK : IsCompact K) (hKV : K ⊆ V)
    (huK : ∀ᵐ x ∂μ, u x ∈ K) (P : ℝ) (hP : 0 ≤ P) (hφ : ∀ x, ‖φ x‖ ≤ P) :
    _root_.MeasureTheory.Integrable (fun x => (∑ j : ι,
      ((fderiv ℝ A (u x) (φ x)) (v j x) (v j x) +
        A (u x) (w j x) (v j x) + A (u x) (v j x) (w j x)))) μ ∧
    HasDerivAt (fun t : ℝ => ∫ x, ∑ j : ι,
      A (u x + t • φ x) (v j x + t • w j x) (v j x + t • w j x) ∂μ)
      (∫ x, (∑ j : ι, ((fderiv ℝ A (u x) (φ x)) (v j x) (v j x) +
        A (u x) (w j x) (v j x) + A (u x) (v j x) (w j x))) ∂μ) 0 := by
  classical
  borelize F (F →L[ℝ] F →L[ℝ] ℝ) (F →L[ℝ] (F →L[ℝ] F →L[ℝ] ℝ))
  obtain ⟨δ₀, hδ₀, C, hC, hbounds⟩ := exists_compact_metric_range_bounds hV hA hK hKV P hP
  let δ := _root_.Min.min δ₀ 1
  have hδ : 0 < δ := lt_min hδ₀ zero_lt_one
  have hδ₀le : δ ≤ δ₀ := min_le_left _ _
  have hδone : δ ≤ 1 := min_le_right _ _
  let U := fun (t : ℝ) (x : α) => u x + t • φ x
  let W := fun (t : ℝ) (j : ι) (x : α) => v j x + t • w j x
  let f := fun (t : ℝ) (x : α) => ∑ j : ι, A (U t x) (W t j x) (W t j x)
  let f' := fun (t : ℝ) (x : α) => ∑ j : ι, ((fderiv ℝ A (U t x) (φ x)) (W t j x) (W t j x) +
      A (U t x) (w j x) (W t j x) + A (U t x) (W t j x) (w j x))
  have hbu (x : α) (hx : u x ∈ K) (t : ℝ) (ht : |t| < δ) :
      U t x ∈ V ∧ ‖A (U t x)‖ ≤ C ∧ ‖fderiv ℝ A (U t x)‖ ≤ C :=
    hbounds (u x) hx (φ x) (hφ x) t (ht.trans_le hδ₀le)
  have hUm (t : ℝ) : _root_.MeasureTheory.AEStronglyMeasurable (U t) μ := hu.add (hφm.const_smul t)
  have hWm (t : ℝ) (j : ι) : _root_.MeasureTheory.AEStronglyMeasurable (W t j) μ :=
    (hv j).aestronglyMeasurable.add ((hw j).aestronglyMeasurable.const_smul t)
  have hAm (t : ℝ) (ht : |t| < δ) : _root_.MeasureTheory.AEStronglyMeasurable (fun x => A (U t x)) μ :=
    aestronglyMeasurable_comp_of_continuousOn hV.measurableSet hA.continuousOn (hUm t)
      (huK.mono fun x hx => (hbu x hx t ht).1)
  have hDAm (t : ℝ) (ht : |t| < δ) : _root_.MeasureTheory.AEStronglyMeasurable (fun x => fderiv ℝ A (U t x)) μ :=
    aestronglyMeasurable_comp_of_continuousOn hV.measurableSet
      (hA.continuousOn_fderiv_of_isOpen hV le_rfl) (hUm t)
      (huK.mono fun x hx => (hbu x hx t ht).1)
  have hfm (t : ℝ) (ht : |t| < δ) : _root_.MeasureTheory.AEStronglyMeasurable (f t) μ := by
    have hh := Finset.aestronglyMeasurable_sum Finset.univ (fun (j : ι) _ =>
      aestronglyMeasurable_clm_apply
        (aestronglyMeasurable_clm_apply (hAm t ht) (hWm t j)) (hWm t j))
    convert hh using 1
    funext x
    simp only [f, Finset.sum_apply]
  have hf'm (t : ℝ) (ht : |t| < δ) : _root_.MeasureTheory.AEStronglyMeasurable (f' t) μ := by
    have hh := Finset.aestronglyMeasurable_sum Finset.univ (fun (j : ι) _ =>
      ((aestronglyMeasurable_clm_apply
        (aestronglyMeasurable_clm_apply (aestronglyMeasurable_clm_apply (hDAm t ht) hφm)
          (hWm t j)) (hWm t j)).add
        (aestronglyMeasurable_clm_apply
          (aestronglyMeasurable_clm_apply (hAm t ht) (hw j).aestronglyMeasurable) (hWm t j))).add
        (aestronglyMeasurable_clm_apply
          (aestronglyMeasurable_clm_apply (hAm t ht) (hWm t j)) (hw j).aestronglyMeasurable))
    convert hh using 1
    funext x
    simp only [f', Finset.sum_apply, Pi.add_apply]
  have hf0 : _root_.MeasureTheory.Integrable (f 0) μ := by
    refine (integrable_sum_norm_sq hv C).mono' (hfm 0 (by simpa using hδ)) ?_
    filter_upwards [huK] with x hx
    simp only [f, U, W, zero_smul, add_zero]
    calc
      ‖∑ j : ι, A (u x) (v j x) (v j x)‖ ≤ ∑ j : ι, ‖A (u x) (v j x) (v j x)‖ := norm_sum_le _ _
      _ ≤ ∑ j : ι, C * ‖v j x‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        have hAy : ‖A (u x)‖ ≤ C := by simpa only [U, zero_smul, add_zero] using
          (hbu x hx 0 (by simpa using hδ)).2.1
        calc
          _ ≤ ‖A (u x)‖ * ‖v j x‖ * ‖v j x‖ := ContinuousLinearMap.le_opNorm₂ _ _ _
          _ ≤ C * ‖v j x‖ * ‖v j x‖ := by gcongr
          _ = C * ‖v j x‖ ^ 2 := by ring
      _ = C * ∑ j : ι, ‖v j x‖ ^ 2 := (Finset.mul_sum ..).symm
  have hdiff (x : α) (hx : u x ∈ K) (t : ℝ) (ht : |t| < δ) :
      HasDerivAt (fun s => f s x) (f' t x) t := by
    have hh := HasDerivAt.sum (u := Finset.univ) (fun (j : ι) _ =>
      hasDerivAt_quadraticVariation A (u x) (φ x) (v j x) (w j x) t
        ((hA.contDiffAt (hV.mem_nhds (hbu x hx t ht).1)).differentiableAt (by norm_num)))
    convert hh using 1 <;> try rfl
    funext s
    simp only [f, U, W, Finset.sum_apply]
  have hnear : Metric.ball (0 : ℝ) δ ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds 0 hδ
  have hresult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := f) (F' := f') (bound := fun x => C * ∑ j : ι,
      (P * (‖v j x‖ + ‖w j x‖) ^ 2 + 2 * ‖w j x‖ * (‖v j x‖ + ‖w j x‖))) hnear
    (by
      filter_upwards [hnear] with t ht
      exact hfm t (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht))
    hf0 (hf'm 0 (by simpa using hδ)) ?_
    (integrable_sum_quadratic_bound hv hw C P) ?_
  · simpa only [f, f', U, W, zero_smul, add_zero] using hresult
  · filter_upwards [huK] with x hx t ht
    have ht' : |t| < δ := by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht
    dsimp only [f']
    calc
      ‖∑ j : ι, ((fderiv ℝ A (U t x) (φ x)) (W t j x) (W t j x) +
          A (U t x) (w j x) (W t j x) + A (U t x) (W t j x) (w j x))‖ ≤
        ∑ j : ι, ‖(fderiv ℝ A (U t x) (φ x)) (W t j x) (W t j x) +
          A (U t x) (w j x) (W t j x) + A (U t x) (W t j x) (w j x)‖ := norm_sum_le _ _
      _ ≤ ∑ j : ι, C * (P * (‖v j x‖ + ‖w j x‖) ^ 2 + 2 * ‖w j x‖ * (‖v j x‖ + ‖w j x‖)) := by
        apply Finset.sum_le_sum
        intro j hj
        have hAt := (hA.contDiffAt (hV.mem_nhds (hbu x hx t ht').1)).differentiableAt (by norm_num)
        rw [← (hasDerivAt_quadraticVariation A (u x) (φ x) (v j x) (w j x) t hAt).deriv]
        exact norm_deriv_quadraticVariation_le A (u x) (φ x) (v j x) (w j x) t C P hAt
          (ht'.le.trans hδone) (hφ x) (hbu x hx t ht').2.1 (hbu x hx t ht').2.2
      _ = C * ∑ j : ι,
          (P * (‖v j x‖ + ‖w j x‖) ^ 2 + 2 * ‖w j x‖ * (‖v j x‖ + ‖w j x‖)) :=
        (Finset.mul_sum ..).symm
  · exact huK.mono fun x hx t ht => hdiff x hx t
      (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.hasDerivAt_integral_metric_energy
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.hasDerivAt_integral_metric_energy target :: scope.openDecls } }

end Integral

section SobolevCoordinates

variable {d n : ℕ}

local instance energyFormNormedAdd :
    NormedAddCommGroup ((EuclideanSpace ℝ (Fin n)) →L[ℝ]
      (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.energyFormNormedAdd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.energyFormNormedAdd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.energyFormNormedAdd ``Submission.DifferentialGeometry.Analysis.Sobolev.energyFormNormedAdd
local instance energyFormNormedSpace :
    NormedSpace ℝ ((EuclideanSpace ℝ (Fin n)) →L[ℝ]
      (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.energyFormNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.energyFormNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.energyFormNormedSpace ``Submission.DifferentialGeometry.Analysis.Sobolev.energyFormNormedSpace

variable {Ω : Set (EuclideanSpace ℝ (Fin d))}
  {u : (EuclideanSpace ℝ (Fin d)) → (EuclideanSpace ℝ (Fin n))}

def metricDirichletEnergy
    (A : (EuclideanSpace ℝ (Fin n)) → (EuclideanSpace ℝ (Fin n)) →L[ℝ]
      (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ)
    (hu : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => u x i) Ω) : ℝ :=
  ∫ x in Ω, ∑ j : Fin d,
    A (u x) (DeGiorgi.weakGradientColumn hu x j) (DeGiorgi.weakGradientColumn hu x j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.metricDirichletEnergy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.metricDirichletEnergy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.metricDirichletEnergy ``Submission.DifferentialGeometry.Analysis.Sobolev.metricDirichletEnergy

theorem metricDirichletEnergy_affine_variation_zero
    (hΩ : IsOpen Ω) (hu : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => u x i) Ω)
    (A : (EuclideanSpace ℝ (Fin n)) → (EuclideanSpace ℝ (Fin n)) →L[ℝ]
      (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ)
    {φ : (EuclideanSpace ℝ (Fin d)) → (EuclideanSpace ℝ (Fin n))}
    (hφ : ContDiff ℝ ∞ φ) (hφs : HasCompactSupport φ) :
    metricDirichletEnergy A (DeGiorgi.componentAffineVariationWitness hΩ hu hφ hφs 0) =
      metricDirichletEnergy A hu := by
  unfold metricDirichletEnergy
  simp only [DeGiorgi.weakGradientColumn_componentAffineVariationWitness, zero_smul, add_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.metricDirichletEnergy_affine_variation_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.metricDirichletEnergy_affine_variation_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.metricDirichletEnergy_affine_variation_zero ``Submission.DifferentialGeometry.Analysis.Sobolev.metricDirichletEnergy_affine_variation_zero


theorem hasDerivAt_metricDirichletEnergy_affine_variation
    (hΩ : IsOpen Ω) (hu : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => u x i) Ω)
    {A : (EuclideanSpace ℝ (Fin n)) → (EuclideanSpace ℝ (Fin n)) →L[ℝ]
      (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ} {V K : Set (EuclideanSpace ℝ (Fin n))}
    (hV : IsOpen V) (hA : ContDiffOn ℝ 1 A V) (hK : IsCompact K) (hKV : K ⊆ V)
    (huK : ∀ᵐ x ∂volume.restrict Ω, u x ∈ K)
    (hsym : ∀ y ∈ K, ∀ v w : (EuclideanSpace ℝ (Fin n)), A y v w = A y w v)
    {φ : (EuclideanSpace ℝ (Fin d)) → (EuclideanSpace ℝ (Fin n))}
    (hφ : ContDiff ℝ ∞ φ) (hφs : HasCompactSupport φ) :
    _root_.MeasureTheory.IntegrableOn (fun x => ∑ j : Fin d,
      ((fderiv ℝ A (u x) (φ x)) (DeGiorgi.weakGradientColumn hu x j)
          (DeGiorgi.weakGradientColumn hu x j) +
        2 * A (u x) (DeGiorgi.weakGradientColumn hu x j)
          (fderiv ℝ φ x (EuclideanSpace.single j 1)))) Ω ∧
    HasDerivAt (fun t : ℝ => metricDirichletEnergy A
      (DeGiorgi.componentAffineVariationWitness hΩ hu hφ hφs t))
      (∫ x in Ω, (∑ j : Fin d,
        ((fderiv ℝ A (u x) (φ x)) (DeGiorgi.weakGradientColumn hu x j)
            (DeGiorgi.weakGradientColumn hu x j) +
          2 * A (u x) (DeGiorgi.weakGradientColumn hu x j)
            (fderiv ℝ φ x (EuclideanSpace.single j 1))))) 0 := by
  classical
  have hum : _root_.MeasureTheory.AEStronglyMeasurable u (volume.restrict Ω) :=
    (MemLp.of_eval_piLp fun i => (hu i).memLp).aestronglyMeasurable
  have hφm : _root_.MeasureTheory.AEStronglyMeasurable φ (volume.restrict Ω) := hφ.continuous.aestronglyMeasurable
  have hv (j : Fin d) : _root_.MeasureTheory.MemLp (fun x => DeGiorgi.weakGradientColumn hu x j) 2
      (volume.restrict Ω) := DeGiorgi.weakGrad_column_memLp hu j
  have hw (j : Fin d) : _root_.MeasureTheory.MemLp (fun x => fderiv ℝ φ x (EuclideanSpace.single j 1)) 2
      (volume.restrict Ω) := by
    have hc : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single j 1)) :=
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    exact (hc.memLp_of_hasCompactSupport (μ := _root_.MeasureTheory.MeasureSpace.volume) (p := 2)
      (hφs.fderiv_apply (𝕜 := ℝ) _)).restrict Ω
  obtain ⟨P₀, hP₀⟩ := hφ.continuous.bounded_above_of_compact_support hφs
  let P := _root_.Max.max P₀ 0
  have hP : 0 ≤ P := le_max_right _ _
  have hPφ : ∀ x, ‖φ x‖ ≤ P := fun x => (hP₀ x).trans (le_max_left _ _)
  obtain ⟨hint, hderiv⟩ := hasDerivAt_integral_metric_energy hum hφm hv hw hV hA hK hKV huK P hP hPφ
  have heq : (fun x => ∑ j : Fin d,
        ((fderiv ℝ A (u x) (φ x)) (DeGiorgi.weakGradientColumn hu x j)
            (DeGiorgi.weakGradientColumn hu x j) +
          A (u x) (fderiv ℝ φ x (EuclideanSpace.single j 1)) (DeGiorgi.weakGradientColumn hu x j) +
          A (u x) (DeGiorgi.weakGradientColumn hu x j)
            (fderiv ℝ φ x (EuclideanSpace.single j 1)))) =ᵐ[volume.restrict Ω]
      (fun x => ∑ j : Fin d,
        ((fderiv ℝ A (u x) (φ x)) (DeGiorgi.weakGradientColumn hu x j)
            (DeGiorgi.weakGradientColumn hu x j) +
          2 * A (u x) (DeGiorgi.weakGradientColumn hu x j)
            (fderiv ℝ φ x (EuclideanSpace.single j 1)))) := by
    filter_upwards [huK] with x hx
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsym (u x) hx (fderiv ℝ φ x (EuclideanSpace.single j 1))
      (DeGiorgi.weakGradientColumn hu x j)]
    ring
  refine ⟨hint.congr heq, ?_⟩
  have hfunc : (fun t : ℝ => metricDirichletEnergy A
      (DeGiorgi.componentAffineVariationWitness hΩ hu hφ hφs t)) =
      (fun t : ℝ => ∫ x in Ω, ∑ j : Fin d,
        A (u x + t • φ x)
          (DeGiorgi.weakGradientColumn hu x j + t • fderiv ℝ φ x (EuclideanSpace.single j 1))
          (DeGiorgi.weakGradientColumn hu x j + t • fderiv ℝ φ x (EuclideanSpace.single j 1))) := by
    funext t
    unfold metricDirichletEnergy
    simp only [DeGiorgi.weakGradientColumn_componentAffineVariationWitness]
  rw [hfunc]
  exact hderiv.congr_deriv (_root_.MeasureTheory.integral_congr_ae heq)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.hasDerivAt_metricDirichletEnergy_affine_variation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.hasDerivAt_metricDirichletEnergy_affine_variation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.hasDerivAt_metricDirichletEnergy_affine_variation ``Submission.DifferentialGeometry.Analysis.Sobolev.hasDerivAt_metricDirichletEnergy_affine_variation

theorem integral_metric_energy_variation_eq_zero_of_isLocalMin
    (hΩ : IsOpen Ω) (hu : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => u x i) Ω)
    {A : (EuclideanSpace ℝ (Fin n)) → (EuclideanSpace ℝ (Fin n)) →L[ℝ]
      (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ} {V K : Set (EuclideanSpace ℝ (Fin n))}
    (hV : IsOpen V) (hA : ContDiffOn ℝ 1 A V) (hK : IsCompact K) (hKV : K ⊆ V)
    (huK : ∀ᵐ x ∂volume.restrict Ω, u x ∈ K)
    (hsym : ∀ y ∈ K, ∀ v w : (EuclideanSpace ℝ (Fin n)), A y v w = A y w v)
    {φ : (EuclideanSpace ℝ (Fin d)) → (EuclideanSpace ℝ (Fin n))}
    (hφ : ContDiff ℝ ∞ φ) (hφs : HasCompactSupport φ)
    (hmin : IsLocalMin (fun t : ℝ => metricDirichletEnergy A
      (DeGiorgi.componentAffineVariationWitness hΩ hu hφ hφs t)) 0) :
    (∫ x in Ω, (∑ j : Fin d,
      ((fderiv ℝ A (u x) (φ x)) (DeGiorgi.weakGradientColumn hu x j)
          (DeGiorgi.weakGradientColumn hu x j) +
        2 * A (u x) (DeGiorgi.weakGradientColumn hu x j)
          (fderiv ℝ φ x (EuclideanSpace.single j 1))))) = 0 :=
  hmin.hasDerivAt_eq_zero
    (hasDerivAt_metricDirichletEnergy_affine_variation hΩ hu hV hA hK hKV huK hsym hφ hφs).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.integral_metric_energy_variation_eq_zero_of_isLocalMin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.integral_metric_energy_variation_eq_zero_of_isLocalMin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.integral_metric_energy_variation_eq_zero_of_isLocalMin ``Submission.DifferentialGeometry.Analysis.Sobolev.integral_metric_energy_variation_eq_zero_of_isLocalMin

theorem integral_metric_energy_variation_eq_zero_of_eventually_energy_le
    (hΩ : IsOpen Ω) (hu : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => u x i) Ω)
    {A : (EuclideanSpace ℝ (Fin n)) → (EuclideanSpace ℝ (Fin n)) →L[ℝ]
      (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ} {V K : Set (EuclideanSpace ℝ (Fin n))}
    (hV : IsOpen V) (hA : ContDiffOn ℝ 1 A V) (hK : IsCompact K) (hKV : K ⊆ V)
    (huK : ∀ᵐ x ∂volume.restrict Ω, u x ∈ K)
    (hsym : ∀ y ∈ K, ∀ v w : (EuclideanSpace ℝ (Fin n)), A y v w = A y w v)
    {φ : (EuclideanSpace ℝ (Fin d)) → (EuclideanSpace ℝ (Fin n))}
    (hφ : ContDiff ℝ ∞ φ) (hφs : HasCompactSupport φ)
    (hmin : ∀ᶠ t in 𝓝 (0 : ℝ), metricDirichletEnergy A hu ≤ metricDirichletEnergy A
      (DeGiorgi.componentAffineVariationWitness hΩ hu hφ hφs t)) :
    (∫ x in Ω, (∑ j : Fin d,
      ((fderiv ℝ A (u x) (φ x)) (DeGiorgi.weakGradientColumn hu x j)
          (DeGiorgi.weakGradientColumn hu x j) +
        2 * A (u x) (DeGiorgi.weakGradientColumn hu x j)
          (fderiv ℝ φ x (EuclideanSpace.single j 1))))) = 0 := by
  apply integral_metric_energy_variation_eq_zero_of_isLocalMin hΩ hu hV hA hK hKV huK hsym hφ hφs
  change ∀ᶠ t in 𝓝 (0 : ℝ),
    metricDirichletEnergy A (DeGiorgi.componentAffineVariationWitness hΩ hu hφ hφs 0) ≤
      metricDirichletEnergy A (DeGiorgi.componentAffineVariationWitness hΩ hu hφ hφs t)
  rwa [metricDirichletEnergy_affine_variation_zero hΩ hu A hφ hφs]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.integral_metric_energy_variation_eq_zero_of_eventually_energy_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.integral_metric_energy_variation_eq_zero_of_eventually_energy_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.integral_metric_energy_variation_eq_zero_of_eventually_energy_le ``Submission.DifferentialGeometry.Analysis.Sobolev.integral_metric_energy_variation_eq_zero_of_eventually_energy_le


end SobolevCoordinates

end DifferentialGeometry.Analysis.Sobolev

end

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.ENNReal _root_.ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

variable {d n : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ (Fin n)

theorem integrable_quadratic_weakGradientColumn
    {Ω : Set V} {f : V → F}
    (hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => f x i) Ω)
    (A : V → F →L[ℝ] F →L[ℝ] ℝ)
    (hA : _root_.MeasureTheory.AEStronglyMeasurable A (volume.restrict Ω))
    {C : ℝ} (hC : ∀ᵐ x ∂volume.restrict Ω, ‖A x‖ ≤ C) (j : Fin d) :
    _root_.MeasureTheory.IntegrableOn (fun x => A x (DeGiorgi.weakGradientColumn hf x j)
      (DeGiorgi.weakGradientColumn hf x j)) Ω := by
  have hG : _root_.MeasureTheory.MemLp (fun x => DeGiorgi.weakGradientColumn hf x j) 2 (volume.restrict Ω) :=
    MemLp.of_eval_piLp fun i => (hf i).weakGrad_component_memLp j
  exact integrable_bilinear_of_apply_aestronglyMeasurable A
    (fun v w => (hA.apply_continuousLinearMap v).apply_continuousLinearMap w) hC hG hG

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.integrable_quadratic_weakGradientColumn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.integrable_quadratic_weakGradientColumn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.integrable_quadratic_weakGradientColumn ``Submission.DifferentialGeometry.Analysis.Sobolev.integrable_quadratic_weakGradientColumn

theorem integrable_metric_weakGradientColumn_of_compact_range
    {Ω : Set V} {f : V → F}
    (hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => f x i) Ω)
    {K : Set F} (hK : IsCompact K) (hfK : ∀ᵐ x ∂volume.restrict Ω, f x ∈ K)
    (A : F → F →L[ℝ] F →L[ℝ] ℝ) (hA : ContinuousOn A K) (j : Fin d) :
    _root_.MeasureTheory.IntegrableOn (fun x => A (f x) (DeGiorgi.weakGradientColumn hf x j)
      (DeGiorgi.weakGradientColumn hf x j)) Ω := by
  classical
  have hfm : _root_.MeasureTheory.MemLp f 2 (volume.restrict Ω) := MemLp.of_eval_piLp fun i => (hf i).memLp
  have hAm : Measurable (K.piecewise A 0) :=
    hA.measurable_piecewise continuous_zero.continuousOn hK.measurableSet
  have hm : _root_.MeasureTheory.AEStronglyMeasurable (fun x => A (f x)) (volume.restrict Ω) := by
    apply (hAm.comp_aemeasurable hfm.aemeasurable).aestronglyMeasurable.congr
    filter_upwards [hfK] with x hx
    exact Set.piecewise_eq_of_mem K A 0 hx
  have hn : ContinuousOn (fun y => ‖A y‖) K :=
    (@continuous_norm (F →L[ℝ] F →L[ℝ] ℝ) inferInstance).comp_continuousOn hA
  obtain ⟨C, hC⟩ := hK.bddAbove_image hn
  exact integrable_quadratic_weakGradientColumn hf (fun x => A (f x)) hm
    (hfK.mono fun x hx => hC (_root_.Set.mem_image_of_mem _ hx)) j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.integrable_metric_weakGradientColumn_of_compact_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.integrable_metric_weakGradientColumn_of_compact_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.integrable_metric_weakGradientColumn_of_compact_range ``Submission.DifferentialGeometry.Analysis.Sobolev.integrable_metric_weakGradientColumn_of_compact_range

end DifferentialGeometry.Analysis.Sobolev

end

end

section

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Metric
open scoped _root_.Topology _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.Analysis.Sobolev

variable {d m : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ (Fin m)

theorem integral_metric_energy_variation_eq_zero_of_ball_minimality
    {z : E → F} {R a : ℝ}
    (hz : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => z x i) (_root_.Metric.ball (0 : E) R))
    (hzc : ContinuousOn z (_root_.Metric.ball (0 : E) R)) (hzrange : _root_.Set.MapsTo z (_root_.Metric.ball (0 : E) R) (_root_.Metric.ball 0 a))
    {U : Set F} (hU : IsOpen U) (hKU : _root_.Metric.closedBall (0 : F) a ⊆ U)
    (B : F → F →L[ℝ] F →L[ℝ] ℝ) (hB : ContDiffOn ℝ 1 B U)
    (hsym : ∀ y ∈ _root_.Metric.closedBall (0 : F) a, ∀ v w, B y v w = B y w v)
    (hmin : ∀ s : ℝ, 0 < s → s < R → ∀ q : E → F,
      ∀ hq : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => q x i) (_root_.Metric.ball (0 : E) s),
      (∀ i, DeGiorgi.MemW01p 2 (fun x => q x i - z x i) (_root_.Metric.ball (0 : E) s)) →
      (∀ᵐ x ∂volume.restrict (_root_.Metric.ball (0 : E) s), q x ∈ _root_.Metric.closedBall (0 : F) a) →
      (1 / 2 : ℝ) * (∑ j : Fin d, ∫ x in _root_.Metric.ball (0 : E) s,
        B (z x) (DeGiorgi.weakGradientColumn hz x j) (DeGiorgi.weakGradientColumn hz x j)) ≤
        (1 / 2 : ℝ) * (∑ j : Fin d, ∫ x in _root_.Metric.ball (0 : E) s,
          B (q x) (DeGiorgi.weakGradientColumn hq x j) (DeGiorgi.weakGradientColumn hq x j)))
    {s : ℝ} (hs : 0 < s) (hsR : s < R) {φ : E → F}
    (hφ : ContDiff ℝ ∞ φ) (hφsupp : tsupport φ ⊆ _root_.Metric.ball (0 : E) s) :
    (∫ x in _root_.Metric.ball (0 : E) s, ∑ j : Fin d,
      ((fderiv ℝ B (z x) (φ x))
          (DeGiorgi.weakGradientColumn hz x j) (DeGiorgi.weakGradientColumn hz x j) +
        2 * B (z x) (DeGiorgi.weakGradientColumn hz x j)
          (fderiv ℝ φ x (EuclideanSpace.single j 1)))) = 0 := by
  classical
  have hsub : _root_.Metric.ball (0 : E) s ⊆ _root_.Metric.ball (0 : E) R := _root_.Metric.ball_subset_ball hsR.le
  have hclosed : _root_.Metric.closedBall (0 : E) s ⊆ _root_.Metric.ball (0 : E) R := _root_.Metric.closedBall_subset_ball hsR
  let hzs (i : Fin m) := (hz i).restrict _root_.Metric.isOpen_ball hsub
  have hφcompact : HasCompactSupport φ :=
    (_root_.ProperSpace.isCompact_closedBall (0 : E) s).of_isClosed_subset (isClosed_tsupport φ)
      (hφsupp.trans _root_.Metric.ball_subset_closedBall)
  let Kz := z '' _root_.Metric.closedBall (0 : E) s
  have hKz : IsCompact Kz := (_root_.ProperSpace.isCompact_closedBall (0 : E) s).image_of_continuousOn
    (hzc.mono hclosed)
  have hKzball : Kz ⊆ _root_.Metric.ball (0 : F) a := by
    rintro y ⟨x, hx, rfl⟩
    exact hzrange (hclosed hx)
  obtain ⟨δ, hδ, hδK⟩ := hKz.exists_thickening_subset_open _root_.Metric.isOpen_ball hKzball
  obtain ⟨C₀, hC₀⟩ := hφ.continuous.bounded_above_of_compact_support hφcompact
  let C : ℝ := _root_.Max.max C₀ 0 + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hφbound (x : E) : ‖φ x‖ ≤ C := (hC₀ x).trans (by dsimp only [C]; linarith [le_max_left C₀ 0])
  have hqrange : ∀ᶠ t in 𝓝 (0 : ℝ),
      MapsTo (fun x => z x + t • φ x) (_root_.Metric.ball (0 : E) s) (_root_.Metric.closedBall (0 : F) a) := by
    filter_upwards [_root_.Metric.ball_mem_nhds (0 : ℝ) (div_pos hδ hC)] with t ht x hx
    apply _root_.Metric.ball_subset_closedBall
    apply hδK
    apply mem_thickening_iff.mpr
    refine ⟨z x, _root_.Set.mem_image_of_mem z (_root_.Metric.ball_subset_closedBall hx), ?_⟩
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    have ht' : |t| < δ / C := by simpa only [_root_.Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using ht
    exact (mul_le_mul_of_nonneg_left (hφbound x) (abs_nonneg t)).trans_lt
      ((lt_div_iff₀ hC).mp ht')
  have hzK : ∀ᵐ x ∂volume.restrict (_root_.Metric.ball (0 : E) s), z x ∈ _root_.Metric.closedBall (0 : F) a := by
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_ball] with x hx
    exact _root_.Metric.ball_subset_closedBall (hzrange (hsub hx))
  have hbaseInt (j : Fin d) : _root_.MeasureTheory.IntegrableOn (fun x => B (z x)
      (DeGiorgi.weakGradientColumn hzs x j) (DeGiorgi.weakGradientColumn hzs x j))
        (_root_.Metric.ball (0 : E) s) :=
    Euclidean.integrable_quadratic_weakGrad_column_of_compact_range hzs
      (_root_.ProperSpace.isCompact_closedBall (0 : F) a) hzK B (hB.continuousOn.mono hKU) j
  have hminvar : ∀ᶠ t in 𝓝 (0 : ℝ), metricDirichletEnergy B hzs ≤
      metricDirichletEnergy B (DeGiorgi.componentAffineVariationWitness
        isOpen_ball hzs hφ hφcompact t) := by
    filter_upwards [hqrange] with t htrange
    let ht := DeGiorgi.componentAffineVariationWitness _root_.Metric.isOpen_ball hzs hφ hφcompact t
    have htrace (i : Fin m) : DeGiorgi.MemW01p 2
        (fun x => (z x + t • φ x) i - z x i) (_root_.Metric.ball (0 : E) s) := by
      have hh := (DeGiorgi.memW01p_of_contDiffComponentHasCompactSupport_subset
        (p := 2) _root_.Metric.isOpen_ball hφ hφcompact hφsupp i).smul t
      convert hh using 1
      funext x
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, add_sub_cancel_left]
    have hqK : ∀ᵐ x ∂volume.restrict (_root_.Metric.ball (0 : E) s), z x + t • φ x ∈ _root_.Metric.closedBall (0 : F) a := by
      filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_ball] with x hx
      exact htrange hx
    have hvarInt (j : Fin d) : _root_.MeasureTheory.IntegrableOn (fun x => B (z x + t • φ x)
        (DeGiorgi.weakGradientColumn ht x j) (DeGiorgi.weakGradientColumn ht x j))
          (_root_.Metric.ball (0 : E) s) :=
      Euclidean.integrable_quadratic_weakGrad_column_of_compact_range ht
        (_root_.ProperSpace.isCompact_closedBall (0 : F) a) hqK B (hB.continuousOn.mono hKU) j
    have hle := hmin s hs hsR (fun x => z x + t • φ x) ht htrace hqK
    unfold metricDirichletEnergy
    rw [_root_.MeasureTheory.integral_finsetSum _ (fun j _ => hbaseInt j),
      _root_.MeasureTheory.integral_finsetSum _ (fun j _ => hvarInt j)]
    have hgrad : DeGiorgi.weakGradientColumn hzs = DeGiorgi.weakGradientColumn hz := rfl
    rw [hgrad]
    linarith [hle]
  exact integral_metric_energy_variation_eq_zero_of_eventually_energy_le _root_.Metric.isOpen_ball hzs
    hU hB (_root_.ProperSpace.isCompact_closedBall (0 : F) a) hKU hzK hsym hφ hφcompact hminvar

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.integral_metric_energy_variation_eq_zero_of_ball_minimality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.integral_metric_energy_variation_eq_zero_of_ball_minimality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.integral_metric_energy_variation_eq_zero_of_ball_minimality ``Submission.DifferentialGeometry.Analysis.Sobolev.integral_metric_energy_variation_eq_zero_of_ball_minimality

end DifferentialGeometry.Analysis.Sobolev

end

end
