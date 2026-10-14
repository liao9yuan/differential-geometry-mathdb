import Submission.DifferentialGeometry.Topology.MetricSpace.DistanceContinuity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Metric
open scoped _root_.Topology

namespace DifferentialGeometry.Topology

variable {A X ι : Type*} [PseudoMetricSpace A] [MeasurableSpace A]
  {μ : Measure A} [Measure.IsOpenPosMeasure μ]
  [MetricSpace X] [CompleteSpace X] [Countable ι]

theorem exists_uniformContinuous_ae_eq_of_truncated_distance_modulus
    {a : ι → X} (ha : DenseRange a) (f : A → X) (w : ι → A → ℝ)
    (hw : ∀ i, w i =ᵐ[μ] (fun x => _root_.Min.min (_root_.Dist.dist (f x) (a i)) 1))
    {ω : ℝ → ℝ} (hω : _root_.Filter.Tendsto ω (𝓝 (0 : ℝ)) (𝓝 0))
    (hmod : ∀ i x y, |w i x - w i y| ≤ ω (_root_.Dist.dist x y)) :
    ∃ F : A → X, UniformContinuous F ∧ F =ᵐ[μ] f := by
  let S : Set A := {x | ∀ i, w i x = _root_.Min.min (_root_.Dist.dist (f x) (a i)) 1}
  have hSae : ∀ᵐ x ∂μ, x ∈ S := ae_all_iff.mpr hw
  have hSdense : Dense S := Measure.dense_of_ae hSae
  let fS : S → X := fun x => f x
  have hfS : UniformContinuous fS :=
    uniformContinuous_of_dense_truncated_distance_modulus ha hω (fun i x y => by
      change |_root_.Min.min (_root_.Dist.dist (f x) (a i)) 1 - _root_.Min.min (_root_.Dist.dist (f y) (a i)) 1| ≤ ω (_root_.Dist.dist x y)
      rw [← x.property i, ← y.property i]
      exact hmod i x y)
  refine ⟨hSdense.extend fS, hSdense.uniformContinuous_extend hfS, ?_⟩
  filter_upwards [hSae] with x hx
  exact hSdense.extend_of_ind hfS ⟨x, hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_uniformContinuous_ae_eq_of_truncated_distance_modulus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_uniformContinuous_ae_eq_of_truncated_distance_modulus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_uniformContinuous_ae_eq_of_truncated_distance_modulus ``Submission.DifferentialGeometry.Topology.exists_uniformContinuous_ae_eq_of_truncated_distance_modulus

end DifferentialGeometry.Topology

end

end

section

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Metric
open scoped _root_.Topology

namespace DifferentialGeometry.Topology

variable {A X ι : Type*} [PseudoMetricSpace A] [MeasurableSpace A] [BorelSpace A]
  {μ : Measure A} [Measure.IsOpenPosMeasure μ]
  [MetricSpace X] [CompleteSpace X] [Countable ι]

theorem exists_continuousOn_ae_eq_of_truncated_distance_modulus_on_open
    {Ω : Set A} (hΩ : IsOpen Ω) {a : ι → X} (ha : DenseRange a)
    (f : A → X) (w : ι → A → ℝ)
    (hw : ∀ i, w i =ᵐ[μ.restrict Ω] (fun x => _root_.Min.min (_root_.Dist.dist (f x) (a i)) 1))
    {ω : ℝ → ℝ} (hω : _root_.Filter.Tendsto ω (𝓝 (0 : ℝ)) (𝓝 0))
    (hmod : ∀ i, ∀ x ∈ Ω, ∀ y ∈ Ω, |w i x - w i y| ≤ ω (_root_.Dist.dist x y)) :
    ∃ F : A → X, ContinuousOn F Ω ∧ F =ᵐ[μ.restrict Ω] f := by
  classical
  let ν : _root_.MeasureTheory.Measure Ω := μ.comap Subtype.val
  let : Measure.IsOpenPosMeasure ν := Measure.IsOpenPosMeasure.comap μ hΩ.isOpenEmbedding_subtypeVal
  have hwae (i : ι) : (fun x : Ω => w i x) =ᵐ[ν]
      (fun x : Ω => _root_.Min.min (_root_.Dist.dist (f x) (a i)) 1) :=
    (ae_restrict_iff_subtype hΩ.measurableSet).mp (hw i)
  obtain ⟨F, hF, hFeq⟩ := exists_uniformContinuous_ae_eq_of_truncated_distance_modulus
    (μ := ν) ha (fun x : Ω => f x) (fun i x => w i x) hwae hω
    (fun i x y => hmod i x x.property y y.property)
  let G : A → X := fun x => if h : x ∈ Ω then F ⟨x, h⟩ else f x
  have hG : ContinuousOn G Ω := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have heq : (fun x : Ω => G x) = F := by
      funext x
      simp only [G, dif_pos x.property]
    exact hF.continuous.congr (fun x => (congrFun heq x).symm)
  refine ⟨G, hG, ?_⟩
  apply (ae_restrict_iff_subtype hΩ.measurableSet).mpr
  filter_upwards [hFeq] with x hx
  simpa only [G, dif_pos x.property] using hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_continuousOn_ae_eq_of_truncated_distance_modulus_on_open then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_continuousOn_ae_eq_of_truncated_distance_modulus_on_open"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_continuousOn_ae_eq_of_truncated_distance_modulus_on_open ``Submission.DifferentialGeometry.Topology.exists_continuousOn_ae_eq_of_truncated_distance_modulus_on_open

end DifferentialGeometry.Topology

end

end
