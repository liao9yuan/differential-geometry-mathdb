import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Invariance
import Submission.DifferentialGeometry.Geometry.Metric.Euclidean
import Submission.DifferentialGeometry.Tensor.Coordinates.ModelBasis
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

set_option autoImplicit false

namespace DifferentialGeometry
namespace Integral
namespace Measure

open _root_.MeasureTheory _root_.Set _root_.Module _root_.Submission.Module
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal _root_.Matrix

section MeasureReduction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry target :: scope.openDecls } }

theorem riemannianMeasure_eq_sum_support
    (g : SmoothRiemannianMetric I M) (ρ : SmoothPartitionOfUnity M I M _root_.Set.univ) :
    riemannianMeasure (I := I) g ρ =
      MeasureTheory.Measure.sum (fun α : {α : M | (Function.support (ρ α)).Nonempty} =>
        (chartLocalMeasure (I := I) g α.val).withDensity
          (fun x => ENNReal.ofReal (ρ α.val x))) := by
  rw [riemannianMeasure_def]
  set s : Set M := {α : M | (Function.support (ρ α)).Nonempty} with hs
  have h := Measure.sum_add_sum_compl s
    (fun α : M => (chartLocalMeasure (I := I) g α).withDensity
      (fun x : M => ENNReal.ofReal (ρ α x)))
  rw [← h]
  have hzero : Measure.sum (fun i : ↥sᶜ =>
      (chartLocalMeasure (I := I) g i.val).withDensity
        (fun x : M => ENNReal.ofReal (ρ i.val x))) = 0 := by
    rw [Measure.sum_eq_zero]
    intro i
    have hρ : ∀ x : M, ρ i.val x = 0 := by
      intro x
      by_contra hne
      exact i.2 (Set.nonempty_iff_ne_empty.mpr (fun hempty => by
        have : x ∈ Function.support (ρ i.val) := hne
        rw [hempty] at this
        exact this.elim))
    have hfun : (fun x : M => ENNReal.ofReal (ρ i.val x)) = 0 := by
      funext x; rw [hρ x, ENNReal.ofReal_zero]; rfl
    rw [hfun, _root_.MeasureTheory.withDensity_zero]
  rw [hzero, add_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.riemannianMeasure_eq_sum_support then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.riemannianMeasure_eq_sum_support"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.riemannianMeasure_eq_sum_support ``Submission.DifferentialGeometry.Integral.Measure.riemannianMeasure_eq_sum_support

end MeasureReduction

section EuclideanVolume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_1 : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

open _root_.Submission.DifferentialGeometry.Tensor.Coordinates

omit [FiniteDimensional ℝ E] in
theorem extChartAt_modelWithCornersSelf (x₀ : E) :
    extChartAt 𝓘(ℝ, E) x₀ = PartialEquiv.refl E := by
  ext x <;> simp [chartAt_self_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.extChartAt_modelWithCornersSelf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.extChartAt_modelWithCornersSelf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.extChartAt_modelWithCornersSelf ``Submission.DifferentialGeometry.Integral.Measure.extChartAt_modelWithCornersSelf

theorem chartBasisVecFiber_modelWithCornersSelf (x₀ x : E) (i : Fin (Module.finrank ℝ E)) :
    chartBasisVecFiber (I := 𝓘(ℝ, E)) x₀ i x = chartModelBasis E i := by
  rw [chartBasisVecFiber, TangentBundle.symmL_model_space]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.chartBasisVecFiber_modelWithCornersSelf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.chartBasisVecFiber_modelWithCornersSelf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.chartBasisVecFiber_modelWithCornersSelf ``Submission.DifferentialGeometry.Integral.Measure.chartBasisVecFiber_modelWithCornersSelf

theorem chartDensity_euclideanMetric (x₀ x : E) :
    chartDensity (I := 𝓘(ℝ, E)) (euclideanMetric (E := E)) x₀ x =
      Real.sqrt (Matrix.det (Matrix.of fun i j => _root_.Inner.inner ℝ (chartModelBasis E i)
        (chartModelBasis E j))) := by
  have hgram : chartGramMatrix (I := 𝓘(ℝ, E)) (euclideanMetric (E := E)) x₀ x =
      Matrix.of (fun i j => _root_.Inner.inner ℝ (chartModelBasis E i) (chartModelBasis E j)) := by
    ext i j
    rw [chartGramMatrix_apply, euclideanMetric_inner,
      chartBasisVecFiber_modelWithCornersSelf x₀ x i,
      chartBasisVecFiber_modelWithCornersSelf x₀ x j]
    rfl
  rw [chartDensity, hgram]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.chartDensity_euclideanMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.chartDensity_euclideanMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.chartDensity_euclideanMetric ``Submission.DifferentialGeometry.Integral.Measure.chartDensity_euclideanMetric

theorem addHaar_withDensity_sqrt_det_gramMatrix_eq_volume
    (b : _root_.Module.Basis (Fin (Module.finrank ℝ E)) ℝ E) :
    b.addHaar.withDensity (fun _ => ENNReal.ofReal (Real.sqrt
      (Matrix.det (Matrix.of fun i j => _root_.Inner.inner ℝ (b i) (b j))))) =
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := by
  classical
  have hu : (stdOrthonormalBasis ℝ E).toBasis.addHaar = (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) :=
    (stdOrthonormalBasis ℝ E).addHaar_eq_volume
  have hterm : ∀ (k i : Fin (Module.finrank ℝ E)),
      ((stdOrthonormalBasis ℝ E).toBasis.repr (b i)) k =
        inner ℝ (b i) ((stdOrthonormalBasis ℝ E) k) := by
    intro k i
    rw [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
      real_inner_comm]
  have hgram : (Matrix.of fun i j => _root_.Inner.inner ℝ (b i) (b j)) =
      ((stdOrthonormalBasis ℝ E).toBasis.toMatrix b)ᵀ *
        ((stdOrthonormalBasis ℝ E).toBasis.toMatrix b) := by
    ext i j
    rw [Matrix.of_apply, Matrix.mul_apply]
    simp only [Matrix.transpose_apply, Basis.toMatrix_apply, hterm]
    rw [← OrthonormalBasis.sum_inner_mul_inner (stdOrthonormalBasis ℝ E) (b i) (b j)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [real_inner_comm (b j) ((stdOrthonormalBasis ℝ E) k)]
  have hdet : Matrix.det (Matrix.of fun i j => _root_.Inner.inner ℝ (b i) (b j)) =
      ((stdOrthonormalBasis ℝ E).toBasis.det b) ^ 2 := by
    rw [hgram, Matrix.det_mul, Matrix.det_transpose, sq]
    rw [Basis.det_apply]
  have hc : ENNReal.ofReal (Real.sqrt
      (Matrix.det (Matrix.of fun i j => _root_.Inner.inner ℝ (b i) (b j)))) =
      ENNReal.ofReal |((stdOrthonormalBasis ℝ E).toBasis.det b)| := by
    rw [hdet, Real.sqrt_sq_eq_abs]
  have hvol : (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) (b.parallelepiped : Set E) =
      ENNReal.ofReal |((stdOrthonormalBasis ℝ E).toBasis.det b)| := by
    rw [← hu]
    exact Measure.addHaar_parallelepiped (stdOrthonormalBasis ℝ E).toBasis b
  have huniq : (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) =
      ENNReal.ofReal |((stdOrthonormalBasis ℝ E).toBasis.det b)| • b.addHaar := by
    rw [Basis.addHaar_def, Measure.addHaarMeasure_unique (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) b.parallelepiped,
      hvol]
  rw [_root_.MeasureTheory.withDensity_const, hc, huniq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.addHaar_withDensity_sqrt_det_gramMatrix_eq_volume then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.addHaar_withDensity_sqrt_det_gramMatrix_eq_volume"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.addHaar_withDensity_sqrt_det_gramMatrix_eq_volume ``Submission.DifferentialGeometry.Integral.Measure.addHaar_withDensity_sqrt_det_gramMatrix_eq_volume

theorem chartLocalMeasure_euclideanMetric (x₀ : E) :
    chartLocalMeasure (I := 𝓘(ℝ, E)) (M := E) (euclideanMetric (E := E)) x₀ =
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := by
  rw [chartLocalMeasure_def, extChartAt_modelWithCornersSelf x₀]
  simp only [PartialEquiv.refl_symm, PartialEquiv.refl_target, PartialEquiv.refl_coe,
    Measure.restrict_univ, Measure.map_id, id_eq]
  have hdens : (fun y : E => ENNReal.ofReal
      (chartDensity (I := 𝓘(ℝ, E)) (euclideanMetric (E := E)) x₀ y)) =
      (fun _ : E => ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun i j =>
        inner ℝ (chartModelBasis E i) (chartModelBasis E j))))) := by
    funext y
    rw [chartDensity_euclideanMetric]
  rw [hdens, modelHaar]
  exact addHaar_withDensity_sqrt_det_gramMatrix_eq_volume (chartModelBasis E)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.chartLocalMeasure_euclideanMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.chartLocalMeasure_euclideanMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.chartLocalMeasure_euclideanMetric ``Submission.DifferentialGeometry.Integral.Measure.chartLocalMeasure_euclideanMetric

end EuclideanVolume

section ModelSpaceVolume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_2 : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_2 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_2 : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_2 target :: scope.openDecls } }

theorem riemannianVolumeMeasure_euclideanMetric
    [T2Space E] [SigmaCompactSpace E] :
    riemannianVolumeMeasure (I := 𝓘(ℝ, E)) (M := E) (euclideanMetric (E := E)) =
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := by
  classical
  set ρ : SmoothPartitionOfUnity E 𝓘(ℝ, E) E univ := chartAtlasPOU 𝓘(ℝ, E) E with hρ
  set T : Set E := {α : E | (Function.support (ρ α)).Nonempty} with hT
  have hC : Countable T :=
    (countable_nonempty_support_of_pou (I := 𝓘(ℝ, E)) ρ).to_subtype
  rw [riemannianVolumeMeasure_def, riemannianMeasure_eq_sum_support (I := 𝓘(ℝ, E)) _ ρ]
  have hp : (fun α : T => (chartLocalMeasure (I := 𝓘(ℝ, E)) (M := E)
        (euclideanMetric (E := E)) α.val).withDensity
        (fun x => ENNReal.ofReal (ρ α.val x))) =
      (fun α : T => (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).withDensity
        (fun x => ENNReal.ofReal (ρ α.val x))) :=
    funext fun α => by rw [chartLocalMeasure_euclideanMetric]
  rw [hp, ← @_root_.MeasureTheory.withDensity_tsum E _ (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) T hC
    (fun α : T => fun x : E => ENNReal.ofReal (ρ α.val x))
    (fun α => measurable_ofReal_pou_weight (I := 𝓘(ℝ, E)) ρ α.val)]
  have hsum : (∑' α : T, (fun x : E => ENNReal.ofReal (ρ α.val x))) = 1 := by
    funext x
    rw [tsum_apply (Pi.summable.2 fun _ => ENNReal.summable)]
    have hsupp : Function.support (fun α : E => ENNReal.ofReal (ρ α x)) ⊆ T := by
      intro α hα
      simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le] at hα
      refine Set.nonempty_iff_ne_empty.mpr ?_
      intro hempty
      have hzero : ρ α x = 0 := by
        by_contra hne
        have : x ∈ Function.support (ρ α) := hne
        rw [hempty] at this
        exact this.elim
      linarith
    rw [← tsum_subtype_eq_of_support_subset hsupp]
    exact tsum_ofReal_pou_eq_one (I := 𝓘(ℝ, E)) ρ x
  rw [hsum, _root_.MeasureTheory.withDensity_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_euclideanMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_euclideanMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_euclideanMetric ``Submission.DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_euclideanMetric

end ModelSpaceVolume

end Measure
end Integral
end DifferentialGeometry
