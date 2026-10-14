import Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernel.PositiveDefinite.GaussianTail
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Chart.Density
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.DualMetric

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Bundle _root_.Submission.Bundle _root_.MeasureTheory
open scoped _root_.ContDiff _root_.ENNReal _root_.Manifold

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean
open _root_.Submission.DifferentialGeometry.Integral.Measure

universe u uH

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.instBorelSpace_differentialGeometry target :: scope.openDecls } }

private theorem metricGram_eq_gramMatrixAt {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] (g : SmoothRiemannianMetric I X) (x : X) :
    (Matrix.of fun i k : Fin (Module.finrank ℝ E) =>
        g.inner x (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i)
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k)) =
      DifferentialGeometry.Integral.L2.gramMatrixAt (I := I) (M := X) g x := by
  ext i j
  simp only [Matrix.of_apply, DifferentialGeometry.Integral.L2.gramMatrixAt_apply,
    DifferentialGeometry.Integral.L2.modelInnerAt_apply]
  with_unfolding_all
    simp only [tangentSpaceModelContinuousLinearEquiv_symm_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.metricGram_eq_gramMatrixAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.metricGram_eq_gramMatrixAt target :: scope.openDecls } }

private theorem metricGram_quadraticForm {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] (g : SmoothRiemannianMetric I X) (x : X) (Z : E) :
    _root_.Inner.inner ℝ (toEuclidean Z)
        (Matrix.toEuclideanCLM (n := Fin (Module.finrank ℝ E)) (𝕜 := ℝ)
          (Matrix.of fun i k : Fin (Module.finrank ℝ E) =>
            g.inner x (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i)
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k))
          (toEuclidean Z)) =
      g.inner x Z Z := by
  classical
  let b := DifferentialGeometry.Tensor.Coordinates.chartModelBasis E
  let v := toEuclidean Z
  have hw : Z = ∑ i, v i • b i := by
    have hvsum : v = ∑ i, v i • EuclideanSpace.single i (1 : ℝ) := by
      let e := (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis
      simpa [e, EuclideanSpace.basisFun_apply] using (e.sum_repr v).symm
    calc
      Z = (toEuclidean (E := E)).symm v := ((toEuclidean (E := E)).symm_apply_apply Z).symm
      _ = (toEuclidean (E := E)).symm (∑ i, v i • EuclideanSpace.single i (1 : ℝ)) :=
        congrArg _ hvsum
      _ = ∑ i, v i • b i := by
        rw [map_sum]
        simp only [b, map_smul, DifferentialGeometry.Tensor.Coordinates.chartModelBasis_apply]
  let B : E →L[ℝ] E →L[ℝ] ℝ := g.inner x
  change _root_.Inner.inner ℝ v (Matrix.toEuclideanCLM (n := Fin (Module.finrank ℝ E)) (𝕜 := ℝ)
      (Matrix.of fun i k => B (b i) (b k)) v) = B Z Z
  rw [Matrix.inner_toEuclideanCLM, hw]
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply,
    smul_eq_mul, dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.metricGram_quadraticForm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.metricGram_quadraticForm target :: scope.openDecls } }

theorem exists_uniform_tail_gaussian_metric_of_finrank_eq {n : ℕ}
    (hn : Module.finrank ℝ E = n) (eps : ℝ≥0∞) (heps : 0 < eps) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
      {X : Type u} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
      (g : SmoothRiemannianMetric I X) (x : X),
      ∫⁻ Z : E in {Z | R < Real.sqrt (g.inner x Z Z)},
        ENNReal.ofReal ((Real.pi ^ ((n : ℝ) / 2))⁻¹ *
          Real.sqrt (Matrix.of fun i k : Fin (Module.finrank ℝ E) =>
            g.inner x (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i)
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k)).det *
          Real.exp (-g.inner x Z Z)) ∂(modelHaar (E := E)) ≤ eps := by
  classical
  subst hn
  by_cases hdim : Module.finrank ℝ E = 0
  · have : Subsingleton E := Module.finrank_zero_iff.mp hdim
    refine ⟨0, le_rfl, fun g x => ?_⟩
    have hempty : {Z : E | 0 < Real.sqrt (g.inner x Z Z)} = ∅ := by
      ext Z
      rw [Subsingleton.elim Z 0]
      change 0 < Real.sqrt ((g.inner x : E →L[ℝ] E →L[ℝ] ℝ) 0 0) ↔ False
      simp
    simpa only [hempty, Measure.restrict_empty, _root_.MeasureTheory.lintegral_zero_measure] using heps.le
  have : Nonempty (Fin (Module.finrank ℝ E)) := ⟨⟨0, Nat.pos_of_ne_zero hdim⟩⟩
  obtain ⟨R, hR, htail⟩ := gaussianPosDef_uniform_tail
    (n := Fin (Module.finrank ℝ E)) eps heps
  refine ⟨R, hR, fun {H} _ {I} {X} _ _ _ g x => ?_⟩
  let A : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    Matrix.of fun i k => g.inner x (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i)
      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k)
  have hA : A.PosDef := by
    rw [show A = _ from metricGram_eq_gramMatrixAt g x]
    exact DifferentialGeometry.Integral.L2.gramMatrixAt_posDef (I := I) (M := X) g x
  let e := toEuclidean (E := E)
  let sE : Set E := {Z | R < Real.sqrt (g.inner x Z Z)}
  let sU : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    {y | R < Real.sqrt (_root_.Inner.inner ℝ y
      (Matrix.toEuclideanCLM (n := Fin (Module.finrank ℝ E)) (𝕜 := ℝ) A y))}
  let dens : E → ℝ≥0∞ := fun Z => ENNReal.ofReal ((Real.pi ^
    ((Module.finrank ℝ E : ℝ) / 2))⁻¹ * Real.sqrt A.det * Real.exp (-g.inner x Z Z))
  let G : E → ℝ≥0∞ := sE.indicator dens
  have hsE : MeasurableSet sE := by
    change MeasurableSet {Z : E | R < Real.sqrt ((g.inner x : E →L[ℝ] E →L[ℝ] ℝ) Z Z)}
    exact measurableSet_lt measurable_const (by fun_prop)
  have hsU : MeasurableSet sU :=
    measurableSet_lt measurable_const (by fun_prop)
  have hquad : ∀ y, g.inner x (e.symm y) (e.symm y) =
      inner ℝ y (Matrix.toEuclideanCLM (n := Fin (Module.finrank ℝ E)) (𝕜 := ℝ) A y) := by
    intro y
    have h := metricGram_quadraticForm g x (e.symm y)
    simp only [e, ContinuousLinearEquiv.apply_symm_apply] at h
    exact h.symm
  have hpoint : ∀ y, G (e.symm y) =
      sU.indicator (fun z => ENNReal.ofReal
        ((Real.pi ^ ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) / 2))⁻¹ *
          Real.sqrt A.det * Real.exp (-_root_.Inner.inner ℝ z
            (Matrix.toEuclideanCLM (n := Fin (Module.finrank ℝ E)) (𝕜 := ℝ) A z)))) y := by
    intro y
    have hmem : e.symm y ∈ sE ↔ y ∈ sU := by
      change R < Real.sqrt (g.inner x (e.symm y) (e.symm y)) ↔ _
      rw [hquad]
      rfl
    by_cases hy : y ∈ sU
    · simp only [G, Set.indicator_of_mem (hmem.2 hy), Set.indicator_of_mem hy, dens, hquad,
        Fintype.card_fin]
    · simp only [G, Set.indicator_of_notMem (fun h => hy (hmem.1 h)),
        Set.indicator_of_notMem hy]
  calc
    ∫⁻ Z : E in sE, dens Z ∂(modelHaar (E := E)) = ∫⁻ Z : E, G Z ∂(modelHaar (E := E)) := by
      rw [← _root_.MeasureTheory.lintegral_indicator hsE]
    _ = ∫⁻ y, G (e.symm y) ∂(Measure.map e (modelHaar (E := E))) := by
      symm
      refine (e.toHomeomorph.measurableEmbedding.lintegral_map _).trans ?_
      refine _root_.MeasureTheory.lintegral_congr fun Z => ?_
      change G (e.symm (e Z)) = G Z
      rw [ContinuousLinearEquiv.symm_apply_apply]
    _ = ∫⁻ y, G (e.symm y)
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) := by
      rw [map_toEuclidean_modelHaar_eq_volume (E := E)]
    _ = ∫⁻ y in sU, ENNReal.ofReal
          ((Real.pi ^ ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) / 2))⁻¹ *
            Real.sqrt A.det * Real.exp (-_root_.Inner.inner ℝ y
              (Matrix.toEuclideanCLM (n := Fin (Module.finrank ℝ E)) (𝕜 := ℝ) A y))) ∂volume := by
      rw [← _root_.MeasureTheory.lintegral_indicator hsU]
      exact _root_.MeasureTheory.lintegral_congr hpoint
    _ ≤ eps := htail A hA

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_uniform_tail_gaussian_metric_of_finrank_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.exists_uniform_tail_gaussian_metric_of_finrank_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_uniform_tail_gaussian_metric_of_finrank_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.exists_uniform_tail_gaussian_metric_of_finrank_eq

theorem exists_uniform_tail_gaussian_metric (eps : ℝ≥0∞) (heps : 0 < eps) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ {X : Type u} [TopologicalSpace X]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
      [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ X]
      (g : SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) X) (x : X),
      ∫⁻ Z : EuclideanSpace ℝ (Fin 3) in {Z | R < Real.sqrt (g.inner x Z Z)},
        ENNReal.ofReal ((Real.pi ^ ((3 : ℝ) / 2))⁻¹ *
          Real.sqrt (Matrix.of fun i k :
              Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) =>
            g.inner x
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis
                (EuclideanSpace ℝ (Fin 3)) i)
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis
                (EuclideanSpace ℝ (Fin 3)) k)).det *
          Real.exp (-g.inner x Z Z)) ∂(modelHaar (E := EuclideanSpace ℝ (Fin 3))) ≤ eps := by
  obtain ⟨R, hR, htail⟩ := exists_uniform_tail_gaussian_metric_of_finrank_eq.{u, 0}
    (E := EuclideanSpace ℝ (Fin 3)) (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3)) eps heps
  exact ⟨R, hR, fun g x => by exact_mod_cast htail g x⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_uniform_tail_gaussian_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.exists_uniform_tail_gaussian_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_uniform_tail_gaussian_metric ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.exists_uniform_tail_gaussian_metric

end DifferentialGeometry.PDE.RicciFlow.Perelman
