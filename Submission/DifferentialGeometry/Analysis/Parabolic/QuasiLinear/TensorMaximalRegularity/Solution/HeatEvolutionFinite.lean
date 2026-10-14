import Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.HeatEvolution
import Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.FiniteProduct

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal
namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
variable {ι : Type*} [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {a T : ℝ}

def heatDuhamelEvolutionFieldPi (hT : 0 < T)
    (u₀ : ι → TensorHs g r s (a + 1))
    (F : PiLp 2 (fun _ : ι => timeL2 (TensorHs g r s a) T)) :
    PiLp 2 (fun _ : ι => timeL2 (TensorHs g r s (a + 2)) T) :=
  WithLp.toLp 2 (fun i => heatDuhamelEvolutionField a hT (u₀ i) (F i))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelEvolutionFieldPi then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelEvolutionFieldPi"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelEvolutionFieldPi ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelEvolutionFieldPi

def heatDuhamelEvolutionPi (hT : 0 < T)
    (u₀ : ι → TensorHs g r s (a + 1))
    (F : PiLp 2 (fun _ : ι => timeL2 (TensorHs g r s a) T)) :
    PiLp 2 (fun _ : ι => timeH1 (TensorHs g r s a) T) :=
  WithLp.toLp 2 (fun i => heatDuhamelEvolution a hT (u₀ i) (F i))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelEvolutionPi then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelEvolutionPi"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelEvolutionPi ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelEvolutionPi

omit [Fintype ι] in
theorem heatDuhamelEvolutionPi_trace0 (hT : 0 < T)
    (u₀ : ι → TensorHs g r s (a + 1))
    (F : PiLp 2 (fun _ : ι => timeL2 (TensorHs g r s a) T)) (i : ι) :
    timeH1.trace0 _ T (heatDuhamelEvolutionPi hT u₀ F i) =
      tensorHsInclusion (g := g) (r := r) (s := s) (show a ≤ a + 1 by linarith) (u₀ i) := by
  change timeH1.trace0 _ T (heatDuhamelEvolution a hT (u₀ i) (F i)) = _
  exact heatDuhamelEvolution_trace0 hT (u₀ i) (F i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelEvolutionPi_trace0 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelEvolutionPi_trace0"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelEvolutionPi_trace0 ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelEvolutionPi_trace0

omit [Fintype ι] in
theorem heatDuhamelEvolutionPi_timeDeriv (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : ι → TensorHs g r s (a + 1))
    (F : PiLp 2 (fun _ : ι => timeL2 (TensorHs g r s a) T)) (i : ι) :
    timeH1.timeDeriv _ T (heatDuhamelEvolutionPi hT u₀ F i) =
      timeScaleLaplacian a (heatDuhamelEvolutionFieldPi hT u₀ F i) + F i := by
  change timeH1.timeDeriv _ T (heatDuhamelEvolution a hT (u₀ i) (F i)) =
    timeScaleLaplacian a (heatDuhamelEvolutionField a hT (u₀ i) (F i)) + F i
  exact heatDuhamelEvolution_timeDeriv hT hc (u₀ i) (F i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelEvolutionPi_timeDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelEvolutionPi_timeDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelEvolutionPi_timeDeriv ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelEvolutionPi_timeDeriv

omit [Fintype ι] in
theorem heatDuhamelEvolutionFieldPi_toTimeL2 (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : ι → TensorHs g r s (a + 1))
    (F : PiLp 2 (fun _ : ι => timeL2 (TensorHs g r s a) T)) :
    ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      timeL2Inclusion (g := g) (r := r) (s := s) (show a ≤ a + 2 by linarith))
      (heatDuhamelEvolutionFieldPi hT u₀ F) =
      WithLp.toLp 2 (fun i => timeH1.toTimeL2 _ T (heatDuhamelEvolution a hT (u₀ i) (F i))) := by
  apply PiLp.ext
  intro i
  change timeL2Inclusion (g := g) (r := r) (s := s) (show a ≤ a + 2 by linarith)
      (heatDuhamelEvolutionField a hT (u₀ i) (F i)) = _
  exact heatDuhamelEvolutionField_toTimeL2 hT hc (u₀ i) (F i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelEvolutionFieldPi_toTimeL2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelEvolutionFieldPi_toTimeL2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelEvolutionFieldPi_toTimeL2 ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelEvolutionFieldPi_toTimeL2

omit [Fintype ι] in
theorem heatDuhamelEvolutionFieldPi_inclusion (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : ι → TensorHs g r s (a + 2))
    (F : PiLp 2 (fun _ : ι => timeL2 (TensorHs g r s a) T)) :
    heatDuhamelEvolutionFieldPi hT
      (fun i => tensorHsInclusion (g := g) (r := r) (s := s)
        (show a + 1 ≤ a + 2 by linarith) (u₀ i)) F =
      maximalRegularityDuhamelSolutionFieldPi hT u₀ F := by
  apply PiLp.ext
  intro i
  change heatDuhamelEvolutionField a hT
      (tensorHsInclusion (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith) (u₀ i)) (F i) =
      maximalRegularityDuhamelSolutionField a hT (u₀ i) (F i)
  exact heatDuhamelEvolutionField_inclusion hT hc (u₀ i) (F i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelEvolutionFieldPi_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelEvolutionFieldPi_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelEvolutionFieldPi_inclusion ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelEvolutionFieldPi_inclusion

omit [Fintype ι] in
theorem heatDuhamelEvolutionPi_inclusion (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : ι → TensorHs g r s (a + 2))
    (F : PiLp 2 (fun _ : ι => timeL2 (TensorHs g r s a) T)) :
    heatDuhamelEvolutionPi hT
      (fun i => tensorHsInclusion (g := g) (r := r) (s := s)
        (show a + 1 ≤ a + 2 by linarith) (u₀ i)) F =
      maximalRegularityDuhamelMapPi hT u₀ F := by
  apply PiLp.ext
  intro i
  change heatDuhamelEvolution a hT
      (tensorHsInclusion (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith) (u₀ i)) (F i) =
      maximalRegularityDuhamelMap a hT (u₀ i) (F i)
  exact heatDuhamelEvolution_inclusion hT hc (u₀ i) (F i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelEvolutionPi_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelEvolutionPi_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelEvolutionPi_inclusion ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelEvolutionPi_inclusion

def heatDuhamelVectorField (hT : 0 < T)
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g r s (a + 1)))
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g r s a)) T) :
    timeL2 (PiLp 2 (fun _ : ι => TensorHs g r s (a + 2))) T :=
  (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T)).symm
    (heatDuhamelEvolutionFieldPi hT u₀ (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) F))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelVectorField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelVectorField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelVectorField ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelVectorField

def heatDuhamelVectorEvolution (hT : 0 < T)
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g r s (a + 1)))
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g r s a)) T) :
    timeH1 (PiLp 2 (fun _ : ι => TensorHs g r s a)) T :=
  timeH1.piLpEquiv.symm
    (heatDuhamelEvolutionPi hT u₀ (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) F))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelVectorEvolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelVectorEvolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelVectorEvolution ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelVectorEvolution

theorem heatDuhamelVectorEvolution_trace0 (hT : 0 < T)
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g r s (a + 1)))
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g r s a)) T) :
    timeH1.trace0 _ T (heatDuhamelVectorEvolution hT u₀ F) =
      ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g) (r := r) (s := s) (show a ≤ a + 1 by linarith)) u₀ := by
  apply PiLp.ext
  intro i
  exact heatDuhamelEvolutionPi_trace0 hT u₀ (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) F) i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelVectorEvolution_trace0 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelVectorEvolution_trace0"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelVectorEvolution_trace0 ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelVectorEvolution_trace0

theorem heatDuhamelVectorEvolution_timeDeriv (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g r s (a + 1)))
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g r s a)) T) :
    timeH1.timeDeriv _ T (heatDuhamelVectorEvolution hT u₀ F) =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorScaleLaplacian (g := g) (r := r) (s := s) a)).compLpL
          2 (timeMeasure T) (heatDuhamelVectorField hT u₀ F) + F := by
  apply (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T)).injective
  rw [map_add, Lp.piLpEquiv_compLpL (𝕜 := ℝ)]
  change Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T)
    ((Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T)).symm
      (WithLp.toLp 2 (fun i =>
        (heatDuhamelEvolutionPi hT u₀ (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) F) i).deriv))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  unfold heatDuhamelVectorField
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply PiLp.ext
  intro i
  exact heatDuhamelEvolutionPi_timeDeriv hT hc u₀
    (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) F) i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelVectorEvolution_timeDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelVectorEvolution_timeDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelVectorEvolution_timeDeriv ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelVectorEvolution_timeDeriv

theorem heatDuhamelVectorField_toFunL2 (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g r s (a + 1)))
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g r s a)) T) :
    (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := r) (s := s)
        (show a ≤ a + 2 by linarith))).compLpL 2 (timeMeasure T)
          (heatDuhamelVectorField hT u₀ F) = (heatDuhamelVectorEvolution hT u₀ F).toFunL2 := by
  apply (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T)).injective
  rw [Lp.piLpEquiv_compLpL (𝕜 := ℝ)]
  simp only [heatDuhamelVectorField, heatDuhamelVectorEvolution,
    timeH1.piLpEquiv_symm_toFunL2, LinearIsometryEquiv.apply_symm_apply]
  apply PiLp.ext
  intro i
  exact heatDuhamelEvolutionField_toTimeL2 hT hc (u₀ i)
    (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T) F i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelVectorField_toFunL2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelVectorField_toFunL2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelVectorField_toFunL2 ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelVectorField_toFunL2

theorem heatDuhamelVectorField_inclusion (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g r s (a + 2)))
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g r s a)) T) :
    heatDuhamelVectorField hT
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith)) u₀) F =
      maximalRegularityDuhamelVectorField hT u₀ F := by
  unfold heatDuhamelVectorField maximalRegularityDuhamelVectorField
  exact congrArg (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T)).symm
    (heatDuhamelEvolutionFieldPi_inclusion hT hc u₀ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelVectorField_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelVectorField_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelVectorField_inclusion ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelVectorField_inclusion

theorem heatDuhamelVectorEvolution_inclusion (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g r s (a + 2)))
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g r s a)) T) :
    heatDuhamelVectorEvolution hT
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith)) u₀) F =
      maximalRegularityDuhamelVectorMap hT u₀ F := by
  unfold heatDuhamelVectorEvolution maximalRegularityDuhamelVectorMap
  exact congrArg timeH1.piLpEquiv.symm
    (heatDuhamelEvolutionPi_inclusion hT hc u₀ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelVectorEvolution_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelVectorEvolution_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelVectorEvolution_inclusion ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelVectorEvolution_inclusion
end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
end

noncomputable section
open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal
namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
variable {ι : Type*} [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {a T : ℝ}

def heatVectorField (a T : ℝ) (u₀ : PiLp 2 (fun _ : ι => TensorHs g r s (a + 1))) :
    timeL2 (PiLp 2 (fun _ : ι => TensorHs g r s (a + 2))) T :=
  (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T)).symm
    (WithLp.toLp 2 (fun i => heatEvolutionField a T (u₀ i)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorField ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorField

def heatVectorEvolution (a T : ℝ) (u₀ : PiLp 2 (fun _ : ι => TensorHs g r s (a + 1))) :
    timeH1 (PiLp 2 (fun _ : ι => TensorHs g r s a)) T :=
  timeH1.piLpEquiv.symm (WithLp.toLp 2 (fun i => heatEvolution a T (u₀ i)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorEvolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorEvolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorEvolution ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorEvolution

theorem heatVectorField_ae
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g r s (a + 1))) :
    heatVectorField a T u₀ =ᵐ[timeMeasure T]
      fun t => WithLp.toLp 2 (fun i => heatEvolutionField a T (u₀ i) t) :=
  Lp.piLpEquiv_symm_apply (𝕜 := ℝ) (timeMeasure T) _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorField_ae then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorField_ae"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorField_ae ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorField_ae

theorem heatVectorField_eq_ae {S : ℝ} (hS : 0 < S) (hST : S ≤ T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g r s (a + 1))) :
    heatVectorField a S u₀ =ᵐ[timeMeasure S] heatVectorField a T u₀ := by
  have hm : timeMeasure S ≤ timeMeasure T := Measure.restrict_mono (_root_.Set.Icc_subset_Icc le_rfl hST) le_rfl
  have hs := heatVectorField_ae (T := S) u₀
  have ht := (heatVectorField_ae (T := T) u₀).filter_mono (_root_.MeasureTheory.ae_mono hm)
  have hi : ∀ᵐ t ∂timeMeasure S, ∀ i : ι,
      heatEvolutionField a S (u₀ i) t = heatEvolutionField a T (u₀ i) t :=
    ae_all_iff.mpr fun i => heatEvolutionField_eq_ae hS hST hc (u₀ i)
  filter_upwards [hs, ht, hi] with t hst htt hit
  rw [hst, htt]
  exact PiLp.ext hit

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorField_eq_ae then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorField_eq_ae"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorField_eq_ae ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorField_eq_ae

theorem heatVectorField_norm_small_time
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g r s (a + 1))) {ε τ : ℝ} (hε : 0 < ε) (hτ : 0 < τ) :
    ∃ δ ∈ _root_.Set.Ioc (0 : ℝ) τ, ∀ T ∈ _root_.Set.Ioc (0 : ℝ) δ, ‖heatVectorField a T u₀‖ < ε := by
  obtain ⟨δ, hδ, hsmall⟩ := TimeSobolev.exists_pos_integral_norm_sq_lt hτ
    (heatVectorField a τ u₀) (sq_pos_of_pos hε)
  refine ⟨δ, hδ, ?_⟩
  intro T hT
  have hsq := hsmall T ⟨hT.1.le, hT.2⟩
  have hn : ‖heatVectorField a T u₀‖ ^ 2 =
      ∫ t in _root_.Set.Icc (0 : ℝ) T, ‖heatVectorField a τ u₀ t‖ ^ 2 := by
    rw [TimeSobolev.norm_sq_eq_integral]
    exact _root_.MeasureTheory.integral_congr_ae ((heatVectorField_eq_ae hT.1 (hT.2.trans hδ.2) hc u₀).fun_comp (fun x => ‖x‖ ^ 2))
  rw [← hn] at hsq
  exact (sq_lt_sq₀ (norm_nonneg _) hε.le).mp hsq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorField_norm_small_time then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorField_norm_small_time"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorField_norm_small_time ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorField_norm_small_time

theorem heatVectorField_toFunL2 (hT : 0 ≤ T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g r s (a + 1))) :
    (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion (g := g) (r := r) (s := s)
      (show a ≤ a + 2 by linarith))).compLpL 2 (timeMeasure T) (heatVectorField a T u₀) =
      (heatVectorEvolution a T u₀).toFunL2 := by
  apply (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T)).injective
  rw [Lp.piLpEquiv_compLpL (𝕜 := ℝ)]
  simp only [heatVectorField, heatVectorEvolution,
    timeH1.piLpEquiv_symm_toFunL2, LinearIsometryEquiv.apply_symm_apply]
  apply PiLp.ext
  intro i
  exact heatEvolutionField_toTimeL2 hT hc (u₀ i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorField_toFunL2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorField_toFunL2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorField_toFunL2 ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorField_toFunL2

theorem heatVectorEvolution_timeDeriv
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g r s (a + 1))) :
    timeH1.timeDeriv _ T (heatVectorEvolution a T u₀) =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorScaleLaplacian
        (g := g) (r := r) (s := s) a)).compLpL 2 (timeMeasure T) (heatVectorField a T u₀) := by
  apply (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T)).injective
  rw [Lp.piLpEquiv_compLpL (𝕜 := ℝ)]
  change Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T)
    ((Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T)).symm
      (WithLp.toLp 2 (fun i => (heatEvolution a T (u₀ i)).deriv))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  unfold heatVectorField
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply PiLp.ext
  intro i
  exact heatEvolution_timeDeriv (u₀ i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorEvolution_timeDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorEvolution_timeDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorEvolution_timeDeriv ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorEvolution_timeDeriv

theorem heatVectorEvolution_trace0
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g r s (a + 1))) :
    timeH1.trace0 _ T (heatVectorEvolution a T u₀) =
      ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion (g := g) (r := r) (s := s)
        (show a ≤ a + 1 by linarith)) u₀ := by
  apply PiLp.ext
  intro i
  exact heatEvolution_trace0 (T := T) (u₀ i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorEvolution_trace0 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorEvolution_trace0"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorEvolution_trace0 ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorEvolution_trace0

private theorem homogeneousField_zero (hT : 0 ≤ T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s)) :
    maximalRegularityHomogeneousSolutionField (g := g) (r := r) (s := s) a T 0 = 0 := by
  apply norm_le_zero_iff.mp
  simpa only [norm_zero, _root_.MulZeroClass.mul_zero] using
    maximalRegularityHomogeneousSolutionField_norm_le hc (0 : TensorHs g r s (a + 2)) hT

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.homogeneousField_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.homogeneousField_zero target :: scope.openDecls } }

private theorem homogeneousEvolution_zero (hT : 0 ≤ T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s)) :
    maximalRegularityHomogeneous (g := g) (r := r) (s := s) a T 0 = 0 := by
  apply timeH1.ext
  · change tensorHsInclusion (g := g) (r := r) (s := s) (show a ≤ a + 2 by linarith) 0 = 0
    exact map_zero _
  · change maximalRegularityHomogeneousDerivField a T 0 = 0
    rw [maximalRegularityHomogeneousDerivField_eq_scaleLaplacian hT hc,
      homogeneousField_zero hT hc, map_zero]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.homogeneousEvolution_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.homogeneousEvolution_zero target :: scope.openDecls } }

theorem heatDuhamelVectorField_eq_add (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g r s (a + 1)))
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g r s a)) T) :
    heatDuhamelVectorField hT u₀ F = heatVectorField a T u₀ +
      maximalRegularityDuhamelVectorField hT 0 F := by
  apply (Lp.piLpEquiv (𝕜 := ℝ) (timeMeasure T)).injective
  rw [map_add]
  simp only [heatDuhamelVectorField, heatVectorField, maximalRegularityDuhamelVectorField,
    LinearIsometryEquiv.apply_symm_apply]
  apply PiLp.ext
  intro i
  change heatDuhamelEvolutionField a hT (u₀ i) _ = heatEvolutionField a T (u₀ i) +
    maximalRegularityDuhamelSolutionField a hT 0 _
  rw [heatDuhamelEvolutionField, maximalRegularityDuhamelSolutionField,
    homogeneousField_zero hT.le hc, zero_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelVectorField_eq_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelVectorField_eq_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelVectorField_eq_add ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelVectorField_eq_add

theorem heatDuhamelVectorEvolution_eq_add (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g r s (a + 1)))
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g r s a)) T) :
    heatDuhamelVectorEvolution hT u₀ F = heatVectorEvolution a T u₀ +
      maximalRegularityDuhamelVectorMap hT 0 F := by
  apply timeH1.piLpEquiv.injective
  rw [map_add]
  simp only [heatDuhamelVectorEvolution, heatVectorEvolution, maximalRegularityDuhamelVectorMap,
    LinearIsometryEquiv.apply_symm_apply]
  apply PiLp.ext
  intro i
  change heatDuhamelEvolution a hT (u₀ i) _ = heatEvolution a T (u₀ i) +
    maximalRegularityDuhamelMap a hT 0 _
  rw [heatDuhamelEvolution, maximalRegularityDuhamelMap,
    homogeneousEvolution_zero hT.le hc, zero_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelVectorEvolution_eq_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelVectorEvolution_eq_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelVectorEvolution_eq_add ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatDuhamelVectorEvolution_eq_add

def heatVectorTrace (hT : 0 ≤ T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g r s (a + 1)))
    (t : ℝ) : PiLp 2 (fun _ : ι => TensorHs g r s (a + 1)) :=
  WithLp.toLp 2 (fun i => (heatEvolutionCrossScale hT hc (u₀ i)).repr t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorTrace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorTrace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorTrace ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorTrace

omit [Fintype ι] in
theorem heatVectorTrace_continuousOn (hT : 0 ≤ T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g r s (a + 1))) :
    ContinuousOn (heatVectorTrace hT hc u₀) (_root_.Set.Icc (0 : ℝ) T) :=
  (PiLp.continuous_toLp 2 _).comp_continuousOn
    (continuousOn_pi.mpr fun i => (heatEvolutionCrossScale hT hc (u₀ i)).continuousOn_repr)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorTrace_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorTrace_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorTrace_continuousOn ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorTrace_continuousOn

omit [Fintype ι] in
theorem heatVectorTrace_initial (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g r s (a + 1))) : heatVectorTrace hT.le hc u₀ 0 = u₀ := by
  apply PiLp.ext
  intro i
  exact heatEvolutionCrossScale_repr_initial hT hc (u₀ i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorTrace_initial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorTrace_initial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorTrace_initial ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorTrace_initial

theorem heatVectorTrace_ae (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g r s (a + 1))) :
    heatVectorTrace hT.le hc u₀ =ᵐ[timeMeasure T] fun t =>
      ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion (g := g) (r := r) (s := s)
        (show a + 1 ≤ a + 2 by linarith)) (heatVectorField a T u₀ t) := by
  have hi : ∀ᵐ t ∂timeMeasure T, ∀ i : ι,
      (heatEvolutionCrossScale hT.le hc (u₀ i)).repr t =
        tensorHsInclusion (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith)
          (heatEvolutionField a T (u₀ i) t) :=
    ae_all_iff.mpr fun i => heatEvolutionCrossScale_repr_ae hT hc (u₀ i)
  filter_upwards [hi, heatVectorField_ae u₀] with t hit ht
  rw [ht]
  exact PiLp.ext (fun i => hit i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorTrace_ae then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorTrace_ae"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorTrace_ae ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorTrace_ae

theorem heatVectorTrace_near_initial (hT : 0 < T)
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g r s (a + 1))) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ ∈ _root_.Set.Ioc (0 : ℝ) T, ∀ t ∈ _root_.Set.Icc (0 : ℝ) δ, ‖heatVectorTrace hT.le hc u₀ t - u₀‖ < ε := by
  have hc0 := heatVectorTrace_continuousOn hT.le hc u₀ 0 (show (0 : ℝ) ∈ _root_.Set.Icc (0 : ℝ) T from ⟨le_rfl, hT.le⟩)
  rw [Metric.continuousWithinAt_iff] at hc0
  obtain ⟨δ, hδ, hclose⟩ := hc0 ε hε
  refine ⟨min T (δ / 2), ⟨lt_min hT (half_pos hδ), min_le_left _ _⟩, ?_⟩
  intro t ht
  have htT : t ∈ _root_.Set.Icc (0 : ℝ) T := ⟨ht.1, ht.2.trans (min_le_left _ _)⟩
  have htd : _root_.Dist.dist t (0 : ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    exact lt_of_le_of_lt (ht.2.trans (min_le_right _ _)) (by linarith)
  have hn := hclose htT htd
  rw [heatVectorTrace_initial hT hc u₀, dist_eq_norm] at hn
  exact hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorTrace_near_initial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorTrace_near_initial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorTrace_near_initial ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorTrace_near_initial
end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
end

noncomputable section
open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal
namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
variable {ι : Type*} [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {a : ℝ}

theorem heatVectorField_near_initial
    (hc : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s))
    (u₀ : PiLp 2 (fun _ : ι => TensorHs g r s (a + 1))) {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ δ ∈ _root_.Set.Ioc (0 : ℝ) τ, ∀ T ∈ _root_.Set.Ioc (0 : ℝ) δ, ∀ᵐ t ∂timeMeasure T,
      ‖ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion (g := g) (r := r) (s := s)
        (show a + 1 ≤ a + 2 by linarith)) (heatVectorField a T u₀ t) - u₀‖ < ε := by
  obtain ⟨δ, hδ, hnear⟩ := heatVectorTrace_near_initial hτ hc u₀ hε
  refine ⟨δ, hδ, ?_⟩
  intro T hT
  have hTτ : T ≤ τ := hT.2.trans hδ.2
  have hfield := heatVectorField_eq_ae hT.1 hTτ hc u₀
  have htrace := heatVectorTrace_ae hτ hc u₀
  have hmono : timeMeasure T ≤ timeMeasure τ :=
    Measure.restrict_mono (_root_.Set.Icc_subset_Icc le_rfl hTτ) le_rfl
  have htraceT := htrace.filter_mono (_root_.MeasureTheory.ae_mono hmono)
  have hnearT : ∀ᵐ t ∂timeMeasure T, ‖heatVectorTrace hτ.le hc u₀ t - u₀‖ < ε := by
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
    exact hnear t ⟨ht.1, ht.2.trans hT.2⟩
  filter_upwards [hfield, htraceT, hnearT] with t hf ht hn
  rw [hf, ← ht]
  exact hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorField_near_initial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorField_near_initial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorField_near_initial ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.heatVectorField_near_initial
end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
end
