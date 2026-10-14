import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Submission.DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix

namespace DifferentialGeometry
namespace Integral
namespace Measure


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

def chartDensity (g : SmoothRiemannianMetric I M) (x₀ : M) : M → ℝ :=
  fun x => Real.sqrt (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g x₀ x).det

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.chartDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.chartDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.chartDensity ``Submission.DifferentialGeometry.Integral.Measure.chartDensity

lemma chartDensity_pos
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet) :
    0 < chartDensity g x₀ x :=
  Real.sqrt_pos.mpr (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_det_pos (I := I) g x₀ hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.chartDensity_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.chartDensity_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.chartDensity_pos ``Submission.DifferentialGeometry.Integral.Measure.chartDensity_pos
lemma chartDensity_contMDiffOn
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    ContMDiffOn I 𝓘(ℝ) ∞ (chartDensity g x₀)
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet := by
  intro x hx
  have hdet := DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_det_contMDiffOn (I := I) g x₀ x hx
  have hpos_ne : (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g x₀ x).det ≠ 0 :=
    ne_of_gt (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_det_pos (I := I) g x₀ hx)
  have hsqrt : ContDiffAt ℝ ∞ Real.sqrt
      (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g x₀ x).det :=
    Real.contDiffAt_sqrt hpos_ne
  have := hsqrt.comp_contMDiffWithinAt (f :=
      fun y : M => (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g x₀ y).det) hdet
  exact this

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.chartDensity_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.chartDensity_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.chartDensity_contMDiffOn ``Submission.DifferentialGeometry.Integral.Measure.chartDensity_contMDiffOn

def chartDensityOnE (g : SmoothRiemannianMetric I M) (x₀ : M) : E → ℝ :=
  fun y => chartDensity (I := I) g x₀ ((extChartAt I x₀).symm y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.chartDensityOnE then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.chartDensityOnE"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.chartDensityOnE ``Submission.DifferentialGeometry.Integral.Measure.chartDensityOnE

lemma chartDensityOnE_contDiffOn
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    ContDiffOn ℝ ∞ (chartDensityOnE (I := I) g x₀)
      (extChartAt I x₀).target := by
  have hbase : ContMDiffOn I 𝓘(ℝ) ∞ (chartDensity (I := I) g x₀)
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet :=
    chartDensity_contMDiffOn (I := I) g x₀
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I x₀).symm
      (extChartAt I x₀).target := contMDiffOn_extChartAt_symm (I := I) x₀
  have hsubset : (extChartAt I x₀).target ⊆
      (extChartAt I x₀).symm ⁻¹'
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet :=
    fun _ hy =>
      DifferentialGeometry.Tensor.Coordinates.extChartAt_symm_mem_trivializationAt_baseSet
        (I := I) x₀ hy
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      ((chartDensity (I := I) g x₀) ∘ (extChartAt I x₀).symm)
      (extChartAt I x₀).target := hbase.comp hsymm hsubset
  exact hcomp.contDiffOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.chartDensityOnE_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.chartDensityOnE_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.chartDensityOnE_contDiffOn ``Submission.DifferentialGeometry.Integral.Measure.chartDensityOnE_contDiffOn

noncomputable def modelHaar : MeasureTheory.Measure E := (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).addHaar

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.modelHaar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.modelHaar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.modelHaar ``Submission.DifferentialGeometry.Integral.Measure.modelHaar

instance modelHaar_isAddHaarMeasure :
    MeasureTheory.Measure.IsAddHaarMeasure (modelHaar (E := E)) := by
  unfold modelHaar
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.modelHaar_isAddHaarMeasure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.modelHaar_isAddHaarMeasure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.modelHaar_isAddHaarMeasure ``Submission.DifferentialGeometry.Integral.Measure.modelHaar_isAddHaarMeasure

theorem map_toEuclidean_modelHaar_eq_volume :
    MeasureTheory.Measure.map (toEuclidean (E := E)) (modelHaar (E := E)) =
      (MeasureTheory.volume :
        MeasureTheory.Measure
          (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) := by
  classical
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  have h₁ :
      MeasureTheory.Measure.map (toEuclidean (E := E))
          (modelHaar (E := E)) =
        ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).map
            (toEuclidean (E := E)).toLinearEquiv).addHaar := by
    unfold modelHaar
    exact Module.Basis.map_addHaar (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E)
      (toEuclidean (E := E))
  rw [h₁]
  have hcancel :
      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).map (toEuclidean (E := E)).toLinearEquiv
        = (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis := by
    refine Module.Basis.eq_of_apply_eq ?_
    intro i
    have hb_i : (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis i
        = EuclideanSpace.single i (1 : ℝ) := by
      simp [OrthonormalBasis.coe_toBasis,
        EuclideanSpace.basisFun_apply (𝕜 := ℝ) (ι := Fin (Module.finrank ℝ E))]
    rw [Module.Basis.map_apply, DifferentialGeometry.Tensor.Coordinates.chartModelBasis_apply, hb_i]
    simp
  rw [hcancel]
  exact (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).addHaar_eq_volume

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.map_toEuclidean_modelHaar_eq_volume then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.map_toEuclidean_modelHaar_eq_volume"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.map_toEuclidean_modelHaar_eq_volume ``Submission.DifferentialGeometry.Integral.Measure.map_toEuclidean_modelHaar_eq_volume

def chartLocalMeasure
    (g : SmoothRiemannianMetric I M) (x₀ : M) : MeasureTheory.Measure M :=
  MeasureTheory.Measure.map (extChartAt I x₀).symm
    (((modelHaar (E := E)).restrict (extChartAt I x₀).target).withDensity
      (fun y : E =>
        ENNReal.ofReal
          (chartDensity g x₀ ((extChartAt I x₀).symm y))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.chartLocalMeasure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.chartLocalMeasure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.chartLocalMeasure ``Submission.DifferentialGeometry.Integral.Measure.chartLocalMeasure

lemma chartLocalMeasure_def
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    chartLocalMeasure (I := I) g x₀ =
      MeasureTheory.Measure.map (extChartAt I x₀).symm
        (((modelHaar (E := E)).restrict (extChartAt I x₀).target).withDensity
          (fun y : E =>
            ENNReal.ofReal
              (chartDensity g x₀ ((extChartAt I x₀).symm y)))) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.chartLocalMeasure_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.chartLocalMeasure_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.chartLocalMeasure_def ``Submission.DifferentialGeometry.Integral.Measure.chartLocalMeasure_def

end Measure
end Integral
end DifferentialGeometry
