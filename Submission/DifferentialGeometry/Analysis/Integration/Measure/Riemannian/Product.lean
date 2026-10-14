
import Submission.DifferentialGeometry.Analysis.Integration.Measure.ModelHaar
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.LinearAlgebra.Determinant

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

set_option autoImplicit false

open _root_.MeasureTheory _root_.Set _root_.Module _root_.Submission.Module
open scoped _root_.ENNReal

namespace DifferentialGeometry
namespace Integral
namespace Measure

open _root_.Submission.DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private local instance instE : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instE
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instE target :: scope.openDecls } }
private local instance instEB : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instEB
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instEB target :: scope.openDecls } }

noncomputable def finrankProdRealEquiv :
    Fin (Module.finrank ℝ (E × ℝ)) ≃ Fin (Module.finrank ℝ E) ⊕ Fin (Module.finrank ℝ ℝ) :=
  (finCongr (Module.finrank_prod (M := E) (M' := ℝ))).trans finSumFinEquiv.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.finrankProdRealEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.finrankProdRealEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.finrankProdRealEquiv ``Submission.DifferentialGeometry.Integral.Measure.finrankProdRealEquiv

theorem addHaar_chartModelBasis_prod_real :
    ENNReal.ofReal |(((chartModelBasis E).prod (chartModelBasis ℝ)).det
        ((chartModelBasis (E × ℝ)).reindex (finrankProdRealEquiv (E := E))))| •
        ((chartModelBasis (E × ℝ)).addHaar) =
      (modelHaar (E := E)).prod (modelHaar (E := ℝ)) := by
  have h := Module.Basis.det_smul_addHaar ((chartModelBasis E).prod (chartModelBasis ℝ))
    ((chartModelBasis (E × ℝ)).reindex (finrankProdRealEquiv (E := E)))
  rw [Module.Basis.addHaar_reindex, Module.Basis.prod_addHaar] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.addHaar_chartModelBasis_prod_real then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.addHaar_chartModelBasis_prod_real"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.addHaar_chartModelBasis_prod_real ``Submission.DifferentialGeometry.Integral.Measure.addHaar_chartModelBasis_prod_real

theorem cast_smul_measure {X : Type*} {m₁ m₂ : MeasurableSpace X} (hm : m₁ = m₂)
    (c : ℝ≥0∞) (μ : @_root_.MeasureTheory.Measure X m₁) :
    cast (congrArg (fun m : MeasurableSpace X => @_root_.MeasureTheory.Measure X m) hm) (c • μ) =
      c • cast (congrArg (fun m : MeasurableSpace X => @_root_.MeasureTheory.Measure X m) hm) μ := by
  cases hm
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.cast_smul_measure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.cast_smul_measure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.cast_smul_measure ``Submission.DifferentialGeometry.Integral.Measure.cast_smul_measure

theorem cast_addHaar {ι X : Type*} [Fintype ι] [NormedAddCommGroup X]
    [NormedSpace ℝ X] {m₁ m₂ : MeasurableSpace X} (hm : m₁ = m₂)
    (b₁ : @BorelSpace X _ m₁) (b₂ : @BorelSpace X _ m₂) (b : _root_.Module.Basis ι ℝ X) :
    cast (congrArg (fun m : MeasurableSpace X => @_root_.MeasureTheory.Measure X m) hm)
        (@Module.Basis.addHaar ι X _ _ _ m₁ b₁ b) =
      @Module.Basis.addHaar ι X _ _ _ m₂ b₂ b := by
  let _ := b₁
  let _ := b₂
  cases hm
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.cast_addHaar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.cast_addHaar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.cast_addHaar ``Submission.DifferentialGeometry.Integral.Measure.cast_addHaar

theorem modelHaar_prod_real :
    cast (congrArg (fun m : MeasurableSpace (E × ℝ) => @_root_.MeasureTheory.Measure (E × ℝ) m)
        (@BorelSpace.measurable_eq (E × ℝ) _
          (@Prod.instMeasurableSpace E ℝ _ _) (Prod.borelSpace)))
      ((modelHaar (E := E)).prod (modelHaar (E := ℝ))) =
    ENNReal.ofReal |(((chartModelBasis E).prod (chartModelBasis ℝ)).det
        ((chartModelBasis (E × ℝ)).reindex (finrankProdRealEquiv (E := E))))| •
      modelHaar (E := E × ℝ) := by
  have h := addHaar_chartModelBasis_prod_real (E := E)
  have h1 := congrArg
    (cast (congrArg (fun m : MeasurableSpace (E × ℝ) => @_root_.MeasureTheory.Measure (E × ℝ) m)
      (@BorelSpace.measurable_eq (E × ℝ) _
        (@Prod.instMeasurableSpace E ℝ _ _) (Prod.borelSpace)))) h
  rw [cast_smul_measure] at h1
  · rw [cast_addHaar] at h1
    · exact h1.symm
    · exact (Prod.borelSpace).measurable_eq
  · exact (Prod.borelSpace).measurable_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.modelHaar_prod_real then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.modelHaar_prod_real"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.modelHaar_prod_real ``Submission.DifferentialGeometry.Integral.Measure.modelHaar_prod_real

end Measure
end Integral
end DifferentialGeometry
