import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Chart.Local
import Submission.DifferentialGeometry.Geometry.Connection.ChartFrame.ChartLieBracket

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Operator

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

omit [NeZero (Module.finrank ℝ E)] in
lemma christoffelCorrection_symm_cancel
    (g : SmoothRiemannianMetric I M) (α : M) (x : M) (v w : TangentSpace I x) :
    christoffelCorrection (I := I) g α x (trivToE (I := I) α x w) v =
      christoffelCorrection (I := I) g α x (trivToE (I := I) α x v) w := by
  classical
  rw [christoffelCorrection_apply, christoffelCorrection_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [chartChristoffel_symm (I := I) g α j i k (extChartAt I α x)]
  congr 1
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.christoffelCorrection_symm_cancel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.christoffelCorrection_symm_cancel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.christoffelCorrection_symm_cancel ``Submission.DifferentialGeometry.Geometry.Connection.christoffelCorrection_symm_cancel


omit [NeZero (Module.finrank ℝ E)] in
theorem chartLeviCivita_torsion_free_on (g : SmoothRiemannianMetric I M) (α : M) :
    ∀ {X Y : Π x : M, TangentSpace I x} {x : M},
      MDiffAt (T% X) x → MDiffAt (T% Y) x →
      x ∈ chartLeviCivitaGoodSet (I := I) α →
      chartLeviCivita (I := I) g α Y x (X x)
        - chartLeviCivita (I := I) g α X x (Y x) =
        VectorField.mlieBracket I X Y x := by
  intro X Y x hX hY hx
  classical
  have hx_source : x ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hx
  have hx_base : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  have hx_int : extChartAt I α x ∈ interior ((extChartAt I α).target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx
  rw [chartLeviCivita_apply (I := I) g α Y hx (X x)]
  rw [chartLeviCivita_apply (I := I) g α X hx (Y x)]
  rw [← map_sub]
  have hreorg :
      (fderiv ℝ (chartESectionRepr (I := I) α Y ∘ (extChartAt I α).symm)
            (extChartAt I α x) (trivToE (I := I) α x (X x))
        + christoffelCorrection (I := I) g α x
            (chartESectionRepr (I := I) α Y x) (X x))
      - (fderiv ℝ (chartESectionRepr (I := I) α X ∘ (extChartAt I α).symm)
            (extChartAt I α x) (trivToE (I := I) α x (Y x))
        + christoffelCorrection (I := I) g α x
            (chartESectionRepr (I := I) α X x) (Y x))
      =
      (fderiv ℝ (chartESectionRepr (I := I) α Y ∘ (extChartAt I α).symm)
            (extChartAt I α x) (trivToE (I := I) α x (X x))
        - fderiv ℝ (chartESectionRepr (I := I) α X ∘ (extChartAt I α).symm)
            (extChartAt I α x) (trivToE (I := I) α x (Y x))) := by
    have hY_repr : chartESectionRepr (I := I) α Y x =
        trivToE (I := I) α x (Y x) :=
      chartE_section_repr_eq_trivToE (I := I) α Y x
    have hX_repr : chartESectionRepr (I := I) α X x =
        trivToE (I := I) α x (X x) :=
      chartE_section_repr_eq_trivToE (I := I) α X x
    rw [hY_repr, hX_repr]
    have hcancel :
        christoffelCorrection (I := I) g α x (trivToE (I := I) α x (Y x)) (X x) =
          christoffelCorrection (I := I) g α x (trivToE (I := I) α x (X x)) (Y x) :=
      christoffelCorrection_symm_cancel (I := I) g α x (X x) (Y x)
    rw [hcancel]
    abel
  rw [hreorg]
  exact (mlieBracket_eq_chart_fderiv_diff (I := I) α x X Y
    hx_source hx_base hx_int hX hY).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartLeviCivita_torsion_free_on then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartLeviCivita_torsion_free_on"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartLeviCivita_torsion_free_on ``Submission.DifferentialGeometry.Geometry.Connection.chartLeviCivita_torsion_free_on

end Connection
end Geometry
end DifferentialGeometry
