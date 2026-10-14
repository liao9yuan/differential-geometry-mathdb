import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Chart.H1

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Function
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TimeSobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {M : Type*} [TopologicalSpace M]

omit [CompleteSpace E] in
theorem curve_c1_local
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M] [IsManifold I 1 M]
    (p : M) {a b : ℝ} (alpha : ℝ → M) (u : timeH1 E (b - a))
    (hsrc : _root_.Set.MapsTo alpha (_root_.Set.Icc a b) (chartAt H p).source)
    (hrep : _root_.Set.EqOn u.toFun (fun r ↦ extChartAt I p (alpha (a + r)))
      (_root_.Set.Icc (0 : ℝ) (b - a)))
    (hu : ContDiffOn ℝ 1 u.toFun (_root_.Set.Icc (0 : ℝ) (b - a))) :
    ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 alpha (_root_.Set.Icc a b) := by
  have hmaps : _root_.Set.MapsTo u.toFun (_root_.Set.Icc (0 : ℝ) (b - a))
      (extChartAt I p).target := by
    intro r hr
    rw [hrep hr]
    apply (extChartAt I p).map_source
    rw [extChartAt_source]
    exact hsrc ⟨le_add_of_nonneg_right hr.1, by linarith [hr.2]⟩
  have hshift : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 (fun r ↦ alpha (a + r))
      (_root_.Set.Icc (0 : ℝ) (b - a)) := by
    have hcomp : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1
        ((extChartAt I p).symm ∘ u.toFun) (_root_.Set.Icc (0 : ℝ) (b - a)) :=
      (contMDiffOn_extChartAt_symm (I := I) (n := 1) p).comp hu.contMDiffOn hmaps
    refine hcomp.congr ?_
    intro r hr
    rw [Function.comp_apply, hrep hr]
    exact ((extChartAt I p).left_inv (by
      rw [extChartAt_source]
      exact hsrc ⟨le_add_of_nonneg_right hr.1, by linarith [hr.2]⟩)).symm
  have hsub : _root_.Set.MapsTo (fun s : ℝ ↦ s - a) (_root_.Set.Icc a b)
      (_root_.Set.Icc (0 : ℝ) (b - a)) := by
    intro s hs
    exact ⟨sub_nonneg.mpr hs.1, sub_le_sub_right hs.2 a⟩
  have hback : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1
      ((fun r ↦ alpha (a + r)) ∘ fun s : ℝ ↦ s - a) (_root_.Set.Icc a b) :=
    hshift.comp (contDiffOn_id.sub contDiffOn_const).contMDiffOn hsub
  refine hback.congr ?_
  intro s _hs
  simp only [Function.comp_apply]
  congr 1
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.curve_c1_local then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.curve_c1_local"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.curve_c1_local ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.curve_c1_local

end TimeSobolev
end Parabolic
end Analysis
end DifferentialGeometry
