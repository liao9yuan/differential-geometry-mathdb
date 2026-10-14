import Submission.DifferentialGeometry.Analysis.Calculus.Manifold.AbsolutelyContinuous
import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1Energy
import Submission.DifferentialGeometry.Analysis.Calculus.Manifold.AbsolutelyContinuousPartition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold
namespace Manifold
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

theorem absolutelyContinuousOnInterval_of_timeH1_extChartAt
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b) (p : M)
    (hsrc : _root_.Set.MapsTo γ (_root_.Set.Icc a b) (chartAt H p).source)
    (u : DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1 E (b - a))
    (hrep : _root_.Set.EqOn u.toFun (fun r => extChartAt I p (γ (a + r))) (_root_.Set.Icc 0 (b - a))) :
    absolutelyContinuousOnInterval I γ a b := by
  have hAC := u.absolutelyContinuousOnInterval_toFun (sub_nonneg.mpr hab)
  have hshift : AbsolutelyContinuousOnInterval (fun t => u.toFun (t - a)) a b := by
    apply hAC.comp_monotone_lipschitzOn (g := fun t => t - a) (K := 1)
    · simpa only [sub_eq_add_neg] using
        (isometry_add_right (-a)).lipschitz.lipschitzOnWith (s := _root_.Set.uIcc a b)
    · exact fun _ _ _ _ hst => sub_le_sub_right hst a
    · intro t ht
      change t ∈ (fun r => r - a) ⁻¹' _root_.Set.uIcc 0 (b - a)
      rw [_root_.Set.preimage_sub_const_uIcc]
      simpa only [zero_add, sub_add_cancel] using ht
  apply absolutelyContinuousOnInterval_of_extChartAt p (by simpa only [_root_.Set.uIcc_of_le hab] using hsrc)
  apply hshift.congr
  intro t ht
  rw [_root_.Set.uIcc_of_le hab] at ht
  have hh := hrep (show t - a ∈ _root_.Set.Icc 0 (b - a) from ⟨sub_nonneg.mpr ht.1, sub_le_sub_right ht.2 a⟩)
  simpa only [add_sub_cancel, Function.comp_apply] using hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.absolutelyContinuousOnInterval_of_timeH1_extChartAt then
    throwError "Refusing to shadow existing declaration Manifold.absolutelyContinuousOnInterval_of_timeH1_extChartAt"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.absolutelyContinuousOnInterval_of_timeH1_extChartAt ``Submission.Manifold.absolutelyContinuousOnInterval_of_timeH1_extChartAt


theorem absolutelyContinuousOnInterval_of_timeH1_chart_partition
    {γ : ℝ → M} {m : ℕ} (t : Fin (m + 1) → ℝ) (ht : Monotone t)
    (p : Fin m → M)
    (u : (i : Fin m) → DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1 E
      (t i.succ - t i.castSucc))
    (hsrc : ∀ i, _root_.Set.MapsTo γ (_root_.Set.Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source)
    (hrep : ∀ i, _root_.Set.EqOn (u i).toFun
      (fun r => extChartAt I (p i) (γ (t i.castSucc + r)))
      (_root_.Set.Icc 0 (t i.succ - t i.castSucc))) :
    absolutelyContinuousOnInterval I γ (t 0) (t (Fin.last m)) := by
  apply absolutelyContinuousOnInterval_of_finite_partition t ht
  intro i
  exact absolutelyContinuousOnInterval_of_timeH1_extChartAt (ht i.castSucc_le_succ)
    (p i) (hsrc i) (u i) (hrep i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.absolutelyContinuousOnInterval_of_timeH1_chart_partition then
    throwError "Refusing to shadow existing declaration Manifold.absolutelyContinuousOnInterval_of_timeH1_chart_partition"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.absolutelyContinuousOnInterval_of_timeH1_chart_partition ``Submission.Manifold.absolutelyContinuousOnInterval_of_timeH1_chart_partition

end Manifold
