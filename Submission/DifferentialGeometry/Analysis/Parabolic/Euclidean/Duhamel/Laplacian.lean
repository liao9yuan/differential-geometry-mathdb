import Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.Duhamel.Frozen
import Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernel.Duhamel.LowerOrder
import Submission.DifferentialGeometry.Analysis.Schauder.Holder.Basic
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Topology.ContinuousMap.CompactlySupported

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.MeasureTheory _root_.Set
open scoped _root_.NNReal
namespace DifferentialGeometry.Analysis.Parabolic.Euclidean
open _root_.Submission.DifferentialGeometry.Analysis.Schauder

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [MeasurableSpace V] [BorelSpace V] [CompleteSpace F] in
theorem coreLap_eq_laplacian
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[ℝ] F))
    (d2u : BoundedContinuousFunction V (V →L[ℝ] V →L[ℝ] F))
    (hu : ∀ x : V, HasFDerivAt (u : V → F) (du x) x)
    (hdu : ∀ x : V, HasFDerivAt (du : V → V →L[ℝ] F) (d2u x) x)
    (x : V) : coreLap d2u x = Laplacian.laplacian (u : V → F) x := by
  have he : fderiv ℝ (u : V → F) = (du : V → V →L[ℝ] F) :=
    funext fun y => (hu y).fderiv
  simp only [coreLap_apply, InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one, he, (hdu x).fderiv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.coreLap_eq_laplacian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.coreLap_eq_laplacian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.coreLap_eq_laplacian ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.coreLap_eq_laplacian

theorem eq_heatSup_sub_heatDuhamel [Nontrivial V]
    {t : ℝ} (ht : 0 < t)
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[ℝ] F))
    (d2u : BoundedContinuousFunction V (V →L[ℝ] V →L[ℝ] F))
    (hu : ∀ x : V, HasFDerivAt (u : V → F) (du x) x)
    (hdu : ∀ x : V, HasFDerivAt (du : V → V →L[ℝ] F) (d2u x) x) :
    (u : V → F) = (fun y => heatSup t u y) - heatDuhamel t (fun _ => coreLap d2u) := by
  have hulip : LipschitzWith ‖du‖₊ (u : V → F) := by
    apply lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
    · exact fun y => (hu y).differentiableAt
    · intro y
      rw [(hu y).fderiv]
      exact_mod_cast du.norm_coe_le_norm y
  have huzero : HolderWith (2 * ‖u‖₊) 0 (u : V → F) :=
    holderWith_zero_of_norm_le u.norm_coe_le_norm
  have huhalf : HolderWith (_root_.Max.max (2 * ‖u‖₊) ‖du‖₊) (1 / 2 : NNReal) (u : V → F) :=
    huzero.of_le_of_le hulip.holderWith (by positivity) (by norm_num)
  funext y
  rw [Pi.sub_apply, heatDuhamel_const_eq_integral_heatSup,
    heatSup_primitive ht u du d2u hu hdu huhalf y]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.eq_heatSup_sub_heatDuhamel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.eq_heatSup_sub_heatDuhamel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.eq_heatSup_sub_heatDuhamel ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.eq_heatSup_sub_heatDuhamel

theorem eq_heatSup_sub_heatDuhamel_of_laplacian_eq
    [Nontrivial V]
    (u g : BoundedContinuousFunction V F) (hu : ContDiff ℝ 2 (u : V → F))
    (hcs : HasCompactSupport (u : V → F))
    (hΔ : ∀ x : V, Laplacian.laplacian (u : V → F) x = g x)
    {t : ℝ} (ht : 0 < t) (x : V) :
    u x = heatSup t u x - heatDuhamel t (fun _ => g) x := by
  have hdf : ContDiff ℝ 1 (fderiv ℝ (u : V → F)) := hu.fderiv_right (by norm_num)
  let du : BoundedContinuousFunction V (V →L[ℝ] F) :=
    (⟨⟨fderiv ℝ (u : V → F), hdf.continuous⟩, hcs.fderiv ℝ⟩ :
      CompactlySupportedContinuousMap V (V →L[ℝ] F)).toBoundedContinuousFunction
  let d2u : BoundedContinuousFunction V (V →L[ℝ] V →L[ℝ] F) :=
    (⟨⟨fderiv ℝ (fderiv ℝ (u : V → F)), hdf.continuous_fderiv (by norm_num)⟩,
      (hcs.fderiv ℝ).fderiv ℝ⟩ :
      CompactlySupportedContinuousMap V (V →L[ℝ] V →L[ℝ] F)).toBoundedContinuousFunction
  have hdu (y : V) : HasFDerivAt (u : V → F) (du y) y :=
    (hu.differentiable (by norm_num) y).hasFDerivAt
  have hd2u (y : V) : HasFDerivAt (du : V → V →L[ℝ] F) (d2u y) y :=
    (hdf.differentiable (by norm_num) y).hasFDerivAt
  have hcore : coreLap d2u = g := by
    apply BoundedContinuousFunction.ext
    intro y
    exact (coreLap_eq_laplacian u du d2u hdu hd2u y).trans (hΔ y)
  have hh := congrFun (eq_heatSup_sub_heatDuhamel ht u du d2u hdu hd2u) x
  simpa only [Pi.sub_apply, hcore] using hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.eq_heatSup_sub_heatDuhamel_of_laplacian_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.eq_heatSup_sub_heatDuhamel_of_laplacian_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.eq_heatSup_sub_heatDuhamel_of_laplacian_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.eq_heatSup_sub_heatDuhamel_of_laplacian_eq

end DifferentialGeometry.Analysis.Parabolic.Euclidean
