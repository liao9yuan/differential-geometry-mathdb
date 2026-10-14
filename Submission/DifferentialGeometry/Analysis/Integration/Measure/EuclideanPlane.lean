import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FunProp

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Set
open scoped _root_.ENNReal

namespace DifferentialGeometry.Analysis

def euclideanPlaneProdEquiv : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] ℝ × ℝ :=
  Complex.orthonormalBasisOneI.repr.symm.toContinuousLinearEquiv.trans Complex.equivRealProdCLM

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.euclideanPlaneProdEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.euclideanPlaneProdEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.euclideanPlaneProdEquiv ``Submission.DifferentialGeometry.Analysis.euclideanPlaneProdEquiv

@[simp] theorem euclideanPlaneProdEquiv_apply (x : EuclideanSpace ℝ (Fin 2)) :
    euclideanPlaneProdEquiv x = (x 0, x 1) := by
  simp [euclideanPlaneProdEquiv, Complex.orthonormalBasisOneI_repr_symm_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.euclideanPlaneProdEquiv_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.euclideanPlaneProdEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.euclideanPlaneProdEquiv_apply ``Submission.DifferentialGeometry.Analysis.euclideanPlaneProdEquiv_apply

@[simp] theorem euclideanPlaneProdEquiv_symm_apply (p : ℝ × ℝ) :
    euclideanPlaneProdEquiv.symm p = WithLp.toLp 2 ![p.1, p.2] := by
  apply euclideanPlaneProdEquiv.injective
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.euclideanPlaneProdEquiv_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.euclideanPlaneProdEquiv_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.euclideanPlaneProdEquiv_symm_apply ``Submission.DifferentialGeometry.Analysis.euclideanPlaneProdEquiv_symm_apply

theorem measurePreserving_euclideanPlaneProdEquiv :
    MeasurePreserving euclideanPlaneProdEquiv _root_.MeasureTheory.MeasureSpace.volume volume := by
  exact Complex.volume_preserving_equiv_real_prod.comp
    Complex.orthonormalBasisOneI.measurePreserving_repr_symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.measurePreserving_euclideanPlaneProdEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.measurePreserving_euclideanPlaneProdEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.measurePreserving_euclideanPlaneProdEquiv ``Submission.DifferentialGeometry.Analysis.measurePreserving_euclideanPlaneProdEquiv

theorem euclideanPlaneProdEquiv_preimage_unit_disk :
    euclideanPlaneProdEquiv ⁻¹' {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1} =
      Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  ext x
  rw [_root_.Set.mem_preimage, euclideanPlaneProdEquiv_apply]
  change x 0 ^ 2 + x 1 ^ 2 < 1 ↔ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1
  rw [EuclideanSpace.ball_zero_eq 1 (by norm_num : (0 : ℝ) ≤ 1)]
  simp [Fin.sum_univ_two]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.euclideanPlaneProdEquiv_preimage_unit_disk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.euclideanPlaneProdEquiv_preimage_unit_disk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.euclideanPlaneProdEquiv_preimage_unit_disk ``Submission.DifferentialGeometry.Analysis.euclideanPlaneProdEquiv_preimage_unit_disk

theorem integral_unit_disk_prod_eq_integral_ball
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℝ × ℝ → F) :
    (∫ p in {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1}, f p) =
      ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1, f (euclideanPlaneProdEquiv x) := by
  have h := measurePreserving_euclideanPlaneProdEquiv.setIntegral_preimage_emb
    euclideanPlaneProdEquiv.toHomeomorph.toMeasurableEquiv.measurableEmbedding f
    {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1}
  rw [euclideanPlaneProdEquiv_preimage_unit_disk] at h
  exact h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integral_unit_disk_prod_eq_integral_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integral_unit_disk_prod_eq_integral_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integral_unit_disk_prod_eq_integral_ball ``Submission.DifferentialGeometry.Analysis.integral_unit_disk_prod_eq_integral_ball

theorem measurePreserving_euclideanPlaneProdEquiv_unit_ball :
    _root_.MeasureTheory.MeasurePreserving euclideanPlaneProdEquiv
      (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1))
      (volume.restrict {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1}) := by
  have h := measurePreserving_euclideanPlaneProdEquiv.restrict_preimage
    (show MeasurableSet {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1} from
      (isOpen_lt (by fun_prop) continuous_const).measurableSet)
  rw [euclideanPlaneProdEquiv_preimage_unit_disk] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.measurePreserving_euclideanPlaneProdEquiv_unit_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.measurePreserving_euclideanPlaneProdEquiv_unit_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.measurePreserving_euclideanPlaneProdEquiv_unit_ball ``Submission.DifferentialGeometry.Analysis.measurePreserving_euclideanPlaneProdEquiv_unit_ball

theorem measurePreserving_euclideanPlaneProdEquiv_symm_unit_disk :
    _root_.MeasureTheory.MeasurePreserving euclideanPlaneProdEquiv.symm
      (volume.restrict {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1})
      (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)) :=
  MeasurePreserving.symm euclideanPlaneProdEquiv.toHomeomorph.toMeasurableEquiv
    measurePreserving_euclideanPlaneProdEquiv_unit_ball

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.measurePreserving_euclideanPlaneProdEquiv_symm_unit_disk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.measurePreserving_euclideanPlaneProdEquiv_symm_unit_disk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.measurePreserving_euclideanPlaneProdEquiv_symm_unit_disk ``Submission.DifferentialGeometry.Analysis.measurePreserving_euclideanPlaneProdEquiv_symm_unit_disk

theorem fderiv_comp_euclideanPlaneProdEquiv_symm_snd
    (f : EuclideanSpace ℝ (Fin 2) → ℝ) (p : ℝ × ℝ) :
    fderiv ℝ (f ∘ euclideanPlaneProdEquiv.symm) p (0, 1) =
      fderiv ℝ f (euclideanPlaneProdEquiv.symm p) (EuclideanSpace.single 1 1) := by
  rw [euclideanPlaneProdEquiv.symm.comp_right_fderiv]
  change fderiv ℝ f (euclideanPlaneProdEquiv.symm p)
    (euclideanPlaneProdEquiv.symm (0, 1)) = _
  congr 1
  rw [euclideanPlaneProdEquiv_symm_apply]
  ext i
  fin_cases i <;> simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.fderiv_comp_euclideanPlaneProdEquiv_symm_snd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.fderiv_comp_euclideanPlaneProdEquiv_symm_snd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.fderiv_comp_euclideanPlaneProdEquiv_symm_snd ``Submission.DifferentialGeometry.Analysis.fderiv_comp_euclideanPlaneProdEquiv_symm_snd

theorem eLpNorm_comp_euclideanPlaneProdEquiv_symm
    {F : Type*} [NormedAddCommGroup F] {f : EuclideanSpace ℝ (Fin 2) → F}
    (hf : _root_.MeasureTheory.AEStronglyMeasurable f
      (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1))) (p : ℝ≥0∞) :
    _root_.MeasureTheory.eLpNorm (f ∘ euclideanPlaneProdEquiv.symm) p
      (volume.restrict {q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 < 1}) =
      eLpNorm f p (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)) :=
  _root_.MeasureTheory.eLpNorm_comp_measurePreserving hf measurePreserving_euclideanPlaneProdEquiv_symm_unit_disk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.eLpNorm_comp_euclideanPlaneProdEquiv_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.eLpNorm_comp_euclideanPlaneProdEquiv_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.eLpNorm_comp_euclideanPlaneProdEquiv_symm ``Submission.DifferentialGeometry.Analysis.eLpNorm_comp_euclideanPlaneProdEquiv_symm

end DifferentialGeometry.Analysis

end

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped _root_.Topology _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

local notation "V" => EuclideanSpace ℝ (Fin 2)

theorem measurePreserving_complex_plane_repr_closedBall (b : ℝ) :
    _root_.MeasureTheory.MeasurePreserving Complex.orthonormalBasisOneI.repr
      (volume.restrict (Metric.closedBall (0 : ℂ) b))
      (volume.restrict (Metric.closedBall (0 : V) b)) := by
  have h := Complex.orthonormalBasisOneI.repr.measurePreserving.restrict_preimage
    (s := Metric.closedBall (0 : V) b) measurableSet_closedBall
  have heq : Complex.orthonormalBasisOneI.repr ⁻¹' Metric.closedBall (0 : V) b =
      Metric.closedBall (0 : ℂ) b := by
    ext z
    simp only [_root_.Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
      LinearIsometryEquiv.norm_map]
  simpa only [heq] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.measurePreserving_complex_plane_repr_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.measurePreserving_complex_plane_repr_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.measurePreserving_complex_plane_repr_closedBall ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.measurePreserving_complex_plane_repr_closedBall

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped _root_.Topology _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

theorem restrict_ball_eq_restrict_closedBall_complex (b : ℝ) :
    volume.restrict (Metric.ball (0 : ℂ) b) =
      volume.restrict (Metric.closedBall (0 : ℂ) b) := by
  apply Measure.restrict_congr_set
  have hnull : ∀ᵐ z : ℂ ∂volume, z ∉ Metric.sphere (0 : ℂ) b :=
    measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere _root_.MeasureTheory.MeasureSpace.volume (0 : ℂ) b)
  filter_upwards [hnull] with z hz
  apply propext
  change _root_.Dist.dist z (0 : ℂ) < b ↔ _root_.Dist.dist z (0 : ℂ) ≤ b
  have hne : _root_.Dist.dist z (0 : ℂ) ≠ b := hz
  exact ⟨le_of_lt, fun h => lt_of_le_of_ne h hne⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.restrict_ball_eq_restrict_closedBall_complex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.restrict_ball_eq_restrict_closedBall_complex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.restrict_ball_eq_restrict_closedBall_complex ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.restrict_ball_eq_restrict_closedBall_complex

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped _root_.Topology _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

local notation "E" => EuclideanSpace ℝ (Fin 2)

theorem measurePreserving_complex_plane_repr_ball (a : ℝ) :
    _root_.MeasureTheory.MeasurePreserving Complex.orthonormalBasisOneI.repr
      (volume.restrict (Metric.ball (0 : ℂ) a))
      (volume.restrict (Metric.ball (0 : E) a)) := by
  have h := Complex.orthonormalBasisOneI.repr.measurePreserving.restrict_preimage
    (s := Metric.ball (0 : E) a) Metric.isOpen_ball.measurableSet
  have heq : Complex.orthonormalBasisOneI.repr ⁻¹' Metric.ball (0 : E) a =
      Metric.ball (0 : ℂ) a := by
    ext z
    simp only [_root_.Set.mem_preimage, Metric.mem_ball, dist_zero_right,
      LinearIsometryEquiv.norm_map]
  simpa only [heq] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.measurePreserving_complex_plane_repr_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.measurePreserving_complex_plane_repr_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.measurePreserving_complex_plane_repr_ball ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.measurePreserving_complex_plane_repr_ball

theorem eLpNorm_comp_complex_plane_repr_ball
    {F : Type*} [NormedAddCommGroup F] (f : E → F) (p : ℝ≥0∞) (a : ℝ) :
    _root_.MeasureTheory.eLpNorm (f ∘ Complex.orthonormalBasisOneI.repr) p
      (volume.restrict (Metric.ball (0 : ℂ) a)) =
      eLpNorm f p (volume.restrict (Metric.ball (0 : E) a)) := by
  have h :=
    Complex.orthonormalBasisOneI.repr.toMeasurableEquiv.measurableEmbedding.eLpNorm_map_measure
    (g := f) (p := p) (μ := volume.restrict (Metric.ball (0 : ℂ) a))
  rw [LinearIsometryEquiv.coe_toMeasurableEquiv,
    (measurePreserving_complex_plane_repr_ball a).map_eq] at h
  exact h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.eLpNorm_comp_complex_plane_repr_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.eLpNorm_comp_complex_plane_repr_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.eLpNorm_comp_complex_plane_repr_ball ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.eLpNorm_comp_complex_plane_repr_ball

theorem integral_comp_complex_plane_repr_ball (f : E → ℝ) (a : ℝ) :
    (∫ z in Metric.ball (0 : ℂ) a, f (Complex.orthonormalBasisOneI.repr z)) =
      ∫ x in Metric.ball (0 : E) a, f x :=
  (measurePreserving_complex_plane_repr_ball a).integral_comp
    Complex.orthonormalBasisOneI.repr.toMeasurableEquiv.measurableEmbedding f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_comp_complex_plane_repr_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_comp_complex_plane_repr_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_comp_complex_plane_repr_ball ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_comp_complex_plane_repr_ball

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end
