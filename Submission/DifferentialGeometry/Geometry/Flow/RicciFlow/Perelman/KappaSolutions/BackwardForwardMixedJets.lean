import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderTimeErrorJets
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardForwardNeck
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Scaling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

private theorem bufferedJetNorm_add_le (epsilon : ℝ)
    (gCov gNorm : SmoothRiemannianMetric SpatialNeckCylinderModel (spatialNeckBuffer epsilon))
    (A B : Tensor0SField (I := SpatialNeckCylinderModel)
      (M := spatialNeckBuffer epsilon) (n := ∞) 2)
    (a : ℕ) (x : spatialNeckBuffer epsilon) :
    tensor02CovDerivNormWith a (A + B) gCov gNorm x ≤
      tensor02CovDerivNormWith a A gCov gNorm x +
        tensor02CovDerivNormWith a B gCov gNorm x := by
  simp only [tensor02CovDerivNormWith, tensor02_cov_deriv_eq_cov_deriv_of_field, covDerivOfField_add,
    ContMDiffSection.coe_add, Pi.add_apply]
  exact Tensor0SBundle.sqrt_normSq0S_add_le gNorm x (a + 2) _ _

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bufferedJetNorm_add_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bufferedJetNorm_add_le target :: scope.openDecls } }


def backwardForwardErrorJet (epsilon c : ℝ)
    (J : ℕ → ℝ → Tensor0SField (I := SpatialNeckCylinderModel)
      (M := spatialNeckBuffer epsilon) (n := ∞) 2) (q : ℕ) (s : ℝ) :
    Tensor0SField (I := SpatialNeckCylinderModel)
      (M := spatialNeckBuffer epsilon) (n := ∞) 2 :=
  (c * (-c⁻¹) ^ q) • J q (1 - s / c) + cylinderTimeErrorJet epsilon c q s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardForwardErrorJet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardForwardErrorJet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardForwardErrorJet ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardForwardErrorJet


theorem backwardForwardErrorJet_zero (epsilon c : ℝ) (hc : (1 : ℝ) / 2 ≤ c)
    (G : ℝ → SmoothRiemannianMetric SpatialNeckCylinderModel (spatialNeckBuffer epsilon))
    (J : ℕ → ℝ → Tensor0SField (I := SpatialNeckCylinderModel)
      (M := spatialNeckBuffer epsilon) (n := ∞) 2)
    (hJ : ∀ theta ∈ _root_.Set.Icc (1 : ℝ) 3, ∀ x v,
      J 0 theta x v = (G theta).inner x (v 0) (v 1) -
        (strongNeckBackgroundMetric epsilon (1 - theta)).inner x (v 0) (v 1))
    (s : ℝ) (hs : s ∈ _root_.Set.Icc (-1 : ℝ) 0) (x : spatialNeckBuffer epsilon)
    (v : Fin 2 → TangentSpace SpatialNeckCylinderModel x) :
    backwardForwardErrorJet epsilon c J 0 s x v =
      (scaleMetric c (lt_of_lt_of_le (by norm_num) hc) (G (1 - s / c))).inner x (v 0) (v 1) -
        (strongNeckBackgroundMetric epsilon s).inner x (v 0) (v 1) := by
  have htheta := backwardForward_time_mapsTo hc hs
  have htime : 1 - (1 - s / c) = s / c := by ring
  simp only [backwardForwardErrorJet, pow_zero, mul_one, ContMDiffSection.coe_add,
    Pi.add_apply, add_apply, ContMDiffSection.coe_smul,
    Pi.smul_apply, smul_apply, smul_eq_mul]
  rw [hJ _ htheta, htime,
    cylinderTimeErrorJet_zero epsilon c (lt_of_lt_of_le (by norm_num) hc) s hs.2,
    scaleMetric_inner, scaleMetric_inner]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardForwardErrorJet_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardForwardErrorJet_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardForwardErrorJet_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardForwardErrorJet_zero


theorem backwardForwardErrorJet_hasDerivWithinAt
    (epsilon c : ℝ) (hc : (1 : ℝ) / 2 ≤ c)
    (J : ℕ → ℝ → Tensor0SField (I := SpatialNeckCylinderModel)
      (M := spatialNeckBuffer epsilon) (n := ∞) 2)
    (hJ : ∀ q theta, theta ∈ _root_.Set.Icc (1 : ℝ) 3 → ∀ (x : spatialNeckBuffer epsilon)
      (v : Fin 2 → TangentSpace SpatialNeckCylinderModel x),
      HasDerivWithinAt (fun r => J q r x v) (J (q + 1) theta x v) (_root_.Set.Icc (1 : ℝ) 3) theta)
    (q : ℕ) (s : ℝ) (hs : s ∈ _root_.Set.Icc (-1 : ℝ) 0) (x : spatialNeckBuffer epsilon)
    (v : Fin 2 → TangentSpace SpatialNeckCylinderModel x) :
    HasDerivWithinAt (fun r => backwardForwardErrorJet epsilon c J q r x v)
      (backwardForwardErrorJet epsilon c J (q + 1) s x v) (_root_.Set.Icc (-1 : ℝ) 0) s := by
  have hmain := backwardForward_time_jet_derivative (fun b r => J b r x v) c
    (backwardForward_time_mapsTo hc) (fun b r hr => hJ b r hr x v) q s hs
  have herr := cylinderTimeErrorJet_hasDerivWithinAt epsilon c q s (_root_.Set.Icc (-1 : ℝ) 0) x v
  simpa only [backwardForwardErrorJet, ContMDiffSection.coe_add, Pi.add_apply,
    add_apply, ContMDiffSection.coe_smul, Pi.smul_apply,
    smul_apply, smul_eq_mul, Pi.add_def] using hmain.add herr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardForwardErrorJet_hasDerivWithinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardForwardErrorJet_hasDerivWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardForwardErrorJet_hasDerivWithinAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardForwardErrorJet_hasDerivWithinAt


theorem backwardForwardErrorJet_covNorm_le
    (epsilon c : ℝ) (hc : (1 : ℝ) / 2 ≤ c)
    (J : ℕ → ℝ → Tensor0SField (I := SpatialNeckCylinderModel)
      (M := spatialNeckBuffer epsilon) (n := ∞) 2)
    (a q : ℕ) (s : ℝ) (hs : s ∈ _root_.Set.Icc (-1 : ℝ) 0) (x : spatialNeckBuffer epsilon) :
    tensor02CovDerivNormWith a (backwardForwardErrorJet epsilon c J q s)
        (strongNeckBackgroundMetric epsilon s) (strongNeckBackgroundMetric epsilon s) x ≤
      (|c * (-c⁻¹) ^ q| * Real.sqrt ((3 : ℝ) ^ (a + 2))) *
        tensor02CovDerivNormWith a (J q (1 - s / c))
          (strongNeckBackgroundMetric epsilon (1 - (1 - s / c)))
          (strongNeckBackgroundMetric epsilon (1 - (1 - s / c))) x +
        |c - 1| * (3 * Real.sqrt 3) := by
  have hmodel := cylinderTimeErrorJet_covNorm_le epsilon c s hs q a x
  have hreference := strongNeckBackground_backward_forward_covNorm_le epsilon
    (1 - s / c) s (backwardForward_time_mapsTo hc hs) hs (J q (1 - s / c)) a x
  have hsum := bufferedJetNorm_add_le epsilon (strongNeckBackgroundMetric epsilon s)
    (strongNeckBackgroundMetric epsilon s) ((c * (-c⁻¹) ^ q) • J q (1 - s / c))
    (cylinderTimeErrorJet epsilon c q s) a x
  rw [tensor02CovDerivNormWith_smul] at hsum
  have hscale := mul_le_mul_of_nonneg_left hreference (abs_nonneg (c * (-c⁻¹) ^ q))
  exact hsum.trans ((add_le_add hscale hmodel).trans_eq (by ring))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardForwardErrorJet_covNorm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardForwardErrorJet_covNorm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardForwardErrorJet_covNorm_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardForwardErrorJet_covNorm_le

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
