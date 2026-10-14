import Submission.DifferentialGeometry.Topology.Homology.Local.NeighborhoodSphere
import Submission.DifferentialGeometry.Topology.Homology.Local.Graded

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Set _root_.Metric _root_.Submission.DifferentialGeometry.LocalDegree
namespace DifferentialGeometry.Homology
universe u
variable {d : ℕ}


def localBallSphereHomologyIso (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (r : ℝ) (hr : 0 < r) {k : Type u} [Ring k] (R : ModuleCat.{u} k) (n : ℕ) :
    relativeHomology (TopCat.of (_root_.Metric.ball x r))
      ({(⟨x,_root_.Metric.mem_ball_self hr⟩ : _root_.Metric.ball x r)}ᶜ : Set (_root_.Metric.ball x r)) R (n + 1) ≅
    reducedSingularHomology R (TopCat.of (_root_.Metric.sphere (0 : E) 1)) n := by
  let _ : ContractibleSpace (_root_.Metric.ball x r) := (convex_ball x r).contractibleSpace ⟨x,_root_.Metric.mem_ball_self hr⟩
  exact relativeReducedConnectingIso _ _ R n ≪≫
    puncturedNeighborhoodSphereHomologyIso E x (_root_.Metric.ball x r) (_root_.Metric.mem_ball_self hr) _root_.Metric.isOpen_ball R n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.localBallSphereHomologyIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.localBallSphereHomologyIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.localBallSphereHomologyIso ``Submission.DifferentialGeometry.Homology.localBallSphereHomologyIso


def euclideanBallLocalGenerator (x : EuclideanSpace ℝ (Fin (d + 1))) (R : ℝ) (hR : 0 < R) :
    relativeHomology (TopCat.of (_root_.Metric.ball x R))
      ({(⟨x,_root_.Metric.mem_ball_self hR⟩ : _root_.Metric.ball x R)}ᶜ : Set (_root_.Metric.ball x R)) (ModuleCat.of ℤ ℤ) (d + 1) :=
  (localBallSphereHomologyIso _ x R hR (ModuleCat.of ℤ ℤ) d).inv (euclideanSphereTopGenerator d)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.euclideanBallLocalGenerator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.euclideanBallLocalGenerator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.euclideanBallLocalGenerator ``Submission.DifferentialGeometry.Homology.euclideanBallLocalGenerator


def euclideanLocalGenerator (d : ℕ) :
    relativeHomology (TopCat.of (EuclideanSpace ℝ (Fin (d + 1))))
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (d + 1)))) (ModuleCat.of ℤ ℤ) (d + 1) :=
  (localEuclideanSphereHomologyIso (ModuleCat.of ℤ ℤ) (d + 1) d).inv (euclideanSphereTopGenerator d)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.euclideanLocalGenerator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.euclideanLocalGenerator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.euclideanLocalGenerator ``Submission.DifferentialGeometry.Homology.euclideanLocalGenerator


theorem euclideanLocalGenerator_ne_zero (d : ℕ) : euclideanLocalGenerator d ≠ 0 := by
  intro h
  have hh := congrArg (localEuclideanSphereHomologyIso (ModuleCat.of ℤ ℤ) (d + 1) d).hom h
  have he := congrArg (fun g => g (euclideanSphereTopGenerator d))
    (localEuclideanSphereHomologyIso (ModuleCat.of ℤ ℤ) (d + 1) d).inv_hom_id
  exact euclideanSphereTopGenerator_ne_zero d (he.symm.trans (hh.trans (map_zero _)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.euclideanLocalGenerator_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.euclideanLocalGenerator_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.euclideanLocalGenerator_ne_zero ``Submission.DifferentialGeometry.Homology.euclideanLocalGenerator_ne_zero


theorem euclideanBallLocalGenerator_ne_zero (x : EuclideanSpace ℝ (Fin (d + 1)))
    (r : ℝ) (hr : 0 < r) : euclideanBallLocalGenerator x r hr ≠ 0 := by
  intro h
  have hh := congrArg (localBallSphereHomologyIso _ x r hr (ModuleCat.of ℤ ℤ) d).hom h
  have he := congrArg (fun g => g (euclideanSphereTopGenerator d))
    (localBallSphereHomologyIso _ x r hr (ModuleCat.of ℤ ℤ) d).inv_hom_id
  exact euclideanSphereTopGenerator_ne_zero d (he.symm.trans (hh.trans (map_zero _)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.euclideanBallLocalGenerator_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.euclideanBallLocalGenerator_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.euclideanBallLocalGenerator_ne_zero ``Submission.DifferentialGeometry.Homology.euclideanBallLocalGenerator_ne_zero

end DifferentialGeometry.Homology
