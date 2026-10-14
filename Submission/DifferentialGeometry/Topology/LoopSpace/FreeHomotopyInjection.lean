import Submission.DifferentialGeometry.Topology.Homotopy.SquareBoundary
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.LoopSpace.BasedCircle
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.ContinuousMap
open scoped _root_.Topology

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] {x : X}


def basedCircleHomotopyTrack (γ δ : basedCircleLoop x) (H : γ.val.Homotopy δ.val) : Path x x where
  toFun t := H (t, 0)
  continuous_toFun := H.continuous.comp (continuous_id.prodMk continuous_const)
  source' := (H.apply_zero 0).trans γ.property
  target' := (H.apply_one 0).trans δ.property

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.basedCircleHomotopyTrack then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.basedCircleHomotopyTrack"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.basedCircleHomotopyTrack ``Submission.DifferentialGeometry.Topology.basedCircleHomotopyTrack



theorem basedCircleHomotopyTrack_commutes (γ δ : basedCircleLoop x)
    (H : γ.val.Homotopy δ.val) :
    ((circleToPath γ).trans (basedCircleHomotopyTrack γ δ H)).Homotopic
      ((basedCircleHomotopyTrack γ δ H).trans (circleToPath δ)) := by
  apply square_boundary_homotopic (circleToPath γ) (circleToPath δ)
    (basedCircleHomotopyTrack γ δ H) (basedCircleHomotopyTrack γ δ H)
    (⟨fun z : unitInterval × unitInterval => H (z.1, (z.2.val : loopCircle)),
      H.continuous.comp (continuous_fst.prodMk
        ((AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_subtype_val.comp continuous_snd)))⟩ :
      C(unitInterval × unitInterval, X))
  · intro s
    exact H.apply_zero _
  · intro s
    exact H.apply_one _
  · intro t
    rfl
  · intro t
    change H (t, ((1 : ℝ) : loopCircle)) = H (t, 0)
    rw [AddCircle.coe_period]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.basedCircleHomotopyTrack_commutes then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.basedCircleHomotopyTrack_commutes"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.basedCircleHomotopyTrack_commutes ``Submission.DifferentialGeometry.Topology.basedCircleHomotopyTrack_commutes



theorem circleToPath_homotopic_of_free
    (hcomm : ∀ a b : FundamentalGroup X x, a * b = b * a)
    (γ δ : basedCircleLoop x) (h : γ.val.Homotopic δ.val) :
    (circleToPath γ).Homotopic (circleToPath δ) := by
  obtain ⟨H⟩ := h
  let r : FundamentalGroup X x := Path.Homotopic.Quotient.mk (basedCircleHomotopyTrack γ δ H)
  let a : FundamentalGroup X x := Path.Homotopic.Quotient.mk (circleToPath γ)
  let b : FundamentalGroup X x := Path.Homotopic.Quotient.mk (circleToPath δ)
  have heq := Path.Homotopic.Quotient.eq.mpr (basedCircleHomotopyTrack_commutes γ δ H)
  change r * a = b * r at heq
  rw [hcomm b r] at heq
  have hab : a = b := mul_left_cancel heq
  exact Path.Homotopic.Quotient.eq.mp hab

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.circleToPath_homotopic_of_free then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.circleToPath_homotopic_of_free"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.circleToPath_homotopic_of_free ``Submission.DifferentialGeometry.Topology.circleToPath_homotopic_of_free



theorem basedCircle_joined_of_free
    (hcomm : ∀ a b : FundamentalGroup X x, a * b = b * a)
    (γ δ : basedCircleLoop x) (h : γ.val.Homotopic δ.val) : Joined γ δ := by
  obtain ⟨H⟩ := circleToPath_homotopic_of_free hcomm γ δ h
  have hc : Continuous H.eval := Path.continuous_uncurry_iff.mp H.continuous
  let p : Path (circleToPath γ) (circleToPath δ) :=
    ⟨⟨H.eval, hc⟩, H.eval_zero, H.eval_one⟩
  have hp0 : Joined (circleToPath γ) (circleToPath δ) := ⟨p⟩
  have hp := hp0.map (basedPathCircleHomeomorph x).continuous
  change Joined (basedPathCircleHomeomorph x ((basedPathCircleHomeomorph x).symm γ))
    (basedPathCircleHomeomorph x ((basedPathCircleHomeomorph x).symm δ)) at hp
  simpa only [Homeomorph.apply_symm_apply] using hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.basedCircle_joined_of_free then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.basedCircle_joined_of_free"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.basedCircle_joined_of_free ``Submission.DifferentialGeometry.Topology.basedCircle_joined_of_free

end DifferentialGeometry.Topology
