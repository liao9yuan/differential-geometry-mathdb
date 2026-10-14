import Submission.DifferentialGeometry.Topology.Manifold.StereographicDoubleCap
import Submission.DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Defs
import Submission.DifferentialGeometry.Topology.Manifold.BallChartScale

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.Topology.Manifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.E3 target :: scope.openDecls } }
private abbrev E4 := EuclideanSpace ℝ (Fin 4)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.E4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.E4 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.S2 target :: scope.openDecls } }
private abbrev S3 := Metric.sphere (0 : E4) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.S3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.S3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE4HAddOfNat : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE4HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE4HAddOfNat target :: scope.openDecls } }

def stereographicSmallBallChart (P : S3) : BallChart 3 (𝓡 3) S3 :=
  (SphereUnitFilling.sphereBallChart P).scale (1 / 4) (by norm_num) (by norm_num)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.stereographicSmallBallChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.stereographicSmallBallChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.stereographicSmallBallChart ``Submission.DifferentialGeometry.Topology.Manifold.stereographicSmallBallChart

def oppositeStereographicSmallBallChart (P : S3) : BallChart 3 (𝓡 3) S3 where
  chart := (stereographicSmallBallChart P).chart.trans
    (sphereAntipodalDiffeomorph (E := E4) (n := 3)).toPartialDiffeomorph
  closedBall_subset_source := fun _ hx =>
    ⟨(stereographicSmallBallChart P).closedBall_subset_source hx, _root_.Set.mem_univ _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.oppositeStereographicSmallBallChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.oppositeStereographicSmallBallChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.oppositeStereographicSmallBallChart ``Submission.DifferentialGeometry.Topology.Manifold.oppositeStereographicSmallBallChart

theorem stereographicSmallBallChart_apply (P : S3) (x : E3) :
    (stereographicSmallBallChart P).chart x = (stereographic' 3 P).symm ((-(1 / 2 : ℝ)) • x) := by
  change (stereographic' 3 P).symm (-((2 : ℝ) • ((1 / 4 : ℝ) • x))) = _
  congr 1
  module

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.stereographicSmallBallChart_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.stereographicSmallBallChart_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.stereographicSmallBallChart_apply ``Submission.DifferentialGeometry.Topology.Manifold.stereographicSmallBallChart_apply

theorem oppositeStereographicSmallBallChart_apply (P : S3) (x : E3) :
    (oppositeStereographicSmallBallChart P).chart x = -(stereographicSmallBallChart P).chart x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.oppositeStereographicSmallBallChart_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.oppositeStereographicSmallBallChart_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.oppositeStereographicSmallBallChart_apply ``Submission.DifferentialGeometry.Topology.Manifold.oppositeStereographicSmallBallChart_apply

theorem stereographicSmallBallChart_image_ball (P : S3) :
    (stereographicSmallBallChart P).chart '' Metric.ball 0 1 =
      (stereographic' 3 P).symm '' Metric.ball 0 (1 / 2) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(-(1 / 2 : ℝ)) • x, ?_, (stereographicSmallBallChart_apply P x).symm⟩
    rw [Metric.mem_ball, dist_zero_right, norm_smul]
    have hx' : ‖x‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
    norm_num
    linarith
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(-2 : ℝ) • x, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, norm_smul]
      have hx' : ‖x‖ < 1 / 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
      norm_num
      linarith
    · rw [stereographicSmallBallChart_apply, smul_smul]
      norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.stereographicSmallBallChart_image_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.stereographicSmallBallChart_image_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.stereographicSmallBallChart_image_ball ``Submission.DifferentialGeometry.Topology.Manifold.stereographicSmallBallChart_image_ball

theorem stereographicSmallBallChart_image_closedBall (P : S3) :
    (stereographicSmallBallChart P).chart '' Metric.closedBall 0 2 =
      (stereographic' 3 P).symm '' Metric.closedBall 0 1 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(-(1 / 2 : ℝ)) • x, ?_, (stereographicSmallBallChart_apply P x).symm⟩
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul]
    have hx' : ‖x‖ ≤ 2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    norm_num
    linarith
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(-2 : ℝ) • x, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, norm_smul]
      have hx' : ‖x‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
      norm_num
      linarith
    · rw [stereographicSmallBallChart_apply, smul_smul]
      norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.stereographicSmallBallChart_image_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.stereographicSmallBallChart_image_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.stereographicSmallBallChart_image_closedBall ``Submission.DifferentialGeometry.Topology.Manifold.stereographicSmallBallChart_image_closedBall

theorem oppositeStereographicSmallBallChart_image (P : S3) (U : Set E3) :
    (oppositeStereographicSmallBallChart P).chart '' U =
      Neg.neg '' ((stereographicSmallBallChart P).chart '' U) :=
  Set.image_comp Neg.neg (stereographicSmallBallChart P).chart U

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.oppositeStereographicSmallBallChart_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.oppositeStereographicSmallBallChart_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.oppositeStereographicSmallBallChart_image ``Submission.DifferentialGeometry.Topology.Manifold.oppositeStereographicSmallBallChart_image

theorem stereographicSmallBallChart_disjoint (P : S3) :
    Disjoint ((stereographicSmallBallChart P).chart '' Metric.closedBall 0 2)
      ((oppositeStereographicSmallBallChart P).chart '' Metric.closedBall 0 2) := by
  rw [oppositeStereographicSmallBallChart_image, stereographicSmallBallChart_image_closedBall]
  apply Set.disjoint_left.mpr
  rintro x ⟨y, hy, rfl⟩ ⟨z, hz, heq⟩
  have hmem : -(stereographic' 3 P).symm y ∈
      (stereographic' 3 P).symm '' Metric.closedBall 0 1 := by
    have hyz : -(stereographic' 3 P).symm y = z := by rw [← heq, neg_neg]
    rwa [hyz]
  have h := (mem_antipodal_stereographic_symm_closedBall (n := 3) P (by norm_num : (0 : ℝ) < 4) y).mp
    (by simpa using hmem)
  have hy' : ‖y‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hy
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.stereographicSmallBallChart_disjoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.stereographicSmallBallChart_disjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.stereographicSmallBallChart_disjoint ``Submission.DifferentialGeometry.Topology.Manifold.stereographicSmallBallChart_disjoint

theorem stereographicSmallBallChart_doublePunctured (P : S3) :
    (((stereographicSmallBallChart P).chart '' Metric.ball 0 1) ∪
      (oppositeStereographicSmallBallChart P).chart '' Metric.ball 0 1)ᶜ =
      (((stereographic' 3 P).symm '' Metric.ball 0 (1 / 2)) ∪
        Neg.neg '' ((stereographic' 3 P).symm '' Metric.ball 0 (4 / 8)))ᶜ := by
  rw [oppositeStereographicSmallBallChart_image, stereographicSmallBallChart_image_ball]
  norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.stereographicSmallBallChart_doublePunctured then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.stereographicSmallBallChart_doublePunctured"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.stereographicSmallBallChart_doublePunctured ``Submission.DifferentialGeometry.Topology.Manifold.stereographicSmallBallChart_doublePunctured

def sphereDoublePuncturedHomeomorph (P : S3) :
    S2 × _root_.Set.Icc (0 : ℝ) 1 ≃ₜ
      (stereographicSmallBallChart P).DoublePunctured (oppositeStereographicSmallBallChart P) :=
  (((sphereAntipodalDiffeomorph (E := E3) (n := 2)).toHomeomorph.prodCongr
    (Homeomorph.refl (_root_.Set.Icc (0 : ℝ) 1))).trans
      (closedStereographicCylinderHomeomorph P (a := 1 / 2) (b := 8) (by norm_num) (by norm_num))).trans
    (Homeomorph.setCongr (stereographicSmallBallChart_doublePunctured P).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereDoublePuncturedHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereDoublePuncturedHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereDoublePuncturedHomeomorph ``Submission.DifferentialGeometry.Topology.Manifold.sphereDoublePuncturedHomeomorph

theorem sphereDoublePuncturedHomeomorph_apply (P : S3) (p : S2 × _root_.Set.Icc (0 : ℝ) 1) :
    (sphereDoublePuncturedHomeomorph P p).val =
      (stereographic' 3 P).symm (((1 / 2 : ℝ) + (8 - 1 / 2) * p.2.val) • (-p.1).val) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereDoublePuncturedHomeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereDoublePuncturedHomeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereDoublePuncturedHomeomorph_apply ``Submission.DifferentialGeometry.Topology.Manifold.sphereDoublePuncturedHomeomorph_apply

theorem sphereDoublePuncturedHomeomorph_lower (P : S3) (z : S2) :
    (sphereDoublePuncturedHomeomorph P (z, ⟨0, by norm_num⟩)).val =
      (stereographicSmallBallChart P).chart z.val := by
  rw [sphereDoublePuncturedHomeomorph_apply, stereographicSmallBallChart_apply]
  congr 1
  change ((1 / 2 : ℝ) + (8 - 1 / 2) * 0) • -z.val = (-(1 / 2 : ℝ)) • z.val
  module

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereDoublePuncturedHomeomorph_lower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereDoublePuncturedHomeomorph_lower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereDoublePuncturedHomeomorph_lower ``Submission.DifferentialGeometry.Topology.Manifold.sphereDoublePuncturedHomeomorph_lower

theorem sphereDoublePuncturedHomeomorph_upper (P : S3) (z : S2) :
    (sphereDoublePuncturedHomeomorph P (z, ⟨1, by norm_num⟩)).val =
      (oppositeStereographicSmallBallChart P).chart (-z).val := by
  rw [sphereDoublePuncturedHomeomorph_apply, oppositeStereographicSmallBallChart_apply,
    stereographicSmallBallChart_apply]
  have hz : ‖z.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using z.property
  have hn : ‖(-(1 / 2 : ℝ)) • (-z).val‖ = 1 / 2 := by
    change ‖(-(1 / 2 : ℝ)) • -z.val‖ = 1 / 2
    simp only [norm_smul, norm_neg, hz]
    norm_num
  rw [← stereographicInverse_antipodal (n := 3) P ((-(1 / 2 : ℝ)) • (-z).val)
    (by intro h; rw [h, norm_zero] at hn; norm_num at hn), hn]
  congr 1
  change ((1 / 2 : ℝ) + (8 - 1 / 2) * 1) • -z.val =
    (-4 / (1 / 2) ^ 2) • ((-(1 / 2 : ℝ)) • -z.val)
  module

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.sphereDoublePuncturedHomeomorph_upper then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.sphereDoublePuncturedHomeomorph_upper"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.sphereDoublePuncturedHomeomorph_upper ``Submission.DifferentialGeometry.Topology.Manifold.sphereDoublePuncturedHomeomorph_upper

end DifferentialGeometry.Topology.Manifold
