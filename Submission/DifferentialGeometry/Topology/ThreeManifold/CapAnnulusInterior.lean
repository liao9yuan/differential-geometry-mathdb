import Submission.DifferentialGeometry.Topology.ThreeManifold.CapBallChart
import Submission.DifferentialGeometry.Topology.Manifold.ClosedBall.BallChart
import Submission.DifferentialGeometry.Topology.Manifold.SmoothEmbeddingDiffeomorph
import Submission.DifferentialGeometry.Topology.Manifold.SpherePolarCoordinates

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Metric _root_.Manifold _root_.Submission.Manifold _root_.Function
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.SphericalCapping

universe u
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Sphere" => Metric.sphere (0 : E3) 1
local notation "PI" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)
private local instance cellCharts : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  Handle.closedCellChartedSpaceSucc 2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCapping.cellCharts
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCapping.cellCharts target :: scope.openDecls } }
private local instance cellSmooth : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) := Handle.closedCellIsManifold 2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCapping.cellSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCapping.cellSmooth target :: scope.openDecls } }
private local instance sphereDimension : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCapping.sphereDimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCapping.sphereDimension target :: scope.openDecls } }

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

private theorem exists_capInteriorChart (b : T.Boundary)
    (B : ClosedCell 3 ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3) :
    ∃ φ : _root_.PartialDiffeomorph (𝓡 3) (𝓡 3) E3 N.Carrier ∞,
      φ.source = _root_.Metric.ball 0 1 ∧
      φ.target = (C.cap b ∘ B) '' {x : ClosedCell 3 | ‖x.val‖ < 1} ∧
      ∀ (x : E3) (hx : ‖x‖ < 1), φ x = C.cap b (B ⟨x, hx.le⟩) :=
  Manifold.exists_partialDiffeomorph_of_closedCell_embedding (C.cap b ∘ B)
    (Manifold.isSmoothEmbedding_diffeomorph_precomp (C.cap b) (C.cap_embedding b) B)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCapping.exists_capInteriorChart
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCapping.exists_capInteriorChart target :: scope.openDecls } }

def capInteriorChart (b : T.Boundary)
    (B : ClosedCell 3 ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3) :
    _root_.PartialDiffeomorph (𝓡 3) (𝓡 3) E3 N.Carrier ∞ :=
  (C.exists_capInteriorChart b B).choose

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.capInteriorChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.capInteriorChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.capInteriorChart ``Submission.DifferentialGeometry.Topology.SphericalCapping.capInteriorChart

@[simp] theorem capInteriorChart_source (b : T.Boundary)
    (B : ClosedCell 3 ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3) :
    (C.capInteriorChart b B).source = _root_.Metric.ball 0 1 :=
  (C.exists_capInteriorChart b B).choose_spec.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.capInteriorChart_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.capInteriorChart_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.capInteriorChart_source ``Submission.DifferentialGeometry.Topology.SphericalCapping.capInteriorChart_source

@[simp] theorem capInteriorChart_target (b : T.Boundary)
    (B : ClosedCell 3 ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3) :
    (C.capInteriorChart b B).target = (C.cap b ∘ B) '' {x : ClosedCell 3 | ‖x.val‖ < 1} :=
  (C.exists_capInteriorChart b B).choose_spec.2.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.capInteriorChart_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.capInteriorChart_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.capInteriorChart_target ``Submission.DifferentialGeometry.Topology.SphericalCapping.capInteriorChart_target

theorem capInteriorChart_apply (b : T.Boundary)
    (B : ClosedCell 3 ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3) {x : E3} (hx : ‖x‖ < 1) :
    C.capInteriorChart b B x = C.cap b (B ⟨x, hx.le⟩) :=
  (C.exists_capInteriorChart b B).choose_spec.2.2 x hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.capInteriorChart_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.capInteriorChart_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.capInteriorChart_apply ``Submission.DifferentialGeometry.Topology.SphericalCapping.capInteriorChart_apply

private theorem norm_sphere_smul (q : Sphere × ℝ) (hq : 0 < q.2) :
    ‖q.2 • q.1.val‖ = q.2 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hq, norm_eq_of_mem_sphere, mul_one]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphericalCapping.norm_sphere_smul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphericalCapping.norm_sphere_smul target :: scope.openDecls } }

def capAnnulusInteriorChart (b : T.Boundary)
    (B : ClosedCell 3 ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3) (v : Sphere) :
    _root_.PartialDiffeomorph PI (𝓡 3) (Sphere × ℝ) N.Carrier ∞ :=
  (Manifold.spherePolarChart (n := 2) v).trans (C.capInteriorChart b B)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.capAnnulusInteriorChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.capAnnulusInteriorChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.capAnnulusInteriorChart ``Submission.DifferentialGeometry.Topology.SphericalCapping.capAnnulusInteriorChart

@[simp] theorem capAnnulusInteriorChart_source (b : T.Boundary)
    (B : ClosedCell 3 ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3) (v : Sphere) :
    (C.capAnnulusInteriorChart b B v).source = {q | q.2 ∈ _root_.Set.Ioo (0 : ℝ) 1} := by
  change {q : Sphere × ℝ | 0 < q.2} ∩ (Manifold.spherePolarChart (n := 2) v) ⁻¹'
    (C.capInteriorChart b B).source = _
  rw [C.capInteriorChart_source]
  ext q
  constructor
  · rintro ⟨h0,h1⟩
    exact ⟨h0, by simpa only [_root_.Set.mem_preimage, Manifold.spherePolarChart_apply,
      mem_ball_zero_iff, norm_sphere_smul q h0] using h1⟩
  · rintro ⟨h0,h1⟩
    refine ⟨h0, ?_⟩
    change q.2 • q.1.val ∈ _root_.Metric.ball (0 : E3) 1
    rwa [mem_ball_zero_iff, norm_sphere_smul q h0]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.capAnnulusInteriorChart_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.capAnnulusInteriorChart_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.capAnnulusInteriorChart_source ``Submission.DifferentialGeometry.Topology.SphericalCapping.capAnnulusInteriorChart_source

theorem capAnnulusInteriorChart_apply (b : T.Boundary)
    (B : ClosedCell 3 ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3) (v : Sphere)
    (q : Sphere × ℝ) (hq : q.2 ∈ _root_.Set.Ioo (0 : ℝ) 1) :
    C.capAnnulusInteriorChart b B v q = C.cap b (B ⟨q.2 • q.1.val, by
      rw [norm_sphere_smul q hq.1]
      exact hq.2.le⟩) :=
  by
    change C.capInteriorChart b B (q.2 • q.1.val) = _
    exact C.capInteriorChart_apply b B (by rw [norm_sphere_smul q hq.1]; exact hq.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.capAnnulusInteriorChart_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.capAnnulusInteriorChart_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.capAnnulusInteriorChart_apply ``Submission.DifferentialGeometry.Topology.SphericalCapping.capAnnulusInteriorChart_apply

theorem isLocalDiffeomorphAt_capAnnulusInteriorChart (b : T.Boundary)
    (B : ClosedCell 3 ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3) (v : Sphere)
    {q : Sphere × ℝ} (hq : q.2 ∈ _root_.Set.Ioo (0 : ℝ) 1) :
    IsLocalDiffeomorphAt PI (𝓡 3) ∞ (C.capAnnulusInteriorChart b B v) q :=
  (C.capAnnulusInteriorChart b B v).isLocalDiffeomorphAt _ _ ∞ (by
    rw [C.capAnnulusInteriorChart_source]
    exact hq)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.isLocalDiffeomorphAt_capAnnulusInteriorChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.isLocalDiffeomorphAt_capAnnulusInteriorChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.isLocalDiffeomorphAt_capAnnulusInteriorChart ``Submission.DifferentialGeometry.Topology.SphericalCapping.isLocalDiffeomorphAt_capAnnulusInteriorChart

theorem cap_comp_homeomorph_notMem_iUnion_capBallChart_closedBall
    (b : T.Boundary) (B : ClosedCell 3 ≃ₜ ClosedCell 3)
    (hsmall : ∀ x : ClosedCell 3, ‖x.val‖ ≤ 1 / 4 → B x = x)
    (x : ClosedCell 3) (hx : 1 / 4 < ‖x.val‖) :
    C.cap b (B x) ∉ ⋃ b', (C.capBallChart b').chart '' _root_.Metric.closedBall (0 : E3) 1 := by
  intro h
  obtain ⟨b', y, hy, heq⟩ := mem_iUnion.mp h
  let r : ℝ := if b'.2 then 1 / 4 else -(1 / 4)
  have habs : |r| = 1 / 4 := by dsimp only [r]; cases b'.2 <;> norm_num
  have hyn : ‖r • y‖ ≤ 1 / 4 := by
    rw [norm_smul, Real.norm_eq_abs, habs]
    have hy' : ‖y‖ ≤ 1 := mem_closedBall_zero_iff.mp hy
    linarith
  let z : ClosedCell 3 := ⟨r • y, by linarith⟩
  have hz : ‖z.val‖ ≤ 1 / 4 := hyn
  have hc : (C.capBallChart b').chart y = C.cap b' z :=
    C.capBallChart_apply b' y (by change ‖r • y‖ < 1; linarith)
  have hcaps : C.cap b' z = C.cap b (B x) := hc.symm.trans heq
  by_cases hb : b' = b
  · subst b'
    have hzx : z = B x := (C.cap_embedding b).isEmbedding.injective hcaps
    have hxz : x = z := B.injective (hzx.symm.trans (hsmall z hz).symm)
    rw [hxz] at hx
    exact not_lt_of_ge hz hx
  · exact Set.disjoint_left.mp (C.cap_disjoint hb) ⟨z,hcaps⟩ ⟨B x,rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.cap_comp_homeomorph_notMem_iUnion_capBallChart_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.cap_comp_homeomorph_notMem_iUnion_capBallChart_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.cap_comp_homeomorph_notMem_iUnion_capBallChart_closedBall ``Submission.DifferentialGeometry.Topology.SphericalCapping.cap_comp_homeomorph_notMem_iUnion_capBallChart_closedBall

theorem capAnnulusInteriorChart_notMem_iUnion_capBallChart_closedBall
    (b : T.Boundary) (B : ClosedCell 3 ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3)
    (hsmall : ∀ x : ClosedCell 3, ‖x.val‖ ≤ 1 / 4 → B x = x) (v : Sphere)
    (q : Sphere × ℝ) (hq : q.2 ∈ _root_.Set.Ioo (1 / 4 : ℝ) 1) :
    C.capAnnulusInteriorChart b B v q ∉
      ⋃ b', (C.capBallChart b').chart '' _root_.Metric.closedBall (0 : E3) 1 := by
  have hq0 : 0 < q.2 := lt_trans (by norm_num) hq.1
  rw [C.capAnnulusInteriorChart_apply b B v q ⟨hq0,hq.2⟩]
  apply C.cap_comp_homeomorph_notMem_iUnion_capBallChart_closedBall b B.toHomeomorph hsmall
  change 1 / 4 < ‖q.2 • q.1.val‖
  rw [norm_sphere_smul q hq0]
  exact hq.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.capAnnulusInteriorChart_notMem_iUnion_capBallChart_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.capAnnulusInteriorChart_notMem_iUnion_capBallChart_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.capAnnulusInteriorChart_notMem_iUnion_capBallChart_closedBall ``Submission.DifferentialGeometry.Topology.SphericalCapping.capAnnulusInteriorChart_notMem_iUnion_capBallChart_closedBall

end DifferentialGeometry.Topology.SphericalCapping
