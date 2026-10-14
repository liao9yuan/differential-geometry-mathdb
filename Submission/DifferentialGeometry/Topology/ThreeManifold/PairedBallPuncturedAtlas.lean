import Submission.DifferentialGeometry.Topology.Manifold.PuncturedBoundaryAtlas
import Submission.DifferentialGeometry.Topology.ThreeManifold.PairedBallGluing

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Metric _root_.Submission.Metric _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PairedBallGluing.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PairedBallGluing.E3 target :: scope.openDecls } }

variable {V : Type v} {E : Type w}
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (b : Bool) →
    OrientedBallChart (N (endpoint e b)).toClosedOrientedManifold)

theorem sigma_mem_flag_image_union_iff (v : V) (S : Set E3) (x : (N v).Carrier) :
    (⟨v, x⟩ : Σ v, (N v).Carrier) ∈ ⋃ p, flagMap N endpoint chart p '' S ↔
      x ∈ ⋃ p : {p : E × Bool // endpoint p.1 p.2 = v},
        (incidenceChart N endpoint chart v p).chart '' S := by
  constructor
  · intro hx
    obtain ⟨p, y, hy, hyx⟩ := mem_iUnion.mp hx
    have hv : endpoint p.1 p.2 = v := congrArg Sigma.fst hyx
    refine mem_iUnion.mpr ⟨⟨p, hv⟩, y, hy, ?_⟩
    have h := (incidenceChart_sigma_apply N endpoint chart v ⟨p, hv⟩ y).trans hyx
    exact eq_of_heq (Sigma.mk.inj h).2
  · intro hx
    obtain ⟨p, y, hy, hyx⟩ := mem_iUnion.mp hx
    refine mem_iUnion.mpr ⟨p.val, y, hy, ?_⟩
    exact (incidenceChart_sigma_apply N endpoint chart v p y).symm.trans
      (congrArg (Sigma.mk v) hyx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.sigma_mem_flag_image_union_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.sigma_mem_flag_image_union_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.sigma_mem_flag_image_union_iff ``Submission.DifferentialGeometry.Topology.PairedBallGluing.sigma_mem_flag_image_union_iff

variable [Finite E]
  (hdisj : Pairwise fun p q =>
    Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
      (flagMap N endpoint chart q '' closedBall (0 : E3) 2))

include hdisj in
theorem exists_smoothBoundaryAtlas_puncturedFactor (v : V) :
    ∃ C : SmoothBoundaryAtlas (𝓡 3) 3
        {x : (N v).Carrier | (⟨v, x⟩ : Σ v, (N v).Carrier) ∉ ⋃ p, flagMap N endpoint chart p '' _root_.Metric.ball (0 : E3) 1},
      ∀ x : PuncturedFactor N endpoint chart v,
        C.ambientChart x x.val 0 = 0 ↔
          (⟨v, x.val⟩ : Σ v, (N v).Carrier) ∈ ⋃ p, flagMap N endpoint chart p '' _root_.Metric.sphere (0 : E3) 1 := by
  let c := fun p : {p : E × Bool // endpoint p.1 p.2 = v} =>
    (incidenceChart N endpoint chart v p).toBallChart
  have hc : Pairwise fun p q =>
      Disjoint ((c p).chart '' _root_.Metric.closedBall (0 : E3) 2) ((c q).chart '' _root_.Metric.closedBall (0 : E3) 2) :=
    pairwise_disjoint_incidenceChart_image N endpoint chart v hdisj
  have hK : {x : (N v).Carrier | (⟨v, x⟩ : Σ v, (N v).Carrier) ∉
      ⋃ p, flagMap N endpoint chart p '' _root_.Metric.ball (0 : E3) 1} =
      (⋃ p, (c p).chart '' _root_.Metric.ball (0 : E3) 1)ᶜ := by
    ext x
    exact not_congr (sigma_mem_flag_image_union_iff N endpoint chart v (_root_.Metric.ball (0 : E3) 1) x)
  have hboundary (x : (N v).Carrier) :
      x ∈ ⋃ p, (c p).chart '' _root_.Metric.sphere (0 : E3) 1 ↔
        (⟨v, x⟩ : Σ v, (N v).Carrier) ∈ ⋃ p, flagMap N endpoint chart p '' _root_.Metric.sphere (0 : E3) 1 :=
    (sigma_mem_flag_image_union_iff N endpoint chart v (_root_.Metric.sphere (0 : E3) 1) x).symm
  change ∃ C : SmoothBoundaryAtlas (𝓡 3) 3
    {x : (N v).Carrier | (⟨v, x⟩ : Σ v, (N v).Carrier) ∉
      ⋃ p, flagMap N endpoint chart p '' _root_.Metric.ball (0 : E3) 1},
    ∀ x : ↥{x : (N v).Carrier | (⟨v, x⟩ : Σ v, (N v).Carrier) ∉
      ⋃ p, flagMap N endpoint chart p '' _root_.Metric.ball (0 : E3) 1},
      C.ambientChart x x.val 0 = 0 ↔
        (⟨v, x.val⟩ : Σ v, (N v).Carrier) ∈ ⋃ p, flagMap N endpoint chart p '' _root_.Metric.sphere (0 : E3) 1
  rw [hK]
  obtain ⟨C, hC⟩ := BallChart.exists_smoothBoundaryAtlas_ball_complement c hc
  exact ⟨C, fun x => (hC x).trans (hboundary x.val)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.exists_smoothBoundaryAtlas_puncturedFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.exists_smoothBoundaryAtlas_puncturedFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.exists_smoothBoundaryAtlas_puncturedFactor ``Submission.DifferentialGeometry.Topology.PairedBallGluing.exists_smoothBoundaryAtlas_puncturedFactor

include hdisj in
theorem exists_isManifold_puncturedFactor (v : V) :
    ∃ charts : ChartedSpace (EuclideanHalfSpace 3) (PuncturedFactor N endpoint chart v),
      let _ := charts
      IsManifold (𝓡∂ 3) ∞ (PuncturedFactor N endpoint chart v) ∧
        ContMDiff (𝓡∂ 3) (𝓡 3) ∞
          (Subtype.val : PuncturedFactor N endpoint chart v → (N v).Carrier) ∧
        ∀ x : PuncturedFactor N endpoint chart v,
          (𝓡∂ 3).IsBoundaryPoint x ↔
            (⟨v, x.val⟩ : Σ v, (N v).Carrier) ∈ ⋃ p, flagMap N endpoint chart p '' _root_.Metric.sphere (0 : E3) 1 := by
  obtain ⟨C, hC⟩ := exists_smoothBoundaryAtlas_puncturedFactor N endpoint chart hdisj v
  exact ⟨C.toChartedSpace, C.isManifold, C.contMDiff_subtype_val,
    fun x => (C.isBoundaryPoint_iff x).trans (hC x)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PairedBallGluing.exists_isManifold_puncturedFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PairedBallGluing.exists_isManifold_puncturedFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PairedBallGluing.exists_isManifold_puncturedFactor ``Submission.DifferentialGeometry.Topology.PairedBallGluing.exists_isManifold_puncturedFactor

end DifferentialGeometry.Topology.PairedBallGluing
