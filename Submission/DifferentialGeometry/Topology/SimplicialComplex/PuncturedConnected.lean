import Submission.DifferentialGeometry.Topology.Manifold.PuncturedConnected
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.VertexChart

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsCombinatorialManifold.isConnected_sdiff_singleton
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifold (n + 2) K) (hconn : IsConnected K.space) (p : E) :
    IsConnected (K.space \ {p}) := by
  classical
  by_cases hp : p ∈ K.space
  · let _ := combinatorialChartedSpace K hK
    let _ : ConnectedSpace K.space := Subtype.connectedSpace hconn
    have hdim : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (n + 2))) := by
      rw [← Module.finrank_eq_rank]
      have hfin : 1 < Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 2))) := by simp
      exact_mod_cast hfin
    have h := (ChartedSpace.isPathConnected_compl_singleton
      (E := EuclideanSpace ℝ (Fin (n + 2))) hdim (⟨p, hp⟩ : K.space)).isConnected
    have heq : ((↑) : K.space → E) '' ({(⟨p, hp⟩ : K.space)}ᶜ) = K.space \ {p} := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, fun he => hy (Subtype.ext he)⟩
      · rintro ⟨hx, hxp⟩
        exact ⟨⟨x, hx⟩, fun h => hxp (congrArg Subtype.val h), rfl⟩
    rw [← heq]
    exact h.image _ continuous_subtype_val.continuousOn
  · rw [sdiff_eq_left.mpr (disjoint_singleton_right.mpr hp)]
    exact hconn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.isConnected_sdiff_singleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.isConnected_sdiff_singleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.isConnected_sdiff_singleton ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.isConnected_sdiff_singleton

end DifferentialGeometry.Topology.PiecewiseLinear
