import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingCellChain
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34InteriorCrossingChartsCells

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open _root_.Classical in
theorem exists_interior_crossing_cell_chain
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hdim : Module.finrank ℝ E = 3)
    {A B J N : Set E} (hJ : IsPLSphere 1 J) (hJA : J ⊆ A ∩ B)
    (hJK : J ⊆ interior K.space) (hcross : ∀ x ∈ J, HasPLCrossingAt A B x)
    (hA : ∀ x ∈ J, ∀ O ∈ 𝓝 x, ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
      (g : EuclideanSpace ℝ (Fin 2) → E), 0 < r ∧ ContinuousOn g (Metric.ball c r) ∧
        _root_.Set.InjOn g (Metric.ball c r) ∧ _root_.Set.MapsTo g (Metric.ball c r) (A ∩ O) ∧ g c = x)
    (hB : ∀ x ∈ J, ∀ O ∈ 𝓝 x, ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
      (g : EuclideanSpace ℝ (Fin 2) → E), 0 < r ∧ ContinuousOn g (Metric.ball c r) ∧
        _root_.Set.InjOn g (Metric.ball c r) ∧ _root_.Set.MapsTo g (Metric.ball c r) (B ∩ O) ∧ g c = x)
    (hN : IsOpen N) (hJN : J ⊆ N) (htrace : (A ∩ B) ∩ N ⊆ J) :
    ∃ R : Geometry.SimplicialComplex ℝ E, IsSubdivision R K ∧ R.faces.Finite ∧
      (PiecewiseLinear.restrict R J).space = J ∧
      Nonempty (Section34CrossingCellChain R (PiecewiseLinear.restrict R J) A B N) := by
  obtain ⟨t, R, ψ, V, Ω, W, P, q, hRK, hRfin, hJR, hcharts, hcover⟩ :=
    exists_subdivision_isolated_crossing_circle_disks_of_local_ball_charts K
      hJ hJA hJK hcross hA hB hN hJN htrace
  let := hRfin.to_subtype
  let Γ := PiecewiseLinear.restrict R J
  let := (restrict_faces_finite R J).to_subtype
  have hΓJ : Γ.space = J := hJR
  have hΓ : IsPLSphere 1 Γ.space := hΓJ.symm ▸ hJ
  have hΓint : Γ.space ⊆ interior R.space := by
    rw [hΓJ, hRK.space_eq]
    exact hJK
  refine ⟨R, hRK, hRfin, hJR, ?_⟩
  apply exists_crossing_cell_chain_of_chart_cover R Γ (hK.of_isSubdivision hRK)
    hdim hΓ (restrict_faces_subset R J) hΓint (ψ := ψ) (V := V) (Ω := Ω) (W := W)
    (P := P) (q := q) ?_ hcover
  intro j
  obtain ⟨-, -, -, hWΩ, hΩN, hψ, hsheets, -, haxis, hP⟩ := hcharts j
  refine ⟨hWΩ, fun _ hx => (hΩN hx).1, hψ, hsheets, ?_, ?_⟩
  · simpa only [hΓJ] using haxis
  · intro i
    obtain ⟨hqi, -, hPi, hread⟩ := hP i
    exact ⟨hqi, hPi, fun x hx => by simpa only [hΓJ] using hread x hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_interior_crossing_cell_chain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_interior_crossing_cell_chain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_interior_crossing_cell_chain ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_interior_crossing_cell_chain

end DifferentialGeometry.Topology.PiecewiseLinear
