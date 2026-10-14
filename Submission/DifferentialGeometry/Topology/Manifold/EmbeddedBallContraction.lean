import Submission.DifferentialGeometry.Analysis.Calculus.Interpolation.RadialContraction
import Submission.DifferentialGeometry.Topology.Manifold.PartialChartSupportedExtension
import Mathlib.Geometry.Manifold.LocalDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Metric _root_.Filter _root_.Topology _root_.Manifold
open scoped _root_.ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {E F H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {I : ModelWithCorners ℝ F H}

theorem exists_diffeomorphs_contracting_embedded_closedBall
    (φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞)
    {r : ℝ} (hr : 0 < r) (hrs : _root_.Metric.closedBall (0 : E) r ⊆ φ.source)
    {V : Set M} (hV : IsOpen V) (himage : φ '' _root_.Metric.closedBall 0 r ⊆ V) :
    ∃ J : ℝ → Diffeomorph I I M M ∞,
      ContMDiff (𝓘(ℝ).prod I) I ∞ (fun q : ℝ × M ↦ J q.1 q.2) ∧
      ContMDiff (𝓘(ℝ).prod I) I ∞ (fun q : ℝ × M ↦ (J q.1).symm q.2) ∧
      J 0 = Diffeomorph.refl I M ∞ ∧
      (∀ t x, 0 ≤ t → x ∈ _root_.Metric.closedBall 0 r → J t (φ x) = φ (Real.exp (-t) • x)) ∧
      ∃ K : Set M, IsCompact K ∧ K ⊆ V ∧ K ⊆ φ.target ∧
        ∀ t x, x ∉ K → J t x = x ∧ (J t).symm x = x := by
  classical
  let U : Set E := φ.source ∩ φ ⁻¹' V
  have hU : IsOpen U := φ.toOpenPartialHomeomorph.isOpen_inter_preimage hV
  have hBU : _root_.Metric.closedBall (0 : E) r ⊆ U := fun x hx ↦ ⟨hrs hx, himage ⟨x, hx, rfl⟩⟩
  obtain ⟨D, hD, hDi, hzero, hrad, K, hK, hKU, hfix⟩ :=
    DifferentialGeometry.Analysis.exists_compact_flow_contracting_closedBall_in_open hr hU hBU
  let e := φ.symm.toOpenPartialHomeomorph
  have hKt : K ⊆ e.target := fun x hx ↦ (hKU hx).1
  obtain ⟨J, hJ, hJi, hJe, hKi, hKit, hJfix⟩ :=
    exists_diffeomorph_extension_of_partial_chart_family e
      φ.contMDiffOn_invFun φ.contMDiffOn_toFun D hD hDi hK hKt hfix
  refine ⟨J, hJ, hJi, ?_, ?_, e.symm '' K, hKi, ?_, hKit, hJfix⟩
  · apply Diffeomorph.ext
    intro x
    rw [(hJe 0 x).1, hzero]
    by_cases hx : x ∈ e.source
    · change (if x ∈ e.source then e.symm (e x) else x) = x
      rw [if_pos hx, e.left_inv hx]
    · exact if_neg hx
  · intro t x ht hx
    rw [(hJe t (φ x)).1]
    have hφx : φ x ∈ e.source := φ.map_source (hrs hx)
    rw [show extendChartById e (D t) (φ x) = e.symm (D t (e (φ x))) from if_pos hφx]
    change φ (D t (φ.symm (φ x))) = _
    have hi : φ.symm.toPartialEquiv (φ.toPartialEquiv x) = x := φ.left_inv (hrs hx)
    rw [hi, hrad t x ht hx]
  · rintro x ⟨z, hz, rfl⟩
    exact (hKU hz).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_diffeomorphs_contracting_embedded_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_diffeomorphs_contracting_embedded_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_diffeomorphs_contracting_embedded_closedBall ``Submission.DifferentialGeometry.Topology.Manifold.exists_diffeomorphs_contracting_embedded_closedBall

end DifferentialGeometry.Topology.Manifold
