import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CollarMetricControl

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Submission.Set
open scoped _root_.Topology _root_.Submission.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [T2Space M] [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem collarEDist_triangle (g : SmoothRiemannianMetric I3 M) (x y z : M) :
    riemannianEDistOf (I := I3) g x z ≤
      riemannianEDistOf (I := I3) g x y + riemannianEDistOf (I := I3) g y z := by
  let : Bundle.RiemannianBundle (TangentSpace I3 : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact Manifold.riemannianEDist_triangle

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.collarEDist_triangle
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.collarEDist_triangle target :: scope.openDecls } }

omit [T2Space M] [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem collarEDist_comm (g : SmoothRiemannianMetric I3 M) (x y : M) :
    riemannianEDistOf (I := I3) g x y = riemannianEDistOf (I := I3) g y x := by
  let : Bundle.RiemannianBundle (TangentSpace I3 : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact Manifold.riemannianEDist_comm

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.collarEDist_comm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.collarEDist_comm target :: scope.openDecls } }

omit [T2Space M] [SigmaCompactSpace M] in
theorem exists_uniform_collar_section_diameter :
    ∃ D : ℝ, 0 < D ∧ ∀ (C : CylinderReference) (h : ℝ → SmoothRiemannianMetric IC Cylinder)
      (g : ℝ → SmoothRiemannianMetric I3 M) (F : PartialDiffeomorph IC I3 Cylinder M ∞)
      (U : Set Cylinder) (times : Set ℝ) (order : ℕ) (eps z : ℝ),
      MetricComparisonOn h g F U times order eps → h 0 = C.metric 0 → 0 ≤ eps → eps ≤ 1 →
      0 ∈ times → U ⊆ F.source → (∀ y : Sphere 2, (y, z) ∈ U) → ∀ p q : Sphere 2,
      riemannianEDistOf (g 0) (F (p, z)) (F (q, z)) ≤ ENNReal.ofReal D := by
  obtain ⟨D, hD, hshort⟩ := exists_uniform_transverse_shortcuts (M := M)
  refine ⟨D, hD, ?_⟩
  intro C h g F U times order eps z cmp hmetric heps heps1 hzero hsource hlevel p q
  obtain ⟨gamma, hstart, hend, hgamma, -, hlen⟩ :=
    hshort C h g F U times order eps z cmp hmetric heps heps1 hzero hsource hlevel p q
  have hdist := edistOf_le_metricPathELength (g 0) (by norm_num : (0 : ℝ) ≤ 1) hgamma
  rw [hstart, hend] at hdist
  exact hdist.trans hlen

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_uniform_collar_section_diameter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_uniform_collar_section_diameter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_uniform_collar_section_diameter ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_uniform_collar_section_diameter

omit [T2Space M] [SigmaCompactSpace M] in
theorem exists_uniform_collar_band_diameter_of_axis :
    ∃ D : ℝ, 0 < D ∧ ∀ (C : CylinderReference) (h : ℝ → SmoothRiemannianMetric IC Cylinder)
      (g : ℝ → SmoothRiemannianMetric I3 M) (F : PartialDiffeomorph IC I3 Cylinder M ∞)
      (U : Set Cylinder) (times : Set ℝ) (order : ℕ) (eps V : ℝ),
      MetricComparisonOn h g F U times order eps → h 0 = C.metric 0 → 0 ≤ eps → eps ≤ 1 →
      0 ∈ times → U ⊆ F.source → _root_.Set.univ ×ˢ _root_.Set.Icc (-10 : ℝ) 10 ⊆ U → 0 ≤ V →
      (∀ (p : Sphere 2) (z : ℝ), z ∈ _root_.Set.Icc (-10 : ℝ) 10 →
        riemannianEDistOf (g 0) (F (p, z)) (F (p, 0)) ≤ ENNReal.ofReal V) →
      ∀ v ∈ F '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-10 : ℝ) 10), ∀ w ∈ F '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-10 : ℝ) 10),
        riemannianEDistOf (g 0) v w ≤ ENNReal.ofReal (D + 2 * V) := by
  obtain ⟨D, hD, hsection⟩ := exists_uniform_collar_section_diameter (M := M)
  refine ⟨D, hD, ?_⟩
  intro C h g F U times order eps V cmp hmetric heps heps1 hzero hsource hslab hV haxis
    v hv w hw
  have hlevel : ∀ y : Sphere 2, (y, (0 : ℝ)) ∈ U :=
    fun y => hslab ⟨mem_univ _, ⟨by norm_num, by norm_num⟩⟩
  obtain ⟨vx, hvx, rfl⟩ := hv
  obtain ⟨wx, hwx, rfl⟩ := hw
  have hvV : riemannianEDistOf (I := I3) (g 0) (F vx) (F (vx.1, 0)) ≤ ENNReal.ofReal V :=
    haxis vx.1 vx.2 hvx.2
  have hwV : riemannianEDistOf (I := I3) (g 0) (F (wx.1, 0)) (F wx) ≤ ENNReal.ofReal V :=
    (collarEDist_comm (g 0) (F (wx.1, 0)) (F wx)).trans_le (haxis wx.1 wx.2 hwx.2)
  have hsec := hsection C h g F U times order eps 0 cmp hmetric heps heps1 hzero hsource hlevel
    vx.1 wx.1
  have htri := collarEDist_triangle (g 0) (F vx) (F (vx.1, 0)) (F wx)
  have htri' := collarEDist_triangle (g 0) (F (vx.1, 0)) (F (wx.1, 0)) (F wx)
  have hstep : riemannianEDistOf (I := I3) (g 0) (F vx) (F (vx.1, 0)) +
      riemannianEDistOf (I := I3) (g 0) (F (vx.1, 0)) (F wx) ≤
      ENNReal.ofReal V + (ENNReal.ofReal D + ENNReal.ofReal V) :=
    add_le_add hvV (htri'.trans (add_le_add hsec hwV))
  have hsum : ENNReal.ofReal V + (ENNReal.ofReal D + ENNReal.ofReal V) =
      ENNReal.ofReal (D + 2 * V) := by
    rw [← add_assoc, ← ENNReal.ofReal_add hV hD.le,
      ← ENNReal.ofReal_add (by linarith : (0 : ℝ) ≤ V + D) hV]
    congr 1
    ring
  exact htri.trans (hstep.trans hsum.le)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_uniform_collar_band_diameter_of_axis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_uniform_collar_band_diameter_of_axis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_uniform_collar_band_diameter_of_axis ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_uniform_collar_band_diameter_of_axis

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
