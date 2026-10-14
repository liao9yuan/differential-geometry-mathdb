import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckOverlap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {x y : M}

private theorem central_sphere_mem_region (nk : SpatialNeck g eps x)
    {z : M} (hz : z ∈ nk.map '' (_root_.Set.univ ×ˢ ({0} : Set ℝ))) :
    z ∈ nk.cylindricalChart.region univ := by
  obtain ⟨q, hq, rfl⟩ := hz
  have hsrc : q ∈ nk.cylindricalChart.domain := by
    have hq0 : q.2 = 0 := hq.2
    have hi := inv_pos.mpr nk.eps_pos
    exact ⟨hq.1, by rw [hq0]; constructor <;> linarith⟩
  exact ⟨nk.cylindricalChart.chart ⟨q, hsrc⟩, ⟨⟨q, hsrc⟩, _root_.Set.mem_univ _, rfl⟩, rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.central_sphere_mem_region
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.central_sphere_mem_region target :: scope.openDecls } }

variable [T2Space M]

theorem SpatialNeck.disjoint_central_spheres_of_edist_gt
    (nk₀ : SpatialNeck g eps x) (nk₁ : SpatialNeck g eps y)
    (hsmall : eps < 1 / 1000000)
    (hfar : ENNReal.ofReal (21 / Real.sqrt (metricScalarAt g x)) < riemannianEDistOf g x y) :
    Disjoint (nk₀.map '' (_root_.Set.univ ×ˢ ({0} : Set ℝ)))
      (nk₁.map '' (_root_.Set.univ ×ˢ ({0} : Set ℝ))) := by
  apply Set.disjoint_left.mpr
  intro z hz₀ hz₁
  have hratio := nk₀.cylindricalChart.scale_ratio_of_metricCloseOn nk₁.cylindricalChart g
    eps (by linarith) nk₀.cylindricalChart_metricCloseOn nk₁.cylindricalChart_metricCloseOn z
    (central_sphere_mem_region nk₀ hz₀) (central_sphere_mem_region nk₁ hz₁)
  change |metricScalarAt g x / metricScalarAt g y - 1| ≤ 17292 * eps at hratio
  have hQ : metricScalarAt g x ≤ 4 * metricScalarAt g y := by
    have hh : metricScalarAt g x / metricScalarAt g y ≤ 4 := by
      linarith [(abs_le.mp hratio).2]
    exact (div_le_iff₀ nk₁.Q_pos).mp hh
  have hsQ : Real.sqrt (metricScalarAt g x) ≤ 2 * Real.sqrt (metricScalarAt g y) := by
    have hx := Real.sq_sqrt nk₀.Q_pos.le
    have hy := Real.sq_sqrt nk₁.Q_pos.le
    nlinarith [Real.sqrt_nonneg (metricScalarAt g x), Real.sqrt_nonneg (metricScalarAt g y)]
  have hdiv : 7 / Real.sqrt (metricScalarAt g y) ≤ 14 / Real.sqrt (metricScalarAt g x) := by
    apply (div_le_div_iff₀ (Real.sqrt_pos.mpr nk₁.Q_pos) (Real.sqrt_pos.mpr nk₀.Q_pos)).mpr
    linarith
  have hother := (nk₁.central_sphere_subset_closedBall hz₁).trans (ENNReal.ofReal_le_ofReal hdiv)
  rw [riemannianEDistOf_comm g y z] at hother
  have hh := (riemannianEDistOf_triangle g x z y).trans
    (add_le_add (nk₀.central_sphere_subset_closedBall hz₀) hother)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← add_div] at hh
  norm_num only at hh
  exact (not_lt_of_ge hh) hfar

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.disjoint_central_spheres_of_edist_gt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.disjoint_central_spheres_of_edist_gt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.disjoint_central_spheres_of_edist_gt ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.disjoint_central_spheres_of_edist_gt

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
