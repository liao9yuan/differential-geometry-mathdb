import Submission.DifferentialGeometry.Geometry.Neck.SpatialBandEscape
import Submission.DifferentialGeometry.Topology.Compactness.SublevelEscape

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set _root_.Manifold _root_.Submission.Manifold _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [T2Space M] {g : SmoothRiemannianMetric I3 M} {eps : ℝ}

theorem tendsto_spatial_neck_center_scalar_atTop_of_midpoint_cocompact
    (p : ℕ → M) (neck : ∀ n, SpatialNeck g eps (p n))
    (hcompact : ∀ B : ℝ, IsCompact {x : M | metricScalarAt g x ≤ B})
    (hescape : _root_.Filter.Tendsto (fun n => (neck n).map ((neck n).center, 3 / 2))
      _root_.Filter.atTop (_root_.Filter.cocompact M)) :
    Tendsto (fun n => metricScalarAt g (p n)) _root_.Filter.atTop atTop := by
  have hmid : _root_.Filter.Tendsto (fun n => metricScalarAt g
      ((neck n).map ((neck n).center, 3 / 2))) _root_.Filter.atTop atTop :=
    (tendsto_atTop_of_isCompact_sublevel hcompact).comp hescape
  have hbound (n : ℕ) : metricScalarAt g ((neck n).map ((neck n).center, 3 / 2)) ≤
      (1 + 4323 * eps) * metricScalarAt g (p n) := by
    have hinv : (3 / 2 : ℝ) < eps⁻¹ :=
      (lt_inv_comm₀ (by norm_num) (neck n).eps_pos).mpr (by linarith [(neck n).eps_small])
    have hsrc : ((neck n).center, 3 / 2) ∈ _root_.Set.univ ×ˢ _root_.Set.Ioo (-eps⁻¹) eps⁻¹ :=
      ⟨mem_univ _, by constructor <;> linarith⟩
    exact ((neck n).scalar_bounds_on_image_window ⟨_, hsrc, rfl⟩).2
  apply tendsto_atTop.mpr
  intro B
  filter_upwards [hmid.eventually_ge_atTop ((1 + 4323 * eps) * B)] with n hn
  have hpos : 0 < 1 + 4323 * eps := by linarith [(neck n).eps_pos]
  exact (mul_le_mul_iff_right₀ hpos).mp (hn.trans (hbound n))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tendsto_spatial_neck_center_scalar_atTop_of_midpoint_cocompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tendsto_spatial_neck_center_scalar_atTop_of_midpoint_cocompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tendsto_spatial_neck_center_scalar_atTop_of_midpoint_cocompact ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tendsto_spatial_neck_center_scalar_atTop_of_midpoint_cocompact

theorem eventually_disjoint_spatial_neck_window_of_center_scalar_tendsto_atTop
    (hsmall : 4323 * eps < 1) (p : ℕ → M) (neck : ∀ n, SpatialNeck g eps (p n))
    (hscalar : _root_.Filter.Tendsto (fun n => metricScalarAt g (p n)) _root_.Filter.atTop _root_.Filter.atTop)
    {K : Set M} (hK : IsCompact K) :
    ∀ᶠ n in _root_.Filter.atTop, Disjoint K ((neck n).map '' (_root_.Set.univ ×ˢ _root_.Set.Ioo (-eps⁻¹) eps⁻¹)) := by
  obtain ⟨B, hB⟩ := hK.bddAbove_image (metricScalar_smooth g).continuous.continuousOn
  have hpos : 0 < 1 - 4323 * eps := by linarith
  filter_upwards [hscalar.eventually_ge_atTop ((B + 1) / (1 - 4323 * eps))] with n hn
  apply disjoint_left.mpr
  intro y hyK hy
  have hl := ((neck n).scalar_bounds_on_image_window hy).1
  have hlo : B + 1 ≤ (1 - 4323 * eps) * metricScalarAt g (p n) := by
    have h := (div_le_iff₀ hpos).mp hn
    simpa only [mul_comm] using h
  have hup := hB ⟨y, hyK, rfl⟩
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_disjoint_spatial_neck_window_of_center_scalar_tendsto_atTop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_disjoint_spatial_neck_window_of_center_scalar_tendsto_atTop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_disjoint_spatial_neck_window_of_center_scalar_tendsto_atTop ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_disjoint_spatial_neck_window_of_center_scalar_tendsto_atTop

theorem eventually_disjoint_spatial_neck_window_of_midpoint_avoids_earlier_band
    (heps : eps ≤ 1 / 156000) (p : ℕ → M) (neck : ∀ n, SpatialNeck g eps (p n))
    (hcompact : ∀ B : ℝ, IsCompact {x : M | metricScalarAt g x ≤ B})
    (havoid : ∀ i j : ℕ, i < j →
      (neck j).map ((neck j).center, 3 / 2) ∉
        (neck i).map '' (_root_.Set.univ ×ˢ _root_.Set.Icc (1 : ℝ) 2))
    {K : Set M} (hK : IsCompact K) :
    ∀ᶠ n in _root_.Filter.atTop, Disjoint K ((neck n).map '' (_root_.Set.univ ×ˢ _root_.Set.Ioo (-eps⁻¹) eps⁻¹)) := by
  apply eventually_disjoint_spatial_neck_window_of_center_scalar_tendsto_atTop
    (by linarith) p neck _ hK
  exact tendsto_spatial_neck_center_scalar_atTop_of_midpoint_cocompact p neck hcompact
    (tendsto_spatial_neck_midpoint_cocompact_of_avoids_earlier_band g heps p neck havoid)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_disjoint_spatial_neck_window_of_midpoint_avoids_earlier_band then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_disjoint_spatial_neck_window_of_midpoint_avoids_earlier_band"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_disjoint_spatial_neck_window_of_midpoint_avoids_earlier_band ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_disjoint_spatial_neck_window_of_midpoint_avoids_earlier_band

theorem eventually_disjoint_spatial_neck_central_band_of_midpoint_avoids_earlier_band
    (heps : eps ≤ 1 / 156000) (p : ℕ → M) (neck : ∀ n, SpatialNeck g eps (p n))
    (hcompact : ∀ B : ℝ, IsCompact {x : M | metricScalarAt g x ≤ B})
    (havoid : ∀ i j : ℕ, i < j →
      (neck j).map ((neck j).center, 3 / 2) ∉
        (neck i).map '' (_root_.Set.univ ×ˢ _root_.Set.Icc (1 : ℝ) 2))
    {K : Set M} (hK : IsCompact K) :
    ∀ᶠ n in _root_.Filter.atTop, Disjoint K ((neck n).map '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-4 : ℝ) 4)) := by
  filter_upwards [eventually_disjoint_spatial_neck_window_of_midpoint_avoids_earlier_band
    heps p neck hcompact havoid hK] with n hn
  apply hn.mono_right
  apply _root_.Set.image_mono
  rintro ⟨q, t⟩ ⟨hq, ht⟩
  have hinv : (4 : ℝ) < eps⁻¹ :=
    (lt_inv_comm₀ (by norm_num) (neck n).eps_pos).mpr (by linarith)
  exact ⟨hq, by constructor <;> linarith [ht.1, ht.2]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_disjoint_spatial_neck_central_band_of_midpoint_avoids_earlier_band then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_disjoint_spatial_neck_central_band_of_midpoint_avoids_earlier_band"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_disjoint_spatial_neck_central_band_of_midpoint_avoids_earlier_band ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_disjoint_spatial_neck_central_band_of_midpoint_avoids_earlier_band

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
