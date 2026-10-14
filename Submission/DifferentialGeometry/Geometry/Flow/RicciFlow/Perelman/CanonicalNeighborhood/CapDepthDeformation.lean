import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalDiffeomorphTransport
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapCollarIsotopy

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

theorem LocalCap.exists_strict_tube_depth [PreconnectedSpace M]
    {S : SolutionOn (I := I3) (M := M) ancientTimeInterval} (hS : IsSolutionOn S)
    {eps alpha : ℝ} {x : M} {U : Set M} (cap : LocalCap S eps x 0 U)
    (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11)
    (heps : eps < neckModelTolerance alpha)
    (g : SmoothRiemannianMetric I3 M) {r : ℝ}
    (hdepth : ∀ y ∈ frontier cap.core.carrier, r ≤ metricDistance g x y) :
    ∃ cap' : LocalCap S (2 * alpha) x 0 U, ∃ r' : ℝ, r < r' ∧
      ∀ y ∈ cap'.tube, r' ≤ metricDistance g x y := by
  obtain ⟨F, hF, _hFi, hF0, hFx, hFU, hstrict, _hsupport⟩ :=
    cap.exists_isotopy_with_strict_tube_depth g hdepth
  let τ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hτ : _root_.Filter.Tendsto τ _root_.Filter.atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hcap := LocalCap.eventually_transport_of_diffeomorph_tendsto hS cap ha hsmall heps
    F hF hF0 τ hτ
  obtain ⟨n, hn⟩ := hcap.exists
  obtain ⟨cap', htube, _hcore, _hmap⟩ := hn
  have hτmem : τ n ∈ _root_.Set.Ioc (0 : ℝ) 1 := by
    dsimp only [τ]
    constructor
    · positivity
    · exact (div_le_one (by positivity)).mpr (le_add_of_nonneg_left (Nat.cast_nonneg n))
  obtain ⟨r', hrr', hdist⟩ := hstrict (τ n) hτmem
  have hout : ∃ cap'' : LocalCap S (2 * alpha) (F (τ n) x) 0 (F (τ n) '' U),
      ∃ r' : ℝ, r < r' ∧ ∀ y ∈ cap''.tube, r' ≤ metricDistance g x y := by
    refine ⟨cap', r', hrr', ?_⟩
    intro y hy
    exact hdist y (htube ▸ hy)
  erw [(hFx (τ n)).1, (hFU (τ n)).1] at hout
  exact hout

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.exists_strict_tube_depth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.exists_strict_tube_depth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.exists_strict_tube_depth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.exists_strict_tube_depth

theorem CanonicalWitness.exists_cap_with_strict_depth [PreconnectedSpace M]
    {S : SolutionOn (I := I3) (M := M) ancientTimeInterval} (hS : IsSolutionOn S)
    {eps alpha C1 C2 : ℝ} {x : M} (K : CanonicalWitness S eps C1 C2 x 0)
    (cap : LocalCap S eps x 0 K.domain.carrier)
    (hcap : ∃ depth, K.alternative = CanonicalAlternative.cap cap depth)
    (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11)
    (heps : eps < neckModelTolerance alpha) :
    ∃ K' : CanonicalWitness S (2 * alpha) C1 C2 x 0,
      K'.domain = K.domain ∧ K'.radius = K.radius ∧
      ∃ cap' : LocalCap S (2 * alpha) x 0 K'.domain.carrier, ∃ depth,
        K'.alternative = CanonicalAlternative.cap cap' depth ∧
        ∀ y ∈ cap'.tube,
          10000 / Real.sqrt (S.scalar 0 x) < metricDistance (S.base.metric 0) x y := by
  obtain ⟨depth, heq⟩ := hcap
  have hfrontier : ∀ y ∈ frontier cap.core.carrier,
      10000 / Real.sqrt (S.scalar 0 x) ≤ metricDistance (S.base.metric 0) x y := by
    intro y hy
    rw [← cap.overlap_eq] at hy
    exact depth y hy.2
  obtain ⟨cap', r', hrr', hdepth⟩ := cap.exists_strict_tube_depth hS ha hsmall heps
    (S.base.metric 0) hfrontier
  have hdeep : ∀ y ∈ cap'.tube,
      10000 / Real.sqrt (S.scalar 0 x) ≤ metricDistance (S.base.metric 0) x y :=
    fun y hy => hrr'.le.trans (hdepth y hy)
  have hv : K.alternative.requiresVolume := by rw [heq]; trivial
  let K' : CanonicalWitness S (2 * alpha) C1 C2 x 0 :=
    { K with
      eps_pos := by positivity
      eps_lt_one := by linarith
      alternative := CanonicalAlternative.cap cap' hdeep
      volume := fun _ => K.volume hv }
  exact ⟨K', rfl, rfl, cap', hdeep, rfl, fun y hy => hrr'.trans_le (hdepth y hy)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.exists_cap_with_strict_depth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.exists_cap_with_strict_depth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.exists_cap_with_strict_depth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CanonicalWitness.exists_cap_with_strict_depth

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
