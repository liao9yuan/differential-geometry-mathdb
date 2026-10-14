import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornDefs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

private theorem clamp_gap_bound {r R s : ℝ} (hrR : r ≤ R) (hsR : s ≤ R) :
    |min s r - s| ≤ R - r := by
  by_cases hsr : s ≤ r
  · rw [min_eq_left hsr, sub_self, abs_zero]
    exact sub_nonneg.mpr hrR
  · rw [min_eq_right (not_le.mp hsr).le, abs_of_nonpos (by linarith : r - s ≤ 0)]
    linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.clamp_gap_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.clamp_gap_bound target :: scope.openDecls } }


theorem clamped_ray_parameter_mem {L r s : ℝ} (hL : 0 ≤ L) (hr : 0 < r) (hs : 0 ≤ s) :
    L * (_root_.Min.min s r / r) ∈ _root_.Set.Icc (0 : ℝ) L := by
  have hmin : 0 ≤ _root_.Min.min s r := le_min hs hr.le
  refine ⟨mul_nonneg hL (div_nonneg hmin hr.le), ?_⟩
  have hfrac : _root_.Min.min s r / r ≤ 1 := (div_le_one hr).mpr (min_le_right _ _)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hfrac hL

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.clamped_ray_parameter_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.clamped_ray_parameter_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.clamped_ray_parameter_mem ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.clamped_ray_parameter_mem


theorem clamped_ray_parameter_monotone {L r : ℝ} (hL : 0 ≤ L) (hr : 0 < r) :
    Monotone (fun s : ℝ => L * (_root_.Min.min s r / r)) := by
  intro s t hst
  exact mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (min_le_min_right r hst) hr.le) hL

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.clamped_ray_parameter_monotone then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.clamped_ray_parameter_monotone"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.clamped_ray_parameter_monotone ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.clamped_ray_parameter_monotone

theorem clamped_ray_parameter_error {L r R s : ℝ} (hr : 0 < r)
    (hrR : r ≤ R) (hs : s ∈ _root_.Set.Icc (0 : ℝ) R) :
    |L * (_root_.Min.min s r / r) - s| ≤ |L - r| + (R - r) := by
  have hfrac0 : 0 ≤ _root_.Min.min s r / r := div_nonneg (le_min hs.1 hr.le) hr.le
  have hfrac1 : _root_.Min.min s r / r ≤ 1 := (div_le_one hr).mpr (min_le_right _ _)
  have heq : L * (_root_.Min.min s r / r) - s = (L - r) * (_root_.Min.min s r / r) + (_root_.Min.min s r - s) := by
    field_simp [hr.ne']
    ring
  calc
    _ = |(L - r) * (_root_.Min.min s r / r) + (_root_.Min.min s r - s)| := congrArg abs heq
    _ ≤ |(L - r) * (_root_.Min.min s r / r)| + |_root_.Min.min s r - s| := abs_add_le _ _
    _ = |L - r| * (_root_.Min.min s r / r) + |_root_.Min.min s r - s| := by rw [abs_mul, abs_of_nonneg hfrac0]
    _ ≤ |L - r| + (R - r) := add_le_add
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hfrac1 (abs_nonneg (L - r)))
      (clamp_gap_bound hrR hs.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.clamped_ray_parameter_error then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.clamped_ray_parameter_error"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.clamped_ray_parameter_error ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.clamped_ray_parameter_error

variable {W : Type*} [MetricSpace W]

theorem EndRay.dist_lt_of_clamped_approximation {E : UniformSpace.Completion W}
    (a : EndRay E) {r R L eps : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hR : R ≤ a.length)
    (gamma : ℝ → W)
    (happrox : ∀ t ∈ _root_.Set.Ioc (0 : ℝ) r, _root_.Dist.dist (gamma (L * (t / r))) (a.point t) < eps)
    {s : ℝ} (hs : s ∈ _root_.Set.Ioc (0 : ℝ) R) :
    dist (gamma (L * (_root_.Min.min s r / r))) (a.point s) < eps + (R - r) := by
  have hm : _root_.Min.min s r ∈ _root_.Set.Ioc (0 : ℝ) r := ⟨lt_min hs.1 hr, min_le_right _ _⟩
  have hma : _root_.Min.min s r ∈ _root_.Set.Ioc (0 : ℝ) a.length := ⟨hm.1, hm.2.trans (hrR.trans hR)⟩
  have hsa : s ∈ _root_.Set.Ioc (0 : ℝ) a.length := ⟨hs.1, hs.2.trans hR⟩
  have hgap : _root_.Dist.dist (a.point (_root_.Min.min s r)) (a.point s) ≤ R - r := by
    rw [a.minimizing _ hma _ hsa]
    exact clamp_gap_bound hrR hs.2
  exact (dist_triangle _ (a.point (_root_.Min.min s r)) _).trans_lt
    (add_lt_add_of_lt_of_le (happrox _ hm) hgap)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndRay.dist_lt_of_clamped_approximation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndRay.dist_lt_of_clamped_approximation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndRay.dist_lt_of_clamped_approximation ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.EndRay.dist_lt_of_clamped_approximation

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
