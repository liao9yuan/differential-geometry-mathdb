import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Defs
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.W.Potential.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Entropy
open scoped _root_.ContDiff

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}

theorem perelmanPotential_redDensity
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x : M)
    {tau : ℝ} (htau : 0 < tau) :
    perelmanPotential (Module.finrank ℝ E) tau (fun y => redDensity S T x y tau) =
      fun y => redLength S T x y tau := by
  funext y
  dsimp only [perelmanPotential, redDensity]
  rw [Real.log_div (Real.exp_ne_zero _)
    (prefactor_pos (Module.finrank ℝ E) htau).ne']
  simp only [Real.log_exp]
  rw [log_prefactor (Module.finrank ℝ E) htau,
    Real.log_mul (by positivity : (4 * Real.pi : ℝ) ≠ 0) htau.ne']
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.perelmanPotential_redDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.perelmanPotential_redDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.perelmanPotential_redDensity ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.perelmanPotential_redDensity

theorem redDensity_eq_perelmanDensity
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x : M)
    {tau : ℝ} (htau : 0 < tau) :
    (fun y => redDensity S T x y tau) =
      perelmanDensity (Module.finrank ℝ E) tau (fun y => redLength S T x y tau) := by
  rw [← perelmanPotential_redDensity S T x htau]
  exact (density_potential (Module.finrank ℝ E)
    (fun y => redDensity S T x y tau) htau (fun _ => Real.exp_pos _)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.redDensity_eq_perelmanDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.redDensity_eq_perelmanDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.redDensity_eq_perelmanDensity ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.redDensity_eq_perelmanDensity

end DifferentialGeometry.PDE.RicciFlow.Perelman
