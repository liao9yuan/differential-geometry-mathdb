import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.W.Potential.Defs
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set
open scoped _root_.Manifold _root_.ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Entropy
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H M : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

theorem contMDiffOn_perelmanPotential
    (n : ℕ) {r : ℕ∞} {s : Set (ℝ × M)} {u : ℝ → M → ℝ}
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) r (fun p : ℝ × M => u p.1 p.2) s)
    (htime : ∀ p ∈ s, 0 < p.1) (hpos : ∀ p ∈ s, 0 < u p.1 p.2) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) r
      (fun p : ℝ × M => perelmanPotential n p.1 (u p.1) p.2) s := by
  intro p hp
  have hbase : 0 < 4 * Real.pi * p.1 := mul_pos (mul_pos (by norm_num) Real.pi_pos) (htime p hp)
  have hbaseSmooth : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) r
      (fun q : ℝ × M => 4 * Real.pi * q.1) s p :=
    contMDiffWithinAt_const.mul contMDiffWithinAt_fst
  have hpf : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) r
      (fun q : ℝ × M => perelmanDensityPrefactor n q.1) s p :=
    (Real.contDiffAt_rpow_const_of_ne (p := -(n : ℝ) / 2) hbase.ne').comp_contMDiffWithinAt
      (f := fun q : ℝ × M => 4 * Real.pi * q.1) (x := p) hbaseSmooth
  have hq := (hu p hp).div₀ hpf (prefactor_pos n (htime p hp)).ne'
  have hl := (Real.contDiffAt_log.2
    (div_ne_zero (hpos p hp).ne' (prefactor_pos n (htime p hp)).ne')).comp_contMDiffWithinAt
      (f := fun q : ℝ × M => u q.1 q.2 / perelmanDensityPrefactor n q.1) (x := p) hq
  exact hl.neg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.contMDiffOn_perelmanPotential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.contMDiffOn_perelmanPotential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.contMDiffOn_perelmanPotential ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.contMDiffOn_perelmanPotential

end DifferentialGeometry.PDE.RicciFlow.Entropy
