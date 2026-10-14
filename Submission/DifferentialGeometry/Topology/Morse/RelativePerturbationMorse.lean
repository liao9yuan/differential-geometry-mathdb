import Submission.DifferentialGeometry.Topology.Morse.RelativePerturbationPositive
import Submission.DifferentialGeometry.Topology.Morse.Defs
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Filter _root_.Function
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
open _root_.Submission.DifferentialGeometry.Topology.Morse
namespace DifferentialGeometry.Morse
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]


theorem associated_chartHessianAt_eq {g : E → ℝ} {x : E} (hg : ContDiffAt ℝ 2 g x) :
    QuadraticMap.associated (R := ℝ) (chartHessianAt g x) = chartHessianBilinAt g x := by
  apply QuadraticMap.associated_left_inverse
  intro v w
  exact hg.isSymmSndFDerivAt (by norm_num) v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.associated_chartHessianAt_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.associated_chartHessianAt_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.associated_chartHessianAt_eq ``Submission.DifferentialGeometry.Morse.associated_chartHessianAt_eq


theorem separatingLeft_chartHessianAt_iff {g : E → ℝ} {x : E} (hg : ContDiffAt ℝ 2 g x) :
    (QuadraticMap.associated (R := ℝ) (chartHessianAt g x)).SeparatingLeft ↔
      Injective (fderiv ℝ (fderiv ℝ g) x) := by
  rw [associated_chartHessianAt_eq hg]
  constructor
  · intro h v w hvw
    apply sub_eq_zero.mp
    apply h
    intro z
    change (fderiv ℝ (fderiv ℝ g) x) (v - w) z = 0
    rw [map_sub, hvw, sub_self, zero_apply]
  · intro h v hv
    apply h
    apply ContinuousLinearMap.ext
    intro w
    have hw : (fderiv ℝ (fderiv ℝ g) x) v w = 0 := hv w
    simpa only [map_zero, zero_apply] using hw

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.separatingLeft_chartHessianAt_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.separatingLeft_chartHessianAt_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.separatingLeft_chartHessianAt_iff ``Submission.DifferentialGeometry.Morse.separatingLeft_chartHessianAt_iff

variable {H M : Type} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]


theorem isNondegenerateCriticalPointAt_of_bijective_hessian {f : M → ℝ} {x : M}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hx : I.IsInteriorPoint x)
    (hcrit : mfderiv I 𝓘(ℝ, ℝ) f x = 0)
    (hess : _root_.Function.Bijective (fderiv ℝ (fderiv ℝ (fun z => f ((extChartAt I x).symm z)))
      (extChartAt I x x))) : IsNondegenerateCriticalPointAt I f x := by
  refine ⟨hcrit,?_⟩
  apply (separatingLeft_chartHessianAt_iff _).mpr hess.1
  let c := DifferentialGeometry.Manifold.interiorChart I ∞ x
  have hc : x ∈ c.source := (DifferentialGeometry.Manifold.mem_interiorChart_source_iff I ∞ x).mpr hx
  exact (((hf.comp_contMDiffOn c.symm.contMDiffOn).contMDiffAt
    (c.open_target.mem_nhds (c.map_source hc))).contDiffAt).of_le
      (show (2 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.isNondegenerateCriticalPointAt_of_bijective_hessian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.isNondegenerateCriticalPointAt_of_bijective_hessian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.isNondegenerateCriticalPointAt_of_bijective_hessian ``Submission.DifferentialGeometry.Morse.isNondegenerateCriticalPointAt_of_bijective_hessian

variable [FiniteDimensional ℝ E] [T2Space M]


theorem exists_positive_relative_morse_on_isCompact {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {K U S : Set M}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (hKI : ∀ x ∈ K, I.IsInteriorPoint x)
    (hUS : U ⊆ S) (hpos : ∀ x ∈ S, 0 < f x) :
    ∃ g : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ g ∧
      (∃ N : Set M, IsOpen N ∧ Uᶜ ⊆ N ∧ _root_.Set.EqOn g f N) ∧
      (∀ x ∈ S, 0 < g x) ∧ ∀ x ∈ K, IsCriticalPointAt I g x →
        IsNondegenerateCriticalPointAt I g x := by
  obtain ⟨g,hg,hfix,hpositive,hreg⟩ :=
    exists_positive_relative_nondegenerate_perturbation hf hK hU hKU hKI hUS hpos
  exact ⟨g,hg,hfix,hpositive,fun x hx hc =>
    isNondegenerateCriticalPointAt_of_bijective_hessian hg (hKI x hx) hc (hreg x hx hc)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.exists_positive_relative_morse_on_isCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.exists_positive_relative_morse_on_isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.exists_positive_relative_morse_on_isCompact ``Submission.DifferentialGeometry.Morse.exists_positive_relative_morse_on_isCompact

end DifferentialGeometry.Morse
