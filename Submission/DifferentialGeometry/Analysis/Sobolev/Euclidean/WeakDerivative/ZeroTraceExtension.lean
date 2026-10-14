import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.WitnessCongruence
import Submission.DifferentialGeometry.External.DeGiorgi.BallExtension.RoughInput

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped _root_.Topology _root_.ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} [NeZero d] {ι : Type*}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ ι

theorem exists_weak_extension_of_memW01p_sub
    {Ω U : Set E} (hΩ : IsOpen Ω) (hU : IsOpen U)
    {w q : E → F} (hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => w x i) Ω)
    (hqw : ∀ i, DeGiorgi.MemW01p 2 (fun x => q x i - w x i) U) :
    ∃ (v : E → F), Nonempty (∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) Ω) ∧
      EqOn v q U ∧ _root_.Set.EqOn v w Uᶜ := by
  classical
  have hz (i : ι) : DeGiorgi.MemW01p 2 (U.indicator (fun x => q x i - w x i)) univ := by
    simpa only [ENNReal.ofReal_ofNat] using
      DeGiorgi.zeroExtend_memW01p_p hU (by norm_num : (1 : ℝ) < 2)
        (by simpa only [ENNReal.ofReal_ofNat] using hqw i)
  let hd (i : ι) := DeGiorgi.MemW1p.someWitness (hz i).memW1p
  let v : E → F := fun x => WithLp.toLp 2 fun i =>
    w x i + U.indicator (fun y => q y i - w y i) x
  let hv (i : ι) : DeGiorgi.MemW1pWitness 2 (fun x => v x i) Ω :=
    (hw i).add (DeGiorgi.MemW1pWitness.restrict hΩ (_root_.Set.subset_univ _) (hd i))
  refine ⟨v, ⟨hv⟩, ?_, ?_⟩
  · intro x hx
    ext i
    change w x i + U.indicator (fun y => q y i - w y i) x = q x i
    rw [_root_.Set.indicator_of_mem hx]
    ring
  · intro x hx
    ext i
    change w x i + U.indicator (fun y => q y i - w y i) x = w x i
    rw [_root_.Set.indicator_of_notMem hx, add_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_weak_extension_of_memW01p_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_weak_extension_of_memW01p_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_weak_extension_of_memW01p_sub ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_weak_extension_of_memW01p_sub

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end
