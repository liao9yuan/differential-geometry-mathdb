import Submission.DifferentialGeometry.External.DeGiorgi.SobolevSpace.Witnesses
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.MeasureTheory
open scoped _root_.ENNReal

namespace DeGiorgi

variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

def MemW1pWitness.congr
    {p : ℝ≥0∞} {Ω : Set V} {u v : V → ℝ}
    (hu : MemW1pWitness p u Ω) (huv : u =ᵐ[volume.restrict Ω] v) :
    MemW1pWitness p v Ω where
  memLp := MemLp.ae_eq huv hu.memLp
  weakGrad := hu.weakGrad
  weakGrad_component_memLp := hu.weakGrad_component_memLp
  isWeakGrad := fun j => (hu.isWeakGrad j).congr_ae huv Filter.EventuallyEq.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.MemW1pWitness.congr then
    throwError "Refusing to shadow existing declaration DeGiorgi.MemW1pWitness.congr"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.MemW1pWitness.congr ``Submission.DeGiorgi.MemW1pWitness.congr

theorem MemW1pWitness.congr_weakGrad
    {p : ℝ≥0∞} {Ω : Set V} {u v : V → ℝ}
    (hu : MemW1pWitness p u Ω) (huv : u =ᵐ[volume.restrict Ω] v) :
    (hu.congr huv).weakGrad = hu.weakGrad := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.MemW1pWitness.congr_weakGrad then
    throwError "Refusing to shadow existing declaration DeGiorgi.MemW1pWitness.congr_weakGrad"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.MemW1pWitness.congr_weakGrad ``Submission.DeGiorgi.MemW1pWitness.congr_weakGrad

end DeGiorgi
