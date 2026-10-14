import Mathlib.Analysis.SpecialFunctions.PolarCoord

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.MeasureTheory _root_.Set _root_.Filter

namespace DifferentialGeometry.Topology

theorem ae_mem_complex_slitPlane : ∀ᵐ z : ℂ ∂volume, z ∈ Complex.slitPlane := by
  have hslit :=
    Complex.volume_preserving_equiv_real_prod.quasiMeasurePreserving.preimage_ae_eq
      polarCoord_source_ae_eq_univ
  filter_upwards [hslit] with z hz
  have hm := hz.mpr (_root_.Set.mem_univ z)
  change 0 < z.re ∨ z.im ≠ 0 at hm
  exact hm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ae_mem_complex_slitPlane then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ae_mem_complex_slitPlane"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ae_mem_complex_slitPlane ``Submission.DifferentialGeometry.Topology.ae_mem_complex_slitPlane

end DifferentialGeometry.Topology
