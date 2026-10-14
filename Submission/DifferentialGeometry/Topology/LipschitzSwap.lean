import Submission.DifferentialGeometry.Topology.LocallyLipschitzOperations

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


open _root_.Filter _root_.Set
open scoped _root_.Topology

namespace LocallyLipschitzOn
open _root_.LocallyLipschitzOn

variable {X Y Z : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
  [PseudoEMetricSpace Z]

open _root_.LocallyLipschitzOn in
theorem comp_swap {s : Set X} {t : Set Y} {f : X × Y → Z}
    (hf : LocallyLipschitzOn (s ×ˢ t) f) :
    LocallyLipschitzOn (t ×ˢ s) (fun p : Y × X => f (p.2, p.1)) := by
  have hswap : LocallyLipschitzOn (t ×ˢ s) (Prod.swap : Y × X → X × Y) :=
    (LipschitzWith.prod_snd.prodMk LipschitzWith.prod_fst).locallyLipschitz.locallyLipschitzOn
  exact hf.comp hswap (fun _ hp => ⟨hp.2, hp.1⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LocallyLipschitzOn.comp_swap then
    throwError "Refusing to shadow existing declaration LocallyLipschitzOn.comp_swap"
  Lean.modifyEnv fun env => Lean.addAlias env `LocallyLipschitzOn.comp_swap ``Submission.LocallyLipschitzOn.comp_swap

end LocallyLipschitzOn
