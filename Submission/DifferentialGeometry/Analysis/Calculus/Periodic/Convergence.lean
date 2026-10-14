import Mathlib.Algebra.Field.Periodic
import Mathlib.Topology.MetricSpace.UniformConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Filter _root_.Set

namespace Function.Periodic
open _root_.Function _root_.Function.Periodic

open _root_.Function _root_.Function.Periodic in
theorem tendstoUniformlyOn_comp_of_Icc
    {ι P T Y : Type*} [PseudoMetricSpace Y] {l : Filter ι}
    {f : ι → ℝ → T → Y} {fInf : ℝ → T → Y}
    {J : Set T} {K : Set P} {c : ℝ} (hc : 0 < c)
    (hper : ∀ᶠ i in l, ∀ t ∈ J, Function.Periodic (fun x => f i x t) c)
    (hperInf : ∀ t ∈ J, Function.Periodic (fun x => fInf x t) c)
    (hf : TendstoUniformlyOn (fun i (q : ℝ × T) => f i q.1 q.2)
      (fun q : ℝ × T => fInf q.1 q.2) l (_root_.Set.Icc (0 : ℝ) c ×ˢ J))
    (x : P → T → ℝ) :
    TendstoUniformlyOn (fun i (q : P × T) => f i (x q.1 q.2) q.2)
      (fun q : P × T => fInf (x q.1 q.2) q.2) l (K ×ˢ J) := by
  rw [Metric.tendstoUniformlyOn_iff] at hf ⊢
  intro ε hε
  filter_upwards [hper, hf ε hε] with i hpi hi
  intro q hq
  have hpair : Function.Periodic (fun y => (fInf y q.2, f i y q.2)) c := by
    intro y
    exact Prod.ext (hperInf q.2 hq.2 y) (hpi q.2 hq.2 y)
  obtain ⟨y, hy, heq⟩ := hpair.exists_mem_Ico₀ hc (x q.1 q.2)
  rw [(Prod.mk.inj heq).1, (Prod.mk.inj heq).2]
  exact hi (y, q.2) ⟨⟨hy.1, hy.2.le⟩, hq.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Function.Periodic.tendstoUniformlyOn_comp_of_Icc then
    throwError "Refusing to shadow existing declaration Function.Periodic.tendstoUniformlyOn_comp_of_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `Function.Periodic.tendstoUniformlyOn_comp_of_Icc ``Submission.Function.Periodic.tendstoUniformlyOn_comp_of_Icc

end Function.Periodic
