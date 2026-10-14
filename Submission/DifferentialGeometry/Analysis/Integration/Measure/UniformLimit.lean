import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.MeasureTheory.Measure.OpenPos

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.Set _root_.MeasureTheory
open scoped _root_.Topology

namespace MeasureTheory
open _root_.MeasureTheory

variable {X Y ι : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] {μ : Measure X} [μ.IsOpenPosMeasure]
  [UniformSpace Y] {l : Filter ι} {F : ι → X → Y} {f : X → Y}

open _root_.MeasureTheory in
theorem tendstoUniformly_of_ae_tendsto_of_equicontinuous
    (hF : Equicontinuous F) (hf : Continuous f)
    (hae : ∀ᵐ x ∂μ, _root_.Filter.Tendsto (fun i => F i x) l (𝓝 (f x))) :
    TendstoUniformly F f l := by
  have hclosed : IsClosed {x | _root_.Filter.Tendsto (fun i => F i x) l (𝓝 (f x))} :=
    hF.isClosed_setOfPred_tendsto hf
  have hdense : Dense {x | _root_.Filter.Tendsto (fun i => F i x) l (𝓝 (f x))} := Measure.dense_of_ae hae
  have hall : ∀ x, _root_.Filter.Tendsto (fun i => F i x) l (𝓝 (f x)) := by
    intro x
    exact hclosed.closure_subset (hdense x)
  have hpi : _root_.Filter.Tendsto F l (𝓝 f) := tendsto_pi_nhds.mpr hall
  exact UniformFun.tendsto_iff_tendstoUniformly.mp
    ((hF.tendsto_uniformFun_iff_pi l f).mpr hpi)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.tendstoUniformly_of_ae_tendsto_of_equicontinuous then
    throwError "Refusing to shadow existing declaration MeasureTheory.tendstoUniformly_of_ae_tendsto_of_equicontinuous"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.tendstoUniformly_of_ae_tendsto_of_equicontinuous ``Submission.MeasureTheory.tendstoUniformly_of_ae_tendsto_of_equicontinuous

end MeasureTheory

end
