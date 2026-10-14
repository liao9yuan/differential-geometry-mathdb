import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryRestriction
import Mathlib.Analysis.Calculus.FDeriv.Extend

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private theorem endpoint_derivatives_of_continuous
    {a b : ℝ} (hab : a < b) {f F : ℝ → ℝ}
    (hf : ContinuousOn f (_root_.Set.Icc a b)) (hF : ContinuousOn F (_root_.Set.Icc a b))
    (hderiv : ∀ t ∈ _root_.Set.Ioo a b, HasDerivWithinAt f (F t) (_root_.Set.Icc a b) t) :
    HasDerivWithinAt f (F a) (_root_.Set.Ici a) a ∧ HasDerivWithinAt f (F b) (_root_.Set.Iic b) b := by
  have hd (t : ℝ) (ht : t ∈ _root_.Set.Ioo a b) : HasDerivAt f (F t) t :=
    (hderiv t ht).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hdiff : DifferentiableOn ℝ f (_root_.Set.Ioo a b) :=
    fun t ht => (hd t ht).differentiableAt.differentiableWithinAt
  constructor
  · apply hasDerivWithinAt_Ici_of_tendsto_deriv hdiff
      ((hf a ⟨le_rfl, hab.le⟩).mono _root_.Set.Ioo_subset_Icc_self) (Ioo_mem_nhdsGT hab)
    have hlim : ContinuousWithinAt F (_root_.Set.Ici a) a :=
      (continuousWithinAt_Icc_iff_Ici hab).mp (hF a ⟨le_rfl, hab.le⟩)
    apply (hlim.mono _root_.Set.Ioi_subset_Ici_self).congr'
    filter_upwards [Ioo_mem_nhdsGT hab] with t ht
    exact (hd t ht).deriv.symm
  · apply hasDerivWithinAt_Iic_of_tendsto_deriv hdiff
      ((hf b ⟨hab.le, le_rfl⟩).mono _root_.Set.Ioo_subset_Icc_self) (Ioo_mem_nhdsLT hab)
    have hlim : ContinuousWithinAt F (_root_.Set.Iic b) b :=
      (continuousWithinAt_Icc_iff_Iic hab).mp (hF b ⟨hab.le, le_rfl⟩)
    apply (hlim.mono _root_.Set.Iio_subset_Iic_self).congr'
    filter_upwards [Ioo_mem_nhdsLT hab] with t ht
    exact (hd t ht).deriv.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endpoint_derivatives_of_continuous
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.endpoint_derivatives_of_continuous target :: scope.openDecls } }

namespace OrientedThreeStage.ClosedSlab

variable {P : OrientedThreeStage.{u}} {u v : ℝ} (G : P.ClosedSlab u v)

theorem ricciAt_continuousOn (x : P.Carrier) (X Y : TangentSpace ThreeModel x) :
    ContinuousOn (fun t => G.flow.ricciAt t x (vec2 X Y)) (_root_.Set.Icc u v) := by
  have heval := tensor0SFamilyContinuousOnSet.eval_continuous
    (I := ThreeModel) (M := P.Carrier) (s := 2) G.equation.ricciCont
    (P := _root_.Set.Icc u v) (τ := fun t => t.1) (b := fun _ => x)
    continuous_subtype_val (fun t => t.2) continuous_const
    (v := fun i _ => vec2 X Y i) (fun _ => continuous_const)
  rw [continuousOn_iff_continuous_domRestrict]
  exact heval

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.ricciAt_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.ricciAt_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.ricciAt_continuousOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.ricciAt_continuousOn

theorem endpoint_derivatives (x : P.Carrier) (X Y : TangentSpace ThreeModel x) :
    HasDerivWithinAt (fun t => (G.flow.base.metric t).inner x X Y)
      (-2 * G.flow.ricciAt u x (vec2 X Y)) (_root_.Set.Ici u) u ∧
    HasDerivWithinAt (fun t => (G.flow.base.metric t).inner x X Y)
      (-2 * G.flow.ricciAt v x (vec2 X Y)) (_root_.Set.Iic v) v := by
  apply endpoint_derivatives_of_continuous G.lt
    (G.equation.smoothMetric.coeff_cont x X Y)
    (continuousOn_const.mul (G.ricciAt_continuousOn x X Y))
  intro t ht
  exact G.equation.equation ⟨t, ht⟩ x X Y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.endpoint_derivatives then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.endpoint_derivatives"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.endpoint_derivatives ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.endpoint_derivatives

def restrictClosed {a b : ℝ} (hua : u ≤ a) (hab : a < b) (hbv : b ≤ v) :
    P.ClosedSlab a b where
  lt := hab
  flow := G.flow.timeRestrict _
  equation := isSolutionOn_timeRestrict G.equation
    (fun _ ht => ⟨hua.trans ht.1, ht.2.trans hbv⟩)
    (fun _ ht => ⟨hua.trans_lt ht.1, ht.2.trans_le hbv⟩)
  smoothUpTo := G.smoothUpTo.mono (fun _ ht => ⟨hua.trans ht.1, ht.2.trans hbv⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.restrictClosed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.restrictClosed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.restrictClosed ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.restrictClosed

def restrictIncoming {a b : ℝ} (hua : u ≤ a) (hab : a < b) (hbv : b ≤ v) :
    P.IncomingSlab a b where
  lt := hab
  flow := G.flow.timeRestrict _
  equation := isSolutionOn_timeRestrict G.equation
    (fun _ ht => ⟨hua.trans ht.1, ht.2.le.trans hbv⟩)
    (fun _ ht => ⟨hua.trans_lt ht.1, ht.2.trans_le hbv⟩)
  smoothUpTo := G.smoothUpTo.mono (fun _ ht => ⟨hua.trans ht.1, ht.2.le.trans hbv⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.restrictIncoming then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.restrictIncoming"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.restrictIncoming ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.restrictIncoming

end OrientedThreeStage.ClosedSlab

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
