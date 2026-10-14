import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.IntervalTransport
import Mathlib.Tactic.Linarith

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage

universe u
variable {P : OrientedThreeStage.{u}}

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.instIsManifoldRealThreeSpaceThreeModelOfNatWithTopENatCarrier : IsManifold ThreeModel 1 P.Carrier :=
  IsManifold.of_le (I := ThreeModel) (M := P.Carrier) (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.instIsManifoldRealThreeSpaceThreeModelOfNatWithTopENatCarrier
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.instIsManifoldRealThreeSpaceThreeModelOfNatWithTopENatCarrier target :: scope.openDecls } }

theorem MetricSmoothUpTo.timeTranslate {g : ℝ → P.Metric} {J J' : Set ℝ}
    (hg : P.MetricSmoothUpTo g J) (a : ℝ)
    (hJ : _root_.Set.MapsTo (fun t => t - a) J' J) :
    P.MetricSmoothUpTo (fun t => g (t - a)) J' := by
  intro p t ht
  obtain ⟨U, hU, hp, hUb, V, hV, htV, A, hA, hEq⟩ := hg p (t - a) (hJ ht)
  refine ⟨U, hU, hp, hUb, (fun s : ℝ => s - a) ⁻¹' V,
    hV.preimage (continuous_id.sub continuous_const), htV,
    (fun z i j => A (z.1 - a, z.2) i j), ?_, ?_⟩
  · intro i j
    have hmap : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) (𝓘(ℝ, ℝ).prod ThreeModel) ∞
        (fun z : ℝ × P.Carrier => (z.1 - a, z.2)) :=
      (contMDiff_fst.sub contMDiff_const).prodMk contMDiff_snd
    exact (hA i j).comp hmap.contMDiffOn (fun z hz => ⟨hz.1, hz.2⟩)
  · intro s hs x hx i j
    exact hEq (s - a) ⟨hs.1, hJ hs.2⟩ x hx i j

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.MetricSmoothUpTo
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.MetricSmoothUpTo.timeTranslate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.MetricSmoothUpTo.timeTranslate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.MetricSmoothUpTo.timeTranslate ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.MetricSmoothUpTo.timeTranslate

private def translatedFlow {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := P.Carrier) D)
    (a : ℝ) (D' : RealTimeInterval) :
    SolutionOn (I := ThreeModel) (M := P.Carrier) D' :=
  (S.timeShift (-a)).cast D'

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.translatedFlow
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.translatedFlow target :: scope.openDecls } }

private theorem translatedFlow_metric_eq {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := P.Carrier) D)
    (a : ℝ) (D' : RealTimeInterval) :
    (translatedFlow S a D').base.metric = fun t => S.base.metric (t - a) := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.translatedFlow_metric_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.translatedFlow_metric_eq target :: scope.openDecls } }

private theorem translatedFlow_equation {D D' : RealTimeInterval}
    {S : SolutionOn (I := ThreeModel) (M := P.Carrier) D}
    (hS : IsSolutionOn S) (a : ℝ)
    (hcarrier : D'.carrier = {t | t - a ∈ D.carrier})
    (hregular : D'.regular = {t | t - a ∈ D.regular}) :
    IsSolutionOn (translatedFlow S a D') := by
  apply isSolutionOn_cast (isSolutionOn_timeShift hS (-a))
  · rw [hcarrier]
    ext t
    simp only [RealTimeInterval.timeShift_carrier, _root_.Set.mem_ofPred_eq, sub_eq_add_neg]
  · rw [hregular]
    ext t
    simp only [RealTimeInterval.timeShift_regular, _root_.Set.mem_ofPred_eq, sub_eq_add_neg]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.translatedFlow_equation
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.translatedFlow_equation target :: scope.openDecls } }

private theorem preimage_Ico_translate (s e a : ℝ) :
    Ico (s + a) (e + a) = {t | t - a ∈ _root_.Set.Ico s e} := by
  ext t
  simp only [_root_.Set.mem_Ico, _root_.Set.mem_ofPred_eq]
  constructor <;> intro ht <;> constructor <;> linarith [ht.1, ht.2]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.preimage_Ico_translate
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.preimage_Ico_translate target :: scope.openDecls } }

private theorem preimage_Ioo_translate (s e a : ℝ) :
    Ioo (s + a) (e + a) = {t | t - a ∈ _root_.Set.Ioo s e} := by
  ext t
  simp only [_root_.Set.mem_Ioo, _root_.Set.mem_ofPred_eq]
  constructor <;> intro ht <;> constructor <;> linarith [ht.1, ht.2]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.preimage_Ioo_translate
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.preimage_Ioo_translate target :: scope.openDecls } }

private theorem preimage_Icc_translate (s e a : ℝ) :
    Icc (s + a) (e + a) = {t | t - a ∈ _root_.Set.Icc s e} := by
  ext t
  simp only [_root_.Set.mem_Icc, _root_.Set.mem_ofPred_eq]
  constructor <;> intro ht <;> constructor <;> linarith [ht.1, ht.2]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.preimage_Icc_translate
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.preimage_Icc_translate target :: scope.openDecls } }

def IncomingSlab.timeTranslate {s e : ℝ} (G : P.IncomingSlab s e) (a : ℝ) :
    P.IncomingSlab (s + a) (e + a) where
  lt := add_lt_add_left G.lt a
  flow := translatedFlow G.flow a _
  equation := translatedFlow_equation G.equation a
    (preimage_Ico_translate s e a) (preimage_Ioo_translate s e a)
  smoothUpTo := by
    simpa only [translatedFlow_metric_eq] using G.smoothUpTo.timeTranslate a
      (show _root_.Set.MapsTo (fun t => t - a) (_root_.Set.Ico (s + a) (e + a)) (_root_.Set.Ico s e) from
        fun t ht => by rwa [preimage_Ico_translate s e a] at ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.timeTranslate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.timeTranslate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.timeTranslate ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.timeTranslate

def ClosedSlab.timeTranslate {s e : ℝ} (G : P.ClosedSlab s e) (a : ℝ) :
    P.ClosedSlab (s + a) (e + a) where
  lt := add_lt_add_left G.lt a
  flow := translatedFlow G.flow a _
  equation := translatedFlow_equation G.equation a
    (preimage_Icc_translate s e a) (preimage_Ioo_translate s e a)
  smoothUpTo := by
    simpa only [translatedFlow_metric_eq] using G.smoothUpTo.timeTranslate a
      (show _root_.Set.MapsTo (fun t => t - a) (_root_.Set.Icc (s + a) (e + a)) (_root_.Set.Icc s e) from
        fun t ht => by rwa [preimage_Icc_translate s e a] at ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.timeTranslate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.timeTranslate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.timeTranslate ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.timeTranslate

@[simp] theorem IncomingSlab.timeTranslate_metric {s e : ℝ}
    (G : P.IncomingSlab s e) (a t : ℝ) :
    (G.timeTranslate a).flow.base.metric t = G.flow.base.metric (t - a) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.timeTranslate_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.timeTranslate_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.timeTranslate_metric ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.timeTranslate_metric

@[simp] theorem ClosedSlab.timeTranslate_metric {s e : ℝ}
    (G : P.ClosedSlab s e) (a t : ℝ) :
    (G.timeTranslate a).flow.base.metric t = G.flow.base.metric (t - a) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.timeTranslate_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.timeTranslate_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.timeTranslate_metric ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.timeTranslate_metric

theorem IncomingSlab.timeTranslate_metric_add {s e : ℝ}
    (G : P.IncomingSlab s e) (a t : ℝ) :
    (G.timeTranslate a).flow.base.metric (t + a) = G.flow.base.metric t := by
  rw [timeTranslate_metric, add_sub_cancel_right]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.timeTranslate_metric_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.timeTranslate_metric_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.timeTranslate_metric_add ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.timeTranslate_metric_add

theorem ClosedSlab.timeTranslate_metric_add {s e : ℝ}
    (G : P.ClosedSlab s e) (a t : ℝ) :
    (G.timeTranslate a).flow.base.metric (t + a) = G.flow.base.metric t := by
  rw [timeTranslate_metric, add_sub_cancel_right]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.timeTranslate_metric_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.timeTranslate_metric_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.timeTranslate_metric_add ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.timeTranslate_metric_add

theorem IncomingSlab.timeTranslate_initial_metric {s e : ℝ}
    (G : P.IncomingSlab s e) (a : ℝ) :
    (G.timeTranslate a).flow.base.metric (s + a) = G.flow.base.metric s :=
  G.timeTranslate_metric_add a s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.timeTranslate_initial_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.timeTranslate_initial_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.timeTranslate_initial_metric ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.timeTranslate_initial_metric

theorem ClosedSlab.timeTranslate_initial_metric {s e : ℝ}
    (G : P.ClosedSlab s e) (a : ℝ) :
    (G.timeTranslate a).flow.base.metric (s + a) = G.flow.base.metric s :=
  G.timeTranslate_metric_add a s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.timeTranslate_initial_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.timeTranslate_initial_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.timeTranslate_initial_metric ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.timeTranslate_initial_metric

@[simp] theorem IncomingSlab.timeTranslate_riemannNorm {s e : ℝ}
    (G : P.IncomingSlab s e) (a t : ℝ) (x : P.Carrier) :
    (G.timeTranslate a).riemannNorm t x = G.riemannNorm (t - a) x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.timeTranslate_riemannNorm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.timeTranslate_riemannNorm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.timeTranslate_riemannNorm ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.timeTranslate_riemannNorm

theorem IncomingSlab.timeTranslate_singularEndpoint_iff {s e : ℝ}
    (G : P.IncomingSlab s e) (a : ℝ) :
    (G.timeTranslate a).SingularEndpoint ↔ G.SingularEndpoint := by
  constructor
  · intro h L hL d hd
    have hd' : d + a ∈ _root_.Set.Ico (s + a) (e + a) :=
      ⟨add_le_add_left hd.1 a, add_lt_add_left hd.2 a⟩
    obtain ⟨t, ht, x, hx⟩ := h L hL (d + a) hd'
    refine ⟨t - a, ⟨?_, ?_⟩, x, ?_⟩
    · linarith [ht.1]
    · linarith [ht.2]
    · simpa only [timeTranslate_riemannNorm] using hx
  · intro h L hL d hd
    have hd' : d - a ∈ _root_.Set.Ico s e := by
      constructor <;> linarith [hd.1, hd.2]
    obtain ⟨t, ht, x, hx⟩ := h L hL (d - a) hd'
    refine ⟨t + a, ⟨?_, ?_⟩, x, ?_⟩
    · linarith [ht.1]
    · linarith [ht.2]
    · simpa only [timeTranslate_riemannNorm, add_sub_cancel_right] using hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.timeTranslate_singularEndpoint_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.timeTranslate_singularEndpoint_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.timeTranslate_singularEndpoint_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.timeTranslate_singularEndpoint_iff

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage
