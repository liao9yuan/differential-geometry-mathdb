import Submission.DifferentialGeometry.Geometry.Curvature.Metric.LeviCivita
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import Submission.DifferentialGeometry.Geometry.Metric.Family.TensorNorm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}

theorem IsSolutionOn.continuousOn_rmNormSq (hS : IsSolutionOn S) :
    ContinuousOn (fun p : ℝ × M =>
      normSq0S (S.base.metric p.1) p.2 4 (S.base.rm04 p.1 p.2))
      (D.carrier ×ˢ (_root_.Set.univ : Set M)) := by
  have hc := continuous_normSq0S_family S.base.metric (fun t x => S.base.rm04 t x)
    hS.smoothMetric.metricTensor_cont hS.rm04Cont
  rw [continuousOn_iff_continuous_domRestrict]
  have hm : Continuous (fun p : D.carrier ×ˢ (_root_.Set.univ : Set M) =>
      ((⟨p.1.1, p.2.1⟩ : D.carrier), p.1.2)) :=
    ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
      (continuous_snd.comp continuous_subtype_val)
  apply (hc.comp hm).congr
  intro p
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IsSolutionOn.continuousOn_rmNormSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IsSolutionOn.continuousOn_rmNormSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IsSolutionOn.continuousOn_rmNormSq ``Submission.DifferentialGeometry.PDE.RicciFlow.IsSolutionOn.continuousOn_rmNormSq

theorem IsSolutionOn.continuousOn_riemannNorm (hS : IsSolutionOn S) :
    ContinuousOn (fun p : ℝ × M =>
      Real.sqrt (normSq0S (S.base.metric p.1) p.2 4 (S.base.rm04 p.1 p.2)))
      (D.carrier ×ˢ (_root_.Set.univ : Set M)) :=
  hS.continuousOn_rmNormSq.sqrt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IsSolutionOn.continuousOn_riemannNorm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IsSolutionOn.continuousOn_riemannNorm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IsSolutionOn.continuousOn_riemannNorm ``Submission.DifferentialGeometry.PDE.RicciFlow.IsSolutionOn.continuousOn_riemannNorm

theorem IsSolutionOn.continuousOn_riemannNorm_time (hS : IsSolutionOn S) (x : M) :
    ContinuousOn (fun t : ℝ =>
      Real.sqrt (normSq0S (S.base.metric t) x 4 (S.base.rm04 t x))) D.carrier := by
  exact hS.continuousOn_riemannNorm.comp (f := fun t : ℝ => (t, x))
    (continuous_id.prodMk continuous_const).continuousOn (fun t ht => ⟨ht, _root_.Set.mem_univ x⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IsSolutionOn.continuousOn_riemannNorm_time then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IsSolutionOn.continuousOn_riemannNorm_time"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IsSolutionOn.continuousOn_riemannNorm_time ``Submission.DifferentialGeometry.PDE.RicciFlow.IsSolutionOn.continuousOn_riemannNorm_time

theorem IsSolutionOn.continuousOn_ricciAt {D : RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D} (hS : IsSolutionOn S)
    (x : M) (v w : TangentSpace I x) :
    ContinuousOn (fun t => S.ricciAt t x (vec2 v w)) D.carrier := by
  let K := D.carrier
  have hcont : Continuous (fun p : K =>
      (S.ricci p.1 x) (fun i : Fin 2 => if i = 0 then v else w)) := by
    have heval := tensor0SFamilyContinuousOnSet.eval_continuous hS.ricciCont
      (P := K) (τ := fun p : K => p.1) (b := fun _ : K => x)
      continuous_subtype_val (fun p => p.2) continuous_const
      (v := fun a : Fin 2 => fun _ : K => if a = 0 then v else w)
      (by
        intro a
        fin_cases a
        · simpa using (continuous_const : Continuous (fun _ : K =>
            (⟨x, v⟩ : TangentBundle I M)))
        · simpa using (continuous_const : Continuous (fun _ : K =>
            (⟨x, w⟩ : TangentBundle I M))))
    simpa [K, vec2] using heval
  rw [continuousOn_iff_continuous_domRestrict]
  exact hcont.congr fun _ => rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IsSolutionOn.continuousOn_ricciAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IsSolutionOn.continuousOn_ricciAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IsSolutionOn.continuousOn_ricciAt ``Submission.DifferentialGeometry.PDE.RicciFlow.IsSolutionOn.continuousOn_ricciAt

theorem IsSolutionOn.continuousOn_ricciTensor [BoundarylessManifold I M]
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D} (hS : IsSolutionOn S)
    (x : M) (v w : TangentSpace I x) :
    ContinuousOn (fun t => ricciTensor (S.base.metric t) x v w) D.carrier := by
  exact (hS.continuousOn_ricciAt x v w).congr fun t _ =>
    (metricRicciAt_apply_eq_ricciTensor (S.base.metric t) x v w).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IsSolutionOn.continuousOn_ricciTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IsSolutionOn.continuousOn_ricciTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IsSolutionOn.continuousOn_ricciTensor ``Submission.DifferentialGeometry.PDE.RicciFlow.IsSolutionOn.continuousOn_ricciTensor

end DifferentialGeometry.PDE.RicciFlow

end

noncomputable section
open _root_.Set _root_.Filter _root_.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.PDE.RicciFlow
universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}

theorem IsSolutionOn.eventually_scalar_riemann_bounds_on_compact
    (hS : IsSolutionOn S) {t : ℝ} (ht : t ∈ D.regular) (x : M)
    {K : Set M} (hK : IsCompact K) {a b c : ℝ}
    (hscalar : ∀ z ∈ K, a * S.scalar t x < S.scalar t z ∧ S.scalar t z < b * S.scalar t x)
    (hrm : ∀ z ∈ K, Real.sqrt (normSq0S (S.base.metric t) z 4 (S.base.rm04 t z)) < c * S.scalar t x) :
    ∀ᶠ p : ℝ × M in 𝓝 (t,x), ∀ z ∈ K,
      a * S.scalar p.1 p.2 < S.scalar p.1 z ∧ S.scalar p.1 z < b * S.scalar p.1 p.2 ∧
      Real.sqrt (normSq0S (S.base.metric p.1) z 4 (S.base.rm04 p.1 z)) < c * S.scalar p.1 p.2 := by
  have hcenter : ContinuousAt (fun p : ℝ × M => S.scalar p.1 p.2) (t,x) :=
    hS.scalarCont.continuousAt (prod_mem_nhds (D.regular_mem_nhds ht) _root_.Filter.univ_mem)
  have hparameter : Continuous (fun q : (ℝ × M) × M => (q.1.1, q.2)) :=
    (continuous_fst.comp continuous_fst).prodMk continuous_snd
  apply hK.eventually_forall_of_forall_eventually
  intro z hz
  have hs0 : ContinuousAt (fun p : ℝ × M => S.scalar p.1 p.2) (t,z) :=
    hS.scalarCont.continuousAt (prod_mem_nhds (D.regular_mem_nhds ht) _root_.Filter.univ_mem)
  have hs : ContinuousAt (fun q : (ℝ × M) × M => S.scalar q.1.1 q.2) ((t,x),z) :=
    hs0.comp (f := fun q : (ℝ × M) × M => (q.1.1,q.2)) (x := ((t,x),z)) hparameter.continuousAt
  have hp : ContinuousAt (fun q : (ℝ × M) × M => S.scalar q.1.1 q.1.2) ((t,x),z) :=
    hcenter.comp (f := (Prod.fst : (ℝ × M) × M → ℝ × M)) (x := ((t,x),z)) continuous_fst.continuousAt
  have hrm0 : ContinuousAt (fun p : ℝ × M =>
      Real.sqrt (normSq0S (S.base.metric p.1) p.2 4 (S.base.rm04 p.1 p.2))) (t,z) :=
    hS.continuousOn_riemannNorm.continuousAt (prod_mem_nhds (D.regular_mem_nhds ht) _root_.Filter.univ_mem)
  have hcurv : ContinuousAt (fun q : (ℝ × M) × M =>
      Real.sqrt (normSq0S (S.base.metric q.1.1) q.2 4 (S.base.rm04 q.1.1 q.2))) ((t,x),z) :=
    hrm0.comp (f := fun q : (ℝ × M) × M => (q.1.1,q.2)) (x := ((t,x),z)) hparameter.continuousAt
  filter_upwards [(hs.sub (hp.const_mul a)).eventually (Ioi_mem_nhds (sub_pos.mpr (hscalar z hz).1)),
    ((hp.const_mul b).sub hs).eventually (Ioi_mem_nhds (sub_pos.mpr (hscalar z hz).2)),
    ((hp.const_mul c).sub hcurv).eventually (Ioi_mem_nhds (sub_pos.mpr (hrm z hz)))] with q hlo hup hnorm
  exact ⟨sub_pos.mp hlo, sub_pos.mp hup, sub_pos.mp hnorm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IsSolutionOn.eventually_scalar_riemann_bounds_on_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IsSolutionOn.eventually_scalar_riemann_bounds_on_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IsSolutionOn.eventually_scalar_riemann_bounds_on_compact ``Submission.DifferentialGeometry.PDE.RicciFlow.IsSolutionOn.eventually_scalar_riemann_bounds_on_compact
end DifferentialGeometry.PDE.RicciFlow

end
