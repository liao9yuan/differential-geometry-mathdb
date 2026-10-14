import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Projection
import Submission.DifferentialGeometry.Topology.Compactness.TimeInterval
import Mathlib.Algebra.Field.Periodic
import Submission.DifferentialGeometry.Analysis.Calculus.TimeJet.SpatialDerivatives

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_forall_isRampOn_Icc_of_continuousOn_deriv
    {P : Type*} [TopologicalSpace P] [CompactSpace P]
    (c : P → ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M)
    {lambda a T : ℝ} (hlambda : 0 < lambda) (haT : a < T)
    (hramp : ∀ p, (c p).IsRampOn g lambda {a})
    (hdy : ContinuousOn
      (fun q : (P × ℝ) × ℝ => deriv (fun z => (c q.1.1).y z q.2) q.1.2)
      ((_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ×ˢ _root_.Set.Icc a T)) :
    ∃ δ > 0, δ ≤ T - a ∧ ∀ p, (c p).IsRampOn g lambda (_root_.Set.Icc a (a + δ)) := by
  have hpos : ∀ p x, 0 < deriv (fun z => (c p).y z a) x := by
    intro p x
    have hangle := (hramp p).2 x a (_root_.Set.mem_singleton a)
    rw [(c p).angle_eq g lambda] at hangle
    have hsp := (c p).speed_pos_of_immersedOn g lambda hlambda
      (hramp p).1 x a (_root_.Set.mem_singleton a)
    exact (mul_pos_iff_of_pos_left (mul_pos hlambda (inv_pos.mpr hsp))).mp hangle
  have hK : IsCompact ((_root_.Set.univ : Set P) ×ˢ _root_.Set.Icc (0 : ℝ) 1) :=
    isCompact_univ.prod _root_.CompactIccSpace.isCompact_Icc
  obtain ⟨δ, hδ, hδT, hpositive⟩ :=
    hK.exists_Icc_mapsTo_of_continuousOn haT isOpen_Ioi hdy
      (fun q _ => hpos q.1 q.2)
  have hpositive_all : ∀ p x t, t ∈ _root_.Set.Icc a (a + δ) →
      0 < deriv (fun z => (c p).y z t) x := by
    intro p x t ht
    have hper : Function.Periodic (deriv (fun z => (c p).y z t)) 1 :=
      (c p).deriv_y_add_period t
    obtain ⟨y, hy, hxy⟩ := hper.exists_mem_Ioc (by norm_num : (0 : ℝ) < 1) x 0
    rw [hxy]
    exact hpositive (p, y) ⟨mem_univ p, hy.1.le, by simpa using hy.2⟩ t ht
  have himm : ∀ p, (c p).ImmersedOn (I := I) (_root_.Set.Icc a (a + δ)) := by
    intro p x t ht hzero
    have hdyzero : deriv (fun z => (c p).y z t) x = 0 := congrArg Prod.snd hzero
    exact (hpositive_all p x t ht).ne' hdyzero
  refine ⟨δ, hδ, hδT, fun p => ⟨himm p, ?_⟩⟩
  intro x t ht
  rw [(c p).angle_eq g lambda]
  exact mul_pos (mul_pos hlambda
    (inv_pos.mpr ((c p).speed_pos_of_immersedOn g lambda hlambda (himm p) x t ht)))
    (hpositive_all p x t ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.exists_forall_isRampOn_Icc_of_continuousOn_deriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.exists_forall_isRampOn_Icc_of_continuousOn_deriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.exists_forall_isRampOn_Icc_of_continuousOn_deriv ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.exists_forall_isRampOn_Icc_of_continuousOn_deriv

theorem exists_isRampOn_Icc_of_smoothOn
    (c : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M)
    {lambda a T : ℝ} (hlambda : 0 < lambda) (haT : a < T)
    (hc : c.SmoothOn (I := I) (_root_.Set.Icc a T)) (hramp : c.IsRampOn g lambda {a}) :
    ∃ δ > 0, a + δ ≤ T ∧ c.IsRampOn g lambda (_root_.Set.Icc a (a + δ)) := by
  have hdy : ContinuousOn (fun q : ℝ × ℝ => deriv (fun z => c.y z q.2) q.1)
      (_root_.Set.univ ×ˢ _root_.Set.Icc a T) :=
    (DifferentialGeometry.Analysis.contDiffOn_deriv_fst isOpen_univ
      (uniqueDiffOn_Icc haT) hc.2).continuousOn
  have hfamily : ContinuousOn
      (fun q : (Unit × ℝ) × ℝ => deriv (fun z => c.y z q.2) q.1.2)
      ((_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ×ˢ _root_.Set.Icc a T) :=
    hdy.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd).continuousOn
      (fun q hq => ⟨mem_univ q.1.2, hq.2⟩)
  obtain ⟨δ, hδ, hδT, hpositive⟩ := exists_forall_isRampOn_Icc_of_continuousOn_deriv
    (fun _ : Unit => c) g hlambda haT (fun _ => hramp) hfamily
  exact ⟨δ, hδ, by linarith, hpositive ()⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.exists_isRampOn_Icc_of_smoothOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.exists_isRampOn_Icc_of_smoothOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.exists_isRampOn_Icc_of_smoothOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve.exists_isRampOn_Icc_of_smoothOn

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve
