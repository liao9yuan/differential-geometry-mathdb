import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open _root_.Bundle
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem pullbackMetric_inner_eq_inner_mfderiv
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (x : M) (v w : TangentSpace I x) (s : ℝ) :
    (Diffeomorph.pullbackMetric (g_fam s) (Φ_fam s)).inner x v w
      = (g_fam s).inner (Φ_fam s x)
          (mfderiv I I (Φ_fam s : M → M) x v)
          (mfderiv I I (Φ_fam s : M → M) x w) := by
  change Diffeomorph.pullbackInner (g_fam s) (Φ_fam s) x v w
      = (g_fam s).inner (Φ_fam s x)
          (mfderiv I I (Φ_fam s : M → M) x v)
          (mfderiv I I (Φ_fam s : M → M) x w)
  unfold Diffeomorph.pullbackInner
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Pullback.pullbackMetric_inner_eq_inner_mfderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Pullback.pullbackMetric_inner_eq_inner_mfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Pullback.pullbackMetric_inner_eq_inner_mfderiv ``Submission.DifferentialGeometry.PDE.RicciFlow.Pullback.pullbackMetric_inner_eq_inner_mfderiv

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem pullbackMetric_inner_funext
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (x : M) (v w : TangentSpace I x) :
    (fun s : ℝ => (Diffeomorph.pullbackMetric (g_fam s) (Φ_fam s)).inner x v w)
      = (fun s : ℝ => (g_fam s).inner (Φ_fam s x)
          (mfderiv I I (Φ_fam s : M → M) x v)
          (mfderiv I I (Φ_fam s : M → M) x w)) := by
  funext s
  exact pullbackMetric_inner_eq_inner_mfderiv g_fam Φ_fam x v w s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Pullback.pullbackMetric_inner_funext then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Pullback.pullbackMetric_inner_funext"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Pullback.pullbackMetric_inner_funext ``Submission.DifferentialGeometry.PDE.RicciFlow.Pullback.pullbackMetric_inner_funext

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem pullbackMetric_inner_hasDerivWithinAt_of_eval
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    {s : Set ℝ} {t : ℝ} {G' : ℝ}
    (x : M) (v w : TangentSpace I x)
    (h_eval : HasDerivWithinAt
      (fun u : ℝ => (g_fam u).inner (Φ_fam u x)
        (mfderiv I I (Φ_fam u : M → M) x v)
        (mfderiv I I (Φ_fam u : M → M) x w))
      G' s t) :
    HasDerivWithinAt
      (fun u : ℝ => (Diffeomorph.pullbackMetric (g_fam u) (Φ_fam u)).inner x v w)
      G' s t := by
  refine h_eval.congr ?_ ?_
  · intro u _
    exact (pullbackMetric_inner_eq_inner_mfderiv g_fam Φ_fam x v w u).symm
  · exact (pullbackMetric_inner_eq_inner_mfderiv g_fam Φ_fam x v w t).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Pullback.pullbackMetric_inner_hasDerivWithinAt_of_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Pullback.pullbackMetric_inner_hasDerivWithinAt_of_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Pullback.pullbackMetric_inner_hasDerivWithinAt_of_eval ``Submission.DifferentialGeometry.PDE.RicciFlow.Pullback.pullbackMetric_inner_hasDerivWithinAt_of_eval

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem pullbackMetric_inner_hasDerivWithinAt_to_eval
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    {s : Set ℝ} {t : ℝ} {G' : ℝ}
    (x : M) (v w : TangentSpace I x)
    (h_pullback : HasDerivWithinAt
      (fun u : ℝ => (Diffeomorph.pullbackMetric (g_fam u) (Φ_fam u)).inner x v w)
      G' s t) :
    HasDerivWithinAt
      (fun u : ℝ => (g_fam u).inner (Φ_fam u x)
        (mfderiv I I (Φ_fam u : M → M) x v)
        (mfderiv I I (Φ_fam u : M → M) x w))
      G' s t := by
  refine h_pullback.congr ?_ ?_
  · intro u _
    exact pullbackMetric_inner_eq_inner_mfderiv g_fam Φ_fam x v w u
  · exact pullbackMetric_inner_eq_inner_mfderiv g_fam Φ_fam x v w t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Pullback.pullbackMetric_inner_hasDerivWithinAt_to_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Pullback.pullbackMetric_inner_hasDerivWithinAt_to_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Pullback.pullbackMetric_inner_hasDerivWithinAt_to_eval ``Submission.DifferentialGeometry.PDE.RicciFlow.Pullback.pullbackMetric_inner_hasDerivWithinAt_to_eval

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem pullbackMetric_inner_hasDerivWithinAt_iff
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    {s : Set ℝ} {t : ℝ} {G' : ℝ}
    (x : M) (v w : TangentSpace I x) :
    HasDerivWithinAt
      (fun u : ℝ => (Diffeomorph.pullbackMetric (g_fam u) (Φ_fam u)).inner x v w)
      G' s t
    ↔ HasDerivWithinAt
      (fun u : ℝ => (g_fam u).inner (Φ_fam u x)
        (mfderiv I I (Φ_fam u : M → M) x v)
        (mfderiv I I (Φ_fam u : M → M) x w))
      G' s t :=
  ⟨pullbackMetric_inner_hasDerivWithinAt_to_eval g_fam Φ_fam x v w,
    pullbackMetric_inner_hasDerivWithinAt_of_eval g_fam Φ_fam x v w⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Pullback.pullbackMetric_inner_hasDerivWithinAt_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Pullback.pullbackMetric_inner_hasDerivWithinAt_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Pullback.pullbackMetric_inner_hasDerivWithinAt_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Pullback.pullbackMetric_inner_hasDerivWithinAt_iff

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem pullbackMetric_inner_hasDerivAt_of_eval
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    {t G' : ℝ}
    (x : M) (v w : TangentSpace I x)
    (h_eval : HasDerivAt
      (fun u : ℝ => (g_fam u).inner (Φ_fam u x)
        (mfderiv I I (Φ_fam u : M → M) x v)
        (mfderiv I I (Φ_fam u : M → M) x w))
      G' t) :
    HasDerivAt
      (fun u : ℝ => (Diffeomorph.pullbackMetric (g_fam u) (Φ_fam u)).inner x v w)
      G' t := by
  rw [← hasDerivWithinAt_univ] at h_eval ⊢
  exact pullbackMetric_inner_hasDerivWithinAt_of_eval g_fam Φ_fam x v w h_eval

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Pullback.pullbackMetric_inner_hasDerivAt_of_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Pullback.pullbackMetric_inner_hasDerivAt_of_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Pullback.pullbackMetric_inner_hasDerivAt_of_eval ``Submission.DifferentialGeometry.PDE.RicciFlow.Pullback.pullbackMetric_inner_hasDerivAt_of_eval

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem pullbackMetric_inner_hasDerivAt_to_eval
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    {t G' : ℝ}
    (x : M) (v w : TangentSpace I x)
    (h_pullback : HasDerivAt
      (fun u : ℝ => (Diffeomorph.pullbackMetric (g_fam u) (Φ_fam u)).inner x v w)
      G' t) :
    HasDerivAt
      (fun u : ℝ => (g_fam u).inner (Φ_fam u x)
        (mfderiv I I (Φ_fam u : M → M) x v)
        (mfderiv I I (Φ_fam u : M → M) x w))
      G' t := by
  rw [← hasDerivWithinAt_univ] at h_pullback ⊢
  exact pullbackMetric_inner_hasDerivWithinAt_to_eval g_fam Φ_fam x v w h_pullback

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Pullback.pullbackMetric_inner_hasDerivAt_to_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Pullback.pullbackMetric_inner_hasDerivAt_to_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Pullback.pullbackMetric_inner_hasDerivAt_to_eval ``Submission.DifferentialGeometry.PDE.RicciFlow.Pullback.pullbackMetric_inner_hasDerivAt_to_eval

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem pullbackMetric_inner_hasDerivAt_iff
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    {t G' : ℝ}
    (x : M) (v w : TangentSpace I x) :
    HasDerivAt
      (fun u : ℝ => (Diffeomorph.pullbackMetric (g_fam u) (Φ_fam u)).inner x v w)
      G' t
    ↔ HasDerivAt
      (fun u : ℝ => (g_fam u).inner (Φ_fam u x)
        (mfderiv I I (Φ_fam u : M → M) x v)
        (mfderiv I I (Φ_fam u : M → M) x w))
      G' t :=
  ⟨pullbackMetric_inner_hasDerivAt_to_eval g_fam Φ_fam x v w,
    pullbackMetric_inner_hasDerivAt_of_eval g_fam Φ_fam x v w⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Pullback.pullbackMetric_inner_hasDerivAt_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Pullback.pullbackMetric_inner_hasDerivAt_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Pullback.pullbackMetric_inner_hasDerivAt_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Pullback.pullbackMetric_inner_hasDerivAt_iff

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem pullbackMetric_inner_hasDerivWithinAt_product_rule
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    {s : Set ℝ} {t : ℝ} {G' A' B' : ℝ}
    (x : M) (v w : TangentSpace I x)
    (h_total : HasDerivWithinAt
      (fun u : ℝ => (g_fam u).inner (Φ_fam u x)
        (mfderiv I I (Φ_fam u : M → M) x v)
        (mfderiv I I (Φ_fam u : M → M) x w))
      (G' + A' + B') s t) :
    HasDerivWithinAt
      (fun u : ℝ => (Diffeomorph.pullbackMetric (g_fam u) (Φ_fam u)).inner x v w)
      (G' + A' + B') s t :=
  pullbackMetric_inner_hasDerivWithinAt_of_eval g_fam Φ_fam x v w h_total

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Pullback.pullbackMetric_inner_hasDerivWithinAt_product_rule then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Pullback.pullbackMetric_inner_hasDerivWithinAt_product_rule"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Pullback.pullbackMetric_inner_hasDerivWithinAt_product_rule ``Submission.DifferentialGeometry.PDE.RicciFlow.Pullback.pullbackMetric_inner_hasDerivWithinAt_product_rule

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem pullbackMetric_inner_hasDerivWithinAt_sum
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    {s : Set ℝ} {t : ℝ} {G' L' : ℝ}
    (x : M) (v w : TangentSpace I x)
    (h_total : HasDerivWithinAt
      (fun u : ℝ => (g_fam u).inner (Φ_fam u x)
        (mfderiv I I (Φ_fam u : M → M) x v)
        (mfderiv I I (Φ_fam u : M → M) x w))
      (G' + L') s t) :
    HasDerivWithinAt
      (fun u : ℝ => (Diffeomorph.pullbackMetric (g_fam u) (Φ_fam u)).inner x v w)
      (G' + L') s t :=
  pullbackMetric_inner_hasDerivWithinAt_of_eval g_fam Φ_fam x v w h_total

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Pullback.pullbackMetric_inner_hasDerivWithinAt_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Pullback.pullbackMetric_inner_hasDerivWithinAt_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Pullback.pullbackMetric_inner_hasDerivWithinAt_sum ``Submission.DifferentialGeometry.PDE.RicciFlow.Pullback.pullbackMetric_inner_hasDerivWithinAt_sum

end DifferentialGeometry.PDE.RicciFlow.Pullback
