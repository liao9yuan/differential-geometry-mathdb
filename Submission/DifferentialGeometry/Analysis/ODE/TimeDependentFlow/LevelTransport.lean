import Submission.DifferentialGeometry.Analysis.ODE.Flow.LinearODE.Sign
import Submission.DifferentialGeometry.Analysis.Calculus.LevelPreservation
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Prod

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace IsIntegralCurve
open _root_.IsIntegralCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {v : ℝ → E → E} {γ : ℝ → E} {F : ℝ × E → ℝ}

open _root_.IsIntegralCurve in
private theorem deriv_time_dependent_comp_at (t : ℝ)
    (hγ : HasDerivAt γ (v t (γ t)) t) (hF : DifferentiableAt ℝ F (t, γ t)) :
    deriv (fun u => F (u, γ u)) t = deriv (fun u => F (u, γ t)) t +
      fderiv ℝ (fun x => F (t, x)) (γ t) (v t (γ t)) := by
  let L := fderiv ℝ F (t, γ t)
  have h := hF.hasFDerivAt
  have htotal := (h.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hγ)).deriv
  have htime := (h.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t (γ t)))).deriv
  have hspace := congrArg (fun A : E →L[ℝ] ℝ => A (v t (γ t)))
    (h.comp (γ t) (hasFDerivAt_prodMk_right (𝕜 := ℝ) t (γ t))).fderiv
  change deriv (fun u => F (u, γ u)) t = L (1, v t (γ t)) at htotal
  change deriv (fun u => F (u, γ t)) t = L (1, 0) at htime
  change fderiv ℝ (fun x => F (t, x)) (γ t) (v t (γ t)) = L (0, v t (γ t)) at hspace
  rw [htotal, htime, hspace, ← map_add]
  congr 1
  simp

run_cmd do
  let target := ``Submission.IsIntegralCurve.deriv_time_dependent_comp_at
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `IsIntegralCurve.deriv_time_dependent_comp_at target :: scope.openDecls } }

open _root_.IsIntegralCurve in
private theorem deriv_time_dependent_comp (hγ : IsIntegralCurve γ v)
    (hF : Differentiable ℝ F) (t : ℝ) :
    deriv (fun u => F (u, γ u)) t = deriv (fun u => F (u, γ t)) t +
      fderiv ℝ (fun x => F (t, x)) (γ t) (v t (γ t)) :=
  deriv_time_dependent_comp_at t (hγ t) (hF (t, γ t))

run_cmd do
  let target := ``Submission.IsIntegralCurve.deriv_time_dependent_comp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `IsIntegralCurve.deriv_time_dependent_comp target :: scope.openDecls } }

open _root_.IsIntegralCurve in
theorem level_eq_iff_of_transport_on (hγ : IsIntegralCurve γ v) (hF : Differentiable ℝ F)
    {D : Set (ℝ × E)} (hstay : ∀ t, (t, γ t) ∈ D)
    {U : Set ℝ} (hU : IsOpen U)
    (htransport : ∀ t x, (t, x) ∈ D → F (t, x) ∈ U →
      fderiv ℝ (fun z => F (t, z)) x (v t x) = -deriv (fun s => F (s, x)) t)
    {r : ℝ} (hr : r ∈ U) (s t : ℝ) :
    F (s, γ s) = r ↔ F (t, γ t) = r := by
  have hdiff : Differentiable ℝ (fun u => F (u, γ u)) :=
    hF.comp (differentiable_id.prodMk (fun u => (hγ u).differentiableAt))
  apply hdiff.continuous.eq_iff_eq_of_deriv_eq_zero_on_preimage hU hdiff.differentiableOn
    (fun u hu => ?_) hr s t
  rw [hγ.deriv_time_dependent_comp hF, htransport u (γ u) (hstay u) hu, add_neg_cancel]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsIntegralCurve.level_eq_iff_of_transport_on then
    throwError "Refusing to shadow existing declaration IsIntegralCurve.level_eq_iff_of_transport_on"
  Lean.modifyEnv fun env => Lean.addAlias env `IsIntegralCurve.level_eq_iff_of_transport_on ``Submission.IsIntegralCurve.level_eq_iff_of_transport_on

open _root_.IsIntegralCurve in
theorem sublevel_lt_iff_of_transport_on (hγ : IsIntegralCurve γ v) (hF : Differentiable ℝ F)
    {D : Set (ℝ × E)} (hstay : ∀ t, (t, γ t) ∈ D)
    {U : Set ℝ} (hU : IsOpen U)
    (htransport : ∀ t x, (t, x) ∈ D → F (t, x) ∈ U →
      fderiv ℝ (fun z => F (t, z)) x (v t x) = -deriv (fun s => F (s, x)) t)
    {r : ℝ} (hr : r ∈ U) (s t : ℝ) :
    F (s, γ s) < r ↔ F (t, γ t) < r := by
  have hdiff : Differentiable ℝ (fun u => F (u, γ u)) :=
    hF.comp (differentiable_id.prodMk (fun u => (hγ u).differentiableAt))
  apply hdiff.continuous.lt_iff_lt_of_deriv_eq_zero_on_preimage hU hdiff.differentiableOn
    (fun u hu => ?_) hr s t
  rw [hγ.deriv_time_dependent_comp hF, htransport u (γ u) (hstay u) hu, add_neg_cancel]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsIntegralCurve.sublevel_lt_iff_of_transport_on then
    throwError "Refusing to shadow existing declaration IsIntegralCurve.sublevel_lt_iff_of_transport_on"
  Lean.modifyEnv fun env => Lean.addAlias env `IsIntegralCurve.sublevel_lt_iff_of_transport_on ``Submission.IsIntegralCurve.sublevel_lt_iff_of_transport_on

open _root_.IsIntegralCurve in
theorem sublevel_le_iff_of_transport_on (hγ : IsIntegralCurve γ v) (hF : Differentiable ℝ F)
    {D : Set (ℝ × E)} (hstay : ∀ t, (t, γ t) ∈ D)
    {U : Set ℝ} (hU : IsOpen U)
    (htransport : ∀ t x, (t, x) ∈ D → F (t, x) ∈ U →
      fderiv ℝ (fun z => F (t, z)) x (v t x) = -deriv (fun s => F (s, x)) t)
    {r : ℝ} (hr : r ∈ U) (s t : ℝ) :
    F (s, γ s) ≤ r ↔ F (t, γ t) ≤ r := by
  rw [le_iff_eq_or_lt, le_iff_eq_or_lt]
  exact or_congr (hγ.level_eq_iff_of_transport_on hF hstay hU htransport hr s t)
    (hγ.sublevel_lt_iff_of_transport_on hF hstay hU htransport hr s t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsIntegralCurve.sublevel_le_iff_of_transport_on then
    throwError "Refusing to shadow existing declaration IsIntegralCurve.sublevel_le_iff_of_transport_on"
  Lean.modifyEnv fun env => Lean.addAlias env `IsIntegralCurve.sublevel_le_iff_of_transport_on ``Submission.IsIntegralCurve.sublevel_le_iff_of_transport_on

open _root_.IsIntegralCurve in
theorem level_eq_iff_of_transport (hγ : IsIntegralCurve γ v) (hF : Differentiable ℝ F)
    {U : Set ℝ} (hU : IsOpen U)
    (htransport : ∀ t x, F (t, x) ∈ U →
      fderiv ℝ (fun z => F (t, z)) x (v t x) = -deriv (fun s => F (s, x)) t)
    {r : ℝ} (hr : r ∈ U) (s t : ℝ) :
    F (s, γ s) = r ↔ F (t, γ t) = r :=
  hγ.level_eq_iff_of_transport_on hF (D := Set.univ) (fun _ => Set.mem_univ _) hU
    (fun t x _ => htransport t x) hr s t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsIntegralCurve.level_eq_iff_of_transport then
    throwError "Refusing to shadow existing declaration IsIntegralCurve.level_eq_iff_of_transport"
  Lean.modifyEnv fun env => Lean.addAlias env `IsIntegralCurve.level_eq_iff_of_transport ``Submission.IsIntegralCurve.level_eq_iff_of_transport

open _root_.IsIntegralCurve in
theorem sublevel_lt_iff_of_transport (hγ : IsIntegralCurve γ v) (hF : Differentiable ℝ F)
    {U : Set ℝ} (hU : IsOpen U)
    (htransport : ∀ t x, F (t, x) ∈ U →
      fderiv ℝ (fun z => F (t, z)) x (v t x) = -deriv (fun s => F (s, x)) t)
    {r : ℝ} (hr : r ∈ U) (s t : ℝ) :
    F (s, γ s) < r ↔ F (t, γ t) < r :=
  hγ.sublevel_lt_iff_of_transport_on hF (D := Set.univ) (fun _ => Set.mem_univ _) hU
    (fun t x _ => htransport t x) hr s t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsIntegralCurve.sublevel_lt_iff_of_transport then
    throwError "Refusing to shadow existing declaration IsIntegralCurve.sublevel_lt_iff_of_transport"
  Lean.modifyEnv fun env => Lean.addAlias env `IsIntegralCurve.sublevel_lt_iff_of_transport ``Submission.IsIntegralCurve.sublevel_lt_iff_of_transport

open _root_.IsIntegralCurve in
theorem sublevel_le_iff_of_transport (hγ : IsIntegralCurve γ v) (hF : Differentiable ℝ F)
    {U : Set ℝ} (hU : IsOpen U)
    (htransport : ∀ t x, F (t, x) ∈ U →
      fderiv ℝ (fun z => F (t, z)) x (v t x) = -deriv (fun s => F (s, x)) t)
    {r : ℝ} (hr : r ∈ U) (s t : ℝ) :
    F (s, γ s) ≤ r ↔ F (t, γ t) ≤ r :=
  hγ.sublevel_le_iff_of_transport_on hF (D := Set.univ) (fun _ => Set.mem_univ _) hU
    (fun t x _ => htransport t x) hr s t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsIntegralCurve.sublevel_le_iff_of_transport then
    throwError "Refusing to shadow existing declaration IsIntegralCurve.sublevel_le_iff_of_transport"
  Lean.modifyEnv fun env => Lean.addAlias env `IsIntegralCurve.sublevel_le_iff_of_transport ``Submission.IsIntegralCurve.sublevel_le_iff_of_transport

end IsIntegralCurve


namespace IsIntegralCurveOn
open _root_.IsIntegralCurveOn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {v : ℝ → E → E} {γ : ℝ → E} {F κ : ℝ × E → ℝ} {a b r : ℝ}

open _root_.IsIntegralCurveOn in
private theorem level_and_sublevels_iff_of_proportional_transport_Ioo
    (hγ : IsIntegralCurveOn γ v (Set.Ioo a b))
    {D : Set (ℝ × E)} (hD : IsOpen D) (hstay : ∀ t ∈ Set.Ioo a b, (t, γ t) ∈ D)
    (hF : DifferentiableOn ℝ F D) (hκ : ContinuousOn κ D)
    (htransport : ∀ t ∈ Set.Ioo a b,
      deriv (fun u => F (u, γ t)) t +
        fderiv ℝ (fun x => F (t, x)) (γ t) (v t (γ t)) =
          κ (t, γ t) * (F (t, γ t) - r))
    {s t : ℝ} (hs : s ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b) :
    (F (s, γ s) = r ↔ F (t, γ t) = r) ∧
      (F (s, γ s) < r ↔ F (t, γ t) < r) ∧
      (F (s, γ s) ≤ r ↔ F (t, γ t) ≤ r) := by
  have hd : ∀ u ∈ Set.Ioo a b, HasDerivAt (fun z => F (z, γ z) - r)
      (κ (u, γ u) * (F (u, γ u) - r)) u := by
    intro u hu
    have hγu := (hγ u hu).hasDerivAt (isOpen_Ioo.mem_nhds hu)
    have hFu := (hF (u, γ u) (hstay u hu)).differentiableAt (hD.mem_nhds (hstay u hu))
    have htotal := hFu.hasFDerivAt.comp_hasDerivAt u ((hasDerivAt_id u).prodMk hγu)
    have hchain := IsIntegralCurve.deriv_time_dependent_comp_at u hγu hFu
    have hderiv : deriv (fun z => F (z, γ z)) u =
        κ (u, γ u) * (F (u, γ u) - r) := hchain.trans (htransport u hu)
    rw [← hderiv]
    exact htotal.differentiableAt.hasDerivAt.sub_const r
  have hκγ : ContinuousOn (fun u => κ (u, γ u)) (Set.Ioo a b) :=
    hκ.comp (continuousOn_id.prodMk hγ.continuousOn) hstay
  have hz := DifferentialGeometry.Analysis.ODE.zero_eq_iff_of_hasDerivAt_mul_Ioo hκγ hd hs ht
  have hn := DifferentialGeometry.Analysis.ODE.neg_iff_neg_of_hasDerivAt_mul_Ioo hκγ hd hs ht
  have hp := DifferentialGeometry.Analysis.ODE.nonpos_iff_nonpos_of_hasDerivAt_mul_Ioo hκγ hd hs ht
  exact ⟨by simpa only [sub_eq_zero] using hz,
    by simpa only [sub_lt_zero] using hn, by simpa only [sub_nonpos] using hp⟩

run_cmd do
  let target := ``Submission.IsIntegralCurveOn.level_and_sublevels_iff_of_proportional_transport_Ioo
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `IsIntegralCurveOn.level_and_sublevels_iff_of_proportional_transport_Ioo target :: scope.openDecls } }

open _root_.IsIntegralCurveOn in
theorem level_eq_iff_of_proportional_transport_Ioo
    (hγ : IsIntegralCurveOn γ v (Set.Ioo a b))
    {D : Set (ℝ × E)} (hD : IsOpen D) (hstay : ∀ t ∈ Set.Ioo a b, (t, γ t) ∈ D)
    (hF : DifferentiableOn ℝ F D) (hκ : ContinuousOn κ D)
    (htransport : ∀ t ∈ Set.Ioo a b,
      deriv (fun u => F (u, γ t)) t +
        fderiv ℝ (fun x => F (t, x)) (γ t) (v t (γ t)) =
          κ (t, γ t) * (F (t, γ t) - r))
    {s t : ℝ} (hs : s ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b) :
    F (s, γ s) = r ↔ F (t, γ t) = r :=
  (level_and_sublevels_iff_of_proportional_transport_Ioo hγ hD hstay hF hκ htransport hs ht).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsIntegralCurveOn.level_eq_iff_of_proportional_transport_Ioo then
    throwError "Refusing to shadow existing declaration IsIntegralCurveOn.level_eq_iff_of_proportional_transport_Ioo"
  Lean.modifyEnv fun env => Lean.addAlias env `IsIntegralCurveOn.level_eq_iff_of_proportional_transport_Ioo ``Submission.IsIntegralCurveOn.level_eq_iff_of_proportional_transport_Ioo

open _root_.IsIntegralCurveOn in
theorem sublevel_lt_iff_of_proportional_transport_Ioo
    (hγ : IsIntegralCurveOn γ v (Set.Ioo a b))
    {D : Set (ℝ × E)} (hD : IsOpen D) (hstay : ∀ t ∈ Set.Ioo a b, (t, γ t) ∈ D)
    (hF : DifferentiableOn ℝ F D) (hκ : ContinuousOn κ D)
    (htransport : ∀ t ∈ Set.Ioo a b,
      deriv (fun u => F (u, γ t)) t +
        fderiv ℝ (fun x => F (t, x)) (γ t) (v t (γ t)) =
          κ (t, γ t) * (F (t, γ t) - r))
    {s t : ℝ} (hs : s ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b) :
    F (s, γ s) < r ↔ F (t, γ t) < r :=
  (level_and_sublevels_iff_of_proportional_transport_Ioo hγ hD hstay hF hκ htransport hs ht).2.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsIntegralCurveOn.sublevel_lt_iff_of_proportional_transport_Ioo then
    throwError "Refusing to shadow existing declaration IsIntegralCurveOn.sublevel_lt_iff_of_proportional_transport_Ioo"
  Lean.modifyEnv fun env => Lean.addAlias env `IsIntegralCurveOn.sublevel_lt_iff_of_proportional_transport_Ioo ``Submission.IsIntegralCurveOn.sublevel_lt_iff_of_proportional_transport_Ioo

open _root_.IsIntegralCurveOn in
theorem sublevel_le_iff_of_proportional_transport_Ioo
    (hγ : IsIntegralCurveOn γ v (Set.Ioo a b))
    {D : Set (ℝ × E)} (hD : IsOpen D) (hstay : ∀ t ∈ Set.Ioo a b, (t, γ t) ∈ D)
    (hF : DifferentiableOn ℝ F D) (hκ : ContinuousOn κ D)
    (htransport : ∀ t ∈ Set.Ioo a b,
      deriv (fun u => F (u, γ t)) t +
        fderiv ℝ (fun x => F (t, x)) (γ t) (v t (γ t)) =
          κ (t, γ t) * (F (t, γ t) - r))
    {s t : ℝ} (hs : s ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b) :
    F (s, γ s) ≤ r ↔ F (t, γ t) ≤ r :=
  (level_and_sublevels_iff_of_proportional_transport_Ioo hγ hD hstay hF hκ htransport hs ht).2.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsIntegralCurveOn.sublevel_le_iff_of_proportional_transport_Ioo then
    throwError "Refusing to shadow existing declaration IsIntegralCurveOn.sublevel_le_iff_of_proportional_transport_Ioo"
  Lean.modifyEnv fun env => Lean.addAlias env `IsIntegralCurveOn.sublevel_le_iff_of_proportional_transport_Ioo ``Submission.IsIntegralCurveOn.sublevel_le_iff_of_proportional_transport_Ioo

end IsIntegralCurveOn
