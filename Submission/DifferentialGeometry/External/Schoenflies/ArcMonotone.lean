/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
/-
Modified for this project; see MODIFICATIONS.md for the local changes.
-/
import Submission.DifferentialGeometry.External.Schoenflies.Subarc

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# A continuous injection between two arcs is monotone

Two parametrizations `f` and `f'` of two arcs, and a continuous injection `g` carrying the
first arc onto the second. Then `g` respects the order in which the two parametrizations
traverse their arcs: the composite parameter map

  `s ↦ (the parameter at which f' sits at g (f s))`

is strictly monotone on `[0, 1]` — increasing or decreasing according to whether `g` matches
the two parametrizations' starting points or swaps them. Consequently `g` carries a subarc of
the first arc onto a subarc of the second, with the *corresponding* parameters.

That last sentence is what every consumer wants, and it is `ArcMatch.image_image_uIcc`:

  `g '' (f '' uIcc s u) = f' '' uIcc (transferParam f f' g s) (transferParam f f' g u)`.

Stated over `uIcc`, it is **orientation-free**: `uIcc` is unordered, so the identity holds
whether the transfer map increases or decreases, and a consumer that does not know which way
round its two parametrizations run does not have to find out. Only the two corollaries about
*initial* and *terminal* subarcs (`image_initial`, `image_terminal`) need the matching-endpoint
hypothesis, and they take it explicitly.

## How the parameter map is built

No inverse parametrization is constructed as a continuous map. `arcParam f' p` picks, by choice,
*a* parameter in `[0, 1]` sitting at `p`; injectivity of `f'` makes it *the* parameter, and its
continuity along the composite is proved by hand from `Schoenflies.exists_ball_inter_subset_image`
— the statement, already on `main`, that a parametrization is an open map onto its arc. That is
exactly the continuity of the inverse, in the only form needed here, and it avoids constructing a
homeomorphism `↥I ≃ₜ ↥A` and pushing it through subtype coercions.

With the composite continuous and injective on `[0, 1]`, Mathlib's
`ContinuousOn.strictMonoOn_of_injOn_Icc'` supplies the monotone-or-antitone dichotomy.

## Blueprint

There is **no blueprint statement for this**. The manuscript uses it silently, in two places:

* `def:matched-pair`, clause 3 — "on each corresponding pair of edges, `g` restricts to a fixed
  chosen homeomorphism between them, matching endpoints". When an edge is subdivided, the two
  halves of that homeomorphism have to be the chosen homeomorphisms of the two new edges; that
  they *are* half-arc-to-half-arc, rather than merely arc-to-arc, is this file.
* `def:generated-structure`, operation 1 (edge subdivision) — "the corresponding point is
  inserted into the corresponding edge using the edge parametrization". "Corresponding" is the
  transfer map below, and the sentence's content is that inserting corresponding points splits
  the edge homeomorphism into two edge homeomorphisms.

Declarations:

* `Schoenflies.arcParam` — the parameter of a point on a parametrized arc.
* `Schoenflies.ArcMatch` — the hypothesis bundle: two parametrized arcs and a continuous
  injection of the first onto the second.
* `Schoenflies.transferParam` — the induced map on parameters.
* `Schoenflies.ArcMatch.continuousOn_param`, `…injOn_param`,
  `…strictMonoOn_or_strictAntiOn_param` — the monotonicity.
* `Schoenflies.ArcMatch.image_image_uIcc`, `…image_subarc` — the orientation-free conclusion.
* `Schoenflies.ArcMatch.image_initial`, `…image_terminal` — initial and terminal subarcs, given
  matching endpoints.
-/

open _root_.Set _root_.unitInterval

namespace Schoenflies

/-! ### The parameter of a point on a parametrized arc -/

open scoped _root_.Classical in
/-- The parameter in `[0, 1]` at which `f` sits at `p`, chosen; junk (`0`) when there is none.

Only ever used under an injectivity hypothesis, which makes the choice unique
(`arcParam_eq_of_apply`). -/
noncomputable def arcParam (f : ℝ → Plane) (p : Plane) : ℝ :=
  if h : ∃ s, s ∈ I ∧ f s = p then h.choose else 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.arcParam then
    throwError "Refusing to shadow existing declaration Schoenflies.arcParam"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.arcParam ``Submission.Schoenflies.arcParam

variable {f f' : ℝ → Plane} {g : Plane → Plane} {p : Plane} {s u : ℝ}

theorem arcParam_spec (hp : p ∈ f '' I) : arcParam f p ∈ I ∧ f (arcParam f p) = p := by
  have h : ∃ s, s ∈ I ∧ f s = p := by
    obtain ⟨s, hs, rfl⟩ := hp
    exact ⟨s, hs, rfl⟩
  rw [arcParam, dif_pos h]
  exact h.choose_spec

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.arcParam_spec then
    throwError "Refusing to shadow existing declaration Schoenflies.arcParam_spec"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.arcParam_spec ``Submission.Schoenflies.arcParam_spec

theorem arcParam_mem_I (hp : p ∈ f '' I) : arcParam f p ∈ I := (arcParam_spec hp).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.arcParam_mem_I then
    throwError "Refusing to shadow existing declaration Schoenflies.arcParam_mem_I"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.arcParam_mem_I ``Submission.Schoenflies.arcParam_mem_I

theorem apply_arcParam (hp : p ∈ f '' I) : f (arcParam f p) = p := (arcParam_spec hp).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.apply_arcParam then
    throwError "Refusing to shadow existing declaration Schoenflies.apply_arcParam"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.apply_arcParam ``Submission.Schoenflies.apply_arcParam

/-- Under injectivity the chosen parameter is the only one. -/
theorem arcParam_eq_of_apply (hi : _root_.Set.InjOn f I) (hs : s ∈ I) (hfs : f s = p) : arcParam f p = s :=
  hi (arcParam_mem_I ⟨s, hs, hfs⟩) hs ((apply_arcParam ⟨s, hs, hfs⟩).trans hfs.symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.arcParam_eq_of_apply then
    throwError "Refusing to shadow existing declaration Schoenflies.arcParam_eq_of_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.arcParam_eq_of_apply ``Submission.Schoenflies.arcParam_eq_of_apply

/-! ### The hypothesis bundle -/

/-- Two parametrized arcs and a continuous injection of the first onto the second.

A `Prop`-valued bundle rather than seven separate hypotheses: every theorem below needs most of
them, and a consumer assembles it once. -/
structure ArcMatch (f f' : ℝ → Plane) (g : Plane → Plane) : Prop where
  /-- The source parametrization is continuous. -/
  continuousOn_src : ContinuousOn f I
  /-- …and injective. -/
  injOn_src : _root_.Set.InjOn f I
  /-- The target parametrization is continuous. -/
  continuousOn_tgt : ContinuousOn f' I
  /-- …and injective. -/
  injOn_tgt : _root_.Set.InjOn f' I
  /-- The map is continuous on the source arc. -/
  continuousOn_map : ContinuousOn g (f '' I)
  /-- …and injective on it. -/
  injOn_map : _root_.Set.InjOn g (f '' I)
  /-- …and carries the source arc onto the target arc. -/
  image_eq : g '' (f '' I) = f' '' I

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.ArcMatch then
    throwError "Refusing to shadow existing declaration Schoenflies.ArcMatch"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.ArcMatch ``Submission.Schoenflies.ArcMatch

/-- The map `g` induces on parameters: send `s` to the parameter at which `f'` sits at
`g (f s)`.

A plain `def`, not depending on the `ArcMatch` proof, so that a consumer can name the target
parameter before it has assembled the hypotheses — which is exactly what
`Schoenflies/RealizeSubdivHomeo.lean` does. -/
noncomputable def transferParam (f f' : ℝ → Plane) (g : Plane → Plane) : ℝ → ℝ :=
  fun s => arcParam f' (g (f s))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.transferParam then
    throwError "Refusing to shadow existing declaration Schoenflies.transferParam"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.transferParam ``Submission.Schoenflies.transferParam

namespace ArcMatch

variable (h : ArcMatch f f' g)
include h

theorem mem_image_map (hs : s ∈ I) : g (f s) ∈ f' '' I := by
  rw [← h.image_eq]
  exact ⟨f s, ⟨s, hs, rfl⟩, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.ArcMatch.mem_image_map then
    throwError "Refusing to shadow existing declaration Schoenflies.ArcMatch.mem_image_map"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.ArcMatch.mem_image_map ``Submission.Schoenflies.ArcMatch.mem_image_map

theorem param_mem_I (hs : s ∈ I) : transferParam f f' g s ∈ I :=
  arcParam_mem_I (h.mem_image_map hs)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.ArcMatch.param_mem_I then
    throwError "Refusing to shadow existing declaration Schoenflies.ArcMatch.param_mem_I"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.ArcMatch.param_mem_I ``Submission.Schoenflies.ArcMatch.param_mem_I

/-- **The defining property**: the target parametrization at the transferred parameter is the
image of the source parametrization. -/
theorem apply_param (hs : s ∈ I) : f' (transferParam f f' g s) = g (f s) :=
  apply_arcParam (h.mem_image_map hs)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.ArcMatch.apply_param then
    throwError "Refusing to shadow existing declaration Schoenflies.ArcMatch.apply_param"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.ArcMatch.apply_param ``Submission.Schoenflies.ArcMatch.apply_param

/-- The transferred parameter is characterized, not merely chosen. -/
theorem param_eq (hu : u ∈ I) (heq : f' u = g (f s)) : transferParam f f' g s = u :=
  arcParam_eq_of_apply h.injOn_tgt hu heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.ArcMatch.param_eq then
    throwError "Refusing to shadow existing declaration Schoenflies.ArcMatch.param_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.ArcMatch.param_eq ``Submission.Schoenflies.ArcMatch.param_eq

theorem injOn_param : _root_.Set.InjOn (transferParam f f' g) I := by
  intro s hs u hu hsu
  -- Equal transferred parameters give equal images, and both maps are injective.
  have : g (f s) = g (f u) := by
    rw [← h.apply_param hs, ← h.apply_param hu, hsu]
  exact h.injOn_src hs hu (h.injOn_map ⟨s, hs, rfl⟩ ⟨u, hu, rfl⟩ this)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.ArcMatch.injOn_param then
    throwError "Refusing to shadow existing declaration Schoenflies.ArcMatch.injOn_param"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.ArcMatch.injOn_param ``Submission.Schoenflies.ArcMatch.injOn_param

/-- **The transfer map is continuous.** This is the continuity of the inverse parametrization
`f'⁻¹`, in the only form needed, and it is proved from the fact that a parametrization is an open
map onto its arc: a prescribed parameter window around `transferParam f f' g s` pulls back to a
ball around `g (f s)`, and continuity of `g ∘ f` turns that into a parameter window around `s`. -/
theorem continuousOn_param : ContinuousOn (transferParam f f' g) I := by
  intro s hs
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  set u₀ := transferParam f f' g s with hu₀
  have hu₀I : u₀ ∈ I := h.param_mem_I hs
  have hval : f' u₀ = g (f s) := h.apply_param hs
  -- The point `g (f s)` is the image of the parameter window `Ioo (u₀ - ε) (u₀ + ε)`.
  have hx : g (f s) ∈ f' '' (_root_.Set.Ioo (u₀ - ε) (u₀ + ε) ∩ I) :=
    ⟨u₀, ⟨⟨by linarith, by linarith⟩, hu₀I⟩, hval⟩
  obtain ⟨r, hr, hball⟩ :=
    exists_ball_inter_subset_image h.continuousOn_tgt h.injOn_tgt isOpen_Ioo hx
  -- `g ∘ f` is continuous within the parameter interval at `s`.
  have hcomp : ContinuousWithinAt (fun x => g (f x)) I s :=
    (h.continuousOn_map (f s) ⟨s, hs, rfl⟩).comp (h.continuousOn_src s hs) (_root_.Set.mapsTo_image f I)
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousWithinAt_iff.mp hcomp r hr
  refine ⟨δ, hδ, fun {x} hxI hxs => ?_⟩
  have hin : g (f x) ∈ Metric.ball (g (f s)) r ∩ f' '' I :=
    ⟨Metric.mem_ball.mpr (hclose hxI hxs), h.mem_image_map hxI⟩
  obtain ⟨v, ⟨hvw, hvI⟩, hveq⟩ := hball hin
  -- Injectivity of `f'` identifies that parameter with the transferred one.
  have : transferParam f f' g x = v :=
    h.injOn_tgt (h.param_mem_I hxI) hvI ((h.apply_param hxI).trans hveq.symm)
  rw [Real.dist_eq, this, abs_lt]
  exact ⟨by linarith [hvw.1], by linarith [hvw.2]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.ArcMatch.continuousOn_param then
    throwError "Refusing to shadow existing declaration Schoenflies.ArcMatch.continuousOn_param"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.ArcMatch.continuousOn_param ``Submission.Schoenflies.ArcMatch.continuousOn_param

/-- **The transfer map is strictly monotone**, in one direction or the other. Which one is
decided by the endpoints; every conclusion below that does not mention an endpoint holds in
both cases. -/
theorem strictMonoOn_or_strictAntiOn_param :
    StrictMonoOn (transferParam f f' g) I ∨ StrictAntiOn (transferParam f f' g) I :=
  ContinuousOn.strictMonoOn_of_injOn_Icc' zero_le_one h.continuousOn_param h.injOn_param

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.ArcMatch.strictMonoOn_or_strictAntiOn_param then
    throwError "Refusing to shadow existing declaration Schoenflies.ArcMatch.strictMonoOn_or_strictAntiOn_param"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.ArcMatch.strictMonoOn_or_strictAntiOn_param ``Submission.Schoenflies.ArcMatch.strictMonoOn_or_strictAntiOn_param

/-- **Every target parameter is hit.** `g` is onto the target arc and `f'` parametrizes it, so
the transfer map is onto `[0, 1]` — this is where `image_eq` earns its keep. -/
theorem surjOn_param : I ⊆ transferParam f f' g '' I := by
  intro v hv
  have hmem : f' v ∈ g '' (f '' I) := by rw [h.image_eq]; exact ⟨v, hv, rfl⟩
  obtain ⟨y, ⟨x, hx, rfl⟩, hy⟩ := hmem
  exact ⟨x, hx, h.param_eq hv hy.symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.ArcMatch.surjOn_param then
    throwError "Refusing to shadow existing declaration Schoenflies.ArcMatch.surjOn_param"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.ArcMatch.surjOn_param ``Submission.Schoenflies.ArcMatch.surjOn_param

/-- The transfer map is a bijection of the parameter interval. -/
theorem image_param_I : transferParam f f' g '' I = I :=
  subset_antisymm (by rintro _ ⟨x, hx, rfl⟩; exact h.param_mem_I hx) h.surjOn_param

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.ArcMatch.image_param_I then
    throwError "Refusing to shadow existing declaration Schoenflies.ArcMatch.image_param_I"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.ArcMatch.image_param_I ``Submission.Schoenflies.ArcMatch.image_param_I

/-! ### The image of a parameter interval -/

theorem param_mem_uIcc (hs : s ∈ I) (hu : u ∈ I) {x : ℝ} (hx : x ∈ _root_.Set.uIcc s u) :
    transferParam f f' g x ∈ _root_.Set.uIcc (transferParam f f' g s) (transferParam f f' g u) := by
  have hxI : x ∈ I := uIcc_subset_I hs hu hx
  rw [_root_.Set.mem_uIcc] at hx ⊢
  rcases h.strictMonoOn_or_strictAntiOn_param with hm | hm
  · rcases hx with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨hm.monotoneOn hs hxI h₁, hm.monotoneOn hxI hu h₂⟩
    · exact Or.inr ⟨hm.monotoneOn hu hxI h₁, hm.monotoneOn hxI hs h₂⟩
  · rcases hx with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inr ⟨hm.antitoneOn hxI hu h₂, hm.antitoneOn hs hxI h₁⟩
    · exact Or.inl ⟨hm.antitoneOn hxI hs h₂, hm.antitoneOn hu hxI h₁⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.ArcMatch.param_mem_uIcc then
    throwError "Refusing to shadow existing declaration Schoenflies.ArcMatch.param_mem_uIcc"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.ArcMatch.param_mem_uIcc ``Submission.Schoenflies.ArcMatch.param_mem_uIcc

/-- **The transfer map carries a parameter interval onto the corresponding one.** Stated over
`uIcc`, so it is indifferent to the direction of either traversal. -/
theorem image_param_uIcc (hs : s ∈ I) (hu : u ∈ I) :
    transferParam f f' g '' _root_.Set.uIcc s u =
      uIcc (transferParam f f' g s) (transferParam f f' g u) := by
  refine subset_antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact h.param_mem_uIcc hs hu hx
  · -- The reverse inclusion is the intermediate value theorem; no monotonicity needed.
    exact intermediate_value_uIcc (h.continuousOn_param.mono (uIcc_subset_I hs hu))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.ArcMatch.image_param_uIcc then
    throwError "Refusing to shadow existing declaration Schoenflies.ArcMatch.image_param_uIcc"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.ArcMatch.image_param_uIcc ``Submission.Schoenflies.ArcMatch.image_param_uIcc

/-- **The map carries a subarc onto the corresponding subarc.** The form every consumer wants,
and the reason for this file. -/
theorem image_image_uIcc (hs : s ∈ I) (hu : u ∈ I) :
    g '' (f '' _root_.Set.uIcc s u) =
      f' '' _root_.Set.uIcc (transferParam f f' g s) (transferParam f f' g u) := by
  rw [← h.image_param_uIcc hs hu, ← _root_.Set.image_comp, ← _root_.Set.image_comp]
  refine _root_.Set.image_congr fun x hx => ?_
  exact (h.apply_param (uIcc_subset_I hs hu hx)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.ArcMatch.image_image_uIcc then
    throwError "Refusing to shadow existing declaration Schoenflies.ArcMatch.image_image_uIcc"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.ArcMatch.image_image_uIcc ``Submission.Schoenflies.ArcMatch.image_image_uIcc

/-- The same in the vocabulary of `Schoenflies/Subarc.lean`. -/
theorem image_subarc (hs : s ∈ I) (hu : u ∈ I) :
    g '' (subarc f s u '' I) =
      subarc f' (transferParam f f' g s) (transferParam f f' g u) '' I := by
  rw [subarc_image, subarc_image, h.image_image_uIcc hs hu]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.ArcMatch.image_subarc then
    throwError "Refusing to shadow existing declaration Schoenflies.ArcMatch.image_subarc"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.ArcMatch.image_subarc ``Submission.Schoenflies.ArcMatch.image_subarc

/-! ### Matching endpoints -/

section Endpoints

variable (h0 : g (f 0) = f' 0)
include h0

theorem param_zero : transferParam f f' g 0 = 0 := h.param_eq zero_mem_I h0.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.ArcMatch.param_zero then
    throwError "Refusing to shadow existing declaration Schoenflies.ArcMatch.param_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.ArcMatch.param_zero ``Submission.Schoenflies.ArcMatch.param_zero

/-- With the starting points matched the transfer map increases. If it decreased, the whole
interval would map below `transferParam f f' g 0 = 0`, which is impossible since transferred
parameters lie in `[0, 1]`. -/
theorem strictMonoOn_param : StrictMonoOn (transferParam f f' g) I := by
  rcases h.strictMonoOn_or_strictAntiOn_param with hm | hm
  · exact hm
  · exact absurd (hm zero_mem_I one_mem_I zero_lt_one)
      (by rw [h.param_zero h0]; exact not_lt.2 (h.param_mem_I one_mem_I).1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.ArcMatch.strictMonoOn_param then
    throwError "Refusing to shadow existing declaration Schoenflies.ArcMatch.strictMonoOn_param"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.ArcMatch.strictMonoOn_param ``Submission.Schoenflies.ArcMatch.strictMonoOn_param

theorem param_one : transferParam f f' g 1 = 1 := by
  -- The parameter `1` is attained somewhere, and the transfer map is largest at `1`.
  obtain ⟨x, hx, hxv⟩ := h.surjOn_param one_mem_I
  have hge := (h.strictMonoOn_param h0).monotoneOn hx one_mem_I hx.2
  rw [hxv] at hge
  exact le_antisymm (h.param_mem_I one_mem_I).2 hge

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.ArcMatch.param_one then
    throwError "Refusing to shadow existing declaration Schoenflies.ArcMatch.param_one"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.ArcMatch.param_one ``Submission.Schoenflies.ArcMatch.param_one

/-- **Initial subarcs correspond.** -/
theorem image_initial (hu : u ∈ I) :
    g '' (f '' _root_.Set.Icc 0 u) = f' '' _root_.Set.Icc 0 (transferParam f f' g u) := by
  have := h.image_image_uIcc zero_mem_I hu
  rwa [_root_.Set.uIcc_of_le hu.1, h.param_zero h0, _root_.Set.uIcc_of_le (h.param_mem_I hu).1] at this

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.ArcMatch.image_initial then
    throwError "Refusing to shadow existing declaration Schoenflies.ArcMatch.image_initial"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.ArcMatch.image_initial ``Submission.Schoenflies.ArcMatch.image_initial

/-- **Terminal subarcs correspond.** -/
theorem image_terminal (hu : u ∈ I) :
    g '' (f '' _root_.Set.Icc u 1) = f' '' _root_.Set.Icc (transferParam f f' g u) 1 := by
  have := h.image_image_uIcc hu one_mem_I
  rwa [_root_.Set.uIcc_of_le hu.2, h.param_one h0, _root_.Set.uIcc_of_le (h.param_mem_I hu).2] at this

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.ArcMatch.image_terminal then
    throwError "Refusing to shadow existing declaration Schoenflies.ArcMatch.image_terminal"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.ArcMatch.image_terminal ``Submission.Schoenflies.ArcMatch.image_terminal

/-- An interior parameter transfers to an interior parameter. -/
theorem param_mem_Ioo (hu : u ∈ _root_.Set.Ioo (0 : ℝ) 1) : transferParam f f' g u ∈ _root_.Set.Ioo (0 : ℝ) 1 := by
  have hm := h.strictMonoOn_param h0
  refine ⟨?_, ?_⟩
  · rw [← h.param_zero h0]
    exact hm zero_mem_I (_root_.Set.Ioo_subset_Icc_self hu) hu.1
  · rw [← h.param_one h0]
    exact hm (_root_.Set.Ioo_subset_Icc_self hu) one_mem_I hu.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.ArcMatch.param_mem_Ioo then
    throwError "Refusing to shadow existing declaration Schoenflies.ArcMatch.param_mem_Ioo"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.ArcMatch.param_mem_Ioo ``Submission.Schoenflies.ArcMatch.param_mem_Ioo

end Endpoints

/-- An interior parameter transfers to an interior parameter, without assuming which way the two
parametrizations run: the two endpoints go to the two endpoints in one order or the other, and
strict monotonicity keeps the inside inside. -/
theorem param_mem_Ioo_of_ends (hends : (transferParam f f' g 0 = 0 ∧ transferParam f f' g 1 = 1) ∨
    (transferParam f f' g 0 = 1 ∧ transferParam f f' g 1 = 0)) (hu : u ∈ _root_.Set.Ioo (0 : ℝ) 1) :
    transferParam f f' g u ∈ _root_.Set.Ioo (0 : ℝ) 1 := by
  have huI : u ∈ I := _root_.Set.Ioo_subset_Icc_self hu
  rcases h.strictMonoOn_or_strictAntiOn_param with hm | hm
  · rcases hends with ⟨e0, e1⟩ | ⟨e0, e1⟩
    · have hlo := hm zero_mem_I huI hu.1
      have hhi := hm huI one_mem_I hu.2
      rw [e0] at hlo
      rw [e1] at hhi
      exact ⟨hlo, hhi⟩
    · -- Increasing yet sending `0` above `1`: impossible.
      have := hm zero_mem_I one_mem_I zero_lt_one
      rw [e0, e1] at this
      linarith
  · rcases hends with ⟨e0, e1⟩ | ⟨e0, e1⟩
    · have := hm zero_mem_I one_mem_I zero_lt_one
      rw [e0, e1] at this
      linarith
    · have hlo := hm huI one_mem_I hu.2
      have hhi := hm zero_mem_I huI hu.1
      rw [e1] at hlo
      rw [e0] at hhi
      exact ⟨hlo, hhi⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.ArcMatch.param_mem_Ioo_of_ends then
    throwError "Refusing to shadow existing declaration Schoenflies.ArcMatch.param_mem_Ioo_of_ends"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.ArcMatch.param_mem_Ioo_of_ends ``Submission.Schoenflies.ArcMatch.param_mem_Ioo_of_ends

end ArcMatch

end Schoenflies
