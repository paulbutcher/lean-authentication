/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Authentication.Attempt

/-!
State machine theorems (AUTH-16.1) and the adversarial cases of AUTH-16.7 that the pure layer
can answer on its own.
-/

namespace Tests.Attempt
open Authentication Authentication.Attempt

variable {tenant : TenantId} {config : TenantConfig tenant} {now : Timestamp}
  {state : AttemptState tenant} {event : AttemptEvent}

/-- The result issues a session. -/
def issuesSession {tenant : TenantId}
    (result : Except AuthError (AttemptState tenant × List (Effect tenant))) : Prop :=
  ∃ next effects subject, result = .ok (next, effects) ∧ Effect.issueSession subject ∈ effects

/-- The result moves the attempt to `completed`. -/
def completes {tenant : TenantId}
    (result : Except AuthError (AttemptState tenant × List (Effect tenant))) : Prop :=
  ∃ next effects, result = .ok (next, effects) ∧ next.phase = .completed

theorem terminal_rejects_everything (h : state.phase.isLive = false) :
    step config now state event = .error .attemptNotLive := by
  simp [step, h]

/-- AUTH-16.1: a completed attempt cannot complete again. -/
theorem completed_rejects_everything (h : state.phase = .completed) :
    step config now state event = .error .attemptNotLive :=
  terminal_rejects_everything (by simp [h, AttemptPhase.isLive])

theorem expired_rejects_everything (h : state.phase = .expired) :
    step config now state event = .error .attemptNotLive :=
  terminal_rejects_everything (by simp [h, AttemptPhase.isLive])

theorem abandoned_rejects_everything (h : state.phase = .abandoned) :
    step config now state event = .error .attemptNotLive :=
  terminal_rejects_everything (by simp [h, AttemptPhase.isLive])

/-- AUTH-16.1: no transition into `completed` from `expired` or `abandoned`. -/
theorem no_completion_from_expired (h : state.phase = .expired) :
    ¬ completes (step config now state event) := by
  simp [completes, expired_rejects_everything h]

theorem no_completion_from_abandoned (h : state.phase = .abandoned) :
    ¬ completes (step config now state event) := by
  simp [completes, abandoned_rejects_everything h]

theorem no_completion_from_completed (h : state.phase = .completed) :
    ¬ completes (step config now state event) := by
  simp [completes, completed_rejects_everything h]

/-- AUTH-16.1: the verification code cannot complete an attempt that is still `pending`. The
code is only shown by opening the link, and opening the link is what makes the attempt
`revealed` (AUTH-5.2.6). -/
theorem no_completion_from_pending_by_code (h : state.phase = .pending)
    (cookie code : PresentedSecret) :
    ¬ completes (step config now state (.revealedCodeSubmitted cookie code)) := by
  simp only [completes, step, h, AttemptPhase.isLive]
  split
  · simp
  · split <;> simp

/-- AUTH-5.2.8: expiry is decided from the clock, so a record left `pending` past its time
completes for nobody. -/
theorem no_completion_after_expiry (h : state.expiresAt ≤ now) :
    ¬ completes (step config now state event) := by
  simp only [completes, step]
  split
  · simp
  · simp

/-- AUTH-5.2.1: opening the magic link is a `GET` that issues no session, whichever device it
arrives on. This is the requirement that keeps the product usable behind mail gateways that
prefetch links, and AUTH-16.7's first adversarial case. -/
theorem link_never_issues_session (token : PresentedSecret) (cookie : Option PresentedSecret) :
    ¬ issuesSession (step config now state (.linkOpened token cookie)) := by
  simp only [issuesSession, step]
  split
  · simp
  · split
    · simp
    · split
      · simp
      · rintro ⟨next, effects, subject, hok, hmem⟩
        simp only [Except.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨-, rfl⟩ := hok
        revert hmem
        split <;> simp

end Tests.Attempt
