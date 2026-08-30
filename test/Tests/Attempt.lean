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

/--
The three phases with no way forward behave as one: an attempt in any of them refuses every
event, with the error that names the reason. The three theorems below are corollaries, and this
is where the case analysis is done.

`AttemptPhase.isLive` answers `true` for `pending` and `revealed` and `false` for `completed`,
`expired` and `abandoned`, so `h` says the attempt is in one of the latter three. `event` is
unconstrained, and so are `config` and `now`: neither the configuration nor the moment can
revive the record. The conclusion is an equality rather than a bare refusal, so the result is
`.error .attemptNotLive` exactly, which is what lets a caller tell a spent attempt from a wrong
secret.
-/
theorem terminal_rejects_everything (h : state.phase.isLive = false) :
    step config now state event = .error .attemptNotLive := by
  simp [step, h]

/--
AUTH-16.1: a completed attempt cannot complete again. A successful sign-in spends its record, so
the confirmation that issued a session cannot be replayed for a second one.

`h` fixes the phase at `completed`. `event` is unconstrained, so a resubmitted confirmation, a
code entered late, and a superseding event are covered alike. The conclusion is the exact error
`.attemptNotLive`. It follows from `terminal_rejects_everything`, `AttemptPhase.isLive` being
`false` at `completed`.
-/
theorem completed_rejects_everything (h : state.phase = .completed) :
    step config now state event = .error .attemptNotLive :=
  terminal_rejects_everything (by simp [h, AttemptPhase.isLive])

/--
An attempt whose phase records expiry refuses every event, and does so without consulting the
clock again. This is what a link that has sat in a mailbox past its lifetime is worth.

`h` fixes the phase at `expired`. `event` and `now` are both unconstrained; in particular the
statement is not that the moment is late, only that the record says the attempt is over. The
conclusion is the exact error `.attemptNotLive`, which is distinct from `.attemptExpired`: the
latter is what `step` answers when it is the clock rather than the phase that closes an attempt.
-/
theorem expired_rejects_everything (h : state.phase = .expired) :
    step config now state event = .error .attemptNotLive :=
  terminal_rejects_everything (by simp [h, AttemptPhase.isLive])

/--
An attempt abandoned in favour of a later one refuses every event. Starting a second sign-in
therefore closes the first, rather than leaving two records that could each still issue.

`h` fixes the phase at `abandoned`, which `step` sets on `.superseded`. `event` is unconstrained,
so the older attempt's own link and code are refused along with everything else. The conclusion
is the exact error `.attemptNotLive`, not merely some failure. It follows from
`terminal_rejects_everything`, `AttemptPhase.isLive` being `false` at `abandoned`.
-/
theorem abandoned_rejects_everything (h : state.phase = .abandoned) :
    step config now state event = .error .attemptNotLive :=
  terminal_rejects_everything (by simp [h, AttemptPhase.isLive])

/--
An expired attempt cannot complete. Once the phase records expiry no later event revives the
record, so a link found in an old mailbox is worth nothing however it is presented.

`h` fixes the phase at `expired`. `event` ranges over the whole of `AttemptEvent`, and `now` is
unconstrained, so the claim does not rest on the clock: the recorded phase alone closes the
record. `completes` holds when the step succeeds with `completed` as the next phase, and the
conclusion denies it. The other half of AUTH-16.1, that the clock closes an attempt whose phase
has not yet been updated, is `no_completion_after_expiry` below.
-/
theorem no_completion_from_expired (h : state.phase = .expired) :
    ¬ completes (step config now state event) := by
  simp [completes, expired_rejects_everything h]

/--
An attempt abandoned because a later one superseded it cannot go on to complete. This is what
makes starting a second sign-in safe: the first is spent rather than merely ignored, so two
outstanding links cannot each yield a session.

`h` fixes the phase at `abandoned`, which `step` sets when it processes `.superseded`. `event`
is unconstrained, so the older attempt's own link and code are covered along with everything
else. `completes` holds when the step succeeds and moves to `completed`, and the conclusion
denies it.
-/
theorem no_completion_from_abandoned (h : state.phase = .abandoned) :
    ¬ completes (step config now state event) := by
  simp [completes, abandoned_rejects_everything h]

/--
Completing is not repeatable: a record already in `completed` cannot be driven there again.
The transition into that phase is what issues the session, so a repeat would be a second session
on one sign-in, which is the shape a replayed confirmation takes.

`h` fixes the phase at `completed`. `event` is unconstrained, so no event is exempted, and
`config`, `now` and `state` are otherwise arbitrary. `completes` holds of a result when the step
succeeds and the next phase is `completed`; the conclusion denies it. It follows from
`completed_rejects_everything`, which yields an error, and an error is not a success at all.
-/
theorem no_completion_from_completed (h : state.phase = .completed) :
    ¬ completes (step config now state event) := by
  simp [completes, completed_rejects_everything h]

/--
AUTH-16.1: the verification code cannot complete an attempt that is still `pending`. The code is
only shown by opening the link, and opening the link is what makes the attempt `revealed`
(AUTH-5.2.6).

`h` fixes the phase at `pending`, the phase every attempt starts in, so the hypothesis is one
real states satisfy rather than one nothing reaches. The event is `.revealedCodeSubmitted cookie
code`, with both secrets arbitrary: the theorem does not suppose the code is wrong, so it holds
for the correct code as firmly as for a guess. `completes` holds when the step succeeds and
moves the attempt to `completed`, and the conclusion denies it, so someone who learns the code
without opening the link has nothing to spend it on.
-/
theorem no_completion_from_pending_by_code (h : state.phase = .pending)
    (cookie code : PresentedSecret) :
    ¬ completes (step config now state (.revealedCodeSubmitted cookie code)) := by
  simp only [completes, step, h, AttemptPhase.isLive]
  split
  · simp
  · split <;> simp

/--
AUTH-5.2.8: expiry is decided from the clock, so a record left `pending` past its time completes
for nobody. Nothing here depends on a sweep having run, which matters because the sweep is
periodic and the request is not.

`completes` holds of a result when the step succeeds and the phase it moves to is `completed`;
the conclusion denies it. `h` is the only hypothesis: the attempt's `expiresAt` is at or before
`now`, the moment the transition is taken. `event` is unconstrained, so link openings,
confirmations, both kinds of code submission, and supersession are covered alike, and `state`
may still be in a live phase, which is the case that matters: a `pending` or `revealed` record
whose phase nobody has updated yet completes for nothing.
-/
theorem no_completion_after_expiry (h : state.expiresAt ≤ now) :
    ¬ completes (step config now state event) := by
  simp only [completes, step]
  split
  · simp
  · simp

/--
AUTH-5.2.1: opening the magic link is a `GET` that issues no session, whichever device it
arrives on. This is the requirement that keeps the product usable behind mail gateways that
prefetch links, and AUTH-16.7's first adversarial case.

`issuesSession` holds of a result when the step succeeds and `Effect.issueSession` is among the
effects it emits; the conclusion denies it. The event is `.linkOpened token cookie`, and neither
argument is constrained: `token` is whatever secret arrived in the link, matching or not, and
`cookie` is `none` for a device that never held one as well as `some` for one that did, so the
same-device and cross-device readings are both covered. `config`, `now` and `state` are the
section variables and are equally unconstrained, so the attempt may be in any phase and at any
point relative to its expiry. What a prefetch can therefore do is move the attempt to `revealed`
and display a page, which is the whole of it.
-/
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
