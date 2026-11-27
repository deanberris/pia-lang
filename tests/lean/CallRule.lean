/-
The verifier's call rule, and what it does and does not lose.

`src/verify/Verifier.cpp` (`stepCall`, docs/verifier.md "Calls") takes a
call on its callee's contract, never its body: the precondition is a goal at
the arguments, the result is fresh, and the postcondition is assumed about
it. This file models that rule over a small language of function bodies and
proves:

1. `partial_sound`: the rule is sound for code that runs. Every execution of
   a verified program that returns meets its contract, for every callee
   body that was itself verified against its contract: mutual recursion
   included, with no termination argument.
2. `ghost_unsound`: the rule is not sound for calls that never run (lemma
   calls and calls in contracts, which codegen erases) unless each callee
   terminates. Two lemmas that call each other prove `False`, and a caller
   that returns 3 is proved to return 7. This was the bug fixed by the
   mutual recursion check (tests/verify/mutual_recursion.pia).
3. `total_sound`: with the termination goals the verifier now raises (a
   measure that decreases at each call within a cycle, and calls between
   cycles going down the call graph's DAG, `lex_descends`), every verified
   function terminates and meets its contract, erased calls included.
4. `modular`: a caller's proof depends only on the callees' contracts, so
   it holds for every implementation of them that is itself verified: what
   separate compilation and the interface hash rely on (ADR 0024, 0039).
   `refine_preserves` is the ABI evolution rule: a weaker precondition and a
   stronger postcondition keep every caller's proof.
5. `precision_gap`: modular proof is incomplete. A property that holds of
   the real callee can be unprovable from its contract.
   `strongest_complete`: taking each callee's contract to be exactly what
   its body computes (inlining it) proves every property that holds, and
   `strongest_not_modular` shows the price: such a proof does not survive a
   change to the callee's body that keeps its contract.

The model is deliberately small: one integer parameter and result per
function, and a body is a tree of calls whose continuations are Lean
functions, so branches and arithmetic are Lean's own. It is faithful to the
rule, which is all the theorems are about; it does not model buffers,
loops or overflow, whose goals are separate from the call rule.
-/

namespace Pia.CallRule

/-- A function's name. -/
abbrev Fn := Nat

/-- A body, with its parameter already substituted (`body f x`).
`call g a k` runs `g a` and continues with its result. `ghost g a b` is a
call the verifier assumes but codegen erases: a lemma call, or a call in a
contract; the code continues with `b` and never runs `g`. -/
inductive Body where
  | ret : Int → Body
  | call : Fn → Int → (Int → Body) → Body
  | ghost : Fn → Int → Body → Body

/-- A program: each function's body at each argument. -/
structure Program where
  body : Fn → Int → Body

/-- Contracts: each function's precondition and postcondition. -/
structure Contracts where
  pre : Fn → Int → Prop
  post : Fn → Int → Int → Prop

/-- What the compiled code does: big-step, so only runs that return.
A ghost call is erased, so it runs nothing. -/
inductive Exec (P : Program) : Body → Int → Prop where
  | ret {v} : Exec P (.ret v) v
  | call {g a k r v} :
      Exec P (P.body g a) r → Exec P (k r) v → Exec P (.call g a k) v
  | ghost {g a b v} : Exec P b v → Exec P (.ghost g a b) v

/-- The verifier's call rule as a weakest precondition: at a call, the
callee's precondition is a goal, and for a fresh result its postcondition
is assumed. An erased call is treated the same way. -/
def wp (C : Contracts) : Body → (Int → Prop) → Prop
  | .ret v, Q => Q v
  | .call g a k, Q => C.pre g a ∧ ∀ r, C.post g a r → wp C (k r) Q
  | .ghost g a b, Q => C.pre g a ∧ ∀ r, C.post g a r → wp C b Q

/-- A program is verified when each body, run on an argument that meets the
precondition, establishes the postcondition under the call rule. -/
def Verified (C : Contracts) (P : Program) : Prop :=
  ∀ f x, C.pre f x → wp C (P.body f x) (C.post f x)

/-- Whether a body erases any call. -/
def NoGhost : Body → Prop
  | .ret _ => True
  | .call _ _ k => ∀ r, NoGhost (k r)
  | .ghost _ _ _ => False

/-! ## 1. Soundness for code that runs -/

/-- Partial correctness: in a program with no erased calls, every run that
returns meets the contract. The induction is on the run, so a callee's
contract is available for any call that returns, recursive or not. -/
theorem partial_sound (C : Contracts) (P : Program) (hv : Verified C P)
    (hng : ∀ f x, NoGhost (P.body f x)) :
    ∀ f x v, C.pre f x → Exec P (P.body f x) v → C.post f x v := by
  -- Generalise over the body run and the postcondition it must meet.
  have key : ∀ b v, Exec P b v → NoGhost b → ∀ Q, wp C b Q → Q v := by
    intro b v h
    induction h with
    | ret => intro _ Q hw; exact hw
    | @call g a k r v hg hk ihg ihk =>
      intro hn Q hw
      obtain ⟨hpre, hpost⟩ := hw
      have hr : C.post g a r := ihg (hng g a) (C.post g a) (hv g a hpre)
      exact ihk (hn r) Q (hpost r hr)
    | ghost _ _ => intro hn; exact hn.elim
  intro f x v hpre h
  exact key _ _ h (hng f x) _ (hv f x hpre)

/-! ## 2. Erased calls without termination: unsound -/

namespace Ghost

/-- `lemma a x = b x`, `lemma b x = a x`, both `ensures false`, and
`seven x = a 0; 3`, which claims `ensures result = 7`. -/
def prog : Program where
  body
    | 0, x => .call 1 x .ret
    | 1, x => .call 0 x .ret
    | _, _ => .ghost 0 0 (.ret 3)

def contracts : Contracts where
  pre _ _ := True
  post
    | 0, _, _ => False
    | 1, _, _ => False
    | _, _, r => r = 7

theorem verified : Verified contracts prog := by
  intro f x _
  match f with
  | 0 => exact ⟨trivial, fun _ h => h.elim⟩
  | 1 => exact ⟨trivial, fun _ h => h.elim⟩
  | n + 2 => exact ⟨trivial, fun _ h => h.elim⟩

theorem runs_to_three : Exec prog (prog.body 2 0) 3 :=
  Exec.ghost Exec.ret

end Ghost

/-- The call rule alone, with erased calls and no termination check, is
unsound: a verified program returns 3 where its contract says 7. -/
theorem ghost_unsound :
    ∃ C P, Verified C P ∧ ∃ f x v, C.pre f x ∧ Exec P (P.body f x) v ∧
      ¬ C.post f x v :=
  ⟨Ghost.contracts, Ghost.prog, Ghost.verified, 2, 0, 3, trivial,
    Ghost.runs_to_three, fun h => (by decide : ¬ ((3 : Int) = 7)) h⟩

/-! ## 3. Termination makes erased calls sound -/

/-- The call rule with the termination goal: each call, erased or not, goes
to a pair `(g, a)` below the caller's `(f, x)` in `R`. -/
def wpT (C : Contracts) (R : Fn × Int → Fn × Int → Prop) (me : Fn × Int) :
    Body → (Int → Prop) → Prop
  | .ret v, Q => Q v
  | .call g a k, Q =>
      C.pre g a ∧ R (g, a) me ∧ ∀ r, C.post g a r → wpT C R me (k r) Q
  | .ghost g a b, Q =>
      C.pre g a ∧ R (g, a) me ∧ ∀ r, C.post g a r → wpT C R me b Q

def VerifiedT (C : Contracts) (R : Fn × Int → Fn × Int → Prop)
    (P : Program) : Prop :=
  ∀ f x, C.pre f x → wpT C R (f, x) (P.body f x) (C.post f x)

/-- Total correctness: if every call descends in a well-founded relation,
every function called within its precondition returns, and meets its
postcondition. Erased calls are sound because each callee does return
some result, so assuming its postcondition about a fresh one is
consistent. -/
theorem total_sound (C : Contracts) (R : Fn × Int → Fn × Int → Prop)
    (wf : WellFounded R) (P : Program) (hv : VerifiedT C R P) :
    ∀ f x, C.pre f x → ∃ v, Exec P (P.body f x) v ∧ C.post f x v := by
  intro f x
  -- Well-founded induction on the caller.
  refine wf.induction (C := fun p => C.pre p.1 p.2 →
      ∃ v, Exec P (P.body p.1 p.2) v ∧ C.post p.1 p.2 v) (f, x) ?_
  intro ⟨f, x⟩ ih hpre
  -- Structural induction on the body, with the callees below it.
  have key : ∀ b Q, wpT C R (f, x) b Q → ∃ v, Exec P b v ∧ Q v := by
    intro b
    induction b with
    | ret v => intro Q hw; exact ⟨v, Exec.ret, hw⟩
    | call g a k ihk =>
      intro Q hw
      obtain ⟨hpre', hR, hpost⟩ := hw
      obtain ⟨r, hr, hp⟩ := ih (g, a) hR hpre'
      obtain ⟨v, hk, hq⟩ := ihk r Q (hpost r hp)
      exact ⟨v, Exec.call hr hk, hq⟩
    | ghost g a b ihb =>
      intro Q hw
      obtain ⟨hpre', hR, hpost⟩ := hw
      obtain ⟨r, _, hp⟩ := ih (g, a) hR hpre'
      obtain ⟨v, hb, hq⟩ := ihb Q (hpost r hp)
      exact ⟨v, Exec.ghost hb, hq⟩
  exact key _ _ (hv f x hpre)

/-- The relation the verifier's goals establish. `rank` numbers the call
graph's cycles (strongly connected components) in topological order, so a
call never goes to a higher rank (Tarjan's algorithm, `markRecursiveGroups`).
A call to a lower rank needs nothing. A call within a cycle, recursive or
mutual, needs the goal "the measure of 'g' at the call is below the measure
of 'f'": `0 ≤ μ f x ∧ μ g a < μ f x` (`decreasesTerm`). -/
def Descends (rank : Fn → Nat) (μ : Fn → Int → Int) (q p : Fn × Int) : Prop :=
  rank q.1 < rank p.1 ∨
    (rank q.1 = rank p.1 ∧ 0 ≤ μ p.1 p.2 ∧ μ q.1 q.2 < μ p.1 p.2)

/-- That relation is well-founded: it lies inside the lexicographic order on
`(rank, μ + 1)`, both as naturals. -/
theorem lex_descends (rank : Fn → Nat) (μ : Fn → Int → Int) :
    WellFounded (Descends rank μ) := by
  let key : Fn × Int → Nat × Nat := fun p => (rank p.1, (μ p.1 p.2 + 1).toNat)
  have wfLex : WellFounded (Prod.Lex (· < ·) (· < ·) : Nat × Nat → Nat × Nat → Prop) :=
    (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf
  apply Subrelation.wf (r := InvImage (Prod.Lex (· < ·) (· < ·)) key) _ (InvImage.wf key wfLex)
  intro q p h
  simp only [InvImage, key]
  rcases h with h | ⟨heq, hnn, hlt⟩
  · exact Prod.Lex.left _ _ h
  · rw [heq]
    apply Prod.Lex.right
    omega

/-- The verifier as it now is: total correctness for every program whose
calls meet the rank-and-measure goals. -/
theorem verifier_sound (C : Contracts) (rank : Fn → Nat) (μ : Fn → Int → Int)
    (P : Program) (hv : VerifiedT C (Descends rank μ) P) :
    ∀ f x, C.pre f x → ∃ v, Exec P (P.body f x) v ∧ C.post f x v :=
  total_sound C _ (lex_descends rank μ) P hv

/-- And no run of such a program breaks a contract, which is the property
`ghost_unsound` lacked. -/
theorem verifier_partial (C : Contracts) (rank : Fn → Nat) (μ : Fn → Int → Int)
    (P : Program) (hv : VerifiedT C (Descends rank μ) P) :
    ∀ f x v, C.pre f x → Exec P (P.body f x) v → C.post f x v := by
  -- Runs are deterministic, so the run that returns is the one
  -- `verifier_sound` found.
  have det : ∀ b v, Exec P b v → ∀ w, Exec P b w → v = w := by
    intro b v h
    induction h with
    | ret => intro w hw; cases hw; rfl
    | call _ _ ihg ihk =>
      intro w hw
      cases hw with
      | call hg' hk' =>
        have := ihg _ hg'
        subst this
        exact ihk _ hk'
    | ghost _ ih => intro w hw; cases hw with | ghost hb => exact ih _ hb
  intro f x v hpre h
  obtain ⟨w, hw, hp⟩ := verifier_sound C rank μ P hv f x hpre
  rw [det _ _ h _ hw]
  exact hp

/-! ## 4. Modularity: proofs against contracts survive any verified callee -/

/-- A caller's goals mention only contracts: if its body meets the call rule
under `C`, then in every program that agrees on the caller's body and is
verified against `C` (any implementation of the callees, linked in later),
the caller meets its contract. -/
theorem modular (C : Contracts) (rank : Fn → Nat) (μ : Fn → Int → Int)
    (f : Fn) (b : Int → Body) :
    ∀ P : Program, VerifiedT C (Descends rank μ) P → P.body f = b →
      ∀ x, C.pre f x → ∃ v, Exec P (b x) v ∧ C.post f x v := by
  intro P hv hb x hpre
  have := verifier_sound C rank μ P hv f x hpre
  rw [hb] at this
  exact this

/-- `C'` refines `C` when each precondition is weaker and each postcondition,
where the old precondition holds, stronger: ADR 0024's rule for a new
version of an interface. -/
def Refines (C' C : Contracts) : Prop :=
  (∀ g a, C.pre g a → C'.pre g a) ∧ (∀ g a r, C.pre g a → C'.post g a r → C.post g a r)

/-- Refinement keeps every caller's proof: what a caller proved against the
old contract it still proves against the new one. -/
theorem refine_preserves (C C' : Contracts) (h : Refines C' C)
    (R : Fn × Int → Fn × Int → Prop) (me : Fn × Int) :
    ∀ b Q, wpT C R me b Q → wpT C' R me b Q := by
  intro b
  induction b with
  | ret _ => intro Q hw; exact hw
  | call g a k ih =>
    intro Q ⟨hp, hR, hk⟩
    exact ⟨h.1 g a hp, hR, fun r hr => ih r Q (hk r (h.2 g a r hp hr))⟩
  | ghost g a b ih =>
    intro Q ⟨hp, hR, hk⟩
    exact ⟨h.1 g a hp, hR, fun r hr => ih Q (hk r (h.2 g a r hp hr))⟩

/-! ## 5. Precision: what a contract weaker than its body costs -/

namespace Gap

/-- `id x = x`, with the contract `requires x >= 0 ensures result >= 0`, and
`three () = id 3`, which claims `ensures result = 3`. -/
def prog : Program where
  body
    | 0, x => .ret x
    | _, _ => .call 0 3 .ret

def contracts : Contracts where
  pre
    | 0, x => 0 ≤ x
    | _, _ => True
  post
    | 0, _, r => 0 ≤ r
    | _, _, r => r = 3

/-- What the code does: `three` returns 3. -/
theorem three_returns_three : ∀ v, Exec prog (prog.body 1 0) v → v = 3 := by
  intro v h
  cases h with
  | call hg hk =>
    cases hg
    cases hk
    rfl

/-- What the call rule can show: nothing about `id 3` but `result >= 0`, so
`result = 3` is not provable. -/
theorem three_unprovable : ¬ wp contracts (prog.body 1 0) (contracts.post 1 0) := by
  intro ⟨_, h⟩
  have := h 4 (show (0 : Int) ≤ 4 by decide)
  exact (by decide : ¬ ((4 : Int) = 3)) this

end Gap

/-- Modular proof is incomplete: a property of the real program that the
call rule cannot prove. -/
theorem precision_gap :
    ∃ C P f x, (∀ v, Exec P (P.body f x) v → C.post f x v) ∧
      ¬ wp C (P.body f x) (C.post f x) :=
  ⟨Gap.contracts, Gap.prog, 1, 0, Gap.three_returns_three, Gap.three_unprovable⟩

/-- The strongest contract of a program: no precondition, and the
postcondition is exactly what the body returns. Using it at a call is
inlining the callee. -/
def strongest (P : Program) : Contracts where
  pre _ _ := True
  post g a r := Exec P (P.body g a) r

/-- With the strongest contracts the call rule is complete for partial
correctness: whatever every run of a body satisfies, the rule proves. -/
theorem strongest_complete (P : Program) :
    ∀ b Q, (∀ v, Exec P b v → Q v) → wp (strongest P) b Q := by
  intro b
  induction b with
  | ret v => intro Q h; exact h v Exec.ret
  | call g a k ih =>
    intro Q h
    exact ⟨trivial, fun r hr => ih r Q (fun v hv => h v (Exec.call hr hv))⟩
  | ghost g a b ih =>
    intro Q h
    exact ⟨trivial, fun _ _ => ih Q (fun v hv => h v (Exec.ghost hv))⟩

/-- But a proof against the strongest contract is a proof about one body.
`id' x = 0` also meets `id`'s published contract `result >= 0`, and with it
`three` returns 0: the proof of `result = 3`, made by inlining `id`, does
not survive a change to `id`'s body that keeps its interface. So an inlined
body has to be part of what a caller's proof depends on, the interface
hash, and a change to it is a change to the interface. -/
theorem strongest_not_modular :
    wp (strongest Gap.prog) (Gap.prog.body 1 0) (Gap.contracts.post 1 0) ∧
      ∃ P' : Program, P'.body 1 = Gap.prog.body 1 ∧
        (∀ x, Gap.contracts.pre 0 x → ∀ r, Exec P' (P'.body 0 x) r →
          Gap.contracts.post 0 x r) ∧
        Exec P' (P'.body 1 0) 0 := by
  refine ⟨strongest_complete _ _ _ Gap.three_returns_three, ?_⟩
  let P' : Program := ⟨fun f x => match f with
    | 0 => .ret 0
    | _ => Gap.prog.body 1 x⟩
  refine ⟨P', rfl, ?_, ?_⟩
  · intro x _ r h
    cases h
    show (0 : Int) ≤ 0
    decide
  · exact Exec.call Exec.ret Exec.ret

end Pia.CallRule

-- The proofs use only Lean's own axioms; CI fails on `sorryAx`.
#print axioms Pia.CallRule.partial_sound
#print axioms Pia.CallRule.ghost_unsound
#print axioms Pia.CallRule.verifier_sound
#print axioms Pia.CallRule.verifier_partial
#print axioms Pia.CallRule.modular
#print axioms Pia.CallRule.refine_preserves
#print axioms Pia.CallRule.precision_gap
#print axioms Pia.CallRule.strongest_complete
#print axioms Pia.CallRule.strongest_not_modular
