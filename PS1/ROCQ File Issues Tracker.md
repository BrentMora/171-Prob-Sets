# ROCQ File Issues Tracker

Files reviewed: `Basics.v`, `Lists.v`, `Logic.v`
Series: Software Foundations — Logical Foundations (Vol. 1)

---

## 1. Hard Errors (Compilation Failures)

### `involution_injective` — `Lists.v`

**Bug 1 — `destruct n1` before `n1` is introduced**

After `intros f H0`, the variables `n1` and `n2` are still universally
quantified in the goal. `destruct n1` fails because `n1` is not yet a local
hypothesis.

```coq
(* BUGGY *)
Proof.
  intros f H0. destruct n1.   (* n1 not in scope *)
  ...
```

Fix: introduce `n1` and `n2` first (the `destruct` is also unnecessary since
both branches are identical):

```coq
(* FIXED *)
Proof.
  intros f H0 n1 n2 H1.
  rewrite H0. rewrite H1. rewrite <- H0. reflexivity.
Qed.
```

---

**Bug 2 — `rewrite <- H1` in the wrong direction**

In the same proof, after `rewrite H0` the goal becomes `f(f(n1)) = n2`.
`H1 : f n1 = f n2`. The tactic `rewrite <- H1` looks for `f n2` to replace
with `f n1`, but `f n2` does not appear in the goal. The correct step is
`rewrite H1` (forward), replacing `f n1` with `f n2` to get `f(f(n2)) = n2`,
after which `rewrite <- H0` closes the goal.

```coq
(* BUGGY *)
- intros n2 H1. rewrite H0. rewrite <- H1. rewrite <- H0. reflexivity.

(* FIXED — same as above, single unified proof *)
intros f H0 n1 n2 H1.
rewrite H0. rewrite H1. rewrite <- H0. reflexivity.
```

---

## 2. Incomplete Proofs (Admitted)

### `de_morgan_4_classical` — `Logic.v`

```coq
Theorem de_morgan_4_classical : forall (P Q : Prop),
    ~ (~ P /\ Q) -> (P \/ ~ Q).
Proof.
Admitted.
```

This theorem is **unprovable in intuitionistic logic** — it requires the law
of excluded middle. The `Admitted` is logically justified but leaves a hole
in the proof development.

---

### `excluded_middle_irrefutable_classical` — `Logic.v`

This proof uses `de_morgan_4_classical` as a stepping stone, so it
**transitively inherits the hole** from the admitted lemma above.

Note: the same theorem is proved correctly and intuitionistically right below
it as `excluded_middle_irrefutable`, making the `_classical` version both
redundant and unsound:

```coq
(* Complete, sound, intuitionistic proof — already in the file *)
Theorem excluded_middle_irrefutable : forall (P : Prop), ~ ~ (P \/ ~ P).
Proof.
  unfold not. intros. apply H. right. intros. apply H. left. apply H0.
Qed.
```

---

## 3. Intentional Aborts (Pedagogical — Not True Bugs)

Three proofs in `Lists.v` are deliberately abandoned to illustrate why a
naive induction strategy fails. They are intentional and do not block
compilation, but they do leave dangling proof attempts in the file.

| Theorem | Reason Aborted |
|---|---|
| `repeat_double_firsttry` | IH too weak — cannot handle `c' + S c'` |
| `rev_length_firsttry` | No lemma yet connecting `++` and `length` |
| `app_rev_length_S_firsttry` | Intermediate helper attempt that also gets stuck |

Each abort drives the discovery of a correct helper lemma
(`repeat_plus` and `app_length_S` respectively).

---

## 4. Semantic / Naming Issue

### `next_working_day` — `Basics.v`

The function advances one day at a time through the full 7-day week,
including weekends:

```coq
| friday    => saturday   (* should be monday if truly "next working day" *)
| saturday  => sunday     (* should be monday *)
| sunday    => monday
```

The bug is **not caught by the existing test**:
```coq
(* this test only exercises weekdays — passes regardless *)
next_working_day (next_working_day monday) = wednesday
```

If the intent is to skip to the next actual working day, `friday`,
`saturday`, and `sunday` should all map to `monday`.

---

## Summary Table

| File | Location | Issue | Severity |
|---|---|---|---|
| `Lists.v` | `involution_injective` | `destruct n1` before `n1` is introduced | Compilation error |
| `Lists.v` | `involution_injective` | `rewrite <- H1` in wrong direction | Compilation error |
| `Logic.v` | `de_morgan_4_classical` | `Admitted` — incomplete proof | Incomplete |
| `Logic.v` | `excluded_middle_irrefutable_classical` | Transitively depends on `Admitted` lemma | Incomplete |
| `Lists.v` | 3 proofs | `Abort` — intentional pedagogical stubs | Intentional |
| `Basics.v` | `next_working_day` | Does not skip weekends as the name implies | Semantic/naming |