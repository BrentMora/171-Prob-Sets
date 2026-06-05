# Bug & Issue Report: Hoare.v, Imp.v, Maps.v

---

## 🔴 Confirmed Bugs

### Bug 1 — Broken `<>` assertion notation (`Hoare.v:57`)

```coq
(* CURRENT — broken *)
Notation "a <> b" := (fun st => (a:Aexp) <> (b:Aexp) st) ...

(* CORRECT — should be *)
Notation "a <> b" := (fun st => (a:Aexp) st <> (b:Aexp) st) ...
```

The left operand `(a:Aexp)` is not applied to `st`. Since `Aexp = state -> nat`,
the expression `(a:Aexp) <> (b:Aexp) st` compares a *function* `(state -> nat)` with
a *nat*, which is a type mismatch. Every other comparison notation on lines 56–61
correctly applies both sides to `st`:

| Notation | Correct? |
|---|---|
| `a = b`  → `(a:Aexp) st = (b:Aexp) st`  | ✅ |
| `a <= b` → `(a:Aexp) st <= (b:Aexp) st` | ✅ |
| `a < b`  → `(a:Aexp) st < (b:Aexp) st`  | ✅ |
| `a >= b` → `(a:Aexp) st >= (b:Aexp) st` | ✅ |
| `a > b`  → `(a:Aexp) st > (b:Aexp) st`  | ✅ |
| `a <> b` → `(a:Aexp) <> (b:Aexp) st`    | ❌ missing `st` on LHS |

This is a **dormant bug**: the notation definition is accepted by ROCQ (notations
are not type-checked at definition time), but any attempt to write `{{ X <> Y }}`
as an assertion will produce a type error at use-site. The notation is never
invoked in the file (all `<>` uses are in the `com` grammar as `BNeq`), so the
bug has not yet surfaced.

---

### Bug 2 — Dead `Reserved Notation` in `If1` module (`Hoare.v:519–523`)

```coq
(* Declared inside If1: *)
Reserved Notation
  "st0 '=[' c ']=>' st1 '/' s"          (* 4 arguments — note the /s *)
  (at level 40, c custom com at level 99,
   st0 constr, st1 constr at next level, ...).

(* But ceval's where-clause defines only 3 arguments: *)
where "st '=[' c ']=>' st'" := (ceval c st st').
```

The `Reserved Notation` introduces a 4-argument form with a trailing `/s` parameter
(suggesting a step-count or label), but the actual `ceval` inductive uses the
standard 3-argument notation from `Imp.v`. The two strings do not match, so the
reserved notation is **never defined and never used** — it is dead code. This
appears to be a remnant of an incomplete attempt to add a step-indexed or
annotated operational semantics to the `If1` module.

---

## 🟠 Inconsistencies

### Inconsistency 1 — Spurious `unfold valid_hoare_triple` in `equivalent_assertion1` (`Hoare.v:169`)

```coq
Example equivalent_assertion1 :
  {{ (X <= 5) [X |-> 3] }} <<->> {{ 3 <= 5 }}.
Proof.
  unfold valid_hoare_triple.  (* <-- has no effect; goal involves <<->>, not a Hoare triple *)
  split. ...
```

The goal is `assert_implies ... /\ assert_implies ...` (from `<<->>`), which has
nothing to do with `valid_hoare_triple`. The unfold silently does nothing because
`valid_hoare_triple` does not appear in the goal. This is a copy-paste error from
an adjacent Hoare-triple proof. It is harmless but signals that the proof was not
written carefully.

---

### Inconsistency 2 — `hoare_if1` second premise uses `skip` instead of a direct implication (`Hoare.v:601–604`)

```coq
(* Current — unnecessarily indirect *)
Theorem hoare_if1 : forall P Q (b : bexp) c1,
  {{ P /\ b  }} c1   {{Q}} ->
  {{ P /\ ~b }} skip {{Q}} ->   (* <-- why skip? *)
  {{P}} if1 b then c1 end {{Q}}.

(* More natural statement *)
Theorem hoare_if1 : forall P Q (b : bexp) c1,
  {{ P /\ b }} c1 {{Q}} ->
  (P /\ ~b) ->> Q ->
  {{P}} if1 b then c1 end {{Q}}.
```

Since `skip` is semantically a no-op, `{{ P /\ ~b }} skip {{Q}}` is logically
identical to `(P /\ ~b) ->> Q`. Using `skip` here forces the proof (at line 616)
to produce a spurious `apply E_Skip` obligation with no logical content. This is
inconsistent with how the consequent rule is handled everywhere else in the file
(which uses `->>` directly). The standard textbook formulation of the one-armed
conditional rule uses an implication, not a triple.

---

### Inconsistency 3 — `lemma1` reimplements a standard library result with a bad name (`Hoare.v:622`)

```coq
Lemma lemma1: forall b, negb b <> true -> b = true.
```

This lemma is a trivial boolean double-negation fact that already exists in the
standard library (accessible via `Bool.negb_false_iff`, `Bool.not_true_iff_false`,
or `Bool.negb_true_iff`). Two specific problems:

1. **Name**: `lemma1` is wholly non-descriptive. A name like `negb_neq_true_iff`
   or `negb_false_implies_true` would be self-documenting. Inside a module this
   also risks shadowing or clashing with other lemmas added later.

2. **Redundancy**: The stdlib already has this, so the manual proof is wasted
   effort and increases maintenance burden.

---

### Inconsistency 4 — Asymmetric `bexp` operators: no `BLt` (`Imp.v`)

The `bexp` type defines:
```coq
| BLe (a1 a2 : aexp)   (* a1 <= a2 *)
| BGt (a1 a2 : aexp)   (* a1 >  a2 *)
```

But there is no `BLt` (`<`). The set `{<=, >}` is logically complete (each can
express the other), but it is asymmetric compared to the dual pair `{<, >=}` which
is absent. This creates a visible inconsistency for users:

- You **can** write `<{ while X > 0 do ... end }>` (uses `BGt`)
- You **cannot** write `<{ while X < 5 do ... end }>` (no `BLt`)
- You **can** write `{{ X < 5 }}` as an *assertion* (uses Coq's propositional `<` on `nat`)

The propositional `<` in assertions and the absence of boolean `<` in programs is
a subtle trap. A user may write `{{ X < Y }}` in a spec without realising they
cannot use `X < Y` as a program guard.

---

### Inconsistency 5 — No map lemmas in `Maps.v`

`Maps.v` defines `total_map` and `t_update` but proves **no lemmas** about them.
Standard properties like `t_update_eq`, `t_update_neq`, `t_update_shadow`,
`t_update_same`, and `t_update_permute` are all absent. As a result, every proof
in `Hoare.v` that reasons about state updates must manually inline:

```coq
unfold t_update; simpl  (* repeated throughout Hoare.v *)
```

This has two consequences:
- **Verbosity**: proofs are longer than necessary.
- **Fragility**: the proofs depend on `String.eqb` being computable for the
  specific variable names `"X"`, `"Y"`, `"Z"`, `"W"`, meaning proofs could
  break if variable representations change.

The Software Foundations series normally includes these lemmas in `Maps.v`. Their
absence suggests the file was stripped or is an incomplete version.

---

## 🟡 Minor Issues / Code Quality

### Minor 1 — Leftover exercise placeholder (`Hoare.v:21`)

```coq
Module ExAssertions.
  Definition assertion1 : Assertion := ...
  Definition assertion2 : Assertion := ...
  Definition assertion3 : Assertion := ...
  Definition assertion4 : Assertion := ...
  (* FILL IN HERE *)   (* <-- unfilled *)
End ExAssertions.
```

An unfinished exercise stub was left in the file.

---

### Minor 2 — Fragile hypothesis numbering in `hoare_seq` proof (`Hoare.v:149–154`)

```coq
inversion H1.
apply H0 in H5.   (* H5 is the first ceval premise from E_Seq *)
- apply H in H8.  (* H8 is the second ceval premise from E_Seq *)
```

The names `H5` and `H8` are auto-generated by `inversion` and depend on exactly
how many hypotheses precede them in the context. Any change to the number of
`intros`-introduced hypotheses (e.g., upstream refactoring in `Imp.v`'s `E_Seq`
constructor) would silently produce wrong or failing names. Better style is to
use `inversion H1 as [... Hc1 Hc2 ...]` with explicit names, or `destruct`.

---

### Minor 3 — Redundant `specialize` before `apply` in `hoare_if` proof (`Hoare.v:396–403`)

```coq
specialize H  with (st := st) (st' := st').
apply H in H9.
...
specialize H0 with (st := st) (st' := st').
apply H0 in H9.
```

ROCQ's unifier infers `st` and `st'` automatically when `apply H in H9` is used.
The explicit `specialize` calls are redundant and add noise. This is also
inconsistent with the rest of the file, where `apply` is used directly without
prior specialization.

---

### Minor 4 — Inconsistent proof style across the file (`Hoare.v`)

The automation tactics `assertion_auto`, `assertion_auto'`, and `assertion_auto''`
are introduced progressively through the file (lines 273, 431, 466), but earlier
proofs that would benefit from them are never retrofitted. For example:

- `hoare_asgn_example1` (line 241) manually unfolds `t_update` and calls
  `reflexivity`, when `assertion_auto` would suffice.
- `if_example` (line 409) manually rewrites `eqb_eq`, when `assertion_auto'`
  would handle it.

This leaves two coexisting styles with no clear guideline for which to use when,
making the file harder to maintain.

---

### Minor 5 — `hoare_while` proof is overly complex (`Hoare.v:651–663`)

```coq
remember <{while b do c end}> as og eqn:Horig.
induction H0.
- inversion Horig.   (* E_Skip    — impossible *)
- inversion Horig.   (* E_Asgn   — impossible *)
- inversion Horig.   (* E_Seq    — impossible *)
- inversion Horig.   (* E_IfTrue — impossible *)
- inversion Horig.   (* E_IfFalse— impossible *)
- inversion Horig. subst. ...  (* E_WhileFalse — real case *)
- inversion Horig. subst. ...  (* E_WhileTrue  — real case *)
```

The `remember`+`induction` pattern generates 7 cases, 5 of which are immediately
dismissed. A direct `inversion H0` on the `ceval` hypothesis would produce only
the two relevant cases (`E_WhileFalse` and `E_WhileTrue`) without the boilerplate,
making the proof cleaner and shorter.

---

## Summary Table

| # | Severity | File | Location | Description |
|---|---|---|---|---|
| 1 | 🔴 Bug | `Hoare.v` | Line 57 | `<>` assertion notation missing `st` on LHS — dormant type error |
| 2 | 🔴 Bug | `Hoare.v` | Lines 519–523 | Dead 4-argument `Reserved Notation` in `If1` — never defined or used |
| 3 | 🟠 Inconsistency | `Hoare.v` | Line 169 | `unfold valid_hoare_triple` in `equivalent_assertion1` has no effect |
| 4 | 🟠 Inconsistency | `Hoare.v` | Lines 601–604 | `hoare_if1` second premise uses `skip` where `->>` is cleaner |
| 5 | 🟠 Inconsistency | `Hoare.v` | Line 622 | `lemma1` is poorly named and duplicates a stdlib result |
| 6 | 🟠 Inconsistency | `Imp.v` | `bexp` type | No `BLt` constructor — `<` usable in assertions but not in programs |
| 7 | 🟠 Inconsistency | `Maps.v` | Entire file | No map lemmas proved — forces verbose `unfold t_update; simpl` everywhere |
| 8 | 🟡 Minor | `Hoare.v` | Line 21 | Unfilled `(* FILL IN HERE *)` in `ExAssertions` |
| 9 | 🟡 Minor | `Hoare.v` | Lines 149–154 | Fragile auto-generated hypothesis names `H5`, `H8` in `hoare_seq` |
| 10 | 🟡 Minor | `Hoare.v` | Lines 396–403 | Redundant `specialize` before `apply` in `hoare_if` |
| 11 | 🟡 Minor | `Hoare.v` | Throughout | Inconsistent proof style: manual unfolds vs. automation tactics |
| 12 | 🟡 Minor | `Hoare.v` | Lines 651–663 | `hoare_while` uses `induction` with 5 vacuous `inversion` cases |
