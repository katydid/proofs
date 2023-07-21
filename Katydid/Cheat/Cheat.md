# Tired of old fat Coq, try new Lean vegetarian

- apply

apply is the same

- intros

In Coq intros, introduces all hypotheses, but in Lean intros needs to name every hypothesis that it introduces. `intro` does not exist.

- elim



- case


- destruct H as [H1 H2]

```
cases H with
| intro H1 H2 =>
```

- split

split is a different tactic in Lean, but you can use `constructor` or `apply And.intro`.

```
constructor -- apply And.intro
case left => exact H2
case right => exact H1
```

- left, right

This is only available in mathlib4

- exists

mathlib4 has a `use` tactic
just `import MathLib.Tactic`

- rewrite H

`rewrite H` in Coq is `rewrite [H]` in Lean
`rw [H]` is the same as `rewrite [H]` followed by `try rfl`

- rewrite <- H

`rewrite <- H` in Coq is `rewrite [<- H]` in Lean

- reflexivity

rfl

- ring

TODO: For this you need mathlib4

- exact

exact works exactly the same.

- assumption

Your assumption that assumption works the same is correct.

- inversion

We don't know

- subst

`subst` in Coq is `subst_vars` in Lean

- cbn

`dsimp` was the closest we could find.

- simpl

`simp` is kind of the same, but more powerful, as it includes at least reflexivity.

`simp only` is less powerful

`simp only [Nat.add_zero]` only uses the theorems in the list to simplify

`simp [Nat.add_zero]` uses the theorems in the list to simplify and also all the usual theorems

`simp_all` TODO: does something else

`simp [*]` TODO: does something else

`simp [*] at *`

`simp at H`  simplifies the hypotheses

- unfold

unfold is the same

- contradiction

This is also `contradiction` in Lean.

- discriminate

This is also `contradiction` in Lean.

- generalize dependent

This is `revert` in Lean.

- remember

TODO: This is `have`

- induction

```
induction x as [ | x0 IHx0].
- ...
- ...
```

In Lean you need to intro a variable before you can do induction on it.

```
intros x
induction x
case zero =>
  ...
case succ x0 IHx0 =>
  ...
```

- constructor

same

- refine

Instead of using `_` using `?_`

`refine (Or.intro_right _ ?_)`

Here the `_` is the inferred type and the `?_` is the hole to prove in the next step.

- lia

linarith is available in mathlib4, but we haven't tried it

- auto

`auto` in Coq is like `simp` in Lean, because it is also extensible. You can add more theorems to this tactic by annotate by `@[simp]` above the theorem and importing it.

- SearchRewrite (_ * (_ + _)).

TODO: In mathlib4 there are several alternatives
- #find
- apply?
- exact?
- rewrite?

- admit

sorry

- specialize

TODO: have and/or specialize

# Other useful tactic

`rename_i`

# Tactic Operators

; => <;>
- => \.
repeat => repeat
try => try

# Pattern Matching

Definition example7 (t : bin): bool :=
match t with N L L => false | _ => true end.