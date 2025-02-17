# LoL

## Interface:

### Total functions

```lean4
def foo : m a := ...

lemma foo_spec (P : m Prop) (Q : a -> m Prop) : { P } foo { x, Q x } := ...
```

### Partial functions (Don't know if it will work)

assume `foo` has a `while`-loop or non-structural recursion

first you prove the following total Hoare-logic

```lean4

lemma foo_spec (P : m Prop) (Q : a -> m Prop) : { P } foo { x, Q x } := ...
```
This means `foo` terminates, providing `P`. This should give you a total function `foo : P -> m a`. We can run it in Lean by `foo sorryAx`.

