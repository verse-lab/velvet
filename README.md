# LoL

## Interface:

### Specifiying effects 
- if `P : m Prop`, `c : m A` and `Q : A -> m Prop` then `{ P } c { Q }` is LoL specification
- to specify effects like thorow we should write `{ P } c { fun _ => throw e }`
  - `\mu := String -> Prop` st `\mu s := (. = s)`

### Total functions

```lean4
def foo : m a := ...

lemma foo_spec (P : m Prop) (Q : a -> m Prop) : { P } foo { x, Q x } := ...
```

