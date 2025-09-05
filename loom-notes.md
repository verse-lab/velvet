## Loom Missing Features

- Match statements
    -- How do we do this?? 
- Recursion
    -- Bigger problem, to be solved laterA
- Standard Library Lemmas for the solver to do things better
    -- String
    -- List
    -- Substring
    -- Map/HashMap

## Loom Understanding 

- Match expressions are difficult
    * Variable number of branches, difficult to express the construct?

**Idea** :
- Why not have a macro that converts Lean inductive types to something that is compatible with Velvet?
- We'll piggyback on if statements
- We'll generate conditions and immediate structures for the inductive branches, that could work?
- Any other idea? I don't know really tbh


Or maybe, I don't know enough lean to express matches, look into this once as well.
