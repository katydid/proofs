# Contributing Guidelines

## How to start

1. Create a pull request on main
2. Add yourself to the AUTHORS file
3. Make sure the github action that automatically checks your proofs passes.
4. Wait for at least one approval from a reviewer
5. Merge (or poke for a merge, depending on your permissions)

## FAQ

### Where to jump in

1. Find a TODO, `admit` or `sorry`.
2. Open an github issue, if you would like to prove something different that you still feels belong here.
3. If there is an already existing proof, that you would like to prove in an different way, you are welcome. In that case, we would like to keep both copies, so copy the name, add a tick `'` at the end, write your alternative proof and submit your pull request.

### Comments

 - Do we like comments? Yes we do.
 - Are they required? No.

### When to use a separate file

Now. When you are starting to ask this question, it is time to start using a separate file.

### Tactics

Tactics unlike proofs, definitions, etc. don't have any types.
This means they lack some documentation and type checking.
For this reason, we require that new tactics come with:
  - some comments above that describe the tactic.
  - some examples below that use the tactic.

If you see a tactic that doesn't meet these requirements at the moment, consider it a Good First Issue to add these.

