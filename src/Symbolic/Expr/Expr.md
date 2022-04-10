# Expr

Predicates (`Pred`) read an input from the input stream and return a bool.
```
A -> bool
```

The symbols read from the input stream are passed into predicates that expect a specific type, but this might not be the same type as the input stream.
This means an assertion has to be made, which might result in an error.  Expressions (`Expr`) are like predicates, except that they might rather return an error:

```
A -> bool + error
```

Expressions can also be composed together to form larger expressions, which means they don't necessarily have to return a `bool`:

```
A -> B + error
```

An expression can only be converted to an predicate if the return type is a bool:

```
(A -> bool + error) -> (A -> bool)
```

The cases that return an error will swallow the error and then simply return a false boolean.

## Why not always swallow the errors

We don't want to always swallow the error, for all expressions, because this would change the semantics.
For example, when we write:

```
not(eq(range(0, 4, $string), ""))
```

We could get a range error, but if range could only return a string and it had to swallow the error, it might return an empty string, which would mean this predicate would result in false, when we would prefer it to return true, since the first four letters could never equal an empty string.



