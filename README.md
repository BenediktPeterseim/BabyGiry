### BabyGiry -- A Probability Monad for Elementary Probability in Lean

This project aims to demonstrate how to "do probability with monads" using a simple toy version of the Giry monad. It allows you to define conditional
events using "conditionally do" blocks of the form:

```lean
def totalValueIsNine : Random Bool := conditionally do -- Define event "totalValueIsNine" conditionally.
  let x <- Unif {1, 2, 3, 4, 5, 6} -- Roll a die.
  let y <- Unif {1, 2, 3, 4, 5, 6} -- Roll another one.
  return x + y = 9 | x ≥ 2 -- Their total value is nine, given that x is at least two.

example : Probability totalValueIsNine = 2/15 := by rfl
```

In such a do block, "random variables" become simply dummy variables in a local context -- no need to fix a "background probability space" as usually done
in classical probability theory to work with random variables. 

The capability of computing conditional probabilities "automatically", by merely specifying a model, also illustrates the basic idea of a probabilistic programming language.
See Examples.lean for more examples, including the famous Monty Hall Problem and a version of the Birthday Paradox.
