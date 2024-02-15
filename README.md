### BabyGiry -- A Probability Monad for Elementary Probability in Lean

This project aims to demonstrate how to "do probability with monads" using a simple toy version of the Giry monad. It allows you to define conditional
events using "conditionally do" blocks of the form:

```lean
def totalValueIsThree : random Bool := conditionally do -- Define event "totalValueIs3" conditionally.
  let x <- UniformDist (Finset.range 6) -- Roll a die.
  let y <- UniformDist (Finset.range 6) -- Roll another one.
  return x + y = 3 | x % 2 = 1 ∧ y < 5 -- Their total value is three, given that x is odd, and y less than five.

theorem rollingDice : Probability totalValueIsThree = 2/15 := by rfl
```

In such a do block, "random variables" become simply dummy variables in a local context -- no need to fix a "background probability space" as usually done
in classical probability theory to work with random variables. 

The capability of computing conditional probabilities "automatically", by merely specifying a model, also illustrates the basic idea of a probabilistic programming language.
See Examples.lean for more examples, including the famous Monty Hall Problem and a version of the Birthday Paradox.
