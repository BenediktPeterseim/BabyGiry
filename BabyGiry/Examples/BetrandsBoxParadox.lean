/-
Copyright (c) 2024 Benedikt Peterseim. All rights reserved.
Author: Benedikt Peterseim
-/
import BabyGiry.Basic

open BabyGiry

/-!
# Betrand's Box Paradox

"There are three boxes:
  a box containing two gold coins,
  a box containing two silver coins,
  a box containing one gold coin and one silver coin.
Choose a box at random.
From this box, withdraw one coin at random.
If that happens to be a gold coin, then what is the probability
that the next coin drawn from the same box is also a gold coin?"

(from Wikipedia "Betrand's Box Paradox", April 2024)
-/

def Trial : Random (String × String) := do
  -- There are three boxes.
  let Boxes := ({["gold", "gold"], -- a box containing two gold coins,
                ["silver", "silver"], -- a box containing two silver coins,
                ["gold", "silver"]} -- a box containing one gold coin and one silver coin.
                : Finset (List String))
  -- Choose a box at random.
  let box <- Unif Boxes
  -- From this box, withdraw one coin at random.
  let i <- Unif {0,1} -- (random index)
  let coin₁ := box[i]! -- (random coin)
  -- The next coin is the other one in the same box.
  let j := (i + 1) % 2 -- (the other index)
  let coin₂ := box[j]! -- (next coin)
  return (coin₁, coin₂)

-- #eval ℙ[coin₂ = "gold" | coin₁ = "gold", (coin₁, coin₂) ~ Trial]
-- >> (2 : Rat)/3
example : ℙ[coin₂ = "gold" | coin₁ = "gold", (coin₁, coin₂) ~ Trial] = 2/3 := by rfl
/-
We can give an even more literal formalisation of the problem
if we use a probabilistic-programming-style `randomly do` notation,
inclusing an `observe` statement that directly allows us to record
information we observe as we move along the trial.
-/
def CoinGold : Random Bool := randomly do
  -- There are three boxes.
  let Boxes := ({["gold", "gold"], -- a box containing two gold coins,
                ["silver", "silver"], -- a box containing two silver coins,
                ["gold", "silver"]} -- a box containing one gold coin and one silver coin.
                : Finset (List String))
  -- Choose a box at random.
  let box <-~ Unif Boxes
  -- From this box, withdraw one coin at random.
  let i <-~ Unif {0,1} -- (random index)
  let coin₁ := box[i]! -- (random coin)
  -- If that happens to be a gold coin,
  observe <| coin₁ = "gold"
  let j := (i + 1) % 2 -- (the other index)
  let coin₂ := box[j]! -- (next coin)
  -- Event that the next coin is also a gold coin:
  return coin₂ = "gold"

-- #eval ℙ[E | E ~ CoinGold]
-- >> (2 : Rat)/3
example : ℙ[E | E ~ CoinGold] = 2/3 := by rfl
