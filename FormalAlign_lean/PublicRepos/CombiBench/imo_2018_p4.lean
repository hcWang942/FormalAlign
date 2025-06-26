/- A site is any point $(x, y)$ in the plane such that $x$ and $y$ are both
positive integers less than or equal to 20. Initially, each of the 400 sites is
unoccupied. Amy and Ben take turns placing stones with Amy going first. On her
turn, Amy places a new red stone on an unoccupied site such that the distance
between any two sites occupied by red stones is not equal to $\sqrt{5}$.

On his turn, Ben places a new blue stone on any unoccupied site. (A site occupied
by a blue stone is allowed to be at any distance from any other occupied site.)
They stop as soon as a player cannot place a stone. Find the greatest $K$ such that
Amy can ensure that she places at least $K$ red stones, no matter how Ben places his
blue stones.-/
import Mathlib

abbrev Site := Fin 20 × Fin 20

def Site.asPoint (s : Site) : EuclideanSpace ℝ (Fin 2) :=
fun x => if x = 0 then (s.1.val + 1) else (s.2.val + 1)

inductive State
| red
| blue
| unoccupied

abbrev Game := Site → State

def initialGame : Game := fun _ => State.unoccupied

def valid_Amy_move (x : Site) (g : Game) : Prop :=
g x = State.unoccupied ∧
∀ y, g y = State.red → dist x.asPoint y.asPoint ≠ √5

def valid_Ben_move (x : Site) (g : Game) : Prop :=
g x = State.unoccupied

def AmyStrategy := Π (g : Game), Option ((x : Site) ×' valid_Amy_move x g)

def Game.updateAccordingToAmyStrategy (g : Game) (s : AmyStrategy) : Option Game :=
(s g) >>= fun p => .some <| Function.update g p.1 .red

def BenStrategy := Π (g : Game), Option ((x : Site) ×' valid_Ben_move x g)

def Game.updateAccordingToBenStrategy (g : Game) (s : BenStrategy) : Option Game :=
(s g) >>= fun p => .some <| Function.update g p.1 .blue

def updateOneTurn (a : AmyStrategy) (b : BenStrategy) (g : Game) : Option Game :=
g.updateAccordingToAmyStrategy a >>= fun g' => g'.updateAccordingToBenStrategy b

def updateGame (a : AmyStrategy) (b : BenStrategy) (g : Game) : ℕ → Option Game
| 0 => .some g
| (n + 1) => updateOneTurn a b g >>= (updateGame a b · n)

def CanPlaceKRedStones (a : AmyStrategy) (b : BenStrategy) : ℕ → Prop
| 0 => True
| n+1 =>
∃ (h : updateGame a b initialGame n |>.isSome),
a ((updateGame a b initialGame n).get h) |>.isSome

abbrev imo_2018_p4_solution : ℕ := 32 --这是啥啊，答案呢

theorem imo_2018_p4 :
(∃ a : AmyStrategy, ∀ b : BenStrategy, CanPlaceKRedStones a b imo_2018_p4_solution) ∧
(∀ a : AmyStrategy, ∃ b : BenStrategy, ¬ CanPlaceKRedStones a b (imo_2018_p4_solution + 1)) := by sorry
