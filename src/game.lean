import basic

/-- 
# How to play
The tactic `mk_random_game` will generate a random number between 1 and 100. You can then use the
tactic `guess n` to guess a random number. If you get it right the goal will be solved otherwise it
will add a hypothesis saying whether you were too high or too low. You have 7 guesses.
 -/
example : true :=
begin
  mk_random_game,
  { 
    guess 10,
    guess 20,
    guess 30,
    guess 40,
    guess 50,
    guess 60,
  },
  trivial,
end