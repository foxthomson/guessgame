import system.random.basic
import tactic

def nat_of_Icc (a : set.Icc 1 100) : ℕ := 
begin
  cases a with val,
  exact val
end

@[derive has_reflect]
structure game :=
( target : ℕ )
( guesses : ℕ )

def game_to_nat := λ g : game, g.target

def game.inc_guess : game → game
| ⟨ n, m ⟩ := ⟨ n, m.succ ⟩ 

def game.inc_guess_ex {n m} : (∃ x : game, game.mk n m = x) → (∃ x : game, game.mk n m.succ = x)
| ⟨ x, hx ⟩ := ⟨ x.inc_guess, begin rw ← hx, refl end ⟩

def start_game (n) : game := ⟨ n, 7 ⟩ 

meta def ex (a : game) : tactic expr := 
  tactic.to_expr ``(∃ x, %%a = x)

meta def mk_random_game : tactic expr :=
do
  start_game <$> nat_of_Icc <$> tactic.random_r 1 100 (by norm_num) >>=
  ex >>= tactic.assert `target

meta def guess (n : ℕ) : tactic unit :=
do
  `(∃ x : game, %%a = x) ← tactic.target,
  do
  { 
    tactic.to_expr ``(game_to_nat %%a = %%n) >>= tactic.assert `result,
    tactic.solve1 (tactic.exact_dec_trivial),
    tactic.trace "Congratulations!!",
    tactic.tautology 
  }
  <|>
  do 
  {
    (
      do
      { 
        tactic.to_expr ``(game_to_nat %%a < %%n) >>= tactic.assert `result,
        tactic.solve1 (tactic.exact_dec_trivial)
      }
      <|>
      do
      { 
        tactic.to_expr ``(game_to_nat %%a > %%n) >>= tactic.assert `result,
        tactic.solve1 (tactic.exact_dec_trivial) 
      } 
    ),
    ( do 
      {
        tactic.interactive.apply ``(game.inc_guess_ex),
        `(game.mk %%n %%g) ← tactic.to_expr ``(%%a),
        expr.to_nat <$> tactic.to_expr ``(%%g) >>= λ x, option.cases_on' x (tactic.trace "hello")
        (λ (guesses : ℕ), tactic.trace $ repr guesses ++ " guesses left")
      }
      <|>
      do {
        tactic.trace "out of guesses",
        tactic.failed
      } 
    )
  }

notation `*` := game.mk _ _