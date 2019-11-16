# lean-game-skeleton
A skeleton game file for use with the [Lean game maker](https://github.com/mpedramfar/Lean-game-maker)

## What is this?

The [Natural Number Game](http://wwwf.imperial.ac.uk/~buzzard/xena/natural_number_game/) was made from [this repository](https://github.com/ImperialCollegeLondon/natural_number_game) using the [Lean game maker](https://github.com/mpedramfar/Lean-game-maker). But if anyone else wants to make a web-based Lean game then perhaps the natural number game is a bit of an intimidating place to start. Here is a completely stripped-down and much simpler game with just two worlds.


## Getting started

This assumes you have [Lean and mathlib installed](https://github.com/leanprover-community/mathlib#installation), and also Mohammad Pedramfar's [Lean game maker](https://github.com/mpedramfar/Lean-game-maker). 

```
git clone git@github.com:kbuzzard/lean-game-skeleton.git
cd lean-game-skeleton/
leanpkg upgrade
update-mathlib
make-lean-game
```
Now in the html directory of the repository you have a two-world two-level game, which you can play (assuming you have an http server installed) by starting the server in the html directory and then pointing a web browser at it.

## Brief explanations

The file `game_config.html` contains the data of the "worlds" (chapters) and "levels". The syntax is fairly self-explanatory. To see a more complex example, look at the `game_config.html` in [the natural number game](https://github.com/ImperialCollegeLondon/natural_number_game/blob/master/game_config.toml) and compare with [the graph it generates](http://wwwf.imperial.ac.uk/~buzzard/xena/natural_number_game/). 

The lines following `/- Tactic : refl` in `src/game/sup_inf/L01defs.lean` are what appears in the drop-down tactic menu (once the player has got to this level). The lemma following `/- Lemma` in the same file is what appears in the drop-down menu of theorems. For more explanation, see the README for the Lean game maker.
