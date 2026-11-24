import VersoManual

open Verso.Genre Manual
open Verso.Code.External

set_option pp.rawOnError true
set_option verso.exampleProject "../"
set_option verso.exampleModule "BfTuringComplete.Exposition.Example"

#doc (Manual) "A Worked Example" =>

Here is a small machine with symbols `0` (the blank), `1` and `2`. It swaps `1` and `2` in every
cell up to the first blank, walks back to the start, and halts.

```anchor swap
def swap : TM0.Machine (Fin 3) (Fin 4)
  | 0, 0 => some (2, .move .left)
  | 0, 1 => some (1, .write 2)
  | 0, 2 => some (1, .write 1)
  | 1, _ => some (0, .move .right)
  | 2, 0 => some (3, .move .right)
  | 2, _ => some (2, .move .left)
  | _, _ => none
```

Each cell of its tape becomes a block of 18 Brainfuck cells, one per flag:

```anchor width
#eval width                         -- 18
```
```anchorInfo width
18
```

The compiled program is 4058 characters of Brainfuck:

```anchor length
#eval (render swapBF).length
```
```anchorInfo length
4058
```

Brainfuck's `eval` is defined for every program but cannot be executed. To watch the program run we
iterate the same `step` function with a step budget, then decode the final tape block by block. The
machine and the program agree:

```anchor runTM
#eval tmOutput [1, 2, 2]            -- some [2, 1, 1, 0]
```
```anchorInfo runTM
some [2, 1, 1, 0]
```

```anchor runBF
#eval bfOutput [1, 2, 2]            -- some [2, 1, 1, 0]
```
```anchorInfo runBF
some [2, 1, 1, 0]
```

These checks run every time the project builds:

```anchor guard
#guard bfOutput [1, 2, 2] = tmOutput [1, 2, 2]
#guard bfOutput [2, 2, 1, 1] = tmOutput [2, 2, 1, 1]
#guard bfOutput [] = tmOutput []
```
