# lfs-curiositymodeling

## What are you trying to model? 
(Include a brief description that would give someone unfamiliar with the topic a basic understanding of your goal.)
- We are trying to model 2048! For those who are unfamiliar with the game, 2048 is a sliding block puzzle in which there are a bunch of tiles on a 4x4 grid. The board starts with two tiles, and each move consists of sliding all the tiles in a certain direction, as well as generating new tiles. When two tiles with the same value on them collide, they combine to make a new tile with the sum of the colliding tiles. The game ends either when the tile with 2048 on it is successfully created or when the board is fully filled and there are no more possible moves. See https://play2048.co/ to play!

## Model Design Choices
#### Complexity
- The original game runs on a 4x4 board with winning condition being the existence of the 2048 tile on the board. To end up with a solution, our trace would have been longer and more complicated than we could have created in a reasonable amount of time. We limited the complexity of our problem by creating a model of the game on a 3x3 board, with winning condition being the existance of a 32 tile. We left all the rules of the game the same, but this limited the complexity of our model while still allowing us to experiment with and learn from modeling the game.

#### Checks and Runs
- We have checks to make sure the transitions are valid (moving from one state to the next), as well as validity checks on the initial and final conditions of the game. The trace we run has exactly 30 states, and plays to find an ending condition of a 32 tile from a valid starting state. A Sterling instance will provide this trace, and it is likely best to either look at the table representation or to project over State to be able to best interperate the instance. The instance will tell you which tiles are in which positions on the board in each state, as well as the move that was played during that state (for easier parsing). Ideally, there would be a visualization for this model, but that was outside the scope of this project.

#### Sigs and Preds
- State Sig: Necessary to keep track of the concept of "time". Also contains the board
- Tile Sig: Abstract sig necessary to represent the tiles in the game. Sigs extending Tile to represent specific tiles
- Direction Sig: Abstract sig to keep represent the possible "moves" the player can make at each time step. Sigs extending Direction to represent specific directions
- wellformed Pred: Makes sure that all tiles are located on the board as well as the proper sup relations between tiles exist.
- increasingOrder Pred: Constrains the resulting tile that comes from a collision of two of the same tiles
- initState Pred: Specifies the starting conditions of the board (ie. two tiles that are either TWO or FOUR, and nothing else)
- finalState32 Pred: Specifies ending condition of the existance of a 32 tile
- validCoord Pred: Makes sure that the tiles stay on the board
- insert Pred: Transition predicate that generates the "random" new tile on each turn
- move Pred: Transition predicate that moves all tiles in the given direction, and deals with collisions of tiles appropriately
- possibleMove Pred: Stops a player from making a move in a certain direction if that move is not valid (eg. cannot move left if there are no tiles with empty space to their left, or a collision is not possible in the horizontal direction). 
- traces Pred: For creating an instance of the model with valid transitions, initial state, and final state. 
