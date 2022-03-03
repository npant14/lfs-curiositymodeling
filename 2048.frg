#lang forge/bsl

//SIGS

sig State {
  board: pfunc Int -> Int -> Tile,
  next: lone State,
  type: one Int, //type used to differentiate between move states and generation states
  dir: lone Direction
}

abstract sig Tile {
  sup: lone Tile
}
one sig TWO, FOUR, EIGHT, SIXTEEN, THIRTYTWO extends Tile {}


abstract sig Direction {}
one sig Left, Right, Up, Down extends Direction {} 

//PREDS

//enforce increasing order of tiles for collisions
pred increasingOrder{
  TWO.sup = FOUR
  FOUR.sup = EIGHT
  EIGHT.sup = SIXTEEN
  SIXTEEN.sup = THIRTYTWO
  no THIRTYTWO.sup
}



//well formedness for 3x3 board
pred wellformed {
  increasingOrder
  all s: State | {
    all row, col: Int | {
      (row < 0 or row > 2 or col < 0 or col > 2) 
        implies no s.board[row][col]    
    }
    s.type = 1 or s.type = 0
    not s.next.type = s.type
  }
}

// constrain the initial condition to have only two tiles on the board
pred initState[s: State] {
  s.type = 0

  #{row, col: Int | s.board[row][col] = TWO} = 2 and #{row, col: Int | s.board[row][col] = FOUR} = 0 //or 
  #{row, col: Int | s.board[row][col] = TWO} = 1 and #{row, col: Int | s.board[row][col] = FOUR} = 1 or 
  #{row, col: Int | s.board[row][col] = TWO} = 0 and #{row, col: Int | s.board[row][col] = FOUR} = 2
  all row, col: Int | s.board[row][col] = TWO or  s.board[row][col] = FOUR or no s.board[row][col]

}

// constrain the final condition to have a 32 tile on the board 
pred finalState32[s: State] {
  some row, col : Int | {
    s.board[row][col] = THIRTYTWO
  }
}

// keep all tiles on the board
pred validCord[i: Int]{
  not(i < 0) and not(i > 3)
}


// model the generation of a tile in a "random" location
pred insert[pre: State, post: State]{
  pre.type = 1
  some row, col: Int | {
    no pre.board[row][col]
    post.board[row][col] = TWO or post.board[row][col] = FOUR
    all row2, col2: Int | not pre.board[row2][col2] = post.board[row2][col2] => {row = row2 and col=col2}
  }
}

// model moving all tiles in a direction and associated collisions
pred move [pre: State, theMove: Direction, post: State]{
  theMove = Left => {
    -- for all rows
    all row: Int | {
      #{col: Int | some pre.board[row][col]} = 0 => #{col: Int | some post.board[row][col]} = 0
      -- if there is only 1 tile in the row
      #{col: Int | some pre.board[row][col]} = 1 =>{
        -- the one tile goes to the post.board[row][0]
        some col: Int | some pre.board[row][col] and post.board[row][0] = pre.board[row][col] and{
          -- the only filled tile in the row in the post state is the left most
          no post.board[row][1] and no post.board[row][2]
        } 
      }
      -- If there are twp tiles in the row
      #{col: Int | some pre.board[row][col]} = 2 => {
       some col1, col2: Int|{
         -- t1 and t2 are disjoint
         some pre.board[row][col1] and some pre.board[row][col2]
         -- col1 is on the left of col 2
         col1 < col2
         -- if both squares are the same, the post row will only have their sup on the left
         pre.board[row][col1] = pre.board[row][col2] =>{
           (post.board[row][0] = (pre.board[row][col1]).sup) and (no post.board[row][1]) and (no post.board[row][2])
         }
         -- if they are both different, then the left most tile goes to the far leftm, and the second most goes to the next spot
         (not pre.board[row][col1] = pre.board[row][col2]) =>{
           post.board[row][0] = pre.board[row][col1] and post.board[row][1] = pre.board[row][col2] and no post.board[row][2]
         }
       }
        
      }
      -- If there are 3 tiles in the row
      #{col: Int | some pre.board[row][col]} = 3 => {
        some col1, col2, col3: Int| {
          -- t1 is on the left, t3 is on the right
          some pre.board[row][col1] and some pre.board[row][col2] and some pre.board[row][col3]
          col1 < col2 and col2 < col3
          -- if the two on the far left are the same, comine them and put the 
          -- extra guy next to them,
          pre.board[row][col1] = pre.board[row][col2] => {
            post.board[row][0] = (pre.board[row][col1]).sup and post.board[row][1] = pre.board[row][col3] and no post.board[row][2]
          }
          -- If the left two arent equal, but the right two are, ...
          ((not pre.board[row][col1] = pre.board[row][col2]) and pre.board[row][col2] = pre.board[row][col3]) => {
            post.board[row][0] = pre.board[row][col1] and post.board[row][1] = (pre.board[row][col3]).sup and no post.board[row][2]
          }
          -- if none are equal, just push them all to the left
          ((not pre.board[row][col1] = pre.board[row][col2]) and (not pre.board[row][col2] = pre.board[row][col3])) => {
             post.board[row][0] = pre.board[row][col1] and post.board[row][1] = pre.board[row][col2] and post.board[row][2] = pre.board[row][col3]
          }
        }
      }
    }
  }



  theMove = Right => {

    -- for all rows
    all row: Int | {
      #{col: Int | some pre.board[row][col]} = 0 => #{col: Int | some post.board[row][col]} = 0
      -- if there is only 1 tile in the row
      #{col: Int | some pre.board[row][col]} = 1 =>{
        -- the one tile goes to the post.board[row][3]
        some col: Int | some pre.board[row][col] and post.board[row][2] = pre.board[row][col] and{
          -- the only filled tile in the row in the post state is the right most
          no post.board[row][1] and no post.board[row][0]
        } 
      }
      -- If there are twp tiles in the row
      #{col: Int | some pre.board[row][col]} = 2 => {
       some col1, col2: Int |{
         -- t1 and t2 are disjoint
         some pre.board[row][col1] and some pre.board[row][col2]
         -- col1 is on the left of col 2
         col1 < col2
         -- if both squares are the same, the post row will only have their sup on the right
         pre.board[row][col1] = pre.board[row][col2] =>{
           post.board[row][2] = (pre.board[row][col1]).sup and no post.board[row][1] and no post.board[row][0]
         }
         -- if they are both different, then the right most tile goes to the far right, and the second most goes to the next spot
         (not pre.board[row][col1] = pre.board[row][col2]) =>{
           post.board[row][1] = pre.board[row][col1] and post.board[row][2] = pre.board[row][col2] and no post.board[row][0]
         }
       }
        
      }
      -- If there are 3 tiles in the row
      #{col: Int | some pre.board[row][col]} = 3 => {
        some col1, col2, col3: Int | {
          -- t1 is on the left, t3 is on the right
          some pre.board[row][col1] and some pre.board[row][col2] and some pre.board[row][col3]
          col1 < col2 and col2 < col3
          -- if the two on the far left are the same, comine them and put the 
          -- extra guy next to them,
          pre.board[row][col1] = pre.board[row][col2] => {
            post.board[row][1] = (pre.board[row][col1]).sup and post.board[row][2] = pre.board[row][col3] and no post.board[row][0]
          }
          -- If the left two arent equal, but the right two are, ...
          ((not pre.board[row][col1] = pre.board[row][col2]) and pre.board[row][col2] = pre.board[row][col3]) => {
            post.board[row][1] = pre.board[row][col1] and post.board[row][2] = (pre.board[row][col3]).sup and no post.board[row][0]
          }
          -- if none are equal, just push them all to the right
          ((not pre.board[row][col1] = pre.board[row][col2]) and (not pre.board[row][col2] = pre.board[row][col3])) => {
             post.board[row][0] = pre.board[row][col1] and post.board[row][1] = pre.board[row][col2] and post.board[row][2] = pre.board[row][col3]
          }
        }
      }
    }

  }

  theMove = Up => {

    -- for all rows
    all col: Int | {
      #{row: Int | some pre.board[row][col]} = 0 => #{row: Int | some post.board[row][col]} = 0
      -- if there is only 1 tile in the row
      #{row: Int | some pre.board[row][col]} = 1 =>{
        -- the one tile goes to the post.board[row][0]
        some t: Tile, row: Int | pre.board[row][col] = t and post.board[0][col] = t and{
          -- the only filled tile in the row in the post state is the top most
          no post.board[1][col] and no post.board[2][col]
        } 
      }
      -- If there are twp tiles in the row
      #{row: Int | some pre.board[row][col]} = 2 => {
       some row1, row2: Int |{
         -- t1 and t2 are disjoint
         some pre.board[row1][col] and some pre.board[row2][col]
         -- row1 is on the top of row2
         row1 < row2
         -- if both squares are the same, the post col will only have their sup on the top
         pre.board[row1][col] = pre.board[row2][col] =>{
           post.board[0][col] = (pre.board[row1][col]).sup and no post.board[1][col] and no post.board[2][col]
         }
         -- if they are both different, then the top most tile goes to the far top, and the second most goes to the next spot
         (not pre.board[row1][col] = pre.board[row2][col]) =>{
           post.board[0][col] = pre.board[row1][col] and post.board[1][col] = pre.board[row2][col] and no post.board[2][col]
         }
       }
        
      }
      -- If there are 3 tiles in the row
      #{row: Int | some pre.board[row][col]} = 3 => {
        some row1, row2, row3: Int| {
          -- t1 is on the top, t3 is on the bottom
          some pre.board[row1][col] and some pre.board[row2][col] and some pre.board[row3][col]
          row1 < row2 and row2 < row3
          -- if the two on the far top are the same, comine them and put the 
          -- extra guy next to them,
          pre.board[row1][col] = pre.board[row2][col] => {
            post.board[0][col] = (pre.board[row1][col]).sup and post.board[1][col] = pre.board[row3][col] and no post.board[2][col]
          }
          -- If the top two arent equal, but the bottom two are, ...
          ((not pre.board[row1][col] = pre.board[row2][col]) and pre.board[row2][col] = pre.board[row3][col]) => {
            post.board[0][col] = pre.board[row1][col] and post.board[1][col] = (pre.board[row3][col]).sup and no post.board[2][col]
          }
          -- if none are equal, just push them all to the top
          ((not pre.board[row1][col] = pre.board[row2][col]) and (not pre.board[row2][col] = pre.board[row3][col])) => {
             post.board[0][col] = pre.board[row1][col] and post.board[1][col] = pre.board[row2][col] and post.board[2][col] = pre.board[row3][col]
          }
        }
      }
    }
  }

  theMove = Down => {

    -- for all cols
    all col: Int | {
      #{row: Int | some pre.board[row][col]} = 0 => #{row: Int | some post.board[row][col]} = 0
      -- if there is only 1 tile in the col
      #{row: Int | some pre.board[row][col]} = 1 =>{
        -- the one tile goes to the post.board[col][2]
        some row: Int | some pre.board[row][col] and post.board[2][col] = pre.board[row][col] and{
          -- the only filled tile in the row in the post state is the bottom most
          no post.board[1][col] and no post.board[0][col]
        } 
      }
      -- If there are twp tiles in the row
      #{row: Int | some pre.board[row][col]} = 2 => {
       some row1, row2: Int|{
         -- t1 and t2 are disjoint
         some pre.board[row1][col] and some pre.board[row2][col]
         -- col1 is on the top of col 2
         row1 < row2
         -- if both squares are the same, the post row will only have their sup on the bottom
         pre.board[row1][col] = pre.board[row2][col] =>{
           post.board[2][col] = (pre.board[row1][col]).sup and no post.board[1][col] and no post.board[0][col]
         }
         -- if they are both different, then the bottom most tile goes to the far bottom, and the second most goes to the next spot
         (not pre.board[row1][col] = pre.board[row2][col]) =>{
           post.board[1][col] = pre.board[row1][col] and post.board[2][col] = pre.board[row2][col] and no post.board[0][col]
         }
       }
        
      }
      -- If there are 3 tiles in the row
      #{row: Int | some pre.board[row][col]} = 3 => {
        some row1, row2, row3: Int| {
          -- t1 is on the top, t3 is on the bottom
          some pre.board[row1][col] and some pre.board[row2][col] and some pre.board[row2][col]
          row1 < row2 and row2 < row3
          -- if the two on the far top are the same, comine them and put the 
          -- extra guy next to them,
          pre.board[row1][col] = pre.board[row2][col] => {
            post.board[1][col] = (pre.board[row1][col]).sup and post.board[2][col] = pre.board[row3][col] and no post.board[0][col]
          }
          -- If the top two arent equal, but the right two are, ...
          ((not pre.board[row1][col] = pre.board[row2][col]) and pre.board[row2][col] = pre.board[row3][col]) => {
            post.board[1][col] = pre.board[row1][col] and post.board[2][col] = (pre.board[row3][col]).sup and no post.board[0][col]
          }
          -- if none are equal, just push them all to the bottom
          ((not pre.board[row1][col] = pre.board[row2][col]) and (not pre.board[row2][col] = pre.board[row3][col])) => {
             post.board[0][col] = pre.board[row1][col] and post.board[1][col] = pre.board[row2][col] and post.board[2][col] = pre.board[row3][col]
          }
        }
      }
    }
  }
}

// says if this move is a possible candidate for a move
pred possibleMove[pre: State, d: Direction]{
  not move[pre, d, pre]
}

pred traces {
  wellformed    
    some initial: State | some final: State | {
        initState[initial]
        finalState32[final]
        no s: State | s.next = initial
        no final.next
        all s: State | s != final implies {
            some m: Direction | {
              s.type = 0 => {
                possibleMove[s, m]
                move[s, m, s.next]
                s.dir = m
              }
              s.type = 1 => insert[s, s.next] and no s.dir
            }
        }
    }
}

example leftNoMerge is {some pre, post: State, d: Direction | move[pre,d,post]  and (not post = pre)} for {
  State = `S0 + `S1
  TWO = `T2
  FOUR = `T4
  EIGHT = `T8
  SIXTEEN = `T16
  THIRTYTWO = `T32
  Tile = TWO + FOUR + EIGHT + SIXTEEN + THIRTYTWO
  sup = {
    `T2 -> `T4 + 
    `T4 -> `T8 + 
    `T8 -> `T16 + 
    `T16 -> `T32
  }
  type = {`S0 -> 0 + `S1 -> 1}
  Left = `L
  Right = `R
  Up = `U
  Down = `D
  Direction = Left + Right + Up + Down
  board = {
    `S0 -> 0 -> 0 -> `T2 + 
    `S0 -> 1 -> 1 -> `T2 + 
    `S0 -> 2 -> 2 -> `T2 + 
    `S1 -> 0 -> 0 -> `T2 + 
    `S1 -> 1 -> 0 -> `T2 + 
    `S1 -> 2 -> 0 -> `T2
  }
}
example leftSomeMerge is {some pre, post: State, d: Direction | move[pre,d,post]  and (not post = pre)} for {
  State = `S0 + `S1
  TWO = `T2
  FOUR = `T4
  EIGHT = `T8
  SIXTEEN = `T16
  THIRTYTWO = `T32
  Tile = TWO + FOUR + EIGHT + SIXTEEN + THIRTYTWO
  sup = {
    `T2 -> `T4 + 
    `T4 -> `T8 + 
    `T8 -> `T16 + 
    `T16 -> `T32
  }
  type = {`S0 -> 0 + `S1 -> 1}
  Left = `L
  Right = `R
  Up = `U
  Down = `D
  Direction = Left + Right + Up + Down
  board = {
    `S0 -> 0 -> 0 -> `T2 + 
    `S0 -> 1 -> 1 -> `T2 + 
    `S0 -> 1 -> 0 -> `T4 +
    `S0 -> 2 -> 2 -> `T2 + 
    `S0 -> 0 -> 2 -> `T2 +
    `S1 -> 0 -> 0 -> `T4 + 
    `S1 -> 1 -> 0 -> `T4 +
    `S1 -> 1 -> 1 -> `T2 + 
    `S1 -> 2 -> 0 -> `T2
  }
}

example rightMerge is {some pre, post: State, d: Direction | move[pre,d,post]  and (not post = pre)} for {
  State = `S0 + `S1
  TWO = `T2
  FOUR = `T4
  EIGHT = `T8
  SIXTEEN = `T16
  THIRTYTWO = `T32
  Tile = TWO + FOUR + EIGHT + SIXTEEN + THIRTYTWO
  sup = {
    `T2 -> `T4 + 
    `T4 -> `T8 + 
    `T8 -> `T16 + 
    `T16 -> `T32
  }
  type = {`S0 -> 0 + `S1 -> 1}
  Left = `L
  Right = `R
  Up = `U
  Down = `D
  Direction = Left + Right + Up + Down
  board = {
    `S0 -> 0 -> 0 -> `T4 + 
    `S0 -> 0 -> 2 -> `T4 +
    `S0 -> 1 -> 0 -> `T4 + 
    `S0 -> 1 -> 1 -> `T4 +
    `S0 -> 2 -> 2 -> `T4 + 
    `S0 -> 2 -> 1 -> `T4 +
    `S1 -> 0 -> 2 -> `T8 + 
    `S1 -> 1 -> 2 -> `T8 +
    `S1 -> 2 -> 2 -> `T8 
  }
}

example leftMerge is {some pre, post: State, d: Direction | move[pre,d,post]  and (not post = pre)} for {
  State = `S0 + `S1
  TWO = `T2
  FOUR = `T4
  EIGHT = `T8
  SIXTEEN = `T16
  THIRTYTWO = `T32
  Tile = TWO + FOUR + EIGHT + SIXTEEN + THIRTYTWO
  sup = {
    `T2 -> `T4 + 
    `T4 -> `T8 + 
    `T8 -> `T16 + 
    `T16 -> `T32
  }
  type = {`S0 -> 0 + `S1 -> 1}
  Left = `L
  Right = `R
  Up = `U
  Down = `D
  Direction = Left + Right + Up + Down
  board = {
    `S0 -> 0 -> 0 -> `T4 + 
    `S0 -> 0 -> 2 -> `T4 +
    `S0 -> 1 -> 0 -> `T4 + 
    `S0 -> 1 -> 1 -> `T4 +
    `S0 -> 2 -> 2 -> `T4 + 
    `S0 -> 2 -> 1 -> `T4 +
    `S1 -> 0 -> 0 -> `T8 + 
    `S1 -> 1 -> 0 -> `T8 +
    `S1 -> 2 -> 0 -> `T8 
  }
}

example upMerge is {some pre, post: State, d: Direction | move[pre,d,post]  and (not post = pre)} for {
  State = `S0 + `S1
  TWO = `T2
  FOUR = `T4
  EIGHT = `T8
  SIXTEEN = `T16
  THIRTYTWO = `T32
  Tile = TWO + FOUR + EIGHT + SIXTEEN + THIRTYTWO
  sup = {
    `T2 -> `T4 + 
    `T4 -> `T8 + 
    `T8 -> `T16 + 
    `T16 -> `T32
  }
  type = {`S0 -> 0 + `S1 -> 1}
  Left = `L
  Right = `R
  Up = `U
  Down = `D
  Direction = Left + Right + Up + Down
  board = {
    `S0 -> 0 -> 0 -> `T4 + 
    `S0 -> 2 -> 0 -> `T4 +
    `S0 -> 1 -> 1 -> `T4 + 
    `S0 -> 0 -> 1 -> `T4 +
    `S0 -> 1 -> 2 -> `T4 + 
    `S0 -> 2 -> 2 -> `T4 +
    `S1 -> 0 -> 0 -> `T8 + 
    `S1 -> 0 -> 1 -> `T8 +
    `S1 -> 0 -> 2 -> `T8 
  }
}

example downMerge is {some pre, post: State, d: Direction | move[pre,d,post]  and (not post = pre)} for {
  State = `S0 + `S1
  TWO = `T2
  FOUR = `T4
  EIGHT = `T8
  SIXTEEN = `T16
  THIRTYTWO = `T32
  Tile = TWO + FOUR + EIGHT + SIXTEEN + THIRTYTWO
  sup = {
    `T2 -> `T4 + 
    `T4 -> `T8 + 
    `T8 -> `T16 + 
    `T16 -> `T32
  }
  type = {`S0 -> 0 + `S1 -> 1}
  Left = `L
  Right = `R
  Up = `U
  Down = `D
  Direction = Left + Right + Up + Down
  board = {
    `S0 -> 0 -> 0 -> `T4 + 
    `S0 -> 2 -> 0 -> `T4 +
    `S0 -> 1 -> 1 -> `T4 + 
    `S0 -> 0 -> 1 -> `T4 +
    `S0 -> 1 -> 2 -> `T4 + 
    `S0 -> 2 -> 2 -> `T4 +
    `S1 -> 2 -> 0 -> `T8 + 
    `S1 -> 2 -> 1 -> `T8 +
    `S1 -> 2 -> 2 -> `T8 
  }
}

example dissapearningSquare is not {some pre, post: State, d: Direction | move[pre,d,post] and (not post = pre)} for {
  State = `S0 + `S1
  TWO = `T2
  FOUR = `T4
  EIGHT = `T8
  SIXTEEN = `T16
  THIRTYTWO = `T32
  Tile = TWO + FOUR + EIGHT + SIXTEEN + THIRTYTWO
  sup = {
    `T2 -> `T4 + 
    `T4 -> `T8 + 
    `T8 -> `T16 + 
    `T16 -> `T32
  }
  type = {`S0 -> 0 + `S1 -> 1}
  Left = `L
  Right = `R
  Up = `U
  Down = `D
  Direction = Left + Right + Up + Down
  board = {
    `S0 -> 0 -> 0 -> `T4 
  }
}

example changingSquare is not {some pre, post: State, d: Direction | move[pre,d,post] and (not post = pre)} for {
  State = `S0 + `S1
  TWO = `T2
  FOUR = `T4
  EIGHT = `T8
  SIXTEEN = `T16
  THIRTYTWO = `T32
  Tile = TWO + FOUR + EIGHT + SIXTEEN + THIRTYTWO
  sup = {
    `T2 -> `T4 + 
    `T4 -> `T8 + 
    `T8 -> `T16 + 
    `T16 -> `T32
  }
  type = {`S0 -> 0 + `S1 -> 1}
  Left = `L
  Right = `R
  Up = `U
  Down = `D
  Direction = Left + Right + Up + Down
  board = {
    `S0 -> 0 -> 0 -> `T4 +
    `S1 -> 0 -> 2 -> `T2
  }
}

example twosToEight is not {some pre, post: State, d: Direction | move[pre,d,post] and (not post = pre)} for {
  State = `S0 + `S1
  TWO = `T2
  FOUR = `T4
  EIGHT = `T8
  SIXTEEN = `T16
  THIRTYTWO = `T32
  Tile = TWO + FOUR + EIGHT + SIXTEEN + THIRTYTWO
  sup = {
    `T2 -> `T4 + 
    `T4 -> `T8 + 
    `T8 -> `T16 + 
    `T16 -> `T32
  }
  type = {`S0 -> 0 + `S1 -> 1}
  Left = `L
  Right = `R
  Up = `U
  Down = `D
  Direction = Left + Right + Up + Down
  board = {
    `S0 -> 0 -> 0 -> `T2 +
    `S0 -> 0 -> 1 -> `T2 + 
    `S1 -> 0 -> 0 -> `T8
  }
}

example dontShiftAllTheWay is not {some pre, post: State, d: Direction | move[pre,d,pre.next] and (not post = pre)} for {
  State = `S0 + `S1
  next = {`S0 -> `S1}
  TWO = `T2
  FOUR = `T4
  EIGHT = `T8
  SIXTEEN = `T16
  THIRTYTWO = `T32
  Tile = TWO + FOUR + EIGHT + SIXTEEN + THIRTYTWO
  sup = {
    `T2 -> `T4 + 
    `T4 -> `T8 + 
    `T8 -> `T16 + 
    `T16 -> `T32
  }
  type = {`S0 -> 0 + `S1 -> 1}
  Left = `L
  Right = `R
  Up = `U
  Down = `D
  Direction = Left + Right + Up + Down
  board = {
    `S0 -> 0 -> 0 -> `T2 +
    `S1 -> 0 -> 1 -> `T2
  }
}

example blockedMerge is not {some pre, post: State, d: Direction | move[pre,d,post] and (not post = pre)} for {
  State = `S0 + `S1
  TWO = `T2
  FOUR = `T4
  EIGHT = `T8
  SIXTEEN = `T16
  THIRTYTWO = `T32
  Tile = TWO + FOUR + EIGHT + SIXTEEN + THIRTYTWO
  sup = {
    `T2 -> `T4 + 
    `T4 -> `T8 + 
    `T8 -> `T16 + 
    `T16 -> `T32
  }
  type = {`S0 -> 0 + `S1 -> 1}
  Left = `L
  Right = `R
  Up = `U
  Down = `D
  Direction = Left + Right + Up + Down
  board = {
    `S0 -> 0 -> 0 -> `T2 +
    `S0 -> 0 -> 2 -> `T2 + 
    `S0 -> 0 -> 1 -> `T4 + 
    `S1 -> 0 -> 0 -> `T4 + 
    `S1 -> 0 -> 1 -> `T4
  }
}

example insertTwo is {some pre : State| insert[pre,pre.next]} for {
  State = `S0 + `S1
  next = {`S0 -> `S1}
  TWO = `T2
  FOUR = `T4
  EIGHT = `T8
  SIXTEEN = `T16
  THIRTYTWO = `T32
  Tile = TWO + FOUR + EIGHT + SIXTEEN + THIRTYTWO
  sup = {
    `T2 -> `T4 + 
    `T4 -> `T8 + 
    `T8 -> `T16 + 
    `T16 -> `T32
  }
  type = {`S0 -> 1 + `S1 -> 0}
  Left = `L
  Right = `R
  Up = `U
  Down = `D
  Direction = Left + Right + Up + Down
  board = {
    `S0 -> 0 -> 0 -> `T2 +
    `S0 -> 0 -> 1 -> `T2 + 
    `S1 -> 0 -> 0 -> `T2 +
    `S1 -> 0 -> 1 -> `T2 + 
    `S1 -> 2 -> 2 -> `T2
  }
}

example insertFour is {some pre : State| insert[pre,pre.next]} for {
  State = `S0 + `S1
  next = {`S0 -> `S1}
  TWO = `T2
  FOUR = `T4
  EIGHT = `T8
  SIXTEEN = `T16
  THIRTYTWO = `T32
  Tile = TWO + FOUR + EIGHT + SIXTEEN + THIRTYTWO
  sup = {
    `T2 -> `T4 + 
    `T4 -> `T8 + 
    `T8 -> `T16 + 
    `T16 -> `T32
  }
  type = {`S0 -> 1 + `S1 -> 0}
  Left = `L
  Right = `R
  Up = `U
  Down = `D
  Direction = Left + Right + Up + Down
  board = {
    `S0 -> 0 -> 0 -> `T2 +
    `S0 -> 0 -> 1 -> `T2 + 
    `S1 -> 0 -> 0 -> `T2 +
    `S1 -> 0 -> 1 -> `T2 + 
    `S1 -> 2 -> 2 -> `T4
  }
}

example insertEight is not {some pre : State| insert[pre,pre.next]} for {
  State = `S0 + `S1
  next = {`S0 -> `S1}
  TWO = `T2
  FOUR = `T4
  EIGHT = `T8
  SIXTEEN = `T16
  THIRTYTWO = `T32
  Tile = TWO + FOUR + EIGHT + SIXTEEN + THIRTYTWO
  sup = {
    `T2 -> `T4 + 
    `T4 -> `T8 + 
    `T8 -> `T16 + 
    `T16 -> `T32
  }
  type = {`S0 -> 1 + `S1 -> 0}
  Left = `L
  Right = `R
  Up = `U
  Down = `D
  Direction = Left + Right + Up + Down
  board = {
    `S0 -> 0 -> 0 -> `T2 +
    `S0 -> 0 -> 1 -> `T2 + 
    `S1 -> 0 -> 0 -> `T2 +
    `S1 -> 0 -> 1 -> `T2 + 
    `S1 -> 2 -> 2 -> `T8
  }
}

example insertTwice is not {some pre : State| insert[pre,pre.next]} for {
  State = `S0 + `S1
  next = {`S0 -> `S1}
  TWO = `T2
  FOUR = `T4
  EIGHT = `T8
  SIXTEEN = `T16
  THIRTYTWO = `T32
  Tile = TWO + FOUR + EIGHT + SIXTEEN + THIRTYTWO
  sup = {
    `T2 -> `T4 + 
    `T4 -> `T8 + 
    `T8 -> `T16 + 
    `T16 -> `T32
  }
  type = {`S0 -> 1 + `S1 -> 0}
  Left = `L
  Right = `R
  Up = `U
  Down = `D
  Direction = Left + Right + Up + Down
  board = {
    `S0 -> 0 -> 0 -> `T2 +
    `S0 -> 0 -> 1 -> `T2 + 
    `S1 -> 0 -> 0 -> `T2 +
    `S1 -> 0 -> 1 -> `T2 + 
    `S1 -> 2 -> 2 -> `T4 + 
    `S1 -> 2 -> 1 -> `T2
  }
}

example insertNone is not {some pre : State| insert[pre,pre.next]} for {
  State = `S0 + `S1
  next = {`S0 -> `S1}
  TWO = `T2
  FOUR = `T4
  EIGHT = `T8
  SIXTEEN = `T16
  THIRTYTWO = `T32
  Tile = TWO + FOUR + EIGHT + SIXTEEN + THIRTYTWO
  sup = {
    `T2 -> `T4 + 
    `T4 -> `T8 + 
    `T8 -> `T16 + 
    `T16 -> `T32
  }
  type = {`S0 -> 1 + `S1 -> 0}
  Left = `L
  Right = `R
  Up = `U
  Down = `D
  Direction = Left + Right + Up + Down
  board = {
    `S0 -> 0 -> 0 -> `T2 +
    `S0 -> 0 -> 1 -> `T2 + 
    `S1 -> 0 -> 0 -> `T2 +
    `S1 -> 0 -> 1 -> `T2
  }
}

example validInitState is {some s: State| initState[s]} for {
  State = `S0
  TWO = `T2
  FOUR = `T4
  EIGHT = `T8
  SIXTEEN = `T16
  THIRTYTWO = `T32
  Tile = TWO + FOUR + EIGHT + SIXTEEN + THIRTYTWO
  sup = {
    `T2 -> `T4 + 
    `T4 -> `T8 + 
    `T8 -> `T16 + 
    `T16 -> `T32
  }
  Left = `L
  Right = `R
  Up = `U
  Down = `D
  Direction = Left + Right + Up + Down

  type = {
    `S0 -> 0
  }

    board = {
    `S0 -> 0 -> 0 -> `T2 + 
    `S0 -> 1 -> 1 -> `T2
  }
}

example TooManyTilesInitState is not {some s: State| initState[s]} for {
  State = `S0
  TWO = `T2
  FOUR = `T4
  EIGHT = `T8
  SIXTEEN = `T16
  THIRTYTWO = `T32
  Tile = TWO + FOUR + EIGHT + SIXTEEN + THIRTYTWO
  sup = {
    `T2 -> `T4 + 
    `T4 -> `T8 + 
    `T8 -> `T16 + 
    `T16 -> `T32
  }

  Left = `L
  Right = `R
  Up = `U
  Down = `D
  Direction = Left + Right + Up + Down

  type = {
    `S0 -> 0
  }

    board = {
    `S0 -> 0 -> 0 -> `T2 + 
    `S0 -> 1 -> 1 -> `T2 + 
    `S0 -> 0 -> 1 -> `T2     
  }
}

example NotEnoughTilesInitState is not {some s: State| initState[s]} for {
  State = `S0
  TWO = `T2
  FOUR = `T4
  EIGHT = `T8
  SIXTEEN = `T16
  THIRTYTWO = `T32
  Tile = TWO + FOUR + EIGHT + SIXTEEN + THIRTYTWO
  sup = {
    `T2 -> `T4 + 
    `T4 -> `T8 + 
    `T8 -> `T16 + 
    `T16 -> `T32
  }
  Left = `L
  Right = `R
  Up = `U
  Down = `D
  Direction = Left + Right + Up + Down

  type = {
    `S0 -> 0
  }

  board = {
    `S0 -> 0 -> 0 -> `T2
  }
}

//example trace!
run {
  traces
} for 3 Int, 30 State for {next is linear}
