#lang forge/bsl

// empty file for the game
// contents to be discussed

sig State {
  board: pfunc Int -> Int -> Tile,
  next: lone State,
  type: one Int,
  dir: lone Direction
}

abstract sig Tile {
  sup: lone Tile
}
one sig TWO, FOUR, EIGHT, SIXTEEN, THIRTYTWO extends Tile {}


abstract sig Direction {}
one sig Left, Right, Up, Down extends Direction {} 
pred increasingOrder{
  TWO.sup = FOUR
  FOUR.sup = EIGHT
  EIGHT.sup = SIXTEEN
  SIXTEEN.sup = THIRTYTWO
  no THIRTYTWO.sup
}

// some sig for move direction perhaps?


//well formedness for 4x4 board
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

// pred init condition
pred initState[s: State] {
  s.type = 0
  // all row, col : Int | {
  //   {
  //     //start with two 2s on the board
  //     {#{s.board[row][col] = TWO} = 2 and
  //      #{s.board[row][col] = FOUR} = 0} or

  //     //or start with one 2 and one 4
  //     {#{s.board[row][col] = TWO} = 1 and
  //     #{s.board[row][col] = FOUR} = 1}}

  //     //everything else is a 0
  //     not {s.board[row][col] = TWO or s.board[row][col] = FOUR} => no s.board[row][col]
  // }

  #{row, col: Int | s.board[row][col] = TWO} = 2 and #{row, col: Int | s.board[row][col] = FOUR} = 0 //or 
  //#{row, col: Int | s.board[row][col] = TWO} = 1 and #{row, col: Int | s.board[row][col] = FOUR} = 1 or 
  //#{row, col: Int | s.board[row][col] = TWO} = 0 and #{row, col: Int | s.board[row][col] = FOUR} = 2
  all row, col: Int | s.board[row][col] = TWO or  s.board[row][col] = FOUR or no s.board[row][col]

}
// pred final condition

pred finalState32[s: State] {
  some row, col : Int | {
    s.board[row][col] = THIRTYTWO
  }
}

pred validCord[i: Int]{
  not(i < 0) and not(i > 3)
}



pred insert[pre: State, post: State]{
  pre.type = 1
  some row, col: Int | {
    no pre.board[row][col]
    post.board[row][col] = TWO or post.board[row][col] = FOUR
    all row2, col2: Int | not pre.board[row2][col2] = post.board[row2][col2] => {row = row2 and col=col2}
  }
}

// transition, move, something.
// unclear what is necessary for this pred at this point in time.  
// Can't move in a direction that you can't move in
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
          -- the only filled tile in the row in the post state is the left most
          no post.board[1][col] and no post.board[2][col]
        } 
      }
      -- If there are twp tiles in the row
      #{row: Int | some pre.board[row][col]} = 2 => {
       some row1, row2: Int |{
         -- t1 and t2 are disjoint
         some pre.board[row1][col] and some pre.board[row2][col]
         -- col1 is on the top of col 2
         row1 < row2
         -- if both squares are the same, the post row will only have their sup on the left
         pre.board[row1][col] = pre.board[row2][col] =>{
           post.board[0][col] = (pre.board[row1][col]).sup and no post.board[1][col] and no post.board[2][col]
         }
         -- if they are both different, then the left most tile goes to the far leftm, and the second most goes to the next spot
         (not pre.board[row1][col] = pre.board[row2][col]) =>{
           post.board[0][col] = pre.board[row1][col] and post.board[1][col] = pre.board[row2][col] and no post.board[2][col]
         }
       }
        
      }
      -- If there are 3 tiles in the row
      #{row: Int | some pre.board[row][col]} = 3 => {
        some row1, row2, row3: Int| {
          -- t1 is on the left, t3 is on the right
          some pre.board[row1][col] and some pre.board[row2][col] and some pre.board[row3][col]
          row1 < row2 and row2 < row3
          -- if the two on the far left are the same, comine them and put the 
          -- extra guy next to them,
          pre.board[row1][col] = pre.board[row2][col] => {
            post.board[0][col] = (pre.board[row1][col]).sup and post.board[1][col] = pre.board[row3][col] and no post.board[2][col]
          }
          -- If the left two arent equal, but the right two are, ...
          ((not pre.board[row1][col] = pre.board[row2][col]) and pre.board[row2][col] = pre.board[row3][col]) => {
            post.board[0][col] = pre.board[row1][col] and post.board[1][col] = (pre.board[row3][col]).sup and no post.board[2][col]
          }
          -- if none are equal, just push them all to the left
          ((not pre.board[row1][col] = pre.board[row2][col]) and (not pre.board[row2][col] = pre.board[row3][col])) => {
             post.board[0][col] = pre.board[row1][col] and post.board[1][col] = pre.board[row2][col] and post.board[2][col] = pre.board[row3][col]
          }
        }
      }
    }
  }

  theMove = Down => {

    -- for all rows
    all col: Int | {
      #{row: Int | some pre.board[row][col]} = 0 => #{row: Int | some post.board[row][col]} = 0
      -- if there is only 1 tile in the row
      #{row: Int | some pre.board[row][col]} = 1 =>{
        -- the one tile goes to the post.board[row][3]
        some row: Int | some pre.board[row][col] and post.board[2][col] = pre.board[row][col] and{
          -- the only filled tile in the row in the post state is the right most
          no post.board[1][col] and no post.board[0][col]
        } 
      }
      -- If there are twp tiles in the row
      #{row: Int | some pre.board[row][col]} = 2 => {
       some row1, row2: Int|{
         -- t1 and t2 are disjoint
         some pre.board[row1][col] and some pre.board[row2][col]
         -- col1 is on the left of col 2
         row1 < row2
         -- if both squares are the same, the post row will only have their sup on the right
         pre.board[row1][col] = pre.board[row2][col] =>{
           post.board[2][col] = (pre.board[row1][col]).sup and no post.board[1][col] and no post.board[0][col]
         }
         -- if they are both different, then the right most tile goes to the far right, and the second most goes to the next spot
         (not pre.board[row1][col] = pre.board[row2][col]) =>{
           post.board[1][col] = pre.board[row1][col] and post.board[2][col] = pre.board[row2][col] and no post.board[0][col]
         }
       }
        
      }
      -- If there are 3 tiles in the row
      #{row: Int | some pre.board[row][col]} = 3 => {
        some row1, row2, row3: Int| {
          -- t1 is on the left, t3 is on the right
          some pre.board[row1][col] and some pre.board[row2][col] and some pre.board[row2][col]
          row1 < row2 and row2 < row3
          -- if the two on the far left are the same, comine them and put the 
          -- extra guy next to them,
          pre.board[row1][col] = pre.board[row2][col] => {
            post.board[1][col] = (pre.board[row1][col]).sup and post.board[2][col] = pre.board[row3][col] and no post.board[0][col]
          }
          -- If the left two arent equal, but the right two are, ...
          ((not pre.board[row1][col] = pre.board[row2][col]) and pre.board[row2][col] = pre.board[row3][col]) => {
            post.board[1][col] = pre.board[row1][col] and post.board[2][col] = (pre.board[row3][col]).sup and no post.board[0][col]
          }
          -- if none are equal, just push them all to the right
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
  // no post : State {
  //   pre.board = post.board
  //   move[]
  // }
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

/*
example validTransition1 is {some pre, post: State, d: Direction | move[pre,d,post]} for {
  State = `S0 + `S1
  TWO = `T2
  FOUR = `T4
  Tile = TWO + FOUR
  sup = {
    `T2 -> `T4
  }
  Left = `L
  Right = `R
  Up = `U
  Down = `D
  Direction = Left + Right + Up + Down
  board = {
    `S0 -> 0 -> 0 -> `T2 + 
    `S0 -> 1 -> 1 -> `T2 + 
    `S0 -> 2 -> 2 -> `T2 + 
    `S0 -> 3 -> 4 -> `T2 + 
    `S1 -> 0 -> 0 -> `T2 + 
    `S1 -> 1 -> 0 -> `T2 + 
    `S1 -> 2 -> 0 -> `T2 + 
    `S1 -> 3 -> 0 -> `T2 
  }
}

example validTransition2 is {some pre, post: State, d: Direction | move[pre,d,post]} for {
  State = `S0 + `S1
  TWO = `T2
  FOUR = `T4
  Tile = TWO + FOUR
  sup = {
    `T2 -> `T4
  }

  Left = `L
  Right = `R
  Up = `U
  Down = `D
  Direction = Left + Right + Up + Down
  board = {
    `S0 -> 0 -> 0 -> `T2 + 
    `S0 -> 0 -> 1 -> `T2 + 
    `S1 -> 0 -> 0 -> `T4 
  }
}
*/
/*
example validTransition2 is {some pre, post: State, d: Direction | move[pre,d,post]} for {
  State = `S0 + `S1
  TWO = `T2
  FOUR = `T4
  Tile = TWO + FOUR
  sup = {
    `T2 -> `T4
  }
  type = {
    `S0 -> 0 + 
    `S1 -> 1
  }
  next = {
    `S0 -> `S1
  }
  Left = `L
  Right = `R
  Up = `U
  Down = `D
  Direction = Left + Right + Up + Down
  board = {
    `S0 -> 0 -> 3 -> `T2 + 
    `S1 -> 0 -> 0 -> `T2 
  }
}

example invalidTransition1 is not {some disj pre, post: State, d: Direction | move[pre,d,post]} for {
  State = `S0 + `S1
  TWO = `T2
  FOUR = `T4
  Tile = TWO + FOUR
  sup = {
    `T2 -> `T4
  }
  type = {
    `S0 -> 0 + 
    `S1 -> 1
  }
  next = {
    `S0 -> `S1
  }
  Left = `L
  Right = `R
  Up = `U
  Down = `D
  Direction = Left + Right + Up + Down
  board = {
    `S0 -> 0 -> 3 -> `T2 +
    `S0 -> 0 -> 2 -> `T2 +
    `S1 -> 1 -> 1 -> `T2
  }
}
*/
run {
  traces
} for 3 Int, 30 State for {next is linear}


// pred trace