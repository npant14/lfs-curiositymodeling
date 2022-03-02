#lang forge/bsl

// empty file for the game
// contents to be discussed

sig State {
  board: pfunc Int -> Int -> Tile
}

abstract sig Tile {
  sup: lone Tile
}
one sig TWO, FOUR extends Tile {}


abstract sig Direction {}
one sig Left, Right, Up, Down extends Direction {} 
pred increasingOrder{
  TWO.sup = FOUR
  no FOUR.sup
}

// some sig for move direction perhaps?


//well formedness for 4x4 board
pred wellformed {
  all s: State | {
    all row, col: Int | {
      (row < 0 or row > 3 or col < 0 or col > 3) 
        implies no s.board[row][col]    
    }
  }
}

// pred init condition
pred initState[s: State] {

}
// pred final condition
pred finalState[s: State] {

}

pred validCord[i: Int]{
  not(i < 0) and not(i > 3)
}

// says if this move is a possible candidate for a move
pred possibleMove[pre: State, move: Direction]{
  move = Left => {
    some rowOfFilled, colOfFilled, rowOfEmpty, ColOfEmpty: Int | {
      validCord[rowOfFilled] and validCord[colOfFilled] and validCord[rowOfEmpty] and validCord[ColOfEmpty]
      some pre.board[rowOfFilled][colOfFilled]
      no pre.board[rowOfEmpty][ColOfEmpty]
      ColOfEmpty < colOfFilled
    }
  }
  move = Right => {

  }

  move = Up => {

  }

  move = Down => {

  }
}


// transition, move, something.
// unclear what is necessary for this pred at this point in time.  
// Can't move in a direction that you can't move in
pred move [pre: State, theMove: Direction, post: State]{
  possibleMove[pre, theMove]
  theMove = Left => {
    -- for all rows
    all row: Int | {
      -- if there is only 1 tile in the row
      #{col: Int | some pre.board[row][col]} = 1 =>{
        -- the one tile goes to the post.board[row][0]
        some t: Tile, col: Int | pre.board[row][col] = t and post.board[row][0] = t and{
          -- the only filled tile in the row in the post state is the left most
          no post.board[row][1] and no post.board[row][2] and no post.board[row][3]
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
           (post.board[row][0] = pre.board[row][col1][sup]) and (no post.board[row][1]) and (no post.board[row][2]) and (no post.board[row][3])
         }
         -- if they are both different, then the left most tile goes to the far leftm, and the second most goes to the next spot
         (not pre.board[row][col1] = pre.board[row][col2]) =>{
           post.board[row][0] = pre.board[row][col1] and post.board[row][1] = pre.board[row][col2] and no post.board[row][2] and no post.board[row][3]
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
            post.board[row][0] = pre.board[row][col1][sup] and post.board[row][1] = pre.board[row][col3] and no post.board[row][2] and no post.board[row][3]
          }
          -- If the left two arent equal, but the right two are, ...
          ((not pre.board[row][col1] = pre.board[row][col2]) and pre.board[row][col2] = pre.board[row][col3]) => {
            post.board[row][0] = pre.board[row][col1] and post.board[row][1] = pre.board[row][col3][sup] and no post.board[row][2] and no post.board[row][3]
          }
          -- if none are equal, just push them all to the left
          ((not pre.board[row][col1] = pre.board[row][col2]) and (not pre.board[row][col2] = pre.board[row][col3])) => {
             post.board[row][0] = pre.board[row][col1] and post.board[row][1] = pre.board[row][col2] and post.board[row][2] = pre.board[row][col3] and no post.board[row][3]
          }
        }
      }
      #{col: Int | some pre.board[row][col]} = 4 =>{
        some col1, col2, col3, col4: Int| {
          -- coll one has t1, and so on...
          some pre.board[row][col1] and some pre.board[row][col2] and some pre.board[row][col3] and some pre.board[row][col4]
          col1 < col2 and col2 < col3 and col3 < col4
          --if there are two matches in the row, combine both fo them on the left
          (pre.board[row][col1] = pre.board[row][col2] and pre.board[row][col3] = pre.board[row][col4]) =>{
            post.board[row][0] = pre.board[row][col1][sup] and post.board[row][1] = pre.board[row][col3][sup] and no post.board[row][2] and no post.board[row][3]
          }
          -- If the left is a mathc, comine those two
          (pre.board[row][col1] = pre.board[row][col2] and (not pre.board[row][col3] = pre.board[row][col4])) =>{
            post.board[row][0] = pre.board[row][col1][sup] and post.board[row][1] = pre.board[row][col3] and post.board[row][2] = pre.board[row][col4] and no post.board[row][3]
          }
          -- if the middle is a match, combine the middle
          ((not pre.board[row][col1] = pre.board[row][col2]) and pre.board[row][col2] = pre.board[row][col3]) =>{
            post.board[row][0] = pre.board[row][col1] and post.board[row][1] = pre.board[row][col2][sup] and post.board[row][2] = pre.board[row][col4] and no post.board[row][3]
          }
          -- if the right is the only match, combine
          ((not pre.board[row][col1] = pre.board[row][col2]) and (not pre.board[row][col2] = pre.board[row][col3]) and (pre.board[row][col3] = pre.board[row][col4])) =>{
            post.board[row][0] = pre.board[row][col1] and post.board[row][1] = pre.board[row][col2] and post.board[row][2] = pre.board[row][col3][sup] and no post.board[row][3]
          }
          -- if there are no matches, then the row stays the same
          ((not pre.board[row][col1] = pre.board[row][col2]) and (not pre.board[row][col2] = pre.board[row][col3]) and (not pre.board[row][col3]=pre.board[row][col4])) => {
          all col: Int | post.board[row][col] = pre.board[row][col]
          }
        }
      }
    }
  }
  theMove = Right => {

    -- for all rows
    all row: Int | {
      -- if there is only 1 tile in the row
      #{col: Int | some pre.board[row][col]} = 1 =>{
        -- the one tile goes to the post.board[row][3]
        some t: Tile, col: Int | pre.board[row][col] = t and post.board[row][3] = t and{
          -- the only filled tile in the row in the post state is the right most
          no post.board[row][1] and no post.board[row][2] and no post.board[row][0]
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
           post.board[row][3] = pre.board[row][col1][sup] and no post.board[row][1] and no post.board[row][2] and no post.board[row][0]
         }
         -- if they are both different, then the right most tile goes to the far right, and the second most goes to the next spot
         (not pre.board[row][col1] = pre.board[row][col2]) =>{
           post.board[row][2] = pre.board[row][col1] and post.board[row][3] = pre.board[row][col2] and no post.board[row][0] and no post.board[row][1]
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
            post.board[row][2] = pre.board[row][col1][sup] and post.board[row][3] = pre.board[row][col3] and no post.board[row][0] and no post.board[row][1]
          }
          -- If the left two arent equal, but the right two are, ...
          ((not pre.board[row][col1] = pre.board[row][col2]) and pre.board[row][col2] = pre.board[row][col3]) => {
            post.board[row][2] = pre.board[row][col1] and post.board[row][3] = pre.board[row][col3][sup] and no post.board[row][0] and no post.board[row][1]
          }
          -- if none are equal, just push them all to the right
          ((not pre.board[row][col1] = pre.board[row][col2]) and (not pre.board[row][col2] = pre.board[row][col3])) => {
             post.board[row][1] = pre.board[row][col1] and post.board[row][2] = pre.board[row][col2] and post.board[row][3] = pre.board[row][col3] and no post.board[row][0]
          }
        }
      }
      #{col: Int | some pre.board[row][col]} = 4 =>{
        some col1, col2, col3, col4: Int | {
          -- coll one has t1, and so on...
          some pre.board[row][col1] and some pre.board[row][col2] and some pre.board[row][col3] and some pre.board[row][col4]
          col1 < col2 and col2 < col3 and col3 < col4
          --if there are two matches in the row, combine both of them on the right
          (pre.board[row][col1] = pre.board[row][col2] and pre.board[row][col3] = pre.board[row][col4]) =>{
            post.board[row][2] = pre.board[row][col1][sup] and post.board[row][3] = pre.board[row][col3][sup] and no post.board[row][0] and no post.board[row][1]
          }
          -- If the left is a match, comine those two
          (pre.board[row][col1] = pre.board[row][col2] and (not pre.board[row][col3] = pre.board[row][col4])) =>{
            post.board[row][1] = pre.board[row][col1][sup] and post.board[row][2] = pre.board[row][col3] and post.board[row][3] = pre.board[row][col4] and no post.board[row][0]
          }
          -- if the middle is a match, combine the middle
          ((not pre.board[row][col3] = pre.board[row][col4]) and pre.board[row][col2] = pre.board[row][col3]) =>{
            post.board[row][1] = pre.board[row][col1] and post.board[row][2] = pre.board[row][col2][sup] and post.board[row][3] = pre.board[row][col4] and no post.board[row][0]
          }
          -- if the right is the only match, combine
          ((not pre.board[row][col1] = pre.board[row][col2]) and (not pre.board[row][col2] = pre.board[row][col3]) and (pre.board[row][col3] = pre.board[row][col4])) =>{
            post.board[row][1] = pre.board[row][col1] and post.board[row][2] = pre.board[row][col2] and post.board[row][3] = pre.board[row][col3][sup] and no post.board[row][0]
          }
          -- if there are no matches, then the row stays the same
          ((not pre.board[row][col1] = pre.board[row][col2]) and (not pre.board[row][col2] = pre.board[row][col3]) and (not pre.board[row][col3]= pre.board[row][col4])) => {
            all col: Int | post.board[row][col] = pre.board[row][col]
          }
        }
      }
    }

  }

  theMove = Up => {

    -- for all rows
    all col: Int | {
      -- if there is only 1 tile in the row
      #{row: Int | some pre.board[row][col]} = 1 =>{
        -- the one tile goes to the post.board[row][0]
        some t: Tile, row: Int | pre.board[row][col] = t and post.board[0][col] = t and{
          -- the only filled tile in the row in the post state is the left most
          no post.board[1][col] and no post.board[2][col] and no post.board[3][col]
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
           post.board[0][col] = pre.board[row1][col][sup] and no post.board[1][col] and no post.board[2][col] and no post.board[3][col]
         }
         -- if they are both different, then the left most tile goes to the far leftm, and the second most goes to the next spot
         (not pre.board[row1][col] = pre.board[row2][col]) =>{
           post.board[0][col] = pre.board[row1][col] and post.board[1][col] = pre.board[row2][col] and no post.board[2][col] and no post.board[3][col]
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
            post.board[0][col] = pre.board[row1][col][sup] and post.board[1][col] = pre.board[row3][col] and no post.board[2][col] and no post.board[3][col]
          }
          -- If the left two arent equal, but the right two are, ...
          ((not pre.board[row1][col] = pre.board[row2][col]) and pre.board[row2][col] = pre.board[row3][col]) => {
            post.board[0][col] = pre.board[row1][col] and post.board[1][col] = pre.board[row3][col][sup] and no post.board[2][col] and no post.board[3][col]
          }
          -- if none are equal, just push them all to the left
          ((not pre.board[row1][col] = pre.board[row2][col]) and (not pre.board[row2][col] = pre.board[row3][col])) => {
             post.board[0][col] = pre.board[row1][col] and post.board[1][col] = pre.board[row2][col] and post.board[2][col] = pre.board[row3][col] and no post.board[3][col]
          }
        }
      }
      #{row: Int | some pre.board[row][col]} = 4 =>{
        some row1, row2, row3, row4: Int| {
          -- coll one has t1, and so on...
          some pre.board[row1][col] and some pre.board[row2][col] and some pre.board[row3][col] and some pre.board[row4][col]
          row1 < row2 and row2 < row3 and row3 < row4
          --if there are two matches in the row, combine both fo them on the left
          (pre.board[row1][col] = pre.board[row2][col] and pre.board[row3][col] = pre.board[row4][col]) =>{
            post.board[0][col] = pre.board[row1][col][sup] and post.board[1][col] = pre.board[row3][col][sup] and no post.board[2][col] and no post.board[3][col]
          }
          -- If the left is a mathc, comine those two
          (pre.board[row1][col] = pre.board[row2][col] and (not pre.board[row3][col] = pre.board[row4][col])) =>{
            post.board[0][col] = pre.board[row1][col][sup] and post.board[1][col] = pre.board[row3][col] and post.board[2][col] = pre.board[row4][col] and no post.board[3][col]
          }
          -- if the middle is a match, combine the middle
          ((not pre.board[row1][col] = pre.board[row2][col]) and pre.board[row2][col] = pre.board[row3][col]) =>{
            post.board[0][col] = pre.board[row1][col] and post.board[1][col] = pre.board[row2][col][sup] and post.board[2][col] = pre.board[row4][col] and no post.board[3][col]
          }
          -- if the right is the only match, combine
          ((not pre.board[row1][col] = pre.board[row2][col]) and (not pre.board[row2][col] = pre.board[row3][col]) and (pre.board[row3][col] = pre.board[row4][col])) =>{
            post.board[0][col] = pre.board[row1][col] and post.board[1][col] = pre.board[row2][col] and post.board[2][col] = pre.board[row3][col][sup] and no post.board[3][col]
          }
          -- if there are no matches, then the row stays the same
          ((not pre.board[row1][col] = pre.board[row2][col]) and (not pre.board[row2][col] = pre.board[row3][col]) and (not pre.board[row3][col]= pre.board[row4][col])) => {
            all row: Int | pre.board[row][col] = post.board[row][col]
          }
        }
      }
    }
  }

  theMove = Down => {

    -- for all rows
    all col: Int | {
      -- if there is only 1 tile in the row
      #{row: Int | some pre.board[row][col]} = 1 =>{
        -- the one tile goes to the post.board[row][3]
        some t: Tile, row: Int | pre.board[row][col] = t and post.board[3][col] = t and{
          -- the only filled tile in the row in the post state is the right most
          no post.board[1][col] and no post.board[2][col] and no post.board[0][col]
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
           post.board[3][col] = pre.board[row1][col][sup] and no post.board[1][col] and no post.board[2][col] and no post.board[0][col]
         }
         -- if they are both different, then the right most tile goes to the far right, and the second most goes to the next spot
         (not pre.board[row1][col] = pre.board[row2][col]) =>{
           post.board[2][col] = pre.board[row1][col] and post.board[3][col] = pre.board[row2][col] and no post.board[0][col] and no post.board[1][col]
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
            post.board[2][col] = pre.board[row1][col][sup] and post.board[3][col] = pre.board[row3][col] and no post.board[0][col] and no post.board[1][col]
          }
          -- If the left two arent equal, but the right two are, ...
          ((not pre.board[row1][col] = pre.board[row2][col]) and pre.board[row2][col] = pre.board[row3][col]) => {
            post.board[2][col] = pre.board[row1][col] and post.board[3][col] = pre.board[row3][col][sup] and no post.board[0][col] and no post.board[1][col]
          }
          -- if none are equal, just push them all to the right
          ((not pre.board[row1][col] = pre.board[row2][col]) and (not pre.board[row2][col] = pre.board[row3][col])) => {
             post.board[1][col] = pre.board[row1][col] and post.board[2][col] = pre.board[row2][col] and post.board[3][col] = pre.board[row3][col] and no post.board[0][col]
          }
        }
      }
      #{row: Int | some pre.board[row][col]} = 4 =>{
        some row1, row2, row3, row4: Int| {
          -- coll one has t1, and so on...
          some pre.board[row1][col] and some pre.board[row2][col] and some pre.board[row2][col] and some pre.board[row4][col]
          row1 < row2 and row2 < row3 and row3 < row4
          --if there are two matches in the row, combine both of them on the right
          (pre.board[row1][col] = pre.board[row2][col] and pre.board[row3][col] = pre.board[row4][col]) =>{
            post.board[2][col] = pre.board[row1][col][sup] and post.board[3][col] = pre.board[row3][col][sup] and no post.board[0][col] and no post.board[1][col]
          }
          -- If the left is a match, comine those two
          (pre.board[row1][col] = pre.board[row2][col] and (not pre.board[row3][col] = pre.board[row4][col])) =>{
            post.board[1][col] = pre.board[row1][col][sup] and post.board[2][col] = pre.board[row3][col] and post.board[3][col] = pre.board[row4][col] and no post.board[0][col]
          }
          -- if the middle is a match, combine the middle
          ((not pre.board[row3][col] = pre.board[row4][col]) and pre.board[row2][col] = pre.board[row3][col]) =>{
            post.board[1][col] = pre.board[row1][col] and post.board[2][col] = pre.board[row2][col][sup] and post.board[3][col] = pre.board[row4][col] and no post.board[0][col]
          }
          -- if the right is the only match, combine
          ((not pre.board[row1][col] = pre.board[row2][col]) and (not pre.board[row2][col] = pre.board[row3][col]) and (pre.board[row3][col] = pre.board[row4][col])) =>{
            post.board[1][col] = pre.board[row1][col] and post.board[2][col] = pre.board[row2][col] and post.board[3][col] = pre.board[row3][col][sup] and no post.board[0][col]
          }
          -- if there are no matches, then the row stays the same
          ((not pre.board[row1][col] = pre.board[row2][col]) and (not pre.board[row2][col] = pre.board[row3][col]) and (not pre.board[row3][col]=pre.board[row4][col])) => {
            all row: Int | pre.board[row][col] = post.board[row][col]
          }
        }
      }
    }
  }
}


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
    `S0 -> 0 -> 2 -> `T2 + 
    `S1 -> 0 -> 0 -> `T4 
  }
}

example invalidTransition1 is {not (some pre, post: State, d: Direction | move[pre,d,post])} for {
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
    `S1 -> 2 -> 0 -> `T2 
  }
}


// pred trace