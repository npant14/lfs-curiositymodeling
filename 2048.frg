#lang forge/bsl

// empty file for the game
// contents to be discussed

sig State {
  board: pfunc Int -> Int -> Tile
}

abstract sig Tile {
  sup: lone Tile
}
one sig ONE, TWO, FOUR, EIGHT, SIXTEEN, THIRTYTWO, SIXTYFOUR, ONETWENTYEIGHT extends Tile {}
one sig TWOFIFTYSIX, FIVETWELVE, TENTWENTYFOUR, TWENTYFOURTYEIGHT extends Tile {}

pred increasingOrder{
  ONE.sup = TWO
  TWO.sup = FOUR
  FOUR.sup = EIGHT
  EIGHT.sup = SIXTEEN
  SIXTEEN.sup = THIRTYTWO
  THIRTYTWO.sup = SIXTYFOUR
  SIXTYFOUR.sup = ONETWENTYEIGHT
  ONETWENTYEIGHT.sup = TWOFIFTYSIX
  TWOFIFTYSIX.sup = FIVETWELVE
  FIVETWELVE.sup = TENTWENTYFOUR
  TENTWENTYFOUR.sup = TWENTYFOURTYEIGHT
  no TWENTYFOURTYEIGHT.sup
}

// some sig for move direction perhaps?


//well formedness for 4x4 board
pred wellformed {
  all s: State | {
    all row, col: Int | {
      (row < 0 or row > 4 or col < 0 or col > 4) 
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
       some col1, col2: Int, t1, t2: Tile |{
         -- t1 and t2 are disjoint
         pre.board[row][col1] = t1 and pre.board[row][col2] = t2
         -- col1 is on the left of col 2
         col1 < col2
         -- if both squares are the same, the post row will only have their sup on the left
         t1 = t2 =>{
           post.board[row][0] = t1.sup and no post.board[row][1] and no post.board[row][2] and no post.board[row][3]
         }
         -- if they are both different, then the left most tile goes to the far leftm, and the second most goes to the next spot
         (not t1 = t2) =>{
           post.board[row][0] = t1 and post.board[row][1] = t2 and no post.board[row][2] and no post.board[row][3]
         }
       }
        
      }
      -- If there are 3 tiles in the row
      #{col: Int | some pre.board[row][col]} = 3 => {
        some col1, col2, col3: Int, t1, t2, t3: Tile | {
          -- t1 is on the left, t3 is on the right
          pre.board[row][col1] = t1 and pre.board[row][col2] = t2 and pre.board[row][col3] = t3
          col1 < col2 and col2 < col3
          -- if the two on the far left are the same, comine them and put the 
          -- extra guy next to them,
          t1 = t2 => {
            post.board[row][0] = t1.sup and post.board[row][1] = t3 and no post.board[row][2] and no post.board[row][3]
          }
          -- If the left two arent equal, but the right two are, ...
          ((not t1 = t2) and t2 = t3) => {
            post.board[row][0] = t1 and post.board[row][1] = t3.sup and no post.board[row][2] and no post.board[row][3]
          }
          -- if none are equal, just push them all to the left
          ((not t1 = t2) and (not t2 = t3)) => {
             post.board[row][0] = t1 and post.board[row][1] = t2 and post.board[row][2] = t3 and no post.board[row][3]
          }
        }
      }
      #{col: Int | some pre.board[row][col]} = 4 =>{
        some col1, col2, col3, col4: Int, t1, t2, t3, t4: Tile | {
          -- coll one has t1, and so on...
          pre.board[row][col1] = t1 and pre.board[row][col2] = t2 and pre.board[row][col3] = t3 and pre.board[row][col4] = t4
          col1 < col2 and col2 < col3 and col3 < col4
          --if there are two matches in the row, combine both fo them on the left
          (t1 = t2 and t3 = t4) =>{
            post.board[row][0] = t1.sup and post.board[row][1] = t3.sup and no post.board[row][2] and no post.board[row][3]
          }
          -- If the left is a mathc, comine those two
          (t1 = t2 and (not t3 = t4)) =>{
            post.board[row][0] = t1.sup and post.board[row][1] = t3 and post.board[row][2] = t4 and no post.board[row][3]
          }
          -- if the middle is a match, combine the middle
          ((not t1 = t2) and t2 = t3) =>{
            post.board[row][0] = t1 and post.board[row][1] = t2.sup and post.board[row][2] = t4 and no post.board[row][3]
          }
          -- if the right is the only match, combine
          ((not t1 = t2) and (not t2 = t3) and (t3 = t4)) =>{
            post.board[row][0] = t1 and post.board[row][1] = t2 and post.board[row][2] = t3.sup and no post.board[row][3]
          }
          -- if there are no matches, then the row stays the same
          ((not t1 = t2) and (not t2 = t3) and (not t3=t4)) => {
            post.board[row] = pre.board[row]
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
       some col1, col2: Int, t1, t2: Tile |{
         -- t1 and t2 are disjoint
         pre.board[row][col1] = t1 and pre.board[row][col2] = t2
         -- col1 is on the left of col 2
         col1 < col2
         -- if both squares are the same, the post row will only have their sup on the right
         t1 = t2 =>{
           post.board[row][3] = t1.sup and no post.board[row][1] and no post.board[row][2] and no post.board[row][0]
         }
         -- if they are both different, then the right most tile goes to the far right, and the second most goes to the next spot
         (not t1 = t2) =>{
           post.board[row][2] = t1 and post.board[row][3] = t2 and no post.board[row][0] and no post.board[row][1]
         }
       }
        
      }
      -- If there are 3 tiles in the row
      #{col: Int | some pre.board[row][col]} = 3 => {
        some col1, col2, col3: Int, t1, t2, t3: Tile | {
          -- t1 is on the left, t3 is on the right
          pre.board[row][col1] = t1 and pre.board[row][col2] = t2 and pre.board[row][col3] = t3
          col1 < col2 and col2 < col3
          -- if the two on the far left are the same, comine them and put the 
          -- extra guy next to them,
          t1 = t2 => {
            post.board[row][2] = t1.sup and post.board[row][3] = t3 and no post.board[row][0] and no post.board[row][1]
          }
          -- If the left two arent equal, but the right two are, ...
          ((not t1 = t2) and t2 = t3) => {
            post.board[row][2] = t1 and post.board[row][3] = t3.sup and no post.board[row][0] and no post.board[row][1]
          }
          -- if none are equal, just push them all to the right
          ((not t1 = t2) and (not t2 = t3)) => {
             post.board[row][1] = t1 and post.board[row][2] = t2 and post.board[row][3] = t3 and no post.board[row][0]
          }
        }
      }
      #{col: Int | some pre.board[row][col]} = 4 =>{
        some col1, col2, col3, col4: Int, t1, t2, t3, t4: Tile | {
          -- coll one has t1, and so on...
          pre.board[row][col1] = t1 and pre.board[row][col2] = t2 and pre.board[row][col3] = t3 and pre.board[row][col4] = t4
          col1 < col2 and col2 < col3 and col3 < col4
          --if there are two matches in the row, combine both of them on the right
          (t1 = t2 and t3 = t4) =>{
            post.board[row][2] = t1.sup and post.board[row][3] = t3.sup and no post.board[row][0] and no post.board[row][1]
          }
          -- If the left is a match, comine those two
          (t1 = t2 and (not t3 = t4)) =>{
            post.board[row][1] = t1.sup and post.board[row][2] = t3 and post.board[row][3] = t4 and no post.board[row][0]
          }
          -- if the middle is a match, combine the middle
          ((not t1 = t2) and t2 = t3) =>{
            post.board[row][1] = t1 and post.board[row][2] = t2.sup and post.board[row][3] = t4 and no post.board[row][0]
          }
          -- if the right is the only match, combine
          ((not t1 = t2) and (not t2 = t3) and (t3 = t4)) =>{
            post.board[row][1] = t1 and post.board[row][2] = t2 and post.board[row][3] = t3.sup and no post.board[row][0]
          }
          -- if there are no matches, then the row stays the same
          ((not t1 = t2) and (not t2 = t3) and (not t3=t4)) => {
            post.board[row] = pre.board[row]
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
       some row1, row2: Int, t1, t2: Tile |{
         -- t1 and t2 are disjoint
         pre.board[col][row1] = t1 and pre.board[col][row2] = t2
         -- col1 is on the top of col 2
         row1 < row2
         -- if both squares are the same, the post row will only have their sup on the left
         t1 = t2 =>{
           post.board[0][col] = t1.sup and no post.board[1][col] and no post.board[2][col] and no post.board[3][col]
         }
         -- if they are both different, then the left most tile goes to the far leftm, and the second most goes to the next spot
         (not t1 = t2) =>{
           post.board[0][col] = t1 and post.board[1][col] = t2 and no post.board[2][col] and no post.board[3][col]
         }
       }
        
      }
      -- If there are 3 tiles in the row
      #{row: Int | some pre.board[row][col]} = 3 => {
        some row1, row2, row3: Int, t1, t2, t3: Tile | {
          -- t1 is on the left, t3 is on the right
          pre.board[row1][col] = t1 and pre.board[row2][col] = t2 and pre.board[row3][col] = t3
          row1 < row2 and row2 < row3
          -- if the two on the far left are the same, comine them and put the 
          -- extra guy next to them,
          t1 = t2 => {
            post.board[0][col] = t1.sup and post.board[1][col] = t3 and no post.board[2][col] and no post.board[3][col]
          }
          -- If the left two arent equal, but the right two are, ...
          ((not t1 = t2) and t2 = t3) => {
            post.board[0][col] = t1 and post.board[1][col] = t3.sup and no post.board[2][col] and no post.board[3][col]
          }
          -- if none are equal, just push them all to the left
          ((not t1 = t2) and (not t2 = t3)) => {
             post.board[0][col] = t1 and post.board[1][col] = t2 and post.board[2][col] = t3 and no post.board[3][col]
          }
        }
      }
      #{row: Int | some pre.board[row][col]} = 4 =>{
        some row1, row2, row3, row4: Int, t1, t2, t3, t4: Tile | {
          -- coll one has t1, and so on...
          pre.board[row1][col] = t1 and pre.board[row2][col] = t2 and pre.board[row3][col] = t3 and pre.board[row4][col] = t4
          row1 < row2 and row2 < row3 and row3 < row4
          --if there are two matches in the row, combine both fo them on the left
          (t1 = t2 and t3 = t4) =>{
            post.board[0][col] = t1.sup and post.board[1][col] = t3.sup and no post.board[2][col] and no post.board[3][col]
          }
          -- If the left is a mathc, comine those two
          (t1 = t2 and (not t3 = t4)) =>{
            post.board[0][col] = t1.sup and post.board[1][col] = t3 and post.board[2][col] = t4 and no post.board[3][col]
          }
          -- if the middle is a match, combine the middle
          ((not t1 = t2) and t2 = t3) =>{
            post.board[0][col] = t1 and post.board[1][col] = t2.sup and post.board[2][col] = t4 and no post.board[3][col]
          }
          -- if the right is the only match, combine
          ((not t1 = t2) and (not t2 = t3) and (t3 = t4)) =>{
            post.board[0][col] = t1 and post.board[1][row] = t2 and post.board[2][row] = t3.sup and no post.board[3][row]
          }
          -- if there are no matches, then the row stays the same
          ((not t1 = t2) and (not t2 = t3) and (not t3=t4)) => {
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
       some row1, row2: Int, t1, t2: Tile |{
         -- t1 and t2 are disjoint
         pre.board[row1][col] = t1 and pre.board[row2][col2] = t2
         -- col1 is on the left of col 2
         row1 < row2
         -- if both squares are the same, the post row will only have their sup on the right
         t1 = t2 =>{
           post.board[3][col] = t1.sup and no post.board[1][col] and no post.board[2][col] and no post.board[0][col]
         }
         -- if they are both different, then the right most tile goes to the far right, and the second most goes to the next spot
         (not t1 = t2) =>{
           post.board[2][col] = t1 and post.board[3][col] = t2 and no post.board[0][col] and no post.board[1][col]
         }
       }
        
      }
      -- If there are 3 tiles in the row
      #{row: Int | some pre.board[row][col]} = 3 => {
        some row1, row2, row3: Int, t1, t2, t3: Tile | {
          -- t1 is on the left, t3 is on the right
          pre.board[row1][col] = t1 and pre.board[row2][col] = t2 and pre.board[row2][col] = t3
          row1 < row2 and row2 < row3
          -- if the two on the far left are the same, comine them and put the 
          -- extra guy next to them,
          t1 = t2 => {
            post.board[2][col] = t1.sup and post.board[3][col] = t3 and no post.board[0][col] and no post.board[1][col]
          }
          -- If the left two arent equal, but the right two are, ...
          ((not t1 = t2) and t2 = t3) => {
            post.board[2][col] = t1 and post.board[3][col] = t3.sup and no post.board[0][col] and no post.board[1][col]
          }
          -- if none are equal, just push them all to the right
          ((not t1 = t2) and (not t2 = t3)) => {
             post.board[1][col] = t1 and post.board[2][col] = t2 and post.board[3][col] = t3 and no post.board[0][col]
          }
        }
      }
      #{row: Int | some pre.board[row][col]} = 4 =>{
        some row1, row2, row3, row4: Int, t1, t2, t3, t4: Tile | {
          -- coll one has t1, and so on...
          pre.board[row1][col] = t1 and pre.board[row2][col] = t2 and pre.board[row2][col] = t3 and pre.board[row4][col] = t4
          row1 < row2 and row2 < row3 and row3 < row4
          --if there are two matches in the row, combine both of them on the right
          (t1 = t2 and t3 = t4) =>{
            post.board[2][col] = t1.sup and post.board[3][col] = t3.sup and no post.board[0][col] and no post.board[1][col]
          }
          -- If the left is a match, comine those two
          (t1 = t2 and (not t3 = t4)) =>{
            post.board[1][col] = t1.sup and post.board[2][col] = t3 and post.board[3][col] = t4 and no post.board[0][col]
          }
          -- if the middle is a match, combine the middle
          ((not t1 = t2) and t2 = t3) =>{
            post.board[1][col] = t1 and post.board[2][col] = t2.sup and post.board[3][col] = t4 and no post.board[0][col]
          }
          -- if the right is the only match, combine
          ((not t1 = t2) and (not t2 = t3) and (t3 = t4)) =>{
            post.board[1][col] = t1 and post.board[2][col] = t2 and post.board[3][col] = t3.sup and no post.board[0][col]
          }
          -- if there are no matches, then the row stays the same
          ((not t1 = t2) and (not t2 = t3) and (not t3=t4)) => {
            all row: Int | pre.board[row][col] = post.board[row][col]
          }
        }
      }
    }
  }
}

// pred trace