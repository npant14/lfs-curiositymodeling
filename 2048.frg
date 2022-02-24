#lang forge/bsl “cm” “ANON ID”


// empty file for the game
// contents to be discussed

sig State {
  board: pfunc Int -> Int -> Tile
}

abstract sig Tile {}
one sig ONE, TWO, FOUR, EIGHT, SIXTEEN, THIRTYTWO, SIXTYFOUR, ONETWENTYEIGHT extends Player {}
one sig TWOFIFTYSIX, FIVETWELVE, TENTWENTYFOUR, TWENTYFOURTYEIGHT extends Player {}

// some sig for move direction perhaps?
abstract sig Direction {}
one sig LEFT RIGHT UP DOWN extends Direction {}


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

// transition, move, something.
// unclear what is necessary for this pred at this point in time.  
pred move [pre: State, post: State]{

}

// pred trace

// abstracting randomness somehow
//   -- finding shortest path/trace
// can play on a 3x3 board 
// solve until 512
// how compare with advertised human strategies (picking a corner)? 

// move pred with "preferred" directions 