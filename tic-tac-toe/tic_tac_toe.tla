\* Ideas were taken from these other examples of tic-tac-toe in TLA+:
\* https://groups.google.com/g/tlaplus/c/rSmABu1YTw4/m/SrICRC12AAAJ
\* https://pron.github.io/files/TicTacToe.pdf

---- MODULE tic_tac_toe ----
EXTENDS TLC, Sequences, Integers, FiniteSets
VARIABLES board, currentPlayer

vars == <<board, currentPlayer>>

winningPositions == {
  {1, 2, 3}, {1, 4, 7}, {1, 5, 9}, {2, 5, 8},
  {3, 5, 7}, {3, 6, 9}, {4, 5, 6}, {7, 8, 9}
}
Free == "_"
CenterPosition == 5
CornerPositions == {1, 3, 7, 9}
DumbPlayer == "X"
SmartPlayer == "O"
NoOne == "No one"
StartingPlayer == "X"

Other(player) == IF player = "X" THEN "O" ELSE "X"
NonEmpty(s) == Cardinality(s) > 0
FreePositions == {p \in DOMAIN board : board[p] = Free}
GetPositions(player) == {p \in DOMAIN board : board[p] = player}
PlayerWon(player) == \E wp \in winningPositions : wp \subseteq GetPositions(player)
Winner == IF PlayerWon("X") THEN "X"
          ELSE IF PlayerWon("O") THEN "O"
          ELSE NoOne
BoardFull == Cardinality(FreePositions) = 0
GameEnded == BoardFull \/ PlayerWon("X") \/ PlayerWon("O")
IsWinningPosition(player, position) == \E wp \in winningPositions: wp \subseteq GetPositions(player) \union {position}
IsBlockingOpponentWin(player, position) == IsWinningPosition(Other(player), position)
ExecuteMove(player, position) == board' = [board EXCEPT ![position] = player]

RandomMove(player) ==
  /\ \E position \in DOMAIN board :
    /\ board[position] = Free
    /\ ExecuteMove(player, position)

SmartMove(player) ==
  LET winning == {p \in FreePositions: IsWinningPosition(player, p)} IN
  LET blocking == {p \in FreePositions: IsBlockingOpponentWin(player, p)} IN
  LET freeCorners == FreePositions \intersect CornerPositions IN
    IF NonEmpty(winning) THEN
      \E p \in winning: ExecuteMove(player, p)
    ELSE IF NonEmpty(blocking) THEN
      \E p \in blocking: ExecuteMove(player, p)
    ELSE IF CenterPosition \in FreePositions THEN
      ExecuteMove(player, CenterPosition)
    ELSE IF NonEmpty(freeCorners) THEN
      /\ \E p \in freeCorners: ExecuteMove(player, p)
    ELSE
      \E p \in FreePositions:  ExecuteMove(player, p)

Init ==
  /\ board = [i \in 1..9 |-> Free]
  /\ currentPlayer = StartingPlayer

Next ==
  \/ ~GameEnded
    /\
      \/ currentPlayer = DumbPlayer
        /\ RandomMove(currentPlayer)
      \/ currentPlayer = SmartPlayer
        /\ SmartMove(currentPlayer)
    /\ currentPlayer' = Other(currentPlayer)
  \/ GameEnded
    /\ PrintT(Winner \o " won!")
    /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars


Range(f) == {f[x] : x \in DOMAIN f}
TypeOK ==
  /\ Range(board) \subseteq  {"X", "O", "_"}
  /\ Cardinality(GetPositions("X")) <= 5
  /\ Cardinality(GetPositions("O")) <= 5
  /\ Cardinality(GetPositions("_")) <= 9

OnlyOneWinner ==
  /\ PlayerWon("X") => ~PlayerWon("O")
  /\ PlayerWon("O") => ~PlayerWon("X")
  /\ Winner = NoOne <=> ~PlayerWon("O") /\ ~PlayerWon("X")

BalancedTurns ==
  LET TurnsStartingPlayer == Cardinality(GetPositions(StartingPlayer)) IN
  LET TurnsOtherPlayer == Cardinality(GetPositions(Other(StartingPlayer))) IN
    \/ (TurnsStartingPlayer = TurnsOtherPlayer)
    \/ (TurnsStartingPlayer = TurnsOtherPlayer + 1)

\* The smart player is not smart enough :-)
DumbPlayerDoesNotWin == PlayerWon(DumbPlayer) = FALSE

boardDisplay == [i \in 0..2 |-> SubSeq(board, (i*3)+1, (i*3)+3)]
Alias == [
  row1 |-> boardDisplay[0],
  row2 |-> boardDisplay[1],
  row3 |-> boardDisplay[2],
  X_has_won |-> PlayerWon("X")
]
====
