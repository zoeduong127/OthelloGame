package model;

import UI.HumanPlayer;

import java.util.ArrayList;
import java.util.List;

public class OthelloGame implements Game{
    private Board board;
    public  Player player1;
    public  Player player2;
    public  String currentMark;
    public int turn;
    public OthelloGame(Player player1,Player player2, Board board) {
        this.player1 = player1;
        this.player2 = player2;
        this.board = board;
        currentMark = Mark.XX.getSymbol();
    }

    public OthelloGame(Player player1,Player player2, Board board, int turn ) {
        this.player1 = player1;
        this.player2 = player2;
        this.board = board;
        this.turn = turn;
    }



    /**
     * Returns the state of the game.
     * @return true if the game is over
     */
    /*@
    requires board != null && getValidMoves() != null;
    ensures (\result == true) ==> (board.isFull() || getValidMoves().size() == 0);
    ensures (\result == false) ==> (board.isFull() == false && getValidMoves().size() != 0);
    */
    public boolean isGameOver() {
        return board.isFull() || getValidMoves().size() == 0;
    }

    /**
     * According to the current mark to be played,
     * it returns the player that plays next
     * @return the player that plays next
     */
    /*@ requires player1 != null && player2 != null;
        ensures (\result == player1) <==> (currentMark.equals(Mark.XX.getSymbol()));
        ensures (\result == player2) <==> (currentMark.equals(Mark.OO.getSymbol()));
    */
    public Player getTurn() {
        if (turn % 2 == 0 ) {
            return player1;
        } else {
            return player2;
        }
    }

    /**
     * Returns the game's winner if it has one.
     * @return the winning player, null if it was a draw
     */
    /*@ requires player1 != null && player2 != null;
        ensures(\result == player1) <==> (isGameOver() == true && getScore(player1) > getScore(player2));
        ensures(\result == player2) <==> (isGameOver() == true && getScore(player1) <= getScore(player2));
        ensures(\result == null) <==> (isGameOver() == false);
    */
    public Player getWinner() {
        if (isGameOver()) {
            if (this.getScore(player1) > this.getScore(player2)){
                return player1;
            } else {
                return player2;
            }
        }
        return null;
    }

    /**
     * Return the score of  given player base on couting the number of mark
     * @param player
     * @return the score of this player
     */
    /*@ requires player != null && board != null;
      ensures (\result >= 0) && (\result <= (Board.DIM * Board.DIM));
    */

    public int getScore(Player player){
        int score = 0;
        for(int i = 0; i < Board.DIM; i ++){
            for(int j = 0; j <Board.DIM; j ++){
                if(player.equals(player1)){
                    if(board.getField(i,j).equals(Mark.XX.getSymbol())){
                        score +=1;
                    }
                }else{
                    if(board.getField(i,j).equals(Mark.OO.getSymbol())) {
                        score += 1;
                    }
                }
            }
        }return score;
    }

    /**
     * Returns a list of valid moves that haven't been played.
     *
     * @return a list of moves that can be played
     */
    /*@
      requires board != null && player1 != null & player2 != null;
      ensures  (\forall int i; 0 <= i  && i < (\result.size()); isValidMove(\result.get(i)) == true);
    */

    public List<OthelloMove> getValidMoves() {
        List<OthelloMove> validMoves = new ArrayList<>();
        for (int i = 0; i < Board.DIM; i++) {
            for (int j = 0; j < Board.DIM; j++) {
                if (board.isEmptyField(i, j)) {
                    if (getTurn().equals(player1)){
                        OthelloMove move =new OthelloMove(Mark.XX.getSymbol(),i,j);
                        if(this.isValidMove(move)){
                            validMoves.add(move);
                        }
                    } else {
                        OthelloMove move = new OthelloMove(Mark.OO.getSymbol(),i,j);
                        if(this.isValidMove(move)){
                            validMoves.add(move);
                        }
                    }
                }
            }
        }
        return validMoves;
    }

    /**
     *
     * Scan all above points of this move to check whener the above direction is valid direction or not;
     * It will check the nearest first . If it is different mark , continue check the next point in the same direction until find a point which has same mark = > valid move
     *
     * @param move the move to check
     * @return true if the move is valid, false otherwise
     */
    /*@ requires  move != null && board != null;
        ensures (\result == true) <==> (\exists int i; 0  <= i  && i < move.getRow() -1 ; !board.getField(i, move.getCol()).equals(getMark()));
        ensures (\result == false) <==> (\forall int i; 0  <= i && i  < move.getRow() - 1; board.getField(i, move.getCol()).equals(getOppositeMark()));
    */

    public boolean CheckAbove(OthelloMove move){
        if(move.getRow() > 0){
            if(board.getField(move.getRow() - 1, move.getCol()).equals(getOppositeMark())){
                for(int i = move.getRow()-1 ; i >= 0 ; i -- ){
                    if(board.getField(i, move.getCol()).equals(getOppositeMark())) {
                        continue;
                    } else if(board.getField(i, move.getCol()).equals(Mark.EMPTY.getSymbol())){
                        return false;
                    }else if(board.getField(i, move.getCol()).equals(getMark())){
                        return true;
                    }
                }
            }return false;
        } return false;
    }
    /**
     *
     * Scan all below points of this move to check whenever the below direction is valid direction or not;
     *
     * @param move the move to check
     * @return true if the move is valid, false otherwise
     */
    /*@ requires  move != null && board != null;
        ensures (\result == true) <==> (\exists int i; i < Board.DIM && i > move.getRow() +1 ; board.getField(i, move.getCol()) == getMark());
        ensures (\result == false) <==> (\forall int i; i < Board.DIM && i > move.getRow() +1 ; board.getField(i, move.getCol()).equals(getOppositeMark()));
    */
    public boolean CheckBelow(OthelloMove move){
        if(move.getRow() < Board.DIM - 1) {
            if (board.getField(move.getRow() + 1, move.getCol()).equals(getOppositeMark())) {
                for (int i = move.getRow() + 1; i < Board.DIM; i++) {
                    if (board.getField(i, move.getCol()).equals(getOppositeMark())) {
                        continue;
                    } else if(board.getField(i, move.getCol()).equals(Mark.EMPTY.getSymbol())){
                        return false;
                    } else if (board.getField(i, move.getCol()).equals(getMark())) {
                        return true;
                    }
                }
            }return false;
        }return false;

    }

    /**
     *
     * Scan all left points of this move to check whenever the left direction is valid direction or not;
     *
     * @param move the move to check
     * @return true if the move is valid, false otherwise
     */
    /*@ requires  move != null && board != null;
        ensures (\result == true) <==> (\exists int i; 0 <= i  && i < move.getCol() -1 ; board.getField(i, move.getCol()) == getMark());
        ensures (\result == false) <==> (\forall int i; 0 <= i  && i < move.getCol() -1 ; board.getField(i, move.getCol()).equals(getOppositeMark()));
    */

    public boolean CheckLeft(OthelloMove move) {
        if(move.getCol() > 0) {
            if (board.getField(move.getRow(), move.getCol() - 1).equals(getOppositeMark())) {
                for (int i = move.getCol() - 1; 0 <= i; i--) {
                    if (board.getField(move.getRow(), i).equals(getOppositeMark())) {
                        continue;
                    }else if (board.getField(move.getRow(), i).equals(Mark.EMPTY.getSymbol())){
                        return false;
                    } else if (board.getField(move.getRow(), i).equals(getMark())) {
                        return true;
                    }
                }
            }return false;
        }return false;
    }


    /**
     * Scan all right points of this move to check whenever the right direction is valid direction or not;
     * @param move the move to check
     * @return true if the move is valid, false otherwise
     */
    /*@ requires  move != null && board != null;
        ensures (\result == true) <==> (\exists int i; Board.DIM <= i  && i > move.getCol() +1 ; board.getField(i, move.getCol()) == getMark());
        ensures (\result == false) <==> (\forall int i; Board.DIM<= i  && i > move.getCol() +1 ; board.getField(i, move.getCol()).equals(getOppositeMark()));
    */
    public boolean CheckRight(OthelloMove move) {
        if(move.getCol() < Board.DIM -1) {
            if (board.getField(move.getRow(), move.getCol() + 1).equals(getOppositeMark())) {
                for (int i = move.getCol() + 1; i < Board.DIM; i++) {
                    if (board.getField(move.getRow(), i).equals(getOppositeMark())) {
                        continue;
                    }else if(board.getField(move.getRow(), i).equals(Mark.EMPTY.getSymbol())){
                        return false;
                    } else if (board.getField(move.getRow(), i).equals(getMark())) {
                        return true;
                    }
                }
            }return false;
        }
        return false;
    }

    /**
     * Scan all right-above points of this move to check whenever the right-above direction is valid direction or not;
     * @param move the move to check
     * @return true if the move is valid, false otherwise
     */
    /*@ requires move != null && board != null;
        ensures (\result == true) <==> (\exists int i, j; move.getRow() -1 > j && j >= 0 && board.DIM > i && move.getCol()+ 1 <  i ; board.getField(j, i) == getMark());
        ensures (\result == false) <==> (\forall int i, j; move.getRow() -1 > j && j >= 0 && board.DIM > i && move.getCol()+ 1 <  i; board.getField(j, i).equals(getOppositeMark()));
    */
    public boolean CheckRightAbove(OthelloMove move) {
        if(move.getCol() < Board.DIM -1 && move.getRow() > 0) {
            if (board.getField(move.getRow() - 1, move.getCol() + 1).equals(getOppositeMark())) {
                int j = move.getRow() - 1;
                for (int i = move.getCol() + 1; i < Board.DIM; i++) {
                    if(0 <= j) {
                        if (board.getField(j, i).equals(getOppositeMark())) {
                            j -=1;
                            continue;
                        }else if(board.getField(j, i).equals(Mark.EMPTY.getSymbol())){
                            return false;
                        } else if (board.getField(j, i).equals(getMark())) {
                            return true;
                        }
                    }else{return false;}

                }
            }return false;
        }
        return false;
    }

    /**
     * Scan all right-below points of this move to check whenever the right-below direction is valid direction or not;
     * @param move the move to check
     * @return true if the move is valid, false otherwise
     */
    /*@ requires move != null && board != null;
        ensures (\result == true) <==> (\exists int i, j; move.getRow() -1 > j && j >= 0 && board.DIM > i && move.getCol()+ 1 <  i ; board.getField(j, i) == getMark());
        ensures (\result == false) <==> (\forall int i, j; move.getRow() -1 > j && j >= 0 && board.DIM > i && move.getCol()+ 1 <  i; board.getField(j, i).equals(getOppositeMark()));
    */
    public boolean CheckRightBelow(OthelloMove move) {
        if(move.getRow() < Board.DIM -1 && move.getCol() < Board.DIM -1) {
            if (board.getField(move.getRow() + 1, move.getCol() + 1).equals(getOppositeMark())) {
                int j = move.getCol() + 1;
                for (int i = move.getRow() + 1; i < Board.DIM; i++) {
                    if(j < Board.DIM) {
                        if (board.getField(i, j).equals(getOppositeMark())) {
                            j +=1;
                            continue;
                        } else if(board.getField(i, j).equals(Mark.EMPTY.getSymbol())){
                            return false;
                        } else if (board.getField(i, j).equals(getMark())) {
                            return true;
                        }
                    }else{return false;}
                }
            }return false;
        }return false;
    }

    /**
     * Scan all left-below points of this move to check whenever the left-below direction is valid direction or not;
     * @param move the move to check
     * @return true if the move is valid, false otherwise
     */
    /*@ requires move != null && board != null;
        ensures (\result == true) <==> (\exists int i, j; move.getCol() -1 > j && j >= 0 && board.DIM > i && move.getRow()+ 1 <  i ; board.getField(j, i) == getMark());
        ensures (\result == false) <==> (\forall int i, j; move.getCol() -1 > j && j >= 0 && board.DIM > i && move.getRow()+ 1 <  i; board.getField(j, i).equals(getOppositeMark()));
    */
    public boolean CheckLeftBelow (OthelloMove move){
        if(move.getRow() < Board.DIM -1 && move.getCol() > 0) {
            if (board.getField(move.getRow() + 1, move.getCol() - 1).equals(getOppositeMark())) {
                int j = move.getCol() - 1;
                for (int i = move.getRow() + 1; i < Board.DIM; i++) {
                    if(0 <= j) {
                        if (board.getField(i, j).equals(getOppositeMark())) {
                            j -=1;
                            continue;
                        } else if(board.getField(i, j).equals(Mark.EMPTY.getSymbol())){
                            return false;
                        } else if (board.getField(i, j).equals(getMark())) {
                            return true;
                        }
                    }else{return false;}

                }
            }return false;
        }return false;
    }
    /**
     * Scan all left-above points of this move to check whenever the left-above direction is valid direction or not;
     * @param move the move to check
     * @return true if the move is valid, false otherwise
     */
    /*@ requires move != null && board != null;
        ensures (\result == true) <==> (\exists int i, j; move.getCol() -1 > j && j >= 0 && move.getRow()-1 > i && 0 <= i ; board.getField(j, i) == getMark());
        ensures (\result == false) <==> (\forall int i, j; move.getCol() -1 > j && j >= 0 && move.getRow()-1 > i && 0 <= i ; board.getField(j, i).equals(getOppositeMark()));
    */

    public boolean CheckLeftAbove (OthelloMove move){
        if(move.getRow() > 0 && move.getCol() > 0) {
            if (board.getField(move.getRow() - 1, move.getCol() - 1).equals(getOppositeMark())) {
                int j = move.getCol() - 1;
                for (int i = move.getRow() - 1; 0 <= i; i--) {
                    if(0 <= j) {
                        if (board.getField(i, j).equals(getOppositeMark())) {
                            j -=1;
                            continue;
                        }else if(board.getField(i, j).equals(Mark.EMPTY.getSymbol())){
                            return false;
                        } else if (board.getField(i, j).equals(getMark())) {
                            return true;
                        }
                    }else{return false;}
                }

            }return false;
        }return false;
    }


    /**
     * Determines if a move is valid or not. If one of direction is true = > valid move.
     * @param move the move to check
     * @return true if the move is valid
     */
    /*@ requires move != null;
        ensures  (\result == true) <==> (CheckAbove(move) || CheckBelow(move) || CheckLeft(move) || CheckRight(move) || CheckLeftAbove(move) || CheckLeftBelow(move) || CheckRightAbove(move) || CheckRightBelow(move));
        ensures (\result == false) <==> (!CheckAbove(move) && !CheckBelow(move) && !CheckLeft(move) && !CheckRight(move) && !CheckLeftAbove(move) && !CheckLeftBelow(move) && !CheckRightAbove(move) && !CheckRightBelow(move));
    */
    @Override
    public boolean isValidMove(OthelloMove move) {
        if(board.isField(move.getRow(), move.getCol())) {
            if (this.CheckAbove(move)) {
                return true;
            } else if (this.CheckBelow(move)) {
                return true;
            } else if (this.CheckLeft(move)) {
                return true;
            } else if (this.CheckRight(move)) {
                return true;
            } else if (this.CheckLeftAbove(move)) {
                return true;
            } else if (this.CheckLeftBelow(move)) {
                return true;
            } else if (this.CheckRightAbove(move)) {
                return true;
            } else return this.CheckRightBelow(move);
        }
        return false;
    }

    /**
     * This method does the passed move
     * and switches the current mark to be played
     * @param move the move to play
     */

    /*@
      requires  move != null && board != null;
      ensures    ((CheckAbove(move) ==> (\exists int i; 0 <= i  && i < move.getCol() -1 ; board.getField(i, move.getCol()) == getMark())) &&
                 (CheckBelow(move) ==> (\exists int i; i < Board.DIM && i > move.getRow() +1 ; board.getField(i, move.getCol()) == getMark())) &&
                 (CheckLeft(move) ==> ((\exists int i; 0 <= i  && i < move.getCol() -1 ; board.getField(i, move.getCol()) == getMark()))) &&
                 (CheckRight(move) ==> (\exists int i; Board.DIM <= i  && i > move.getCol() +1 ; board.getField(i, move.getCol()) == getMark())) &&
                 (CheckRightAbove(move) ==> (\exists int i, j; move.getRow() -1 > j && j >= 0 && board.DIM > i && move.getCol()+ 1 <  i ; board.getField(j, i) == getMark())) &&
                 (CheckRightBelow(move) ==> (\exists int i, j; move.getRow() -1 > j && j >= 0 && board.DIM > i && move.getCol()+ 1 <  i ; board.getField(j, i) == getMark())) &&
                 (CheckLeftBelow(move) ==> (\exists int i, j; move.getCol() -1 > j && j >= 0 && move.getRow()-1 > i && 0 <= i ; board.getField(j, i) == getMark())) &&
                 (CheckLeftAbove(move) ==> (\exists int i, j; move.getCol() -1 > j && j >= 0 && move.getRow()-1 > i && 0 <= i ; board.getField(j, i) == getMark())));
    */

    @Override
    public void doMove(OthelloMove move) {
        //Flip all valid mark if above direction is possible
        if (this.CheckAbove(move)) {board.setField(move.getRow(), move.getCol(), getMark());
            for (int i = move.getRow() - 1; i >= 0; i--) {
                if (board.getField(i, move.getCol()).equals(getOppositeMark())) {
                    board.setField(i, move.getCol(), getMark());
                } else {break;}
            }
        }
        //Flip all valid mark if below direction is possible
        if (this.CheckBelow(move)) {board.setField(move.getRow(), move.getCol(), getMark());
            for (int i = move.getRow() + 1; i < Board.DIM; i++) {
                if (board.getField(i, move.getCol()).equals(getOppositeMark())) {
                    board.setField(i, move.getCol(), getMark());
                } else {break;}
            }
        }
        //Flip all valid mark if left direction is possible
        if (this.CheckLeft(move)) {board.setField(move.getRow(), move.getCol(), getMark());
            for (int i = move.getCol() - 1; 0 <= i; i--) {
                if (board.getField(move.getRow(), i).equals(getOppositeMark())) {
                    board.setField(move.getRow(), i, getMark());
                } else {break;}
            }
        }
        //Flip all valid mark if right direction is possible
        if (this.CheckRight(move)) {board.setField(move.getRow(), move.getCol(), getMark());
            for (int i = move.getCol() + 1; i < Board.DIM; i++) {
                if (board.getField(move.getRow(), i).equals(getOppositeMark())) {
                    board.setField(move.getRow(), i, getMark());
                } else {break;}
            }
        }
        //Flip all valid mark if right-above direction is possible
        if (this.CheckRightAbove(move)) {board.setField(move.getRow(), move.getCol(), getMark());
            int j = move.getRow() - 1;
            for (int i = move.getCol() + 1; i < Board.DIM; i++) {
                if (0 <= j) {
                    if (board.getField(j, i).equals(getOppositeMark())) {
                        board.setField(j, i, getMark());
                        j -= 1;
                    } else {break;}
                }
            }
        }
        //Flip all valid mark if right-below direction is possible
        if (this.CheckRightBelow(move)) {board.setField(move.getRow(), move.getCol(), getMark());
            int j = move.getCol() + 1;
            for (int i = move.getRow() + 1; i < Board.DIM; i++) {
                if (j < Board.DIM) {
                    if (board.getField(i, j).equals(getOppositeMark())) {
                        board.setField(i, j, getMark());
                        j += 1;
                    } else {break;}
                }
            }
        }

        //Flip all valid mark if left-below direction is possible
        if (this.CheckLeftBelow(move)) {board.setField(move.getRow(), move.getCol(), getMark());
            int j = move.getCol() - 1;
            for (int i = move.getRow() + 1; i < Board.DIM; i++) {
                if (0 <= j) {
                    if (board.getField(i, j).equals(getOppositeMark())) {
                        board.setField(i, j, getMark());
                        j -= 1;
                    } else {break;}
                }
            }
        }

        //Flip all valid mark if left-above direction is possible
        if(this.CheckLeftAbove(move)){board.setField(move.getRow(),move.getCol(), getMark());int j = move.getCol() - 1;
            for (int i = move.getRow() - 1; 0<= i; i--) {
                if (0 <=j ){
                    if (board.getField(i, j).equals(getOppositeMark())) {
                        board.setField(i,j, getMark());
                        j -=1;
                    }else{break;}
                }
            }
        }
        turn +=1;
    }

    /**
     * Returns the mark to be played
     * @return the mark that should be played next
     */

    /*@
       requires player1 != null && player2 != null;
       ensures ( \result == Mark.XX.getSymbol()) <==> (getTurn()== player1);
       ensures ( \result == Mark.OO.getSymbol()) <==> (getTurn()== player2);
    */
    public String getMark() {
        if(getTurn().equals(player1)) {
            return Mark.XX.getSymbol();
        }else{
            return Mark.OO.getSymbol();
        }
    }
    public String getOppositeMark(){
        if(getMark().equals(Mark.XX.getSymbol())){
            return Mark.OO.getSymbol();
        }else{
            return Mark.XX.getSymbol();
        }
    }
    public Player getOppositePlayer(){
        if(getTurn() == player1){
            return  player2;
        }else{
            return player2;
        }
    }

    /**
     * Create a copy of current game
     *
     * @return copy of game
     */
    public OthelloGame deepCopy() {
        return new OthelloGame(player1, player2, board.deepCopy(), turn);
    }

    /**
     * Returns a String representation of this board. In addition to the current
     * situation, the String also shows the numbering of the fields.
     * @return the game situation as String
     */
    public String toString() {
        return board.toString();
    }
    public static void main (String[] arg){
        HumanPlayer  player1 = new HumanPlayer("a");
        HumanPlayer  player2 = new HumanPlayer("b");
        OthelloGame board = new OthelloGame(player1,player2, new Board());
        OthelloGame board1 = board.deepCopy();
        board1.doMove(new OthelloMove(Mark.XX.getSymbol(), 3,2));
        System.out.println(board);
        System.out.println(board1);
    }


}
