package model.MainGame;

import Player.Human.Player;
import model.Move.Move;

import java.util.List;
/**
 * A simple turn-based game.
 */
public interface Game {

    /**
     * Check if the game is over, i.e., there is a winner or no more moves are available.
     * @return whether the game is over
     */
    //@ ensures \result <==> getValidMoves().size() == 0;
    //@ ensures \result == false ==> getWinner() == null;
    //@ ensures \result <==> getTurn() != null;
    //@ pure;
    boolean isGameOver();

    /**
     * Query whose turn it is
     * @return the player whose turn it is
     */
    //@ pure;
    Player getTurn();

    /**
     * Get the winner of the game. If the game is a draw, then this method returns null.
     * @return the winner, or null if no player is the winner
     */
    //@ pure;
    Player getWinner();

    /**
     * Return all moves that are valid in the current state of the game
     *
     * @return the list of currently valid moves
     */
    //@ ensures (\forall Move m; \result.contains(m); isValidMove(m));
    //@ pure;
    List<Move> getValidMoves();

    /**
     * Check if a move is a valid move
     * @param move the move to check
     * @return true if the move is a valid move
     */
    //@ ensures \result <==> (\exists Move m; getValidMoves().contains(m); m.equals(move));
    //@ pure;
    boolean isValidMove(Move move);

    /**
     * Perform the move, assuming it is a valid move.
     * @param move the move to play
     */
    //@ requires isValidMove(move);
    void doMove(Move move);
    /**
     * get current mark of game
     * @return  a string of mark
     */
    //@ pure;
    String getMark();


    /**
     * get the opponent's mark;
     * @return the string of mark
     */
    //@ pure;
    String getOppositeMark();

    /**
     * indicate the second player in this game
     * @return player who is opponent of current player in this game
     */
    //@ ensures \result != getTurn();
    Player getOppositePlayer();

    /**
     * Create a deep copy of current game
     * @return a deep copy of board, player, current turn
     */

    Game deepCopy();
}
