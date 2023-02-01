package Player.AI;

import Player.Human.Player;
import model.MainGame.Game;
import model.MainGame.OthelloGame;
import model.Move.Move;
import model.Move.OthelloMove;

import java.util.List;

/**
 * This class implements the Minimax AI for the Othello game.*
 * The Minimax algorithm is a decision-making algorithm that determines the best move for a player in a two-player game.
 * In the context of Othello, this AI will consider all possible moves for both players, and choose the move that leads to
 * the best outcome for the AI player.
 *
 **/
 public class SmartStrategy implements Strategy {
    private final String name;

    // Constructor for default bot
    public SmartStrategy() {
        this.name = "Smart Strategy";
    }

    // Constructor for a bot with a given name;
    public SmartStrategy(String name){
        this.name = name;
    }

    /**
     * To calculate the gap of score between this player and opponent
     * @param game the current Othello game
     * @param player the current player of this game
     * @return the gap between 2 players in this game
     */
    //@ requires game != null && player != null;
    //@ ensures \result instanceof Integer;
    public int heuristic(OthelloGame game, Player player){
        int ourScore = game.getScore(player);
        int opponetScore = game.getScore(game.getOppositePlayer());
        return (ourScore - opponetScore);
    }
    /**
     * Determines whether there is a bestMove base on calculate the score after 6 turns
     * @param game The instance of TicTacToeGame which is being played
     * @return Move which wins the game, or null if no such move exists
     */
    //@ requires game != null;
    //@ ensures \result instanceof Move;
    //@ ensures game.getValidMoves().size() != 0 ==> ((\forall Move move ; game.isValidMove(move) ; move.getMark() == game.getMark()));
    @Override
    public Move determineMove(Game game){
        List<Move> validMove = game.getValidMoves();
        if(validMove.size() == 0){
            return new OthelloMove(game.getMark(), 8, 0);
        }
        int bestMove = Integer.MIN_VALUE;
        Move bestmove = null;
        Player original = game.getTurn();
        Player opponent = game.getOppositePlayer();
        for(Move move : validMove){
            Game copyGame = game.deepCopy();
            copyGame.doMove(move);
            int val = minimaxValue((OthelloGame) copyGame, original,opponent,1);
            if(val > bestMove){
                bestMove = val;
                bestmove = move;
            }
        }
        return bestmove;
    }

    /**
     * Calculates the minimax value for the current state of the Othello game.*
     * The minimax value is an evaluation of the current state of the game, with the goal of finding the best move for the current player.
     * The value is calculated by considering all possible moves and evaluating the outcome of each move using the minimax algorithm.
     * The value returned is the best possible outcome for the current player.
     *
     * @param game1 The current state of the Othello game.
     * @param original The original player.
     * @param current The current player.
     * @param depth The current depth in the search tree.
     * @return The minimax value for the current state of the game.
     */
    /*@
       requires game1 != null && original != null && current != null && depth instanceof Integer;
       ensures \result instanceof Integer;
    */
    public int minimaxValue(OthelloGame game1,Player original, Player current, int depth){
        if((depth == 6) || game1.isGameOver()){
            return heuristic(game1, original);
        }
        Player opponent = game1.getOppositePlayer();
        List<Move> validMove = game1.getValidMoves();
        int numMoves = game1.getValidMoves().size();
        if(numMoves == 0){
            return minimaxValue(game1, original, opponent, depth + 1);
        }else {
            int bestMoveval = Integer.MIN_VALUE; // for finding max
            if (original != current) {
                bestMoveval = Integer.MAX_VALUE; // for finding min
            }
            for (Move move : validMove) {
                Game gamecopy = game1.deepCopy();
                gamecopy.doMove(move);
                int val = minimaxValue((OthelloGame) gamecopy, original, opponent, depth + 1);
                if (original == current) {
                    if (val > bestMoveval) {
                        bestMoveval = val;
                    }
                } else {
                    if (val < bestMoveval) {
                        bestMoveval = val;
                    }
                }
            }
            return bestMoveval;
        }
    }

    /**
     * Getter for the name of the strategy.
     * @return String name of strategy
     */
    //@ pure;
    @Override
    public String getName() {
        return name;
    }

}
