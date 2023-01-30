package AI;

import model.*;

import java.util.ArrayList;
import java.util.List;

/**
 * Implements the Strategy interface to define a Smart Strategy.
 */
public class SmartStrategy implements Strategy {
    private String name;


    public SmartStrategy() {
        this.name = "Smart Strategy";
    }
    public int heuristic(OthelloGame game, Player player){
        int ourScore = game.getScore(player);
        int opponetScore = game.getScore(game.getOppositePlayer());
        return (ourScore - opponetScore);
    }
    /**
     * Determines whether there is a move that instantly wins the game for the current player.
     * @param game The instance of TicTacToeGame which is being played
     * @return Move which wins the game, or null if no such move exists
     */
    @Override
    public OthelloMove determineMove(OthelloGame game){
        List<OthelloMove> validMove = game.getValidMoves();
        int bestMove = Integer.MIN_VALUE;
        OthelloMove bestmove = null;
        Player original = game.getTurn();
        Player opponent = game.getOppositePlayer();
        for(OthelloMove move : validMove){
            Game copyGame = game.deepCopy();
            copyGame.doMove(move);
            int val = minimaxValue((OthelloGame) copyGame, original, opponent,1);
            if(val > bestMove){
                bestMove = val;
                bestmove = move;
            }
        }
        return bestmove;
    }
    public int minimaxValue(OthelloGame game1,Player original, Player current, int depth){
        if((depth == 6) || game1.isGameOver()){
            return heuristic(game1, original);
        }
        Player opponent = game1.getOppositePlayer();
        List<OthelloMove> validMove = game1.getValidMoves();
        int numMoves = game1.getValidMoves().size();
        if(numMoves == 0){
            return minimaxValue(game1, original, opponent, depth + 1);
        }else {
            int bestMoveval = Integer.MIN_VALUE; // for finding max
            if (original != current) {
                bestMoveval = Integer.MAX_VALUE; // for fining min
            }
            for (OthelloMove move : validMove) {
                OthelloGame gamecopy = game1.deepCopy();
                gamecopy.doMove(move);
                int val = minimaxValue(gamecopy, original, opponent, depth + 1);
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
    public String getName() {
        return name;
    }




    /**
     * Determines which move should be played next by the Smart Strategy.
     * Uses the findWinningMove method and a deep copy of the game
     * to simulate playing moves for the AI and the player and determine
     * which move is best.
     * @param game The instance of TicTacToeGame that is being played
     * @return Move which wins the game instantly, move which stops enemy from winning
     * or random move if the former don't apply.
     */
}
