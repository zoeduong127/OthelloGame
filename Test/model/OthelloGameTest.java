package model;

import Player.Human.Player;
import Player.Human.HumanPlayer;
import model.MainGame.Board;
import model.MainGame.OthelloGame;
import model.Move.Mark;
import model.Move.OthelloMove;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;
class OthelloGameTest {
    private OthelloGame game;
    private Player player1;
    private Player player2;
    private Board board;

    @BeforeEach
    void setUp() {
        board = new Board();
        player1 = new HumanPlayer("Huyen");
        player2 = new HumanPlayer("Bong");
        game = new OthelloGame(player1, player2,board);
    }


    /**
     * First case: Test with board is full of mark;
     * First case: Test with board is not full of mark but board does not have any validmovesboard.setField( i ,j, Mark.XX);;
     */

    @Test
    void isGameOver() {
        //Case1:
        for(int i = 0 ; i < board.DIM ; i ++){
            for(int j = 0; j < board.DIM; j ++){
                board.setField( i ,j, Mark.XX.getSymbol());
            }
        }
        assertTrue(game.isGameOver());
        //Case 2:
        board.reset();
        for( int i = 0; i < 7 ; i ++){
            for(int j = 0; j < 7; j++){
                board.setField( i ,j, Mark.XX.getSymbol());
            }
        }
        assertTrue(game.isGameOver());

    }


    /**
     * Test with the case having a winner with mark X;
     *
     */
    @Test
    void getWinner() {
        //Case 1:
        for(int i = 0 ; i < 7 ; i ++){
            for(int j = 0; j < 7; j ++){
                board.setField( i ,j, Mark.XX.getSymbol());
            }
        }
        assertEquals(game.getWinner(), player1);
    }

    /**
     * CHeck return the list of valid move . Check the size of this list
     */


    @Test
    void getValidMoves() {
        //Intial board game
        assertEquals(game.getValidMoves().size(), 4);

        //Set some mark for board and check again
        board.setField(4,5, Mark.XX.getSymbol());
        board.setField(3,5, Mark.OO.getSymbol());
        assertEquals(game.getValidMoves().size(),5);

        //Set nearly full of board with mark OO and check how many valid move with mark XX
        board.reset();
        for(int i = 0 ; i < 7 ; i ++) {
            for (int j = 0; j < 7; j++) {
                board.setField(i, j, Mark.OO.getSymbol());
            }
        }
        assertEquals(game.getValidMoves().size(), 0);
    }

    /**
     * Check the above direction of this move in intial time and after having some change on board
     */
    @Test
    void checkAbove() {
        //Initial time
        assertTrue(game.CheckAbove(new OthelloMove(Mark.XX.getSymbol(), 5,4)));
        // Change something on board
        board.setField(3,2, Mark.XX.getSymbol());
        board.setField(3,3, Mark.XX.getSymbol());
        board.setField(4,2, Mark.OO.getSymbol());
        board.setField(4,3, Mark.OO.getSymbol());
        // Check again
        for(int i = 2 ; i < 5; i ++) {
            assertTrue(game.CheckAbove(new OthelloMove(Mark.XX.getSymbol(), 5, i)));
        }

    }


    /**
     * Check the below direction of this move in intial time and after having some change on board
     */
    @Test
    void checkBelow() {
        //Initial time
        assertTrue(game.CheckBelow(new OthelloMove(Mark.XX.getSymbol(), 2, 3)));
        //Change something on board
        board.setField(3,2, Mark.XX.getSymbol());
        board.setField(2,2, Mark.OO.getSymbol());
        // Check again
        assertFalse(game.CheckBelow(new OthelloMove(Mark.XX.getSymbol(), 5,4)));
        assertTrue(game.CheckBelow(new OthelloMove(Mark.XX.getSymbol(), 1,2)));
        assertTrue(game.CheckBelow(new OthelloMove(Mark.XX.getSymbol(), 2,3)));


    }


    /**
     * Check the Left direction of this move in intial time and after having some change on board
     */
    @Test
    void checkLeft() {
        board.setField(3,2, Mark.XX.getSymbol());
        board.setField(2,2, Mark.OO.getSymbol());
        assertTrue(game.CheckLeft(new OthelloMove(Mark.XX.getSymbol(), 4,5)));
        assertFalse(game.CheckLeft(new OthelloMove(Mark.XX.getSymbol(), 1,2)));
        assertFalse(game.CheckLeft(new OthelloMove(Mark.XX.getSymbol(), 2,3)));

    }

    /**
     * Check the Right direction of this move in intial time and after having some change on board
     */

    @Test
    void checkRight() {
        assertTrue(game.CheckRight(new OthelloMove(Mark.XX.getSymbol(), 3,2)));
        board.setField(3,2, Mark.XX.getSymbol());
        board.setField(2,2, Mark.OO.getSymbol());
        assertFalse(game.CheckRight(new OthelloMove(Mark.XX.getSymbol(), 4,5)));
        assertFalse(game.CheckRight(new OthelloMove(Mark.XX.getSymbol(), 1,2)));
        assertFalse(game.CheckRight(new OthelloMove(Mark.XX.getSymbol(), 2,3)));

    }

    /**
     * Check the Right-above direction of this move in intial time and after having some change on board
     */
    @Test
    void checkRightAbove() {
        // Initial time
        for(int i = 0 ; i < board.DIM ; i ++) {
            for (int j = 0; j < board.DIM; j++) {
                assertFalse(game.CheckRightAbove(new OthelloMove(Mark.XX.getSymbol(), i, j)));
            }
        }
        // Afterthat
        board.setField(4,3, Mark.OO.getSymbol());
        assertTrue(game.CheckRightAbove(new OthelloMove(Mark.OO.getSymbol(),5,2)));
    }

    /**
     * Check the right-below direction of this move in intial time and after having some change on board
     */
    @Test
    void checkRightBelow() {
        //Initial time
        for(int i = 0 ; i < board.DIM ; i ++) {
            for (int j = 0; j < board.DIM; j++) {
                assertFalse(game.CheckRightBelow(new OthelloMove(Mark.XX.getSymbol(), i, j)));
            }
        }
        //Afterthat
        board.setField(3,4, Mark.OO.getSymbol());
        board.setField(3,5 , Mark.OO.getSymbol());
        board.setField(4,4, Mark.XX.getSymbol());
        board.setField(4,5, Mark.XX.getSymbol());
        assertTrue(game.CheckRightBelow(new OthelloMove(Mark.XX.getSymbol(), 2,3)));
        assertTrue(game.CheckRightBelow(new OthelloMove(Mark.XX.getSymbol(), 2,2)));

    }

    /**
     * Check the Left-below direction of this move in intial time and after having some change on board
     */
    @Test
    void checkLeftBelow() {
        //Initital time
        for(int i = 0 ; i < board.DIM ; i ++) {
            for (int j = 0; j < board.DIM; j++) {
                assertFalse(game.CheckLeftBelow(new OthelloMove(Mark.XX.getSymbol(), i, j)));
            }
        }
        //Afterthat
        board.setField(3,4, Mark.OO.getSymbol());
        board.setField(3,5 , Mark.OO.getSymbol());
        board.setField(4,4, Mark.XX.getSymbol());
        board.setField(4,5, Mark.XX.getSymbol());
        assertTrue(game.CheckLeftBelow(new OthelloMove(Mark.XX.getSymbol(), 2,5)));
        assertTrue(game.CheckLeftBelow(new OthelloMove(Mark.XX.getSymbol(), 2,6)));

    }
    /**
     * Check the Left-above direction of this move in intial time and after having some change on board
     */
    @Test
    void checkLeftAbove() {
        for(int i = 0 ; i < board.DIM ; i ++) {
            for (int j = 0; j < board.DIM; j++) {
                assertFalse(game.CheckLeftAbove(new OthelloMove(Mark.XX.getSymbol(), i, j)));
            }
        }
        board.setField(3,4, Mark.OO.getSymbol());
        board.setField(3,5 , Mark.OO.getSymbol());
        board.setField(4,4, Mark.XX.getSymbol());
        board.setField(4,5, Mark.XX.getSymbol());
        assertFalse(game.CheckLeftAbove(new OthelloMove(Mark.XX.getSymbol(), 2,5)));
        assertFalse(game.CheckLeftAbove(new OthelloMove(Mark.XX.getSymbol(), 2,6)));
    }


    /**
     * Check isvalidmove method check inital validmove with mark X
     * The expected results is 4;
     */
    @Test
    void isValidMove() {
        assertTrue(game.isValidMove(new OthelloMove(Mark.XX.getSymbol(), 2,3)));
        assertTrue(game.isValidMove(new OthelloMove(Mark.XX.getSymbol(), 3,2)));
        assertTrue(game.isValidMove(new OthelloMove(Mark.XX.getSymbol(), 4,5)));
        assertTrue(game.isValidMove(new OthelloMove(Mark.XX.getSymbol(), 5,4)));
    }
    /**
     * Check the board is not full of Mark but there is not validmode so the game is over.
     */
    @Test
    void doMovenofull() {
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 2,3));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 2,2));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 4,5));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 3,5));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 2,5));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 1,3));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 0,3));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 2,4));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 2,1));
        assertTrue(game.isGameOver());
        assertEquals(game.getWinner(), player1);
    }

    /**
     * Check the board is full and find winner by comparing the score.
     */
    @Test
    void doMovefull(){
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 4,5));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 3,5));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 2,5));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 5,3));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 2,2));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 2,3));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 2,4));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 3,6));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 4,2));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 5,6));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 4,7));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 3,7));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 6,7));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 1,4));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 0,3));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 3,2));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 6,4));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 5,1));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 4,6));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 1,2));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 0,1));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 0,5));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 1,1));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 5,4));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 5,5));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 2,6));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 2,7));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 0,2));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 2,1));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 7,4));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 7,3));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 1,7));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 3,1));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 1,0));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 0,4));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 7,2));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 0,7));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 5,2));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 3,0));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 1,6));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 6,0));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 2,0));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 6,3));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 5,7));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 6,5));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 0,0));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 1,5));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 7,7));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 6,1));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 6,6));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 7,6));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 5,0));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 4,1));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 7,5));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 7,0));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 7,1));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 6,2));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 0,6));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 4,0));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 1,3));
        assertTrue(game.isGameOver());
        assertEquals(game.getWinner(), player2);
        assertEquals(game.getScore(player1), 26);
    }
    @Test
    void doMovefull1(){
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 2,3));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 2,4));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 1,5));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 2,2));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 5,4));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 5,3));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 6,2));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 0,6));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 1,1));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 1,3));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 5,2));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 0,0));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 0,3));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 0,4));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 0,5));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 6,3));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 0,7));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 6,1));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 7,0));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 6,0));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 7,1));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 4,5));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 6,5));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 5,5));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 5,6));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 6,7));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 5,0));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 7,5));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 7,6));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 4,2));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 5,7));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 4,1));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 7,7));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 6,4));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 7,3));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 1,2));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 1,0));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 0,1));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 4,0));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 5,1));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 7,2));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 3,2));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 3,1));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 2,1));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 2,0));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 6,6));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 3,0));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 1,4));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 1,6));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 4,6));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 4,7));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 3,7));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 7,4));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 3,5));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 2,5));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 3,6));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 2,6));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(), 2,7));
        game.doMove(new OthelloMove(Mark.XX.getSymbol(), 1,7));
        game.doMove(new OthelloMove(Mark.OO.getSymbol(),0,2));
        assertTrue(game.isGameOver());
        assertEquals(game.getWinner(), player1);
        assertEquals(game.getScore(player1), 51);
        assertEquals(game.getScore(player2), 13);
    }

}