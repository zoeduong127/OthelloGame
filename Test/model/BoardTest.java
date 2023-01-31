package model;

import model.MainGame.Board;
import model.Move.Mark;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class BoardTest {
    private Board board;

    @BeforeEach
    public void setUp() {
        board = new Board();
    }


    @Test
    void isField() {
        assertFalse(board.isField(-1,-2));
        for (int i = 0; i < board.DIM; i++) {
            for (int j = 0; j < board.DIM; j++) {
                assertTrue(board.isField(i, j));
            }
        }
    }

    @Test
    void getField() {
        assertEquals(board.getField(3,3), Mark.OO.getSymbol());
        assertEquals(board.getField(3,4), Mark.XX.getSymbol());
        assertEquals(board.getField(4,3), Mark.XX.getSymbol());
        assertEquals(board.getField(4,4), Mark.OO.getSymbol());
    }

    @Test
    void isEmptyField() {
        for (int i = 0; i < 2; i++) {
            for (int j = 0; j < 2; j++) {
                assertTrue(board.isEmptyField(i, j));
            }
        }
    }

    @Test
    void setField() {
        for (int i = 0; i < 2; i++) {
            for (int j = 0; j < 2; j++) {
                board.setField(i, j , Mark.XX.getSymbol());
                assertFalse(board.isEmptyField(i, j));
                assertEquals(board.getField(i , j), Mark.XX.getSymbol());
            }
        }
    }

    @Test
    void isFull() {
        for (int i = 0; i < board.DIM; i++) {
            for (int j = 0; j < Board.DIM; j++) {
                board.setField(i, j, Mark.XX.getSymbol());
            }
        }
        assertTrue(board.isFull());
    }

}