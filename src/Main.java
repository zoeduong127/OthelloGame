import model.Mark;

import javax.swing.*;

public class Main  {
    public static void main(String[] args) {
        Mark emptyPoint = Mark.EMPTY;
        Mark blackPoint = Mark.XX;
        Mark whitePoint = Mark.OO;
        System.out.print(emptyPoint.getSymbol());
        System.out.print(blackPoint.getSymbol());
        System.out.print(whitePoint.getSymbol());
    }
}