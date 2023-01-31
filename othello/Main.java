

public class Main {
    public static final String ANSI_GREEN_BACKGROUND = "\u001B[42m";
    public static final String ANSI_RESET = "\u001B[0m";
    public static final String WHITE_POINT = "\u25CB";
    public static final String BLACK_POINT = "\u25CF";

    public static void main(String[] args) {
        for (int i = 0; i < 8; i++) {
            for (int j = 0; j < 8; j++) {
                if ((i + j) % 2 == 0) {
                    System.out.print(ANSI_GREEN_BACKGROUND + "   " + ANSI_RESET);
                } else {
                    System.out.print(ANSI_GREEN_BACKGROUND + (i < 4 ? WHITE_POINT : BLACK_POINT) + ANSI_RESET);
                }
            }
            System.out.println();
        }
    }
}