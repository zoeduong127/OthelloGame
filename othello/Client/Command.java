package Client;

/**
 * This interface is a collection of Command from client send to server and vice versa
 */
public interface Command {
    public static final String HELLO = "HELLO";
    public static final String LOGIN = "LOGIN";
    public static final String ALREADYLOGGEDIN = "ALREADYLOGGEDIN";
    public static final String QUEUE = "QUEUE";
    public static final String NEWGAME = "NEWGAME";
    public static final String MOVE = "MOVE";
    public static final String QUIT = "QUIT";
    public static final String GAMEOVER = "GAMEOVER";
    public static final String HELP = "HELP";
    public static final String LIST = "LIST";
    public static final String ERROR = "ERROR";
    public static final String VICTORY = "VICTORY";
    public static final String DISCONNECT = "DISCONNECT";
    public static final String DRAW = "DRAW";
}
