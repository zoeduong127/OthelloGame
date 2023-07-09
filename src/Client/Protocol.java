package Client;

/**
 * Protocol class with constants and methods for creating protocol messages
 */
public final class Protocol {
    private Protocol() {}

    public static final String Description = "Server from client center";
    public static final String SEND_COMMAND = "[CLIENT] ";
    public static final String SERVER_MESS = "[SERVER] ";
    public static final String SEPARATOR = "~";



    /**
     * Build a new protocol message which instructs the server that client want to say something
     * @param command the title of content client want to send to server
     * @param argument the main content of argument which client want to send to server
     * @return a complete format for message with header and content
     */
    public static String sendCommand(String command, String argument) {
        return command + SEPARATOR + argument;
    }

    /**
     * Build a new protocol message which instructs to display the message from server  to player
     * @param input the content of message
     * @return the right format of message
     */

    public static String Servermess( String input){
        return SERVER_MESS + input;
    }
    /**
     * Build a new protocol message which instructs to display the message from client to player
     * @param input the content of message
     * @return the right format of message
     */
    public static String Clientmess(String input){
        return SEND_COMMAND + input;
    }

    /**
     * The list of client's state during the process connect and player with server.
     */
    public enum ClientState {
        CONNECT_AWAITING,
        HELLO_AWAITING,
        LOGIN_AWAITING,
        DECISION,
        NEWGAME_AWAITING,
        MOVE_AWAITING,
        HELP,
        QUIT
    }

}
