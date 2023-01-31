package Client;


/**
 * This class represents an exception related to a protocol.
 * @author [Author Name]
 */
public class ProtocolException extends Exception {
    /**
     * Constructs a new ProtocolException with the specified input as the error message.
     * @param input the error message
     */
    public ProtocolException(String input){
        super("[Error] "+ input);
    }
}
