package Client;

import java.io.IOException;

public interface Listen {
    /**
     * An interface that defines a listener for incoming messages in a server-client game application.
     */
    /**
     * reiceived and handler message from the server
     * @param input message from server
     * @throws IOException if I/O occurs when reading message
     * @throws ProtocolException if message is not in format.
     */
    void handleMessage(String input) throws IOException, ProtocolException;

}
