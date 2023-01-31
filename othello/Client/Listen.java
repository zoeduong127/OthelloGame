package Client;

import java.io.IOException;

public interface Listen {
    /**
     * An interface that defines a listener for incoming messages in a server-client game application.
     */

    void handleMessage(String input) throws IOException, ProtocolException;
}
