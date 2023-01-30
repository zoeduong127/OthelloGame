package Client;

import java.io.IOException;

public interface ChatListener  {

    void handleMessage(String input) throws IOException;
}
