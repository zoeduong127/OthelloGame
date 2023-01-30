package Client;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.Scanner;

public class ClientTUI {
    private PrintWriter print;
    public static BufferedReader reader;
    public ClientTUI(){
        print = new PrintWriter(System.out, true);
        reader = new BufferedReader(new InputStreamReader(System.in));
    }
    public void println(String string){
        print.println(string);
    }
    public static void main (String[] args) throws IOException {
        ClientTUI tui = new ClientTUI();
        Client client = new Client();
        tui.println("Enter the port: ");
        int serverPort = Integer.parseInt(reader.readLine());
        tui.println("Enter the server address: ");
        String serverAddress = reader.readLine();
        try {
            if (!client.connect(InetAddress.getByName(serverAddress), serverPort)) {
                tui.println("\n ERROR: Failed to connect! Try again.");
            }
        } catch (UnknownHostException e) {
            tui.println("\n ERROR: Failed to find the Server Address! Try again.");
        }
    }
}
