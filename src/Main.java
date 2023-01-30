import java.io.File;
import javax.sound.sampled.AudioSystem;
import javax.sound.sampled.Clip;

public class Main {
    public static void playSound(String fileName) {
        try {
            File soundFile = new File(fileName);
            Clip clip = AudioSystem.getClip();
            clip.open(AudioSystem.getAudioInputStream(soundFile));
            clip.start();
        } catch (Exception e) {
            System.out.println("Error playing sound: " + e.getMessage());
        }
    }

    public static void main(String[] args) {
        // play sound when client connects successfully
        playSound("C:\\Users\\Admin\\Downloads\\Project\\Document\\SeeTinh-HoangThuyLinh-7702265.mp3");
    }
}
