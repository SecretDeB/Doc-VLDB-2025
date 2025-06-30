package src.opt;

import constants.Constant;
import org.tartarus.snowball.SnowballStemmer;
import utility.Helper;

import java.io.*;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.math.RoundingMode;
import java.net.ServerSocket;
import java.net.Socket;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.time.Duration;
import java.time.Instant;
import java.util.*;
import java.util.logging.Level;
import java.util.logging.Logger;

public class Client extends Thread {

    private static Properties properties;
    private static final Logger log = Logger.getLogger(Logger.GLOBAL_LOGGER_NAME);
    // the mod value
    private static final long modValue = Constant.getModParameter();
    private static final int hashBlockCount = Constant.getHashBlockCount();
    private static final int hashBlockSize = Constant.getHashBlockSize();
    // the mod value for BigInteger
    private static final BigInteger modValueBig = Constant.getModBigParameter();
    private static String searchKeyword;
    private static String clientId;
    private static List<Object> objects;
    private static int serverCount;
    private static BigInteger[] keywordShares;
    private static long[][] keywordVectorShares;
    private static int keywordCount;
    private static long[] keywordVector;
    // to store the number of files
    private static int fileCount;
    // to store the index of the keyword in act table
    private static int phase1Result;
    private static ArrayList<Long> phase2Result;
    private static long[] hash_list;
    private static long[][] phase3Result;
    private static boolean serverVerification;
    private static boolean clientVerification;
    private static long[][] fileVectors;
    private static long[][][] fileVectorsShares;
    private static long[][] hash;
    private static String type;
    private static int numThreads;
    private static String stage;
    private static String stageLabel;
    private static boolean flagCVP1;
    private static BigInteger[] servers_1_2_3;
    private static BigInteger[] servers_1_2_4;
    private static BigInteger[] servers_2_3_4;
    private static BigInteger[] servers_1_3_4;
    private static ArrayList<Instant> comTime = new ArrayList<>();
    private static ArrayList<Instant> waitTime = new ArrayList<>();
    private static Scanner console;
    private static int fileLength;
    private static long[][] objectsReceivedLong1D;
    // to stores server shares as long values for 2D array
    private static long[][][] objectsReceivedLong2D;
    // to stores server shares as long values for 1D array
    private static String[][] objectsReceivedString1D;
    // to stores server shares as long values for 2D array
    private static String[][][] serverSharesAsString_2D;
    private static String[][] content;
    private static String[] finalContent;
    private static ArrayList<Instant> removeTime;
    private static ArrayList<Double> perServerTime;
    private static String[] serverIP;
    private static int[] serverPort;
    private static ServerSocket ss;
    private static Socket socketClient;
    private static Socket socketServer;
    private static ObjectOutputStream outputStream;
    private static ObjectInputStream inputStream;
    private static long[] hashServer;
    // to store stemmer object
    private static SnowballStemmer stemmer;
    // to store the numeric version of text
    private static StringBuilder numericText;
    // to store the updates text
    private static StringBuilder newText;
    private static long[] optInvRowVec;
    private static long[] optInvColVec;
    private static long[][] optInvRowVecShare;
    private static long[][] optInvColVecShare;
    private static int optRow;
    private static int optCol;
    private static int startingPos;
    private static int countItems;
    private static long[][][] optIndexShare;
    private static long[][] serverVerificationPhase3;
    private static long[][][] verificationServer2DPhase3;
    private static int checkpoint1;

    /**
     * to perform hash digest of given data using SHA-1
     *
     * @param data The given data
     * @return The numeric hash digest value of 20B
     * @throws NoSuchAlgorithmException
     */
    public static String hashDigest(String data) throws NoSuchAlgorithmException {
        MessageDigest md = MessageDigest.getInstance("SHA-1");
        md.update(data.getBytes());
        byte[] digest = md.digest();
        BigInteger result = (new BigInteger(digest)).mod(modValueBig);
        return result.toString();
    }

    /**
     * Convert keyword to number
     *
     * @param data the keyword
     * @return the numeric format of keyword
     */
    public static void keywordToNumber(String data) {
        numericText = new StringBuilder("");
        for (int i = 0; i < data.length(); i++) {
            numericText.append((int) data.charAt(i) - 86);
        }
    }

    /**
     * To convert numeric string to string values
     *
     * @param numericString the numeric format of string
     * @return the cleartext string
     */
    public static String decrypt_numeric_string(String numericString) {
        StringBuilder text = new StringBuilder();
        int substring;
        if (numericString.length() % 2 == 1)
            numericString = numericString.substring(0, numericString.length() - 1);

        for (int i = 0; i < numericString.length(); i = i + 2) {
            substring = Integer.parseInt(numericString.substring(i, (i + 2)));

            if (substring >= 10 && substring <= 99) {
                if (substring == 10) {
                    text.append((char) (96));
                } else if (substring <= 14) {
                    text.append((char) (substring + 112));
                } else if (substring >= 65 && substring <= 90) {
                    text.append((char) (substring + 32));
                } else {
                    text.append((char) (substring));
                }
            }

        }

        return text.toString();
    }

    /**
     * To perform cleanup tasks in course of program execution
     */
    public static void cleanUp() {
        // re-initializing the list to hold values received from server
        objects = Collections.synchronizedList(new ArrayList<>());
    }

    /**
     * To perform cleanup tasks in course of program execution
     */
    public static void cleanUpPhaseData(int phase) {
        switch (phase) {
            case 1 -> {
                servers_1_2_3 = new BigInteger[numThreads];
                servers_1_2_4 = new BigInteger[numThreads];
                servers_1_3_4 = new BigInteger[numThreads];
                servers_2_3_4 = new BigInteger[numThreads];
                perServerTime = new ArrayList<>();
                removeTime = new ArrayList<>();
            }
            case 2 -> {
                objectsReceivedLong1D = null;
                keywordVectorShares = new long[serverCount][keywordCount];
                hashServer = new long[hashBlockCount];
                optInvRowVec = new long[optRow];
                optInvColVec = new long[optCol];
                optInvRowVecShare = new long[serverCount][optRow];
                optInvColVecShare = new long[serverCount][optCol];
                optIndexShare = new long[serverCount][2][];
                hash_list = new long[hashBlockCount];
                perServerTime = new ArrayList<>();
                removeTime = new ArrayList<>();
            }
            case 3 -> {
                // GC
                objectsReceivedLong1D = null;
                verificationServer2DPhase3 = null;
                phase3Result = null;
                hash = null;
                content = null;
                perServerTime = new ArrayList<>();
                removeTime = new ArrayList<>();
                fileVectors = new long[1][fileCount + 1]; // one for sample file
                fileVectorsShares = new long[serverCount][1 + 1][fileCount + 1];
                hash = new long[1][hashBlockCount];
                content = new String[1][numThreads];
                serverVerificationPhase3 = new long[1][checkpoint1];
                finalContent = new String[1];}
        }
    }

    /**
     * To interpolate share values to retrieve secret
     * @param share the shares
     * @return the cleartext/interpolated value
     */
    public static BigInteger lagrangeInterpolation(BigInteger[] share) {
        return switch (share.length) {
            case 2 -> ((BigInteger.valueOf(2).multiply(share[0])).mod(modValueBig).subtract(share[1]))
                    .mod(modValueBig);
            case 3 -> (((BigInteger.valueOf(3)
                    .multiply(share[0])).mod(modValueBig).subtract((BigInteger.valueOf(3)
                    .multiply(share[1])).mod(modValueBig))).mod(modValueBig).add(share[2])).mod(modValueBig);
            default -> throw new IllegalStateException("Unexpected value: " + share.length);
        };
    }

    /**
     * To interpolate share values to retrieve secret
     *
     * @param share the shares
     * @return the cleartext/interpolated value
     */
    public static BigInteger lagrangeInterpolation(BigInteger[] share, long x0, long x1, long x2) {
        BigInteger result;
        BigDecimal part_a = new BigDecimal((BigInteger.valueOf(x1 * x2).multiply(share[0]))).
                divide(new BigDecimal(BigInteger.valueOf(((x0 - x1) * (x0 - x2)))), 10, RoundingMode.DOWN);
        BigDecimal part_b = new BigDecimal((BigInteger.valueOf(x0 * x2).multiply(share[1]))).
                divide(new BigDecimal(BigInteger.valueOf(((x1 - x0) * (x1 - x2)))), 10, RoundingMode.DOWN);
        BigDecimal part_c = new BigDecimal((BigInteger.valueOf(x0 * x1).multiply(share[2]))).
                divide(new BigDecimal(BigInteger.valueOf(((x2 - x0) * (x2 - x1)))), 10, RoundingMode.DOWN);

        BigDecimal a = (part_a.add(part_b).add(part_c)).divide(BigDecimal.valueOf(1), 0, RoundingMode.CEILING);
        result = (new BigInteger(String.valueOf(a))).mod(modValueBig);
        return result;
    }

    /**
     * To interpolate share values to retrieve secret
     *
     * @param share the shares
     * @return the cleartext/interpolated value
     */
    public static long lagrangeInterpolation(long[] share) {
        return switch (share.length) {
            case 2 -> Math.floorMod((((2 * share[0]) % modValue) - share[1]), modValue);
            case 3 -> (Math.floorMod((((3 * share[0]) % modValue) -
                    ((3 * share[1]) % modValue)), modValue) + share[2]) % modValue;
            default -> throw new IllegalStateException("Unexpected value: " + share.length);
        };
    }

    /**
     * start client to receive data from server
     *
     * @param serverCount the number of server to receive from
     */
    public static void startClient(int serverCount) {

        try {
            System.out.println("Client Listening........");
            while (objects.size() != serverCount) {
                //Reading data from the server
                waitTime.add(Instant.now());
                socketClient = ss.accept();
                inputStream = new ObjectInputStream(socketClient.getInputStream());
                waitTime.add(Instant.now());

                objects.add(inputStream.readObject());
            }
        } catch (IOException ex) {
            log.log(Level.SEVERE, ex.getMessage());
        } catch (ClassNotFoundException e) {
            throw new RuntimeException(e);
        }
    }

    /**
     * To create a socket and send data to the server
     *
     * @param data the data to be sent
     * @param IP   the IP of the target server
     * @param port the port of the target server
     * @throws IOException
     */
    public static void sendToServer(Object data, String IP, int port) throws IOException {
        try {
            waitTime.add(Instant.now());
            // creating server socket and output stream
            socketServer = new Socket(IP, port);
            outputStream = new ObjectOutputStream(socketServer.getOutputStream());
            waitTime.add(Instant.now());
            // writing data to stream
            outputStream.writeObject(data);
        } catch (IOException ex) {
            log.log(Level.SEVERE, ex.getMessage());
        }
    }

    /**
     * To read values from objects
     *
     * @param type the type of object as 1D or 2D
     */
    public static void readObjectsAsLong(String type) {
        if (type.equals("1D")) {
            for (int i = 0; i < objects.size(); i++) {
                int temp = (int) (((long[]) objects.get(i))[((long[]) objects.get(i)).length - 1]);
                objectsReceivedLong1D[temp - 1] = ((long[]) objects.get(i));
            }
        } else if (type.equals("2D")) {
            for (int i = 0; i < objects.size(); i++) {
                int temp = (int) (((long[][]) objects.get(i))[((long[][]) objects.get(i)).length - 1][0]);
                objectsReceivedLong2D[temp - 1] = ((long[][]) objects.get(i));
            }
        }
    }

    /**
     * To read values from objects
     *
     * @param type the type of object as 1D or 2D
     */
    public static void readObjectsAsString(String type) {
        if (type.equals("1D")) {
            for (int i = 0; i < objects.size(); i++) {
                String objectRead = new String((byte[]) objects.get(i), StandardCharsets.UTF_8);
                int temp = objectRead.charAt(objectRead.length() - 1) - '0';
                objectsReceivedString1D[temp - 1] = objectRead.split(",");
            }

        } else if (type.equals("2D")) {
            for (int i = 0; i < objects.size(); i++) {
                byte[][] data = (byte[][]) objects.get(i);
                int temp = new String(data[data.length - 1], StandardCharsets.UTF_8).charAt(0) - '0';
                serverSharesAsString_2D[temp - 1] = new String[phase2Result.size()][];
                for (int j = 0; j < data.length - 1; j++) {
                    serverSharesAsString_2D[temp - 1][j] = new String(data[j], StandardCharsets.UTF_8).split(",");
                }
            }
        }

    }

    /**
     * Create share for secret value as string
     *
     * @param secret      the secret value as string
     * @param serverCount the number of servers for which shares are to be created
     * @return the share of the secret value as string is returned for given number of server as servercount
     */
    public static BigInteger[] shamirSecretShares(StringBuilder secret, int serverCount) {

        BigInteger secretBig = new BigInteger(String.valueOf(secret));
        Random rand = new Random();
        BigInteger[] share = new BigInteger[serverCount];

        BigInteger slope = BigInteger.valueOf(rand.nextLong(Constant.getMaxRandomBound() - Constant.getMinRandomBound()) +
                Constant.getMinRandomBound());

        // check if the secret size is enough for long or BigInteger calculation
        for (int i = 0; i < serverCount; i++) {
            share[i] = ((BigInteger.valueOf(i + 1).multiply(slope)).add(secretBig)).mod(modValueBig);
        }
        return share;
    }

    /**
     * Create share for secret value as string
     *
     * @param secret      the secret value as string
     * @param serverCount the number of servers for which shares are to be created
     * @return the share of the secret value as string is returned for given number of server as servercount
     */
    public static long[] shamirSecretShares(long secret, int serverCount) {
        Random rand = new Random();
        long[] share = new long[serverCount];
        // choosing the slope value for line
        long slope = rand.nextInt(Constant.getMaxRandomBound() - Constant.getMinRandomBound()) +
                Constant.getMinRandomBound();
        // check if the secret size is enough for long or BigInteger calculation
        for (int i = 0; i < serverCount; i++) {
            share[i] = (((i + 1) * slope) + secret) % modValue;
        }
        return share;
    }

    /**
     * Process input keyword and create share for secret value
     *
     * @param searchKeyword the secret value
     * @return the share of the secret value is returned for given number of server as servercount
     */
    public static void createShares(String searchKeyword) {

        // changing all case to lowercase
        searchKeyword = searchKeyword.toLowerCase();

        // perform stemming of the token
        stemmer.setCurrent(searchKeyword);
        stemmer.stem();
        searchKeyword = stemmer.getCurrent();

        // converting keyword as string to number
        keywordToNumber(searchKeyword);

        //padding token to avoid leakage due to keyword size
        if (numericText.length() < 2 * Constant.getMaxKeywordLength()) {
            while (numericText.length() < 2 * Constant.getMaxKeywordLength())
                numericText.append(Constant.getPadding());
        }

        // creating the shares
        keywordShares = shamirSecretShares(numericText, serverCount);
    }

    /**
     * create job to be run by each thread
     */
    public static class ThreadTask implements Runnable {
        private int threadNum;
        private String stage;
        private String stageLabel;

        public ThreadTask(int threadNum, String stage, String stageLabel) {
            this.threadNum = threadNum;
            this.stage = stage;
            this.stageLabel = stageLabel;
        }

        @Override
        public void run() {
            if (stage.equals("1")) {
                if (stageLabel.equals("1"))
                    task11(threadNum);
                else if (stageLabel.equals("2")) {
                    task12(threadNum);
                }
            } else if (stage.equals("2")) {
                if (stageLabel.equals("1")) {
                    task21(threadNum);
                } else if (stageLabel.equals("2")) {
                    task22(threadNum);
                }

            } else if (stage.equals("3")) {
                if (stageLabel.equals("1")) {
                    task31(threadNum);
                } else if (stageLabel.equals("2")) {
                    task32(threadNum);
                } else if (stageLabel.equals("3")) {
                    task33(threadNum);
                }

            }

        }
    }

    /**
     * create thread for multithreaded execution
     *
     * @param stage
     * @param stageLabel
     */
    public static void createThreads(String stage, String stageLabel) {
        List<Thread> threadList = new ArrayList<>();
        // Create threads and add them to thread-list
        int threadNum;
        for (int i = 0; i < numThreads; i++) {
            threadNum = i + 1;
            threadList.add(new Thread(new ThreadTask(threadNum, stage, stageLabel), "Thread" + threadNum));
        }
        // Start all threads
        for (int i = 0; i < numThreads; i++) {
            threadList.get(i).start();
        }
        // Wait for all threads to finish
        for (Thread thread : threadList) {
            try {
                thread.join();
            } catch (InterruptedException ex) {
                ex.printStackTrace();
            }
        }
    }

    /**
     * To create shares of the file vectors
     * multithreaded across number of files
     * @param threadNum the thread number
     */
    public static void task31(int threadNum) {
        long[] shares;
        int batchSize = (int) Math.ceil(fileCount / (double) numThreads);
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;
        if (end > fileCount) {
            end = fileCount;
        }

        for (int m = 0; m < fileVectors.length; m++) {
            for (int i = start; i < end; i++) {
                shares = shamirSecretShares(fileVectors[m][i], serverCount);
                for (int j = 0; j < serverCount; j++)
                    fileVectorsShares[j][m][i] = shares[j];
            }
        }
    }

    /**
     * to interpolate the content of the file
     * multithreaded across the maximum length of file
     * @param threadNum
     */
    public static void task32(int threadNum) {
        long[] shares = new long[serverCount];
        int batchSize = (int) Math.ceil(fileLength / (double) numThreads);
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;
        if (end > fileLength) {
            end = fileLength;
        }

        for (int i = 0; i < phase3Result.length; i++) {
            StringBuilder str = new StringBuilder();
            for (int j = start; j < end; j++) {
                for (int l = 0; l < serverCount; l++) {
                    shares[l] = objectsReceivedLong2D[l][i][j];
                }
                phase3Result[i][j] = lagrangeInterpolation(shares);
                if (j < hashBlockCount) {
                    hash[i][j] = phase3Result[i][j];
                } else {
                    str.append(phase3Result[i][j]);
                }
            }
            content[i][threadNum - 1] = String.valueOf(str);
        }
    }

    /**
     * interpolate the keyword vector containing the list of keywords a file contains
     * @param threadNum
     */
    public static void task33(int threadNum) {
        long[] shares = new long[serverCount];
        int batchSize = (int) Math.ceil((checkpoint1) / (double) numThreads);
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;
        if (end > (checkpoint1)) {
            end = checkpoint1;
        }

        for (int i = 0; i < phase2Result.size(); i++) {
            for (int j = start; j < end; j++) {
                for (int l = 0; l < serverCount; l++) {
                    shares[l] = objectsReceivedLong2D[l][i][j];
                }
                serverVerificationPhase3[i][j] = lagrangeInterpolation(shares);
                shares = shamirSecretShares(serverVerificationPhase3[i][j], serverCount);
                for (int l = 0; l < serverCount; l++) {
                    verificationServer2DPhase3[l][i][j] = shares[l];
                }
            }
        }
    }

    /**
     * create shares of the array
     * @param data the data
     * @param serverCount the number of servers
     * @return the shares af the data
     */
    public static long[][][] createShares(long[][] data, int serverCount) {
        long[][][] result = new long[serverCount][data.length][data[0].length];
        for (int i = 0; i < data.length; i++) {
            for (int j = 0; j < data[0].length; j++) {
                long[] shares = shamirSecretShares(data[i][j], serverCount);
                for (int l = 0; l < serverCount; l++) {
                    result[l][i][j] = shares[l];
                }
            }
        }
        return result;
    }

    /**
     * convert keywords list to size of ACT keywords
     * @param data the list of keyword indices
     * @return elongated list of size equal to ACT keywords
     */
    public static long[][] fileKeyToActKey(long[][] data) {
        long[][] result = new long[data.length][keywordCount];
        for (int i = 0; i < data.length; i++) {
            for (int j = 0; j < data[0].length; j++) { // first position if fileid
                if (data[i][j] != 0) {
                    result[i][(int) data[i][j] - 1] = 1;
                }
            }
        }
        return result;
    }

    /**
     * to fetch the file given file id
     * @throws IOException
     * @throws NoSuchAlgorithmException
     */
    public static void phase3() throws IOException, NoSuchAlgorithmException {
        stage = "3";
        serverCount = 3;

        // TODO: delete this line
        List<Long> phaseResultTemp = phase2Result;
        phase2Result = new ArrayList<>();
        phase2Result.add(phaseResultTemp.get(0));

        // preparing fileVectors vector for sending to server
        int k = 0;
        for (long file : phase2Result) {
            if (file == 0) {
                file = fileCount + 1;
            }
            fileVectors[k][(int) (file - 1)] = 1;
//            fileVectors[k][(int) (file+1) -1] = 1;  // Test for client correctness for server: test 1
//            fileVectors[k][(int) (file + 1) - 1] = 2;  // Test for client correctness for server: test 3, 4, 5
            k++;
        }
        // create shares of the fileVectors
        stageLabel = "1";
        createThreads(stage, stageLabel);
        // sending shares to the server
        removeTime.add(Instant.now());
        comTime.add(Instant.now());
        long[][] data2D;
        int org = startingPos % optCol;
        for (int i = 0; i < serverCount; i++) {
            fileVectorsShares[Math.floorMod(i - 1, serverCount)][phase2Result.size()][0] = (i + 1);
            fileVectorsShares[Math.floorMod(i - 1, serverCount)][phase2Result.size()][1] = (org + Math.floorMod(i - 1, serverCount) + 1);
            data2D = fileVectorsShares[Math.floorMod(i - 1, serverCount)];
            sendToServer(data2D, serverIP[i], serverPort[i]);
        }
        comTime.add(Instant.now());
        perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, serverCount));
        comTime = new ArrayList<>();
        waitTime = new ArrayList<>();
        removeTime.add(Instant.now());

        if (serverVerification) {
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            startClient(serverCount);
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, serverCount));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());
            type = "2D";
            objectsReceivedLong2D = new long[serverCount][][];
            readObjectsAsLong(type);
            cleanUp();
            boolean flag = true;
            for (int j = 0; j < serverCount; j++) {
                if (objectsReceivedLong2D[j][0][0] == 0) {
                    flag = false;
                    break;
                }
            }
            if (!flag) {
                log.info("Client has prepared an incorrect file vector");
                System.exit(0);
            }
        } else {
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            startClient(serverCount);
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, serverCount));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());
            type = "2D";
            objectsReceivedLong2D = new long[serverCount][][];
            readObjectsAsLong(type);
            cleanUp();
        }
        serverVerificationPhase3 = new long[phase2Result.size()][checkpoint1];
        verificationServer2DPhase3=new long[serverCount][phase2Result.size()][checkpoint1];
        stageLabel = "3";
        createThreads(stage, stageLabel);
        // create array out of file keyword and then create its shares
        long[][] fileKeys = fileKeyToActKey(serverVerificationPhase3);
        verificationServer2DPhase3 = createShares(fileKeys, serverCount);
        // send to server the shares
        removeTime.add(Instant.now());
        comTime.add(Instant.now());
        for (int i = 0; i < serverCount; i++) {
            data2D = verificationServer2DPhase3[Math.floorMod(i - 1, serverCount)];
            sendToServer(data2D, serverIP[i], serverPort[i]);
        }
        comTime.add(Instant.now());
        perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, serverCount));
        comTime = new ArrayList<>();
        waitTime = new ArrayList<>();
        removeTime.add(Instant.now());

        removeTime.add(Instant.now());
        comTime.add(Instant.now());
        startClient(serverCount);
        comTime.add(Instant.now());
        perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, serverCount));
        comTime = new ArrayList<>();
        waitTime = new ArrayList<>();
        removeTime.add(Instant.now());
        type = "2D";
        objectsReceivedLong2D = new long[serverCount][][];
        readObjectsAsLong(type);
        cleanUp();
        boolean flag = true;
        for (int j = 0; j < serverCount; j++) {
            if (objectsReceivedLong2D[j][0][0] == 0) {
                flag = false;
                break;
            }
        }
        if (!flag) {
            log.info("Client has prepared an incorrect file vector Or has no access on all keywords of requested file.");
            System.exit(0);
        }
        // to fetch the file content
        fileLength = objectsReceivedLong2D[0][0].length;
        phase3Result = new long[phase2Result.size()][fileLength];
        stageLabel = "2";
        createThreads(stage, stageLabel);
        for (int i = 0; i < phase3Result.length; i++) {
            finalContent[i] = "";
            for (int p = 0; p < numThreads; p++) {
                finalContent[i] = finalContent[i] + content[i][p];
            }
            finalContent[i] = decrypt_numeric_string(finalContent[i]);
        }
        if (clientVerification) {
            String hashC;
            long[] hashClient;
            int h;
            for (int i = 0; i < phase3Result.length; i++) {
                hashC = hashDigest(finalContent[i].trim());
                h = 0;
                hashClient = new long[hashBlockCount];
                for (int j = 0; j < hashC.length(); j = j + hashBlockSize) {
                    int end = j + hashBlockSize;
                    if (end > hashC.length())
                        end = hashC.length();
                    hashClient[h] = Long.parseLong(hashC.substring(j, end));
                    h++;
                }
                for (int m = 0; m < hashBlockCount; m++) {
//                    hash[i][m] = 90; // Test for server correctness for client
                    if (!(hash[i][m] == hashClient[m])) {
                        log.info("The files content provided by the servers is incorrect.");
                        flag = false;
                    }
                }
            }
            if (!flag) {
                log.info("The files content results by the servers is incorrect");
                System.exit(0);
            }
        }
        System.out.println("The file/s with keyword " + searchKeyword + " is/are stored in results folder.");
        for (int i = 0; i < phase3Result.length; i++) {
            Helper.writeToFile(String.valueOf(phase2Result.get(i)), finalContent[i], stage);
        }
    }

    /**
     * To create shares of keyword vector formed in phase 2 based on keyword index fetched from phase 1
     * multithreaded across number of keywords
     *
     * @param threadNum the number of threads
     */
    public static void task21(int threadNum) {
        Instant start1=Instant.now();
        int batchSize = (int) Math.ceil(keywordCount / (double) numThreads);
        long[] shares;
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;
        if (end > keywordCount) {
            end = keywordCount;
        }

        for (int i = start; i < end; i++) {
            shares = shamirSecretShares(keywordVector[i], serverCount);
            for (int j = 0; j < serverCount; j++)
                keywordVectorShares[j][i] = shares[j];
        }
        Instant end1=Instant.now();
//        System.out.println("keyword vector:"+Duration.between(start1,end1).toMillis());
    }

    /**
     * to interpolate ADDR data returned from server
     */
    public static void readAddrTable() {
        Instant start1=Instant.now();
        System.out.println("ADDR result");
        long interpolatedValue;
        long[] shares = new long[serverCount];
        for (int i = 0; i < objectsReceivedLong1D[0].length - 1; i++) {
            for (int j = 0; j < serverCount; j++) {
                shares[j] = objectsReceivedLong1D[j][i];
            }
            interpolatedValue = lagrangeInterpolation(shares);
            System.out.print(interpolatedValue + " ");
            if (i == 0) {
                startingPos = (int) interpolatedValue;
            } else if (i == 1) {
                countItems = (int) interpolatedValue;
            } else {
                hashServer[i - 2] = interpolatedValue;
            }
        }
        System.out.println();
        Instant end1=Instant.now();
//        System.out.println("readAddrTable:"+Duration.between(start1,end1).toMillis());
    }

    // multithreaded across number of opt inverted index row and col

    /**
     * create shares of row and column vector of opt inverted index
     * multithreaded across number of columns
     *
     * @param threadNum thread number
     */
    public static void task22(int threadNum) {
        Instant start1=Instant.now();
        int batchSize = (int) Math.ceil(optCol / (double) numThreads);
        long[] shares;
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;
        if (end > optCol) {
            end = optCol;
        }
        for (int i = start; i < end; i++) {
            shares = shamirSecretShares(optInvColVec[i], serverCount);
            for (int j = 0; j < serverCount; j++)
                optInvColVecShare[j][i] = shares[j];
        }

        batchSize = (int) Math.ceil(optRow / (double) numThreads);
        start = (threadNum - 1) * batchSize;
        end = start + batchSize;
        if (end > optRow) {
            end = optRow;
        }
        for (int i = start; i < end; i++) {
            shares = shamirSecretShares(optInvRowVec[i], serverCount);
            for (int j = 0; j < serverCount; j++)
                optInvRowVecShare[j][i] = shares[j];
        }
        Instant end1=Instant.now();
//        System.out.println("row and column vector:"+Duration.between(start1,end1).toMillis());
    }

    /**
     * to interpolate the file ids received from the server
     */
    public static void phase2ResultInterpolation() {
        Instant start1=Instant.now();
        long interpolatedValue;
        long[] shares = new long[serverCount];
        for (int i = 0; i < countItems; i++) {
            for (int j = 0; j < serverCount; j++) {
                shares[j] = objectsReceivedLong1D[j][(startingPos + i) % optCol];
            }
            interpolatedValue = lagrangeInterpolation(shares);
            if (i < hashBlockCount) {
                hash_list[i] = interpolatedValue;
            } else {
                phase2Result.add(interpolatedValue);
            }
        }
        Instant end1=Instant.now();
//        System.out.println("phase2ResultInterpolation:"+Duration.between(start1,end1).toMillis());
    }

    /**
     * To perform phase 2 operation of fetching the file ids for the search keyword from inverted index and addr
     * @throws IOException
     * @throws NoSuchAlgorithmException
     */
    public static void phase2() throws IOException, NoSuchAlgorithmException {
        phase2Result = new ArrayList<>();
        stage = "2";
        serverCount = 3;
        {
            // retrieve addr data
            keywordVector = new long[keywordCount];
            keywordVector[phase1Result] = 1;
//            System.out.println("phase1Result:" + phase1Result);
//        keywordVector[phase1Result + 1] = 1; // Test 1,2
//        keywordVector[phase1Result] = 3; // Test 3,4,5
            stageLabel = "1";
            createThreads(stage, stageLabel);

            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            long[] data1D; // sending share to the server
            for (int i = 0; i < serverCount; i++) {
                data1D = keywordVectorShares[Math.floorMod(i - 1, 3)];
                sendToServer(data1D, serverIP[i], serverPort[i]);
            }
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, serverCount));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());

            // server either sends addr data or server verification for keyword vector as false if verification fails
            if (serverVerification) {
                removeTime.add(Instant.now());
                comTime.add(Instant.now());
                startClient(serverCount);
                comTime.add(Instant.now());
                perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, serverCount));
                comTime = new ArrayList<>();
                waitTime = new ArrayList<>();
                removeTime.add(Instant.now());
                type = "1D";
                objectsReceivedLong1D = new long[serverCount][];
                readObjectsAsLong(type);
                cleanUp();
                boolean flag = true;
                for (int j = 0; j < serverCount; j++) {
                    if (objectsReceivedLong1D[j][0] == 0) {
                        flag = false;
                        break;
                    }
                }
                if (!flag) {
                    log.info("Client has prepared an incorrect keyword vector.");
                    System.exit(0);
                }
            } else {
                removeTime.add(Instant.now());
                comTime.add(Instant.now());
                startClient(serverCount);
                comTime.add(Instant.now());
                perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, serverCount));
                comTime = new ArrayList<>();
                waitTime = new ArrayList<>();
                removeTime.add(Instant.now());
                type = "1D";
                objectsReceivedLong1D = new long[serverCount][]; // receive addr data
                readObjectsAsLong(type);
                cleanUp();
            }
            // interpolate and get position in opt_inv, number of files for keyword and hash values from addr table
            readAddrTable();
            // verifying if the addr data sent by server about the position and count items is correct
            if (clientVerification) {
                String hash = hashDigest(hashDigest(String.valueOf(startingPos)) + countItems);
                long[] hashClient = new long[hashBlockCount];
                // breaking hash digest into hash blocks to compare against what is received from server
                int j = 0;
                for (int i = 0; i < hash.length(); i = i + hashBlockSize) {
                    int end = i + hashBlockSize;
                    if (end > hash.length())
                        end = hash.length();
                    hashClient[j] = Long.parseLong(hash.substring(i, end));
                    j++;
                }
                // compare hash blocks with each other
                for (int i = 0; i < hashBlockCount; i++) {
//                indexHashList[i]=90; // test for server
                    if (!(hashServer[i] == hashClient[i])) {
                        log.info("The addr content provided by the servers is incorrect.");
                        removeTime.add(Instant.now());
                        comTime.add(Instant.now());
                        for (int p = 0; p < serverCount; p++) {
                            sendToServer(new long[][]{{0}}, serverIP[p], serverPort[p]);
                        }
                        comTime.add(Instant.now());
                        perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, serverCount));
                        comTime = new ArrayList<>();
                        waitTime = new ArrayList<>();
                        removeTime.add(Instant.now());
                        System.exit(0);
                    }
                }
            }
        }

        // process the data received from server to get the file ids
        // create vector to extract file_ids from opt_inv s
        optInvRowVec[startingPos / optCol] = 1;
        int startIndex = startingPos % optCol;
        int endIndex = ((startingPos + countItems) - 1) % optCol;
        for (int i = 0; i < optCol; i++) { // vector for extracting only particular columns
            if (i < startIndex || i > endIndex)
                optInvColVec[i] = 1;
//            optInvColVec[i] = 1; // test client correctness for server
        }
        // create shares of row and column vector
        stageLabel = "2";
        createThreads(stage, stageLabel);
        // sending share to the server
        removeTime.add(Instant.now());
        comTime.add(Instant.now());
        long[][] data2D;
        for (int i = 0; i < serverCount; i++) {
            optIndexShare[i][0] = optInvRowVecShare[i];
            optIndexShare[i][1] = optInvColVecShare[i];
            data2D = optIndexShare[i];
            sendToServer(data2D, serverIP[i], serverPort[i]);
        }
        comTime.add(Instant.now());
        perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, serverCount));
        comTime = new ArrayList<>();
        waitTime = new ArrayList<>();
        removeTime.add(Instant.now());
        // check if hash digest of cell in column vector match the addr hash digest
        if (serverVerification) {
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            startClient(serverCount);
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, serverCount));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());
            type = "1D";
            objectsReceivedLong1D = new long[serverCount][];
            readObjectsAsLong(type);
            cleanUp();
            boolean flag = true;
            for (int j = 0; j < serverCount; j++) {
                if (objectsReceivedLong1D[j][0] == 0) {
                    flag = false;
                    break;
                }
            }
            if (!flag) {
                log.info("Client has prepared an incorrect opt inv row/col vector.");
                System.exit(0);
            }
        } else {
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            startClient(serverCount);
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, serverCount));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());
            type = "1D"; // receive the file ids
            objectsReceivedLong1D = new long[serverCount][];
            readObjectsAsLong(type);
            cleanUp();
        }
        // interpolate the file ids received
        phase2ResultInterpolation();
        if (clientVerification) {
            String hash = hashDigest(searchKeyword);
            long[] hashClient = new long[hashBlockCount];
//             getting hash digest for file ids received
            for (long fileId : phase2Result) {
                hash = hashDigest(hash + fileId);
            }
            // breaking hash digest into hash blocks to compare against what is received from server
            int j = 0;
            String temp = hash;
            for (int i = 0; i < temp.length(); i = i + hashBlockSize) {
                int end = i + hashBlockSize;
                if (end > temp.length())
                    end = temp.length();
                hashClient[j] = Long.parseLong(temp.substring(i, end));
                j++;
            }
            // formatting hash blocks to compare against each other
            for (int i = 0; i < hashBlockCount; i++) {
//                hash_list[i]=90; // test server
                if (!(hash_list[i] == hashClient[i])) {
                    log.info("The files id/s provided by the servers is incorrect.");
                    removeTime.add(Instant.now());
                    comTime.add(Instant.now());
                    for (int p = 0; p < serverCount; p++) {
                        sendToServer(new long[][]{{0}}, serverIP[p], serverPort[p]);
                    }
                    comTime.add(Instant.now());
                    perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, serverCount));
                    comTime = new ArrayList<>();
                    waitTime = new ArrayList<>();
                    removeTime.add(Instant.now());
                    System.exit(0);
                }
            }
        }
        System.out.println("The file/s with keyword " + searchKeyword + " are stores in results folder. ");
        StringBuilder fileIds = new StringBuilder("");
        for (long file : phase2Result) {
            fileIds.append(file).append(",");
        }
        Helper.writeToFile("fileIds", String.valueOf(fileIds), stage);
    }

    /**
     * interpolate server data send as part of phase 1 computation
     * multithreaded across number of keywords
     *
     * @param threadNum
     */
    public static void task11(int threadNum) {
        BigInteger interpolatedValue;
        int batchSize = (int) Math.ceil(keywordCount / (double) numThreads);
        BigInteger[] shares = new BigInteger[serverCount];
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;
        if (end > keywordCount) {
            end = keywordCount;
        }

        BigInteger value0 = BigInteger.valueOf(0);
        for (int i = start; i < end; i++) {
            for (int j = 0; j < serverCount; j++) {
                shares[j] = new BigInteger(objectsReceivedString1D[j][i]);
            }
            interpolatedValue = lagrangeInterpolation(shares);
            if (interpolatedValue.equals(value0)) {
                phase1Result = i;
            }
        }
    }

    /**
     * interpolate server data send as part of phase 1 computation during server verification is true
     * multithreaded across number of keywords
     *
     * @param threadNum
     */
    public static void task12(int threadNum) {
        int batchSize = (int) Math.ceil(keywordCount / (double) numThreads);
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;
        if (end > keywordCount) {
            end = keywordCount;
        }
        BigInteger value0 = BigInteger.valueOf(0);
        BigInteger[] shares = new BigInteger[serverCount];
        for (int i = start; i < end; i++) {
            shares[0] = new BigInteger(objectsReceivedString1D[0][i]);
            shares[1] = new BigInteger(objectsReceivedString1D[1][i]);
            shares[2] = new BigInteger(objectsReceivedString1D[2][i]);
            servers_1_2_3[threadNum - 1] = lagrangeInterpolation(shares, 1, 2, 3);
            shares[0] = new BigInteger(objectsReceivedString1D[0][i]);
            shares[1] = new BigInteger(objectsReceivedString1D[1][i]);
            shares[2] = new BigInteger(objectsReceivedString1D[3][i]);
            servers_1_2_4[threadNum - 1] = lagrangeInterpolation(shares, 1, 2, 4);
            shares[0] = new BigInteger(objectsReceivedString1D[1][i]);
            shares[1] = new BigInteger(objectsReceivedString1D[2][i]);
            shares[2] = new BigInteger(objectsReceivedString1D[3][i]);
            servers_2_3_4[threadNum - 1] = lagrangeInterpolation(shares, 2, 3, 4);
            shares[0] = new BigInteger(objectsReceivedString1D[0][i]);
            shares[1] = new BigInteger(objectsReceivedString1D[2][i]);
            shares[2] = new BigInteger(objectsReceivedString1D[3][i]);
            servers_1_3_4[threadNum - 1] = lagrangeInterpolation(shares, 1, 3, 4);
            // checking if server values are consistent across pairs
            if (servers_1_2_3[threadNum - 1].equals(value0) || servers_1_2_4[threadNum - 1].equals(value0)
                    || servers_2_3_4[threadNum - 1].equals(value0) || servers_1_3_4[threadNum - 1].equals(value0)) {
                phase1Result = i;
                if (!(servers_1_2_3[threadNum - 1].equals(servers_1_2_4[threadNum - 1])
                        && servers_1_2_4[threadNum - 1].equals(servers_2_3_4[threadNum - 1])
                        && servers_2_3_4[threadNum - 1].equals(servers_1_3_4[threadNum - 1]))) {
                    flagCVP1 = false;
                    break;
                }
            }
        }
    }

    /**
     * For fetching the index of search keyword from ACT table
     *
     * @throws IOException
     */
    public static void phase1() throws IOException {
        stage = "1";
        phase1Result = -1;
        serverCount = 3;
        // if no client verification, only three servers are required
        if (clientVerification) {
            serverCount = 4;
        }
        // creating shares for the keyword
        createShares(searchKeyword);

        // sending search keyword shares and client id to the server
        removeTime.add(Instant.now());
        comTime.add(Instant.now());
        BigInteger[] data1D = new BigInteger[2];
        data1D[1] = new BigInteger(clientId);
        for (int i = 0; i < serverCount; i++) {
            if (i <= 2) {
                data1D[0] = keywordShares[Math.floorMod(i - 1, 3)];
            } else {
                data1D[0] = keywordShares[3];
            }
//            System.out.println(serverIP[i]);
//            System.out.println(serverPort[i]);
            sendToServer(data1D, serverIP[i], serverPort[i]);
//            System.out.println("sent");
        }
        comTime.add(Instant.now());
        perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, serverCount));
        comTime = new ArrayList<>();
        waitTime = new ArrayList<>();
        removeTime.add(Instant.now());

        // waiting for servers to send the search keyword index in ACT table
        removeTime.add(Instant.now());
        comTime.add(Instant.now());
        startClient(serverCount);
        comTime.add(Instant.now());
        perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, serverCount));
        comTime = new ArrayList<>();
        waitTime = new ArrayList<>();
        removeTime.add(Instant.now());

        // extracting search keyword indexes in ACT table
        type = "1D";
        objectsReceivedString1D = new String[serverCount][];
        readObjectsAsString(type); // reading data sent by servers
        cleanUp();
        keywordCount = (objectsReceivedString1D[0].length - 1); // since last element stores the label for the server

        if (!clientVerification) { // off clientVerification
            stageLabel = "1";
            createThreads(stage, stageLabel); // running threads to interpolate the data
        } else {
            flagCVP1 = true;
            stageLabel = "2";
            createThreads(stage, stageLabel);
            if (!flagCVP1) {
                log.info("The access control results by the servers is incorrect.");
                removeTime.add(Instant.now());
                comTime.add(Instant.now());
                for (int i = 0; i < serverCount; i++) {
                    sendToServer(new long[]{0}, serverIP[i], serverPort[i]);
                }
                comTime.add(Instant.now());
                perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, serverCount));
                comTime = new ArrayList<>();
                waitTime = new ArrayList<>();
                removeTime.add(Instant.now());
                System.exit(0);
            }
        }

        // to inform the servers to terminate if client has no access on the keyword or does not wish to continue
        if (phase1Result == -1) {
            log.info("Client has no access on documents of keyword '" + searchKeyword + "'.");
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            for (int i = 0; i < serverCount; i++) {
                sendToServer(new long[]{0}, serverIP[i], serverPort[i]);
            }
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, serverCount));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());
            System.exit(0);
        }
        System.out.println("The index of keyword " + searchKeyword + " is " + (phase1Result + 1) + ".");
    }

    /**
     * Performs initialization tasks like reading from the properties files, initial memory allocation etc
     *
     * @throws IOException
     */
    public static void initialization() throws IOException, ClassNotFoundException, InstantiationException, IllegalAccessException {
        // reading the commonProperties file for client
        Properties commonProperties = Helper.readPropertiesFile("config/Common.properties");

        serverVerification = Boolean.parseBoolean(commonProperties.getProperty("serverVerification"));
        clientVerification = Boolean.parseBoolean(commonProperties.getProperty("clientVerification"));
        numThreads = Integer.parseInt(commonProperties.getProperty("numThreads"));
        optRow = Integer.parseInt(commonProperties.getProperty("optRow"));
        optCol = Integer.parseInt(commonProperties.getProperty("optCol"));
        fileCount = Integer.parseInt(commonProperties.getProperty("fileCount"));
        checkpoint1 = Integer.parseInt(commonProperties.getProperty("checkpoint1"));

        console = new Scanner(System.in);

        // reading each server Ip and port numbers
        if (serverVerification) {
            serverCount = 4;
        } else {
            serverCount = 3;
        }
        serverIP = new String[serverCount];
        serverPort = new int[serverCount];
        for (int i = 0; i < serverCount; i++) {
            serverIP[i] = commonProperties.getProperty("serverIP" + (i + 1));
            serverPort[i] = Integer.parseInt(commonProperties.getProperty("serverPort" + (i + 1)));
        }

        // to open a socket at Client side to actively listen for data from servers
        int clientPort = Integer.parseInt(commonProperties.getProperty("clientPort"));
        ss = new ServerSocket(clientPort);

        // initialization the stemmer for english keywords
        Class stemClass = Class.forName("org.tartarus.snowball.ext.englishStemmer");
        stemmer = (SnowballStemmer) stemClass.newInstance();

        cleanUp();

        System.out.println("Number of thread:" + numThreads);
        System.out.println("serverVerification:" + serverVerification);
        System.out.println("clientVerification:" + clientVerification);
    }

    public static void main(String[] args) throws IOException, NoSuchAlgorithmException, ClassNotFoundException, InstantiationException, IllegalAccessException, InterruptedException {
        // to calculate the time
        Instant start, end;
        double totalTime;
        // to store the phase id
        int phase;
        // the number of times program was run for experiment
        int count = 0;
        // to store client/server program for experiment
        int type = 0;
        // fetching all the search keywords
        String fileName = "data/cleartext/keywords.txt";
        String[] keywords = Helper.readFile(fileName);

        initialization();

        // to iterate for the experiment run count
        for (int i = 0; i < Helper.getRunCount(); i++) {
            // request input from the client
            // the client id making the search for keyword
            System.out.println("Enter client id authorised to search the keyword!");
            clientId = console.next();
//            clientId = "1";
            // the keyword search by the client
            System.out.println("Enter a keyword to search!");
            searchKeyword = console.next();
//            searchKeyword = keywords[i];
//            searchKeyword = "jarnold";
            // to clean results folder from previous runs data
            Helper.cleanResultFolder();

            // phase 1
            phase = 1;
            cleanUpPhaseData(phase);
            System.out.println("Start of Phase 1.");
            System.out.println("---------------------------------------");
            start = Instant.now();
            phase1();
            end = Instant.now();
            totalTime = Duration.between(start, end).toMillis();
            Helper.printTimes(phase, null, null, removeTime, perServerTime, totalTime, count);
            System.out.println("End of Phase 1.");
            cleanUpPhaseData(phase);

            // phase 2
            phase = 2;
            cleanUpPhaseData(phase);
            System.out.println("Start of Phase 2.");
            System.out.println("---------------------------------------");
            start = Instant.now();
            phase2();
            end = Instant.now();
            totalTime = Duration.between(start, end).toMillis();
            Helper.printTimes(phase, null, null, removeTime, perServerTime, totalTime, count);
            System.out.println("End of Phase 2.");
            cleanUpPhaseData(phase);

            //phase 3
            phase=3;
            cleanUpPhaseData(phase);
            System.out.println("Start of Phase 3.");
            System.out.println("---------------------------------------");
            start = Instant.now();
            phase3();
            end = Instant.now();
            totalTime = Duration.between(start, end).toMillis();
            Helper.printTimes(phase, null, null, removeTime, perServerTime, totalTime, count);
            System.out.println("End of Phase 3.");
            cleanUpPhaseData(phase);

            count++;
        }
        System.out.println("Time taken on an average for over " + (Helper.getRunCount() - Helper.getBuffer()) + " round for each phase is below");
        Helper.timeTaken(type);
    }
}


