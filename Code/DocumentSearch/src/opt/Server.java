package src.opt;

import constants.Constant;
import utility.Helper;

import java.io.File;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.math.BigInteger;
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

public class Server {

    private static final Logger log = Logger.getLogger(Logger.GLOBAL_LOGGER_NAME);
    private static final int hashBlockCount = Constant.getHashBlockCount();
    private static final int hashBlockSize = Constant.getHashBlockSize();
    // the mod value
    private static final long modValue = Constant.getModParameter();
    // the mod value for BigInteger
    private static final BigInteger modValueBig = Constant.getModBigParameter();
    private static long[] result;
    private static int serverNumber;
    private static long seedServerRandomValue;
    private static ServerSocket ss;
    private static Socket socketClient;
    private static ObjectOutputStream outputStream;
    private static ObjectInputStream inputStream;
    private static Object objects;
    private static List<Object> objectsList;
    private static boolean serverVerification;
    private static BigInteger searchKeywordShare;
    private static int clientId;
    private static long[] searchKeywordVectorShare;
    private static int keywordCount;
    private static long[] randomSharesPhase1Sum;
    // to store number of files
    private static int fileCount;
    // to store the maximum length of a file
    private static int fileLength;
    // to store the maximum number of files a keyword can occur in
    private static long[][] fileVectorShare;
    // to store the result for phase1
    private static StringBuilder[] phase1Result;
    // to store the result for phase3
    private static long[][] phase3Result;
    private static BigInteger[] verificationForServer;
    // for phase 3 verification phase
    private static long[][][] verificationForServerThreadPhase3;
    private static long[][] fileIds;
    private static int numThreads;
    private static String stage;
    private static String stageLabel;
    private static ArrayList<Instant> removeTime;
    private static ArrayList<Instant> comTime = new ArrayList<>();
    private static ArrayList<Instant> waitTime = new ArrayList<>();
    private static ArrayList<Double> perServerTime;
    private static int fileRequestedCount;
    // to store the act table read from file
    private static BigInteger[][] act;
    // to store the file DS read from file
    private static long[][] files;
    // to store the file DS read from file
    private static long[][] fileKeyword;
    private static long[][][] phase3ResultThread;
    // to store the server port
    private static int serverPort;
    // to store the client IP
    private static String clientIP;
    // to store the client port
    private static int clientPort;
    private static long[] phase2AddrResult;
    private static long[] phase2AddrResultSlice;
    private static long[][] addr;
    private static long[] optInv;
    private static long[][] optIndexShare;
    private static long[] optInvRowVec;
    private static long[] optInvColVec;
    private static long[] phase2OptInvResult;
    private static long[][] optInvServerVerification;
    private static long[][] optInvHashValues;
    private static int nextServerPort1;
    private static String nextServerIp1;
    private static int nextServerPort2;
    private static String nextServerIp2;
    private static String nextServerIp3;
    private static int nextServerPort3;
    private static int serverCount;
    private static int checkpoint1;
    private static long[][] objectsReceivedLong1D;
    private static long[][][] serverVerificationShares2D;
    private static long[] permutReorgVector;
    private static String type;
    private static int optCol;
    private static int optRow;
    // to stores server shares as long values for 1D array
    private static String[][] objectsReceivedString1D;
    // to stores server shares as long values for 2D array
    private static String[][][] objectsReceivedString2D;
    private static long[][] randomSharesPhase2;
    private static long[] randomSharesPhase2Sum;

    /**
     * to send random shares to neighbouring server
     *
     * @param randomShares the random number shares
     * @throws IOException
     * @throws ClassNotFoundException
     */
    public static void helper(long[][] randomShares, int serverCount, int phase) throws IOException, ClassNotFoundException {
        if (phase == 1) {
            if (serverCount == 3) {
                // first 1 sends to 2 and 3, then 3 to 1 and 2, then 2 to 3 and 1,
                if (serverNumber == 1) {
                    sendToServer(randomShares[0], nextServerIp1, nextServerPort1);
                    sendToServer(randomShares[1], nextServerIp2, nextServerPort2);
                    waitTime = new ArrayList<>();
                    startServerMulti();
                    waitTime = new ArrayList<>();
                    type = "1D";
                    objectsReceivedLong1D = new long[serverCount][];
                    readObjectsAsLong(type);
                    cleanUp();
                } else if (serverNumber == 2) {
                    // receiving verification result from 2 servers
                    startServerMulti();
                    waitTime = new ArrayList<>();
                    // sending verification result to 2 servers
                    sendToServer(randomShares[1], nextServerIp1, nextServerPort1);
                    sendToServer(randomShares[2], nextServerIp2, nextServerPort2);
                    waitTime = new ArrayList<>();
                    type = "1D";
                    objectsReceivedLong1D = new long[serverCount][];
                    readObjectsAsLong(type);
                    cleanUp();
                } else {
                    // receiving verification result from 1 servers
                    startServerMulti();
                    waitTime = new ArrayList<>();
                    // sending verification result to 2 servers
                    sendToServer(randomShares[2], nextServerIp1, nextServerPort1);
                    sendToServer(randomShares[0], nextServerIp2, nextServerPort2);
                    waitTime = new ArrayList<>();
                    objectsReceivedLong1D = new long[serverCount][];
                    type = "1D";
                    readObjectsAsLong(type);
                    cleanUp();
                    // receiving verification result from 1 servers
                    startServerMulti();
                    waitTime = new ArrayList<>();
                    type = "1D";
                    readObjectsAsLong(type);
                    cleanUp();
                }
            } else {
                // first 1 sends to 2,3,4, then 3 to 1,2,4, then 4 sends to 1,2,3, then 2 to 3,1,4,
                if (serverNumber == 1) {
                    sendToServer(randomShares[0], nextServerIp1, nextServerPort1);
                    sendToServer(randomShares[1], nextServerIp2, nextServerPort2);
                    sendToServer(randomShares[3], nextServerIp3, nextServerPort3);
                    waitTime = new ArrayList<>();
                    startServerMulti(0);
                    waitTime = new ArrayList<>();
                    type = "1D";
                    objectsReceivedLong1D = new long[serverCount][];
                    readObjectsAsLong(type);
                    cleanUp();
                } else if (serverNumber == 2) {
                    // receiving verification result from 2 servers
                    startServerMulti(0);
                    waitTime = new ArrayList<>();
                    // sending verification result to 2 servers
                    sendToServer(randomShares[1], nextServerIp1, nextServerPort1);
                    sendToServer(randomShares[2], nextServerIp2, nextServerPort2);
                    sendToServer(randomShares[3], nextServerIp3, nextServerPort3);
                    waitTime = new ArrayList<>();
                    type = "1D";
                    objectsReceivedLong1D = new long[serverCount][];
                    readObjectsAsLong(type);
                    cleanUp();
                } else if (serverNumber == 3) {
                    // receiving verification result from 1 servers
                    startServerMulti(1);
                    waitTime = new ArrayList<>();
                    // sending verification result to 2 servers
                    sendToServer(randomShares[2], nextServerIp1, nextServerPort1);
                    sendToServer(randomShares[0], nextServerIp2, nextServerPort2);
                    sendToServer(randomShares[3], nextServerIp3, nextServerPort3);
                    waitTime = new ArrayList<>();
                    objectsReceivedLong1D = new long[serverCount][];
                    type = "1D";
                    readObjectsAsLong(type);
                    cleanUp();
                    // receiving verification result from 1 servers
                    startServerMulti(2);
                    waitTime = new ArrayList<>();
                    type = "1D";
                    readObjectsAsLong(type);
                    cleanUp();
                } else if (serverNumber == 4) {
                    // receiving verification result from 1 servers
                    startServerMulti(2);
                    waitTime = new ArrayList<>();
                    // sending verification result to 2 servers
                    sendToServer(randomShares[2], nextServerIp1, nextServerPort1);
                    sendToServer(randomShares[0], nextServerIp2, nextServerPort2);
                    sendToServer(randomShares[1], nextServerIp3, nextServerPort3);
                    waitTime = new ArrayList<>();
                    objectsReceivedLong1D = new long[serverCount][];
                    type = "1D";
                    readObjectsAsLong(type);
                    cleanUp();
                    // receiving verification result from 1 servers
                    startServerMulti(1);
                    waitTime = new ArrayList<>();
                    type = "1D";
                    readObjectsAsLong(type);
                    cleanUp();
                }
            }
        } else if (phase == 2) {
            // send random number shares to servers
            if (serverNumber == 1) {
                sendToServer(randomSharesPhase2[1], nextServerIp1, nextServerPort1);
                sendToServer(randomSharesPhase2[2], nextServerIp2, nextServerPort2);
                waitTime = new ArrayList<>();
                startServerMulti();
                waitTime = new ArrayList<>();
                type = "1D";
                objectsReceivedLong1D = new long[serverCount][];
                readObjectsAsLong(type);
                cleanUp();
            } else if (serverNumber == 2) {
                startServerMulti();
                waitTime = new ArrayList<>();
                sendToServer(randomSharesPhase2[2], nextServerIp1, nextServerPort1);
                sendToServer(randomSharesPhase2[0], nextServerIp2, nextServerPort2);
                waitTime = new ArrayList<>();
                type = "1D";
                objectsReceivedLong1D = new long[serverCount][];
                readObjectsAsLong(type);
                cleanUp();
            } else {
                startServerMulti();
                waitTime = new ArrayList<>();
                sendToServer(randomSharesPhase2[0], nextServerIp1, nextServerPort1);
                sendToServer(randomSharesPhase2[1], nextServerIp2, nextServerPort2);
                waitTime = new ArrayList<>();
                objectsReceivedLong1D = new long[serverCount][];
                type = "1D";
                readObjectsAsLong(type);
                cleanUp();
                startServerMulti();
                waitTime = new ArrayList<>();
                type = "1D";
                readObjectsAsLong(type);
                cleanUp();
            }
        }
    }

    /**
     * Create random number's shares
     *
     * @throws IOException
     * @throws ClassNotFoundException
     */
    public static void createRandomShares(int serverCount, int phase) throws IOException, ClassNotFoundException {
        if (phase == 1) {
            long prgServer;
            long[] shares;
            Random seedGenerator = new Random(seedServerRandomValue);
            long[][] randomSharesPhase1 = new long[serverCount][keywordCount + 1]; // one for server label
            for (int i = 0; i < keywordCount; i++) {
                prgServer = seedGenerator.nextLong(Constant.getMaxRandomBound() -
                        Constant.getMinRandomBound()) + Constant.getMinRandomBound();
                shares = shamirSecretShares(prgServer, serverCount);
                for (int j = 0; j < shares.length; j++) {
                    randomSharesPhase1[j][i] = shares[j];
                }
            }
            for (int j = 0; j < serverCount; j++) {
                randomSharesPhase1[j][keywordCount] = serverNumber;
            }
            helper(randomSharesPhase1, serverCount, phase);
            // sum all the random shares received from the neighbouring servers
            randomSharesPhase1Sum = new long[keywordCount];
            if (serverCount == 3) {
                for (int k = 0; k < keywordCount; k++) {
                    prgServer = 0;
                    for (int j = 0; j < serverCount; j++) {
                        if (j != (serverNumber - 1)) {
                            prgServer = (prgServer + objectsReceivedLong1D[j][k]) % modValue;
                        } else {
                            prgServer = (prgServer + randomSharesPhase1[Math.floorMod(serverNumber - 2, serverCount)][k]) % modValue;
                        }
                    }
                    randomSharesPhase1Sum[k] = prgServer;
                }
            } else {
                if (serverNumber <= 3) {
                    for (int k = 0; k < keywordCount; k++) {
                        prgServer = 0;
                        for (int j = 0; j < serverCount; j++) {
                            if (j != (serverNumber - 1)) {
                                prgServer = (prgServer + objectsReceivedLong1D[j][k]) % modValue;
                            } else {
                                prgServer = (prgServer + randomSharesPhase1[Math.floorMod(serverNumber - 2, 3)][k]) % modValue;
                            }
                        }
                        randomSharesPhase1Sum[k] = prgServer;
                    }
                } else {
                    for (int k = 0; k < keywordCount; k++) {
                        prgServer = 0;
                        for (int j = 0; j < serverCount; j++) {
                            if (j != (serverNumber - 1)) {
                                prgServer = (prgServer + objectsReceivedLong1D[j][k]) % modValue;
                            } else {
                                prgServer = (prgServer + randomSharesPhase1[3][k]) % modValue;
                            }
                        }
                        randomSharesPhase1Sum[k] = prgServer;
                    }
                }

            }
        } else if (phase == 2) {
            // create random numbers sha
            Random seedGenerator = new Random(seedServerRandomValue);
            randomSharesPhase2 = new long[serverCount][optCol + 1];
            randomSharesPhase2Sum = new long[optCol];
            long[] shares;
            long prgServer;
            for (int i = 0; i < optCol; i++) {
                prgServer = (seedGenerator.nextLong(Constant.getMaxRandomBound() -
                        Constant.getMinRandomBound()) + Constant.getMinRandomBound());
                shares = shamirSecretShares(prgServer, serverCount);
                for (int j = 0; j < shares.length; j++) {
                    randomSharesPhase2[j][i] = shares[j];
                }
            }
            for (int j = 0; j < serverCount; j++) {
                randomSharesPhase2[j][optCol] = serverNumber;
            }
            helper(randomSharesPhase2, serverCount, phase);
            for (int i = 0; i < optCol; i++) {
                prgServer = 0;
                for (int j = 0; j < serverCount; j++) {
                    if (j != serverNumber - 1) {
                        prgServer = (prgServer + objectsReceivedLong1D[j][i]) % modValue;
                    } else {
                        prgServer = (prgServer + randomSharesPhase2[j][i]) % modValue;
                    }
                }
                randomSharesPhase2Sum[i] = prgServer;
            }
        }
    }

    /**
     * Create share for secret value as long
     *
     * @param secret      the secret value as long
     * @param serverCount the number of servers for which shares are to be created
     * @return the share of the secret value as long is returned for given number of server as servercount
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
     * To read values from objects
     *
     * @param type the type of object as 1D or 2D
     */
    public static void readObjectsAsLong(String type) {
        if (type.equals("1D")) {
            for (int i = 0; i < objectsList.size(); i++) {
                int temp = (int) (((long[]) objectsList.get(i))[((long[]) objectsList.get(i)).length - 1]);
                objectsReceivedLong1D[temp - 1] = ((long[]) objectsList.get(i));
            }
        } else if (type.equals("2D")) {
            for (int i = 0; i < objectsList.size(); i++) {
                int temp = (int) (((long[][]) objectsList.get(i))[((long[][]) objectsList.get(i)).length - 1][0]);
                serverVerificationShares2D[temp - 1] = ((long[][]) objectsList.get(i));
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
            for (int i = 0; i < objectsList.size(); i++) {
                String objectRead = new String((byte[]) objectsList.get(i), StandardCharsets.UTF_8);
                int temp = objectRead.charAt(objectRead.length() - 1) - '0';
                objectsReceivedString1D[temp - 1] = objectRead.split(",");
            }
        } else if (type.equals("2D")) {
            for (int i = 0; i < objectsList.size(); i++) {
                byte[][] data = (byte[][]) objectsList.get(i);
                int temp = new String(data[data.length - 1], StandardCharsets.UTF_8).charAt(0) - '0';
                objectsReceivedString2D[temp - 1] = new String[fileRequestedCount][];
                for (int j = 0; j < data.length - 1; j++) {
                    objectsReceivedString2D[temp - 1][j] = new String(data[j], StandardCharsets.UTF_8).split(",");
                }
            }
        }

    }

    /**
     * to send data to client
     * @param data
     */
    public static void sendToClient(Object data) {
        try {
            waitTime.add(Instant.now());
            socketClient = new Socket(clientIP, clientPort);
            outputStream = new ObjectOutputStream(socketClient.getOutputStream());
            waitTime.add(Instant.now());
            outputStream.writeObject(data);
        } catch (IOException ex) {
            log.log(Level.SEVERE, ex.getMessage());
        }
    }

    /**
     * to send data to a server
     *
     * @param data       the data
     * @param serverIp   the server IP
     * @param serverPort the server port
     */
    public static void sendToServer(Object data, String serverIp, int serverPort) {
        try {
            waitTime.add(Instant.now());
            socketClient = new Socket(serverIp, serverPort);
            outputStream = new ObjectOutputStream(socketClient.getOutputStream());
            waitTime.add(Instant.now());
            outputStream.writeObject(data);
        } catch (IOException ex) {
            log.log(Level.SEVERE, ex.getMessage());
        }
    }

    /**
     * to start server to listen for multiple items
     *
     * @throws IOException
     * @throws ClassNotFoundException
     */
    public static void startServerMulti() throws IOException, ClassNotFoundException {
        if (serverNumber != 3) { // server 1 and 2 will wait for two items
            while (objectsList.size() != (serverCount - 1)) {
                //Reading data from the server
                waitTime.add(Instant.now());
                socketClient = ss.accept();
                inputStream = new ObjectInputStream(socketClient.getInputStream());
                waitTime.add(Instant.now());
                objectsList.add(inputStream.readObject());
            }
        } else { // server 3 will wait for 1 items
            while (objectsList.size() != 1) {
                //Reading data from the server
                waitTime.add(Instant.now());
                socketClient = ss.accept();
                inputStream = new ObjectInputStream(socketClient.getInputStream());
                waitTime.add(Instant.now());
                objectsList.add(inputStream.readObject());
            }
        }
    }

    /**
     * to start server to listen for multiple items
     *
     * @throws IOException
     * @throws ClassNotFoundException
     */
    public static void startServerMulti(int x) throws IOException, ClassNotFoundException {
        if (serverNumber <= 2) {
            while (objectsList.size() != (serverCount - 1)) {
                //Reading data from the server
                waitTime.add(Instant.now());
                socketClient = ss.accept();
                inputStream = new ObjectInputStream(socketClient.getInputStream());
                waitTime.add(Instant.now());
                objectsList.add(inputStream.readObject());
            }
        } else if (serverNumber == 3) {
            while (objectsList.size() != x) {
                //Reading data from the server
                waitTime.add(Instant.now());
                socketClient = ss.accept();
                inputStream = new ObjectInputStream(socketClient.getInputStream());
                waitTime.add(Instant.now());
                objectsList.add(inputStream.readObject());
            }
        } else if (serverNumber == 4) {
            while (objectsList.size() != x) {
                //Reading data from the server
                waitTime.add(Instant.now());
                socketClient = ss.accept();
                inputStream = new ObjectInputStream(socketClient.getInputStream());
                waitTime.add(Instant.now());
                objectsList.add(inputStream.readObject());
            }
        }
    }

    /**
     * to start server to listen to client
     */
    public static void startServer() {
        try {
            System.out.println("Server" + serverNumber + " Listening........");
            waitTime.add(Instant.now());
            Socket socketServer = ss.accept();
            inputStream = new ObjectInputStream(socketServer.getInputStream());
            waitTime.add(Instant.now());
//            System.out.println(objects);
            objects = inputStream.readObject();
//            System.out.println(objects);
        } catch (IOException | ClassNotFoundException ex) {
            log.log(Level.SEVERE, ex.getMessage());
        }
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
            } else if (stage.equals("2")) {
                if (stageLabel.equals("1")) {
                    task21(threadNum);
                } else if (stageLabel.equals("2")) {
                    try {
                        task22(threadNum);
                    } catch (NoSuchAlgorithmException e) {
                        throw new RuntimeException(e);
                    }
                } else if (stageLabel.equals("3")) {
                    task23(threadNum);
                } else if (stageLabel.equals("4")) {
                    task24(threadNum);
                } else if (stageLabel.equals("5")) {
                    task25(threadNum);
                }
            } else if (stage.equals("3")) {
                if (stageLabel.equals("1")) {
                    task31(threadNum);
                } else if (stageLabel.equals("2")) {
                    task32(threadNum);
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
        // Create threads and add them to threadlist
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
     * To interpolate share values to retrieve secret
     *
     * @param share the shares
     * @return the cleartext/interpolated value
     */
    public static BigInteger lagrangeInterpolation(BigInteger share[]) {
        return switch (share.length) {
            case 2 -> ((BigInteger.valueOf(2).multiply(share[0])).mod(modValueBig)
                    .subtract(share[1])).mod(modValueBig);
            case 3 -> (((BigInteger.valueOf(3)
                    .multiply(share[0])).mod(modValueBig).subtract((BigInteger.valueOf(3)
                    .multiply(share[1])).mod(modValueBig))).mod(modValueBig).add(share[2])).mod(modValueBig);
            default -> throw new IllegalStateException("Unexpected value: " + share.length);
        };
    }

    /**
     * to compute hash digest of each cell of inverted index
     *
     * @throws NoSuchAlgorithmException
     */
    public static void calOptInvHashValues() throws NoSuchAlgorithmException {
        optInvHashValues = new long[optInv.length][hashBlockCount];
        for (int i = 0; i < optInv.length; i++) {
            String digest = hashDigest(String.valueOf(i));
            int m = 0, h = 0;
            while (m < digest.length()) {
                int end = m + hashBlockSize;
                if (end > digest.length())
                    end = digest.length();
                optInvHashValues[i][h] = Long.parseLong(digest.substring(m, end));
                h++;
                m = m + hashBlockSize;
            }
        }
    }

    /**
     * To perform cleanup tasks in course of program execution
     */
    public static void cleanUp() {
        // re-initializing the list to hold values received from server
        objectsList = Collections.synchronizedList(new ArrayList<>());
    }

    /**
     * To perform cleanup tasks in course of program execution
     */
    public static void cleanUpPhaseData(int phase) {
        switch (phase) {
            case 1 -> {
                phase1Result = new StringBuilder[numThreads];
                perServerTime = new ArrayList<>();
                removeTime = new ArrayList<>();
                waitTime = new ArrayList<>();
                comTime = new ArrayList<>();
            }
            case 2 -> {
                searchKeywordVectorShare = null;
                optIndexShare = null;
                optInvRowVec = null;
                optInvColVec = null;
                phase2AddrResult = new long[addr[0].length];
                phase2AddrResultSlice = new long[addr[0].length - hashBlockCount + 1];
                optInvServerVerification = new long[optCol][hashBlockCount];
                perServerTime = new ArrayList<>();
                removeTime = new ArrayList<>();
                waitTime = new ArrayList<>();
                comTime = new ArrayList<>();
            }
            case 3 -> {
                perServerTime = new ArrayList<>();
                removeTime = new ArrayList<>();
                waitTime = new ArrayList<>();
                comTime = new ArrayList<>();
                fileVectorShare = null;
                verificationForServerThreadPhase3 = null;
            }
        }
    }

    /**
     * read all tables ACT, ADDR, inverted Index, Files, Files keyword
     *
     * @throws IOException
     * @throws NoSuchAlgorithmException
     */
    public static void readDataStructures() throws IOException, NoSuchAlgorithmException {
        String actName;
        File file;
        if (serverNumber <= 3) {
            serverCount = 3;
            actName = "act" + (Math.floorMod(serverNumber - 2, serverCount) + 1) + ".txt";
            file = new File("data/share/" + actName);
            act = Helper.readFileAsBigInt(file);
            String addrName = "addr" + (Math.floorMod(serverNumber - 2, serverCount) + 1) + ".txt";
            file = new File("data/share/" + addrName);
            addr = Helper.readFileAsLong(file);
            String optInvName = "invertedIndexOpt" + serverNumber + ".txt";
            file = new File("data/share/" + optInvName);
            optInv = Helper.readFileAs1D(file);
            String fileName = "file" + (Math.floorMod(serverNumber - 2, serverCount) + 1) + ".txt";
            file = new File("data/share/" + fileName);
            files = Helper.readFileAsLong(file);
            String fileKeywordName = "fileKeyword" + (Math.floorMod(serverNumber - 2, serverCount) + 1) + ".txt";
            file = new File("data/share/" + fileKeywordName);
            fileKeyword = Helper.readFileAsLong(file);

            keywordCount = act[0].length;
            fileCount = files.length - 1;

            calOptInvHashValues();
        } else {
            actName = "act4.txt";
            file = new File("data/share/" + actName);
            act = Helper.readFileAsBigInt(file);
            keywordCount = act[0].length;
        }
    }

    /**
     * to send IPs of neighboring server
     */
    public static void setNeighbourIP(Properties properties) {
        switch (serverNumber) {
            case 1:
                serverPort = Integer.parseInt(properties.getProperty("serverPort1"));
                nextServerIp1 = properties.getProperty("serverIP2");
                nextServerPort1 = Integer.parseInt(properties.getProperty("serverPort2"));
                nextServerIp2 = properties.getProperty("serverIP3");
                nextServerPort2 = Integer.parseInt(properties.getProperty("serverPort3"));
                nextServerIp3 = properties.getProperty("serverIP4");
                nextServerPort3 = Integer.parseInt(properties.getProperty("serverPort4"));
                break;
            case 2:
                serverPort = Integer.parseInt(properties.getProperty("serverPort2"));
                nextServerIp1 = properties.getProperty("serverIP3");
                nextServerPort1 = Integer.parseInt(properties.getProperty("serverPort3"));
                nextServerIp2 = properties.getProperty("serverIP1");
                nextServerPort2 = Integer.parseInt(properties.getProperty("serverPort1"));
                nextServerIp3 = properties.getProperty("serverIP4");
                nextServerPort3 = Integer.parseInt(properties.getProperty("serverPort4"));
                break;
            case 3:
                serverPort = Integer.parseInt(properties.getProperty("serverPort3"));
                nextServerIp1 = properties.getProperty("serverIP1");
                nextServerPort1 = Integer.parseInt(properties.getProperty("serverPort1"));
                nextServerIp2 = properties.getProperty("serverIP2");
                nextServerPort2 = Integer.parseInt(properties.getProperty("serverPort2"));
                nextServerIp3 = properties.getProperty("serverIP4");
                nextServerPort3 = Integer.parseInt(properties.getProperty("serverPort4"));
                break;
            case 4:
                serverPort = Integer.parseInt(properties.getProperty("serverPort4"));
                nextServerIp1 = properties.getProperty("serverIP1");
                nextServerPort1 = Integer.parseInt(properties.getProperty("serverPort1"));
                nextServerIp2 = properties.getProperty("serverIP2");
                nextServerPort2 = Integer.parseInt(properties.getProperty("serverPort2"));
                nextServerIp3 = properties.getProperty("serverIP3");
                nextServerPort3 = Integer.parseInt(properties.getProperty("serverPort3"));
                break;
        }
    }

    /**
     * share data with neighbouring servers
     *
     * @param data the data to be shared
     * @throws IOException
     * @throws ClassNotFoundException
     */
    public static void communicateAllServers(long[] data, boolean temp) {
        if (serverNumber == 1) {
            // sending rotated own vector to next server data
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            sendToServer(data, nextServerIp1, nextServerPort1);
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());
            // received the rotated data from previous server
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            startServer();
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());
        } else {
            // received the rotated data from previous server
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            startServer();
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());
            // sending rotated own vector to next server data to the client
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            sendToServer(data, nextServerIp1, nextServerPort1);
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());
        }
    }

    /**
     * share data with neighbouring servers
     *
     * @param data the data to be shared
     * @throws IOException
     * @throws ClassNotFoundException
     */
    public static void communicateAllServers(long[][] data) throws IOException, ClassNotFoundException {
        if (serverNumber == 1) {
            // sending verification result to 2 servers
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            sendToServer(data, nextServerIp1, nextServerPort1);
            sendToServer(data, nextServerIp2, nextServerPort2);
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 2));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());
            // receiving verification result from 2 servers
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            startServerMulti();
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 2));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());
            serverVerificationShares2D = new long[serverCount][][];
            type = "2D";
            readObjectsAsLong(type);
            cleanUp();
        } else if (serverNumber == 2) {
            // receiving verification result from 2 servers
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            startServerMulti();
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 2));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());
            // sending verification result to 2 servers
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            sendToServer(data, nextServerIp1, nextServerPort1);
            sendToServer(data, nextServerIp2, nextServerPort2);
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 2));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());
            serverVerificationShares2D = new long[serverCount][][];
            type = "2D";
            readObjectsAsLong(type);
            cleanUp();
        } else {
            // receiving verification result from 1 servers
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            startServerMulti();
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());
            // sending verification result to 2 servers
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            sendToServer(data, nextServerIp1, nextServerPort1);
            sendToServer(data, nextServerIp2, nextServerPort2);
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 2));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());
            serverVerificationShares2D = new long[serverCount][][];
            type = "2D";
            readObjectsAsLong(type);
            cleanUp();
            // receiving verification result from 1 servers
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            startServerMulti();
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());
            type = "2D";
            readObjectsAsLong(type);
            cleanUp();
        }

    }

    /**
     * share data with neighbouring servers
     *
     * @param data the data to be shared
     * @throws IOException
     * @throws ClassNotFoundException
     */
    public static void communicateAllServers(long[] data, int neighbours) throws IOException, ClassNotFoundException {
        if (neighbours == 1) {
            if (serverNumber == 1) {
                removeTime.add(Instant.now());
                comTime.add(Instant.now());
                sendToServer(data, nextServerIp2, nextServerPort2);
                comTime.add(Instant.now());
                perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
                comTime = new ArrayList<>();
                waitTime = new ArrayList<>();
                removeTime.add(Instant.now());
                removeTime.add(Instant.now());
                comTime.add(Instant.now());
                startServer();
                comTime.add(Instant.now());
                perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
                comTime = new ArrayList<>();
                waitTime = new ArrayList<>();
                removeTime.add(Instant.now());
            } else {
                removeTime.add(Instant.now());
                comTime.add(Instant.now());
                startServer();
                comTime.add(Instant.now());
                perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
                comTime = new ArrayList<>();
                waitTime = new ArrayList<>();
                removeTime.add(Instant.now());
                removeTime.add(Instant.now());
                comTime.add(Instant.now());
                sendToServer(data, nextServerIp2, nextServerPort2);
                comTime.add(Instant.now());
                perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
                comTime = new ArrayList<>();
                waitTime = new ArrayList<>();
                removeTime.add(Instant.now());
            }

        } else if (neighbours == 2) {
            if (serverNumber == 1) {
                // sending verification result to 2 servers
                removeTime.add(Instant.now());
                comTime.add(Instant.now());
                sendToServer(data, nextServerIp1, nextServerPort1);
                sendToServer(data, nextServerIp2, nextServerPort2);
                comTime.add(Instant.now());
                perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 2));
                comTime = new ArrayList<>();
                waitTime = new ArrayList<>();
                removeTime.add(Instant.now());
                // receiving verification result from 2 servers
                removeTime.add(Instant.now());
                comTime.add(Instant.now());
                startServerMulti();
                comTime.add(Instant.now());
                perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 2));
                comTime = new ArrayList<>();
                waitTime = new ArrayList<>();
                removeTime.add(Instant.now());
                type = "1D";
                objectsReceivedLong1D = new long[serverCount][];
                readObjectsAsLong(type);
                cleanUp();
            } else if (serverNumber == 2) {
                // receiving verification result from 2 servers
                removeTime.add(Instant.now());
                comTime.add(Instant.now());
                startServerMulti();
                comTime.add(Instant.now());
                perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 2));
                comTime = new ArrayList<>();
                waitTime = new ArrayList<>();
                removeTime.add(Instant.now());
                // sending verification result to 2 servers
                removeTime.add(Instant.now());
                comTime.add(Instant.now());
                sendToServer(data, nextServerIp1, nextServerPort1);
                sendToServer(data, nextServerIp2, nextServerPort2);
                comTime.add(Instant.now());
                perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 2));
                comTime = new ArrayList<>();
                waitTime = new ArrayList<>();
                removeTime.add(Instant.now());
                type = "1D";
                objectsReceivedLong1D = new long[serverCount][];
                readObjectsAsLong(type);
                cleanUp();
            } else {
                // receiving verification result from 1 servers
                removeTime.add(Instant.now());
                comTime.add(Instant.now());
                startServerMulti();
                comTime.add(Instant.now());
                perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
                comTime = new ArrayList<>();
                waitTime = new ArrayList<>();
                removeTime.add(Instant.now());
                // sending verification result to 2 servers
                removeTime.add(Instant.now());
                comTime.add(Instant.now());
                sendToServer(data, nextServerIp1, nextServerPort1);
                sendToServer(data, nextServerIp2, nextServerPort2);
                comTime.add(Instant.now());
                perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 2));
                comTime = new ArrayList<>();
                waitTime = new ArrayList<>();
                removeTime.add(Instant.now());
                objectsReceivedLong1D = new long[serverCount][];
                type = "1D";
                readObjectsAsLong(type);
                cleanUp();
                // receiving verification result from 1 servers
                removeTime.add(Instant.now());
                comTime.add(Instant.now());
                startServerMulti();
                comTime.add(Instant.now());
                perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
                comTime = new ArrayList<>();
                waitTime = new ArrayList<>();
                removeTime.add(Instant.now());
                type = "1D";
                readObjectsAsLong(type);
                cleanUp();
            }
        }
    }

    /**
     * share data with neighbouring servers
     *
     * @param data the data to be shared
     * @throws IOException
     * @throws ClassNotFoundException
     */
    public static void communicateAllServers(byte[] data) throws IOException, ClassNotFoundException {
        // first 1 sends to 2 and 3, then 3 to 1 and 2, then 2 to 3 and 1,
        if (serverNumber == 1) {
            // sending verification data to two servers
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            sendToServer(data, nextServerIp1, nextServerPort1);
            sendToServer(data, nextServerIp2, nextServerPort2);
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 2));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());
            // receiving verification data from two servers
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            startServerMulti();
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 2));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());
            type = "1D";
            objectsReceivedString1D = new String[serverCount][];
            readObjectsAsString(type);
            cleanUp();
        } else if (serverNumber == 2) {
            // receiving verification data from two servers
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            startServerMulti();
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 2));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());
            type = "1D";
            objectsReceivedString1D = new String[serverCount][];
            readObjectsAsString(type);
            cleanUp();
            // sending verification data to two servers
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            sendToServer(data, nextServerIp1, nextServerPort1);
            sendToServer(data, nextServerIp2, nextServerPort2);
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 2));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());
        } else {
            // receiving verification data from two servers
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            startServerMulti();
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());
            // sending verification data to two servers
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            sendToServer(data, nextServerIp1, nextServerPort1);
            sendToServer(data, nextServerIp2, nextServerPort2);
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 2));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());
            type = "1D";
            objectsReceivedString1D = new String[serverCount][];
            readObjectsAsString(type);
            cleanUp();
            // receiving verification data from two servers
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            startServerMulti();
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());
            type = "1D";
            readObjectsAsString(type);
            cleanUp();
        }
    }

    /**
     * share data with neighbouring servers
     *
     * @param data the data to be shared
     * @throws IOException
     * @throws ClassNotFoundException
     */
    public static void communicateAllServers(byte[][] data) throws IOException, ClassNotFoundException {
        // first 1 sends to 2 and 3, then 3 to 1 and 2, then 2 to 3 and 1,
        if (serverNumber == 1) {
            // sending verification result to 2 servers
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            sendToServer(data, nextServerIp1, nextServerPort1);
            sendToServer(data, nextServerIp2, nextServerPort2);
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 2));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());
            // receiving verification result from 2 servers
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            startServerMulti();
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 2));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());
            objectsReceivedString2D = new String[serverCount][][];
            type = "2D";
            readObjectsAsString(type);
            cleanUp();

        } else if (serverNumber == 2) {
            // receiving verification result from 2 servers
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            startServerMulti();
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 2));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());
            // sending verification result to 2 servers
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            sendToServer(data, nextServerIp1, nextServerPort1);
            sendToServer(data, nextServerIp2, nextServerPort2);
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 2));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());
            objectsReceivedString2D = new String[serverCount][][];
            type = "2D";
            readObjectsAsString(type);
            cleanUp();
        } else {
            // receiving verification result from 1 servers
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            startServerMulti();
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());
            // sending verification result to 2 servers
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            sendToServer(data, nextServerIp1, nextServerPort1);
            sendToServer(data, nextServerIp2, nextServerPort2);
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 2));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());
            objectsReceivedString2D = new String[serverCount][][];
            type = "2D";
            readObjectsAsString(type);
            cleanUp();
            // receiving verification result from 1 servers
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            startServerMulti();
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());
            type = "2D";
            readObjectsAsString(type);
            cleanUp();
        }
    }

    /**
     * performs dot product between file keyword matrix and file vector , file data matrix and file vector
     * multithreaded across number of files
     *
     * @param threadNum
     */
    public static void task31(int threadNum) {
        int batchSize = (int) Math.ceil((fileCount + 1) / (double) numThreads);
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;
        if (end > (fileCount + 1)) {
            end = (fileCount + 1);
        }

        for (int i = 0; i < fileRequestedCount; i++) {
            for (int j = start; j < end; j++) {
                long[] temp = fileKeyword[j];
//                System.out.println("j:"+j);
//                System.out.println("k:"+temp.length);
//                System.out.println(verificationForServerThreadPhase3.length);
//                System.out.println(verificationForServerThreadPhase3[0].length);
//                System.out.println(verificationForServerThreadPhase3[0][0].length);

                for (int k = 0; k < temp.length; k++) {
                    verificationForServerThreadPhase3[i][threadNum - 1][k] = (verificationForServerThreadPhase3[i][threadNum - 1][k]
                            + (temp[k] * fileVectorShare[i][j]) % modValue) % modValue;
                }
                temp = files[i];
                for (int k = 0; k < temp.length; k++) {
                    phase3ResultThread[i][threadNum - 1][k] = (phase3ResultThread[i][threadNum - 1][k]
                            + (fileVectorShare[i][j] * temp[k]) % modValue) % modValue;
                }
            }
        }
    }

    /**
     * to aggregate the file content data across threads
     *
     * @param threadNum
     */
    public static void task32(int threadNum) {
        int batchSize = (int) Math.ceil((fileLength) / (double) numThreads);
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;

        if (end > (fileLength)) {
            end = (fileLength);
        }

        for (int i = 0; i < fileRequestedCount; i++) {
            for (int j = 0; j < numThreads; j++) {
                for (int k = start; k < end; k++) {
                    phase3Result[i][k] = (phase3Result[i][k] + phase3ResultThread[i][j][k]) % modValue;
                }
            }
        }
    }

    /**
     * to rotate the vector with given permutation
     *
     * @param direction     the direction clock or anti-clock
     * @param rotationValue the value of rotation
     * @return the rotated array
     */
    public static long[] rotateVector(int direction, int rotationValue) {

        long[] rotatedVector = new long[permutReorgVector.length];

        if (direction == 1) { // left rotation

            for (int i = 0; i < permutReorgVector.length; i++) {
                int index = Math.floorMod((i - rotationValue), permutReorgVector.length);
                rotatedVector[index] = permutReorgVector[i];
            }
        } else if (direction == 0) { // right rotation
            for (int i = 0; i < permutReorgVector.length; i++) {
                int index = ((i + rotationValue) % permutReorgVector.length);
                rotatedVector[index] = permutReorgVector[i];
            }
        }
        return rotatedVector;
    }

    /**
     * perform test 3, 4, 5, 3= sum(arr), 4= sum(arr*arr), 5=4-3
     *
     * @param arr the input array
     * @return the reuslt of test 3, 4,5
     */
    public static long[][] binaryCompute(long[][] arr) {
        long[][] result = new long[arr.length + 1][3];
        for (int i = 0; i < arr.length; i++) {
            long resultA = 0, resultA2 = 0, temp;
            for (int j = 0; j < arr[0].length; j++) {
                temp = (fileVectorShare[i][j] * fileVectorShare[i][j]) % modValue;
                resultA = (resultA + fileVectorShare[i][j]) % modValue;
                resultA2 = (resultA2 + temp) % modValue;
                result[i][0] = resultA;
                result[i][1] = resultA2;
            }
            result[i][2] = fileIds[i][0];
        }
        result[result.length - 1][0] = Math.floorMod(serverNumber - 2, serverCount) + 1;
        return result;
    }

    /**
     * to interpolate the array
     *
     * @param neighbourData the data from neighbouring server
     * @param ownData       the data computed by individual server
     * @param serverCount   the number of servers
     * @return the interpolated value
     */
    public static long[][] interpolate(long[][][] neighbourData, long[][] ownData, int serverCount) {
        long[] shares = new long[serverCount];
        long[][] result = new long[ownData.length - 1][ownData[0].length];
        for (int i = 0; i < result.length; i++) {
            for (int j = 0; j < result[0].length; j++) {
                for (int l = 0; l < serverCount; l++) {
                    if (l == (Math.floorMod(serverNumber - 2, serverCount))) {
                        shares[l] = ownData[i][j];
                    } else {
                        shares[l] = neighbourData[l][i][j];
                    }
                }
                result[i][j] = lagrangeInterpolation(shares);
            }
        }
        return result;
    }

    /**
     * check the correctness of result
     *
     * @param data the matrix
     * @return result true or false
     */
    public static boolean checkBinary(long[][] data) {
        boolean flag = true;
        for (int i = 0; i < fileRequestedCount; i++) {
            if (data[i][0] != 1 || data[i][1] != 1 || data[i][2] != 0) {
                flag = false;
                break;
            }
        }
        return flag;
    }

    /**
     * to fetch the file given file id
     *
     * @throws IOException
     * @throws NoSuchAlgorithmException
     */
    public static void phase3() throws IOException, ClassNotFoundException, NoSuchAlgorithmException {
        stage = "3";

        // Waiting for client to send the data
        removeTime.add(Instant.now());
        comTime.add(Instant.now());
        startServer();
        comTime.add(Instant.now());
        perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
        comTime = new ArrayList<>();
        waitTime = new ArrayList<>();
        removeTime.add(Instant.now());
        // reading the data sent by client
        fileVectorShare = (long[][]) objects;
        fileRequestedCount = fileVectorShare.length - 1;
        // this is executed if client is unhappy with phase2 result send by server and wants to discontinue
        if (fileVectorShare[0][0] == 0) {
            log.info("Client wishes to discontinue the search.");
            return;
        }
        {
            // check if client has access to all the keyword of the file
            long[][] verificationForServer = new long[fileRequestedCount][1 + checkpoint1 + hashBlockCount]; // file id and keyword access test
            verificationForServerThreadPhase3 = new long[fileRequestedCount][numThreads][1 + checkpoint1 + hashBlockCount];
            fileIds = new long[fileRequestedCount + 1][1];
            // performing operation to get the file content and keyword list
            phase3Result = new long[fileRequestedCount + 1][fileLength]; // 1 more to store the label for server
            phase3ResultThread = new long[fileRequestedCount][numThreads][fileLength];
            stageLabel = "1";
            createThreads(stage, stageLabel);
            for (int i = 0; i < fileRequestedCount; i++) { // aggregate the value over thread
                for (int j = 0; j < numThreads; j++) {
                    for (int k = 0; k < checkpoint1 + 1 + hashBlockCount; k++) {
                        verificationForServer[i][k] = (verificationForServer[i][k] + verificationForServerThreadPhase3[i][j][k])
                                % modValue;
                    }
                }
                fileIds[i][0] = verificationForServer[i][0];
            }
            if (serverVerification) {
                int ownRotate = (int) fileVectorShare[fileRequestedCount][0];
                int otherRotate = (int) fileVectorShare[fileRequestedCount][1];
                // verify if the file id sent is correct
                permutReorgVector = new long[optCol];
                System.arraycopy(phase2OptInvResult, 0, permutReorgVector, 0, optCol);
                // rotate own vector
                permutReorgVector = rotateVector(0, ownRotate);
                communicateAllServers(permutReorgVector, true);
                permutReorgVector = (long[]) objects;
                // rotate data received from server
                permutReorgVector = rotateVector(1, otherRotate);
                // subtract the file ids to see if same file id is requested as in phase 2
                for (int i = 0; i < fileRequestedCount; i++) {
                    fileIds[i][0] = Math.floorMod((fileIds[i][0] -
                            permutReorgVector[i + hashBlockCount]), modValue);
                }
                long[][] ownData = binaryCompute(fileVectorShare);
                communicateAllServers(ownData);
                long[][] binaryResult = interpolate(serverVerificationShares2D, ownData, serverCount);
                if (!checkBinary(binaryResult)) {
                    log.info("Client has prepared an incorrect file vector");
                    removeTime.add(Instant.now());
                    comTime.add(Instant.now());
                    sendToClient(new long[][]{{0}, {serverNumber}});
                    comTime.add(Instant.now());
                    perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
                    comTime = new ArrayList<>();
                    waitTime = new ArrayList<>();
                    removeTime.add(Instant.now());
                    return;
                }
            }
            // to get the keyword for a file
            long[][] result1 = new long[fileRequestedCount + 1][checkpoint1];
            for (int i = 0; i < verificationForServer.length; i++) {
                for (int j = hashBlockCount + 1; j < verificationForServer[0].length; j++) {
                    result1[i][j - hashBlockCount - 1] = verificationForServer[i][j];
                }
            }
            // sending to client
            result1[result1.length - 1] = new long[]{Math.floorMod(serverNumber - 2, serverCount) + 1};
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            sendToClient(result1);
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());

            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            startServer();
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());
            // received keyword list in ACT size and reduced degrees
            long[][] received = (long[][]) objects;
            // check if the file keyword list returned is correct
            long[][] hashResult = new long[fileRequestedCount + 1][hashBlockCount];
            for (int i = 0; i < fileRequestedCount; i++) {
                long[] result = new long[hashBlockCount];
                for (int k = 0; k < keywordCount; k++) {
                    for (int j = 0; j < hashBlockCount; j++) {
                        result[j] = (result[j] + (received[i][k] * optInvHashValues[(k + 1)][j]) % modValue) % modValue;
                    }
                }
                for (int j = 0; j < hashBlockCount; j++) {
                    hashResult[i][j] = Math.floorMod((result[j] - verificationForServer[i][j + 1]), modValue);
                }
            }
            hashResult[hashResult.length - 1][0] = (Math.floorMod(serverNumber - 2, serverCount) + 1);
            //communicate to the servers
            communicateAllServers(hashResult);
            long[][] hashRes = interpolate(serverVerificationShares2D, hashResult, serverCount);
            for (int i = 0; i < fileRequestedCount; i++) {
                for (int j = 0; j < hashBlockCount; j++) {
                    if (hashRes[i][j] != 0) {
//                        log.info("Client has prepared an incorrect file vector");
//                        removeTime.add(Instant.now());
//                        comTime.add(Instant.now());
//                        sendToClient(new long[][]{{0}, {serverNumber}});
//                        comTime.add(Instant.now());
//                        perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
//                        comTime = new ArrayList<>();
//                        waitTime = new ArrayList<>();
//                        removeTime.add(Instant.now());
//                        return;
                    }
                }
            }
            // to check if client has access on all keywords
            BigInteger[] temp1 = new BigInteger[fileRequestedCount];
            for (int i = 0; i < fileRequestedCount; i++) {
                temp1[i] = BigInteger.valueOf(0);
            }
            for (int i = 0; i < fileRequestedCount; i++) {
                for (int k = 0; k < keywordCount; k++) {
                    temp1[i] = (temp1[i].add((BigInteger.valueOf(received[i][k])
                            .multiply(act[clientId][k])).mod(modValueBig))).mod(modValueBig);
                }
            }
            StringBuilder[] temp3 = new StringBuilder[fileRequestedCount];
            byte[][] result = new byte[fileRequestedCount + 1][];
            for (int i = 0; i < fileRequestedCount; i++) {
                temp3[i] = new StringBuilder("");
                temp3[i].append(temp1[i]).append(",");
                result[i] = temp3[i].toString().getBytes(StandardCharsets.UTF_8);
            }
            result[result.length - 1] = String.valueOf(Math.floorMod(serverNumber - 2, serverCount) + 1).getBytes(StandardCharsets.UTF_8);
            communicateAllServers(result);
            // check if the interpolated value yields desired value
            BigInteger[] testResultBig = new BigInteger[fileRequestedCount];
            BigInteger[] sharesBig = new BigInteger[serverCount];
            for (int i = 0; i < fileRequestedCount; i++) {
                for (int l = 0; l < serverCount; l++) {
                    if (l == (Math.floorMod(serverNumber - 2, serverCount))) {
                        sharesBig[l] = temp1[i];
                    } else {
                        sharesBig[l] = new BigInteger(objectsReceivedString2D[l][i][0]);
                    }
                }
                testResultBig[i] = lagrangeInterpolation(sharesBig);
            }
            boolean flag = true;
            for (int i = 0; i < fileRequestedCount; i++) {
                if (!(testResultBig[i].equals(BigInteger.valueOf(0)))) {
                    flag = false;
                    break;
                }
            }

            if (!flag) {
                log.info("Client has prepared an incorrect file vector Or has no access on all keywords of requested file.");
                removeTime.add(Instant.now());
                comTime.add(Instant.now());
                sendToClient(new long[][]{{0}, {serverNumber}});
                comTime.add(Instant.now());
                perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
                comTime = new ArrayList<>();
                waitTime = new ArrayList<>();
                removeTime.add(Instant.now());
                return;
            }
        }
        // to fetch file content
        stageLabel = "2";
        createThreads(stage, stageLabel);
        phase3Result[phase3Result.length - 1] = new long[]{(Math.floorMod(serverNumber - 2, serverCount) + 1)};
        removeTime.add(Instant.now());
        comTime.add(Instant.now());
        sendToClient(phase3Result);
        comTime.add(Instant.now());
        perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
        comTime = new ArrayList<>();
        waitTime = new ArrayList<>();
        removeTime.add(Instant.now());
    }


    /**
     * perform dot product of keyword vector with addr table
     * multithreaded across the column i.e. the content of addr table
     *
     * @param threadNum the number of threads
     */
    public static void task21(int threadNum) {
        int batchSize = (int) Math.ceil(addr[0].length / (double) numThreads);
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;
        if (end > addr[0].length) {
            end = addr[0].length;
        }

        for (int i = 0; i < keywordCount; i++) {
            long[] temp = addr[i];
            for (int j = start; j < end; j++) {
                phase2AddrResult[j] = (phase2AddrResult[j] +
                        (temp[j] * searchKeywordVectorShare[i]) % modValue) % modValue;
            }
        }
    }

    /**
     * To perform dot product with addr table, act's client access and keyword list
     * multithreaded across number of keywords
     *
     * @param threadNum the thread id
     */
    public static void task24(int threadNum) {
        int batchSize = (int) Math.ceil((addr[0].length + 6) / (double) numThreads);
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;
        if (end > (addr[0].length + 2)) {
            end = (addr[0].length + 2);
        }
        BigInteger[] keywords = act[0];
        BigInteger[] access = act[clientId];
        verificationForServer[0] = BigInteger.valueOf(0);
        verificationForServer[1] = BigInteger.valueOf(0);
        for (int i = 0; i < keywordCount; i++) {
            long[] temp = addr[i];
            for (int j = start; j < end; j++) {
                if (j < addr[0].length) {
                    phase2AddrResult[j] = (phase2AddrResult[j] +
                            (temp[j] * searchKeywordVectorShare[i]) % modValue) % modValue;
                } else if (j == addr[0].length) {
                    verificationForServer[0] = ((keywords[i].
                            multiply(BigInteger.valueOf(searchKeywordVectorShare[i]))).mod(modValueBig).add(verificationForServer[0])).mod(modValueBig);
                } else if (j == addr[0].length + 1) {
                    verificationForServer[1] = ((access[i].
                            multiply(BigInteger.valueOf(searchKeywordVectorShare[i]))).mod(modValueBig).add(verificationForServer[1])).mod(modValueBig);
                }
            }
        }
    }

    /**
     * to perform dot product with row vector and inverted index
     * multithreaded across the number of rows in opt inverted index
     *
     * @param threadNum
     */
    public static void task23(int threadNum) {
        int batchSize = (int) Math.ceil((optCol) / (double) numThreads);
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;
        if (end > optCol) {
            end = optCol;
        }
        for (int i = 0; i < optRow; i++) {
            for (int j = start; j < end; j++) {
                phase2OptInvResult[j] = (phase2OptInvResult[j] +
                        (optInv[i * optInvColVec.length + j] * optInvRowVec[i]) % modValue) % modValue;
            }
        }
    }

    /**
     * to perform dot product with row vector and inverted index and also dot product with
     * row vector and hash digest matrix
     * multithreaded across the number of cols in opt inverted index
     *
     * @param threadNum thread number
     * @throws NoSuchAlgorithmException
     */
    public static void task22(int threadNum) throws NoSuchAlgorithmException {
        int batchSize = (int) Math.ceil((optCol) / (double) numThreads);
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;
        if (end > optCol) {
            end = optCol;
        }

        for (int i = 0; i < optRow; i++) {
            for (int j = start; j < end; j++) {
                for (int k = 0; k < 3; k++) {
                    optInvServerVerification[j][k] = (optInvServerVerification[j][k] +
                            (optInvHashValues[i * optInvColVec.length + j][k] * optInvRowVec[i]) % modValue)
                            % modValue;
                }
                phase2OptInvResult[j] = (phase2OptInvResult[j] +
                        (optInv[i * optInvColVec.length + j] * optInvRowVec[i]) % modValue) % modValue;
            }
        }
    }

    /**
     * to perform dot product with column vector and result from task22
     * multithreaded across number of keywords
     * @param threadNum thread number
     */
    public static void task25(int threadNum) {
        int batchSize = (int) Math.ceil((hashBlockCount) / (double) numThreads);
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;
        if (end > hashBlockCount) {
            end = hashBlockCount;
        }

        for (int i = 0; i < optCol; i++) {
            for (int j = start; j < end; j++) {
                result[j] = (result[j] + (Math.floorMod((1 - optInvColVec[i]), modValue)
                        * optInvServerVerification[i][j]) % modValue) % modValue;
            }
        }
    }

    /**
     * To perform phase 2 operation of fetching the file ids for the search keyword from inverted index and addr
     *
     * @throws IOException
     * @throws NoSuchAlgorithmException
     */
    public static boolean phase2() throws InterruptedException, IOException, ClassNotFoundException {
        phase2OptInvResult = new long[optCol + 1];
        stage = "2";
        serverCount = 3;
        int phase = 2;
        // Waiting for client to send the data
        removeTime.add(Instant.now());
        comTime.add(Instant.now());
        startServer();
        comTime.add(Instant.now());
        perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
        comTime = new ArrayList<>();
        waitTime = new ArrayList<>();
        removeTime.add(Instant.now());
        // read data send from client
        searchKeywordVectorShare = (long[]) objects;
        // this will execute if the client is unhappy with servers results in phase 1 and wants to end the search op
        if (searchKeywordVectorShare[0] == 0) {
            log.info("Client wishes to discontinue the search.");
            return true;
        }
        {
            // if verification is required by servers to check if keywords vector sent by client is in accordance to the keyword
            // search by client in phase1 and then returning the addr table data
            if (serverVerification) {
                verificationForServer = new BigInteger[2];
                stageLabel = "4";
                createThreads(stage, stageLabel);
                verificationForServer[0] = (verificationForServer[0].subtract(searchKeywordShare)).mod(modValueBig);

                // for test 3, 4, 5 , 3= sum(A) , 4 = sum(A^2), 5 = 4-3
                // without test 5
                long[] result = new long[2]; // one for sum(A) and one for sum(A^2)
                // with test 5
//            long result[] = new long[2 + keywordCount]; // keywordcount for sum(a^2) -sum(A)
                long temp1;
                for (int i = 0; i < keywordCount; i++) {
                    temp1 = (searchKeywordVectorShare[i] * searchKeywordVectorShare[i]) % modValue;
                    result[0] = (result[0] + searchKeywordVectorShare[i]) % modValue;
                    result[1] = (result[1] + temp1) % modValue;
                    // with test 5
//                result[i + 2] = (temp1 - searchKeywordVectorShare[i]) % modValue;
                }
                // preparing data to send to neighboring server
                StringBuilder temp = new StringBuilder("");
                temp.append(verificationForServer[0]).append(",").append(verificationForServer[1]).append(",");
                for (long l : result) {
                    temp.append(l).append(",");
                }
                temp.append((Math.floorMod(serverNumber - 2, serverCount) + 1));
                // converting to byte array as we need to send biginteger data also
                byte[] byteList = temp.toString().getBytes(StandardCharsets.UTF_8);
                communicateAllServers(byteList);
                // interpolate the data recived from neighbours
                BigInteger[] resInterBig = new BigInteger[2]; // verification data interpolation
                // without test 5
                long[] resInter = new long[2]; // two tests
                // with test 5
//            long[] resInter = new long[2 + keywordCount];
                long[] sharesLong = new long[serverCount];
                BigInteger[] sharesBig = new BigInteger[serverCount];
                for (int i = 0; i < verificationForServer.length + result.length; i++) {
                    if (i >= 2) { // test 3,4,5
                        for (int p = 0; p < serverCount; p++) {
                            if (p == ((Math.floorMod(serverNumber - 2, serverCount)))) {
                                sharesLong[p] = result[i - 2];
                            } else {
                                sharesLong[p] = Long.parseLong(objectsReceivedString1D[p][i]);
                            }
                        }
                        resInter[i - 2] = lagrangeInterpolation(sharesLong);
                    } else { // test 1,2
                        for (int p = 0; p < serverCount; p++) {
                            if (p == ((Math.floorMod(serverNumber - 2, serverCount)))) {
                                sharesBig[p] = verificationForServer[i];
                            } else {
                                sharesBig[p] = new BigInteger(objectsReceivedString1D[p][i]);
                            }
                        }
                        resInterBig[i] = lagrangeInterpolation(sharesBig);
                    }
                }
                // test the values are interpolated as expected
                boolean flag = resInterBig[0].equals(BigInteger.valueOf(0)) && resInterBig[1].equals(BigInteger.valueOf(0))
                        && resInter[0] == 1 && resInter[1] == 1;
                // with test 5
//            if (flag) {
//                for (int i = 2; i < resInterBig.length; i++) {
//                    if (resInter[0] != 0) {
//                        flag = false;
//                        break;
//                    }
//                }
//            }


                if (!flag) {
                    log.info("Client has prepared an incorrect keyword vector.");
                    removeTime.add(Instant.now());
                    comTime.add(Instant.now());
                    sendToClient(new long[]{0, serverNumber});
                    comTime.add(Instant.now());
                    perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
                    comTime = new ArrayList<>();
                    waitTime = new ArrayList<>();
                    removeTime.add(Instant.now());
                    return true;
                }
            } else {
                stageLabel = "1"; // compute addr data result
                createThreads(stage, stageLabel);
            }
            // copying everything except hash digest for positions
            System.arraycopy(phase2AddrResult, 0, phase2AddrResultSlice, 0, phase2AddrResultSlice.length);
            phase2AddrResultSlice[phase2AddrResultSlice.length - 1] = (Math.floorMod(serverNumber - 2, serverCount) + 1);
            // sending to client
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            sendToClient(phase2AddrResultSlice);
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());
        }

        {
            // performing operation to get the file ids
//         Waiting for client to send the position and count of data to be retrieved from opt tabel
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            startServer();
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());
            //read object returned from client
            optIndexShare = (long[][]) objects;
            // this will execute if the client is unhappy with servers results in for addr
            if (optIndexShare[0][0] == 0) {
                log.info("Client wishes to discontinue the search.");
                return true;
            }
            optInvRowVec = optIndexShare[0];
            optInvColVec = optIndexShare[1];
            int neighbours;
            // to verify if row and column vector created by client is correct
            if (serverVerification) {
                stageLabel = "2";
                createThreads(stage, stageLabel);
                //with test 5
//            long[] result = new long[hashBlockCount + 2 + optInvRowVec.length + optInvColVec.length + 1];
                // without test 5
                result = new long[hashBlockCount + 1]; // one to add the server label
                // for test 1
                stageLabel = "5";
                createThreads(stage, stageLabel);
                //sending addr data to servers
                long[] data = new long[hashBlockCount + 1];
                for (int i = 0; i < hashBlockCount; i++) {
                    data[i] = phase2AddrResult[2 + hashBlockCount + i];
                }
                data[data.length - 1] = (Math.floorMod(serverNumber - 2, serverCount) + 1);
                // shares data with neighbouring servers
                neighbours = 1;
                communicateAllServers(data, neighbours);
                // receive data from neighbouring servers
                data = (long[]) objects;
                for (int i = 0; i < 3; i++) { // performing subtraction with its own computed hash digest of column vector positions
                    result[i] = Math.floorMod((result[i] - data[i]), modValue);
                }
                result[result.length - 1] = serverNumber;
                neighbours = 2;
                communicateAllServers(result, neighbours);
                // check if hash digest on column vector send by client - one stored at server in addr table is zero
                long[] hashResult = new long[hashBlockCount];
                long[] shares = new long[serverCount];
                for (int i = 0; i < result.length - 1; i++) {
                    for (int l = 0; l < serverCount; l++) {
                        if (l == (serverNumber - 1)) {
                            shares[l] = result[i];
                        } else {
                            shares[l] = objectsReceivedLong1D[l][i];
                        }
                    }
                    hashResult[i] = lagrangeInterpolation(shares);
                }
                boolean flag = true;
                for (int i = 0; i < hashBlockCount; i++) {
                    if (hashResult[i] != 0) {
                        flag = false;
                        break;
                    }
                }
                if (!flag) {
                    log.info("Client has prepared an incorrect opt inv row/col vector.");
                    removeTime.add(Instant.now());
                    comTime.add(Instant.now());
                    sendToClient(new long[]{0, serverNumber});
                    comTime.add(Instant.now());
                    perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
                    comTime = new ArrayList<>();
                    waitTime = new ArrayList<>();
                    removeTime.add(Instant.now());
                    return true;
                }
            } else {
                stageLabel = "3"; // fetch file ids from the inverted index
                createThreads(stage, stageLabel);
            }
            // create random number shares and share with other server and compute the final sum of random number
            // received from neighbouring servers
            removeTime.add(Instant.now());
            createRandomShares(serverCount, phase);
            removeTime.add(Instant.now());
            // perform dot product between result from column vector and add random value
            for (int i = 0; i < optCol; i++) {
                phase2OptInvResult[i] = ((randomSharesPhase2Sum[i] * optInvColVec[i]) % modValue
                        + phase2OptInvResult[i]) % modValue;
            }
            phase2OptInvResult[phase2OptInvResult.length - 1] = serverNumber;
            // send to client the file ids
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            sendToClient(phase2OptInvResult);
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());
        }
        return false;
    }

    /**
     * To compare search keyword with server keyword and access value for the client
     * multithreaded across number of keywords
     * @param threadNum the number of threads to run the program on
     */
    public static void task11(int threadNum) {
        int batchSize = (int) Math.ceil(keywordCount / (double) numThreads);
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;
        if (end > keywordCount) {
            end = keywordCount;
        }

        BigInteger[] keywords = act[0];
        BigInteger[] access = act[clientId];
        BigInteger temp;
        // (serverKeyword-userKeyword+ access) * randomValue
        for (int i = start; i < end; i++) {
            temp = (((keywords[i].subtract(searchKeywordShare)).mod(modValueBig).add(access[i])).mod(modValueBig)
                    .multiply(BigInteger.valueOf(randomSharesPhase1Sum[i]))).mod(modValueBig);
            phase1Result[threadNum - 1].append(temp).append(",");
        }
    }

    /**
     * For fetching the index of search keyword from ACT table
     *
     * @throws IOException
     */
    public static void phase1() throws InterruptedException, IOException, ClassNotFoundException {
        int phase = 1;
        if (!serverVerification) { // off serverVerification
            stage = "1";
            serverCount = 3;
            // Waiting for client to send the search keyword shares
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            startServer();
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());
//            System.out.println("recived");
            // reading the data sent by client
//            System.out.println(((BigInteger[]) objects).length);
            searchKeywordShare = ((BigInteger[]) objects)[0];
            clientId = ((BigInteger[]) objects)[1].intValue() + 1; // since 1st row are keywords and 2nd row are position of keywords
            // initializing
            for (int i = 0; i < numThreads; i++) {
                phase1Result[i] = new StringBuilder("");
            }
            // create random number shares and share with other server and compute the final sum of random number
            // received from neighbouring servers
            removeTime.add(Instant.now());
            createRandomShares(serverCount, phase);
            removeTime.add(Instant.now());

            // computing phase 1 operation on ACT list
            stageLabel = "1";
            createThreads(stage, stageLabel);
            // adding thread data
            for (int i = 1; i < numThreads; i++) {
                phase1Result[0].append(phase1Result[i]);
            }
            phase1Result[0].append(Math.floorMod(serverNumber - 2, serverCount) + 1);
            // converting to byte array inorder to send biginteger array
            byte[] byteList = phase1Result[0].toString().getBytes(StandardCharsets.UTF_8);
//            System.out.println(byteList.length);
            // sending to client
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            sendToClient(byteList);
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());
        } else {
            stage = "1";
            serverCount = 4;
            // Waiting for client to send the search keyword shares
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            startServer();
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());
            // reading the data sent by client
            searchKeywordShare = ((BigInteger[]) objects)[0];
            clientId = ((BigInteger[]) objects)[1].intValue() + 1; // since 1st row are keywords and 2nd row are position of keywords
            // initializing
            for (int i = 0; i < numThreads; i++) {
                phase1Result[i] = new StringBuilder("");
            }
            // create random number shares and share with other server and compute the final sum of random number
            // received from neighbouring servers
            removeTime.add(Instant.now());
            createRandomShares(serverCount, phase);
            removeTime.add(Instant.now());

            // computing phase 1 operation on ACT list
            stageLabel = "1";
            createThreads(stage, stageLabel);
            // adding thread data
            for (int i = 1; i < numThreads; i++) {
                phase1Result[0].append(phase1Result[i]);
            }
            if (serverNumber <= 3) {
                phase1Result[0].append(Math.floorMod(serverNumber - 2, 3) + 1);
            } else {
                phase1Result[0].append(4);
            }
            // converting to byte array
            byte[] byteList = phase1Result[0].toString().getBytes(StandardCharsets.UTF_8);
            // sending to client
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            sendToClient(byteList);
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());
        }
    }

    /**
     * Performs initialization tasks like reading from the properties files, initial memory allocation etc
     *
     * @throws IOException
     */
    public static void initialization(String[] args) throws IOException, NoSuchAlgorithmException {
        // determining the server id
        serverNumber = Integer.parseInt(args[0]);

        // reading the specificProperties file for server
        Properties specificProperties = Helper.readPropertiesFile("config/Server" + serverNumber + ".properties");
        // reading the commonProperties file for server
        Properties commonProperties = Helper.readPropertiesFile("config/Common.properties");

        serverVerification = Boolean.parseBoolean(commonProperties.getProperty("serverVerification"));
        clientPort = Integer.parseInt(commonProperties.getProperty("clientPort"));
        clientIP = commonProperties.getProperty("clientIP");
        seedServerRandomValue = Long.parseLong(specificProperties.getProperty("seedServerRandomValue"));
        optRow = Integer.parseInt(commonProperties.getProperty("optRow"));
        optCol = Integer.parseInt(commonProperties.getProperty("optCol"));
        fileLength = Integer.parseInt(commonProperties.getProperty("maxFileLength"));
        checkpoint1 = Integer.parseInt(commonProperties.getProperty("checkpoint1"));
        numThreads = Integer.parseInt(commonProperties.getProperty("numThreads"));
        setNeighbourIP(commonProperties);
        // read all tables
        readDataStructures();
        // to open a socket at Client side to actively listen for data from client
        ss = new ServerSocket(serverPort);

        cleanUp();

        System.out.println("numThreads:" + numThreads);
        System.out.println("serverVerification:" + serverVerification);
        System.out.println("keywordCount:" + keywordCount);
        System.out.println("fileCount:" + fileCount);
    }

    public static void main(String args[]) throws IOException, InterruptedException, NoSuchAlgorithmException, ClassNotFoundException {
        // to calculate the time
        Instant start, end;
        double totalTime;
        // to store the phase value
        int phase;
        // to store client/server program for experiment
        int type = serverNumber;
        // the number of times program was run for experiment
        int count = 0;

        initialization(args);

        while (true) {
            if (serverNumber <= 3) {
                // phase 1
                System.out.println("Start of Phase 1.");
                System.out.println("---------------------------------------");
                phase = 1;
                cleanUpPhaseData(phase);
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
                boolean flag = phase2();
                end = Instant.now();
                totalTime = Duration.between(start, end).toMillis();
                Helper.printTimes(phase, null, null, removeTime, perServerTime, totalTime, count);
                System.out.println("End of Phase 2.");
                cleanUpPhaseData(phase);
                if (!flag) {
                    phase = 3;
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
                }
            } else if (serverNumber == 4 && serverVerification) {
                // phase 1
                System.out.println("Start of Phase 1.");
                System.out.println("---------------------------------------");
                phase = 1;
                cleanUpPhaseData(phase);
                start = Instant.now();
                phase1();
                end = Instant.now();
                totalTime = Duration.between(start, end).toMillis();
                Helper.printTimes(phase, null, null, removeTime, perServerTime, totalTime, count);
                System.out.println("End of Phase 1.");
                cleanUpPhaseData(phase);
            } else {
                System.exit(0);
            }

            count++;
            if (count == Helper.getRunCount()) {
                count = 0;
                System.out.println("Time taken on an average for over " + (Helper.getRunCount() - Helper.getBuffer()) + " round for each phase is below");
                Helper.timeTaken(type);
            }
        }
    }
}
