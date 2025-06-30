package src.opt;

import constants.Constant;
import org.tartarus.snowball.SnowballStemmer;
import utility.Helper;

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

public class DBO extends Thread {

    private static Properties properties;
    private static final Logger log = Logger.getLogger(Logger.GLOBAL_LOGGER_NAME);

    private static int newFileId;
    private static String searchKeyword;
    private static boolean access;
    private static String clientId;
    private static List<Object> objects;
    private static int serverCount;
    private static BigInteger[] keywordShares;
    private static long[][] keywordVectorShares;
    private static long[] shares;
    //    private static String[] data1D;
//    private static long[][] data2D;
    private static int keywordCount;
    private static int clientCount;
    private static long[] keywordVector;
    private static long seedDBO;

    // to store the maximum number of files a keyword can occur in
    private static int fileMaxCount;
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
    private static BigInteger hashContent;
    private static long[][] hash;
    private static String type;
    private static int numThreads;
    private static String stage;
    private static String stageLabel;
    private static boolean flagCVP1;
    private static BigInteger[][] serverShares;
    private static BigInteger[] servers_1_2;
    private static BigInteger[] servers_2_3;
    private static BigInteger[] servers_3_1;
    private static ArrayList<Instant> comTime = new ArrayList<>();
    private static ArrayList<Instant> waitTime = new ArrayList<>();
    private static Scanner console;
    private static int fileLength;
    private static long[][] addr;
    private static BigInteger[] noAccessCode;


    // to stores server shares as string values for 1D array
    private static BigInteger[][] serverSharesAsBigInteger_1D;
    // to stores server shares as string values for 2D array
    private static BigInteger[][][] serverSharesAsBigInteger_2D;
    // to stores server shares as long values for 1D array
    private static long[][] serverSharesAsLong_1D;
    // to stores server shares as long values for 2D array
    private static long[][][] serverSharesAsLong_2D;
    // to stores server shares as long values for 1D array
    private static String[][] objectReadString1D;
    // to stores server shares as long values for 2D array
    private static String[][][] serverSharesAsString_2D;

    private static long[][] verificationServerPhase3;
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
    private static int clientPort;
    private static long[] indexHashList;


    private static BigInteger[][] singleDShares;
    private static BigInteger phase1ResultAccess;
    private static long[][] singleDSharesLong;
    private static long[][][] doubleDSharesLong;
    private static BigInteger[][][] doubleDSharesBig;
    private static StringBuilder[][][] doubleDSharesBigString;
    private static BigInteger[][] doubleDataBig;
    private static StringBuilder[][] doubleDataBigString;
    private static BigInteger[] singleData;
    private static long[] singleDataLong;
    private static long[][] doubleDataLong;
    private static long[][][] doubleDShares;

    // to store stemmer object
    private static SnowballStemmer stemmer;

    // to store the numeric version of text
    private static StringBuilder numericText;
    // to store the updates text
    private static StringBuilder newText;


    //    private static long[] indexHashList;
    private static BigInteger indexHash;
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
    private static long[] serverVerificationPhase3Result;
    private static long[] phase2Interpolation;
    private static long[][][] verificationServer2DPhase3;
    private static long[] phase2ResultAll;
    private static boolean freeSlot;


//    /**
//     * to perform hash digest of given data using SHA-1
//     *
//     * @param data The given data
//     * @return The numeric hash digest value of 20B
//     * @throws NoSuchAlgorithmException
//     */
//    private static String hashDigest(String data) throws NoSuchAlgorithmException {
//        MessageDigest md = MessageDigest.getInstance("SHA-1");
//        md.update(data.getBytes());
//        byte[] digest = md.digest();
//        StringBuilder numeric_hash_value = new StringBuilder();
//        for (int i = 0; i < digest.length; i++) {
//            if (digest[i] < 0) {
//                numeric_hash_value.append(digest[i] + 256);
//            } else
//                numeric_hash_value.append(digest[i]);
//        }
//
//        return String.valueOf(numeric_hash_value);
//    }

    /**
     * to perform hash digest of given data using SHA-1
     *
     * @param data The given data
     * @return The numeric hash digest value of 20B
     * @throws NoSuchAlgorithmException
     */
    private static String hashDigest(String data) throws NoSuchAlgorithmException {
        MessageDigest md = MessageDigest.getInstance("SHA-1");
        md.update(data.getBytes());
        byte[] digest = md.digest();
        BigInteger result = Helper.mod(new BigInteger(digest));
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
    private static String decrypt_numeric_string(String numericString) {
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

    // multithreaded across number of files
    private static void task31(int threadNum) {

        int batchSize = (int) Math.ceil((fileCount) / (double) numThreads);
        long[] shares;
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;

        if (end > fileCount) {
            end = fileCount;
        }

        for (int m = 0; m < fileVectors.length; m++) {
            for (int i = start; i < end; i++) {
                shares = shamirSecretSharingAsLong(fileVectors[m][i], serverCount);
                for (int j = 0; j < serverCount; j++)
                    fileVectorsShares[j][m][i] = shares[j];
            }
        }
    }

    // multithreaded across the maximum length of file
    private static void task32(int threadNum) {

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
                    shares[l] = serverSharesAsLong_2D[l][i][j];
                }
                phase3Result[i][j] = lagrangeInterpolationAsLong(shares);

                if (j < Constant.getHashBlockCount()) {
                    hash[i][j] = phase3Result[i][j];
                } else {
                    str.append(phase3Result[i][j]);
                }
            }
            content[i][threadNum - 1] = String.valueOf(str);

        }
    }


    // multithreaded across the maximum length of file
    private static void task33(int threadNum) {

        long[] shares = new long[serverCount];
        int batchSize = (int) Math.ceil((keywordCount + 1) / (double) numThreads);
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;
        if (end > (keywordCount + 1)) {
            end = keywordCount + 1;
        }

        for (int i = 0; i < phase2Result.size(); i++) {
            for (int j = start; j < end; j++) {
                for (int l = 0; l < serverCount; l++) {
                    shares[l] = serverSharesAsLong_2D[l][i][j];
                }
                serverVerificationPhase3[i][j] = lagrangeInterpolationAsLong(shares);

                shares = shamirSecretSharingAsLong(serverVerificationPhase3[i][j], serverCount);
                for (int l = 0; l < serverCount; l++) {
//                    System.out.print(shares[l]+" ");
                    verificationServer2DPhase3[l][i][j] = shares[l];
                }
//                System.out.println();
            }

        }
    }

//    // multithreaded across the maximum length of file
//    private static void task32(int threadNum) {
//
//        BigInteger[] shares = new BigInteger[serverCount];
//        int batchSize = (int) Math.ceil(fileLength / (double) numThreads);
//        int start = (threadNum - 1) * batchSize;
//        int end = start + batchSize;
//        if (end > fileLength) {
//            end = fileLength;
//        }
//
//        BigInteger interpolatedValue;
//        for (int i = 0; i < phase3Result.length; i++) {
//            StringBuilder str = new StringBuilder();
//
//            for (int j = start; j < end; j++) {
//                for (int l = 0; l < serverCount; l++) {
//                    shares[l] = new BigInteger(serverSharesAsString_2D[l][i][j]);
//                }
//                interpolatedValue = lagrangeInterpolationAsBigInteger(shares);
//
////                if(!interpolatedValue.equals(BigInteger.valueOf(0))){
////                    System.out.println(interpolatedValue);
////                }
//
//                if (j == 0) {
//                    hashContent = interpolatedValue;
//                } else {
//                    str.append(interpolatedValue);
//                }
//            }
//            content[i][threadNum - 1] = String.valueOf(str);
//
//        }
//    }

    private static void phase3() throws IOException, NoSuchAlgorithmException {

        stage = "3";
        serverCount = 3;

        List<Long> phaseResultTemp = phase2Result;
        phase2Result = new ArrayList<>();
        phase2Result.add(phaseResultTemp.get(0));

        // preparing fileVectors vector for sending to server
        fileVectors = new long[phase2Result.size()][fileCount + 1]; // one for sample file
        int k = 0;
        for (long file : phase2Result) {
            fileVectors[k][(int) (file - 1)] = 1;
//            fileVectors[k][(int) (file+1) -1] = 1;  // Test for client correctness for server: test 1
//            fileVectors[k][(int) (file + 1) - 1] = 2;  // Test for client correctness for server: test 3, 4, 5
            k++;
        }

        // create shares of the fileVectors
        fileVectorsShares = new long[serverCount][phase2Result.size()][fileCount + 1];
        shares = new long[serverCount];

        stageLabel = "3.1";
        createThreads(stage, stageLabel);

        // sending shares to the server
        removeTime.add(Instant.now());
        comTime.add(Instant.now());
        long[][] data2D;
        for (int i = 0; i < serverCount; i++) {
            data2D = fileVectorsShares[Math.floorMod(i - 1, serverCount)];
            sendToServer(data2D, serverIP[i], serverPort[i]);
        }
        comTime.add(Instant.now());
        perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, serverCount));
        comTime = new ArrayList<>();
        waitTime = new ArrayList<>();
        removeTime.add(Instant.now());

        // perform tasks so that server can verify that the file vector sent is the vector based on result from phase 2
        if (serverVerification) {

            verificationServerPhase3 = new long[serverCount][2];
            int org = startingPos % optCol;

            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            long[] data1D;
            for (int i = 0; i < serverCount; i++) {
                verificationServerPhase3[i][0] = (i + 1);
                verificationServerPhase3[i][1] = org + Math.floorMod(i - 1, serverCount) + 1;
                data1D = verificationServerPhase3[i];
                sendToServer(data1D, serverIP[i], serverPort[i]);
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
            serverSharesAsLong_2D = new long[serverCount][][];
            readObjectsAsLong(type);
            cleanUp();

            verificationServer2DPhase3 = new long[serverCount][phase2Result.size()][keywordCount + 1];
            serverVerificationPhase3 = new long[phase2Result.size()][keywordCount + 1];

            stageLabel = "3.3";
            createThreads(stage, stageLabel);

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
            serverSharesAsLong_2D = new long[serverCount][][];
            readObjectsAsLong(type);
            cleanUp();

            boolean flag = true;

            for (int j = 0; j < serverCount; j++) {
                if (serverSharesAsLong_2D[j][0][0] == 0) {
                    flag = false;
                    break;
                }
            }

            if (!flag) {
                log.info("Client has prepared an incorrect file vector Or has no access on all keywords of requested file.");
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
            serverSharesAsLong_2D = new long[serverCount][][];
            readObjectsAsLong(type);
            cleanUp();

        }
//
        // perform interpolation to retrieve file contents

        fileLength = serverSharesAsLong_2D[0][0].length;
        phase3Result = new long[phase2Result.size()][fileLength];
        hash = new long[phase3Result.length][Constant.getHashBlockCount()];
        content = new String[phase3Result.length][numThreads];
        stageLabel = "3.2";
        createThreads(stage, stageLabel);
        finalContent = new String[phase3Result.length];

        for (int i = 0; i < phase3Result.length; i++) {
            finalContent[i] = "";
            for (int p = 0; p < numThreads; p++) {
                finalContent[i] = finalContent[i] + content[i][p];
            }
            finalContent[i] = decrypt_numeric_string(finalContent[i]);
        }

        if (clientVerification) {
            boolean flag = true;
            String hashC;
            long[] hashClient;
            int h;
            for (int i = 0; i < phase3Result.length; i++) {
                hashC = hashDigest(finalContent[i].trim());
                h = 0;
                hashClient = new long[Constant.getHashBlockCount()];
                for (int j = 0; j < hashC.length(); j = j + Constant.getHashBlockSize()) {
                    int end = j + Constant.getHashBlockSize();
                    if (end > hashC.length())
                        end = hashC.length();
                    hashClient[h] = Long.parseLong(hashC.substring(j, end));
                    h++;
                }

                for (int m = 0; m < Constant.getHashBlockCount(); m++) {
//                    hash[i][m] = 90; // Test for server correctness for client
                    if (!(hash[i][m] == hashClient[m])) {
                        log.info("The files content provided by the servers is incorrect.");
                        System.exit(0);
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

    // multithreaded across number of keywords
    private static void task12(int threadNum) {
        int batchSize = (int) Math.ceil(keywordCount / (double) numThreads);
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;

        if (end > keywordCount) {
            end = keywordCount;
        }

        BigInteger s1, s2, s3;

        BigInteger s11 = BigInteger.valueOf(1);
        BigInteger s12 = BigInteger.valueOf(2);
        BigInteger s13 = BigInteger.valueOf(3);

        BigInteger value0 = BigInteger.valueOf(0);

        for (int i = start; i < end; i++) {

            s1 = new BigInteger(objectReadString1D[0][i]);
            s2 = new BigInteger(objectReadString1D[1][i]);
            s3 = new BigInteger(objectReadString1D[2][i]);

            // evaluating value in pairs
            servers_1_2[threadNum - 1] = Helper.mod(Helper.mod(s12.multiply(s1))
                    .subtract(Helper.mod(s11.multiply(s2))));
            servers_2_3[threadNum - 1] = Helper.mod(Helper.mod(s13.multiply(s2))
                    .subtract(Helper.mod(s12.multiply(s3))));
            servers_3_1[threadNum - 1] = Helper.mod(Helper.mod(s13.multiply(s1))
                    .subtract(Helper.mod(s11.multiply(s3))));

//             servers_1_2 = BigInteger.valueOf(0); // Test for server correctness for client

            // checking if server values are consistent across pairs
            if (servers_1_2[threadNum - 1].equals(value0) || servers_2_3[threadNum - 1].equals(value0)
                    || servers_3_1[threadNum - 1].equals(value0)) {
                phase1Result = i;
                if (!(servers_1_2[threadNum - 1].equals(servers_2_3[threadNum - 1])
                        && servers_2_3[threadNum - 1].equals(servers_3_1[threadNum - 1]))) {
                    flagCVP1 = false;
                    break;
                }
            }
        }
    }


    /**
     * To perform cleanup tasks in course of program execution
     */
    public static void cleanUp() {
        // re-initializing the list to hold values received from server
        objects = Collections.synchronizedList(new ArrayList<>());
    }

    /**
     * To interpolate string values
     *
     * @param share the string value of the shares
     * @return the cleartext/interpolated value
     */
    private static BigInteger lagrangeInterpolationAsBigInteger(BigInteger share[]) {

        return switch (share.length) {
            case 2 -> Helper.mod(Helper.mod(BigInteger.valueOf(2).multiply(share[0]))
                    .subtract(share[1]));
            case 3 -> Helper.mod(Helper.mod(Helper.mod(BigInteger.valueOf(3)
                    .multiply(share[0])).subtract(Helper.mod(BigInteger.valueOf(3)
                    .multiply(share[1])))).add(share[2]));
            default -> throw new IllegalStateException("Unexpected value: " + share.length);
        };
    }

    /**
     * To interpolate string values
     *
     * @param share the string value of the shares
     * @return the cleartext/interpolated value
     */
    private static BigInteger lagrangeInterpolationAsBigInteger1(BigInteger share[]) {

        return switch (share.length) {
            case 2 -> Helper.mod(Helper.mod(Helper.mod(BigInteger.valueOf(3).multiply(share[0]))
                    .subtract(share[1])).divide(BigInteger.valueOf(2)));
            case 3 -> Helper.mod(Helper.mod(Helper.mod(BigInteger.valueOf(3)
                    .multiply(share[0])).subtract(Helper.mod(BigInteger.valueOf(3)
                    .multiply(share[1])))).add(share[2]));
            default -> throw new IllegalStateException("Unexpected value: " + share.length);
        };
    }

    /**
     * To interpolate long values
     *
     * @param share the long value of the shares
     * @return the cleartext/interpolated value
     */
    private static long lagrangeInterpolationAsLong(long share[]) {
        return switch (share.length) {
            case 2 -> Helper.mod(Helper.mod(2 * share[0]) - share[1]);
            case 3 -> Helper.mod((Helper.mod(Helper.mod(3 * share[0]) -
                    Helper.mod(3 * share[1]))) + share[2]);
            default -> throw new IllegalStateException("Unexpected value: " + share.length);
        };
    }


    private static void startClient(int serverCount) {

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

    private static BigInteger lagrangeInterpolationCustomized(BigInteger share1, BigInteger share2, int i, int j) {

        return Helper.mod(Helper.mod(BigInteger.valueOf(i).multiply(share1))
                .subtract(Helper.mod(BigInteger.valueOf(j).multiply(share2))));
    }

    /**
     * To read values from objects as string
     *
     * @param type the type of object as 1D or 2D
     */
    private static void readObjectsAsBigInteger(String type) {
        if (type.equals("1D")) {
            for (int i = 0; i < objects.size(); i++) {
                int temp = ((BigInteger[]) objects.get(i))[((BigInteger[]) objects.get(i)).length - 1].intValue();
                serverSharesAsBigInteger_1D[temp - 1] = ((BigInteger[]) objects.get(i));
            }
        } else if (type.equals("2D")) {
            for (int i = 0; i < objects.size(); i++) {
                int temp = ((BigInteger[][]) objects.get(i))[((BigInteger[][]) objects.get(i)).length - 1][0].intValue();
                serverSharesAsBigInteger_2D[temp - 1] = ((BigInteger[][]) objects.get(i));
            }
        }
    }

    /**
     * To read values from objects as long
     *
     * @param type the type of object as 1D or 2D
     */
    private static void readObjectsAsLong1(String type) {
        if (type.equals("1D")) {
            for (int i = 0; i < objects.size(); i++) {
                int temp = (int) (((long[]) objects.get(i))[((long[]) objects.get(i)).length - 1]);
                serverSharesAsLong_1D[temp - 1] = ((long[]) objects.get(i));
            }
        } else if (type.equals("2D")) {
            for (int i = 0; i < objects.size(); i++) {
                long[][] data = (long[][]) objects.get(i);
//                int temp = (int) (((long[][]) objects.get(i))[((long[][]) objects.get(i)).length - 1][0]);
                int temp = (int) data[0][data[0].length - 1];
                serverSharesAsLong_2D[temp - 1] = ((long[][]) objects.get(i));
            }
        }
    }

    /**
     * To read values from objects as long
     *
     * @param type the type of object as 1D or 2D
     */
    private static void readObjectsAsLong(String type) {
        if (type.equals("1D")) {
            for (int i = 0; i < objects.size(); i++) {
                int temp = (int) (((long[]) objects.get(i))[((long[]) objects.get(i)).length - 1]);
                serverSharesAsLong_1D[temp - 1] = ((long[]) objects.get(i));
            }
        } else if (type.equals("2D")) {
            for (int i = 0; i < objects.size(); i++) {
                int temp = (int) (((long[][]) objects.get(i))[((long[][]) objects.get(i)).length - 1][0]);
                serverSharesAsLong_2D[temp - 1] = ((long[][]) objects.get(i));
            }
        }
    }

    /**
     * To read values from objects as long
     *
     * @param type the type of object as 1D or 2D
     */
    private static void readObjectsAsString(String type) {
        if (type.equals("1D")) {
            for (int i = 0; i < objects.size(); i++) {
                String objectRead = new String((byte[]) objects.get(i), StandardCharsets.UTF_8);
                int temp = objectRead.charAt(objectRead.length() - 1) - '0';
                objectReadString1D[temp - 1] = objectRead.split(",");
            }

        } else if (type.equals("2D")) {
            for (int i = 0; i < objects.size(); i++) {
                byte[][] data = (byte[][]) objects.get(i);
                int temp = new String(data[data.length - 1], StandardCharsets.UTF_8).charAt(0) - '0';
//                System.out.println("Server nu:" + temp);
                serverSharesAsString_2D[temp - 1] = new String[phase2Result.size()][];
                for (int j = 0; j < data.length - 1; j++) {
                    serverSharesAsString_2D[temp - 1][j] = new String(data[j], StandardCharsets.UTF_8).split(",");
                }
            }
        }

    }

    private static class ThreadTask implements Runnable {
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
            if (stage.equals("0")) {
                if (stageLabel.equals("1")) {
                    task01(singleData, threadNum);
                } else if (stageLabel.equals("2")) {
                    task02(singleDataLong, threadNum);
                } else if (stageLabel.equals("3")) {
                    task03(doubleDataLong, threadNum);
                } else if (stageLabel.equals("4")) {
//                    task04(doubleDataLong, threadNum);
                } else if (stageLabel.equals("5")) {
                    task05(serverSharesAsLong_2D, threadNum);
                } else if (stageLabel.equals("6")) {
                    try {
                        task06(threadNum);
                    } catch (NoSuchAlgorithmException e) {
                        throw new RuntimeException(e);
                    }
                } else if (stageLabel.equals("7")) {
                    task07(doubleDataBig, threadNum);
                }
                else if (stageLabel.equals("9")) {
                    task09(doubleDataBigString, threadNum);
                }
            } else if (stage.equals("1")) {
                if (stageLabel.equals("1"))
                    task11(threadNum);
                else if (stageLabel.equals("2")) {
                    task12(threadNum);
                } else if (stageLabel.equals("3")) {
                    task13(threadNum);
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

    private static void createThreads(String stage, String stageLabel) {
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
     * Create share for secret value as string
     *
     * @param secret      the secret value as tring
     * @param serverCount the number of servers for which shares are to be created
     * @return the share of the secret value as string is returned for given number of server as servercount
     */
    private static BigInteger[] shamirSecretSharingAsBigInt(StringBuilder secret, int serverCount) {

        BigInteger secretBig = new BigInteger(String.valueOf(secret));
        Random rand = new Random();
        BigInteger[] share = new BigInteger[serverCount];

        // choosing the slope value for line
//        BigInteger slope = BigInteger.valueOf(rand.nextInt(Constant.getMaxRandomBound() - Constant.getMinRandomBound()) +
//                Constant.getMinRandomBound());

        long slope = rand.nextLong(Constant.getMaxRandomBound() - Constant.getMinRandomBound()) +
                Constant.getMinRandomBound();

        // check if the secret size is enough for long or BigInteger calculation
        for (int i = 0; i < serverCount; i++) {
            share[i] = Helper.mod(Helper.mod(BigInteger.valueOf(i + 1).multiply(BigInteger.valueOf(slope))).add(secretBig));
        }

        return share;
    }


    /**
     * Create share for secret value as string
     *
     * @param secret      the secret value as tring
     * @param serverCount the number of servers for which shares are to be created
     * @return the share of the secret value as string is returned for given number of server as servercount
     */
    private static long[] shamirSecretSharingAsLong(long secret, int serverCount) {
        Random rand = new Random();
        long[] share = new long[serverCount];

        // choosing the slope value for line
        long slope = rand.nextInt(Constant.getMaxRandomBound() - Constant.getMinRandomBound()) +
                Constant.getMinRandomBound();

        // check if the secret size is enough for long or BigInteger calculation
        for (int i = 0; i < serverCount; i++) {
            share[i] = Helper.mod(Helper.mod(Helper.mod(i + 1) * slope)
                    + secret);
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
        keywordShares = shamirSecretSharingAsBigInt(numericText, serverCount);
    }


    private static long[] getHashBlocks(String hash) {
        long[] temp = new long[Constant.getHashBlockCount()];
        int j = 0;
        for (int i = 0; i < hash.length(); i = i + Constant.getHashBlockSize()) {
            int end = i + Constant.getHashBlockSize();
            if (end > hash.length())
                end = hash.length();

            temp[j] = Long.parseLong(hash.substring(i, end));
            j++;
        }
        return temp;
    }


    public static void task03(long[][] data, int threadNum) {

        Instant start1 = Instant.now();

        int batchSize = (int) Math.ceil(data.length / (double) numThreads);
        long[] shares;
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;

        if (end > data.length) {
            end = data.length;
        }

//        System.out.println(start + " " + end);
        int l = data[0].length;
        for (int k = start; k < end; k++) {
            long[] temp = data[k];
            for (int i = 0; i < l; i++) {
                shares = shamirSecretSharingAsLong(temp[i], serverCount);
                for (int j = 0; j < serverCount; j++)
                    doubleDSharesLong[j][k][i] = shares[j];
            }
        }
        Instant end1 = Instant.now();
//        System.out.println("Time:" + Duration.between(start1, end1).toMillis());
    }


    public static void task05(long[][][] data, int threadNum) {
        long[] shares = new long[serverCount];
        int batchSize = (int) Math.ceil((data[0].length - 1) / (double) numThreads);
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;
        if (end > (data[0].length - 1)) {
            end = data[0].length - 1;
        }

        for (int i = start; i < end; i++) {
            for (int j = 0; j < data[0][0].length; j++) {
                for (int l = 0; l < serverCount; l++) {
                    shares[l] = serverSharesAsLong_2D[l][i][j];
                }
                doubleDataLong[i][j] = lagrangeInterpolationAsLong(shares);
            }
        }

    }

    public static void task06(int threadNum) throws NoSuchAlgorithmException {
        Instant start1=Instant.now();
        int batchSize = (int) Math.ceil((keywordCount - phase1Result) / (double) numThreads);
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;
        if (end > (keywordCount - phase1Result)) {
            end = keywordCount - phase1Result;
        }

//        System.out.println("indexes start" + start + phase1Result);
//        System.out.println("indexes end" + end + phase1Result);


        long start_, count;
        int pointer;
        String hash;

        for (int i = start + phase1Result; i < end + phase1Result; i++) {
            if ((doubleDataLong[phase1Result][0] / optCol) == (doubleDataLong[i][0] / optCol)) {
                if (i != phase1Result) {
                    start_ = doubleDataLong[i][0] + 2;
                    count = doubleDataLong[i][1];
                } else {
                    start_ = doubleDataLong[i][0];
                    count = doubleDataLong[i][1] + 1;
                }
            } else {
                start_ = doubleDataLong[i][0] + optCol;
                count = doubleDataLong[i][1];
            }

            // change of hash digest for start and count
            String hashAC = hashDigest(hashDigest(String.valueOf(start_)) + (count));
            addr[i][0] = start_;
            addr[i][1] = count;
            // breaking hash digest into hash blocks
            long[] temp = getHashBlocks(hashAC);
            for (int j = 0; j < Constant.getHashBlockCount(); j++) {
                addr[i][2 + j] = temp[j];
            }

            // change of hash digest for positions
            for (int j = (int) start_; j < start_ + count; j++) {
                hash = hashDigest(String.valueOf(j));
                pointer = 0;
                for (int k = 0; k < hash.length(); k = k + Constant.getHashBlockSize()) {
                    int end_ = k + Constant.getHashBlockSize();
                    if (end_ > hash.length())
                        end_ = hash.length();
                    addr[i][2 + Constant.getHashBlockCount() + pointer] = Helper.mod(addr[i][2 + Constant.getHashBlockCount() + pointer] +
                            Helper.mod(Long.parseLong(hash.substring(k, end_))));
                    pointer++;
                }
            }
        }

        Instant end1=Instant.now();
//        System.out.println("duration here:"+Duration.between(start1,end1).toMillis());

    }

    private static void updateAddrData(Boolean flag) throws NoSuchAlgorithmException, IOException {
        if (flag) { // if free slot avaliable

            stage = "0";
//            System.out.println("free slot addr");
            // changing count of items
            doubleDataLong = new long[keywordCount][2 + 2 * Constant.getHashBlockCount()];
            doubleDataLong[phase1Result][1] = 1;

            // change of hash digest for start and count

            String hashAC = hashDigest(hashDigest(String.valueOf(startingPos)) + (countItems + 1));

//            System.out.println("after:" + hashAC);
//             breaking hash digest into hash blocks
            long[] temp = getHashBlocks(hashAC);
            // finding difference between hash blocks
            for (int i = 0; i < Constant.getHashBlockCount(); i++) {
                doubleDataLong[phase1Result][2 + i] = Helper.mod(temp[i] - indexHashList[i]);
            }

            // change of hash digest for position vector
            hashAC = hashDigest(String.valueOf((startingPos + countItems + 1)));
//            System.out.println("after:" + hashAC);
            temp = getHashBlocks(hashAC);
            // finding difference between hash blocks
            for (int i = 0; i < Constant.getHashBlockCount(); i++) {
                doubleDataLong[phase1Result][2 + Constant.getHashBlockCount() + i] = Helper.mod(temp[i] -
                        indexHashList[Constant.getHashBlockCount() + i]);
            }

            Instant start = Instant.now();
            doubleDSharesLong = new long[serverCount][keywordCount][2 + 2 * Constant.getHashBlockCount()];
            stageLabel = "3";
            createThreads(stage, stageLabel);

            Instant end = Instant.now();
//            System.out.println("Time:" + Duration.between(start, end).toMillis());
//            for (int i = 0; i < 2 + Constant.getHashBlockCount(); i++) {
//                System.out.print(doubleDataLong[phase1Result][i] + " ");
//            }
//            System.out.println();

            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            // sending search keyword shares and client id to the server
            long[][] data2D;
            for (int i = 0; i < serverCount; i++) {
                data2D = doubleDSharesLong[Math.floorMod(i - 1, 3)];
                sendToServer(data2D, serverIP[i], serverPort[i]);
            }
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, serverCount));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());
        } else { // free slot unavailable
//            System.out.println("no free slot addr");
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            long[][] data2D;
            for (int i = 0; i < serverCount; i++) {
                data2D = new long[][]{{0}};
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
            serverSharesAsLong_2D = new long[serverCount][][];
            readObjectsAsLong(type);
            cleanUp();

            stage = "0";
            stageLabel = "5";
            doubleDataLong = new long[keywordCount][2 + 2 * Constant.getHashBlockCount()];
            createThreads(stage, stageLabel);

//            System.out.println("b4");
//            for (long[] a : doubleDataLong) {
//                for (long b : a) {
//                    System.out.print(b + " ");
//                }
//                System.out.println();
//            }

            // update entire addr list
            addr = new long[keywordCount][2 + 2 * Constant.getHashBlockCount()];
            stage = "0";
            stageLabel = "6";
            createThreads(stage, stageLabel);


//            System.out.println("after");
//            for (long[] a : addr) {
//                for (long b : a) {
//                    System.out.print(b + " ");
//                }
//                System.out.println();
//            }


            // send to server
            doubleDSharesLong = new long[serverCount][keywordCount][2 + 2 * Constant.getHashBlockCount()];
            doubleDataLong = addr;
            stageLabel = "3";
            createThreads(stage, stageLabel);

            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            // sending search keyword shares and client id to the server
            for (int i = 0; i < serverCount; i++) {
                data2D = doubleDSharesLong[Math.floorMod(i - 1, 3)];
                sendToServer(data2D, serverIP[i], serverPort[i]);
            }
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, serverCount));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());
        }

    }


    public static void task02(long[] data, int threadNum) {

        int batchSize = (int) Math.ceil(data.length / (double) numThreads);
        long[] shares;
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;

        if (end > data.length) {
            end = data.length;
        }

//        System.out.println(start+" "+end);

        for (int i = start; i < end; i++) {
            shares = shamirSecretSharingAsLong(data[i], serverCount);
            for (int j = 0; j < serverCount; j++)
                singleDSharesLong[j][i] = shares[j];
        }

    }

    public static void updateOptValues() throws NoSuchAlgorithmException, IOException {
        // computing original hash digest of position values
        StringBuilder hDigestS = new StringBuilder("");
        StringBuilder temp;
//        System.out.println("startingPos:" + startingPos);
        for (int i = 0; i < Constant.getHashBlockCount(); i++) {
            temp = new StringBuilder(String.valueOf(phase2Interpolation[(i + startingPos) % optCol]));
//            System.out.println((i + startingPos) % optCol);
            while (temp.length() < Constant.getHashBlockSize()) {
                temp.insert(0, "0");
            }
            hDigestS.append(temp);
        }

//        System.out.println("old:" + hDigestS);

        // create new hash digest for new file id
        String hDigestC = hashDigest(String.valueOf(hDigestS.append(newFileId)));
//        System.out.println("new:" + hDigestC);

        long[] temp1 = getHashBlocks(hDigestC);
//        {
//
//        freeSlot = true;
//        System.out.println("Time:" + freeSlot);
//
//        singleDataLong = new long[optCol * optRow];
//
//        // breaking hash digest into hash blocks to compare against what is received from server
//
//
//        // finding difference between hash blocks
//        for (int i = 0; i < Constant.getHashBlockCount(); i++) {
//            singleDataLong[i + startingPos] = Helper.mod(temp1[i] -
//                    phase2Interpolation[i + (startingPos % optCol)]);
//        }

        // adding new file id
//        singleDataLong[startingPos + countItems] = newFileId;

//            System.out.println("here");
//            for (int i = startingPos; i < startingPos + optCol; i++) {
//                System.out.print(singleDataLong[i] + " ");
//            }
//            System.out.println();

//        Instant start = Instant.now();
//        stage = "0";
//        stageLabel = "2";
//        singleDSharesLong = new long[serverCount][optCol * optRow];
//        createThreads(stage, stageLabel);
//        Instant end = Instant.now();
//        System.out.println("here:" + Duration.between(start, end).toMillis());

//        removeTime.add(Instant.now());
//        comTime.add(Instant.now());
//        // sending search keyword shares and client id to the server
//        long[] data1D;
//        for (int i = 0; i < serverCount; i++) {
//            data1D = singleDSharesLong[i];
//            sendToServer(data1D, serverIP[i], serverPort[i]);
//        }
//        comTime.add(Instant.now());
//        perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, serverCount));
//        comTime = new ArrayList<>();
//        waitTime = new ArrayList<>();
//        removeTime.add(Instant.now());
//    }


//        System.out.println(((startingPos + countItems) % optCol));
//        System.out.println(phase2Interpolation[(startingPos + countItems) % optCol]);
        {
            if (((startingPos % optCol) < ((startingPos + countItems) % optCol)) &&
                    phase2Interpolation[(startingPos + countItems) % optCol] != 0) { //slot present

                freeSlot = true;

                singleDataLong = new long[optCol * optRow];

                // breaking hash digest into hash blocks to compare against what is received from server


                // finding difference between hash blocks
                for (int i = 0; i < Constant.getHashBlockCount(); i++) {
                    singleDataLong[i + startingPos] = Helper.mod(temp1[i] -
                            phase2Interpolation[i + (startingPos % optCol)]);
                }

                // adding new file id
                singleDataLong[startingPos + countItems] = newFileId;

//            System.out.println("here");
//            for (int i = startingPos; i < startingPos + optCol; i++) {
//                System.out.print(singleDataLong[i] + " ");
//            }
//            System.out.println();

                Instant start = Instant.now();
                stage = "0";
                stageLabel = "2";
                singleDSharesLong = new long[serverCount][optCol * optRow];
                createThreads(stage, stageLabel);
                Instant end = Instant.now();
//                System.out.println("here:" + Duration.between(start, end).toMillis());

                removeTime.add(Instant.now());
                comTime.add(Instant.now());
                // sending search keyword shares and client id to the server
                long[] data1D;
                for (int i = 0; i < serverCount; i++) {
                    data1D = singleDSharesLong[i];
                    sendToServer(data1D, serverIP[i], serverPort[i]);
                }
                comTime.add(Instant.now());
                perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, serverCount));
                comTime = new ArrayList<>();
                waitTime = new ArrayList<>();
                removeTime.add(Instant.now());
            } else {
                freeSlot = false;

//                System.out.println("freee slot not presnt");
                removeTime.add(Instant.now());
                comTime.add(Instant.now());
                long[] data1D;
                for (int i = 0; i < serverCount; i++) {
                    data1D = new long[]{0};
                    sendToServer(data1D, serverIP[i], serverPort[i]);
                }
                comTime.add(Instant.now());
                perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, serverCount));
                comTime = new ArrayList<>();
                waitTime = new ArrayList<>();
                removeTime.add(Instant.now());

//            // update the optInv
//            long[] newOpt = new long[2 * optCol];
//            newOpt[(startingPos % optCol) + countItems] = newFileId;
//
//            int k = 0;
//            for (int i = 0; i < phase2Interpolation.length; i++) {
//                if (i == (startingPos % optCol) + countItems) {
//                    k++;
//                }
//                newOpt[k] = phase2Interpolation[i];
//                k++;
//            }
//
//            for (long a : newOpt) {
//                System.out.print(a + " ");
//            }
//            System.out.println();

                singleDataLong = new long[(optCol + 1) * optRow];

                // breaking hash digest into hash blocks to compare against what is received from server


                // finding difference between hash blocks
                for (int i = 0; i < Constant.getHashBlockCount(); i++) {
                    singleDataLong[i + startingPos] = Helper.mod(temp1[i] -
                            phase2Interpolation[i + (startingPos % optCol)]);
                }

                // adding new file id
                singleDataLong[startingPos + countItems] = newFileId;

//            System.out.println("here2");
//            for (int i = startingPos; i <= startingPos + countItems; i++) {
//                System.out.print(singleDataLong[i] + " ");
//            }
//            System.out.println();


                stage = "0";
                stageLabel = "2";
                singleDSharesLong = new long[serverCount][((optCol + 1) * optRow) + 1];
                createThreads(stage, stageLabel);

                removeTime.add(Instant.now());
                comTime.add(Instant.now());
                // sending search keyword shares and client id to the server
                for (int i = 0; i < serverCount; i++) {
                    singleDSharesLong[i][(optCol + 1) * optRow] = startingPos / optCol; // the row of the data
                    data1D = singleDSharesLong[i];
                    sendToServer(data1D, serverIP[i], serverPort[i]);
                }
                comTime.add(Instant.now());
                perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, serverCount));
                comTime = new ArrayList<>();
                waitTime = new ArrayList<>();
                removeTime.add(Instant.now());

                optRow++;
            }
        }
    }


    // multithreaded across number of keywords
    private static void task11(int threadNum) {
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
                shares[j] = new BigInteger(objectReadString1D[j][i]);
            }
            interpolatedValue = lagrangeInterpolationAsBigInteger(shares);
//            System.out.print(interpolatedValue + " ");
            if (interpolatedValue.equals(value0)) {
                phase1Result = i;
            }
        }
    }

    public static void getKeywordIndex() throws IOException {
        // to store the stage
        stage = "1";
        phase1Result = -1;
        serverCount = 3;
        // creating shares for the keyword
        createShares(searchKeyword);
        removeTime.add(Instant.now());
        comTime.add(Instant.now());

//        System.out.println(searchKeyword);
        // sending search keyword shares and client id to the server
        BigInteger[] data1D = new BigInteger[1];
        for (int i = 0; i < serverCount; i++) {
//            System.out.println(keywordShares[Math.floorMod(i - 1, 3)]);
            data1D[0] = keywordShares[Math.floorMod(i - 1, 3)];
            sendToServer(data1D, serverIP[i], serverPort[i]);
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
        serverCount = 3;
        objectReadString1D = new String[serverCount][];
        readObjectsAsString(type); // reading data sent by servers
        cleanUp();
        keywordCount = (objectReadString1D[0].length - 1); // since last element stores the label for the server
        stageLabel = "1";
        createThreads(stage, stageLabel); // running threads to interpolate the data
    }

    // multithreaded across number of keywords
    private static void task21(int threadNum) {

        int batchSize = (int) Math.ceil(keywordCount / (double) numThreads);
        long[] shares;
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;

        if (end > keywordCount) {
            end = keywordCount;
        }

        for (int i = start; i < end; i++) {
            shares = shamirSecretSharingAsLong(keywordVector[i], serverCount);
            for (int j = 0; j < serverCount; j++)
                keywordVectorShares[j][i] = shares[j];
        }
    }

    private static void readAddrTable() {
        long interpolatedValue;
        long[] shares = new long[serverCount];

        for (int i = 0; i < serverSharesAsLong_1D[0].length - 1; i++) {
            for (int j = 0; j < serverCount; j++) {
                shares[j] = serverSharesAsLong_1D[j][i];
            }
            interpolatedValue = lagrangeInterpolationAsLong(shares);
            System.out.print(interpolatedValue + " ");
            if (i == 0) {
                startingPos = (int) interpolatedValue;
            } else if (i == 1) {
                countItems = (int) interpolatedValue;
            } else {
                indexHashList[i - 2] = interpolatedValue;
            }
        }
        System.out.println();
    }

    private static void getAddrData() throws IOException, NoSuchAlgorithmException {
        stage = "2";
        serverCount = 3;

        // preparing  addr/keyword vector share for sending to server to retrieve the addr data for the keyword
        keywordVector = new long[keywordCount];
        keywordVector[phase1Result] = 1;
        keywordVectorShares = new long[serverCount][keywordCount];

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

        removeTime.add(Instant.now());
        comTime.add(Instant.now());
        startClient(serverCount);
        comTime.add(Instant.now());
        perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, serverCount));
        comTime = new ArrayList<>();
        waitTime = new ArrayList<>();
        removeTime.add(Instant.now());

        type = "1D";
        serverSharesAsLong_1D = new long[serverCount][];
        readObjectsAsLong(type);
        cleanUp();

        // process the data received from server to get the file ids
        // get position in opt_inv, number of files for keyword and hash values from addr table
        indexHashList = new long[2 * Constant.getHashBlockCount()];
        readAddrTable();
    }

    // multithreaded across number of opt inverted index row and col
    private static void task22(int threadNum) {
        int batchSize = (int) Math.ceil((optRow) / (double) numThreads);
        long[] shares;
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;

        if (end > (optRow)) {
            end = (optRow);
        }

        for (int i = start; i < end; i++) {
            shares = shamirSecretSharingAsLong(optInvRowVec[i], serverCount);
            for (int j = 0; j < serverCount; j++)
                optInvRowVecShare[j][i] = shares[j];
        }
    }

    private static void phase2ResultInterpolation() {

        long[] shares = new long[serverCount];
//        System.out.println(optCol);
        for (int i = 0; i < optCol; i++) {
//            System.out.println(i);
            for (int j = 0; j < serverCount; j++) {
                shares[j] = serverSharesAsLong_1D[j][i];
            }
            phase2Interpolation[i] = lagrangeInterpolationAsLong(shares);
//            System.out.print(phase2Interpolation[i] + " ");
        }
//        System.out.println();
    }

    public static void getOptValues() throws IOException {
        stage = "2";
        // create vector to extract file_ids from opt_inv and another vector for extracting only particular columns
        optInvRowVec = new long[optRow];
        optInvRowVec[startingPos / optCol] = 1;

        optInvRowVecShare = new long[serverCount][optRow];
        optIndexShare = new long[serverCount][1][optRow];

        stageLabel = "2";
        createThreads(stage, stageLabel);

        removeTime.add(Instant.now());
        comTime.add(Instant.now());
        long[][] data2D; // sending share to the server
        for (int i = 0; i < serverCount; i++) {
            optIndexShare[i][0] = optInvRowVecShare[i];
            data2D = optIndexShare[i];
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

        type = "1D";
        serverSharesAsLong_1D = new long[serverCount][];
        readObjectsAsLong(type);
        cleanUp();

        phase2Result = new ArrayList<>();
        hash_list = new long[Constant.getHashBlockCount()];
        phase2Interpolation = new long[optCol];
        phase2ResultInterpolation();
    }


    /**
     * to add new files with existing keywords
     *
     * @throws IOException
     * @throws NoSuchAlgorithmException
     */
    public static void addFilesOpt() throws IOException, NoSuchAlgorithmException {
        serverCount = 3;
        // get keyword index
        getKeywordIndex();

        // to inform the servers to terminate if client has no access on the keyword or does not wish to continue
        if (phase1Result == -1) {
            log.info("Not found '" + searchKeyword + "'.");
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

        getAddrData();

        getOptValues();
        updateOptValues();

        updateAddrData(freeSlot);
    }


    public static void task07(BigInteger[][] data, int threadNum) {

        int batchSize = (int) Math.ceil(data.length / (double) numThreads);
        BigInteger[] shares;
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;

        if (end > data.length) {
            end = data.length;
        }

        for (int k = start; k < end; k++) {
            for (int i = 0; i < data[0].length; i++) {
                shares = shamirSecretSharingAsBigInt(new StringBuilder(data[k][i].toString()), serverCount);
                for (int j = 0; j < serverCount; j++)
                    doubleDSharesBig[j][k][i] = shares[j];
            }
        }
    }


    public static void task09(StringBuilder[][] data, int threadNum) {

        Instant start1 = Instant.now();

        int batchSize = (int) Math.ceil(data.length / (double) numThreads);
        BigInteger[] shares;
        long[] sharesLong;
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;

        if (end > data.length) {
            end = data.length;
        }

//        System.out.println(start + " " + end);
        int l = data[0].length;
        for (int k = start; k < end; k++) {
            StringBuilder[] temp = data[k];
            for (int i = 0; i < l; i++) {
                if(i==phase1Result){
                    shares = shamirSecretSharingAsBigInt(temp[i], serverCount);
                    for (int j = 0; j < serverCount; j++)
                        doubleDSharesBigString[j][k][0].append(shares[j]).append(",");
                }else {
                    sharesLong = shamirSecretSharingAsLong(Long.parseLong(temp[i].toString()), serverCount);
                    for (int j = 0; j < serverCount; j++)
                        doubleDSharesBigString[j][k][0].append(sharesLong[j]).append(",");
                }
            }
        }
        Instant end1 = Instant.now();
//        System.out.println("Time:" + Duration.between(start1, end1).toMillis());
    }


    public static void deleteKeywordOpt() throws IOException, NoSuchAlgorithmException {

        serverCount = 3;
        getKeywordIndex();

        // to inform the servers to terminate if client has no access on the keyword or does not wish to continue
        if (phase1Result == -1) {
            log.info("Not found '" + searchKeyword + "'.");

            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            for (int i = 0; i < serverCount; i++) {
                sendToServer(new long[][]{{0}}, serverIP[i], serverPort[i]);
            }

            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, serverCount));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());

            System.exit(0);
        }
        System.out.println("The index of keyword " + searchKeyword + " is " + (phase1Result + 1) + ".");

        // update the act list

        StringBuilder[][] actUpdate = new StringBuilder[clientCount + 2][keywordCount];
        for (int i = 0; i < clientCount + 2; i++) {
            for (int j = 0; j < keywordCount; j++) {
                actUpdate[i][j] = new StringBuilder("0");
            }
        }
        for (int i = 0; i < clientCount; i++) {
            actUpdate[i + 2][phase1Result] = new StringBuilder(noAccessCode[phase1Result].toString());
        }

        // send the act list

        serverCount = 4;
        stage = "0";
        doubleDataBigString = actUpdate;
//        System.out.println(actUpdate[0][0]);
        actUpdate = null;
//        System.out.println(doubleDataLong.length);
//        System.out.println(doubleDataLong[0].length);
//        System.out.println(doubleDataLong[0][0]);
        doubleDSharesBigString = new StringBuilder[serverCount][clientCount + 2][1];
        for (int j = 0; j < serverCount; j++) {
            for (int i = 0; i < (clientCount + 2); i++) {
                doubleDSharesBigString[j][i][0]=new StringBuilder("");
            }
        }
        stageLabel = "9";
        createThreads(stage, stageLabel);

        removeTime.add(Instant.now());
        comTime.add(Instant.now());
        // sending search keyword shares and client id to the server


        byte[][][] result = new byte[serverCount][clientCount+2][];
        for (int j = 0; j < serverCount; j++) {
//            System.out.println("j:"+j);
            for (int i = 0; i < (clientCount + 2); i++) {
                result[j][i] = doubleDSharesBigString[j][i][0].toString().getBytes(StandardCharsets.UTF_8);
//                System.out.println(doubleDSharesBigString[j][i][0].toString());
            }
        }


        byte[][] data2D;

        for (int i = 0; i < serverCount; i++) {
            if (i <= 2) {
                data2D = result[Math.floorMod(i - 1, 3)];
            } else {
                data2D = result[i];
            }
            sendToServer(data2D, serverIP[i], serverPort[i]);
//            System.out.println("sent");
        }
        comTime.add(Instant.now());
        perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, serverCount));
        comTime = new ArrayList<>();
        waitTime = new ArrayList<>();
        removeTime.add(Instant.now());


//        {
//            // update the addr list
//            serverCount = 3;
//            getAddrData();
//
//            long[][] addrUpdate = new long[keywordCount][2 + 2 * Constant.getHashBlockCount()];
//            addrUpdate[phase1Result][0] = Helper.mod(-startingPos);
//            addrUpdate[phase1Result][1] = Helper.mod(-countItems);
//            for (int i = 0; i < 2 * Constant.getHashBlockCount(); i++) {
//                addrUpdate[phase1Result][2 + i] = Helper.mod(-indexHashList[i]);
//            }
//
//            // send the addr list
//
//            Instant start = Instant.now();
//            stage = "0";
//            doubleDataLong = addrUpdate;
//            doubleDSharesLong = new long[serverCount][keywordCount][2 + 2 * Constant.getHashBlockCount()];
//            stageLabel = "3";
//            createThreads(stage, stageLabel);
//            Instant end = Instant.now();
//            System.out.println("here11:" + Duration.between(start, end).toMillis());
//
//            removeTime.add(Instant.now());
//            comTime.add(Instant.now());
//            // sending search keyword shares and client id to the server
//            long[][] data2DD;
//            serverCount = 3;
//            for (int i = 0; i < serverCount; i++) {
//                data2DD = doubleDSharesLong[Math.floorMod(i - 1, 3)];
//                sendToServer(data2DD, serverIP[i], serverPort[i]);
//            }
//            comTime.add(Instant.now());
//            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, serverCount));
//            comTime = new ArrayList<>();
//            waitTime = new ArrayList<>();
//            removeTime.add(Instant.now());
//        }
    }

    public static void deleteFileOpt() throws IOException, NoSuchAlgorithmException {

        serverCount = 3;
        getKeywordIndex();

        // to inform the servers to terminate if client has no access on the keyword or does not wish to continue
        if (phase1Result == -1) {
            log.info("Not found '" + searchKeyword + "'.");

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

        getAddrData();

        getOptValues();


//        System.out.println("be");
//        for (long a : phase2Interpolation) {
//            System.out.print(a + " ");
//        }
//        System.out.println();

        // update the file ids
        String hDigestC = hashDigest(searchKeyword);
        singleDataLong = new long[optCol * optRow];
        for (int i = 0; i < countItems; i++) {
            if (i >= Constant.getHashBlockCount()) {
                if (phase2Interpolation[(i + startingPos) % optCol] != newFileId)
                    hDigestC = hashDigest(hDigestC + newFileId);
            }
            if (phase2Interpolation[(i + startingPos) % optCol] == newFileId) {
                singleDataLong[startingPos + i] = Helper.mod(-newFileId);
            }
        }


//        System.out.println(hDigestC);
        // create new hash digest for new file id
        long[] temp1 = getHashBlocks(hDigestC);

        for (int i = 0; i < Constant.getHashBlockCount(); i++) {
            singleDataLong[i + startingPos] = Helper.mod(temp1[i] -
                    phase2Interpolation[i + (startingPos % optCol)]);
        }


//        System.out.println("sing");
//        for (long a : singleDataLong) {
//            System.out.print(a + " ");
//        }
//        System.out.println();

        stage = "0";
        stageLabel = "2";
        singleDSharesLong = new long[serverCount][optCol * optRow];
        createThreads(stage, stageLabel);

        removeTime.add(Instant.now());
        comTime.add(Instant.now());
        // sending search keyword shares and client id to the server
        long[] data1D;
        for (int i = 0; i < serverCount; i++) {
            data1D = singleDSharesLong[i];
            sendToServer(data1D, serverIP[i], serverPort[i]);
        }
        comTime.add(Instant.now());
        perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, serverCount));
        comTime = new ArrayList<>();
        waitTime = new ArrayList<>();
        removeTime.add(Instant.now());
    }


    // multithreaded across number of keywords
    private static void task13(int threadNum) {
        BigInteger interpolatedValue;
        int batchSize = (int) Math.ceil(keywordCount / (double) numThreads);
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;

        if (end > keywordCount) {
            end = keywordCount;
        }

        BigInteger value0 = BigInteger.valueOf(0);
        BigInteger[] shares = new BigInteger[serverCount];

        for (int i = start; i < end; i++) {

            for (int j = 0; j < serverCount; j++) {
                shares[j] = new BigInteger(objectReadString1D[j][i]);
            }
            interpolatedValue = lagrangeInterpolationAsBigInteger(shares);
            if (interpolatedValue.equals(value0) || interpolatedValue.equals(noAccessCode[i])) {
                phase1Result = i;
                phase1ResultAccess = interpolatedValue;
            }
        }
//        System.out.println();
    }

    /**
     * Generate no access code for each keyword same across all clients for a given keyword
     */
    public static void noAccessCodeGenerate() {
        noAccessCode = new BigInteger[keywordCount];
        BigInteger bigInteger = Constant.getMaxLimitNoAccess().subtract(Constant.getMinLimitNoAccess());
        int len = Constant.getMaxLimitNoAccess().bitLength();
        BigInteger res;
        for (int i = 0; i < keywordCount; i++) {
//            Random randNum = new Random((seedDBO + (i + 1)));
            Random randNum = new Random((seedDBO));
            res = new BigInteger(len, randNum);
            if (res.compareTo(Constant.getMinLimitNoAccess()) < 0)
                noAccessCode[i] = res.add(Constant.getMinLimitNoAccess());
            if (res.compareTo(bigInteger) >= 0)
                noAccessCode[i] = res.mod(bigInteger).add(Constant.getMinLimitNoAccess());
        }
    }

    /**
     * To perform cleanup tasks in course of program execution
     */
    public static void cleanUpOpData() {
        perServerTime = new ArrayList<>();
        removeTime = new ArrayList<>();
        comTime = new ArrayList<>();
        waitTime = new ArrayList<>();
    }

    /**
     * create shares of updated access
     *
     * @param data
     * @param threadNum
     */
    public static void task01(BigInteger[] data, int threadNum) {

        int batchSize = (int) Math.ceil(data.length / (double) numThreads);
        BigInteger[] shares;
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;

        if (end > data.length) {
            end = data.length;
        }

        for (int i = start; i < end; i++) {
            shares = shamirSecretSharingAsBigInt(new StringBuilder(String.valueOf(data[i])), serverCount);
            for (int j = 0; j < serverCount; j++)
                singleDShares[j][i] = shares[j];
        }

    }

    /**
     * get the access and index of keyword  for that client
     *
     * @throws IOException
     */
    public static void getAccessKeyword() throws IOException {
        // to store the stage
        stage = "1";
        phase1Result = -1;
        serverCount = 3;
        // creating shares for the keyword
        createShares(searchKeyword);
        // sending to server the shares
        removeTime.add(Instant.now());
        comTime.add(Instant.now());
        // sending search keyword shares and client id to the server
        BigInteger[] data1D = new BigInteger[2];
        data1D[1] = new BigInteger(clientId);
        for (int i = 0; i < serverCount; i++) {
            data1D[0] = keywordShares[Math.floorMod(i - 1, 3)];
            sendToServer(data1D, serverIP[i], serverPort[i]);
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
        serverCount = 3;
        objectReadString1D = new String[serverCount][];
        readObjectsAsString(type); // reading data sent by servers
        cleanUp();
        keywordCount = (objectReadString1D[0].length - 1); // since last element stores the label for the server
        stageLabel = "3";
        createThreads(stage, stageLabel); // running threads to interpolate the data
        // to inform the servers to terminate if client has no access on the keyword or does not wish to continue
        if (phase1Result == -1) {
            log.info("Not found '" + searchKeyword + "'.");
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            for (int i = 0; i < serverCount; i++) {
                sendToServer(new BigInteger[]{BigInteger.valueOf(0)}, serverIP[i], serverPort[i]);
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
     * to grant or revoke access of a keyword for a given client
     *
     * @throws IOException
     */
    public static void revokeGrantAccess() throws IOException {
        serverCount = 3;
        // getting access and index for keyword
        getAccessKeyword();
//        System.out.println("Index:" + phase1Result);
//        System.out.println("Previous Access:" + phase1ResultAccess);
        // the vector containing updated access for the client for the given keyword
        serverCount = 4;
        singleData = new BigInteger[keywordCount];
        for (int i = 0; i < keywordCount; i++) {
            singleData[i] = BigInteger.valueOf(0);
        }
        singleDShares = new BigInteger[serverCount][keywordCount];
        // to update the access of the keyword for that client
        boolean flag = false;
        if (access) { // access grant
            if (!phase1ResultAccess.equals(BigInteger.valueOf(0L))) { // access not present by doing -noaccesscode
                singleData[phase1Result] = Helper.mod(BigInteger.valueOf(0).subtract(noAccessCode[phase1Result]));
                flag = true;
            }
        } else { // access revoke
            if (phase1ResultAccess.equals(BigInteger.valueOf(0L))) { // access present
                singleData[phase1Result] = noAccessCode[phase1Result];
                flag = true;
            }
        }
        // send the update access list of client to server for all keywords
        if (flag) {
            stage = "0";
            stageLabel = "1";
            createThreads(stage, stageLabel);
            StringBuilder[] temp = new StringBuilder[serverCount];
            for (int i = 0; i < serverCount; i++) {
                temp[i] = new StringBuilder("");
            }
            // appending all keywords new access
            for (int i = 0; i < serverCount; i++) {
                for (int j = 0; j < keywordCount; j++) {
                    temp[i].append(singleDShares[i][j]).append(",");
                }
                temp[i].append(clientId);
            }
            // sending new keyword access for the client
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            byte[] data1D;
            for (int i = 0; i < serverCount; i++) {
                if (i <= 2) {
                    data1D = temp[Math.floorMod(i - 1, 3)].toString().getBytes(StandardCharsets.UTF_8);
                } else {
                    data1D = temp[3].toString().getBytes(StandardCharsets.UTF_8);
                }
                sendToServer(data1D, serverIP[i], serverPort[i]);
//                System.out.println("sent");
            }
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, serverCount));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());
        } else {
            System.out.println("Access required already exists!");
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            // sending search keyword shares and client id to the server
            BigInteger[] data1D = new BigInteger[1];
            for (int i = 0; i < serverCount; i++) {
                data1D[0] = BigInteger.valueOf(0);
                sendToServer(data1D, serverIP[i], serverPort[i]);
            }
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, serverCount));
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
    public static void initialization() throws IOException, ClassNotFoundException, InstantiationException, IllegalAccessException {
        // reading the properties file for client
        Properties specificProperties = Helper.readPropertiesFile("config/DBO.properties");
        // reading the commonProperties file for client
        Properties commonProperties = Helper.readPropertiesFile("config/Common.properties");

        serverVerification = Boolean.parseBoolean(commonProperties.getProperty("serverVerification"));
        clientVerification = Boolean.parseBoolean(commonProperties.getProperty("clientVerification"));
        numThreads = Integer.parseInt(commonProperties.getProperty("numThreads"));
//        fileCount = Integer.parseInt(commonProperties.getProperty("maxDocs"));
//        console = new Scanner(System.in);
        optRow = Integer.parseInt(commonProperties.getProperty("optRow"));
        optCol = Integer.parseInt(commonProperties.getProperty("optCol"));
        clientCount = Integer.parseInt(commonProperties.getProperty("clientCount"));
        seedDBO = Integer.parseInt(specificProperties.getProperty("seedDBO"));
        keywordCount = Integer.parseInt(commonProperties.getProperty("keywordCount"));
        // reading each server Ip and port numbers
        serverCount = 4;
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

        servers_1_2 = new BigInteger[numThreads];
        servers_2_3 = new BigInteger[numThreads];
        servers_3_1 = new BigInteger[numThreads];
        cleanUp();

        noAccessCodeGenerate();
        System.out.println("Number of thread:" + numThreads);
        System.out.println("serverVerification:" + serverVerification);
        System.out.println("clientVerification:" + clientVerification);
    }

    public static void main(String[] args) throws IOException, NoSuchAlgorithmException, ClassNotFoundException, InstantiationException, IllegalAccessException, InterruptedException {
        initialization();
        // to calculate the time
        Instant start, end;
        double totalTime;

        //operation can be add or delete new/old file/keyword, revoke or grant access
        System.out.println("Please enter the code to perform the desired operation:");
        System.out.println("1: Add new file to existing or new keyword");
        System.out.println("2: Delete existing keywords");
        System.out.println("3: Delete file for existing keyword");
        System.out.println("4: Grant/revoke access on keyword");
        System.out.println("Enter the operation code from above list  ");
        int operation = Integer.parseInt(console.next());
        int count = 0;
        String fileName = "data/cleartext/keywords.txt";
        String[] keywords = Helper.readFile(fileName);
        for (int i = 0; i < Helper.getRunCount(); i++) {
            // sending operation code to server
            serverCount = 4;
            for (int j = 0; j < serverCount; j++) {
                sendToServer(operation, serverIP[j], serverPort[j]);
            }
            switch (operation) {
                case 1 -> {
                    // to add new files with existing keywords
                    System.out.println("Please enter below details:");
                    System.out.println("1. Keyword to be searched");
//                searchKeyword = console.next();
                    searchKeyword = "home";
                    System.out.println("2. New file id to add");
//                newFileId = Integer.parseInt(console.next());
                    newFileId = 20+i;
                    cleanUpOpData();
                    start = Instant.now();
                    addFilesOpt();
                    end = Instant.now();
                    totalTime = Duration.between(start, end).toMillis();
                    Helper.printTimesNew("Add new file", null, null, removeTime, perServerTime, totalTime, count);
                }
                case 2 -> {
                    System.out.println("Please enter below details:");
                    System.out.println("1. Keyword to be deleted");
//                searchKeyword = console.next();
//                    searchKeyword = "javamail";
                    searchKeyword = keywords[i];
                    perServerTime = new ArrayList<>();
                    removeTime = new ArrayList<>();
                    comTime = new ArrayList<>();
                    waitTime = new ArrayList<>();
                    start = Instant.now();
                    deleteKeywordOpt();
                    end = Instant.now();
                    totalTime = Duration.between(start, end).toMillis();
                    Helper.printTimesNew("Delete keyword", null, null, removeTime, perServerTime, totalTime, count);
                }
                case 3 -> {
                    System.out.println("Please enter below details:");
                    System.out.println("1. Keyword to be searched");
//                searchKeyword = console.next();
                    searchKeyword = "home";
                    System.out.println("2. File id to delete");
//                newFileId = Integer.parseInt(console.next());
                    newFileId = 1;
                    perServerTime = new ArrayList<>();
                    removeTime = new ArrayList<>();
                    comTime = new ArrayList<>();
                    waitTime = new ArrayList<>();
                    start = Instant.now();
                    deleteFileOpt();
                    end = Instant.now();
                    totalTime = Duration.between(start, end).toMillis();
                    Helper.printTimesNew("add", null, null, removeTime, perServerTime, totalTime, count);
                }
                case 4 -> {
//                 revoke or grant access to already existing keyword
                    System.out.println("Please enter below details:");
                    System.out.println("1. Enter client id");
//                clientId = console.next();
                    System.out.println("2. Keyword whose access to grant or revoke");
//                searchKeyword = console.next();
                    System.out.println("3. Enter 0 to grant access and 1 to revoke");
//                access = Boolean.parseBoolean(console.next());

                    clientId = "1";
                    searchKeyword = "home";
                    if (i % 2 == 0) {
                        access = false;
                    } else {
                        access = true;
                    }
                    cleanUpOpData();
                    start = Instant.now();
                    revokeGrantAccess();
                    end = Instant.now();
                    totalTime = Duration.between(start, end).toMillis();
                    Helper.printTimesNew("Grant/revoke", null, null, removeTime, perServerTime, totalTime, count);
                }
                default -> System.out.println("Enter valid code for any operation!");
            }
            count++;
        }

        System.out.println("Time taken on an average for over " + (Helper.getRunCount() - Helper.getBuffer()) + " round for each phase is below");
        Helper.timeTaken(0);
    }
}


