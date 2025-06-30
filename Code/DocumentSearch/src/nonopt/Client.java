package src.nonopt;

import constants.Constant;
import org.tartarus.snowball.SnowballStemmer;
import utility.Helper;

import java.io.*;
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

public class Client extends Thread {

    private static Properties properties;
    private static final Logger log = Logger.getLogger(Logger.GLOBAL_LOGGER_NAME);
    private static final long modValue = Constant.getModParameter();
    private static final int hashBlockCount = Constant.getHashBlockCount();
    private static final int hashBlockSize = Constant.getHashBlockSize();
    // the mod value for BigInteger
    private static final BigInteger modValueBig = Constant.getModBigParameter();
    private static String searchKeyword;
    private static int indexKey;
    private static String clientId;
    private static List<Object> objects;
    private static int serverCount;
    private static long[][][] verificationServer2DPhase3;
    private static long[][] serverVerificationPhase3;
    private static BigInteger[] keywordShares;
    private static long[][] keywordVectorShares;
    private static long[] shares;
    //    private static String[] data1D;
//    private static long[][] data2D;
    private static int keywordCount;
    private static long[] keywordVector;

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
    private static long[][] hash;
    private static String type;
    private static int numThreads;
    private static String stage;
    private static String stageLabel;
    private static boolean flagCVP1;
    private static BigInteger[] servers_1_2;
    private static BigInteger[] servers_2_3;
    private static BigInteger[] servers_3_1;
    private static ArrayList<Instant> comTime = new ArrayList<>();
    private static ArrayList<Instant> waitTime = new ArrayList<>();
    private static Scanner console;
    private static int fileLength;

    // to stores server shares as string values for 1D array
    private static BigInteger[][] serverSharesAsBigInteger_1D;
    // to stores server shares as string values for 2D array
    private static BigInteger[][][] serverSharesAsBigInteger_2D;
    // to stores server shares as long values for 1D array
    private static long[][] serverSharesAsLong_1D;
    // to stores server shares as long values for 2D array
    private static long[][][] serverSharesAsLong_2D;

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

    // to store stemmer object
    private static SnowballStemmer stemmer;

    // to store the numeric version of text
    private static StringBuilder numericText;
    // to store the updates text
    private static StringBuilder newText;

    private static String[][] serverSharesAsString_1D;
    // to stores server shares as long values for 2D array
    private static String[][][] serverSharesAsString_2D;

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

        int batchSize = (int) Math.ceil((fileVectors[0].length) / (double) numThreads);
        long[] shares;
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;

        if (end > fileVectors[0].length) {
            end = fileVectors[0].length;
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

    private static void phase3() throws IOException, NoSuchAlgorithmException {

        stage = "3";
        serverCount = 3;

        //TODO: delete
        List<Long> phaseResultTemp = phase2Result;
        phase2Result = new ArrayList<>();
        phase2Result.add(phaseResultTemp.get(0));

        // preparing fileVectors vector for sending to server
        fileVectors = new long[phase2Result.size()][fileCount + 1];
        int k = 0;
        for (long file : phase2Result) {
            fileVectors[k][(int) (file - 1)] = 1;
//            fileVectors[k][(int) (file+1) -1] = 1;  // Test for client correctness for server: test 1
            fileVectors[k][(int) (file + 1) - 1] = 2;  // Test for client correctness for server: test 2, 3, 4

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
            data2D = fileVectorsShares[i];
            sendToServer(data2D, serverIP[i], serverPort[i]);
        }
        comTime.add(Instant.now());
        perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, serverCount));
        comTime = new ArrayList<>();
        waitTime = new ArrayList<>();
        removeTime.add(Instant.now());

        // perform tasks so that server can verify that the file vector sent is the vector based on result from phase 2
        if (serverVerification) {
            // waiting for server to send the verification data
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
                data2D = verificationServer2DPhase3[i];
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
                log.info("Client has prepared an incorrect file vector.");
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
//                        log.info("The files content provided by the servers is incorrect.");
//                        flag=false;
//                        System.exit(0);
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
            Helper.writeToFile(String.valueOf(phase3Result[i][0]), finalContent[i], stage);
        }
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

    // multithreaded across number of fileMaxCount and hashSize
    private static void task22(int threadNum) {

        long interpolatedValue;

        int batchSize = (int) Math.ceil((fileMaxCount + Constant.getHashBlockCount()) / (double) numThreads);
        long[] shares = new long[serverCount];
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;

        if (end > fileMaxCount + Constant.getHashBlockCount()) {
            end = fileMaxCount + Constant.getHashBlockCount();
        }

        for (int i = start; i < end; i++) {
            for (int j = 0; j < serverCount; j++) {
                shares[j] = serverSharesAsLong_1D[j][i];
            }
            interpolatedValue = lagrangeInterpolationAsLong(shares);
            if (i < Constant.getHashBlockCount()) {
                hash_list[i] = interpolatedValue;
            } else {
                if (interpolatedValue != 0)
                    phase2Result.add(interpolatedValue);
            }
        }
    }

    private static void phase2() throws IOException, NoSuchAlgorithmException {

        stage = "2";
        serverCount = 3;

        // preparing  addr/keyword vector share for sending to server to retrieve the addr data for the keyword
        keywordVector = new long[keywordCount];
        keywordVector[phase1Result] = 1;
//        keywordVector[phase1Result + 1] = 1; // Test 1,2
//        keywordVector[phase1Result] = 3; // Test 3,4,5
        keywordVectorShares = new long[serverCount][keywordCount];

        stageLabel = "2.1";
        createThreads(stage, stageLabel);

        removeTime.add(Instant.now());
        comTime.add(Instant.now());
        long[] data1D; // sending share to the server
        for (int i = 0; i < serverCount; i++) {
            data1D = keywordVectorShares[i];
            sendToServer(data1D, serverIP[i], serverPort[i]);
        }
        comTime.add(Instant.now());
        perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, serverCount));
        comTime = new ArrayList<>();
        waitTime = new ArrayList<>();
        removeTime.add(Instant.now());

        // perform tasks so that server can verify that the vector sent is the vector based on result from phase 1
        if (serverVerification) {
//            removeTime.add(Instant.now());
//            comTime.add(Instant.now());
//            startClient(serverCount);
//            comTime.add(Instant.now());
//            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, serverCount));
//            comTime = new ArrayList<>();
//            waitTime = new ArrayList<>();
//            removeTime.add(Instant.now());
//
//            type = "1D";
//            serverSharesAsLong_1D = new long[serverCount][];
//            readObjectsAsLong(type);
//            cleanUp();
//
//            boolean flag = true;
//
//            for (int j = 0; j < serverCount; j++) {
//                if (serverSharesAsLong_1D[j][0] == 0) {
//                    flag = false;
//                    break;
//                }
//            }
//
//            if (!flag) {
//                log.info("Client has prepared an incorrect keyword vector.");
//                System.exit(0);
//            }
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
            serverSharesAsLong_1D = new long[serverCount][];
            readObjectsAsLong(type);
            cleanUp();
        }

        // process the data received from server to get the file ids

        fileMaxCount = serverSharesAsLong_1D[0].length - Constant.getHashBlockCount() - 1; // since last index stores the label for server
        phase2Result = new ArrayList<>();
        hash_list = new long[Constant.getHashBlockCount()];

        stageLabel = "2.2";
        createThreads(stage, stageLabel);

//        if (clientVerification) {
//
//            String hash = hashDigest(searchKeyword);
//            long[] hashClient = new long[Constant.getHashBlockCount()];
//
//            // getting hash digest for file ids received
//            for (long fileId : phase2Result) {
//                hash = hashDigest(hash + fileId);
//            }
//
//            // breaking hash digest into hash blocks to compare against what is received from server
//            int j = 0;
//            for (int i = 0; i < hash.length(); i = i + Constant.getHashBlockSize()) {
//                int end = i + Constant.getHashBlockSize();
//                if (end > hash.length())
//                    end = hash.length();
//                hashClient[j] = Long.parseLong(hash.substring(i, end));
//                j++;
//            }
//
//            // formatting hash blocks to compare against each other
//            for (int i = 0; i < Constant.getHashBlockCount(); i++) {
////                hash_list[i] = 90; // to test server correctness on file ids sent to client
//                if (!(hash_list[i] == hashClient[i])) {
//                    log.info("The files id/s provided by the servers is incorrect.");
//
//                    comTime.add(Instant.now());
//                    for (int p = 0; p < serverCount; p++) {
//                        sendToServer(new long[][]{{0}}, serverIP[p], serverPort[p]);
//                    }
//                    comTime.add(Instant.now());
//
//                    System.exit(0);
//                }
//            }
//
//        }

        System.out.println("The file/s with keyword " + searchKeyword + " are stores in results folder. ");
        StringBuilder fileIds = new StringBuilder("");
//        for (long file : phase2Result) {
//            fileIds.append(file).append(",");
//        }
//        Helper.writeToFile("fileIds", String.valueOf(fileIds), stage);
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
                shares[j] = new BigInteger(serverSharesAsString_1D[j][i]);
            }
            interpolatedValue = lagrangeInterpolationAsBigInteger(shares);
            if (interpolatedValue.equals(value0)) {
                phase1Result = i;
            }
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

            s1 = new BigInteger(serverSharesAsString_1D[0][i]);
            s2 = new BigInteger(serverSharesAsString_1D[1][i]);
            s3 = new BigInteger(serverSharesAsString_1D[2][i]);

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


    private static void phase1() throws IOException {
        // to store the stage
        stage = "1";
        phase1Result = -1;

        // creating shares for the keyword
        createShares(searchKeyword);

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
        serverSharesAsString_1D = new String[serverCount][];
        readObjectsAsString(type); // reading data sent by servers
        cleanUp();
        keywordCount = (serverSharesAsString_1D[0].length - 1); // since last element stores the label for the server

        if (!clientVerification) {
            stageLabel = "1.1";
            createThreads(stage, stageLabel); // running threads to interpolate the data
        } else {
            flagCVP1 = true;

            stageLabel = "1.2";
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
            phase1Result = indexKey;
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
     * To perform cleanup tasks in course of program execution
     */
    private static void cleanUp() {
        // re-initializing the list to hold values received from server
        objects = Collections.synchronizedList(new ArrayList<>());
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
     * To interpolate string values
     *
     * @param share the string value of the shares
     * @return the cleartext/interpolated value
     */
    private static BigInteger lagrangeInterpolationAsBigInteger(BigInteger share[]) {

        return switch (share.length) {
            case 2 -> Helper.mod(Helper.mod(new BigInteger(String.valueOf(2)).multiply(share[0]))
                    .subtract(share[1]));
            case 3 -> Helper.mod(Helper.mod(Helper.mod(new BigInteger(String.valueOf(3))
                    .multiply(share[0])).subtract(Helper.mod(new BigInteger(String.valueOf(3))
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

    public static long lagrangeInterpolationAsLong(long[] share) {
        return switch (share.length) {
            case 2 -> Math.floorMod((((2 * share[0]) % modValue) - share[1]), modValue);
            case 3 -> (Math.floorMod((((3 * share[0]) % modValue) -
                    ((3 * share[1]) % modValue)), modValue) + share[2]) % modValue;
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
        } catch (IOException | ClassNotFoundException ex) {
            log.log(Level.SEVERE, ex.getMessage());
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
    private static void sendToServer(Object data, String IP, int port) throws IOException {

        try {
            waitTime.add(Instant.now());
            // creating server socket and output stream
            socketServer = new Socket(IP, port);
            outputStream = new ObjectOutputStream(socketServer.getOutputStream());
            waitTime.add(Instant.now());

            // writing data to stream
            outputStream.writeObject(data);

//            waitTime.add(Instant.now());
//            // closing the socket
//            socketServer.close();
//            waitTime.add(Instant.now());
        } catch (IOException ex) {
            log.log(Level.SEVERE, ex.getMessage());
        }
    }


    private static BigInteger lagrangeInterpolationCustomized(BigInteger share[], int i, int j) {

        return Helper.mod(Helper.mod(BigInteger.valueOf(i).multiply(share[0])).subtract(Helper.mod(BigInteger.valueOf(j).multiply(share[1]))));
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
            if (stage.equals("1")) {
                if (stageLabel.equals("1.1"))
                    task11(threadNum);
                else if (stageLabel.equals("1.2")) {
                    task12(threadNum);
                }
            } else if (stage.equals("2")) {
                if (stageLabel.equals("2.1")) {
                    task21(threadNum);
                } else if (stageLabel.equals("2.2")) {
                    task22(threadNum);
                }

            } else if (stage.equals("3")) {
                if (stageLabel.equals("3.1")) {
                    task31(threadNum);
                } else if (stageLabel.equals("3.2")) {
                    task32(threadNum);
                } else if (stageLabel.equals("3.3")) {
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
    private static BigInteger[] shamirSecretSharingAsBigInteger(String secret, int serverCount) {
        Random rand = new Random();
        BigInteger[] share = new BigInteger[serverCount];

        // choosing the slope value for line
        long slope = rand.nextInt(Constant.getMaxRandomBound() - Constant.getMinRandomBound()) +
                Constant.getMinRandomBound();

        // check if the secret size is enough for long or BigInteger calculation
        for (int i = 0; i < serverCount; i++) {
            share[i] = Helper.mod(Helper.mod(new BigInteger(String.valueOf(i + 1))
                    .multiply(new BigInteger(String.valueOf(slope)))).add(new BigInteger(secret)));
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
    public static long[] shamirSecretSharingAsLong(long secret, int serverCount) {
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
     * TO convert string to numeric representation
     *
     * @param text The input text
     */
    public static void convertToNumeric(String text) {
        numericText = new StringBuilder();
        newText = new StringBuilder();
        char letter;
        int asciiValue;
        for (int i = 0; i < text.length(); i++) {
            letter = text.charAt(i);
            asciiValue = (int) letter;

            // considering only special characters, alphabets and numbers
            if (32 <= asciiValue && asciiValue <= 126) {
                // converting all ascii values to two digits for easy reconstruction of file
                if (asciiValue == 96)
                    numericText.append("10");
                else if (97 <= asciiValue && asciiValue <= 122)
                    numericText.append(asciiValue - 32);
                else if (123 <= asciiValue)
                    numericText.append(asciiValue - 112);
                else
                    numericText.append(asciiValue);

                // only those letter of the text within the ascii range 32-126
                newText.append(letter);
            }
        }
    }

    /**
     * Process input keyword and create share for secret value
     *
     * @param searchKeyword the secret value
     * @return the share of the secret value is returned for given number of server as servercount
     */
    private static void createShares(String searchKeyword) {

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

    /**
     * Convert keyword to number
     *
     * @param data the keyword
     * @return the numeric format of keyword
     */
    public static String keywordToNumber(String data) {
        numericText = new StringBuilder("");
        for (int i = 0; i < data.length(); i++) {
            numericText = numericText.append((int) data.charAt(i) - 86);
        }
        return numericText.toString();

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
        BigInteger slope = BigInteger.valueOf(rand.nextInt(Constant.getMaxRandomBound() - Constant.getMinRandomBound()) +
                Constant.getMinRandomBound());

        // check if the secret size is enough for long or BigInteger calculation
        for (int i = 0; i < serverCount; i++) {
            share[i] = Helper.mod(Helper.mod(BigInteger.valueOf(i + 1).multiply(slope)).add(secretBig));
        }

        return share;
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
                serverSharesAsString_1D[temp - 1] = objectRead.split(",");
            }

        } else if (type.equals("2D")) {
            for (int i = 0; i < objects.size(); i++) {
                byte[][] data = (byte[][]) objects.get(i);
                int temp = new String(data[data.length - 1], StandardCharsets.UTF_8).charAt(0) - '0';
                System.out.println("Server nu:" + temp);
                serverSharesAsString_2D[temp - 1] = new String[phase2Result.size()][];
                for (int j = 0; j < data.length - 1; j++) {
                    serverSharesAsString_2D[temp - 1][j] = new String(data[j], StandardCharsets.UTF_8).split(",");
                }
            }
        }
    }

    /**
     * Performs initialization tasks like reading from the properties files, initial memory allocation etc
     *
     * @throws IOException
     */
    private static void initialization() throws IOException, ClassNotFoundException, InstantiationException, IllegalAccessException {


        // reading the commonProperties file for client
        Properties commonProperties = Helper.readPropertiesFile("config/Common.properties");

        serverVerification = Boolean.parseBoolean(commonProperties.getProperty("serverVerification"));
        clientVerification = Boolean.parseBoolean(commonProperties.getProperty("clientVerification"));
        numThreads = Integer.parseInt(commonProperties.getProperty("numThreads"));

        fileCount = Integer.parseInt(commonProperties.getProperty("fileCount"));

        console = new Scanner(System.in);

        // reading each server Ip and port numbers
        serverCount = 3;

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

    public static void main(String[] args) throws IOException, NoSuchAlgorithmException, ClassNotFoundException, InstantiationException, IllegalAccessException {

        String actName = "keywords.txt";
        File file = new File("data/cleartext/" + actName);

        // to store all lines of the file
        ArrayList<String> lines = new ArrayList<>();

        BufferedReader bf = new BufferedReader(new FileReader(file));
        String line = bf.readLine();

        // reading all lines
        while (line != null) {
            lines.add(line);
            line = bf.readLine();
        }

        // to store file into array
        String[] act;
        act = lines.get(0).split(",");


        // to calculate the time
        Instant start, end;
        double totalTime;

        // to store the phase value
        int phase;

        initialization();

        // the number of times program was run for experiment
        int limit = Helper.getRunCount();
        int count = 0;

        // to store client/server program for experiment
        int type = 0;

        int j = 0;
        // to iterate for the experiment run count
        for (int i = 0; i < Helper.getRunCount(); i++) {
            Helper.cleanResultFolder();
            // request input from the client

            // the client id making the search for keyword
            System.out.println("Enter client id authorised to search the keyword!");
//            clientId = console.next();
            clientId = "1";
            // the keyword search by the client
            System.out.println("Enter a keyword to search!");
//            searchKeyword = console.next();
            searchKeyword = act[i];
            indexKey = i;

//            //phase 1
//            servers_1_2 = new BigInteger[numThreads];
//            servers_2_3 = new BigInteger[numThreads];
//            servers_3_1 = new BigInteger[numThreads];
//            System.out.println("Start of Phase 1.");
//            System.out.println("---------------------------------------");
//            perServerTime = new ArrayList<>();
//            removeTime = new ArrayList<>();
//            start = Instant.now();
//            phase1();
//            end = Instant.now();
//            phase = 1;
//            totalTime = Duration.between(start, end).toMillis();
//            Helper.printTimes(phase, null, null, removeTime, perServerTime, totalTime, count);
//            System.out.println("End of Phase 1.");
//            //GC
//            servers_1_2 = null;
//            servers_2_3 = null;
//            servers_3_1 = null;
//            keywordShares = null;
//            serverSharesAsString_1D = null;

            phase1Result = 0;
            keywordCount = 5000;
            System.out.println("Start of Phase 2.");
            System.out.println("---------------------------------------");
            perServerTime = new ArrayList<>();
            removeTime = new ArrayList<>();
            start = Instant.now();
            phase2();
            end = Instant.now();
            phase = 2;
            totalTime = Duration.between(start, end).toMillis();
            Helper.printTimes(phase, null, null, removeTime, perServerTime, totalTime, count);
            System.out.println("End of Phase 2.");
            j++;
//            System.out.println("Start of Phase 3.");
//            System.out.println("---------------------------------------");
//            perServerTime = new ArrayList<>();
//            removeTime = new ArrayList<>();
//            start = Instant.now();
//            phase3();
//            end = Instant.now();
//            phase = 3;
//            totalTime = Duration.between(start, end).toMillis();
//            Helper.printTimes(phase, null, null, removeTime, perServerTime, totalTime, count);
//            System.out.println("End of Phase 3.");

            count++;
        }

        System.out.println("Time taken on an average for over " + (Helper.getRunCount() - Helper.getBuffer()) + " round for each phase is below");
        Helper.timeTaken(type);

    }
}


