package src.nonopt;

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
import java.time.Duration;
import java.time.Instant;
import java.util.*;
import java.util.logging.Level;
import java.util.logging.Logger;

public class Server {

    private static Properties properties;
    private static final Logger log = Logger.getLogger(Logger.GLOBAL_LOGGER_NAME);
    private static final long modValue = Constant.getModParameter();
    // the mod value for BigInteger
    private static final BigInteger modValueBig = Constant.getModBigParameter();
    private static String actName;
    private static String invertedIndexName;
    private static String fileName;
    private static long[][] fileKeyword;
    private static int serverNumber;
    private static File file;
    private static long seedServer;
    private static ServerSocket ss;
    private static Socket socketServer;
    private static Socket socketClient;
    private static ObjectOutputStream outputStream;
    private static ObjectInputStream inputStream;
    private static Object objects;
    private static boolean serverVerification;
    private static boolean clientVerification;
    private static BigInteger searchKeywordShare;
    private static int clientId;
    private static long[] searchKeywordVectorShare;
    private static int keywordCount;
    private static List<Object> objectsList;
    private static long[][][] serverVerificationShares2D;
    private static long[][] verificationForServer;


    // to store number of files
    private static int fileCount;
    // to store the maximum length of a file
    private static int fileLength;
    private static int nextServerPort1;
    private static String nextServerIp1;
    private static int nextServerPort2;
    private static String nextServerIp2;
    private static int serverCount;
    private static long seedServerP2;
    // to store the maximum number of files a keyword can occur in
    private static int fileMaxCount;
    private static long[][] fileVectorShare;

    // to store the result for phase1
    private static StringBuilder[] phase1Result;
    private static long prgServer;
    // to store the result for phase2
    private static long[] phase2Result;
    // to store the result for phase3
    private static long[][] phase3Result;

    // for phase 2 verification phase
    private static BigInteger[][] verificationForServerThread;

    // for phase 3 verification phase
    private static long[][][] verificationForServerThreadPhase3;

    private static int numThreads;
    private static String stage;
    private static String stageLabel;
    private static ArrayList<Instant> removeTime;
    private static ArrayList<Instant> comTime = new ArrayList<>();
    private static ArrayList<Instant> waitTime = new ArrayList<>();
    private static long[][] randomShares;
    private static long[] randomSharesSum;
    private static ArrayList<Double> perServerTime;
    private static int fileRequestedCount;
    private static long[][] serverVerificationShares1D;

    // to store the act table read from file
    private static BigInteger[][] act;
    // to store the inverted index read from file
    private static long invertedIndex[][];
    // to store the file DS read from file
    private static long[][] files;
    private static long[][][] phase3ResultThread;

    // to store the server port
    private static int serverPort;
    // to store the client IP
    private static String clientIP;
    // to store the client port
    private static int clientPort;

    private static String type;
    // to stores server shares as long values for 1D array
    private static String[][] serverSharesAsString_1D;
    // to stores server shares as long values for 2D array
    private static String[][][] serverSharesAsString_2D;

    /**
     * To perform cleanup tasks in course of program execution
     */
    private static void cleanUp() {
        // re-initializing the list to hold values received from server
        objectsList = Collections.synchronizedList(new ArrayList<>());
    }

    // multithreaded across number of files
    private static void task31(int threadNum) {

        int batchSize = (int) Math.ceil((fileCount + 1) / (double) numThreads);
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;

        if (end > (fileCount + 1)) {
            end = (fileCount + 1);
        }

        for (int i = 0; i < fileRequestedCount; i++) {
            for (int j = start; j < end; j++) {
                long[] temp = fileKeyword[j];
                for (int k = 0; k < keywordCount + 1; k++) {
                    verificationForServerThreadPhase3[i][threadNum - 1][k] = Helper.mod(verificationForServerThreadPhase3[i][threadNum - 1][k]
                            + Helper.mod(temp[k] * fileVectorShare[i][j]));

                }
                temp = files[i];
                for (int k = 0; k < temp.length; k++) {
                    phase3ResultThread[i][threadNum - 1][k] = Helper.mod(phase3ResultThread[i][threadNum - 1][k]
                            + Helper.mod(fileVectorShare[i][j] * temp[k]));
                }
            }
        }
    }


    // multithreaded across the number of files
    private static void task32(int threadNum) {

        int batchSize = (int) Math.ceil((fileCount + 1) / (double) numThreads);
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;

        if (end > fileCount + 1) {
            end = fileCount + 1;
        }

        for (int m = 0; m < fileRequestedCount; m++) {
            for (int i = start; i < end; i++) {
                long[] temp = files[i];
                for (int j = keywordCount; j < temp.length; j++) {
                    phase3ResultThread[m][threadNum - 1][j - keywordCount] = Helper.mod(phase3ResultThread[m][threadNum - 1][j - keywordCount]
                            + Helper.mod(fileVectorShare[m][i] * temp[j]));
                }
            }
        }
    }

    private static void phase3() throws IOException, ClassNotFoundException {
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

        // performing phase 2 operations
        fileVectorShare = (long[][]) objects;
        fileRequestedCount = fileVectorShare.length;

        // this is executed if client is unhappy with phase2 result send by server and wants to discontinue
        if (fileVectorShare[0][0] == 0) {
            log.info("Client wishes to discontinue the search.");
            return;
        }

        // performing operation to get the file content
        phase3Result = new long[fileRequestedCount + 1][fileLength]; // 1 more to store the label for server
        phase3ResultThread = new long[fileRequestedCount][numThreads][fileLength];

        // if verification is required by servers below operation is performed
        if (serverVerification) {

            long prgServer;
            long[] shares;

            Random seedGenerator = new Random(seedServerP2);
            long[][] randomShares = new long[serverCount][keywordCount + 1 + 1]; // one for server label one for file id
            for (int i = 0; i < (keywordCount + 1); i++) {
                prgServer = Helper.mod(seedGenerator.nextLong(Constant.getMaxRandomBound() -
                        Constant.getMinRandomBound()) + Constant.getMinRandomBound());
                shares = shamirSecretSharingAsLong(prgServer, serverCount);
                for (int j = 0; j < shares.length; j++) {
                    randomShares[j][i] = shares[j];
                }
            }
            for (int j = 0; j < serverCount; j++) {
                randomShares[j][keywordCount + 1] = serverNumber;
            }

            // send random number shares to servers
            if (serverNumber == 1) {

                // sending verification result to 2 servers
                removeTime.add(Instant.now());
                comTime.add(Instant.now());
                sendToServer(randomShares[0], nextServerIp1, nextServerPort1);
                sendToServer(randomShares[1], nextServerIp2, nextServerPort2);
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
                serverVerificationShares1D = new long[serverCount][];
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
                sendToServer(randomShares[1], nextServerIp1, nextServerPort1);
                sendToServer(randomShares[2], nextServerIp2, nextServerPort2);
                comTime.add(Instant.now());
                perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 2));
                comTime = new ArrayList<>();
                waitTime = new ArrayList<>();
                removeTime.add(Instant.now());


                type = "1D";
                serverVerificationShares1D = new long[serverCount][];
                readObjectsAsLong(type);
                cleanUp();
            } else {
                // receiving verification result from 1 servers
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
                sendToServer(randomShares[2], nextServerIp1, nextServerPort1);
                sendToServer(randomShares[0], nextServerIp2, nextServerPort2);
                comTime.add(Instant.now());
                perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 2));
                comTime = new ArrayList<>();
                waitTime = new ArrayList<>();
                removeTime.add(Instant.now());

                serverVerificationShares1D = new long[serverCount][];
                type = "1D";
                readObjectsAsLong(type);
                cleanUp();

                // receiving verification result from 1 servers
                removeTime.add(Instant.now());
                comTime.add(Instant.now());
                startServerMulti();
                comTime.add(Instant.now());
                perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 2));
                comTime = new ArrayList<>();
                waitTime = new ArrayList<>();
                removeTime.add(Instant.now());

                type = "1D";
                readObjectsAsLong(type);
                cleanUp();
            }

            long[][] verificationForServer = new long[fileRequestedCount + 1][1 + keywordCount]; // file id and keyword access test
            verificationForServerThreadPhase3 = new long[fileRequestedCount + 1][numThreads][1 + keywordCount];

            Instant start = Instant.now();
            stageLabel = "3.1";
            createThreads(stage, stageLabel);
            Instant end = Instant.now();
            System.out.println("3.1  " + Duration.between(start, end).toMillis());

            long[] randomSharesSum = new long[(keywordCount + 1)];

            BigInteger[] temp1 = new BigInteger[fileRequestedCount];
            for (int i = 0; i < fileRequestedCount; i++) {
                temp1[i] = BigInteger.valueOf(0);
            }

            long[][] fileIds = new long[fileRequestedCount][1];
            for (int i = 0; i < fileRequestedCount; i++) {
                for (int j = 0; j < numThreads; j++) {
                    for (int k = 0; k < keywordCount + 1; k++) {
                        verificationForServer[i][k] = Helper.mod(verificationForServer[i][k] + verificationForServerThreadPhase3[i][j][k]);
                    }
                }
                fileIds[i][0] = verificationForServer[i][0];

                for (int k = 0; k < keywordCount + 1; k++) {
                    prgServer = 0;
                    for (int j = 0; j < serverCount; j++) {
                        if (j != (serverNumber - 1)) {
//                            System.out.println(serverVerificationShares1D[j][k]);
                            prgServer = Helper.mod(prgServer + serverVerificationShares1D[j][k]);
                        } else {
//                            System.out.println(Math.floorMod(serverNumber - 2, serverCount));
//                            System.out.println(randomShares[Math.floorMod(serverNumber - 2, serverCount)][k]);
                            prgServer = Helper.mod(prgServer + randomShares[Math.floorMod(serverNumber - 2, serverCount)][k]);
                        }
                    }
//                    System.out.print(prgServer+" ");
                    randomSharesSum[k] = prgServer;
                    verificationForServer[i][k] = Helper.mod(verificationForServer[i][k] + prgServer);
                }

//                System.out.println();
            }

            // sending to client
            verificationForServer[verificationForServer.length - 1] = new long[]{serverNumber};


            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            sendToClient(verificationForServer);
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 2));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());

            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            startServer();
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 2));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());


            long[][] received = (long[][]) objects;


//            System.out.println("received");
//            for(long[] a :received){
//                for(long b:a){
//                    System.out.print(b+" ");
//                }
//                System.out.println();
//            }

            for (int i = 0; i < fileRequestedCount; i++) {
                for (int k = 1; k < keywordCount + 1; k++) {
                    received[i][k] = Helper.mod(received[i][k] - randomSharesSum[k]);


//                    System.out.println(act[clientId][k - 1]);
//                    System.out.println(received[i][k]);
                    temp1[i] = Helper.mod(temp1[i].add(Helper.mod(BigInteger.valueOf(received[i][k])
                            .multiply(act[clientId][k - 1]))));
                }
//                System.out.println("temp:" + temp1[i]);
            }

//            for(BigInteger[] a :temp1){
//                for(BigInteger b:a){
//                    System.out.print(b+" ");
//                }
//                System.out.println();
//            }

            for (int i = 0; i < fileRequestedCount; i++) {
//                System.out.println(permutReorgVector[i + Constant.getHashBlockCount()]);
//                System.out.println(fileIds[i][0]);
                fileIds[i][0] = Helper.mod(fileIds[i][0] -
                        phase2Result[i + Constant.getHashBlockCount()]);

//                System.out.println(fileIds[i][0]);
            }

            // without test 5
            long[][] temp2 = new long[fileRequestedCount][2];

            // without test 5
//            long[][] temp2=new long[fileRequestedCount][2+fileCount];


            // test 3,4,5
            for (int i = 0; i < fileRequestedCount; i++) {
                long resultA = 0, resultA2 = 0, temp;
                for (int j = 0; j < fileCount; j++) {
                    temp = Helper.mod(fileVectorShare[i][j] * fileVectorShare[i][j]);
                    resultA = Helper.mod(resultA + fileVectorShare[i][j]);
                    resultA2 = Helper.mod(resultA2 + temp);

                    // with test 5
//                    temp2[i][j + 2] = Helper.mod(temp - fileVectorShare[i][j]);
                }

                temp2[i][0] = resultA;
                temp2[i][1] = resultA2;
            }

            StringBuilder[] temp3 = new StringBuilder[fileRequestedCount];
            byte[][] result = new byte[fileRequestedCount + 1][];
            for (int i = 0; i < fileRequestedCount; i++) {
                temp3[i] = new StringBuilder("");
                temp3[i].append(fileIds[i][0]).append(",").append(temp1[i]).append(",");

                for (int j = 0; j < temp2[i].length; j++) {
                    temp3[i].append(temp2[i][j]).append(",");
                }
                result[i] = temp3[i].toString().getBytes(StandardCharsets.UTF_8);
            }
            result[result.length - 1] = String.valueOf(serverNumber).getBytes(StandardCharsets.UTF_8);


            if (serverNumber == 1) {

                // sending verification result to 2 servers
                removeTime.add(Instant.now());
                comTime.add(Instant.now());
                sendToServer(result, nextServerIp1, nextServerPort1);
                sendToServer(result, nextServerIp2, nextServerPort2);
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

                serverSharesAsString_2D = new String[serverCount][][];
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
                sendToServer(result, nextServerIp1, nextServerPort1);
                sendToServer(result, nextServerIp2, nextServerPort2);
                comTime.add(Instant.now());
                perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 2));
                comTime = new ArrayList<>();
                waitTime = new ArrayList<>();
                removeTime.add(Instant.now());


                serverSharesAsString_2D = new String[serverCount][][];
                type = "2D";
                readObjectsAsString(type);
                cleanUp();
            } else {
                // receiving verification result from 1 servers
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
                sendToServer(result, nextServerIp1, nextServerPort1);
                sendToServer(result, nextServerIp2, nextServerPort2);
                comTime.add(Instant.now());
                perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 2));
                comTime = new ArrayList<>();
                waitTime = new ArrayList<>();
                removeTime.add(Instant.now());

                serverSharesAsString_2D = new String[serverCount][][];
                type = "2D";
                readObjectsAsString(type);
                cleanUp();

                // receiving verification result from 1 servers
                removeTime.add(Instant.now());
                comTime.add(Instant.now());
                startServerMulti();
                comTime.add(Instant.now());
                perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 2));
                comTime = new ArrayList<>();
                waitTime = new ArrayList<>();
                removeTime.add(Instant.now());

                type = "2D";
                readObjectsAsString(type);
                cleanUp();
            }


            // interpolate
            BigInteger[] testResultBig = new BigInteger[fileRequestedCount];


            //  without test 5
            long[][] testResultLong = new long[fileRequestedCount][3];

            // with test 5
//            long[][] testResultLong = new long[fileRequestedCount][3 + fileCount];


            // uncomment to use without test 5
//            long[][] hashRes = new long[fileRequestedCount][3];

            shares = new long[serverCount];
            BigInteger[] sharesBig = new BigInteger[serverCount];


            for (int i = 0; i < fileRequestedCount; i++) {
                for (int j = 0; j < 2 + temp2[0].length; j++) {
                    if (j != 1) {
                        for (int l = 0; l < serverCount; l++) {
                            if (l == (serverNumber - 1)) {
                                if (j != 0) {
                                    shares[l] = temp2[i][j - 2];
                                } else {
                                    shares[l] = verificationForServer[i][0];
                                }
                            } else {
                                shares[l] = Long.parseLong(serverSharesAsString_2D[l][i][j]);
                            }
                        }
                        if (j == 0) {
                            testResultLong[i][j] = lagrangeInterpolationAsLong(shares);
                        } else {
                            testResultLong[i][j - 1] = lagrangeInterpolationAsLong(shares);
                        }
                    } else {
                        for (int l = 0; l < serverCount; l++) {
                            if (l == (serverNumber - 1)) {
                                sharesBig[l] = temp1[i];
                            } else {
                                sharesBig[l] = new BigInteger(serverSharesAsString_2D[l][i][j]);
                            }
                        }
                        testResultBig[i] = lagrangeInterpolationAsBigInteger(sharesBig);
                    }
                }
            }


            boolean flag = true;
            for (int i = 0; i < fileRequestedCount; i++) {

//                System.out.println("i:"+i);
//                System.out.println(testResultLong[i][0]);
//                System.out.println(testResultBig[i]);
//                System.out.println(testResultLong[i][1]);
//                System.out.println(testResultLong[i][2]);
                if (testResultLong[i][0] != 0
                        || !(testResultBig[i].equals(BigInteger.valueOf(0)))
                        || testResultLong[i][1] != 1
                        || testResultLong[i][2] != 1) {
                    flag = false;
                    break;
                }
            }

            // with test 5
//            if (flag) {
//                for (int i = 0; i < fileRequestedCount; i++) {
//                    for (int j = 2; j < fileCount; j++) {
//                        if (testResultLong[i][j] != 0) {
//                            flag = false;
//                            break;
//                        }
//                    }
//                }
//            }

            if (!flag) {
                log.info("Client has prepared an incorrect file vector.");

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
        } else {
            stageLabel = "3.2";
            createThreads(stage, stageLabel);
        }

        for (int i = 0; i < fileRequestedCount; i++) {
            for (int j = 0; j < numThreads; j++) {
                for (int k = 0; k < fileLength; k++) {
                    phase3Result[i][k] = Helper.mod(phase3Result[i][k] + phase3ResultThread[i][j][k]);
                }
            }
        }

        phase3Result[phase3Result.length - 1] = new long[]{serverNumber};

        removeTime.add(Instant.now());
        comTime.add(Instant.now());
        sendToClient(phase3Result);
        comTime.add(Instant.now());
        perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
        comTime = new ArrayList<>();
        waitTime = new ArrayList<>();
        removeTime.add(Instant.now());

    }

    //    // multithreaded across number of keywords
    private static void task21(int threadNum) {
//        int batchSize = (int) Math.ceil(keywordCount / (double) numThreads);
//        int start = (threadNum - 1) * batchSize;
//        int end = start + batchSize;
//
//        if (end > keywordCount) {
//            end = keywordCount;
//        }
//
//        String[] keywords = act[0];
//        String[] access = act[clientId];
//
//        verificationForServerThread[threadNum - 1][0] = BigInteger.valueOf(0);
//        verificationForServerThread[threadNum - 1][1] = BigInteger.valueOf(0);
//        for (int i = start; i < end; i++) {
//            verificationForServerThread[threadNum - 1][0] = Helper.mod(Helper.mod(new BigInteger(keywords[i]).
//                    multiply(new BigInteger(String.valueOf(searchKeywordVectorShare[i])))).add(verificationForServerThread[threadNum - 1][0]));
//            verificationForServerThread[threadNum - 1][1] = Helper.mod(Helper.mod(new BigInteger(access[i]).
//                    multiply(new BigInteger(String.valueOf(searchKeywordVectorShare[i])))).add(verificationForServerThread[threadNum - 1][1]));
//        }
    }

    // multithreaded across the column i.e. the file ids of inverted index
    private static void task22(int threadNum) {
        int batchSize = (int) Math.ceil((invertedIndex[0].length) / (double) numThreads);
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;

        if (end > invertedIndex[0].length) {
            end = invertedIndex[0].length;
        }

        for (int i = 0; i < invertedIndex.length; i++) {
            long[] temp = invertedIndex[i];

            for (int j = start; j < end; j++) {
                phase2Result[j] = (phase2Result[j] +
                        (temp[j] * searchKeywordVectorShare[i])%modValue)%modValue;
            }
        }
    }

    // multithreaded across number of keywords
    private static void task24(int threadNum) {
        int batchSize = (int) Math.ceil(keywordCount / (double) numThreads);
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;

        if (end > keywordCount) {
            end = keywordCount;
        }

        BigInteger[] keywords = act[0];
        BigInteger[] access = act[clientId];

        verificationForServerThread[threadNum - 1][0] = BigInteger.valueOf(0);
        verificationForServerThread[threadNum - 1][1] = BigInteger.valueOf(0);
        for (int i = start; i < end; i++) {
            verificationForServerThread[threadNum - 1][0] = Helper.mod(Helper.mod(keywords[i].
                    multiply(BigInteger.valueOf(searchKeywordVectorShare[i]))).add(verificationForServerThread[threadNum - 1][0]));
            verificationForServerThread[threadNum - 1][1] = Helper.mod(Helper.mod(access[i].
                    multiply(BigInteger.valueOf(searchKeywordVectorShare[i]))).add(verificationForServerThread[threadNum - 1][1]));
        }
    }

    private static boolean phase2() throws InterruptedException, IOException, ClassNotFoundException {
        stage = "2";
        serverCount=3;

        // Waiting for client to send the data
        removeTime.add(Instant.now());
        comTime.add(Instant.now());
        startServer();
        comTime.add(Instant.now());
        perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
        comTime = new ArrayList<>();
        waitTime = new ArrayList<>();
        removeTime.add(Instant.now());

        System.out.println("hello");

        // performing phase 2 operations
        searchKeywordVectorShare = (long[]) objects;

        // this will execute if the client is unhappy with servers results in phase 1 and wants to end the search op
        if (searchKeywordVectorShare[0] == 0) {
            log.info("Client wishes to discontinue the search.");
            return true;
        }

        // if verification is required by servers to check if keywords vector sent by client is in accordance to the keyword
        // search by client in phase1
//        if (serverVerification) {
//            // performing test 1 and test 2
//            verificationForServerThread = new BigInteger[numThreads][2];
//            stageLabel = "2.4";
//            createThreads(stage, stageLabel);
//
//            BigInteger[] verificationForServer = new BigInteger[2];
//
//            verificationForServer[0] = BigInteger.valueOf(0);
//            verificationForServer[1] = BigInteger.valueOf(0);
//            for (int i = 0; i < numThreads; i++) {
//                verificationForServer[0] = Helper.mod(verificationForServer[0].add(verificationForServerThread[i][0]));
//                verificationForServer[1] = Helper.mod(verificationForServer[1].add(verificationForServerThread[i][1]));
//
//            }
//            verificationForServer[0] = Helper.mod(verificationForServer[0].subtract(searchKeywordShare));
//
//            // for test 3, 4, 5
//
//            // without test 5
//            long[] result = new long[2]; // one for sum(A) and one for sum(A^2)
//
//            // with test 5
////            long result[] = new long[2 + keywordCount]; // keywordcount for sum(a^2) -sum(A)
//
//            long temp1;
//            for (int i = 0; i < keywordCount; i++) {
//                temp1 = Helper.mod(searchKeywordVectorShare[i] * searchKeywordVectorShare[i]);
//
//                result[0] = Helper.mod(result[0] + searchKeywordVectorShare[i]);
//                result[1] = Helper.mod(result[1] + temp1);
//
//                // with test 5
////                result[i + 2] = Helper.mod(temp1 - searchKeywordVectorShare[i]);
//            }
//
//            StringBuilder temp = new StringBuilder("");
//
//            //preparing data to sent to server
//            temp.append(verificationForServer[0]).append(",").append(verificationForServer[1]).append(",");
//            for (long l : result) {
//                temp.append(l).append(",");
//            }
//            temp.append(serverNumber);
//
//            // converting to byte array
//            byte[] byteList = temp.toString().getBytes(StandardCharsets.UTF_8);
//
//
//            if (serverNumber == 1) {
//
//                // sending verification data to two servers
//                removeTime.add(Instant.now());
//                comTime.add(Instant.now());
//                sendToServer(byteList, nextServerIp1, nextServerPort1);
//                sendToServer(byteList, nextServerIp2, nextServerPort2);
//                comTime.add(Instant.now());
//                perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 2));
//                comTime = new ArrayList<>();
//                waitTime = new ArrayList<>();
//                removeTime.add(Instant.now());
//
//
//                // receiving verification data from two servers
//                removeTime.add(Instant.now());
//                comTime.add(Instant.now());
//                startServerMulti();
//                comTime.add(Instant.now());
//                perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 2));
//                comTime = new ArrayList<>();
//                waitTime = new ArrayList<>();
//                removeTime.add(Instant.now());
//
//
//                type = "1D";
//                serverSharesAsString_1D = new String[serverCount][];
//                readObjectsAsString(type);
//                cleanUp();
//            } else if (serverNumber == 2) {
//
//                // receiving verification data from two servers
//                removeTime.add(Instant.now());
//                comTime.add(Instant.now());
//                startServerMulti();
//                comTime.add(Instant.now());
//                perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 2));
//                comTime = new ArrayList<>();
//                waitTime = new ArrayList<>();
//                removeTime.add(Instant.now());
//
//                type = "1D";
//                serverSharesAsString_1D = new String[serverCount][];
//                readObjectsAsString(type);
//                cleanUp();
//
//                // sending verification data to two servers
//                removeTime.add(Instant.now());
//                comTime.add(Instant.now());
//                sendToServer(byteList, nextServerIp1, nextServerPort1);
//                sendToServer(byteList, nextServerIp2, nextServerPort2);
//                comTime.add(Instant.now());
//                perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 2));
//                comTime = new ArrayList<>();
//                waitTime = new ArrayList<>();
//                removeTime.add(Instant.now());


//            } else {
//                // receiving verification data from two servers
//                removeTime.add(Instant.now());
//                comTime.add(Instant.now());
//                startServerMulti();
//                comTime.add(Instant.now());
//                perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 2));
//                comTime = new ArrayList<>();
//                waitTime = new ArrayList<>();
//                removeTime.add(Instant.now());
//
//                // sending verification data to two servers
//                removeTime.add(Instant.now());
//                comTime.add(Instant.now());
//                sendToServer(byteList, nextServerIp1, nextServerPort1);
//                sendToServer(byteList, nextServerIp2, nextServerPort2);
//                comTime.add(Instant.now());
//                perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 2));
//                comTime = new ArrayList<>();
//                waitTime = new ArrayList<>();
//                removeTime.add(Instant.now());
//
//                type = "1D";
//                serverSharesAsString_1D = new String[serverCount][];
//                readObjectsAsString(type);
//                cleanUp();
//
//                // receiving verification data from two servers
//                removeTime.add(Instant.now());
//                comTime.add(Instant.now());
//                startServerMulti();
//                comTime.add(Instant.now());
//                perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 2));
//                comTime = new ArrayList<>();
//                waitTime = new ArrayList<>();
//                removeTime.add(Instant.now());
//
//                type = "1D";
//                readObjectsAsString(type);
//                cleanUp();
//            }
//
//            // interpolate
//            BigInteger[] resInterBig = new BigInteger[2]; // verification data interpolation
//
//            // without test 5
//            long[] resInter = new long[2]; // two tests
//
//            // with test 5
////            long[] resInter = new long[2 + keywordCount];
//
//            long[] sharesLong = new long[serverCount];
//            BigInteger[] sharesBig = new BigInteger[serverCount];
//
//            for (int i = 0; i < verificationForServer.length + result.length; i++) {
//                if (i >= 2) { // test 3,4,5
//                    for (int p = 0; p < serverCount; p++) {
//                        if (p == (serverNumber - 1)) {
//                            sharesLong[p] = result[i - 2];
//                        } else {
//                            sharesLong[p] = Long.parseLong(serverSharesAsString_1D[p][i]);
//                        }
//                    }
//                    resInter[i - 2] = lagrangeInterpolationAsLong(sharesLong);
//                } else { // test 1,2
//                    for (int p = 0; p < serverCount; p++) {
//                        if (p == (serverNumber - 1)) {
//                            sharesBig[p] = verificationForServer[i];
//                        } else {
//                            sharesBig[p] = new BigInteger(serverSharesAsString_1D[p][i]);
//                        }
//                    }
//                    resInterBig[i] = lagrangeInterpolationAsBigInteger(sharesBig);
//                }
//            }
//
//            System.out.println(resInterBig[0]);
//            System.out.println(resInterBig[1]);
//            System.out.println(resInter[0]);
//            System.out.println(resInter[1]);
//            boolean flag = resInterBig[0].equals(BigInteger.valueOf(0)) && resInterBig[1].equals(BigInteger.valueOf(0))
//                    && resInter[0] == 1 && resInter[1] == 1;
//
//            // with test 5
////            if (flag) {
////                for (int i = 2; i < resInterBig.length; i++) {
////                    if (resInter[0] != 0) {
////                        flag = false;
////                        break;
////                    }
////                }
//            }

//            if (!flag) {
//                log.info("Client has prepared an incorrect keyword vector.");
//
//                removeTime.add(Instant.now());
//                comTime.add(Instant.now());
//                sendToClient(new long[]{0, serverNumber});
//                comTime.add(Instant.now());
//                perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
//                comTime = new ArrayList<>();
//                waitTime = new ArrayList<>();
//                removeTime.add(Instant.now());
//                return true;
//            }
//        }

        // performing operation to get the file ids
        phase2Result = new long[fileMaxCount + Constant.getHashBlockCount() + 1]; // 1 to store the label for the server

        stageLabel = "2.2";
        createThreads(stage, stageLabel);

//        for(long a:phase2Result){
//            System.out.print(a+", ");
//        }
//        System.out.println();

        phase2Result[phase2Result.length - 1] = serverNumber;
        removeTime.add(Instant.now());
        comTime.add(Instant.now());
        sendToClient(phase2Result);
        comTime.add(Instant.now());
        perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
        System.out.println("b:"+Helper.calculateSendToServerTime(comTime, waitTime, 1));
        comTime = new ArrayList<>();
        waitTime = new ArrayList<>();
        removeTime.add(Instant.now());

        return false;
    }


    // multithreaded across number of keywords
    private static void task11(int threadNum) {
        int batchSize = (int) Math.ceil(keywordCount / (double) numThreads);
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;

        if (end > keywordCount) {
            end = keywordCount;
        }

        BigInteger[] keywords = act[0];
        BigInteger[] access = act[clientId];
        BigInteger temp;


        for (int i = start; i < end; i++) {
            temp = Helper.mod((Helper.mod(Helper.mod(keywords[i].subtract(searchKeywordShare)).add(access[i])))
                    .multiply(BigInteger.valueOf(randomSharesSum[i])));
            phase1Result[threadNum - 1].append(temp).append(",");
        }

    }

    public static void createRandomShares() throws IOException, ClassNotFoundException {
        long prgServer;
        long[] shares;

        Random seedGenerator = new Random(seedServerP2);
        randomShares = new long[serverCount][keywordCount + 1]; // one for server label
        for (int i = 0; i < keywordCount; i++) {
            prgServer = Helper.mod(seedGenerator.nextLong(Constant.getMaxRandomBound() -
                    Constant.getMinRandomBound()) + Constant.getMinRandomBound());
            shares = shamirSecretSharingAsLong(prgServer, serverCount);
            for (int j = 0; j < shares.length; j++) {
                randomShares[j][i] = shares[j];
            }
        }
        for (int j = 0; j < serverCount; j++) {
            randomShares[j][keywordCount] = serverNumber;
        }

        // send random number shares to servers
        if (serverNumber == 1) {
            sendToServer(randomShares[0], nextServerIp1, nextServerPort1);
            sendToServer(randomShares[1], nextServerIp2, nextServerPort2);
            waitTime = new ArrayList<>();
            startServerMulti();
            waitTime = new ArrayList<>();
            type = "1D";
            serverVerificationShares1D = new long[serverCount][];
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
            serverVerificationShares1D = new long[serverCount][];
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
            serverVerificationShares1D = new long[serverCount][];
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
    }

    private static void phase1() throws InterruptedException, IOException, ClassNotFoundException {
        stage = "1";

        // Waiting for client to send the search keyword shares
        removeTime.add(Instant.now());
        comTime.add(Instant.now());
        startServer();
        comTime.add(Instant.now());
        perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
        comTime = new ArrayList<>();
        waitTime = new ArrayList<>();
        removeTime.add(Instant.now());

        // Performing phase1 operation on the data received from the client
        // reading the data sent by client
        searchKeywordShare = ((BigInteger[]) objects)[0];
        clientId = ((BigInteger[]) objects)[1].intValue() + 1; // since 1st row are keywords and 2nd row are position of keywords

        // initilializing
        for (int i = 0; i < numThreads; i++) {
            phase1Result[i] = new StringBuilder("");
        }


        removeTime.add(Instant.now());
        createRandomShares();
        randomSharesSum = new long[keywordCount];
        long prgServer;
        for (int k = 0; k < keywordCount; k++) {
            prgServer = 0;
            for (int j = 0; j < serverCount; j++) {
                if (j != (serverNumber - 1)) {
                    prgServer = Helper.mod(prgServer + serverVerificationShares1D[j][k]);
                } else {
                    prgServer = Helper.mod(prgServer + randomShares[Math.floorMod(serverNumber - 2, serverCount)][k]);
                }
            }
            randomSharesSum[k] = prgServer;
        }
        removeTime.add(Instant.now());

        // computing phase 1 operation on ACT list
        stageLabel = "1.1";
        createThreads(stage, stageLabel);

        // adding thread data
        for (int i = 1; i < numThreads; i++) {
            phase1Result[0].append(phase1Result[i]);
        }
        phase1Result[0].append(Math.floorMod(serverNumber - 2, serverCount) + 1);

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


    private static void sendToClient(Object data) {

        try {
            waitTime.add(Instant.now());
            socketClient = new Socket(clientIP, clientPort);
            outputStream = new ObjectOutputStream(socketClient.getOutputStream());
            waitTime.add(Instant.now());

            Instant start=Instant.now();
            outputStream.writeObject(data);
            Instant end=Instant.now();
            System.out.println(Duration.between(start,end).toMillis());

//            waitTime.add(Instant.now());
//            socketClient.close();
//            waitTime.add(Instant.now());
        } catch (IOException ex) {
            log.log(Level.SEVERE, ex.getMessage());
        }
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

    /**
     * To read values from objects as long
     *
     * @param type the type of object as 1D or 2D
     */
    private static void readObjectsAsLong(String type) {
        if (type.equals("1D")) {
            for (int i = 0; i < objectsList.size(); i++) {
                int temp = (int) (((long[]) objectsList.get(i))[((long[]) objectsList.get(i)).length - 1]);
                serverVerificationShares1D[temp - 1] = ((long[]) objectsList.get(i));
            }
        } else if (type.equals("2D")) {
            for (int i = 0; i < objectsList.size(); i++) {
                int temp = (int) (((long[][]) objectsList.get(i))[((long[][]) objectsList.get(i)).length - 1][0]);
                serverVerificationShares2D[temp - 1] = ((long[][]) objectsList.get(i));
            }
        }
    }

    private static void sendToServer(Object data, String serverIp, int serverPort) {

        try {
            waitTime.add(Instant.now());
            socketClient = new Socket(serverIp, serverPort);
            outputStream = new ObjectOutputStream(socketClient.getOutputStream());
            waitTime.add(Instant.now());

            outputStream.writeObject(data);

//            waitTime.add(Instant.now());
//            socketClient.close();
//            waitTime.add(Instant.now());
        } catch (IOException ex) {
            log.log(Level.SEVERE, ex.getMessage());
        }
    }


    /**
     * To read values from objects as long
     *
     * @param type the type of object as 1D or 2D
     */
    private static void readObjectsAsString(String type) {
        if (type.equals("1D")) {
            for (int i = 0; i < objectsList.size(); i++) {
                String objectRead = new String((byte[]) objectsList.get(i), StandardCharsets.UTF_8);
                int temp = objectRead.charAt(objectRead.length() - 1) - '0';
                serverSharesAsString_1D[temp - 1] = objectRead.split(",");
            }

        } else if (type.equals("2D")) {
            for (int i = 0; i < objectsList.size(); i++) {
                byte[][] data = (byte[][]) objectsList.get(i);
                int temp = new String(data[data.length - 1], StandardCharsets.UTF_8).charAt(0) - '0';
                serverSharesAsString_2D[temp - 1] = new String[fileRequestedCount][];
                for (int j = 0; j < data.length - 1; j++) {
                    serverSharesAsString_2D[temp - 1][j] = new String(data[j], StandardCharsets.UTF_8).split(",");
                }
//                for (String[] a : serverSharesAsString_2D[temp - 1]) {
//                    for (String b : a) {
//                        System.out.print(b + " ");
//                    }
//                    System.out.println();
//                }
            }
        }

    }

    private static void startServerMulti() throws IOException, ClassNotFoundException {

        if (serverNumber != 3) {
            while (objectsList.size() != (serverCount - 1)) {
                //Reading data from the server
                waitTime.add(Instant.now());
                socketClient = ss.accept();
                inputStream = new ObjectInputStream(socketClient.getInputStream());
                waitTime.add(Instant.now());

                objectsList.add(inputStream.readObject());

            }
        } else {
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
     * Create share for secret value as long
     *
     * @param secret      the secret value as long
     * @param serverCount the number of servers for which shares are to be created
     * @return the share of the secret value as long is returned for given number of server as servercount
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


    private static void startServer() {

        try {

            System.out.println("Server" + serverNumber + " Listening........");
            waitTime.add(Instant.now());
            socketServer = ss.accept();
            inputStream = new ObjectInputStream(socketServer.getInputStream());
            waitTime.add(Instant.now());

            objects = inputStream.readObject();

        } catch (IOException | ClassNotFoundException ex) {
            log.log(Level.SEVERE, ex.getMessage());
        }
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
            } else if (stage.equals("2")) {
                if (stageLabel.equals("2.1")) {
                    task21(threadNum);
                } else if (stageLabel.equals("2.2")) {
                    task22(threadNum);
                } else if (stageLabel.equals("2.4")) {
                    task24(threadNum);
                }
            } else if (stage.equals("3")) {
                if (stageLabel.equals("3.1")) {
                    task31(threadNum);
                } else if (stageLabel.equals("3.2")) {
                    task32(threadNum);
                }
            }

        }
    }

    private static void createThreads(String stage, String stageLabel) {
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


    private static void readDataStructures() throws IOException {

//        actName = "act" + serverNumber + ".txt";
//        actName = "act" + (Math.floorMod(serverNumber - 2, serverCount) + 1) + ".txt";
        invertedIndexName = "invertedIndex" + serverNumber + ".txt";
//        invertedIndexName = "invertedIndex" + (Math.floorMod(serverNumber - 2, serverCount) + 1) + ".txt";
//        fileName = "file" + serverNumber + ".txt";
//        String fileKeywordName = "fileKeyword" + serverNumber + ".txt";


//        file = new File("data/share/" + actName);
//        act = Helper.readFileAsBigInt(file);
        file = new File("data/share/" + invertedIndexName);
        invertedIndex = Helper.readFileAsLong(file);
//        file = new File("data/share/" + fileName);
//        files = Helper.readFileAsLong(file);
//        file = new File("data/share/" + fileKeywordName);
//        fileKeyword = Helper.readFileAsLong(file);

//        keywordCount = act[0].length;
        fileMaxCount = invertedIndex[0].length - Constant.getHashBlockCount();
//        fileCount = files.length - 1;
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

                break;
            case 2:
                serverPort = Integer.parseInt(properties.getProperty("serverPort2"));
                nextServerIp1 = properties.getProperty("serverIP3");
                nextServerPort1 = Integer.parseInt(properties.getProperty("serverPort3"));
                nextServerIp2 = properties.getProperty("serverIP1");
                nextServerPort2 = Integer.parseInt(properties.getProperty("serverPort1"));

                break;
            case 3:
                serverPort = Integer.parseInt(properties.getProperty("serverPort3"));
                nextServerIp1 = properties.getProperty("serverIP1");
                nextServerPort1 = Integer.parseInt(properties.getProperty("serverPort1"));
                nextServerIp2 = properties.getProperty("serverIP2");
                nextServerPort2 = Integer.parseInt(properties.getProperty("serverPort2"));

                break;
            case 4:
                serverPort = Integer.parseInt(properties.getProperty("serverPort4"));
                nextServerIp1 = properties.getProperty("serverIP1");
                nextServerPort1 = Integer.parseInt(properties.getProperty("serverPort1"));
                nextServerIp2 = properties.getProperty("serverIP2");
                nextServerPort2 = Integer.parseInt(properties.getProperty("serverPort2"));

                break;
        }
    }

    /**
     * Performs initialization tasks like reading from the properties files, initial memory allocation etc
     *
     * @throws IOException
     */
    private static void initialization(String[] args) throws IOException {

        // determining the server id
        serverNumber = Integer.parseInt(args[0]);

        // reading the specificProperties file for server
        Properties specificProperties = Helper.readPropertiesFile("config/Server" + serverNumber + ".properties");
        // reading the commonProperties file for server
        Properties commonProperties = Helper.readPropertiesFile("config/Common.properties");

        serverVerification = Boolean.parseBoolean(commonProperties.getProperty("serverVerification"));
        clientPort = Integer.parseInt(commonProperties.getProperty("clientPort"));
        clientIP = commonProperties.getProperty("clientIP");

        fileLength = Integer.parseInt(commonProperties.getProperty("maxFileLength"));
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

    public static void main(String args[]) throws IOException, InterruptedException, ClassNotFoundException {

        // to calculate the time
        Instant start, end;
        double totalTime;

        // to store the phase value
        int phase;
        // to check if the phase1 is to be run or not due to verification flag
        boolean phase1Flag = false;

        initialization(args);

        // to store client/server program for experiment
        int type = serverNumber;
        // the number of times program was run for experiment
        int count = 0;

        while (true) {
            if (clientVerification)
                phase1Flag = true;
            else {
                if (serverNumber <= 3)
                    phase1Flag = true;
            }

//            if (phase1Flag) {
//
//                System.out.println("Start of Phase 1.");
//                System.out.println("---------------------------------------");
//
//                // phase 1
//                phase1Result = new StringBuilder[numThreads];
//                perServerTime = new ArrayList<>();
//                removeTime = new ArrayList<>();
//                waitTime = new ArrayList<>();
//                comTime = new ArrayList<>();
//                start = Instant.now();
//                phase1();
//                end = Instant.now();
//                phase = 1;
//                totalTime = Duration.between(start, end).toMillis();
//                Helper.printTimes(phase, null, null, removeTime, perServerTime, totalTime, count);
//                System.out.println("End of Phase 1.");
//
//                //GC
//                phase1Result = null;
//            }


            System.out.println("Start of Phase 2.");
            System.out.println("---------------------------------------");

            perServerTime = new ArrayList<>();
            removeTime = new ArrayList<>();
            start = Instant.now();
            boolean flag = phase2();
            end = Instant.now();
            phase = 2;
            totalTime = Duration.between(start, end).toMillis();
            Helper.printTimes(phase, null, null, removeTime, perServerTime, totalTime, count);
            System.out.println("End of Phase 2.");

//            if (!flag) {
//                System.out.println("Start of Phase 3.");
//                System.out.println("---------------------------------------");
//
//                perServerTime = new ArrayList<>();
//                removeTime = new ArrayList<>();
//                start = Instant.now();
//                phase3();
//                end = Instant.now();
//                phase = 3;
//                totalTime = Duration.between(start, end).toMillis();
//                Helper.printTimes(phase, null, null, removeTime, perServerTime, totalTime, count);
//                System.out.println("End of Phase 3.");
//            }

            count++;

            if (count == Helper.getRunCount()) {
                count = 0;
                System.out.println("Time taken on an average for over " + (Helper.getRunCount() - Helper.getBuffer()) + " round for each phase is below");
                Helper.timeTaken(type);
            }
        }
    }
}
