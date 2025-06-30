package src.opt;

import constants.Constant;
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

public class ServerDBO {

    private static Properties properties;
    private static final Logger log = Logger.getLogger(Logger.GLOBAL_LOGGER_NAME);

    private static String actName;
    private static String invertedIndexName;
    private static String fileName;
    private static String fileKeywordName;
    private static int serverNumber;
    private static File file;
    private static long seedServer;
    private static long seedServerP2;
    private static ServerSocket ss;
    private static Socket socketServer;
    private static Socket socketClient;
    private static ObjectOutputStream outputStream;
    private static ObjectInputStream inputStream;
    private static Object objects;
    private static List<Object> objectsList;
    private static boolean serverVerification;
    private static boolean clientVerification;
    private static BigInteger searchKeywordShare;
    private static int clientId;
    private static long[] searchKeywordVectorShare;
    private static int keywordCount;
    // the mod value
    private static final long modValue = Constant.getModParameter();
    // the mod value for BigInteger
    private static final BigInteger modValueBig = Constant.getModBigParameter();
    // to store number of files
    private static int fileCount;
    // to store the maximum length of a file
    private static int fileLength;
    // to store the maximum number of files a keyword can occur in
    private static int fileMaxCount;
    private static long[][] fileVectorShare;

    // to store the result for phase1
    private static StringBuilder[] phase1Result;
    // to store the result for phase2
    private static long[] phase2Result;
    // to store the result for phase3
    private static long[][] phase3Result;

    // for phase 2 verification phase
    private static BigInteger[][] verificationForServerThread;
    private static BigInteger[] verificationForServer;

    // for phase 3 verification phase
    private static long[][][] verificationForServerThreadPhase3;

    private static int numThreads;
    private static String stage;
    private static String stageLabel;
    private static ArrayList<Instant> removeTime;
    private static ArrayList<Instant> comTime = new ArrayList<>();
    private static ArrayList<Instant> waitTime = new ArrayList<>();
    private static ArrayList<Double> perServerTime;
    private static int fileRequestedCount;
    private static String[] newAccess;

    private static long[] newOptInv;
    private static long[][] newAddr;
    private static byte[][] actUpdate;

    private static int operation;

    // to store the act table read from file
    private static BigInteger[][] act;
    private static BigInteger[][] act_old;
    // to store the inverted index read from file
    private static long invertedIndex[][];
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
    private static BigInteger[] phase2AddrResultBigint;
    private static String addrName;
    private static String optInvName;
    private static long[][] addr;
    private static long[][] addr_old;
    private static long[][] addrUpdate;
    private static BigInteger[][] addrHash;
    private static long[] optInv;
    private static long[] optInv_old;
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
    private static int nextServerPort3;
    private static String nextServerIp3;
    private static int serverCount;
    private static long[][] serverVerificationShares1D;
    private static long[][][] serverVerificationShares2D;
    private static BigInteger[][] serverVerificationShares1DBig;
    private static BigInteger[][][] serverVerificationShares2DBig;
    private static long[] permutReorgVector;
    private static String type;
    private static int optCol;
    private static int optRow;
    private static int optCol_old;
    private static int optRow_old;
    // to stores server shares as long values for 1D array
    private static String[][] serverSharesAsString_1D;
    // to stores server shares as long values for 2D array
    private static String[][][] serverSharesAsString_2D;
    private static long[][] randomSharesPhase2;
    private static long[] randomSharesPhase2Sum;


    private static long[] tryN;

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

    // multithreaded across number of files
//    private static void task31(int threadNum) {
//
//        int batchSize = (int) Math.ceil(fileCount / (double) numThreads);
//        int start = (threadNum - 1) * batchSize;
//        int end = start + batchSize;
//
//        if (end > fileCount) {
//            end = fileCount;
//        }
//
//        for (int i = 0; i < fileRequestedCount; i++) {
//            int k = -1, m = 0;
//            for (int j = 0; j < tryN.length; j++) {
//                if (j % (keywordCount + 1) == 0) {
//
//                    k++;
//
//                    m = 0;
//                }
////                System.out.println(j + " " + m + " " + k);
////                verificationForServerThreadPhase3[i][m] = (verificationForServerThreadPhase3[i][m]
////                        + (tryN[j] * 10) % 100000007)% 100000007;
//                verificationForServerThreadPhase3[i][m] =
//                        (tryN[j] * 10) % 100000007;
//
//
//                m++;
//
////                System.out.println();
//            }
//        }
//
//
//    }

//    // multithreaded across the number of files
//    private static void task32(int threadNum) {
//
//        int batchSize = (int) Math.ceil((fileCount + 1) / (double) numThreads);
//        int start = (threadNum - 1) * batchSize;
//        int end = start + batchSize;
//
//        if (end > fileCount + 1) {
//            end = fileCount + 1;
//        }
//
//        for (int m = 0; m < fileRequestedCount; m++) {
//            for (int i = start; i < end; i++) {
//                BigInteger[] temp = files[i];
//
//                for (int j = 1; j < temp.length; j++) {
//                    phase3ResultThread[m][threadNum - 1][j - 1] = Helper.mod(phase3ResultThread[m][threadNum - 1][j - 1]
//                            .add(Helper.mod(BigInteger.valueOf(fileVectorShare[m][i]).multiply(temp[j]))));
//                }
//
//            }
//        }
//    }

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
                for (int j = 0; j < temp.length; j++) {
                    phase3ResultThread[m][threadNum - 1][j] = Helper.mod(phase3ResultThread[m][threadNum - 1][j]
                            + Helper.mod(fileVectorShare[m][i] * temp[j]));
                }
            }
        }
    }


    private static long[] rotateVector(int direction, int rotationValue) {

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

            // Waiting for client to send the data
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            startServer();
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());

            long[] receivedVector = (long[]) objects;
            int ownRotate = (int) receivedVector[0];
            int otherRotate = (int) receivedVector[1];

            permutReorgVector = new long[optInvColVec.length];
            if (optCol >= 0) System.arraycopy(phase2OptInvResult, 0, permutReorgVector, 0, optCol);

            // rotate own vector
            permutReorgVector = rotateVector(0, ownRotate);

            if (serverNumber == 1) {

                // sending rotated own vector to next server data
                removeTime.add(Instant.now());
                comTime.add(Instant.now());
                sendToServer(permutReorgVector, nextServerIp1, nextServerPort1);
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
                sendToServer(permutReorgVector, nextServerIp1, nextServerPort1);
                comTime.add(Instant.now());
                perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
                comTime = new ArrayList<>();
                waitTime = new ArrayList<>();
                removeTime.add(Instant.now());
            }

            permutReorgVector = (long[]) objects;


            // rotate data received from server
            permutReorgVector = rotateVector(1, otherRotate);


            // test 1,2
            long[][] verificationForServer = new long[fileRequestedCount + 1][1 + keywordCount]; // file id and keyword access test


            verificationForServerThreadPhase3 = new long[fileRequestedCount + 1][numThreads][1 + keywordCount];
//            verificationForServerThreadPhase3 = new long[fileRequestedCount + 1][1 + keywordCount];


//            System.out.println(fileKeyword.length);
//            System.out.println(fileKeyword[0].length);
//            tryN = new long[(keywordCount + 1) * (fileCount + 1)];
//            System.out.println(tryN.length);

//            int h = 0;
//            for (long[] a : fileKeyword) {
//                for (long b : a) {
//                    tryN[h] = b;
//                    h++;
//                }
//            }


            // generate random number shares
//            Random seedGenerator = new Random(seedServerP2);
//            long[][] randomShares = new long[serverCount][keywordCount + 1 + 1]; // one for server label one for file id
//            long[] shares;
//            for (int i = 0; i < keywordCount + 1; i++) {
//                prgServer = Helper.mod(seedGenerator.nextLong(Constant.getMaxRandomBound() -
//                        Constant.getMinRandomBound()) + Constant.getMinRandomBound());
//
////                System.out.print(prgServer+" ");
//                shares = shamirSecretSharingAsLong(prgServer, serverCount);
//                for (int j = 0; j < shares.length; j++) {
//                    randomShares[j][i] = shares[j];
//                }
//            }
////            System.out.println();
//            for (int j = 0; j < serverCount; j++) {
//                randomShares[j][keywordCount + 1] = serverNumber;
//            }

//            System.out.println("before");
//            for (long a[] : randomShares) {
//                for (long b : a) {
//                    System.out.print(b + " ");
//                }
//                System.out.println();
//            }


            int count = 0;
            long prgServer;
            long[][] randomShares = new long[serverCount][];
            long[] shares;
            if ((keywordCount + 1) > optCol) {
                count = (keywordCount + 1) - optCol;
            }
            if (count > 0) {
                Random seedGenerator = new Random(seedServerP2);
                randomShares = new long[serverCount][count + 1]; // one for server label one for file id
                for (int i = 0; i < count; i++) {
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

            }


//            System.out.println("after");
//            for (int i = 0; i < serverVerificationShares1D.length; i++) {
//                if (i != serverNumber - 1) {
//                    for (int j = 0; j < keywordCount + 1 + 1; j++) {
//                        System.out.print(serverVerificationShares1D[i][j] + " ");
//                    }
//                    System.out.println();
//                }
//
//            }

//            Instant start = Instant.now();
            stageLabel = "3.1";
            createThreads(stage, stageLabel);
//            Instant end = Instant.now();
//            System.out.println("3.1  " + Duration.between(start, end).toMillis());

            long[] randomSharesSum = new long[count];

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

                    if (k < optCol) {
                        prgServer = randomSharesPhase2Sum[k];
                    } else {
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
                    }
                    verificationForServer[i][k] = Helper.mod(verificationForServer[i][k] + prgServer);
                }
//                System.out.println();
            }

            // sending to client
            verificationForServer[verificationForServer.length - 1] = new long[]{Math.floorMod(serverNumber - 2, serverCount) + 1};

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

                    if (k < optCol) {
                        received[i][k] = Helper.mod(received[i][k] - randomSharesPhase2Sum[k]);
                    } else {
                        received[i][k] = Helper.mod(received[i][k] - randomSharesSum[k]);
                    }

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
                        permutReorgVector[i + Constant.getHashBlockCount()]);

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
            result[result.length - 1] = String.valueOf(Math.floorMod(serverNumber - 2, serverCount) + 1).getBytes(StandardCharsets.UTF_8);


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
                            if (l == (Math.floorMod(serverNumber - 2, serverCount))) {
                                if (j != 0) {
                                    shares[l] = temp2[i][j - 2];
                                } else {
                                    shares[l] = fileIds[i][0];
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
                            if (l == (Math.floorMod(serverNumber - 2, serverCount))) {
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

//                System.out.println("i:" + i);
//                System.out.println(testResultLong[i][0]);
//                System.out.println(testResultBig[i]);
//                System.out.println(testResultLong[i][1]);
//                System.out.println(testResultLong[i][2]);
                if (testResultLong[i][0] != 0
                        || !(testResultBig[i].equals(BigInteger.valueOf(0)))
                        || testResultLong[i][1] != 1
                        || testResultLong[i][2] != 1) {
//                    flag = false;
//                    break;
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

        phase3Result[phase3Result.length - 1] = new long[]{(Math.floorMod(serverNumber - 2, serverCount) + 1)};
//        phase3Result[0][fileLength] = (Math.floorMod(serverNumber - 2, serverCount) + 1);


        removeTime.add(Instant.now());
        comTime.add(Instant.now());
        sendToClient(phase3Result);
        comTime.add(Instant.now());
        perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
        comTime = new ArrayList<>();
        waitTime = new ArrayList<>();
        removeTime.add(Instant.now());
    }





    // multithreaded across the number of cols in opt inverted index
    private static void task22(int threadNum) throws NoSuchAlgorithmException {
//        int batchSize = (int) Math.ceil((optCols) / (double) numThreads);
//        int start = (threadNum - 1) * batchSize;
//        int end = start + batchSize;
//
//        if (end > optCols) {
//            end = optCols;
//        }
//
//        for (int i = 0; i < optRows; i++) {
//            for (int j = start; j < end; j++) {
//                for (int k = 0; k < Constant.getHashBlockCount(); k++) {
//                    optInvServerVerification[j][k] = Helper.mod(optInvServerVerification[j][k] +
//                            Helper.mod(optInvHashValues[i * optInvColVec.length + j][k] * optInvRowVec[i]));
//                }
//
//            }
//        }


        int batchSize = (int) Math.ceil((optCol) / (double) numThreads);
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;

        if (end > optCol) {
            end = optCol;
        }

        for (int i = 0; i < optRow; i++) {
            for (int j = start; j < end; j++) {
                for (int k = 0; k < Constant.getHashBlockCount(); k++) {
                    optInvServerVerification[j][k] = Helper.mod(optInvServerVerification[j][k] +
                            Helper.mod(optInvHashValues[i * optInvColVec.length + j][k] * optInvRowVec[i]));
                }

                phase2OptInvResult[j] = Helper.mod(phase2OptInvResult[j] +
                        Helper.mod(optInv[i * optInvColVec.length + j] * optInvRowVec[i]));
            }
        }
    }

    // multithreaded across the number of cols in opt inverted index
//    private static void task22(int threadNum) throws NoSuchAlgorithmException {
//        Instant start1 = Instant.now();
//        int batchSize = (int) Math.ceil((optCols * optRows) / (double) numThreads);
//        int start = (threadNum - 1) * batchSize;
//        int end = start + batchSize;
//
//        if (end > optCols * optRows) {
//            end = optCols * optRows;
//        }
//
////        for (int k = 0; k < Constant.getHashBlockCount(); k++) {
////            for (int i = 0; i < optInvRowVec.length; i++) {
////                for (int j = start; j < end; j++) {
////                    optInvServerVerification[k][j] = Helper.mod(optInvServerVerification[k][j] +
////                            Helper.mod(optInvHashValues[k][i * optInvColVec.length + j] * optInvRowVec[i]));
////                }
////            }
////        }
//
//
//        for (int k = 0; k < Constant.getHashBlockCount(); k++) {
//            int i = -1;
//            for (int j = start; j < end; j++) {
//                if (j % optCols == 0) {
//                    i++;
//                }
//                optInvServerVerification[k][j % optCols] = Helper.mod(optInvServerVerification[k][j % optCols] +
//                        Helper.mod(optInvHashValues[k][j] * optInvRowVec[i]));
//            }
//        }
//        Instant end1 = Instant.now();
//        System.out.println(Duration.between(start1, end1).toMillis());
//    }


//    // multithreaded across the number of rows in opt inverted index
//    private static void task23(int threadNum) {
//        int batchSize = (int) Math.ceil((optCols) / (double) numThreads);
//        int start = (threadNum - 1) * batchSize;
//        int end = start + batchSize;
//
//        if (end > optCols) {
//            end = optCols;
//        }
//
//        for (int i = 0; i < optRows; i++) {
//            for (int j = start; j < end; j++) {
//                phase2OptInvResult[j] = Helper.mod(phase2OptInvResult[j] +
//                        Helper.mod(optInv[i * optInvColVec.length + j] * optInvRowVec[i]));
//            }
//        }
//
//    }


    // multithreaded across number of keywords
    private static void task24(int threadNum) {
//        int batchSize = (int) Math.ceil(keywordCount / (double) numThreads);
//        int start = (threadNum - 1) * batchSize;
//        int end = start + batchSize;
//
//        if (end > keywordCount) {
//            end = keywordCount;
//        }
//
//        BigInteger[] keywords = act[0];
//        BigInteger[] access = act[clientId];
//
//        verificationForServerThread[threadNum - 1][0] = BigInteger.valueOf(0);
//        verificationForServerThread[threadNum - 1][1] = BigInteger.valueOf(0);
//        for (int i = start; i < end; i++) {
//            verificationForServerThread[threadNum - 1][0] = Helper.mod(Helper.mod(keywords[i].
//                    multiply(BigInteger.valueOf(searchKeywordVectorShare[i]))).add(verificationForServerThread[threadNum - 1][0]));
//            verificationForServerThread[threadNum - 1][1] = Helper.mod(Helper.mod(access[i].
//                    multiply(BigInteger.valueOf(searchKeywordVectorShare[i]))).add(verificationForServerThread[threadNum - 1][1]));
//        }

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
                    phase2AddrResult[j] = Helper.mod(phase2AddrResult[j] +
                            Helper.mod(temp[j] * searchKeywordVectorShare[i]));
                } else if (j == addr[0].length) {
                    verificationForServer[0] = Helper.mod(Helper.mod(keywords[i].
                            multiply(BigInteger.valueOf(searchKeywordVectorShare[i]))).add(verificationForServer[0]));
                } else if (j == addr[0].length + 1) {
                    verificationForServer[1] = Helper.mod(Helper.mod(access[i].
                            multiply(BigInteger.valueOf(searchKeywordVectorShare[i]))).add(verificationForServer[1]));
                }
            }
        }
    }


    // multithreaded across number of keywords
    private static void task26(int threadNum) {
        int batchSize = (int) Math.ceil((keywordCount) / (double) numThreads);
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;

        if (end > keywordCount) {
            end = keywordCount;
        }

        for (int i = start; i < end; i++) {
//            System.out.println("i:" + i);
            for (int j = 0; j < 2 + (2 * Constant.getHashBlockCount()); j++) {
                addr[i][j] = Helper.mod(addr[i][j] + newAddr[i][j]);
//                if(i==0)
//                    System.out.print(addr[i][j] + " ");
            }
        }
//        System.out.println();


    }


    private static void updateAddrData() throws InterruptedException, IOException, ClassNotFoundException {

        stage = "2";

        // Waiting for client to send the data
        removeTime.add(Instant.now());
        comTime.add(Instant.now());
        startServer();
        comTime.add(Instant.now());
        perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
        comTime = new ArrayList<>();
        waitTime = new ArrayList<>();
        removeTime.add(Instant.now());

        newAddr = (long[][]) objects;

        if (newAddr[0][0] != 0) { // if free slot present
            // computing phase 1 operation on ACT list
            stageLabel = "6";
            createThreads(stage, stageLabel);
        } else { // if free slot absent

//            System.out.println("no free slot ");
            // sending to client

//            System.out.println("here");
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            sendToClient(addr);
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());

//            System.out.println("sent ");
//            System.out.println(addr.length);
//            System.out.println(addr[0].length);
            // Waiting for client to send the data
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            startServer();
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());

            long[][] addrTemp = (long[][]) objects;

            System.arraycopy(addrTemp, 0, addr, 0, addrTemp.length);
        }

    }
//
//    // multithreaded across number of keywords
//    private static void task13(int threadNum) {
//        int batchSize = (int) Math.ceil(keywordCount / (double) numThreads);
//        int start = (threadNum - 1) * batchSize;
//        int end = start + batchSize;
//
//        if (end > keywordCount) {
//            end = keywordCount;
//        }
//
//        BigInteger[] access = act[clientId];
//
//        for (int i = start; i < end; i++) {
//            act[clientId][i] = Helper.mod(newAccess[i].add(access[i]));
//            System.out.print(act[clientId][i]+" ");
//        }
//        System.out.println();
//    }


    //     multithreaded across number of keywords
    private static void task12(int threadNum) {
        int batchSize = (int) Math.ceil(keywordCount / (double) numThreads);
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;

        if (end > keywordCount) {
            end = keywordCount;
        }

        BigInteger[] keywords = act[0];
        BigInteger[] access = act[clientId];
        BigInteger temp;

        long prgServer;
        Random seedGenerator = new Random(seedServer);
        for (int i = start; i < end; i++) {
            prgServer = seedGenerator.nextLong(Constant.getMaxRandomBound() -
                    Constant.getMinRandomBound()) + Constant.getMinRandomBound();
            temp = Helper.mod((Helper.mod(Helper.mod(keywords[i].subtract(searchKeywordShare)).add(access[i])))
                    .multiply(BigInteger.valueOf(prgServer)));
            phase1Result[threadNum - 1].append(temp).append(",");
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

    /**
     * To read values from objects as string
     *
     * @param type the type of object as 1D or 2D
     */
    private static void readObjectsAsBigInteger(String type) {
        if (type.equals("1D")) {
            for (int i = 0; i < objectsList.size(); i++) {
                int temp = ((BigInteger[]) objectsList.get(i))[((BigInteger[]) objectsList.get(i)).length - 1].intValue();
                serverVerificationShares1DBig[temp - 1] = ((BigInteger[]) objectsList.get(i));
            }
        } else if (type.equals("2D")) {
            for (int i = 0; i < objectsList.size(); i++) {
                int temp = ((BigInteger[][]) objectsList.get(i))[((BigInteger[][]) objectsList.get(i)).length - 1][0].intValue();
                serverVerificationShares2DBig[temp - 1] = ((BigInteger[][]) objectsList.get(i));
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


    private static void sendToClient(Object data) {

        try {
            waitTime.add(Instant.now());
            socketClient = new Socket(clientIP, clientPort);
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
     * to start server to listen to the client
     */
    public static void startServer() {
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
                if (stageLabel.equals("1"))
                    task01(threadNum);
                else if (stageLabel.equals("2")) {
                    task02(threadNum);
                }
            } else if (stage.equals("1")) {
                if (stageLabel.equals("1"))
                    task11(threadNum);
                else if (stageLabel.equals("2"))
                    task12(threadNum);
                else if (stageLabel.equals("3"))
                    task13(threadNum);
                else if (stageLabel.equals("4"))
                    task14(threadNum);
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
                } else if (stageLabel.equals("6")) {
                    task26(threadNum);
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


    private static void calOptInvHashValues() throws NoSuchAlgorithmException {
        optInvHashValues = new long[optInv.length][Constant.getHashBlockCount()];
        for (int i = 0; i < optInv.length; i++) {
            String digest = hashDigest(String.valueOf(i));
            int m = 0;
            int h = 0;
            while (m < digest.length()) {
                int end = m + Constant.getHashBlockSize();
                if (end > digest.length())
                    end = digest.length();
                optInvHashValues[i][h] = Long.parseLong(digest.substring(m, end));
                h++;
                m = m + Constant.getHashBlockSize();
            }
        }
    }

//    private static void calOptInvHashValues() throws NoSuchAlgorithmException {
//        optInvHashValues = new long[Constant.getHashBlockCount()][optInv.length];
//        for (int i = 0; i < optInv.length; i++) {
//            String digest = hashDigest(String.valueOf(i));
//            int m = 0;
//            int h = 0;
//            while (m < digest.length()) {
//                int end = m + Constant.getHashBlockSize();
//                if (end > digest.length())
//                    end = digest.length();
//                optInvHashValues[h][i] = Long.parseLong(digest.substring(m, end));
//                h++;
//                m = m + Constant.getHashBlockSize();
//            }
//        }
//    }

    /**
     * To perform cleanup tasks in course of program execution
     */
    public static void cleanUp() {
        // re-initializing the list to hold values received from server
        objectsList = Collections.synchronizedList(new ArrayList<>());
    }


    // multithreaded across the number of rows in opt inverted index
    private static void task23(int threadNum) {
        int batchSize = (int) Math.ceil((optCol) / (double) numThreads);
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;

        if (end > optCol) {
            end = optCol;
        }

        for (int i = 0; i < optRow; i++) {
            for (int j = start; j < end; j++) {
//                System.out.println("i:"+i+" j:"+j);
//                System.out.println("optInv[i * optCol + j]:"+optInv[i * optCol + j]);
                phase2OptInvResult[j] = (phase2OptInvResult[j] +
                        (optInv[i * optCol + j] * optInvRowVec[i])%modValue)%modValue;
            }
        }

    }

    public static void getOptValues() {
//         performing operation to get the file ids
//         Waiting for client to send the position and count of data to be retrieved from opt tabel
        removeTime.add(Instant.now());
        comTime.add(Instant.now());
        startServer();
        comTime.add(Instant.now());
        perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
        comTime = new ArrayList<>();
        waitTime = new ArrayList<>();
        removeTime.add(Instant.now());
        optIndexShare = (long[][]) objects;
        optInvRowVec = optIndexShare[0];
        phase2OptInvResult = new long[optCol + 1];
        stageLabel = "3";
        createThreads(stage, stageLabel);
        phase2OptInvResult[phase2OptInvResult.length - 1] = serverNumber;
        removeTime.add(Instant.now());
        comTime.add(Instant.now());
        sendToClient(phase2OptInvResult);
        comTime.add(Instant.now());
        perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
        comTime = new ArrayList<>();
        waitTime = new ArrayList<>();
        removeTime.add(Instant.now());
    }

    // multithreaded across number of keywords
    private static void task25(int threadNum) {
        int batchSize = (int) Math.ceil((optInv.length) / (double) numThreads);
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;

        if (end > (optInv.length)) {
            end = (optInv.length);
        }

        for (int j = start; j < end; j++) {
            optInv[j] = Helper.mod(optInv[j] + newOptInv[j]);
//            if(j%optCol==0 && j!=0)
//                System.out.println();;
//            System.out.print(optInv[j] + " ");

        }

    }

    public static void updateOptValues() {
        removeTime.add(Instant.now());
        comTime.add(Instant.now());
        startServer();
        comTime.add(Instant.now());
        perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
        comTime = new ArrayList<>();
        waitTime = new ArrayList<>();
        removeTime.add(Instant.now());

        newOptInv = (long[]) objects;

//        System.out.println("O:" + newOptInv[0]);

        if (newOptInv[0] != 0) {// free slot present
            // computing phase 1 operation on ACT list

//            System.out.println("free slot");
            stageLabel = "5";
            createThreads(stage, stageLabel);

//            for (int i = 130; i < 130 + optCol; i++) {
//                System.out.print(optInv[i] + " ");
//            }
//            System.out.println();
        } else {// free slot absent

//            System.out.println("no free slot");


            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            startServer();
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());

            newOptInv = (long[]) objects;
            int row = (int) newOptInv[newOptInv.length - 1];
//            System.out.println("row:" + row);
//            System.out.println("newOptInv:" + newOptInv.length);

            long[] newOpt = new long[optInv.length + optCol];

            int l = 0;
            for (int i = 0; i < newOpt.length; i++) {
                if (i / optCol == row || i / optCol == row + 1) {
                    if (i / optCol == row) {
                        newOpt[i] = newOptInv[i] + optInv[l];
                        l++;
                    } else {
                        newOpt[i] = newOptInv[i];
                    }

                } else {
                    newOpt[i] = optInv[l];
                    l++;
                }
            }
            optInv = newOpt;
//            System.out.println("new");
//            for (int i = 0; i < newOpt.length; i++) {
////                if (i / optCol == row || i / optCol == row + 1) {
////                    System.out.print(newOpt[i] + " ");
////                }
//                if(i%optCol==0 && i!=0)
//                    System.out.println();;
//                System.out.print(newOpt[i] + " ");
//            }
//            System.out.println();

            optRow++;

        }

    }

    /**
     * to perform operation  between ACT list and search keyword
     * @param threadNum
     */
    public static void task14(int threadNum) {
        int batchSize = (int) Math.ceil(keywordCount / (double) numThreads);
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;
        if (end > keywordCount) {
            end = keywordCount;
        }
        BigInteger[] keywords = act[0];
        BigInteger temp;
        for (int i = start; i < end; i++) {
            temp = (keywords[i].subtract(searchKeywordShare)).mod(modValueBig);
            phase1Result[threadNum - 1].append(temp).append(",");
        }
    }

    private static void getKeywordIndex() throws InterruptedException, UnsupportedEncodingException {
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
//        System.out.println(searchKeywordShare);
        // initializing
        phase1Result = new StringBuilder[numThreads];
        for (int i = 0; i < numThreads; i++) {
            phase1Result[i] = new StringBuilder("");
        }
        // computing phase 1 operation on ACT list
        stageLabel = "4";
        createThreads(stage, stageLabel);
        // adding thread data
        for (int i = 1; i < numThreads; i++) {
            phase1Result[0].append(phase1Result[i]);
        }
//        System.out.println(phase1Result[0]);
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

    // multithreaded across the column i.e. the content of addr table
    private static void task21(int threadNum) {
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
                        (temp[j] * searchKeywordVectorShare[i]) % modValue) %modValue;
            }
        }
    }

    private static boolean getAddrData() throws InterruptedException, IOException, ClassNotFoundException {
        stage = "2";

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
        searchKeywordVectorShare = (long[]) objects;

        if (searchKeywordVectorShare[0] != 0) {
            phase2AddrResult = new long[addr[0].length + 1]; // 1 to store the label for the server
            stageLabel = "1";
            createThreads(stage, stageLabel);
            phase2AddrResult[phase2AddrResult.length - 1] = (Math.floorMod(serverNumber - 2, serverCount) + 1);
            // sending to client
            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            sendToClient(phase2AddrResult);
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());
            return true;
        }
        return false;
    }

    /**
     * to add new files with existing keywords
     * @throws IOException
     * @throws NoSuchAlgorithmException
     */
    public static void addFilesOpt() throws IOException, InterruptedException, ClassNotFoundException {
        getKeywordIndex(); // get keyword index
        boolean flag = getAddrData();
        if (flag) {
            getOptValues();
            updateOptValues();
            updateAddrData();
        }
    }

    private static void task01(int threadNum) {
        Instant stary_=Instant.now();
        int batchSize = (int) Math.ceil((keywordCount) / (double) numThreads);
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;

        if (end > keywordCount) {
            end = keywordCount;
        }

        for (int k = 0; k < act.length; k++) {
            String [] str=new String(actUpdate[k], StandardCharsets.UTF_8).split(",");
            for (int i = start; i < end; i++) {
//                System.out.println(str[i]);
                act[k][i] = (act[k][i].add(new BigInteger(str[i]))).mod(modValueBig);
//                    System.out.print(act[k][i]+" ");
            }
//            System.out.println();
        }
        Instant end_=Instant.now();
//        System.out.println("Time:"+Duration.between(stary_,end_).toMillis());


    }

    private static void task02(int threadNum) {
        int batchSize = (int) Math.ceil((keywordCount) / (double) numThreads);
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;

        if (end > keywordCount) {
            end = keywordCount;
        }

        for (int k = start; k < end; k++) {
            for (int i = 0; i < 2 + 2 * Constant.getHashBlockCount(); i++) {
                addr[k][i] = Helper.mod(addr[k][i] + addrUpdate[k][i]);
            }
        }
    }


    public static void deleteKeywordOpt() throws IOException, InterruptedException, ClassNotFoundException {

        if(serverNumber<=3){
            getKeywordIndex();
        }


        removeTime.add(Instant.now());
        comTime.add(Instant.now());
        startServer();
        comTime.add(Instant.now());
        perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
        comTime = new ArrayList<>();
        waitTime = new ArrayList<>();
        removeTime.add(Instant.now());

        actUpdate = (byte[][]) objects;
//        System.out.println(actUpdate.length);
//        System.out.println(actUpdate[0].length);

        if (!new String(actUpdate[0]).split(",")[0].equals("0")) {

//            for (int i = 2; i < act.length; i++) {
//                System.out.print(act[i][0] + " ");
//            }
//            System.out.println();

            stage = "0";
            stageLabel = "1";
            createThreads(stage, stageLabel);
//            System.out.println("cn ");

//            for (int i = 2; i < act.length; i++) {
//                System.out.print(act[i][0] + " ");
//            }
//            System.out.println();

//            {
//
//
//                // update the addr list
//                if (serverNumber <= 3) {
//                    boolean flag = getAddrData();
//                    if (flag) {
//                        removeTime.add(Instant.now());
//                        comTime.add(Instant.now());
//                        startServer();
//                        comTime.add(Instant.now());
//                        perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
//                        comTime = new ArrayList<>();
//                        waitTime = new ArrayList<>();
//                        removeTime.add(Instant.now());
//
//                        addrUpdate = (long[][]) objects;
//
//                        stage = "0";
//                        stageLabel = "2";
//                        createThreads(stage, stageLabel);
//
////                for (int i = 0; i < 2 + 2 * Constant.getHashBlockCount(); i++) {
////                    System.out.print(addr[0][i] + " ");
////                }
////                System.out.println();
//                    }
//                }
//            }
        }
    }

    public static void deleteFileOpt() throws IOException, NoSuchAlgorithmException, InterruptedException, ClassNotFoundException {
        getKeywordIndex();

        boolean flag = getAddrData();
        if (flag) {
            getOptValues();

            removeTime.add(Instant.now());
            comTime.add(Instant.now());
            startServer();
            comTime.add(Instant.now());
            perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
            comTime = new ArrayList<>();
            waitTime = new ArrayList<>();
            removeTime.add(Instant.now());


            stage="2";
            newOptInv = (long[]) objects;
            stageLabel = "5";
            createThreads(stage, stageLabel);
//
//            System.out.println("he");
//            for (int i=0;i<optInv.length;i++){
//                System.out.print(optInv[i]+" ");
//            }
//            System.out.println();
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
            addr = Helper.readFileAsLong1(file, (Math.floorMod(serverNumber - 2, serverCount) + 1));
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
     * clean variables after an operation
     */
    public static void cleanUpOpData() {
        perServerTime = new ArrayList<>();
        removeTime = new ArrayList<>();
        comTime = new ArrayList<>();
        waitTime = new ArrayList<>();
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
        for (int i = start; i < end; i++) {
            temp = ((keywords[i].subtract(searchKeywordShare)).mod(modValueBig).add(access[i])).mod(modValueBig);
            phase1Result[threadNum - 1].append(temp).append(",");
        }
    }

    /**
     * to update the access for the client
     * multithreaded across number of keywords
     * @param threadNum
     */
    public static void task13(int threadNum) {
        int batchSize = (int) Math.ceil(keywordCount / (double) numThreads);
        int start = (threadNum - 1) * batchSize;
        int end = start + batchSize;
        if (end > keywordCount) {
            end = keywordCount;
        }
        BigInteger[] access = act[clientId];
        for (int i = start; i < end; i++) {
            act[clientId][i] = (new BigInteger(newAccess[i]).add(access[i])).mod(modValueBig);
//            System.out.print(act[clientId][i]+" ");
        }
//        System.out.println();
    }

    /**
     * @throws InterruptedException
     * @throws UnsupportedEncodingException
     */
    public static void getAccessKeyword() throws InterruptedException, UnsupportedEncodingException {
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
        // reading the data sent by client
        searchKeywordShare = ((BigInteger[]) objects)[0];
        clientId = ((BigInteger[]) objects)[1].intValue() + 1; // since 1st row are keywords and 2nd row are position of keywords
        // initializing
        phase1Result = new StringBuilder[numThreads];
        for (int i = 0; i < numThreads; i++) {
            phase1Result[i] = new StringBuilder("");
        }
        // computing phase 1 operation on ACT list
        stageLabel = "1";
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

    /**
     * to grant or revoke access of a keyword for a given client
     */
    public static void revokeGrantAccess() throws UnsupportedEncodingException, InterruptedException {
        if (serverNumber <= 3) {
            getAccessKeyword();// get access and index of keyword
        }
        // waiting for server to send update access result
        removeTime.add(Instant.now());
        comTime.add(Instant.now());
        startServer();
        comTime.add(Instant.now());
        perServerTime.add(Helper.calculateSendToServerTime(comTime, waitTime, 1));
        comTime = new ArrayList<>();
        waitTime = new ArrayList<>();
        removeTime.add(Instant.now());
        byte[] temp1 = (byte[]) objects;
        String objectRead = new String(temp1, StandardCharsets.UTF_8);
        clientId = Integer.parseInt(objectRead.substring(objectRead.lastIndexOf(",") + 1)) + 1;
        objectRead = objectRead.substring(0, objectRead.lastIndexOf(","));
        newAccess = objectRead.split(",");
        if (!newAccess[0].equals("0")) {
            // updating the access values
            stage = "1";
            stageLabel = "3";
            createThreads(stage, stageLabel);
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
        // reading the properties file for server
        Properties specificProperties = Helper.readPropertiesFile("config/Server" + serverNumber
                + ".properties");
        // reading the commonProperties file for client
        Properties commonProperties = Helper.readPropertiesFile("config/Common.properties");

        serverVerification = Boolean.parseBoolean(commonProperties.getProperty("serverVerification"));
        clientVerification = Boolean.parseBoolean(commonProperties.getProperty("clientVerification"));

        clientPort = Integer.parseInt(commonProperties.getProperty("clientPort"));
        clientIP = commonProperties.getProperty("clientIP");
        numThreads = Integer.parseInt(commonProperties.getProperty("numThreads"));
//        fileLength = Integer.parseInt(commonProperties.getProperty("maxFileLength"));
        optRow = Integer.parseInt(commonProperties.getProperty("optRow"));
        optCol = Integer.parseInt(commonProperties.getProperty("optCol"));
//        seedServer = Long.parseLong(specificProperties.getProperty("seedServer"));
//        seedServerP2 = Long.parseLong(specificProperties.getProperty("seedServerP2"));
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
        System.out.println("numThreads:" + numThreads);
    }

    public static void main(String args[]) throws IOException, InterruptedException, NoSuchAlgorithmException, ClassNotFoundException {
        // to calculate the time
        Instant start, end;
        double totalTime;

        initialization(args);
        int count = 0;
        while (true) {
            // Waiting for DBO
            startServer();
            operation = (int) objects; // the operation

            switch (operation) {
                case 1 -> {
                    cleanUpOpData();
                    start = Instant.now();
                    addFilesOpt();
                    end = Instant.now();
                    totalTime = Duration.between(start, end).toMillis();
                    Helper.printTimesNew("Add new file", null, null, removeTime, perServerTime, totalTime, count);
                }
                case 2 -> {
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
            if (count == Helper.getRunCount()) {
                count = 0;
                System.out.println("Time taken on an average for over " + (Helper.getRunCount() - Helper.getBuffer()) + " round for each phase is below");
                Helper.timeTaken(1);
            }
        }
    }
}
