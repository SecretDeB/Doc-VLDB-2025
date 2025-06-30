package src.outsource;

import java.io.*;
import java.math.BigInteger;
import java.nio.file.Files;
import java.nio.file.Path;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.time.Duration;
import java.time.Instant;
import java.util.*;

import constants.Constant;
import org.tartarus.snowball.SnowballStemmer;
import utility.Helper;

public class DataOutsource {

    // the number of servers
    private static int serverCount;
    // the number of keywords
    private static int keywordCount;
    // the number of files
    private static int fileCount;
    // the number of clients
    private static int clientCount;
    // the folder with search keywords
    private static String binFolder;
    // to store the number of keywords in the file
    private static LinkedHashMap<Integer, Integer> fileKeywordCount = new LinkedHashMap<>();
    // stores hash blocks
    private static long[] hashBlocks;
    // folder to store cleartext and share of data structures ACt, Inverted Index and Files
    private static String shareDirectory;
    // the directory storing all the documents partioned by clients
    private static String documentDirectory;
    // the directory for code and data
    private static String mainDir;
    // threshold for maximum occurrence of a keyword across all files
    private static int keywordMaxFreq;
    // the map of keywords and the files in which they occur
    private static LinkedHashMap<String, LinkedHashMap<String, String>> keywordFileMap = new LinkedHashMap<>();
    // the map of keywords and the files in which they occur for optimized code
    private static LinkedHashMap<String, List<String>> keywordClientAccess = new LinkedHashMap<>();
    // to store the numeric version of text
    private static StringBuilder numericText;
    // to store the updates text
    private static StringBuilder newText;
    // to store maximum size of file
    private static int maxFileSize = Integer.MIN_VALUE;
    // cleartext of file DS
    private static StringBuilder fileCleartext;
    // cleartext of file keywords
    private static StringBuilder fileKeywordCleartext;
    // name of cleartext file
    private static String fileNameCleartext;
    // name of share file
    private static String fileNameShare;
    // the seed for DBO
    private static int seedDBO;
    // the max number of files a keyword can be in
    private static int checkpoint1;
    // the min number of files a keyword can be in
    private static int checkpoint2;
    // bin containing all search keywords
    private static int binNumber;
    // stores hash digest
    private static List<String> hashConstant;
    // to store the number of files a keyword occurs
    private static final LinkedHashMap<String, Map<String, String>> keywordFileStats = new LinkedHashMap<>();
    // stores position of each keyword in act table
    private static LinkedHashMap<String, String> keywordPostion = new LinkedHashMap<>();
    // starting index of a keyword
    private static int indexPos = 0;
    // to calculate the size of opt inverted index
    private static int sizeIIOPT = 0;
    // number of columns in opt inverted index
    private static int colSize;
    // number of rows in opt inverted index
    private static int rowSize;
    // to store the filtered keywords
    private static LinkedHashMap<String, String> keywordList = new LinkedHashMap<>();
    // the mod value
    private static final long modValue = Constant.getModParameter();
    // the mod value for BigInteger
    private static final BigInteger modValueBig = Constant.getModBigParameter();


    /**
     * To write the string into file
     *
     * @param fileName the name of file to write into
     * @param content  the content to write into files
     */
    public static void writeToFile(String fileName, String content) {
        try {
            FileWriter myWriter = new FileWriter(fileName + ".txt", true);
            myWriter.write(content);
            myWriter.close();
        } catch (IOException e) {
            System.out.println("An error occurred while writing to the file.");
            e.printStackTrace();
        }
    }

    /**
     * Create share for secret value as string
     *
     * @param secret      the secret value as tring
     * @param serverCount the number of servers for which shares are to be created
     * @return the share of the secret value as string is returned for given number of server as servercount
     */
    private static String[] shamirSecretShares(String secret, int serverCount) {

        BigInteger secretBig = new BigInteger(secret);
        Random rand = new Random();
        String[] share = new String[serverCount];

        BigInteger slope = BigInteger.valueOf(rand.nextLong(Constant.getMaxRandomBound() - Constant.getMinRandomBound()) +
                Constant.getMinRandomBound());

        // check if the secret size is enough for long or BigInteger calculation
        for (int i = 0; i < serverCount; i++) {
            share[i] = String.valueOf(((BigInteger.valueOf(i + 1).multiply(slope)).add(secretBig)).mod(modValueBig));
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
    private static String[] shamirSecretShares(long secret, int serverCount) {
        Random rand = new Random();
        String[] share = new String[serverCount];

        // choosing the slope value for line
        long slope = rand.nextInt(Constant.getMaxRandomBound() - Constant.getMinRandomBound()) +
                Constant.getMinRandomBound();

        for (int i = 0; i < serverCount; i++) {
            share[i] = String.valueOf((((i + 1) * slope) + secret) % modValue);
        }
        return share;
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
            numericText.append((int) data.charAt(i) - 86);
        }
        return numericText.toString();

    }

    /**
     * To convert string to numeric representation
     *
     * @param text The input text
     */
    public static void convertToNumeric(String text) {
        text = text.toLowerCase();
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
        BigInteger result = (new BigInteger(digest)).mod(modValueBig);
        return result.toString();
    }

    /**
     * remove existing shares and cleartext file
     */
    public static void removeFiles() {
        // to remove existing cleartext and share files from /data folder
        remove(shareDirectory + "cleartext/" + "act" + 0 + ".txt");
        remove(shareDirectory + "cleartext/" + "act00" + ".txt");
        remove(shareDirectory + "cleartext/" + "invertedIndex" + 0 + ".txt");
        remove(shareDirectory + "cleartext/" + "invertedIndexOpt" + 0 + ".txt");
        remove(shareDirectory + "cleartext/" + "addr" + 0 + ".txt");
        remove(shareDirectory + "cleartext/" + "addr00" + ".txt");
        remove(shareDirectory + "cleartext/" + "file" + 0 + ".txt");
        remove(shareDirectory + "cleartext/" + "fileKeyword" + 0 + ".txt");
        remove(shareDirectory + "cleartext/" + "keywords.txt");

        for (int i = 1; i <= serverCount; i++) {
            remove(shareDirectory + "share/" + "act" + i + ".txt");
            remove(shareDirectory + "share/" + "invertedIndex" + i + ".txt");
            remove(shareDirectory + "share/" + "invertedIndexOpt" + i + ".txt");
            remove(shareDirectory + "share/" + "addr" + i + ".txt");
            remove(shareDirectory + "share/" + "file" + i + ".txt");
            remove(shareDirectory + "share/" + "fileKeyword" + i + ".txt");
        }
        remove(shareDirectory + "share/" + "act4" + ".txt");

    }

    /**
     * To generate a random BigInteger value
     *
     * @param seed The seed of generating the random value
     * @return The random BigInteger value
     */
    public static BigInteger generateBigIntegerRandomNum(long seed) {
        BigInteger bigInteger = Constant.getMaxLimitNoAccess().subtract(Constant.getMinLimitNoAccess());
        Random randNum = new Random(seed);
        int len = Constant.getMaxLimitNoAccess().bitLength();
        BigInteger res;
        BigInteger temp1 = BigInteger.valueOf(0);
        res = new BigInteger(len, randNum);
        if (res.compareTo(Constant.getMinLimitNoAccess()) < 0)
            temp1 = res.add(Constant.getMinLimitNoAccess());
        if (res.compareTo(bigInteger) >= 0)
            temp1 = res.mod(bigInteger).add(Constant.getMinLimitNoAccess());

        return temp1;
    }

    /**
     * To convert a hash digest value into hash blocks and add to previous generated hash blocks
     *
     * @param data the data whose hash digest blocks is to be created
     * @return an array of hash blocks
     * @throws NoSuchAlgorithmException
     */
    public static void createAddHashBlocks(String data) throws NoSuchAlgorithmException {
        String hash = hashDigest(data);
        int pointer = 0, end;
        for (int j = 0; j < hash.length(); j = j + Constant.getHashBlockSize()) {
            end = j + Constant.getHashBlockSize();
            if (end > hash.length())
                end = hash.length();
            hashBlocks[pointer] = (hashBlocks[pointer] + Long.parseLong(hash.substring(j, end))) % modValue;
            pointer++;
        }
    }

    /**
     * To convert a value into  blocks
     *
     * @param data the data whose blocks is to be created
     * @return an array of blocks
     * @throws NoSuchAlgorithmException
     */
    public static List<String> createStringBlocks(String data) {
        String substring;
        List<String> result = new ArrayList<>();
        int end;
        for (int i = 0; i < data.length(); i += Constant.getHashBlockSize()) {
            end = i + Constant.getHashBlockSize();
            if (end >= data.length())
                end = data.length();
            substring = data.substring(i, end);
            result.add(substring);
        }
        return result;
    }

    /**
     * code  to reinitialize variables
     */
    public static void cleanUp() {
        keywordPostion = null;
        hashBlocks = null;
        keywordList = null;
    }

    /**
     * Read keywords from the choose bin file
     *
     * @param fileId the id of the bin to read from
     */
    public static void readBinKeywords(int fileId) {
        BufferedReader br = null;
        try {
            String filePath = shareDirectory + "cleartext/" + binFolder + "/" + "bin" + fileId + ".txt";
            File file = new File(filePath);
            br = new BufferedReader(new FileReader(file));
            String line = null;
            while ((line = br.readLine()) != null) {
                String[] parts = line.split(":");
                String name = parts[0].trim();
                keywordList.put(name, "");
            }
        } catch (Exception e) {
            e.printStackTrace();
        } finally {
            if (br != null) {
                try {
                    br.close();
                } catch (Exception e) {
                }
            }
        }
    }

    /**
     * To create shares and write cleartext and shares to file
     *
     * @param vector            the data whose shares to be created
     * @param fileNameCleartext the name of cleartext file
     * @param fileCleartext     the cleartext data
     * @param fileNameShare     the name of share file
     */
    public static void createShares(List<String> vector, String fileNameCleartext, StringBuilder fileCleartext, String fileNameShare) {

        StringBuilder[] dsShares = new StringBuilder[serverCount];
        for (int i = 0; i < serverCount; i++) {
            dsShares[i] = new StringBuilder("");
        }
        String[] shares;
        String filename;
        for (String element : vector) {
            shares = shamirSecretShares(Long.parseLong(element), serverCount);
            for (int i = 0; i < serverCount; i++) {
                dsShares[i].append(shares[i]).append(",");
            }
        }
        for (int i = 0; i < serverCount; i++) {
            dsShares[i].append("\n");
        }

        // writing cleartext to the file
        writeToFile(fileNameCleartext, String.valueOf(fileCleartext));
        // writing share to the file
        for (int i = 0; i < serverCount; i++) {
            filename = fileNameShare + (i + 1);
            writeToFile(filename, String.valueOf(dsShares[i]));
        }
    }

    /**
     * To create shares and write cleartext and shares to file
     *
     * @param vector            the data whose shares to be created
     * @param fileNameCleartext the name of cleartext file
     * @param fileCleartext     the cleartext data
     * @param fileNameShare     the name of share file
     */
    public static void createShares(long[] vector, String fileNameCleartext, StringBuilder fileCleartext, String fileNameShare) {

        StringBuilder[] dsShares = new StringBuilder[serverCount];
        for (int i = 0; i < serverCount; i++) {
            dsShares[i] = new StringBuilder("");
        }

        String[] shares;
        String filename;
        for (long element : vector) {
            shares = shamirSecretShares(element, serverCount);
            for (int i = 0; i < serverCount; i++) {
                dsShares[i].append(shares[i]).append(",");
            }
        }
        for (int i = 0; i < serverCount; i++) {
            dsShares[i].append("\n");
        }

        writeToFile(fileNameCleartext, String.valueOf(fileCleartext));

        // writing share to the file
        for (int i = 0; i < serverCount; i++) {
            filename = fileNameShare + (i + 1);
            writeToFile(filename, String.valueOf(dsShares[i]));
        }

    }

    /**
     * To add sample file to file data structure
     */
    public static void addSampleFile() throws NoSuchAlgorithmException {

        fileCleartext = new StringBuilder();
        List<String> fileVector = new ArrayList<>();
        convertToNumeric(Constant.getSampleFile());
        fileVector.addAll(createStringBlocks(hashDigest(String.valueOf(newText))));
        if (fileVector.size() < Constant.getHashBlockCount()) {
            while (fileVector.size() != Constant.getHashBlockCount())
                fileVector.add("0");
        }
        fileVector.addAll(createStringBlocks(String.valueOf(numericText)));
//        fileCleartext.append(fileVector).append("\n");
        fileCleartext.append(fileVector);
//        System.out.println(fileCleartext);
        fileCleartext.replace(0, 1, "");
        fileCleartext.replace(fileCleartext.length() - 1, fileCleartext.length(), "");
        fileCleartext.append("\n");

        // creating shares and writing to file
        fileNameCleartext = shareDirectory + "cleartext/file" + (0);
        fileNameShare = shareDirectory + "share/file";
        createShares(fileVector, fileNameCleartext, fileCleartext, fileNameShare);

        // file keyword shares
        fileKeywordCleartext = new StringBuilder();
        long[] fileKeys = new long[checkpoint2 + Constant.getHashBlockCount() + 1];
        for (int i = 0; i < Constant.getHashBlockCount(); i++) {
            fileKeys[i + 1] = Long.parseLong(hashConstant.get(i));
        }
//        fileKeywordCleartext.append("0").append(":").append(Arrays.toString(fileKeys)).append("\n");

        String str = Arrays.toString(fileKeys).replace("[", "");
        str = str.replace("]", "");
        fileKeywordCleartext.append(str);
        fileKeywordCleartext.append("\n");

        // creating shares and writing to file
        fileNameCleartext = shareDirectory + "cleartext/fileKeyword" + 0;
        fileNameShare = shareDirectory + "share/fileKeyword";
        createShares(fileKeys, fileNameCleartext, fileKeywordCleartext, fileNameShare);
    }

    /**
     * To delete the file, given the file path
     *
     * @param path the path of file to deleted
     */
    public static void remove(String path) {
        File file = new File(path);

        // check if the files exits
        if (file.exists()) {
            file.delete();
        }

    }

    public static void display() {
        System.out.println("Original");
        System.out.println("========================================================");
        System.out.println("Total no. of keywords in " + fileCount + " files is " + keywordCount);
        System.out.println("INPUT");
        System.out.println("========================================================");
        System.out.println("Total no. of files is " + fileCount);
        System.out.println("Total no. of keywords  is " + keywordCount);
        System.out.println("Output");
        System.out.println("========================================================");
        System.out.println("Total no. of files is " + (fileCount));
        System.out.println("Total no. of keywords  is " + keywordCount);
        System.out.println("Size of act is " + clientCount + " * " + keywordCount);
        System.out.println("Size of inverted index non-optimized is " + keywordCount + " * " + (keywordMaxFreq));
        System.out.println("Size of inverted index optimized is " + sizeIIOPT);
        System.out.println("Column Size: " + colSize);
        System.out.println("Row Size:  " + rowSize);
        System.out.println("Size of inverted index optimized matrix is " + rowSize + " * " + colSize);
        System.out.println("Size of files DS is " + fileCount + " * " + maxFileSize);
    }

    // to delete document directory
    public static void deleteDirectory(File directoryToBeDeleted) {
        File[] allContents = directoryToBeDeleted.listFiles();
        if (allContents != null) {
            for (File file : allContents) {
                deleteDirectory(file);
            }
        }
        directoryToBeDeleted.delete();
    }

    /**
     * Parses a single file to collect all the keywords for that file
     *
     * @param file   the path of the file
     * @param fileId the id of the file
     * @throws ClassNotFoundException
     * @throws InstantiationException
     * @throws IllegalAccessException
     */
    public static void fileParse(File file, String fileId) throws ClassNotFoundException, InstantiationException,
            IllegalAccessException {

        Map<String, String> tempMap;

        // reading the content of the file
        String content;
        try {
            content = Files.readString(file.toPath());
        } catch (Exception e) {
            return;
        }

        // initializing the stemmer for english keywords
        Class stemClass = Class.forName("org.tartarus.snowball.ext.englishStemmer");
        SnowballStemmer stemmer = (SnowballStemmer) stemClass.newInstance();

        // extract token for each line
        String[] tokens;
        tokens = content.split("[.;:!?/\\\\,#@$&)(\" =]");

        // iterating over the tokens
        for (String token : tokens) {
            token = token.toLowerCase();
            token = token.trim();

            // removing words of undesired length and not having alpha characters
            if ((token.length() >= Constant.getMinKeywordLength() && token.length() <= Constant.getMaxKeywordLength())
                    && token.matches("[a-z]+")) {

                // perform stemming of the token
                stemmer.setCurrent(token);
                stemmer.stem();
                token = stemmer.getCurrent();

                // checking if keywordFileStats map contains token
                if (!keywordFileStats.containsKey(token)) {
                    keywordFileStats.put(token, new LinkedHashMap<>());
                }

                // appending new file id to the key=token
                if (!keywordFileStats.get(token).containsKey(String.valueOf(fileId))) {
                    keywordFileStats.get(token).put(String.valueOf(fileId), "");
                }
            }
        }

//        // display the keywordFileStats map
//        Helper.display(keywordFileStats);
    }

    /**
     * To store key value information as key = keyword and value = the id of files containing the keyword
     * Uses clientCount as input
     *
     * @throws ClassNotFoundException
     * @throws InstantiationException
     * @throws IllegalAccessException
     */
    public static void keywordFileStats() throws ClassNotFoundException, InstantiationException, IllegalAccessException {

        int status = 0, fileId = 1, clientId = 1;

        while (clientId <= clientCount) {
            File file = new File(documentDirectory + clientId + "/" + fileId);

            while (file.exists()) {

                fileParse(file, String.valueOf(fileId));

                fileId++;
                file = new File(documentDirectory + clientId + "/" + fileId);

                // logging the status of completion
                status++;
                if (status % 10000 == 0)
                    System.out.println("Completed reading " + status + " files");
            }
            clientId++;
        }
        System.out.println("Number of files parsed by " + clientCount + " clients is " + (fileId - 1));

        // removing keywords occurring in more than keywordMaxFreq files
        LinkedHashMap<String, Integer> keywordFileCount = new LinkedHashMap<>();
        for (String keyword : keywordFileStats.keySet()) {
            if (keywordFileStats.get(keyword).size() < keywordMaxFreq) {
                keywordFileCount.put(keyword, keywordFileStats.get(keyword).size());
//                if(keyword.length()>6){
//                    keywordFileCount.remove(keyword);
//                }
            }
//             for 3. stats
//            keywordFileCount.put(keyword, keywordFileStats.get(keyword).size());
        }

        // 1. length vs name of keywords with that length
//        LinkedHashMap<Integer, List<String>> keywordLengthStats = new LinkedHashMap<>();
//        int keywordLen;
//        for (String keyword : keywordFileStats.keySet()) {
//            keywordLen = keyword.length();
//            if (!keywordLengthStats.containsKey(keywordLen)) {
//                keywordLengthStats.put(keywordLen, new ArrayList<>());
//            }
//            // appending keyword to the key=keywordLen
//            if (!keywordLengthStats.get(keywordLen).contains(keyword)) {
//                keywordLengthStats.get(keywordLen).add(keyword);
//            }
//        }
//        // sort keywordLengthStats in asc order
//        ArrayList<Integer> sortedKeys
//                = new ArrayList<>(keywordLengthStats.keySet());
//        Collections.sort(sortedKeys, Collections.reverseOrder());
//
//        // write keywordLengthStats to file
//        StringBuilder stringBuilder = new StringBuilder("");
//        for (Integer keywordLength : sortedKeys) {
////            stringBuilder.append(keywordLength).append(":").append(keywordLengthStats.get(keywordLength).size()).append("\n");
//            stringBuilder.append(keywordLength).append(":").append(keywordLengthStats.get(keywordLength)).append("\n");
//        }
//        String filename = shareDirectory + "cleartext/keywordLengthStats";
//        remove(filename + ".txt");
//        writeToFile(filename, String.valueOf(stringBuilder));

//         2. Create bins for 1k, 5k and 10k keywords
//         remove existing bins and keyword stats

        {
            remove(shareDirectory + "cleartext/" + binFolder + "/" + "keywordStats.txt");
            for (int i = 0; i < Constant.getBinCount(); i++) {
                remove(shareDirectory + "cleartext/" + binFolder + "/" + "bin" + (i + 1) + ".txt");
            }

            // to sort keywords based on file count in ascending order
            System.out.println("Total number of keyword :" + keywordFileCount.size());
            Object[] a = keywordFileCount.entrySet().toArray();
            Arrays.sort(a, new Comparator() {
                public int compare(Object o1, Object o2) {
                    return ((Map.Entry<String, Integer>) o1).getValue()
                            .compareTo(((Map.Entry<String, Integer>) o2).getValue());
                }
            });

            // initializing bins
            StringBuilder[] bins = new StringBuilder[Constant.getBinCount()];
            for (int j = 0; j < bins.length; j++) {
                bins[j] = new StringBuilder("");
            }

            int i = 0, l = 0;
            Object[] b = new Object[keywordCount];
            for (int k = keywordFileCount.size() - keywordCount; k < keywordFileCount.size(); k++) {
                b[l] = a[k];
                l++;
            }
            a = b;

            // put the keywordCount keywords into bins of 1k, 5k and 10k
            StringBuilder str = new StringBuilder();
            String filename = shareDirectory + "cleartext/" + binFolder + "/" + "keywordStats";
            int[] count = new int[Constant.getBinCount()];
            while (i < keywordCount) {
                str = new StringBuilder();
                str.append(((Map.Entry<String, Integer>) a[i]).getKey()).append(":").append(((Map.Entry<String, Integer>) a[i]).getValue()).append("\n");
                writeToFile(filename, String.valueOf(str));
                int temp = 0;
                if (i % 10 == 0) {
                    temp = 0;
                } else if (i % 10 <= 4) {
                    temp = 1;
                } else {
                    temp = 2;
                }
                for (int j = temp; j < bins.length; j++) {
                    bins[j].append(str);
                    count[j] += ((Map.Entry<String, Integer>) a[i]).getValue(); // the number of files a keyword is present in
                }
                i++;
            }

            // writing to file the bins so created
            filename = shareDirectory + "cleartext/" + binFolder + "/" + "bin";
            System.out.println("Number of files in each bin");
            for (int j = 0; j < bins.length; j++) {
                writeToFile(filename + (j + 1), String.valueOf(bins[j]));
                System.out.println("bin" + (j + 1) + "=" + count[j]);
            }
        }

        System.out.println();

//        {
//            // 3. number of files a keyword can be in
//            String filename = shareDirectory + "cleartext/KeywordsFileStats";
//            remove(filename + ".txt");
//            System.out.println("Total number of keyword :" + keywordFileCount.size());
//            Object[] a = keywordFileCount.entrySet().toArray();
//            Arrays.sort(a, new Comparator() {
//                public int compare(Object o1, Object o2) {
//                    return ((Map.Entry<String, Integer>) o2).getValue()
//                            .compareTo(((Map.Entry<String, Integer>) o1).getValue());
//                }
//            });
//            int i = 0;
//            StringBuilder str;
//            while (i < a.length) {
//                str = new StringBuilder();
//                str.append(((Map.Entry<String, Integer>) a[i]).getKey()).append(":").append(((Map.Entry<String, Integer>) a[i]).getValue()).append("\n");
//                writeToFile(filename, String.valueOf(str));
//                i++;
//            }
//        }
    }

    /**
     * To move all the files from directories and subdirectories under documentDirectory path
     * Uses fileCount and clientCount as input
     */
    public static void aggregateDocuments() throws IOException {

        // delete existing documentDirectory
        deleteDirectory(new File(documentDirectory));

        // copying files to each client directory in equal amount
        int pivot = (int) Math.floor(fileCount / Double.parseDouble(String.valueOf(clientCount)));
        int start = 1;
        for (int i = 0; i < clientCount; i++) {
            new File(documentDirectory + (i + 1)).mkdirs();
            for (int j = 0; j < pivot; j++) {
                Files.copy(Path.of(mainDir + "aggregate_docs/" + start),
                        Path.of(documentDirectory + (i + 1) + "/" + start));
                start++;
            }
        }

        // copying remaining documents to first client directory
        if (start <= fileCount) {
            while (start <= fileCount) {
                Files.copy(Path.of("/Desktop/Research/D+/code_data/aggregate_docs/" + start),
                        Path.of(documentDirectory + clientCount + "/" + start));
                start++;
            }
        }
    }

    /**
     * sort fileKeywordCount and write to file
     */
    public static void getFileKeywordCount() {
        String filename = shareDirectory + "cleartext/fileKeywordsStats";
        remove(filename + ".txt");
        // to sort the fileKeywordCount map to get checkpoint1 and checkpoint2
        Object[] a = fileKeywordCount.entrySet().toArray();
        Arrays.sort(a, new Comparator() {
            public int compare(Object o1, Object o2) {
                return ((Map.Entry<Integer, Integer>) o1).getValue()
                        .compareTo(((Map.Entry<Integer, Integer>) o2).getValue());
            }
        });
        int i = 0;
        StringBuilder str;
        while (i < a.length) {
            str = new StringBuilder();
            str.append(((Map.Entry<Integer, Integer>) a[i]).getKey()).append(":").append(((Map.Entry<Integer, Integer>) a[i]).getValue()).append("\n");
            writeToFile(filename, String.valueOf(str));
            i++;
        }

    }

    /**
     * To create ACT, ADDR and inverted index
     */
    public static void dataStructureCreation() throws NoSuchAlgorithmException {

        List<String> temp;
        String[] shares;
        String[] keywordShares = new String[4];
        StringBuilder keywordClear = new StringBuilder("");
        String[] keywordPosition = new String[4];
        StringBuilder keywordPositionClear = new StringBuilder("");
        Arrays.fill(keywordShares, "");
        Arrays.fill(keywordPosition, "");
        String[][] actAccess = new String[clientCount][4];
        StringBuilder actAccessClear = new StringBuilder("");
        for (int i = 0; i < actAccess.length; i++) {
            Arrays.fill(actAccess[i], "");
        }
        String filename, hashValue;
        int indexNoOPT, indexOPT, indexOPTClear, status = 0, fileCountPerKeyword;
        Map<String, String> perKeywordFiles;
        colSize = keywordMaxFreq + Constant.getHashBlockCount();
        // cleartext of act DS
        // cleartext of act DS
        StringBuilder actCleartext = new StringBuilder("");
        // to store the share of act DS
        String[] actShareDS = new String[4];
        StringBuilder actClear = new StringBuilder("");
        Arrays.fill(actShareDS, "");
        long[] addr;
        List<String> vectorOpt, vectorNoOpt;
        StringBuilder invertedIndexOptCleartext, invertedIndexCleartext, addrCleartext, keywords;

        List<String> addrHashBlocks;
        keywords = new StringBuilder();
        int key_number=0;
        int rowSize=100;
        for (String token : keywordFileMap.keySet()) {
            key_number++;
            StringBuilder addrClear = new StringBuilder("");
            // string variables for cleartext values
            invertedIndexOptCleartext = new StringBuilder();
            invertedIndexCleartext = new StringBuilder();
            addrCleartext = new StringBuilder();
            vectorOpt = new ArrayList<>();
            vectorNoOpt = new ArrayList<>();
            hashBlocks = new long[Constant.getHashBlockCount()];

            // startPos, countItems, hash digest(startPos, countItems), hash digest position from startPos to countItems
            addr = new long[2 + (2 * Constant.getHashBlockCount())];
            perKeywordFiles = keywordFileMap.get(token); // all files of a keyword

            // for opt
            // to pad with zeros if the free row cells is not enough to accommodate the keyword file

//            System.out.println("sizeIIOPT:"+sizeIIOPT);
//            System.out.println("sizeIIOPT1:"+(addr[0] / colSize));
//            System.out.println("sizeIIOPT22:"+((addr[0] + Constant.getHashBlockCount() + perKeywordFiles.size() - 1)));
//            System.out.println("sizeIIOPT2:"+((addr[0] + Constant.getHashBlockCount() + perKeywordFiles.size() - 1) / colSize));
            if ((addr[0] / colSize) != (addr[0] + Constant.getHashBlockCount() + perKeywordFiles.size() - 1) / colSize) {
                for (int j = sizeIIOPT % colSize; j < colSize; j++) {
                    invertedIndexOptCleartext.append("0").append(",");
                    vectorOpt.add("0");
                    sizeIIOPT++;
                }
//                addr[0] = sizeIIOPT; // startPos
            }

//            System.out.println("sizeIIOPT1:" + sizeIIOPT);

//            for(String a:vectorOpt){
//                System.out.print(a+", ");
//            }
//            System.out.println();

            // used to put hash digest at desired position
            indexOPT = vectorOpt.size();
            indexOPTClear = invertedIndexOptCleartext.length();
//            System.out.println("indexOPT:"+indexOPT);
            indexNoOPT = 0;

            // computing hash digest of file ids
            hashValue = hashDigest(token);
            int p=0;
            for (String element : perKeywordFiles.keySet()) {
                hashValue = hashDigest(hashValue + element);
                // here opt
                invertedIndexOptCleartext.append(element).append(",");
                vectorOpt.add(element);
                // here non-opt
                invertedIndexCleartext.append(element).append(",");
                vectorNoOpt.add(element);
                // for addr
                // compute hash digest of each occupied cell for addr
                createAddHashBlocks(String.valueOf(sizeIIOPT));

                sizeIIOPT++; // to track the size of invertedIndexOPT

                if(p==0){
                    addr[0] = sizeIIOPT-1; // startPos
                    p=1;
                }
            }
//            System.out.println("sizeIIOPT2:" + sizeIIOPT);

//            System.out.println("indexOPT:"+indexOPT);
            // dividing the hash value of file ids into blocks and adding to vector
            temp = createStringBlocks(hashValue);

            while (temp.size() != Constant.getHashBlockCount()) {
                // for opt
                temp.add("0");
                // for non-opt
                temp.add("0");
            }
//            System.out.println("temp.size:" + temp.size());
            // for opt
            vectorOpt.addAll(indexOPT, temp);
            // for non-opt
            vectorNoOpt.addAll(indexNoOPT, temp);
//            for(String a:vectorOpt){
//                System.out.print(a+", ");
//            }
//            System.out.println();
            // adding zeroes if size is not upto HashBlockCount


            // appending hash value to cleartext string
            for (int i = temp.size() - 1; i >= 0; i--) {
                // for opt
                invertedIndexOptCleartext.insert(indexOPTClear, temp.get(i) + ",");
                // for non-opt
                invertedIndexCleartext.insert(indexNoOPT, temp.get(i) + ",");
                // for addr
                // compute hash digest of each occupied cell for addr
                createAddHashBlocks(String.valueOf(sizeIIOPT));

                sizeIIOPT++;
            }

//            System.out.println("sizeIIOPT3:" + sizeIIOPT);

            // here opt
//            invertedIndexOptCleartext.insert(0, "[");
//            invertedIndexOptCleartext.append("]");
            // adding fake padded
            int pad;
            if ((colSize - (sizeIIOPT % colSize)) < Constant.getPaddedFakes()) {
                if ((colSize - (sizeIIOPT % colSize)) > 0)
                    pad = (colSize - (sizeIIOPT % colSize));
                else {
                    pad = Constant.getPaddedFakes();
                }
            } else {
                pad = Constant.getPaddedFakes();
            }
            for (int j = 0; j < pad; j++) {
                invertedIndexOptCleartext.append("0").append(",");
                vectorOpt.add("0");

                sizeIIOPT++;
            }
//            sizeIIOPT++;
//            System.out.println("sizeIIOPT4:" + sizeIIOPT);
            invertedIndexOptCleartext.append("\n");
            //creating shares
            fileNameCleartext = shareDirectory + "cleartext/invertedIndexOpt" + (0);
            fileNameShare = shareDirectory + "share/invertedIndexOpt";
            createShares(vectorOpt, fileNameCleartext, invertedIndexOptCleartext, fileNameShare);
//            if(key_number<=keywordFileMap.size()/2){
//
//
//                if(key_number==keywordFileMap.size()/2){
//                    System.out.println("sizeIIOPT:"+sizeIIOPT);
//                    rowSize = (int) Math.ceil(sizeIIOPT / (double) colSize);
//                    System.out.println("rowsie:"+rowSize);
//                    System.out.println("colsize:"+colSize);
//                    invertedIndexOptCleartext = new StringBuilder();
//                    vectorOpt = new ArrayList<>();
//                    while (sizeIIOPT++ < (colSize * rowSize)) {
//                        invertedIndexOptCleartext.append("0").append(",");
//                        vectorOpt.add("0");
//                    }
//                    sizeIIOPT--;
//                    System.out.println("end:" + sizeIIOPT);
//                    System.out.println("vector size:" + vectorOpt.size());
//                    // creating shares
//                    if (vectorOpt.size() > 0) {
//                        fileNameCleartext = shareDirectory + "cleartext/invertedIndexOpt" + (0);
//                        fileNameShare = shareDirectory + "share/invertedIndexOpt";
//                        createShares(vectorOpt, fileNameCleartext, fileCleartext, fileNameShare);
//                    }
//                }
//
//            }


            {
                // here non-opt
                // padding each entry to max file count
                invertedIndexCleartext.insert(0, "[");
                invertedIndexCleartext.append("]");
                fileCountPerKeyword = keywordFileMap.get(token).size();
                while (fileCountPerKeyword++ != keywordMaxFreq) {
                    invertedIndexCleartext.append("0").append(",");
                    vectorNoOpt.add("0");
                }
                invertedIndexCleartext.append("\n");
                // creating shares
                fileNameCleartext = shareDirectory + "cleartext/invertedIndex" + (0);
                fileNameShare = shareDirectory + "share/invertedIndex";
                createShares(vectorNoOpt, fileNameCleartext, invertedIndexCleartext, fileNameShare);

            }

            //System.out.println();
            // for addr
            // copying hash value of positions to ADDR table
            for (int i = 0; i < Constant.getHashBlockCount(); i++) {
                addr[2 + Constant.getHashBlockCount() + i] = hashBlocks[i];
            }
            addr[1] = Constant.getHashBlockCount() + perKeywordFiles.size(); //  countItems
            // hash digest of start and item count
            addrHashBlocks = createStringBlocks(hashDigest(hashDigest(String.valueOf(addr[0])) + addr[1]));
            createAddHashBlocks(hashDigest(String.valueOf(addr[0])) + addr[1]);
            for (int i = 0; i < Constant.getHashBlockCount(); i++) {
                addr[2 + i] = Long.parseLong(addrHashBlocks.get(i));
            }
            String str = Arrays.toString(addr).replace("[", "");
            str = str.replace("]", "");
            // share creation for addr
            addrCleartext.append(status + 1).append(".").append(token).append(",").append(Arrays.toString(addr));
            addrClear.append(str);
            addrClear.append("\n");
            writeToFile(shareDirectory + "cleartext/addr00", String.valueOf(addrClear));

            addrCleartext.append("\n");
            fileNameCleartext = shareDirectory + "cleartext/addr" + (0);
            fileNameShare = shareDirectory + "share/addr";
            createShares(addr, fileNameCleartext, addrCleartext, fileNameShare);
//            if(key_number<=keywordFileMap.size()/2){
//
//
//            }

            // act table creation
            keywordToNumber(token);
            //padding token to avoid leakage due to keyword size
            if (numericText.length() < 2 * Constant.getMaxKeywordLength()) {
                while (numericText.length() < 2 * Constant.getMaxKeywordLength())
                    numericText.append("99");
            }
            // for cleartext act
            actCleartext.append(status + 1).append(".").append(token).append("(").append(numericText).append("):").append(keywordClientAccess.get(token).toString()).append("\n");
            // creating share for numeric keyword values
            serverCount = 4;
            shares = shamirSecretShares(String.valueOf(numericText), serverCount);
            for (int i = 0; i < serverCount; i++) {
                keywordShares[i] += shares[i] + ",";
            }
            keywordClear.append(numericText).append(",");
            // creating share for numeric keyword values position
            shares = shamirSecretShares(status + 1, serverCount);
            for (int i = 0; i < serverCount; i++) {
                keywordPosition[i] += shares[i] + ",";
            }
            keywordPositionClear.append((status + 1)).append(",");
            // creation of share for access on keywords
            int client = 0;
            for (String element : keywordClientAccess.get(token)) {
                shares = shamirSecretShares(element, serverCount);
                for (int i = 0; i < serverCount; i++) {
                    actAccess[client][i] += shares[i] + ",";
                }
                client++;
                actAccessClear.append(element).append(",");
            }

            serverCount = 3;

            // storing all keywords
            keywords.append(token).append(",");

            // logging the status of completion
            status++;
            if (status % 100 == 0)
                System.out.println("Completed reading " + status + " keywords");

        }
        // write all keywords to file
        writeToFile(shareDirectory + "cleartext/keywords", keywords.toString());
        keywordCount = keywordFileMap.size();
        keywordFileMap = null;
        keywordClientAccess = null;

        // merging all client access share and keywords share into one
        serverCount = 4;
        for (int j = 0; j < serverCount; j++) {
            actShareDS[j] += keywordShares[j] + "\n" + keywordPosition[j] + "\n";
            for (int i = 0; i < clientCount; i++) {
                actShareDS[j] += actAccess[i][j] + "\n";
            }
        }
        actClear.append(keywordClear).append("\n").append(keywordPositionClear).append("\n").append(actAccessClear);
        keywordPosition = null;
        keywordShares = null;
        // writing act share
        //cleartext
        writeToFile(shareDirectory + "cleartext/act0", String.valueOf(actCleartext));
        writeToFile(shareDirectory + "cleartext/act00", String.valueOf(actClear));
        // writing the share to files
        for (int i = 0; i < serverCount; i++) {
            // writing share of act DS to file
            filename = shareDirectory + "share/act" + (i + 1);
            writeToFile(filename, actShareDS[i]);
        }
        serverCount = 3;

        // filling all the empty columns of last row of op inverted index
        {
            rowSize = (int) Math.ceil(sizeIIOPT / (double) colSize);
            invertedIndexOptCleartext = new StringBuilder();
            vectorOpt = new ArrayList<>();
            System.out.println("end:" + sizeIIOPT);
            while (sizeIIOPT++ < (colSize * rowSize)) {
                invertedIndexOptCleartext.append("0").append(",");
                vectorOpt.add("0");
            }
            sizeIIOPT--;
            System.out.println("end:" + sizeIIOPT);
            System.out.println("end1:" + vectorOpt.size());
            // creating shares
            if (vectorOpt.size() > 0) {
                fileNameCleartext = shareDirectory + "cleartext/invertedIndexOpt" + (0);
                fileNameShare = shareDirectory + "share/invertedIndexOpt";
                createShares(vectorOpt, fileNameCleartext, fileCleartext, fileNameShare);
            }
        }
    }

    /**
     * Processes each file for extracting keywords
     *
     * @param file     The file to be processed for keywords
     * @param clientId The client id who has access to all keywords for this file
     * @param fileId   The id of the file
     * @throws IOException
     */
    public static void filePreprocessing(File file, String clientId, String fileId) throws IOException, NoSuchAlgorithmException, ClassNotFoundException, InstantiationException, IllegalAccessException {
        // reading file
        String content;
        try {
            content = Files.readString(file.toPath());
        } catch (Exception e) {
            return;
        }

        // initialization the stemmer for english keywords
        Class stemClass = Class.forName("org.tartarus.snowball.ext.englishStemmer");
        SnowballStemmer stemmer = (SnowballStemmer) stemClass.newInstance();

        BigInteger randomBig;
        LinkedHashMap<String, String> tempMap;
        String position;
        List<String> fileKeys = new ArrayList<>();
        hashBlocks = new long[Constant.getHashBlockCount()];

//        List<String> fileKeywords = new ArrayList<>(keywordList.size());
//        for(int i=0;i<keywordList.size();i++){
//            fileKeywords.add("0");
//        }
        // extract token for each line
        String[] tokens = content.split("[.;:!?/\\\\,#@$&)(\" =]");
        for (String token : tokens) {
            token = token.toLowerCase();
            token = token.trim();

            // check if token is all alphabetic and of desired length
            if ((token.length() >= Constant.getMinKeywordLength() && token.length() <= Constant.getMaxKeywordLength())
                    && token.matches("[a-z]+")) {

                // perform stemming of the token
                stemmer.setCurrent(token);
                stemmer.stem();
                token = stemmer.getCurrent();

                // storing each token access for client and their corresponding file id
                if (keywordList.containsKey(token)) {
                    if (!keywordFileMap.containsKey(token)) {
                        // storing keyword as key and file ids containing keyword as value
                        keywordFileMap.put(token, new LinkedHashMap<>());
                        // storing position of token
                        keywordPostion.put(token, String.valueOf(++indexPos));
//                        fileKeywords.set(indexPos-1, "1");
                        randomBig = generateBigIntegerRandomNum(seedDBO);
//                      generateBigIntegerRandomNum(seedDBO+indexPos);
                        // initializing access for all the clients as no access
                        keywordClientAccess.put(token, new ArrayList<>(Collections.nCopies(clientCount, String.valueOf(randomBig))));
                    }
                    // storing the file id corresponding to the keyword
                    if (!keywordFileMap.get(token).containsKey(String.valueOf(fileId))) {
                        tempMap = keywordFileMap.get(token);
                        tempMap.put(String.valueOf(fileId), "");
                        keywordFileMap.put(token, tempMap);
//                        fileKeywords.set(Integer.parseInt(keywordPostion.get(token))-1, "1");
                    }
                    // setting access as true for the client
                    keywordClientAccess.get(token).set(Integer.parseInt(clientId) - 1, Constant.getAccessConstant());
                    position = keywordPostion.get(token);
                    if (!fileKeys.contains(position)) {
                        fileKeys.add(position);
                        createAddHashBlocks(position);
                    }
                }
            }
        }

        // creation of file keyword data structure

//        {
//            fileKeywordCleartext = new StringBuilder();
//            fileKeywordCleartext.append(fileKeywords);
//            fileKeywordCleartext.replace(0, 1, "");
//            fileKeywordCleartext.replace(fileKeywordCleartext.length() - 1, fileKeywordCleartext.length(), "");
//            fileKeywordCleartext.append("\n");
//
//            fileNameCleartext = shareDirectory + "cleartext/fileKeywordLarge" + (0);
//            fileNameShare = shareDirectory + "share/fileKeywordLarge";
//            createShares(fileKeywords, fileNameCleartext, fileKeywordCleartext, fileNameShare);
//        }

//         1. to calculate the number of max and minimum keywords count a file can have
//        fileKeywordCount.put(Integer.valueOf(fileId), fileKeys.size());
        {
            // creation of file data structure
            StringBuilder fileCleartext = new StringBuilder();
            convertToNumeric(content);
            List<String> fileVector = new ArrayList<>();

            // appending hash digest of the file content
            fileVector.addAll(createStringBlocks(hashDigest(String.valueOf(newText))));
            if (fileVector.size() < Constant.getHashBlockCount()) {
                while (fileVector.size() != Constant.getHashBlockCount())
                    fileVector.add("0");
            }

            // adding string blocks of numericText
            fileVector.addAll(createStringBlocks(String.valueOf(numericText)));
//            int x = fileVector.size();
//            while (x != (19148)) {
//                fileVector.add("0");
//                x = fileVector.size();
//            }
            fileCleartext.append(fileVector);
//            System.out.println(fileCleartext);
            fileCleartext.replace(0, 1, "");
            fileCleartext.replace(fileCleartext.length() - 1, fileCleartext.length(), "");
            fileCleartext.append("\n");

            // computing the max size of file
            if (maxFileSize < fileVector.size()) {
                maxFileSize = fileVector.size();
            }
            fileNameCleartext = shareDirectory + "cleartext/file" + (0);
            fileNameShare = shareDirectory + "share/file";
            createShares(fileVector, fileNameCleartext, fileCleartext, fileNameShare);

//            // creating shares and writing to the file
//            if(Long.parseLong(fileId)<=(fileCount/2)) {
//
//            }




            fileKeywordCleartext = new StringBuilder();
            // pad fileKeys list to checkpoint2 (the min value)
            int pad;
            int oldSize = fileKeys.size();
//            System.out.println(fileKeys.size());
            if (fileKeys.size() <= checkpoint2) {
                pad = checkpoint2 - fileKeys.size();
            } else {
                pad = checkpoint1 - fileKeys.size();
            }
            for (int i = 0; i < pad; i++)
                fileKeys.add("0");

//            System.out.println("i:"+fileId);
//            System.out.println(pad);
//            System.out.println(checkpoint2);
//            System.out.println(checkpoint1);


            // if a file has no keywords from keywordList, a constant hash digest is taken else the
            // real hash digest hashBlocks is taken
            if (oldSize != 0) {
                for (int i = 0; i < Constant.getHashBlockCount(); i++)
                    fileKeys.add(i, String.valueOf(hashBlocks[i]));
            } else {
                for (int i = 0; i < Constant.getHashBlockCount(); i++)
                    fileKeys.add(i, hashConstant.get(i));
            }

//            fileKeys.add(0, fileId); // add fileId in the beginning
//            fileKeywordCleartext.append(fileId).append(":").append(fileKeys).append("\n");
            fileKeywordCleartext.append(fileKeys);
            fileKeywordCleartext.replace(0, 1, "");
            fileKeywordCleartext.replace(fileKeywordCleartext.length() - 1, fileKeywordCleartext.length(), "");
            fileKeywordCleartext.append("\n");

//            System.out.println("file="+fileKeys.size());
            // creating shares and writing to file


            fileNameCleartext = shareDirectory + "cleartext/fileKeyword" + (0);
            fileNameShare = shareDirectory + "share/fileKeyword";
            createShares(fileKeys, fileNameCleartext, fileKeywordCleartext, fileNameShare);
        }
    }

    public static void readFile() throws IOException, NoSuchAlgorithmException, ClassNotFoundException, InstantiationException, IllegalAccessException {
        readBinKeywords(binNumber);
        System.out.println("The number of keywords in the bin" + binNumber + " is " + keywordList.size());

        // used as hash digest in fileKeyword data structure for files containing no keywords from the keywordList
        hashConstant = createStringBlocks(hashDigest(String.valueOf(keywordCount + 1)));

        // reading all files to prepare keyword-file id mapping for keywords in keywordList
        String filename;
        int status = 0, fileId = 1, clientId = 1;
        while (clientId <= clientCount) {
            File file = new File(documentDirectory + clientId + "/" + fileId);
            while (file.exists()) { // check if file exists
                filePreprocessing(file, String.valueOf(clientId), String.valueOf(fileId));

                fileId++;
                file = new File(documentDirectory + clientId + "/" + fileId);
                // logging the status of completion
                status++;
                if (status % 10000 == 0)
                    System.out.println("Completed reading " + status + " files");
            }
            clientId++;
        }
        System.out.println("Number of files read: " + (fileId - 1) + " by clients:" + (clientId - 1));

        addSampleFile();
        System.out.println("size:" + keywordFileMap.size());
//        getFileKeywordCount();
        System.out.println("Reading files completed");
        cleanUp();

        dataStructureCreation();
        System.out.println("Data structures creation completed");

        display();
    }

    /**
     * Performs initialization of outsource parameters
     */
    public static void initialization() throws IOException, ClassNotFoundException, InstantiationException, IllegalAccessException {

        // reads outsource properties file
        String pathName = "config/outsource.properties";
        Properties properties = Helper.readPropertiesFile(pathName);

        mainDir = properties.getProperty("mainDir");
        documentDirectory = mainDir + "document/";
        shareDirectory = mainDir + "DocumentSearch_HE/data/";

        fileCount = Integer.parseInt(properties.getProperty("fileCount"));
        clientCount = Integer.parseInt(properties.getProperty("clientCount"));
        keywordCount = Integer.parseInt(properties.getProperty("keywordCount"));
        binFolder = properties.getProperty("binFolder");
        binNumber = Integer.parseInt(properties.getProperty("binNumber"));
        seedDBO = Integer.parseInt(properties.getProperty("seedDBO"));
        checkpoint1 = Integer.parseInt(properties.getProperty("checkpoint1"));
        checkpoint2 = Integer.parseInt(properties.getProperty("checkpoint2"));
        keywordMaxFreq = Integer.parseInt(properties.getProperty("keywordMaxFreq"));
        System.out.println("keywordMaxFreq:" + keywordMaxFreq);
        serverCount = 3;


        removeFiles();

        System.out.println("Creation of client directories started...");
//        aggregateDocuments();
        System.out.println("Creation of client directories completed!");

        System.out.println("Creation of keyword bins started...");
//        keywordFileStats();
//        System.out.println("Creation of keyword bins completed!");
        System.out.println(" checkpoint1:" + checkpoint1);
        System.out.println(" checkpoint2:" + checkpoint2);
    }


    public static void main(String[] args) throws IOException, NoSuchAlgorithmException, ClassNotFoundException, InstantiationException, IllegalAccessException {
        initialization();
        Instant start = Instant.now();
        readFile();
        Instant end = Instant.now();
        System.out.println("Time taken for data outsourcing is " + Duration.between(start, end).toMinutes() + " mins");
    }
}