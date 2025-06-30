package constants;

import java.math.BigInteger;

public class Constant {
    private static String padding = "99";
    private static final int minRandomBound = 2;
    private static final int maxRandomBound = 20;
    private static final long modParameter = 10000007;
//    private static final BigInteger modBigParameter = new BigInteger("100000000000000000000000000000000000007");
    private static final BigInteger modBigParameter = new BigInteger("1000000000000000000000000000000000000000000000007");
    private static final int hashBlockCount = 8;
    private static final int hashBlockSize = 6;
    private static final int hashBlockSize1 = 48;
    private static final String delimiter = ".;:!?#@$&() =";
    private static final int maxKeywordCount = 1000;
    private static final int paddedFakes = 5;
    private static final String sampleFile = "Hello world";
    private static final BigInteger maxLimitNoAccess = new BigInteger("38373737373737373737373737373737373737");
    private static final BigInteger minLimitNoAccess = new BigInteger("37373737373737373737373737373737373737");
    private static final String accessConstant = "0";
    private static final int maxKeyOccurrence = 10000;
    private static final int minKeywordLength = 4;
    private static final int maxKeywordLength = 19; // 19
    private static final int minDataDistribution = 10;
    private static final int maxDataDistribution = 30;
    private static final int binCount = 3;
    private static final int longLength=18;
    private static final int stringBlock=4;


    public static int getHashBlockSize1(){
        return  hashBlockSize1;
    }
    public  static int getStringBlock(){
        return stringBlock;
    }
    public static int getLongLength(){
        return longLength;
    }
    public static String getPadding() {
        return padding;
    }

    /**
     * The minimum bound for random value generation
     *
     * @return the minimum value
     */
    public static int getMinRandomBound() {
        return minRandomBound;
    }

    /**
     * The maximum bound for random value generation
     *
     * @return the maximum value
     */
    public static int getMaxRandomBound() {
        return maxRandomBound;
    }

//    /**
//     * The mod value for long type
//     *
//     * @return the mod value
//     */
//    public static BigInteger getModBigParameter2() {
//        return modBigParameter2;
//    }

    /**
     * The mod value for long type
     *
     * @return the mod value
     */
    public static long getModParameter() {
        return modParameter;
    }

    /**
     * The mod value for Biginteger type
     *
     * @return the mod value
     */
    public static BigInteger getModBigParameter() {
        return modBigParameter;
    }

    /**
     * To return the number of hash blocks
     * @return
     */
    public static int getHashBlockCount() {
        return hashBlockCount;
    }

    /**
     * To return the size of a hash block
     * @return
     */
    public static int getHashBlockSize() {
        return hashBlockSize;
    }

    public static String getDelimiter() {
        return delimiter;
    }

    /**
     * The maximum number of keywords read from the file
     *
     * @return the maximum number of keywords
     */
    public static int getMaxKeywordCount() {
        return maxKeywordCount;
    }

    /**
     * The number of fakes added to opt inverted index
     *
     * @return the number of fakes
     */
    public static int getPaddedFakes() {
        return paddedFakes;
    }

    public static String getSampleFile() {
        return sampleFile;
    }

    /**
     * The constant to denote the minimum no-access of client value
     *
     * @return the minimum no-access constants
     */
    public static BigInteger getMinLimitNoAccess() {
        return minLimitNoAccess;
    }

    /**
     * The constant to denote the maximum no-access of client value
     *
     * @return the maximum no-access constants
     */
    public static BigInteger getMaxLimitNoAccess() {
        return maxLimitNoAccess;
    }

    /**
     * The constants to denote the access of client over the keyword
     *
     * @return the access constants
     */
    public static String getAccessConstant() {
        return accessConstant;
    }

    /**
     * The maximum length of keywords considered for pre-processing
     *
     * @return the maximum length
     */
    public static int getMaxKeywordLength() {
        return maxKeywordLength;
    }

    /**
     * The minimum length of keywords considered for pre-processing
     *
     * @return the minimum length
     */
    public static int getMinKeywordLength() {
        return minKeywordLength;
    }

    /**
     * The minimum data distribution for keyword increase experiments
     *
     * @return the minimum value for data distribution
     */
    public static int getMinDataDistribution() {
        return minDataDistribution;
    }

    /**
     * The maximum data distribution for keyword increase experiments
     *
     * @return the maximum value for data distribution
     */
    public static int getMaxDataDistribution() {
        return maxDataDistribution;
    }

    public static int getBinCount() {
        return binCount;
    }
}
