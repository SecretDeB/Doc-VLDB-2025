//
//  main.cpp
//  
//
//  Created on 3/7/24.
//




//#include <iostream>
//
//using namespace std;
//int main() {
//    std::cout << "Hello, World!" << std::endl;
//    //    EncryptionParameters parms(scheme_type::bfv);
//    return 0;
//}

#include <iostream>
#include <cmath>
#include "seal/seal.h"
#include "main.h"

using namespace seal;
using namespace std;
using namespace std::chrono;

//using namespace boost::multiprecision;

SEALContext *context;
Evaluator *evaluator;
Encryptor *encryptor;
Decryptor *decryptor;
RelinKeys relin_keys;
BatchEncoder *batch_encoder;
size_t slot_count,row_size,poly_modulus_degree;
int row_index,start_,end_;

long lagrangeInterpolationAsLong( vector<uint64_t> share, int length) {
    switch (length) {
        case 2:
            return 2 * share[0] - share[1];
        case 3:
            return (3 * share[0]) - (3 * share[1]) + share[2];
        default:
            throw runtime_error("Unexpected value: " + to_string(length));
    }
}

void display(vector<uint64_t> data, int m){
    cout<<"Original :"<<endl;
    for (size_t i=0; i<m;i++) {
        cout<<data[i]<<",";
    }
    cout<<endl;
}

void display(vector<vector<uint64_t>> data, int m, int n){
    cout<<"Original :"<<endl;
    for (size_t i=0; i<m;i++) {
        for(size_t j=0;j<n;j++ ){
            cout<<data[i][j]<<",";
        }
        cout<<endl;
    }
}

vector<vector<uint64_t>> initializeArray(int m, int n){
    vector<vector<uint64_t>> data(m);
    uint64_t t=rand()% 100 +1;
    for (size_t i=0; i<m;i++) {
        data[i] = vector<uint64_t>(n);
        for(size_t j=0;j<n;j++ ){
            data[i][j]=t;
            t=rand()% 100 +1;
        }
    }
//    display(data, m,n);
    return data;
}

vector<uint64_t> initializeArray(int m){
    vector<uint64_t> data(m);
    uint64_t t=rand()% 100 +1;
    for (size_t i=0; i<m;i++) {
        data[i]=t;
        t=rand()% 100 +1;
    }
//    data[0]=1;
//    display(data, m);
    return data;
}

vector<uint64_t> initializeCol(int m){
    vector<uint64_t> data(m);
    uint64_t t=rand()% 100 +1;
    for (size_t i=0; i<m;i++) {
        data[i]=0;
        t=rand()% 100 +1;
    }
    data[0]=1;
    data[2]=1;
    data[4]=1;
    data[6]=1;
    data[8]=1;
//    display(data, m);
    return data;
}

vector<uint64_t> initializeColInvertedIndex(int m){
    vector<uint64_t> data(m);
    uint64_t t=rand()% 100 +1;
    for (size_t i=0; i<m;i++) {
        data[i]=t;
        t=rand()% 100 +1;
    }
//    display(data, m);
    return data;
}

//vector<Ciphertext> encrypt(vector<uint64_t> data, int m){
//    vector<Ciphertext> result(m);
//    Ciphertext x_encrypted;
//    for (size_t i=0; i<m;i++) {
//        Plaintext x_plain(uint64_to_hex_string(data[i]));
//        encryptor->encrypt(x_plain, x_encrypted);
//        result[i]=x_encrypted;
//    }
//    return result;
//}

vector<vector<Ciphertext>> encrypt(vector<vector<uint64_t>> data, int m, int n){
    vector<vector<Ciphertext>> result(m);
    Plaintext plain_matrix;
    Ciphertext encrypted_matrix;
    vector<uint64_t> pod_result;
    vector<uint64_t> vec_temp;
    int bound=ceil(n/double(poly_modulus_degree));
    cout<<"bound:"<<bound<<endl;
    int start,end;
    for (int i=0; i<m; i++) {
        result[i]=vector<Ciphertext>(bound);
        for(int j=0;j<bound;j++){
            start=j*poly_modulus_degree;
            end=start+poly_modulus_degree;
            if(end>n){
                end=n;
            }
            vec_temp= std::vector<uint64_t>(data[i].begin() +start,data[i].begin() + end);
            batch_encoder->encode(vec_temp, plain_matrix);
//            batch_encoder->decode(plain_matrix, pod_result);
//            print_matrix(pod_result, row_size);
//            cout << "plaintext matrix size:" <<pod_result.size() << endl;
//            print_line(__LINE__);
//            cout << "Encrypt plain_matrix to encrypted_matrix." << endl;
            encryptor->encrypt(plain_matrix, result[i][j]);
        }
    }
    return result;
}

vector<Ciphertext> encrypt(vector<uint64_t> data,int n){
    vector<Ciphertext> result(n);
    Plaintext plain_matrix;
    Ciphertext encrypted_matrix;
    vector<uint64_t> pod_result;
    vector<uint64_t> vec_temp;
    int bound=ceil(n/double(poly_modulus_degree));
    cout<<"bound:"<<bound<<endl;
    int start,end;
    for(int j=0;j<bound;j++){
        start=j*poly_modulus_degree;
        end=start+poly_modulus_degree;
        if(end>n){
            end=n;
        }
        vec_temp= std::vector<uint64_t>(data.begin() +start,data.begin() + end);
        batch_encoder->encode(vec_temp, plain_matrix);
//        batch_encoder->decode(plain_matrix, pod_result);
//        print_matrix(pod_result, row_size);
//        cout << "plaintext matrix size :" <<pod_result.size() << endl;
//        print_line(__LINE__);
//        cout << "Encrypt plain_matrix to encrypted_matrix." << endl;
        encryptor->encrypt(plain_matrix, result[j]);
    }
    return result;
}

vector<vector<Ciphertext>> encrypt(int m,int n, int index){
    vector<vector<Ciphertext>> result(m);
    int bound=ceil(n/double(poly_modulus_degree));
    cout<<"boumd:"<<bound;
    Plaintext plain_matrix;
    Ciphertext encrypted_matrix;
    vector<uint64_t> pod_result;
    vector<uint64_t> row_vec_zero(poly_modulus_degree,0ULL);
    vector<uint64_t> row_vec_one(poly_modulus_degree,1ULL);
    vector<uint64_t> row_vec(poly_modulus_degree,0ULL);
    for (int i=0; i<m; i++) {
        if(index==i)
        {
            row_vec=row_vec_one;
        }
        result[i]=vector<Ciphertext>(bound);
        for(int j=0;j<bound;j++){
//            cout<<"j:"<<j<<" i:"<<i<<endl;
            batch_encoder->encode(row_vec, plain_matrix);
//            batch_encoder->decode(plain_matrix, pod_result);
//           print_matrix(pod_result, row_size);
//           cout << "plaintext matrix size :" <<pod_result.size() << endl;
//           print_line(__LINE__);
//           cout << "Encrypt plain_matrix to encrypted_matrix LOLLL." << endl;
            encryptor->encrypt(plain_matrix, result[i][j]);
        }
        if(index==i)
        {
            row_vec=row_vec_zero;
        }
    }
    return result;
}

vector<Ciphertext> encrypt(int n, uint64_t value){
    int bound=ceil(n/double(poly_modulus_degree));
    vector<Ciphertext> result(bound);
    Plaintext plain_matrix;
    Ciphertext encrypted_matrix;
    vector<uint64_t> pod_result;
    vector<uint64_t> row_vec_value(poly_modulus_degree,value);
    for(int j=0;j<bound;j++){
        batch_encoder->encode(row_vec_value, plain_matrix);
//        batch_encoder->decode(plain_matrix, pod_result);
//        print_matrix(pod_result, row_size);
//        cout << "plaintext matrix size :" <<pod_result.size() << endl;
//        print_line(__LINE__);
//        cout << "Encrypt plain_matrix to encrypted_matrix." << endl;
        encryptor->encrypt(plain_matrix, result[j]);
    }
    return result;
}



vector<Ciphertext> encryptColVector(int n, int start_, int end_){
    
    cout<<"heer"<<endl;
    int bound=ceil(n/double(poly_modulus_degree));
    vector<uint64_t> data(n);
    for (int i = 0; i < n; i++) {
        if (i < start_ || i > end_)
            data[i] = 1;
    }
    for (int i = 0; i < n; i++) {
        cout<<data[i]<<",";
    }
    cout<<endl;
    vector<Ciphertext> result(bound);
    Plaintext plain_matrix;
    Ciphertext encrypted_matrix;
    vector<uint64_t> pod_result;
    vector<uint64_t> vec_temp;
    int start,end;
    for(int j=0;j<bound;j++){
        start=j*poly_modulus_degree;
        end=start+poly_modulus_degree;
        if(end>n){
            end=n;
        }
        vec_temp= std::vector<uint64_t>(data.begin() +start,data.begin() + end);
        batch_encoder->encode(vec_temp, plain_matrix);
//        batch_encoder->decode(plain_matrix, pod_result);
//       print_matrix(pod_result, row_size);
//       cout << "plaintext matrix size:" <<pod_result.size() << endl;
//       print_line(__LINE__);
//       cout << "Encrypt plain_matrix to encrypted_matrix." << endl;
        encryptor->encrypt(plain_matrix, result[j]);
    }
    return result;
}

vector<vector<Ciphertext>> encryptAddr(vector<vector<uint64_t>> data, int m, int n){
    vector<vector<Ciphertext>> result(m);
    Ciphertext x_encrypted;
    for (size_t i=0; i<m;i++) {
        result[i] = vector<Ciphertext>(n);
        for(size_t j=0;j<n;j++ ){
            cout<<"i:"<<i<<"j:"<<j<<endl;
            Plaintext x_plain(uint64_to_hex_string(data[i][j]));
            encryptor->encrypt(x_plain, x_encrypted);
            result[i][j]=x_encrypted;
        }
    }
    return result;
}

//vector<Ciphertext> encryptAddr(vector<uint64_t> data, int m){
//    vector<Ciphertext> result(m);
//    Ciphertext x_encrypted;
//    for (size_t i=0; i<m;i++) {
////        cout<<"m:"<<i<<endl;
//        Plaintext x_plain(uint64_to_hex_string(data[i]));
//        encryptor->encrypt(x_plain, x_encrypted);
//        result[i]=x_encrypted;
//    }
//    return result;
//}


void decrypt(vector<Ciphertext> data, int m){
    cout<<"Decrypted :"<<endl;
    Plaintext decrypted_result;
    for (size_t i=0; i<m;i++) {
        decryptor->decrypt(data[i], decrypted_result);
        string str1 =decrypted_result.to_string();
        int ptr=stoi(str1, 0, 16);;
        cout<< ptr <<",";
    }
    cout<<endl;

}

void decrypt(vector<vector<Ciphertext>> data, int m, int n){
    cout<<"Decrypted :"<<endl;
    Plaintext decrypted_result;
    for (size_t i=0; i<m;i++) {
        for(size_t j=0;j<n;j++ ){
            decryptor->decrypt(data[i][j], decrypted_result);
            string str1 =decrypted_result.to_string();
            int ptr=stoi(str1, 0, 16);;
        }
    }
}

vector<Ciphertext> dotProduct(vector<vector<Ciphertext>> data1,vector<vector<Ciphertext>> data2, int m, int n){

    int bound=ceil(n/double(poly_modulus_degree));
    vector<Ciphertext> result(bound);
    Ciphertext temp;
    vector<uint64_t> pod_result;
    Plaintext plain_result;

    
    for (size_t i=0; i<m;i++) {
        for(int j=0;j<bound;j++){
//            cout<<"j:"<<j<<" i:"<<i<<endl;
//            decryptor->decrypt(data1[i][j], plain_result);
//            batch_encoder->decode(plain_result, pod_result);
//            cout << "    + Result plaintext matrix ...... Correct ." << endl;
//            print_matrix(pod_result, row_size);
            evaluator->multiply_inplace(data1[i][j], data2[i][j]);
//            decryptor->decrypt(data1[i][j], plain_result);
//            batch_encoder->decode(plain_result, pod_result);
//            cout << "    + Result plaintext matrix ...... Correct ." << endl;
//            print_matrix(pod_result, row_size);
            evaluator->relinearize_inplace(data1[i][j], relin_keys);
            if(i==0){
                result[j]=data1[i][j];
            }else{
                evaluator->add_inplace(result[j],data1[i][j]);
//                decryptor->decrypt(result[j], plain_result);
//                batch_encoder->decode(plain_result, pod_result);
//                cout << "    + Result plaintext matrix ...... Correct ." << endl;
//                print_matrix(pod_result, row_size);
//                cout << "Encrypt plain_matrix to encrypted_matrix." << endl;
            }
        }
    }
    return result;
}

vector<Ciphertext> dotProductActKeys(vector<vector<Ciphertext>> data1,vector<Ciphertext> data2, int n){

    int bound=ceil(n/double(poly_modulus_degree));
    vector<Ciphertext> result(bound);
    Ciphertext temp;
    vector<uint64_t> pod_result;
    Plaintext plain_result;

    
        for(int j=0;j<bound;j++){
//            decryptor->decrypt(data1[2][j], plain_result);
//            batch_encoder->decode(plain_result, pod_result);
//            cout << "    + Result plaintext matrix ...... Correct ." << endl;
//            print_matrix(pod_result, row_size);
            evaluator->multiply(data1[2][j], data2[j],result[j]);
//            decryptor->decrypt(result[j], plain_result);
//            batch_encoder->decode(plain_result, pod_result);
//            cout << "    + Result plaintext matrix ...... Correct ." << endl;
//            print_matrix(pod_result, row_size);
            evaluator->relinearize_inplace(data1[2][j], relin_keys);
        }
    
    return result;
}


vector<Ciphertext> dotProduct(vector<vector<Ciphertext>> data1,vector<vector<Ciphertext>> data2, vector<Ciphertext> data3,vector<Ciphertext> data4, int m, int n){

    int bound=ceil(n/double(poly_modulus_degree));
    cout<<"dot"<<endl;
    vector<Ciphertext> result(bound);
    Ciphertext temp;
    vector<uint64_t> pod_result;
    Plaintext plain_result;
    for (size_t i=0; i<m;i++) {
        for(int j=0;j<bound;j++){
            evaluator->multiply_inplace(data1[i][j], data2[i][j]);
//            print_line(__LINE__);
//            cout << "mul." << endl;
//            decryptor->decrypt(data1[i][j], plain_result);
//            batch_encoder->decode(plain_result, pod_result);
//            print_matrix(pod_result, row_size);
            evaluator->relinearize_inplace(data1[i][j], relin_keys);
            
            if(i==0){
                result[j]=data1[i][j];
            }else{
                evaluator->add_inplace(result[j],data1[i][j]);
//                print_line(__LINE__);
//                cout << "mul." << endl;
//                decryptor->decrypt(result[j], plain_result);
//                batch_encoder->decode(plain_result, pod_result);
//                print_matrix(pod_result, row_size);
            }
        }
    }

    for(int j=0;j<bound;j++){
        evaluator->multiply_inplace(data4[j], data3[j]);
//        print_line(__LINE__);
        
//        cout << "rand * col." << endl;
//        decryptor->decrypt(data4[j], plain_result);
//        batch_encoder->decode(plain_result, pod_result);
//        cout << "    + Result plaintext matrix ...... Correct." << endl;
//        print_matrix(pod_result, row_size);
        evaluator->add_inplace(result[j], data4[j]);
//        print_line(__LINE__);
//        cout << "ADD." << endl;
//        decryptor->decrypt(result[j], plain_result);
//        batch_encoder->decode(plain_result, pod_result);
//        cout << "    + Result plaintext matrix ...... Correct." << endl;
//        print_matrix(pod_result, row_size);
    }
    return result;
}

void initialize(int x){
    EncryptionParameters parms(scheme_type::bfv);
    poly_modulus_degree = x;
    parms.set_poly_modulus_degree(poly_modulus_degree);
    parms.set_coeff_modulus(CoeffModulus::BFVDefault(poly_modulus_degree));
    parms.set_plain_modulus(PlainModulus::Batching(poly_modulus_degree, 50));
    context = new SEALContext(parms);
    print_line(__LINE__);
    cout << "Set encryption parameters and print" << endl;
    print_parameters(*context);
    cout << "Parameter validation (success): " << context->parameter_error_message() << endl;
    auto qualifiers = context->first_context_data()->qualifiers();
    cout << "Batching enabled: " << boolalpha << qualifiers.using_batching << endl;
    // keys
    KeyGenerator keygen(*context);
    SecretKey secret_key = keygen.secret_key();
    PublicKey public_key;
    keygen.create_public_key(public_key);
    keygen.create_relin_keys(relin_keys);
    encryptor= new Encryptor(*context, public_key);
    evaluator = new Evaluator(*context);
    decryptor = new Decryptor(*context, secret_key);
    batch_encoder= new BatchEncoder(*context);
    slot_count = batch_encoder->slot_count();
    row_size = slot_count / 2;
    cout << "Plaintext matrix slot count: " << slot_count << endl;
    cout << "Plaintext matrix row size: " << row_size << endl;
}
    
uint64_t keywordToNumber(string data) {
    std::string numericText = "";
        for (size_t i = 0; i < data.length(); i++) {
            numericText += std::to_string(static_cast<int>(data[i]) - 86);
        }
        
    
    const size_t maxKeywordLength = 6;
        const std::string padding = "99";

        if (numericText.length() < 2 * maxKeywordLength) {
            while (numericText.length() < 2 * maxKeywordLength) {
                numericText.append(padding);
            }
        }
    std::cout << "Numeric Text: " << numericText << std::endl;
    
    return stol(numericText);
}
    
vector<Ciphertext> phase1(vector<vector<Ciphertext>> act_encrypted,vector<Ciphertext> row_act_encrypted,vector<Ciphertext> act_rand_encrypted, int m , int n ){
    
    
    int bound=ceil(n/double(poly_modulus_degree));
    vector<Ciphertext> result(bound);
    vector<uint64_t> pod_result;
    Plaintext plain_result;
    for(int j=0;j<bound;j++){
        evaluator->sub(act_encrypted[0][j], row_act_encrypted[j],result[j]);
        evaluator->relinearize_inplace(result[j], relin_keys);
//        cout << "    + Noise budget in encrypted_matrix: " << decryptor->invariant_noise_budget(result[j]) << " bits"<< endl;
//        cout << "after subtraction." << endl;
//        decryptor->decrypt(result[j], plain_result);
//        batch_encoder->decode(plain_result, pod_result);
//        print_matrix(pod_result, row_size);
        evaluator->add_inplace(result[j],act_encrypted[2][j]);
        evaluator->relinearize_inplace(result[j], relin_keys);
//        cout << "    + Noise budget in encrypted_matrix: " << decryptor->invariant_noise_budget(result[j]) << " bits"<< endl;
//        cout << "after addition.t." << endl;
//        decryptor->decrypt(result[j], plain_result);
//        batch_encoder->decode(plain_result, pod_result);
//        print_matrix(pod_result, row_size);
        evaluator->multiply_inplace(result[j],act_rand_encrypted[j]);
        evaluator->relinearize_inplace(result[j], relin_keys);
//        cout << "    + Noise budget in encrypted_matrix: " << decryptor->invariant_noise_budget(result[j]) << " bits"<< endl;
//        cout << "after multiply" << endl;
//        decryptor->decrypt(result[j], plain_result);
//        batch_encoder->decode(plain_result, pod_result);
//        print_matrix(pod_result, row_size);
    }
    return result;
    
}

void printResultAddr(vector<Ciphertext> result, int n){
    int k=0;
    int bound=ceil(n/double(poly_modulus_degree));
    vector<uint64_t> pod_result;
    Plaintext plain_result;
    for(int j=0;j<bound;j++){
        cout << "Decrypt and decode result." << endl;
        decryptor->decrypt(result[j], plain_result);
        batch_encoder->decode(plain_result, pod_result);
        for(int j=0;j<poly_modulus_degree;j++){
            cout<<pod_result[j]<<",";
            start_=pod_result[0];
            end_=start_+pod_result[1];
            k++;
            if(k>=n){return ;}
        }
//        print_matrix(pod_result, row_size);
    }
}

vector<uint64_t> printResultFile(vector<Ciphertext> result, int n){
    int k=0;
    int bound=ceil(n/double(poly_modulus_degree));
    vector<uint64_t> pod_result;
    vector<uint64_t> result_;
    Plaintext plain_result;
    for(int j=0;j<bound;j++){
        decryptor->decrypt(result[j], plain_result);
        batch_encoder->decode(plain_result, pod_result);
        for(int j=0;j<poly_modulus_degree;j++){
            cout<<pod_result[j]<<",";
            start_=pod_result[0];
            end_=start_+pod_result[1];
            result_.push_back(pod_result[j]);
            k++;
//            cout<<"k="<<k<<endl;;
            if(k>=n){return result_;}
        }
//        print_matrix(pod_result, row_size);
    }
    
    
    for(int i=0;i<result_.size();i++)
    {
        cout<<result_[i]<<","<<endl;
    }
    return result_;
}


int printResult(vector<Ciphertext> result, int n){
    int index=-1;
    int bound=ceil(n/double(poly_modulus_degree));
    vector<uint64_t> pod_result;
    Plaintext plain_result;
    int k=0;
    for(int i=0;i<bound;i++){
        print_line(__LINE__);
        cout << "Decrypt and decode result." << endl;
        decryptor->decrypt(result[i], plain_result);
        batch_encoder->decode(plain_result, pod_result);
        for(int j=0;j<poly_modulus_degree;j++){
//            cout<<pod_result[j]<<",";
            if(pod_result[j]==0){
                index=i*poly_modulus_degree+j;
            }
            k++;
            if(k>=n){return index;}
        }
//        print_matrix(pod_result, row_size);
    }
    cout<<endl;
    return index;
}

vector<vector<uint64_t>> readFile(const std::string& filename) {
    
    
    cout<<"reading files"<<endl;
    // To store all lines of the file
    std::vector<std::string> lines;

    std::ifstream file(filename);
    std::string line;

    // Reading all lines
    while (std::getline(file, line)) {
        lines.push_back(line);
    }

    // To store file into 2D vector
    std::vector<std::vector<uint64_t>> result(lines.size());
    int i=0;
    for (const std::string& l : lines) {
        std::vector<uint64_t> row;
        std::stringstream ss(l);
        std::string cell;
        while (std::getline(ss, cell, ',')) {
            row.push_back(std::stol(cell));
        }

        result[i]=row;
        i++;
    }
    
//    for(int i=0;i<result.size();i++){
//        for(int j=0;j<result[i].size();j++)
//        {
//            cout<<result[i][j]<<",";
//        }
//        cout<<endl;
//    }

    return result;
}

std::vector<std::string> readKeys(const std::string& fileName) {
    std::ifstream file(fileName);
    std::vector<std::string> lines;
    std::string line;

    while (std::getline(file, line)) {
        // Assuming '[' only occurs in the first line
        if (!lines.empty())
            line.erase(std::remove(line.begin(), line.end(), '['), line.end());
        lines.push_back(line);
    }

    // To store file into array
    std::string firstLine = lines.front();
    std::vector<std::string> result;
    size_t pos = 0;
    while ((pos = firstLine.find(',')) != std::string::npos) {
        result.push_back(firstLine.substr(0, pos));
        firstLine.erase(0, pos + 1);
    }
    result.push_back(firstLine); // Adding the last element after the last comma
//    for(int i=0;i<result.size();i++){cout<<result[i]<<",";}
//    cout<<endl;
    

    return result;
}


std::vector<vector<uint64_t>> readOptInv(const std::string& filename, int m, int n) {
    // To store all lines of the file
    std::vector<std::string> lines;

    std::ifstream file(filename);
    std::string line;

    // Reading all lines
    while (std::getline(file, line)) {
        lines.push_back(line);
    }

    // To store file into vector
    std::vector<vector<uint64_t>> result(m);
    int i=0,j=0;
    for (const std::string& l : lines) {
        std::stringstream ss(l);
        std::string cell;

        while (std::getline(ss, cell, ',')) {
            if(j==0){
                result[i]=vector<uint64_t>(n);
            }
//            cout<<cell;
               result[i][j]=std::stol(cell);
            j++;
            if(j>=n){
                j=0;
                i++;
            }
        }
    }
    
//    for(int i=0;i<result.size();i++){
//        for(int j=0;j<result[i].size();j++)
//        {
//            cout<<result[i][j]<<",";
//        }
//        cout<<endl;
//    }

    return result;
}


std::vector<uint64_t> fileKeyToActKey(std::vector<uint64_t> data, int keywordCount ) {
    std::vector<uint64_t> result(keywordCount, 0ULL);

    for (int i = 0; i < data.size(); i++) {
            if (data[i] != 0) {
                result[static_cast<int>(data[i]) - 1] = 1;
            }
        }
    
    
    cout<<endl;
    for(int i=0;i<result.size();i++){
            
                cout<<result[i]<<",";
            
    }
    cout<<endl;


    return result;
}


int main(){
    
    int m,n,row,col;
    
    string filename="Desktop/Research/D+/code_data/DocumentSearch_HE/data/cleartext/keywords.txt";
    vector<std::string>keys=readKeys(filename);

    // phase 1
    initialize(8192);
//    vector<vector<uint64_t>> act=initializeArray(m,n);
     filename="Desktop/Research/D+/code_data/DocumentSearch_HE/data/cleartext/act00.txt";
    vector<vector<uint64_t>> act=readFile(filename);
    m=act.size(),n=act[0].size();
    cout<<m<<":"<<n<<endl;
    cout<<"encrypted act"<<endl;
    vector<vector<Ciphertext>> act_encrypted=encrypt(act,  m,n);
////
    int c_time=0,s_time=0,c_time_tot=0,s_time_tot=0;
//
    int index;
    for(int i=0;i<1;i++){
        c_time=0,s_time=0;
        auto start = high_resolution_clock::now();
        string keyword=keys[i];
        cout<<keyword<<endl;
        uint64_t key=keywordToNumber(keyword);
        vector<Ciphertext> row_act_encrypted=encrypt(n,key);
        auto stop = high_resolution_clock::now();
        auto duration = duration_cast<milliseconds>(stop - start);
        c_time+=duration.count();
//        cout << endl<<"Client time: " << duration.count() << " milliseconds" << endl<<endl;

        start = high_resolution_clock::now();
       cout<<"encrypted rand"<<endl;
       vector<uint64_t> rand=initializeArray(n);
       vector<Ciphertext> act_rand_encrypted=encrypt(rand,n);
       vector<Ciphertext> result_1=phase1(act_encrypted,row_act_encrypted,act_rand_encrypted,m,n);
        stop = high_resolution_clock::now();
        duration = duration_cast<milliseconds>(stop - start);
        s_time=duration.count();
       cout << endl<<"Server time: " << s_time << " milliseconds" << endl;

        start = high_resolution_clock::now();
        cout<<endl;
         index=printResult(result_1,n);
        cout<<"index keyword:"<<index<<endl;;
        stop = high_resolution_clock::now();
        duration = duration_cast<milliseconds>(stop - start);
        c_time+=duration.count();
        cout << endl<<"Client time: " << c_time << " milliseconds" << endl<<endl;
        c_time_tot+=c_time;
        s_time_tot+=s_time;
    }

    cout << endl<<"Total Client time: " << (c_time) << " milliseconds" << endl<<endl;
    cout << endl<<" Total Server time: " << (s_time) << " milliseconds" << endl<<endl;



    // ADDR operations

    initialize(8192);
   cout<<"ADDR operation:"<<endl;
    filename="/Desktop/Research/D+/code_data/DocumentSearch_HE/data/cleartext/addr00.txt";
   vector<vector<uint64_t>> addr=readFile(filename);
    m=addr.size(),n=addr[0].size(), row_index=index;
    cout<<m<<":"<<n<<endl;
//   vector<vector<uint64_t>> addr=initializeArray(m,n);
    vector<vector<Ciphertext>> addr_encrypted=encrypt(addr,  m,n);


    c_time=0,s_time=0;
//    initialize(32768);

    // 1/0 vector
     cout<<"row vector"<<endl;
     auto start = high_resolution_clock::now();
     vector<vector<Ciphertext>> row_addr_encrypted=encrypt(m,n,row_index);
     auto stop = high_resolution_clock::now();
     auto duration = duration_cast<milliseconds>(stop - start);
    c_time+=duration.count();

    // dot product
    cout<<"dot pro:"<<endl;
      start = high_resolution_clock::now();
     vector<Ciphertext> result_21=dotProduct(addr_encrypted,row_addr_encrypted, m, n);
      stop = high_resolution_clock::now();
      duration = duration_cast<milliseconds>(stop - start);
    s_time+=duration.count();
//        cout << "Time taken by function: " << duration.count() << " milliseconds" << endl;

    start = high_resolution_clock::now();
    cout<<"Addr result :"<<endl;
    printResultAddr(result_21, n);
    stop = high_resolution_clock::now();
    duration = duration_cast<milliseconds>(stop - start);
    c_time+=duration.count();
//        cout << "Time taken by function: " << duration.count() << " milliseconds" << endl;


    initialize(16384);
    filename="/Desktop/Research/D+/code_data/DocumentSearch_HE/data/cleartext/invertedIndexOpt0.txt";
    m=579,n=58,row_index=start_/n;
    cout<<"strat:"<<start_<<" end:"<<end_<<endl;
    vector<vector<uint64_t>> invertedIndex=readOptInv(filename,m,n);
//    vector<vector<uint64_t>> invertedIndex=initializeArray(m,n);
    vector<vector<Ciphertext>> invertedIndex_encrypted=encrypt(invertedIndex,  m,n);
    cout<<"done1"<<endl;

    // 1/0 row vector
    start = high_resolution_clock::now();
    int start_pos=start_%n,end_pos=(end_-1)%n;
    vector<vector<Ciphertext>> row_inv_encrypted=encrypt(m,n,row_index);
//    // 1/0 col vector
//    vector<uint64_t> col_vec=initializeCol(n);
    cout<<"strat:"<<start_pos<<" end:"<<end_pos<<endl;
    vector<Ciphertext> col_inv_encrypted=encryptColVector(n,start_pos,end_pos);
    cout<<"done2"<<endl;

    vector<uint64_t>  rand=initializeArray(n);
    vector<Ciphertext>  act_rand_encrypted=encrypt(rand,n);
    cout<<"done3"<<endl;
    stop = high_resolution_clock::now();
    duration = duration_cast<milliseconds>(stop - start);

    c_time+=duration.count();

//    // dot product
    start = high_resolution_clock::now();
    vector<Ciphertext> result_22= dotProduct(invertedIndex_encrypted,row_inv_encrypted,col_inv_encrypted,act_rand_encrypted, m,n);
    stop = high_resolution_clock::now();
    duration = duration_cast<milliseconds>(stop - start);
    cout << "Time taken by function: " << duration.count() << " milliseconds" << endl;
    cout<<"done3"<<endl;
    s_time+=duration.count();


    start = high_resolution_clock::now();
    printResultAddr(result_22,n);
    stop = high_resolution_clock::now();
    duration = duration_cast<milliseconds>(stop - start);
    c_time+=duration.count();

    cout << endl<<"Total Client time: " << (c_time) << " milliseconds" << endl<<endl;
        cout << endl<<" Total Server time: " << (s_time) << " milliseconds" << endl<<endl;
    //

    
    // file keyword
    
    initialize(8192);
    c_time=0,s_time=0;
    filename="/Desktop/Research/D+/code_data/DocumentSearch_HE/data/cleartext/fileKeyword0.txt";
    m=101,n=8+539,row_index=0;
//    m=6,n=8+10,row_index=0;
    vector<vector<uint64_t>> fileKeys=readFile(filename);
    vector<vector<Ciphertext>> fileKeys_encrypted=encrypt(fileKeys,  m,n);
    cout<<"done1"<<endl;

    filename="/Desktop/Research/D+/code_data/DocumentSearch_HE/data/cleartext/act00.txt";
   vector<vector<uint64_t>> act_=readFile(filename);
   cout<<"encrypted act"<<endl;
   vector<vector<Ciphertext>> act_encrypted_=encrypt(act_,  act.size(),act[0].size());

    // 1/0 row vector
     start = high_resolution_clock::now();
    vector<vector<Ciphertext>> row_file_encrypted=encrypt(m,n,row_index);
     stop = high_resolution_clock::now();
     duration = duration_cast<milliseconds>(stop - start);
    c_time+=duration.count();

    //dot
    start = high_resolution_clock::now();
   vector<Ciphertext> result_31= dotProduct(fileKeys_encrypted,row_file_encrypted, m,n);
   stop = high_resolution_clock::now();
   duration = duration_cast<milliseconds>(stop - start);
   cout << "Time taken by function: " << duration.count() << " milliseconds" << endl;
   cout<<"done3"<<endl;
   s_time+=duration.count();

    start = high_resolution_clock::now();
    vector<uint64_t> fileKeyowrds= printResultFile(result_31,n);
    vector<uint64_t> actIndex= fileKeyToActKey(fileKeyowrds, n );
    vector<Ciphertext> actIndex_encrypted=encrypt(actIndex,n);
    stop = high_resolution_clock::now();
    duration = duration_cast<milliseconds>(stop - start);
    c_time+=duration.count();

    //dot
    start = high_resolution_clock::now();
    dotProductActKeys(act_encrypted,actIndex_encrypted,n);
    duration = duration_cast<milliseconds>(stop - start);
    cout << "Time taken by function: " << duration.count() << " milliseconds" << endl;
    cout<<"done3"<<endl;
    s_time+=duration.count();

//    initialize(8192);
    filename="/Desktop/Research/D+/code_data/DocumentSearch_HE/data/cleartext/file0.txt";
    m=101,n=19148,row_index=0;
//    m=6,n=550,row_index=0;
    vector<vector<uint64_t>> filesC=readFile(filename);
    vector<vector<Ciphertext>> filesC_encrypted=encrypt(filesC,  m,n);
    cout<<"done1"<<endl;

    // 1/0 row vector
     start = high_resolution_clock::now();
    vector<vector<Ciphertext>> row_fileC_encrypted=encrypt(m,n,row_index);
     stop = high_resolution_clock::now();
     duration = duration_cast<milliseconds>(stop - start);
    c_time+=duration.count();

    //dot
    start = high_resolution_clock::now();
   vector<Ciphertext> result_32= dotProduct(filesC_encrypted,row_fileC_encrypted, m,n);
   stop = high_resolution_clock::now();
   duration = duration_cast<milliseconds>(stop - start);
   cout << "Time taken by function: " << duration.count() << " milliseconds" << endl;
   cout<<"done3"<<endl;
   s_time+=duration.count();

    start = high_resolution_clock::now();
//    cout<<"output here"<<endl;
    vector<uint64_t> fileKeyowrd= printResultFile(result_32,n);

    stop = high_resolution_clock::now();
    duration = duration_cast<milliseconds>(stop - start);
    c_time+=duration.count();
    
    
    cout << endl<<"Total Client time: " << (c_time) << " milliseconds" << endl<<endl;
            cout << endl<<" Total Server time: " << (s_time) << " milliseconds" << endl<<endl;
    return 0;
}
