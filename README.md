# Access Control for Information-Theoretically Secure Data

This repository includes the implementation of the DocStar framework.

<b> NOTICE:</b> This is an academic proof-of-concept prototype and has not received careful code review. This implementation is NOT ready for production use.

<img width="1920" height="509" alt="fig_arch" src="https://github.com/user-attachments/assets/c3162648-ee50-46b3-b0f3-8543e2043719" />


### Dependencies
To build DocStar, one needs to install:
* Java (openjdk version "19" has been used for testing)

### Setup
#### To run locally
We have created a sample data for 500k files and 5k keywords. The shares and the cleartext files for all data structures are stored in the 'Data/' folder. Copy the '/share' and '/cleartext' folders into the '/data' of '/code/DocumentSearch.' To execute document search using the optimized inverted index, run commands within the '/code/DocumentSearch' folder as below:

Compile:
```
javac src/opt/Server.java
javac -Xlint src/opt/Client.java
javac utility/Helper.java
```

Execute each of these commands in separate terminals:
```
java src/opt/Server.java 1
java src/opt/Server.java 2
java src/opt/Server.java 3
java src/opt/Server.java 4
```


Once all the servers are up (say, "Server is listening"), execute the following command:
```
java src/opt/Client.java
```

Upon execution of 'Client.java,' the user will be prompted to enter the client ID and search keyword. These parameters will be used to retrieve the document the client ID has access to and contains the keyword. 

Results of the document search will be written in files saved under the 'result/' folder.

One can also change the configuration parameters to run the programs on different numbers of threads, file count, keyword count, etc., by modifying the '/config/Common.properties' file

#### To run on AWS machines
We assume the users are aware of the process of creating an EC2 instance on AWS. Upon creation of five AWS machines, similar to running the program on the local machine, prepare AWS machines with required dependencies. Set the `port` and `host_ip` for each AWS server in the '/config/Common.properties' file. Copy the share of a respective server into their '/data/share' folder. Similar to the compile and execute step above, execute the algorithm to search for a document with a keyword.

## To perform fully homomorphic encryption(FHE) based search
### Dependencies
To build, one needs to install the following:
* Microsoft Seal (4.1) (https://github.com/microsoft/SEAL)
* C++ 
* Cmake

### Setup
For the same share data, execute below to perform FHE based operation :
```
cmake -S . -B build
cd build
make or make install
```

Within the program, the user can input the search keyword to fetch the documents containing the keyword.

