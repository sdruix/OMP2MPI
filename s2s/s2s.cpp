#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <stdlib.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <dirent.h>
#include <errno.h>
#include <vector>
#include <time.h>
#include <stdio.h>
#include <float.h>
#include <cstdlib>
#include <sys/time.h>
#include <algorithm>
#include <getopt.h>
#include "math.h"
#include <cstring>
#include <locale>
using namespace std;
int _firstExecuted;

class Timer {
    timeval timer[2];

public:

    timeval start() {
        gettimeofday(&this->timer[0], NULL);
        return this->timer[0];
    }

    timeval stop() {
        gettimeofday(&this->timer[1], NULL);
        return this->timer[1];
    }

    int duration() const {
        int secs(this->timer[1].tv_sec - this->timer[0].tv_sec);
        int usecs(this->timer[1].tv_usec - this->timer[0].tv_usec);

        if (usecs < 0) {
            --secs;
            usecs += 1000000;
        }

        return static_cast<int> (secs * 1000 + usecs / 1000.0 + 0.5);
    }
};

void createFolders(string codesFolder, string logFolder, string execFolder) {
    std::stringstream createCodesFolder, createExecFolder, createLogFolder, cleanCodesFolder, cleanExecutablesFolder;
    createCodesFolder << "mkdir " << codesFolder << " > /dev/null";
    system(createCodesFolder.str().c_str());
    createLogFolder << "mkdir " << logFolder << " > /dev/null";
    system(createLogFolder.str().c_str());
    createExecFolder << "mkdir " << codesFolder << "/" << execFolder << " > /dev/null";
    system(createExecFolder.str().c_str());
    cleanCodesFolder << "rm " << codesFolder << "/*.c* ";
    //cout << cleanCodesFolder.str() << endl;
    system(cleanCodesFolder.str().c_str());
    cleanExecutablesFolder << "rm " << codesFolder << "/" << execFolder << "/*.out ";
    //cout << cleanCodesFolder.str() << endl;
    system(cleanExecutablesFolder.str().c_str());
}

void testFile(string filename, string logFolder, int extKind, int step, string logFilename, int energy, int folderTest, int numProcsMin, int numMax, int withNOOMP, string name) {

    std::stringstream checkFile2trans, checkFile2transMP, timeFilePath, logPath;
    Timer tm;
    ofstream csvOut;
    logPath << logFolder << "/";
    timeFilePath << logPath.str() << logFilename;

    if (!step && folderTest == 1) {
        csvOut.open(timeFilePath.str().c_str(), ios::trunc);
        if (energy)
            csvOut << "Version/Measure;Processors Number;Time Expended(ms.); Energy Consumtion(J.); \n";
        else
            csvOut << "Version/Measure;Processors Number;Time Expended(ms.)\n";
    } else {
        csvOut.open(timeFilePath.str().c_str(), ios::app);
    }

    system("clear");

    if (!step) {
        cout << "---------------------------Compiling original file without transforms---------------------------\n";
    } else {
        cout << "---------------------------Compiling transformed file---------------------------\n";
    }
    std::stringstream filename_justOMP, filename_withoutOMP;
    int check;


    ifstream origFile(filename.c_str());
    std::string lineF;
    std::ofstream ompFile, noOmpFile;
    string shortName;
    if (filename.find("/") >= 0 && filename.find("/") < filename.length())
        filename = "." + filename.substr(filename.find_last_of("/"), filename.length());
    if (!extKind) {
        shortName = filename.substr(0, filename.length() - 2);
        filename_justOMP << shortName << "OMP.c";
        filename_withoutOMP << shortName << "noOMP.c";
    } else {
        shortName = filename.substr(0, filename.length() - 4);
        filename_justOMP << shortName << "OMP.cpp";
        filename_withoutOMP << shortName << "noOMP.cpp";
    }

    std::cout << "Generated File OpenMP: " << filename_justOMP.str() << std::endl;
    ompFile.open(filename_justOMP.str().c_str(), std::ios::trunc);
    noOmpFile.open(filename_withoutOMP.str().c_str(), std::ios::trunc);
    while (getline(origFile, lineF)) {
        int finded = 0;
        if (lineF.find("pragma") > 0 && lineF.find("pragma") < lineF.length()) {
            finded = 1;
            if (lineF.find("check") > 0 && lineF.find("check") < lineF.length()) {
                std::cout << "Pragma line detected: " << lineF << std::endl;
                lineF = lineF.substr(0, lineF.find("check"));
                std::cout << "Pragma line detected(mod): " << lineF << std::endl;
            }
            if (lineF.find("fixed") > 0 && lineF.find("fixed") < lineF.length()) {
                std::cout << "Pragma line detected: " << lineF << std::endl;
                lineF = lineF.substr(0, lineF.find("fixed"));
                std::cout << "Pragma line detected(mod): " << lineF << std::endl;
            }
        }
        ompFile << lineF << "\n";
        if (!finded)
            noOmpFile << lineF << "\n";
    }
    ompFile.close();
    noOmpFile.close();
    origFile.close();

    if (!step) {
        std::cout << "With OpenMP...\n";
        if (extKind) {
            checkFile2transMP << "g++ " << filename_justOMP.str().c_str() << "   -fopenmp -lm -o MP.out";
        } else {
            checkFile2transMP << "gcc " << filename_justOMP.str().c_str() << " -std=c99  -fopenmp -lm -o MP.out";
        }
        check = system(checkFile2transMP.str().c_str());
        if (!(check == 0)) {
            cerr << "Error compiling original file (OpenMP): " << filename_justOMP.str() << "\n";
            exit(-1);
        } else {
            cout << "compilation OK\n";
        }
    }
    if (withNOOMP) {
        cout << "Without OpenMP...\n";
        if (extKind) {
            checkFile2trans << "g++ " << filename_withoutOMP.str().c_str() << "  -lm -o noMP.out";
        } else {
            checkFile2trans << "gcc " << filename_withoutOMP.str().c_str() << " -std=c99 -lm -o noMP.out";
        }
        check = system(checkFile2trans.str().c_str());
        if (!(check == 0 || check == 768)) {
            cerr << "Error compiling original file (No OpenMP): " << filename_withoutOMP << "\n";
            exit(-1);
        } else {
            cout << "compilation OK\n";
        }
    }
    cout << "Execute OMP from: " << numProcsMin << " to: " << numMax << endl;
    csvOut.close();
    for (int i = numProcsMin; i <= numMax; i*=2) {
        csvOut.open(timeFilePath.str().c_str(), ios::app);
        stringstream setOMPthreats;
        setOMPthreats << "OMP_NUM_THREADS=" << i;
        putenv((char *) setOMPthreats.str().c_str());
        cout << "Checking the enviroment variable OMP_NUM_THREADS" << endl;
        int thread_qty = std::max(atoi(std::getenv("OMP_NUM_THREADS")), 1);
        if (thread_qty != i) {
            cerr << "ERROR: threads not set to: " << i << " actThreads = " << thread_qty << endl;

        } else {
            cout << "Num threads correctly set to: " << i << endl;
        }

        if (!step) {
            if (i == numProcsMin && withNOOMP)
                csvOut << filename << " Orig without OpenMP;1;";
        } else {
            if (withNOOMP)
                csvOut << filename << " trans without OpenMP;" << i << ";";
        }
        std::cout << "Measuring time..." << std::endl;
        if (i == numProcsMin) {
            if (withNOOMP) {
                std::cout << "Without OpenMP" << std::endl;
                stringstream execCommand;
                execCommand << "./noMP.out >>" << logFolder << "/" << name << "-exec.txt";
                tm.start();
                check = system(execCommand.str().c_str());
                tm.stop();
                if (!(check == 0)) {
                    cerr << "Execution error of file: " << "./noMP.out (" << check << ")" << "\n";
                } else {
                    cout << "execution OK\n";
                }

                csvOut << tm.duration() << ";";



                if (energy) {
                    std::cout << "Measuring ENERGY..." << std::endl;
                    double numexec = (10000 / tm.duration())*10;
                    if (numexec < 1)
                        numexec = 1;
                    std::cout << "Time expeded(" << tm.duration() << ") -> rep: " << numexec << std::endl;
                    std::stringstream energyCommand, csvAux;
                    string line;
                    ofstream codeEnergy;
                    system("touch energy.sh");
                    system("chmod 777 energy.sh");
                    codeEnergy.open("energy.sh", ios::trunc);
                    codeEnergy << "#!/bin/bash\n"
                            << "for run in {1.." << ceil(numexec) << "}; do  " << "./noMP.out;done";
                    codeEnergy.close();
                    energyCommand << "conso-task.sh --res 10 --sum ./energy.sh > " << "temp.txt";
                    check = system(energyCommand.str().c_str());
                    if (check != 0) {
                        cerr << "Error using command: " << energyCommand.str().c_str() << "\n";
                    }
                    ifstream auxCsv("temp.txt");
                    getline(auxCsv, line);
                    getline(auxCsv, line);
                    istringstream linestream(line);
                    string item;
                    string item1;
                    getline(linestream, item, ';');
                    istringstream linestream1(item);
                    getline(linestream, item, ';');
                    istringstream linestream2(item);
                    getline(linestream1, item1, ':');
                    getline(linestream1, item1, ':');
                    item1 = item1.substr(0, item1.find(" J"));
                    csvAux.imbue(std::locale("es_ES.UTF-8"));
                    csvAux << atoi(item1.c_str()) << ";";
                    csvOut << csvAux.str().c_str();
                }
                csvOut << "\n";
                std::cout << "DOne" << std::endl;
            }
        }


        if (!step) {
            cout << "With OpenMP..." << endl;
            csvOut << filename << " with OpenMP;" << i << ";";
            std::cout << "Measuring time..." << std::endl;
            stringstream execCommand;
            execCommand << "./MP.out >>" << logFolder << "/" << name << "-exec.txt";
            tm.start();
            check = system(execCommand.str().c_str());
            tm.stop();
            if (!(check == 0 || check == 768)) {
                cerr << "Execution error of file: " << "./MP.out (" << check << ")" << "\n";
            } else {
                cout << "execution OK\n";
            }

            csvOut << tm.duration() << ";";

            if (energy) {
                std::cout << "Measuring energy..." << std::endl;
                double numexec = (10000 / tm.duration())*10;
                if (numexec < 1)
                    numexec = 1;
                std::stringstream energyCommand2, csvAux;
                string line;
                ofstream codeEnergy;
                std::cout << "Time expeded(" << tm.duration() << ") -> rep: " << numexec << std::endl;
                codeEnergy.open("energy.sh", ios::trunc);
                codeEnergy << "#!/bin/bash\n"
                        << "for run in {1.." << ceil(numexec) << "}; do  " << "./MP.out;done";
                codeEnergy.close();
                energyCommand2 << "conso-task.sh --sum ./energy.sh 10 > " << "temp.txt";
                check = system(energyCommand2.str().c_str());
                if (check != 0) {
                    cerr << "Error using command: " << energyCommand2.str().c_str() << "\n";
                }
                ifstream auxCsv("temp.txt");
                std::cout << "doNE" << std::endl;
                getline(auxCsv, line);
                getline(auxCsv, line);
                istringstream linestream(line);
                string item;
                string item1;
                getline(linestream, item, ';');
                istringstream linestream1(item);
                getline(linestream, item, ';');
                istringstream linestream2(item);
                getline(linestream1, item1, ':');
                getline(linestream1, item1, ':');
                item1 = item1.substr(0, item1.find(" J"));
                csvAux.imbue(std::locale("es_ES.UTF-8"));
                csvAux << atoi(item1.c_str()) << ";";
                csvOut << csvAux.str().c_str();
            }
            csvOut << "\n";
            std::cout << "DOne" << std::endl;
        }
        csvOut.close();
    }

    //    cout<<"OMP: "<<filename_justOMP.str()<<endl;
    //    cout<<"noOMP: "<<filename_withoutOMP.str()<<endl;
    //    cin.get();
    stringstream rmOMPfile;
    rmOMPfile << " rm " << filename_justOMP.str() << endl;
    system(rmOMPfile.str().c_str());

    //    stringstream rmNoOMPfile;
    //    rmNoOMPfile <<" rm "<< filename_withoutOMP.str()<<endl;
    //    system(rmNoOMPfile.str().c_str());
    //    
    //    stringstream rmExecOMP, rmExecNoOMP;
    //    rmExecOMP << "rm ./MP.out";
    //   
    //    system(rmExecOMP.str().c_str());
    //     if(withNOOMP) {
    //        system(rmExecNoOMP.str().c_str());
    //        rmExecNoOMP << "rm ./noMP.out";
    //     }

}

std::string getFileExtension(const std::string& FileName) {
    if (FileName.find_last_of(".") != std::string::npos)
        return FileName.substr(FileName.find_last_of(".") + 1);
    return "";
}

string cleanWhiteSpaces(string toClean) {
    if(!toClean.empty()) {
        while(std::string(toClean).find_first_of(" ")==0){                       
            toClean = std::string(toClean).substr(1,std::string(toClean).length());
        }
        while(std::string(toClean).find_last_of(" ")==std::string(toClean).length()-1){
            toClean = std::string(toClean).substr(0,std::string(toClean).length()-1);
        }
    }
    return toClean;
}

void doPause() {

    cin.get(); //pausa
    cout << "Press Key to Continue...\n";
}

int getdir(string dir, vector<string> &files, int withSubDir) {
    DIR *dp;
    struct dirent *dirp;
    struct stat st;
    if ((dp = opendir(dir.c_str())) == NULL) {
        cout << "Error(" << errno << ") opening " << dir << endl;
        return errno;
    }

    while ((dirp = readdir(dp)) != NULL) {
        string fileName = dir + "/" + string(dirp->d_name);
        if (string(dirp->d_name).compare(".") != 0
                && string(dirp->d_name).compare("..") != 0) {
            lstat(fileName.c_str(), &st);
            cout << "Processing..." << endl;
            if (!S_ISDIR(st.st_mode)) {
                files.push_back(fileName);
                cout << "Found file: " << fileName << endl;
            } else {
                cout << "Found directory: " << fileName << endl;
                if (withSubDir) {
                    cout << "Opening dir: " << string(dirp->d_name) << endl;
                    getdir(fileName, files, withSubDir);
                }
            }
        }
    }
    closedir(dp);

    return 0;
}

void compile(vector<string> files, string cP, string codesDir, string execDir, int pause, int verbose) {
    ofstream compFile;
    int numFiles = 0;

    for (int i = 0; i < (signed)files.size(); i++) {
        if (files[i].length() > 4) {
            string extension = files[i].substr(files[i].length() - 4, files[i].length());
            if (extension == ".cpp") {

                if (numFiles > 0) {
                    compFile.open(cP.c_str(), ios::app);
                } else {
                    compFile.open(cP.c_str(), ios::trunc);
                }
                cout << "------------------------------------------------\n";
                cout << "Compiling " << files[i] << endl;
                compFile << "---------------------------Compiling " << files[i]
                        << "-------------------------" << "\n" << endl;
                compFile.close();
                std::stringstream complilationCommand, complilationCommandV;
                string name = files[i].substr(0, files[i].length() - 4);
                name = name.substr(name.find_last_of("/") + 1, name.length());
                complilationCommand << "mpic++ -fopenmp -lm -o ./"
                        << codesDir << "/" << execDir
                        << "/" << name << ".out ./"
                        << files[i]
                        << " 2>> " << cP << "\n";
                int check = system(complilationCommand.str().c_str());
                if (!(check == 0 || check == 256)) {
                    cerr << "Error using command: " << complilationCommand.str().c_str() << "\n";
                    exit(-1);
                    cerr << "------------------------------------------------\n";
                }
                cout << "------------------------------------------------\n";
                if (verbose) {
                    complilationCommand << "mpic++  -fopenmp -lm -o ./"
                            << codesDir << "/" << execDir
                            << "/" << name << ".out ./"
                            << files[i] << "\n";
                    system(complilationCommandV.str().c_str());
                }

            }
            extension = files[i].substr(files[i].length() - 2, files[i].length());
            if (extension == ".c") {

                if (numFiles > 0) {
                    compFile.open(cP.c_str(), ios::app);
                } else {
                    compFile.open(cP.c_str(), ios::trunc);
                }
                cout << "------------------------------------------------\n";
                cout << "Compiling " << files[i] << endl;
                compFile << "---------------------------Compiling " << files[i]
                        << "-------------------------" << "\n" << endl;
                compFile.close();
                std::stringstream complilationCommand, complilationCommandV;
                string name = files[i].substr(0, files[i].length() - 2);
                name = name.substr(name.find_last_of("/") + 1, name.length());
                complilationCommand << "mpicc -std=c99 -fopenmp -lm -o ./"
                        << codesDir << "/" << execDir
                        << "/" << name << ".out " << files[i]
                        << " 2>> " << cP << "\n";
                int check = system(complilationCommand.str().c_str());
                if (!(check == 0 || check == 256)) {
                    cerr << "Error using command: " << complilationCommand.str().c_str() << "\n";
                    exit(-1);
                    cerr << "------------------------------------------------\n";
                }
                cout << "------------------------------------------------\n";
                if (verbose) {
                    complilationCommand << "mpicc -std=c99 -fopenmp -lm -o ./"
                            << codesDir << "/" << execDir
                            << "/" << name << ".out " << files[i] << "\n";
                    system(complilationCommandV.str().c_str());
                }


            }
            numFiles++;
        }

    }
    if (numFiles <= 0) {
        cerr << "------------------------------------------------\n";
        cerr << "No *.cpp or *.c files in folder: " << codesDir << "\n" << endl;
        cerr << "------------------------------------------------\n";
        exit(-1);
    }

}

void execute(vector<string> files, string csvP, string errP, string codesDir, string execDir, int rep, int tries, int pause, int energy, int numProcs, string executeInstrucction) {
    std::cout.imbue(std::locale("es_ES.UTF-8"));
    int numFiles = 0;
    Timer tm;
    ofstream csvOut, execErrorsFile;


    ifstream inFile(csvP.c_str());
    string line;
    std::stringstream cpuTimes;


    int n = std::count(std::istreambuf_iterator<char>(inFile), std::istreambuf_iterator<char>(), '\n') + 1;
    ifstream inFile2(csvP.c_str());
    string legend = "Version/Measure";
    cout << "Analizing log file..." << endl;
    if (n > 1) {
        for (int nL = 0; nL < n; ++nL) {

            getline(inFile2, line);
            // cout<<line<<endl;

            istringstream linestream(line);
            string item;
            getline(linestream, item, ';');
            //            cout<<"Analizing line : "<<line<< "("<<item<<")"<<endl;
            if (nL >= 1 && item.find("OpenMP") >= 0 && item.find("OpenMP") < item.length()) {
                //                cout<<"OpenMP test line line detected"<<endl;
                cpuTimes << line << "\n";
            } else if (nL == 0) {
                cpuTimes << line << "\n";
            } else {
                getline(linestream, item, ';');
                if (atoi(item.c_str()) < numProcs)
                    cpuTimes << line;
            }
        }
    } else {
        //        cout<<"Not OpenMP test Detected"<<endl;
        if (energy) {
            cpuTimes << "Version/Measure;NumProcs;Time Expended(ms.); Energy Consumtion(J.); \n";
        } else {
            cpuTimes << "Version/Measure;NumProcs;Time Expended(ms.); \n";
        }
    }
    cout << "Final times: \n" << cpuTimes.str() << endl;
    //cin.get();
    if (_firstExecuted) {
        csvOut.open(csvP.c_str(), ios::trunc);
        csvOut << cpuTimes.str();
        csvOut.close();
        _firstExecuted = 0;
    }

    double cpu_time_used;

    for (unsigned int i = 0; i < files.size(); i++) {

        if (files[i].length() > 4) {
            string extension = files[i].substr(files[i].length() - 4, files[i].length());
            if (extension == ".out") {

                numFiles++;
                csvOut.open(csvP.c_str(), ios::app);

                execErrorsFile.open(errP.c_str(), ios::app);

                cout << "------------------------------------------------\n";
                cout << "Executing (" << codesDir << ") " << files[i] << endl;
                csvOut << files[i]
                        << ";";
                //Create signature
                //csvOut << createSignature(files[i]);
                csvOut << numProcs << ";";
                execErrorsFile << "---------------------------Executing (" << codesDir << ") " << files[i]
                        << "-------------------------" << endl;
                csvOut.close();
                execErrorsFile.close();
                std::stringstream executeCommand, energyCommand, executeErrorsCommand;
                executeCommand << executeInstrucction << " -np " << numProcs << " " << files[i] << " --run  >> " << errP;
                executeErrorsCommand << executeInstrucction << " -np " << numProcs << " " << files[i] << " --run  2>> " << errP;
                cpu_time_used = 0;

                int failed = 0, totalFail = 0;
                for (int it = 0; it < rep; ++it) {
                    cout << "*Repetition(Time): " << it + 1 << "*\n" << endl;
                    double minimumTime = DBL_MAX;
                    int it1 = 0;
                    for (it1 = 0; it1 < tries; ++it1) {
                        if (tries > 0)
                            cout << it1 << "...";
                        tm.start();
                        int check = system(executeCommand.str().c_str());
                        std::cout << "C1: " << check << "\n";
                        if (check != 0 && check != 256 && check != 768) {
                            failed++;
                            cerr << "Error using command: " << executeCommand.str().c_str() << "\n";
                            exit(-1);
                            cerr << "------------------------------------------------\n";
                        }
                        tm.stop();

                        if (tm.duration() < minimumTime) {
                            minimumTime = (double) tm.duration();
                        }
                        if (tries > 0)
                            cout << "\n" << endl;
                    }
                    if (failed == tries) {
                        totalFail++;
                    }
                    if (failed != it1) {
                        cpu_time_used += minimumTime;
                    }
                    failed = 0;
                }

                execErrorsFile.open(errP.c_str(), ios::app);
                execErrorsFile << system(executeErrorsCommand.str().c_str());
                execErrorsFile.close();
                double exec = cpu_time_used / (rep - totalFail);
                //cout<<"DTIM: "<< exec<<endl;
                csvOut.imbue(std::locale("es_ES.UTF-8"));
                csvOut.open(csvP.c_str(), ios::app);
                csvOut << exec << ";";
                if (energy) {
                    double numexec = (10000 / exec)*10;
                    ofstream codeEnergy;
                    system("touch energy.sh");
                    system("chmod 777 energy.sh");
                    codeEnergy.open("energy.sh", ios::trunc);
                    codeEnergy << "#!/bin/bash\n"
                            << "for run in {1.." << ceil(numexec) << "}; do  " << executeInstrucction << " ./"
                            << codesDir << "/" << execDir
                            << "/" << files[i] << ";done";
                    codeEnergy.close();
                    energyCommand << "conso-task.sh --res 10 --sum ./energy.sh > " << "temp.txt";
                    cout << "Measuring energy: " << "1.." << ceil(numexec) << endl;
                    std::stringstream energyString;
                    double totalE = 0.0;
                    // cout<<"NEE: "<<ceil(numexec)<<endl;
                    // cin.get();
                    failed = 0;
                    for (int it = 0; it < rep; ++it) {
                        cout << "*Repetition(Energy): " << it + 1 << "*\n" << endl;
                        int check = system(energyCommand.str().c_str());
                        std::cout << "C2: " << check << "\n";
                        if (check != 0) {
                            failed++;
                            cerr << "Error using command: " << energyCommand.str().c_str() << "\n";
                            exit(-1);
                            //                    cerr << "------------------------------------------------\n";
                        }
                        cout << "------------------------------------------------\n";

                        ifstream auxCsv("temp.txt");

                        getline(auxCsv, line);
                        getline(auxCsv, line);
                        istringstream linestream(line);
                        string item;
                        string item1;
                        getline(linestream, item, ';');
                        istringstream linestream1(item);
                        getline(linestream, item, ';');
                        istringstream linestream2(item);
                        getline(linestream1, item1, ':');
                        getline(linestream1, item1, ':');
                        item1 = item1.substr(0, item1.find(" J"));

                        totalE += atoi(item1.c_str());
                        cout << "E: " << atoi(item1.c_str()) << endl;
                    }
                    energyString.imbue(std::locale("es_ES.UTF-8"));
                    energyString << totalE / (rep - failed) / ceil(numexec);
                    cout << "To write: " << energyString.str() << endl;
                    //cin.get();
                    //csvOut.open(csvP.c_str(), ios::app);
                    csvOut << energyString.str().c_str() << ";";

                }
                csvOut << "\n";
                csvOut.close();
            }
        }
    }
    if (numFiles <= 0) {
        cerr << "------------------------------------------------\n";
        cerr << "No *.out files in folder: " << codesDir << "/" << execDir << "\n" << endl;
        cerr << "------------------------------------------------\n";
    }


}

inline bool exists(const std::string& name) {
    return ( access(name.c_str(), F_OK) != -1);
}

int main(int argc, char *argv[]) {

    int rep = 1, tries = 1, checkOri = 0, energy = 0, verbose = 0, pause = 0, toDo = 3, numProcsMin = 2, numProcsMax = 2, withSubdir = 0, scalability = 0;
    string filename, execFolder, codesFolder, logFolder, logFilename, fileFolder, executeCommand;
    vector<string> filesToTransform = vector<string > ();
    filename = "";
    fileFolder = "";
    codesFolder = "codes";
    execFolder = "executables";
    executeCommand = "mpirun";
    logFolder = "log";
    logFilename = "log.csv";
    int nextOption; // return value of getopt
    int withNOOMP = 0;
    int folderTest = 0;
    while ((nextOption = getopt(argc, argv, "r:t:f:F:c:e:n:N:l:E:oOhHivL:xp01234ws")) != -1) {
        switch (nextOption) {
            case 'r':
                rep = atoi(optarg);
                break;
            case 't':
                tries = atoi(optarg);
                break;
            case 'n':
                numProcsMin = atoi(optarg);
                if (numProcsMax < numProcsMin)
                    numProcsMax = numProcsMin;
                break;
            case 'N':
                numProcsMax = atoi(optarg);
                break;
            case 'o':
                checkOri = 1;
                folderTest = 0;
                break;
            case 'O':
                checkOri = 1;
                scalability = 1;
                folderTest = 0;
                break;
            case 'f':
                filename = optarg;
                break;
            case 'F':
                fileFolder = optarg;
                break;
            case 'w':
                withSubdir = 1;
                break;
            case 'c':
                codesFolder = optarg;
                break;
            case 'e':
                execFolder = optarg;
                break;
            case 'E':
                executeCommand = optarg;
                break;
            case 'p':
                pause = 1;
                break;
            case 's':
                withNOOMP = 1;
                break;
            case 'l':
                logFolder = optarg;
                break;
            case 'L':
                logFilename = optarg;
                break;
            case 'x':
                energy = 1;
                break;
            case 'v':
                verbose = 1;
                break;
            case '0':
                toDo = 0;
                break;
            case '1':
                toDo = 1;
                break;
            case '2':
                toDo = 2;
                break;
            case '3':
                toDo = 3;
                break;
            case '4':
                toDo = 4;
                break;
            case 'H':
            case 'h':
                cout << argv[0] << " [-[0|1|2|3|4]][-o][-i][-p][-x][-f[name]][-F[name] -w][-c[name]][-e[name]][-l[name]][-L[name]][-c[name]][-e[name]][-r[number]][-t[number]]\n"
                        " -0 Transform\n"
                        " -1 Compile preTranslated Versions\n"
                        " -2 Execute preCompiled Versions\n"
                        " -3 Transform & Compile & Execute\n"
                        " -4 Compile & Execute preTransformed Files\n"
                        " -o Check (Compile and Execute original file)\n"
                        " -O Check (Compile and Execute original file OpenMP) form scalability chart\n"
                        " -s Check (Compile and Execute original file NoOpenMP) form scalability chart\n"
                        " -f <filename to convert>\n"
                        " -F <folder of files to convert>\n"
                        " -w Transform files in subdirectory of file folder\n"
                        " -c <output subfolder for transformed codes(default: 'codes')>\n"
                        " -e <output subfolder for executables (default: 'executables')>\n"
                        " -E <specify a custom comand to execute generated files (default: 'mpirun')>\n"
                        " -l <output subfolder for log files (default: 'log')>\n"
                        " -L <output filename for log files (default: 'log.csv')>\n"
                        " -r <number of code executions to extract average>\n"
                        " -t <number of tries for each execution repetition to get just the best execution time>\n"
                        " -n <number of minumum processors to evaluate in execution>\n"
                        " -N <number of maximum processors to evaluate in execution>\n"
                        " -p Pause after each processed file\n"
                        " -x Report energy. \n"
                        " -v --verbose St0 Verbose MPI compilation errors(on/off)\n"
                        " -[h|H] --help Display this usage information. \n" << endl;
                exit(0);
                break;
            default:
                cerr << argv[0] << " [-[0|1|2|3|4]][-o][-i][-p][-x][-f[name]][-F[name] -w][-c[name]][-e[name]][-l[name]][-L[name]][-c[name]][-e[name]][-r[number]][-t[number]]\n"
                        " -0 Transform\n"
                        " -1 Compile preTranslated Versions\n"
                        " -2 Execute preCompiled Versions\n"
                        " -3 Transform & Compile & Execute\n"
                        " -4 Compile & Execute preTransformed Files\n"
                        " -o Check (Compile and Execute original file OpenMP/NoOpenMP)\n"
                        " -O Check (Compile and Execute original file OpenMP/NoOpenMP) form scalability chart\n"
                        " -s Check (Compile and Execute original file NoOpenMP) form scalability chart\n"
                        " -f <filename to convert>\n"
                        " -F <folder of files to convert>\n"
                        " -w Transform files in subdirectory of file folder\n"
                        " -c <output subfolder for transformed codes(default: 'codes')>\n"
                        " -e <output subfolder for executables (default: 'executables')>\n"
                        " -E <specify a custom comand to execute generated files (default: 'mpirun')>\n"
                        " -l <output subfolder for log files (default: 'log')>\n"
                        " -L <output filename for log files (default: 'log.csv')>\n"
                        " -r <number of code executions to extract average>\n"
                        " -t <number of tries for each execution repetition to get just the best execution time>\n"
                        " -n <number of minumum processors to evaluate in execution>\n"
                        " -N <number of maximum processors to evaluate in execution>\n"
                        " -p Pause after each processed file\n"
                        " -x Report energy. \n"
                        " -v --verbose St0 Verbose MPI compilation errors(on/off)\n"
                        " -[h|H] --help Display this usage information. \n" << endl;
                exit(0);

        }

    }
    if (toDo == 0 || toDo == 3)
        createFolders(codesFolder, logFolder, execFolder);

    if (fileFolder.compare("") != 0) {
        cout << "Getting Folder: " << fileFolder << endl;
        getdir(fileFolder, filesToTransform, withSubdir);
    } else {
        if (filename.compare("") == 0 && (toDo == 0 || toDo == 3)) {
            cerr << "You Must to Specify the file or a folder of files to transform:" << endl;
            cerr << "-f <filename to convert>" << endl;
            cerr << "-F <folder of files to convert>" << endl;
            exit(-1);
        }
        filesToTransform.push_back(filename);
    }

    string logFilenameBack = logFilename;
    for (unsigned int numF = 0; numF < filesToTransform.size(); ++numF) {

        filename = filesToTransform[numF];

        if (!exists(filename.c_str())) {
            cerr << "The filename specified does not exist" << endl;
            exit(-1);
        }

        string name;
        int error = 0;
        if (filename.find_last_of("/") >= 0 && filename.find_last_of("/") < filename.length())
            name = filename.substr(filename.find_last_of("/"), filename.length());
        else
            name = filename;

        int extKind = 0;
        string extension = getFileExtension(filename);
        if (extension.compare("c") == 0) {
            extKind = 0;
            name = name.substr(0, name.length() - 2) + "MPI";
        } else if (extension.compare("cpp") == 0) {
            extKind = 1;
            name = name.substr(0, name.length() - 4) + "MPI";
        } else {
            cout << filename << " is not a supported file\n";
            //  cout << "Just allowed .c and .cpp files\n";
            error = 1;
        }

        if (!error) {
            stringstream tempLogName;
            tempLogName << name << "-" << logFilenameBack;
            logFilename = tempLogName.str();
            cout << "Starting transformation of file: " << filename << endl;
            string line, firstLine;
            ifstream preprocessFile(filename);
            int found = 0;
            string includeS = "#include";
            vector<string> includeVector;
            includeVector.push_back("#include <mpi.h>");
            includeVector.push_back("#include <stdlib.h>");
            while (getline(preprocessFile, line) && !found) {

                // line = cleanWhiteSpaces(line);

                string subline = line.substr(0, includeS.length());
                string subsubline = line.substr(0, 2);
                string firstChar = line.substr(0, 1);
                if (subline.compare(includeS) == 0) {
                    //Avoid inlude mpi duplicated
                    if (line.find("mpi.h") < 0 || line.find("mpi.h") > line.length()) {
                        includeVector.push_back(line);
                        //cout<<"Not found in "<< line <<" ("<<line.find_first_of("mpi.h")<<")"<< endl;
                    }
                }

                if (subline.compare(includeS) != 0 && line.compare("") != 0
                        && subsubline.compare("//") != 0
                        && subsubline.compare("/*") != 0
                        && firstChar.compare("#") != 0) {
                    if (line.find_first_of("[") >= 0 && line.find_first_of("[") < line.size())
                        line = line.substr(0, line.find_first_of("[") + 1);
                    firstLine = line;
                    found = 1;
                }
            }

            preprocessFile.close();
            std::stringstream mergeToAddMPI, deleteTempFile, createTempFile;
            string tempName;
            if (extKind)
                tempName = "temp.cpp";
            else
                tempName = "temp.c";
            createTempFile << "echo \"#include <mpi.h>\" >" << tempName;

            system(createTempFile.str().c_str());



            int check;

            mergeToAddMPI << "cat " << filename << " >> " << tempName;
            check = system(mergeToAddMPI.str().c_str());
            if (!(check == 0 || check == 256)) {
                cerr << "Error using command: " << mergeToAddMPI.str().c_str() << "\n";
                exit(-1);
                cerr << "------------------------------------------------\n";
            }

            if (checkOri && toDo != 0 && toDo != 1) {
                if (scalability)
                    testFile(filename, logFolder, extKind, 0, logFilename, energy, 1, numProcsMin, numProcsMax, withNOOMP, name);
                else
                    testFile(filename, logFolder, extKind, 0, logFilename, energy, 1, numProcsMax, numProcsMax, withNOOMP, name);
            }


            std::stringstream nameF, nameOUT, commandOUT;
            if (extKind) {
                nameOUT << codesFolder << "/" << name << ".cpp";
                commandOUT << "trans-phasec++ -y " << tempName << " -o " << nameOUT.str() << "  -I/usr/lib/openmpi/include/ " << std::endl;
            } else {
                nameOUT << codesFolder << "/" << name << ".c";
                commandOUT << "trans-phasecc -y " << tempName << " -o " << nameOUT.str() << " -std=c99 -I/usr/lib/openmpi/include/ " << std::endl;
            }
            if (toDo == 0 || toDo == 3) {



                cout << commandOUT.str() << endl;
                commandOUT << " > /dev/null";
                //std::cin.get();
                check = system(commandOUT.str().c_str());
                if (!(check == 0 || check == 256)) {
                    cerr << "Error using command: " << commandOUT.str().c_str() << "\n";
                    exit(-1);
                    cerr << "------------------------------------------------\n";
                }
                cout << "------------------------------------------------\n";

                ifstream postprocessFile(nameOUT.str());
                found = 0;
                //cout <<"FL: "<< firstLine << endl;
                //cin.get();
                int lines = 0;
                while (getline(postprocessFile, line)) {
                    if (line.find(firstLine) == 0 || found) {
                        includeVector.push_back(line);
                        found = 1;
                        lines++;
                        //cout<< line<<endl;
                    }

                }
                postprocessFile.close();


                //                deleteTempFile << " rm "<<tempName.c_str();
                //                check = system(deleteTempFile.str().c_str());
                //                if (!(check == 0 || check == 256)) {
                //                    cerr << "Error using command: " << deleteTempFile.str().c_str() << "\n";
                //                    exit(-1);
                //                    cerr << "------------------------------------------------\n";
                //                }
                ofstream transFile;
                transFile.open(nameOUT.str(), ios::trunc);

                for (unsigned int incN = 0; incN < includeVector.size(); ++incN) {
                    transFile << includeVector[incN] << "\n";
                    lines++;
                }
                transFile.close();
                if (lines == 0) {
                    stringstream rmFile;
                    rmFile << "rm " << nameOUT.str();
                    system(rmFile.str().c_str());
                }

            }
            vector<string> files = vector<string > ();
            if (toDo == 1 || toDo == 3 || toDo == 4) {
                std::stringstream compFilePath;
                //getdir(codesFolder, files, 0);
                if (exists(nameOUT.str().c_str())) {
                    files.push_back(nameOUT.str());
                    compFilePath << logFolder << "/compilation.txt";
                    string cP = compFilePath.str();

                    compile(files, cP, codesFolder, execFolder, pause, verbose);
                }
            }
            files.clear();
            if (toDo == 2 || toDo == 3 || toDo == 4) {
                std::stringstream csvFilePath, execErrorsPath, execF;
                execF << codesFolder << "/" << execFolder;
                //getdir(execF.str().c_str(), files, 0);
                stringstream nameExec;
                nameExec << codesFolder << "/" << execFolder << "/" << name << ".out";
                //                cout<< nameExec.str()<<endl;
                //                cin.get();
                if (exists(nameExec.str().c_str())) {
                    files.push_back(nameExec.str());
                    csvFilePath << logFolder << "/" << logFilename;
                    execErrorsPath << logFolder << "/" << name << "-execErrors.txt";

                    string csvFP = csvFilePath.str();
                    string errP = execErrorsPath.str();
                    _firstExecuted = 1;
                    for (int n = numProcsMin; n <= numProcsMax; n *= 2) {
                        cout << "Executing using " << n << " processors" << endl;
                        execute(files, csvFP, errP, codesFolder, execFolder, rep, tries, pause, energy, n, executeCommand);
                    }

                }
            }
            files.clear();
            //            stringstream rmCodes, rmExec;
            //            rmCodes <<"rm "<<nameOUT.str();
            //            cout<< rmCodes.str()<<endl;
            //            rmExec << "rm "<< codesFolder <<"/"<< execFolder <<"/*.out";
            //            cout<< rmExec.str()<<endl;
            //            system(rmCodes.str().c_str());
            //            system(rmExec.str().c_str());
            //cin.get();
        }


    }


    return 0;
}


