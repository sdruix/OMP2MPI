# OMP2MPI

Custom Source-To-Source Compiler + Mercurium Framework installation and configuration for Linux. 

<br />
##Introduction

The presented tool is Source to Source compiles (S2S) based on BSC's [Mercurium Framework](https://pm.bsc.es/mcxx)[1]. Mercurium is a source-to-source compilation infrastructure aimed at fast prototyping and supports C and C++ languages and is mainly used in Nanos environment to implement OpenMP but since it is quite extensible it has been used to implement other programming models or compiler transformations. This framework is used in order to implement our S2S transformation phases, providing us with the Abstract Syntax Tree(AST) as an easy access to the table of symbols. This information is analyzed through our set of tools to parse and translate the original problem to an optimum version of target language.

* **OMP2MPI**[2], automatically generates MPI source code from OpenMP. Allowing that the program exploits non shared-memory architectures such as cluster, or Network-on-Chip based(NoC-based) Multiprocessors-System-onChip (MPSoC). OMP2MPI gives a solution that allow further optimization by an expert that want to achieve better results. Tested set of problems obtains in most of cases with more than 20x of speedup for 64 cores compared to the sequential version and an average speedup over 4x compared to OpenMP.


[1] J. Balart, A. Duran, M. Gonzalez, X. Martorell, E. Ayguade, and J. Labarta. [Nanos mercurium: a research compiler for openmp](http://personals.ac.upc.edu/aduran/papers/2004/mercurium_ewomp04.pdf). In Proceedings of the European Workshop on OpenMP, volume 8, 2004.

[2] Albert Saa-Garriga, David Castells-Rufas, and Jordi Carrabina. 2015. [OMP2MPI: Automatic MPI code generation from OpenMP programs](http://arxiv.org/html/1501.03064). In High Performance Energy Efficient Embedded Systems. ACM.

##Installation

###You will need:
+ flex 2.5.x
+ gperf 3.0.x
+ automake-1.9 (or newer)
+ autoconf-2.59 (or newer)
+ libtool-1.5.22 (or newer)
+ gcc and g++ (4.4)
+ Mercurium

###Installation Instructions:


	1. git clone git://github.com/sdruix/OMP2MPI.git ~/.mcxx
	2. cd ~/.mcxx && autoreconf
	3. ./configure [--prefix=path/to/set] --enable-tl-openmp-profile
  	4. make
  	5. [sudo] make install
  	6. For OMP2MPI execution: omp2mpi [-h] 
  	
##Comments

Pay attention to the installation/configuration process because some questions will be asked. Sometimes easy ones as your Github user/email, sometimes more difficult ones as your root credentials to be able to proceed!

Relative to my work, I'd like to share it with the world under an simple clause: If you use it the least you must choose something from this list.

* Make any constructive comment of my code. I'm here to learn.
* Contribute something to this source code. Updates, fixes, features... Whatever!

Besides that, I hope you are kind enough to reference any your sources whether is my code or a code from a 3rd party! I must to apologize since I know that the source code is not well commented, but all the function names were thought to be meaningful.

