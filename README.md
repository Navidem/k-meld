# HOW TO INSTALL:


## Build LLVM 
	```sh 
	$ cd llvm-8.0.0 
	$ ./build-llvm.sh 
	```

## Build K-MeLD 
	```sh 
	# Build the analysis pass of analyzer 
	$ cd 	../analyzer 
	$ make 
	# Now, the  binary is located at analyzer/build/lib/ 
	```
 

# Test the installation
	# in analyzer/ directory run the following:
	python kmeld_runner.py -f kzalloc
	# there should be run/kzalloc/missmatchesFound.txt containing two leaks found

# Run K-MeLD on your code
	# place all of your LLVM bitcode files in run/bc_files/
	# run the following command to initializ and perform pre-processing:
	python kmeld_runner.py -i
	# assuming that you want to check the memory leaks for function FOI, run:
	python kmeld_runner.py -f FOI
	# results will be written to run/FOI/missmatchesFound.txt
