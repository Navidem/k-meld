#!/usr/bin/python

import sys, getopt
import subprocess
import os


def prepare_bc_list():
    global wd
    bc_dir = wd+"bc_files"
    with open(wd+"bc.list", "w") as fl:
        for _, _, filenames in os.walk(bc_dir):
            # dirpath, dirnames, filenames
            for bc in filenames:
                fl.writelines(wd+"bc_files/"+bc+"\n")


def run_initials():
    cmd1 = ["./build/lib/k-meld", "-call-graph"]
    ret1 = subprocess.call(cmd1)
    if ret1 == 0:
        print "## init finished, now you can run on your chosen FOI"

def prepare_foi_file(FOI):
    global wd
    with open(wd+"foi.txt", "w") as fl:
        fl.writelines("%s"%FOI)


def run_analysis(FOI):
    cmd1 = ["./build/lib/k-meld", "-ownership-analysis"]
    cmd2 = ["./seq-miner-wrapper.py", "0.6", FOI]
    ret1 = subprocess.call(cmd1)
    ret2 = subprocess.call(cmd2)
    if ret1 == 0 and ret2 == 0:
        print "## Check the results in run/"+FOI+"/missmatchesFound.txt"

def process_args(argv):
    global init, FOI
    try:
        opts, args = getopt.getopt(argv,"hif:",["init","foi="])
    except getopt.GetoptError:
        print 'kmeld_runner.py -i | -f FOI'
        sys.exit(1)
    for opt, arg in opts:
        if opt == '-h':
            print 'kmeld_runner.py -i | -f FOI'
            sys.exit()
        elif opt in ("-i", "--init"):
            init = True
        elif opt in ("-f", "--foi"):
            FOI = arg



wd = ""
FOI = ""
init = False
if __name__ == "__main__":
    process_args(sys.argv[1:])
    
    wd = os.getcwd()
    wd += "/run/"    
    
    prepare_bc_list()
    if init:
        run_initials()
    elif FOI != "":
        prepare_foi_file(FOI)
        run_analysis(FOI)
    else:
        print "argv parse error!"    
