#!/usr/bin/python

import subprocess
import sys
import random
import os

import pattern_match as pm

equal = {}
equal[26] = [26, 65] #kfree, free_perspu
lastFoiUseSet = set()
escapingPaths = set()
wEscaping = True


def getSupp(item):
	return item[1]

def pattern_match(patt, seq):
	if len(patt) > len(seq):
		print "Pattern is longer than input sequence!"
		return False
	index = 0
	for item in seq:
		pattEntry = patt[index]
		if pattEntry in equal:
			lookFor = equal[pattEntry]
		else:
			lookFor = [pattEntry]
		if item in lookFor:
			index += 1
		if index == len(patt):	#this check can go into the above loop?
			return True
	return False


def interleave(fp):
    with open("interleaved.txt", "w") as inter:

        for line in fp:
		idx, seq = line.split("- ")
        	seq = seq.split()
		if idx in escapingPaths:	
			continue
		outSeq = []
		for opID in seq:
			if mapping[opID].startswith("call"):
				if opID == foiID or opID in lastFoiUseSet: #foi or those working on foi as lastUse
					outSeq.append(opID)
			else:
				outSeq.append(opID)
		outLine = " -1 ".join(outSeq) + " -2\n"
	        inter.writelines([outLine])

def fill_lastFoiUseSet():
	with open(wd+"errPathLastFoiCallUseMap.txt", "r") as fl:
		for line in fl:
			ln = line.split("- ")
			if len(ln) > 1:
				fnName = ln[1].strip()
				if fnName == "":
					continue
				fnID = revMap["call "+fnName]
				lastFoiUseSet.add(fnID)

def print_release_support(mined, candMap, re):
    entry = mined[candMap[re]]
    print "release support: " + str(entry[-1])
    

def fill_escapings():
	with open(wd+"escapingInsnErrPaths.txt", "r") as fl:
		for line in fl:
			escapingPaths.add(line.strip())


if len(sys.argv) < 3:
    print "Usage: ./seq-miner-wrapper.py \"support-level\" \"foi\" "
    exit(1)
supp = sys.argv[1]
tmp1 = open("tmp1.txt","w+")

foi = sys.argv[2]

cwd = os.getcwd()
wd = cwd + "/run/" + foi + "/"


#load the mapping
mapping = {}
revMap = {}
with open(wd+"OP_Map_index.txt", "r") as mpFile:
	for line in mpFile:
		entries = line.split()
		idd = entries[0]
		op = " ".join(entries[1:])
		mapping[idd] = op
		revMap[op] = idd

sampled = "sampledErrPaths.txt"
foiID = revMap["call "+foi]



sampled = wd+"errPostPathInsnSeq.txt" #used for normal mining



#use this set to prune any function not working on FOI
fill_lastFoiUseSet()

#use this to reduce the number of paths passed to mining
if wEscaping:
	fill_escapings()

# INTERLEAVE
with open(sampled, "r") as fp: 
	interleave(fp)



# MINING
cmd2 = ["java", "-jar", cwd+"/cloFAST.jar", 
	"interleaved.txt", supp]
print "Running " + " ".join(cmd2)
subprocess.call(cmd2)



mined = []
with open("interleaved"+"-"+supp+".txt", "r") as output:
	for line in output:
		patt, relSupp = line.split(")")
		relSupp = relSupp.split("relativeSupp")[1].split()[0]
		patt = patt.split(",")
		res = []
		for pt in patt:
			res.append(pt.translate(None, ' ({)},'))
		mined.append([res, float(relSupp)])
mined.sort(key = getSupp) 
candPatt = []
candRelease = set()
candMap ={}
print lastFoiUseSet
for mnIdx, mn in enumerate(mined):
	currCandRel = -1
	currM = mn[0]
	if len(currM) < 2: #just foi is in the sig
		continue	
	candPatt.append(currM)
	for c in reversed(currM):
		# if mapping[c] not in ['ret', 'phi']:
		if c in lastFoiUseSet:
			currCandRel = c
			break
	if currCandRel != -1:	
		candMap[currCandRel]  = mnIdx
		candRelease.add(currCandRel)	
  
# print candRelease, lastFoiUseSet
release = candRelease.intersection(lastFoiUseSet)
if len(release) == 0:
	print "No release function found! terminating ..."
	exit() 

foi_id = revMap["call "+foi]
if foi_id in release:
	print "skipping foi from release set!! SHOULD be debugged!"
	release.remove(foi_id)

print "Found releases:"
print release
if wEscaping:
	print "wEscaping is enabled ..."
	matchArg = ["--foi", foi, "--wEscapeMode", "--patt", foiID, revMap["icmp"], list(release)[0], revMap["ret"], "--releases"]
else:
	matchArg = ["--foi", foi, "--patt", foiID, revMap["icmp"], list(release)[0], revMap["ret"], "--releases"]
  
print "+=+=+=+=+="
for re in release:
	if mapping[re] in ["call IS_ERR", "call printk", "call dev_printk"]:
		continue
	matchArg.append(re)
 	print_release_support(mined, candMap, re)
	print mapping[re]
print "+=+=+=+=+="
print matchArg
pm.match(matchArg)
