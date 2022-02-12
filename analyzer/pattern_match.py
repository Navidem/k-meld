#!/usr/bin/python

import sys
import subprocess
import os
import collections

releaseSetDic = {}
cs_map = {}
cs_string_map = {} 
rev_cs_string_map = {}
ret_map = {}
op_map = {}
op_map_rev = {}
matched = {}
supp = "0.6"
finalMiss = []
pathLastCall = {}
calleesMap = {}
callGraphMapIndex = {}
callGraphMap = []
loopOverFoi = set()
condRelease = set()
succConditionalConsume = set()
escapingPaths = set()
afterEscapePathsIds = set()
afterEscapePaths = []
afterEscapePathsIdsMap = {}
afterEscapePathsMap = collections.defaultdict(list) #map from escapee funcs to its paths
escapeePairsMap = collections.defaultdict(list) #map from escapee funcs to its pairs
foi_startMap = {}
consumerSet = set()
release_id = ""
main_release = ""
found = set()
foundDirty = set()
foundMissingLast = []
lastCallCheckSide = {}
line_offset = []
wEscapeMode = False
consumeEnabled = True

def storeFound(idx, dirty):
	if dirty:
		foundDirty.add(idx)
	if dirty != True:
		found.add(idx)



def check_callees_against_release(toCheckCall, visited):
	visited.add(toCheckCall)
	if len(visited) > 3: 
		return False
	clLineIndex = callGraphMapIndex[toCheckCall]

	entry = callGraphMap[int(clLineIndex) + 1]
	callees = entry.split()

	for cl in callees:
		if "call "+cl in op_map_rev.keys():
			look = op_map_rev["call "+cl]
			if look in releaseSetDic[release_id]:
				return True
        if len(callees) > 5:    #such function is not a release wrapper! So don't process it!
            return False

	for cl in callees:	
		if (cl in callGraphMapIndex.keys()) and  (cl not in visited):
			if check_callees_against_release(cl, visited):
				return True
			visited.pop()
	return False

def fill_loop():
	with open(wd+"loopFoiInsnPaths.txt", "r") as fl:
		for line in fl:
			loopOverFoi.add(line.strip())

def fill_conditionalReleases():
	with open(wd+"conditionalReleasePaths.txt", "r") as fl:
		for line in fl:
			condRelease.add(line.strip())

def fill_escapings():
	with open(wd+"escapingInsnErrPaths.txt", "r") as fl:
		for line in fl:
			escapingPaths.add(line.strip())
	try:
		with open(wd+"escErrPostPathInsnSeq.txt", "r") as fl: #paths collected by working on escaping pointers
			for line in fl:
				pId, p = line.split("-")
				afterEscapePathsIds.add(pId)
				afterEscapePaths.append(line.strip())
				afterEscapePathsIdsMap[pId] = p.strip()
	except:
		print "No escErrPostPathInsnSeq.txt exists!"
	try:
		with open(wd+"escapedPathsFoiStarts.txt", 'r') as fl:
			for line in fl:
				pId, rest = line.split(":")
				foi_startMap[pId] = rest.strip()
				escapee = rest.split()[0]
				afterEscapePathsMap[escapee].append(pId) #map from escapee func to the paths starting from it
	except:
		print "No escapedPathsFoiStarts.txt exists!"

def fill_calleesMap():
	with open(os.getcwd()+"/run/calleesFoiLastUseMap.txt", "r") as fl:
		for line in fl:
			k, v = line.split(":")
			mapEntry = collections.defaultdict(list)
			for elm in v.split():
				elm = elm.strip()
				fn, pth = elm.split("|")
				if pth == "+":
					mapEntry['+'].append(fn)
				elif pth == "N":
					mapEntry['norm'].append(fn)
				elif pth == "E":
					mapEntry['err'].append(fn)
				else:
					print "INVALID path indicator incalleesFoiLastUseMap.txt"
					exit(1)
			calleesMap[k] = mapEntry


def fill_callGraphMapIndex():
	with open(os.getcwd()+"/run/callGraphFileIndex.txt", "r") as fl:
		for line in fl:
			fnName, lnNum = line.split()
			callGraphMapIndex[fnName] = lnNum
def fill_lineOffset():
	global callGraphMap
	offset = 0
	with open(os.getcwd()+"/run/callGraphMap.txt", "r") as fl:
		callGraphMap = fl.readlines()
		# for line in callGraphMap:
		# 	line_offset.append(offset)
		# 	offset += len(line)

def fill_pathLastCalls():
	with open(wd+"errPathLastFoiCallUseMap.txt", "r") as fl:
		for line in fl:
			ln = line.split("- ")
			if len(ln) > 1:
				if ln[1] != main_release: 
					pathLastCall[ln[0]] = ln[1].strip()

def fill_csMap():
	src_counter = 0
	with open(wd+"errInsnPath_Map_CS.txt", "r") as fl:
		data = fl.readlines()
		for c, line in enumerate(data):
			if line[0] == "[":
				idx, src = line.split()
				idx = idx.strip("[]")	
				if src in rev_cs_string_map:
					src_id = rev_cs_string_map[src]
				else:
					src_id =  src_counter
					src_counter += 1
					rev_cs_string_map[src] = src_id
					cs_string_map[src_id] = src		

				cs_map[idx] = src_id
				ret_map[idx] = data[c+1].strip()
	with open(wd+"insnPath_Map_CS.txt", "r") as fl:
		data = fl.readlines()
		for c, line in enumerate(data):
			if line[0] == "[":
				idx, src = line.split()
				idx = idx.strip("[]")
				# if idx == '192':
				# 	pass	
				if src in rev_cs_string_map:
					src_id = rev_cs_string_map[src]
				else:
					src_id =  src_counter
					src_counter += 1
					rev_cs_string_map[src] = src_id
					cs_string_map[src_id] = src	

				cs_map[idx] = src_id
				ret_map[idx] = data[c+1].strip()				

def fill_opMaps():
	with open(wd+"OP_Map_index.txt", 'r') as fl:
		for line in fl:
			tmp = line.split()
			fn_id = tmp[0]
			fn = " ".join(tmp[1:])
			op_map[fn_id] = fn
			op_map_rev[fn] = fn_id	

def fill_release(input):

	if input not in ["call kfree", "call kfree_skb", "call dev_kfree_skb_irq"]:
		return 
	look = input
	look_id = op_map_rev[look]
	if look_id in releaseSetDic:
		pass
	else:
		releaseSetDic[look_id] = [look_id]

def addEqual(key, eqID):
	key_id = op_map_rev["call "+key]
	tmp = releaseSetDic[key_id]
	tmp.append(eqID)
	releaseSetDic[key_id] = tmp

def pattern_match(patt, seq):
	if len(patt) > len(seq):
		print "Pattern is longer than input sequence!"
		return False
	icmp_id = op_map_rev["icmp"]
	patt = [x for x in patt if x != icmp_id] 
	index = 0
	for item in seq:
		pattEntry = patt[index]
		if pattEntry in releaseSetDic.keys():
			lookFor = releaseSetDic[pattEntry]
		else:
			lookFor = [pattEntry]

		if item in lookFor:
			index += 1
		if index == len(patt):	
			return True
	return False

def fill_consumer(relSet):
	with open(os.getcwd()+"/run/releaseTerminals.txt", "r") as fl:
		for line in fl:
			consumerSet.add(line.strip())

def checkConsume(lCall, side, runningVisit):
	if lCall not in calleesMap.keys():
		return False
	
	if lCall in consumerSet:
		return True

	lookAfter = []
	clMap = calleesMap[lCall]

	if side == "fail":
		lookAfter = clMap['err']+ clMap['norm'] + clMap['+']
		if "IMPB" in lookAfter:	
			lookAfter.remove("IMPB")
	if lookAfter == [] or side == "succ":
		lookAfter = clMap['norm']+ clMap['+']
	if side == 'both':
		lookAfter = clMap['err'] + clMap['norm'] + clMap['+']

	#sanity check: lookAfter cannot be empty
	if lookAfter == []:
		return False

	for callee in lookAfter:
		if callee in ["ESCP", "UNLK", "TERM", "IMPB"]: 
			continue
		if callee in ["NULL", "UNDF", "VALF"]:
			return False
		if callee not in runningVisit:
			runningVisit.add(callee)
			if checkConsume(callee, side, runningVisit) == False:
				return False
	if side == "both":
		consumerSet.add(lCall) 
	return True

def fill_lastCallCheckSide():
	with open(wd+"errPathLastFoiCallSide.txt", "r") as fl:
		for line in fl:
			pId, side = line.split("- ")
			lastCallCheckSide[pId] = side.strip()

#============================
def match(args):
	strict = False
	global release_id
	global releaseSetDic
	global main_release
	global wd
	global wEscapeMode
	global found
	global foundDirty
	global consumerSet

	
	patt = []

	for idx, item in enumerate(args):
		if item.startswith("--strict"):
			strict = True
			continue
		if item.startswith("--sig"):
			patt = args[idx+1:] 
			break
		if item.startswith("--releases"):	
			releaseSetDic[patt[-2]] = args[idx+1:]
			break
		if item.startswith("--patt"):
			idx2 = idx + 1
			while (args[idx2][0] != "-"):
				patt.append(args[idx2])
				idx2 += 1
			continue
		if item.startswith("--foi"):
			FOI = args[idx+1]
			continue
		if item == "--wEscapeMode":
			wEscapeMode = True
			continue

	if patt == []:
		print "Usage: ./patt-match.py [--strict] --sig <seq-of-insns>"
		exit

	wd = os.getcwd() + "/run/" + FOI + "/"  
	
	print releaseSetDic
	print patt
	print "Going to match ..."


	fill_opMaps()
	fill_csMap()
	fill_pathLastCalls()
	fill_calleesMap()
	fill_callGraphMapIndex()
	fill_lineOffset() 
	fill_loop()
	fill_conditionalReleases()
	fill_lastCallCheckSide()
	
	if wEscapeMode:
		fill_escapings()


	with open(wd+"errPostPathInsnSeq.txt", "r") as fl:
		lines = fl.readlines()


	prevCallS = ""
	currentCallS = ""
	matchedPaths = []
	unmatchedPaths = []

	release_id = patt[-2]
	main_release = op_map[release_id]

	fill_release(main_release)
	print releaseSetDic

	relSetNames = set() #name of release funcs
	for rId in releaseSetDic[release_id]:
		relN = op_map[rId].split()[1] 
		relSetNames.add(relN)

	if consumeEnabled:
		fill_consumer(relSetNames)
		# print consumerSet

	lines += afterEscapePaths

	for line in lines:
		idx, seq = line.split("- ")
		callSeq = []
		for s in reversed(seq.split()[1:]):
			if op_map[s].startswith('call'):
				callSeq.append(op_map[s].split()[1])

		if len(seq.split()) == 3: 
			print "potentially FOI failure path, skipping! " + idx
			continue	
		
		if strict == True:
			if prevCallS != currentCallS:	
				if len(matchedPaths) > 0 and len(unmatchedPaths) > 0:
					print "does not match on these:"
					for un in unmatchedPaths:
						print "%s %s"%(un, callSiteDict[un])
				matchedPaths = []
				unmatchedPaths = []
		
			if pattern_match(patt, seq.split()) == False:
				unmatchedPaths.append(idx)
			else:
				matchedPaths.append(idx)
		
		else:
			dirty = False
			freed = False
			for foiCl in callSeq:
				if foiCl in relSetNames:
					freed = True
					break
			if freed:
				print "matched on (no leak): " + idx
				matched[idx] = release_id				
				continue

			if wEscapeMode:
				if idx in escapingPaths:
					print "foi is escaping: "+idx
					continue

			if idx not in pathLastCall.keys():
				print "does not found lastCall on: "+ idx
				foundMissingLast.append(idx)
				continue			
			lastCall = pathLastCall[idx]

			if lastCall.find("print") != -1:
				if len(callSeq) > 1:
					lastCall = callSeq[1]
			
			if consumeEnabled:
				if lastCall in consumerSet:
					print "foi is consumed: "+idx
					continue

				side = "both"
				if idx in lastCallCheckSide:
					d = lastCallCheckSide[idx]
					if d == 'S':
						side = "succ" 
					elif d == 'F':
						side = "fail"
					else:
						side = "both"
					
				if checkConsume(lastCall, side, set()):
					print "found new consumer in path " + idx + ": " + lastCall + " " + side
					continue
			
			if idx in loopOverFoi:
				print "::Loop::"
				dirty = True
			if idx in condRelease:
				print "::Condition::"
				dirty = True

			print "does not match on (potential leak): "+ idx
			storeFound(idx, dirty)

	dirtyCs = set()
	for item in foundDirty:
		dirtyCs.add(cs_map[item])

	for item in condRelease:	
		dirtyCs.add(cs_map[item])

	for item in loopOverFoi:	
		if item in cs_map:
			dirtyCs.add(cs_map[item])

	for item in found:
		if cs_map[item] in dirtyCs:
			foundDirty.add(item)

	found = found - foundDirty

	foundAfterEscape = set()
	for item in found:
		if item in afterEscapePathsIds:
			foundAfterEscape.add(item)

	found = found - foundAfterEscape
	
	with open(wd+"missmatchesFound.txt", "w") as fl:
		i = 1
		visited_cs = set()
		for idx in found:
			if cs_map[idx] in visited_cs:	
				continue
			fl.writelines("[%d] %s\n%s\n\n"%(i, idx, cs_string_map[cs_map[idx]]))
			visited_cs.add(cs_map[idx])
			i += 1

		fl.writelines("=======After Escape Paths======\n")
		potentialFOIs = set()
		with open(os.getcwd()+"/run/potentialFOIs.txt",'r') as flp:
			for line in flp:
				potentialFOIs.add(line.split()[0])
		i = 1
		for idx in foundAfterEscape:
			if cs_map[idx] in visited_cs:	#for now just print unique callsites
				continue		
			escapeeN = foi_startMap[idx].split()[0]
			if escapeeN in potentialFOIs:
				print idx+" poteintail FOI, skipping to report it: " + escapeeN
				continue
			fl.writelines("[%d] AE: %s\t%s\n%s\n\n"%(i, idx, foi_startMap[idx] , cs_string_map[cs_map[idx]]))
			visited_cs.add(cs_map[idx])
			i += 1


		fl.writelines("=======Found under loop/condition======\n")
		i = 1
		for idx in foundDirty:
			if cs_map[idx] in visited_cs:	
				continue		
			fl.writelines("[%d] L/C: %s\n%s\n\n"%(i, idx, cs_string_map[cs_map[idx]]))
			visited_cs.add(cs_map[idx])
			i += 1

		fl.writelines("=======failed to find last FOI use======\n")
		i = 1
		for idx in foundMissingLast:
			if cs_map[idx] in visited_cs:	
				continue		
			fl.writelines("[%d] missingLastU: %s\n%s\n\n"%(i, idx, cs_string_map[cs_map[idx]]))
			visited_cs.add(cs_map[idx])
			i += 1

if __name__ == "__main__":
	match(sys.argv[1:])
