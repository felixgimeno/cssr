#!/bin/python3
# Felix Gimeno's implementation of CSSR algorithm 
from typing import Dict,Any,Set

states = [{""}] # type: List[Set[str]]
#lista de estados, estado es conjunto sufijos {"ab","ba"} ...
alphabet = "" 
count = dict() # type: Dict[str, int] 
histories = dict() # type: Dict[str, Dict[str,float]]
computedProbabilitiesFromStates = dict() # type: Dict[int,Dict[str,float]]
smallquantity = 0.0000001 # prevent division by zero
already = set() # type: Set[str]

def move(ax: str, stateNumber1 : int, stateNumber2 : int, estimate : bool):
	global states
	
	#print("function move debug sN1 "+str(stateNumber1)+" sN2 "+str(stateNumber2))
	#print("before move")
	#print(states[stateNumber1])
	#print(states[stateNumber2])
	if ax in states[stateNumber1]:  
		states[stateNumber1].remove(ax)
	if estimate: getProbabilityFromState(stateNumber1, True)
	states[stateNumber2].add(ax)
	if estimate: getProbabilityFromState(stateNumber2, True)
	#print("after move")
	#print(states[stateNumber1])
	#print(states[stateNumber2])
	return

def Test(p, ax : str, stateNumber:int, alpha):
	if ax not in count.keys(): return ##not sure if breaks anything
	def chi_square(p : Dict[str,Any], stateNumber : int, alpha : float) -> bool:
		summation = 0
		p2 = getProbabilityFromState(stateNumber, False)
		for letter in alphabet:
			if letter not in p.keys(): p[letter] = 0
			if letter not in p2.keys(): p[letter] = 0
			if p2[letter] == 0: continue
			summation += (p[letter]-p2[letter])**2 / max(p2[letter],smallquantity)
		#import numpy
		#import scipy.stats	
		#observed = numpy.array(list(map(lambda x: p[x],alphabet)))
		#expected = numpy.array(list(map(lambda x: p2[x],alphabet))) 
		#(t,tt) = scipy.stats.chisquare(observed, expected)	
		## test = scipy.stats.chi2.ppf(1-alpha,len(alphabet)-1)	#constant
		#print("summation {} t {} tt {}".format(summation, t,tt)) # summation == t for all ...
		if summation > alpha: return False #it works
		#if tt < 1-alpha: return False
		return True

	global states
	#null hypothesis
	if (chi_square(p,stateNumber,alpha)):
		states[stateNumber].add(ax)
		return
	for stateNumber2 in range(len(states)):
		if stateNumber2 != stateNumber:
			if chi_square(p,stateNumber2,alpha):
				move(ax,stateNumber,stateNumber2,True)
				return
	states.append(set())
	move(ax,stateNumber,len(states)-1,True)
	return

def getProbabilityFromState(stateNumber:int, forced : bool):
	global computedProbabilitiesFromStates
	if stateNumber in computedProbabilitiesFromStates.keys() and not forced: return computedProbabilitiesFromStates[stateNumber]
	probability = dict() # type: Dict[str,float]
	totalSum = sum(map(lambda x: count[x], states[stateNumber].intersection(count.keys()))) # type: float
	totalSum = max(smallquantity,totalSum)
	for letter in alphabet:
		probability[letter] = 0
		for suffix in states[stateNumber].intersection(count.keys()):
			if suffix in histories.keys() and letter in histories[suffix].keys():
				probability[letter] += histories[suffix][letter]*count[suffix]
		probability[letter] /= totalSum	
	computedProbabilitiesFromStates[stateNumber] = probability	
	return probability
	
def cssr(Lmax : int, alpha : float):
	#part one: initialize/initialization
	L = 0

	global states
	states = [{""}] # "" null string suffix of everything 

	#part two: homogenize/sufficiency: to do: estimate 
	while L < Lmax:
		n = len(states)
		for stateNumber in range(n):
			getProbabilityFromState(stateNumber, False)
			for suffix in frozenset(states[stateNumber]):
				if len(suffix) > L: continue
				for letter in alphabet:
					if letter+suffix not in histories.keys():  histories[letter+suffix]= dict()
					p = histories[letter+suffix] #estimate("P(X_t | X^{t-1}_{t-l} = ax)")
					#print("cssr debug "+str(L)+" stateNumber "+str(stateNumber)+" suffix "+suffix+" letter "+letter)
					if letter+suffix not in already: ## only children of level L suffixes should be considered ... 
						Test(p,letter+suffix,stateNumber,alpha)
					already.add(letter+suffix) ##	
		#from itertools import groupby
		#states = [set(k) for k,v in groupby(sorted(states))]			
		# si reordeno o quito, computedProbabilitiesFromStates cambia ...
		
		#setOfLists = set([sorted(list(j)) for j in states])
		#states = sorted([set(j) for j in setOfLists])
		
		#print("cssr part two before removing parents "+str(states))
		
		def remove_parents() -> None: #if every child in different sets, and different from parent, then remove 
			f = dict() # type: Dict[str,int]
			for stateNumber in range(len(states)): 
				for suffix in states[stateNumber]: 
					f[suffix] = stateNumber
			for stateNumber in range(len(states)): 
				for suffix in frozenset(states[stateNumber]):
					acc = 0
					g = set() # type: Set[int]
					for letter in alphabet:
						if letter+suffix in f: g.add(f[letter+suffix])
					if stateNumber in g: continue
					if len(g) == len(alphabet):
						states[stateNumber].remove(suffix)
						print("cssr debug part two removing parent suffix {}".format(suffix))
						getProbabilityFromState(stateNumber, True)
		remove_parents()
		#print("cssr part two after removing parents "+str(states))
		print("cssr debug part two L {} end".format(L))	
		L += 1
		
	states = [{i for i in state if len(i) >= lmax-1} for state in states] # suffixes with length less than lmax can be ignored, but with length Lmax -1 or Lmax cannot
	from itertools import groupby
	states = [set(k) for k,v in groupby(sorted(states)) if len(k) != 0]		
	print("cssr debug part two end")
	#print("cssr part two states "+str(states))		
	
	#return
	#part three: determinize/recursion
	
	def whichState(w : str) -> int: # epsilon function
		if w not in count.keys(): return -1
		def isSuffix(str1 : str ,str2 : str ) -> bool: return str1.endswith(str2)
		for stateNumber in range(len(states)):
			for suffix in states[stateNumber]:
				if isSuffix(w,suffix): 
					return stateNumber
		print("whichState error {}".format(w))
		exit()

	f = dict() # type:Dict[str,int]
	for stateNumber in range(len(states)): 
		for suffix in states[stateNumber]: 
			f[suffix] = stateNumber
	#print(f)				
	def suffixToState(suffix:str)->int:
		if suffix in f: return f[suffix]
		if len(suffix) > Lmax: return suffixToState(suffix[len(suffix)-Lmax:len(suffix)])
		return -1
	def stateTransitions(stateNumber : int)->Set[int]:
		g = set() # type: Set[int]
		t = any(map(lambda j: len(j) == Lmax-1, states[stateNumber]))
		for suffix in states[stateNumber]:
			if t and len(suffix) == lmax:continue
			mylist = list(map(lambda letter: suffixToState(suffix+letter),alphabet))
			#print("suffix "+suffix+" "+str(mylist))
			g.update(mylist)
		#print("transitionable states from "+str(stateNumber)+" "+str(g))	
		if -1 in g: g.remove(-1)
		if stateNumber in g: g.remove(stateNumber)
		return g		 
	def remove_transient():
		G = set() # type: Set[int]
		for stateNumber in range(len(states)):	
			if states[stateNumber] == set(): continue
			G.update(stateTransitions(stateNumber))
		t = False
		for stateNumber in range(len(states)):
			if states[stateNumber] == set(): continue
			if stateNumber not in G: 
				print("cssr debug part three removing transient state with number "+str(stateNumber)+" and elements "+str(states[stateNumber]))
				states[stateNumber] = set() # si inalcanzables son transient
				t = True
		#print("t {} G {}".format(t,G))
		if t: remove_transient()			
	remove_transient()
	
	states = [set(k) for k,v in groupby(sorted(states)) if len(k) != 0]	
	
	recursive = False
	while not recursive:
		recursive = True
		for stateNumber in range(len(states)):
			for letter in alphabet:
				T1 = -1
				#t = any(map(lambda j: len(j) == Lmax-1, states[stateNumber]))
				for x in frozenset(states[stateNumber]):
					#if t and len(x) == Lmax: continue
					#to prevent 'data closures', len(x)=lmax -1 except if state doesnt have len lmax-1 elements 
					T0 = whichState(x+letter)
					if T0 == -1 : continue
					if T1 == -1 :
						T1 = T0
					else:
						T2 = T0
						if T1 != T2:
							states.append(set())
							#move(x,stateNumber,len(states)-1,False) #remeber we are using frozensets ...
							for y in frozenset(states[stateNumber]):
								T3 = whichState(y+letter)
								if T3 == -1: continue
								if T2 == T3:
									move(y,stateNumber,len(states)-1,False) 	
							recursive = False
							if len(states[len(states)-1]) > 0:
								print("cssr debug part three spawned new state {}".format(states[len(states)-1]))
														  
	print("cssr debug part three done")
	return

def init(data : str, lmax : int) -> None:
	#histories es diccionario de str a diccionario str freq	:: histories[suffix][letter] is probability that letter follows suffix in data
	def getHistories(data : str, lmax:int) -> Dict[str, Dict[str,float]]  :
		def count_l(histories : Dict[str, Dict[str,int]], data : str, l : int) -> None : # (pass by assignment)histories is dictionary ...,data string, length l int 
			for index in range(len(data)-l):
				currentHistory = data[index:index+l]
				nextLetter = data[index+l]
				if currentHistory not in histories: histories[currentHistory] = dict()
				if nextLetter not in histories[currentHistory]:  histories[currentHistory][nextLetter]=0
				histories[currentHistory][nextLetter] += 1

		def countToFrequency(histories : Dict[str, Dict[str,Any]]) -> None: #(pass by assignment) histories is dictionary of (pastString, dictionary(nextLetter,intCount))
			for history in histories:
				totalSum = sum(histories[history].values())
				totalSum *= 1.0
				for key in histories[history].keys():
					histories[history][key] /= totalSum
					#histories[history][key] = round(histories[history][key], 16) ##############################
		histories = dict() # type: Dict[str,Dict[str,Any]]
		for l in range(lmax+1):
			count_l(histories,data,l)
		countToFrequency(histories)
		return histories
	def getCount(data : str, lmax : int) -> Dict[str, int] :
		#getCount(data,lmax)[str] is number of times str (string length <= lmax) appears in data
		count = dict() # type: Dict[str, int] 
		for l in range(lmax+1):
			for index in range(len(data)-l):
				current = data[index:index+l]
				if current not in count: count[current] = 0
				count[current] += 1
		return count
	global count
	count =	getCount(data, lmax)
	global histories
	histories = getHistories(data, lmax)
	return	

from random import random, randint
myData = ""
N = 100000
nextState = 'A'
alphabet = "01"	
alpha = 0.001

selection = 1
lmax=3

for i in range(N):
	if selection == 1:
		##the even process
		if (random() > 0.5): myData = myData + "11"
		else: myData = myData + "0" 
	if selection == 2:
		## anbn process
		n = randint(1,2)
		myData += "0"*n+"1"*n
	if selection == 3: # to test determinize step
		if nextState == 'A':
			if randint(0,1) == 0:
				myData += '0'
				nextState='B'
			else:
				myData += '1'
				nextState='C'	
		elif nextState == 'B':
			if randint(0,1) == 0:			
				myData += '0'
				nextState='C'
			else:
				myData += '1'
				nextState='A'				
		else:
			myData +='1'		
			nextState ='A'

init(myData,lmax)
#print("count") 
#print(count)
#print("histories")
#print(histories)
print("cssr starting")
cssr(lmax,alpha)
print("cssr done")

from itertools import groupby
states = [set(k) for k,v in groupby(sorted(states)) if len(k) != 0]		

#print("states")
#print(states)
#print("prettier")
for i in range(len(states)):
	print(sorted(states[i]))
import math	
print("cssr done with lmax {} logN/logk {} number of states {} alphabet size {} alpha {}".format(lmax,math.log(len(myData))/math.log(len(alphabet)),len(states),len(alphabet),alpha))	
#	print(getProbabilityFromState(i,True))
#Test(getProbabilityFromState(0,True),"011",0,alpha)
#print(states)	
#print("even prettier")
#for state in states:
#	print({i for i in state if len(i) >= lmax -1})
