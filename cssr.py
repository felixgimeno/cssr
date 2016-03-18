#!/bin/python3
# Felix Gimeno's implementation of CSSR algorithm
from typing import Dict, Any, Set
from random import random, randint
from math import log
from itertools import groupby
import numpy as np
from scipy.stats import chisquare


class cssr():
	states = [{""}]  # type: List[Set[str]]
	alphabet = ""
	count = dict()  # type: Dict[str, int]
	histories = dict()  # type: Dict[str, Dict[str,float]]
	computedProbabilitiesFromStates = dict()  # type: Dict[int,Dict[str,float]]
	smallquantity = 0.0000001  # prevent division by zero
	already = set()  # type: Set[str]
	debug = True
	
	def __init__(self, alphabet, data, lmax, alpha):
		self.alphabet = alphabet
		self.data = data
		self.lmax = lmax
		self.alpha = alpha

	def move(self, ax: str, stateNumber1 : int, stateNumber2 : int, estimate : bool):
		if ax in self.states[stateNumber1]:
			self.states[stateNumber1].remove(ax)
		if estimate:
			self.getProbabilityFromState(stateNumber1, True)
		self.states[stateNumber2].add(ax)
		if estimate:
			self.getProbabilityFromState(stateNumber2, True)
		return

	def Test(self, p, ax : str, stateNumber:int):
		if ax not in self.count.keys():
			return
		
		def chi_square(self, p, stateNumber) -> bool:
			myImplementation = True
			if myImplementation:
				summation = 0
				p2 = self.getProbabilityFromState(stateNumber, False)
				for letter in self.alphabet:
					if letter not in p.keys(): p[letter] = 0
					if letter not in p2.keys(): p[letter] = 0
					if p2[letter] == 0: continue
					summation += (p[letter]-p2[letter])**2 / max(p2[letter],self.smallquantity)
				return summation <= self.alpha
			# as for now, scipy.stats.chisquare gives bad results ...	
			p2 = self.getProbabilityFromState(stateNumber, False)
			observed = np.array(list(map(lambda x: p.get(x, 0), self.alphabet)))
			expected = np.array(list(map(lambda x: p2.get(x, 0), self.alphabet))) 
			(t, _) = chisquare(observed, expected)	
			return t <= self.alpha
		# null hypothesis
		if (chi_square(self, p, stateNumber)):
			self.states[stateNumber].add(ax)
			return
		# alternative hypothesis	
		for stateNumber2 in range(len(self.states)):
			if stateNumber2 != stateNumber:
				if chi_square(self, p, stateNumber2):
					self.move(ax, stateNumber, stateNumber2, True)
					return
		# new state			
		self.states.append(set())
		self.move(ax, stateNumber, -1 + len(self.states), True)
		return

	def getProbabilityFromState(self, stateNumber:int, forced : bool):
		if not forced and stateNumber in self.computedProbabilitiesFromStates: 
			return self.computedProbabilitiesFromStates[stateNumber]
		totalSum = sum(self.count.setdefault(x, 0) for x in self.states[stateNumber]) # type: float
		totalSum = max(self.smallquantity, totalSum)
		probability = dict() # type: Dict[str,float]
		for letter in self.alphabet:
			probability[letter] = 0
			for suffix in self.states[stateNumber]:
				try:
					probability[letter] += self.histories[suffix][letter]*self.count[suffix]
				except KeyError:
					self.count.setdefault(suffix, 0)
					self.histories.setdefault(suffix, dict())
					self.histories[suffix].setdefault(letter, 0.0)	
			probability[letter] /= totalSum	
		self.computedProbabilitiesFromStates[stateNumber] = probability	
		return probability
		
	def mainAlgorithm(self):
		# part one: initialize/initialization
		L = 0
		self.states = [{""}]
		# part two: homogenize/sufficiency: to do: estimate
		while L < self.lmax:
			n = len(self.states)
			for stateNumber in range(n):
				self.getProbabilityFromState(stateNumber, False)
				for suffix in frozenset(self.states[stateNumber]):
					if len(suffix) > L: 
						continue
					for letter in self.alphabet:
						if letter+suffix not in self.histories.keys():  self.histories[letter+suffix]= dict()
						p = self.histories[letter+suffix] #estimate("P(X_t | X^{t-1}_{t-l} = ax)")
						#print("cssr debug "+str(L)+" stateNumber "+str(stateNumber)+" suffix "+suffix+" letter "+letter)
						if letter+suffix not in self.already: ## only children of level L suffixes should be considered ... 
							self.Test(p,letter+suffix,stateNumber)
						self.already.add(letter+suffix) ##	
			def remove_parents(states, alphabet) -> None: #if every child in different sets, and different from parent, then remove 
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
							self.getProbabilityFromState(stateNumber, True)
			remove_parents(self.states,self.alphabet)
			#print("cssr part two after removing parents "+str(states))
			print("cssr debug part two L {} end".format(L))	
			L += 1
			
		print("cssr debug part two end")
		
		self.states = self.getStates()
		
		# part three: determinize/recursion
		
		def whichState(count, states, w : str) -> int: # epsilon function
			if w not in count: 
				return -1
			for index, elem in enumerate(states):
				for suffix in elem:
					if w.endswith(suffix):
						return index				
			print("whichState error {}".format(w))
			exit()

		f = dict() # type:Dict[str,int]
		for stateNumber in range(len(self.states)): 
			for suffix in self.states[stateNumber]: 
				f[suffix] = stateNumber
		def suffixToState(suffix : str, lmax : int)->int:
			if suffix in f: 
				return f[suffix]
			if len(suffix) > lmax: 
				return suffixToState(suffix[len(suffix)-lmax:len(suffix)], lmax)
			return -1
		def stateTransitions(states, stateNumber : int, lmax : int, alphabet : str) -> Set[int]:
			g = set() # type: Set[int]
			t = any(map(lambda j: len(j) == lmax-1, states[stateNumber]))
			for suffix in states[stateNumber]:
				if t and len(suffix) == lmax:continue
				mylist = list(map(lambda letter: suffixToState(suffix+letter, lmax),alphabet))
				#print("suffix "+suffix+" "+str(mylist))
				g.update(mylist)
			#print("transitionable states from "+str(stateNumber)+" "+str(g))	
			if -1 in g: g.remove(-1)
			if stateNumber in g: g.remove(stateNumber)
			return g		 
		def remove_transient(states, lmax, alphabet) -> None:
			# if state node in-degree is zero then unreachable then transient
			G = set() # type: Set[int]
			for stateNumber in range(len(states)):	
				if states[stateNumber] == set(): continue
				G.update(stateTransitions(states, stateNumber, lmax, alphabet))
			t = False
			for stateNumber in range(len(states)):
				if states[stateNumber] == set(): continue
				if stateNumber not in G: 
					print("cssr debug part three removing transient state with number "+str(stateNumber)+" and elements "+str(states[stateNumber]))
					states[stateNumber] = set()
					t = True
			if t: 
				remove_transient(states, lmax, alphabet)			
			return
		remove_transient(self.states, self.lmax, self.alphabet)
		
		self.states = self.getStates()

		def newState(self, index, letter, T2):
			self.states.append(set())
			visited = set()
			for y in frozenset(state):
				if y in visited:
					pass
				visited.add(y)
				T3 = whichState(self.count, self.states, y+letter)
				if T3 == -1: 
					continue
				if T2 == T3:
					self.move(y, index, len(self.states)-1, False) 	
			if len(self.states[len(self.states)-1]) > 0:
				print("cssr debug part three spawned new state {}".format(self.states[len(self.states)-1]))
			return
		
		recursive = False
		while not recursive:
			recursive = True
			for letter in self.alphabet:
				for index, state in enumerate(self.states):
					T1 = -1
					staterecursive = False
					while not staterecursive:
						staterecursive = True
						for x in state:
							#if t and len(x) == Lmax: continue
							#to prevent 'data closures', len(x)=lmax -1 except if state doesnt have len lmax-1 elements 
							T0 = whichState(self.count, self.states, x+letter)
							if T0 == -1 : 
								continue
							if T1 == -1 :
								T1 = T0
							elif T1 != T0:
								newState(self, index, letter, T0)
								recursive = False
								staterecursive = False
								break
															  
		print("cssr debug part three done")
		return

	def precompute(self) -> None:
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
		self.count = getCount(self.data, self.lmax)
		self.histories = getHistories(self.data, self.lmax)
		return	

	def getStates(self):
		# after cssr part two,
		# suffixes with length less than lmax can be ignored,
		# but with length Lmax -1 or Lmax cannot
		states = self.states
		states = [{i for i in state if len(i) >= self.lmax-1} for state in states] 	
		states = [set(k) for k,v in groupby(sorted(states)) if len(k) != 0]	
		self.states = states
		return self.states
		
def main():
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

	myCSSR = cssr(alphabet,myData,lmax,alpha)
	print("precomputing")
	myCSSR.precompute()
	print("precomputing done")
	print("CSSR start")
	myCSSR.mainAlgorithm()
	print("CSSR end")
	states = myCSSR.getStates()	
	for state in states:
		print(state)
	print("values lmax {} logN/logk {} number of states {} alphabet size {} alpha {}"
		.format(lmax, log(len(myData)) / log(len(alphabet)), len(states), len(alphabet), alpha))	
	return	

if __name__ == "__main__":
	main()
