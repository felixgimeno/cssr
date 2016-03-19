#!/bin/python3
# Felix Gimeno's implementation of CSSR algorithm
# the most time-consuming operations are precompute, whichState and getProbabilityFromState 
from typing import Dict, Any, Set
from random import random, randint
from math import log
from itertools import groupby


class cssr():
	states = [{""}]  # type: List[Set[str]]
	alphabet = ""
	count = dict()  # type: Dict[str, int]
	histories = dict()  # type: Dict[str, Dict[str,float]]
	computedProbabilitiesFromStates = dict()  # type: Dict[int,Dict[str,float]]
	smallquantity = 0.0000001  # prevent division by zero
	debug = False

	
	def setDebugFlag(self):
		debug = True
		
	def __init__(self, alphabet, data, lmax, alpha):
		self.alphabet = alphabet
		self.data = data
		self.lmax = lmax
		self.alpha = alpha

	def Test(self, p, ax : str, stateNumber:int):
		if ax not in self.count.keys():
			return

		def chi_square(self, p, stateNumber) -> bool:
			p2 = self.getProbabilityFromState(stateNumber, False)
			summation = 0
			for letter in self.alphabet:
				x = p.setdefault(letter, 0)
				y = p2.setdefault(letter, 0)
				summation += (x - y)**2 / max(y, self.smallquantity)
			return summation <= self.alpha

		def move(self, ax: str, stateNumber1 : int, stateNumber2 : int, estimate : bool) -> None:
			self.states[stateNumber1].discard(ax)
			self.states[stateNumber2].add(ax)
			if estimate:
				self.getProbabilityFromState(stateNumber1, True)
				self.getProbabilityFromState(stateNumber2, True)
			return

		# null hypothesis
		if (chi_square(self, p, stateNumber)):
			self.states[stateNumber].add(ax)
			return
		# alternative hypothesis
		for stateNumber2 in range(len(self.states)):
			if stateNumber2 != stateNumber:
				if chi_square(self, p, stateNumber2):
					move(self, ax, stateNumber, stateNumber2, True)
					return
		# new state			
		self.states.append(set())
		move(self, ax, stateNumber, -1 + len(self.states), True)
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
	
	def mainAlgorithmPartTwo(self) -> None:
		# part two: homogenize/sufficiency
		def remove_parents(states, alphabet) -> None: 
			# if every child in different sets, and different from parent, then remove 
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
						if self.debug:
							print("cssr debug part two removing parent suffix {}".format(suffix))
						self.getProbabilityFromState(stateNumber, True)
			return
		already = set()  # type: Set[str]	
		for L in range(self.lmax):
			n = len(self.states)
			for stateNumber in range(n):
				self.getProbabilityFromState(stateNumber, False)
				for suffix in frozenset(self.states[stateNumber]):
					if len(suffix) > L: 
						continue
					for letter in self.alphabet:
						if letter+suffix not in already:
							p = self.histories.setdefault(letter+suffix, dict())
							self.Test(p,letter+suffix,stateNumber)
							already.add(letter+suffix)

			remove_parents(self.states,self.alphabet)
			if self.debug:
				print("cssr debug part two L {} end".format(L))	
			
		if self.debug:
			print("cssr debug part two end")
		
		self.states = self.getStates()
		return
		
	def mainAlgorithmPartThree(self):
		# part three: determinize/recursion
		
		# for removing transitions, to prevent 'data closures', 
		# len(x) = -1 + lmax except if state doesn't have len lmax-1 elements
		
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
					if self.debug:
						print("cssr debug part three removing transient state with number "+str(stateNumber)+" and elements "+str(states[stateNumber]))
					states[stateNumber] = set()
					t = True
			if t: 
				remove_transient(states, lmax, alphabet)			
			return
		remove_transient(self.states, self.lmax, self.alphabet)
		
		self.states = self.getStates()

		

		def whichState(count, states, w : str, lmax) -> int:
			# epsilon function
			if w not in count: 
				return -1
			if w in f:
				value = f[w]
				if any(w.endswith(suffix) for suffix in states[value]):
					return value	 	
			for index, elem in enumerate(states):
				if any(w.endswith(suffix) for suffix in elem):
					return index	
			#print("whichState error {}".format(w))
			#exit()
			# suffixToState(w, lmax)
			
		def newState(self, index, letter, T2):
			result = list(map(lambda y: (y, whichState(self.count, self.states, y+letter, self.lmax)), self.states[index]))
			self.states.append(set())
			indexDest = -1 + len(self.states)
			for suffix, value in result:
				if -1 == value: 
					continue
				elif T2 == value:
					self.states[index].remove(suffix)
					self.states[indexDest].add(suffix)
					f[suffix] = value
			stateDest = self.states[indexDest]
			if len(stateDest) > 0 and self.debug:
				print("cssr debug part three spawned new state {}".format(stateDest))
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
							
							T0 = whichState(self.count, self.states, x+letter, self.lmax)
							if T0 == -1 : 
								continue
							if T1 == -1 :
								T1 = T0
							elif T1 != T0:
								newState(self, index, letter, T0)
								recursive = False
								staterecursive = False
								break
															  
		if self.debug:
			print("cssr debug part three done")
		return
	
	def mainAlgorithm(self) -> None:
		self.mainAlgorithmPartTwo()
		self.mainAlgorithmPartThree()
		return

	"""def precompute(self) -> None:
		#histories es diccionario de str a diccionario str freq	:: histories[suffix][letter] is probability that letter follows suffix in data
		def getHistories(data : str, lmax:int) -> Dict[str, Dict[str,float]]  :
			def count_l(histories : Dict[str, Dict[str,int]], data : str, l : int) -> None : # (pass by assignment)histories is dictionary ...,data string, length l int 
				for index in range(len(data)-l):
					currentHistory = data[index:index+l]
					nextLetter = data[index+l]
					if currentHistory not in histories: histories[currentHistory] = dict()
					if nextLetter not in histories[currentHistory]:  histories[currentHistory][nextLetter]=0
					histories[currentHistory][nextLetter] += 1

			def countToFrequency(histories : Dict[str, Dict[str,Any]]) -> None: 
				# (pass by assignment) histories is dictionary of (pastString, dictionary(nextLetter,intCount))
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
					if current not in count: 
						count[current] = 0
					count[current] += 1
			return count
		self.count = getCount(self.data, self.lmax)
		self.histories = getHistories(self.data, self.lmax)
		return	"""

	def precompute_by_index(self) -> None:
		self.count = dict()  # type: Dict[str, int]
		self.histories = dict()
		for index in range(len(self.data)):
			for l in range(1 + self.lmax):
				if index+l >= len(self.data):
					continue	
				current = self.data[index:index+l]
				self.count[current] = 1 + self.count.setdefault(current, 0)
				
				nextLetter = self.data[index+l]
				self.histories.setdefault(current, dict())
				self.histories[current][nextLetter] = 1 + self.histories[current].setdefault(nextLetter, 0)
		for history in self.histories:
			totalSum = 1.0 * sum(self.histories[history].values())
			for letter in self.histories[history]:
				self.histories[history][letter] /= totalSum
		
	def getStates(self):
		# after cssr part two,
		# suffixes with length less than lmax can be ignored,
		# but with length -1+lmax or lmax cannot
		states = self.states
		states = [{i for i in state if len(i) >= -1 + self.lmax} for state in states] 	
		states = [set(k) for k, v in groupby(sorted(states)) if len(k) != 0]	
		self.states = states
		return self.states

		
def main():
	myData = ""
	N = 100000
	nextState = 'A'
	alphabet = "01"	
	alpha = 0.1

	selection = 1
	lmax=17

	for i in range(N):
		if selection == 1:
			# the even process
			if (random() > 0.5): 
				myData = myData + "11"
			else: 
				myData = myData + "0" 
		if selection == 2:
			# anbn process
			n = randint(1,2)
			myData += "0"*n+"1"*n
		if selection == 3: 
			# to test determinize step
			if nextState == 'A':
				if randint(0, 1) == 0:
					myData += '0'
					nextState = 'B'
				else:
					myData += '1'
					nextState = 'C'	
			elif nextState == 'B':
				if randint(0, 1) == 0:			
					myData += '0'
					nextState = 'C'
				else:
					myData += '1'
					nextState = 'A'				
			else:
				myData += '1'		
				nextState = 'A'

	myCSSR = cssr(alphabet, myData, lmax, alpha)
	print("precomputing")
	myCSSR.precompute_by_index()
	print("precomputing done")
	print("CSSR start")
	myCSSR.mainAlgorithm()
	print("CSSR end")
	states = myCSSR.getStates()
	if len(states) < 10:	
		for state in states:
			print(state)
	print("values lmax {} logN/logk {} number of states {} alphabet size {} alpha {}"
		.format(lmax, log(len(myData)) / log(len(alphabet)), len(states), len(alphabet), alpha))	
	return	

if __name__ == "__main__":
	main()
