#!/usr/bin/python3
# Felix Gimeno's implementation of CSSR algorithm
# the most time-consuming operations are precompute, whichState and getProbabilityFromState 
from typing import Dict, Any, Set
from random import random, randint
from math import log
from itertools import groupby
from os import stat
from functools import lru_cache
import json


class cssr():
	fileid = ""
	lmax = 0
	alpha = 0.0
	states = [{""}]  # type: List[Set[str]]
	alphabet = ""
	count = dict()  # type: Dict[str, int]
	histories = dict()  # type: Dict[str, Dict[str,float]]
	computedProbabilitiesFromStates = dict()  # type: Dict[int,Dict[str,float]]
	smallquantity = 0.0000001  # prevent division by zero
	debug = False

	
	def setDebugFlag(self):
		self.debug = True
	
	def decreaseLmax(self, lmax: int) -> None:
		if (lmax < self.lmax):
			self.lmax = lmax
		else:
			print("decreaseLmax error")
			exit(1)

	def setAlpha(self, alpha):
		self.alpha = alpha	

	def __init__(self, alphabet: str, fileid : str, lmax: int, alpha: float, formatting : bool) -> None:
		self.alphabet = alphabet
		self.fileid = fileid
		self.lmax = lmax
		self.alpha = alpha
		self.formatting = formatting

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
	def Test(self, p, ax : str, stateNumber : int):
		if ax not in self.count.keys():
			return

		# null hypothesis
		if (self.chi_square(p, stateNumber)):
			self.states[stateNumber].add(ax)
			return

		# alternative hypothesis
		for stateNumber2 in range(len(self.states)):
			if stateNumber2 != stateNumber:
				if self.chi_square(p, stateNumber2):
					self.move(ax, stateNumber, stateNumber2, True)
					return
		
		# new state			
		self.states.append(set())
		self.move(ax, stateNumber, -1 + len(self.states), True)
		return
	@lru_cache(maxsize = None)	
	def mult(self, letter: str, suffix: str):
		try:
			return self.histories[suffix][letter] * self.count[suffix]
		except KeyError:
			self.count.setdefault(suffix, 0)
			self.histories.setdefault(suffix, dict())
			self.histories[suffix].setdefault(letter, 0.0)
		return 0.0
	
	def letter_probability(self, letter : str, index : int):
		return sum(self.mult(letter, suffix) for suffix in self.states[index])
				
	def getProbabilityFromState(self, stateNumber:int, forced : bool):
		if not forced and stateNumber in self.computedProbabilitiesFromStates: 
			return self.computedProbabilitiesFromStates[stateNumber]
		totalSum = sum(self.count.setdefault(x, 0) for x in self.states[stateNumber]) # type: float
		totalSum = max(self.smallquantity, totalSum)
		probability = dict() # type: Dict[str,float]
		for letter in self.alphabet:
			probability[letter] = self.letter_probability(letter, stateNumber) / totalSum
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
			# except if it is the last one
			G = set()  # type: Set[int]
			acc = 0
			for stateNumber in range(len(states)):	
				if states[stateNumber] == set(): continue
				G.update(stateTransitions(states, stateNumber, lmax, alphabet))
				acc +=1
			t = False
			for stateNumber in range(len(states)):
				if states[stateNumber] == set(): continue
				if stateNumber not in G and acc != 1: 
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
			w = w[len(w)-lmax:len(w)]
			if w in f:
				if f[w] is not None: 
					value = f[w]
					if value >= 0 and value < len(states) and w in states[value]:
						return value
			for index, elem in enumerate(states):
				if w in elem:
					f[w] = index
					return index
			
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
		self.states = [{""}]
		self.computedProbabilitiesFromStates = dict()  # type: Dict[int,Dict[str,float]]
		
		self.mainAlgorithmPartTwo()
		self.mainAlgorithmPartThree()
		
		return

	def precompute_by_index(self) -> None:
		self.count = dict()  # type: Dict[str, int]
		self.histories = dict()
		class myFile:
			def __init__(self, myId : str, lmax : int) -> None:
				self.f = open(myId, 'r')
				self.v = self.f.read(lmax+4)
				self.index = 0
			def readMore(self):
				w = self.f.read(1)
				self.v = self.v[1:] + w
				self.index += 1
				return w != '' 
			def get(self, index1, index2):
				return self.v[index1-self.index:index2-self.index]
			def len(self) -> int:
				return len(self.v)
			def close(self):
				self.f.close()
			def getIndex(self) -> int:
				return self.index			
		mF = myFile(self.fileid, self.lmax)
		while True:
			index = mF.getIndex()
			for l in range(1 + self.lmax):
				if l >= mF.len():
					continue
				current = mF.get(index, index+l)
				self.count[current] = 1 + self.count.setdefault(current, 0)
				
				nextLetter = mF.get(index+l,index+l+1)
				self.histories.setdefault(current, dict())
				self.histories[current][nextLetter] = 1 + self.histories[current].setdefault(nextLetter, 0)
			mF.readMore()
			if mF.len() == 0: 
				break
		mF.close()			
		for history in self.histories:
			totalSum = 1.0 * sum(self.histories[history].values())
			for letter in self.histories[history]:
				self.histories[history][letter] /= totalSum
		return		
	def precompute_write(self) -> None:
		json.dump(self.count, open("cssr_count.out",'w'), sort_keys=True, indent=4, separators=(',', ': '))
		json.dump(self.histories, open("cssr_histories.out",'w'), sort_keys=True, indent=4, separators=(',', ': '))
	def precompute_read(self) -> None:
		self.count = dict(json.load(open("cssr_count.out",'r')) )
		self.histories = dict(json.load(open("cssr_histories.out",'r')))
	def getStates(self):
		# after cssr part two,
		# suffixes with length less than lmax can be ignored,
		# but with length -1+lmax or lmax cannot
		states = self.states
		states = [{i for i in state if len(i) >= -1 + self.lmax} for state in states] 	
		states = [set(k) for k, v in groupby(sorted(states)) if len(k) != 0]	
		self.states = states
		return self.states
	def states_write(self) -> None:
		m = {i : {j : w for j, w in enumerate(v)} for i, v in enumerate(self.states)}
		#print(m)
		json.dump(m, open("cssr_"+str(self.alpha)+".out",'w'), sort_keys=True, indent=4, separators=(',', ': '))
def generateSample(selection:int, N:int) -> None:
	if selection == 5:
		generateLabyrinth(N)
		return
	myData = ""
	nextState = 'A'
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
	# f = open("cssr.in",'w')
	# f.write(myData)
	# f.close()				
	return
	
def generateLabyrinth(N: int):
	class board:
		board=[[0,0,0],[0,0,0],[0,0,0]]
		current = (0, 0)
		start =   (0, 0)
		end =     (0, 0)
		
		
		def __init__(self, c, r) -> None:
			self.c = c
			self.r = r	
		def pos(self, t) -> bool:
			x, y = t
			#print(str(x)+" "+str(y))
			s = x >= 0 and y >= 0 and self.c >= x and self.r >= y
			#print(s)
			return s  	 
		def get(self,x,y) -> int:
			return self.board[x][y]
		def posnext(self) -> str:
			while True:
				m = randint(0,6)
				n = [1, 1, 1, 2, 2, 3, 4][m]
				letter = {1 : "R", 2: "U", 3 :"L",4:"D"}[n]
				#print("letter "+letter)
				x, y = self.current
				pnext = (x, y)
				if letter == "R": pnext = (x+1, y)
				if letter == "U": pnext = (x,y+1)
				if letter == "L": pnext = (x-1,y)
				if letter == "D": pnext = (x,y-1)
				if not self.pos(pnext):
					continue
				if pnext == self.end or pnext == self.start:
					self.current = self.start
					return letter + "S"
				self.current = pnext
				return letter
			return ""
	myBoard = board(2,2)
	l =  ( myBoard.posnext() for i in range(1, N) )
	string = str("".join(list(l)))
	with open("cssr.in",'w') as f:
		f.write(string)
	return	
	
def main():
	generate_again = True
	if generate_again:
		selection = 1
		N = 100000000	
		generateSample(selection, N)
	alphabet = "01"	
	lmax = 25
	my_file_id = "cssr.in"
	my_formatting = False
	alpha = 0.001
	myCSSR = cssr(alphabet, my_file_id, lmax, alpha, my_formatting)
	
	load_again = True
	if load_again:
		print("parsing")
		myCSSR.precompute_by_index()
		myCSSR.precompute_write()
		print("parsing done, written to file")
		return
	#myCSSR.setDebugFlag()
	print("parse: reading from file")
	myCSSR.precompute_read()
	print("parse: done")
	#alphalist = [0.001, 0.01, 0.1, 1, 10, 100, 1000]
	alphalist = [0.001]
	alphalist.reverse()
	for alpha in alphalist:
		myCSSR.setAlpha(alpha)
		print("CSSR start")
		myCSSR.mainAlgorithm()
		print("CSSR end")
		states = myCSSR.getStates()
		"""
		if len(states) < 10:	
			for state in states:
				if len(state) < 20:
					print(state)
		"""
		myCSSR.states_write()
		print(
			"CSSR done with values lmax {} logN/logk {} number of states {} alphabet size {} alpha {}"
			.format(lmax, log(stat("cssr.in").st_size) / log(len(alphabet)), len(states), len(alphabet), alpha)	
			)
	return	

if __name__ == "__main__":
	main()
	
