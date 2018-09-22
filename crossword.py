from nltk.corpus import words,wordnet
import numpy as np
from datetime import datetime
import os,sys
from tkinter import Tk,Canvas,Text,mainloop
from tqdm import tqdm
from joblib import Parallel,delayed
from multiprocessing import cpu_count
from string import ascii_letters
import json

class letternode:

	def __init__(self,letter,square):
		self.letter = letter
		self.connections = {}
		self.square_location = square.location

	def makeConnection(self,node):
		if not node.square_location in self.connections:
			self.connections[node.square_location] = []
		if not self.square_location in node.connections:
			node.connections[self.square_location] = []
		if not node in self.connections[node.square_location]:
			self.connections[node.square_location].append(node)
			node.connections[self.square_location].append(self)

class Square:

	def __init__(self,location,across=0,down=0,block=False):
		self.location = location
		self.down = down
		self.across = across
		self.block = block
		self.letter = ''
		self.rect = None
		self.nodes = {}

	def blockself(self):
		self.block = True

	def getPossibleLetters(self,solution,clues):
		return set.intersection(*[clue.getPossibleLetters(self,solution) for clue in clues])

class Clue:

	def __init__(self,number,squares,across=False,down=False):
		self.number = number
		self.squares = squares
		self.across = across
		self.down = down
		self.word = ''
		self.hint = ''
		self.solved = False
		self.length = None

	def fill(self,word,hint):
		self.hint = hint
		self.word = word

	def getPossibleLetters(self,square,solution):
		fbnodes = self.getPossibleNodes(square,solution,1)
		bfnodes = self.getPossibleNodes(square,solution,-1)
		nodes = set.intersection(fbnodes,bfnodes)
		return set([node.letter for node in nodes])

	def getPossibleNodes(self,square,solution,direction):
		if direction == 1:
			i = 0
		elif direction == -1:
			i = len(self.squares) - 1
		nodes = list(self.squares[i].nodes.values())
		if self.squares[i] in solution:
			nodes = [node for node in nodes if node.letter == solution[self.squares[i]]]
		while self.squares[i] is not square:
			i += direction
			nodes = [node for node in nodes if
					 self.squares[i].location in node.connections
					 for node in node.connections[self.squares[i].location]]
			if self.squares[i] in solution:
				nodes = [node for node in nodes if node.letter == solution[self.squares[i]]]
		return set(nodes)

class Board:

	def __init__(self,size,P0=0.5,P=0.9):
		self.size = size
		self.blocks = []
		self.clues = []
		self.Ps = [P0,0,0] # can have first square block but not next two
		for i in range(3,self.size):
			self.Ps.append(P)
		self.squares = [Square((j,i)) for i in range(self.size) for j in range(self.size)]
		self.squares_by_location = {square.location:square for square in self.squares}
		self.clues_by_square = {square:[] for square in self.squares}

	def generateBlocks(self,seed=11):
		np.random.seed(seed)
		leftcount = 0
		downcounts = np.zeros((self.size),dtype=int)
		halfsize = int(self.size/2)
		#make all clue lengths appropriate, don't make any clues too short
		#the top half of the board is filled in and twice reflected
		for i in range(halfsize):
			for j in range(self.size):
				# if not near any walls
				if j < self.size-3 and i < halfsize-3:
					blockprob = (self.Ps[leftcount]*self.Ps[downcounts[j]]*
								 self.Ps[self.size-1-j]*self.Ps[halfsize-1-i])**(1./4)
				# if near the middle (reflective wall) but not near the right edge
				elif j < self.size-3:
					blockprob = (self.Ps[leftcount]*self.Ps[downcounts[j]]*
								 self.Ps[self.size-1-j]*
								 self.Ps[downcounts[self.size-1-j]+halfsize-1-i])**(1./4)
				# if near both walls
				else:
					blockprob = (self.Ps[leftcount]*self.Ps[downcounts[j]])**(1./2)

				corner = ((i < 3 and j < 3) or (i < 3 and j > self.size-3))

				pathblocked = False
				if i > 2:
					pathblocked = True
					j_curs = [j]
					for i_ind in range(i-1,0,-1):
						j_curs2 = []
						for j_cur in j_curs:
							left = max([j_cur-1,0])
							right = min([j_cur+2,self.size-1])
							for j_ind in range(left,right):
								if self.squares_by_location[(j_ind,i_ind)].block:
									j_curs2.append(j_ind)
						if j_curs2:
							j_curs = j_curs2
						else:
							pathblocked = False
							break

				if ((not corner) and (not pathblocked) and
					(np.random.random() < blockprob)):
					self.squares_by_location[(j,i)].blockself()
					leftcount = -1
					downcounts[j] = -1

				#if the last one was a block and you're at the wall, this one must be a block
				if (j > self.size-3) and self.squares_by_location[(j-1,i)].block:
					self.squares_by_location[(j,i)].blockself()
					leftcount = -1
				if (i > self.size-3) and self.squares_by_location[(j,i-1)].block:
					self.squares_by_location[(j,i)].blockself()
					downcounts[j] = -1

				leftcount += 1
				downcounts[j] += 1
			leftcount = 0

		#now reflect to bottom half
		for i in range(int(self.size/2)):
			for j in range(self.size):
				if self.squares_by_location[(j,i)].block:
					self.squares_by_location[(self.size-1-j,self.size-1-i)].blockself()

		self.blocks = [square for square in self.squares if square.block]
		self.squares = [square for square in self.squares if not square.block]


	def generateClues(self):
		self.clues = []
		self.clues_by_square = {square:[] for square in self.squares}
		cluecount = 1
		#now go through and add clues and connect to next and previous squares
		for i in range(self.size):
			for j in range(self.size):
				if j == 0 or self.squares_by_location[(j-1,i)].block:
					k = j
					squares = []
					while (k < self.size) and (not self.squares_by_location[(k,i)].block):
						squares.append(self.squares_by_location[(k,i)])
						k += 1
					if len(squares) > 1:
						current_clue = Clue(cluecount,squares,across=True)
						for square in squares:
							self.clues_by_square[square].append(current_clue)
						self.squares_by_location[(j,i)].across = cluecount
						self.clues.append(current_clue)

				if i == 0 or self.squares_by_location[(j,i-1)].block:
					k = i
					squares = []
					while (k < self.size) and (not self.squares_by_location[(j,k)].block):
						squares.append(self.squares_by_location[(j,k)])
						k += 1
					if len(squares) > 1:
						current_clue = Clue(cluecount,squares,down=True)
						for square in squares:
							self.clues_by_square[square].append(current_clue)
						self.squares_by_location[(j,i)].down = cluecount
						self.clues.append(current_clue)

				if self.squares_by_location[(j,i)].across or self.squares_by_location[(j,i)].down:
					cluecount += 1
		for clue in self.clues:
			clue.length = len(clue.squares)

	def getClues(self,location):
		return self.clues_by_square[self.squares_by_location[location]]

	def getSquare(self,location):
		return self.squares_by_location[location]

	def draw(self,canvas,ss):
		for square in self.squares:
			loc = square.location
			id = canvas.create_text((10+ss/2+ss*loc[0],10+2*ss/3+ss*loc[1]),
									text=square.letter.upper(),
									font=("Helvetica",int(18*16/self.size)))
			square.id = id
			rect = canvas.create_rectangle(10+ss*loc[0],10+ss*loc[1],10+ss*loc[0]+ss,
										   10+ss*loc[1]+ss)
			square.rect = rect
			if square.across:
				canvas.create_text((10+ss/5+ss*loc[0],10+ss/5+ss*loc[1]),
									text=square.across,
									font=("Helvetica",int(8*16/self.size)))
			if square.down:
				canvas.create_text((10+ss/5+ss*loc[0],10+ss/5+ss*loc[1]),
									text=square.down,
									font=("Helvetica",int(8*16/self.size)))
		for square in self.blocks:
			loc = square.location
			canvas.create_rectangle(10+ss*loc[0],10+ss*loc[1],
									10+ss*loc[0]+ss,10+ss*loc[1]+ss,
									fill='black')

	def updateDraw(self,canvas):
		for square in self.squares:
			if not square.id is None:
				canvas.itemconfig(square.id,text=square.letter.upper())

class Crossword:

	def __init__(self,codex,size=16,P0=0.5,P=0.9):
		self.codex = codex
		self.size = size
		self.generateWordlist()
		self.P0 = P0
		self.P = P

	def display(self,root):
		self.drawCrossword(root)
		root.mainloop()

	def generateMasterWordlist(self):
		allwords = words.words()
		with open('xworddict.txt','w') as f:
			with open('xworddictlite.txt','w') as fl:
				for word in tqdm(allwords):
					syns = wordnet.synsets(word)
					if syns:
						if len(word) > 2:
							for s in syns:
								clue = s.definition()
								if word in clue:
									clue = clue.replace(word,'_'*len(word))
								fl.write('%s::%s\n' %(word,s.definition()))
						syns += [h for s in syns for t in (s.hypernyms(),s.hyponyms()) for h in t]
						lemmas = [l for s in syns for l in s.lemmas()]
						lemmas += [l2 for l in lemmas for l2 in l.derivationally_related_forms()]
						word_list = set([l.name() for l in lemmas if len(l.name()) > 2])
						clue_dict = {word:[s.definition() for s in wordnet.synsets(word)]
									 for word in word_list}
						for word in word_list.copy():
							if not word.isalnum():
								clues = clue_dict.pop(word)
								for bad_char in [char for char in word if not char in ascii_letters]:
									word = word.replace(bad_char,'')
								clue_dict[word] = clues
						for word in clue_dict:
							for clue in clue_dict[word]:
								if '::' in clue:
									clue = clue.replace('::',': :')
								if word in clue:
									clue = clue.replace(word,'_'*len(word))
								f.write('%s::%s\n' %(word,clue))
			f.close()

	def generateWordlist(self):
		dict_file = 'dictionaries/%s.txt' %(self.codex)
		if not os.path.isfile(dict_file):
			raise ValueError('Codex %s not found' %(self.codex))
		with open(dict_file,'r') as f:
			self.wordlist = {i+1:{} for i in range(2,self.size)}
			for line in f:
				line = line.rstrip()
				word,clue = line.split('::')
				if len(word) > 2 and len(word) <= self.size:
					word = word.upper()
					if word in self.wordlist[len(word)]:
						self.wordlist[len(word)][word].append(clue)
					else:
						self.wordlist[len(word)][word] = [clue]
			f.close()

	def addCluetoWordlist(self,word,clue):
		with open('%s.txt' %(self.codex),'a') as f:
			f.write('%s::%s\n' %(word,clue))
			f.close()

	def drawCrossword(self,root):
		screen_width = root.winfo_screenwidth()
		screen_height = root.winfo_screenheight()
		width = screen_width/2
		height = screen_height
		canvas = Canvas(root,width=width,height=width)
		ss = 0.95*width/self.size #square size
		self.board.draw(canvas,ss)
		acrosstext = Text(root,width=int(width/20),height=height)
		acrosstext.insert('end','Across\n')
		downtext = Text(root,width=int(width/20),height=height)
		downtext.insert('end','Down\n')
		for clue in sorted(self.board.clues,key=lambda x: x.number):
			if clue.across:
				acrosstext.insert('end',(str(clue.number) + '. ' + clue.hint + '\n'))
			if clue.down:
				downtext.insert('end',(str(clue.number) + '. ' + clue.hint + '\n'))
		canvas.pack(side = 'left')
		downtext.pack(side = 'right')
		acrosstext.pack(side = 'right')
		root.update()
		return canvas

	def setSolution(self,solution):
		self.clearSolution()
		for location in solution:
			square = self.board.getSquare(location)
			square.letter = solution[location]

	def _setSolution(self,solution):
		self.clearSolution()
		for square in solution:
			square.letter = solution[square]

	def clearSolution(self):
		for square in self.board.squares:
			square.letter = ''

	def setNodes(self):
		for clue_length in tqdm(self.wordlist):
			for word in self.wordlist[clue_length]:
				for clue in self.board.clues:
					if clue.length == clue_length:
						self.connect(clue,word)

	def connect(self,clue,word):
		for i in range(len(clue.squares)):
			square = clue.squares[i]
			letters = word[:i+1]
			if not letters in square.nodes:
				letter = word[i]
				square.nodes[letters] = letternode(letter,square)
			if i > 0:
				prev_letters = word[:i]
				prev_square = clue.squares[i-1]
				square.nodes[letters].makeConnection(prev_square.nodes[prev_letters])

	def getLeastOptionSquare(self,solution):
		squares = set([square for square in solution for clue in self.board.getClues(square.location)
					   for square in clue.squares if not square in solution])
		choices = {square:square.getPossibleLetters(solution,self.board.getClues(square.location))
				   for square in squares}
		choice_lens = {square:len(choices[square]) for square in choices}
		if choice_lens:
			los = min(choice_lens,key=choice_lens.get)
		else:
			square = [square for square in self.board.squares if not square in solution][0]
			return square,square.getPossibleLetters(solution,self.board.getClues(square.location))
		return los,choices[los]

	def solve(self,seed=11,size_limit=1e3,n_jobs=1):
		self.board = Board(self.size,P0=self.P0,P=self.P)
		self.board.generateBlocks(seed=seed)
		self.board.generateClues()
		print('Setting Nodes')
		self.setNodes()
		np.random.seed(seed)
		seed_square = np.random.choice(self.board.squares)
		letters = set([node.letter for node in seed_square.nodes.values()])
		solutions = [{seed_square:letter} for letter in letters]
		np.random.shuffle(solutions)
		if n_jobs > 1:
			with Parallel(n_jobs=n_jobs) as parallel:
				print('Solving')
				for solution_index in tqdm(range(1,len(self.board.squares))):
					n = len(solutions)
					print(n)
					n_per_batch = n//(n_jobs-1)
					batches = {i:range(i*n_per_batch,(i+1)*n_per_batch) for
							   i in range(n_jobs-1)}
					batches[n_jobs-1] = range((n_jobs-1)*n_per_batch,n)
					next_solutions = []
					results = parallel(delayed(getSolutions)
									   (self,solutions,batches[n])
									   	for n in range(n_jobs))
					solutions = []; result_ind = 0;
					while len(solutions) < size_limit and result_ind < n_jobs:
						next_solution_ind = 0; next_solution_len = len(results[result_ind])
						while len(solutions) < size_limit and next_solution_ind < next_solution_len:
							solutions.append(results[result_ind][next_solution_ind])
							next_solution_ind += 1
						result_ind += 1
				if not solutions:
					print('No solution found using this much memory')
					return
		else:
			for solution_index in tqdm(range(1,len(self.board.squares))):
				print(len(solutions))
				next_solutions = []
				for solution in solutions:
					square,letters = self.getLeastOptionSquare(solution)
					next_solutions += [{**solution,square:letter} for letter in letters]
				np.random.shuffle(next_solutions)
				solutions = []; next_solution_ind = 0; next_solution_len = len(next_solutions)
				while len(solutions) < size_limit and next_solution_ind < next_solution_len:
					solutions.append(next_solutions[next_solution_ind])
					next_solution_ind += 1
				if not solutions:
					print('No solution found using this much memory')
					return
		if solutions:
			solutions = [{square.location:letter for square,letter in solution.items()}
					 for solution in solutions]
			self.saveSolutions(solutions,seed)
			return True
		return False

	def saveSolutions(self,solutions,seed):
		dirname = 'solutions/%s/solution_%i_%i/' %(self.codex,self.size,seed)
		if not os.path.isdir(dirname):
			os.makedirs(dirname)
		j = 0
		while os.path.isfile(dirname + '%i.npz' %(j)):
			j += 1
		i = 0
		while i < len(solutions):
			solution = solutions[i]
			clues = self.generateClues(solution)
			np.savez_compressed(dirname + '%i.npz' %(i+j),solution=solution,clues=clues)
			i += 1

	def loadSolution(self,seed=0,j=None,name=None):
		self.board = Board(self.size,P0=self.P0,P=self.P)
		if name is not None:
			f = np.load('solutions/%s/%s.npz' %(self.codex,name))
		elif j is None:
			fs = os.listdir('solutions/%s/solution_%i_%i' %(self.codex,self.size,seed))
			f = np.load('solutions/%s/solution_%i_%i/' %(self.codex,self.size,seed) +
				 np.random.choice(fs))
		else:
			f = np.load('solutions/%s/solution_%i_%i/%i.npz' %(self.codex,self.size,seed,j))
		solution,clues = f['solution'].item(),f['clues'].item()
		if name is not None:
			np.savez_compressed('solutions/%s/%s.npz' %(self.codex,name),solution=solution,clues=clues)
		else:
			word_len = np.random.choice(range(max(int(self.size/2),3),int(self.size)))
			np.savez_compressed('solutions/%s/%s.npz' %(self.codex,
				np.random.choice(list(self.wordlist[word_len].keys()))),
													    solution=solution,clues=clues)
		for square in self.board.squares.copy():
			if square.location in solution:
				square.letter = solution[square.location]
			else:
				square.blockself()
				self.board.squares.remove(square)
				self.board.blocks.append(square)
		self.board.generateClues()
		clues = self.fillClues(solution,clues)
		for word in clues:
			if word in self.wordlist[len(word)]:
				if not clues[word] in self.wordlist[len(word)][word]:
					self.addCluetoWordlist(word,clues[word])
			else:
				self.addCluetoWordlist(word,clues[word])
		self.generateWordlist()
		return solution,clues

	def generateClues(self,solution):
		clues = {}
		for location in solution:
			square = self.board.getSquare(location)
			square.letter = solution[location]
		for clue in self.board.clues:
			word = ''.join([square.letter for square in clue.squares])
			if word in self.wordlist[len(word)]:
				this_clue = np.random.choice(self.wordlist[len(word)][word])
				clues[word] = this_clue
				clue.fill(word,this_clue)
			else:
				syns = wordnet.synsets(word)
				if syns:
					this_clue = np.random.choice(syns).definition().replace(word,'_'*len(word))
					clues[word] = this_clue
					clue.fill(word,this_clue)
				else:
					raise ValueError('Could not find word %s' %word)
		self.clearSolution()
		return clues

	def fillClues(self,solution,clues):
		for location in solution:
			square = self.board.getSquare(location)
			square.letter = solution[location]
		for clue in self.board.clues:
			word = ''.join([square.letter for square in clue.squares])
			clue.fill(word,clues[word])
		self.clearSolution()
		return clues

	def solutionToText(self,name):
		solution,clues = self.loadSolution(name=name)
		with open('solutions/%s/%s_solution.txt' %(self.codex,name),'w') as f:
			for location in solution:
				f.write('%i,%i:%s\n' %(location[0],location[1],solution[location]))
			f.close()
		with open('solutions/%s/%s_clues.txt' %(self.codex,name),'w') as f:
			for word in clues:
				f.write('%s:%s\n' %(word,clues[word]))
			f.close()

	def solutionToJSON(self,name):
		solution,clues = self.loadSolution(name=name)
		with open('solutions/%s/%s.json' %(self.codex,name),'w') as f:
			json_solution = {}
			for location,letter in solution.items():
				if location[0] in json_solution:
					json_solution[location[0]][location[1]] = letter
				else:
					json_solution[location[0]] = {location[1]:letter}
			json.dump({'solution':json_solution,'clues':clues},f,indent=4,sort_keys=True)

	def codexToJSON(self):
		with open('dictionaries/%s.json' %(self.codex),'w') as f:
			json.dump({str(key):value for key,value in self.wordlist.items()},f,indent=4)

def getSolutions(crossword,solutions,indices):
	next_solutions = []
	for solution in [solutions[i] for i in indices]:
		square,letters = crossword.getLeastOptionSquare(solution)
		next_solutions += [{**solution,square:letter} for letter in letters]
	return next_solutions

if __name__ == '__main__':
	if not len(sys.argv) == 4:
		raise ValueError('Please enter seed, size limit, number of jobs')
	_,seed,size_limit,n_jobs = sys.argv
	n_jobs = int(n_jobs); seed = int(seed); size_limit = float(size_limit);
	c = Crossword('master',size=16)
	solved = False
	while not solved:
		if c.solve(seed=seed,size_limit=size_limit,n_jobs=n_jobs):
			solution,clues = c.loadSolution(seed=seed,j=0)
			c.fillClues(solution,clues)
			c.setSolution(solution)
			c.display(Tk())
			solved = True
		seed += 1
