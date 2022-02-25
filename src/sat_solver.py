from hashlib import new
from multiprocessing import Process, Value, Array, Manager
from numpy.random import choice
import sys
import random
import time
import json
import os
from tkinter import N

class Solver:
  def __init__(self, filename):
    # parse the file
    f = open(filename, 'r')
    line = f.readline()
    self.filename = os.path.basename(os.path.normpath(filename))
    print(self.filename, end = ": ")
    while line[0] != 'p':
      line = f.readline()
    tokens = line.split()
    varSize = int(tokens[2])
    cnfSize = int(tokens[3])
    self.varSize = varSize
    self.varSet = set(range(1, varSize+1))
    self.cnfList = []
    for _ in range(cnfSize):
      line = f.readline()
      lineSplitted = line.split()
      clause = set([int(v) for v in lineSplitted][:-1])
      self.cnfList.append(clause)
    f.close()

    # initialize heuristics 
    self.numDetermHeurstics = 4
    self.numProcesses = 5
    self.heuristics = {}
    self.heuristics[0] = self.twoSidedJeroslowWangLiteral
    self.heuristics[1] = self.jeroslowWangLiteral
    self.heuristics[2] = self.dlcsLiteral
    self.heuristics[3] = self.dlisLiteral
    self.heuristics[4] = self.mixedLiteral

  ### multiprocessor solve function
  def solve(self):
    # shared variables
    self.manager = Manager()
    self.processes = [None]*self.numProcesses
    self.sat = Value('i', 0)
    self.assignment = Array('i', [0]*self.varSize)
    self.done = Value('i', -1)
    self.lock = self.manager.Lock()
    
    # solve
    start_time = time.time()
    for i in range(self.numProcesses):
      self.processes[i] = Process(target = self.singleSolve, args = (set(), i,))
      self.processes[i].start()
    while self.done.value == -1: # wait until one process finishes
      continue
    print(self.done.value)
    end_time = time.time()

    # terminate processes
    for i in range(self.numProcesses):
      self.processes[i].terminate()
    
    # record result
    sat = self.sat.value
    assignment = self.assignment
    result = {}
    result["Instance"] = self.filename[:-4] if self.filename[-4:] == '.cnf' else self.filename
    if sat:
      assignment = sorted(assignment, key = lambda x: abs(x))
      result['Solution'] = ' '.join(['%d true' % (v) if v > 0 else '%d false' % (-v) for v in assignment])
    result['Result'] = 'SAT' if sat else 'UNSAT'
    result['Time'] = '%.2f' % (end_time-start_time)
    return result
  
  ### single-processor solve function
  def singleSolve(self, assignment, index):
    # run with the corresponding heuristics
    sat, assignment = self.recursiveSolve(self.cnfList, self.varSet, assignment, heuristics= self.heuristics[index])

    # update the shared result member variables
    self.lock.acquire() # to prevent race
    if self.done.value != -1: # only the first process that acquires the lock can update the assignment
      return
    self.sat.value = sat
    for i, elt in enumerate(assignment):
      self.assignment[i] = elt
    self.done.value = index
    self.lock.release()
    return
  
  ### Remove unit and pure literals
  def removeUnitLiterals(self, cnfList, varSet, assignment):
    # assert len(varSet) + len(assignment) == self.varSize
    newCnfList = []
    newVarSet = varSet.copy()
    newAssignment = assignment.copy()

    # go through all clauses
    changed = False
    for clause in cnfList:
      if len(clause) == 1:
        literal = next(iter(clause))
        if -literal in newAssignment:
          # assert len(newVarSet) + len(newAssignment) == self.varSize
          return False, True, newCnfList, newVarSet, assignment # False means that there is no possible satisfying assignment
        elif literal not in newAssignment:
          changed = True
          newVarSet.remove(abs(literal))
          newAssignment.add(literal)
    
    # create the newCnfList
    for clause in cnfList:
      append = True
      newClause = clause.copy()
      for literal in clause:
        if literal in newAssignment:
          append = False
          break
        if -literal in newAssignment:
          newClause.remove(literal)
      if append:
        newCnfList.append(newClause)
    # assert len(newVarSet) + len(newAssignment) == self.varSize
    return True, changed, newCnfList, newVarSet, newAssignment

  def removePureLiterals(self, cnfList, varSet, assignment):
    # assert len(varSet) + len(assignment) == self.varSize
    newCnfList = []
    newVarSet = varSet.copy()
    newAssignment = assignment.copy()
    changed = False
    observed = set()
    
    # iterate through the clauses
    for clause in cnfList:
      for literal in clause:
        observed.add(literal)
    
    # update the assignment
    for var in varSet:
      if var not in observed or -var not in observed:
        changed = True
        newVarSet.remove(var)
        if -var in observed:
          newAssignment.add(-var)
        else:
          newAssignment.add(var)
    
    # update the clauses
    for clause in cnfList:
      append = True
      newClause = clause.copy()
      for literal in clause:
        if literal in newAssignment:
          append = False
          break
        if -literal in newAssignment:
          newClause.remove(literal)
      if append:
        newCnfList.append(newClause)
    # assert len(newVarSet) + len(newAssignment) == self.varSize
    return changed, newCnfList, newVarSet, newAssignment

  ### Heuristics to choose a literal
  def randomLiteral(self, curVarSet, curCnfList):
    # purely random
    var = random.choice(range(len(curVarSet)))
    literal = -var if random.getrandbits(1) else var
    return literal

  def dlcsLiteral(self, curVarSet, curCnfList):
    # Dynamic Largest Combined Sum
    scores = {}
    for v in curVarSet:
      scores[v] = 0
      scores[-v] = 0
    bestScore = -1
    bestVariable = 0
    for clause in curCnfList:
      for literal in clause:
        scores[literal] += 1
        if bestScore < scores[literal] + scores[-literal]:
          bestScore = scores[literal] + scores[-literal]
          bestVariable = abs(literal)
    return bestVariable if scores[bestVariable] > scores[-bestVariable] else -bestVariable
  
  def dlisLiteral(self, curVarSet, curCnfList):
    # Dynamic Largest Individual Sum
    scores = {}
    for v in curVarSet:
      scores[v] = 0
      scores[-v] = 0
    bestScore = -1
    bestLiteral = 0
    for clause in curCnfList:
      for literal in clause:
        scores[literal] += 1
        if bestScore < scores[literal]:
          bestScore = scores[literal]
          bestLiteral = literal
    return bestLiteral

  def jeroslowWangLiteral(self, curVarSet, curCnfList):
    # JeroslowWang heuristics
    scores = {}
    for v in curVarSet:
      scores[v] = 0
      scores[-v] = 0
    bestScore = -1
    bestLiteral = 0
    for clause in curCnfList:
      l = len(clause)
      for literal in clause:
        scores[literal] += pow(2, -l)
        if bestScore < scores[literal]:
          bestScore = scores[literal]
          bestLiteral = literal
    return bestLiteral

  def twoSidedJeroslowWangLiteral(self, curVarSet, curCnfList):
    # two sided Jeroslow Wang heuristics
    scores = {}
    for v in curVarSet:
      scores[v] = 0
      scores[-v] = 0
    bestScore = -1
    bestVariable = 0
    for clause in curCnfList:
      l = len(clause)
      for literal in clause:
        scores[literal] += pow(2, -l)
        if bestScore < scores[literal] + scores[-literal]:
          bestScore = scores[literal] + scores[-literal]
          bestVariable = abs(literal)
    return bestVariable if scores[bestVariable] > scores[-bestVariable] else -bestVariable  

  def mixedLiteral(self, curVarSet, curCnfList):
    # choose a heuristics randomly and apply
    return self.heuristics[choice(range(self.numDetermHeurstics), 1, [0.5, 0.2, 0.2, 0.1])[0]](curVarSet, curCnfList)

  ### update variable set and cnf list when literal is chosen
  def chooseBranch(self, curVarSet, curCnfList, literal):
    newVarSet = curVarSet.copy()
    # assert abs(literal) in newVarSet
    newVarSet.remove(abs(literal))
    newCnfList = []
    for clause in curCnfList:
      if literal in clause:
        continue
      elif -literal in clause:
        newClause = clause.copy()
        newClause.remove(-literal)
        newCnfList.append(newClause)
      else:
        newCnfList.append(clause.copy())
    return newVarSet, newCnfList

  ### recursive solver
  def recursiveSolve(self, curCnfList, curVarSet, assignment, heuristics = None):
    # set heuristics
    if heuristics == None:
      heuristics = self.twoSidedJeroslowWangLiteral
    
    # initial condition
    if not curCnfList:
      return True, curVarSet.union(assignment)
    if set() in curCnfList:
      return False, set()

    # remove unit/pure literals
    changed = True
    while changed:
      sat, tmp1, curCnfList, curVarSet, assignment = self.removeUnitLiterals(curCnfList, curVarSet, assignment)
      if not sat:  
        return sat, set()
      tmp2, curCnfList, curVarSet, assignment = self.removePureLiterals(curCnfList, curVarSet, assignment)
      changed = tmp1 or tmp2
    if not curCnfList:
      return True, curVarSet.union(assignment)
    if set() in curCnfList:
      return False, set()

    # choose a random literal from curVarSet
    literal = heuristics(curVarSet, curCnfList)

    # Branch 1
    newVarSet, newCnfList = self.chooseBranch(curVarSet, curCnfList, literal)
    assignment.add(literal)
    sat, newAssignment = self.recursiveSolve(newCnfList, newVarSet, assignment, heuristics)
    if sat:
      return sat, newAssignment

    # Try the other branch
    assignment.remove(literal)
    newVarSet, newCnfList = self.chooseBranch(curVarSet, curCnfList, -literal)
    assignment.add(-literal)
    sat, newAssignment = self.recursiveSolve(newCnfList, newVarSet, assignment, heuristics)
    if sat:
      return sat, newAssignment
    
    # Both branch failed
    return False, set()
    
def main():
  args = sys.argv
  if len(args) != 2:
    print('usage error : python3 sat_solver.py [FILENAME.cnf]')
    return
  solver = Solver(args[1])
  res = solver.solve()
  print(json.dumps(res))

if __name__ == '__main__':
  main()
