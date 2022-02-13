import sys
import random
import time
import pathlib
class Solver:
  varSet = set()
  cnfList = []
  filename = ''
  assignment = set()
  def __init__(self, filename):
    f = open(filename, 'r')
    line = f.readline()
    self.filename = str(pathlib.PurePath(filename))
    while line[0] != 'p':
      line = f.readline()
    tokens = line.split()
    varSize = int(tokens[2])
    cnfSize = int(tokens[3])
    self.varSet = set(range(1, varSize+1))
    self.cnfList = []
    for _ in range(cnfSize):
      line = f.readline()
      lineSplitted = line.split()
      clause = set([int(v) for v in lineSplitted][:-1])
      self.cnfList.append(clause)
    f.close()

  def solve(self):
    # start timing
    start_time = time.time()
    # remove unit literals
    sat = False
    assignment = set()
    if self.removeUnitLiterals():
      print('unit literals removed')
      self.removePureLiterals()
      print('pure literals removed')
      sat, assignment = self.recursiveSolve(self.varSet, self.cnfList)
      if sat:
        assignment = sorted(self.assignment.union(assignment), key = lambda x: abs(x))
    end_time = time.time()
    res = {}
    res['Instance'] = self.filename
    res['Result'] = 'SAT' if sat else 'UNSAT'
    res['Solution'] = ' '.join(['%d True' % (v) if v > 0 else '%d False' % (-v) for v in assignment])
    res['Time'] = '%f' % (end_time-start_time)
    return res

  def removeUnitLiterals(self):
    # go through all clauses
    for clause in self.cnfList:
      if len(clause) == 1:
        literal = next(iter(clause))
        if -literal in self.assignment:
          return False
        elif literal not in self.assignment:
          self.varSet.remove(abs(literal))
          self.assignment.add(literal)
    newCnfList = []
    for clause in self.cnfList:
      append = True
      newClause = clause.copy()
      for literal in clause:
        if literal in self.assignment:
          append = False
          break
        if -literal in self.assignment:
          newClause.remove(literal)
      if append:
        newCnfList.append(newClause)
    self.cnfList = newCnfList
    return True

  def removePureLiterals(self):
    observed = set()
    for clause in self.cnfList:
      for literal in clause:
        observed.add(literal)
    newVarSet = self.varSet.copy()
    for var in self.varSet:
      if var not in observed or -var not in observed:
        newVarSet.remove(var)
        if -var in observed:
          self.assignment.add(-var)
        else:
          self.assignment.add(var)
    newCnfList = []
    for clause in self.cnfList:
      append = True
      newClause = clause.copy()
      for literal in clause:
        if literal in self.assignment:
          append = False
          break
        if -literal in self.assignment:
          newClause.remove(literal)
      if append:
        newCnfList.append(newClause)
    self.varSet = newVarSet
    self.cnfList = newCnfList

  def randomLiteral(self, curVarSet, curCnfList):
    # purely random
    var = random.sample(curVarSet, 1)[0]
    literal = -var if random.getrandbits(1) else var
    return literal

  def jeroslowWangLiteral(self, curVarSet, curCnfList):
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

  def chooseBranch(self, curVarSet, curCnfList, literal):
    newVarSet = curVarSet.copy()
    newVarSet.remove(abs(literal))
    newCnfList = []
    for clause in curCnfList:
      if literal in clause:
        continue
      elif -literal in clause:
        newCnf = clause.copy()
        newCnf.remove(-literal)
        newCnfList.append(newCnf)
      else:
        newCnfList.append(clause.copy())
    return newVarSet, newCnfList

  def recursiveSolve(self, curVarSet, curCnfList):
    # check initial condition
    if not curCnfList:
      return True, curVarSet
    if set() in curCnfList:
      return False, set()
    # choose a random literal from curVarSet
    literal = self.twoSidedJeroslowWangLiteral(curVarSet, curCnfList)
    # Branch 1
    newVarSet, newCnfList = self.chooseBranch(curVarSet, curCnfList, literal)
    sat, assignment = self.recursiveSolve(newVarSet, newCnfList)
    if sat:
      assignment.add(literal)
      return sat, assignment
    # Try the other branch
    newVarSet, newCnfList = self.chooseBranch(curVarSet, curCnfList, -literal)
    sat, assignment = self.recursiveSolve(newVarSet, newCnfList)
    if sat:
      assignment.add(-literal)
      return sat, assignment
    return False, set()
    
    

def main():
  args = sys.argv
  if len(args) != 2:
    print('ussage error : python3 sat_solver.py [FILENAME.cnf]')
    return
  solver = Solver(args[1])
  res = solver.solve()
  print(res)



if __name__ == '__main__':
  main()
