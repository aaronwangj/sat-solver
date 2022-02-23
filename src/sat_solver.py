import sys
import random
import time
import json
import os
class Solver:
  varSet = set()
  cnfList = []
  filename = ''
  assignment = set()
  def __init__(self, filename):
    f = open(filename, 'r')
    line = f.readline()
    self.filename = os.path.basename(os.path.normpath(filename))
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
    result = {}
    result["Instance"] = self.filename[:-4]
    start_time = time.time()
    # remove unit literals
    sat = False
    assignment = set()
    changed = True
    while changed:
      sat, tmp1 = self.removeUnitLiterals()
      if not sat:
        end_time = time.time()
        result['Result'] = 'UNSAT'
        result['Time'] = '%f' % (end_time-start_time)
        return result
      tmp2 = self.removePureLiterals()
      changed = tmp1 or tmp2
    sat, assignment = self.recursiveSolve(self.varSet, self.cnfList)
    if sat:
      assignment = sorted(self.assignment.union(assignment), key = lambda x: abs(x))
    end_time = time.time()
    result['Result'] = 'SAT' if sat else 'UNSAT'
    if sat:
      result['Solution'] = ' '.join(['%d true' % (v) if v > 0 else '%d false' % (-v) for v in assignment])
    result['Time'] = '%f' % (end_time-start_time)
    return result

  def removeUnitLiterals(self):
    # go through all clauses
    changed = False
    for clause in self.cnfList:
      if len(clause) == 1:
        literal = next(iter(clause))
        if -literal in self.assignment:
          return False, True
        elif literal not in self.assignment:
          changed = True
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
    return True, changed

  def removePureLiterals(self):
    changed = False
    observed = set()
    for clause in self.cnfList:
      for literal in clause:
        observed.add(literal)
    newVarSet = self.varSet.copy()
    for var in self.varSet:
      if var not in observed or -var not in observed:
        changed = True
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
    return changed

  def randomLiteral(self, curVarSet, curCnfList):
    # purely random
    var = random.sample(curVarSet, 1)[0]
    literal = -var if random.getrandbits(1) else var
    return literal

  def dlcsLiteral(self, curVarSet, curCnfList):
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
    literal = self.dlcsLiteral(curVarSet, curCnfList)
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
    print('usage error : python3 sat_solver.py [FILENAME.cnf]')
    return
  solver = Solver(args[1])
  res = solver.solve()
  print(json.dumps(res))

if __name__ == '__main__':
  main()
