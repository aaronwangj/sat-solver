from hashlib import new
import sys
import random
import time
import json
import os
class Solver:
  varSet = set()
  cnfList = []
  filename = ''
  varSize = 0
  cnfSize = 0
  def __init__(self, filename):
    f = open(filename, 'r')
    line = f.readline()
    self.filename = os.path.basename(os.path.normpath(filename))
    while line[0] != 'p':
      line = f.readline()
    tokens = line.split()
    varSize = int(tokens[2])
    cnfSize = int(tokens[3])
    self.varSize = varSize
    self.cnfSize = cnfSize
    self.varSet = set(range(1, varSize+1))
    self.cnfList = []
    for _ in range(cnfSize):
      line = f.readline()
      lineSplitted = line.split()
      clause = set([int(v) for v in lineSplitted][:-1])
      self.cnfList.append(clause)
    f.close()

  def solve(self):
    # solve
    start_time = time.time()
    assignment = set()
    sat, assignment = self.recursiveSolve(self.cnfList, self.varSet, assignment)
    end_time = time.time()
    # record
    result = {}
    result["Instance"] = self.filename[:-4] if self.filename[-4:] == '.cnf' else self.filename
    if sat:
      assignment = sorted(assignment, key = lambda x: abs(x))
      result['Solution'] = ' '.join(['%d true' % (v) if v > 0 else '%d false' % (-v) for v in assignment])
    result['Result'] = 'SAT' if sat else 'UNSAT'
    result['Time'] = '%.2f' % (end_time-start_time)
    return result
  
  def removeUnitLiterals(self, cnfList, varSet, assignment):
    # go through all clauses
    assert len(varSet) + len(assignment) == self.varSize
    newCnfList = []
    newVarSet = varSet.copy()
    newAssignment = assignment.copy()
    changed = False
    for clause in cnfList:
      if len(clause) == 1:
        literal = next(iter(clause))
        if -literal in newAssignment:
          assert len(newVarSet) + len(newAssignment) == self.varSize
          return False, True, newCnfList, newVarSet, assignment
        elif literal not in newAssignment:
          changed = True
          newVarSet.remove(abs(literal))
          newAssignment.add(literal)
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
    assert len(newVarSet) + len(newAssignment) == self.varSize
    return True, changed, newCnfList, newVarSet, newAssignment

  def removePureLiterals(self, cnfList, varSet, assignment):
    assert len(varSet) + len(assignment) == self.varSize
    newCnfList = []
    newVarSet = varSet.copy()
    newAssignment = assignment.copy()
    changed = False
    observed = set()
    for clause in cnfList:
      for literal in clause:
        observed.add(literal)
    for var in varSet:
      if var not in observed or -var not in observed:
        changed = True
        newVarSet.remove(var)
        if -var in observed:
          newAssignment.add(-var)
        else:
          newAssignment.add(var)
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
    assert len(newVarSet) + len(newAssignment) == self.varSize
    return changed, newCnfList, newVarSet, newAssignment

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
    assert abs(literal) in newVarSet
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

  def recursiveSolve(self, curCnfList, curVarSet, assignment, heuristics = None):
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
