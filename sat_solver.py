import sys
import random
import time
class Solver:
  varSet = set()
  cnfList = []
  filename = ''
  assignment = set()
  def __init__(self, filename):
    f = open(filename, 'r')
    line = f.readline()
    self.filename = filename
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
      cnf = set([int(v) for v in lineSplitted][:-1])
      self.cnfList.append(cnf)
    f.close()

  def solve(self):
    # start timing
    start_time = time.time()
    # remove pure literals

    # remove unit literals
    sat, assignment = self.recursiveSolve(self.varSet, self.cnfList)
    end_time = time.time()
    # end timing
    assignment = sorted(assignment.union(self.assignment), key = lambda x: abs(x))
    res = {}
    res['Instance'] = self.filename
    res['Result'] = 'SAT' if sat else 'UNSAT'
    res['Solution'] = ' '.join(['%d True' % (v) if v > 0 else '%d False' % (-v) for v in assignment])
    res['Time'] = '%f' % (end_time-start_time)
    return res

  def removeUnitLiterals(self):
    observed = set()
    # go through all clauses
    for clause in self.cnfList:
      if len(clause) == 1 and -clause.peek() not in observed:
        observed.add(clause.peek())

    return True


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
    for cnf in curCnfList:
      if literal in cnf:
        continue
      elif -literal in cnf:
        newCnf = cnf.copy()
        newCnf.remove(-literal)
        newCnfList.append(newCnf)
      else:
        newCnfList.append(cnf.copy())
    return newVarSet, newCnfList

  def recursiveSolve(self, curVarSet, curCnfList):
    # check initial condition
    if not curCnfList:
      return True, curVarSet
    if set() in curCnfList:
      return False, None
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
    return False, None
    
    

def main():
  args = sys.argv
  if len(args) != 2:
    print('ussage error : python3 sat_solver.py [FILENAME.cnf]')
    return
  # varSet, cnfList = read_cnf(args[1])
  # print(varSet)
  # print(cnfList)
  solver = Solver(args[1])
  # print(solver.varSet)
  # print(solver.cnfList)
  res = solver.solve()
  print(res)

def read_cnf(filename):
  f = open(filename, 'r')
  line = f.readline()
  while line[0] != 'p':
    line = f.readline()
  tokens = line.split()
  varSize = int(tokens[2])
  cnfSize = int(tokens[3])
  varSet = set(range(1, varSize+1))
  cnfList = []
  for _ in range(cnfSize):
    line = f.readline()
    lineSplitted = line.split()
    cnf = set([int(v) for v in lineSplitted][:-1])
    cnfList.append(cnf)
  return varSet, cnfList



if __name__ == '__main__':
  main()
