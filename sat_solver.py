import sys

def main():
  args = sys.argv
  if len(args) != 2:
    print('ussage error : python3 sat_solver.py [FILENAME.cnf]')
    return
  varSet, cnfList = read_cnf(args[1])
  print(varSet)
  print(cnfList)

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
