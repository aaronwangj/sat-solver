import sys

def read_cnf(filename):
  f = open(filename, 'r')
  line = f.readline()
  while line[0] != 'p':
    line = f.readline()
  tokens = line.split()
  varSize = tokens[2]
  cnfSize = tokens[3]
  varSet = set(range(1, varSize+1))
  cnfList = []
  for _ in range(cnfSize):
    line = f.readline()
    lineSplitted = line.split()
    cnf = set(lineSplitted[:-1])
    cnfList.append(cnf)
  return varSet, cnfList



# if __name__ == '__main__':
  # do things
args = sys.argv
  # if len(args) != 2:
  #   # usage error
  #   print('ussage error : TODO')
varSet, cnfList = read_cnf(args[1])
print(varSet)
print(cnfList)
