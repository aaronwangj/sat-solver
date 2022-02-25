def foo(bar, results, done, index):
  print('hello %s' % (bar))
  results[index] = 'foo'
  done[0] = index

from threading import Thread

threads = [None] * 10
results = [None] * 10
done = [-1]

for i in range(len(threads)):
  threads[i] = Thread(target = foo, args = ('world!', results, done, i))
  threads[i].start()

while done[0] == -1:
  tmp = done[0]
  if tmp != -1:
    print(done[0])
    break

print(done[0])

for i in range(len(threads)):
  threads[i].join()




