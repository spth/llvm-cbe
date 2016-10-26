#include <assert.h>
#include <stdint.h>
#include <stdio.h>

#define assertEquals(E, A) \
  assertEquals_f(E, A, __FILE__, __LINE__);

void assertEquals_f(int expected, int actual, const char* file, int line)
{
  if(expected == actual)
    return;

  fprintf(stderr, "Assertion failed at %s(%d):", file, line);
  fprintf(stderr, "  Expected: %d\n", expected);
  fprintf(stderr, "  Actual: %d\n", actual);
  abort();
}
