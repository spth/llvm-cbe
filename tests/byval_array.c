#include "test.h"

typedef struct
{
  int32_t values[4];
} array;

int32_t sum_of_squares(array a);

int main()
{
  array a;
  a.values[0] = 1;
  a.values[1] = 2;
  a.values[2] = 3;
  a.values[3] = 4;
  assertEquals(1*1+2*2+3*3+4*4, sum_of_squares(a));

  // sanity check
  assert(a.values[0] == 1);
  assert(a.values[1] == 2);
  assert(a.values[2] == 3);
  assert(a.values[3] == 4);
  return 0;
}

