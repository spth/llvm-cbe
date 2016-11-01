#include "test.h"

int32_t get42();

int main()
{
  assertEquals(42, get42());
  return 0;
}

