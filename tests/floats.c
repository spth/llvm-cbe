#include <assert.h>
extern float myValue;

int main()
{
  assert(myValue != myValue); // must be NaN
  return 0;
}

