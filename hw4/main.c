#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

extern uint64_t our_code_starts_here() asm("our_code_starts_here");
extern uint64_t print(uint64_t val) asm("print");
const NUM_TAG_MASK = 0x0000000000000001L;
const TRUE = 0xFFFFFFFFFFFFFFFFL;
const FALSE = 0x7FFFFFFFFFFFFFFFL;

uint64_t print(uint64_t val)
{
  // Number
  if ((NUM_TAG_MASK ^ val) & 1 == 1)
  {
    printf("%n", val);
  }
  else if (val == TRUE)
  {
    printf("true");
  }
  else if (val == FALSE)
  {
    printf("false");
  }
  else
  {
    printf("Unknown value: %#018x\n", val);
  }

  return val;
}

int main(int argc, char **argv)
{
  uint64_t result = our_code_starts_here();
  print(result);
  return 0;
}
