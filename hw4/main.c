#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

extern uint64_t our_code_starts_here() asm("our_code_starts_here");
extern uint64_t print(uint64_t val) asm("print");
const uint64_t NUM_TAG_MASK = 0x0000000000000001L;
const uint64_t BOOL_TAG_MASK = 0x0000000000000007L;
const uint64_t TRUE = 0xFFFFFFFFFFFFFFFFL;
const uint64_t FALSE = 0x7FFFFFFFFFFFFFFFL;

uint64_t print(uint64_t val)
{
  // Number
  if (((NUM_TAG_MASK ^ val) & 1) == 1)
  {
    printf("%lu", val >> 1); // maybe llu/lld/ld?
  }
  else if (val == TRUE)
  {
    printf("true");
  }
  else if (val == FALSE)
  {
    printf("false");
  }
  else if (((BOOL_TAG_MASK ^ val) & 1) == 1)
  {
    printf("Bool tag provided with hex value: %#018lx\n", val);
  }
  else
  {
    printf("Unknown value and type: %#018lx\n", val);
  }

  return val;
}

int main(int argc, char **argv)
{
  uint64_t result = our_code_starts_here();
  print(result);
  return 0;
}
