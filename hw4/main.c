#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

extern uint64_t our_code_starts_here() asm("our_code_starts_here");
extern uint64_t print(uint64_t val) asm("print");
extern void error(uint64_t errCode, uint64_t val) asm("error");
const uint64_t NUM_TAG_MASK = 0x0000000000000001L;
const uint64_t BOOL_TAG_MASK = 0x0000000000000007L;
const uint64_t TRUE = 0xFFFFFFFFFFFFFFFFL;
const uint64_t FALSE = 0x7FFFFFFFFFFFFFFFL;
const uint64_t COMP_NOT_NUM = 1L;
const uint64_t ARITH_NOT_NUM = 2L;
const uint64_t LOGIC_NOT_BOOL = 3L;
const uint64_t IF_NOT_BOOL = 4L;
const uint64_t OVERFLOW = 5L;

void error(uint64_t errCode, uint64_t val) {
  if (errCode == COMP_NOT_NUM) {
    fprintf(stderr, "Expected number type for comparison op, got %#018lx\n", val);
  } else if (errCode == ARITH_NOT_NUM) {
    fprintf(stderr, "Expected number type for arithmetic op, got %#018lx\n", val);
  } else if (errCode == LOGIC_NOT_BOOL) {
    fprintf(stderr, "Expected bool type for logical op, got %#018lx\n", val);
  } else if (errCode == IF_NOT_BOOL) {
    fprintf(stderr, "Expected bool type for if stmt, got %#018lx\n", val);
  } else if (errCode == OVERFLOW) {
    fprintf(stderr, "Overflow occurred for arithmetic operation, got %#018lx\n", val);
  } else {
    fprintf(stderr, "Unknown error code provided (%#018lx\n) for value %#018lx\n", 
        errCode, val);
  }

  exit(errCode);
}

uint64_t print(uint64_t val)
{
  // Number
  if (((NUM_TAG_MASK ^ val) & 1) == 1)
  {
    printf("%lu\n", val >> 1); // maybe llu/lld/ld?
  }
  else if (val == TRUE)
  {
    printf("true\n");
  }
  else if (val == FALSE)
  {
    printf("false\n");
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
